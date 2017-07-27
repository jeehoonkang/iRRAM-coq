From iris.program_logic Require Export weakestpre.
From iris.base_logic.lib Require Export invariants.
From iris.heap_lang Require Export lang.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import frac_auth auth.
From iRRAM.lang Require Import proofmode notation.
Require Import Reals String.
Require Export ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlZInt ExtrOcamlString.
Set Default Proof Using "Type".


(* monad *)

Inductive result T :=
| OK (t:T)
| Err (err:string)
.
Arguments OK {T}.
Arguments Err {T}.

Definition bind {T1 T2} (e1:result T1) (e2:T1 -> result T2): result T2 :=
  match e1 with
  | OK e1 => e2 e1
  | Err err => Err err
  end.


(* types *)

Inductive iRRAM_expr :=
| iRRAM_Var (x:string)
| iRRAM_Lit (l:base_lit)
| iRRAM_UnOp (op:un_op) (e1:iRRAM_expr)
| iRRAM_BinOp (op:bin_op) (e1 e2:iRRAM_expr)
| iRRAM_TernOp (op:tern_op) (e1 e2 e3:iRRAM_expr)
| iRRAM_Pair (e1 e2:iRRAM_expr)
| iRRAM_Fst (e1:iRRAM_expr)
| iRRAM_Snd (e1:iRRAM_expr)
| iRRAM_Load (e1:iRRAM_expr)
.

Inductive iRRAM_stmt :=
| iRRAM_Return (e1:iRRAM_expr)
| iRRAM_VarDecl (x:string) (e1:iRRAM_expr)
| iRRAM_While (e1:iRRAM_expr) (e2:list iRRAM_stmt)
| iRRAM_Repeat (e1:list iRRAM_stmt) (e2:iRRAM_expr)
| iRRAM_If (e1:iRRAM_expr) (e2 e3:list iRRAM_stmt)
| iRRAM_Store (e1 e2:iRRAM_expr)
.

Inductive iRRAM_type :=
| iRRAM_Int
| iRRAM_Bool
| iRRAM_REAL
.

Structure iRRAM_function := mk_iRRAM_function {
  name: string;
  params: list (iRRAM_type * string);
  restype: iRRAM_type;
  body: list iRRAM_stmt;
}.


(* converter *)

Fixpoint to_iRRAM_expr (e:expr): result iRRAM_expr :=
  match e with
  | Var x => OK $ iRRAM_Var x
  | Rec _ _ _ => Err "to_iRRAM_expr: Rec not supported"
  | App _ _ => Err "to_iRRAM_expr: App not supported"
  | While _ _ => Err "to_iRRAM_expr: While not supported"
  | Repeat _ _ => Err "to_iRRAM_expr: Repeat not supported"
  | Lit l => OK $ iRRAM_Lit l
  | UnOp op e1 =>
    bind (to_iRRAM_expr e1) (fun v1 =>
      OK $ iRRAM_UnOp op v1)
  | BinOp op e1 e2 =>
    bind (to_iRRAM_expr e1) (fun v1 =>
    bind (to_iRRAM_expr e2) (fun v2 =>
      OK $ iRRAM_BinOp op v1 v2))
  | TernOp op e1 e2 e3 =>
    bind (to_iRRAM_expr e1) (fun v1 =>
    bind (to_iRRAM_expr e2) (fun v2 =>
    bind (to_iRRAM_expr e3) (fun v3 =>
      OK $ iRRAM_TernOp op v1 v2 v3)))
  | If _ _ _ => Err "to_iRRAM_expr: If not supported"
  | Pair e1 e2 =>
    bind (to_iRRAM_expr e1) (fun v1 =>
    bind (to_iRRAM_expr e2) (fun v2 =>
      OK $ iRRAM_Pair v1 v2))
  | Fst e1 =>
    bind (to_iRRAM_expr e1) (fun v1 =>
      OK $ iRRAM_Fst v1)
  | Snd e1 =>
    bind (to_iRRAM_expr e1) (fun v1 =>
      OK $ iRRAM_Snd v1)
  | InjL _ => Err "to_iRRAM_expr: InjL not supported"
  | InjR _ => Err "to_iRRAM_expr: InjR not supported"
  | Case _ _ _ => Err "to_iRRAM_expr: Case not supported"
  | Fork _ => Err "to_iRRAM_expr: Fork not supported"
  | Alloc _ => Err "to_iRRAM_expr: Alloc not supported"
  | Load e1 =>
    bind (to_iRRAM_expr e1) (fun v1 =>
      OK $ iRRAM_Load v1)
  | Store _ _ => Err "to_iRRAM_expr: Store not supported"
  | CAS _ _ _ => Err "to_iRRAM_expr: CAS not supported"
  end.

Fixpoint to_iRRAM_stmts (e:expr): result (list iRRAM_stmt) :=
  match e with
  | Seq e1 e2 =>
    bind (to_iRRAM_stmts e1) (fun v1 =>
    bind (to_iRRAM_stmts e2) (fun v2 =>
      OK $ (v1 ++ v2)))
  | Let (BNamed x) (Alloc e1) e2 =>
    bind (to_iRRAM_expr e1) (fun v1 =>
    bind (to_iRRAM_stmts e2) (fun v2 =>
      OK $ (iRRAM_VarDecl x v1) :: v2))
  | While e1 e2 =>
    bind (to_iRRAM_expr e1) (fun v1 =>
    bind (to_iRRAM_stmts e2) (fun v2 =>
      OK $ [iRRAM_While v1 v2]))
  | Repeat e1 e2 =>
    bind (to_iRRAM_stmts e1) (fun v1 =>
    bind (to_iRRAM_expr e2) (fun v2 =>
      OK $ [iRRAM_Repeat v1 v2]))
  | If e1 e2 e3 =>
    bind (to_iRRAM_expr e1) (fun v1 =>
    bind (to_iRRAM_stmts e2) (fun v2 =>
    bind (to_iRRAM_stmts e3) (fun v3 =>
      OK $ [iRRAM_If v1 v2 v3])))
  | Store e1 e2 =>
    bind (to_iRRAM_expr e1) (fun v1 =>
    bind (to_iRRAM_expr e2) (fun v2 =>
      OK $ [iRRAM_Store v1 v2]))
  | e1 =>
    bind (to_iRRAM_expr e1) (fun v1 =>
      OK $ [iRRAM_Return v1])
  end.

Fixpoint to_iRRAM_params (paramtypes: list iRRAM_type) (e:expr): result (list (iRRAM_type * string) * expr) :=
  match paramtypes, e with
  | ptype::ptypes, Lam (BNamed x) e =>
    bind (to_iRRAM_params ptypes e) (fun r =>
      OK ((ptype, x) :: r.(fst), r.(snd)))
  | [], _ =>
    OK ([], e)
  | _, _ =>
    Err "to_iRRAM_params: invalid expression"
  end.

Definition to_iRRAM_function (name:string) (paramtypes: list iRRAM_type) (restype: iRRAM_type) (e:expr)
  : result iRRAM_function :=
  bind (to_iRRAM_params paramtypes e) (fun r =>
  bind (to_iRRAM_stmts r.(snd)) (fun s =>
    OK $ mk_iRRAM_function name r.(fst) restype s)).

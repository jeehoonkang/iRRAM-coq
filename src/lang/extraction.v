From iris.program_logic Require Export weakestpre.
From iris.base_logic.lib Require Export invariants.
From iris.heap_lang Require Export lang.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import frac_auth auth.
From iRRAM.lang Require Import proofmode notation.
Require Import Reals String.
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

(* to_string *)

Definition newline := String "010" "".

Definition lit_to_string (l:base_lit): string :=
  match l with
  | LitInt z => "TODO"
  | LitREAL r => "TODO"
  | LitBool b => "TODO"
  | LitUnit => "void"
  | LitLoc l => "loc"
  end.

Definition un_op_to_string (op:un_op): string :=
  match op with
  | NegOp => "~"
  | MinusUnOp => "-"
  end.

Definition bin_op_to_string (op:bin_op): string :=
  match op with
  | PlusOp => "+"
  | MinusOp => "-"
  | MulOp => "*"
  | DivOp => "/"
  | PowOp => "^"
  | LeOp => "<="
  | LtOp => "<"
  | EqOp => "=="
  end.

Definition iRRAM_bin_op_to_string op v1 v2: string :=
  match op with
  | PowOp => "REAL_pow(" ++ v1 ++ ", " ++ v2 ++ ")"
  | _ => "(" ++ v1 ++ " " ++ (bin_op_to_string op) ++ " " ++ v2 ++ ")"
  end.

Definition iRRAM_tern_op_to_string op v1 v2 v3: string :=
  match op with
  | RLtOp => "REAL_lt(" ++ v1 ++ ", " ++ v2 ++ ", " ++ v3 ++ ")"
  end.

Fixpoint iRRAM_expr_to_string (e:iRRAM_expr): string :=
  match e with
  | iRRAM_Var x => x
  | iRRAM_Lit l => lit_to_string l
  | iRRAM_UnOp op e1 => "(" ++ (un_op_to_string op) ++ " " ++ (iRRAM_expr_to_string e1) ++ ")"
  | iRRAM_BinOp op e1 e2 => iRRAM_bin_op_to_string op (iRRAM_expr_to_string e1) (iRRAM_expr_to_string e2)
  | iRRAM_TernOp op e1 e2 e3 => iRRAM_tern_op_to_string op (iRRAM_expr_to_string e1) (iRRAM_expr_to_string e2) (iRRAM_expr_to_string e3)
  | iRRAM_Pair e1 e2 => "make_pair(" ++ (iRRAM_expr_to_string e1) ++ ", " ++ (iRRAM_expr_to_string e2) ++ ")"
  | iRRAM_Fst e1 => (iRRAM_expr_to_string e1) ++ ".first"
  | iRRAM_Snd e1 => (iRRAM_expr_to_string e1) ++ ".second"
  | iRRAM_Load e1 => "(*" ++ (iRRAM_expr_to_string e1) ++ ")"
  end.

Fixpoint spaces (indent:nat): string :=
  match indent with
  | O => ""
  | S indent' => "  " ++ (spaces indent')
  end.

Definition iRRAM_stmts_to_string_ (iRRAM_stmts_to_string:nat -> iRRAM_stmt -> string) (indent:nat) (s:list iRRAM_stmt): string :=
  fold_left append (map (iRRAM_stmts_to_string indent) s) "".

Fixpoint iRRAM_stmt_to_string (indent:nat) (s:iRRAM_stmt): string :=
  match s with
  | iRRAM_Return e1 => (spaces indent) ++ "return " ++ (iRRAM_expr_to_string e1) ++ ";" ++ newline
  | iRRAM_VarDecl x e1 => (spaces indent) ++ "auto " ++ x ++ " = " ++ (iRRAM_expr_to_string e1) ++ ";" ++ newline
  | iRRAM_While e1 e2 =>
    (spaces indent) ++ "while (" ++ (iRRAM_expr_to_string e1) ++ ") {" ++ newline ++
    iRRAM_stmts_to_string_ iRRAM_stmt_to_string (S indent) e2 ++
    (spaces indent) ++ "}" ++ newline
  | iRRAM_Repeat e1 e2 =>
    (spaces indent) ++ "do {" ++ newline ++
    iRRAM_stmts_to_string_ iRRAM_stmt_to_string (S indent) e1 ++
    (spaces indent) ++ "} while (" ++ (iRRAM_expr_to_string e2) ++ ");" ++ newline
  | iRRAM_If e1 e2 e3 =>
    (spaces indent) ++ "if (" ++ (iRRAM_expr_to_string e1) ++ ") {" ++ newline ++
    iRRAM_stmts_to_string_ iRRAM_stmt_to_string (S indent) e2 ++
    (spaces indent) ++ "}" ++ newline ++
    (spaces indent) ++ "else {" ++ newline ++
    iRRAM_stmts_to_string_ iRRAM_stmt_to_string (S indent) e3 ++
    (spaces indent) ++ "}" ++ newline
  | iRRAM_Store e1 e2 =>
    (spaces indent) ++ "*(" ++ (iRRAM_expr_to_string e1) ++ ") = " ++ (iRRAM_expr_to_string e2) ++ ";" ++ newline
  end.

Definition iRRAM_stmts_to_string := iRRAM_stmts_to_string_ iRRAM_stmt_to_string.

Definition iRRAM_type_to_string t :=
  match t with
  | iRRAM_Int => "int"
  | iRRAM_Bool => "Bool"
  | iRRAM_REAL => "REAL"
  end.

Definition iRRAM_function_to_string f: string :=
  (iRRAM_type_to_string f.(restype)) ++ " " ++ f.(name) ++ "(" ++
  "TODO" ++
  ") {" ++ newline ++
  (iRRAM_stmts_to_string 1 f.(body)) ++
  "}" ++ newline.


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

Definition expr_to_iRRAM_function_string (name:string) (paramtypes: list iRRAM_type) (restype: iRRAM_type) (e:expr): string :=
  match to_iRRAM_function name paramtypes restype e with
  | OK f => iRRAM_function_to_string f
  | Err err => "// " ++ err
  end.

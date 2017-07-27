open Lang
open Extraction


let camlstring_of_coqstring (s: char list) =
  let r = Bytes.create (List.length s) in
  let rec fill pos = function
  | [] -> r
  | c :: s -> Bytes.set r pos c; fill (pos + 1) s
  in Bytes.to_string (fill 0 s)

let coqstring_of_camlstring s =
  let rec cstring accu pos =
    if pos < 0 then accu else cstring (s.[pos] :: accu) (pos - 1)
  in cstring [] (String.length s - 1)


open Coq_heap_lang

let string_of_lit (l:base_lit): string =
  match l with
  | LitInt(z) -> string_of_int z
  | LitREAL(r) -> TODO
  | LitBool(b) -> string_of_bool b
  | LitUnit -> "void"
  | LitLoc(l) -> "loc"

let string_of_un_op (op:un_op): string =
  match op with
  | NegOp -> "~"
  | MinusUnOp -> "-"

let bin_op_to_string (op:bin_op): string =
  match op with
  | PlusOp -> "+"
  | MinusOp -> "-"
  | MulOp -> "*"
  | DivOp -> "/"
  | PowOp -> "^"
  | LeOp -> "<="
  | LtOp -> "<"
  | EqOp -> "=="

let string_of_bin_op op v1 v2: string =
  match op with
  | PowOp -> "REAL_pow(" ++ v1 ++ ", " ++ v2 ++ ")"
  | _ -> "(" ++ v1 ++ " " ++ (bin_op_to_string op) ++ " " ++ v2 ++ ")"

let iRRAM_tern_op_to_string op v1 v2 v3: string =
  match op with
  | RLtOp -> "REAL_lt(" ++ v1 ++ ", " ++ v2 ++ ", " ++ v3 ++ ")"

let rec string_of_expr (e:iRRAM_expr): string =
  match e with
  | iRRAM_Var x -> x
  | iRRAM_Lit l -> lit_to_string l
  | iRRAM_UnOp op e1 -> "(" ++ (un_op_to_string op) ++ " " ++ (iRRAM_expr_to_string e1) ++ ")"
  | iRRAM_BinOp op e1 e2 -> iRRAM_bin_op_to_string op (iRRAM_expr_to_string e1) (iRRAM_expr_to_string e2)
  | iRRAM_TernOp op e1 e2 e3 -> iRRAM_tern_op_to_string op (iRRAM_expr_to_string e1) (iRRAM_expr_to_string e2) (iRRAM_expr_to_string e3)
  | iRRAM_Pair e1 e2 -> "make_pair(" ++ (iRRAM_expr_to_string e1) ++ ", " ++ (iRRAM_expr_to_string e2) ++ ")"
  | iRRAM_Fst e1 -> (iRRAM_expr_to_string e1) ++ ".first"
  | iRRAM_Snd e1 -> (iRRAM_expr_to_string e1) ++ ".second"
  | iRRAM_Load e1 -> "(*" ++ (iRRAM_expr_to_string e1) ++ ")"

let rec spaces (indent:int): string =
  if indent <= 0
  then ""
  else " " + (spaces (indent - 1))

let 

let rec string_of_stmt ?(indent=0) (s:iRRAM_stmt): string =
  match s with
  | iRRAM_Return e1 -> (spaces indent) ++ "return " ++ (iRRAM_expr_to_string e1) ++ ";\n"
  | iRRAM_VarDecl x e1 -> (spaces indent) ++ "auto " ++ x ++ " = " ++ (iRRAM_expr_to_string e1) ++ ";\n"
  | iRRAM_While e1 e2 ->
    (spaces indent) ++ "while (" ++ (iRRAM_expr_to_string e1) ++ ") {\n" ++
    string_of_stmts ~indent:(indent + 1) e) e2 ++
    (spaces indent) ++ "}\n"
  | iRRAM_Repeat e1 e2 ->
    (spaces indent) ++ "do {\n" ++
    string_of_stmts ~indent:(indent + 1) e1 ++
    (spaces indent) ++ "} while (" ++ (iRRAM_expr_to_string e2) ++ ");\n"
  | iRRAM_If e1 e2 e3 ->
    (spaces indent) ++ "if (" ++ (iRRAM_expr_to_string e1) ++ ") {\n" ++
    string_of_stmts ~indent:(indent + 1) e2 ++
    (spaces indent) ++ "}\n" ++
    (spaces indent) ++ "else {\n" ++
    string_of_stmts ~indent:(indent + 1) e3 ++
    (spaces indent) ++ "}\n"
  | iRRAM_Store e1 e2 ->
    (spaces indent) ++ "*(" ++ (iRRAM_expr_to_string e1) ++ ") = " ++ (iRRAM_expr_to_string e2) ++ ";\n"

and string_of_stmts ?(indent=0) (s:list iRRAM_stmt): string =
  String.concat ";\n" (List.map (string_of_stmt ~indent:indent) s)

let string_of_type t =
  match t with
  | iRRAM_Int -> "int"
  | iRRAM_Bool -> "bool"
  | iRRAM_REAL -> "REAL"

let string_of_function f =
  (string_of_type f.(restype)) ++ " " ++ f.(name) ++ "(" ++
  "TODO" ++
  ") {\n" ++
  (string_of_stmts 1 f.(body)) ++
  "}\n".

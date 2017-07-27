open Batteries
open Printf
open Datatypes
open Lang
open Extraction


let camlstring_of_coqstring (s: char list) =
  let r = Bytes.create (List.length s) in
  let rec fill pos = function
  | [] -> r
  | c :: s -> Bytes.set r pos c; fill (pos + 1) s
  in Bytes.to_string (fill 0 s)


open Coq_heap_lang

let string_of_lit (l:base_lit): string =
  match l with
  | LitInt(z) -> string_of_int z
  | LitREAL(r) -> "TODO"
  | LitBool(b) -> string_of_bool b
  | LitUnit -> "void"
  | LitLoc(l) -> "loc"

let string_of_un_op (op:un_op): string =
  match op with
  | NegOp -> "~"
  | MinusUnOp -> "-"
  | RCastOp -> "REAL"

let string_of_un_op op v1: string =
  match op with
  | RCastOp -> sprintf "REAL(%s)" v1
  | _ -> sprintf "(%s %s)" (string_of_un_op op) v1

let string_of_bin_op (op:bin_op): string =
  match op with
  | PlusOp -> "+"
  | MinusOp -> "-"
  | MulOp -> "*"
  | DivOp -> "/"
  | PowOp -> "^"
  | RQuotOp -> "REAL"
  | LeOp -> "<="
  | LtOp -> "<"
  | EqOp -> "=="

let string_of_bin_op op v1 v2: string =
  match op with
  | PowOp -> sprintf "power(%s, %s)" v1 v2
  | RQuotOp -> sprintf "(REAL(%s) / REAL(%s))" v1 v2
  | _ -> sprintf "(%s %s %s)" v1 (string_of_bin_op op) v2

let string_of_tern_op op v1 v2 v3: string =
  match op with
  | RLtOp -> sprintf "REAL_lt(%s, %s, %s)" v1 v2 v3

let rec string_of_expr (e:iRRAM_expr): string =
  match e with
  | Coq_iRRAM_Var x -> camlstring_of_coqstring x
  | Coq_iRRAM_Lit l -> string_of_lit l
  | Coq_iRRAM_UnOp (op, e1) -> string_of_un_op op (string_of_expr e1)
  | Coq_iRRAM_BinOp (op, e1, e2) -> string_of_bin_op op (string_of_expr e1) (string_of_expr e2)
  | Coq_iRRAM_TernOp (op, e1, e2, e3) -> string_of_tern_op op (string_of_expr e1) (string_of_expr e2) (string_of_expr e3)
  | Coq_iRRAM_Pair (e1, e2) -> sprintf "make_pair(%s, %s)" (string_of_expr e1) (string_of_expr e2)
  | Coq_iRRAM_Fst e1 -> sprintf "(%s.first)" (string_of_expr e1)
  | Coq_iRRAM_Snd e1 -> sprintf "(%s.second)" (string_of_expr e1)
  | Coq_iRRAM_Load e1 -> (string_of_expr e1)

let rec spaces (indent:int): string =
  if indent <= 0
  then ""
  else "  " ^ (spaces (indent - 1))

let rec string_of_stmt ?(indent=0) (s:iRRAM_stmt): string =
  match s with
  | Coq_iRRAM_Return e1 -> (spaces indent) ^ "return " ^ (string_of_expr e1) ^ ";\n"
  | Coq_iRRAM_VarDecl (x, e1) -> (spaces indent) ^ "auto " ^ (camlstring_of_coqstring x) ^ " = " ^ (string_of_expr e1) ^ ";\n"
  | Coq_iRRAM_While (e1, e2) ->
    (spaces indent) ^ "while (" ^ (string_of_expr e1) ^ ") {\n" ^
    (string_of_stmts ~indent:(indent + 1) e2) ^
    (spaces indent) ^ "}\n"
  | Coq_iRRAM_Repeat (e1, e2) ->
    (spaces indent) ^ "do {\n" ^
    string_of_stmts ~indent:(indent + 1) e1 ^
    (spaces indent) ^ "} while (" ^ (string_of_expr e2) ^ ");\n"
  | Coq_iRRAM_If (e1, e2, e3) ->
    (spaces indent) ^ "if (" ^ (string_of_expr e1) ^ ") {\n" ^
    string_of_stmts ~indent:(indent + 1) e2 ^
    (spaces indent) ^ "}\n" ^
    (spaces indent) ^ "else {\n" ^
    string_of_stmts ~indent:(indent + 1) e3 ^
    (spaces indent) ^ "}\n"
  | Coq_iRRAM_Store (e1, e2) ->
    (spaces indent) ^ (string_of_expr e1) ^ " = " ^ (string_of_expr e2) ^ ";\n"

and string_of_stmts ?(indent=0) (s:iRRAM_stmt list): string =
  String.concat "\n" (List.map (string_of_stmt ~indent:indent) s)

let string_of_type t =
  match t with
  | Coq_iRRAM_Int -> "int"
  | Coq_iRRAM_Bool -> "bool"
  | Coq_iRRAM_REAL -> "REAL"

let string_of_param p =
  sprintf "%s %s" (string_of_type (fst p)) (camlstring_of_coqstring (snd p))

let string_of_params ps =
  String.concat ", " (List.map string_of_param ps)

let string_of_function f =
  "#include \"iRRAM/lib.h\"\n" ^
  "#include \"iRRAM-lt.h\"\n\n" ^
  "using namespace iRRAM;\n\n" ^
  (string_of_type f.restype) ^ " " ^ (camlstring_of_coqstring f.name) ^ "(" ^
  (string_of_params f.params) ^
  ") {\n" ^
  (string_of_stmts ~indent:1 f.body) ^
  "}\n"

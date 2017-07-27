open Printf
open Ilog2_extraction
open IRRAM
open Extraction

let _ =
  match ilog2_iRRAM with
  | OK(f) -> print_string (string_of_function f)
  | Err(e) -> printf "// Err: %s" (camlstring_of_coqstring e)

From iRRAM.lang Require Import extraction ilog2.
Set Default Proof Using "Type".

Definition ilog2_iRRAM := to_iRRAM_function "ilog2" [iRRAM_REAL] iRRAM_Int ilog2.

Pwd.
Cd "ocaml/extraction".
Pwd.
Separate Extraction ilog2_iRRAM.
Pwd.
Cd "../..".
Pwd.

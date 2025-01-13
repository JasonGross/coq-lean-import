From LeanImport Require Import Lean.
Require Import ZArith. Set Printing All.

Open Scope Z_scope.
Check 5.
Print Z.
Check (Z.to_nat 5).
Print positive.
Set Printing Depth 100000000.
Check (0, 1, 2, 3, 4, 5, 6, 7, 8).
Lean Import "./hello.out".

Require Export init.
Require Import generic univ.

Ltac curryk const :=
  apply (curryKind (F Ty (F Ty Ty))); simpl; apply const.


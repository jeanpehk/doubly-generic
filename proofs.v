Set Implicit Arguments.

Require Export init.
Require Import univ utils.

(* A few example proofs with the universe. *)

(* Decoding constants in a closed env always correct. *)

Theorem natdeceq :
  decodeClosed (Con nil Nat) = nat.
Proof. unfold decodeClosed; unfold decodeType. reflexivity. Defined.

Theorem unitdeceq :
  decodeClosed (Con nil Unit) = unit.
Proof. unfold decodeClosed; unfold decodeType. reflexivity. Defined.

Theorem prdeceq :
  decodeClosed (Con nil Prod) = prod.
Proof. unfold decodeClosed; unfold decodeType. reflexivity. Defined.

Theorem smdeceq :
  decodeClosed (Con nil Sum) = sum.
Proof. unfold decodeClosed; unfold decodeType. reflexivity. Defined.


Require Export init.
Require Import univ examples.

(* simple proofs about self-defined generic types *)

Theorem sum_eq_teither (A B : Type)
  : sum A B = decodeClosed teither A B.
Proof.
  unfold decodeClosed; unfold decodeType; simpl.
  reflexivity.
Qed.

Definition optMaybe (A : Type) (o : option A) : decodeClosed tmaybe A :=
  match o with
  | Some x => inr x
  | None => inl tt
  end.

Definition maybeOpt (A : Type) (t : decodeClosed tmaybe A) : option A :=
  match t with
  | inl tt => None
  | inr x => Some x
  end.

Theorem opt_eq_tmaybe (A : Type) (o : option A)
  : maybeOpt (optMaybe o) = o.
Proof.
  destruct o as [sa |].
  - reflexivity.
  - reflexivity.
Qed.

Theorem tmaybe_eq_opt (A : Type) (m : decodeClosed tmaybe A)
  : optMaybe (maybeOpt m) = m.
Proof.
  destruct m as [sm |].
  - destruct sm; reflexivity.
  - reflexivity.
Qed.


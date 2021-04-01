From Coq Require Import Program.

Require Export init.
Require Import generic univ utils.

(* Example of a datatype-generic map. *)

(* type definition needed for gmap *)
Definition Map : vec Type 2 -> Type :=
  fun vs => vhd vs -> vhd (vtl vs).

(* helper for defining sums *)
Definition doSum (A1 B1 : Type)
  : (A1 -> B1) -> forall (A2 B2 : Type), (A2 -> B2) -> (A1 + A2) -> (B1 + B2) :=
  fun f =>
    fun _ _ g sa =>
      match sa with
      | inl a => inl (f a)
      | inr b => inr (g b)
      end.

(* helper for defining prods *)
Definition doProd (A1 B1 : Type)
  : (A1 -> B1) -> forall (A2 B2 : Type), (A2 -> B2) -> (A1 * A2) -> (B1 * B2) :=
  fun f _ _ g sa => (f (fst sa), g (snd sa)).

Definition mapConst : tyConstEnv Map :=
  fun k c =>
    match c in const k
    return kit k Map (repeat (decodeClosed (Con c)))
    with
    | Nat => fun n => n
    | Unit => fun _ => tt
    | Prod => @doProd
    | Sum => @doSum
    end.

Program Definition mConst : NGen Map :=
  nGen
  (fun tt => tt)
  (fun n => n)
  (@doSum)
  (@doProd).

Definition gmap (k : kind) (t : ty k) : kit k Map (repeat (decodeClosed t)) :=
  ngen _ mConst.


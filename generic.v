Set Implicit Arguments.

Require Import univ utils.

Require Import Nat.

(* Generic Library *)

(** Still mostly just playing around, this is basically a combination of ideas
  from 'Arity-Generic Datatype-Generic Programming' and
  'Polytypic Programming in Coq'. **)

Record PolyType (n : nat) : Type := polyType {
typeKindStar : nary_fn n Set Set
}.

(****** Type specialization ******)

(** "The type of a generic function instance from four pieces of information:
    - the arity of the operation, given with an implicit argument n
    - a function b to construct the type in the base case
    - the kind k itself
    - a vector v of n Coq types, each of kind k" *)

(* so b is literally the way to construct the type of the operation
      e.g. Map : vec Set 2 -> Set
      Map (A :: B :: []) = A -> B *)
Fixpoint kit (n : nat) (k : kind) (b : vec Set n -> Set)
  : vec (decodeKind k) n -> Set :=
    match k return vec (decodeKind k) n -> Set with
    | Ty => fun vs => b vs
    | F k1 k2 => fun vs => quantify (fun As => kit k1 b As ->
                                               kit k2 b (zap vs As))
    end.

(* kit (kind-indexed type) for tuples *)
Fixpoint kit' (n : nat) (k : kind) (pt : PolyType n)
  : tupleT (decodeKind k) n -> decodeKind Ty :=
    match k return tupleT (decodeKind k) n -> decodeKind Ty with
    | Ty => uncurry _ _ _ (typeKindStar pt)
    | F k1 k2 => fun tup => quantifyT _ _ (fun As => kit' k1 pt As ->
                                                kit' k2 pt (zapT _ _ _ tup As))
    end.

(* some map examples: *)
Definition Map : vec Set 2 -> Set :=
  fun vs => vhd vs -> vhd (vtl vs).

Definition MapT : PolyType 2 :=
  polyType 2 (fun A B => A -> B).

Definition vect (A B : Set) := vcons A (vcons B (vnil _)).
Definition tupt := (unit, (nat, tt)).

Compute kit Ty Map (vect nat unit). (* = nat -> unit *)
Compute kit' Ty MapT tupt. (* = unit -> nat *)

(* type for mapping constants to a value *)
Definition tyConstEnv (n : nat) (b : vec Set (S n) -> Set) : Set :=
  forall (k:kind) (c:const k), kit k b (repeat _ (decodeClosed _ (Con _ _ c))).

(* helper for mapConst *)
Definition doSum (A1 B1 : Set)
  : (A1 -> B1) -> forall (A2 B2 : Set), (A2 -> B2) -> (A1 + A2) -> (B1 + B2) :=
  fun f =>
    fun _ _ g sa =>
      match sa with
      | inl a => inl (f a)
      | inr b => inr (g b)
      end.

(* helper for mapConst *)
Definition doProd (A1 B1 : Set)
  : (A1 -> B1) -> forall (A2 B2 : Set), (A2 -> B2) -> (A1 * A2) -> (B1 * B2) :=
  fun f _ _ g sa => (f (fst sa), g (snd sa)).

(* Example of building a function for mapping constants to a value. *)
Definition mapConst : tyConstEnv Map :=
  fun k c =>
    match c in const k return kit _ Map (repeat _ (decodeClosed _ (Con _ _ c))) with
    | Nat => fun n => n
    | Unit => fun _ => tt
    | Prod => doProd
    | Sum => doSum
    end.

(* examples of using mapConst *)
Compute mapConst Prod unit bool (fun _ => true) nat nat (fun b => b + 1) (tt,2).
Compute mapConst Sum _ _ (fun _ => true)
                     _ _ (fun n => if eqb n 1 then true else false) (inr 2).

(* Now what is left is term specialization and then done for type-genericity *)

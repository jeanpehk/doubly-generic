Set Implicit Arguments.

(* Utilities *)

(* A1 -> .. -> An -> B *)
Fixpoint nary_fn (n : nat) (A B : Type) :=
  match n with
  | O => B
  | S n' => A -> nary_fn n' A B
  end.

(*** Vectors ***)

Inductive vec (A : Type) : nat -> Type :=
  | vnil : vec A O
  | vcons : forall n, A -> vec A n -> vec A (S n).

(* tail *)
Definition vtl (A : Type) (n : nat) (v : vec A (S n)) : vec A n :=
  match v with
  | vcons _ tl' => tl'
  end.

(* head *)
Definition vhd (A : Type) (n : nat) (v : vec A (S n)) : A :=
  match v with
  | vcons a _ => a
  end.

(* quantify a vector *)
Fixpoint quantify (A : Type) (n : nat)
  : (vec A n -> Set) -> Set :=
    match n return (vec A n -> Set) -> Set with
    | O => fun f => f (vnil _)
    | S n' => fun f => forall a : A,
                quantify (fun As => f (vcons a As))
    end.
 
(* curry for arity-genericiry *)
Fixpoint curry (A : Type) (n : nat)
  : forall (G : vec A n -> Set), (forall X : vec A n, G X) -> quantify G :=
    match n return forall (G : vec A n -> Set),
    (forall X : vec A n, G X) -> quantify G with
    | O => fun _ f => f (vnil _)
    | S n' => fun _ f => (fun (a:A) =>
                curry _ (fun As => f (vcons a As)))
    end.
 
Set Asymmetric Patterns.

(* ADMITTED *)
Definition uncurry (n : nat) (A : Type) (G : vec A n -> Set)
  : quantify G -> (forall (va : vec A n), G va).
  Admitted.

(*
(* uncurry for arity-genericity *)
Fixpoint uncurry (n : nat) (A : Set) (G : vec A n -> Set) (va : vec A n)
  : forall (G : vec A n -> Set), quantify G -> (forall (va : vec A n), G va) :=
  match n return forall (G : vec A n -> Set), quantify G ->
    (forall (va : vec A n), G va) with
  | O => fun G f va => match va in vec _ O return G va with
    | vnil => f
    end
  | S n' => fun G f va => match va in vec _ (S n') return G va with
    | vcons p a As  => uncurry _ (f a) As
    end
  end.
  *)
  
(* uncurry a vector *)
Fixpoint uncurryV (A B : Type) (n : nat) : nary_fn n A B -> vec A n -> B :=
match n return nary_fn n A B -> vec A n -> B with
| O => fun x _ => x
| S n' => fun f t => uncurryV _ (f (vhd t)) (vtl t)
end.
Unset Asymmetric Patterns.

(* apply a vector of functions to a vector *)
Fixpoint zap (A B : Type) (n : nat) (vf : vec (A -> B) n)
  : vec A n -> vec B n :=
  match vf in vec _ n return vec _ n -> vec _ n with
  | vnil _ => fun _ => vnil _
  | vcons f vf' => fun m =>
                            vcons (f (vhd m)) (zap vf' (vtl m))
  end.

(* construct a vector with n elements of a:A *)
Fixpoint repeat (n : nat) (A : Type) (a : A) : vec A n :=
  match n with
  | O => vnil _
  | S n' => vcons a (repeat _ a)
  end.

(*** Tuples ***)

Fixpoint tupleT (A : Type) (n : nat) : Type :=
  match n with
  | O => unit
  | S n' => A * tupleT A n'
  end.

Fixpoint gtupleT (A : Set) (n : nat) (f : A -> Type) :
  tupleT A n -> Type :=
  match n return tupleT A n -> Type with
  | O => fun tup => unit
  | S n' => fun tup =>
              let (a, b) := tup in (f a * gtupleT n' f b)%type
  end.

(* tail *)
Definition tupletl (A : Type) (n : nat) (t : tupleT A (S n)) : tupleT A n :=
  match t with
  | (_, r) => r
  end.

(* head *)
Definition tuplehd (A : Type) (n : nat) (t : tupleT A (S n)) : A :=
  match t with
  | (a, _) => a
  end.

(* apply a tuple of functions to a tuple *)
Fixpoint zapT (A B : Type) (n : nat)
  : tupleT (A -> B) n -> tupleT A n -> tupleT B n :=
  match n return tupleT (A -> B) n -> tupleT A n -> tupleT B n with
  | O => fun f As => tt
  | S n' => fun f As => ((tuplehd f) (tuplehd As),
        zapT _ _ _ (tupletl f) (tupletl As))
  end.

(* uncurry a tuple *)
Fixpoint uncurryT (A B : Type) (n : nat) : nary_fn n A B -> tupleT A n -> B :=
match n return nary_fn n A B -> tupleT A n -> B with
| O => fun x _ => x
| S n' => fun f t => let (x, y) := t in uncurryT _ _ n' (f x) y
end.

(* curry a tuple *)
Fixpoint quantifyT (A : Type) (n : nat)
  : (tupleT A n -> Set) -> Set :=
    match n return (tupleT A n -> Set) -> Set with
    | O => fun f => f tt
    | S n' => fun f => forall a : A,
                quantifyT A n' (fun As => f (a, As))
    end.


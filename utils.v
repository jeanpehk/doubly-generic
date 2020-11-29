From Coq Require Import Program List.
Set Universe Polymorphism.

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

(* induction scheme for vectors, taken from coq stdlib *)
Definition rectS {A} (P : forall {n}, vec A (S n) -> Type)
  (bas : forall a : A, P (vcons a (vnil _)))
  (rect: forall a {n} (v : vec A (S n)), P v -> P (vcons a v)) :=
  fix rectS_fix {n} (v : vec A (S n)) : P v :=
  match v with
  |@vcons _ 0 a v =>
      match v with
      | vnil _ => bas a
      | _ => fun devil => False_ind (@IDProp) devil
      end
  |@vcons _ (S nn') a v => rect a v (rectS_fix v)
  |_ => fun devil => False_ind (@IDProp) devil
  end.

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
  : (vec A n -> Type) -> Type :=
    match n return (vec A n -> Type) -> Type with
    | O => fun f => f (vnil _)
    | S n' => fun f => forall a : A,
                quantify (fun As => f (vcons a As))
    end.
 
(* curry for arity-genericity *)
Fixpoint curry (A : Type) (n : nat)
  : forall (G : vec A n -> Type), (forall X : vec A n, G X) -> quantify G :=
    match n return forall (G : vec A n -> Type),
    (forall X : vec A n, G X) -> quantify G with
    | O => fun _ f => f (vnil _)
    | S n' => fun _ f => (fun (a:A) =>
                curry _ (fun As => f (vcons a As)))
    end.

Definition vec_nil_case {A : Type} (v : vec A 0) : v = vnil A :=
  match v with (vnil _) => eq_refl end.

Definition veq_hdtl {A : Type} {n : nat} (v : vec A (S n)) :
  v = vcons (vhd v) (vtl v).
Proof.
  apply rectS with (v := v).
  - intros. simpl. reflexivity.
  - intros. simpl. reflexivity.
Defined.

Lemma vec_cons_case {A : Type} {n : nat} (v : vec A (S n)) :
  {x : A & {u : vec A n | v = vcons x u}}.
Proof.
  apply existT with (x:=vhd v).
  apply exist with (x:=vtl v).
  apply veq_hdtl.
Defined.

Fixpoint uncurry' (n : nat) (A : Type) {struct n}
  : forall (G : vec A n -> Type), quantify G -> forall (va : vec A n), G va.
Proof.
  intros G f va. induction n as [| n' IH].
  - hnf in f. pose proof vec_nil_case va as H. rewrite H. exact f.
  - hnf in f.
    pose proof vec_cons_case va as H. destruct H as [a [As H]].
    rewrite H. exact (uncurry' _ _ _ (f a) As). Defined.

(* uncurry a vector *)
Fixpoint uncurryV (A B : Type) (n : nat) : nary_fn n A B -> vec A n -> B :=
  match n return nary_fn n A B -> vec A n -> B with
  | O => fun x _ => x
  | S n' => fun f t => uncurryV _ (f (vhd t)) (vtl t)
  end.

(* apply a vector of functions to a vector *)
Fixpoint zap (A B : Type) (n : nat) (vf : vec (A -> B) n)
  : vec A n -> vec B n :=
  match vf in vec _ n return vec _ n -> vec _ n with
  | vnil _ => fun _ => vnil _
  | vcons f vf' => fun m => vcons (f (vhd m)) (zap vf' (vtl m))
  end.

Fixpoint zaps (A B : Set) (n : nat) (vf : vec (A -> B) n)
  : vec A n -> vec B n :=
  match vf in vec _ n return vec _ n -> vec _ n with
  | vnil _ => fun _ => vnil _
  | vcons f vf' => fun m => vcons (f (vhd m)) (zap vf' (vtl m))
  end.

(* construct a vector with n elements of a:A *)
Fixpoint repeat (n : nat) (A : Type) (a : A) : vec A n :=
  match n with
  | O => vnil _
  | S n' => vcons a (repeat _ a)
  end.

Fixpoint repeats (n : nat) (A : Set) (a : A) : vec A n :=
  match n with
  | O => vnil _
  | S n' => vcons a (repeat _ a)
  end.


Set Universe Polymorphism.

(* A Simple arity-generic map ala Fridlender + Indrika / Weirich + Casinghino *)

(* https://dl.acm.org/doi/pdf/10.1145/1707790.1707799 <- W + C *)
(* https://www.brics.dk/RS/01/10/BRICS-RS-01-10.pdf <- F + I *)

Inductive vec (A : Type) : nat -> Type :=
  | vnil : vec A O
  | vcons : forall n, A -> vec A n -> vec A (S n).

Fixpoint repeat (n : nat) (A : Type) (a : A) : vec A n :=
  match n with
  | O => vnil _
  | S n' => vcons _ _ a (repeat _ _ a)
  end.

Definition hd (n : nat) (A : Type) (v : vec A (S n)) : A :=
  match v with
  | vcons _ _ a _ => a
  end.

Definition tl (n : nat) (A : Type) (v : vec A (S n)) : vec A n :=
  match v with
  | vcons _ _ _ v' => v'
  end.

Fixpoint zap (n : nat) (A B : Type) (vf : vec (A -> B) n) :
  vec A n -> vec B n :=
  match vf in vec _ n return vec _ n -> vec _ n with
  | vnil _ => fun _ => vnil _
  | vcons _ _ f vf' => fun va =>
                      vcons _ _ (f (hd _ _ va)) (zap _ _ _ vf' (tl _ _ va))
  end.

(* example maps using repeat and zap: *)
Definition map0 (m : nat) (A : Type) (a : A): vec A m := repeat _ _  a.
Definition map1 (m : nat) (A B : Type) (f : A -> B) (va : vec A m) : vec B m :=
  zap _ _ _ (repeat _ _ f) va.
Definition map2 (m : nat) (A B C : Type) (f : A -> B -> C) (va : vec A m) (vb : vec B m)
  : vec C m :=
  zap _ _ _ (zap _ _ _ (repeat _ _ f) va) vb.

Definition vint1 := vcons _ _ 1 (vcons _ _ 2 (vcons _ _ 3 (vnil _))).
Compute vint1.
Definition vint2 := vcons _ _ 10 (vcons _ _ 9 (vcons _ _ 8 (vnil _))).
Compute vint2.

Compute map2 _ _ _ _ (fun a b => a + b) (vint1) (vint2). (* -> 2 :: 11 *)

(* function for generating function types for maps *)
Fixpoint arrTy (n : nat) (v : vec Type (S n)) : Type :=
  match v with
  | vcons _ O x _ => x
  | vcons _ (S n') x v' => x -> (arrTy _ v')
  end.

(* This is allowed because of universe polymoprhism.                 *)
(* Otherwise the following error msg:                                *)

(* The term "vcons Set 1 nat (vcons Set 0 unit (vnil Set))" has type *)
(* "vec Set 2" while it is expected to have type "vec Type 2"        *)
(*   (universe inconsistency).                                       *)
Compute arrTy 1 (vcons _ _ nat (vcons _ _ unit (vnil _))). (* = nat -> unit *)

Definition arrTyVec (m n : nat) (vs : vec Type (S n)) : Type :=
  arrTy _ (zap _ _ _ (repeat _ _ (fun A => vec A m)) vs).

(* = vec nat _ -> vec unit _*)
Compute arrTyVec _ _ (vcons _ _ nat (vcons _ _ unit (vnil _))).

(* Helper function for nvecmap *)
Fixpoint g (n m : nat) (ts : vec Type (S n)) :
  vec (arrTy _ ts) m -> arrTyVec m _ ts :=
  match ts in vec _ (S n) return vec (arrTy _ ts) m -> arrTyVec m _ ts with
  | vcons _ O _ _ => fun f => f
  | vcons _ (S n') x ts' => fun f =>
                              fun a => g _ _ ts' (zap _ _ _ f a)
  end.

(* Construct the return term without currying, e.g. (rt : vec nat -> vec unit) *)
Definition nvecmap (m n : nat) (ts : vec Type (S n)) (f : arrTy n ts) :
  arrTyVec m n ts :=
  g _ _ ts (repeat _ _ f).

Definition types := vcons _ _ nat (vcons _ _ unit (vcons _ _ nat (vnil _))).
Check types. (* : vec Set 3 *)
Definition f : nat -> unit -> nat := fun n t => n + 1.

Definition ret := nvecmap 2 _ types f.
Check ret. (* : arrTyVec 2 2 types *)

Definition natv := vcons _ _ 2 (vcons _ _ 55 (vnil _)).
Definition unitv := vcons _ _ tt (vcons _ _ tt (vnil _)).

(* A simple example map with previous definitions.              *)
(* Still need to unnecessarily provide vector of types (types)  *)
(* and individual vectors (natv + unitv), but atleast it works. *)
Definition examplemap := (nvecmap _ 2 types f) natv unitv.

Compute examplemap.
Compute hd _ _ examplemap.          (* -> 3  *)
Compute hd _ _ (tl _ _ examplemap). (* -> 56 *)


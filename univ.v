From Coq Require Import List Program.

Set Implicit Arguments.
Set Asymmetric Patterns.

(* Set Universe Polymorphism.
Set Universe Minimization ToSet. *)

(* Universe definition. *)

Inductive kind : Set :=
  | Ty : kind
  | F  : kind -> kind -> kind.

(* From 'own' kinds to Coq kinds. *)
Fixpoint decodeKind (k : kind) : Type :=
  match k with
  | Ty => Set
  | F k1 k2 => decodeKind k1 -> decodeKind k2
  end.

(* Constants that are indexed by kinds. *)
Inductive const : kind -> Set :=
  | Nat : const Ty
  | Unit : const Ty
  | Sum : const (F Ty (F Ty Ty))
  | Prod : const (F Ty (F Ty Ty)).

(* Decode kind of constant to a Coq kind. *)
Fixpoint decodeConst (k : kind) (c : const k) : decodeKind k :=
  match c in const k return decodeKind k with
  | Nat => nat
  | Unit => unit
  | Sum => sum
  | Prod => prod
  end.

(* 'Datatype-generic operations are described by kind-indexed types.'     *)
(* 'They have different types according to the kinds of their arguments.' *)

(* 'We start with a code for types, give an interpretation of that     *)
(*  code as an Agda type and then define the generic operation by      *)
(*  interpreting that code as an Agda function (like geq).'            *)

(* Context for kinds. *)
Definition ctx : Type := list kind.

(* Variables *)
Inductive tyvar : ctx -> kind -> Type :=
  | Vz : forall G k, tyvar (k :: G) k
  | Vs : forall G k k', tyvar G k -> tyvar (k' :: G) k.

Import EqNotations.

Lemma tvcase :
  forall G k k' (P : tyvar (k' :: G) k -> Type),
  (*(forall (pf : k=k'), P (eq_vs (Vz G k) pf)) ->*)
  (forall (pf : k=k'), P (rew [fun x:kind => tyvar (x :: G) k] pf in Vz G k)) ->
  (forall x, P (Vs _ x)) ->
  forall x, P x.
  Proof.
    intros.
    refine
    (match x as x' in tyvar (k0 :: G0) k1
    return forall (pk' : k0 = k') (pk : k1 = k) (pg : G0 = G),
    rew [fun x : kind => tyvar (x :: _) k] pk' in
    rew [fun x' : kind => tyvar (_ :: _) x'] pk in
    rew [fun g : ctx => tyvar (_ :: g) _] pg in
    x' = x
    -> P x
    with
    | Vz _ _ => _
    | Vs _ _ _ _ => _
    end eq_refl eq_refl eq_refl eq_refl).
    - intros. subst. apply X.
    - intros. subst. simpl. apply (X0 t).
  Defined.

(* Datatype for representing types of arbitrary kinds.    *)
(* Indexed by the typing context and the kind of the type. *)
Inductive typ : ctx -> kind -> Type :=
  | Var : forall G k, tyvar G k -> typ G k
  | Lam : forall G k1 k2, typ (k1 :: G) k2 -> typ G (F k1 k2)
  | App : forall G k1 k2, typ G (F k1 k2) -> typ G k1 -> typ G k2
  | Con : forall G k, const k -> typ G k.

(* Type in an empty context *)
Definition ty : kind -> Type :=
  typ nil.

(* Now we can represent type constructors,            *)
(* what we need is a way to decode them as Coq types. *)

(* Environment for kinds. *)
(* If  '.. -> Set' then 'Large non-prop ind types must be in Type' *)
Inductive env : list kind -> Type :=
  | enil : env nil
  | econs : forall k G, decodeKind k -> env G -> env (k :: G).

Definition envtl (k : kind) (G : ctx) (en : env (k :: G)) : env G :=
  match en with
  | econs _ _ _ G' => G'
  end.

Theorem slookup' : forall (k : kind) (G : ctx) (tv : tyvar G k) (e : env G),
  decodeKind k.
Proof.
  intros. induction tv.
  - inversion e. apply X.
  - inversion e. exact (IHtv X0).
Defined.

(* lookup a type from env *)
Fixpoint slookup (k : kind) (G : ctx) (tv : tyvar G k) : env G -> decodeKind k :=
  match tv in tyvar G k return env G -> decodeKind k with
  | Vz _ _ => fun env =>
                 match env in env G with
                 | econs _ _ v G => v
                 end
  | Vs _ _ _ x => fun env => slookup x (envtl env)
  end.

(* hmm if you do '.. : typ G k -> env G ..' instead      *)
(* doesn't understand that the function terminates       *)
Fixpoint decodeType (k : kind) (G : ctx) (t : typ G k) : env G -> decodeKind k := 
  match t in typ G k return env G -> decodeKind k with
  | Var _ _ x => fun e =>
                   slookup x e
  | Lam _ _ _ t1 => fun e =>
                      fun y => decodeType t1 (econs _ y e)
  | App _ _ _ t1 t2 => fun e =>
                         (decodeType t1 e) (decodeType t2 e)
  | Con _ _ c => fun e =>
                   decodeConst c
  end.

(* decode a closed type *)
Definition decodeClosed (k : kind)
  : ty k -> decodeKind k :=
  fun t => decodeType t enil.

(********* Examples: *********)

(* Shorthands for constants *)
Definition tnat := Con nil Nat.
Definition tunit := Con nil Unit.
Definition tsum := Con nil Sum.
Definition tprod := Con nil Prod.

(* Shorthands for constants in a context *)
Definition tnatc := fun ctx => Con ctx Nat.
Definition tunitc := fun ctx => Con ctx Unit.
Definition tsumc := fun ctx => Con ctx Sum.
Definition tprodc := fun ctx => Con ctx Prod.

(* Shorthands for other types *)
Definition tmaybe : ty (F Ty Ty) :=
  Lam (App (App (tsumc _) (tunitc _)) (Var (Vz _ _))).
(* \a -> \b -> (sum a) b *)
Definition teither : ty (F Ty (F Ty Ty)) :=
  Lam (Lam
    (App (App (tsumc _)
      (Var (Vs _ (Vz _ _)))) (Var (Vz _ _)))).

(* Shorthands for decoding closed types *)
Definition deNat := decodeClosed (Con _ Nat).
Definition deUnit := decodeClosed (Con _ Unit).
Definition deMaybe (A : Set) := decodeClosed tmaybe A.
Definition deEither (A B : Set) := decodeClosed teither A B.

(* Compute examples *)
Compute deNat. (* = nat *)
Compute deUnit. (* = unit *)
Compute deMaybe. (* = fun A : Set => (unit + A) *)
Compute deMaybe nat. (* = (unit + nat) *)
Compute deEither. (* = fun A B : Set => (A + B) *)
Compute deEither nat unit. (* = (nat + unit) *)

Compute decodeClosed (Con _ Nat).

(* Initial thougths for next phase: *)

(** decodeType is a function and cannot be used in function definitions.
   What is needed is a type level function that constructs the type of decodeType,
   aka specType. I guess decodeKind is already the type of this function?
   | specType : decodeKind |
   | specTerm : specType |
     => specType -> decodeKind **)


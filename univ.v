From Coq Require Import List.

Require Export init.

Import EqNotations.

(* Universe definition. *)

Inductive kind : Type :=
  | Ty : kind
  | F  : kind -> kind -> kind.

Fixpoint decodeKind (k : kind) : Type :=
  match k with
  | Ty => Type
  | F k1 k2 => decodeKind k1 -> decodeKind k2
  end.

(* Constants that are indexed by kinds. *)
Inductive const : kind -> Type :=
  | Nat : const Ty
  | Unit : const Ty
  | Sum : const (F Ty (F Ty Ty))
  | Prod : const (F Ty (F Ty Ty)).

Fixpoint decodeConst (k : kind) (c : const k) : decodeKind k :=
  match c in const k return decodeKind k with
  | Nat => nat
  | Unit => unit
  | Sum => sum
  | Prod => prod
  end.

(* Context for kinds. *)
Definition ctx : Type := list kind.

(* type variables *)
Inductive tyvar : ctx -> kind -> Type :=
  | Vz : forall G k, tyvar (k :: G) k
  | Vs : forall G k k', tyvar G k -> tyvar (k' :: G) k.

(* case for dependent destruction on tyvar,
   needed for proof of 'nlookup' in generic.v *)
Lemma tvcase :
  forall G k k' (P : tyvar (k' :: G) k -> Type),
  (forall (pf : k=k'), P (rew [fun x:kind => tyvar (x :: G) k] pf in Vz)) ->
  (forall x, P (Vs x)) ->
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
    | Vz => _
    | Vs _ => _
    end eq_refl eq_refl eq_refl eq_refl).
    - intros. subst. apply X.
    - intros. subst. simpl. apply (X0 t).
  Defined.

(* Datatype for representing types. *)
Inductive typ : ctx -> kind -> Type :=
  | Var : forall G k, tyvar G k -> typ G k
  | Lam : forall G k1 k2, typ (k1 :: G) k2 -> typ G (F k1 k2)
  | App : forall G k1 k2, typ G (F k1 k2) -> typ G k1 -> typ G k2
  | Con : forall G k, const k -> typ G k.

(* Type in an empty context *)
Definition ty : kind -> Type :=
  typ nil.

(* Environment for kinds. *)
Inductive env : list kind -> Type :=
  | enil : env nil
  | econs : forall k G, decodeKind k -> env G -> env (k :: G).

Definition envtl (k : kind) (G : ctx) (en : env (k :: G)) : env G :=
  match en with
  | econs _ G' => G'
  end.

(* lookup a type from env *)
Fixpoint slookup (k : kind) (G : ctx) (tv : tyvar G k) : env G -> decodeKind k :=
  match tv in tyvar G k return env G -> decodeKind k with
  | Vz => fun env =>
                 match env in env G with
                 | econs v G => v
                 end
  | Vs x => fun env => slookup x (envtl env)
  end.

Fixpoint decodeType (k : kind) (G : ctx) (t : typ G k) : env G -> decodeKind k := 
  match t in typ G k return env G -> decodeKind k with
  | Var x => fun e =>
                   slookup x e
  | Lam t1 => fun e =>
                      fun y => decodeType t1 (econs y e)
  | App t1 t2 => fun e =>
                         (decodeType t1 e) (decodeType t2 e)
  | Con c => fun e =>
                   decodeConst c
  end.

(* decode a closed type *)
Definition decodeClosed (k : kind)
  : ty k -> decodeKind k :=
  fun t => decodeType t enil.


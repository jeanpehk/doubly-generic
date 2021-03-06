From Coq Require Import Program List Datatypes.
Import ListNotations.

Require Export init.
Require Import univ utils.

(* Generic Library *)

(* Most of the type signatures and the general structure of the library from
    Weirich + Casinghino
    - https://dl.acm.org/doi/pdf/10.1145/1707790.1707799
    Which itself is largely based on the generic library by Verbruggen et al.:
    - https://dl.acm.org/doi/pdf/10.1145/1411318.1411326 *)

(* Main differences are in the usage of universepolymorfism
   and in the curiosities of Coq with regards to getting the definitions
   to actually typecheck. *)

(****** Type level definitions ******)
Section types.

(* A kind-indexed type.
   Needed for specializing types. *)
Fixpoint kit (n : nat) (k : kind) (b : vec Type (S n) -> Type)
  : vec (decodeKind k) (S n) -> Type :=
    match k return vec (decodeKind k) (S n) -> Type with
    | Ty => fun vs => b vs
    | F k1 k2 => fun vs => quantify (fun As => kit k1 b As ->
                                               kit k2 b (zap vs As))
    end.

(* version of kit with arguments curried for easier proofs. *)
Fixpoint unkit (n : nat) (k : kind) (b : vec Type (S n) -> Type)
  : vec (decodeKind k) (S n) -> Type :=
    match k return vec (decodeKind k) (S n) -> Type with
    | Ty => fun vs => b vs
    | F k1 k2 => fun vs =>
        forall a,
        kit k1 b a ->
        unkit k2 b (zap vs a)
    end.

(* Type for mapping constants to a value.
   Needed for the type signature of ngen. *)
Definition tyConstEnv (n : nat) (b : vec Type (S n) -> Type) : Type :=
  forall k c, kit k b (repeat (decodeClosed (Con _ c))).

End types.

(****** Term specialization ******)
Section terms.

  (* env of terms of kind-indexed types
     Needed for constructing specialized terms. *)
  Inductive stenv (n : nat) (b : vec Type (S n) -> Type) : ctx -> Type :=
    | nnil : stenv b nil
    | ncons : forall {k} {G} (a : vec (decodeKind k) (S n)),
        kit k b a -> stenv b G -> stenv b (cons k G).

  (* interpret a generic type + vector of envs to a vec of types *)
  Definition interpToVec (G : ctx) (k : kind) (n : nat)
    : typ G k -> vec (env G) n -> vec (decodeKind k) n :=
    fun t vs =>
      zap (repeat (decodeType t)) vs.

  (* if two types are equal then kit t1 implies kit t2 *)
  Definition eqkit : forall (n : nat) (k : kind) (b : vec Type (S n) -> Type)
    (t1 t2 : vec (decodeKind k) (S n)),
    t1 = t2 -> kit k b t1 -> kit k b t2.
  Proof.
    intros. induction H; assumption.
  Defined.

  (* turn an stenv to a vector of envs *)
  (* use '@' to provide implicits explicitly *)
  Fixpoint transpose {n : nat} {b : vec Type (S n) -> Type}
    {G : ctx} (ste : stenv b G)
    : vec (env G) (S n) :=
      match ste with
      | nnil => repeat enil
      | ncons a _ ste => zap (zap (repeat (@econs _ _)) a) (transpose ste)
      end.

  (* currykinds for occasionally easier proofs. *)
  Program Fixpoint curryKind (k : kind) (n : nat) (b : vec Type (S n) -> Type)
    : forall v : vec (decodeKind k) (S n),
    unkit k b v -> kit k b v :=
    match k
    return forall v : vec (decodeKind k) (S n),
    unkit k b v -> kit k b v
    with
    | Ty => _
    | F k1 k2 => fun v vs =>
        curry (fun (x:vec (decodeKind k1) _) =>
              kit k1 b x ->
              kit k2 b (zap v x))
              (fun As y => curryKind k2 _ (zap v As) (vs As y))
    end.

  (* PROOFS to help with term specialization,
     type signatures from definitions by Weirich + Casinghino. *)

  (* six lemmas for typechecking different cases of generic types in ngen  *)

  Lemma c6 : forall (n : nat) (A B : Type) (f : A -> B) (x : A),
    zap (repeat (n:=n) f) (repeat x) = repeat (f x).
  Proof.
    intros n A B f x. induction n.
    - simpl. reflexivity.
    - simpl. rewrite IHn. reflexivity.
  Defined.

  Lemma caseCon : forall (n : nat) (k : kind) (G : ctx) (c : const k)
    (envs : vec (env G) n),
      repeat (decodeClosed (Con _ c)) = interpToVec (Con _ c) envs.
  Proof.
    intros n k G c envs. induction envs.
    - simpl. destruct G.
      + simpl. reflexivity.
      + simpl. reflexivity.
    - simpl. rewrite IHenvs. destruct G.
      + simpl. reflexivity.
      + simpl. reflexivity.
  Defined.

  Lemma caseApp : forall (n : nat) (k1 k2 : kind) (G : ctx)
    (t1 : typ G (F k1 k2))
    (t2 : typ G k1)
    (envs : vec (env G) n),
    zap (interpToVec t1 envs) (interpToVec t2 envs) = interpToVec (App t1 t2) envs.
  Proof.
    intros n k1 k2 G t1 t2 envs. generalize dependent G.
    induction envs.
    - destruct G.
      + simpl. reflexivity.
      + simpl. reflexivity.
    -  destruct a.
      + simpl. apply veq_add. apply IHenvs.
      + simpl. apply veq_add. apply IHenvs.
  Defined.

  Lemma caseLam : forall (n : nat) (k k' : kind) (G : ctx)
    (t : typ (cons k' G) k) (envs : vec (env G) n) (As : vec (decodeKind k') n),
    interpToVec t (zap (zap (repeat (@econs k' G)) As) envs)
    = zap (interpToVec (Lam t) envs) As.
  Proof.
    intros. destruct n.
    - induction envs eqn:An.
      + simpl. destruct G.
        * simpl. reflexivity.
        * simpl. reflexivity.
      + destruct G.
        * apply veq_add. simpl in IHv. apply IHv with (envs := v). reflexivity.
        * apply veq_add. simpl. simpl in IHv. apply IHv with (envs := v).
          reflexivity.
    - induction envs.
      + simpl. destruct G.
        * simpl. reflexivity.
        * simpl. reflexivity.
      + destruct G.
        * apply veq_add. apply IHenvs.
        * apply veq_add. apply IHenvs.
  Defined.

  Lemma caseVar : forall (n : nat) (k k' : kind) (G : ctx)
    (x : tyvar G k') (t1 : vec (decodeKind k) n) (envs : vec (env G) n),
    interpToVec (Var x) envs
    = interpToVec (Var (Vs _ x)) (zap (zap (repeat (@econs _ _)) t1) envs).
  Proof.
    intros. induction envs.
    - simpl. destruct G.
      + simpl. reflexivity.
      + simpl. reflexivity.
    - simpl. destruct G.
      + apply veq_add. apply IHenvs.
      + apply veq_add. apply IHenvs.
  Defined.

  Lemma caseVz : forall (n : nat) (k : kind) (G : ctx)
    (a : vec (decodeKind k) n) (envs : vec (env G) n),
    a = interpToVec (Var (Vz _ _)) (zap (zap (repeat (@econs _ _)) a) envs).
  Proof.
    intros. induction a.
    - simpl. reflexivity.
    - apply veq_add. apply IHa.
  Defined.

  (** Lookup a type for var from stenv.
      Requires a self defined lemma 'tvcase' for destructing v.
      Done following the idea presented by James Wilcox in:
      - https://jamesrwilcox.com/dep-destruct.html               **)
  Fixpoint nlookup (n : nat) (k : kind) (b : vec Type (S n) -> Type) (G : ctx)
    (v : tyvar G k) (ste : stenv b G) :
    kit k b (interpToVec (Var v) (transpose ste)).
  Proof.
    destruct ste.
    - inversion v.
    - pattern v; apply tvcase; clear v; intros.
      + subst. apply eqkit with (t1:=a).
        * pose proof (caseVz _ (a:=a) (transpose ste)) as ch. simpl in ch; simpl.
          rewrite <- ch; reflexivity.
        * assumption.
      + pose proof (caseVar _ x a (transpose ste)) as ch.
        apply eqkit with (b0:=b) in ch.
        * apply ch.
        * apply nlookup.
  Defined.

  Hint Resolve eqkit transpose c6 : core.

  (* term specialization with non-empty context *)
  (* - pretty unreadable.. ways to better automate or simplify logic? *)
  Fixpoint ngen' (n : nat) (b : vec Type (S n) -> Type)
    (G : ctx) (k : kind) (t : typ G k)
    : forall (ve : stenv b G) (ce : tyConstEnv b),
    kit k b (interpToVec t (transpose ve)) :=
    match t in typ G k
    return forall ve ce,
    kit k b (interpToVec t (transpose ve)) with
    | Var x => fun ve ce => nlookup x ve
    | Lam t1 => fun ve ce => curry _ (fun a nwt =>
                  eqkit _ _ (caseLam t1 ltac:(auto) a)
                  (ngen' t1 (ncons a nwt ve) ce))
    | @App _ _ k2 t1 t2 => fun ve ce =>
        eqkit _ _ (caseApp t1 t2 ltac:(auto))
        (uncurry' (fun a => (forall _,
                       (kit k2 b (zap (interpToVec t1 ltac:(auto)) a))))
        (ngen' t1 ve ce)
        (interpToVec t2 ltac:(auto)) (ngen' t2 ve ce))
    | Con _ c => fun ve ce => eqkit _ _ (caseCon c ltac:(auto)) (ce _ c)
    end.

  (* term specialization in an empty context. *)
  Definition ngen (n : nat) (b : vec Type (S n) -> Type) (k : kind) (t : ty k)
  (ce : tyConstEnv b) : kit k b (repeat (decodeClosed t)) :=
  eqkit _ _ ltac:(auto) (ngen' _ nnil ce).

End terms.

(* A Record interface for defining generic functions with the library.
    - transform is the form of the types for the base cases.
    - rest are cases for defining behaviour for the base cases.        *)
  Record NGen (n : nat) : Type := nGen
  {
    transform : vec Type (S n) -> Type;
    cunit :
      kit Ty transform (repeat (decodeClosed (Con [] Unit)));
    cnat :
      kit Ty transform (repeat (decodeClosed (Con [] Nat)));
    csum :
      kit (F Ty (F Ty Ty)) transform (repeat (decodeClosed (Con [] Sum)));
    cprod :
      kit (F Ty (F Ty Ty)) transform (repeat (decodeClosed (Con [] Prod)));
  }.


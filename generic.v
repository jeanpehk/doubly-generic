Set Implicit Arguments.
Set Universe Polymorphism.

From Coq Require Import Program List Datatypes.
Import ListNotations.

Require Import univ utils.


(* Generic Library *)

(****** Type specialization ******)
Section types.

Fixpoint kit (n : nat) (k : kind) (b : vec Type (S n) -> Type)
  : vec (decodeKind k) (S n) -> Type :=
    match k return vec (decodeKind k) (S n) -> Type with
    | Ty => fun vs => b vs
    | F k1 k2 => fun vs => quantify (fun As => kit k1 b As ->
                                               kit k2 b (zap vs As))
    end.

(* type for mapping constants to a value *)
Definition tyConstEnv (n : nat) (b : vec Type (S n) -> Type) : Type :=
  forall (k:kind) (c:const k), kit k b (repeat _ (decodeClosed (Con _ c))).

End types.

(****** Term specialization ******)
Section terms.

  (* env of kind-indexed types *)
  Inductive ngenv (n : nat) (b : vec Type (S n) -> Type) : ctx -> Type :=
    | nnil : ngenv b nil
    | ncons : forall {k} {G} (a : vec (decodeKind k) (S n)),
        kit k b a -> ngenv b G -> ngenv b (cons k G).

  (* interpret a generic type + vector of envs to a vec of types *)
  Definition interp' (G : ctx) (k : kind) (n : nat)
    : typ G k -> vec (env G) n -> vec (decodeKind k) n :=
    fun t vs =>
      zap (repeat _ (decodeType t)) vs.

  (* kit equality *)
  Definition eqkit : forall (n : nat) (k : kind) (b : vec Type (S n) -> Type)
    (t1 t2 : vec (decodeKind k) (S n)),
    t1 = t2 -> kit k b t1 -> kit k b t2.
  Proof.
    intros. induction H; assumption.
  Defined.

  (* turn an ngenv to a vector of envs *)
  (* use '@' to provide implicits explicitly *)
  Fixpoint transpose {n : nat} {b : vec Type (S n) -> Type}
    {G : ctx} (nge : ngenv b G)
    : vec (env G) (S n) :=
      match nge with
      | nnil _ => repeat _ enil
      | ncons a _ nge => zap (zap (repeat _ (@econs _ _)) a) (transpose nge)
      end.

  (* PROOFS to help with term specialization, definitions from W + C *)

  (* helper *)
  Lemma eqtail : forall {A} (n : nat) (t1 t2 : vec A n) (x : A),
    t1 = t2 -> vcons x t1 = vcons x t2.
  Proof.
    intros A n t1 t2 x eq. rewrite eq. reflexivity.
  Defined.

  Lemma c6 : forall (n : nat) (A B : Type) (f : A -> B) (x : A),
    zap (repeat n f) (repeat n x) = repeat n (f x).
  Proof.
    intros n A B f x. induction n.
    - simpl. reflexivity.
    - simpl. rewrite IHn. reflexivity.
  Defined.

  Lemma c5 : forall (n : nat) (k : kind) (G : ctx) (c : const k)
    (envs : vec (env G) n),
      repeat n (decodeClosed (Con _ c)) = interp' (Con _ c) envs.
  Proof.
    intros n k G c envs. induction envs.
    - simpl. destruct G.
      + simpl. reflexivity.
      + simpl. reflexivity.
    - simpl. rewrite IHenvs. destruct G.
      + simpl. reflexivity.
      + simpl. reflexivity.
  Defined.

  Lemma c4 : forall (n : nat) (k1 k2 : kind) (G : ctx)
    (t1 : typ G (F k1 k2))
    (t2 : typ G k1)
    (envs : vec (env G) n),
    zap (interp' t1 envs) (interp' t2 envs) = interp' (App t1 t2) envs.
  Proof.
    intros n k1 k2 G t1 t2 envs. generalize dependent G.
    induction envs.
    - destruct G.
      + simpl. reflexivity.
      + simpl. reflexivity.
    -  destruct a.
      + simpl. apply eqtail. unfold interp' in IHenvs. apply IHenvs.
      + simpl. apply eqtail. unfold interp' in IHenvs. apply IHenvs.
  Defined.

  Lemma c3 : forall (n : nat) (k k' : kind) (G : ctx)
    (t : typ (cons k' G) k) (envs : vec (env G) n) (As : vec (decodeKind k') n),
    interp' t (zap (zap (repeat n (@econs k' G)) As) envs)
    = zap (interp' (Lam t) envs) As.
  Proof.
    intros. destruct n.
    - induction envs eqn:An.
      + simpl. destruct G.
        * simpl. reflexivity.
        * simpl. reflexivity.
      + destruct G.
        * apply eqtail. simpl in IHv. apply IHv with (envs := v). reflexivity.
        * apply eqtail. simpl. simpl in IHv. apply IHv with (envs := v).
          reflexivity.
    - induction envs.
      + simpl. destruct G.
        * simpl. reflexivity.
        * simpl. reflexivity.
      + destruct G.
        * apply eqtail. apply IHenvs.
        * apply eqtail. apply IHenvs.
  Defined.

  Lemma c2 : forall (n : nat) (k k' : kind) (G : ctx)
    (x : tyvar G k') (t1 : vec (decodeKind k) n) (envs : vec (env G) n),
    interp' (Var x) envs
    = interp' (Var (Vs _ x)) (zap (zap (repeat n (@econs _ _)) t1) envs).
  Proof.
    intros. induction envs.
    - simpl. destruct G.
      + simpl. reflexivity.
      + simpl. reflexivity.
    - simpl. destruct G.
      + apply eqtail. apply IHenvs.
      + apply eqtail. apply IHenvs.
  Defined.

  Lemma c1 : forall (n : nat) (k : kind) (G : ctx)
    (a : vec (decodeKind k) n) (envs : vec (env G) n),
    a = interp' (Var (Vz _ _)) (zap (zap (repeat n (@econs _ _)) a) envs).
  Proof.
    intros. induction a.
    - simpl. reflexivity.
    - apply eqtail. apply IHa.
  Defined.

  (** Lookup a type for var from nge.
      Requires a self defined lemma 'tvcase' for destructing v.
      Done following the idea presented by James Wilcox in:
      - https://jamesrwilcox.com/dep-destruct.html              **)
  Fixpoint nlookup (n : nat) (k : kind) (b : vec Type (S n) -> Type) (G : ctx)
    (v : tyvar G k) (nge : ngenv b G) :
    kit k b (interp' (Var v) (transpose nge)).
  Proof.
    destruct nge.
    - inversion v.
    - pattern v; apply tvcase; clear v; intros.
      + subst. apply eqkit with (t1:=a).
        * pose proof (c1 _ a (transpose nge)) as ch. simpl in ch; simpl.
          rewrite <- ch; reflexivity.
        * assumption.
      + pose proof (c2 _ x a (transpose nge)) as ch.
        apply eqkit with (b:=b) in ch.
        * apply ch.
       * exact (nlookup _ _ _ _ x nge). Defined.

  (* term specialization with non-empty context *)
  Fixpoint ngen' (n : nat) (b : vec Type (S n) -> Type)
    (G : ctx) (k : kind) (t : typ G k)
    : forall (ve : ngenv b G) (ce : tyConstEnv b),
    kit k b (interp' t (transpose ve)) :=
    match t in typ G k
    return forall (ve : ngenv b G) (ce : tyConstEnv b),
    kit k b (interp' t (transpose ve)) with
    | Var x => fun ve ce => nlookup x ve
    | @Lam _ k1 k2 t1 => fun ve ce =>
        curry _ (fun (a : vec (decodeKind k1) (S n)) (nwt : kit k1 b a) =>
                  eqkit _ _ (c3 t1 (transpose ve) a)
                  (ngen' t1 (ncons a nwt ve) ce))
    | @App _ k1 k2 t1 t2 => fun ve ce =>
        eqkit _ _ (c4 t1 t2 (transpose ve))
        (@uncurry' (S n) (decodeKind k1) (fun a => (forall _: kit k1 b a,
                       (kit k2 b (zap (interp' t1 (transpose ve)) a))))
        (@ngen' _ _ _ (F k1 k2) t1 ve ce)
        (interp' t2 (transpose ve)) (ngen' t2 ve ce)
        )
    | Con _ c => fun ve ce => eqkit _ _ (c5 c (transpose ve)) (ce _ c)
    end.

  (* term specialization in an empty context. *)
  Definition ngen (n : nat) (b : vec Type (S n) -> Type) (k : kind) (t : ty k)
  (ce : tyConstEnv b) : kit k b (repeat (S n) (decodeClosed t)) :=
  eqkit k b (c6 _ _ _ ) (ngen' t (nnil _) ce).

End terms.


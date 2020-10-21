Set Implicit Arguments.

Require Import univ utils.

From Coq Require Import Nat.

(* Generic Library *)

(** Still mostly just playing around, this is basically a combination of ideas
  from 'Arity-Generic Datatype-Generic Programming' and
  'Polytypic Programming in Coq'. **)

(****** Type specialization ******)

(** "The type of a generic function instance from four pieces of information:
    - the arity of the operation, given with an implicit argument n
    - a function b to construct the type in the base case
    - the kind k itself
    - a vector v of n Coq types, each of kind k" *)

(* so b is literally the way to construct the type of the operation
      e.g. Map : vec Set 2 -> Set
      Map (A :: B :: []) = A -> B *)
Fixpoint kit (n : nat) (k : kind) (b : vec Set (S n) -> Set)
  : vec (decodeKind k) (S n) -> Set :=
    match k return vec (decodeKind k) (S n) -> Set with
    | Ty => fun vs => b vs
    | F k1 k2 => fun vs => quantify (fun As => kit k1 b As ->
                                               kit k2 b (zap vs As))
    end.

(* type for map operation: [a,b] -> (a -> b) *)
Definition Map : vec Set 2 -> Set :=
  fun vs => vhd vs -> vhd (vtl vs).

(* type for mapping constants to a value *)
Definition tyConstEnv (n : nat) (b : vec Set (S n) -> Set) : Set :=
  forall (k:kind) (c:const k), kit k b (repeat _ (decodeClosed (Con _ c))).

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
    match c in const k return kit _ Map (repeat _ (decodeClosed (Con _ c))) with
    | Nat => fun n => n
    | Unit => fun _ => tt
    | Prod => doProd
    | Sum => doSum
    end.

(* Example map with defs so far, works only for constants. *)
Definition cmap (n : nat) {b : vec Set (S n) -> Set} (k : kind) (c : const k) :=
  mapConst c.

Compute cmap Prod _ bool (fun _ => true) nat nat (fun b => b + 1) (tt,2).
Compute cmap Sum _ bool (fun _ => true)
                 nat bool (fun n => if eqb n 1 then true else false) (inr 2).

(* Now what is left is term specialization and then done for type-genericity *)

Section terms.
 (* section for term specialization *)

  (* NGENV *)
  Inductive ngenv (n : nat) : (vec Set (S n) -> Set) -> ctx -> Type :=
    | nnil : forall b, ngenv b nil
    | ncons : forall b (k:kind) (G : ctx) (a : vec (decodeKind k) (S n)),
        kit k b a -> ngenv b G -> ngenv b (cons k G).

  (* interpret a generic type + vector of envs to a vec of types *)
  Definition interp' (G : ctx) (k : kind) (n : nat)
    : typ G k -> vec (env G) n -> vec (decodeKind k) n :=
    fun t vs =>
      zap (repeat _ (decodeType t)) vs.

  (* kit equality *)
  Definition eqkit : forall (n : nat) (k : kind) (b : vec Set (S n) -> Set)
    (t1 t2 : vec (decodeKind k) (S n)),
    t1 = t2 -> kit k b t1 -> kit k b t2.
  Proof.
    intros. induction H; assumption.
  Defined.

  (* bunch of ngenvs to a vector of envs *)
  (* use '@' to provide implicits explicitly *)
  Fixpoint transpose (n : nat) (b : vec Set (S n) -> Set) (G : ctx) (nge : ngenv b G)
    : vec (env G) (S n) :=
      match nge with
      | nnil _ => repeat _ enil
      | ncons _ a _ nge => zap (zap (repeat _ (@econs _ _)) a) (transpose nge)
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
        * apply eqtail. simpl. simpl in IHv. apply IHv with (envs := v). reflexivity.
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

  (* ADMITTED FOR TESTING OTHER DEFS *)
  Fixpoint nlookup (n : nat) (k : kind) (b : vec Set (S n) -> Set) (G : ctx)
    : forall (v : tyvar G k) (nge : ngenv b G),
  kit k b (interp' (Var v) (transpose nge)).
  Proof. Admitted.

  (*
  Fixpoint nlookup' (n : nat) (k : kind) (b : vec Set (S n) -> Set) (G : ctx)
    : forall (tv : tyvar G k) (nge : ngenv b G),
    kit k b (interp' (Var tv) (transpose nge)) :=
    fun tv nge =>
      match tv in tyvar G k, nge in ngenv b G
      return kit k b (interp' (Var tv) (transpose nge)) with
      | Vz _ _, ncons _ x e ne =>
          eqkit _ _ (c1 _ x (transpose ne))
      | Vs g v, ncons _ x e ne =>
          _
    end.
    *)

  (* term specialization with non-empty context *)
  Fixpoint ngen' (n : nat) (b : vec Set (S n) -> Set) (G : ctx) (k : kind) (t : typ G k)
    : forall (ve : ngenv b G) (ce : tyConstEnv b), kit k b (interp' t (transpose ve)) :=
    match t in typ G k
    return forall (ve : ngenv b G) (ce : tyConstEnv b),
    kit k b (interp' t (transpose ve)) with
    | Var x => fun ve ce => nlookup x ve
    | @Lam _ k1 k2 t1 => fun ve ce =>
        curry _ (fun (a : vec (decodeKind k1) (S n)) (nwt : kit k1 b a) =>
                  eqkit _ _ (c3 t1 (transpose ve) a)
                  (ngen' t1 (ncons _ a nwt ve) ce))
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
  Definition ngen (n : nat) (b : vec Set (S n) -> Set) (k : kind) (t : ty k)
  (ce : tyConstEnv b) : kit k b (repeat (S n) (decodeClosed t)) :=
  @eqkit n k b _ _ (c6 _ _ _ ) (ngen' t (nnil _) ce).

End terms.

(* generic map *)
Definition gmap (k : kind) (t : ty k) : kit k Map (repeat 2 (decodeClosed t)) :=
  ngen t mapConst.

(* examples  of using gmap, still need to fix defs for 'nlookup' and 'uncurry' *)
Compute gmap tprod _ _ (fun a => a + 1) _ _ (fun b => negb b) (1,true).
(* tmaybe is a self defined type, definition in 'univ.v' *)
Compute gmap tmaybe _ bool (fun _ => false) (inl tt). (* ~ Nothing *)
Compute gmap tmaybe _ _ (fun _ => false) (inr 3). (* ~ Just 3 *)


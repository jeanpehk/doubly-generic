Set Implicit Arguments.
Set Universe Polymorphism.

From Coq Require Import Program.

Require Import univ utils.


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

(* type for mapping constants to a value *)
Definition tyConstEnv (n : nat) (b : vec Set (S n) -> Set) : Set :=
  forall (k:kind) (c:const k), kit k b (repeat _ (decodeClosed (Con _ c))).

Section cmap.
  (* An example of defining constants for map *)

  (* type for the operation aka: [a,b] to (a -> b) *)
  Definition Map : vec Set 2 -> Set :=
    fun vs => vhd vs -> vhd (vtl vs).

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
      match c in const k
      return kit _ Map (repeat _ (decodeClosed (Con _ c))) with
      | Nat => fun n => n
      | Unit => fun _ => tt
      | Prod => doProd
      | Sum => doSum
      end.
End cmap.

(* Now what is left is term specialization and then done for type-genericity *)

Section terms.
 (* section for term specialization *)

  (* env of kind-indexed types *)
  Inductive ngenv (n : nat) (b : vec Set (S n) -> Set) : ctx -> Type :=
    | nnil : ngenv b nil
    | ncons : forall {k} {G} (a : vec (decodeKind k) (S n)),
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

  (* turn an ngenv to a vector of envs *)
  (* use '@' to provide implicits explicitly *)
  Fixpoint transpose (n : nat) (b : vec Set (S n) -> Set)
    (G : ctx) (nge : ngenv b G)
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

  (* Lookup a type for var from nge  *)
  Fixpoint nlookup (n : nat) (k : kind) (b : vec Set (S n) -> Set) (G : ctx)
    (v : tyvar G k) (nge : ngenv b G) :
    kit k b (interp' (Var v) (transpose nge)).
  Proof.
    intros.

    destruct nge.
    - inversion v.
    - dependent destruction v.
      + apply eqkit with (t1 := a).
        * pose proof (c1 _ a (transpose nge)) as ch. simpl in ch. simpl.
          rewrite <- ch. reflexivity.
        * apply k1.
      + pose proof (c2 _ v a (transpose nge)) as ch.
        apply eqkit with (b:=b) in ch.
        * apply ch.
        * exact (nlookup _ _ _ _ v nge).

          (** stuck without dependent destruction:

    destruct nge.
    - inversion v.
    - inversion v; subst.
      + apply eqkit with (t1 := a).
        * pose proof (c1 _ a (transpose nge)) as ch. simpl in ch. simpl.
          (* needs Var (Vz G k) = Var v *)
          admit.
        * apply k1.
      + pose proof (c2 _ X a (transpose nge)) as ch.
        apply eqkit with (b:=b) in ch.
        * (* needs Var (Vs k0 X) = Var v *)
          admit.
        * exact (nlookup _ _ _ _ X nge).

          **)
  Defined.

  (* term specialization with non-empty context *)
  Fixpoint ngen' (n : nat) (b : vec Set (S n) -> Set)
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
  Definition ngen (n : nat) (b : vec Set (S n) -> Set) (k : kind) (t : ty k)
  (ce : tyConstEnv b) : kit k b (repeat (S n) (decodeClosed t)) :=
  eqkit k b (c6 _ _ _ ) (ngen' t (nnil _) ce).

End terms.

(* Now we can use ngen and mapConst to define a generic map *)

Definition gmap (k : kind) (t : ty k) : kit k Map _ :=
  ngen t mapConst.

(* examples  of using gmap *)
Compute gmap tprod _ _ (fun a => a + 1) _ _ (fun b => negb b) (1,true).
(* tmaybe is a self defined type, definition in 'univ.v' *)
Compute gmap tmaybe _ bool (fun _ => false) (inl tt). (* ~ Nothing *)
Compute gmap tmaybe _ _ (fun n => false) (inr 3). (* ~ Just 3 *)
Compute gmap teither _ _ (fun _ => false) _ _ (fun _ => true) (inl tt).

(***********************************************************************)
(* with these datatype-genericity done, now just need to add arity-gen *)
(***********************************************************************)

(* turn a vector of types into a function type, e.g [a,b,c] into: a -> b -> c *)
Fixpoint funTy {n : nat} (v : vec Type (S n)) : Type :=
  match v with
  | @vcons _ O x xs => x
  | @vcons _ (S n') x xs => x -> funTy xs
  end.

(* helpers for incoming example definitions *)
Definition pr : decodeKind (F Ty (F Ty Ty)) := prod.
Definition sm : decodeKind (F Ty (F Ty Ty)) := sum.

Section argm.
  (* example of the functionality that the user needs to provide *)
  (* aka how doubly-generic map works for constants *)

  (* nat constant for nmapconst *)
  Fixpoint cNat (n : nat) : kit Ty funTy (repeat (S n) nat) :=
    let f := (fix cNat' (n' : nat)
      : kit Ty funTy (repeat (S n') nat) :=
      match n' return kit Ty funTy (repeat (S n') nat) with
      | O => O
      | S O => fun x => x
      | S (S m) => fun x y => cNat' m
    end) in
    match n return kit Ty funTy (repeat (S n) nat) with
    | O => O
    | S O => fun x => x
    | (S (S m)) =>
        if Nat.odd m
        then fun x y => cNat m
        else fun x => f (S m)
    end.

  (* unit constant for nmapconst *)
  Fixpoint cUnit (n : nat) : kit Ty funTy (repeat (S n) unit) :=
    match n with
    | O => tt
    | S n' => fun x => cUnit n'
    end.

  Fixpoint hProd (n : nat) {struct n}
    : forall (va : vec Type (S n)), funTy va
    -> forall (vb : vec Type (S n)), funTy vb
    -> funTy (zap (zap (repeat _ prod) va) vb).
  Proof. Admitted.

  (* helper for defining sums *)
  Definition hSum (n : nat)
    : forall (va : vec Type (S n)), funTy va
    -> forall (vb : vec Type (S n)), funTy vb
    -> funTy (zap (zap (repeat _ sum) va) vb).
  Proof.
  Admitted.

  (* helper for defining prods
  Fixpoint hProd (n : nat)
    : forall (va : vec Type (S n)), funTy va
    -> forall (vb : vec Type (S n)), funTy vb
    -> funTy (zap (zap (repeat _ prod) va) vb) :=
      fun va =>
      match va in vec _ (S n)
      return funTy va -> forall (vb : vec Type (S n)),
      funTy vb -> funTy (zap (zap (repeat _ prod) va) vb) with
      | @vcons _ O A As => fun a _ b => (a, b)
      | @vcons _ (S m) A As => fun a vb =>
          match vb with
          | vcons B Bs => fun b =>
            fun p => hProd _ As (a (fst p)) Bs (b (snd p))
          end
      end.*)

  (* sum constant for nmapconst *)
  Definition cSum (n : nat) : kit (F Ty (F Ty Ty)) funTy (repeat (S n) sm).
  Admitted.

  (* prod constant for nmapconst *)
  Definition cProd (n : nat) : kit (F Ty (F Ty Ty)) funTy (repeat (S n) pr).
  Admitted.

  Definition nmapConst {n : nat} : tyConstEnv (@funTy n) :=
    fun k c =>
      match c in const k with
      (*in const k return kit _ Map (repeat _ (decodeClosed (Con _ c))) with *)
      | Nat => cNat _
      | Unit => cUnit _
      | Prod => cProd _
      | Sum => cSum _
      end.

End argm.

Section eq.
  (* An example of building a doubly-generic equality function *)

  Fixpoint geq {n : nat} (v : vec Type (S n)) : Type :=
    match v with
    | @vcons _ O x _ => x -> bool
    | @vcons _ (S m) x xs => x -> geq xs
    end.

  Fixpoint geqFalse (n : nat) (v : vec Set (S n)) : geq v :=
    match v in vec _ (S n) return geq v with
    | @vcons _ O x _ => fun _ => false
    | @vcons _ (S m) x xs => fun _ => geqFalse xs
    end.

  (* wrong *)
  Fixpoint eqNat (n : nat) : kit Ty geq (repeat (S n) nat) :=
    let f := (fix eqNat' (n' : nat) : kit Ty geq (repeat (S n') nat) :=
      match n' return kit Ty geq (repeat (S n') nat) with
      | O => fun _ => true
      | S O => fun a b => Nat.eqb a b
      | S (S m) =>
          fun a b => if Nat.eqb a b then (eqNat m) else geqFalse (repeat _ nat)
          (*
      | S (S m) => fun a b =>
          if eqb a b then eqNat m else geqFalse (repeat _ nat)
          *)
    end) in
      match n return kit Ty geq (repeat (S n) nat) with
      | O => fun _ => true
      | S O => fun a b => Nat.eqb a b
      | S n => fun a b => if Nat.eqb a b then (f n) a else geqFalse (repeat _ nat)
          (*
      | O => fun _ => true
      | S O => fun a b => eqb a b
      | S (S m) => fun a b =>
          if eqb a b then f (S m) b else geqFalse (repeat _ nat)
          *)
      end.

  Fixpoint eqUnit (n : nat) : kit Ty geq (repeat (S n) unit) :=
    match n with
    | O => fun _ => true
    | S n' => fun _ => eqUnit n'
    end.

  (* sum constant for nmapconst *)
  Definition eqProd (n : nat) : kit (F Ty (F Ty Ty)) geq (repeat (S n) pr).
  Admitted.

  Definition eqSum (n : nat) : kit (F Ty (F Ty Ty)) geq (repeat (S n) sm).
  Admitted.

  Definition neqConst {n : nat} : tyConstEnv (@geq n) :=
    fun k c =>
      match c in const k with
      (*in const k return kit _ Map (repeat _ (decodeClosed (Con _ c))) with *)
      | Nat => eqNat _
      | Unit => eqUnit _
      | Prod => eqProd _
      | Sum => eqSum _
      end.

End eq.

(* Now can define a doubly-generic map with ngen and nmapConst *)

Definition ngmap (n : nat) (k : kind) (t : ty k)
  : kit k funTy (repeat (S n) (decodeClosed t)) :=
  ngen t nmapConst.

Definition ngeq (n : nat) (k : kind) (t : ty k)
  : kit k geq (repeat (S n) (decodeClosed t)) :=
  ngen t neqConst.

(* some test examples for map *)
Compute ngmap 0 tunit. (* = () *)
Compute ngmap 1 tunit tt. (* = () *)
Compute ngmap 0 tnat. (* = 0 *)
Compute ngmap 1 tnat 1. (* = 1 *)
Compute ngmap 2 tnat 1 2. (* = 2 *)
Compute ngmap 3 tnat 1 2 3. (* = 3 *)

Compute ngeq 0 tunit tt. (* = true *)
Compute ngeq 1 tunit tt tt. (* = true *)
Compute ngeq 0 tnat 1. (* = true *)
Compute ngeq 1 tnat 1 1. (* = true *)
Compute ngeq 2 tnat 1 1 2. (* = false *)
Compute ngeq 3 tnat 2 1 2 3. (* = .. *)


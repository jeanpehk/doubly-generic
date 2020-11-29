Set Implicit Arguments.
Set Universe Polymorphism.

From Coq Require Import Program List Datatypes.
Import ListNotations.

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
Fixpoint kit (n : nat) (k : kind) (b : vec Type (S n) -> Type)
  : vec (decodeKind k) (S n) -> Type :=
    match k return vec (decodeKind k) (S n) -> Type with
    | Ty => fun vs => b vs
    | F k1 k2 => fun vs => quantify (fun As => kit k1 b As ->
                                               kit k2 b (zap vs As))
    end.

Fixpoint unkit (n : nat) (k : kind) (b : vec Type (S n) -> Type)
  : vec (decodeKind k) (S n) -> Type :=
    match k return vec (decodeKind k) (S n) -> Type with
    | Ty => fun vs => b vs
    | F k1 k2 => fun vs =>
        forall (a : vec (decodeKind k1) _),
        kit k1 b a ->
        unkit k2 b (zap vs a)
    end.

(* type for mapping constants to a value *)
Definition tyConstEnv (n : nat) (b : vec Type (S n) -> Type) : Type :=
  forall (k:kind) (c:const k), kit k b (repeat _ (decodeClosed (Con _ c))).

Section cmap.
  (* An example of defining constants for map *)

  (* type for the operation aka: [a,b] to (a -> b) *)
  Definition Map : vec Type 2 -> Type :=
    fun vs => vhd vs -> vhd (vtl vs).

  (* helper for mapConst *)
  Definition doSum (A1 B1 : Type)
    : (A1 -> B1) -> forall (A2 B2 : Type), (A2 -> B2) -> (A1 + A2) -> (B1 + B2) :=
    fun f =>
      fun _ _ g sa =>
        match sa with
        | inl a => inl (f a)
        | inr b => inr (g b)
        end.

  (* helper for mapConst *)
  Definition doProd (A1 B1 : Type)
    : (A1 -> B1) -> forall (A2 B2 : Type), (A2 -> B2) -> (A1 * A2) -> (B1 * B2) :=
    fun f _ _ g sa => (f (fst sa), g (snd sa)).

  (* Example of building a function for mapping constants to a value. *)
  Definition mapConst : tyConstEnv Map :=
    fun k c =>
      match c in const k
      return kit k Map (repeat _ (decodeClosed (Con _ c)))
      with
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
  Inductive ngenv (n : nat) (b : vec Type (S n) -> Type) : ctx -> Type :=
    | nnil : ngenv b nil
    | ncons : forall {k} {G} (a : vec (decodeKind k) (S n)),
        kit k b a -> ngenv b G -> ngenv b (cons k G).

  (* interpret a generic type + vector of envs to a vec of types *)
  Definition interp' (G : ctx) (k : kind) (n : nat)
    : typ G k -> vec (env G) n -> vec (decodeKind k) n :=
    fun t vs =>
      zap (repeat _ (decodeType t)) vs.

  Lemma zr : forall n G k (t1 : tyvar G k) (a : env G) (v : vec (env G) n),
    zap (repeat (S n) (decodeType (Var t1))) (vcons a v)
    = vcons (decodeType (Var t1) a)
    (zap (repeat n (decodeType (Var t1))) v).
  Proof.
    intros. reflexivity.
  Defined.

  Lemma ineqv : forall n G k (t1 t2 : tyvar G k) (v : vec (env G) n),
    interp' (Var t1) v = interp' (Var t2) v.
  Proof.
    intros.
    intros. induction v.
    - destruct t1; reflexivity.
    - unfold interp'. unfold interp' in IHv. rewrite zr. rewrite zr.
      rewrite IHv. simpl.
  Admitted.

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

(*
  Import EqNotations.

   https://jamesrwilcox.com/dep-destruct.html 
  Lemma inv (k k' : kind) (G : ctx) (v : tyvar (k' :: G) k) :
    {p : k' = k | rew [fun k' : kind => tyvar (k' :: G) k] p in v = Vz G k} +
    {w : tyvar G k | v = Vs k' w}.
  Proof.
    pattern v. apply tvcase; intros.
    - left. apply exist with (x:=eq_sym pf). subst; auto.
    - right. apply exist with (x:=x). reflexivity.
  Defined.*)

  (* Lookup a type for var from nge  *)
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

         (*
    - pose proof inv v as i. destruct i as [[p e] | [w e]].
      + subst. apply eqkit with (t1 := a).
        * pose proof (c1 _ a (transpose nge)) as ch. simpl in ch. simpl.
          cbn in e. rewrite e.
          rewrite <- ch. reflexivity.
        * apply k1.
      + rewrite e.
        pose proof (c2 _ w a (transpose nge)) as ch.
        apply eqkit with (b:=b) in ch.
        * apply ch.
       * exact (nlookup _ _ _ _ w nge). Defined.
         *)

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

(* Now we can use ngen and mapConst to define a generic map *)

Definition gmap (k : kind) (t : ty k) : kit k Map _ :=
  ngen t mapConst.

(* examples  of using gmap *)
Compute gmap tprod nat nat (fun a => a + 1) bool bool (fun b => negb b) (1,true).
(* tmaybe is a self defined type, definition in 'univ.v' *)
Compute gmap tmaybe _ bool (fun _ => false) (inl tt). (* = inl () *)
Compute gmap tmaybe nat nat (fun n => n + 1) (inr 3). (* = inr 4 *)
(* teither is a self defined type, definition in 'univ.v' *)
Compute gmap teither _ bool (fun _ => false)
                     _ bool (fun _ => true) (inl tt). (* = inl false *)

(***********************************************************************)
(* with these datatype-genericity done, now just need to add arity-gen *)
(***********************************************************************)

(* turn a vector of types into a function type, e.g [a,b,c] into: a -> b -> c *)
Fixpoint funTy {n : nat} (v : vec Type (S n)) : Type :=
  match v with
  | @vcons _ O x xs => x
  | @vcons _ (S n') x xs => x -> funTy xs
  end.

Section argm.
  (* example of the functionality that the user needs to provide *)
  (* aka how doubly-generic map works for constants *)

  (* nat constant for nmapconst *)
  Fixpoint cNat (n : nat) : kit Ty funTy (repeat (S n) _) :=
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
  Fixpoint cUnit (n : nat) : kit Ty funTy (repeat (S n) _) :=
    match n with
    | O => tt
    | S n' => fun x => cUnit n'
    end.

  (* Error axiom for finishing defs in sums *)
  Axiom error : False.

  (* helpers for defining sums *)
  Fixpoint hSumLeft (n : nat)
    : forall (va : vec Type (S n)), funTy va ->
    forall (vb : vec Type (S n)), funTy (zap (zap (repeat _ sum) va) vb).
  Proof.
    intros VA a VB. simpl.
    pose proof veq_hdtl VA as pfa;
    pose proof veq_hdtl VB as pfb.
    destruct n as [| n'].
    - rewrite pfa in a. apply (inl a).
    - intros x. destruct x.
      + rewrite pfa in a. simpl in a.
        pose proof a v as pa.
        pose proof hSumLeft _ _ pa (vtl VB) as pf.
        apply pf.
      + pose proof error as err. exfalso; apply err.
  Defined.

  Fixpoint hSumRight (n : nat)
    : forall (va : vec Type (S n)) (vb : vec Type (S n)),
    funTy vb -> funTy (zap (zap (repeat _ sum) va) vb).
  Proof.
    intros VA VB b. pose proof veq_hdtl VB as pfb.
    destruct n as [| n'].
    - rewrite pfb in b. apply (inr b).
    - intros x; destruct x as [left | right].
      + exfalso; apply error.
      + rewrite pfb in b. simpl in b.
        pose proof b right as pb.
        pose proof hSumRight n' (vtl VA)  (vtl VB) pb  as pf.
        apply pf.
  Defined.

  Definition hSum (n : nat)
    : forall (va : vec Type (S n)), funTy va
    -> forall (vb : vec Type (S n)), funTy vb
    -> funTy (zap (zap (repeat _ sum) va) vb).
  Proof.
    intros VA a VB b.
    destruct n as [| n'].
    (* no arguments, chooses arbitrary case inr *)
    - simpl. rewrite veq_hdtl in b. simpl in b. apply (inr b).
    - intros x; destruct x as [lr | rt].
      + rewrite veq_hdtl in a. simpl in a.
        pose proof a lr as pfa.
        apply hSumLeft; apply pfa.
      + rewrite veq_hdtl in b. simpl in b.
        pose proof b rt as pfb.
        apply hSumRight; apply pfb.
 Defined.

  (* sum constant for nmapconst *)
  Definition cSum (n : nat) : kit (F Ty (F Ty Ty)) funTy (repeat (S n) sum).
  Proof.
  Admitted.

  Program Fixpoint kindCurry (k : kind) (n : nat) (b : vec Type (S n) -> Type)
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
              (fun As y => kindCurry k2 _ (zap v As) (vs As y))
    end.

  (* [a, b], [c,d] => [(a, c)], [(b, d)] => (a, c) -> (b, d) *)

  (* no fucking clue if correct dadadaaa *)
  Fixpoint hProd (n : nat)
    : forall (va : vec Type (S n)), funTy va
    -> forall (vb : vec Type (S n)), funTy vb
    -> funTy (zap (zap (repeat _ prod) va) vb).
      Proof.
        destruct n;
        intros VA a VB b;
        pose proof veq_hdtl VA as pfa;
        pose proof veq_hdtl VB as pfb.
        - apply pair.
          + rewrite pfa in a; apply a.
          + rewrite pfb in b; apply b.
        - refine (fun pr => _). intros.
          destruct pr as [pa pb].
          apply hProd.
          + rewrite pfa in a. apply a. apply pa.
          + rewrite pfb in b. apply b. apply pb.
      Defined.

  (* prod constant for nmapconst *)
  Fixpoint cProd (n : nat) : kit (F Ty (F Ty Ty)) funTy (repeat (S n) prod).
  Proof.
    apply (kindCurry (F Ty (F Ty Ty))).
    simpl. intros VA a VB b.
    pose proof hProd VA a VB b as hp.
    simpl in hp.
    apply hp.
  Defined.

  Fixpoint nmapConst {n : nat} : tyConstEnv (@funTy n).
  refine (fun k c => _).
  refine
  (match c with
    | Nat => _
    | Unit => _
    | Prod => _
    | Sum => _
    end
  ).
  (* this just returns 0 for all,
     maybe change to return last nat given (like cNat) *)
  - induction n.
    + simpl. apply (cNat 0).
    + refine (fun x => _). apply IHn.
  - induction n.
    + apply tt.
    + refine (fun x => _). apply IHn.
  - pose proof (kindCurry (F Ty (F Ty Ty))) as pf.
    apply pf. simpl. intros VA a VB b.
    pose proof hSum VA a VB b as hp. simpl in hp.
    apply hp.
  - pose proof (kindCurry (F Ty (F Ty Ty))) as pf.
    apply pf. simpl. intros VA a VB b.
    pose proof hProd VA a VB b as hp. simpl in hp.
    apply hp.
  Defined.

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

  Program Fixpoint eqNat (n : nat) {measure n} : kit Ty geq (repeat (S n) nat) :=
    match n with
    | O => fun _ => true
    | S O => fun a b => Nat.eqb a b
    | S (S m) => fun a b =>
        if Nat.eqb a b then eqNat (S m) b
                       else geqFalse (repeat _ nat)
    end.

  Fixpoint eqUnit (n : nat) : kit Ty geq (repeat (S n) unit) :=
    match n with
    | O => fun _ => true
    | S n' => fun _ => eqUnit n'
    end.

  Fixpoint heqProd (n : nat)
    : forall (va : vec Type (S n)), geq va
    -> forall (vb : vec Type (S n)), geq vb
    -> geq (zap (zap (repeat _ prod) va) vb).
  Proof.
    intros. destruct n.
    - simpl. refine (fun pr => _).
      apply true.
    - simpl; intros pr. destruct pr as [a b].
      apply heqProd.
  Admitted.

  Definition heqSum (n : nat)
    : forall (va : vec Type (S n)), geq va
    -> forall (vb : vec Type (S n)), geq vb
    -> geq (zap (zap (repeat _ sum) va) vb).
  Proof. Admitted.

  (* sum constant for neqconst  *)
  Fixpoint eqProd (n : nat) : kit (F Ty (F Ty Ty)) geq (repeat (S n) prod). Admitted.

  Definition eqSum (n : nat) : kit (F Ty (F Ty Ty)) geq (repeat (S n) sum).
  Admitted.

  (*
  Program Fixpoint neqConst {n : nat} : tyConstEnv (@geq n) :=
    fun k c =>
      match c in const k
      with
      (*in const k return kit _ Map (repeat _ (decodeClosed (Con _ c))) with *)
      | Nat => eqNat _
      | Unit => eqUnit _
      | Prod => eqProd _
      | Sum => eqSum _
      end.
      *)

End eq.

(* Now can define a doubly-generic map with ngen and nmapConst *)

Definition ngmap (n : nat) (k : kind) (t : ty k)
  : kit k funTy (repeat (S n) (decodeClosed t)) :=
  ngen t nmapConst.

(*
Definition ngeq (n : nat) (k : kind) (t : ty k)
  : kit k geq (repeat (S n) (decodeClosed t)) :=
  ngen t neqConst.
      *)

(* some test examples for map *)

(* some test examples for unit map *)
Compute ngmap 0 tunit. (* = () *)
Compute ngmap 1 tunit tt. (* = () *)
Compute ngmap 0 tnat. (* = 0 *)

(* some test examples for nat map *)
Compute ngmap 1 tnat 1. (* = 1 *)
Compute ngmap 2 tnat 1 2. (* = 2 *)
Compute ngmap 3 tnat 1 2 3. (* = 3 *)

(* some test examples for prod map *)
Compute ngmap 1 tprod nat nat
  (fun x => x + 1) bool bool (fun _ => true) (1,true).
Compute ngmap 2 tprod nat nat nat
  (fun x y => x + y) bool bool bool (fun x y => andb x y) (1,true) (2, false).
Compute ngmap 3 tprod nat nat nat nat
  (fun x y z => x + y + z) bool bool nat nat
  (fun x y z => if andb x y then 0 else z)
  (1,true) (2, false) (1, 100). (* = (4, 100) *)

(* some test examples for sum map *)
Compute ngmap 1 tsum nat nat
  (fun x => x + 1) bool bool (fun _ => true) (inl 1).
Compute ngmap 2 tsum nat nat nat
  (fun x y => x + y) bool bool bool (fun x y => andb x y)
  (inl 1) (inl 1).
Compute ngmap 3 tsum nat nat nat nat
  (fun x y z => x + y + z) bool bool nat nat
  (fun x y z => if andb x y then 0 else z)
  (inr true) (inr false) (inr 4). (* = inr 4 *)

(* some test examples for self defined maybe *)
Compute ngmap 1 tmaybe _ bool (fun _ => false) (inl tt). (* = inl () *)
Compute ngmap 2 tmaybe nat nat nat (fun x => fun y => x + y)
  (inr 3) (inr 2).

(*
(* some test examples for unit eq *)
Compute ngeq 0 tunit tt. (* = true *)
Compute ngeq 1 tunit tt tt. (* = true *)

(* some test examples for nat eq *)
Compute ngeq 0 tnat 1. (* = true *)
Compute ngeq 1 tnat 1 1. (* = true *)
Compute ngeq 2 tnat 2 2 1. (* = false *)
Compute ngeq 3 tnat 1 1 1 2. (* = false *)
      *)

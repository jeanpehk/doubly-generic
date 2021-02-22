From Coq Require Import Program List.

Import ListNotations.

Require Export init.
Require Import generic univ utils.

(* examples of defining types with the universe. *)
Section univTypes.

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

  (* examples of defining maybe and either with the universe. *)

  Definition tmaybe : ty (F Ty Ty) :=
    Lam (App (App (tsumc _) (tunitc _)) (Var (Vz _ _))).

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

End univTypes.

(* Example of a datatype-generic function. *)
Section dtgen.

  (* type definition needed for gmap *)
  Definition Map : vec Type 2 -> Type :=
    fun vs => vhd vs -> vhd (vtl vs).

  (* helper for defining sums *)
  Definition doSum (A1 B1 : Type)
    : (A1 -> B1) -> forall (A2 B2 : Type), (A2 -> B2) -> (A1 + A2) -> (B1 + B2) :=
    fun f =>
      fun _ _ g sa =>
        match sa with
        | inl a => inl (f a)
        | inr b => inr (g b)
        end.

  (* helper for defining prods *)
  Definition doProd (A1 B1 : Type)
    : (A1 -> B1) -> forall (A2 B2 : Type), (A2 -> B2) -> (A1 * A2) -> (B1 * B2) :=
    fun f _ _ g sa => (f (fst sa), g (snd sa)).

  (** constants **)
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

  (* gmap *)
  Definition gmap (k : kind) (t : ty k) : kit k Map _ :=
    specTerm t mapConst.

  (* examples  of using gmap *)
  Compute gmap tprod nat nat (fun a => a + 1) bool bool (fun b => negb b) (1,true).
  (* tmaybe is a self defined type, definition in 'univ.v' *)
  Compute gmap tmaybe _ bool (fun _ => false) (inl tt). (* = inl () *)
  Compute gmap tmaybe nat nat (fun n => n + 1) (inr 3). (* = inr 4 *)
  (* teither is a self defined type, definition in 'univ.v' *)
  Compute gmap teither _ bool (fun _ => false)
                       _ bool (fun _ => true) (inl tt). (* = inl false *)

  (* A more general definition using record 'NGen' *)
  Definition ggmap (n : nat) := (@nGen _)
    Map
    (fun n => n)
    (fun tt => tt)
    doSum
    doProd.

  Check ggmap 2.

End dtgen.

(* Example of a arity-generic and datatype-generic function. *)
Section aritydtgen.

  (* helpers for making doubly generic defs *)

  (* type definition needed for doubly generic map *)
  Fixpoint nMap {n : nat} (v : vec Type (S n)) : Type :=
    match v with
    | @vcons _ O x xs => x
    | @vcons _ (S n') x xs => x -> nMap xs
    end.

  (* nat constant for nmapconst  *)
  Fixpoint ccNat (n : nat)
    : kit Ty nMap (repeat (S n) (decodeClosed (Con [] Nat))) :=
    match n return kit Ty nMap (repeat (S n) (decodeClosed (Con [] Nat))) with
    | O => O
    | S O => fun x => x
    | S m => fun x y => ccNat _
    end.

  Fixpoint cNat (n : nat) : kit Ty nMap (repeat (S n) (decodeClosed (Con [] Nat))) :=
    let f := (fix cNat' (n' : nat)
      : kit Ty nMap (repeat (S n') (decodeClosed (Con [] Nat))) :=
      match n' return kit Ty nMap (repeat (S n') (decodeClosed (Con [] Nat))) with
      | O => O
      | S O => fun x => x
      | S (S m) => fun x y => cNat' m
    end) in
    match n return kit Ty nMap (repeat (S n) (decodeClosed (Con [] Nat))) with
    | O => O
    | S O => fun x => x
    | (S (S m)) =>
        if Nat.odd m
        then fun x y => cNat m
        else fun x => f (S m)
    end.

  (* unit constant for nmapconst *)
  Fixpoint cUnit (n : nat)
    : kit Ty nMap (repeat (S n) (decodeClosed (Con [] Unit))) :=
    match n with
    | O => tt
    | S n' => fun x => cUnit n'
    end.

  (* Error axiom for finishing defs in sums *)
  Axiom error : False.

  (* helper for defining left-side cases of sums *)
  Fixpoint hSumLeft (n : nat)
    : forall (va : vec Type (S n)), nMap va ->
    forall (vb : vec Type (S n)), nMap (zap (zap (repeat _ sum) va) vb).
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
      (* error case *)
      + pose proof error as err. exfalso; apply err.
  Defined.

  (* helper for defining right-side cases of sums *)
  Fixpoint hSumRight (n : nat)
    : forall (va : vec Type (S n)) (vb : vec Type (S n)),
    nMap vb -> nMap (zap (zap (repeat _ sum) va) vb).
  Proof.
    intros VA VB b. pose proof veq_hdtl VB as pfb.
    destruct n as [| n'].
    - rewrite pfb in b. apply (inr b).
    - intros x; destruct x as [left | right].
      (* error case *)
      + exfalso; apply error.
      + rewrite pfb in b. simpl in b.
        pose proof b right as pb.
        pose proof hSumRight n' (vtl VA)  (vtl VB) pb  as pf.
        apply pf.
  Defined.

  (* case for sums in curried form  *)
  Definition hSum (n : nat)
    : forall (va : vec Type (S n)), nMap va
    -> forall (vb : vec Type (S n)), nMap vb
    -> nMap (zap (zap (repeat _ sum) va) vb).
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

  (* case for prods in curried form  *)
  Fixpoint hProd (n : nat)
    : forall (va : vec Type (S n)), nMap va
    -> forall (vb : vec Type (S n)), nMap vb
    -> nMap (zap (zap (repeat _ (decodeClosed (Con [] Prod))) va) vb).
      Proof.
        destruct n;
        intros VA a VB b;
        pose proof veq_hdtl VA as pfa;
        pose proof veq_hdtl VB as pfb.
        - apply pair.
          + rewrite pfa in a; apply a.
          + rewrite pfb in b; apply b.
        - simpl; intros pr.
          destruct pr as [pa pb].
          apply hProd.
          + rewrite pfa in a. apply a. apply pa.
          + rewrite pfb in b. apply b. apply pb.
      Defined.

  Lemma nat_eq_closedNat : decodeClosed (Con [] Nat) = nat.
  Proof.
    unfold decodeClosed. reflexivity.
  Defined.

  (* Combined cases for the generic constants *)
  Definition nmapConst {n : nat} : tyConstEnv (@nMap n).
  refine (fun k c => _).
  refine
  (match c with
    | Nat => cNat _
    | Unit => cUnit _
    | Prod => _
    | Sum => _
    end
  ).
  (* Case for sum *)
  - apply (curryKind (F Ty (F Ty Ty))). simpl.
    apply hSum.
  (* Case for prod *)
  - apply (curryKind (F Ty (F Ty Ty))); simpl.
    apply hProd.
  Defined.

  (* doubly generic map *)
  Definition ngmap (n : nat) (k : kind) (t : ty k)
    : kit k nMap (repeat (S n) (decodeClosed t)) :=
    specTerm t nmapConst.

  (* A more general definition using record 'NGen' *)
  Program Definition nggmap (n : nat) := (@nGen n)
    nMap
    _
    _
    _
    _
    .
  (* Unit case *)
  Next Obligation.
    - induction n.
      + apply tt.
      + intros x. apply IHn. Defined.
  (* Nat case *)
  Next Obligation.
    - induction n.
      + apply 0.
      + intros x. apply IHn. Defined.
  (* Sum case *)
  Next Obligation.
    - pose proof @nmapConst n (F Ty (F Ty Ty)) Sum as pf.
      apply pf. Defined.
  (* Prod case *)
  Next Obligation.
    - pose proof @nmapConst n (F Ty (F Ty Ty)) Prod as pf.
      apply pf. Defined.

  (* some test examples for unit map *)
  Compute ngmap 0 tunit. (* = () *)
  Compute ngmap 1 tunit tt. (* = () *)
  Compute ngmap 0 tnat. (* = 0 *)

  (* some test examples for nat map *)
  Compute ngmap 1 tnat 1. (* = 1 *)
  Compute ngmap 2 tnat 1 2. (* = 2 *)
  Compute ngmap 3 tnat 1 2 3. (* = 3 *)

  (* some test examples for prod map *)
  Compute ngmap 1 tprod
    _ _ (fun x => x + 1)
    _ _ (fun _ => true)
    (1,false).
  Compute ngmap 2 tprod
    nat nat nat (fun x y => x + y)
    bool bool bool (fun x y => andb x y)
    (15,true) (4, false).
  Compute ngmap 3 tprod
    _ _ _ _ (fun x y z => x + y + z)
    _ _ _ _ (fun x y z => andb (andb x y) z)
    (11,true) (2, true) (6, true). (* = (19, true) *)

  (* some test examples for sum map *)
  Compute ngmap 1 tsum
    _ _ (fun x => x + 1)
    _ _ (fun _ => true)
    (inl 1). (* = inl 2 *)
  Compute ngmap 2 tsum
    _ _ _ (fun x y => x + y)
    _ _ _ (fun x y => andb x y)
    (inl 2) (inl 5). (* = inl 7 *)
  Compute ngmap 3 tsum
    _ _ _ _ (fun x y z => x + y + z)
    _ _ _ _ (fun x y z => if andb x y then 0 else z)
    (inr true) (inr false) (inr 4). (* = inr 4 *)

  (* some test examples for self defined tmaybe *)
  Compute ngmap 1 tmaybe
    _ _ (fun _ => false)
    (inl tt). (* = inl () *)
  Compute ngmap 2 tmaybe
    _ _ _ (fun x => fun y => x + y)
    (inr 3) (inr 2). (* = inr 5 *)

End aritydtgen.


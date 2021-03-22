From Coq Require Import Program List.

Import ListNotations.
Import EqNotations.

Require Export init.
Require Import generic univ utils.

(* examples of defining types with the universe. *)
Section univTypes.

  (* Shorthands for constants *)
  Definition tnat := Con (G:=nil) Nat.
  Definition tunit := Con (G:=nil) Unit.
  Definition tsum := Con (G:=nil) Sum.
  Definition tprod := Con (G:=nil) Prod.

  (* Shorthands for constants in a context *)
  Definition tnatc := fun c:ctx => Con (G:=c) Nat.
  Definition tunitc := fun c:ctx => Con (G:=c) Unit.
  Definition tsumc := fun c:ctx => Con (G:=c) Sum.
  Definition tprodc := fun c:ctx => Con (G:=c) Prod.

  (* examples of defining maybe and either with the universe. *)

  Definition tmaybe : ty (F Ty Ty) :=
    Lam (App (App tsumc tunitc) (Var (Vz ))).

  Definition teither : ty (F Ty (F Ty Ty)) :=
    Lam (Lam
      (App (App tsumc
        (Var (Vs (Vz )))) (Var (Vz )))).

  (* Shorthands for decoding closed types *)
  Definition deNat := decodeClosed (Con Nat).
  Definition deUnit := decodeClosed (Con Unit).
  Definition deMaybe (A : Set) := decodeClosed tmaybe A.
  Definition deEither (A B : Set) := decodeClosed teither A B.

  (* Compute examples *)
  Compute deNat. (* = nat *)
  Compute deUnit. (* = unit *)
  Compute deMaybe. (* = fun A : Set => (unit + A) *)
  Compute deMaybe nat. (* = (unit + nat) *)
  Compute deEither. (* = fun A B : Set => (A + B) *)
  Compute deEither nat unit. (* = (nat + unit) *)

  Compute decodeClosed (Con Nat).

End univTypes.

Section dtgen.
  (* Example of a datatype-generic map. *)

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

  Definition mapConst : tyConstEnv Map :=
    fun k c =>
      match c in const k
      return kit k Map (repeat (decodeClosed (Con c)))
      with
      | Nat => fun n => n
      | Unit => fun _ => tt
      | Prod => @doProd
      | Sum => @doSum
      end.

  Program Definition mConst : NGen Map :=
    nGen
    (fun tt => tt)
    (fun n => n)
    (@doSum)
    (@doProd).

  Definition gmap (k : kind) (t : ty k) : kit k Map (repeat (decodeClosed t)) :=
    ngen _ mConst.

  (* examples  of using gmap *)
  Compute gmap tprod nat nat (fun a => a + 1) bool bool (fun b => negb b) (1,true).
  (* tmaybe is a self defined type, definition in 'univ.v' *)
  Compute gmap tmaybe _ bool (fun _ => false) (inl tt). (* = inl () *)
  Compute gmap tmaybe nat nat (fun n => n + 1) (inr 3). (* = inr 4 *)
  (* teither is a self defined type, definition in 'univ.v' *)
  Compute gmap teither _ bool (fun _ => false)
                       _ bool (fun _ => true) (inl tt). (* = inl false *)

End dtgen.

Section aritydtgen.
  (* Example of a arity-generic and datatype-generic function. *)

  (** Definitions for arity-generic datatype-generic map
      - ngmap is partial so this version uses an error axiom.
      - a version is included that uses sums later (optNgmap). **)

  (* type definition needed for doubly generic map *)
  Fixpoint nMap {n : nat} (v : vec Type (S n)) : Type :=
    match v with
    | @vcons _ O x xs => x
    | @vcons _ (S n') x xs => x -> nMap xs
    end.

  (* chose to return last given n for nat consts *)
  Fixpoint cNat (n : nat) : kit Ty nMap (repeat (n:=S n) (decodeClosed (Con Nat))) :=
    let f := (fix cNat' (n' : nat)
      : kit Ty nMap (repeat (n:=S n') (decodeClosed (Con Nat))) :=
      match n' return kit Ty nMap (repeat (n:=S n') (decodeClosed (Con Nat))) with
      | O => O
      | S O => fun x => x
      | S (S m) => fun x y => cNat' m
    end) in
    match n return kit Ty nMap (repeat (n:=S n) (decodeClosed (Con Nat))) with
    | O => O
    | S O => fun x => x
    | S (S m) =>
        if Nat.odd m
        then fun x y => cNat m
        else fun x => f (S m)
    end.

  Fixpoint cUnit (n : nat)
    : kit Ty nMap (repeat (n:=S n) (decodeClosed (Con Unit))) :=
    match n with
    | O => tt
    | S n' => fun x => cUnit n'
    end.

  (* Error axiom for finishing defs in sums *)
  Axiom error : False.

  (* helper for defining left-side cases of sums *)
  Fixpoint cSumLeft (n : nat)
    : forall (va : vec Type (S n)), nMap va ->
    forall (vb : vec Type (S n)), nMap (zap (zap (repeat sum) va) vb).
  Proof.
    intros VA a VB. simpl.
    pose proof veq_hdtl (v:=VA) as pfa;
    pose proof veq_hdtl (v:=VB) as pfb.
    destruct n as [| n'].
    - rewrite pfa in a. simpl in a. apply (inl a).
    - intros x. destruct x as [l | r].
      + rewrite pfa in a; simpl in a.
        apply cSumLeft.
        pose proof a l as pa; apply pa.
      + exfalso; apply error.
  Defined.

  (* helper for defining right-side cases of sums *)
  Fixpoint cSumRight (n : nat)
    : forall (va : vec Type (S n)) (vb : vec Type (S n)),
    nMap vb -> nMap (zap (zap (repeat sum) va) vb).
  Proof.
    intros VA VB b. pose proof veq_hdtl (v:=VB) as pfb.
    destruct n as [| n'].
    - rewrite pfb in b. apply (inr b).
    - intros x; destruct x as [left | right].
      (* error case *)
      + exfalso; apply error.
      + rewrite pfb in b. simpl in b.
        pose proof b right as pb.
        pose proof cSumRight n' (vtl VA) (vtl VB) pb as pf.
        apply pf.
  Defined.

  (* case for sums in curried form  *)
  Definition cSum (n : nat)
    : forall (va : vec Type (S n)), nMap va
    -> forall (vb : vec Type (S n)), nMap vb
    -> nMap (zap (zap (repeat sum) va) vb).
  Proof.
    intros VA a VB b.
    destruct n as [| n'].
    (* chooses arbitrary case inr *)
    - simpl. rewrite veq_hdtl in b. simpl in b. apply (inr b).
    - intros x; destruct x as [lr | rt].
      + rewrite veq_hdtl in a. simpl in a.
        pose proof a lr as pfa.
        apply cSumLeft; apply pfa.
      + rewrite veq_hdtl in b. simpl in b.
        pose proof b rt as pfb.
        apply cSumRight; apply pfb.
   Defined.

  (* case for prods in curried form  *)
  Fixpoint cProd (n : nat)
    : forall (va : vec Type (S n)), nMap va
    -> forall (vb : vec Type (S n)), nMap vb
    -> nMap (zap (zap (repeat (decodeClosed (Con Prod))) va) vb).
      Proof.
        destruct n;
        intros VA a VB b;
        pose proof veq_hdtl (v:=VA) as pfa;
        pose proof veq_hdtl (v:=VB) as pfb.
        - apply pair.
          + rewrite pfa in a; apply a.
          + rewrite pfb in b; apply b.
        - simpl; intros pr.
          destruct pr as [pa pb].
          apply cProd.
          + rewrite pfa in a. apply a. apply pa.
          + rewrite pfb in b. apply b. apply pb.
      Defined.

  (* A simple tactic to simplify prod and sum consts. *)
  Ltac curryk const :=
    apply (curryKind (F Ty (F Ty Ty))); simpl; apply const.

  (* Combined cases for the generic constants *)
  Program Definition nmapConst {n : nat} : tyConstEnv (@nMap n) :=
    fun k c =>
      match c with
      | Nat => cNat _
      | Unit => cUnit _
      | Prod => ltac:(curryk (cProd (n:=n)))
      | Sum => ltac:(curryk (cSum (n:=n)))
      end.

  Definition nConst (n : nat) : NGen nMap (n:=n) :=
    nGen
    (cUnit _)
    (cNat _)
    (ltac:(curryk (cSum (n:=n))))
    (ltac:(curryk (cProd (n:=n)))).

  (* doubly generic map *)
  Definition ngmap (n : nat) (k : kind) (t : ty k)
    : kit k nMap (repeat (decodeClosed t)) :=
    ngen _ nConst (n:=n).

  (* Definitions for arity-generic datatype-generic map
     - This version uses option instead of an axiom.
     - Needs a lot of unnecessary sums *)

  Fixpoint optNMap {n : nat} (v : vec Type (S n)) : Type :=
    match v with
    | @vcons _ O x xs => x
    | @vcons _ (S n') x xs => x -> option (optNMap xs)
    end.

  (* nat constant for nmapconst  *)
  Program Fixpoint optNat (n : nat)
    : kit Ty optNMap (repeat (decodeClosed (Con Nat))) :=
    match n as n'
    return forall (pf : n=n'),
    kit Ty optNMap (repeat (n:=S n') (decodeClosed (Con Nat))) with
    | O => _
    | S n => _
    end eq_refl.
  Next Obligation.
    Proof.
      exact 0.
    Defined.
  Next Obligation.
    Proof.
      revert X.
      induction n as [| n' IHn']; intros x; apply Some.
      - exact x.
      - intros y. apply IHn'; exact y.
    Defined.

  (* unit constant for nmapconst *)
  Fixpoint optUnit (n : nat)
    : kit (n:=n) Ty optNMap (repeat (decodeClosed (Con Unit))).
  Proof.
    destruct n as [| n'].
    - simpl; exact tt.
    - intros x; apply Some. apply optUnit.
  Defined.

 Fixpoint optSumLeft (n : nat)
    : forall (va : vec Type (S n)), optNMap va ->
    forall (vb : vec Type (S n)), optNMap (zap (zap (repeat sum) va) vb).
  Proof.
    intros VA a VB. simpl.
    pose proof @veq_hdtl _ _ VA as pfa.
    destruct n as [| n'].
    - rewrite pfa in a. simpl in a. apply (inl a).
    - intros x; destruct x as [xl | xr].
      (* case for left side *)
      + rewrite pfa in a; simpl in a.
        apply a in xl; destruct xl as [somex |].
        (* case for some *)
        * apply Some; apply optSumLeft; apply somex.
        (* case for none *)
        * apply None.
      (* case for right side *)
      + apply None.
  Defined.

  Fixpoint optSumRight (n : nat)
    : forall (va : vec Type (S n)) (vb : vec Type (S n)),
    optNMap vb -> optNMap (zap (zap (repeat sum) va) vb).
  Proof.
    intros VA VB b. simpl.
    pose proof @veq_hdtl _ _ VB as pfb.
    destruct n as [| n'].
    - rewrite pfb in b; simpl in b. apply (inr b).
    - intros x; destruct x as [xl | xr].
      (* case for left side *)
      + apply None.
      (* case for right side *)
      + rewrite pfb in b; simpl in b.
        apply b in xr. destruct xr as [somex |].
        (* case for some *)
        * apply Some; apply optSumRight; apply somex.
        (* case for none *)
        * apply None.
  Defined.

  Definition optSum (n : nat)
    : forall (va : vec Type (S n)), optNMap va
    -> forall (vb : vec Type (S n)), optNMap vb
    -> optNMap (zap (zap (repeat sum) va) vb).
  Proof.
    intros VA a VB b.
    destruct n as [| n'].
    (* no arguments, chooses arbitrary case inr *)
    - simpl. rewrite veq_hdtl in b. simpl in b. apply (inr b).
    - intros x; destruct x as [lx | rx].
      + rewrite veq_hdtl in a; simpl in a.
        apply a in lx. destruct lx as [somex |].
        (* case for some *)
        * apply Some; apply optSumLeft; apply somex.
        (* case for none *)
        * apply None.
      + rewrite veq_hdtl in b; simpl in b.
        apply b in rx; destruct rx as [somex |].
        (* case for some *)
        * apply Some; apply optSumRight; apply somex.
        (* case for none *)
        * apply None.
  Defined.

  (* case for prods in curried form  *)
  Fixpoint optProd (n : nat)
    : forall (va : vec Type (S n)), optNMap va
    -> forall (vb : vec Type (S n)), optNMap vb
    -> optNMap (zap (zap (repeat (decodeClosed (Con Prod))) va) vb).
  Proof.
    destruct n;
    intros VA a VB b;
    pose proof @veq_hdtl _ _ VA as pfa;
    pose proof @veq_hdtl _ _ VB as pfb.
    - rewrite pfa in a; simpl in a.
      rewrite pfb in b; simpl in b.
      apply pair.
      (* inl case *)
      + apply a.
      (* inr case *)
      + apply b.
    - rewrite pfa in a; simpl in a.
      rewrite pfb in b; simpl in b.
      intros pr. destruct pr as [pa pb].
      apply a in pa. apply b in pb.
      destruct pa as [somea |].
      + destruct pb as [someb |].
        * apply Some; apply optProd.
          { apply somea. }
          { apply someb. }
        * apply None.
      + apply None.
  Defined.

  Definition optNMapConst {n : nat} : tyConstEnv (@optNMap n) :=
    fun k c =>
      match c with
      | Nat => optNat _
      | Unit => optUnit _
      | Prod => ltac:(curryk (optProd (n:=n)))
      | Sum => ltac:(curryk (optSum (n:=n)))
      end.

  Definition optNConst {n : nat} : NGen optNMap (n:=n) :=
    nGen
    (optUnit _)
    (optNat _)
    (ltac:(curryk (optSum (n:=n))))
    (ltac:(curryk (optProd (n:=n)))).

  (* doubly generic map WITH OPTION *)
  Definition optNgmap (n : nat) (k : kind) (t : ty k)
    : kit (n:=n) k optNMap (repeat (decodeClosed t)) :=
    ngen _ optNConst (n:=n).

End aritydtgen.

(* EXAMPLES *)

(* - ngmap *)

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
  (1,false). (* = (2, true) *)

Compute ngmap 2 tprod
  nat nat nat (fun x y => x + y)
  bool bool bool (fun x y => andb x y)
  (15,true) (4, false). (* = (19, false) *)

Compute ngmap 3 tprod
  _ _ _ _ (fun x y z => x + y + z)
  _ _ _ _ (fun x y z => andb (andb x y) z)
  (11,true) (2, true) (6, true). (* = (19, true) *)

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
  _ _ _ (fun x y => x + y)
  (inr 3) (inr 2). (* = inr 5 *)

(* - optNgmap *)

(* optNgmap aka ngmap with maybes examples. *)

Compute optNgmap 1 tprod
  _ _ (fun x => (Some (x + 1)))
  _ _ (fun _ => (Some true))
  (1,false). (* = Some (2, true) *)

Compute optNgmap 1 tsum
  _ _ (fun x => (Some (x + 1)))
  _ _ (fun _ => (Some true))
  (inl 1). (* = Some (inl 2) *)

(* ohh the beauty of it.. *)
Compute
  (match optNgmap 2 tsum
  _ _ _ (fun x => Some (fun y => (Some (y + 1))))
  _ _ _ (fun _ => Some (fun _ => (Some false)))
  (inl tt)
  with
  | Some x => x
  | _ => _
  end) (inl 1). (* = Some (inl 2) *)

(* nmap is partial, this is err since arguments use
   different constructors in a sum. *)
Compute
  (match optNgmap 2 tsum
  _ _ _ (fun x => Some (fun x => Some (x + 1)))
  _ _ _ (fun _ => Some (fun _ => Some false))
  (inl tt)
  with
  | Some x => x
  | _ => _
  end) (inr false). (* = None *)


Require Export init.
Require Import generic univ utils tactics.

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
Definition optngmap (n : nat) (k : kind) (t : ty k)
  : kit (n:=n) k optNMap (repeat (decodeClosed t)) :=
  ngen _ optNConst (n:=n).


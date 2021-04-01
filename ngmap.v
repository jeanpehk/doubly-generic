Require Export init.
Require Import generic univ utils tactics.

(* Example of an arity-generic and datatype-generic function. *)

(** - ngmap is partial so this version uses an error axiom.
    - a version that uses sums is included in `optngmap.v`.   **)

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

(* Combined cases for the generic constants *)
Definition nmapConst {n : nat} : tyConstEnv (@nMap n) :=
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


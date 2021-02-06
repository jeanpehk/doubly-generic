Set Implicit Arguments.
Set Universe Polymorphism.

From Coq Require Import Program.

Require Import generic univ utils.

(* generic helpers for making doubly generic defs *)

Fixpoint unkit (n : nat) (k : kind) (b : vec Type (S n) -> Type)
  : vec (decodeKind k) (S n) -> Type :=
    match k return vec (decodeKind k) (S n) -> Type with
    | Ty => fun vs => b vs
    | F k1 k2 => fun vs =>
        forall (a : vec (decodeKind k1) _),
        kit k1 b a ->
        unkit k2 b (zap vs a)
    end.

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

End dtgen.

(* Example of a arity-generic and datatype-generic function. *)
Section aritydtgen.

  (* type definition needed for doubly generic map *)
  Fixpoint funTy {n : nat} (v : vec Type (S n)) : Type :=
    match v with
    | @vcons _ O x xs => x
    | @vcons _ (S n') x xs => x -> funTy xs
    end.

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
      (* error case *)
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
      (* error case *)
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

  (* helper for defining prods *)
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
  (* CASE FOR NAT
    this just returns 0 for all,
     maybe change to return last nat given (like cNat) *)
  - induction n.
    + simpl. apply (cNat 0).
    + refine (fun x => _). apply IHn.
  (* CASE FOR UNIT *)
  - induction n.
    + apply tt.
    + refine (fun x => _). apply IHn.
  (* CASE FOR SUM *)
  - pose proof (kindCurry (F Ty (F Ty Ty))) as pf.
    apply pf. simpl. intros VA a VB b.
    pose proof hSum VA a VB b as hp. simpl in hp.
    apply hp.
  (* CASE FOR PROD *)
  - pose proof (kindCurry (F Ty (F Ty Ty))) as pf.
    apply pf. simpl. intros VA a VB b.
    pose proof hProd VA a VB b as hp. simpl in hp.
    apply hp.
  Defined.


  (* doubly generic map *)
  Definition ngmap (n : nat) (k : kind) (t : ty k)
    : kit k funTy (repeat (S n) (decodeClosed t)) :=
    specTerm t nmapConst.

  (* some test examples for unit map *)
  Compute ngmap 0 tunit. (* = () *)
  Compute ngmap 1 tunit tt. (* = () *)
  Compute ngmap 0 tnat. (* = 0 *)

  (* some test examples for nat map *)
  Compute ngmap 1 tnat 1. (* = 1 *)
  Compute ngmap 2 tnat 1 2. (* = 2 *)
  Compute ngmap 3 tnat 1 2 3. (* = 3 *)

  (* some test examples for prod map *)
  Compute ngmap 1 tprod _ _
    (fun x => x + 1) _ _ (fun _ => true) (1,false).
  Compute ngmap 2 tprod nat nat nat
    (fun x y => x + y) bool bool bool (fun x y => andb x y) (1,true) (2, false).
  Compute ngmap 3 tprod nat nat nat nat
    (fun x y z => x + y + z) bool bool nat nat
    (fun x y z => if andb x y then 0 else z)
    (1,true) (2, false) (1, 100). (* = (4, 100) *)

  (* some test examples for sum map *)
  Compute ngmap 1 tsum
    _ _ (fun x => x + 1)
    _ _ (fun _ => true)
    (inl 1). (* = inl 2 *)
  Compute ngmap 2 tsum nat nat nat
    (fun x y => x + y) bool bool bool (fun x y => andb x y)
    (inl 1) (inl 1).
  Compute ngmap 3 tsum nat nat nat nat
    (fun x y z => x + y + z) bool bool nat nat
    (fun x y z => if andb x y then 0 else z)
    (inr true) (inr false) (inr 4). (* = inr 4 *)

  (* some test examples for self defined tmaybe *)
  Compute ngmap 1 tmaybe _ bool (fun _ => false) (inl tt). (* = inl () *)
  Compute ngmap 2 tmaybe nat nat nat (fun x => fun y => x + y)
    (inr 3) (inr 2).

End aritydtgen.

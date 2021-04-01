From Coq Require Import Program List.

Import ListNotations.
Import EqNotations.

Require Export init.
Require Import generic univ gmap ngmap optngmap utils.

(* examples of defining types with the universe. *)

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

(** examples of gmap **)

Compute gmap tprod nat nat (fun a => a + 1) bool bool (fun b => negb b) (1,true).
(* tmaybe is a self defined type, definition in 'univ.v' *)
Compute gmap tmaybe _ bool (fun _ => false) (inl tt). (* = inl () *)
Compute gmap tmaybe nat nat (fun n => n + 1) (inr 3). (* = inr 4 *)
(* teither is a self defined type, definition in 'univ.v' *)
Compute gmap teither _ bool (fun _ => false)
                     _ bool (fun _ => true) (inl tt). (* = inl false *)

(** examples of ngmap **)

(* unit ngmap *)
Compute ngmap 0 tunit. (* = () *)
Compute ngmap 1 tunit tt. (* = () *)

(* nat ngmap *)
Compute ngmap 0 tnat. (* = 0 *)
Compute ngmap 1 tnat 1. (* = 1 *)
Compute ngmap 2 tnat 1 2. (* = 2 *)
Compute ngmap 3 tnat 1 2 3. (* = 3 *)

(* prod ngmap *)
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

(* sum ngmap *)
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

(* self defined tmaybe *)
Compute ngmap 1 tmaybe
  _ _ (fun _ => false)
  (inl tt). (* = inl () *)

Compute ngmap 2 tmaybe
  _ _ _ (fun x y => x + y)
  (inr 3) (inr 2). (* = inr 5 *)

(* examples for optngmap *)

(* prod optngmap *)
Compute optngmap 1 tprod
  _ _ (fun x => (Some (x + 1)))
  _ _ (fun _ => (Some true))
  (1,false). (* = Some (2, true) *)

(* sum optngmap *)
Compute optngmap 1 tsum
  _ _ (fun x => (Some (x + 1)))
  _ _ (fun _ => (Some true))
  (inl 1). (* = Some (inl 2) *)

(* ohh the beauty of it.. *)
Compute
  (match optngmap 2 tsum
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
  (match optngmap 2 tsum
  _ _ _ (fun x => Some (fun x => Some (x + 1)))
  _ _ _ (fun _ => Some (fun _ => Some false))
  (inl tt)
  with
  | Some x => x
  | _ => _
  end) (inr false). (* = None *)


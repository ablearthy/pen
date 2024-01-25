From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Print True.

Theorem true_is_true : True.
Proof.
  exact: I.
Qed.

Definition true_is_true' : True := I.

Eval compute in true_is_true.
Eval compute in true_is_true'.

Print False.

Theorem one_eq_two : False -> 1 = 2.
Proof.
  (* exact: False_ind. *)
  case.
Qed.

Theorem imp_trans {P Q R} : (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  move=> pq qr p.
  apply: (qr (pq p)).
Qed.


Module Connectives.
Variables P Q R : Prop.

Goal P /\ Q -> P.
Proof.
  case=>//.
Qed.

Goal P \/ Q -> Q \/ P.
Proof.
  case.
  by right.
  by left.
Qed.

Theorem absurd : P -> ~ P -> Q.
Proof.
  by [].
Qed.

Theorem contraP : (P -> Q) -> ~ Q -> ~ P.
Proof.
  by move=> /[swap] ; apply: comp.
Qed.

Locate "exists".
Print ex.

Theorem ex_imp_ex A (S T : A -> Prop)
  : (exists a : A, S a)
  -> (forall x : A, S x -> T x)
  -> exists b : A, T b.
Proof.
  case=> a Sa f.
  exists a.
  by apply: f.
Qed.

End Connectives.

(* Module Classic.
Require Import Classical_Prop.

Print classic.
Check imply_to_or.

End Classic. *)

Set Printing Universes.
Check bool.
Check Set.
Check Prop.
Check Type.

Definition S := forall T, list T.

Theorem all_imp_ist A (P Q : A -> Prop) :
  (forall x, P x -> Q x)
  -> (forall y, P y)
  -> (forall z, Q z).
Proof.
  move=> pq p z.
  apply: pq.
  apply: p.
Qed.

Theorem or_distributes_over_and P Q R :
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  split.
  case.
  split ; by left.
  case.
  split ; by right.
  case.
  case.
  by left.
  move=> q.
  by case ; [left | right].
Qed.

Inductive my_ex A (S : A -> Prop) : Prop := my_ex_intro x of S x.

Goal forall A (S : A -> Prop), my_ex S <-> exists y: A, S y.
Proof.
  split ; case=> x p ; by split with x.
Qed.

Theorem dist_exists_or (X : Type) (P Q : X -> Prop) :
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  split.
  case=> x.
  case ; [left | right] ; by exists x.
  case ; case=> x ; exists x ; by [left | right].
Qed.

Theorem two_is_three A
  : (exists x : A, (forall R : A -> Prop, R x))
  -> 2 = 3.
Proof.
  case=> x R.
  apply: R.
Qed.

Definition dys_imp (P Q: Prop) := (P -> Q) -> (Q -> P).
Definition dys_contrap (P Q: Prop) := (P -> Q) -> (~P -> ~Q).

Theorem di_false: (forall P Q: Prop, dys_imp P Q) -> False.
Proof.
  move=> d.
  apply: d.
  case.
  by [].
Qed.


Theorem dc_false: (forall P Q: Prop, dys_contrap P Q) -> False.
Proof.
  move=> d.
  apply: (d False True) ; by [].
Qed.

Theorem excluded_middle_irrefutable: forall (P : Prop), ~ ~(P \/ ~ P).
Proof.
  move=> P /[dup] D1 D2.
  apply: D1. (* man accepts devil's statement *)
  right.     (* devil chooses (b) *)
  move=> a.  (* man gets `a` *)
  apply: D2. (* man accepts devil's statement *)
  by left.   (* devil chooses (a) *)
Qed.

Theorem not_forall_exists A (P : A -> Prop): 
  (forall x: A, P x) -> ~(exists y: A, ~ P y).
Proof.
  move=> p.
  case=> x l.
  apply: l.
  apply: (p x).
Qed.

Definition excluded_middle := forall P: Prop, P \/ ~P.

Theorem not_exists_forall :
  excluded_middle -> forall (X: Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  move=> lem X P p x.
  case: (lem (P x))=>//.
  move=> e.
  apply: False_ind.
  apply: p.
  by exists x.
Qed.
  

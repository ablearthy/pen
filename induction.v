From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Variable P : nat -> Prop.

Fixpoint nat2_ind_fix (P0 : P 0) (P1 : P 1) (Pn : forall n, P n -> P n.+2) (n : nat) : P n :=
  match n with
  | 0 => P0
  | 1 => P1
  | m.+2 => Pn m (nat2_ind_fix P0 P1 Pn m)
  end.


Inductive nat2_ind_inductive n : Prop :=
  | nat2_ind_inductive0 of n = 0
  | nat2_ind_inductive1 of n = 1
  | nat2_ind_inductiven n' of n = n'.+2 & nat2_ind_inductive n'.

Print nat2_ind_fix.
Print nat2_ind_inductive_ind.

Print nat_ind.

Lemma nat2_ind :
  P 0 -> P 1 -> (forall n, P n -> P (n.+2)) -> forall n, P n.
Proof.
  move=> P0 P1 Pn n.
  (* TODO *)
Admitted.
  
  

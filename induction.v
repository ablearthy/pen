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
  
  
(* Sum *)

Fixpoint sum (l : seq nat) : nat :=
  match l with
  | [::] => 0
  | x :: xs => x + sum xs
  end.

Fixpoint sum_tail' (acc : nat) (l : seq nat) : nat :=
  match l with
  | [::] => acc
  | x :: xs => sum_tail' (acc + x) xs
  end.
    
Definition sum_tail := sum_tail' 0.

Theorem sum_tail_correct (l : seq nat) : sum_tail l = sum l.
Proof.
  elim: l=>//=.
  move=> x xs.
  rewrite /sum_tail=>//=.
  rewrite add0n.
Abort.

Lemma sum_tail'_sum (l : seq nat) (n acc : nat) : sum_tail' (acc + n) l = n + sum_tail' acc l.
Proof.
  elim: l acc=>//=.
  by move=> acc ; rewrite addnC.
  move=> x xs H acc.
  by rewrite -addnA [n+x]addnC addnA (H (acc + x)).
Qed.

Theorem sum_tail'_correct (l : seq nat) (acc : nat) : sum_tail' acc l = acc + sum l.
Proof.
  elim: l=>//=.
  by rewrite addn0.
  move=> x xs.
  rewrite [x + _]addnC addnA.
  move=><-.
  by rewrite [sum_tail' _ _ + _]addnC sum_tail'_sum.
Qed.

Theorem sum_tail_correct (l : seq nat) : sum_tail l = sum l.
Proof.
  by rewrite -[sum _]add0n /sum_tail sum_tail'_correct.
Qed.

From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Lemma andb_true_elim b c: b && c -> c = true.
Proof.
  (* move/andP.
  case=> _.
  by case: c. *)

  (* case: c ; first by []. *)
  
  (* case: c; [by case: b | by []]. *) (* doesn't work *)

  (* case: c; [by [] | by case: b]. *)
  
  by do ![done | case: b | case: c].
Qed.


Definition is_zero n := n == 0.


Lemma is_zero_paradox: is_zero 1 -> False.
Proof. done. Show Proof. Qed.

Inductive evenP n : Prop := EvenZero of n = 0 | EvenSS m of m.+2 = n & evenP m.

Fixpoint evenb n :=
  match n with
  | m.+2 => evenb m
  | l => l == 0
  end.

Lemma evenP_contra n : evenP (n + 1 + n) -> False.
Proof.
  elim: n.
  rewrite addn0 add0n.
  case=>//=.
  move=> n H.
  rewrite [_ + n.+1]addnS [n.+1 + _ + _]addnCAC [_ + n.+1]addnS.
  move=> H1.
  apply: H.
  case: H1=>[|m Hm] //=.
  suff: m = (n + 1 + n).
  by move=>->.
  by rewrite -[m]subn0 -(subnDr 2) addn2 Hm -addn2 subnDr subn0.
Qed.

Lemma evenb_contra n: evenb (n + 1 + n) -> False.
Proof.
  elim: n=>[|m Hm] //.
  rewrite [_ + m.+1]addnS [m.+1 + _ + _]addnCAC [_ + m.+1]addnS.
  by rewrite /evenb.
Qed.

Lemma evenP_plus n m : evenP n -> evenP m -> evenP (n + m).
Proof.
  elim=>n'.
  by move=>->.
  move=> m' <- H1 H2 H3; rewrite addnC !addnS addnC.
  constructor 2 with (m' + m)=>//=.
  by apply: H2.
Qed.

Lemma evenb_plus n m : evenb n -> evenb m -> evenb (n + m).
Proof.
  move: (leqnn n).
  elim: n {-2}n.
  - by case=>//=.
  move=> n Hn.
  case=>//.
  case=> n0 //.
  by move /ltnW /Hn.
Qed.

Fixpoint nat2_ind (P: nat -> Type) (P0 : P 0) (P1 : P 1) (Pn : forall n, P n -> P (n.+2)) n: P n
  := match n with
  | 0 => P0
  | 1 => P1
  | m.+2 => Pn m (nat2_ind P0 P1 Pn m)
  end.

Lemma nat2_ind' (P: nat -> Prop): 
  P 0 -> P 1 -> (forall n, P n -> P (n.+2)) -> forall n, P n.
Proof.
  move=> P0 P1 Pn n.
  suff: (P n /\ P (n.+1)).
  by case.
  elim: n=>//= n.
  by case=> H2 H3 ; split ; [|apply: Pn].
Qed.


Lemma evenb_plus2 n m : evenb n -> evenb m -> evenb (n + m).
Proof.
  by elim/nat2_ind: n.
Qed.


Fixpoint div2 n := if n is p.+2 then (div2 p).+1 else 0.

Lemma div2_le n : div2 n <= n.
Proof.
  suff: ((div2 n <= n) /\ (div2 n.+1 <= n.+1)) by case.
  elim: n=>// n.
  case=> H1 H2.
  split=>//=.
  apply: (leq_trans H1 (leqnSn n)).
Qed.

Lemma div2_le2 n : div2 n <= n.
Proof.
  elim/nat2_ind: n=>//=.
  move=> n Hn.
  apply: (leq_trans Hn (leqnSn n)).
Qed.

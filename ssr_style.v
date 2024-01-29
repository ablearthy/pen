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


Inductive beautiful n : Prop :=
  | b_0 of n = 0
  | b_3 of n = 3
  | b_5 of n = 5
  | b_sum n' m' of beautiful n' & beautiful m' & n = n' + m'.

Lemma b_timesm n m : beautiful n -> beautiful (m * n).
Proof.
  elim.
  - move=> n' ->.
    by rewrite muln0 ; constructor.
  - move=> n' ->.
    elim: m.
    by constructor.
  - move=> {}n' Hn'.
    rewrite -[n'.+1]addn1 mulnDl mul1n.
    constructor 4 with (n' := n' * 3) (m' := 3)=>//=.
    by constructor.
  - move=> {}n'->.
    elim: m.
    by rewrite mul0n ; constructor.
    move=> {}n' Hn'.
    rewrite -[n'.+1]addn1 mulnDl mul1n.
    constructor 4 with (n' := n' * 5) (m' := 5)=>//=.
    by constructor.
  - move=> n0 n' m' Hn' Hmn' Hm' Hmm'->.
    rewrite mulnDr.
    by constructor 4 with (n' := m * n') (m' := m * m')=>//=.
Qed.

Lemma b_timesm2 n m : beautiful n -> beautiful (m * n).
Proof.
  elim: m.
  by rewrite mul0n ; constructor.
  move=> n' Hn Hn2.
  rewrite -addn1 mulnDl mul1n.
  constructor 4 with (n' := n' * n) (m' := n)=>//=.
  by apply: Hn.
Qed.

Inductive gorgeous n : Prop :=
  | g_0 of n = 0
  | g_plus3 m of gorgeous m & n = m + 3
  | g_plus5 m of gorgeous m & n = m + 5.

Lemma gorgeous_plus13 n: gorgeous n -> gorgeous (n + 13). 
Proof.
  constructor 2 with (n + 10) ; last by rewrite -addnA.
  constructor 3 with (n + 5) ; last by rewrite -addnA.
  by constructor 3 with n.
Qed.

Lemma gorgeous_plus n m : gorgeous n -> gorgeous m -> gorgeous (n + m).
Proof.
  elim.
  - by move=>_ ->.
  - move=> n' m' gm' H-> /H H1.
    by constructor 2 with (m' + m) ; last by rewrite addnACl [3 + _]addnC [m + m']addnC.
  - move=> n' m' gm' H-> /H H1.
    by constructor 3 with (m' + m) ; last by rewrite addnACl [5 + _]addnC [m + m']addnC.
Qed.

Lemma beautiful_gorgeous n : beautiful n -> gorgeous n.
Proof.
  elim.
  - by move=> _ -> ; constructor.
  - move=> _ -> ; by constructor 2 with 0=>//= ; constructor.
  - move=> _ -> ; by constructor 3 with 0=>//= ; constructor.
  - move=> n0 n' m' _ gn' _ gm' ->.
    by apply: gorgeous_plus.
Qed.

Lemma g_times2 n : gorgeous n -> gorgeous (n * 2).
Proof.
  elim.
  - move=> _ -> ; by constructor.
  - move=> n' m g g2 ->.
    rewrite mulnDl.
    constructor 2 with (m * 2 + 3).
    constructor 2 with (m * 2)=>//=.
    by rewrite -addnA.
  - move=> n' m g g2 ->.
    rewrite mulnDl.
    constructor 3 with (m * 2 + 5).
    constructor 3 with (m * 2)=>//=.
    by rewrite -addnA.
Qed.

Lemma gorgeous_beautiful n : gorgeous n -> beautiful n.
Proof.
  elim.
  - by move=> _-> ; constructor.
  - move=> n0 m _ b ->.
    constructor 4 with (n' := m) (m' := 3)=>//= ; last by constructor.
  - move=> n0 m _ b ->.
    constructor 4 with (n' := m) (m' := 5)=>//= ; last by constructor.
Qed.

Definition gorgeous_b n : bool :=
  match n with
  | 1 | 2 | 4 | 7 => false
  | _ => true
  end.
    
Fixpoint div3 n :=
  match n with
  | 0 | 1 | 2 => 0
  | n.+3 => (div3 n).+1
  end.
    
Fixpoint nat3_ind (P : nat -> Prop) (P0 : P 0) (P1 : P 1) (P2 : P 2)
  (Pn : forall n, P n -> P (n.+3)) (n : nat) : P n :=
  match n with
  | 0 => P0
  | 1 => P1
  | 2 => P2
  | m.+3 => Pn m (nat3_ind P0 P1 P2 Pn m)
  end.

Lemma repr3 n : n > 7 -> exists k, [\/ n = 3 * k + 8, n = 3 * k + 9 | n = 3 * k + 10].
Proof.
  move: n.
  do 8! case=>//=.
  move=> n _.
  exists (div3 n).
  elim/nat3_ind: n.
  - by constructor 1.
  - by constructor 2.
  - by constructor 3.
  - move=> n.
    case=> prf.
    - constructor 1=>//=.
      by rewrite -[(div3 _).+1]addn1 mulnDr muln1 -addnA [3 + _]addnC addnA addn3 prf.
    - constructor 2=>//=.
      by rewrite -[(div3 _).+1]addn1 mulnDr muln1 -addnA [3 + _]addnC addnA addn3 prf.
    - constructor 3=>//=.
      by rewrite -[(div3 _).+1]addn1 mulnDr muln1 -addnA [3 + _]addnC addnA addn3 prf.
Qed.

Lemma gorgeous3 n : gorgeous (3 * n).
Proof.
  apply: beautiful_gorgeous.
  rewrite mulnC.
  apply: b_timesm.
  by constructor.
Qed.

Lemma gorgeous8 : gorgeous 8.
Proof.
  constructor 3 with 3 ; last by [].
  constructor 2 with 0 ; last by [].
  by constructor.
Qed.

Lemma gorgeous9 : gorgeous 9.
Proof.
  constructor 2 with 6 ; last by [].
  constructor 2 with 3 ; last by [].
  constructor 2 with 0 ; last by [].
  by constructor.
Qed.

Lemma gorgeous10 : gorgeous 10.
Proof.
  constructor 3 with 5 ; last by [].
  constructor 3 with 0 ; last by [].
  by constructor.
Qed.

Lemma gorgeous_criteria n : n > 7 -> gorgeous n.
Proof.
  case/repr3=>k ; case=>-> ; apply: gorgeous_plus ; try by apply: gorgeous3.
  - by apply: gorgeous8.
  - by apply: gorgeous9.
  - by apply: gorgeous10.
Qed.

Lemma gorgeous_refl' n : n > 7 -> reflect (gorgeous n) true.
Proof.
  constructor.
  by apply: gorgeous_criteria.
Qed.

Lemma not_gorgeous1 : ~ (gorgeous 1).
Proof.
  case=> m //= ; move=> gm /eqP ; do ?[rewrite addnS eqSS] ; by rewrite addnS.
Qed.
  
Lemma not_gorgeous2 : ~ (gorgeous 2).
Proof.
  case=> m //= ; move=> gm /eqP ; do ?[rewrite addnS eqSS] ; by rewrite addnS.
Qed.

Lemma not_gorgeous4 : ~ (gorgeous 4).
Proof.
  case=> m //= ; move=> gm /eqP ; do ?[rewrite addnS eqSS] ; try by rewrite addnS.
  rewrite addn0.
  move/eqP.
  move: gm=> /[swap] <-.
  by exact: not_gorgeous1.
Qed.

Lemma not_gorgeous7 : ~ (gorgeous 7).
Proof.
  case=> m //= ; move=> gm /eqP ; do ?[rewrite addnS eqSS] ; rewrite addn0 ; move/eqP ; move: gm=> /[swap] <-.
  by exact: not_gorgeous4.
  by exact: not_gorgeous2.
Qed.

Lemma gorg_refl n : reflect (gorgeous n) (gorgeous_b n).
Proof.
  case: n.
  by constructor ; constructor.
  case.
  by constructor ; apply: not_gorgeous1.
  case.
  by constructor ; apply: not_gorgeous2.
  case.
  by constructor ; apply: gorgeous3 1.
  case.
  by constructor ; apply: not_gorgeous4.
  case.
  by constructor ; constructor 3 with 0 ; constructor=>//=.
  case.
  by constructor ; apply: gorgeous3 2.
  case.
  by constructor ; apply: not_gorgeous7.
  move=> n.
  by apply: gorgeous_refl'.
Qed.


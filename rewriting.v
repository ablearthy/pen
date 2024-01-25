From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Locate "_ = _".
Print eq.

Inductive my_eq A (x : A) : A -> Prop := my_eq_refl : my_eq x x.
Notation "x === y" := (my_eq x y) (at level 70).

Lemma my_eq_sym A (x y : A) : x === y -> y === x.
Proof.
  by case.
Qed.

Lemma my_eq_Leibniz A (x y : A) (P : A -> Prop) : x === y -> P x -> P y.
Proof. by case. Qed.

Goal 2 === 1 -> False.
Proof.
  move=> H.
  pose D x := if x is 2 then False else True.
  by case: H (I : D 1).
Qed.


Definition double A (f : A -> A) (x : A) : A := f (f x).

Fixpoint nat_iter (n : nat) {A} (f : A -> A) (x : A) : A
  := if n is u.+1 then f (nat_iter u f x) else x.
      
Lemma double2 A (x : A) f t
  : t = double f x -> double f t = nat_iter 4 f x.
Proof.
  by move=>->.
Qed.

Definition f x y := x + y.

Goal forall x y, x + y + (y + x) = f y x + f y x.
Proof.
  move=> x y.
  rewrite /f.
  congr (_ + _).
  by apply: addnC.
Qed.


Goal forall x y z, (x + (y + z)) = (z + y + x).
Proof.
  move=> x y z.
  by rewrite [x + _]addnC [y + _]addnC.
Qed.


Lemma addnCA: forall m n p, m + (n + p) = n + (m + p).
Proof.
  move=> m n.
  by elim: m=> [| m Hm] p ; rewrite ?add0n ?addSnnS -?addnS.
Qed.
  

Lemma addnC: forall m n, m + n = n + m.
Proof.
  move=> m n.
  by rewrite -{1}[n]addn0 addnCA addn0.
Qed.

Goal forall n m, (m <= n) /\ (m > n) -> False.
Proof.
  move=> n m ; case.
  elim: m n=> [| m Hm] n //.
  move=> /[dup] kek.
  rewrite -[n](ltn_predK kek).
  move=> /[swap] /ltnSE /[swap].
  by move: (Hm n.-1).
Qed.

  
Goal forall n m, (m <= n) /\ (m > n) -> False.
Proof.
  move=> m n ; case.
  elim: m n => [ | m IHm ] [ | n] //.
  exact: IHm n.
Qed.

Definition maxn m n := if m < n then n else m.

Inductive leq_xor_gtn m n : bool -> bool -> Set :=
  | LeqNotGtn of m <= n : leq_xor_gtn m n true false
  | GtnNotLeq of n < m  : leq_xor_gtn m n false true.

Lemma leqP m n : leq_xor_gtn m n (m <= n) (n < m).
Proof.
  rewrite ltnNge.
  by case X: (m <= n) ; constructor=>// ; rewrite ltnNge X.
Qed.

Goal forall n m, (m <= n) /\ (m > n) -> False.
Proof.
  move=> n m.
  move/andP.
  case: leqP ; by [].
Qed.

Lemma max_is_max m n: n <= maxn m n /\ m <= maxn m n.
Proof.
  rewrite /maxn.
  case: (leqP n m)=>//.
  by split ; [| apply: ltnW ].
Qed.
  


Goal 1 === 2 -> False.
Proof.
  move=> H.
  pose D x := if x is 1 then False else True.
  by case: H (I : D 2).
Qed.

Lemma rewrite_is_fun T (f : T -> T -> T) (a b c : T):
  commutative f -> associative f ->
  f (f b a) c = f a (f c b).
Proof.
  move=> comm assoc.
  by rewrite [f c b]comm [f a _]assoc [f b a]comm.
Qed.

Lemma max_l m n: n <= m -> maxn m n = m.
Proof.
  rewrite /maxn.
  case: leqP=>//.
Qed.
    
Lemma succ_max_distr_r n m : (maxn n m).+1 = maxn (n.+1) (m.+1).
Proof.
  rewrite /maxn.
  case: leqP.
  by rewrite ltnNge ltnS =>->//.
  move=> n_le_m.
  suff: n.+1 < m.+1.
  by move=>->.
  by [].
Qed.

Lemma plus_max_distr_l m n p: maxn (p + n) (p + m) = p + maxn n m.
Proof.
  rewrite /maxn.
  case: leqP=>//.
  by rewrite leq_add2l ltnNge /negb =>->.
  by rewrite ltn_add2l =>->.
Qed.

Inductive nat_rels m n : bool -> bool -> bool -> Set :=
  | CompareNatLt of m < n : nat_rels m n true false false
  | CompareNatGt of m > n : nat_rels m n false true false
  | CompareNatEq of m = n : nat_rels m n false false true.

Lemma natrelP m n : nat_rels m n (m < n) (n < m) (m == n).
Proof.
  rewrite ltn_neqAle eqn_leq ; case: ltnP ; first by constructor.
  by rewrite leq_eqVlt orbC; case: leqP; constructor; first exact/eqnP.
Qed.

Definition minn m n := if m < n then m else n.

Lemma addn_min_max m n : minn m n + maxn m n = m + n.
Proof.
  rewrite /minn /maxn.
  by case: natrelP ; rewrite addnC.
Qed.
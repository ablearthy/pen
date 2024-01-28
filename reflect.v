From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(* Set Printing Coercions. *)

Goal forall P Q R, P -> (P -> Q -> R) -> Q -> R.
Proof.
  by move=> P Q R p /(_ p).
Qed.

Print andb.

Definition XOR (P Q: Prop) := (P \/ Q) /\ ~(P /\ Q).

Definition xorb b := if b then negb else id.


Lemma xorP_gen (b1 b2 : bool)(P1 P2: Prop): 
  reflect P1 b1 -> reflect P2 b2 -> reflect (XOR P1 P2) (xorb b1 b2).
Proof.
  case=>H1 ; case=> H2 //= ; constructor.
  - by case=>_ /(_ (conj H1 H2)).
  - split.
    by left.
    by case=>_ /H2.
  - split.
    by right.
    by case=> /H1.
  - by case; case.
Qed.

Lemma xorP (b1 b2 : bool): reflect (XOR b1 b2) (xorb b1 b2).
Proof.
  exact (xorP_gen idP idP).
Qed.

Definition XOR' (P Q: Prop) := (P /\ ~Q) \/ (~P /\ Q).

Lemma XORequiv P Q: XOR P Q <-> XOR' P Q.
Proof.
  split.
  - case=> H1 H2.
    case: H1=> x.
    - left ; split=>//.
      move=> q.
      by apply: H2.
    - right ; split=>//.
      move=> p.
      by apply: H2.
  - case=> H ; split ; case: H.
    - by left.
    - by move=> _ q ; case.
    - by right.
    - by move=> p _ ; case.
Qed.

Lemma xorP' (b1 b2 : bool): reflect (XOR' b1 b2) (xorb b1 b2).
Proof.
  by case: xorP ; move/XORequiv ; constructor.
Qed.

Lemma xorbC (b1 b2: bool) : (xorb b1 b2) = (xorb b2 b1). 
Proof.
  by case: b1 ; case: b2=>//=.
Qed.

Lemma xorbA (b1 b2 b3: bool) : (xorb (xorb b1 b2) b3) = (xorb b1 (xorb b2 b3)). 
Proof.
  by case: b1 ; case: b2 ; case: b3=> //=.
Qed.

Lemma xorCb (b1 b2: bool) : (XOR b1 b2) <-> (XOR b2 b1). 
Proof.
  by split ; move/xorP=> H ; apply/xorP ; rewrite xorbC.
Qed.

Lemma xorAb (b1 b2 b3: bool) : (XOR (XOR b1 b2) b3) <-> (XOR b1 (XOR b2 b3)). 
Proof.
  split.
  - move/(xorP_gen (xorP _ _) idP)=> H.
    apply/(xorP_gen idP (xorP _ _)).
    by rewrite -xorbA.
  - move/(xorP_gen idP (xorP _ _))=> H.
    apply/(xorP_gen (xorP _ _) idP).
    by rewrite xorbA.
Qed.

Goal forall (b1 b2 b3 : bool), xorb b1 (xorb b2 b3) = xorb (xorb b1 b2) b3.
Proof.
  case ; case ; case=>//=.
Qed.


Lemma ExistsUnique1 A (P : A -> A -> Prop): 
  (exists !x, exists y, P x y) -> 
  (exists !x, exists y, P y x) ->
  (exists !x, exists !y, P x y).
Proof.
  case=> x1 ; case ; case=> y1 Px1y1 ; move=> prf1.
  case=> x2 ; case ; case=> y2 Py2x2 ; move=> prf2.
  exists x1 ; split.
  - exists x2 ; split.
    - suff: x2 = y1.
      - by move=> eq ; rewrite eq.
      - by apply: prf2 ; exists x1.
    - by move=> _x Px1_x ; apply: prf2 ; exists x1.
  - move=> _x.
    case=> _y [P_x_y _].
    by apply: prf1 ; by exists _y.
Qed.

Definition Q x y : Prop := 
  (x == true) && (y == true) || (x == false).

Lemma not_qlm : (exists !x, exists !y, ~ (Q x y)).
Proof.
  exists true.
  split.
  exists false.
  split.
  - by rewrite /Q.
    case=>pred //=.
    rewrite /Q.
    suff: False.
    - by [].
    - by apply: pred.
  - case=>H //=.
    suff: False=>//=.
    case: H=> y.
    case=> a _.
    apply: a.
    case: y ; by [].
Qed.

Lemma qlm : (exists !x, exists !y, Q x y).
Proof.
  exists true.
  split.
  - exists true.
    split.
    by [].
    by case.
  - case=>//=.
    case ; case ; case=> _.
    by apply.
    move=> H.
    apply: Logic.eq_sym.
    by apply: (H true).
Qed.
    
Lemma ExistsUnique2 : 
  (forall A (P : A -> A -> Prop),
   (exists !x, exists !y, P x y) ->
   (exists !x, exists y, P x y) /\ (exists !x, exists y, P y x)) ->
  False.
Proof.
  move=> /(_ _ _ qlm) ; case.
  case. case ; case=> _ prf _.
  - suff: true = false=>//=.
    apply: prf.
    by exists false.
  - suff: false = true=>//=.
    apply: prf.
    by exists true.
Qed.


    

    
    
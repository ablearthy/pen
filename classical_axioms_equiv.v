From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition peirce := forall P Q : Prop, ((P -> Q) -> P) -> P.
Definition dne := forall P : Prop, ~ ~ P -> P.
Definition lem := forall P : Prop, P \/ ~ P.
Definition dmlnan := forall P Q : Prop, ~ (~ P /\ ~ Q) -> P \/ Q.
Definition implies_to_or := forall P Q : Prop, (P -> Q) -> (~ P \/ Q).

Definition not_not_intro (P : Prop) (p : P) : ~ ~ P := (fun notp => notp p).

Definition const [P Q : Prop] (a : P) (b : Q) := a.

Lemma peirce_imp_dne : peirce -> dne.
Proof.
  move=> prc P f.
  exact: (prc P False (comp (False_ind P) f)).
Qed.

Lemma dmlnan_imp_peirce : dmlnan -> peirce.
Proof.
  move=> d P Q pqp.
  suff: (P -> Q) \/ P.
  case ; by [].
  apply: d.
  case.
  by apply: contra_not.
Qed.

Lemma dne_imp_dmlnan : dne -> dmlnan.
Proof.
  move=> d P Q.
  suff:  ~ (P \/ Q) -> ~ ~ (~ P /\ ~ Q).
  move=> tmp1 tmp2.
  move: (contra_not tmp1)=> tmp3.
  apply: d.
  apply: tmp3.
  apply: not_not_intro.
  by [].
  move=> tmp1.
  apply: not_not_intro.
  apply: conj.
  exact: (fun x => tmp1 (or_introl x)).
  exact: (fun x => tmp1 (or_intror x)).
Qed.

Lemma lem_imp_dne : lem -> dne.
Proof.
    move=> l P.
    case: (l P).
    by [].
    move=> f1 f2.
    exact ((comp (False_ind P) f2) f1).
Qed.

Lemma implies_to_or_imp_lem : implies_to_or -> lem.
Proof.
  move=> ito P.
  move: (ito P P id).
  rewrite or_comm.
  by [].
Qed.

Lemma peirce_imp_implies_to_or : peirce -> implies_to_or.
Proof.
  move=> prc P Q pq.
  suff: P \/ ~ P.
  case.
  move=> p.
  exact: (or_intror (pq p)).
  by apply: or_introl.
  exact: (((comp dne_imp_dmlnan peirce_imp_dne) prc) P (~ P) (fun (x : (~ P /\ ~ ~ P)) => (proj2 x) (proj1 x))).
Qed.

(* ------------------------------------------------------------------------- *)

Definition comp4 {A B C D E} (a : A -> B) (b : B -> C) (c : C -> D) (d : D -> E)
  := comp d (comp c (comp b a)).

Theorem peirce_iff_dne : peirce <-> dne.
Proof.
  split.
  exact: peirce_imp_dne.
  exact: comp dmlnan_imp_peirce dne_imp_dmlnan.
Qed.

Theorem dne_iff_lem : dne <-> lem.
Proof.
  split.
  exact: comp4 dne_imp_dmlnan dmlnan_imp_peirce peirce_imp_implies_to_or implies_to_or_imp_lem.
  exact: lem_imp_dne.
Qed.

Theorem lem_iff_dmlnan : lem <-> dmlnan.
Proof.
  split.
  exact: comp dne_imp_dmlnan lem_imp_dne.
  rewrite -dne_iff_lem.
  exact: comp peirce_imp_dne dmlnan_imp_peirce.
Qed.

Theorem dmlnan_iff_implies_to_or : dmlnan <-> implies_to_or.
Proof.
  split.
  move=> d.
  apply: peirce_imp_implies_to_or.
  by rewrite peirce_iff_dne dne_iff_lem lem_iff_dmlnan.
  rewrite -lem_iff_dmlnan.
  by exact implies_to_or_imp_lem.
Qed.
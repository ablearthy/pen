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
  apply: prc.
  by move=> /f.
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
  move=> d P Q p.
  apply: d.
  move: p.
  apply: contra_not.
  split.
  by move=> /or_introl.
  by move=> /or_intror.
Qed.

Lemma lem_imp_dne : lem -> dne.
Proof.
    move=> l P.
    by case: (l P).
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
  by right ; apply (pq p).
  by left.
  apply: ((comp dne_imp_dmlnan peirce_imp_dne) prc).
  by apply: and_rect.
Qed.

(* ------------------------------------------------------------------------- *)

Theorem peirce_iff_dne : peirce <-> dne.
Proof.
  split.
  exact: peirce_imp_dne.
  exact: comp dmlnan_imp_peirce dne_imp_dmlnan.
Qed.

Theorem dne_iff_lem : dne <-> lem.
Proof.
  split.
  rewrite -peirce_iff_dne.
  move=> p.
  apply: implies_to_or_imp_lem.
  apply: peirce_imp_implies_to_or.
  by [].
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
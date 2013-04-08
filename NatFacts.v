Require Import Utf8.
Require Import Omega.
Require Import Eqdep Eqdep_dec.

Set Implicit Arguments.

(** * Facts about Natural Numbers *)
Section le_rel.
  Lemma le_refl n : n <= n. trivial. Qed.

  Lemma le_trans : forall n m p, n <= m -> m <= p -> n <= p.
    intuition.
  Qed.
End le_rel.

Add Parametric Relation : _ @le
  reflexivity proved by le_refl
  transitivity proved by le_trans
    as le_rel.

(** Proof thanks to Robbert Krebbers <mailinglists@robbertkrebbers.nl>
    on coq-club *)

Lemma nat_le_proofs_unicity : ∀ (x y : nat) (p q : x <= y), p = q.
Proof.
  assert (∀ x y (p : x ≤ y) y' (q : x ≤ y'),
            y = y' → eq_dep nat (le x) y p y' q) as aux;
  [ | intros x y p q; now apply (eq_dep_eq_dec eq_nat_dec), aux ].
  fix 3. intros x ? [|y p] ? [|y' q].
  * easy.
  * clear nat_le_proofs_unicity. omega.
  * clear nat_le_proofs_unicity. omega.
  * injection 1. intros Hy. now case (@nat_le_proofs_unicity x y p y' q Hy).
Qed.

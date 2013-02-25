(** printing '*' %\ensuremath{\times}% #&times;# *)
(** printing * %\ensuremath{\times}% #&times;# *)
(** printing ★ %\ensuremath{\star}% #&#9733;# *)
(** printing "★" %\ensuremath{\star}% #&#9733;# *)
(** printing '★' %\ensuremath{\star}% #&#9733;# *)
(** printing '⊔' %\ensuremath{\sqcup}% #&#x2294;# *)
(** printing ⊔ %\ensuremath{\sqcup}% #&#x2294;# *)
(** printing 'π' %\ensuremath{\pi}% #&pi;# *)
(** printing π %\ensuremath{\pi}% #&pi;# *)
(** printing ₁ %\ensuremath{_1}% #<sub>1</sub># *)
(** printing ₂ %\ensuremath{_2}% #<sub>2</sub># *)
(** printing π₁ %\ensuremath{\pi_1}% #&pi;<sub>1</sub># *)
(** printing π₂ %\ensuremath{\pi_2}% #&pi;<sub>2</sub># *)
(** printing 'π₁' %\ensuremath{\pi_1}% #&pi;<sub>1</sub># *)
(** printing 'π₂' %\ensuremath{\pi_2}% #&pi;<sub>2</sub># *)
(** printing ≅ %\ensuremath{\cong}% #&cong;# *)
(** printing λ %\ensuremath{\lambda}% #&lambda;# *)
(** printing 'o' %\ensuremath{\circ}% #&#x25cb;# *)
(** printing o %\ensuremath{\circ}% #&#x25cb;# *)
(** printing i ⁻¹ %\ensuremath{i^{-1}}% #i<sup>-1</sup># *)
(** printing 'i ⁻¹' %\ensuremath{i^{-1}}% #i<sup>-1</sup># *)
(** printing "i ⁻¹" %\ensuremath{i^{-1}}% #i<sup>-1</sup># *)
(** printing ⁻¹ %\ensuremath{^{-1}}% #<sup>-1</sup># *)
(** printing '⁻¹' %\ensuremath{^{-1}}% #<sup>-1</sup># *)
(** printing '⁻' %\ensuremath{^{-}}% #<sup>-</sup># *)
(** printing '¹' %\ensuremath{^{1}}% #<sup>1</sup># *)
(** printing ⁻ %\ensuremath{^{-}}% #<sup>-</sup># *)
(** printing ¹ %\ensuremath{^{1}}% #<sup>1</sup># *)
(** printing :> %:\ensuremath{>}% #:># *)
(** printing ':>' %:\ensuremath{>}% #:># *)
(** printing _1_ %\ensuremath{\text{\underline{2}}}% #<u>2</u># *)
(** printing '_1_' %\ensuremath{\text{\underline{2}}}% #<u>2</u># *)
(** printing _2_ %\ensuremath{\text{\underline{2}}}% #<u>2</u># *)
(** printing '_2_' %\ensuremath{\text{\underline{2}}}% #<u>2</u># *)

Require Import Utf8 Setoid.
Require Import Monoid.

Set Implicit Arguments.

Generalizable All Variables.

Definition smallest_monoid : Monoid unit.
  eexists (@Build_ComputationalMonoid _ tt (fun _ _ => tt)).
  split;
  repeat intros [];
  reflexivity.
Defined.

Lemma no_smaller_monoid : Monoid Empty_set -> False.
  intro M.
  destruct (@id _ M).
Qed.

Inductive two := twoa | twob.

Inductive three := one | zeroa | zerob.

Definition f : three -> three -> three :=
  fun x y => match (x, y) with
               | (one, z) => z
               | (z, one) => z
               | (zeroa, _) => zeroa
               | (zerob, _) => zerob
             end.

Definition three_monoid : Monoid three.
  eexists (@Build_ComputationalMonoid _ one f).
  split; repeat intros []; reflexivity.
Defined.

Lemma two_monoid_is_commutative (M : Monoid two) : is_commutative M.
  repeat intro;
  pose proof (@left_id _ _ M);
  pose proof (@right_id _ _ M);
  set (i := @id _ M) in *; clearbody i;
  hnf in *;
  repeat match goal with
           | [ H := _ |- _ ] => subst H
           | [ H : two |- _ ] => destruct H
           | [ H : _ |- _ ] => rewrite H
         end;
  try reflexivity.
Qed.

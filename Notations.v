Require Import JMeq.
Notation ℕ := nat.

Infix "==" := JMeq (at level 70, right associativity).

Infix "×" := prod (at level 40, left associativity) : type_scope.

Reserved Infix "o" (at level 40, left associativity).

(** [Reserved Notation "i ⁻¹" (at level 10).] *)

(* begin hide *)
Reserved Notation "i ⁻¹" (at level 10).
(* end hide *)

Reserved Infix "≅" (at level 70).

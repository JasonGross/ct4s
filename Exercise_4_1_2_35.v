Require Import Utf8.
Require Import Category Functor ComputableCategory SetCategory.

Set Implicit Arguments.

Generalizable All Variables.

(** ------------------------------------------------------------------------ *)
(** * Exercise 4.1.2.35 *)
Section Exercise_4_1_2_35.
  (** ** Problem *)
  (** If someone said "[Ob] is a functor from [Cat] to [Set]," what might
      they mean? *)
  Let Cat := CategoryOfCategories.
  Let Sets := CategoryOfTypes.

  Example ObFunctor : Functor Cat Sets
    := {| ObjectOf := (fun C : Cat => projT1 C);
          MorphismOf := (fun C D (F : Morphism Cat C D) =>
                           ObjectOf F : Morphism Sets _ _);
          FCompositionOf := (fun _ _ _ _ _ => eq_refl);
          FIdentityOf := (fun _ => eq_refl) |}.
End Exercise_4_1_2_35.
(** ------------------------------------------------------------------------ *)

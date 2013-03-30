(** printing 'o' %\ensuremath{\circ}% #&#x25cb;# *)
(** printing o %\ensuremath{\circ}% #&#x25cb;# *)
(** printing λ %\ensuremath{\lambda}% #&lambda;# *)

Require Import Utf8.
Require Export Category.

Set Implicit Arguments.

Generalizable All Variables.

(** * Category of Sets *)
(** (The category Set of sets). Chapter 2 was all about the category
    of sets, denoted [Set]. The objects are the sets and the morphisms
    are the functions; we even used the current notation, referring to
    the set of functions [X -> Y] as #<tt>Hom<sub>Set</sub>(X,
    Y)</tt>#$\text{Hom}_{\text{Set}}(X, Y)$.  The composition formula
    [o] is given by function composition, and for every set [X], the
    identity function [id X : X -> X] serves as the identity morphism
    for [X : Ob(Set)]. The two laws clearly hold, so [Set] is indeed a
    category. *)

(** We use [Notation] to get around type-checking until we instantiate
    it with a particular universe. *)

Notation IndexedCategoryOf obj coerce :=
  (@Build_Category obj
                   (fun s d => coerce s -> coerce d)
                   (fun _ => (fun x => x))
                   (fun _ _ _ f g => (fun x => f (g x)))
                   (fun _ _ _ _ _ _ f => eq_refl)
                   (fun _ _ f => eq_refl : (fun x => f x) = f)
                   (fun _ _ f => eq_refl : (fun x => f x) = f)
  ).

Notation CategoryOf Sets :=
  ({|
      (*Object := Sets;*)
      Morphism := (fun X Y : Sets => X -> Y);
      Identity := (fun X : Sets => (fun x : X => x));
      Compose := (fun _ _ _ f g => (fun x => f (g x)));
      LeftIdentity := (fun X Y p => @eq_refl _ p : (λ x : X, p x) = p);
      RightIdentity := (fun X Y p => @eq_refl _ p : (λ x : X, p x) = p);
      Associativity := (fun _ _ _ _ _ _ _ => eq_refl)
    |}
   : @Category Sets).

Definition CategoryOfSets := CategoryOf Set.
Definition CategoryOfTypes := CategoryOf Type.
Definition CategoryOfProps := CategoryOf Prop.

(** printing ∫ %\ensuremath{\int}% #&int;# *)
Require Export Category Functor FunctorCategory.
Require Import Common SetCategory Notations NaturalTransformation.

Set Implicit Arguments.

Generalizable All Variables.

Section Grothendieck.
  (**
     Quoting Wikipedia:

     The Grothendieck construction is an auxiliary construction used
     in the mathematical field of category theory.

     Let [F : C -> Set] be a functor from any small category to the
     category of sets.  The Grothendieck construct for [F] is the
     category [Γ F] whose objects are pairs [(c, x)], where [c : C] is
     an object and [x : F c] is an element, and for which the set [Hom
     (Γ F) (c1, x1) (c2, x2)] is the set of morphisms [f : c1 -> c2]
     in [C] such that [F.(MorphismOf) f x1 = x2].  *)

  Context `(C : @Category objC).
  Variable F : Functor C CategoryOfTypes.

  Record GrothendieckPair :=
    {
      GrothendieckC : C;
      GrothendieckX : F GrothendieckC
    }.

  Lemma GrothendieckPair_eta (x : GrothendieckPair) : Build_GrothendieckPair (GrothendieckC x) (GrothendieckX x) = x.
    destruct x; reflexivity.
  Defined.

  Definition GrothendieckCompose cs xs cd xd cd' xd' :
    { f : C.(Morphism) cd cd' | F.(MorphismOf) f xd = xd' } -> { f : C.(Morphism) cs cd | F.(MorphismOf) f xs = xd } ->
    { f : C.(Morphism) cs cd' | F.(MorphismOf) f xs = xd' }.
    intros m2 m1.
    exists (Compose (proj1_sig m2) (proj1_sig m1)).
    abstract (
        destruct m1, m2;
        rewrite FCompositionOf;
        unfold CategoryOfTypes, Compose;
        simpl;
        repeat (rewrite_rev_hyp || apply f_equal || reflexivity)
      ).
  Defined.

  Arguments GrothendieckCompose [cs xs cd xd cd' xd'] / _ _.

  Definition GrothendieckIdentity c x : { f : C.(Morphism) c c | F.(MorphismOf) f x = x }.
    exists (Identity c).
    abstract (
        rewrite FIdentityOf;
        unfold CategoryOfTypes, Identity;
        reflexivity
      ).
  Defined.

  Local Hint Extern 1 (@eq (sig _) _ _) => simpl_eq : category.

  Definition CategoryOfElements : @Category GrothendieckPair.
    refine (@Build_Category _
                            (fun s d =>
                               { f : C.(Morphism) (GrothendieckC s) (GrothendieckC d) | F.(MorphismOf) f (GrothendieckX s) = (GrothendieckX d) })
                            (fun x => GrothendieckIdentity (GrothendieckC x) (GrothendieckX x))
                            (fun _ _ _ m1 m2 => GrothendieckCompose m1 m2)
                            _
                            _
                            _);
    abstract (
        unfold GrothendieckC, GrothendieckX, GrothendieckCompose, GrothendieckIdentity in *;
        intros; destruct_type GrothendieckPair; destruct_sig; eauto with category
      ).
  Defined.

  Definition GrothendieckProjectionFunctor : Functor CategoryOfElements C.
    refine {| ObjectOf := (fun x : CategoryOfElements => GrothendieckC x);
              MorphismOf := (fun s d (m : CategoryOfElements.(Morphism) s d) => proj1_sig m)
           |};
    abstract (eauto with category; intros; destruct_type CategoryOfElements; simpl; reflexivity).
  Defined.
End Grothendieck.

Notation "∫ F" := (CategoryOfElements F).

(*Section functorial.
  Context `(C : @Category objC).

  Definition GrothendieckFunctorFunctorial F G (T : Morphism (CategoryOfTypes ^ C) F G)
  : Morphism CategoryOfTypes (∫ F) (∫ G)
    := fun x => {| GrothendieckC := GrothendieckC x;
                   GrothendieckX := T (GrothendieckC x) (GrothendieckX x) |}.
End functorial.*)

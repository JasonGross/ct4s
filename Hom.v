Require Import FunctionalExtensionality.
Require Export Category Functor Duals SetCategory ProductCategory.
Require Import Common ProductInducedFunctors.

Set Implicit Arguments.

Generalizable All Variables.

Local Open Scope category_scope.

Section HomFunctor.
  Local Open Scope morphism_scope.

  Context `(C : @Category objC).
  Let COp := OppositeCategory C.

  Definition HomFunctor : Functor (COp * C) CategoryOfTypes.
    refine (Build_Functor (COp * C) CategoryOfTypes
                          (fun c'c => fst c'c ~> snd c'c)
                          (fun _ _ hf => fun g => (snd hf) o g o (fst hf))
                          _
                          _
           );
    abstract (
        simpl;
        repeat (apply functional_extensionality_dep || intro);
        autorewrite with morphism;
        reflexivity
      ).
  Defined.

  Section covariant_contravariant.
    Local Open Scope functor_scope.
    Local Arguments InducedProductSndFunctor / _ _ _ _ _ _ _ _.
    Definition CovariantHomFunctor (A : OppositeCategory C) :=
      Eval simpl in HomFunctor ⟨ A , - ⟩.
    Definition ContravariantHomFunctor (A : C) := HomFunctor ⟨ - , A ⟩.
  End covariant_contravariant.
End HomFunctor.

Section SplitHomFunctor.
  Context `(C : @Category objC).
  Let COp := OppositeCategory C.

  Lemma SplitHom (X Y : COp * C)
  : forall gh,
      MorphismOf (HomFunctor C) (s := X) (d := Y) gh =
      (Compose
         (MorphismOf (ContravariantHomFunctor C (snd Y)) (s := fst X) (d := fst Y) (fst gh))
         (MorphismOf (CovariantHomFunctor C (fst X)) (s := snd X) (d := snd Y) (snd gh))).
  Proof.
    destruct X, Y.
    intro gh; destruct gh.
    simpl in *.
    apply functional_extensionality_dep; intro.
    autorewrite with morphism.
    reflexivity.
  Qed.

  Lemma SplitHom' (X Y : COp * C)
  : forall gh,
                                      MorphismOf (HomFunctor C) (s := X) (d := Y) gh =
                                      (Compose
                                         (MorphismOf (CovariantHomFunctor C (fst Y)) (s := snd X) (d := snd Y) (snd gh))
                                         (MorphismOf (ContravariantHomFunctor C (snd X)) (s := fst X) (d := fst Y) (fst gh))).
  Proof.
    destruct X, Y.
    intro gh; destruct gh.
    simpl in *.
    apply functional_extensionality_dep; intro.
    autorewrite with morphism.
    reflexivity.
  Qed.
End SplitHomFunctor.

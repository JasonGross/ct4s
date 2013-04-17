Require Export ProductCategory Functor NaturalTransformation.
Require Import Common Notations.

Set Implicit Arguments.

Generalizable All Variables.

Local Ltac product_induced_functors_t :=
  intros; simpl; repeat (rewrite <- FCompositionOf || rewrite <- FIdentityOf);
  apply f_equal; expand; autorewrite with morphism;
  reflexivity.

Section ProductInducedFunctors.
  Context `(C : @Category objC).
  Context `(D : @Category objD).
  Context `(E : @Category objE).

  Variable F : Functor (C * D) E.

  Definition InducedProductFstFunctor (d : D) : Functor C E.
    refine {| ObjectOf := (fun c => F (c, d));
              MorphismOf := (fun _ _ m => MorphismOf F (s := (_, d)) (d := (_, d)) (m, Identity d))
           |};
    abstract product_induced_functors_t.
  Defined.

  Definition InducedProductSndFunctor (c : C) : Functor D E.
    refine {| ObjectOf := (fun d => F (c, d));
              MorphismOf := (fun _ _ m => MorphismOf F (s := (c, _)) (d := (c, _)) (Identity c, m))
           |};
    abstract product_induced_functors_t.
  Defined.
End ProductInducedFunctors.

Notation "F ⟨ c , - ⟩" := (InducedProductSndFunctor F c) : functor_scope.
Notation "F ⟨ - , d ⟩" := (InducedProductFstFunctor F d) : functor_scope.

Section ProductInducedNaturalTransformations.
  Context `(C : @Category objC).
  Context `(D : @Category objD).
  Context `(E : @Category objE).

  Variable F : Functor (C * D) E.

  Definition InducedProductFstNaturalTransformation {s d} (m : Morphism C s d) : NaturalTransformation (F ⟨ s, - ⟩) (F ⟨ d, - ⟩).
    match goal with
      | [ |- NaturalTransformation ?F0 ?G0 ] =>
        refine (Build_NaturalTransformation F0 G0
                                            (fun d => MorphismOf F (s := (_, d)) (d := (_, d)) (m, Identity (C := D) d))
                                            _
               )
    end;
    abstract product_induced_functors_t.
  Defined.

  Definition InducedProductSndNaturalTransformation {s d} (m : Morphism D s d) : NaturalTransformation (F ⟨ -, s ⟩) (F ⟨ - , d ⟩).
    match goal with
      | [ |- NaturalTransformation ?F0 ?G0 ] =>
        refine (Build_NaturalTransformation F0 G0
                                            (fun c => MorphismOf F (s := (c, _)) (d := (c, _)) (Identity (C := C) c, m))
                                            _
               )
    end;
    abstract product_induced_functors_t.
  Defined.
End ProductInducedNaturalTransformations.

Notation "F ⟨ f , - ⟩" := (InducedProductSndNaturalTransformation F f) : natural_transformation_scope.
Notation "F ⟨ - , f ⟩" := (InducedProductFstNaturalTransformation F f) : natural_transformation_scope.

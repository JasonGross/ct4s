Require Import ProofIrrelevance.
Require Export Category Functor ProductCategory.
Require Import Common Notations InitialTerminalCategory FEqualDep.

Set Implicit Arguments.

Generalizable All Variables.

Local Open Scope category_scope.

Section CommaCategory.
  Context `(A : @Category objA).
  Context `(B : @Category objB).
  Context `(C : @Category objC).
  Variable S : Functor A C.
  Variable T : Functor B C.

  (** Quoting Wikipedia:
     Suppose that [A], [B], and [C] are categories, and [S] and [T]
     are functors
     [S : A -> C <- B : T]
     We can form the comma category [(S ↓ T)] as follows:
     (o) The objects are all triples [(α, β, f)] with [α] an object in
         [A], [β] an object in [B], and [f : S α -> T β] a morphism in
         [C].
     (o) The morphisms from [(α, β, f)] to [(α', β', f')] are all
         pairs [(g, h)] where [g : α -> α'] and [h : β -> β'] are
         morphisms in [A] and [B] respectively, such that the
         following diagram commutes:
         [[
               S g
          S α -----> S α'
           |          |
         f |          | f'
           |          |
           V          V
          T β -----> T β'
               T h
         ]]
     Morphisms are composed by taking [(g, h) ○ (g', h')] to be
     [(g ○ g', h ○ h')], whenever the latter expression is defined.
     The identity morphism on an object [(α, β, f)] is [(Identity α, Identity β)].
   *)

  Record CommaCategory_Object := { CommaCategory_Object_Member :> { αβ : objA * objB & C.(Morphism) (S (fst αβ)) (T (snd αβ)) } }.

  Let SortPolymorphic_Helper (A T : Type) (Build_T : A -> T) := A.

  Definition CommaCategory_ObjectT := Eval hnf in SortPolymorphic_Helper Build_CommaCategory_Object.
  Global Identity Coercion CommaCategory_Object_Id : CommaCategory_ObjectT >-> sigT.
  Definition Build_CommaCategory_Object' (mem : CommaCategory_ObjectT) := Build_CommaCategory_Object mem.
  Global Coercion Build_CommaCategory_Object' : CommaCategory_ObjectT >-> CommaCategory_Object.

  Record CommaCategory_Morphism (αβf α'β'f' : CommaCategory_ObjectT) :=
    { CommaCategory_Morphism_Member
        :> { gh : (A.(Morphism) (fst (projT1 αβf)) (fst (projT1 α'β'f'))) * (B.(Morphism) (snd (projT1 αβf)) (snd (projT1 α'β'f')))
           | Compose (T.(MorphismOf) (snd gh)) (projT2 αβf) = Compose (projT2 α'β'f') (S.(MorphismOf) (fst gh)) }
    }.

  Definition CommaCategory_MorphismT (αβf α'β'f' : CommaCategory_ObjectT) :=
    Eval hnf in SortPolymorphic_Helper (@Build_CommaCategory_Morphism αβf α'β'f').
  Global Identity Coercion CommaCategory_Morphism_Id : CommaCategory_MorphismT >-> sig.
  Definition Build_CommaCategory_Morphism' αβf α'β'f' (mem : @CommaCategory_MorphismT αβf α'β'f') :=
    @Build_CommaCategory_Morphism _ _ mem.
  Global Coercion Build_CommaCategory_Morphism' : CommaCategory_MorphismT >-> CommaCategory_Morphism.

  Lemma CommaCategory_Morphism_Eq
  : forall αβf α'β'f' (M N : CommaCategory_Morphism αβf α'β'f'),
      proj1_sig M = proj1_sig N
      -> M = N.
  Proof.
    clear.
    intros.
    destruct M as [ [ ] ], N as [ [ ] ];
      f_equal;
      simpl_eq;
      subst; reflexivity.
  Qed.

  Global Arguments CommaCategory_Object_Member _ : simpl nomatch.
  Global Arguments CommaCategory_Morphism_Member _ _ _ : simpl nomatch.

  Definition CommaCategory_Compose s d d'
             (gh : CommaCategory_MorphismT d d') (g'h' : CommaCategory_MorphismT s d) :
    CommaCategory_MorphismT s d'.
  Proof.
    exists (Compose (C := A * B) (proj1_sig gh) (proj1_sig g'h')).
    hnf in *; simpl in *.
    abstract (
        destruct_all_hypotheses;
        unfold Morphism in *;
          destruct_hypotheses;
        repeat rewrite FCompositionOf;
        repeat try_associativity ltac:(t_rev_with t')
      ).
  Defined.

  Global Arguments CommaCategory_Compose _ _ _ _ _ / .

  Definition CommaCategory_Identity x : CommaCategory_MorphismT x x.
    exists (Identity (C := A * B) (projT1 x)).
    abstract (
        simpl; autorewrite with category; reflexivity
      ).
  Defined.

  Global Arguments CommaCategory_Identity _ / .

  Local Ltac comma_t :=
    repeat (
        let H:= fresh in intro H; destruct H as [ [ ] ]
      );
    destruct_hypotheses;
    simpl in *;
    simpl_eq;
    autorewrite with category;
    f_equal;
    try reflexivity.

  Lemma CommaCategory_Associativity
  : forall o1 o2 o3 o4 (m1 : CommaCategory_MorphismT o1 o2) (m2 : CommaCategory_MorphismT o2 o3) (m3 : CommaCategory_MorphismT o3 o4),
      CommaCategory_Compose (CommaCategory_Compose m3 m2) m1 =
      CommaCategory_Compose m3 (CommaCategory_Compose m2 m1).
  Proof.
    abstract (
        simpl_eq;
        repeat rewrite Associativity;
        reflexivity
      ).
  Qed.

  Lemma CommaCategory_LeftIdentity
  : forall a b (f : CommaCategory_MorphismT a b),
      CommaCategory_Compose (CommaCategory_Identity b) f = f.
  Proof.
    abstract comma_t.
  Qed.

  Lemma CommaCategory_RightIdentity
  : forall a b (f : CommaCategory_MorphismT a b),
      CommaCategory_Compose f (CommaCategory_Identity a) = f.
  Proof.
    abstract comma_t.
  Qed.

  Definition CommaCategory : @Category CommaCategory_Object.
    match goal with
      | [ |- @Category ?obj ] =>
        refine (@Build_Category obj
                                CommaCategory_Morphism
                                CommaCategory_Identity
                                CommaCategory_Compose
                                _ _ _
               )
    end;
    abstract (
        intros;
        destruct_type' @CommaCategory_Morphism;
        unfold CommaCategory_Morphism_Member, Build_CommaCategory_Morphism';
        try apply f_equal;
        apply CommaCategory_Associativity ||
              apply CommaCategory_LeftIdentity ||
              apply CommaCategory_RightIdentity
      ).
  Defined.
End CommaCategory.

Hint Unfold CommaCategory_Compose CommaCategory_Identity : category.
Hint Constructors CommaCategory_Morphism CommaCategory_Object : category.

Notation "S ↓ T" := (CommaCategory S T) : category_scope.

Section SliceCategory.
  Context `(A : @Category objA).
  Context `(C : @Category objC).
  Variable a : C.
  Variable S : Functor A C.
  Let B := TerminalCategory.

  Definition SliceCategory_Functor : Functor B C
    := FunctorFromTerminal _ a.

  Definition SliceCategory := CommaCategory S SliceCategory_Functor.
  Definition CosliceCategory := CommaCategory SliceCategory_Functor S.

(* [x ↓ F] is a coslice category; [F ↓ x] is a slice category; [x ↓ F] deals with morphisms [x -> F y]; [F ↓ x] has morphisms [F y -> x] *)
End SliceCategory.

Section SliceCategoryOver.
  Context `(C : @Category objC).
  Variable a : C.

  Definition SliceCategoryOver := SliceCategory a (IdentityFunctor C).
  Definition CosliceCategoryOver := CosliceCategory a (IdentityFunctor C).
End SliceCategoryOver.

Section ArrowCategory.
  Context `(C : @Category objC).

  Definition ArrowCategory := CommaCategory (IdentityFunctor C) (IdentityFunctor C).
End ArrowCategory.

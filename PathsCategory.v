Require Import Utf8.
Require Export Category Path.
Require Import Common.

Set Implicit Arguments.

Generalizable All Variables.

(** * Category of Paths *)

Section PathsCategory.
  Variable V : Type.
  Variable E : V -> V -> Type.

  Hint Immediate concatenate_associative.
  Hint Rewrite concatenate_associative.

  Definition PathsCategory : @Category V.
    refine (@Build_Category _
                            (@path V E)
                            (@NoEdges _ _)
                            (fun _ _ _ p p' => concatenate p' p)
                            _
                            _
                            _);
    abstract t_with t'.
  Defined.
End PathsCategory.

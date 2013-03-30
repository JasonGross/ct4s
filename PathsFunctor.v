Require Import Utf8.
Require Import JMeq.
Require Export Graph GraphCategory Functor.
Require Export PathsCategory UnderlyingGraph.
Require Import FEqualDep.
Require Import Common.

Set Implicit Arguments.

Generalizable All Variables.

(** * Paths functor *)

Section PathsFunctor.
  (** ** Example 4.1.2.19. [paths-graph] *)
  (** Let [G = (V, A, src, tgt)] be a graph. Then for any pair of
      vertices [v w : G], there is a set [Path_G(v,w)] of paths from
      [v] to [w]; see Definition 3.3.2.1. In fact there is a set
      [Path_G] and functions [src, tgt : Path_G -> V]. That
      information is enough to define a new graph, [Paths(G) := (V,
      Path_G, src, tgt)].  Moreover, given a graph homomorphism [f : G
      -> G'], every path in [G] is sent under [f] to a path in
      [G']. So [Paths : Grph -> Grph] is a functor. *)

  (** We use the underlying graph of the paths category, because we
      have already Coq'ed those two constructions. *)
  Section paths_functor.
    Variables G G' : Graph.
    Variable f : GraphHomomorphism G G'.

    Fixpoint PathsHomomorphism_on_edges src tgt (p : path (Edge G) src tgt)
    : path (Edge G') (f src) (f tgt)
      := match p with
           | NoEdges => NoEdges
           | AddEdge _ _ p0 e => AddEdge (PathsHomomorphism_on_edges p0)
                                         (OnEdges f _ _ e)
         end.

    Definition PathsHomomorphism
    : Morphism CategoryOfGraphs
               (UnderlyingGraph (PathsCategory (Edge G)))
               (UnderlyingGraph (PathsCategory (Edge G')))
      := Build_GraphHomomorphism (UnderlyingGraph (PathsCategory (Edge G)))
                                 (UnderlyingGraph (PathsCategory (Edge G')))
                                 (OnVertices f)
                                 PathsHomomorphism_on_edges.
  End paths_functor.

  Local Ltac t0 :=
    repeat match goal with
             | _ => intro
             | _ => reflexivity
             | _ => apply GraphHomomorphism_Eq
             | _ => apply eq_JMeq
             | [ H : _ |- _ ] => rewrite H
             | _ => progress ( hnf in *; simpl in * )
           end.

  Local Ltac t :=
    repeat match goal with
             | _ => progress t0
             | [ p : path _ _ _ |- _ ] => induction p; solve [ t0 ]
           end.

  Definition PathsFunctor : Functor CategoryOfGraphs CategoryOfGraphs.
    refine (Build_Functor CategoryOfGraphs CategoryOfGraphs
                          (fun G => UnderlyingGraph (PathsCategory (Edge G)))
                          PathsHomomorphism
                          _
                          _);
    abstract t.
  Defined.
End PathsFunctor.

import Mathlib

/-!
# Spanning Trees and Graph Properties

This file defines fundamental concepts in graph theory using the `SimpleGraph` API in Lean 4,
focusing on properties such as acyclicity, connectivity, trees, and spanning trees. It also provides
utility definitions for enumerating edges, counting set cardinality, and generating subsets.

## Main Definitions

* `SimpleGraph.acyclic`     : A graph with no nontrivial cycles.
* `SimpleGraph.Vertices`    : The set of vertices adjacent to at least one other vertex.
* `SimpleGraph.connected`   : A graph where every pair of vertices is connected by a walk.
* `SimpleGraph.tree`        : A graph that is connected and acyclic.
* `SimpleGraph.Edges`       : The list of edges in a graph as unordered vertex pairs.
* `SimpleGraph.spanningTree`: A tree subgraph using only edges from the original graph.
* `Set.cardinality`         : The number of elements in a finite set.
* `subsets`                 : All subsets of a set with a fixed cardinality.
* `spanningtrees`           : The set of all spanning trees of a graph.

These definitions support formal reasoning and algorithmic development in graph theory,
including enumeration and verification of spanning structures.
-/

variable {V : Type} [DecidableEq V] [Fintype V]

namespace SimpleGraph

/-- A graph is *acyclic* if it contains no nontrivial closed walks (cycles). -/
def acyclic (G : SimpleGraph V) : Prop :=
  ∀ (v : V) (p : Walk G v v), ¬p.IsCircuit

/-- The set of vertices that are adjacent to at least one other vertex in the graph. -/
def Vertices (G : SimpleGraph V) : Set V :=
  { v | ∃ w, G.Adj v w ∨ G.Adj w v }

/-- A graph is *connected* if there exists a walk between every pair of vertices. -/
def connected (G : SimpleGraph V) : Prop :=
  Nonempty <| ∀ (v w : V), Walk G v w

/-- A *tree* is a graph that is both connected and acyclic. -/
def tree (G : SimpleGraph V) : Prop :=
  connected G ∧ acyclic G

/-- The list of all edges in a graph, represented as unordered pairs (`Sym2 V`). -/
noncomputable def Edges (G : SimpleGraph V) [DecidableRel G.Adj] : List (Sym2 V) :=
  List.filter (fun e => e ∈ G.edgeSet) (Finset.sym2 Finset.univ).toList

/-- A graph `T` is a *spanning tree* of `G` if it is a tree and all its edges come from `G`. -/
def spanningTree (G : SimpleGraph V) (T : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel T.Adj] : Prop :=
  tree T ∧ T.Edges ⊆ G.Edges

end SimpleGraph

/-- The cardinality of a finite set, computed via conversion to a `Finset`. -/
def Set.cardinality {α : Type} (s : Set α) [Fintype s] : Nat :=
  (s.toFinset).card

/-- The set of all subsets of `s` having exactly `n` elements. -/
def subsets {α : Type} (s : Set α) (n : Nat) : Set (Set α) :=
  { t | t ⊆ s ∧ @Set.cardinality _ t = n }


structure SpanningTree {V : Type} [DecidableEq V] [Fintype V] (G : SimpleGraph V)[DecidableRel G.Adj] where
  (tree : SimpleGraph V)
  (isTree : SimpleGraph.tree tree)
  inst : DecidableRel tree.Adj
  (isSpanning : tree.Vertices = G.Vertices ∧ tree.Edges ⊆ G.Edges)

/-- The set of all spanning trees of a graph `G` that span its vertex set and use only its edges. -/
def spanningtrees {V : Type} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Set (SimpleGraph V) :=
  { T | ∃a : SpanningTree G, a.tree = T}

instance {V : Type} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Fintype (spanningtrees G) :=
    sorry
    
/-- The number of spanning trees of a graph `G` is the cardinality of the set of all spanning trees. -/
def numSpanningTrees {V : Type} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Nat :=
  Set.cardinality (spanningtrees G)

#synth Fintype (SimpleGraph (Fin 3))

#moogle "Subgraph of a finite graph is finite."

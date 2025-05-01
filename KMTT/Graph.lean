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
* `Sym2.toProd`: Converts an unordered pair to an ordered pair based on a linear order.
* `Sym2.toProd_mem`: Proves that the elements of the ordered pair are members of the original unordered pair.
* `Sym2.equality_left` and `Sym2.equality_right`: Lemmas for substituting equal vertices in edges.
* `edge_exist_adj`: Establishes the equivalence between adjacency and edge membership in the graph's edge set.
* `adjEdge`: Checks if an edge (by index) is incident to a given vertex.
* `SimpleGraph.EdgesIncident`: The set of edge indices incident to a vertex.
* `bool_to_prop'`: Converts a boolean function to a predicate.
* `Set.cardinality`         : The number of elements in a finite set.
* `subsets`                 : All subsets of a set with a fixed cardinality.
* `SpanningTree`: A structure representing a spanning tree of a graph, including its properties.
* `SimpleGraph.spanningtrees`: The set of all spanning trees of a graph.
* `SimpleGraph.numSpanningTrees`: The number of spanning trees of a graph.

These definitions support formal reasoning and algorithmic development in graph theory,
including enumeration and verification of spanning structures.
-/

variable {V : Type} [DecidableEq V] [Fintype V] [LinearOrder V]
open Classical
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

end SimpleGraph

-- Converts a Sym2 (unordered pair) to an ordered pair using a linear order
/- `Thanks to Professor Siddhartha Gadgil` -/
def Sym2.toProd {α : Type} [LinearOrder α] (s : Sym2 α) : α × α :=
  Quot.lift
    (fun (a, b) => if a < b then (a, b) else (b, a))
    (by
      intro (a, b) (c, d)
      simp
      intro h
      apply Or.elim h
      · intro h₁
        simp [h₁]
      · intro h₂
        simp [h₂]
        if h' : c < d then
          simp [h']
          have h'' : ¬ d < c := by
            simp [le_of_lt, h']
          simp [h'']
        else
          simp [h']
          if h'' : d < c then
            simp [h'']
          else
            intro h'''
            apply And.intro
            · apply le_antisymm
              · exact h'''
              · revert h'
                simp
            · apply le_antisymm
              · revert h'
                simp
              · exact h''') s

-- Proves that the elements of the ordered pair produced by `Sym2.toProd` are members of the original unordered pair.
/- `Thanks to Professor Siddhartha Gadgil` -/
theorem Sym2.toProd_mem {α : Type}[LinearOrder α] (s : Sym2 α) :
    s.toProd.1 ∈ s ∧ s.toProd.2 ∈ s := by
      revert s
      apply Quot.ind
      intro (a, b)
      by_cases p:a < b <;> simp [p, Sym2.toProd]

set_option linter.unusedSectionVars false
-- Lemma showing that equality `v = w` allows substitution on the left side within `Sym2.mk`.
lemma Sym2.equality_left {v w : V} (h : v = w) : ∀ x : V, s(v,x) = s(w, x) := by
  simp [h]

-- Lemma showing that equality `v = w` allows substitution on the right side within `Sym2.mk`.
lemma Sym2.equality_right {v w : V} (h : v = w) : ∀ x : V, s(x,v) = s(x, w) := by
  simp [h]

-- Establishes the equivalence between adjacency `G.Adj v w` and the corresponding edge `Sym2.mk (v , w)` being in the graph's edge set `G.Edges`.
lemma SimpleGraph.edge_exist_adj  (G : SimpleGraph V) [DecidableRel G.Adj] (v w : V)
  : G.Adj v w ↔ Sym2.mk (v , w) ∈  G.Edges := by
  apply Iff.intro
  · intro h
    simp [SimpleGraph.Edges]
    assumption
  · intro h
    simp [SimpleGraph.Edges] at h
    assumption

-- Checks if an edge (specified by its index `e`) is incident to vertex `v`. Returns `true` if incident, `false` otherwise.
noncomputable def adjEdge (v: V) {G: SimpleGraph V} [DecidableRel G.Adj] : (Fin G.Edges.length)  → Bool :=
  fun e =>
    let (a, b) := Sym2.toProd (G.Edges.get e)
    if a = v then true
    else if b = v then true
    else false

-- Converts a function `p : α → Bool` into a predicate `α → Prop`.
def bool_to_prop' {α : Type} (p : α → Bool) : α → Prop :=
  fun x => p x = true


-- Defines the Finset of edge indices incident to a given vertex `v`.
noncomputable def SimpleGraph.EdgesIncident {G : SimpleGraph V} [DecidableRel G.Adj] (v : V) :
  Finset (Fin G.Edges.length) :=
  Finset.filter (bool_to_prop' (adjEdge v)) (Finset.univ : Finset (Fin G.Edges.length))

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
def SimpleGraph.spanningtrees {V : Type} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Set (SimpleGraph V) :=
  { T | ∃a : SpanningTree G, a.tree = T}

noncomputable instance {V : Type} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Fintype (G.spanningtrees) :=
    setFintype (G.spanningtrees)

/-- The number of spanning trees of a graph `G` is the cardinality of the set of all spanning trees. -/
noncomputable def SimpleGraph.numSpanningTrees {V : Type} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Nat :=
  Set.cardinality (G.spanningtrees)

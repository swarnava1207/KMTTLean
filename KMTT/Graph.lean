import Mathlib

#print SimpleGraph
#print Nonempty

def g₁ : SimpleGraph Nat :=
  ⟨ fun n m => n = m + 1 ∨ n = m - 1,sorry,sorry⟩

#check SimpleGraph.isTree_iff

namespace SimpleGraph


variable {V : Type} [DecidableEq V]

def acyclic (G : SimpleGraph V) : Prop :=
  ∀ (v : V) (p : Walk G v v), ¬p.IsCircuit

def Vertices (G : SimpleGraph V) : Set V :=
  { v | ∃ w, G.Adj v w ∨ G.Adj w v }

def connected (G : SimpleGraph V) : Prop :=
  Nonempty <| ∀ (v w : V), Walk G v w

def tree (G : SimpleGraph V) : Prop :=
  connected G ∧ acyclic G

def Edges (G : SimpleGraph V) : Set (V × V) :=
  { e | G.Adj e.1 e.2 }

def spanningTree (G : SimpleGraph V) (T : SimpleGraph V) : Prop :=
  tree T ∧ T.Edges ⊆ G.Edges

#print Set

end SimpleGraph
def Set.cardinality {α : Type}  (s : Set α) [Fintype s] : Nat :=
  (s.toFinset).card

def subsets {α : Type} (s : Set α) (n : Nat) : Set (Set α) :=
  { t | t ⊆ s ∧ @Set.cardinality _ t = n }

def spanningtrees {V : Type} [DecidableEq V] (G : SimpleGraph V) : Set (SimpleGraph V) :=
  { T | SimpleGraph.tree T ∧ T.Vertices = G.Vertices ∧ T.Edges ⊆ G.Edges }

def g₂ : SimpleGraph (Fin 3) :=
  ⟨ fun n m => n = m + 1 ∨ n = m - 1,sorry,sorry⟩

#eval (spanningtrees g₂).cardinality

import Mathlib
import KMTT.Graph

/-!
# Graph Matrix Utilities

This file provides matrix-based representations and operations for graphs using `SimpleGraph`,
including incidence matrices, submatrix selection, edge and vertex processing, and structure
theorems relating the incidence matrix to Laplacians.

It includes both helper functions for handling finite sets, matrices, and lists,
as well as more sophisticated operations like incidence matrix minors and verification
of matrix identities related to graph theory.

## Main Definitions and Theorems

- `SimpleGraph.IncidenceMatrix` (alias `SimpleGraph.Inc`): The incidence matrix of a graph.
- `I`: The identity matrix of dimension `n`.
- `List.remove`: Removes an indexed element from a list.
- `remove_length`: Proves that `List.remove` decreases list length by 1.
- `SimpleGraph.IncMinor`: Minor of the incidence matrix by removing one edge.
- `SimpleGraph.Lapminor`: Minor of the Laplacian matrix by removing the last row and column.
- `non_zero_iff_incident`: Predicate checking if an edge corresponds to non-zero entries in the incidence matrix.
- `edge_vertex_bijection`: Maps an incident edge index to the adjacent vertex.
- `inc_incT_diag_degree`: States that `(Inc * Incᵀ) v v = degree v`.

These constructions are useful for combinatorics, spectral graph theory, and matrix-tree theorem formulations.
-/
open Classical
variable {V : Type} [DecidableEq V] [Fintype V][LinearOrder V]



-- The incidence matrix of a simple graph G, oriented by the linear order on vertices.
noncomputable def SimpleGraph.IncidenceMatrix {V : Type} [DecidableEq V][Fintype V][LinearOrder V](G : SimpleGraph V)[DecidableRel G.Adj]
  : Matrix V (Fin (G.Edges.length)) ℚ :=
  fun v e =>
    let (a, b) := Sym2.toProd (G.Edges.get e)
    if v = a then 1
    else if v = b then -1
    else 0

-- Shorthand alias for `SimpleGraph.IncidenceMatrix`.
alias SimpleGraph.Inc := SimpleGraph.IncidenceMatrix


-- Defines the identity matrix of size `n x n` over the rationals `ℚ`.
def I {n : Nat} : Matrix (Fin n) (Fin n) ℚ := 1


-- Removes the i-th element from a list, given proof that i < l.length.
def List.remove {α : Type} (l : List α) (i : ℕ) (h : i < l.length) : List α :=
  match l with
  | [] => []
  | x :: xs =>
    if h' : i = 0 then xs
    else x :: List.remove xs (i - 1) (by
    simp_all only [length_cons]
    ; omega )

-- Proves that `List.remove` decreases the length of the list by exactly 1.
theorem remove_length {α : Type} (l : List α) (i : ℕ) (h : i < l.length) :
  (List.remove l i h).length = l.length - 1 := by
  induction l generalizing i with
  | nil =>
    simp only [List.length_nil] at h
    exact absurd h (Nat.not_lt_zero i)
  | cons x xs ih =>
    simp only [List.remove]
    split_ifs with h_i_eq_zero
    · simp only [List.length_cons, Nat.add_succ_sub_one, Nat.zero_add]
      rfl
    · simp only [List.length_cons, Nat.add_succ_sub_one, Nat.zero_add]
      rw [ih (i - 1)]
      simp
      match xs with
      | [] => aesop
      | y :: ys => simp

-- The incidence matrix of a graph minor obtained by removing the last edge from the edge list.
noncomputable def SimpleGraph.IncMinor {n : ℕ} (G : SimpleGraph (Fin (n + 1))) [DecidableRel G.Adj]
        : Matrix (Fin n) (Fin (G.Edges.length - 1)) ℚ :=
        let m : ℕ := G.Edges.length
        if h' : m = 0 then
          fun i j => 0
        else
          let edge_filter : List (Sym2 (Fin (n + 1))) :=
            G.Edges.remove (m-1) (by simp [m]; omega)
        have m_eq : edge_filter.length = G.Edges.length - 1 := by
          simp [edge_filter]
          apply remove_length
        fun i j =>
          let e := edge_filter.get (by rw [m_eq]; exact j)
          let (a, b) := Sym2.toProd e
          if i = a then 1
          else if i = b then -1
          else 0

-- The minor of the Laplacian matrix of a graph, obtained by removing the last row and column.
def SimpleGraph.Lapminor {n : ℕ} (G : SimpleGraph (Fin (n + 1))) [DecidableRel G.Adj]
        : Matrix (Fin n) (Fin n) ℚ :=
        fun i j => G.lapMatrix ℚ i j

-- A predicate checking if an edge `e` corresponds to non-zero entries in the incidence matrix `G.Inc`.
def non_zero_iff_incident (G : SimpleGraph V) [DecidableRel G.Adj]
  : (Sym2 V) → Prop
    := fun e =>
      let (a, b) := Sym2.toProd e
      ∃ i j, G.Inc a i = 1 ∧ G.Inc b j = -1

-- Shows that the square of the incidence matrix entry `G.Inc v x` is 1 if edge `x` is incident to vertex `v`, and 0 otherwise.
theorem adj_prop (v : V) (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∀ x :  (Fin G.Edges.length), G.Inc v x * (G.Inc v x) = if adjEdge v x then 1 else 0 := by
  intro x
  simp only [Matrix.mul_apply, SimpleGraph.Inc]
  simp [adjEdge]
  simp [SimpleGraph.IncidenceMatrix]
  aesop

-- Maps an edge index `e` incident to vertex `v` to the other vertex of the edge. If not incident, returns `v`.
noncomputable def edge_vertex_bijection (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    Fin G.Edges.length → V :=
    fun e =>
      let (a, b) := Sym2.toProd (G.Edges.get e)
      if a = v then b
      else if b = v then a
      else v



-- States that the diagonal entry `(v,v)` of the matrix product `Inc * Incᵀ` equals the degree of vertex `v`.
theorem inc_incT_diag_degree (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∀ v, (G.Inc * G.Inc.transpose) v v = G.degree v := by
  intro v
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  simp [adj_prop]
  unfold SimpleGraph.degree
  sorry -- Proof needs completion

-- Shows that for distinct non-adjacent vertices `v, w`, the product of their corresponding entries in any column `e` of the incidence matrix is 0.
@[simp]lemma not_adj_zero (G : SimpleGraph V)[DecidableRel G.Adj]{v w : V} (h_ne : v ≠ w)
  (h_adj : ¬ G.Adj v w) :
  ∀ e : Fin (G.Edges.length), G.IncidenceMatrix v e * (G.IncidenceMatrix w e) = 0 := by
  intro e
  simp [SimpleGraph.edge_exist_adj]
  simp_all only [ne_eq]
  let unordered_e :=G.Edges.get e
  let (a, b) := Sym2.toProd unordered_e
  by_cases h : a = v
  · by_cases h' : b = w
    · simp [SimpleGraph.edge_exist_adj] at h_adj
      have : s(a,b) ∈ G.Edges := by
        have : a ∈ unordered_e ∧ b ∈ unordered_e := by
          sorry -- Proof needs completion: requires showing a,b are the elements of unordered_e
        sorry -- Proof needs completion: requires showing unordered_e is s(a,b)
      aesop
    · simp[h',h, SimpleGraph.IncidenceMatrix]
      apply Or.intro_right
      split
      · sorry -- Proof needs completion: requires showing w ≠ a and w ≠ b
      · sorry -- Proof needs completion: requires showing w ≠ a and w ≠ b

  · sorry -- Proof needs completion: handle case a ≠ v


-- Shows that for distinct adjacent vertices `v, w`, the product `Inc v e * Inc w e` is -1 if edge `e` is `s(v,w)`, and 0 otherwise.
@[simp]lemma adj_minus_one (G : SimpleGraph V)[DecidableRel G.Adj]{v w : V}
  (h_ne : v ≠ w)(h_adj : G.Adj v w) :
  ∀ e , G.IncidenceMatrix v e * (G.IncidenceMatrix w e) = if (G.Edges.get e) = Sym2.mk (v ,w) then -1 else 0
    := by sorry -- Proof needs completion

-- Defines a function that always returns -1 of type `ℚ`.
def neg_id {α : Type} (v : α) : ℚ := -1

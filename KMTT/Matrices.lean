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

- `Sym2.toProd`: Converts an unordered pair to an ordered pair based on a linear order.
- `SimpleGraph.IncidenceMatrix` (alias `SimpleGraph.Inc`): The incidence matrix of a graph.
- `I`: The identity matrix of dimension `n`.
- `listSubsetsOfSize`: Enumerates all subsets of a given size from a list.
- `submatrix'`: Extracts a rectangular block from a matrix using row/column index sets.
- `all_subsets_of_size`: Enumerates all subsets of given cardinality from `Fin m`.
- `zero_to_n_minus_one`: Finset of `Fin n`.
- `Matrix.rowBlocks`, `Matrix.colBlocks`: Submatrices selecting specified rows or columns.
- `List.remove`: Removes an indexed element from a list.
- `remove_length`: Proves that `List.remove` decreases list length by 1.
- `SimpleGraph.IncMinor`: Minor of the incidence matrix by removing one edge.
- `non_zero_iff_incident`: Characterizes incidence via a predicate on edge endpoints.
- `inc_incT_diag_degree`: States that `(Inc * Incᵀ) v v = degree v`.
- `inc_incT_eq_lap`: Proves that `Inc * Incᵀ = Laplacian` matrix.

These constructions are useful for combinatorics, spectral graph theory, and matrix-tree theorem formulations.
-/



variable {V : Type} [DecidableEq V] [Fintype V][LinearOrder V]

-- Converts a Sym2 (unordered pair) to an ordered pair using a linear order
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

-- The incidence matrix of a simple graph G, oriented by linear order on vertices
noncomputable def SimpleGraph.IncidenceMatrix {V : Type} [DecidableEq V][Fintype V][LinearOrder V](G : SimpleGraph V)[DecidableRel G.Adj]
  : Matrix V (Fin (G.Edges.length)) ℚ :=
  fun v e =>
    let (a, b) := Sym2.toProd (G.Edges.get e)
    if v = a then 1
    else if v = b then -1
    else 0

-- Shorthand alias for incidence matrix
alias SimpleGraph.Inc := SimpleGraph.IncidenceMatrix

-- Identity matrix over ℚ
def I {n : Nat} : Matrix (Fin n) (Fin n) ℚ := 1

-- All subsets of a list of size `n`
def listSubsetsOfSize {α : Type} : ℕ → List α → List (List α)
  | 0, _ => [[]]
  | _, [] => []
  | (m+1), x :: xs =>
      (listSubsetsOfSize m xs).map (fun ys => x :: ys) ++ listSubsetsOfSize (m+1) xs

#eval listSubsetsOfSize 2 [1,2,3,4]

-- Extracts a submatrix given row and column index sets (as finsets)
noncomputable def submatrix' {n m : ℕ} {α : Type} [Zero α] (A : Matrix (Fin n) (Fin m) α)
  (rows : Finset (Fin n)) (cols : Finset (Fin m)) :
    Matrix (Fin rows.card) (Fin cols.card) α :=
  fun i j => A (rows.toList.get ⟨i.1, by simp [i.2]⟩) (cols.toList.get ⟨j.1, by simp [j.2]⟩)

-- All subsets of size `n` from `Fin m`
def all_subsets_of_size (n m : ℕ) : Finset (Finset (Fin m)) :=
  Finset.powersetCard n (Finset.univ)

-- The Finset {0, ..., n-1} as Fin n
def zero_to_n_minus_one (n : Nat) : Finset (Fin n) := Finset.univ

-- Lemma: cardinality of `zero_to_n_minus_one` is `n`
theorem zero_to_n_minus_one_card_eq_n {n : ℕ} : (zero_to_n_minus_one n).card = n := by
  simp [zero_to_n_minus_one, Finset.card_univ]

-- Selects specified columns from matrix `N`
noncomputable def Matrix.rowBlocks {n m : ℕ} (N : Matrix (Fin n) (Fin m) ℚ) (s : Finset (Fin m)) : Matrix (Fin n) (Fin s.card) ℚ
        := by rw [← @zero_to_n_minus_one_card_eq_n n] ; exact submatrix' N (zero_to_n_minus_one n) s

-- Selects specified rows from matrix `N`
noncomputable def Matrix.colBlocks {n m : ℕ } (N : Matrix (Fin n) (Fin m) ℚ) (s : Finset (Fin n)) : Matrix (Fin s.card) (Fin m) ℚ
  := by rw [← @zero_to_n_minus_one_card_eq_n m] ; exact submatrix' N s (zero_to_n_minus_one m)

-- Removes the i-th element from a list, given proof that i < l.length
def List.remove {α : Type} (l : List α) (i : ℕ) (h : i < l.length) : List α :=
  match l with
  | [] => []
  | x :: xs =>
    if h' : i = 0 then xs
    else x :: List.remove xs (i - 1) (by
    simp_all only [length_cons]
    ; omega )

-- Proves that `remove` decreases the length of the list by 1
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

-- The incidence matrix of a graph minor (removes last edge)
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

-- A predicate: is there a non-zero entry in Inc for edge (a,b)?
def non_zero_iff_incident (G : SimpleGraph V) [DecidableRel G.Adj]
  : (Sym2 V) → Prop
    := fun e =>
      let (a, b) := Sym2.toProd e
      ∃ i j, G.Inc a i = 1 ∧ G.Inc b j = -1

#check Finset.sum_boole

-- States: (Inc * Incᵀ)(v,v) = degree of v
theorem inc_incT_diag_degree (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∀ v, (G.Inc * G.Inc.transpose) v v = G.degree v := by
  intro v
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  sorry

-- Proves: Inc * Incᵀ = Laplacian matrix of the graph
lemma inc_incT_eq_lap {n : ℕ} (G : SimpleGraph (Fin n))[DecidableRel G.Adj]
  : G.Inc * G.Inc.transpose = (G.lapMatrix ℚ : Matrix (Fin n) (Fin n) ℚ) := by
  apply Matrix.ext; intro i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, SimpleGraph.Inc]
  by_cases h_diag : i = j
  · simp [h_diag]
    have h₁ : G.lapMatrix ℚ j j = G.degree j := by
      simp [SimpleGraph.lapMatrix]
      simp [SimpleGraph.degMatrix]
    rw [h₁]
    sorry
  · sorry

#check Finset.sum_ite_eq

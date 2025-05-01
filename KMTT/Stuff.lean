import Mathlib
import KMTT.Graph
import KMTT.Matrices
/-!

# Stuff
This file contains the stuff I had used to get the initial minor of a matrix. But then I,
could not get to formalise the Cauchy-Binet theorem, so these forms are not used anywhere.

# Definitions and Theorems
- `listSubsetsOfSize` : Given a list and a size, it returns all subsets of that size.
- `submatrix'` : Given a matrix and two sets of indices, it returns the submatrix corresponding to those indices.
- `all_subsets_of_size` : Given two numbers, it returns all subsets of the first number of size equal to the second.
- `zero_to_n_minus_one` : Given a number, it returns the set of indices from 0 to that number minus one.
- `zero_to_n_minus_one_card_eq_n` : A theorem that states the cardinality of `zero_to_n_minus_one` is equal to the number itself.
- `Matrix.rowBlocks` : Given a matrix and a set of columns, it returns the submatrix corresponding to those columns.
- `Matrix.colBlocks` : Given a matrix and a set of rows, it returns the submatrix corresponding to those rows.
-/

/-- This function generates all subsets of a given size from a list. -/
def listSubsetsOfSize {α : Type} : ℕ → List α → List (List α)
  | 0, _ => [[]]
  | _, [] => []
  | (m+1), x :: xs =>
      (listSubsetsOfSize m xs).map (fun ys => x :: ys) ++ listSubsetsOfSize (m+1) xs

/-- Extracts a submatrix given row and column index sets (as finsets) -/
noncomputable def submatrix' {n m : ℕ} {α : Type} [Zero α] (A : Matrix (Fin n) (Fin m) α)
  (rows : Finset (Fin n)) (cols : Finset (Fin m)) :
    Matrix (Fin rows.card) (Fin cols.card) α :=
  fun i j => A (rows.toList.get ⟨i.1, by simp [i.2]⟩) (cols.toList.get ⟨j.1, by simp [j.2]⟩)

/-- All subsets of size `n` from `Fin m` -/
def all_subsets_of_size (n m : ℕ) : Finset (Finset (Fin m)) :=
  Finset.powersetCard n (Finset.univ)

/-- The Finset {0, ..., n-1} as Fin n -/
def zero_to_n_minus_one (n : Nat) : Finset (Fin n) := Finset.univ

/-- Lemma: cardinality of `zero_to_n_minus_one` is `n` -/
theorem zero_to_n_minus_one_card_eq_n {n : ℕ} : (zero_to_n_minus_one n).card = n := by
  simp [zero_to_n_minus_one, Finset.card_univ]

/-- Selects specified columns from matrix `N` -/
noncomputable def Matrix.rowBlocks {n m : ℕ} (N : Matrix (Fin n) (Fin m) ℚ) (s : Finset (Fin m)) : Matrix (Fin n) (Fin s.card) ℚ
        := by rw [← @zero_to_n_minus_one_card_eq_n n] ; exact submatrix' N (zero_to_n_minus_one n) s

/-- Selects specified rows from matrix `N` -/
noncomputable def Matrix.colBlocks {n m : ℕ } (N : Matrix (Fin n) (Fin m) ℚ) (s : Finset (Fin n)) : Matrix (Fin s.card) (Fin m) ℚ
  := by rw [← @zero_to_n_minus_one_card_eq_n m] ; exact submatrix' N s (zero_to_n_minus_one m)

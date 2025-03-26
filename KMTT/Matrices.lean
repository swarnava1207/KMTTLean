import Mathlib
--import Graph.SimpleGraph
open SimpleGraph

#print SimpleGraph.lapMatrix
#print SimpleGraph.incMatrix    --need to understand
#print SimpleGraph.adjMatrix

variable {V : Type} [DecidableEq V]
def SimpleGraph.Edges (G : SimpleGraph V) : Set (V × V) :=
  { e | G.Adj e.1 e.2 }

def IncidenceMatrix {V : Type} [DecidableEq V] (G : SimpleGraph V) : Matrix V G.Edges Int :=
  fun v e => if v = e.val.1 then 1 else if v = e.val.2 then -1 else 0

#print Matrix

def I {n : Nat} : Matrix (Fin n) (Fin n) Int := 1


def listSubsetsOfSize {α : Type} : ℕ → List α → List (List α)
  | 0, _ => [[]]
  | _, [] => []
  | (m+1), x :: xs =>
      (listSubsetsOfSize m xs).map (fun ys => x :: ys) ++ listSubsetsOfSize (m+1) xs

#eval listSubsetsOfSize 2 [1,2,3,4]

#check Finset (Fin 2)

noncomputable def submatrix {n m : ℕ} {α : Type} [Zero α] (A : Matrix (Fin n) (Fin m) α)
  (rows : Finset (Fin n)) (cols : Finset (Fin m)) :
    Matrix (Fin rows.card) (Fin cols.card) α :=
  fun i j => A (rows.toList.get ⟨i.1, by simp [i.2]⟩) (cols.toList.get ⟨j.1, by simp [j.2]⟩)
/-
⊢ {α : Type u_1} → ℕ → Finset α → Finset (Finset α)
-/
#check Finset.powersetCard
def all_subsets_of_size (n m : ℕ) : Finset (Finset (Fin m)) :=
  Finset.powersetCard n (Finset.univ)

#eval all_subsets_of_size 2 3   -- {{0, 1}, {0, 2}, {1, 2}}
#eval (all_subsets_of_size 2 2) -- {{0, 1}}

#synth Fintype (Fin 3) -- Fin.fintype 3

lemma toprove_cauchybinet {m n : Nat} (A : Matrix (Fin n) (Fin m) Int) (B : Matrix (Fin m) (Fin n) Int) :
  ∀ a : Int, a^m * (a • (I) + A * B).det = a^n * (a • (I) + B * A).det := by
  sorry
/-
⊢ {α : Type u_1} → (p : α → Prop) → [inst : DecidablePred p] → (l : Finset α) → (∃! a, a ∈ l ∧ p a) → α
-/
#check Finset.choose

def zero_to_n_minus_one (n : Nat) : Finset (Fin n) := (all_subsets_of_size n n).choose
                                                        (fun s => s.card = n)
                                                          (by sorry)

theorem CauchyBinet {m n : Nat} (M : Matrix (Fin m) (Fin n) Int) (N : Matrix (Fin n) (Fin m) Int) :
  (M * N).det = ∑ s ∈ all_subsets_of_size n m,
  (submatrix M s (zero_to_n_minus_one n)).det * (submatrix N (zero_to_n_minus_one n) s).det :=
  by sorry

#check Finset.card_erase_le
#check Nat.pos_of_ne_zero
#check Finset.erase



--- Check minor of a matrix, and blockmatrix stuff





end SimpleGraph

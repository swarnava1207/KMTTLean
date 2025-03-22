import Mathlib
--import Graph.SimpleGraph
namespace SimpleGraph

#print SimpleGraph.lapMatrix
#print SimpleGraph.incMatrix    --need to understand
#print SimpleGraph.adjMatrix

variable {V : Type} [DecidableEq V]
def Edges (G : SimpleGraph V) : Set (V × V) :=
  { e | G.Adj e.1 e.2 }

def IncidenceMatrix {V : Type} [DecidableEq V] (G : SimpleGraph V) : Matrix V G.Edges Int :=
  fun v e => if v = e.val.1 then 1 else if v = e.val.2 then -1 else 0

#print Matrix

def IdentityMatrix (n : Nat) : Matrix (Fin n) (Fin n) Int :=
  fun i j => if i = j then 1 else 0

alias I := IdentityMatrix




def listSubsetsOfSize {α : Type} : ℕ → List α → List (List α)
  | 0, _ => [[]]
  | _, [] => []
  | (m+1), x :: xs =>
      (listSubsetsOfSize m xs).map (fun ys => x :: ys) ++ listSubsetsOfSize (m+1) xs

#eval listSubsetsOfSize 2 [1,2,3,4]

#check Finset (Fin 2)

noncomputable def submatrix {n m : ℕ} {α : Type} [Zero α] (A : Matrix (Fin n) (Fin m) α) (rows : Finset (Fin n)) (cols : Finset (Fin m)) : Matrix (Fin rows.card) (Fin cols.card) α :=
  fun i j => A (rows.toList.get ⟨i.1, by simp [i.2]⟩) (cols.toList.get ⟨j.1, by simp [j.2]⟩)


#check Finset.powersetCard

def all_subsets_of_size (n m : ℕ) : Finset (Finset (Fin m)) :=
  Finset.powersetCard n (Finset.univ)

#check all_subsets_of_size 2 3
#eval all_subsets_of_size 2 3

#synth Fintype (Fin 3)

lemma toprove_cauchybinet {m n : Nat} (A : Matrix (Fin n) (Fin m) Int) (B : Matrix (Fin m) (Fin n) Int) :
  ∀ a : Int, a^m * (a • (I n) + A * B).det = a^n * (a • (I m) + B * A).det :=
  sorry

/--
error: typeclass instance problem is stuck, it is often due to metavariables
  Fintype (?m.49370 s)
-/
#guard_msgs in
theorem CauchyBinet {m n : Nat} (M : Matrix (Fin m) (Fin n) Int) (N : Matrix (Fin n) (Fin m) Int) :
  (M * N).det = ∑ s ∈ all_subsets_of_size n m, (submatrix M s _).det * (submatrix N _ s).det :=
  by sorry

#check Finset.card_erase_le

#leansearch "0 as an element of Fin n?"

#check Nat.pos_of_ne_zero

lemma removal_decrease_card {α : Type} [DecidableEq α] [Fintype α] (s : Finset α) (a : α) : (Finset.erase s a).card < s.card :=
  by


#check Finset.erase

def Matrix.minor {m n : ℕ} {α : Type} [Zero α] (A : Matrix (Fin m) (Fin n) α) (h₁ : m ≠ 0) (h₂ : n ≠ 0) : Matrix (Fin (m-1)) (Fin (n-1)) α :=
  submatrix A (Finset.univ.erase ⟨0, by apply Nat.pos_of_ne_zero h₁⟩) (Finset.univ.erase ⟨0, by apply Nat.pos_of_ne_zero h₂⟩)


lemma inc_lap {V : Type} [DecidableEq V] (G : SimpleGraph V) :




end SimpleGraph

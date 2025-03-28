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

-- define permutations of length n in Fin m


def listSubsetsOfSize {α : Type} : ℕ → List α → List (List α)
  | 0, _ => [[]]
  | _, [] => []
  | (m+1), x :: xs =>
      (listSubsetsOfSize m xs).map (fun ys => x :: ys) ++ listSubsetsOfSize (m+1) xs

#eval listSubsetsOfSize 2 [1,2,3,4]

#check Finset (Fin 2)

noncomputable def submatrix {n m : ℕ} {α : Type} [Zero α] (A : Matrix (Fin n) (Fin m) α) (rows : Finset (Fin n)) (cols : Finset (Fin m)) : Matrix (Fin rows.card) (Fin cols.card) α :=
  fun i j => A (rows.toList.get ⟨i.1, by simp [i.2]⟩) (cols.toList.get ⟨j.1, by simp [j.2]⟩)


lemma toprove_cauchybinet {m n : Nat} (A : Matrix (Fin n) (Fin m) Int) (B : Matrix (Fin m) (Fin n) Int) :
  ∀ a : Int, a^m * (a • (I n) + A * B).det = a^n * (a • (I m) + B * A).det :=
  sorry

theorem CauchyBinet {m n : Nat} (M : Matrix (Fin m) (Fin n) Int) (N : Matrix (Fin n) (Fin m) Int) :
  (M * N).det = ∑ sorry

#check CategoryTheory.Mat.id_apply_self



end SimpleGraph

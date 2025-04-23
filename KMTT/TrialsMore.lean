import Mathlib
--import Graph.SimpleGraph

import Mathlib.Data.Sym.Sym2
#print Quot.lift
#print Sym2
def Sym2.toProd' (s : Sym2 ℕ) : ℕ × ℕ :=
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
            simp [Nat.le_of_lt, h']
          simp [h'']
        else
          simp [h']
          if h'' : d < c then
            simp [h'']
          else
            intro h'''
            cases h'''
            case refl => simp
            case step h_new => simp [h',h'']
                               rename_i m
                               cases Nat.lt_trichotomy c m
                               case inl hlt =>
                                apply And.intro
                                · simp [hlt] at h'
                                  revert h' h''
                                  omega
                                · simp [hlt] at h'
                                  revert h' h''
                                  omega
                               case inr hge =>
                                  cases hge
                                  case inl heq =>
                                    simp [heq] at h'
                                  case inr hgt =>
                                    apply And.intro
                                    · simp [hgt] at h'
                                      revert h' h''
                                      omega
                                    · simp [hgt] at h'
                                      revert h' h''
                                      omega) s



def Sym2.toProd {α : Type} [LinearOrder α] (s : Sym2 α) : α × α :=
  Quot.lift
    (fun (a, b) => if a < b then (a, b) else (b, a))
    (by sorry) s



variable {V : Type} [DecidableEq V]

open SimpleGraph

#print Sym2
#print SimpleGraph
#print SimpleGraph.lapMatrix
#print SimpleGraph.incMatrix    --need to understand
#print SimpleGraph.adjMatrix

#print incMatrix
#print SimpleGraph.Adj
--#moogle "Sym2 α to α × α?"





#print Matrix

def SimpleGraph.IncidenceMatrix {V : Type} [DecidableEq V][LinearOrder V](G : SimpleGraph V) : Matrix V G.Edges Int :=
  fun v e =>
    let (a, b) := Sym2.toProd e
    if v = a then 1
    else if v = b then -1
    else 0

def I {n : Nat} : Matrix (Fin n) (Fin n) Int := 1

alias SimpleGraph.Inc := SimpleGraph.IncidenceMatrix
alias L := lapMatrix
alias A := adjMatrix

def listSubsetsOfSize {α : Type} : ℕ → List α → List (List α)
  | 0, _ => [[]]
  | _, [] => []
  | (m+1), x :: xs =>
      (listSubsetsOfSize m xs).map (fun ys => x :: ys) ++ listSubsetsOfSize (m+1) xs

#eval listSubsetsOfSize 2 [1,2,3,4]

#check Finset (Fin 2)

noncomputable def submatrix' {n m : ℕ} {α : Type} [Zero α] (A : Matrix (Fin n) (Fin m) α)
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

def zero_to_n_minus_one (n : Nat) : Finset (Fin n) := Finset.univ

#check Finset.card_univ

theorem zero_to_n_minus_one_card_eq_n {n : ℕ} : (zero_to_n_minus_one n).card = n := by
  simp [zero_to_n_minus_one, Finset.card_univ]

noncomputable def Matrix.rowBlocks {n m : ℕ} (N : Matrix (Fin n) (Fin m) Int) (s : Finset (Fin m)) : Matrix (Fin n) (Fin s.card) Int
        := by rw [← @zero_to_n_minus_one_card_eq_n n] ; exact submatrix' N (zero_to_n_minus_one n) s



noncomputable def Matrix.colBlocks {n m : ℕ } (N : Matrix (Fin n) (Fin m) Int) (s : Finset (Fin n)) : Matrix (Fin s.card) (Fin m) Int
  := by rw [← @zero_to_n_minus_one_card_eq_n m] ; exact submatrix' N s (zero_to_n_minus_one m)


theorem CauchyBinet {m n : Nat} (M : Matrix (Fin m) (Fin n) Int) (N : Matrix (Fin n) (Fin m) Int) :
  (M * N).det = ∑ s ∈ all_subsets_of_size n m,
  (Matrix.colBlocks M s).det * (Matrix.rowBlocks N s).det :=
  by sorry

#check Finset.card_erase_le
#check Nat.pos_of_ne_zero
#check Finset.erase

lemma inc_incT_eq_lap {n : ℕ} (G : SimpleGraph (Fin n))[DecidableRel G.Adj]
  :
  G.Inc * G.Inc.transpose = (G.lapMatrix : Matrix (Fin n) (Fin n) ℤ) :=
    by sorry



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

def spanningTree [LinearOrder V] (G : SimpleGraph V) (T : SimpleGraph V) : Prop :=
  tree T ∧ T.Edges ⊆ G.Edges

#print Set

end SimpleGraph
def Set.cardinality {α : Type}  (s : Set α) [Fintype s] : Nat :=
  (s.toFinset).card

def subsets {α : Type} (s : Set α) (n : Nat) : Set (Set α) :=
  { t | t ⊆ s ∧ @Set.cardinality _ t = n }

def spanningtrees {V : Type} [DecidableEq V][LinearOrder V] (G : SimpleGraph V) : Set (SimpleGraph V) :=
  { T | SimpleGraph.tree T ∧ T.Vertices = G.Vertices ∧ T.Edges ⊆ G.Edges }


/-- Kirchhoff’s Matrix Tree Theorem.
For a graph `G` on vertices `Fin (n+1)` (with a suitable ordering) and with an edge set that can be
identified with `Fin (m+1)`, the determinant of the minor (obtained by removing the first row and column)
of its Laplacian equals the number of spanning trees of `G`. -/
theorem kirchhoff_matrix_tree_theorem {n m : ℕ} (G : SimpleGraph (Fin (n + 1)))
  [LinearOrder (Fin (n + 1))]
  [Fintype { e : Sym2 (Fin (n + 1)) // G.Adj e.toProd.1 e.toProd.2 }]
  [LinearOrder { e : Sym2 (Fin (n + 1)) // G.Adj e.toProd.1 e.toProd.2 }]
  (h : Fintype.card { e : Sym2 (Fin (n + 1)) // G.Adj e.toProd.1 e.toProd.2 } = m + 1)
  : det (Matrix.minorFirst (Laplacian G)) = (spanningtrees G).cardinality :=
by

  rw [inc_incT_eq_lap]
  have cb := Matrix.det_mul' (SimpleGraph.IncidenceMatrix G).transpose (SimpleGraph.IncidenceMatrix G)
  rw [cb]
  rw [spanning_tree_sum_eq]

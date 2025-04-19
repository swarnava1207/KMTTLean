import Mathlib
--import Graph.SimpleGraph

import Mathlib.Data.Sym.Sym2
#print Quot.lift
#print Sym2


#check le_or_gt

#check PartialOrder
open SimpleGraph

#print Sym2
#print SimpleGraph
#print SimpleGraph.lapMatrix
#print SimpleGraph.incMatrix    --need to understand
#print SimpleGraph.adjMatrix
#print SimpleGraph.edgeSet
#print incMatrix
#print SimpleGraph.Adj
--#moogle "Sym2 α to α × α?"
#print Finset.toList
#print Finset
#print Decidable


variable {V : Type} [DecidableEq V] [Fintype V][LinearOrder V]



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

/-- **To be removed** -/
noncomputable def SimpleGraph.Edges (G : SimpleGraph V) [DecidableRel G.Adj] : List (Sym2 V) :=
  List.filter (fun e => e ∈ G.edgeSet) (Finset.sym2 Finset.univ).toList

#print Matrix

noncomputable def SimpleGraph.IncidenceMatrix {V : Type} [DecidableEq V][Fintype V][LinearOrder V](G : SimpleGraph V)[DecidableRel G.Adj]
  : Matrix V (Fin (G.Edges.length)) ℚ :=
  fun v e =>
    let (a, b) := Sym2.toProd (G.Edges.get e)
    if v = a then 1
    else if v = b then -1
    else 0

alias SimpleGraph.Inc := SimpleGraph.IncidenceMatrix


def I {n : Nat} : Matrix (Fin n) (Fin n) ℚ := 1

--alias SimpleGraph.Inc := SimpleGraph.IncidenceMatrix
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

/-
⊢ {α : Type u_1} → (p : α → Prop) → [inst : DecidablePred p] → (l : Finset α) → (∃! a, a ∈ l ∧ p a) → α
-/
#check Finset.choose

def zero_to_n_minus_one (n : Nat) : Finset (Fin n) := Finset.univ

#check Finset.card_univ

theorem zero_to_n_minus_one_card_eq_n {n : ℕ} : (zero_to_n_minus_one n).card = n := by
  simp [zero_to_n_minus_one, Finset.card_univ]

noncomputable def Matrix.rowBlocks {n m : ℕ} (N : Matrix (Fin n) (Fin m) ℚ) (s : Finset (Fin m)) : Matrix (Fin n) (Fin s.card) ℚ
        := by rw [← @zero_to_n_minus_one_card_eq_n n] ; exact submatrix' N (zero_to_n_minus_one n) s



noncomputable def Matrix.colBlocks {n m : ℕ } (N : Matrix (Fin n) (Fin m) ℚ) (s : Finset (Fin n)) : Matrix (Fin s.card) (Fin m) ℚ
  := by rw [← @zero_to_n_minus_one_card_eq_n m] ; exact submatrix' N s (zero_to_n_minus_one m)

def List.remove {α : Type} (l : List α) (i : ℕ) (h : i < l.length) : List α :=
  match l with
  | [] => []
  | x :: xs =>
    if h' : i = 0 then xs
    else x :: List.remove xs (i - 1) (by
    simp_all only [length_cons]
    ; omega )

#eval List.remove [1,2,3,4] 2 (by simp)

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


#print Finset.equivFin
#print List.choose

-- def SimpleGraph.degree (G : SimpleGraph V) (v : V) : ℕ
--   := G.degMatrix v v

noncomputable def SimpleGraph.IncMinor {n : ℕ} (G : SimpleGraph (Fin (n + 1))) [DecidableRel G.Adj]
        : Matrix (Fin n) (Fin (G.Edges.length - 1)) ℚ :=
        let m : ℕ := G.Edges.length
        if h' : m = 0 then
          fun i j => 0
        else
          let edge_filter : List (Sym2 (Fin (n + 1))) :=
            G.Edges.remove (m-1) (by simp [m]; omega)
        --let m : ℕ := edge_filter.length
        have m_eq : edge_filter.length = G.Edges.length - 1 := by
          simp [edge_filter]
          apply remove_length
        fun i j =>
          let e := edge_filter.get (by rw [m_eq]; exact j)
          let (a, b) := Sym2.toProd e
          if i = a then 1
          else if i = b then -1
          else 0

#check Finset.card_erase_le
#check Nat.pos_of_ne_zero
#check Finset.erase
#check SimpleGraph
#check SimpleGraph.lapMatrix

#check SimpleGraph.degree
#moogle "Sum of an indicator function."
#check Finset.sum_boole

theorem inc_incT_diag_degree (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∀ v, (G.Inc * G.Inc.transpose) v v = G.degree v := by
  intro v
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  let p (x : Fin (G.Edges.length)) : Prop := G.Inc v x * G.Inc v x = 1
  ]





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









#synth AddGroupWithOne ℚ

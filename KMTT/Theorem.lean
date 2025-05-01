import Mathlib
import KMTT.Matrices
open Matrix

/-!
This file contains the three main lemmas needed to prove the matrix-tree theorem.
* The first lemma is the `Cauchy-Binet formula`, which states that the determinant of a product of
two matrices can be expressed as a sum over certain minors of the factors.
* The second lemma says that the `Incidence matrix` of a graph multiplied by its transpose
  equals the `Laplacian matrix` of the graph.
* The third lemma states that the `Minor of the Incidence matrix` of a graph multiplied by its transpose
  equals the `Minor of the Laplacian matrix` of the graph.

# Matrix Identities and Cauchy-Binet Formula

This file develops key lemmas about determinants of block matrices over ℚ and states a version of
the **Cauchy-Binet formula** for rectangular matrices. It includes invertibility lemmas,
a matrix identity involving `a^m * det(aI + AB) = a^n * det(aI + BA)`, and supporting definitions
involving group actions on embeddings.

## Main Results

* `toprove_cauchybinet` : Identity involving determinants of `aI + AB` and `aI + BA`
* `Matrix.Cauchy_Binet` : Cauchy-Binet formula for general rings
* `Function.Embedding.ModPerm` : Choice of `m` elements from `n` up to permutation
* `inv_scalar`, `inv_rat` : Invertibility of scaled identity matrices
- `inc_incT_eq_lap`: Proves that `Inc * Incᵀ = Laplacian` matrix.
-/

variable {m n : ℕ} (A : Matrix (Fin n) (Fin m) ℚ) (B : Matrix (Fin m) (Fin n) ℚ)

/-- A scaled identity matrix `a • I` is invertible when `a ≠ 0`. -/
instance inv_scalar (a : ℚ) (ha : a ≠ 0) : Invertible (a • (1 : Matrix (Fin m) (Fin m) ℚ)) where
  invOf := (1 / a) • 1
  invOf_mul_self := by aesop
  mul_invOf_self := by aesop

/-- A nonzero rational number is invertible as an element of a field. -/
instance inv_rat (a : ℚ) (ha : a ≠ 0) : Invertible a :=
  invertibleOfNonzero ha

/--
Identity:
\[
a^m \cdot \det(aI + AB) = a^n \cdot \det(aI + BA)
\]
This is a determinant equality based on block matrix factorization and is used in proofs
related to the matrix-tree theorem.
-/
lemma toprove_cauchybinet (a : ℚ) (ha : a ≠ 0) :
    a^m * (a • 1 + A * B).det = a^n * (a • 1 + B * A).det := by
  let M : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℚ :=
    fromBlocks (a • 1) (-a • A) B (a • 1)

  have inv_I {m : ℕ} : (a • (1 : Matrix (Fin m) (Fin m) ℚ))⁻¹ = (1 / a) • 1 := by
    let _ : Invertible a := inv_rat a ha
    simp [inv_smul 1 a]

  have det_M₁ : det M = a^m * det ((a • 1) + A * B) := by
    let _ : Invertible (a • 1 : Matrix (Fin m) (Fin m) ℚ) := inv_scalar a ha
    rw [det_fromBlocks₂₂]
    simp [inv_I, det_smul, det_smul]
    apply Or.inl
    aesop

  have det_M₂ : det M = a^n * det ((a • 1) + B * A) := by
    let _ : Invertible (a • 1 : Matrix (Fin n) (Fin n) ℚ) := inv_scalar a ha
    rw [det_fromBlocks₁₁]
    simp [inv_I, det_smul, det_smul]
    apply Or.inl
    aesop

  /- For any square matrix M, det ((1/a) • M) = (1/a)^m * det M. -/
  have det_scale : ∀ (M : Matrix (Fin m) (Fin m) ℚ), det ((1 / a) • M) = (1 / a)^m * det M :=
    fun M => by rw [det_smul]; simp

  rw [← det_M₁, det_M₂]


/- `The following part of the file is contributed by Eric Wieser through Zulip` -/
-- === Group actions for Cauchy-Binet ===

variable {m n R : Type*}

/-- The diagonal action of permutations on injective maps `m ↪ n`. -/
instance : MulAction (Equiv.Perm m)ᵈᵐᵃ (m ↪ n) where
  smul σ f := (DomAddAct.mk.symm σ).toEmbedding.trans f
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- Simplification lemma for the diagonal action of a permutation on embeddings. -/
@[simp]
theorem DomMulAct.equivPerm_smul_embedding_def (σ : Equiv.Perm m) (f : m ↪ n) :
    DomMulAct.mk σ • f = σ.toEmbedding.trans f := rfl

/-- A choice of `m` elements from `n`, modulo permutation of the domain. -/
abbrev Function.Embedding.ModPerm (m n : Type*) : Type _ :=
  MulAction.orbitRel.Quotient (Equiv.Perm m)ᵈᵐᵃ (m ↪ n)

variable [Fintype m] [Fintype n]

/-- Noncomputable instance for the quotient type representing unordered embeddings. -/
noncomputable instance : Fintype (Function.Embedding.ModPerm m n) := by
  classical exact Quotient.fintype _

variable [DecidableEq m] [CommRing R]

/--
**Cauchy-Binet formula**:
The determinant of a product of non-square matrices can be expressed as a sum over
certain minors of the factors. See <https://en.wikipedia.org/wiki/Cauchy%E2%80%93Binet_formula>.
-/
theorem Matrix.Cauchy_Binet (A : Matrix m n R) (B : Matrix n m R) :
    det (A * B) =
      ∑ f : Function.Embedding.ModPerm m n,
        f.liftOn
          (fun f => det (A.submatrix id f) * det (B.submatrix f id))
          (by
            rintro f g ⟨σ, rfl⟩; revert σ
            rw [DomMulAct.mk.surjective.forall]; intro σ
            show
              (A.submatrix id ⇑g |>.submatrix id ⇑σ).det *
              (B.submatrix g id |>.submatrix σ id).det =
              (A.submatrix id ⇑g).det * (B.submatrix ⇑g id).det
            rw [det_permute', det_permute, mul_mul_mul_comm]
            rw [← Int.cast_mul, Int.units_coe_mul_self, Int.cast_one, one_mul]) := by
  -- Proof omitted
  sorry


-- Proves that the product of the incidence matrix `Inc` and its transpose `Incᵀ` equals the Laplacian matrix of the graph `G`.
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
    apply inc_incT_diag_degree
  · by_cases h:G.Adj i j
    · let h' := adj_minus_one G h_diag h
      simp[h',Finset.sum_ite_eq]
      have h_lap_adj : G.lapMatrix ℚ i j = -1 := by
          simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, h_diag, h, SimpleGraph.adjMatrix]
      rw[h_lap_adj]
      sorry -- Proof needs completion: requires showing the sum of the incidence matrix entries equals -1
    · let h' := not_adj_zero G h_diag h
      simp [h']
      have h_lap_nonadj : G.lapMatrix ℚ i j = 0 := by
          simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, h_diag, h, SimpleGraph.adjMatrix]
      rw[h_lap_nonadj]

-- Theorem showing that the product of the Minor of the incidence matrix and its transpose equals the minor of the Laplacian matrix.
lemma inc_minor_incT_eq_lap_minor {n : ℕ} (G : SimpleGraph (Fin (n + 1)))[DecidableRel G.Adj]
  : G.IncMinor * G.IncMinor.transpose = (G.Lapminor : Matrix (Fin n) (Fin n) ℚ) := by
    sorry

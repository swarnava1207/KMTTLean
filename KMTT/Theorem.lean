import Mathlib
open Matrix
variable {m n : ℕ} (A : Matrix (Fin n) (Fin m) ℚ ) (B : Matrix (Fin m) (Fin n) ℚ )

-- Main theorem: Cauchy–Binet–type determinant identity for rectangular matrices.
-- For A : n×m and B : m×n and any nonzero a ∈ \Z, we have
--
--   a^m * det (a • I n + A * B) = a^n * det (a • I m + B * A)
--
-- Helper lemma for index arithmetic.
lemma sub_lt_helper {a b c : ℕ} (hb : 0 < b ∨ b = 0) (h : a < b + c) : a - b < c :=
  by sorry


#print Fin
-- Definition of block matrix constructor.
def ofBlock {α : Type*} [Zero α] {m n p q : ℕ}
  (A : Matrix (Fin m) (Fin n) α)
  (B : Matrix (Fin m) (Fin q) α)
  (C : Matrix (Fin p) (Fin n) α)
  (D : Matrix (Fin p) (Fin q) α) :
  Matrix (Fin (m + p)) (Fin (n + q)) α :=
fun i j =>
if hi : i.val < m then
  if hj : j.val < n then
    A ⟨i, hi⟩ ⟨j, hj⟩
  else
    let j' : Fin q :=
      ⟨j - n, by apply sub_lt_helper; exact Or.symm (Nat.eq_zero_or_pos n); exact j.is_lt⟩
    B ⟨i, hi⟩ j'
else
  let i' : Fin p :=
    ⟨i - m, sub_lt_helper (Or.symm (Nat.eq_zero_or_pos m)) i.is_lt⟩ ;
  if hj : (j : ℕ) < n then
    C i' ⟨j, hj⟩
  else
    let j' : Fin q :=
      ⟨j - n, sub_lt_helper (Or.symm (Nat.eq_zero_or_pos n)) j.is_lt⟩ ;
    D i' j'

--#leansearch "Scalar matrices are invertible?"
#check Matrix.fromBlocks₁₁Invertible
abbrev I {m : ℕ}: Matrix (Fin m) (Fin m) ℚ := 1
#print Field
#print Invertible
#moogle "non-zero rationals are invertible."

instance inv_scalar (a : ℚ) (ha : a ≠ 0) : Invertible (a • (1 :(Matrix (Fin m) (Fin m) ℚ)) ) :=
  by sorry
instance inv_rat (a : ℚ) (ha : a ≠ 0) : Invertible a :=
  by exact invertibleOfNonzero ha

theorem toprove_cauchybinet (a : ℚ) (ha : a ≠ 0)  :
  a^m * (a • I + A * B).det = a^n * (a • I + B * A).det :=
by
  let M₁ : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℚ := fromBlocks (a • 1) (-a • A) (B) (a • 1)
  let M₂ : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℚ := fromBlocks (a • 1) (B) (-a • A) (a • 1)
  have det_M₁_M₂ : det M₁ = det M₂ :=
    by
      simp

  have inv_I {m : ℕ} : (a • ((1 :(Matrix (Fin m) (Fin m) ℚ))))⁻¹ = (1/a) • 1 :=
  by
    let i : Invertible a := by
      apply inv_rat a ha
    -- Standard fact: (a•I)⁻¹ = (1/a)•I over a field when a ≠ 0.
    simp [inv_smul 1 a]


  have det_M₁ : det M₁ = a^m * det ((a • 1) + A * B) :=
    by
    let i : Invertible (a • (1 :(Matrix (Fin m) (Fin m) ℚ))) := by
      apply inv_scalar a ha
    rw [det_fromBlocks₂₂]
    simp [inv_I, det_smul, det_smul]
    apply Or.inl
    aesop

  have det_M₂ : det M₂ = a^n * det ((a • 1) + B * A) :=
    by
    let i : Invertible (a • (1 :(Matrix (Fin n) (Fin n) ℚ))) := by
      apply inv_scalar a ha
    rw [det_fromBlocks₂₂]
    simp [inv_I, det_smul, det_smul]
    apply Or.inl
    aesop

  /- Factor out the scalar from the bloc\Z in the second determinant.
     Note that for an m×m matrix M, det ((1/a) • M) = (1/a)^m * det M.
  -/
  have det_scale : ∀ (M : Matrix (Fin m) (Fin m) ℚ), det ((1/a) • M) = (1/a)^m * det M :=
    fun M => by rw [det_smul]; simp





  rw [← det_M₁, det_M₁']

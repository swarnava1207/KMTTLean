import Mathlib
open Matrix


variable {m n : ℕ} (A : Matrix (Fin n) (Fin m) ℤ ) (B : Matrix (Fin m) (Fin n) ℤ )

-- Main theorem: Cauchy–Binet–type determinant identity for rectangular matrices.
-- For A : n×m and B : m×n and any nonzero a ∈ \Z, we have
--
--   a^m * det (a • I n + A * B) = a^n * det (a • I m + B * A)
--
-- Helper lemma for index arithmetic.
lemma sub_lt_helper {a b c : ℕ} (hb : 0 < b ∨ b = 0) (h : a < b + c) : a - b < c :=
by
  
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

#check Matrix.fromBlocks₁₁Invertible
def I {m : ℕ}: Matrix (Fin m) (Fin m) ℤ := 1

theorem toprove_cauchybinet (a : ℤ) (ha : a ≠ 0)  :
  a^m * (a • I + A * B).det = a^n * (a • I + B * A).det :=
by
  let M : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℤ := fromBlocks (a • 1) (-A) (B) (a • 1)
  have inv_I {m : ℕ} : (a • (@I m))⁻¹ = (1/a) • 1 :=
  by
    -- Standard fact: (a•I)⁻¹ = (1/a)•I over a field when a ≠ 0.
    --apply @inv_smul inferInstance inferInstance inferInstance I a inferInstance
    sorry

  have det_M₁ : det M = a^m * det ((a • I) + A * B) :=
    by rw [det_fromBlocks₂₂]
  /- Factor out the scalar from the bloc\Z in the second determinant.
     Note that for an m×m matrix M, det ((1/a) • M) = (1/a)^m * det M.
  -/
  have det_scale : ∀ (M : Matrix (Fin m) (Fin m) ℤ), det ((1/a) • M) = (1/a)^m * det M :=
    fun M => by rw [det_smul]; simp

  have det_M₁' : det M = a^n * det ((a • I) +  B * A) :=
    by sorry

  rw [← det_M₁, det_M₁']

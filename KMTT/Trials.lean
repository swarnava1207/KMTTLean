import Mathlib

variable {m n R : Type*}

-- This probably belongs in mathlib
instance : MulAction (Equiv.Perm m)ᵈᵐᵃ (m ↪ n) where
  smul σ f := (DomAddAct.mk.symm σ).toEmbedding.trans f
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp]
theorem DomMulAct.equivPerm_smul_embedding_def (σ : Equiv.Perm m) (f : m ↪ n) :
    DomMulAct.mk σ • f = σ.toEmbedding.trans f := rfl

/-- A choice of `m` elements of `n`. -/
abbrev Function.Embedding.ModPerm (m n : Type*) : Type _ :=
  -- or could build the quotient manually
  MulAction.orbitRel.Quotient (Equiv.Perm m)ᵈᵐᵃ (m ↪ n)

variable [Fintype m] [Fintype n]

-- this is a hack, a decidable algorithm would be better!
noncomputable instance : Fintype (Function.Embedding.ModPerm m n) := by
  classical exact Quotient.fintype _

variable [DecidableEq m] [CommRing R]

open Nat

/-- Cauchy-Binet, https://en.wikipedia.org/wiki/Cauchy%E2%80%93Binet_formula -/
theorem Matrix.det_mul' (A : Matrix m n R) (B : Matrix n m R) :
    det (A * B) = ∑ f : Function.Embedding.ModPerm m n,
      f.liftOn
        (fun f => det (A.submatrix id f) * det (B.submatrix f id))
        (by
          rintro f g ⟨σ, rfl⟩; revert σ; rw [DomMulAct.mk.surjective.forall]; intro σ
          show (A.submatrix id ⇑g |>.submatrix id ⇑σ).det * (B.submatrix g id |>.submatrix σ id).det = (A.submatrix id ⇑g).det * (B.submatrix (⇑g) id).det
          rw [det_permute', det_permute, mul_mul_mul_comm]
          rw [← Int.cast_mul, Int.units_coe_mul_self, Int.cast_one, one_mul]) := by
  -- real proof starts here
  sorry




#print Quot
#print Quot.lift

abbrev NatPair := Quot (α := Nat × Nat)
    (fun (a, b) (c, d) => a = d && b = c)

def smaller : NatPair → Nat :=
  Quot.lift (fun (a, b) => if a < b then a else b)
  (by                       -- ∀ (a b : α), r a b → f a = f b
    intro (a, b) (c, d)
    simp
    intro h₁ h₂
    rw [← h₁, ← h₂]
    if h: a < b then
      simp [h]
      have h' : ¬ b <a := by
        simp [Nat.le_of_lt, h]
      simp [h']
    else
      simp [h]
      if h': b < a then
        simp [h']
      else
        simp [h']
        cases Nat.lt_trichotomy a b
        case inl hlt =>
          simp [hlt] at h
        case inr hge =>
          cases hge
          case inl heq =>
            simp [heq]
          case inr hgt =>
            simp [hgt] at h'
    )


def larger : NatPair → Nat :=
  Quot.lift (fun (a, b) => if a < b then b else a)
  (by
    intro (a, b) (c, d)
    simp
    intro h₁ h₂
    rw [← h₁, ← h₂]
    if h: a < b then
      simp [h]
      have h' : ¬ b <a := by
        simp [Nat.le_of_lt, h]
      simp [h']
    else
      simp [h]
      if h': b < a then
        simp [h']
      else
        simp [h']
        cases Nat.lt_trichotomy a b
        case inl hlt =>
          simp [hlt] at h
        case inr hge =>
          cases hge
          case inl heq =>
            simp [heq]
          case inr hgt =>
            simp [hgt] at h'
    )

#print Quot.mk
abbrev NatPair.mk (a b : Nat) : NatPair :=
  Quot.mk (α := Nat × Nat) (fun (a, b) (c, d) => a = d && b = c) ((a, b) : Nat × Nat)

theorem smaller_le_larger (a b : Nat):
  smaller (NatPair.mk a b) ≤
    larger (NatPair.mk a b) :=
  by
    rw [NatPair.mk, smaller, larger]
    simp
    if h:a < b then
      simp [h]
      exact Nat.le_of_lt h
    else
      simp [h]
      exact Nat.le_of_not_gt h

#check Quot.ind

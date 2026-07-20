import ArithmeticHodge.Analysis.RationalPosDefCertificate

open Matrix
open scoped ComplexOrder

namespace ArithmeticHodge.Analysis

/-!
# Rational semidefinite factorization certificates

Unlike positive-definite LDL certificates, a positive-semidefinite Gram
factorization may contain zero diagonal pivots and its factor need not be
invertible.  The following replay lemmas retain exactly that weaker shape.
-/

/-- An exact rational `L * diagonal d * Lᴴ` factorization with nonnegative
diagonal entries certifies positive semidefiniteness after casting to the
reals.  No invertibility hypothesis on `L` is needed. -/
theorem rationalLDL_posSemidef_real
    {n : Type*} [Fintype n] [DecidableEq n]
    (A L : Matrix n n ℚ) (d : n → ℚ)
    (hd : ∀ i, 0 ≤ d i)
    (hA : A = L * Matrix.diagonal d * Lᴴ) :
    Matrix.PosSemidef ((Rat.castHom ℝ).mapMatrix A) := by
  rw [hA, map_mul, map_mul]
  rw [show (Rat.castHom ℝ).mapMatrix Lᴴ =
      ((Rat.castHom ℝ).mapMatrix L)ᴴ by
    ext i j
    simp [RingHom.mapMatrix_apply]]
  have hdiag : Matrix.PosSemidef
      ((Rat.castHom ℝ).mapMatrix (Matrix.diagonal d)) := by
    rw [RingHom.mapMatrix_apply,
      Matrix.diagonal_map (map_zero (Rat.castHom ℝ))]
    apply Matrix.PosSemidef.diagonal
    intro i
    exact (Rat.cast_nonneg (K := ℝ)).2 (hd i)
  exact hdiag.mul_mul_conjTranspose_same
    ((Rat.castHom ℝ).mapMatrix L)

/-- Complex-valued analogue of `rationalLDL_posSemidef_real`. -/
theorem rationalLDL_posSemidef_complex
    {n : Type*} [Fintype n] [DecidableEq n]
    (A L : Matrix n n ℚ) (d : n → ℚ)
    (hd : ∀ i, 0 ≤ d i)
    (hA : A = L * Matrix.diagonal d * Lᴴ) :
    Matrix.PosSemidef ((Rat.castHom ℂ).mapMatrix A) := by
  rw [hA, map_mul, map_mul]
  rw [show (Rat.castHom ℂ).mapMatrix Lᴴ =
      ((Rat.castHom ℂ).mapMatrix L)ᴴ by
    ext i j
    simp [RingHom.mapMatrix_apply]]
  have hdiag : Matrix.PosSemidef
      ((Rat.castHom ℂ).mapMatrix (Matrix.diagonal d)) := by
    rw [RingHom.mapMatrix_apply,
      Matrix.diagonal_map (map_zero (Rat.castHom ℂ))]
    apply Matrix.PosSemidef.diagonal
    intro i
    change (0 : ℂ) ≤ (d i : ℂ)
    rw [Complex.nonneg_iff]
    simpa using hd i
  exact hdiag.mul_mul_conjTranspose_same
    ((Rat.castHom ℂ).mapMatrix L)

end ArithmeticHodge.Analysis

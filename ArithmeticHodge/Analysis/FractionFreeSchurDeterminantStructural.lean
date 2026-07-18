import Mathlib.LinearAlgebra.Matrix.SchurComplement

set_option autoImplicit false

open Matrix

namespace ArithmeticHodge.Analysis.FractionFreeSchurDeterminantStructural

noncomputable section

/-!
# Fraction-free Schur determinant

Clearing the leading determinant from a Schur complement commutes with
taking its determinant.  The identity below is stated over a field only to
use the ordinary inverse in its short proof; its conclusion is division-free.
-/

/-- Determinant of the fraction-free Schur complement of an invertible
leading block. -/
theorem det_det_smul_sub_mul_adjugate_mul
    {m n K : Type*}
    [DecidableEq m] [Fintype m]
    [DecidableEq n] [Fintype n] [Nonempty n]
    [Field K]
    (A : Matrix m m K) (B : Matrix m n K)
    (C : Matrix n m K) (D : Matrix n n K)
    (hA : A.det ≠ 0) :
    Matrix.det (A.det • D - C * A.adjugate * B) =
      A.det ^ (Fintype.card n - 1) *
        Matrix.det (Matrix.fromBlocks A B C D) := by
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
  letI : Invertible A := Matrix.invertibleOfIsUnitDet A hunit
  have hadjugate : A.det • ⅟A = A.adjugate := by
    change A.det • A⁻¹ = A.adjugate
    rw [Matrix.inv_def, smul_smul]
    simp [hA]
  have hfractionFree :
      A.det • D - C * A.adjugate * B =
        A.det • (D - C * ⅟A * B) := by
    rw [smul_sub]
    congr 1
    rw [← hadjugate, Matrix.mul_smul, Matrix.smul_mul]
  rw [hfractionFree, Matrix.det_smul, Matrix.det_fromBlocks₁₁]
  have hcard : 1 ≤ Fintype.card n := Fintype.card_pos
  calc
    A.det ^ Fintype.card n * (D - C * ⅟A * B).det =
        (A.det ^ (Fintype.card n - 1) * A.det) *
          (D - C * ⅟A * B).det := by
      rw [← pow_succ, Nat.sub_add_cancel hcard]
    _ = A.det ^ (Fintype.card n - 1) *
        (A.det * (D - C * ⅟A * B).det) := by ring

end


end ArithmeticHodge.Analysis.FractionFreeSchurDeterminantStructural

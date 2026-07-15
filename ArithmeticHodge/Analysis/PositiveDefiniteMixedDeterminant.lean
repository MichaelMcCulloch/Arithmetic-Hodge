import ArithmeticHodge.Analysis.RationalIntervalSchur
import Mathlib.Analysis.Matrix.Order

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.PositiveDefiniteMixedDeterminant

noncomputable section

open Matrix
open scoped ComplexOrder MatrixOrder
open RationalIntervalSchur

variable {n : Type*} [Fintype n] [DecidableEq n]

set_option backward.isDefEq.respectTransparency false in
/-- The Frobenius pairing of two complex positive-definite matrices is
strictly positive.  Writing the second form as `Cᵀ C` turns the pairing
into the trace of the positive-definite congruence `C A Cᵀ`. -/
theorem trace_mul_pos_of_posDef
    {A B : Matrix n n ℂ} [Nonempty n]
    (hA : A.PosDef) (hB : B.PosDef) :
    0 < Matrix.trace (A * B) := by
  have hfac : ∃ C : Matrix n n ℂ, IsUnit C ∧ B = star C * C :=
    (CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self (a := B)).mp
      hB.isStrictlyPositive
  obtain ⟨C, hC, hBfac⟩ := hfac
  rw [Matrix.star_eq_conjTranspose] at hBfac
  subst B
  have hCinj : Function.Injective C.vecMul :=
    Matrix.vecMul_injective_iff_isUnit.mpr hC
  have hcongr : (C * A * Cᴴ).PosDef :=
    hA.mul_mul_conjTranspose_same hCinj
  rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle]
  exact hcongr.trace_pos

/-- Real specialization of `trace_mul_pos_of_posDef`, obtained by entrywise
complexification. -/
theorem real_trace_mul_pos_of_posDef
    {A B : Matrix n n ℝ} [Nonempty n]
    (hA : A.PosDef) (hB : B.PosDef) :
    0 < Matrix.trace (A * B) := by
  have hcomplex := trace_mul_pos_of_posDef
    hA.complexOfReal hB.complexOfReal
  have hmul :
      complexOfRealMatrix A * complexOfRealMatrix B =
        complexOfRealMatrix (A * B) := by
    ext i j
    simp only [Matrix.mul_apply, complexOfRealMatrix, Complex.ofReal_sum,
      Complex.ofReal_mul]
  rw [hmul] at hcomplex
  have hreal := (Complex.pos_iff.mp hcomplex).1
  simpa [Matrix.trace, complexOfRealMatrix] using hreal

end

end ArithmeticHodge.Analysis.PositiveDefiniteMixedDeterminant

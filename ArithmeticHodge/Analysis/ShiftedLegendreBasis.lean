import ArithmeticHodge.Analysis.ShiftedLegendreOrthogonality
import Mathlib.Algebra.Polynomial.Sequence

set_option autoImplicit false

open Polynomial Set Submodule

namespace ArithmeticHodge.Analysis.ShiftedLegendreBasis

noncomputable section

open ShiftedLegendreOrthogonality

/-!
# The shifted-Legendre polynomial basis

The integer shifted Legendre family keeps degree `n` after transport to
`ℝ`.  Its strict degree growth makes it a polynomial sequence; since every
nonzero real leading coefficient is a unit, `Polynomial.Sequence` supplies
spanning and a basis without any degree cutoff.
-/

@[simp]
theorem degree_shiftedLegendreReal (n : ℕ) :
    (shiftedLegendreReal n).degree = n := by
  rw [shiftedLegendreReal,
    Polynomial.degree_map_eq_of_injective Int.cast_injective,
    Polynomial.degree_shiftedLegendre]

@[simp]
theorem natDegree_shiftedLegendreReal (n : ℕ) :
    (shiftedLegendreReal n).natDegree = n := by
  exact Polynomial.natDegree_eq_of_degree_eq_some
    (degree_shiftedLegendreReal n)

theorem shiftedLegendreReal_ne_zero (n : ℕ) :
    shiftedLegendreReal n ≠ 0 := by
  exact Polynomial.degree_ne_bot.mp (by simp)

/-- Distinct shifted Legendre polynomials are orthogonal on `[0,1]`. -/
theorem integral_shiftedLegendreReal_mul_eq_zero
    {m n : ℕ} (hmn : m ≠ n) :
    (∫ x : ℝ in 0..1,
      (shiftedLegendreReal m).eval x *
        (shiftedLegendreReal n).eval x) = 0 := by
  rcases lt_or_gt_of_ne hmn with hmn | hnm
  · exact integral_eval_mul_shiftedLegendreReal_eq_zero n
      (shiftedLegendreReal m) (by simpa using hmn)
  · calc
      (∫ x : ℝ in 0..1,
          (shiftedLegendreReal m).eval x *
            (shiftedLegendreReal n).eval x) =
          ∫ x : ℝ in 0..1,
            (shiftedLegendreReal n).eval x *
              (shiftedLegendreReal m).eval x := by
            apply intervalIntegral.integral_congr
            intro x _hx
            ring
      _ = 0 := integral_eval_mul_shiftedLegendreReal_eq_zero m
        (shiftedLegendreReal n) (by simpa using hnm)

/-- The shifted Legendre family packaged as a polynomial sequence. -/
def shiftedLegendreRealSequence : Polynomial.Sequence ℝ where
  elems' := shiftedLegendreReal
  degree_eq' := degree_shiftedLegendreReal

@[simp]
theorem shiftedLegendreRealSequence_apply (n : ℕ) :
    shiftedLegendreRealSequence n = shiftedLegendreReal n := rfl

theorem shiftedLegendreReal_leadingCoeff_isUnit (n : ℕ) :
    IsUnit (shiftedLegendreReal n).leadingCoeff := by
  rw [isUnit_iff_ne_zero]
  exact Polynomial.leadingCoeff_ne_zero.mpr (shiftedLegendreReal_ne_zero n)

/-- The shifted Legendre sequence is linearly independent over `ℝ`. -/
theorem shiftedLegendreReal_linearIndependent :
    LinearIndependent ℝ shiftedLegendreReal := by
  exact shiftedLegendreRealSequence.linearIndependent

/-- The shifted Legendre polynomials span every real polynomial. -/
theorem shiftedLegendreReal_span_eq_top :
    Submodule.span ℝ (Set.range shiftedLegendreReal) = ⊤ := by
  exact shiftedLegendreRealSequence.span
    shiftedLegendreReal_leadingCoeff_isUnit

/-- The algebraic shifted-Legendre basis of `ℝ[X]`. -/
def shiftedLegendreRealBasis : Module.Basis ℕ ℝ ℝ[X] :=
  shiftedLegendreRealSequence.basis
    shiftedLegendreReal_leadingCoeff_isUnit

@[simp]
theorem shiftedLegendreRealBasis_apply (n : ℕ) :
    shiftedLegendreRealBasis n = shiftedLegendreReal n := by
  simpa only [shiftedLegendreRealBasis, shiftedLegendreRealSequence_apply] using
    Polynomial.Sequence.basis_eq_self shiftedLegendreRealSequence
      shiftedLegendreReal_leadingCoeff_isUnit n

end

end ArithmeticHodge.Analysis.ShiftedLegendreBasis

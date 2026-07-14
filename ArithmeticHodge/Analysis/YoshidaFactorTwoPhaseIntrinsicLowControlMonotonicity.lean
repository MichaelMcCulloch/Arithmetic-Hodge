import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowControlsPositive

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowControlMonotonicity

noncomputable section

open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicLowControlsPositive

/-!
# Structural monotonicity gates for the intrinsic low controls

The three successive differences of the cubic Bernstein controls have much
smaller exact descriptions than an entrywise expansion of the controls.  In
particular, the two adjugate coefficients cancel from the middle difference,
while the last difference contains their sum with a positive sign.

Everything in this file is exact algebra.  No phase sampling, finite mode
enumeration, interval subdivision, or numerical enclosure is used.
-/

/-! ## Power-basis descriptions of the three steps -/

/-- The first Bernstein step is one third of the linear power coefficient. -/
theorem factorTwoIntrinsicBoundaryControlStep01_eq_power1_div_three
    (c d : ℝ) :
    factorTwoIntrinsicBoundaryControlStep01 c d =
      factorTwoIntrinsicBoundaryPower1 c d / 3 := by
  unfold factorTwoIntrinsicBoundaryControlStep01
    factorTwoIntrinsicBoundaryControl0 factorTwoIntrinsicBoundaryControl1
  ring

/-- The middle Bernstein step is one third of the sum of the linear and
quadratic power coefficients. -/
theorem factorTwoIntrinsicBoundaryControlStep12_eq_power1_add_power2_div_three
    (c d : ℝ) :
    factorTwoIntrinsicBoundaryControlStep12 c d =
      (factorTwoIntrinsicBoundaryPower1 c d +
        factorTwoIntrinsicBoundaryPower2 c d) / 3 := by
  unfold factorTwoIntrinsicBoundaryControlStep12
    factorTwoIntrinsicBoundaryControl1 factorTwoIntrinsicBoundaryControl2
  ring

/-- The last Bernstein step is the endpoint derivative of the power-basis
cubic, divided by three. -/
theorem factorTwoIntrinsicBoundaryControlStep23_eq_power_derivative_div_three
    (c d : ℝ) :
    factorTwoIntrinsicBoundaryControlStep23 c d =
      (factorTwoIntrinsicBoundaryPower1 c d +
        2 * factorTwoIntrinsicBoundaryPower2 c d +
        3 * factorTwoIntrinsicBoundaryPower3 c d) / 3 := by
  unfold factorTwoIntrinsicBoundaryControlStep23
    factorTwoIntrinsicBoundaryControl2 factorTwoIntrinsicBoundaryControl3
  ring

/-! ## Cancellative Schur descriptions -/

/-- Exact first-step Schur gate. -/
theorem three_mul_factorTwoIntrinsicBoundaryControlStep01
    (c d : ℝ) :
    3 * factorTwoIntrinsicBoundaryControlStep01 c d =
      factorTwoIntrinsicEvenDetCoefficient0 *
          factorTwoIntrinsicOddDirectionQuadratic c d +
        factorTwoIntrinsicEvenDetCoefficient1 *
          factorTwoIntrinsicOddPhaseQuadratic 1 c d -
        factorTwoIntrinsicAdjugateCoefficient0 c d := by
  rw [factorTwoIntrinsicBoundaryControlStep01_eq_power1_div_three]
  unfold factorTwoIntrinsicBoundaryPower1
  ring

/-- Exact middle-step Schur gate.  The coefficient-zero adjugate term cancels
identically; only the direction coefficient remains. -/
theorem three_mul_factorTwoIntrinsicBoundaryControlStep12
    (c d : ℝ) :
    3 * factorTwoIntrinsicBoundaryControlStep12 c d =
      (factorTwoIntrinsicEvenDetCoefficient0 +
          factorTwoIntrinsicEvenDetCoefficient1) *
          factorTwoIntrinsicOddDirectionQuadratic c d +
        (factorTwoIntrinsicEvenDetCoefficient1 +
          factorTwoIntrinsicEvenDetCoefficient2) *
          factorTwoIntrinsicOddPhaseQuadratic 1 c d -
        factorTwoIntrinsicAdjugateCoefficient1 c d := by
  rw [factorTwoIntrinsicBoundaryControlStep12_eq_power1_add_power2_div_three]
  unfold factorTwoIntrinsicBoundaryPower1 factorTwoIntrinsicBoundaryPower2
  ring

/-- Exact last-step Schur gate.  Both adjugate coefficients occur with a
positive sign. -/
theorem three_mul_factorTwoIntrinsicBoundaryControlStep23
    (c d : ℝ) :
    3 * factorTwoIntrinsicBoundaryControlStep23 c d =
      (factorTwoIntrinsicEvenDetCoefficient0 +
          2 * factorTwoIntrinsicEvenDetCoefficient1 +
          3 * factorTwoIntrinsicEvenDetCoefficient2) *
          factorTwoIntrinsicOddDirectionQuadratic c d +
        (factorTwoIntrinsicEvenDetCoefficient1 +
          2 * factorTwoIntrinsicEvenDetCoefficient2) *
          factorTwoIntrinsicOddPhaseQuadratic 1 c d +
        factorTwoIntrinsicAdjugateCoefficient0 c d +
        factorTwoIntrinsicAdjugateCoefficient1 c d := by
  rw [factorTwoIntrinsicBoundaryControlStep23_eq_power_derivative_div_three]
  unfold factorTwoIntrinsicBoundaryPower1 factorTwoIntrinsicBoundaryPower2
    factorTwoIntrinsicBoundaryPower3
  ring

/-! ## Sharp homogeneous-quadratic gates -/

private theorem step01_expansion (c d : ℝ) :
    factorTwoIntrinsicBoundaryControlStep01 c d =
      intrinsicBinaryQuadratic00 factorTwoIntrinsicBoundaryControlStep01 * c ^ 2 +
        2 * intrinsicBinaryQuadratic02
          factorTwoIntrinsicBoundaryControlStep01 * c * d +
        intrinsicBinaryQuadratic22
          factorTwoIntrinsicBoundaryControlStep01 * d ^ 2 := by
  unfold intrinsicBinaryQuadratic00 intrinsicBinaryQuadratic02
    intrinsicBinaryQuadratic22
    factorTwoIntrinsicBoundaryControlStep01
    factorTwoIntrinsicBoundaryControl0 factorTwoIntrinsicBoundaryControl1
    factorTwoIntrinsicBoundaryPower0 factorTwoIntrinsicBoundaryPower1
    factorTwoIntrinsicOddPhaseQuadratic
    factorTwoIntrinsicOddDirectionQuadratic
    factorTwoIntrinsicAdjugateCoefficient0
    factorTwoIntrinsicEvenAdjugateCoupling
    factorTwoIntrinsicAlternatingRow0 factorTwoIntrinsicAlternatingRow2
  ring

private theorem step12_expansion (c d : ℝ) :
    factorTwoIntrinsicBoundaryControlStep12 c d =
      intrinsicBinaryQuadratic00 factorTwoIntrinsicBoundaryControlStep12 * c ^ 2 +
        2 * intrinsicBinaryQuadratic02
          factorTwoIntrinsicBoundaryControlStep12 * c * d +
        intrinsicBinaryQuadratic22
          factorTwoIntrinsicBoundaryControlStep12 * d ^ 2 := by
  unfold intrinsicBinaryQuadratic00 intrinsicBinaryQuadratic02
    intrinsicBinaryQuadratic22
    factorTwoIntrinsicBoundaryControlStep12
    factorTwoIntrinsicBoundaryControl1 factorTwoIntrinsicBoundaryControl2
    factorTwoIntrinsicBoundaryPower0 factorTwoIntrinsicBoundaryPower1
    factorTwoIntrinsicBoundaryPower2
    factorTwoIntrinsicOddPhaseQuadratic
    factorTwoIntrinsicOddDirectionQuadratic
    factorTwoIntrinsicAdjugateCoefficient0
    factorTwoIntrinsicAdjugateCoefficient1
    factorTwoIntrinsicEvenAdjugateCoupling
    factorTwoIntrinsicAlternatingRow0 factorTwoIntrinsicAlternatingRow2
  ring

private theorem step23_expansion (c d : ℝ) :
    factorTwoIntrinsicBoundaryControlStep23 c d =
      intrinsicBinaryQuadratic00 factorTwoIntrinsicBoundaryControlStep23 * c ^ 2 +
        2 * intrinsicBinaryQuadratic02
          factorTwoIntrinsicBoundaryControlStep23 * c * d +
        intrinsicBinaryQuadratic22
          factorTwoIntrinsicBoundaryControlStep23 * d ^ 2 := by
  unfold intrinsicBinaryQuadratic00 intrinsicBinaryQuadratic02
    intrinsicBinaryQuadratic22
    factorTwoIntrinsicBoundaryControlStep23
    factorTwoIntrinsicBoundaryControl2 factorTwoIntrinsicBoundaryControl3
    factorTwoIntrinsicBoundaryPower0 factorTwoIntrinsicBoundaryPower1
    factorTwoIntrinsicBoundaryPower2 factorTwoIntrinsicBoundaryPower3
    factorTwoIntrinsicOddPhaseQuadratic
    factorTwoIntrinsicOddDirectionQuadratic
    factorTwoIntrinsicAdjugateCoefficient0
    factorTwoIntrinsicAdjugateCoefficient1
    factorTwoIntrinsicEvenAdjugateCoupling
    factorTwoIntrinsicAlternatingRow0 factorTwoIntrinsicAlternatingRow2
  ring

/-- The first monotonicity inequality is exactly its three-scalar Gram gate. -/
theorem factorTwoIntrinsicBoundaryControlStep01_nonneg_iff :
    (∀ c d : ℝ, 0 ≤ factorTwoIntrinsicBoundaryControlStep01 c d) ↔
      IntrinsicBinaryQuadraticPSD factorTwoIntrinsicBoundaryControlStep01 :=
  intrinsicBinaryQuadratic_nonneg_iff_of_expansion
    factorTwoIntrinsicBoundaryControlStep01 step01_expansion

/-- The middle monotonicity inequality is exactly its three-scalar Gram gate. -/
theorem factorTwoIntrinsicBoundaryControlStep12_nonneg_iff :
    (∀ c d : ℝ, 0 ≤ factorTwoIntrinsicBoundaryControlStep12 c d) ↔
      IntrinsicBinaryQuadraticPSD factorTwoIntrinsicBoundaryControlStep12 :=
  intrinsicBinaryQuadratic_nonneg_iff_of_expansion
    factorTwoIntrinsicBoundaryControlStep12 step12_expansion

/-- The last monotonicity inequality is exactly its three-scalar Gram gate. -/
theorem factorTwoIntrinsicBoundaryControlStep23_nonneg_iff :
    (∀ c d : ℝ, 0 ≤ factorTwoIntrinsicBoundaryControlStep23 c d) ↔
      IntrinsicBinaryQuadraticPSD factorTwoIntrinsicBoundaryControlStep23 :=
  intrinsicBinaryQuadratic_nonneg_iff_of_expansion
    factorTwoIntrinsicBoundaryControlStep23 step23_expansion

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowControlMonotonicity

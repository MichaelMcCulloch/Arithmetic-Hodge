import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicEvenCleanSharp
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowControlMonotonicity
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddLowEndpointStructuralPositive

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowControlStep01Positive

noncomputable section

open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicLowControlsPositive
open YoshidaFactorTwoPhaseIntrinsicLowControlMonotonicity
open YoshidaFactorTwoPhaseLowSchur

/-!
# The first intrinsic Bernstein step as one coupled Cauchy inequality

The first Bernstein step has a very small determinant margin when its three
entries are bounded independently.  Here it is instead kept as the exact
Schur complement of the positive-endpoint even form.  The resulting analytic
target is a single Cauchy inequality in all four intrinsic coefficients.

No phase sampling, finite mode enumeration, interval subdivision, or
computational enclosure is used.
-/

/-- The positive-endpoint even quadratic, kept as one form. -/
def factorTwoIntrinsicEvenPlusQuadratic (u v : ℝ) : ℝ :=
  factorTwoStructuralPhaseLow00 1 * u ^ 2 +
    2 * factorTwoStructuralPhaseLow02 1 * u * v +
    factorTwoStructuralPhaseLow22 1 * v ^ 2

/-- The complete alternating bilinear coordinate on the intrinsic four-mode
block.  This is deliberately not split into four absolute values. -/
def factorTwoIntrinsicAlternatingBilinear
    (u v c d : ℝ) : ℝ :=
  u * factorTwoIntrinsicAlternatingRow0 c d +
    v * factorTwoIntrinsicAlternatingRow2 c d

/-- The exact odd budget occurring after the positive-endpoint even block is
eliminated.  Its second coefficient is the logarithmic derivative of the
even determinant in the inward Bernstein direction. -/
def factorTwoIntrinsicStep01ExactOddBudget (c d : ℝ) : ℝ :=
  factorTwoIntrinsicOddDirectionQuadratic c d +
    (factorTwoIntrinsicEvenDetCoefficient1 /
      factorTwoIntrinsicEvenDetCoefficient0) *
        factorTwoIntrinsicOddPhaseQuadratic 1 c d

/-- Cancellation-preserving analytic form of the first Bernstein gate. -/
def FactorTwoIntrinsicStep01ExactCauchy : Prop :=
  ∀ u v c d : ℝ,
    factorTwoIntrinsicAlternatingBilinear u v c d ^ 2 ≤
      factorTwoIntrinsicEvenPlusQuadratic u v *
        factorTwoIntrinsicStep01ExactOddBudget c d

/-! ## A general two-dimensional adjugate/Cauchy identity -/

private theorem adjugate_cauchy_iff
    (q00 q02 q22 j0 j2 R : ℝ)
    (h00 : 0 < q00) (hdet : 0 < q00 * q22 - q02 ^ 2) :
    q22 * j0 ^ 2 - 2 * q02 * j0 * j2 + q00 * j2 ^ 2 ≤
        (q00 * q22 - q02 ^ 2) * R ↔
      ∀ u v : ℝ,
        (u * j0 + v * j2) ^ 2 ≤
          (q00 * u ^ 2 + 2 * q02 * u * v + q22 * v ^ 2) * R := by
  let A : ℝ := q22 * j0 ^ 2 - 2 * q02 * j0 * j2 + q00 * j2 ^ 2
  let D : ℝ := q00 * q22 - q02 ^ 2
  have hD : 0 < D := by simpa only [D] using hdet
  have hAidentity :
      q00 * A = (q00 * j2 - q02 * j0) ^ 2 + D * j0 ^ 2 := by
    dsimp only [A, D]
    ring
  have hA : 0 ≤ A := by
    have hscaled : 0 ≤ q00 * A := by
      rw [hAidentity]
      exact add_nonneg (sq_nonneg _) (mul_nonneg hD.le (sq_nonneg _))
    nlinarith
  have hE (u v : ℝ) :
      0 ≤ q00 * u ^ 2 + 2 * q02 * u * v + q22 * v ^ 2 := by
    have hscaled : 0 ≤ q00 *
        (q00 * u ^ 2 + 2 * q02 * u * v + q22 * v ^ 2) := by
      rw [show q00 *
          (q00 * u ^ 2 + 2 * q02 * u * v + q22 * v ^ 2) =
        (q00 * u + q02 * v) ^ 2 + D * v ^ 2 by
          dsimp only [D]
          ring]
      exact add_nonneg (sq_nonneg _) (mul_nonneg hD.le (sq_nonneg _))
    nlinarith
  constructor
  · intro hAR u v
    let E : ℝ := q00 * u ^ 2 + 2 * q02 * u * v + q22 * v ^ 2
    let L : ℝ := u * j0 + v * j2
    have hLagrange :
        E * A - D * L ^ 2 =
          (u * (q00 * j2 - q02 * j0) +
            v * (q02 * j2 - q22 * j0)) ^ 2 := by
      dsimp only [E, A, D, L]
      ring
    have hDA : D * L ^ 2 ≤ E * A := by
      nlinarith [sq_nonneg
        (u * (q00 * j2 - q02 * j0) +
          v * (q02 * j2 - q22 * j0))]
    have hER : E * A ≤ E * (D * R) := by
      apply mul_le_mul_of_nonneg_left
      · simpa only [A, D] using hAR
      · exact hE u v
    have : D * L ^ 2 ≤ D * (E * R) := by
      calc
        D * L ^ 2 ≤ E * A := hDA
        _ ≤ E * (D * R) := hER
        _ = D * (E * R) := by ring
    dsimp only [D, E, L] at this ⊢
    nlinarith
  · intro hCauchy
    by_cases hAzero : A = 0
    · have hj0sq : j0 ^ 2 = 0 := by
        have hscaled : q00 * A = 0 := by rw [hAzero, mul_zero]
        rw [hAidentity] at hscaled
        nlinarith [sq_nonneg (q00 * j2 - q02 * j0)]
      have hj0 : j0 = 0 := sq_eq_zero_iff.mp hj0sq
      have hR := hCauchy 1 0
      rw [hj0] at hR
      norm_num at hR
      have : 0 ≤ D * R := by
        have hR0 : 0 ≤ R := by nlinarith
        exact mul_nonneg hD.le hR0
      simpa only [A, D, hAzero] using this
    · have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hAzero)
      let u : ℝ := q22 * j0 - q02 * j2
      let v : ℝ := q00 * j2 - q02 * j0
      have hlinear : u * j0 + v * j2 = A := by
        dsimp only [u, v, A]
        ring
      have henergy :
          q00 * u ^ 2 + 2 * q02 * u * v + q22 * v ^ 2 = D * A := by
        dsimp only [u, v, D, A]
        ring
      have hchosen := hCauchy u v
      rw [hlinear, henergy] at hchosen
      have hcancel : A ≤ D * R := by
        have hrewrite : (D * A) * R = A * (D * R) := by ring
        rw [hrewrite] at hchosen
        nlinarith
      simpa only [A, D] using hcancel

/-! ## Exact equivalence for the production first step -/

/-- With the positive-endpoint even Sylvester gates, universal
nonnegativity of the first Bernstein step is *equivalent* to the complete
four-variable Cauchy inequality above. -/
theorem factorTwoIntrinsicBoundaryControlStep01_nonneg_iff_exactCauchy
    (hplus00 : 0 < factorTwoStructuralPhaseLow00 1)
    (hplusDet : 0 < factorTwoIntrinsicEvenPhaseDet 1) :
    (∀ c d : ℝ, 0 ≤ factorTwoIntrinsicBoundaryControlStep01 c d) ↔
      FactorTwoIntrinsicStep01ExactCauchy := by
  let q00 : ℝ := factorTwoStructuralPhaseLow00 1
  let q02 : ℝ := factorTwoStructuralPhaseLow02 1
  let q22 : ℝ := factorTwoStructuralPhaseLow22 1
  let D : ℝ := q00 * q22 - q02 ^ 2
  have hq00 : 0 < q00 := by simpa only [q00] using hplus00
  have hD : 0 < D := by
    simpa only [D, q00, q02, q22, factorTwoIntrinsicEvenPhaseDet] using
      hplusDet
  have hcoefficient0 : factorTwoIntrinsicEvenDetCoefficient0 = D := by
    unfold factorTwoIntrinsicEvenDetCoefficient0
    simp only [factorTwoIntrinsicEvenPhaseDet, D, q00, q02, q22]
  have hDne : D ≠ 0 := ne_of_gt hD
  constructor
  · intro hstep u v c d
    let j0 : ℝ := factorTwoIntrinsicAlternatingRow0 c d
    let j2 : ℝ := factorTwoIntrinsicAlternatingRow2 c d
    let R : ℝ := factorTwoIntrinsicStep01ExactOddBudget c d
    have hbudget :
        D * R =
          factorTwoIntrinsicEvenDetCoefficient0 *
              factorTwoIntrinsicOddDirectionQuadratic c d +
            factorTwoIntrinsicEvenDetCoefficient1 *
              factorTwoIntrinsicOddPhaseQuadratic 1 c d := by
      dsimp only [R, factorTwoIntrinsicStep01ExactOddBudget]
      rw [hcoefficient0]
      field_simp [hDne]
    have hthree := three_mul_factorTwoIntrinsicBoundaryControlStep01 c d
    have hthree' :
        3 * factorTwoIntrinsicBoundaryControlStep01 c d =
          factorTwoIntrinsicEvenDetCoefficient0 *
              factorTwoIntrinsicOddDirectionQuadratic c d +
            factorTwoIntrinsicEvenDetCoefficient1 *
              factorTwoIntrinsicOddPhaseQuadratic 1 c d -
            (q22 * j0 ^ 2 - 2 * q02 * j0 * j2 + q00 * j2 ^ 2) := by
      simpa only [factorTwoIntrinsicAdjugateCoefficient0,
        factorTwoIntrinsicEvenAdjugateCoupling, j0, j2, q00, q02, q22] using
        hthree
    have hAdj :
        q22 * j0 ^ 2 - 2 * q02 * j0 * j2 + q00 * j2 ^ 2 ≤ D * R := by
      have hs := hstep c d
      rw [hbudget]
      nlinarith
    have hC := (adjugate_cauchy_iff q00 q02 q22 j0 j2 R hq00 hD).mp hAdj u v
    simpa only [factorTwoIntrinsicAlternatingBilinear,
      factorTwoIntrinsicEvenPlusQuadratic, j0, j2, R, q00, q02, q22] using hC
  · intro hCauchy c d
    let j0 : ℝ := factorTwoIntrinsicAlternatingRow0 c d
    let j2 : ℝ := factorTwoIntrinsicAlternatingRow2 c d
    let R : ℝ := factorTwoIntrinsicStep01ExactOddBudget c d
    have hbudget :
        D * R =
          factorTwoIntrinsicEvenDetCoefficient0 *
              factorTwoIntrinsicOddDirectionQuadratic c d +
            factorTwoIntrinsicEvenDetCoefficient1 *
              factorTwoIntrinsicOddPhaseQuadratic 1 c d := by
      dsimp only [R, factorTwoIntrinsicStep01ExactOddBudget]
      rw [hcoefficient0]
      field_simp [hDne]
    have hC : ∀ u v : ℝ,
        (u * j0 + v * j2) ^ 2 ≤
          (q00 * u ^ 2 + 2 * q02 * u * v + q22 * v ^ 2) * R := by
      intro u v
      simpa only [factorTwoIntrinsicAlternatingBilinear,
        factorTwoIntrinsicEvenPlusQuadratic, j0, j2, R, q00, q02, q22] using
        hCauchy u v c d
    have hAdj :=
      (adjugate_cauchy_iff q00 q02 q22 j0 j2 R hq00 hD).mpr hC
    have hthree := three_mul_factorTwoIntrinsicBoundaryControlStep01 c d
    have hthree' :
        3 * factorTwoIntrinsicBoundaryControlStep01 c d =
          factorTwoIntrinsicEvenDetCoefficient0 *
              factorTwoIntrinsicOddDirectionQuadratic c d +
            factorTwoIntrinsicEvenDetCoefficient1 *
              factorTwoIntrinsicOddPhaseQuadratic 1 c d -
            (q22 * j0 ^ 2 - 2 * q02 * j0 * j2 + q00 * j2 ^ 2) := by
      simpa only [factorTwoIntrinsicAdjugateCoefficient0,
        factorTwoIntrinsicEvenAdjugateCoupling, j0, j2, q00, q02, q22] using
        hthree
    rw [hbudget] at hAdj
    nlinarith

/-- The exact coupled Cauchy inequality, rather than three independently
rounded Gram entries, closes the requested structural PSD gate. -/
theorem factorTwoIntrinsicBoundaryControlStep01_psd_of_exactCauchy
    (hplus00 : 0 < factorTwoStructuralPhaseLow00 1)
    (hplusDet : 0 < factorTwoIntrinsicEvenPhaseDet 1)
    (hCauchy : FactorTwoIntrinsicStep01ExactCauchy) :
    IntrinsicBinaryQuadraticPSD factorTwoIntrinsicBoundaryControlStep01 := by
  apply factorTwoIntrinsicBoundaryControlStep01_nonneg_iff.mp
  exact (factorTwoIntrinsicBoundaryControlStep01_nonneg_iff_exactCauchy
    hplus00 hplusDet).mpr hCauchy

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowControlStep01Positive

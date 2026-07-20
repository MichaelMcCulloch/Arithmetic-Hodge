import ArithmeticHodge.Analysis.YoshidaFourCellEvenEndpointSeedCombinedNormStructural

set_option autoImplicit false

open MeasureTheory Real Set
open scoped Interval

namespace ArithmeticHodge.Analysis.YoshidaFourCellEvenEndpointSeedUniversalClosureStructural

noncomputable section

open YoshidaConstantBounds
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoPhaseHigherLegendreDecomposition
open YoshidaFactorTwoPhaseIntrinsicHigherResidual
open YoshidaFactorTwoPhaseIntrinsicNineCanonicalProjectionStructural
open YoshidaFourCellEvenEndpointCoshSchurStructural
open YoshidaFourCellEvenEndpointCapacityCauchyStructural
open YoshidaFourCellEvenEndpointSeedCapacityCrossStructural
open YoshidaFourCellEvenEndpointSeedCombinedNormStructural
open YoshidaFourCellEvenEndpointSeedCutoffEightBridgeStructural
open YoshidaFourCellEvenEndpointSeedRegularRemainderStructural
open YoshidaFourCellEvenPolarSchurStructural
open YoshidaFourCellEvenZeroCoshCoupledCoreStructural
open YoshidaFourCellParityHalfFoldStructural
open YoshidaFourCellParityOperatorStructural
open YoshidaRegularKernelBound

/-!
# Universal endpoint-seed low--tail closure

The canonical cutoff-eight residual need not itself have zero wide-cosh
moment.  Consequently the already-closed tail Schur theorem cannot simply be
applied to that residual.  This file instead keeps the tail row as a genuine
Riesz functional.  Its squared norm is bounded before any zero-cosh
assumption is used, and a sharp scalar Young split removes that functional
from the remaining universal obligation.

The resulting free-parameter Young estimate is deliberately diagnostic.  It
shows exactly how an unweighted tail norm trades against the very thin finite
row margin, without asserting that a fixed coarse split closes the universal
Schur determinant.  A final proof needs a weighted/harmonic tail estimate (or
an equivalent coupled block argument) rather than another fixed mass charge.
-/

/-- The rational squared-norm budget retained by the canonical complete
endpoint-tail representer before weakening the fixed `1/80` seed reserve to
the actual seed bracket. -/
def fourCellEvenEndpointSeedCanonicalTailNormBudget : ℝ :=
  5221 / 19600000

/-- The complete endpoint-seed row carried by a genuine `P8+` residual. -/
def fourCellEvenEndpointSeedCanonicalTailRow (r : ℝ → ℝ) : ℝ :=
  fourCellEvenEndpointCapacityPolarization
      fourCellEvenEndpointCoshSeed r -
    2 * fourCellOperatorHalfWidth *
      (∫ t : ℝ in 0..2,
        yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
          factorTwoCenteredCorrelationBilinear
            fourCellEvenEndpointCoshSeed r t)

/-- The explicit finite row in the canonical cutoff-eight decomposition. -/
def fourCellEvenEndpointSeedCanonicalLowRow
    (w : ℝ → ℝ) (hw : Continuous w) : ℝ :=
  fourCellEvenEndpointSeedP0246CompleteLowRow
    (factorTwoCanonicalLegendreCoefficient w hw 0)
    (factorTwoCanonicalLegendreCoefficient w hw 2)
    (factorTwoCanonicalLegendreCoefficient w hw 4)
    (factorTwoCanonicalLegendreCoefficient w hw 6)

/-- The centered squared mass of the canonical `P8+` residual. -/
def fourCellEvenEndpointSeedCanonicalTailMass
    (w : ℝ → ℝ) (hw : Continuous w) : ℝ :=
  ∫ x : ℝ in -1..1, centeredLegendreHigherResidual w hw 8 x ^ 2

/-- The canonical combined representer satisfies the sharper rational norm
bound used before the final multiplication by the seed pivot. -/
theorem integral_endpointSeedProjectedTailRowRepresenter_canonical_sq_le_rational :
    (∫ x : ℝ in -1..1,
      fourCellEvenEndpointSeedProjectedTailRowRepresenter
        fourCellEvenEndpointSeedCanonicalTailSelectorPolynomial x ^ 2) ≤
      fourCellEvenEndpointSeedCanonicalTailNormBudget := by
  let a : ℝ := fourCellOperatorHalfWidth
  let A : ℝ → ℝ := fourCellEvenEndpointSeedProjectedCapacityRepresenter
  let E : ℝ → ℝ := fourCellEndpointSeedRegularRemainderRepresenter
  have hlog0 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have hlogUpper : Real.log 2 ≤ (6932 / 10000 : ℝ) :=
    strict_log_two_bounds.2.le
  have hlogSq : Real.log 2 ^ 2 ≤ (6932 / 10000 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hlog0 hlogUpper 2
  have haSq : a ^ 2 ≤ (19 / 100 : ℝ) := by
    have hscaled := mul_le_mul_of_nonneg_left hlogSq
      (by norm_num : (0 : ℝ) ≤ 25 / 64)
    calc
      a ^ 2 = (25 / 64 : ℝ) * Real.log 2 ^ 2 := by
        dsimp only [a]
        unfold fourCellOperatorHalfWidth
        ring
      _ ≤ (25 / 64 : ℝ) * (6932 / 10000 : ℝ) ^ 2 := hscaled
      _ ≤ (19 / 100 : ℝ) := by norm_num
  have hA : MemLp A 2 (volume.restrict (Ioc (-1 : ℝ) 1)) := by
    simpa only [A] using memLp_fourCellEvenEndpointSeedProjectedCapacityRepresenter
  have hE : MemLp E 2 (volume.restrict (Ioc (-1 : ℝ) 1)) := by
    simpa only [E] using memLp_fourCellEndpointSeedRegularRemainderRepresenter
  have hAnorm : (∫ x : ℝ in -1..1, A x ^ 2) ≤ (21 / 100000 : ℝ) := by
    simpa only [A] using integral_endpointSeedProjectedCapacityRepresenter_sq_le
  have hEnorm : (∫ x : ℝ in -1..1, E x ^ 2) ≤ (1 / 245000 : ℝ) := by
    simpa only [E] using
      integral_fourCellEndpointSeedRegularRemainderRepresenter_sq_le
  have hEnonneg : 0 ≤ ∫ x : ℝ in -1..1, E x ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun _ _ ↦ sq_nonneg _)
  have hyoung := integral_sub_const_mul_sq_le_five_four_add_five
    A E a hA hE
  have hAterm :
      (5 / 4 : ℝ) * (∫ x : ℝ in -1..1, A x ^ 2) ≤
        (5 / 4 : ℝ) * (21 / 100000) :=
    mul_le_mul_of_nonneg_left hAnorm (by norm_num)
  have hEterm :
      5 * a ^ 2 * (∫ x : ℝ in -1..1, E x ^ 2) ≤
        5 * (19 / 100 : ℝ) * (1 / 245000) := by
    calc
      5 * a ^ 2 * (∫ x : ℝ in -1..1, E x ^ 2) ≤
          5 * (19 / 100 : ℝ) * (∫ x : ℝ in -1..1, E x ^ 2) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left haSq (by norm_num)) hEnonneg
      _ ≤ 5 * (19 / 100 : ℝ) * (1 / 245000) :=
        mul_le_mul_of_nonneg_left hEnorm (by norm_num)
  have hpointwise : ∀ x ∈ Icc (-1 : ℝ) 1,
      fourCellEvenEndpointSeedProjectedTailRowRepresenter
          fourCellEvenEndpointSeedCanonicalTailSelectorPolynomial x =
        A x - a * E x := by
    intro x hx
    dsimp only [A, a, E]
    rw [endpointSeedProjectedTailRowRepresenter_canonical_eq,
      fourCellEvenEndpointSeedRegularTailRepresenter_sub_selector_eq_remainder
        hx]
  calc
    (∫ x : ℝ in -1..1,
        fourCellEvenEndpointSeedProjectedTailRowRepresenter
          fourCellEvenEndpointSeedCanonicalTailSelectorPolynomial x ^ 2) =
      ∫ x : ℝ in -1..1, (A x - a * E x) ^ 2 := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
        change
          fourCellEvenEndpointSeedProjectedTailRowRepresenter
              fourCellEvenEndpointSeedCanonicalTailSelectorPolynomial x ^ 2 =
            (A x - a * E x) ^ 2
        rw [hpointwise x hx]
    _ ≤ (5 / 4 : ℝ) * (∫ x : ℝ in -1..1, A x ^ 2) +
        5 * a ^ 2 * (∫ x : ℝ in -1..1, E x ^ 2) := hyoung
    _ ≤ (5 / 4 : ℝ) * (21 / 100000) +
        5 * (19 / 100 : ℝ) * (1 / 245000) :=
      add_le_add hAterm hEterm
    _ = fourCellEvenEndpointSeedCanonicalTailNormBudget := by
      norm_num [fourCellEvenEndpointSeedCanonicalTailNormBudget]

/-- Cauchy closure of the complete endpoint tail row, with no zero-cosh or
endpoint-trace hypothesis on the tail itself. -/
theorem fourCellEvenEndpointSeedCanonicalTailRow_sq_le_rational_mass
    (r : ℝ → ℝ) (hr : Continuous r)
    (hlow : centeredLegendreMomentsVanishBelow r 8) :
    fourCellEvenEndpointSeedCanonicalTailRow r ^ 2 ≤
      fourCellEvenEndpointSeedCanonicalTailNormBudget *
        (∫ x : ℝ in -1..1, r x ^ 2) := by
  simpa only [fourCellEvenEndpointSeedCanonicalTailRow] using
    fourCellEvenEndpointSeedTailRow_sq_le_mass_of_projectedRepresenterNorm
      r hr hlow fourCellEvenEndpointSeedCanonicalTailSelectorPolynomial
      natDegree_fourCellEvenEndpointSeedCanonicalTailSelectorPolynomial_lt_eight
      (memLp_fourCellEvenEndpointSeedProjectedTailRowRepresenter
        fourCellEvenEndpointSeedCanonicalTailSelectorPolynomial)
      fourCellEvenEndpointSeedCanonicalTailNormBudget
      integral_endpointSeedProjectedTailRowRepresenter_canonical_sq_le_rational

/-- Exact scalar Young inequality with a free positive allocation parameter.
Keeping the parameter free is essential: a fixed split can consume more tail
diagonal than the four-cell operator possesses. -/
theorem add_sq_le_of_positive_youngParameter
    (x y η : ℝ) (hη : 0 < η) :
    (x + y) ^ 2 ≤
      (1 + η) * x ^ 2 + (1 + η⁻¹) * y ^ 2 := by
  have hηne : η ≠ 0 := hη.ne'
  have hinv0 : 0 ≤ η⁻¹ := (inv_pos.mpr hη).le
  have hid :
      (1 + η) * x ^ 2 + (1 + η⁻¹) * y ^ 2 - (x + y) ^ 2 =
        η⁻¹ * (η * x - y) ^ 2 := by
    field_simp [hηne]
    all_goals ring
  rw [← sub_nonneg, hid]
  exact mul_nonneg hinv0 (sq_nonneg (η * x - y))

/-- The canonical row is bounded by one explicit finite-row square and the
mass of the moment-eight residual, for every positive Young allocation.
This is an unconditional diagnostic interface; closing the universal Schur
step still requires a sharper weighted tail allocation than the unweighted
mass estimate alone supplies. -/
theorem fourCellEvenEndpointSeedRow_sq_le_canonicalLowTailBudget_of_positive
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w)
    (heven : Function.Even w)
    (hzero : fourCellPositiveCoshMoment w
      (fourCellOperatorHalfWidth / 2) = 0)
    (η : ℝ) (hη : 0 < η) :
    fourCellEvenEndpointSeedRow w ^ 2 ≤
      (1 + η) *
          fourCellEvenEndpointSeedCanonicalLowRow w hw ^ 2 +
        (1 + η⁻¹) * fourCellEvenEndpointSeedCanonicalTailNormBudget *
          fourCellEvenEndpointSeedCanonicalTailMass w hw := by
  let r : ℝ → ℝ := centeredLegendreHigherResidual w hw 8
  let L : ℝ := fourCellEvenEndpointSeedCanonicalLowRow w hw
  let T : ℝ := fourCellEvenEndpointSeedCanonicalTailRow r
  have hr : Continuous r := by
    simpa only [r] using continuous_centeredLegendreHigherResidual w hw 8
  have hrGap : centeredLegendreMomentsVanishBelow r 8 := by
    simpa only [r] using centeredLegendreHigherResidual_momentsVanishBelow w hw 8
  have hT : T ^ 2 ≤
      fourCellEvenEndpointSeedCanonicalTailNormBudget *
        (∫ x : ℝ in -1..1, r x ^ 2) := by
    simpa only [T] using
      fourCellEvenEndpointSeedCanonicalTailRow_sq_le_rational_mass r hr hrGap
  have hscale : 0 ≤ (1 + η⁻¹) := by
    have hinv : 0 < η⁻¹ := inv_pos.mpr hη
    positivity
  have hTscaled := mul_le_mul_of_nonneg_left hT hscale
  have hrow := fourCellEvenEndpointSeedRow_eq_canonicalCutoffEightLow_add_tail
    w hw hlocal heven hzero
  have hrow' : fourCellEvenEndpointSeedRow w = L + T := by
    dsimp only [L, T, fourCellEvenEndpointSeedCanonicalLowRow,
      fourCellEvenEndpointSeedCanonicalTailRow, r]
    simpa only [sub_eq_add_neg, add_assoc] using hrow
  rw [hrow']
  calc
    (L + T) ^ 2 ≤ (1 + η) * L ^ 2 + (1 + η⁻¹) * T ^ 2 :=
      add_sq_le_of_positive_youngParameter L T η hη
    _ ≤ (1 + η) * L ^ 2 +
        (1 + η⁻¹) * fourCellEvenEndpointSeedCanonicalTailNormBudget *
          (∫ x : ℝ in -1..1, r x ^ 2) := by
      nlinarith only [hTscaled]
    _ = (1 + η) *
          fourCellEvenEndpointSeedCanonicalLowRow w hw ^ 2 +
        (1 + η⁻¹) * fourCellEvenEndpointSeedCanonicalTailNormBudget *
          fourCellEvenEndpointSeedCanonicalTailMass w hw := by
      dsimp only [L, r, fourCellEvenEndpointSeedCanonicalTailMass]

end

end ArithmeticHodge.Analysis.YoshidaFourCellEvenEndpointSeedUniversalClosureStructural

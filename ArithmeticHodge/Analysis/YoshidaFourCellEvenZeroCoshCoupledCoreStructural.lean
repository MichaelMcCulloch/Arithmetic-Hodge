import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicHigherResidual
import ArithmeticHodge.Analysis.YoshidaFactorTwoFixedLagRepresenterStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024Structural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineCanonicalProjectionStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineFullMixedDecompositionStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineP6EvenCleanPolynomialGramStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4MinusEndpointReduction
import ArithmeticHodge.Analysis.YoshidaFourCellEvenCapacityStructural
import ArithmeticHodge.Analysis.YoshidaFourCellEvenEndpointCapacityCauchyStructural
import ArithmeticHodge.Analysis.YoshidaFourCellEvenZeroCoshRegularStructural
import ArithmeticHodge.Analysis.ShiftedLegendreCenteredL2Structural
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.NumberTheory.ZetaValues

set_option autoImplicit false

open MeasureTheory Real Set Filter
open Polynomial
open scoped BigOperators unitInterval

namespace ArithmeticHodge.Analysis.YoshidaFourCellEvenZeroCoshCoupledCoreStructural

noncomputable section

open UnitIntervalLogEnergyAffine
open MultiplicativeWeilFourCellRealRescaleStructural
open ShiftedLegendreCenteredParity
open ShiftedLegendreCenteredL2Structural
open ShiftedLegendreFiniteEnergyGap
open ShiftedLegendreL2Basis
open ShiftedLegendreLogEnergyOrthogonalProjection
open ShiftedLegendreOrthogonality
open ThreeByThreeRankOneSchur
open TwoByTwoSchur
open YoshidaEndpointEvenLowProfile
open YoshidaEndpointEvenStructuralReduction
open YoshidaConstantBounds
open YoshidaEndpointEvenMeanZeroPositive
open YoshidaEndpointEvenFullPolarization
open YoshidaEndpointPotentialBound
open YoshidaEndpointPotentialIntegrable
open YoshidaEndpointPotentialLegendreOffDiagonalStructural
open YoshidaFactorTwoPhaseIntrinsicHigherResidual
open YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024Structural
open YoshidaFactorTwoPhaseIntrinsicNineCanonicalProjectionStructural
open YoshidaFactorTwoPhaseIntrinsicNineFullMixedDecompositionStructural
open YoshidaFactorTwoPhaseIntrinsicNineP6EvenCleanPolynomialGramStructural
open YoshidaFactorTwoPhaseIntrinsicNineP6EvenCorrelationStructural
open YoshidaFactorTwoPhaseIntrinsicNineP6EvenProfileCorrelationStructural
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFactorTwoPhaseIntrinsicRetainedSingularGapStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4CorrelationStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4EndpointProfile
open YoshidaFactorTwoPhaseIntrinsicSixP4MinusEndpointReduction
open YoshidaFactorTwoPhaseIntrinsicSixSchurReduction
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoFixedLagRepresenterStructural
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoPhaseHigherLegendreDecomposition
open YoshidaFactorTwoPhaseEnvelope
open YoshidaFactorTwoPhaseSingularWeightedCauchyStructural
open YoshidaFactorTwoPhaseStructuralLowData
open YoshidaFourCellEvenCapacityStructural
open YoshidaFourCellEvenEndpointCapacityCauchyStructural
open YoshidaFourCellEvenPolarSchurStructural
open YoshidaFourCellEvenZeroCoshRegularStructural
open YoshidaFourCellEndpointVarianceStructural
open YoshidaFourCellParityHalfFoldStructural
open YoshidaFourCellParityOperatorStructural

/-!
# The infinite even tail of the zero-cosh coupled core

The adverse endpoint translation and the logarithmic endpoint potential are
kept as one positive capacity block.  Once the `P₀/P₂/P₄` coordinates
have been removed, the sixth shifted-Legendre harmonic gap alone is already
strictly stronger than the `33 / 20` coupled-core target.  Thus the unresolved
part of the zero-cosh problem is a finite low block and its cross with this
infinite tail, rather than the tail itself.
-/

private theorem shiftedLegendreReal_zero_centered_six (x : ℝ) :
    (shiftedLegendreReal 0).eval ((x + 1) / 2) = centeredEvenP0 x := by
  norm_num [shiftedLegendreReal, Polynomial.shiftedLegendre,
    Polynomial.eval_map, Polynomial.eval_finset_sum,
    Finset.sum_range_succ, Nat.choose, centeredEvenP0]

private theorem shiftedLegendreReal_two_centered_six (x : ℝ) :
    (shiftedLegendreReal 2).eval ((x + 1) / 2) = centeredEvenP2 x := by
  norm_num [shiftedLegendreReal, Polynomial.shiftedLegendre,
    Polynomial.eval_map, Polynomial.eval_finset_sum,
    Finset.sum_range_succ, Nat.choose, centeredEvenP2]
  ring

private theorem shiftedLegendreReal_four_centered_six (x : ℝ) :
    (shiftedLegendreReal 4).eval ((x + 1) / 2) =
      factorTwoCenteredP4 x := by
  norm_num [shiftedLegendreReal, Polynomial.shiftedLegendre,
    Polynomial.eval_map, Polynomial.eval_finset_sum,
    Finset.sum_range_succ, Nat.choose, factorTwoCenteredP4]
  ring

/-- The canonical cutoff-six projection of an even profile is exactly its
three genuine `P₀/P₂/P₄` coordinates. -/
theorem centeredLegendreLowProjection_six_eq_intrinsicEvenP024Profile
    (w : ℝ → ℝ) (hw : Continuous w) (heven : Function.Even w) :
    centeredLegendreLowProjection w hw 6 =
      factorTwoIntrinsicEvenP024Profile
        (factorTwoCanonicalLegendreCoefficient w hw 0)
        (factorTwoCanonicalLegendreCoefficient w hw 2)
        (factorTwoCanonicalLegendreCoefficient w hw 4) := by
  have h1 := centeredPullback_repr_eq_zero_of_even_of_odd
    w (centeredPullback_memLp_two w hw) heven 1 (by norm_num : Odd 1)
  have h3 := centeredPullback_repr_eq_zero_of_even_of_odd
    w (centeredPullback_memLp_two w hw) heven 3 (by norm_num : Odd 3)
  have h5 := centeredPullback_repr_eq_zero_of_even_of_odd
    w (centeredPullback_memLp_two w hw) heven 5 (by norm_num : Odd 5)
  change shiftedLegendreHilbertBasis.repr (centeredPullbackL2 w hw) 1 = 0 at h1
  change shiftedLegendreHilbertBasis.repr (centeredPullbackL2 w hw) 3 = 0 at h3
  change shiftedLegendreHilbertBasis.repr (centeredPullbackL2 w hw) 5 = 0 at h5
  funext x
  unfold centeredLegendreLowProjection centeredLegendreProjectionPolynomial
    shiftedLegendrePartialProjectionPolynomial
  rw [Polynomial.eval_finset_sum]
  simp only [normalizedShiftedLegendrePolynomial, Polynomial.eval_smul,
    smul_eq_mul, Finset.sum_range_succ, Finset.sum_range_zero,
    h1, h3, h5, zero_mul, zero_add, add_zero]
  rw [shiftedLegendreReal_zero_centered_six,
    shiftedLegendreReal_two_centered_six,
    shiftedLegendreReal_four_centered_six]
  unfold factorTwoIntrinsicEvenP024Profile factorTwoEvenStructuralLowProfile
    factorTwoIntrinsicSixEvenTail factorTwoCanonicalLegendreCoefficient
  simp only [Pi.add_apply]
  ring

/-- The canonical cutoff-eight projection of an even profile is exactly its
four genuine `P₀/P₂/P₄/P₆` coordinates. -/
theorem centeredLegendreLowProjection_eight_eq_intrinsicEvenP0246Profile
    (w : ℝ → ℝ) (hw : Continuous w) (heven : Function.Even w) :
    centeredLegendreLowProjection w hw 8 =
      factorTwoIntrinsicEvenP0246Profile
        (factorTwoCanonicalLegendreCoefficient w hw 0)
        (factorTwoCanonicalLegendreCoefficient w hw 2)
        (factorTwoCanonicalLegendreCoefficient w hw 4)
        (factorTwoCanonicalLegendreCoefficient w hw 6) := by
  have h1 := centeredPullback_repr_eq_zero_of_even_of_odd
    w (centeredPullback_memLp_two w hw) heven 1 (by norm_num : Odd 1)
  have h3 := centeredPullback_repr_eq_zero_of_even_of_odd
    w (centeredPullback_memLp_two w hw) heven 3 (by norm_num : Odd 3)
  have h5 := centeredPullback_repr_eq_zero_of_even_of_odd
    w (centeredPullback_memLp_two w hw) heven 5 (by norm_num : Odd 5)
  have h7 := centeredPullback_repr_eq_zero_of_even_of_odd
    w (centeredPullback_memLp_two w hw) heven 7 (by norm_num : Odd 7)
  change shiftedLegendreHilbertBasis.repr (centeredPullbackL2 w hw) 1 = 0 at h1
  change shiftedLegendreHilbertBasis.repr (centeredPullbackL2 w hw) 3 = 0 at h3
  change shiftedLegendreHilbertBasis.repr (centeredPullbackL2 w hw) 5 = 0 at h5
  change shiftedLegendreHilbertBasis.repr (centeredPullbackL2 w hw) 7 = 0 at h7
  funext x
  unfold centeredLegendreLowProjection centeredLegendreProjectionPolynomial
    shiftedLegendrePartialProjectionPolynomial
  rw [Polynomial.eval_finset_sum]
  simp only [normalizedShiftedLegendrePolynomial, Polynomial.eval_smul,
    smul_eq_mul, Finset.sum_range_succ, Finset.sum_range_zero,
    h1, h3, h5, h7, zero_mul, zero_add, add_zero]
  rw [shiftedLegendreReal_zero_centered_six,
    shiftedLegendreReal_two_centered_six,
    shiftedLegendreReal_four_centered_six]
  unfold factorTwoIntrinsicEvenP0246Profile
    factorTwoIntrinsicEvenP024Profile factorTwoEvenStructuralLowProfile
    factorTwoIntrinsicSixEvenTail factorTwoCanonicalLegendreCoefficient
    factorTwoCenteredP6
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The canonical degree-zero Hilbert coordinate is exactly the ordinary
centered constant coefficient. -/
theorem factorTwoCanonicalLegendreCoefficient_zero_eq_centeredEvenP0Coefficient
    (w : ℝ → ℝ) (hw : Continuous w) :
    factorTwoCanonicalLegendreCoefficient w hw 0 =
      centeredEvenP0Coefficient w := by
  unfold factorTwoCanonicalLegendreCoefficient centeredPullbackL2
  rw [repr_centeredPullback_zero_eq_coefficient w
    (centeredPullback_memLp_two w hw), norm_shiftedLegendreL2_zero]
  norm_num

/-- Unit-interval polynomial representing the intrinsic even `P₀/P₂/P₄`
profile. -/
def factorTwoIntrinsicEvenP024Polynomial
    (c0 c2 c4 : ℝ) : ℝ[X] :=
  c0 • shiftedLegendreReal 0 + c2 • shiftedLegendreReal 2 +
    c4 • shiftedLegendreReal 4

/-- Unit-interval polynomial representing the intrinsic even
`P₀/P₂/P₄/P₆` profile. -/
def factorTwoIntrinsicEvenP0246Polynomial
    (c0 c2 c4 c6 : ℝ) : ℝ[X] :=
  factorTwoIntrinsicEvenP024Polynomial c0 c2 c4 +
    c6 • shiftedLegendreReal 6

theorem centeredPolynomialLift_intrinsicEvenP024Polynomial
    (c0 c2 c4 : ℝ) :
    centeredPolynomialLift
        (factorTwoIntrinsicEvenP024Polynomial c0 c2 c4) =
      factorTwoIntrinsicEvenP024Profile c0 c2 c4 := by
  funext x
  unfold factorTwoIntrinsicEvenP024Polynomial centeredPolynomialLift
  simp only [Polynomial.eval_add, Polynomial.eval_smul, smul_eq_mul]
  rw [shiftedLegendreReal_zero_centered_six,
    shiftedLegendreReal_two_centered_six,
    shiftedLegendreReal_four_centered_six]
  unfold factorTwoIntrinsicEvenP024Profile factorTwoEvenStructuralLowProfile
    factorTwoIntrinsicSixEvenTail
  simp only [Pi.add_apply]

theorem centeredPolynomialLift_intrinsicEvenP0246Polynomial
    (c0 c2 c4 c6 : ℝ) :
    centeredPolynomialLift
        (factorTwoIntrinsicEvenP0246Polynomial c0 c2 c4 c6) =
      factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6 := by
  funext x
  unfold factorTwoIntrinsicEvenP0246Polynomial centeredPolynomialLift
  simp only [Polynomial.eval_add, Polynomial.eval_smul, smul_eq_mul]
  rw [show
      (factorTwoIntrinsicEvenP024Polynomial c0 c2 c4).eval ((x + 1) / 2) =
        factorTwoIntrinsicEvenP024Profile c0 c2 c4 x by
    exact congrFun
      (centeredPolynomialLift_intrinsicEvenP024Polynomial c0 c2 c4) x]
  unfold factorTwoIntrinsicEvenP0246Profile factorTwoCenteredP6
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]

theorem natDegree_factorTwoIntrinsicEvenP024Polynomial_lt_six
    (c0 c2 c4 : ℝ) :
    (factorTwoIntrinsicEvenP024Polynomial c0 c2 c4).natDegree < 6 := by
  unfold factorTwoIntrinsicEvenP024Polynomial
  have hdeg :
      (c0 • shiftedLegendreReal 0 + c2 • shiftedLegendreReal 2 +
        c4 • shiftedLegendreReal 4).natDegree ≤ 4 := by
    compute_degree
  omega

theorem natDegree_factorTwoIntrinsicEvenP0246Polynomial_lt_eight
    (c0 c2 c4 c6 : ℝ) :
    (factorTwoIntrinsicEvenP0246Polynomial c0 c2 c4 c6).natDegree < 8 := by
  unfold factorTwoIntrinsicEvenP0246Polynomial
    factorTwoIntrinsicEvenP024Polynomial
  have hdeg :
      (c0 • shiftedLegendreReal 0 + c2 • shiftedLegendreReal 2 +
        c4 • shiftedLegendreReal 4 +
          c6 • shiftedLegendreReal 6).natDegree ≤ 6 := by
    compute_degree
  omega

/-- Shifted-Legendre orthogonality removes the complete raw-energy cross
between `P₀/P₂/P₄` and every tail above degree five. -/
theorem centeredRawLogEnergy_intrinsicEvenP024_add_tail
    (c0 c2 c4 : ℝ) (r : ℝ → ℝ) (hr : Continuous r)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) r)
    (hlow : centeredLegendreMomentsVanishBelow r 6) :
    centeredRawLogEnergy
        (factorTwoIntrinsicEvenP024Profile c0 c2 c4 + r) =
      centeredRawLogEnergy
          (factorTwoIntrinsicEvenP024Profile c0 c2 c4) +
        centeredRawLogEnergy r := by
  let p : ℝ[X] := factorTwoIntrinsicEvenP024Polynomial c0 c2 c4
  have hpdeg : p.natDegree < 6 := by
    simpa only [p] using
      natDegree_factorTwoIntrinsicEvenP024Polynomial_lt_six c0 c2 c4
  have hsplit := centeredRawLogEnergy_centeredPolynomialLift_add_tail
    p r hr hlocal hlow hpdeg
  rw [show centeredPolynomialLift p =
      factorTwoIntrinsicEvenP024Profile c0 c2 c4 by
    simpa only [p] using
      centeredPolynomialLift_intrinsicEvenP024Polynomial c0 c2 c4] at hsplit
  exact hsplit

/-- The ordinary mass cross between the retained low profile and its
moment-six tail vanishes exactly. -/
theorem intervalIntegral_intrinsicEvenP024_mul_tail_eq_zero
    (c0 c2 c4 : ℝ) (r : ℝ → ℝ) (hr : Continuous r)
    (hlow : centeredLegendreMomentsVanishBelow r 6) :
    (∫ x : ℝ in -1..1,
      factorTwoIntrinsicEvenP024Profile c0 c2 c4 x * r x) = 0 := by
  let p : ℝ[X] := factorTwoIntrinsicEvenP024Polynomial c0 c2 c4
  have hpdeg : p.natDegree < 6 := by
    simpa only [p] using
      natDegree_factorTwoIntrinsicEvenP024Polynomial_lt_six c0 c2 c4
  have hzero := intervalIntegral_centeredPolynomialLift_mul_tail_eq_zero
    p r hr hlow hpdeg
  rw [show centeredPolynomialLift p =
      factorTwoIntrinsicEvenP024Profile c0 c2 c4 by
    simpa only [p] using
      centeredPolynomialLift_intrinsicEvenP024Polynomial c0 c2 c4] at hzero
  exact hzero

/-- Exact Pythagorean mass split for `P₀/P₂/P₄` plus a moment-six
tail. -/
theorem integral_intrinsicEvenP024_add_tail_sq
    (c0 c2 c4 : ℝ) (r : ℝ → ℝ) (hr : Continuous r)
    (hlow : centeredLegendreMomentsVanishBelow r 6) :
    (∫ x : ℝ in -1..1,
      (factorTwoIntrinsicEvenP024Profile c0 c2 c4 x + r x) ^ 2) =
      (∫ x : ℝ in -1..1,
        factorTwoIntrinsicEvenP024Profile c0 c2 c4 x ^ 2) +
        ∫ x : ℝ in -1..1, r x ^ 2 := by
  have hp := factorTwoIntrinsicEvenP024Profile_continuous c0 c2 c4
  have hsplit := integral_add_sq
    (factorTwoIntrinsicEvenP024Profile c0 c2 c4) r hp hr
  have hcross := intervalIntegral_intrinsicEvenP024_mul_tail_eq_zero
    c0 c2 c4 r hr hlow
  simpa only [Pi.add_apply, hcross, mul_zero, zero_add, add_zero] using hsplit

/-- Exact coupled-core polarization across the retained `P₀/P₂/P₄`
profile and a moment-six tail.  Shifted-Legendre orthogonality removes the
raw cross; the sole surviving cross is the joint endpoint-capacity form. -/
theorem fourCellEvenZeroCoshCoupledCore_intrinsicEvenP024_add_tail
    (c0 c2 c4 : ℝ) (r : ℝ → ℝ) (hr : Continuous r)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) r)
    (hlow : centeredLegendreMomentsVanishBelow r 6) :
    fourCellEvenZeroCoshCoupledCore
        (factorTwoIntrinsicEvenP024Profile c0 c2 c4 + r) =
      fourCellEvenZeroCoshCoupledCore
          (factorTwoIntrinsicEvenP024Profile c0 c2 c4) +
        2 * fourCellEvenEndpointCapacityPolarization
          (factorTwoIntrinsicEvenP024Profile c0 c2 c4) r +
        fourCellEvenZeroCoshCoupledCore r := by
  have hp := factorTwoIntrinsicEvenP024Profile_continuous c0 c2 c4
  have hraw := centeredRawLogEnergy_intrinsicEvenP024_add_tail
    c0 c2 c4 r hr hlocal hlow
  have hcapacity := fourCellEvenEndpointCapacityQuadratic_add
    (factorTwoIntrinsicEvenP024Profile c0 c2 c4) r hp hr
  unfold fourCellEvenZeroCoshCoupledCore
  unfold fourCellEvenEndpointCapacityQuadratic at hcapacity
  rw [hraw]
  linarith

/-! ## The first tail mode diagnoses the surviving polarization -/

/-- Exact endpoint-potential row from `P₀/P₂/P₄` to the first even tail
mode `P₆`.  The three rational entries are the all-degree Legendre
potential entries at distance six, four, and two respectively. -/
theorem integral_endpointPotential_mul_intrinsicEvenP024_mul_P6
    (c0 c2 c4 : ℝ) :
    (∫ x : ℝ in -1..1,
      yoshidaEndpointPotential x *
        factorTwoIntrinsicEvenP024Profile c0 c2 c4 x *
          factorTwoCenteredP6 x) =
      (1 / 21 : ℝ) * c0 + (1 / 18 : ℝ) * c2 +
        (1 / 11 : ℝ) * c4 := by
  have h0 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * centeredEvenP0 x *
        factorTwoCenteredP6 x) volume (-1) 1 :=
    YoshidaEndpointEvenTailRepresenter.intervalIntegrable_endpointPotential_mul centeredEvenP0
      factorTwoCenteredP6 (by unfold centeredEvenP0; fun_prop)
      continuous_factorTwoCenteredP6
  have h2 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * centeredEvenP2 x *
        factorTwoCenteredP6 x) volume (-1) 1 :=
    YoshidaEndpointEvenTailRepresenter.intervalIntegrable_endpointPotential_mul centeredEvenP2
      factorTwoCenteredP6 (by unfold centeredEvenP2; fun_prop)
      continuous_factorTwoCenteredP6
  have h4 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * factorTwoCenteredP4 x *
        factorTwoCenteredP6 x) volume (-1) 1 :=
    YoshidaEndpointEvenTailRepresenter.intervalIntegrable_endpointPotential_mul factorTwoCenteredP4
      factorTwoCenteredP6 continuous_factorTwoCenteredP4
      continuous_factorTwoCenteredP6
  rw [show (fun x : ℝ ↦ yoshidaEndpointPotential x *
      factorTwoIntrinsicEvenP024Profile c0 c2 c4 x *
        factorTwoCenteredP6 x) =
      fun x ↦ c0 *
          (yoshidaEndpointPotential x * centeredEvenP0 x *
            factorTwoCenteredP6 x) +
        (c2 * (yoshidaEndpointPotential x * centeredEvenP2 x *
            factorTwoCenteredP6 x) +
          c4 * (yoshidaEndpointPotential x * factorTwoCenteredP4 x *
            factorTwoCenteredP6 x)) by
      funext x
      unfold factorTwoIntrinsicEvenP024Profile
        factorTwoEvenStructuralLowProfile factorTwoIntrinsicSixEvenTail
      simp only [Pi.add_apply]
      ring,
    intervalIntegral.integral_add (h0.const_mul c0)
      ((h2.const_mul c2).add (h4.const_mul c4)),
    intervalIntegral.integral_add (h2.const_mul c2) (h4.const_mul c4)]
  repeat rw [intervalIntegral.integral_const_mul]
  rw [integral_endpointPotential_mul_centeredEvenP0_mul_P6,
    integral_endpointPotential_mul_centeredEvenP2_mul_P6,
    integral_endpointPotential_mul_P4_mul_P6]
  ring

/-- Exact endpoint-capacity polarization from the retained low profile to
`P₆`.  This is the first concrete row of the one cross term left by the
canonical cutoff-six decomposition. -/
theorem fourCellEvenEndpointCapacityPolarization_intrinsicEvenP024_P6
    (c0 c2 c4 : ℝ) :
    fourCellEvenEndpointCapacityPolarization
        (factorTwoIntrinsicEvenP024Profile c0 c2 c4)
        factorTwoCenteredP6 =
      c0 * ((1 / 21 : ℝ) +
          (2856 / 78125 : ℝ) * (Real.sqrt 2 * Real.log 2)) +
        c2 * ((1 / 18 : ℝ) +
          (46536 / 1953125 : ℝ) * (Real.sqrt 2 * Real.log 2)) +
        c4 * ((1 / 11 : ℝ) -
          (381976 / 48828125 : ℝ) * (Real.sqrt 2 * Real.log 2)) := by
  have hpotential :=
    integral_endpointPotential_mul_intrinsicEvenP024_mul_P6 c0 c2 c4
  have hprime :=
    factorTwoCenteredCorrelationBilinear_intrinsicEvenP024_p6
      c0 c2 c4 (8 / 5)
  norm_num [factorTwoIntrinsicP6Correlation06,
    factorTwoIntrinsicP6Correlation26,
    factorTwoIntrinsicP6Correlation46] at hprime
  unfold fourCellEvenEndpointCapacityPolarization
  rw [hpotential, hprime]
  ring

/-- The first nonconstant low-to-tail capacity row is strictly positive. -/
theorem fourCellEvenEndpointCapacityPolarization_P2_P6_pos :
    0 < fourCellEvenEndpointCapacityPolarization
      (factorTwoIntrinsicEvenP024Profile 0 1 0)
      factorTwoCenteredP6 := by
  rw [fourCellEvenEndpointCapacityPolarization_intrinsicEvenP024_P6]
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hbeta : 0 < Real.sqrt 2 * Real.log 2 := mul_pos hsqrt hlog
  simp only [zero_mul, one_mul, zero_add, add_zero]
  nlinarith only [hbeta]

/-- Negating the admissible `P₆` tail flips the capacity cross.  Hence the
surviving low/tail polarization has no structural sign, even before any
higher tail modes are present. -/
theorem fourCellEvenEndpointCapacityPolarization_P2_negP6_neg :
    fourCellEvenEndpointCapacityPolarization
      (factorTwoIntrinsicEvenP024Profile 0 1 0)
      ((-1 : ℝ) • factorTwoCenteredP6) < 0 := by
  rw [fourCellEvenEndpointCapacityPolarization_smul_right]
  nlinarith only [fourCellEvenEndpointCapacityPolarization_P2_P6_pos]

/-- The retained `3/100` low reserve and `4/5` tail-mass reserve are too
small to absorb even the single `P₂/P₆` capacity row.  This is an exact
determinant obstruction to closing the cross by those two coarse reserves
alone; a sharper quantitative Young allocation is genuinely required. -/
theorem coarse_P2_P6_reserve_product_lt_capacityPolarization_sq :
    ((3 / 100 : ℝ) * (2 / 5)) * ((4 / 5 : ℝ) * (2 / 13)) <
      fourCellEvenEndpointCapacityPolarization
        (factorTwoIntrinsicEvenP024Profile 0 1 0)
        factorTwoCenteredP6 ^ 2 := by
  let B : ℝ := fourCellEvenEndpointCapacityPolarization
    (factorTwoIntrinsicEvenP024Profile 0 1 0) factorTwoCenteredP6
  have hB : (1 / 18 : ℝ) < B := by
    dsimp only [B]
    rw [fourCellEvenEndpointCapacityPolarization_intrinsicEvenP024_P6]
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    have hbeta : 0 < Real.sqrt 2 * Real.log 2 := mul_pos hsqrt hlog
    simp only [zero_mul, one_mul, zero_add, add_zero]
    nlinarith only [hbeta]
  have hrat : ((3 / 100 : ℝ) * (2 / 5)) *
      ((4 / 5 : ℝ) * (2 / 13)) < (1 / 18 : ℝ) ^ 2 := by
    norm_num
  dsimp only [B] at hB ⊢
  nlinarith only [hB, hrat]

/-- Equivalently, an explicit scalar multiple of `P₆` makes the sum of the
two coarse diagonal reserves and twice the mixed capacity row negative. -/
theorem exists_P6_scale_coarse_reserves_do_not_absorb_capacityCross :
    ∃ c6 : ℝ,
      (3 / 250 : ℝ) + (8 / 65 : ℝ) * c6 ^ 2 +
        2 * fourCellEvenEndpointCapacityPolarization
          (factorTwoIntrinsicEvenP024Profile 0 1 0)
          factorTwoCenteredP6 * c6 < 0 := by
  let B : ℝ := fourCellEvenEndpointCapacityPolarization
    (factorTwoIntrinsicEvenP024Profile 0 1 0) factorTwoCenteredP6
  have hdet : (3 / 250 : ℝ) * (8 / 65) < B ^ 2 := by
    have h := coarse_P2_P6_reserve_product_lt_capacityPolarization_sq
    norm_num at h ⊢
    simpa only [B] using h
  refine ⟨-(65 / 8 : ℝ) * B, ?_⟩
  dsimp only [B] at hdet ⊢
  nlinarith only [hdet]

/-! ## The promoted `P₀/P₂/P₄/P₆` finite block -/

/-- Exact dyadic endpoint Gram on the first four even Legendre modes. -/
theorem fourCellEndpointPairing_intrinsicEvenP0246Profile
    (c0 c2 c4 c6 : ℝ) :
    fourCellEndpointPairing
        (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) =
      (2 / 5 : ℝ) * c0 ^ 2 + (48 / 125 : ℝ) * c0 * c2 -
        (144 / 3125 : ℝ) * c0 * c4 -
        (5712 / 78125 : ℝ) * c0 * c6 +
        (962 / 15625 : ℝ) * c2 ^ 2 -
        (8144 / 78125 : ℝ) * c2 * c4 -
        (93072 / 1953125 : ℝ) * c2 * c6 -
        (164582 / 3515625 : ℝ) * c4 ^ 2 +
        (763952 / 48828125 : ℝ) * c4 * c6 +
        (456595778 / 15869140625 : ℝ) * c6 ^ 2 := by
  rw [fourCellEndpointPairing_eq_centeredEndpointCorrelation,
    centeredEndpointCorrelation_intrinsicEvenP0246]
  norm_num [evenStructuralCorrelation00, evenStructuralCorrelation02,
    evenStructuralCorrelation22, factorTwoIntrinsicP4Correlation04,
    factorTwoIntrinsicP4Correlation24, factorTwoIntrinsicP4Correlation44,
    factorTwoIntrinsicP6Correlation06, factorTwoIntrinsicP6Correlation26,
    factorTwoIntrinsicP6Correlation46, factorTwoIntrinsicP6Correlation66]
  ring

/-- Exact coupled-core Gram after promoting the adverse `P₆` row into the
finite block.  No low/tail estimate enters this identity. -/
theorem fourCellEvenZeroCoshCoupledCore_intrinsicEvenP0246Profile_eq_gram
    (c0 c2 c4 c6 : ℝ) :
    fourCellEvenZeroCoshCoupledCore
        (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) =
      factorTwoP6EvenRawLogGram c0 c2 c4 c6 / 4 +
        factorTwoP6EvenPotentialGram c0 c2 c4 c6 -
        Real.sqrt 2 * Real.log 2 *
          ((2 / 5 : ℝ) * c0 ^ 2 + (48 / 125 : ℝ) * c0 * c2 -
            (144 / 3125 : ℝ) * c0 * c4 -
            (5712 / 78125 : ℝ) * c0 * c6 +
            (962 / 15625 : ℝ) * c2 ^ 2 -
            (8144 / 78125 : ℝ) * c2 * c4 -
            (93072 / 1953125 : ℝ) * c2 * c6 -
            (164582 / 3515625 : ℝ) * c4 ^ 2 +
            (763952 / 48828125 : ℝ) * c4 * c6 +
            (456595778 / 15869140625 : ℝ) * c6 ^ 2) := by
  unfold fourCellEvenZeroCoshCoupledCore
  rw [centeredRawLogEnergy_intrinsicEvenP0246,
    integral_endpointPotential_mul_intrinsicEvenP0246_sq,
    fourCellEndpointPairing_intrinsicEvenP0246Profile]

/-- A rational box Schur certificate for the promoted four-mode block.
The first six arguments are the `P₂/P₄/P₆` Gram, the next three are
the constant border, and `D` is the charged constant diagonal. -/
private theorem p0246_box_schur_nonnegative
    (a b c d e f x y z D c0 c2 c4 c6 : ℝ)
    (ha : (137 / 1000 : ℝ) ≤ a ∧ a ≤ 1371 / 10000)
    (hb : (1939 / 10000 : ℝ) ≤ b ∧ b ≤ 194 / 1000)
    (hc : (789 / 10000 : ℝ) ≤ c ∧ c ≤ 79 / 1000)
    (hd : (2881 / 10000 : ℝ) ≤ d ∧ d ≤ 2882 / 10000)
    (he : (832 / 10000 : ℝ) ≤ e ∧ e ≤ 833 / 10000)
    (hf : (1964 / 10000 : ℝ) ≤ f ∧ f ≤ 1965 / 10000)
    (hx : (1451 / 10000 : ℝ) ≤ x ∧ x ≤ 1452 / 10000)
    (hy : (1225 / 10000 : ℝ) ≤ y ∧ y ≤ 1226 / 10000)
    (hz : (834 / 10000 : ℝ) ≤ z ∧ z ≤ 835 / 10000)
    (hD : (1921 / 1000 : ℝ) ≤ D ∧ D ≤ 961 / 500) :
    0 ≤ D * c0 ^ 2 + 2 * x * c0 * c2 + 2 * y * c0 * c4 +
      2 * z * c0 * c6 + symmetricQuadratic a b c d e f c2 c4 c6 := by
  rcases ha with ⟨haL, haU⟩
  rcases hb with ⟨hbL, hbU⟩
  rcases hc with ⟨hcL, hcU⟩
  rcases hd with ⟨hdL, hdU⟩
  rcases he with ⟨heL, heU⟩
  rcases hf with ⟨hfL, hfU⟩
  rcases hx with ⟨hxL, hxU⟩
  rcases hy with ⟨hyL, hyU⟩
  rcases hz with ⟨hzL, hzU⟩
  rcases hD with ⟨hDL, hDU⟩
  have ha0 : 0 ≤ a := by linarith
  have hb0 : 0 ≤ b := by linarith
  have hc0' : 0 ≤ c := by linarith
  have hd0 : 0 ≤ d := by linarith
  have he0 : 0 ≤ e := by linarith
  have hf0 : 0 ≤ f := by linarith
  have hx0 : 0 ≤ x := by linarith
  have hy0 : 0 ≤ y := by linarith
  have hz0 : 0 ≤ z := by linarith
  have hDpos : 0 < D := by linarith
  have lower_mul (u v lu lv : ℝ)
      (hu : lu ≤ u) (hv : lv ≤ v) (hlu : 0 ≤ lu) (hlv : 0 ≤ lv) :
      lu * lv ≤ u * v := by
    exact mul_le_mul hu hv hlv (le_trans hlu hu)
  have upper_mul (u v U V : ℝ)
      (hu : u ≤ U) (hv : v ≤ V) (hv0 : 0 ≤ v) (hU0 : 0 ≤ U) :
      u * v ≤ U * V := by
    exact mul_le_mul hu hv hv0 hU0
  have habL : (137 / 1000 : ℝ) * (2881 / 10000) ≤ a * d :=
    lower_mul a d (137 / 1000) (2881 / 10000) haL hdL (by norm_num) (by norm_num)
  have hbSqU : b ^ 2 ≤ (194 / 1000 : ℝ) ^ 2 := by
    simpa only [pow_two] using
      upper_mul b b (194 / 1000) (194 / 1000) hbU hbU hb0 (by norm_num)
  have hminor : 0 < leadingMinorTwo a b d := by
    unfold leadingMinorTwo
    nlinarith only [habL, hbSqU]
  let T : ℝ := symmetricDeterminant a b c d e f
  have hadL := habL
  have hadfL :
      (137 / 1000 : ℝ) * (2881 / 10000) * (1964 / 10000) ≤
        a * d * f :=
    lower_mul (a * d) f
      ((137 / 1000 : ℝ) * (2881 / 10000)) (1964 / 10000)
      hadL hfL (by norm_num) (by norm_num)
  have hbcL : (1939 / 10000 : ℝ) * (789 / 10000) ≤ b * c :=
    lower_mul b c (1939 / 10000) (789 / 10000)
      hbL hcL (by norm_num) (by norm_num)
  have hbceL :
      (1939 / 10000 : ℝ) * (789 / 10000) * (832 / 10000) ≤
        b * c * e :=
    lower_mul (b * c) e
      ((1939 / 10000 : ℝ) * (789 / 10000)) (832 / 10000)
      hbcL heL (by norm_num) (by norm_num)
  have heSqU : e ^ 2 ≤ (833 / 10000 : ℝ) ^ 2 := by
    simpa only [pow_two] using
      upper_mul e e (833 / 10000) (833 / 10000) heU heU he0 (by norm_num)
  have haeSqU : a * e ^ 2 ≤
      (1371 / 10000 : ℝ) * (833 / 10000) ^ 2 :=
    upper_mul a (e ^ 2) (1371 / 10000) ((833 / 10000) ^ 2)
      haU heSqU (sq_nonneg e) (by norm_num)
  have hcSqU : c ^ 2 ≤ (79 / 1000 : ℝ) ^ 2 := by
    simpa only [pow_two] using
      upper_mul c c (79 / 1000) (79 / 1000) hcU hcU hc0' (by norm_num)
  have hdcSqU : d * c ^ 2 ≤
      (2882 / 10000 : ℝ) * (79 / 1000) ^ 2 :=
    upper_mul d (c ^ 2) (2882 / 10000) ((79 / 1000) ^ 2)
      hdU hcSqU (sq_nonneg c) (by norm_num)
  have hfbsqU : f * b ^ 2 ≤
      (1965 / 10000 : ℝ) * (194 / 1000) ^ 2 :=
    upper_mul f (b ^ 2) (1965 / 10000) ((194 / 1000) ^ 2)
      hfU hbSqU (sq_nonneg b) (by norm_num)
  have hTlower : (7 / 50000 : ℝ) < T := by
    dsimp only [T]
    unfold symmetricDeterminant
    nlinarith only [hadfL, hbceL, haeSqU, hdcSqU, hfbsqU]
  have hdet : 0 < T := by linarith
  let A : ℝ := adjugateQuadratic a b c d e f x y z
  have hdfU : d * f ≤ (2882 / 10000 : ℝ) * (1965 / 10000) :=
    upper_mul d f (2882 / 10000) (1965 / 10000)
      hdU hfU hf0 (by norm_num)
  have heSqL : (832 / 10000 : ℝ) ^ 2 ≤ e ^ 2 := by
    simpa only [pow_two] using
      lower_mul e e (832 / 10000) (832 / 10000)
        heL heL (by norm_num) (by norm_num)
  have hcoef1 : d * f - e ^ 2 ≤ (249 / 5000 : ℝ) := by
    nlinarith only [hdfU, heSqL]
  have hxSqU : x ^ 2 ≤ (211 / 10000 : ℝ) := by
    have h := upper_mul x x (1452 / 10000) (1452 / 10000)
      hxU hxU hx0 (by norm_num)
    norm_num at h ⊢
    nlinarith only [h]
  have ht1 : (d * f - e ^ 2) * x ^ 2 ≤ (1051 / 1000000 : ℝ) := by
    have h := upper_mul (d * f - e ^ 2) (x ^ 2)
      (249 / 5000) (211 / 10000) hcoef1 hxSqU (sq_nonneg x) (by norm_num)
    nlinarith only [h]
  have hceU : c * e ≤ (79 / 1000 : ℝ) * (833 / 10000) :=
    upper_mul c e (79 / 1000) (833 / 10000) hcU heU he0 (by norm_num)
  have hbfL : (1939 / 10000 : ℝ) * (1964 / 10000) ≤ b * f :=
    lower_mul b f (1939 / 10000) (1964 / 10000)
      hbL hfL (by norm_num) (by norm_num)
  have hcoef2 : c * e - b * f ≤ (-157 / 5000 : ℝ) := by
    nlinarith only [hceU, hbfL]
  have hxyL : (1777 / 100000 : ℝ) ≤ x * y := by
    have h := lower_mul x y (1451 / 10000) (1225 / 10000)
      hxL hyL (by norm_num) (by norm_num)
    nlinarith only [h]
  have hxy0 : 0 ≤ x * y := mul_nonneg hx0 hy0
  have ht2 : 2 * (c * e - b * f) * x * y ≤ (-111 / 100000 : ℝ) := by
    have hfirst : (c * e - b * f) * (x * y) ≤
        (-157 / 5000 : ℝ) * (x * y) :=
      mul_le_mul_of_nonneg_right hcoef2 hxy0
    have hsecond : (-157 / 5000 : ℝ) * (x * y) ≤
        (-157 / 5000 : ℝ) * (1777 / 100000) :=
      mul_le_mul_of_nonpos_left hxyL (by norm_num)
    nlinarith only [hfirst, hsecond]
  have hbeU : b * e ≤ (194 / 1000 : ℝ) * (833 / 10000) :=
    upper_mul b e (194 / 1000) (833 / 10000) hbU heU he0 (by norm_num)
  have hcdL : (789 / 10000 : ℝ) * (2881 / 10000) ≤ c * d :=
    lower_mul c d (789 / 10000) (2881 / 10000)
      hcL hdL (by norm_num) (by norm_num)
  have hcoef3 : b * e - c * d ≤ (-13 / 2000 : ℝ) := by
    nlinarith only [hbeU, hcdL]
  have hxzL : (121 / 10000 : ℝ) ≤ x * z := by
    have h := lower_mul x z (1451 / 10000) (834 / 10000)
      hxL hzL (by norm_num) (by norm_num)
    nlinarith only [h]
  have hxz0 : 0 ≤ x * z := mul_nonneg hx0 hz0
  have ht3 : 2 * (b * e - c * d) * x * z ≤ (-157 / 1000000 : ℝ) := by
    have hfirst : (b * e - c * d) * (x * z) ≤
        (-13 / 2000 : ℝ) * (x * z) :=
      mul_le_mul_of_nonneg_right hcoef3 hxz0
    have hsecond : (-13 / 2000 : ℝ) * (x * z) ≤
        (-13 / 2000 : ℝ) * (121 / 10000) :=
      mul_le_mul_of_nonpos_left hxzL (by norm_num)
    nlinarith only [hfirst, hsecond]
  have hafU : a * f ≤ (1371 / 10000 : ℝ) * (1965 / 10000) :=
    upper_mul a f (1371 / 10000) (1965 / 10000) haU hfU hf0 (by norm_num)
  have hcSqL : (789 / 10000 : ℝ) ^ 2 ≤ c ^ 2 := by
    simpa only [pow_two] using
      lower_mul c c (789 / 10000) (789 / 10000)
        hcL hcL (by norm_num) (by norm_num)
  have hcoef4 : a * f - c ^ 2 ≤ (104 / 5000 : ℝ) := by
    nlinarith only [hafU, hcSqL]
  have hySqU : y ^ 2 ≤ (151 / 10000 : ℝ) := by
    have h := upper_mul y y (1226 / 10000) (1226 / 10000)
      hyU hyU hy0 (by norm_num)
    norm_num at h ⊢
    nlinarith only [h]
  have ht4 : (a * f - c ^ 2) * y ^ 2 ≤ (315 / 1000000 : ℝ) := by
    have h := upper_mul (a * f - c ^ 2) (y ^ 2)
      (104 / 5000) (151 / 10000) hcoef4 hySqU (sq_nonneg y) (by norm_num)
    nlinarith only [h]
  have hbcU : b * c ≤ (194 / 1000 : ℝ) * (79 / 1000) :=
    upper_mul b c (194 / 1000) (79 / 1000) hbU hcU hc0' (by norm_num)
  have haeL : (137 / 1000 : ℝ) * (832 / 10000) ≤ a * e :=
    lower_mul a e (137 / 1000) (832 / 10000)
      haL heL (by norm_num) (by norm_num)
  have hcoef5 : b * c - a * e ≤ (1 / 250 : ℝ) := by
    nlinarith only [hbcU, haeL]
  have hyzU : y * z ≤ (1024 / 100000 : ℝ) := by
    have h := upper_mul y z (1226 / 10000) (835 / 10000)
      hyU hzU hz0 (by norm_num)
    nlinarith only [h]
  have ht5 : 2 * (b * c - a * e) * y * z ≤ (82 / 1000000 : ℝ) := by
    have h := upper_mul (b * c - a * e) (y * z)
      (1 / 250) (1024 / 100000) hcoef5 hyzU
      (mul_nonneg hy0 hz0) (by norm_num)
    nlinarith only [h]
  have hadU : a * d ≤ (1371 / 10000 : ℝ) * (2882 / 10000) :=
    upper_mul a d (1371 / 10000) (2882 / 10000) haU hdU hd0 (by norm_num)
  have hbSqL : (1939 / 10000 : ℝ) ^ 2 ≤ b ^ 2 := by
    simpa only [pow_two] using
      lower_mul b b (1939 / 10000) (1939 / 10000)
        hbL hbL (by norm_num) (by norm_num)
  have hcoef6 : a * d - b ^ 2 ≤ (1 / 500 : ℝ) := by
    nlinarith only [hadU, hbSqL]
  have hzSqU : z ^ 2 ≤ (7 / 1000 : ℝ) := by
    have h := upper_mul z z (835 / 10000) (835 / 10000)
      hzU hzU hz0 (by norm_num)
    norm_num at h ⊢
    nlinarith only [h]
  have ht6 : (a * d - b ^ 2) * z ^ 2 ≤ (14 / 1000000 : ℝ) := by
    have h := upper_mul (a * d - b ^ 2) (z ^ 2)
      (1 / 500) (7 / 1000) hcoef6 hzSqU (sq_nonneg z) (by norm_num)
    nlinarith only [h]
  have hAupper : A ≤ (195 / 1000000 : ℝ) := by
    dsimp only [A]
    unfold adjugateQuadratic
    nlinarith only [ht1, ht2, ht3, ht4, ht5, ht6]
  have hDT : (1 / 5000 : ℝ) < D * T := by
    have hprod := lower_mul D T (1921 / 1000) (7 / 50000)
      hDL hTlower.le (by norm_num) (by norm_num)
    nlinarith only [hprod]
  have hAdj : (1 / D : ℝ) * A ≤ T := by
    rw [show (1 / D : ℝ) * A = A / D by ring, div_le_iff₀ hDpos]
    nlinarith only [hAupper, hDT]
  have hschur := (rankOne_sub_nonneg_iff a b c d e f
    (by linarith : 0 < a) hminor hdet (1 / D) x y z).2 hAdj c2 c4 c6
  let Q : ℝ := symmetricQuadratic a b c d e f c2 c4 c6
  let L : ℝ := x * c2 + y * c4 + z * c6
  have hschur' : 0 ≤ Q - (1 / D) * L ^ 2 := by
    simpa only [Q, L] using hschur
  have hscaled := mul_nonneg hDpos.le hschur'
  have hscaled' : 0 ≤ D * Q - L ^ 2 := by
    rw [mul_sub] at hscaled
    have hDne : D ≠ 0 := hDpos.ne'
    rw [show D * ((1 / D) * L ^ 2) = L ^ 2 by field_simp] at hscaled
    exact hscaled
  have hsquare := sq_nonneg (D * c0 + L)
  have hscaledForm : 0 ≤ D *
      (D * c0 ^ 2 + 2 * x * c0 * c2 + 2 * y * c0 * c4 +
        2 * z * c0 * c6 + Q) := by
    nlinarith only [hscaled', hsquare]
  have hscaledForm' : 0 ≤
      (D * c0 ^ 2 + 2 * x * c0 * c2 + 2 * y * c0 * c4 +
        2 * z * c0 * c6 + Q) * D := by
    simpa only [mul_comm] using hscaledForm
  have hfinal := nonneg_of_mul_nonneg_left hscaledForm' hDpos
  simpa only [Q] using hfinal

private theorem sqrtTwo_mul_logTwo_P0246_bounds :
    (9802 / 10000 : ℝ) < Real.sqrt 2 * Real.log 2 ∧
      Real.sqrt 2 * Real.log 2 < (9803 / 10000 : ℝ) := by
  have hsSq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hs0 := Real.sqrt_nonneg 2
  have hsLower :
      (1414213562373095 / 1000000000000000 : ℝ) < Real.sqrt 2 := by
    norm_num
    nlinarith
  have hsUpper : Real.sqrt 2 <
      (1414213562373096 / 1000000000000000 : ℝ) := by
    norm_num
    nlinarith
  have hl := strict_log_two_fine_bounds
  have hl0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hprodLower :
      (1414213562373095 / 1000000000000000 : ℝ) *
          (69314718055 / 100000000000) <
        Real.sqrt 2 * Real.log 2 := by
    calc
      _ < Real.sqrt 2 * (69314718055 / 100000000000 : ℝ) :=
        mul_lt_mul_of_pos_right hsLower (by norm_num)
      _ < Real.sqrt 2 * Real.log 2 :=
        mul_lt_mul_of_pos_left hl.1 (Real.sqrt_pos.2 (by norm_num))
  have hprodUpper : Real.sqrt 2 * Real.log 2 <
      (1414213562373096 / 1000000000000000 : ℝ) *
        (69314718057 / 100000000000) := by
    calc
      Real.sqrt 2 * Real.log 2 <
          (1414213562373096 / 1000000000000000 : ℝ) * Real.log 2 :=
        mul_lt_mul_of_pos_right hsUpper hl0
      _ < (1414213562373096 / 1000000000000000 : ℝ) *
          (69314718057 / 100000000000) :=
        mul_lt_mul_of_pos_left hl.2 (by norm_num)
  constructor <;> norm_num at hprodLower hprodUpper ⊢ <;> linarith

set_option maxHeartbeats 800000 in
/-- The complete promoted `P₀/P₂/P₄/P₆` core retains three percent
of every nonconstant mass coordinate after paying the `33/20` target.  The
only defect is a charge of five on the constant coordinate.  This theorem
absorbs the formerly obstructing `P₂/P₆` row inside one exact finite Schur
block. -/
theorem three_div_hundred_nonconstantReserve_P0246_le_core_add_constantDefect
    (c0 c2 c4 c6 : ℝ) :
    (33 / 20 : ℝ) *
        (∫ x : ℝ in -1..1,
          factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6 x ^ 2) +
        (3 / 100 : ℝ) *
          ((2 / 5 : ℝ) * c2 ^ 2 + (2 / 9 : ℝ) * c4 ^ 2 +
            (2 / 13 : ℝ) * c6 ^ 2) ≤
      fourCellEvenZeroCoshCoupledCore
        (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) +
          5 * c0 ^ 2 := by
  let beta : ℝ := Real.sqrt 2 * Real.log 2
  let a : ℝ :=
    3 / 5 + (41 / 75 - (2 / 5 : ℝ) * Real.log 2) -
      (962 / 15625 : ℝ) * beta - 33 / 50 -
        (3 / 100 : ℝ) * (2 / 5)
  let b : ℝ := 1 / 7 + (4072 / 78125 : ℝ) * beta
  let c : ℝ := 1 / 18 + (46536 / 1953125 : ℝ) * beta
  let d : ℝ :=
    25 / 54 + (1739 / 5670 - (2 / 9 : ℝ) * Real.log 2) +
      (164582 / 3515625 : ℝ) * beta - 11 / 30 -
        (3 / 100 : ℝ) * (2 / 9)
  let e : ℝ := 1 / 11 - (381976 / 48828125 : ℝ) * beta
  let f : ℝ :=
    49 / 130 + (249251 / 1171170 - (2 / 13 : ℝ) * Real.log 2) -
      (456595778 / 15869140625 : ℝ) * beta - 33 / 130 -
        (3 / 100 : ℝ) * (2 / 13)
  let x : ℝ := 1 / 3 - (24 / 125 : ℝ) * beta
  let y : ℝ := 1 / 10 + (72 / 3125 : ℝ) * beta
  let z : ℝ := 1 / 21 + (2856 / 78125 : ℝ) * beta
  let D : ℝ :=
    2 - 2 * Real.log 2 - (2 / 5 : ℝ) * beta - 33 / 10 + 5
  have hl := strict_log_two_fine_bounds
  have hbeta := sqrtTwo_mul_logTwo_P0246_bounds
  have ha : (137 / 1000 : ℝ) ≤ a ∧ a ≤ 1371 / 10000 := by
    constructor <;> dsimp only [a, beta] <;> nlinarith
  have hb : (1939 / 10000 : ℝ) ≤ b ∧ b ≤ 194 / 1000 := by
    constructor <;> dsimp only [b, beta] <;> nlinarith
  have hc : (789 / 10000 : ℝ) ≤ c ∧ c ≤ 79 / 1000 := by
    constructor <;> dsimp only [c, beta] <;> nlinarith
  have hd : (2881 / 10000 : ℝ) ≤ d ∧ d ≤ 2882 / 10000 := by
    constructor <;> dsimp only [d, beta] <;> nlinarith
  have he : (832 / 10000 : ℝ) ≤ e ∧ e ≤ 833 / 10000 := by
    constructor <;> dsimp only [e, beta] <;> nlinarith
  have hf : (1964 / 10000 : ℝ) ≤ f ∧ f ≤ 1965 / 10000 := by
    constructor <;> dsimp only [f, beta] <;> nlinarith
  have hx : (1451 / 10000 : ℝ) ≤ x ∧ x ≤ 1452 / 10000 := by
    constructor <;> dsimp only [x, beta] <;> nlinarith
  have hy : (1225 / 10000 : ℝ) ≤ y ∧ y ≤ 1226 / 10000 := by
    constructor <;> dsimp only [y, beta] <;> nlinarith
  have hz : (834 / 10000 : ℝ) ≤ z ∧ z ≤ 835 / 10000 := by
    constructor <;> dsimp only [z, beta] <;> nlinarith
  have hD : (1921 / 1000 : ℝ) ≤ D ∧ D ≤ 961 / 500 := by
    constructor <;> dsimp only [D, beta] <;> nlinarith
  have hbox := p0246_box_schur_nonnegative
    a b c d e f x y z D c0 c2 c4 c6 ha hb hc hd he hf hx hy hz hD
  have hcore :=
    fourCellEvenZeroCoshCoupledCore_intrinsicEvenP0246Profile_eq_gram
      c0 c2 c4 c6
  have hmass := factorTwoIntrinsicEnergy_intrinsicEvenP0246 c0 c2 c4 c6
  change (∫ x : ℝ in -1..1,
      factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6 x ^ 2) = _ at hmass
  rw [hmass, hcore]
  unfold factorTwoP6EvenRawLogGram factorTwoP6EvenPotentialGram
  dsimp only [a, b, c, d, e, f, x, y, z, D, beta] at hbox
  unfold symmetricQuadratic at hbox
  nlinarith only [hbox]

/-! ## Canonical cutoff-eight low/tail split -/

/-- Shifted-Legendre orthogonality removes the complete raw-energy cross
between `P₀/P₂/P₄/P₆` and every tail starting at degree eight. -/
theorem centeredRawLogEnergy_intrinsicEvenP0246_add_tail
    (c0 c2 c4 c6 : ℝ) (r : ℝ → ℝ) (hr : Continuous r)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) r)
    (hlow : centeredLegendreMomentsVanishBelow r 8) :
    centeredRawLogEnergy
        (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6 + r) =
      centeredRawLogEnergy
          (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) +
        centeredRawLogEnergy r := by
  let p : ℝ[X] := factorTwoIntrinsicEvenP0246Polynomial c0 c2 c4 c6
  have hpdeg : p.natDegree < 8 := by
    simpa only [p] using
      natDegree_factorTwoIntrinsicEvenP0246Polynomial_lt_eight c0 c2 c4 c6
  have hsplit := centeredRawLogEnergy_centeredPolynomialLift_add_tail
    p r hr hlocal hlow hpdeg
  rw [show centeredPolynomialLift p =
      factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6 by
    simpa only [p] using
      centeredPolynomialLift_intrinsicEvenP0246Polynomial c0 c2 c4 c6] at hsplit
  exact hsplit

/-- The ordinary mass cross between `P₀/P₂/P₄/P₆` and its
moment-eight tail vanishes exactly. -/
theorem intervalIntegral_intrinsicEvenP0246_mul_tail_eq_zero
    (c0 c2 c4 c6 : ℝ) (r : ℝ → ℝ) (hr : Continuous r)
    (hlow : centeredLegendreMomentsVanishBelow r 8) :
    (∫ x : ℝ in -1..1,
      factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6 x * r x) = 0 := by
  let p : ℝ[X] := factorTwoIntrinsicEvenP0246Polynomial c0 c2 c4 c6
  have hpdeg : p.natDegree < 8 := by
    simpa only [p] using
      natDegree_factorTwoIntrinsicEvenP0246Polynomial_lt_eight c0 c2 c4 c6
  have hzero := intervalIntegral_centeredPolynomialLift_mul_tail_eq_zero
    p r hr hlow hpdeg
  rw [show centeredPolynomialLift p =
      factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6 by
    simpa only [p] using
      centeredPolynomialLift_intrinsicEvenP0246Polynomial c0 c2 c4 c6] at hzero
  exact hzero

/-- Exact Pythagorean mass split at the canonical even cutoff eight. -/
theorem integral_intrinsicEvenP0246_add_tail_sq
    (c0 c2 c4 c6 : ℝ) (r : ℝ → ℝ) (hr : Continuous r)
    (hlow : centeredLegendreMomentsVanishBelow r 8) :
    (∫ x : ℝ in -1..1,
      (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6 x + r x) ^ 2) =
      (∫ x : ℝ in -1..1,
        factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6 x ^ 2) +
        ∫ x : ℝ in -1..1, r x ^ 2 := by
  have hp := continuous_factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6
  have hsplit := integral_add_sq
    (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) r hp hr
  have hcross := intervalIntegral_intrinsicEvenP0246_mul_tail_eq_zero
    c0 c2 c4 c6 r hr hlow
  simpa only [Pi.add_apply, hcross, mul_zero, zero_add, add_zero] using hsplit

/-- Exact coupled-core polarization at cutoff eight.  Raw orthogonality leaves
only the joint endpoint-capacity border between the finite low block and the
infinite tail. -/
theorem fourCellEvenZeroCoshCoupledCore_intrinsicEvenP0246_add_tail
    (c0 c2 c4 c6 : ℝ) (r : ℝ → ℝ) (hr : Continuous r)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) r)
    (hlow : centeredLegendreMomentsVanishBelow r 8) :
    fourCellEvenZeroCoshCoupledCore
        (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6 + r) =
      fourCellEvenZeroCoshCoupledCore
          (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) +
        2 * fourCellEvenEndpointCapacityPolarization
          (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) r +
        fourCellEvenZeroCoshCoupledCore r := by
  have hp := continuous_factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6
  have hraw := centeredRawLogEnergy_intrinsicEvenP0246_add_tail
    c0 c2 c4 c6 r hr hlocal hlow
  have hcapacity := fourCellEvenEndpointCapacityQuadratic_add
    (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) r hp hr
  unfold fourCellEvenZeroCoshCoupledCore
  unfold fourCellEvenEndpointCapacityQuadratic at hcapacity
  rw [hraw]
  linarith

/-- Every even tail starting at `P₈` retains the full eighth harmonic
coefficient `761 / 280`.  The endpoint-potential/prime capacity is kept as
one nonnegative block. -/
theorem sevenHundredSixtyOne_div_twoHundredEighty_mass_le_coupledCore_of_even_legendreTail
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w)
    (heven : Function.Even w)
    (hlow : centeredLegendreMomentsVanishBelow w 8) :
    (761 / 280 : ℝ) * (∫ x : ℝ in -1..1, w x ^ 2) ≤
      fourCellEvenZeroCoshCoupledCore w := by
  let M : ℝ := ∫ x : ℝ in -1..1, w x ^ 2
  let B : ℝ := fourCellEvenEndpointCapacityQuadratic w
  have hB : 0 ≤ B := by
    simpa only [B] using
      fourCellEvenEndpointCapacityQuadratic_nonnegative w hw heven
  have hraw := harmonic_mul_intrinsicEnergy_le_raw_div_four
    w hw hlocal 8 hlow
  norm_num [harmonic, Finset.sum_range_succ] at hraw
  have hgap : (761 / 280 : ℝ) * M ≤ centeredRawLogEnergy w / 4 := by
    simpa only [M, factorTwoIntrinsicEnergy] using hraw
  change 0 ≤ (∫ x : ℝ in -1..1,
      yoshidaEndpointPotential x * w x ^ 2) -
    Real.sqrt 2 * Real.log 2 * fourCellEndpointPairing w at hB
  unfold fourCellEvenZeroCoshCoupledCore
  dsimp only [M] at hgap ⊢
  linarith

/-- At cutoff eight, the finite low block and infinite tail diagonal blocks
already clear the full `33 / 20` target under the global constant-coordinate
bound.  The promoted low reserve and the tail's `299 / 280` surplus absorb
the finite block's constant defect. -/
theorem thirtyThree_div_twenty_mass_le_coupledCore_diagonalSum_P0246_add_tail
    (c0 c2 c4 c6 : ℝ) (r : ℝ → ℝ) (hr : Continuous r)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) r)
    (heven : Function.Even r)
    (hlow : centeredLegendreMomentsVanishBelow r 8)
    (hconstant : c0 ^ 2 ≤ (1 / 4000 : ℝ) *
      (2 * c0 ^ 2 + (2 / 5 : ℝ) * c2 ^ 2 +
        (2 / 9 : ℝ) * c4 ^ 2 + (2 / 13 : ℝ) * c6 ^ 2 +
        (∫ x : ℝ in -1..1, r x ^ 2))) :
    (33 / 20 : ℝ) *
        (∫ x : ℝ in -1..1,
          (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6 x + r x) ^ 2) ≤
      fourCellEvenZeroCoshCoupledCore
          (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) +
        fourCellEvenZeroCoshCoupledCore r := by
  let N : ℝ := (2 / 5 : ℝ) * c2 ^ 2 + (2 / 9 : ℝ) * c4 ^ 2 +
    (2 / 13 : ℝ) * c6 ^ 2
  let R : ℝ := ∫ x : ℝ in -1..1, r x ^ 2
  have hR : 0 ≤ R := by
    dsimp only [R]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun _ _ ↦ sq_nonneg _)
  have hconstant' : 3998 * c0 ^ 2 ≤ N + R := by
    dsimp only [N, R]
    nlinarith only [hconstant]
  have habsorb : 5 * c0 ^ 2 ≤
      (3 / 100 : ℝ) * N + (299 / 280 : ℝ) * R := by
    nlinarith only [hconstant', hR, sq_nonneg c2, sq_nonneg c4,
      sq_nonneg c6]
  have hlowReserve :=
    three_div_hundred_nonconstantReserve_P0246_le_core_add_constantDefect
      c0 c2 c4 c6
  have htail :=
    sevenHundredSixtyOne_div_twoHundredEighty_mass_le_coupledCore_of_even_legendreTail
      r hr hlocal heven hlow
  have hmassSplit := integral_intrinsicEvenP0246_add_tail_sq
    c0 c2 c4 c6 r hr hlow
  rw [hmassSplit]
  dsimp only [N, R] at habsorb
  nlinarith only [hlowReserve, htail, habsorb]

/-- The exact finite budget available for the cutoff-eight capacity Schur
complement.  One five-hundredth of the nonconstant low mass is held back to
pay the constant defect jointly with the tail. -/
def fourCellEvenP0246CutoffEightLowSchurReserve
    (c0 c2 c4 c6 : ℝ) : ℝ :=
  fourCellEvenZeroCoshCoupledCore
      (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) -
    (33 / 20 : ℝ) *
      (∫ x : ℝ in -1..1,
        factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6 x ^ 2) +
    5 * c0 ^ 2 -
    (1 / 500 : ℝ) *
      ((2 / 5 : ℝ) * c2 ^ 2 + (2 / 9 : ℝ) * c4 ^ 2 +
        (2 / 13 : ℝ) * c6 ^ 2)

/-- The promoted finite block leaves a nonnegative cutoff-eight Schur
reserve, without any hypothesis on its four coordinates. -/
theorem fourCellEvenP0246CutoffEightLowSchurReserve_nonnegative
    (c0 c2 c4 c6 : ℝ) :
    0 ≤ fourCellEvenP0246CutoffEightLowSchurReserve c0 c2 c4 c6 := by
  have h :=
    three_div_hundred_nonconstantReserve_P0246_le_core_add_constantDefect
      c0 c2 c4 c6
  unfold fourCellEvenP0246CutoffEightLowSchurReserve
  nlinarith only [h, sq_nonneg c2, sq_nonneg c4, sq_nonneg c6]

/-! ## Square-integrability of the exact capacity representer -/

/-- The endpoint logarithm is square-integrable at its singular endpoint.
The structural input is the standard domination of `log x` by every
negative fractional power; no endpoint truncation is used. -/
private theorem intervalIntegrable_log_sq_zero_one :
    IntervalIntegrable (fun x : ℝ ↦ Real.log x ^ 2) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
  have hr : IntegrableOn
      (fun x : ℝ ↦ 16 * x ^ (-(1 / 2 : ℝ))) (Ioc 0 1) volume := by
    have h := intervalIntegral.intervalIntegrable_rpow'
      (a := (0 : ℝ)) (b := 1) (r := -(1 / 2 : ℝ)) (by norm_num)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)] at h
    exact h.const_mul 16
  apply Integrable.mono' hr
  · exact (Real.measurable_log.pow_const 2).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hx0 : 0 < x := hx.1
    have hx1 : x ≤ 1 := hx.2
    let y : ℝ := x ^ (1 / 4 : ℝ)
    have hy : 0 < y := Real.rpow_pos_of_pos hx0 _
    have hlog := Real.abs_log_mul_self_rpow_lt x (1 / 4 : ℝ)
      hx0 hx1 (by norm_num)
    norm_num at hlog
    have hprod : |Real.log x| * y < 4 := by
      dsimp only [y]
      simpa only [abs_mul,
        abs_of_pos (Real.rpow_pos_of_pos hx0 _)] using hlog
    have hp0 : 0 ≤ |Real.log x| * y :=
      mul_nonneg (abs_nonneg _) hy.le
    have hmul :
        0 ≤ (4 - |Real.log x| * y) * (4 + |Real.log x| * y) :=
      mul_nonneg (sub_nonneg.mpr hprod.le) (add_nonneg (by norm_num) hp0)
    have hsq : |Real.log x| ^ 2 * y ^ 2 ≤ 16 := by
      nlinarith only [hmul]
    have hySq : y ^ 2 = x ^ (1 / 2 : ℝ) := by
      dsimp only [y]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
      norm_num
    have hneg : x ^ (-(1 / 2 : ℝ)) = (y ^ 2)⁻¹ := by
      rw [Real.rpow_neg hx0.le, hySq]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs, hneg,
      ← div_eq_mul_inv]
    exact (le_div_iff₀ (sq_pos_of_pos hy)).2 hsq

private theorem intervalIntegrable_log_sq_zero_two :
    IntervalIntegrable (fun x : ℝ ↦ Real.log x ^ 2) volume 0 2 := by
  apply intervalIntegrable_log_sq_zero_one.trans
  apply ContinuousOn.intervalIntegrable
  exact (Real.continuousOn_log.mono (by
    intro x hx
    rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at hx
    simp only [mem_compl_iff, mem_singleton_iff]
    linarith [hx.1])).pow 2

/-- The full centered endpoint potential belongs to `L²(-1,1)`. -/
private theorem intervalIntegrable_endpointPotential_sq :
    IntervalIntegrable (fun x : ℝ ↦ yoshidaEndpointPotential x ^ 2)
      volume (-1) 1 := by
  have hlog := intervalIntegrable_log_sq_zero_two
  have hminus : IntervalIntegrable
      (fun x : ℝ ↦ Real.log (1 - x) ^ 2) volume (-1) 1 := by
    convert (hlog.comp_sub_left 1).symm using 1 <;> norm_num
  have hplus : IntervalIntegrable
      (fun x : ℝ ↦ Real.log (1 + x) ^ 2) volume (-1) 1 := by
    convert hlog.comp_add_left 1 using 1 <;> norm_num
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)] at hminus hplus ⊢
  have hdom : IntegrableOn
      (fun x : ℝ ↦ (1 / 2 : ℝ) *
        (Real.log (1 - x) ^ 2 + Real.log (1 + x) ^ 2))
      (Ioc (-1) 1) volume := (hminus.add hplus).const_mul (1 / 2)
  apply Integrable.mono' hdom
  · unfold yoshidaEndpointPotential
    exact (((Real.measurable_log.comp
      (measurable_const.sub (measurable_id.pow_const 2))).neg.div_const 2)
        |>.pow_const 2).aestronglyMeasurable
  · have hne1 : ∀ᵐ x : ℝ ∂(volume.restrict (Ioc (-1 : ℝ) 1)), x ≠ 1 :=
      (MeasureTheory.Measure.ae_ne volume (1 : ℝ)).filter_mono
        (ae_mono Measure.restrict_le_self)
    filter_upwards [ae_restrict_mem measurableSet_Ioc, hne1] with x hx hx1
    have hxneg1 : x ≠ -1 := ne_of_gt hx.1
    have hsub : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx1)
    have hadd : 1 + x ≠ 0 := by
      intro hzero
      apply hxneg1
      linarith
    unfold yoshidaEndpointPotential
    rw [show 1 - x ^ 2 = (1 - x) * (1 + x) by ring,
      Real.log_mul hsub hadd]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith only [sq_nonneg (Real.log (1 - x) - Real.log (1 + x))]

private theorem memLp_two_restrict_centered_of_continuous
    (f : ℝ → ℝ) (hf : Continuous f) :
    MemLp f 2 (volume.restrict (Ioc (-1 : ℝ) 1)) := by
  have hmeas : AEStronglyMeasurable f
      (volume.restrict (Ioc (-1 : ℝ) 1)) :=
    hf.aestronglyMeasurable.restrict
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  have hcompact : IntegrableOn (fun x : ℝ ↦ ‖f x‖ ^ 2)
      (Icc (-1 : ℝ) 1) :=
    (hf.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  exact hcompact.mono_set Ioc_subset_Icc_self

private theorem memLp_endpointPotential_mul_continuous
    (p : ℝ → ℝ) (hp : Continuous p) :
    MemLp (fun x : ℝ ↦ yoshidaEndpointPotential x * p x) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * p x)
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
    apply Measurable.aestronglyMeasurable
    unfold yoshidaEndpointPotential
    exact ((Real.measurable_log.comp
      (measurable_const.sub (measurable_id.pow_const 2))).neg.div_const 2).mul
        hp.measurable
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  have hI : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x ^ 2 * p x ^ 2)
      volume (-1) 1 := by
    simpa only [mul_comm] using
      intervalIntegrable_endpointPotential_sq.continuousOn_mul
        (hp.pow 2).continuousOn
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)] at hI
  apply hI.congr
  filter_upwards with x
  rw [Real.norm_eq_abs, sq_abs]
  ring

private theorem memLp_fixedLagK_intrinsicEvenP0246
    (c0 c2 c4 c6 : ℝ) :
    MemLp
      (factorTwoFixedLagK (8 / 5)
        (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6)) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
  let p : ℝ → ℝ := factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6
  have hp : Continuous p := by
    simpa only [p] using
      continuous_factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6
  have hrightBase : MemLp (fun x : ℝ ↦ p ((8 / 5 : ℝ) + x)) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) :=
    memLp_two_restrict_centered_of_continuous _
      (hp.comp (continuous_const.add continuous_id))
  have hright : MemLp
      (factorTwoFixedLagRightRepresenter (8 / 5) p) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
    simpa only [factorTwoFixedLagRightRepresenter] using
      hrightBase.indicator (measurableSet_Icc :
        MeasurableSet (Icc (-1 : ℝ) (1 - 8 / 5)))
  have hleftBase : MemLp (fun x : ℝ ↦ p (x - (8 / 5 : ℝ))) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) :=
    memLp_two_restrict_centered_of_continuous _
      (hp.comp (continuous_id.sub continuous_const))
  have hleft : MemLp
      (factorTwoFixedLagLeftRepresenter (8 / 5) p) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
    simpa only [factorTwoFixedLagLeftRepresenter] using
      hleftBase.indicator (measurableSet_Icc :
        MeasurableSet (Icc (-1 + 8 / 5 : ℝ) 1))
  simpa only [factorTwoFixedLagK, p] using hright.add hleft

/-- Additivity of the retained capacity polarization in its second
continuous argument. -/
theorem fourCellEvenEndpointCapacityPolarization_add_right
    (u v w : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    (hw : Continuous w) :
    fourCellEvenEndpointCapacityPolarization u (v + w) =
      fourCellEvenEndpointCapacityPolarization u v +
        fourCellEvenEndpointCapacityPolarization u w := by
  have hvI : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * (u x * v x))
      volume (-1) 1 :=
    intervalIntegrable_endpointPotential_mul _ (hu.mul hv)
  have hwI : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * (u x * w x))
      volume (-1) 1 :=
    intervalIntegrable_endpointPotential_mul _ (hu.mul hw)
  have hpotential :
      (∫ x : ℝ in -1..1,
        yoshidaEndpointPotential x * u x * (v + w) x) =
      (∫ x : ℝ in -1..1,
        yoshidaEndpointPotential x * u x * v x) +
      ∫ x : ℝ in -1..1,
        yoshidaEndpointPotential x * u x * w x := by
    rw [show (fun x : ℝ ↦
        yoshidaEndpointPotential x * u x * (v + w) x) =
      fun x ↦ yoshidaEndpointPotential x * (u x * v x) +
        yoshidaEndpointPotential x * (u x * w x) by
      funext x
      simp only [Pi.add_apply]
      ring,
      intervalIntegral.integral_add hvI hwI]
    congr 1 <;> apply intervalIntegral.integral_congr <;>
      intro x _hx <;> ring
  have hprime :
      factorTwoCenteredCorrelationBilinear u (v + w) (8 / 5) =
        factorTwoCenteredCorrelationBilinear u v (8 / 5) +
          factorTwoCenteredCorrelationBilinear u w (8 / 5) := by
    unfold factorTwoCenteredCorrelationBilinear
    rw [factorTwoCenteredCrossCorrelation_add_right u v w hu hv hw,
      factorTwoCenteredCrossCorrelation_add_left v w u hv hw hu]
    ring
  unfold fourCellEvenEndpointCapacityPolarization
  rw [hpotential, hprime]
  ring

/-- Unweighted Riesz-dual route to the cutoff-eight capacity determinant.
Any square-integrable representer of the capacity row may be altered by the
annihilated low Legendre span before applying this theorem.  Consequently the
remaining estimate concerns one projected representer norm, not the list of
tail modes. -/
theorem cutoffEight_capacitySchur_of_projectedRepresenterL2
    (c0 c2 c4 c6 : ℝ) (r G : ℝ → ℝ) (hr : Continuous r)
    (hG : MemLp G 2 (volume.restrict (Ioc (-1 : ℝ) 1)))
    (hrepresenter :
      fourCellEvenEndpointCapacityPolarization
          (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) r =
        ∫ x : ℝ in -1..1, G x * r x)
    (hdual : (∫ x : ℝ in -1..1, G x ^ 2) ≤
      (7461 / 7000 : ℝ) *
        fourCellEvenP0246CutoffEightLowSchurReserve c0 c2 c4 c6) :
    fourCellEvenEndpointCapacityPolarization
          (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) r ^ 2 ≤
      fourCellEvenP0246CutoffEightLowSchurReserve c0 c2 c4 c6 *
        ((7461 / 7000 : ℝ) *
          (∫ x : ℝ in -1..1, r x ^ 2)) := by
  let μ : Measure ℝ := volume.restrict (Ioc (-1 : ℝ) 1)
  have hrMeas : AEStronglyMeasurable r μ :=
    hr.aestronglyMeasurable.restrict
  have hrLp : MemLp r 2 μ := by
    rw [memLp_two_iff_integrable_sq_norm hrMeas]
    have hcompact : IntegrableOn (fun x : ℝ ↦ ‖r x‖ ^ 2)
        (Icc (-1 : ℝ) 1) :=
      (hr.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
    exact hcompact.mono_set Ioc_subset_Icc_self
  have hcauchy :=
    YoshidaEndpointWeightedCauchy.sq_integral_mul_le_weighted
      μ (fun _ : ℝ ↦ 1) G r (by simp)
        (by simpa only [div_one, Real.sqrt_one] using hG)
        (by simpa only [Real.sqrt_one, one_mul] using hrLp)
  have hcauchy' :
      (∫ x : ℝ in -1..1, G x * r x) ^ 2 ≤
        (∫ x : ℝ in -1..1, G x ^ 2) *
          (∫ x : ℝ in -1..1, r x ^ 2) := by
    repeat rw [intervalIntegral.integral_of_le (by norm_num)]
    simpa only [μ, div_one, one_mul] using hcauchy
  have hR : 0 ≤ ∫ x : ℝ in -1..1, r x ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun _ _ ↦ sq_nonneg _)
  have hscaled := mul_le_mul_of_nonneg_right hdual hR
  rw [hrepresenter]
  calc
    (∫ x : ℝ in -1..1, G x * r x) ^ 2 ≤
        (∫ x : ℝ in -1..1, G x ^ 2) *
          (∫ x : ℝ in -1..1, r x ^ 2) := hcauchy'
    _ ≤ ((7461 / 7000 : ℝ) *
          fourCellEvenP0246CutoffEightLowSchurReserve c0 c2 c4 c6) *
        (∫ x : ℝ in -1..1, r x ^ 2) := hscaled
    _ = fourCellEvenP0246CutoffEightLowSchurReserve c0 c2 c4 c6 *
        ((7461 / 7000 : ℝ) *
          (∫ x : ℝ in -1..1, r x ^ 2)) := by ring

/-- Exact one-variable Riesz representer of the cutoff-eight endpoint-
capacity row.  The symmetric fixed-lag representer keeps both prime boundary
pieces in one even channel. -/
def fourCellEvenP0246CutoffEightCapacityRepresenter
    (c0 c2 c4 c6 : ℝ) (x : ℝ) : ℝ :=
  yoshidaEndpointPotential x *
      factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6 x -
    (Real.sqrt 2 * Real.log 2 / 2) *
      factorTwoFixedLagK (8 / 5)
        (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) x

/-- The exact capacity representer is automatically square-integrable.  Its
only singular factor is the endpoint logarithm; the fixed-lag part is a sum
of two compactly supported translates of a polynomial. -/
theorem memLp_fourCellEvenP0246CutoffEightCapacityRepresenter
    (c0 c2 c4 c6 : ℝ) :
    MemLp (fourCellEvenP0246CutoffEightCapacityRepresenter c0 c2 c4 c6) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
  let p : ℝ → ℝ := factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6
  have hp : Continuous p := by
    simpa only [p] using
      continuous_factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6
  have hV : MemLp (fun x : ℝ ↦ yoshidaEndpointPotential x * p x) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) :=
    memLp_endpointPotential_mul_continuous p hp
  have hrightBase : MemLp (fun x : ℝ ↦ p ((8 / 5 : ℝ) + x)) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) :=
    memLp_two_restrict_centered_of_continuous _
      (hp.comp (continuous_const.add continuous_id))
  have hright : MemLp
      (factorTwoFixedLagRightRepresenter (8 / 5) p) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
    simpa only [factorTwoFixedLagRightRepresenter] using
      hrightBase.indicator (measurableSet_Icc :
        MeasurableSet (Icc (-1 : ℝ) (1 - 8 / 5)))
  have hleftBase : MemLp (fun x : ℝ ↦ p (x - (8 / 5 : ℝ))) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) :=
    memLp_two_restrict_centered_of_continuous _
      (hp.comp (continuous_id.sub continuous_const))
  have hleft : MemLp
      (factorTwoFixedLagLeftRepresenter (8 / 5) p) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
    simpa only [factorTwoFixedLagLeftRepresenter] using
      hleftBase.indicator (measurableSet_Icc :
        MeasurableSet (Icc (-1 + 8 / 5 : ℝ) 1))
  have hK : MemLp (factorTwoFixedLagK (8 / 5) p) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
    simpa only [factorTwoFixedLagK] using hright.add hleft
  have hcapacity := hV.sub (hK.const_mul (Real.sqrt 2 * Real.log 2 / 2))
  simpa only [fourCellEvenP0246CutoffEightCapacityRepresenter, p] using
    hcapacity

theorem intervalIntegrable_fourCellEvenP0246CutoffEightCapacityRepresenter_mul
    (c0 c2 c4 c6 : ℝ) (r : ℝ → ℝ) (hr : Continuous r) :
    IntervalIntegrable
      (fun x : ℝ ↦
        fourCellEvenP0246CutoffEightCapacityRepresenter c0 c2 c4 c6 x * r x)
      volume (-1) 1 := by
  let p : ℝ → ℝ := factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6
  have hp : Continuous p := by
    simpa only [p] using
      continuous_factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6
  have hV : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * p x * r x)
      volume (-1) 1 := by
    simpa only [mul_assoc] using
      intervalIntegrable_endpointPotential_mul
        (fun x ↦ p x * r x) (hp.mul hr)
  have hright :=
    intervalIntegrable_mul_factorTwoFixedLagRightRepresenter
      (8 / 5) p r hp hr
  have hleft0 :=
    intervalIntegrable_mul_factorTwoFixedLagLeftRepresenter
      (8 / 5) r p hr hp
  have hleft : IntervalIntegrable
      (fun x : ℝ ↦ factorTwoFixedLagLeftRepresenter (8 / 5) p x * r x)
      volume (-1) 1 := by
    apply hleft0.congr
    intro x _hx
    ring
  have hK : IntervalIntegrable
      (fun x : ℝ ↦ factorTwoFixedLagK (8 / 5) p x * r x)
      volume (-1) 1 := by
    apply (hright.add hleft).congr
    intro x _hx
    unfold factorTwoFixedLagK
    ring
  apply (hV.sub (hK.const_mul (Real.sqrt 2 * Real.log 2 / 2))).congr
  intro x _hx
  unfold fourCellEvenP0246CutoffEightCapacityRepresenter
  dsimp only [p]
  ring

/-- The capacity polarization is exactly the pairing with its fixed-lag
representer. -/
theorem fourCellEvenEndpointCapacityPolarization_P0246_eq_representerPairing
    (c0 c2 c4 c6 : ℝ) (r : ℝ → ℝ) (hr : Continuous r) :
    fourCellEvenEndpointCapacityPolarization
        (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) r =
      ∫ x : ℝ in -1..1,
        fourCellEvenP0246CutoffEightCapacityRepresenter c0 c2 c4 c6 x * r x := by
  let p : ℝ → ℝ := factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6
  have hp : Continuous p := by
    simpa only [p] using
      continuous_factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6
  have hV : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * p x * r x)
      volume (-1) 1 := by
    simpa only [mul_assoc] using
      intervalIntegrable_endpointPotential_mul
        (fun x ↦ p x * r x) (hp.mul hr)
  have hright :=
    intervalIntegrable_mul_factorTwoFixedLagRightRepresenter
      (8 / 5) p r hp hr
  have hleft0 :=
    intervalIntegrable_mul_factorTwoFixedLagLeftRepresenter
      (8 / 5) r p hr hp
  have hleft : IntervalIntegrable
      (fun x : ℝ ↦ factorTwoFixedLagLeftRepresenter (8 / 5) p x * r x)
      volume (-1) 1 := by
    apply hleft0.congr
    intro x _hx
    ring
  have hK : IntervalIntegrable
      (fun x : ℝ ↦ factorTwoFixedLagK (8 / 5) p x * r x)
      volume (-1) 1 := by
    apply (hright.add hleft).congr
    intro x _hx
    unfold factorTwoFixedLagK
    ring
  have hprime := correlationBilinear_eq_fixedLagK
    (8 / 5) p r hp hr (by norm_num : (8 / 5 : ℝ) ∈ Icc 0 2)
  unfold fourCellEvenEndpointCapacityPolarization
    fourCellEvenP0246CutoffEightCapacityRepresenter
  dsimp only [p] at hprime ⊢
  rw [show (fun x : ℝ ↦
      (yoshidaEndpointPotential x * p x -
          Real.sqrt 2 * Real.log 2 / 2 *
            factorTwoFixedLagK (8 / 5) p x) * r x) =
      fun x ↦ yoshidaEndpointPotential x * p x * r x -
        (Real.sqrt 2 * Real.log 2 / 2) *
          (factorTwoFixedLagK (8 / 5) p x * r x) by
    funext x
    ring,
    intervalIntegral.integral_sub hV
      (hK.const_mul (Real.sqrt 2 * Real.log 2 / 2)),
    intervalIntegral.integral_const_mul, hprime]
  ring

/-- Subtract an arbitrary degree-below-eight polynomial selector from the
capacity representer.  Every canonical moment-eight tail annihilates this
selector exactly. -/
def fourCellEvenP0246CutoffEightProjectedCapacityRepresenter
    (c0 c2 c4 c6 : ℝ) (q : ℝ[X]) (x : ℝ) : ℝ :=
  fourCellEvenP0246CutoffEightCapacityRepresenter c0 c2 c4 c6 x -
    centeredPolynomialLift q x

/-- Subtracting any polynomial selector preserves square-integrability, so
the projected Riesz route has no separate domain premise. -/
theorem memLp_fourCellEvenP0246CutoffEightProjectedCapacityRepresenter
    (c0 c2 c4 c6 : ℝ) (q : ℝ[X]) :
    MemLp
      (fourCellEvenP0246CutoffEightProjectedCapacityRepresenter
        c0 c2 c4 c6 q) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
  have hq : Continuous (centeredPolynomialLift q) := by
    unfold centeredPolynomialLift
    fun_prop
  have hqLp := memLp_two_restrict_centered_of_continuous _ hq
  simpa only [fourCellEvenP0246CutoffEightProjectedCapacityRepresenter] using
    (memLp_fourCellEvenP0246CutoffEightCapacityRepresenter
      c0 c2 c4 c6).sub hqLp

/-! ## The canonical degree-below-eight selector -/

/-- The four low Legendre pairings of the capacity row. -/
def fourCellEvenP0246CutoffEightCapacityRow0
    (c0 c2 c4 c6 : ℝ) : ℝ :=
  fourCellEvenEndpointCapacityPolarization
    (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) centeredEvenP0

def fourCellEvenP0246CutoffEightCapacityRow2
    (c0 c2 c4 c6 : ℝ) : ℝ :=
  fourCellEvenEndpointCapacityPolarization
    (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) centeredEvenP2

def fourCellEvenP0246CutoffEightCapacityRow4
    (c0 c2 c4 c6 : ℝ) : ℝ :=
  fourCellEvenEndpointCapacityPolarization
    (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) factorTwoCenteredP4

def fourCellEvenP0246CutoffEightCapacityRow6
    (c0 c2 c4 c6 : ℝ) : ℝ :=
  fourCellEvenEndpointCapacityPolarization
    (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) factorTwoCenteredP6

/-- The exact `L²` projection of the capacity representer onto
`P₀/P₂/P₄/P₆`.  The factors are the reciprocals of the classical
Legendre squared norms `2/(2n+1)`. -/
def fourCellEvenP0246CutoffEightCanonicalSelectorPolynomial
    (c0 c2 c4 c6 : ℝ) : ℝ[X] :=
  factorTwoIntrinsicEvenP0246Polynomial
    (fourCellEvenP0246CutoffEightCapacityRow0 c0 c2 c4 c6 / 2)
    (5 * fourCellEvenP0246CutoffEightCapacityRow2 c0 c2 c4 c6 / 2)
    (9 * fourCellEvenP0246CutoffEightCapacityRow4 c0 c2 c4 c6 / 2)
    (13 * fourCellEvenP0246CutoffEightCapacityRow6 c0 c2 c4 c6 / 2)

theorem natDegree_fourCellEvenP0246CutoffEightCanonicalSelectorPolynomial_lt_eight
    (c0 c2 c4 c6 : ℝ) :
    (fourCellEvenP0246CutoffEightCanonicalSelectorPolynomial
      c0 c2 c4 c6).natDegree < 8 := by
  unfold fourCellEvenP0246CutoffEightCanonicalSelectorPolynomial
  exact natDegree_factorTwoIntrinsicEvenP0246Polynomial_lt_eight _ _ _ _

theorem centeredPolynomialLift_cutoffEightCanonicalSelector
    (c0 c2 c4 c6 : ℝ) :
    centeredPolynomialLift
        (fourCellEvenP0246CutoffEightCanonicalSelectorPolynomial
          c0 c2 c4 c6) =
      factorTwoIntrinsicEvenP0246Profile
        (fourCellEvenP0246CutoffEightCapacityRow0 c0 c2 c4 c6 / 2)
        (5 * fourCellEvenP0246CutoffEightCapacityRow2 c0 c2 c4 c6 / 2)
        (9 * fourCellEvenP0246CutoffEightCapacityRow4 c0 c2 c4 c6 / 2)
        (13 * fourCellEvenP0246CutoffEightCapacityRow6 c0 c2 c4 c6 / 2) := by
  unfold fourCellEvenP0246CutoffEightCanonicalSelectorPolynomial
  exact centeredPolynomialLift_intrinsicEvenP0246Polynomial _ _ _ _

/-- Squared norm of the exact four-coordinate projection of the capacity
representer. -/
def fourCellEvenP0246CutoffEightCapacityLowProjectionEnergy
    (c0 c2 c4 c6 : ℝ) : ℝ :=
  fourCellEvenP0246CutoffEightCapacityRow0 c0 c2 c4 c6 ^ 2 / 2 +
    (5 / 2 : ℝ) *
      fourCellEvenP0246CutoffEightCapacityRow2 c0 c2 c4 c6 ^ 2 +
    (9 / 2 : ℝ) *
      fourCellEvenP0246CutoffEightCapacityRow4 c0 c2 c4 c6 ^ 2 +
    (13 / 2 : ℝ) *
      fourCellEvenP0246CutoffEightCapacityRow6 c0 c2 c4 c6 ^ 2

theorem integral_cutoffEightCanonicalSelector_sq_eq_lowProjectionEnergy
    (c0 c2 c4 c6 : ℝ) :
    (∫ x : ℝ in -1..1,
      centeredPolynomialLift
          (fourCellEvenP0246CutoffEightCanonicalSelectorPolynomial
            c0 c2 c4 c6) x ^ 2) =
      fourCellEvenP0246CutoffEightCapacityLowProjectionEnergy
        c0 c2 c4 c6 := by
  rw [centeredPolynomialLift_cutoffEightCanonicalSelector]
  have hmass := factorTwoIntrinsicEnergy_intrinsicEvenP0246
    (fourCellEvenP0246CutoffEightCapacityRow0 c0 c2 c4 c6 / 2)
    (5 * fourCellEvenP0246CutoffEightCapacityRow2 c0 c2 c4 c6 / 2)
    (9 * fourCellEvenP0246CutoffEightCapacityRow4 c0 c2 c4 c6 / 2)
    (13 * fourCellEvenP0246CutoffEightCapacityRow6 c0 c2 c4 c6 / 2)
  change (∫ x : ℝ in -1..1,
      factorTwoIntrinsicEvenP0246Profile
        (fourCellEvenP0246CutoffEightCapacityRow0 c0 c2 c4 c6 / 2)
        (5 * fourCellEvenP0246CutoffEightCapacityRow2 c0 c2 c4 c6 / 2)
        (9 * fourCellEvenP0246CutoffEightCapacityRow4 c0 c2 c4 c6 / 2)
        (13 * fourCellEvenP0246CutoffEightCapacityRow6 c0 c2 c4 c6 / 2) x ^ 2) = _
    at hmass
  rw [hmass]
  unfold fourCellEvenP0246CutoffEightCapacityLowProjectionEnergy
  ring

/-- Pairing the capacity row with its canonical low selector gives exactly
the selector's squared norm.  Thus this polynomial is the genuine Hilbert
projection, not merely an annihilating surrogate. -/
theorem capacityPolarization_cutoffEightCanonicalSelector_eq_lowProjectionEnergy
    (c0 c2 c4 c6 : ℝ) :
    fourCellEvenEndpointCapacityPolarization
        (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6)
        (centeredPolynomialLift
          (fourCellEvenP0246CutoffEightCanonicalSelectorPolynomial
            c0 c2 c4 c6)) =
      fourCellEvenP0246CutoffEightCapacityLowProjectionEnergy
        c0 c2 c4 c6 := by
  let p : ℝ → ℝ := factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6
  let b0 : ℝ := fourCellEvenP0246CutoffEightCapacityRow0 c0 c2 c4 c6
  let b2 : ℝ := fourCellEvenP0246CutoffEightCapacityRow2 c0 c2 c4 c6
  let b4 : ℝ := fourCellEvenP0246CutoffEightCapacityRow4 c0 c2 c4 c6
  let b6 : ℝ := fourCellEvenP0246CutoffEightCapacityRow6 c0 c2 c4 c6
  let d0 : ℝ := b0 / 2
  let d2 : ℝ := 5 * b2 / 2
  let d4 : ℝ := 9 * b4 / 2
  let d6 : ℝ := 13 * b6 / 2
  let s : ℝ → ℝ := factorTwoIntrinsicEvenP0246Profile d0 d2 d4 d6
  have hp : Continuous p := by
    simpa only [p] using
      continuous_factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6
  have hP0 : Continuous centeredEvenP0 := by
    unfold centeredEvenP0
    fun_prop
  have hP2 : Continuous centeredEvenP2 := by
    unfold centeredEvenP2
    fun_prop
  have hP4 : Continuous factorTwoCenteredP4 :=
    continuous_factorTwoCenteredP4
  have hP6 : Continuous factorTwoCenteredP6 :=
    continuous_factorTwoCenteredP6
  have hs : s =
      d0 • centeredEvenP0 +
        (d2 • centeredEvenP2 +
          (d4 • factorTwoCenteredP4 + d6 • factorTwoCenteredP6)) := by
    funext x
    unfold s factorTwoIntrinsicEvenP0246Profile
      factorTwoIntrinsicEvenP024Profile factorTwoEvenStructuralLowProfile
      factorTwoIntrinsicSixEvenTail
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hf0 : Continuous (d0 • centeredEvenP0) := by
    change Continuous (fun x ↦ d0 * centeredEvenP0 x)
    exact continuous_const.mul hP0
  have hf2 : Continuous (d2 • centeredEvenP2) := by
    change Continuous (fun x ↦ d2 * centeredEvenP2 x)
    exact continuous_const.mul hP2
  have hf4 : Continuous (d4 • factorTwoCenteredP4) := by
    change Continuous (fun x ↦ d4 * factorTwoCenteredP4 x)
    exact continuous_const.mul hP4
  have hf6 : Continuous (d6 • factorTwoCenteredP6) := by
    change Continuous (fun x ↦ d6 * factorTwoCenteredP6 x)
    exact continuous_const.mul hP6
  rw [centeredPolynomialLift_cutoffEightCanonicalSelector]
  change fourCellEvenEndpointCapacityPolarization p s = _
  rw [hs,
    fourCellEvenEndpointCapacityPolarization_add_right p
      (d0 • centeredEvenP0)
      (d2 • centeredEvenP2 +
        (d4 • factorTwoCenteredP4 + d6 • factorTwoCenteredP6))
      hp hf0 (hf2.add (hf4.add hf6)),
    fourCellEvenEndpointCapacityPolarization_add_right p
      (d2 • centeredEvenP2)
      (d4 • factorTwoCenteredP4 + d6 • factorTwoCenteredP6)
      hp hf2 (hf4.add hf6),
    fourCellEvenEndpointCapacityPolarization_add_right p
      (d4 • factorTwoCenteredP4) (d6 • factorTwoCenteredP6)
      hp hf4 hf6,
    fourCellEvenEndpointCapacityPolarization_smul_right,
    fourCellEvenEndpointCapacityPolarization_smul_right,
    fourCellEvenEndpointCapacityPolarization_smul_right,
    fourCellEvenEndpointCapacityPolarization_smul_right]
  dsimp only [d0, d2, d4, d6, b0, b2, b4, b6, p]
  unfold fourCellEvenP0246CutoffEightCapacityLowProjectionEnergy
    fourCellEvenP0246CutoffEightCapacityRow0
    fourCellEvenP0246CutoffEightCapacityRow2
    fourCellEvenP0246CutoffEightCapacityRow4
    fourCellEvenP0246CutoffEightCapacityRow6
  ring

/-- Exact Pythagorean identity for the canonical selector.  The projected
representer norm is the full norm minus precisely the four low capacity-row
squares. -/
theorem integral_cutoffEightCanonicalProjectedRepresenter_sq_eq
    (c0 c2 c4 c6 : ℝ) :
    (∫ x : ℝ in -1..1,
      fourCellEvenP0246CutoffEightProjectedCapacityRepresenter
        c0 c2 c4 c6
        (fourCellEvenP0246CutoffEightCanonicalSelectorPolynomial
          c0 c2 c4 c6) x ^ 2) =
      (∫ x : ℝ in -1..1,
        fourCellEvenP0246CutoffEightCapacityRepresenter
          c0 c2 c4 c6 x ^ 2) -
        fourCellEvenP0246CutoffEightCapacityLowProjectionEnergy
          c0 c2 c4 c6 := by
  let G : ℝ → ℝ :=
    fourCellEvenP0246CutoffEightCapacityRepresenter c0 c2 c4 c6
  let q : ℝ[X] :=
    fourCellEvenP0246CutoffEightCanonicalSelectorPolynomial c0 c2 c4 c6
  let S : ℝ → ℝ := centeredPolynomialLift q
  have hScont : Continuous S := by
    dsimp only [S]
    unfold centeredPolynomialLift
    fun_prop
  have hGsqOn : Integrable (fun x : ℝ ↦ ‖G x‖ ^ 2)
      (volume.restrict (Ioc (-1 : ℝ) 1)) :=
    (memLp_fourCellEvenP0246CutoffEightCapacityRepresenter
      c0 c2 c4 c6).integrable_norm_pow (by norm_num)
  have hGsq : IntervalIntegrable (fun x : ℝ ↦ G x ^ 2)
      volume (-1) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
    apply hGsqOn.congr
    filter_upwards with x
    rw [Real.norm_eq_abs, sq_abs]
  have hGS : IntervalIntegrable (fun x : ℝ ↦ G x * S x)
      volume (-1) 1 := by
    simpa only [G, S, q] using
      intervalIntegrable_fourCellEvenP0246CutoffEightCapacityRepresenter_mul
        c0 c2 c4 c6
        (centeredPolynomialLift
          (fourCellEvenP0246CutoffEightCanonicalSelectorPolynomial
            c0 c2 c4 c6)) hScont
  have hSsq : IntervalIntegrable (fun x : ℝ ↦ S x ^ 2)
      volume (-1) 1 := (hScont.pow 2).intervalIntegrable (-1) 1
  have hpair : (∫ x : ℝ in -1..1, G x * S x) =
      fourCellEvenP0246CutoffEightCapacityLowProjectionEnergy
        c0 c2 c4 c6 := by
    rw [← capacityPolarization_cutoffEightCanonicalSelector_eq_lowProjectionEnergy]
    symm
    simpa only [G, S, q] using
      fourCellEvenEndpointCapacityPolarization_P0246_eq_representerPairing
        c0 c2 c4 c6
        (centeredPolynomialLift
          (fourCellEvenP0246CutoffEightCanonicalSelectorPolynomial
            c0 c2 c4 c6)) hScont
  have hSnorm : (∫ x : ℝ in -1..1, S x ^ 2) =
      fourCellEvenP0246CutoffEightCapacityLowProjectionEnergy
        c0 c2 c4 c6 := by
    simpa only [S, q] using
      integral_cutoffEightCanonicalSelector_sq_eq_lowProjectionEnergy
        c0 c2 c4 c6
  change (∫ x : ℝ in -1..1, (G x - S x) ^ 2) = _
  rw [show (fun x : ℝ ↦ (G x - S x) ^ 2) =
      fun x ↦ G x ^ 2 - 2 * (G x * S x) + S x ^ 2 by
    funext x
    ring,
    intervalIntegral.integral_add (hGsq.sub (hGS.const_mul 2)) hSsq,
    intervalIntegral.integral_sub hGsq (hGS.const_mul 2),
    intervalIntegral.integral_const_mul, hpair, hSnorm]
  ring

/-! ## Exact fixed-lag projected tail -/

private def cutoffEightFixedLagRightP0 (x : ℝ) : ℝ :=
  centeredEvenP0 (x - 8 / 5)

private def cutoffEightFixedLagRightP2 (x : ℝ) : ℝ :=
  centeredEvenP2 (x - 8 / 5)

private def cutoffEightFixedLagRightP4 (x : ℝ) : ℝ :=
  factorTwoCenteredP4 (x - 8 / 5)

private def cutoffEightFixedLagRightP6 (x : ℝ) : ℝ :=
  factorTwoCenteredP6 (x - 8 / 5)

private theorem two_mul_integral_fixedLagRightP0_P0 :
    2 * (∫ x : ℝ in 3 / 5..1,
      cutoffEightFixedLagRightP0 x * cutoffEightFixedLagRightP0 x) =
      4 / 5 := by
  unfold cutoffEightFixedLagRightP0 centeredEvenP0
  norm_num

private theorem two_mul_integral_fixedLagRightP0_P2 :
    2 * (∫ x : ℝ in 3 / 5..1,
      cutoffEightFixedLagRightP0 x * cutoffEightFixedLagRightP2 x) =
      48 / 125 := by
  unfold cutoffEightFixedLagRightP0 cutoffEightFixedLagRightP2
    centeredEvenP0 centeredEvenP2
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (3 / 5) 1)
    (Continuous.intervalIntegrable (by fun_prop) (3 / 5) 1)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [integral_pow]
  norm_num

private theorem two_mul_integral_fixedLagRightP0_P4 :
    2 * (∫ x : ℝ in 3 / 5..1,
      cutoffEightFixedLagRightP0 x * cutoffEightFixedLagRightP4 x) =
      -144 / 3125 := by
  unfold cutoffEightFixedLagRightP0 cutoffEightFixedLagRightP4
    centeredEvenP0 factorTwoCenteredP4
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (3 / 5) 1)
    (Continuous.intervalIntegrable (by fun_prop) (3 / 5) 1)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [integral_pow]
  norm_num

private theorem two_mul_integral_fixedLagRightP0_P6 :
    2 * (∫ x : ℝ in 3 / 5..1,
      cutoffEightFixedLagRightP0 x * cutoffEightFixedLagRightP6 x) =
      -5712 / 78125 := by
  unfold cutoffEightFixedLagRightP0 cutoffEightFixedLagRightP6 centeredEvenP0
  simp only [factorTwoCenteredP6_eq]
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (3 / 5) 1)
    (Continuous.intervalIntegrable (by fun_prop) (3 / 5) 1)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [integral_pow]
  norm_num

private theorem two_mul_integral_fixedLagRightP2_P2 :
    2 * (∫ x : ℝ in 3 / 5..1,
      cutoffEightFixedLagRightP2 x * cutoffEightFixedLagRightP2 x) =
      3844 / 15625 := by
  unfold cutoffEightFixedLagRightP2 centeredEvenP2
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (3 / 5) 1)
    (Continuous.intervalIntegrable (by fun_prop) (3 / 5) 1)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [integral_pow]
  norm_num

private theorem two_mul_integral_fixedLagRightP2_P4 :
    2 * (∫ x : ℝ in 3 / 5..1,
      cutoffEightFixedLagRightP2 x * cutoffEightFixedLagRightP4 x) =
      1008 / 15625 := by
  unfold cutoffEightFixedLagRightP2 cutoffEightFixedLagRightP4
    centeredEvenP2 factorTwoCenteredP4
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (3 / 5) 1)
    (Continuous.intervalIntegrable (by fun_prop) (3 / 5) 1)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [integral_pow]
  norm_num

private theorem two_mul_integral_fixedLagRightP2_P6 :
    2 * (∫ x : ℝ in 3 / 5..1,
      cutoffEightFixedLagRightP2 x * cutoffEightFixedLagRightP6 x) =
      -28176 / 1953125 := by
  unfold cutoffEightFixedLagRightP2 cutoffEightFixedLagRightP6 centeredEvenP2
  simp only [factorTwoCenteredP6_eq]
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (3 / 5) 1)
    (Continuous.intervalIntegrable (by fun_prop) (3 / 5) 1)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [integral_pow]
  norm_num

private theorem two_mul_integral_fixedLagRightP4_P4 :
    2 * (∫ x : ℝ in 3 / 5..1,
      cutoffEightFixedLagRightP4 x * cutoffEightFixedLagRightP4 x) =
      97444 / 703125 := by
  unfold cutoffEightFixedLagRightP4 factorTwoCenteredP4
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (3 / 5) 1)
    (Continuous.intervalIntegrable (by fun_prop) (3 / 5) 1)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [integral_pow]
  norm_num

private theorem two_mul_integral_fixedLagRightP4_P6 :
    2 * (∫ x : ℝ in 3 / 5..1,
      cutoffEightFixedLagRightP4 x * cutoffEightFixedLagRightP6 x) =
      626544 / 9765625 := by
  unfold cutoffEightFixedLagRightP4 cutoffEightFixedLagRightP6
    factorTwoCenteredP4
  simp only [factorTwoCenteredP6_eq]
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (3 / 5) 1)
    (Continuous.intervalIntegrable (by fun_prop) (3 / 5) 1)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [integral_pow]
  norm_num

private theorem two_mul_integral_fixedLagRightP6_P6 :
    2 * (∫ x : ℝ in 3 / 5..1,
      cutoffEightFixedLagRightP6 x * cutoffEightFixedLagRightP6 x) =
      1342897924 / 15869140625 := by
  unfold cutoffEightFixedLagRightP6
  simp only [factorTwoCenteredP6_eq]
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (3 / 5) 1)
    (Continuous.intervalIntegrable (by fun_prop) (3 / 5) 1)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [integral_pow]
  norm_num

/-- Full squared norm of the symmetric fixed-lag representer before removing
its four low Legendre coordinates. -/
def fourCellEvenP0246CutoffEightFixedLagFullGram
    (c0 c2 c4 c6 : ℝ) : ℝ :=
  (4 / 5 : ℝ) * c0 ^ 2 +
    2 * (48 / 125 : ℝ) * c0 * c2 -
    2 * (144 / 3125 : ℝ) * c0 * c4 -
    2 * (5712 / 78125 : ℝ) * c0 * c6 +
    (3844 / 15625 : ℝ) * c2 ^ 2 +
    2 * (1008 / 15625 : ℝ) * c2 * c4 -
    2 * (28176 / 1953125 : ℝ) * c2 * c6 +
    (97444 / 703125 : ℝ) * c4 ^ 2 +
    2 * (626544 / 9765625 : ℝ) * c4 * c6 +
    (1342897924 / 15869140625 : ℝ) * c6 ^ 2

set_option maxHeartbeats 800000 in
theorem integral_fixedLagK_intrinsicEvenP0246_sq_eq_fullGram
    (c0 c2 c4 c6 : ℝ) :
    (∫ x : ℝ in -1..1,
      factorTwoFixedLagK (8 / 5)
        (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) x ^ 2) =
      fourCellEvenP0246CutoffEightFixedLagFullGram c0 c2 c4 c6 := by
  let p : ℝ → ℝ := factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6
  let K : ℝ → ℝ := factorTwoFixedLagK (8 / 5) p
  have hp : Continuous p := by
    simpa only [p] using
      continuous_factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6
  have hpEven : Function.Even p := by
    simpa only [p] using
      even_factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6
  have hKsqOn : Integrable (fun x : ℝ ↦ ‖K x‖ ^ 2)
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
    simpa only [K, p] using
      (memLp_fixedLagK_intrinsicEvenP0246 c0 c2 c4 c6).integrable_norm_pow
        (by norm_num)
  have hKsq : IntervalIntegrable (fun x : ℝ ↦ K x ^ 2)
      volume (-1) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
    apply hKsqOn.congr
    filter_upwards with x
    rw [Real.norm_eq_abs, sq_abs]
  have hKEven : Function.Even K := by
    intro x
    unfold K factorTwoFixedLagK
    rw [factorTwoFixedLagRightRepresenter_neg_of_even hpEven,
      factorTwoFixedLagLeftRepresenter_neg_of_even hpEven]
    ring
  have hDensityEven : Function.Even (fun x : ℝ ↦ K x ^ 2) := by
    intro x
    change K (-x) ^ 2 = K x ^ 2
    rw [hKEven x]
  have hfold := integral_neg_one_one_eq_two_mul_zero_one_of_even
    (fun x : ℝ ↦ K x ^ 2) hKsq hDensityEven
  have hzero : (∫ x : ℝ in 0..3 / 5, K x ^ 2) = 0 := by
    apply intervalIntegral.integral_zero_ae
    filter_upwards [MeasureTheory.Measure.ae_ne volume (3 / 5 : ℝ)] with x hxne hx
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 3 / 5)] at hx
    have hxlt : x < 3 / 5 := lt_of_le_of_ne hx.2 hxne
    have hright : x ∉ Icc (-1 : ℝ) (1 - 8 / 5) := by
      intro h
      linarith [hx.1, h.2]
    have hleft : x ∉ Icc (-1 + 8 / 5 : ℝ) 1 := by
      intro h
      linarith [hxlt, h.1]
    unfold K factorTwoFixedLagK factorTwoFixedLagRightRepresenter
      factorTwoFixedLagLeftRepresenter
    rw [Set.indicator_of_notMem hright, Set.indicator_of_notMem hleft]
    norm_num
  have hright :
      (∫ x : ℝ in 3 / 5..1, K x ^ 2) =
        ∫ x : ℝ in 3 / 5..1, p (x - 8 / 5) ^ 2 := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num : (3 / 5 : ℝ) ≤ 1)] at hx
    have hrightNot : x ∉ Icc (-1 : ℝ) (1 - 8 / 5) := by
      intro h
      linarith [hx.1, h.2]
    have hleftMem : x ∈ Icc (-1 + 8 / 5 : ℝ) 1 := by
      constructor <;> linarith [hx.1, hx.2]
    change K x ^ 2 = p (x - 8 / 5) ^ 2
    unfold K factorTwoFixedLagK factorTwoFixedLagRightRepresenter
      factorTwoFixedLagLeftRepresenter
    rw [Set.indicator_of_notMem hrightNot,
      Set.indicator_of_mem hleftMem, zero_add]
  have hzeroI : IntervalIntegrable (fun x : ℝ ↦ K x ^ 2)
      volume 0 (3 / 5) := hKsq.mono_set (by
    intro x hx
    norm_num at hx ⊢
    constructor <;> linarith [hx.1, hx.2])
  have hrightI : IntervalIntegrable (fun x : ℝ ↦ K x ^ 2)
      volume (3 / 5) 1 := hKsq.mono_set (by
    intro x hx
    norm_num at hx ⊢
    constructor <;> linarith [hx.1, hx.2])
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    hzeroI hrightI
  rw [hzero, zero_add, hright] at hsplit
  rw [← hsplit] at hfold
  change (∫ x : ℝ in -1..1, K x ^ 2) = _
  rw [hfold]
  rw [show (fun x : ℝ ↦ p (x - 8 / 5) ^ 2) = fun x ↦
      c0 ^ 2 *
          (cutoffEightFixedLagRightP0 x * cutoffEightFixedLagRightP0 x) +
        (2 * c0 * c2) *
          (cutoffEightFixedLagRightP0 x * cutoffEightFixedLagRightP2 x) +
        (2 * c0 * c4) *
          (cutoffEightFixedLagRightP0 x * cutoffEightFixedLagRightP4 x) +
        (2 * c0 * c6) *
          (cutoffEightFixedLagRightP0 x * cutoffEightFixedLagRightP6 x) +
        c2 ^ 2 *
          (cutoffEightFixedLagRightP2 x * cutoffEightFixedLagRightP2 x) +
        (2 * c2 * c4) *
          (cutoffEightFixedLagRightP2 x * cutoffEightFixedLagRightP4 x) +
        (2 * c2 * c6) *
          (cutoffEightFixedLagRightP2 x * cutoffEightFixedLagRightP6 x) +
        c4 ^ 2 *
          (cutoffEightFixedLagRightP4 x * cutoffEightFixedLagRightP4 x) +
        (2 * c4 * c6) *
          (cutoffEightFixedLagRightP4 x * cutoffEightFixedLagRightP6 x) +
        c6 ^ 2 *
          (cutoffEightFixedLagRightP6 x * cutoffEightFixedLagRightP6 x) by
    funext x
    unfold p factorTwoIntrinsicEvenP0246Profile
      factorTwoIntrinsicEvenP024Profile factorTwoEvenStructuralLowProfile
      factorTwoIntrinsicSixEvenTail cutoffEightFixedLagRightP0
      cutoffEightFixedLagRightP2 cutoffEightFixedLagRightP4
      cutoffEightFixedLagRightP6
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring]
  repeat rw [intervalIntegral.integral_add]
  all_goals try
    apply Continuous.intervalIntegrable
    simp only [cutoffEightFixedLagRightP0, cutoffEightFixedLagRightP2,
      cutoffEightFixedLagRightP4, cutoffEightFixedLagRightP6,
      centeredEvenP0, centeredEvenP2, factorTwoCenteredP4,
      factorTwoCenteredP6_eq]
    fun_prop
  repeat rw [intervalIntegral.integral_const_mul]
  have h00 :
      (∫ x : ℝ in 3 / 5..1,
        cutoffEightFixedLagRightP0 x * cutoffEightFixedLagRightP0 x) =
        2 / 5 := by
    linarith [two_mul_integral_fixedLagRightP0_P0]
  have h02 :
      (∫ x : ℝ in 3 / 5..1,
        cutoffEightFixedLagRightP0 x * cutoffEightFixedLagRightP2 x) =
        24 / 125 := by
    linarith [two_mul_integral_fixedLagRightP0_P2]
  have h04 :
      (∫ x : ℝ in 3 / 5..1,
        cutoffEightFixedLagRightP0 x * cutoffEightFixedLagRightP4 x) =
        -72 / 3125 := by
    linarith [two_mul_integral_fixedLagRightP0_P4]
  have h06 :
      (∫ x : ℝ in 3 / 5..1,
        cutoffEightFixedLagRightP0 x * cutoffEightFixedLagRightP6 x) =
        -2856 / 78125 := by
    linarith [two_mul_integral_fixedLagRightP0_P6]
  have h22 :
      (∫ x : ℝ in 3 / 5..1,
        cutoffEightFixedLagRightP2 x * cutoffEightFixedLagRightP2 x) =
        1922 / 15625 := by
    linarith [two_mul_integral_fixedLagRightP2_P2]
  have h24 :
      (∫ x : ℝ in 3 / 5..1,
        cutoffEightFixedLagRightP2 x * cutoffEightFixedLagRightP4 x) =
        504 / 15625 := by
    linarith [two_mul_integral_fixedLagRightP2_P4]
  have h26 :
      (∫ x : ℝ in 3 / 5..1,
        cutoffEightFixedLagRightP2 x * cutoffEightFixedLagRightP6 x) =
        -14088 / 1953125 := by
    linarith [two_mul_integral_fixedLagRightP2_P6]
  have h44 :
      (∫ x : ℝ in 3 / 5..1,
        cutoffEightFixedLagRightP4 x * cutoffEightFixedLagRightP4 x) =
        48722 / 703125 := by
    linarith [two_mul_integral_fixedLagRightP4_P4]
  have h46 :
      (∫ x : ℝ in 3 / 5..1,
        cutoffEightFixedLagRightP4 x * cutoffEightFixedLagRightP6 x) =
        313272 / 9765625 := by
    linarith [two_mul_integral_fixedLagRightP4_P6]
  have h66 :
      (∫ x : ℝ in 3 / 5..1,
        cutoffEightFixedLagRightP6 x * cutoffEightFixedLagRightP6 x) =
        671448962 / 15869140625 := by
    linarith [two_mul_integral_fixedLagRightP6_P6]
  rw [h00, h02, h04, h06, h22, h24, h26, h44, h46, h66]
  unfold fourCellEvenP0246CutoffEightFixedLagFullGram
  ring

private theorem factorTwoCenteredCorrelationBilinear_intrinsicEvenP0246_left
    (c0 c2 c4 c6 : ℝ) (r : ℝ → ℝ) (t : ℝ) (hr : Continuous r) :
    factorTwoCenteredCorrelationBilinear
        (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) r t =
      c0 * factorTwoCenteredCorrelationBilinear centeredEvenP0 r t +
        c2 * factorTwoCenteredCorrelationBilinear centeredEvenP2 r t +
        c4 * factorTwoCenteredCorrelationBilinear factorTwoCenteredP4 r t +
        c6 * factorTwoCenteredCorrelationBilinear factorTwoCenteredP6 r t := by
  have h0 : Continuous centeredEvenP0 := by
    unfold centeredEvenP0
    fun_prop
  have h2 : Continuous centeredEvenP2 := by
    unfold centeredEvenP2
    fun_prop
  have h4 : Continuous factorTwoCenteredP4 :=
    continuous_factorTwoCenteredP4
  have h6 : Continuous factorTwoCenteredP6 :=
    continuous_factorTwoCenteredP6
  let f0 : ℝ → ℝ := fun x ↦ c0 * centeredEvenP0 x
  let f2 : ℝ → ℝ := fun x ↦ c2 * centeredEvenP2 x
  let f4 : ℝ → ℝ := fun x ↦ c4 * factorTwoCenteredP4 x
  let f6 : ℝ → ℝ := fun x ↦ c6 * factorTwoCenteredP6 x
  have hf0 : Continuous f0 := continuous_const.mul h0
  have hf2 : Continuous f2 := continuous_const.mul h2
  have hf4 : Continuous f4 := continuous_const.mul h4
  have hf6 : Continuous f6 := continuous_const.mul h6
  have hadd (u v w : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
      (hw : Continuous w) :
      factorTwoCenteredCorrelationBilinear (u + v) w t =
        factorTwoCenteredCorrelationBilinear u w t +
          factorTwoCenteredCorrelationBilinear v w t := by
    unfold factorTwoCenteredCorrelationBilinear
    rw [factorTwoCenteredCrossCorrelation_add_left u v w hu hv hw t,
      factorTwoCenteredCrossCorrelation_add_right w u v hw hu hv t]
    ring
  have hprofile :
      factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6 =
        ((f0 + f2) + f4) + f6 := by
    funext x
    unfold factorTwoIntrinsicEvenP0246Profile
      factorTwoIntrinsicEvenP024Profile factorTwoEvenStructuralLowProfile
      factorTwoIntrinsicSixEvenTail
    simp only [f0, f2, f4, f6, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hprofile,
    hadd ((f0 + f2) + f4) f6 r ((hf0.add hf2).add hf4) hf6 hr,
    hadd (f0 + f2) f4 r (hf0.add hf2) hf4 hr,
    hadd f0 f2 r hf0 hf2 hr]
  change
    factorTwoCenteredCorrelationBilinear (c0 • centeredEvenP0) r t +
          factorTwoCenteredCorrelationBilinear (c2 • centeredEvenP2) r t +
        factorTwoCenteredCorrelationBilinear (c4 • factorTwoCenteredP4) r t +
      factorTwoCenteredCorrelationBilinear (c6 • factorTwoCenteredP6) r t = _
  have hsmul (c : ℝ) (u : ℝ → ℝ) :
      factorTwoCenteredCorrelationBilinear (c • u) r t =
        c * factorTwoCenteredCorrelationBilinear u r t := by
    simpa using factorTwoCenteredCorrelationBilinear_smul_smul
      c 1 u r t
  rw [hsmul c0 centeredEvenP0, hsmul c2 centeredEvenP2,
    hsmul c4 factorTwoCenteredP4, hsmul c6 factorTwoCenteredP6]

private theorem factorTwoCenteredCorrelationBilinear_intrinsicEvenP0246_p0
    (c0 c2 c4 c6 : ℝ) :
    factorTwoCenteredCorrelationBilinear
        (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6)
        centeredEvenP0 (8 / 5) =
      (2 / 5 : ℝ) * c0 + (24 / 125 : ℝ) * c2 -
        (72 / 3125 : ℝ) * c4 - (2856 / 78125 : ℝ) * c6 := by
  rw [factorTwoCenteredCorrelationBilinear_intrinsicEvenP0246_left
    c0 c2 c4 c6 centeredEvenP0 (8 / 5) (by
      unfold centeredEvenP0
      fun_prop),
    factorTwoCenteredCorrelationBilinear_p0_p0,
    factorTwoCenteredCorrelationBilinear_comm centeredEvenP2 centeredEvenP0,
    factorTwoCenteredCorrelationBilinear_p0_p2,
    factorTwoCenteredCorrelationBilinear_comm factorTwoCenteredP4 centeredEvenP0,
    factorTwoCenteredCorrelationBilinear_p0_p4,
    factorTwoCenteredCorrelationBilinear_comm factorTwoCenteredP6 centeredEvenP0,
    factorTwoCenteredCorrelationBilinear_p0_p6]
  norm_num [factorTwoIntrinsicP4Correlation04,
    factorTwoIntrinsicP6Correlation06]
  ring

private theorem factorTwoCenteredCorrelationBilinear_intrinsicEvenP0246_p2
    (c0 c2 c4 c6 : ℝ) :
    factorTwoCenteredCorrelationBilinear
        (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6)
        centeredEvenP2 (8 / 5) =
      (24 / 125 : ℝ) * c0 + (962 / 15625 : ℝ) * c2 -
        (4072 / 78125 : ℝ) * c4 - (46536 / 1953125 : ℝ) * c6 := by
  rw [factorTwoCenteredCorrelationBilinear_intrinsicEvenP0246_left
    c0 c2 c4 c6 centeredEvenP2 (8 / 5) (by
      unfold centeredEvenP2
      fun_prop),
    factorTwoCenteredCorrelationBilinear_p0_p2,
    factorTwoCenteredCorrelationBilinear_p2_p2,
    factorTwoCenteredCorrelationBilinear_comm factorTwoCenteredP4 centeredEvenP2,
    factorTwoCenteredCorrelationBilinear_p2_p4,
    factorTwoCenteredCorrelationBilinear_comm factorTwoCenteredP6 centeredEvenP2,
    factorTwoCenteredCorrelationBilinear_p2_p6]
  norm_num [factorTwoIntrinsicP4Correlation24,
    factorTwoIntrinsicP6Correlation26]
  ring

private theorem factorTwoCenteredCorrelationBilinear_intrinsicEvenP0246_p4
    (c0 c2 c4 c6 : ℝ) :
    factorTwoCenteredCorrelationBilinear
        (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6)
        factorTwoCenteredP4 (8 / 5) =
      -(72 / 3125 : ℝ) * c0 - (4072 / 78125 : ℝ) * c2 -
        (164582 / 3515625 : ℝ) * c4 +
        (381976 / 48828125 : ℝ) * c6 := by
  rw [factorTwoCenteredCorrelationBilinear_intrinsicEvenP0246_left
    c0 c2 c4 c6 factorTwoCenteredP4 (8 / 5)
      continuous_factorTwoCenteredP4,
    factorTwoCenteredCorrelationBilinear_p0_p4,
    factorTwoCenteredCorrelationBilinear_p2_p4,
    factorTwoCenteredCorrelationBilinear_self,
    centeredEndpointCorrelation_p4,
    factorTwoCenteredCorrelationBilinear_comm factorTwoCenteredP6 factorTwoCenteredP4,
    factorTwoCenteredCorrelationBilinear_p4_p6]
  norm_num [factorTwoIntrinsicP4Correlation04,
    factorTwoIntrinsicP4Correlation24, factorTwoIntrinsicP4Correlation44,
    factorTwoIntrinsicP6Correlation46]
  ring

private theorem factorTwoCenteredCorrelationBilinear_intrinsicEvenP0246_p6
    (c0 c2 c4 c6 : ℝ) :
    factorTwoCenteredCorrelationBilinear
        (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6)
        factorTwoCenteredP6 (8 / 5) =
      -(2856 / 78125 : ℝ) * c0 - (46536 / 1953125 : ℝ) * c2 +
        (381976 / 48828125 : ℝ) * c4 +
        (456595778 / 15869140625 : ℝ) * c6 := by
  rw [factorTwoCenteredCorrelationBilinear_intrinsicEvenP0246_left
    c0 c2 c4 c6 factorTwoCenteredP6 (8 / 5)
      continuous_factorTwoCenteredP6,
    factorTwoCenteredCorrelationBilinear_p0_p6,
    factorTwoCenteredCorrelationBilinear_p2_p6,
    factorTwoCenteredCorrelationBilinear_p4_p6,
    factorTwoCenteredCorrelationBilinear_p6_p6]
  norm_num [factorTwoIntrinsicP6Correlation06,
    factorTwoIntrinsicP6Correlation26, factorTwoIntrinsicP6Correlation46,
    factorTwoIntrinsicP6Correlation66]
  ring

/-- Exact low Legendre coordinates of the fixed-lag representer. -/
def fourCellEvenP0246CutoffEightFixedLagRow0
    (c0 c2 c4 c6 : ℝ) : ℝ :=
  (4 / 5 : ℝ) * c0 + (48 / 125 : ℝ) * c2 -
    (144 / 3125 : ℝ) * c4 - (5712 / 78125 : ℝ) * c6

def fourCellEvenP0246CutoffEightFixedLagRow2
    (c0 c2 c4 c6 : ℝ) : ℝ :=
  (48 / 125 : ℝ) * c0 + (1924 / 15625 : ℝ) * c2 -
    (8144 / 78125 : ℝ) * c4 - (93072 / 1953125 : ℝ) * c6

def fourCellEvenP0246CutoffEightFixedLagRow4
    (c0 c2 c4 c6 : ℝ) : ℝ :=
  -(144 / 3125 : ℝ) * c0 - (8144 / 78125 : ℝ) * c2 -
    (329164 / 3515625 : ℝ) * c4 +
    (763952 / 48828125 : ℝ) * c6

def fourCellEvenP0246CutoffEightFixedLagRow6
    (c0 c2 c4 c6 : ℝ) : ℝ :=
  -(5712 / 78125 : ℝ) * c0 - (93072 / 1953125 : ℝ) * c2 +
    (763952 / 48828125 : ℝ) * c4 +
    (913191556 / 15869140625 : ℝ) * c6

private theorem integral_fixedLagK_intrinsicEvenP0246_mul_eq_two_correlation
    (c0 c2 c4 c6 : ℝ) (r : ℝ → ℝ) (hr : Continuous r) :
    (∫ x : ℝ in -1..1,
      factorTwoFixedLagK (8 / 5)
        (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) x * r x) =
      2 * factorTwoCenteredCorrelationBilinear
        (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) r (8 / 5) := by
  have h := correlationBilinear_eq_fixedLagK
    (8 / 5) (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) r
    (continuous_factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) hr
    (by norm_num : (8 / 5 : ℝ) ∈ Icc 0 2)
  linarith

theorem integral_fixedLagK_intrinsicEvenP0246_mul_P0
    (c0 c2 c4 c6 : ℝ) :
    (∫ x : ℝ in -1..1,
      factorTwoFixedLagK (8 / 5)
          (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) x *
        centeredEvenP0 x) =
      fourCellEvenP0246CutoffEightFixedLagRow0 c0 c2 c4 c6 := by
  rw [integral_fixedLagK_intrinsicEvenP0246_mul_eq_two_correlation
    c0 c2 c4 c6 centeredEvenP0 (by unfold centeredEvenP0; fun_prop),
    factorTwoCenteredCorrelationBilinear_intrinsicEvenP0246_p0]
  unfold fourCellEvenP0246CutoffEightFixedLagRow0
  ring

theorem integral_fixedLagK_intrinsicEvenP0246_mul_P2
    (c0 c2 c4 c6 : ℝ) :
    (∫ x : ℝ in -1..1,
      factorTwoFixedLagK (8 / 5)
          (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) x *
        centeredEvenP2 x) =
      fourCellEvenP0246CutoffEightFixedLagRow2 c0 c2 c4 c6 := by
  rw [integral_fixedLagK_intrinsicEvenP0246_mul_eq_two_correlation
    c0 c2 c4 c6 centeredEvenP2 (by unfold centeredEvenP2; fun_prop),
    factorTwoCenteredCorrelationBilinear_intrinsicEvenP0246_p2]
  unfold fourCellEvenP0246CutoffEightFixedLagRow2
  ring

theorem integral_fixedLagK_intrinsicEvenP0246_mul_P4
    (c0 c2 c4 c6 : ℝ) :
    (∫ x : ℝ in -1..1,
      factorTwoFixedLagK (8 / 5)
          (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) x *
        factorTwoCenteredP4 x) =
      fourCellEvenP0246CutoffEightFixedLagRow4 c0 c2 c4 c6 := by
  rw [integral_fixedLagK_intrinsicEvenP0246_mul_eq_two_correlation
    c0 c2 c4 c6 factorTwoCenteredP4 continuous_factorTwoCenteredP4,
    factorTwoCenteredCorrelationBilinear_intrinsicEvenP0246_p4]
  unfold fourCellEvenP0246CutoffEightFixedLagRow4
  ring

theorem integral_fixedLagK_intrinsicEvenP0246_mul_P6
    (c0 c2 c4 c6 : ℝ) :
    (∫ x : ℝ in -1..1,
      factorTwoFixedLagK (8 / 5)
          (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) x *
        factorTwoCenteredP6 x) =
      fourCellEvenP0246CutoffEightFixedLagRow6 c0 c2 c4 c6 := by
  rw [integral_fixedLagK_intrinsicEvenP0246_mul_eq_two_correlation
    c0 c2 c4 c6 factorTwoCenteredP6 continuous_factorTwoCenteredP6,
    factorTwoCenteredCorrelationBilinear_intrinsicEvenP0246_p6]
  unfold fourCellEvenP0246CutoffEightFixedLagRow6
  ring

/-- The exact low Legendre projection of the fixed-lag representer. -/
def fourCellEvenP0246CutoffEightFixedLagSelectorPolynomial
    (c0 c2 c4 c6 : ℝ) : ℝ[X] :=
  factorTwoIntrinsicEvenP0246Polynomial
    (fourCellEvenP0246CutoffEightFixedLagRow0 c0 c2 c4 c6 / 2)
    (5 * fourCellEvenP0246CutoffEightFixedLagRow2 c0 c2 c4 c6 / 2)
    (9 * fourCellEvenP0246CutoffEightFixedLagRow4 c0 c2 c4 c6 / 2)
    (13 * fourCellEvenP0246CutoffEightFixedLagRow6 c0 c2 c4 c6 / 2)

theorem centeredPolynomialLift_cutoffEightFixedLagSelector
    (c0 c2 c4 c6 : ℝ) :
    centeredPolynomialLift
        (fourCellEvenP0246CutoffEightFixedLagSelectorPolynomial
          c0 c2 c4 c6) =
      factorTwoIntrinsicEvenP0246Profile
        (fourCellEvenP0246CutoffEightFixedLagRow0 c0 c2 c4 c6 / 2)
        (5 * fourCellEvenP0246CutoffEightFixedLagRow2 c0 c2 c4 c6 / 2)
        (9 * fourCellEvenP0246CutoffEightFixedLagRow4 c0 c2 c4 c6 / 2)
        (13 * fourCellEvenP0246CutoffEightFixedLagRow6 c0 c2 c4 c6 / 2) := by
  unfold fourCellEvenP0246CutoffEightFixedLagSelectorPolynomial
  exact centeredPolynomialLift_intrinsicEvenP0246Polynomial _ _ _ _

def fourCellEvenP0246CutoffEightFixedLagLowProjectionEnergy
    (c0 c2 c4 c6 : ℝ) : ℝ :=
  fourCellEvenP0246CutoffEightFixedLagRow0 c0 c2 c4 c6 ^ 2 / 2 +
    (5 / 2 : ℝ) *
      fourCellEvenP0246CutoffEightFixedLagRow2 c0 c2 c4 c6 ^ 2 +
    (9 / 2 : ℝ) *
      fourCellEvenP0246CutoffEightFixedLagRow4 c0 c2 c4 c6 ^ 2 +
    (13 / 2 : ℝ) *
      fourCellEvenP0246CutoffEightFixedLagRow6 c0 c2 c4 c6 ^ 2

def fourCellEvenP0246CutoffEightProjectedFixedLagRepresenter
    (c0 c2 c4 c6 : ℝ) (x : ℝ) : ℝ :=
  factorTwoFixedLagK (8 / 5)
      (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) x -
    centeredPolynomialLift
      (fourCellEvenP0246CutoffEightFixedLagSelectorPolynomial
        c0 c2 c4 c6) x

private theorem intervalIntegrable_fixedLagK_intrinsicEvenP0246_mul
    (c0 c2 c4 c6 : ℝ) (r : ℝ → ℝ) (hr : Continuous r) :
    IntervalIntegrable
      (fun x : ℝ ↦
        factorTwoFixedLagK (8 / 5)
            (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) x * r x)
      volume (-1) 1 := by
  let p : ℝ → ℝ := factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6
  have hp : Continuous p := by
    simpa only [p] using
      continuous_factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6
  have hright :=
    intervalIntegrable_mul_factorTwoFixedLagRightRepresenter
      (8 / 5) p r hp hr
  have hleft0 :=
    intervalIntegrable_mul_factorTwoFixedLagLeftRepresenter
      (8 / 5) r p hr hp
  have hleft : IntervalIntegrable
      (fun x : ℝ ↦ factorTwoFixedLagLeftRepresenter (8 / 5) p x * r x)
      volume (-1) 1 := by
    apply hleft0.congr
    intro x _hx
    ring
  apply (hright.add hleft).congr
  intro x _hx
  unfold factorTwoFixedLagK
  dsimp only [p]
  ring

theorem integral_cutoffEightFixedLagSelector_sq_eq_lowProjectionEnergy
    (c0 c2 c4 c6 : ℝ) :
    (∫ x : ℝ in -1..1,
      centeredPolynomialLift
          (fourCellEvenP0246CutoffEightFixedLagSelectorPolynomial
            c0 c2 c4 c6) x ^ 2) =
      fourCellEvenP0246CutoffEightFixedLagLowProjectionEnergy
        c0 c2 c4 c6 := by
  rw [centeredPolynomialLift_cutoffEightFixedLagSelector]
  have hmass := factorTwoIntrinsicEnergy_intrinsicEvenP0246
    (fourCellEvenP0246CutoffEightFixedLagRow0 c0 c2 c4 c6 / 2)
    (5 * fourCellEvenP0246CutoffEightFixedLagRow2 c0 c2 c4 c6 / 2)
    (9 * fourCellEvenP0246CutoffEightFixedLagRow4 c0 c2 c4 c6 / 2)
    (13 * fourCellEvenP0246CutoffEightFixedLagRow6 c0 c2 c4 c6 / 2)
  change (∫ x : ℝ in -1..1,
      factorTwoIntrinsicEvenP0246Profile
        (fourCellEvenP0246CutoffEightFixedLagRow0 c0 c2 c4 c6 / 2)
        (5 * fourCellEvenP0246CutoffEightFixedLagRow2 c0 c2 c4 c6 / 2)
        (9 * fourCellEvenP0246CutoffEightFixedLagRow4 c0 c2 c4 c6 / 2)
        (13 * fourCellEvenP0246CutoffEightFixedLagRow6 c0 c2 c4 c6 / 2) x ^ 2) = _
    at hmass
  rw [hmass]
  unfold fourCellEvenP0246CutoffEightFixedLagLowProjectionEnergy
  ring

theorem integral_fixedLagK_mul_cutoffEightSelector_eq_lowProjectionEnergy
    (c0 c2 c4 c6 : ℝ) :
    (∫ x : ℝ in -1..1,
      factorTwoFixedLagK (8 / 5)
          (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) x *
        centeredPolynomialLift
          (fourCellEvenP0246CutoffEightFixedLagSelectorPolynomial
            c0 c2 c4 c6) x) =
      fourCellEvenP0246CutoffEightFixedLagLowProjectionEnergy
        c0 c2 c4 c6 := by
  let K : ℝ → ℝ := factorTwoFixedLagK (8 / 5)
    (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6)
  let b0 : ℝ := fourCellEvenP0246CutoffEightFixedLagRow0 c0 c2 c4 c6
  let b2 : ℝ := fourCellEvenP0246CutoffEightFixedLagRow2 c0 c2 c4 c6
  let b4 : ℝ := fourCellEvenP0246CutoffEightFixedLagRow4 c0 c2 c4 c6
  let b6 : ℝ := fourCellEvenP0246CutoffEightFixedLagRow6 c0 c2 c4 c6
  let d0 : ℝ := b0 / 2
  let d2 : ℝ := 5 * b2 / 2
  let d4 : ℝ := 9 * b4 / 2
  let d6 : ℝ := 13 * b6 / 2
  have h0 : Continuous centeredEvenP0 := by
    unfold centeredEvenP0
    fun_prop
  have h2 : Continuous centeredEvenP2 := by
    unfold centeredEvenP2
    fun_prop
  have h0I : IntervalIntegrable (fun x : ℝ ↦ K x * centeredEvenP0 x)
      volume (-1) 1 := by
    simpa only [K] using
      intervalIntegrable_fixedLagK_intrinsicEvenP0246_mul
        c0 c2 c4 c6 centeredEvenP0 h0
  have h2I : IntervalIntegrable (fun x : ℝ ↦ K x * centeredEvenP2 x)
      volume (-1) 1 := by
    simpa only [K] using
      intervalIntegrable_fixedLagK_intrinsicEvenP0246_mul
        c0 c2 c4 c6 centeredEvenP2 h2
  have h4I : IntervalIntegrable (fun x : ℝ ↦ K x * factorTwoCenteredP4 x)
      volume (-1) 1 := by
    simpa only [K] using
      intervalIntegrable_fixedLagK_intrinsicEvenP0246_mul
        c0 c2 c4 c6 factorTwoCenteredP4 continuous_factorTwoCenteredP4
  have h6I : IntervalIntegrable (fun x : ℝ ↦ K x * factorTwoCenteredP6 x)
      volume (-1) 1 := by
    simpa only [K] using
      intervalIntegrable_fixedLagK_intrinsicEvenP0246_mul
        c0 c2 c4 c6 factorTwoCenteredP6 continuous_factorTwoCenteredP6
  rw [centeredPolynomialLift_cutoffEightFixedLagSelector]
  change (∫ x : ℝ in -1..1,
    K x * factorTwoIntrinsicEvenP0246Profile d0 d2 d4 d6 x) = _
  rw [show (fun x : ℝ ↦
      K x * factorTwoIntrinsicEvenP0246Profile d0 d2 d4 d6 x) =
    fun x ↦ d0 * (K x * centeredEvenP0 x) +
      (d2 * (K x * centeredEvenP2 x) +
        (d4 * (K x * factorTwoCenteredP4 x) +
          d6 * (K x * factorTwoCenteredP6 x))) by
    funext x
    unfold factorTwoIntrinsicEvenP0246Profile
      factorTwoIntrinsicEvenP024Profile factorTwoEvenStructuralLowProfile
      factorTwoIntrinsicSixEvenTail
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring,
    intervalIntegral.integral_add (h0I.const_mul d0)
      ((h2I.const_mul d2).add ((h4I.const_mul d4).add (h6I.const_mul d6))),
    intervalIntegral.integral_add (h2I.const_mul d2)
      ((h4I.const_mul d4).add (h6I.const_mul d6)),
    intervalIntegral.integral_add (h4I.const_mul d4) (h6I.const_mul d6)]
  repeat rw [intervalIntegral.integral_const_mul]
  dsimp only [K]
  rw [integral_fixedLagK_intrinsicEvenP0246_mul_P0,
    integral_fixedLagK_intrinsicEvenP0246_mul_P2,
    integral_fixedLagK_intrinsicEvenP0246_mul_P4,
    integral_fixedLagK_intrinsicEvenP0246_mul_P6]
  dsimp only [d0, d2, d4, d6, b0, b2, b4, b6]
  unfold fourCellEvenP0246CutoffEightFixedLagLowProjectionEnergy
  ring

theorem integral_cutoffEightProjectedFixedLagRepresenter_sq_eq
    (c0 c2 c4 c6 : ℝ) :
    (∫ x : ℝ in -1..1,
      fourCellEvenP0246CutoffEightProjectedFixedLagRepresenter
        c0 c2 c4 c6 x ^ 2) =
      fourCellEvenP0246CutoffEightFixedLagFullGram c0 c2 c4 c6 -
        fourCellEvenP0246CutoffEightFixedLagLowProjectionEnergy
          c0 c2 c4 c6 := by
  let K : ℝ → ℝ := factorTwoFixedLagK (8 / 5)
    (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6)
  let S : ℝ → ℝ := centeredPolynomialLift
    (fourCellEvenP0246CutoffEightFixedLagSelectorPolynomial c0 c2 c4 c6)
  have hScont : Continuous S := by
    dsimp only [S]
    unfold centeredPolynomialLift
    fun_prop
  have hKsqOn : Integrable (fun x : ℝ ↦ ‖K x‖ ^ 2)
      (volume.restrict (Ioc (-1 : ℝ) 1)) :=
    (memLp_fixedLagK_intrinsicEvenP0246 c0 c2 c4 c6).integrable_norm_pow
      (by norm_num)
  have hKsq : IntervalIntegrable (fun x : ℝ ↦ K x ^ 2)
      volume (-1) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
    apply hKsqOn.congr
    filter_upwards with x
    rw [Real.norm_eq_abs, sq_abs]
  have hKS : IntervalIntegrable (fun x : ℝ ↦ K x * S x)
      volume (-1) 1 := by
    simpa only [K, S] using
      intervalIntegrable_fixedLagK_intrinsicEvenP0246_mul c0 c2 c4 c6
        (centeredPolynomialLift
          (fourCellEvenP0246CutoffEightFixedLagSelectorPolynomial
            c0 c2 c4 c6)) hScont
  have hSsq : IntervalIntegrable (fun x : ℝ ↦ S x ^ 2)
      volume (-1) 1 := (hScont.pow 2).intervalIntegrable (-1) 1
  have hpair : (∫ x : ℝ in -1..1, K x * S x) =
      fourCellEvenP0246CutoffEightFixedLagLowProjectionEnergy
        c0 c2 c4 c6 := by
    simpa only [K, S] using
      integral_fixedLagK_mul_cutoffEightSelector_eq_lowProjectionEnergy
        c0 c2 c4 c6
  have hSnorm : (∫ x : ℝ in -1..1, S x ^ 2) =
      fourCellEvenP0246CutoffEightFixedLagLowProjectionEnergy
        c0 c2 c4 c6 := by
    simpa only [S] using
      integral_cutoffEightFixedLagSelector_sq_eq_lowProjectionEnergy
        c0 c2 c4 c6
  have hKnorm : (∫ x : ℝ in -1..1, K x ^ 2) =
      fourCellEvenP0246CutoffEightFixedLagFullGram c0 c2 c4 c6 := by
    simpa only [K] using
      integral_fixedLagK_intrinsicEvenP0246_sq_eq_fullGram c0 c2 c4 c6
  change (∫ x : ℝ in -1..1, (K x - S x) ^ 2) = _
  rw [show (fun x : ℝ ↦ (K x - S x) ^ 2) =
      fun x ↦ K x ^ 2 - 2 * (K x * S x) + S x ^ 2 by
    funext x
    ring,
    intervalIntegral.integral_add (hKsq.sub (hKS.const_mul 2)) hSsq,
    intervalIntegral.integral_sub hKsq (hKS.const_mul 2),
    intervalIntegral.integral_const_mul, hKnorm, hpair, hSnorm]
  ring

/-- Exact rational Gram of the fixed-lag representer after removing its
four low even Legendre coordinates. -/
def fourCellEvenP0246CutoffEightProjectedFixedLagGram
    (c0 c2 c4 c6 : ℝ) : ℝ :=
  (409292364 / 6103515625 : ℝ) * c0 ^ 2 +
    2 * (10364852784 / 152587890625 : ℝ) * c0 * c2 +
    2 * (230583359856 / 3814697265625 : ℝ) * c0 * c4 +
    2 * (3096631893936 / 95367431640625 : ℝ) * c0 * c6 +
    (269782035804 / 3814697265625 : ℝ) * c2 ^ 2 +
    2 * (6330010863536 / 95367431640625 : ℝ) * c2 * c4 +
    2 * (94043534060016 / 2384185791015625 : ℝ) * c2 * c6 +
    (495807790725572 / 7152557373046875 : ℝ) * c4 ^ 2 +
    2 * (3027599173655344 / 59604644775390625 : ℝ) * c4 * c6 +
    (1039233584463721932 / 19371509552001953125 : ℝ) * c6 ^ 2

set_option maxHeartbeats 800000 in
theorem fixedLagFullGram_sub_lowProjectionEnergy_eq_projectedGram
    (c0 c2 c4 c6 : ℝ) :
    fourCellEvenP0246CutoffEightFixedLagFullGram c0 c2 c4 c6 -
        fourCellEvenP0246CutoffEightFixedLagLowProjectionEnergy
          c0 c2 c4 c6 =
      fourCellEvenP0246CutoffEightProjectedFixedLagGram c0 c2 c4 c6 := by
  unfold fourCellEvenP0246CutoffEightFixedLagFullGram
    fourCellEvenP0246CutoffEightFixedLagLowProjectionEnergy
    fourCellEvenP0246CutoffEightFixedLagRow0
    fourCellEvenP0246CutoffEightFixedLagRow2
    fourCellEvenP0246CutoffEightFixedLagRow4
    fourCellEvenP0246CutoffEightFixedLagRow6
    fourCellEvenP0246CutoffEightProjectedFixedLagGram
  ring

theorem integral_cutoffEightProjectedFixedLagRepresenter_sq_eq_projectedGram
    (c0 c2 c4 c6 : ℝ) :
    (∫ x : ℝ in -1..1,
      fourCellEvenP0246CutoffEightProjectedFixedLagRepresenter
        c0 c2 c4 c6 x ^ 2) =
      fourCellEvenP0246CutoffEightProjectedFixedLagGram c0 c2 c4 c6 := by
  rw [integral_cutoffEightProjectedFixedLagRepresenter_sq_eq,
    fixedLagFullGram_sub_lowProjectionEnergy_eq_projectedGram]

/-! ## Exact endpoint-potential tail series

The all-degree endpoint-potential formula turns the cutoff-eight tail Gram
into rational stride-two series (off diagonal) and shifted reciprocal-square
series (diagonal).  The first lemma is the structural telescope used by all
six off-diagonal entries. -/

private theorem hasSum_strideTwo_reciprocalDifference
    (a : ℝ) (ha : 0 < a) :
    HasSum (fun r : ℕ ↦
      1 / (2 * (r : ℝ) + a) -
        1 / (2 * (r : ℝ) + a + 2)) (1 / a) := by
  have hnonneg : ∀ r : ℕ,
      0 ≤ 1 / (2 * (r : ℝ) + a) -
        1 / (2 * (r : ℝ) + a + 2) := by
    intro r
    apply sub_nonneg.mpr
    apply one_div_le_one_div_of_le
    · positivity
    · linarith
  apply (hasSum_iff_tendsto_nat_of_nonneg hnonneg (1 / a)).2
  have hsum (n : ℕ) :
      (∑ r ∈ Finset.range n,
        (1 / (2 * (r : ℝ) + a) -
          1 / (2 * (r : ℝ) + a + 2))) =
        1 / a - 1 / (2 * (n : ℝ) + a) := by
    induction n with
    | zero => norm_num
    | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        push_cast
        ring
  simp_rw [hsum]
  have hmul : Tendsto (fun n : ℕ ↦ 2 * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop
      (by norm_num : (0 : ℝ) < 2)
  have hden : Tendsto (fun n : ℕ ↦ 2 * (n : ℝ) + a) atTop atTop :=
    hmul.atTop_add tendsto_const_nhds
  have hinv : Tendsto (fun n : ℕ ↦
      1 / (2 * (n : ℝ) + a)) atTop (nhds 0) := by
    simpa only [one_div] using tendsto_inv_atTop_zero.comp hden
  simpa using
    ((tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ 1 / a)
      atTop (nhds (1 / a))).sub hinv)

/-- Centered Parseval summand of the endpoint-potential tails sourced in
Legendre degrees `m` and `k`, with target degree `2r+8`. -/
def cutoffEightPotentialTailSummand (m k r : ℕ) : ℝ :=
  let n : ℝ := 2 * (r : ℝ) + 8
  2 * (2 * n + 1) /
    ((n - (m : ℝ)) * (n + (m : ℝ) + 1) *
      (n - (k : ℝ)) * (n + (k : ℝ) + 1))

theorem hasSum_cutoffEightPotentialTail_P0_P2 :
    HasSum (cutoffEightPotentialTailSummand 0 2) (1 / 54 : ℝ) := by
  have h6 := hasSum_strideTwo_reciprocalDifference 6 (by norm_num)
  have h9 := hasSum_strideTwo_reciprocalDifference 9 (by norm_num)
  have h := HasSum.mul_left (1 / 3 : ℝ) (h6.sub h9)
  convert h using 1
  · funext r
    have hr : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
    have h6' : 2 * (r : ℝ) + 6 ≠ 0 := by linarith
    have h8' : 2 * (r : ℝ) + 8 ≠ 0 := by linarith
    have h9' : 2 * (r : ℝ) + 9 ≠ 0 := by linarith
    have h11' : 2 * (r : ℝ) + 11 ≠ 0 := by linarith
    have hm2 : 2 * (r : ℝ) + 8 - 2 ≠ 0 := by linarith
    have hp1 : 2 * (r : ℝ) + 8 + 1 ≠ 0 := by linarith
    have hp3 : 2 * (r : ℝ) + 8 + 3 ≠ 0 := by linarith
    dsimp [cutoffEightPotentialTailSummand]
    (field_simp [h6', h8', h9', h11', hm2, hp1, hp3] ; ring_nf)
  · norm_num

theorem hasSum_cutoffEightPotentialTail_P0_P4 :
    HasSum (cutoffEightPotentialTailSummand 0 4) (17 / 792 : ℝ) := by
  have h4 := hasSum_strideTwo_reciprocalDifference 4 (by norm_num)
  have h6 := hasSum_strideTwo_reciprocalDifference 6 (by norm_num)
  have h9 := hasSum_strideTwo_reciprocalDifference 9 (by norm_num)
  have h11 := hasSum_strideTwo_reciprocalDifference 11 (by norm_num)
  have h := HasSum.mul_left (1 / 10 : ℝ)
    ((h4.add h6).sub (h9.add h11))
  convert h using 1
  · funext r
    have hr : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
    have h4' : 2 * (r : ℝ) + 4 ≠ 0 := by linarith
    have h6' : 2 * (r : ℝ) + 6 ≠ 0 := by linarith
    have h8' : 2 * (r : ℝ) + 8 ≠ 0 := by linarith
    have h9' : 2 * (r : ℝ) + 9 ≠ 0 := by linarith
    have h11' : 2 * (r : ℝ) + 11 ≠ 0 := by linarith
    have h13' : 2 * (r : ℝ) + 13 ≠ 0 := by linarith
    have hm4 : 2 * (r : ℝ) + 8 - 4 ≠ 0 := by linarith
    have hp1 : 2 * (r : ℝ) + 8 + 1 ≠ 0 := by linarith
    have hp5 : 2 * (r : ℝ) + 8 + 5 ≠ 0 := by linarith
    dsimp [cutoffEightPotentialTailSummand]
    (field_simp [h4', h6', h8', h9', h11', h13', hm4, hp1, hp5] ;
      ring_nf)
  · norm_num

theorem hasSum_cutoffEightPotentialTail_P0_P6 :
    HasSum (cutoffEightPotentialTailSummand 0 6) (469 / 15444 : ℝ) := by
  have h2 := hasSum_strideTwo_reciprocalDifference 2 (by norm_num)
  have h4 := hasSum_strideTwo_reciprocalDifference 4 (by norm_num)
  have h6 := hasSum_strideTwo_reciprocalDifference 6 (by norm_num)
  have h9 := hasSum_strideTwo_reciprocalDifference 9 (by norm_num)
  have h11 := hasSum_strideTwo_reciprocalDifference 11 (by norm_num)
  have h13 := hasSum_strideTwo_reciprocalDifference 13 (by norm_num)
  have h := HasSum.mul_left (1 / 21 : ℝ)
    (((h2.add h4).add h6).sub ((h9.add h11).add h13))
  convert h using 1
  · funext r
    have hr : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
    have h2' : 2 * (r : ℝ) + 2 ≠ 0 := by linarith
    have h4' : 2 * (r : ℝ) + 4 ≠ 0 := by linarith
    have h6' : 2 * (r : ℝ) + 6 ≠ 0 := by linarith
    have h8' : 2 * (r : ℝ) + 8 ≠ 0 := by linarith
    have h9' : 2 * (r : ℝ) + 9 ≠ 0 := by linarith
    have h11' : 2 * (r : ℝ) + 11 ≠ 0 := by linarith
    have h13' : 2 * (r : ℝ) + 13 ≠ 0 := by linarith
    have h15' : 2 * (r : ℝ) + 15 ≠ 0 := by linarith
    have hm6 : 2 * (r : ℝ) + 8 - 6 ≠ 0 := by linarith
    have hp1 : 2 * (r : ℝ) + 8 + 1 ≠ 0 := by linarith
    have hp7 : 2 * (r : ℝ) + 8 + 7 ≠ 0 := by linarith
    dsimp [cutoffEightPotentialTailSummand]
    (field_simp [h2', h4', h6', h8', h9', h11', h13', h15',
        hm6, hp1, hp7] ; ring_nf)
  · norm_num

theorem hasSum_cutoffEightPotentialTail_P2_P4 :
    HasSum (cutoffEightPotentialTailSummand 2 4) (1 / 44 : ℝ) := by
  have h4 := hasSum_strideTwo_reciprocalDifference 4 (by norm_num)
  have h11 := hasSum_strideTwo_reciprocalDifference 11 (by norm_num)
  have h := HasSum.mul_left (1 / 7 : ℝ) (h4.sub h11)
  convert h using 1
  · funext r
    have hr : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
    have h4' : 2 * (r : ℝ) + 4 ≠ 0 := by linarith
    have h6' : 2 * (r : ℝ) + 6 ≠ 0 := by linarith
    have h11' : 2 * (r : ℝ) + 11 ≠ 0 := by linarith
    have h13' : 2 * (r : ℝ) + 13 ≠ 0 := by linarith
    have hm2 : 2 * (r : ℝ) + 8 - 2 ≠ 0 := by linarith
    have hm4 : 2 * (r : ℝ) + 8 - 4 ≠ 0 := by linarith
    have hp3 : 2 * (r : ℝ) + 8 + 3 ≠ 0 := by linarith
    have hp5 : 2 * (r : ℝ) + 8 + 5 ≠ 0 := by linarith
    dsimp [cutoffEightPotentialTailSummand]
    (field_simp [h4', h6', h11', h13', hm2, hm4, hp3, hp5] ;
      ring_nf)
  · norm_num

theorem hasSum_cutoffEightPotentialTail_P2_P6 :
    HasSum (cutoffEightPotentialTailSummand 2 6) (37 / 1144 : ℝ) := by
  have h2 := hasSum_strideTwo_reciprocalDifference 2 (by norm_num)
  have h4 := hasSum_strideTwo_reciprocalDifference 4 (by norm_num)
  have h11 := hasSum_strideTwo_reciprocalDifference 11 (by norm_num)
  have h13 := hasSum_strideTwo_reciprocalDifference 13 (by norm_num)
  have h := HasSum.mul_left (1 / 18 : ℝ)
    ((h2.add h4).sub (h11.add h13))
  convert h using 1
  · funext r
    have hr : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
    have h2' : 2 * (r : ℝ) + 2 ≠ 0 := by linarith
    have h4' : 2 * (r : ℝ) + 4 ≠ 0 := by linarith
    have h6' : 2 * (r : ℝ) + 6 ≠ 0 := by linarith
    have h11' : 2 * (r : ℝ) + 11 ≠ 0 := by linarith
    have h13' : 2 * (r : ℝ) + 13 ≠ 0 := by linarith
    have h15' : 2 * (r : ℝ) + 15 ≠ 0 := by linarith
    have hm2 : 2 * (r : ℝ) + 8 - 2 ≠ 0 := by linarith
    have hm6 : 2 * (r : ℝ) + 8 - 6 ≠ 0 := by linarith
    have hp3 : 2 * (r : ℝ) + 8 + 3 ≠ 0 := by linarith
    have hp7 : 2 * (r : ℝ) + 8 + 7 ≠ 0 := by linarith
    dsimp [cutoffEightPotentialTailSummand]
    (field_simp [h2', h4', h6', h11', h13', h15', hm2, hm6,
        hp3, hp7] ; ring_nf)
  · norm_num

theorem hasSum_cutoffEightPotentialTail_P4_P6 :
    HasSum (cutoffEightPotentialTailSummand 4 6) (1 / 26 : ℝ) := by
  have h2 := hasSum_strideTwo_reciprocalDifference 2 (by norm_num)
  have h13 := hasSum_strideTwo_reciprocalDifference 13 (by norm_num)
  have h := HasSum.mul_left (1 / 11 : ℝ) (h2.sub h13)
  convert h using 1
  · funext r
    have hr : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
    have h2' : 2 * (r : ℝ) + 2 ≠ 0 := by linarith
    have h4' : 2 * (r : ℝ) + 4 ≠ 0 := by linarith
    have h13' : 2 * (r : ℝ) + 13 ≠ 0 := by linarith
    have h15' : 2 * (r : ℝ) + 15 ≠ 0 := by linarith
    have hm4 : 2 * (r : ℝ) + 8 - 4 ≠ 0 := by linarith
    have hm6 : 2 * (r : ℝ) + 8 - 6 ≠ 0 := by linarith
    have hp5 : 2 * (r : ℝ) + 8 + 5 ≠ 0 := by linarith
    have hp7 : 2 * (r : ℝ) + 8 + 7 ≠ 0 := by linarith
    dsimp [cutoffEightPotentialTailSummand]
    (field_simp [h2', h4', h13', h15', hm4, hm6, hp5, hp7] ;
      ring_nf)
  · norm_num

theorem fourCellEvenEndpointCapacityPolarization_P0246_eq_projectedRepresenterPairing
    (c0 c2 c4 c6 : ℝ) (r : ℝ → ℝ) (hr : Continuous r)
    (hlow : centeredLegendreMomentsVanishBelow r 8)
    (q : ℝ[X]) (hq : q.natDegree < 8) :
    fourCellEvenEndpointCapacityPolarization
        (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) r =
      ∫ x : ℝ in -1..1,
        fourCellEvenP0246CutoffEightProjectedCapacityRepresenter
          c0 c2 c4 c6 q x * r x := by
  have hbase :=
    intervalIntegrable_fourCellEvenP0246CutoffEightCapacityRepresenter_mul
      c0 c2 c4 c6 r hr
  have hpoly : IntervalIntegrable
      (fun x : ℝ ↦ centeredPolynomialLift q x * r x) volume (-1) 1 :=
    ((by
      unfold centeredPolynomialLift
      fun_prop : Continuous (centeredPolynomialLift q)).mul hr).intervalIntegrable
        (-1) 1
  have hzero := intervalIntegral_centeredPolynomialLift_mul_tail_eq_zero
    q r hr hlow hq
  rw [fourCellEvenEndpointCapacityPolarization_P0246_eq_representerPairing
    c0 c2 c4 c6 r hr]
  unfold fourCellEvenP0246CutoffEightProjectedCapacityRepresenter
  rw [show (fun x : ℝ ↦
      (fourCellEvenP0246CutoffEightCapacityRepresenter c0 c2 c4 c6 x -
          centeredPolynomialLift q x) * r x) =
      fun x ↦
        fourCellEvenP0246CutoffEightCapacityRepresenter c0 c2 c4 c6 x * r x -
          centeredPolynomialLift q x * r x by
    funext x
    ring,
    intervalIntegral.integral_sub hbase hpoly, hzero, sub_zero]

/-- The last capacity determinant follows from one projected-representer
`L²` norm bound.  The selector polynomial is arbitrary below degree eight,
so it may be chosen as the exact low Legendre projection of the representer. -/
theorem cutoffEight_capacitySchur_of_projectedCapacityRepresenterL2
    (c0 c2 c4 c6 : ℝ) (r : ℝ → ℝ) (hr : Continuous r)
    (hlow : centeredLegendreMomentsVanishBelow r 8)
    (q : ℝ[X]) (hq : q.natDegree < 8)
    (hG : MemLp
      (fourCellEvenP0246CutoffEightProjectedCapacityRepresenter
        c0 c2 c4 c6 q) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)))
    (hdual :
      (∫ x : ℝ in -1..1,
        fourCellEvenP0246CutoffEightProjectedCapacityRepresenter
          c0 c2 c4 c6 q x ^ 2) ≤
        (7461 / 7000 : ℝ) *
          fourCellEvenP0246CutoffEightLowSchurReserve c0 c2 c4 c6) :
    fourCellEvenEndpointCapacityPolarization
          (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) r ^ 2 ≤
      fourCellEvenP0246CutoffEightLowSchurReserve c0 c2 c4 c6 *
        ((7461 / 7000 : ℝ) *
          (∫ x : ℝ in -1..1, r x ^ 2)) := by
  apply cutoffEight_capacitySchur_of_projectedRepresenterL2
    c0 c2 c4 c6 r
      (fourCellEvenP0246CutoffEightProjectedCapacityRepresenter
        c0 c2 c4 c6 q) hr hG
  · exact
      fourCellEvenEndpointCapacityPolarization_P0246_eq_projectedRepresenterPairing
        c0 c2 c4 c6 r hr hlow q hq
  · exact hdual

/-- Assumption-minimal projected-representer handoff: after the selector has
degree below eight, only its quantitative squared-norm estimate remains. -/
theorem cutoffEight_capacitySchur_of_projectedCapacityRepresenterNorm
    (c0 c2 c4 c6 : ℝ) (r : ℝ → ℝ) (hr : Continuous r)
    (hlow : centeredLegendreMomentsVanishBelow r 8)
    (q : ℝ[X]) (hq : q.natDegree < 8)
    (hdual :
      (∫ x : ℝ in -1..1,
        fourCellEvenP0246CutoffEightProjectedCapacityRepresenter
          c0 c2 c4 c6 q x ^ 2) ≤
        (7461 / 7000 : ℝ) *
          fourCellEvenP0246CutoffEightLowSchurReserve c0 c2 c4 c6) :
    fourCellEvenEndpointCapacityPolarization
          (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) r ^ 2 ≤
      fourCellEvenP0246CutoffEightLowSchurReserve c0 c2 c4 c6 *
        ((7461 / 7000 : ℝ) *
          (∫ x : ℝ in -1..1, r x ^ 2)) := by
  exact cutoffEight_capacitySchur_of_projectedCapacityRepresenterL2
    c0 c2 c4 c6 r hr hlow q hq
      (memLp_fourCellEvenP0246CutoffEightProjectedCapacityRepresenter
        c0 c2 c4 c6 q) hdual

/-- Exact scalar Schur reduction of the last cutoff-eight capacity border.
The tail factor `7461 / 7000 = 299 / 280 - 1 / 500` is what remains after
reserving one five-hundredth of total nonconstant mass for the constant
coordinate.  Thus the displayed determinant inequality is the sole analytic
low-to-tail input: no sign or finite-mode exhaustion is assumed. -/
theorem thirtyThree_div_twenty_mass_le_coupledCore_P0246_add_tail_of_capacitySchur
    (c0 c2 c4 c6 : ℝ) (r : ℝ → ℝ) (hr : Continuous r)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) r)
    (heven : Function.Even r)
    (hlow : centeredLegendreMomentsVanishBelow r 8)
    (hconstant : c0 ^ 2 ≤ (1 / 4000 : ℝ) *
      (2 * c0 ^ 2 + (2 / 5 : ℝ) * c2 ^ 2 +
        (2 / 9 : ℝ) * c4 ^ 2 + (2 / 13 : ℝ) * c6 ^ 2 +
        (∫ x : ℝ in -1..1, r x ^ 2)))
    (hcapacitySchur :
      fourCellEvenEndpointCapacityPolarization
          (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) r ^ 2 ≤
        fourCellEvenP0246CutoffEightLowSchurReserve c0 c2 c4 c6 *
          ((7461 / 7000 : ℝ) *
            (∫ x : ℝ in -1..1, r x ^ 2))) :
    (33 / 20 : ℝ) *
        (∫ x : ℝ in -1..1,
          (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6 x + r x) ^ 2) ≤
      fourCellEvenZeroCoshCoupledCore
        (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6 + r) := by
  let N : ℝ := (2 / 5 : ℝ) * c2 ^ 2 + (2 / 9 : ℝ) * c4 ^ 2 +
    (2 / 13 : ℝ) * c6 ^ 2
  let R : ℝ := ∫ x : ℝ in -1..1, r x ^ 2
  let L : ℝ := fourCellEvenP0246CutoffEightLowSchurReserve c0 c2 c4 c6
  let C : ℝ := fourCellEvenEndpointCapacityPolarization
    (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) r
  let T : ℝ := (7461 / 7000 : ℝ) * R
  have hR : 0 ≤ R := by
    dsimp only [R]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun _ _ ↦ sq_nonneg _)
  have hN : 0 ≤ N := by
    dsimp only [N]
    positivity
  have hL : 0 ≤ L := by
    simpa only [L] using
      fourCellEvenP0246CutoffEightLowSchurReserve_nonnegative
        c0 c2 c4 c6
  have hT : 0 ≤ T := by
    dsimp only [T]
    positivity
  have hconstant' : 3998 * c0 ^ 2 ≤ N + R := by
    dsimp only [N, R]
    nlinarith only [hconstant]
  have hdefect : 5 * c0 ^ 2 ≤ (1 / 500 : ℝ) * (N + R) := by
    nlinarith only [hconstant']
  have hschur : 0 ≤ L + 2 * C + T := by
    apply scalar_low_tail_nonneg L T C hL hT
    simpa only [L, T, C, R] using hcapacitySchur
  have htail :=
    sevenHundredSixtyOne_div_twoHundredEighty_mass_le_coupledCore_of_even_legendreTail
      r hr hlocal heven hlow
  have hmass := integral_intrinsicEvenP0246_add_tail_sq
    c0 c2 c4 c6 r hr hlow
  have hcore := fourCellEvenZeroCoshCoupledCore_intrinsicEvenP0246_add_tail
    c0 c2 c4 c6 r hr hlocal hlow
  rw [hmass, hcore]
  dsimp only [L, T, C, N, R] at hschur htail hdefect ⊢
  unfold fourCellEvenP0246CutoffEightLowSchurReserve at hschur
  nlinarith only [hschur, htail, hdefect]

private theorem integral_polynomial_ten
    (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ l r : ℝ) :
    (∫ x : ℝ in l..r,
      a₀ * x ^ 0 + a₁ * x ^ 1 + a₂ * x ^ 2 + a₃ * x ^ 3 + a₄ * x ^ 4 +
        a₅ * x ^ 5 + a₆ * x ^ 6 + a₇ * x ^ 7 + a₈ * x ^ 8 +
          a₉ * x ^ 9 + a₁₀ * x ^ 10) =
      a₀ * (r - l) + a₁ * (r ^ 2 - l ^ 2) / 2 +
        a₂ * (r ^ 3 - l ^ 3) / 3 + a₃ * (r ^ 4 - l ^ 4) / 4 +
          a₄ * (r ^ 5 - l ^ 5) / 5 + a₅ * (r ^ 6 - l ^ 6) / 6 +
            a₆ * (r ^ 7 - l ^ 7) / 7 + a₇ * (r ^ 8 - l ^ 8) / 8 +
              a₈ * (r ^ 9 - l ^ 9) / 9 + a₉ * (r ^ 10 - l ^ 10) / 10 +
                a₁₀ * (r ^ 11 - l ^ 11) / 11 := by
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) l r)
    (Continuous.intervalIntegrable (by fun_prop) l r)]
  repeat rw [intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  ring

/-- Exact retained dyadic translation on the genuine even `P₀/P₂/P₄`
profile.  In particular, the prime row is not replaced by an independent
operator-norm estimate. -/
theorem fourCellEndpointPairing_intrinsicEvenP024Profile
    (c0 c2 c4 : ℝ) :
    fourCellEndpointPairing
        (factorTwoIntrinsicEvenP024Profile c0 c2 c4) =
      (2 / 5 : ℝ) * c0 ^ 2 + (48 / 125 : ℝ) * c0 * c2 -
        (144 / 3125 : ℝ) * c0 * c4 +
        (962 / 15625 : ℝ) * c2 ^ 2 -
        (8144 / 78125 : ℝ) * c2 * c4 -
        (164582 / 3515625 : ℝ) * c4 ^ 2 := by
  unfold fourCellEndpointPairing factorTwoIntrinsicEvenP024Profile
    factorTwoEvenStructuralLowProfile factorTwoIntrinsicSixEvenTail
    centeredEvenP0 centeredEvenP2 factorTwoCenteredP4
  simp only [Pi.add_apply]
  rw [show (fun x : ℝ ↦
      (c0 * 1 + c2 * ((3 * x ^ 2 - 1) / 2) +
          c4 * ((35 * x ^ 4 - 30 * x ^ 2 + 3) / 8)) *
        (c0 * 1 + c2 * ((3 * (x - 8 / 5) ^ 2 - 1) / 2) +
          c4 * ((35 * (x - 8 / 5) ^ 4 -
            30 * (x - 8 / 5) ^ 2 + 3) / 8))) =
      (fun x ↦
        ((58341 / 8000 : ℝ) * c4 ^ 2 - (8471 / 1000 : ℝ) * c2 * c4 -
            (167 / 100 : ℝ) * c2 ^ 2 + (9911 / 500 : ℝ) * c0 * c4 +
            (71 / 25 : ℝ) * c0 * c2 + c0 ^ 2) * x ^ 0 +
        (-(1119 / 50 : ℝ) * c4 ^ 2 + (701 / 25 : ℝ) * c2 * c4 +
            (12 / 5 : ℝ) * c2 ^ 2 - (1492 / 25 : ℝ) * c0 * c4 -
            (24 / 5 : ℝ) * c0 * c2) * x ^ 1 +
        (-(19653 / 400 : ℝ) * c4 ^ 2 - (14517 / 1000 : ℝ) * c2 * c4 +
            (213 / 50 : ℝ) * c2 ^ 2 + (597 / 10 : ℝ) * c0 * c4 +
            3 * c0 * c2) * x ^ 2 +
        ((2133 / 10 : ℝ) * c4 ^ 2 - (1438 / 25 : ℝ) * c2 * c4 -
            (36 / 5 : ℝ) * c2 ^ 2 - 28 * c0 * c4) * x ^ 3 +
        (-(120973 / 800 : ℝ) * c4 ^ 2 + (4079 / 40 : ℝ) * c2 * c4 +
            (9 / 4 : ℝ) * c2 ^ 2 + (35 / 4 : ℝ) * c0 * c4) * x ^ 4 +
        (-(1561 / 10 : ℝ) * c4 ^ 2 - 63 * c2 * c4) * x ^ 5 +
        ((4179 / 16 : ℝ) * c4 ^ 2 + (105 / 8 : ℝ) * c2 * c4) * x ^ 6 +
        (-(245 / 2 : ℝ) * c4 ^ 2) * x ^ 7 +
        (1225 / 64 : ℝ) * c4 ^ 2 * x ^ 8 + 0 * x ^ 9 + 0 * x ^ 10) by
      funext x
      ring,
    integral_polynomial_ten]
  norm_num
  ring

/-- The exact raw-plus-potential Gram on the low even profile.  This is
deduced from the retained singular square, so the logarithmic potential and
raw kernel remain one structural identity. -/
theorem raw_div_four_add_potential_add_logMass_intrinsicEvenP024Profile
    (c0 c2 c4 : ℝ) :
    centeredRawLogEnergy
          (factorTwoIntrinsicEvenP024Profile c0 c2 c4) / 4 +
        (∫ x : ℝ in -1..1, yoshidaEndpointPotential x *
          factorTwoIntrinsicEvenP024Profile c0 c2 c4 x ^ 2) +
        Real.log 2 *
          (∫ x : ℝ in -1..1,
            factorTwoIntrinsicEvenP024Profile c0 c2 c4 x ^ 2) =
      symmetricQuadratic
        2 (1 / 3) (1 / 10) (86 / 75) (1 / 7) (2182 / 2835)
        c0 c2 c4 := by
  let w : ℝ → ℝ := factorTwoIntrinsicEvenP024Profile c0 c2 c4
  have hw : Continuous w := by
    simpa only [w] using
      factorTwoIntrinsicEvenP024Profile_continuous c0 c2 c4
  have hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w := by
    simpa only [w] using
      factorTwoIntrinsicEvenP024Profile_locallyLipschitzOn c0 c2 c4
  have hs := half_singularWeightedEnergy_eq_protected_add_logMass
    w (0 : ℝ → ℝ) hw continuous_zero hlocal
      (by
        have hd : ContDiff ℝ 1 (fun _ : ℝ ↦ (0 : ℝ)) := contDiff_const
        change LocallyLipschitzOn (Icc (-1 : ℝ) 1) (fun _ : ℝ ↦ (0 : ℝ))
        exact hd.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1))
      0 0
  have hzero :=
    half_singularWeightedEnergy_intrinsicEvenP024_zero c0 c2 c4
  have h0raw : centeredRawLogEnergy (0 : ℝ → ℝ) = 0 := by
    unfold centeredRawLogEnergy
    simp
  change (1 / 2 : ℝ) *
      factorTwoPhaseSingularWeightedEnergy w (0 : ℝ → ℝ) 0 0 = _
    at hzero
  unfold factorTwoIntrinsicProtectedBlock factorTwoIntrinsicEnergy
    factorTwoIntrinsicPotentialEnergy at hs
  simp [factorTwoCenteredPhaseCorrelation,
    factorTwoCenteredCrossCorrelation] at hs
  rw [h0raw] at hs
  norm_num at hs hzero
  simpa only [w] using hs.symm.trans hzero

/-- Exact coupled-core quadratic on the low even profile.  The last line is
the exact dyadic prime Gram, not a separately estimated prime loss. -/
theorem fourCellEvenZeroCoshCoupledCore_intrinsicEvenP024Profile_eq_quadratic
    (c0 c2 c4 : ℝ) :
    fourCellEvenZeroCoshCoupledCore
        (factorTwoIntrinsicEvenP024Profile c0 c2 c4) =
      symmetricQuadratic
          2 (1 / 3) (1 / 10) (86 / 75) (1 / 7) (2182 / 2835)
          c0 c2 c4 -
        Real.log 2 *
          (2 * c0 ^ 2 + (2 / 5 : ℝ) * c2 ^ 2 +
            (2 / 9 : ℝ) * c4 ^ 2) -
        Real.sqrt 2 * Real.log 2 *
          ((2 / 5 : ℝ) * c0 ^ 2 + (48 / 125 : ℝ) * c0 * c2 -
            (144 / 3125 : ℝ) * c0 * c4 +
            (962 / 15625 : ℝ) * c2 ^ 2 -
            (8144 / 78125 : ℝ) * c2 * c4 -
            (164582 / 3515625 : ℝ) * c4 ^ 2) := by
  have henergy :=
    raw_div_four_add_potential_add_logMass_intrinsicEvenP024Profile
      c0 c2 c4
  have hmass := integral_factorTwoIntrinsicEvenP024Profile_sq c0 c2 c4
  have hpair :=
    fourCellEndpointPairing_intrinsicEvenP024Profile c0 c2 c4
  unfold fourCellEvenZeroCoshCoupledCore
  rw [hmass] at henergy
  rw [hpair]
  linarith

set_option maxHeartbeats 600000 in
/-- Quantitative low-block reserve before imposing the zero-cosh cone.  The
nonconstant `P₂/P₄` mass survives with coefficient `3 / 100`; the only
defect is the displayed constant-coordinate charge.  This is the form that
can be absorbed jointly with the infinite tail. -/
theorem three_div_hundred_nonconstantReserve_le_coupledCore_add_constantDefect
    (c0 c2 c4 : ℝ) :
    (33 / 20 : ℝ) *
        (∫ x : ℝ in -1..1,
          factorTwoIntrinsicEvenP024Profile c0 c2 c4 x ^ 2) +
        (3 / 100 : ℝ) *
          ((2 / 5 : ℝ) * c2 ^ 2 + (2 / 9 : ℝ) * c4 ^ 2) ≤
      fourCellEvenZeroCoshCoupledCore
        (factorTwoIntrinsicEvenP024Profile c0 c2 c4) +
          (451 / 10 : ℝ) * c0 ^ 2 := by
  let beta : ℝ := Real.sqrt 2 * Real.log 2
  let N : ℝ := (2 / 5 : ℝ) * c2 ^ 2 + (2 / 9 : ℝ) * c4 ^ 2
  let A00 : ℝ :=
    2 - 2 * Real.log 2 - (2 / 5 : ℝ) * beta - 33 / 10
  let A22 : ℝ :=
    86 / 75 - (2 / 5 : ℝ) * Real.log 2 -
      (962 / 15625 : ℝ) * beta - 33 / 50
  let A44 : ℝ :=
    2182 / 2835 - (2 / 9 : ℝ) * Real.log 2 +
      (164582 / 3515625 : ℝ) * beta - 11 / 30
  let C02 : ℝ := 2 / 3 - (48 / 125 : ℝ) * beta
  let C04 : ℝ := 1 / 5 + (144 / 3125 : ℝ) * beta
  let C24 : ℝ := 2 / 7 + (8144 / 78125 : ℝ) * beta
  have hlogLower := strict_log_two_bounds.1
  have hlogUpper := strict_log_two_bounds.2
  have hsqrtLower := sqrt_two_kernel_bounds.1
  have hsqrtUpper := sqrt_two_kernel_bounds.2
  have hlogPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hbeta0 : 0 ≤ beta := by
    dsimp only [beta]
    positivity
  have hbeta : beta ≤ (981 / 1000 : ℝ) := by
    dsimp only [beta]
    have hsqrtPos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    have hfirst : Real.sqrt 2 * Real.log 2 <
        (70711 / 50000 : ℝ) * Real.log 2 :=
      mul_lt_mul_of_pos_right hsqrtUpper hlogPos
    have hsecond : (70711 / 50000 : ℝ) * Real.log 2 <
        (70711 / 50000 : ℝ) * (6932 / 10000 : ℝ) :=
      mul_lt_mul_of_pos_left hlogUpper (by norm_num)
    norm_num at hfirst hsecond ⊢
    linarith
  have hbetaLower : (49 / 50 : ℝ) ≤ beta := by
    dsimp only [beta]
    have hproduct :
        (141421 / 100000 : ℝ) * (6931 / 10000 : ℝ) <
          Real.sqrt 2 * Real.log 2 := by
      calc
        (141421 / 100000 : ℝ) * (6931 / 10000 : ℝ) <
            Real.sqrt 2 * (6931 / 10000 : ℝ) :=
          mul_lt_mul_of_pos_right hsqrtLower (by norm_num)
        _ < Real.sqrt 2 * Real.log 2 :=
          mul_lt_mul_of_pos_left hlogLower
            (Real.sqrt_pos.2 (by norm_num))
    norm_num at hproduct ⊢
    linarith
  have hA00 : (-31 / 10 : ℝ) ≤ A00 := by
    dsimp only [A00]
    nlinarith
  have hA22 : (1489 / 10000 : ℝ) ≤ A22 := by
    dsimp only [A22]
    nlinarith
  have hA44 : (2948 / 10000 : ℝ) ≤ A44 := by
    dsimp only [A44]
    nlinarith only [hlogUpper, hbetaLower]
  have hC02 : 0 ≤ C02 := by
    dsimp only [C02]
    nlinarith
  have hC02Upper : C02 ≤ (2 / 3 : ℝ) := by
    dsimp only [C02]
    nlinarith
  have hC04 : 0 ≤ C04 := by
    dsimp only [C04]
    nlinarith
  have hC04Upper : C04 ≤ (1 / 4 : ℝ) := by
    dsimp only [C04]
    nlinarith
  have hC24 : 0 ≤ C24 := by
    dsimp only [C24]
    nlinarith
  have hC24Upper : C24 ≤ (19399 / 50000 : ℝ) := by
    dsimp only [C24]
    nlinarith
  have hcross02 :
      -(28 * c0 ^ 2 + (1 / 250 : ℝ) * c2 ^ 2) ≤
        C02 * c0 * c2 := by
    by_cases hp : 0 ≤ c0 * c2
    · have hnonneg : 0 ≤ C02 * (c0 * c2) :=
        mul_nonneg hC02 hp
      calc
        -(28 * c0 ^ 2 + (1 / 250 : ℝ) * c2 ^ 2) ≤ 0 := by
          nlinarith only [sq_nonneg c0, sq_nonneg c2]
        _ ≤ C02 * c0 * c2 := by simpa only [mul_assoc] using hnonneg
    · have hp' : c0 * c2 < 0 := lt_of_not_ge hp
      have hcompare : (2 / 3 : ℝ) * (c0 * c2) ≤
          C02 * (c0 * c2) :=
        mul_le_mul_of_nonpos_right hC02Upper hp'.le
      have hsquare := sq_nonneg (84 * c0 + c2)
      have hyoung :
          -(28 * c0 ^ 2 + (1 / 250 : ℝ) * c2 ^ 2) ≤
            (2 / 3 : ℝ) * (c0 * c2) := by
        nlinarith only [hsquare, sq_nonneg c2]
      calc
        -(28 * c0 ^ 2 + (1 / 250 : ℝ) * c2 ^ 2) ≤
            (2 / 3 : ℝ) * (c0 * c2) := hyoung
        _ ≤ C02 * c0 * c2 := by simpa only [mul_assoc] using hcompare
  have hcross04 :
      -(14 * c0 ^ 2 + (1 / 896 : ℝ) * c4 ^ 2) ≤
        C04 * c0 * c4 := by
    by_cases hp : 0 ≤ c0 * c4
    · have hnonneg : 0 ≤ C04 * (c0 * c4) :=
        mul_nonneg hC04 hp
      calc
        -(14 * c0 ^ 2 + (1 / 896 : ℝ) * c4 ^ 2) ≤ 0 := by
          nlinarith only [sq_nonneg c0, sq_nonneg c4]
        _ ≤ C04 * c0 * c4 := by simpa only [mul_assoc] using hnonneg
    · have hp' : c0 * c4 < 0 := lt_of_not_ge hp
      have hcompare : (1 / 4 : ℝ) * (c0 * c4) ≤
          C04 * (c0 * c4) :=
        mul_le_mul_of_nonpos_right hC04Upper hp'.le
      have hsquare := sq_nonneg (112 * c0 + c4)
      have hyoung :
          -(14 * c0 ^ 2 + (1 / 896 : ℝ) * c4 ^ 2) ≤
            (1 / 4 : ℝ) * (c0 * c4) := by
        nlinarith only [hsquare]
      calc
        -(14 * c0 ^ 2 + (1 / 896 : ℝ) * c4 ^ 2) ≤
            (1 / 4 : ℝ) * (c0 * c4) := hyoung
        _ ≤ C04 * c0 * c4 := by simpa only [mul_assoc] using hcompare
  have hcross24 :
      -((1329 / 10000 : ℝ) * c2 ^ 2 +
          (177 / 625 : ℝ) * c4 ^ 2) ≤
        C24 * c2 * c4 := by
    by_cases hp : 0 ≤ c2 * c4
    · have hnonneg : 0 ≤ C24 * (c2 * c4) :=
        mul_nonneg hC24 hp
      calc
        -((1329 / 10000 : ℝ) * c2 ^ 2 +
            (177 / 625 : ℝ) * c4 ^ 2) ≤ 0 := by
          nlinarith only [sq_nonneg c2, sq_nonneg c4]
        _ ≤ C24 * c2 * c4 := by simpa only [mul_assoc] using hnonneg
    · have hp' : c2 * c4 < 0 := lt_of_not_ge hp
      have hcompare : (19399 / 50000 : ℝ) * (c2 * c4) ≤
          C24 * (c2 * c4) :=
        mul_le_mul_of_nonpos_right hC24Upper hp'.le
      have hdisc : 0 ≤
          4 * (1329 / 10000 : ℝ) * (177 / 625 : ℝ) -
            (19399 / 50000 : ℝ) ^ 2 := by norm_num
      have hsquare := sq_nonneg
        (2 * (1329 / 10000 : ℝ) * c2 +
          (19399 / 50000 : ℝ) * c4)
      have hrest : 0 ≤
          (4 * (1329 / 10000 : ℝ) * (177 / 625 : ℝ) -
            (19399 / 50000 : ℝ) ^ 2) * c4 ^ 2 :=
        mul_nonneg hdisc (sq_nonneg c4)
      have hyoung :
          -((1329 / 10000 : ℝ) * c2 ^ 2 +
              (177 / 625 : ℝ) * c4 ^ 2) ≤
            (19399 / 50000 : ℝ) * (c2 * c4) := by
        nlinarith only [hsquare, hrest]
      calc
        -((1329 / 10000 : ℝ) * c2 ^ 2 +
            (177 / 625 : ℝ) * c4 ^ 2) ≤
            (19399 / 50000 : ℝ) * (c2 * c4) := hyoung
        _ ≤ C24 * c2 * c4 := by simpa only [mul_assoc] using hcompare
  have hp24 : (1 / 25 : ℝ) * N ≤
      A22 * c2 ^ 2 + A44 * c4 ^ 2 + C24 * c2 * c4 := by
    have h22 := mul_le_mul_of_nonneg_right hA22 (sq_nonneg c2)
    have h44 := mul_le_mul_of_nonneg_right hA44 (sq_nonneg c4)
    dsimp only [N]
    nlinarith
  have hminorCost :
      (1 / 250 : ℝ) * c2 ^ 2 + (1 / 896 : ℝ) * c4 ^ 2 ≤
        (1 / 100 : ℝ) * N := by
    dsimp only [N]
    nlinarith only [sq_nonneg c2, sq_nonneg c4]
  have hquadratic : (3 / 100 : ℝ) * N ≤
      A00 * c0 ^ 2 + A22 * c2 ^ 2 + A44 * c4 ^ 2 +
        C02 * c0 * c2 + C04 * c0 * c4 + C24 * c2 * c4 +
          (451 / 10 : ℝ) * c0 ^ 2 := by
    have h00 := mul_le_mul_of_nonneg_right hA00 (sq_nonneg c0)
    linear_combination h00 + hp24 + hcross02 + hcross04 + hminorCost
  have hcore :=
    fourCellEvenZeroCoshCoupledCore_intrinsicEvenP024Profile_eq_quadratic
      c0 c2 c4
  have hmass := integral_factorTwoIntrinsicEvenP024Profile_sq c0 c2 c4
  rw [hmass, hcore]
  unfold symmetricQuadratic
  dsimp only [A00, A22, A44, C02, C04, C24, beta, N] at hquadratic
  nlinarith only [hquadratic]

/-- The complete low `P₀/P₂/P₄` coupled core clears `33 / 20` on
the narrow constant cone.  This is a direct corollary of the quantitative
nonconstant reserve above. -/
theorem thirtyThree_div_twenty_mass_le_coupledCore_intrinsicEvenP024_of_constant_small
    (c0 c2 c4 : ℝ)
    (hconstant : c0 ^ 2 ≤ (1 / 4000 : ℝ) *
      (2 * c0 ^ 2 + (2 / 5 : ℝ) * c2 ^ 2 +
        (2 / 9 : ℝ) * c4 ^ 2)) :
    (33 / 20 : ℝ) *
        (∫ x : ℝ in -1..1,
          factorTwoIntrinsicEvenP024Profile c0 c2 c4 x ^ 2) ≤
      fourCellEvenZeroCoshCoupledCore
        (factorTwoIntrinsicEvenP024Profile c0 c2 c4) := by
  let N : ℝ := (2 / 5 : ℝ) * c2 ^ 2 + (2 / 9 : ℝ) * c4 ^ 2
  have hreserve :=
    three_div_hundred_nonconstantReserve_le_coupledCore_add_constantDefect
      c0 c2 c4
  have hconstant' : 3998 * c0 ^ 2 ≤ N := by
    dsimp only [N]
    nlinarith only [hconstant]
  have habsorb : (451 / 10 : ℝ) * c0 ^ 2 ≤
      (3 / 100 : ℝ) * N := by
    nlinarith only [hconstant']
  dsimp only [N] at hreserve habsorb
  linarith

private theorem upperStripPotential_le_fullPotential_of_even
    (w : ℝ → ℝ) (hw : Continuous w) (heven : Function.Even w) :
    2 * (∫ x : ℝ in 3 / 5..1,
        yoshidaEndpointPotential x * w x ^ 2) ≤
      ∫ x : ℝ in -1..1,
        yoshidaEndpointPotential x * w x ^ 2 := by
  let g : ℝ → ℝ := fun x ↦ yoshidaEndpointPotential x * w x ^ 2
  have hgFull : IntervalIntegrable g volume (-1) 1 := by
    simpa only [g] using intervalIntegrable_endpointPotential_mul_sq w hw
  have hgEven : Function.Even g := by
    intro x
    dsimp only [g, yoshidaEndpointPotential]
    rw [heven x]
    ring_nf
  have hfold := integral_neg_one_one_eq_two_mul_zero_one_of_even
    g hgFull hgEven
  have hleft : IntervalIntegrable g volume 0 (3 / 5) := by
    apply hgFull.mono_set
    intro x hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 3 / 5)] at hx
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hright : IntervalIntegrable g volume (3 / 5) 1 := by
    apply hgFull.mono_set
    intro x hx
    rw [uIcc_of_le (by norm_num : (3 / 5 : ℝ) ≤ 1)] at hx
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact ⟨by linarith [hx.1], hx.2⟩
  have hleftNonneg : 0 ≤ ∫ x : ℝ in 0..3 / 5, g x := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro x hx
    have hxIcc : x ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    exact mul_nonneg (yoshidaEndpointPotential_nonneg_on_Icc hxIcc)
      (sq_nonneg _)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hleft hright
  dsimp only [g] at hfold hsplit hleftNonneg ⊢
  linarith

/-- On an even profile, the exact endpoint potential pays the exact retained
dyadic translation while leaving a strict positive strip reserve. -/
theorem endpointPotential_sub_dyadicPairing_nonnegative
    (w : ℝ → ℝ) (hw : Continuous w) (heven : Function.Even w) :
    0 ≤ (∫ x : ℝ in -1..1,
        yoshidaEndpointPotential x * w x ^ 2) -
      Real.sqrt 2 * Real.log 2 * fourCellEndpointPairing w := by
  let S : ℝ := ∫ x : ℝ in 3 / 5..1,
    yoshidaEndpointPotential x * w x ^ 2
  let V : ℝ := ∫ x : ℝ in -1..1,
    yoshidaEndpointPotential x * w x ^ 2
  let P : ℝ := Real.sqrt 2 * Real.log 2 * fourCellEndpointPairing w
  have hprime : P ≤ (99 / 50 : ℝ) * S := by
    simpa only [P, S] using
      fourCell_dyadicPairing_le_endpointStripPotential w hw heven
  have hstrip : 2 * S ≤ V := by
    simpa only [S, V] using
      upperStripPotential_le_fullPotential_of_even w hw heven
  have hS : 0 ≤ S := by
    dsimp only [S]
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro x hx
    have hxIcc : x ∈ Icc (-1 : ℝ) 1 :=
      ⟨by linarith [hx.1], by linarith [hx.2]⟩
    exact mul_nonneg (yoshidaEndpointPotential_nonneg_on_Icc hxIcc)
      (sq_nonneg _)
  change 0 ≤ V - P
  nlinarith

/-- The complete infinite even tail above `P₄` retains the full sixth
harmonic coefficient `49 / 20`.  The prime/potential pair remains the exact
positive endpoint-capacity block. -/
theorem fortyNine_div_twenty_mass_le_coupledCore_of_even_legendreTail
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w)
    (heven : Function.Even w)
    (hlow : centeredLegendreMomentsVanishBelow w 6) :
    (49 / 20 : ℝ) * (∫ x : ℝ in -1..1, w x ^ 2) ≤
      fourCellEvenZeroCoshCoupledCore w := by
  let M : ℝ := ∫ x : ℝ in -1..1, w x ^ 2
  let B : ℝ := (∫ x : ℝ in -1..1,
      yoshidaEndpointPotential x * w x ^ 2) -
    Real.sqrt 2 * Real.log 2 * fourCellEndpointPairing w
  have hM : 0 ≤ M := by
    dsimp only [M]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun _ _ ↦ sq_nonneg _)
  have hB : 0 ≤ B := by
    simpa only [B] using
      endpointPotential_sub_dyadicPairing_nonnegative w hw heven
  have hraw := harmonic_mul_intrinsicEnergy_le_raw_div_four
    w hw hlocal 6 hlow
  norm_num [harmonic, Finset.sum_range_succ] at hraw
  have hgap : (49 / 20 : ℝ) * M ≤ centeredRawLogEnergy w / 4 := by
    simpa only [M, factorTwoIntrinsicEnergy] using hraw
  unfold fourCellEvenZeroCoshCoupledCore
  dsimp only [M, B] at hgap hB ⊢
  linarith

/-- The low and tail diagonal blocks already clear the full `33 / 20`
target under the global constant-coordinate bound.  The low nonconstant
reserve and the tail's `4 / 5` surplus jointly absorb the entire constant
defect.  Consequently, only the genuine coupled-core polarization remains
in the canonical cutoff-six decomposition. -/
theorem thirtyThree_div_twenty_mass_le_coupledCore_diagonalSum_P024_add_tail
    (c0 c2 c4 : ℝ) (r : ℝ → ℝ) (hr : Continuous r)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) r)
    (heven : Function.Even r)
    (hlow : centeredLegendreMomentsVanishBelow r 6)
    (hconstant : c0 ^ 2 ≤ (1 / 4000 : ℝ) *
      (2 * c0 ^ 2 + (2 / 5 : ℝ) * c2 ^ 2 +
        (2 / 9 : ℝ) * c4 ^ 2 +
        (∫ x : ℝ in -1..1, r x ^ 2))) :
    (33 / 20 : ℝ) *
        (∫ x : ℝ in -1..1,
          (factorTwoIntrinsicEvenP024Profile c0 c2 c4 x + r x) ^ 2) ≤
      fourCellEvenZeroCoshCoupledCore
          (factorTwoIntrinsicEvenP024Profile c0 c2 c4) +
        fourCellEvenZeroCoshCoupledCore r := by
  let N : ℝ := (2 / 5 : ℝ) * c2 ^ 2 + (2 / 9 : ℝ) * c4 ^ 2
  let R : ℝ := ∫ x : ℝ in -1..1, r x ^ 2
  have hR : 0 ≤ R := by
    dsimp only [R]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun _ _ ↦ sq_nonneg _)
  have hconstant' : 3998 * c0 ^ 2 ≤ N + R := by
    dsimp only [N, R]
    nlinarith only [hconstant]
  have habsorb : (451 / 10 : ℝ) * c0 ^ 2 ≤
      (3 / 100 : ℝ) * N + (4 / 5 : ℝ) * R := by
    nlinarith only [hconstant', hR, sq_nonneg c2, sq_nonneg c4]
  have hlowReserve :=
    three_div_hundred_nonconstantReserve_le_coupledCore_add_constantDefect
      c0 c2 c4
  have htail :=
    fortyNine_div_twenty_mass_le_coupledCore_of_even_legendreTail
      r hr hlocal heven hlow
  have hmass := integral_intrinsicEvenP024_add_tail_sq
    c0 c2 c4 r hr hlow
  rw [hmass]
  dsimp only [N, R] at habsorb
  linarith

/-- Canonical arbitrary-profile form of the stronger cutoff-eight diagonal
closure.  The first four even Legendre coordinates and the complete
moment-eight tail already clear `33 / 20`; only their endpoint-capacity
polarization is omitted. -/
theorem thirtyThree_div_twenty_mass_le_canonicalCoupledCore_cutoffEight_diagonalSum
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w)
    (heven : Function.Even w)
    (hzero : fourCellPositiveCoshMoment w
      (fourCellOperatorHalfWidth / 2) = 0) :
    (33 / 20 : ℝ) * (∫ x : ℝ in -1..1, w x ^ 2) ≤
      fourCellEvenZeroCoshCoupledCore
          (centeredLegendreLowProjection w hw 8) +
        fourCellEvenZeroCoshCoupledCore
          (centeredLegendreHigherResidual w hw 8) := by
  let c0 : ℝ := factorTwoCanonicalLegendreCoefficient w hw 0
  let c2 : ℝ := factorTwoCanonicalLegendreCoefficient w hw 2
  let c4 : ℝ := factorTwoCanonicalLegendreCoefficient w hw 4
  let c6 : ℝ := factorTwoCanonicalLegendreCoefficient w hw 6
  let p : ℝ → ℝ := factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6
  let r : ℝ → ℝ := centeredLegendreHigherResidual w hw 8
  have hpEq : centeredLegendreLowProjection w hw 8 = p := by
    simpa only [c0, c2, c4, c6, p] using
      centeredLegendreLowProjection_eight_eq_intrinsicEvenP0246Profile
        w hw heven
  have hsum : p + r = w := by
    rw [← hpEq]
    simpa only [r] using
      centeredLegendreLowProjection_add_higherResidual w hw 8
  have hr : Continuous r := by
    simpa only [r] using continuous_centeredLegendreHigherResidual w hw 8
  have hrLocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) r := by
    simpa only [r] using
      locallyLipschitzOn_centeredLegendreHigherResidual w hw hlocal 8
  have hrEven : Function.Even r := by
    simpa only [r] using
      centeredLegendreHigherResidual_even w hw heven 8
  have hrGap : centeredLegendreMomentsVanishBelow r 8 := by
    simpa only [r] using
      centeredLegendreHigherResidual_momentsVanishBelow w hw 8
  have hc0 : c0 = centeredEvenP0Coefficient w := by
    simpa only [c0] using
      factorTwoCanonicalLegendreCoefficient_zero_eq_centeredEvenP0Coefficient
        w hw
  have hmassSplit := integral_intrinsicEvenP0246_add_tail_sq
    c0 c2 c4 c6 r hr hrGap
  have hmassLow := factorTwoIntrinsicEnergy_intrinsicEvenP0246 c0 c2 c4 c6
  change (∫ x : ℝ in -1..1, p x ^ 2) = _ at hmassLow
  have hmassSum :
      (∫ x : ℝ in -1..1, (p x + r x) ^ 2) =
        ∫ x : ℝ in -1..1, w x ^ 2 := by
    have h := congrArg
      (fun q : ℝ → ℝ ↦ ∫ x : ℝ in -1..1, q x ^ 2) hsum
    simpa only [Pi.add_apply] using h
  have htotal :
      (∫ x : ℝ in -1..1, w x ^ 2) =
        2 * c0 ^ 2 + (2 / 5 : ℝ) * c2 ^ 2 +
          (2 / 9 : ℝ) * c4 ^ 2 + (2 / 13 : ℝ) * c6 ^ 2 +
          (∫ x : ℝ in -1..1, r x ^ 2) := by
    change (∫ x : ℝ in -1..1, (p x + r x) ^ 2) = _ at hmassSplit
    rw [hmassLow] at hmassSplit
    linarith
  have hcGlobal :=
    centeredEvenP0Coefficient_sq_le_one_div_fourThousand_mass_of_coshMoment_zero
      w hw heven hzero
  have hconstant : c0 ^ 2 ≤ (1 / 4000 : ℝ) *
      (2 * c0 ^ 2 + (2 / 5 : ℝ) * c2 ^ 2 +
        (2 / 9 : ℝ) * c4 ^ 2 + (2 / 13 : ℝ) * c6 ^ 2 +
        (∫ x : ℝ in -1..1, r x ^ 2)) := by
    calc
      c0 ^ 2 = centeredEvenP0Coefficient w ^ 2 := by rw [hc0]
      _ ≤ (1 / 4000 : ℝ) * (∫ x : ℝ in -1..1, w x ^ 2) :=
        hcGlobal
      _ = (1 / 4000 : ℝ) *
          (2 * c0 ^ 2 + (2 / 5 : ℝ) * c2 ^ 2 +
            (2 / 9 : ℝ) * c4 ^ 2 + (2 / 13 : ℝ) * c6 ^ 2 +
            (∫ x : ℝ in -1..1, r x ^ 2)) := by rw [htotal]
  have hdiag :=
    thirtyThree_div_twenty_mass_le_coupledCore_diagonalSum_P0246_add_tail
      c0 c2 c4 c6 r hr hrLocal hrEven hrGap hconstant
  rw [hpEq]
  rw [← hmassSum]
  simpa only [p] using hdiag

/-- Canonical full-core handoff at cutoff eight.  Once the single displayed
capacity-dual determinant is proved for the canonical low projection and
moment-eight residual, the complete `33 / 20` coupled-core inequality follows
with no further mode estimates. -/
theorem thirtyThree_div_twenty_mass_le_canonicalCoupledCore_cutoffEight_of_capacitySchur
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w)
    (heven : Function.Even w)
    (hzero : fourCellPositiveCoshMoment w
      (fourCellOperatorHalfWidth / 2) = 0)
    (hcapacitySchur :
      fourCellEvenEndpointCapacityPolarization
          (centeredLegendreLowProjection w hw 8)
          (centeredLegendreHigherResidual w hw 8) ^ 2 ≤
        fourCellEvenP0246CutoffEightLowSchurReserve
            (factorTwoCanonicalLegendreCoefficient w hw 0)
            (factorTwoCanonicalLegendreCoefficient w hw 2)
            (factorTwoCanonicalLegendreCoefficient w hw 4)
            (factorTwoCanonicalLegendreCoefficient w hw 6) *
          ((7461 / 7000 : ℝ) *
            (∫ x : ℝ in -1..1,
              centeredLegendreHigherResidual w hw 8 x ^ 2))) :
    (33 / 20 : ℝ) * (∫ x : ℝ in -1..1, w x ^ 2) ≤
      fourCellEvenZeroCoshCoupledCore w := by
  let c0 : ℝ := factorTwoCanonicalLegendreCoefficient w hw 0
  let c2 : ℝ := factorTwoCanonicalLegendreCoefficient w hw 2
  let c4 : ℝ := factorTwoCanonicalLegendreCoefficient w hw 4
  let c6 : ℝ := factorTwoCanonicalLegendreCoefficient w hw 6
  let p : ℝ → ℝ := factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6
  let r : ℝ → ℝ := centeredLegendreHigherResidual w hw 8
  have hpEq : centeredLegendreLowProjection w hw 8 = p := by
    simpa only [c0, c2, c4, c6, p] using
      centeredLegendreLowProjection_eight_eq_intrinsicEvenP0246Profile
        w hw heven
  have hsum : p + r = w := by
    rw [← hpEq]
    simpa only [r] using
      centeredLegendreLowProjection_add_higherResidual w hw 8
  have hr : Continuous r := by
    simpa only [r] using continuous_centeredLegendreHigherResidual w hw 8
  have hrLocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) r := by
    simpa only [r] using
      locallyLipschitzOn_centeredLegendreHigherResidual w hw hlocal 8
  have hrEven : Function.Even r := by
    simpa only [r] using
      centeredLegendreHigherResidual_even w hw heven 8
  have hrGap : centeredLegendreMomentsVanishBelow r 8 := by
    simpa only [r] using
      centeredLegendreHigherResidual_momentsVanishBelow w hw 8
  have hc0 : c0 = centeredEvenP0Coefficient w := by
    simpa only [c0] using
      factorTwoCanonicalLegendreCoefficient_zero_eq_centeredEvenP0Coefficient
        w hw
  have hmassSplit := integral_intrinsicEvenP0246_add_tail_sq
    c0 c2 c4 c6 r hr hrGap
  have hmassLow := factorTwoIntrinsicEnergy_intrinsicEvenP0246 c0 c2 c4 c6
  change (∫ x : ℝ in -1..1, p x ^ 2) = _ at hmassLow
  have hmassSum :
      (∫ x : ℝ in -1..1, (p x + r x) ^ 2) =
        ∫ x : ℝ in -1..1, w x ^ 2 := by
    have h := congrArg
      (fun q : ℝ → ℝ ↦ ∫ x : ℝ in -1..1, q x ^ 2) hsum
    simpa only [Pi.add_apply] using h
  have htotal :
      (∫ x : ℝ in -1..1, w x ^ 2) =
        2 * c0 ^ 2 + (2 / 5 : ℝ) * c2 ^ 2 +
          (2 / 9 : ℝ) * c4 ^ 2 + (2 / 13 : ℝ) * c6 ^ 2 +
          (∫ x : ℝ in -1..1, r x ^ 2) := by
    change (∫ x : ℝ in -1..1, (p x + r x) ^ 2) = _ at hmassSplit
    rw [hmassLow] at hmassSplit
    linarith
  have hcGlobal :=
    centeredEvenP0Coefficient_sq_le_one_div_fourThousand_mass_of_coshMoment_zero
      w hw heven hzero
  have hconstant : c0 ^ 2 ≤ (1 / 4000 : ℝ) *
      (2 * c0 ^ 2 + (2 / 5 : ℝ) * c2 ^ 2 +
        (2 / 9 : ℝ) * c4 ^ 2 + (2 / 13 : ℝ) * c6 ^ 2 +
        (∫ x : ℝ in -1..1, r x ^ 2)) := by
    calc
      c0 ^ 2 = centeredEvenP0Coefficient w ^ 2 := by rw [hc0]
      _ ≤ (1 / 4000 : ℝ) * (∫ x : ℝ in -1..1, w x ^ 2) :=
        hcGlobal
      _ = (1 / 4000 : ℝ) *
          (2 * c0 ^ 2 + (2 / 5 : ℝ) * c2 ^ 2 +
            (2 / 9 : ℝ) * c4 ^ 2 + (2 / 13 : ℝ) * c6 ^ 2 +
            (∫ x : ℝ in -1..1, r x ^ 2)) := by rw [htotal]
  have hschur :
      fourCellEvenEndpointCapacityPolarization p r ^ 2 ≤
        fourCellEvenP0246CutoffEightLowSchurReserve c0 c2 c4 c6 *
          ((7461 / 7000 : ℝ) *
            (∫ x : ℝ in -1..1, r x ^ 2)) := by
    rw [hpEq] at hcapacitySchur
    simpa only [c0, c2, c4, c6, p, r] using hcapacitySchur
  have hfull :=
    thirtyThree_div_twenty_mass_le_coupledCore_P0246_add_tail_of_capacitySchur
      c0 c2 c4 c6 r hr hrLocal hrEven hrGap hconstant hschur
  rw [hsum] at hfull
  rw [← hmassSum]
  simpa only [p] using hfull

/-- Canonical arbitrary-profile form of the diagonal closure.  On the
zero-wide-cosh hyperplane the cutoff-six low block and its infinite tail,
before their one surviving polarization is inserted, already clear the
complete `33 / 20` target. -/
theorem thirtyThree_div_twenty_mass_le_canonicalCoupledCore_diagonalSum
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w)
    (heven : Function.Even w)
    (hzero : fourCellPositiveCoshMoment w
      (fourCellOperatorHalfWidth / 2) = 0) :
    (33 / 20 : ℝ) * (∫ x : ℝ in -1..1, w x ^ 2) ≤
      fourCellEvenZeroCoshCoupledCore
          (centeredLegendreLowProjection w hw 6) +
        fourCellEvenZeroCoshCoupledCore
          (centeredLegendreHigherResidual w hw 6) := by
  let c0 : ℝ := factorTwoCanonicalLegendreCoefficient w hw 0
  let c2 : ℝ := factorTwoCanonicalLegendreCoefficient w hw 2
  let c4 : ℝ := factorTwoCanonicalLegendreCoefficient w hw 4
  let p : ℝ → ℝ := factorTwoIntrinsicEvenP024Profile c0 c2 c4
  let r : ℝ → ℝ := centeredLegendreHigherResidual w hw 6
  have hpEq : centeredLegendreLowProjection w hw 6 = p := by
    simpa only [c0, c2, c4, p] using
      centeredLegendreLowProjection_six_eq_intrinsicEvenP024Profile
        w hw heven
  have hsum : p + r = w := by
    rw [← hpEq]
    simpa only [r] using
      centeredLegendreLowProjection_add_higherResidual w hw 6
  have hr : Continuous r := by
    simpa only [r] using continuous_centeredLegendreHigherResidual w hw 6
  have hrLocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) r := by
    simpa only [r] using
      locallyLipschitzOn_centeredLegendreHigherResidual w hw hlocal 6
  have hrEven : Function.Even r := by
    simpa only [r] using
      centeredLegendreHigherResidual_even w hw heven 6
  have hrGap : centeredLegendreMomentsVanishBelow r 6 := by
    simpa only [r] using
      centeredLegendreHigherResidual_momentsVanishBelow w hw 6
  have hc0 : c0 = centeredEvenP0Coefficient w := by
    simpa only [c0] using
      factorTwoCanonicalLegendreCoefficient_zero_eq_centeredEvenP0Coefficient
        w hw
  have hmassSplit := integral_intrinsicEvenP024_add_tail_sq
    c0 c2 c4 r hr hrGap
  have hmassLow := integral_factorTwoIntrinsicEvenP024Profile_sq c0 c2 c4
  have hmassSum :
      (∫ x : ℝ in -1..1, (p x + r x) ^ 2) =
        ∫ x : ℝ in -1..1, w x ^ 2 := by
    have h := congrArg
      (fun q : ℝ → ℝ ↦ ∫ x : ℝ in -1..1, q x ^ 2) hsum
    simpa only [Pi.add_apply] using h
  have htotal :
      (∫ x : ℝ in -1..1, w x ^ 2) =
        2 * c0 ^ 2 + (2 / 5 : ℝ) * c2 ^ 2 +
          (2 / 9 : ℝ) * c4 ^ 2 +
          (∫ x : ℝ in -1..1, r x ^ 2) := by
    dsimp only [p] at hmassSplit hmassSum
    rw [hmassLow] at hmassSplit
    linarith
  have hcGlobal :=
    centeredEvenP0Coefficient_sq_le_one_div_fourThousand_mass_of_coshMoment_zero
      w hw heven hzero
  have hconstant : c0 ^ 2 ≤ (1 / 4000 : ℝ) *
      (2 * c0 ^ 2 + (2 / 5 : ℝ) * c2 ^ 2 +
        (2 / 9 : ℝ) * c4 ^ 2 +
        (∫ x : ℝ in -1..1, r x ^ 2)) := by
    calc
      c0 ^ 2 = centeredEvenP0Coefficient w ^ 2 := by rw [hc0]
      _ ≤ (1 / 4000 : ℝ) * (∫ x : ℝ in -1..1, w x ^ 2) :=
        hcGlobal
      _ = (1 / 4000 : ℝ) *
          (2 * c0 ^ 2 + (2 / 5 : ℝ) * c2 ^ 2 +
            (2 / 9 : ℝ) * c4 ^ 2 +
            (∫ x : ℝ in -1..1, r x ^ 2)) := by rw [htotal]
  have hdiag :=
    thirtyThree_div_twenty_mass_le_coupledCore_diagonalSum_P024_add_tail
      c0 c2 c4 r hr hrLocal hrEven hrGap hconstant
  rw [hpEq]
  rw [← hmassSum]
  simpa only [p] using hdiag

/-- In particular, the infinite even tail clears the actual `33 / 20`
coupled-core target with an `4 / 5` mass reserve. -/
theorem thirtyThree_div_twenty_mass_le_coupledCore_of_even_legendreTail
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w)
    (heven : Function.Even w)
    (hlow : centeredLegendreMomentsVanishBelow w 6) :
    (33 / 20 : ℝ) * (∫ x : ℝ in -1..1, w x ^ 2) ≤
      fourCellEvenZeroCoshCoupledCore w := by
  have hstrong :=
    fortyNine_div_twenty_mass_le_coupledCore_of_even_legendreTail
      w hw hlocal heven hlow
  have hmass : 0 ≤ ∫ x : ℝ in -1..1, w x ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun _ _ ↦ sq_nonneg _)
  nlinarith

end

end ArithmeticHodge.Analysis.YoshidaFourCellEvenZeroCoshCoupledCoreStructural

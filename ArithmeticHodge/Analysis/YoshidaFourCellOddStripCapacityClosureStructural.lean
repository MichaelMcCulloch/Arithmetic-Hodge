import ArithmeticHodge.Analysis.YoshidaFourCellOddStripCapacityAssemblyStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddPolarPotentialStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicRankResidualBound
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseLegendreFourFiveStructural
import ArithmeticHodge.Analysis.YoshidaEndpointPotentialOddCoercivity
import ArithmeticHodge.Analysis.YoshidaEndpointPullbackLipschitz
import ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedRemainderEnvelopeKernel
import ArithmeticHodge.Analysis.YoshidaFourCellRegularKernelWideEnvelope
import ArithmeticHodge.Analysis.YoshidaFourCellOddP3P7RegularCrossStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddP3P9RegularCrossStructural
import ArithmeticHodge.Analysis.UnitIntervalLogEnergyLipschitz
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddCleanSharp
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddP5CleanCrossStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddP5PerturbationDiagonalStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCenteredP9Structural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP7P9CorrelationStructural
import ArithmeticHodge.Analysis.ShiftedLegendrePolynomialGap

set_option autoImplicit false

open MeasureTheory Polynomial Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddStripCapacityClosureStructural

noncomputable section

open YoshidaEndpointPotentialBound
open YoshidaEndpointPotentialExactLowMode
open YoshidaEndpointEvenLowPotential
open YoshidaEndpointPositiveDistanceFold
open CenteredOddOneThreeEnergy
open CenteredEndpointCorrelation
open YoshidaConstantBounds
open YoshidaEndpointPotentialIntegrable
open YoshidaEndpointWeightedCauchy
open YoshidaEndpointPotentialOddCoercivity
open YoshidaEndpointTriangleFoldLipschitz
open YoshidaEndpointOcticOddCoercivity
open YoshidaEndpointOcticPotential
open YoshidaEndpointOcticTwoModeSchurData
open YoshidaEndpointEvenProjectedRemainderEnvelopeKernel
open YoshidaFourCellRegularKernelWideEnvelope
open YoshidaFourCellOddP3P7RegularCrossStructural
open YoshidaFourCellOddP3P9RegularCrossStructural
open YoshidaEndpointPullbackLipschitz
open YoshidaFourCellOddPolarPotentialStructural
open YoshidaFourCellOddStripCapacityAssemblyStructural
open YoshidaFourCellOddEndpointStripCoercivityStructural
open YoshidaFourCellOddStripEmbeddingStructural
open YoshidaFourCellRawParityFoldStructural
open YoshidaFourCellRegularParityFoldStructural
open YoshidaFourCellParityHalfFoldStructural
open YoshidaFourCellParityOperatorStructural
open YoshidaFactorTwoPhaseIntrinsicRankResidualBound
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFactorTwoIntegrableLagRepresenterStructural
open YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive
open YoshidaFactorTwoPhaseIntrinsicOddCleanSharp
open YoshidaFactorTwoPhaseIntrinsicOddP5CleanCrossStructural
open YoshidaFactorTwoPhaseIntrinsicOddP5CorrelationStructural
open YoshidaFactorTwoPhaseIntrinsicOddP5PerturbationCrossStructural
open YoshidaFactorTwoPhaseIntrinsicOddP5PerturbationDiagonalStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4WeightedMass
open YoshidaFactorTwoPhaseIntrinsicOddLowEndpointStructuralPositive
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
open YoshidaFactorTwoPhaseCenteredP9Structural
open YoshidaFactorTwoPhaseP7P9CorrelationStructural
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoPhaseSymmetricCarleman
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointParityPencil
open YoshidaFactorTwoEndpointClean
open YoshidaEndpointOddOneThreeRawPolarization
open YoshidaEndpointOddResidualRegularity
open YoshidaEndpointEvenTailRepresenter
open YoshidaRegularKernelBound
open ShiftedLegendreFiniteEnergyGap
open ShiftedLegendreCenteredLowModeThreeL2
open ShiftedLegendreCenteredLowModes
open ShiftedLegendreLogEigen
open ShiftedLegendreLogKernel
open ShiftedLegendreOrthogonality
open ShiftedLogKernelCrossEnergy
open UnitIntervalIntegralBridge
open UnitIntervalLogEnergyAffine
open UnitIntervalLogEnergyLipschitz
open UnitIntervalLogEnergyProjection

/-!
# Sharp rank control for the odd four-cell strip operator

The previous pointwise polar payment used the deliberately loose estimate
`sinh (a x / 2) <= x / 3`.  At the production halfwidth one instead has the
rational bound `sinh (a x / 2) <= 7 x / 25`.  Combined with the quadratic
part of the endpoint potential, this lowers the cost of the complete odd
rank from `8 / 9` to `343 / 625` of one positive-half potential copy.
-/

/-- The exact positive base of the strip operator before subtracting its one
negative hyperbolic rank.  No regular-row, prime, or raw-energy term has been
estimated in this definition. -/
def fourCellOddStripCapacityBase (w : ℝ → ℝ) : ℝ :=
  (1 / 2 : ℝ) * fourCellOddEndpointStripEvenRawEnergy w +
    Real.sqrt 2 * Real.log 2 * fourCellOddEndpointStripEvenMass w +
    (2 - Real.sqrt 2 * Real.log 2) *
      fourCellOddEndpointStripOddMass w +
    (1 / 2 : ℝ) *
      (fourCellPositiveHalfRawSameSignEnergy w -
        fourCellOddEndpointStripRawEnergy w) +
    (1 / 2 : ℝ) * fourCellPositiveHalfRawReflectedEnergy w (-1) +
    2 * (∫ x : ℝ in 0..1,
      yoshidaEndpointPotential x * w x ^ 2) -
    2 * (Real.log (2 * fourCellOperatorHalfWidth) +
        Real.eulerMascheroniConstant + Real.log Real.pi) *
      (∫ x : ℝ in 0..1, w x ^ 2) +
    fourCellOperatorHalfWidth *
      (fourCellPositiveHalfRegularSameSignSquare w
          fourCellOperatorHalfWidth +
        fourCellPositiveHalfRegularReflectedSquare w
          fourCellOperatorHalfWidth (-1)) -
    2 * fourCellOperatorHalfWidth *
      fourCellPositiveHalfRegularRowMass w fourCellOperatorHalfWidth

/-- Exact rank-one normal form of the retained strip operator. -/
theorem fourCellOddStripCapacityLowerOperator_eq_base_sub_rank
    (w : ℝ → ℝ) :
    fourCellOddStripCapacityLowerOperator w =
      fourCellOddStripCapacityBase w -
        8 * fourCellOperatorHalfWidth *
          fourCellPositiveSinhMoment w
            (fourCellOperatorHalfWidth / 2) ^ 2 := by
  unfold fourCellOddStripCapacityLowerOperator
    fourCellOddStripCapacityBase
  ring

/-- The rational diagonal allocation selected by the exact-row Schur
problem: a small scalar mass plus `7 / 50` of the endpoint potential. -/
def fourCellOddStripBlendedAllocation (w : ℝ → ℝ) : ℝ :=
  (3 / 200 : ℝ) * (∫ x : ℝ in 0..1, w x ^ 2) +
    (7 / 50 : ℝ) *
      (∫ x : ℝ in 0..1, yoshidaEndpointPotential x * w x ^ 2)

/-- The exact raw/prime part of the odd strip base.  This is the global
positive-half raw form with only the adverse endpoint-strip prime channel
replaced by its sharp local gap. -/
def fourCellOddStripRetainedPrimeRawCapacity (w : ℝ → ℝ) : ℝ :=
  (1 / 2 : ℝ) * fourCellOddEndpointStripEvenRawEnergy w +
    Real.sqrt 2 * Real.log 2 * fourCellOddEndpointStripEvenMass w +
    (2 - Real.sqrt 2 * Real.log 2) *
      fourCellOddEndpointStripOddMass w +
    (1 / 2 : ℝ) *
      (fourCellPositiveHalfRawSameSignEnergy w -
        fourCellOddEndpointStripRawEnergy w) +
    (1 / 2 : ℝ) * fourCellPositiveHalfRawReflectedEnergy w (-1)

/-- The standard sharp odd raw/potential reserve, written entirely on the
positive half interval.  Its coefficient `14 / 5` is the half-interval form
of the structural `7 / 5` centered coercivity theorem. -/
def fourCellOddHalfCoreReserve (w : ℝ → ℝ) : ℝ :=
  (1 / 2 : ℝ) *
      (fourCellPositiveHalfRawSameSignEnergy w +
        fourCellPositiveHalfRawReflectedEnergy w (-1)) +
    2 * (∫ x : ℝ in 0..1, yoshidaEndpointPotential x * w x ^ 2) -
    (14 / 5 : ℝ) * (∫ x : ℝ in 0..1, w x ^ 2)

/-- The known centered odd coercivity supplies a nonnegative core reserve
without a cutoff or a finite-dimensional computation. -/
theorem fourCellOddHalfCoreReserve_nonneg
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w) :
    0 ≤ fourCellOddHalfCoreReserve w := by
  let f : unitInterval → ℝ := fun t ↦ centeredPullback w (t : ℝ)
  have hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w :=
    hw.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1)
  obtain ⟨C, hLip⟩ := exists_lipschitzWith_centeredPullback w hlocal
  have hfcont : Continuous f := by
    dsimp only [f, centeredPullback]
    fun_prop
  have hfmem : MemLp f 2 :=
    hfcont.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  have henergy : Integrable (unitIntervalRawLogEnergyIntegrand f) :=
    integrable_unitIntervalRawLogEnergyIntegrand_of_lipschitzWith f
      (by simpa only [f] using hLip)
  have hcoercive :=
    seven_fifths_mul_integral_sq_le_logEnergy_div_four_add_endpointPotential
      w hw.continuous (by simpa only [f] using hfmem)
        (by simpa only [f] using henergy) hodd
        (intervalIntegrable_endpointPotential_mul_sq w hw.continuous)
  have hraw := centeredRawLogEnergy_div_four_eq_positiveHalf_odd
    w hlocal hodd
  have hpotential := endpointPotential_eq_two_mul_positiveHalf
    w hw.continuous (Or.inr hodd)
  have hmass := integral_sq_eq_two_mul_positiveHalf
    w hw.continuous (Or.inr hodd)
  rw [hraw, hpotential, hmass] at hcoercive
  unfold fourCellOddHalfCoreReserve
  linarith

/-- Quantitative form of the centered odd core estimate.  Unlike the bare
`7 / 5` coercivity theorem, it retains the exact positive `P₁/P₃` Schur
quadratic after the whole infinite odd tail has been absorbed by its uniform
`53 / 60` reserve. -/
theorem oddOneThreeSchurQuadratic_le_centeredCore
    (w : ℝ → ℝ) (hwcont : Continuous w)
    (hf : MemLp (fun t : unitInterval ↦ centeredPullback w (t : ℝ)) 2)
    (henergy : Integrable (unitIntervalRawLogEnergyIntegrand
      (fun t : unitInterval ↦ centeredPullback w (t : ℝ))))
    (hwodd : Function.Odd w)
    (hpotential : IntervalIntegrable
      (fun x ↦ yoshidaEndpointPotential x * w x ^ 2) volume (-1) 1) :
    schurS11 * centeredOddP1Coefficient w ^ 2 +
        2 * schurS13 * centeredOddP1Coefficient w *
          centeredOddP3Coefficient w +
        schurS33 * centeredOddP3Coefficient w ^ 2 ≤
      centeredRawLogEnergy w / 4 +
        (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * w x ^ 2) -
        (7 / 5 : ℝ) * (∫ x : ℝ in -1..1, w x ^ 2) := by
  let a := centeredOddP1Coefficient w
  let b := centeredOddP3Coefficient w
  let v := centeredOddOneThreeResidual w
  let r := centeredOddCombinedOcticResidual w
  have hlog := centered_odd_one_three_tail_energy_le
    w hwcont hf henergy hwodd
  have hmass0 := integral_centeredOddOneThreeResidual_sq w hwcont
  have hmass :
      (∫ x : ℝ in -1..1, w x ^ 2) =
        (2 / 3 : ℝ) * a ^ 2 + (2 / 7 : ℝ) * b ^ 2 +
          ∫ x : ℝ in -1..1, v x ^ 2 := by
    dsimp only [a, b, v]
    linarith
  have hpot := integral_octic_mul_sq_decomposition w hwcont
  have hgram := integral_combinedOcticResidual_sq w
  have htail := octic_residual_tail_nonneg w
  have hcompletion := tailReserve_completion w hwcont
  have hQ11 : rawLowQ11 =
      (1 - 7 / 5 : ℝ) * (2 / 3 : ℝ) + 13771 / 41580 := by
    norm_num [rawLowQ11]
  have hQ33 : rawLowQ33 =
      (11 / 6 - 7 / 5 : ℝ) * (2 / 7 : ℝ) + 23161 / 180180 := by
    norm_num [rawLowQ33]
  have hQ13 : rawLowQ13 = (8 / 65 : ℝ) := by
    rfl
  have hδ : tailReserve = 137 / 60 - 7 / 5 := by
    norm_num [tailReserve]
  have hSchurEq :
      schurS11 * a ^ 2 + 2 * schurS13 * a * b + schurS33 * b ^ 2 =
        rawLowQ11 * a ^ 2 + 2 * rawLowQ13 * a * b +
          rawLowQ33 * b ^ 2 -
        (residualGramC11 * a ^ 2 +
          2 * residualGramC13 * a * b + residualGramC33 * b ^ 2) /
            tailReserve := by
    unfold schurS11 schurS13 schurS33
    ring
  have hsecond :
      schurS11 * a ^ 2 + 2 * schurS13 * a * b + schurS33 * b ^ 2 ≤
        rawLowQ11 * a ^ 2 + 2 * rawLowQ13 * a * b +
          rawLowQ33 * b ^ 2 +
        tailReserve * (∫ x : ℝ in -1..1, v x ^ 2) +
        2 * (∫ x : ℝ in -1..1, v x * r x) +
        ∫ x : ℝ in -1..1, yoshidaEndpointOctic x * v x ^ 2 := by
    rw [hSchurEq]
    dsimp only [a, b, v, r] at hgram hcompletion htail ⊢
    rw [hgram] at hcompletion
    norm_num [tailReserve] at hcompletion ⊢
    linarith
  have hfirst :
      rawLowQ11 * a ^ 2 + 2 * rawLowQ13 * a * b +
          rawLowQ33 * b ^ 2 +
          tailReserve * (∫ x : ℝ in -1..1, v x ^ 2) +
          2 * (∫ x : ℝ in -1..1, v x * r x) +
          ∫ x : ℝ in -1..1, yoshidaEndpointOctic x * v x ^ 2 ≤
        centeredRawLogEnergy w / 4 +
          (∫ x : ℝ in -1..1, yoshidaEndpointOctic x * w x ^ 2) -
          (7 / 5 : ℝ) * (∫ x : ℝ in -1..1, w x ^ 2) := by
    dsimp only [a, b, v, r] at hlog hmass hpot ⊢
    rw [hQ11, hQ13, hQ33, hδ]
    linarith
  have hocticInt : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointOctic x * w x ^ 2) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    unfold yoshidaEndpointOctic
    fun_prop
  have hmono :
      (∫ x : ℝ in -1..1, yoshidaEndpointOctic x * w x ^ 2) ≤
        ∫ x : ℝ in -1..1, yoshidaEndpointPotential x * w x ^ 2 := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo
      (by norm_num : (-1 : ℝ) ≤ 1) hocticInt hpotential
    intro x hx
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply octic_le_endpointPotential
    rw [abs_lt]
    exact hx
  linarith [hsecond.trans hfirst]

/-- Positive-half form of the retained low-mode Schur reserve.  This is the
quantitative reserve available for absorbing the coupled four-cell local
width defect. -/
theorem oddOneThreeSchurQuadratic_le_fourCellOddHalfCoreReserve
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w) :
    schurS11 * centeredOddP1Coefficient w ^ 2 +
        2 * schurS13 * centeredOddP1Coefficient w *
          centeredOddP3Coefficient w +
        schurS33 * centeredOddP3Coefficient w ^ 2 ≤
      fourCellOddHalfCoreReserve w := by
  let f : unitInterval → ℝ := fun t ↦ centeredPullback w (t : ℝ)
  have hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w :=
    hw.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1)
  obtain ⟨C, hLip⟩ := exists_lipschitzWith_centeredPullback w hlocal
  have hfcont : Continuous f := by
    dsimp only [f, centeredPullback]
    fun_prop
  have hfmem : MemLp f 2 :=
    hfcont.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  have henergy : Integrable (unitIntervalRawLogEnergyIntegrand f) :=
    integrable_unitIntervalRawLogEnergyIntegrand_of_lipschitzWith f
      (by simpa only [f] using hLip)
  have hcenter := oddOneThreeSchurQuadratic_le_centeredCore
    w hw.continuous (by simpa only [f] using hfmem)
      (by simpa only [f] using henergy) hodd
      (intervalIntegrable_endpointPotential_mul_sq w hw.continuous)
  have hraw := centeredRawLogEnergy_div_four_eq_positiveHalf_odd
    w hlocal hodd
  have hpotential := endpointPotential_eq_two_mul_positiveHalf
    w hw.continuous (Or.inr hodd)
  have hmass := integral_sq_eq_two_mul_positiveHalf
    w hw.continuous (Or.inr hodd)
  rw [hraw, hpotential, hmass] at hcenter
  unfold fourCellOddHalfCoreReserve
  linarith

/-! ## The uncompleted low--tail core reserve -/

/-- Exact octic lower model before spending the infinite-tail reserve in a
Schur complement.  This form keeps the residual mass, the low--tail octic
coupling, and the residual octic square available for the four-cell defect.
-/
def fourCellOddCoupledOcticCoreLower (w : ℝ → ℝ) : ℝ :=
  rawLowQ11 * centeredOddP1Coefficient w ^ 2 +
    2 * rawLowQ13 * centeredOddP1Coefficient w *
      centeredOddP3Coefficient w +
    rawLowQ33 * centeredOddP3Coefficient w ^ 2 +
    tailReserve *
      (∫ x : ℝ in -1..1, centeredOddOneThreeResidual w x ^ 2) +
    2 * (∫ x : ℝ in -1..1,
      centeredOddOneThreeResidual w x *
        centeredOddCombinedOcticResidual w x) +
    ∫ x : ℝ in -1..1,
      yoshidaEndpointOctic x * centeredOddOneThreeResidual w x ^ 2

/-- The centered odd core dominates the exact coupled octic model without
performing the residual Schur completion. -/
theorem fourCellOddCoupledOcticCoreLower_le_centeredCore
    (w : ℝ → ℝ) (hwcont : Continuous w)
    (hf : MemLp (fun t : unitInterval ↦ centeredPullback w (t : ℝ)) 2)
    (henergy : Integrable (unitIntervalRawLogEnergyIntegrand
      (fun t : unitInterval ↦ centeredPullback w (t : ℝ))))
    (hwodd : Function.Odd w)
    (hpotential : IntervalIntegrable
      (fun x ↦ yoshidaEndpointPotential x * w x ^ 2) volume (-1) 1) :
    fourCellOddCoupledOcticCoreLower w ≤
      centeredRawLogEnergy w / 4 +
        (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * w x ^ 2) -
        (7 / 5 : ℝ) * (∫ x : ℝ in -1..1, w x ^ 2) := by
  let a := centeredOddP1Coefficient w
  let b := centeredOddP3Coefficient w
  let v := centeredOddOneThreeResidual w
  let r := centeredOddCombinedOcticResidual w
  have hlog := centered_odd_one_three_tail_energy_le
    w hwcont hf henergy hwodd
  have hmass0 := integral_centeredOddOneThreeResidual_sq w hwcont
  have hmass :
      (∫ x : ℝ in -1..1, w x ^ 2) =
        (2 / 3 : ℝ) * a ^ 2 + (2 / 7 : ℝ) * b ^ 2 +
          ∫ x : ℝ in -1..1, v x ^ 2 := by
    dsimp only [a, b, v]
    linarith
  have hpot := integral_octic_mul_sq_decomposition w hwcont
  have hQ11 : rawLowQ11 =
      (1 - 7 / 5 : ℝ) * (2 / 3 : ℝ) + 13771 / 41580 := by
    norm_num [rawLowQ11]
  have hQ33 : rawLowQ33 =
      (11 / 6 - 7 / 5 : ℝ) * (2 / 7 : ℝ) + 23161 / 180180 := by
    norm_num [rawLowQ33]
  have hQ13 : rawLowQ13 = (8 / 65 : ℝ) := by
    rfl
  have hdelta : tailReserve = 137 / 60 - 7 / 5 := by
    norm_num [tailReserve]
  have hfirst :
      rawLowQ11 * a ^ 2 + 2 * rawLowQ13 * a * b +
          rawLowQ33 * b ^ 2 +
          tailReserve * (∫ x : ℝ in -1..1, v x ^ 2) +
          2 * (∫ x : ℝ in -1..1, v x * r x) +
          ∫ x : ℝ in -1..1, yoshidaEndpointOctic x * v x ^ 2 ≤
        centeredRawLogEnergy w / 4 +
          (∫ x : ℝ in -1..1, yoshidaEndpointOctic x * w x ^ 2) -
          (7 / 5 : ℝ) * (∫ x : ℝ in -1..1, w x ^ 2) := by
    dsimp only [a, b, v, r] at hlog hmass hpot ⊢
    rw [hQ11, hQ13, hQ33, hdelta]
    linarith
  have hocticInt : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointOctic x * w x ^ 2) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    unfold yoshidaEndpointOctic
    fun_prop
  have hmono :
      (∫ x : ℝ in -1..1, yoshidaEndpointOctic x * w x ^ 2) ≤
        ∫ x : ℝ in -1..1, yoshidaEndpointPotential x * w x ^ 2 := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo
      (by norm_num : (-1 : ℝ) ≤ 1) hocticInt hpotential
    intro x hx
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply octic_le_endpointPotential
    rw [abs_lt]
    exact hx
  unfold fourCellOddCoupledOcticCoreLower
  dsimp only [a, b, v, r] at hfirst ⊢
  linarith

/-- Positive-half form of the same uncompleted coupled reserve. -/
theorem fourCellOddCoupledOcticCoreLower_le_fourCellOddHalfCoreReserve
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w) :
    fourCellOddCoupledOcticCoreLower w ≤ fourCellOddHalfCoreReserve w := by
  let f : unitInterval → ℝ := fun t ↦ centeredPullback w (t : ℝ)
  have hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w :=
    hw.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1)
  obtain ⟨C, hLip⟩ := exists_lipschitzWith_centeredPullback w hlocal
  have hfcont : Continuous f := by
    dsimp only [f, centeredPullback]
    fun_prop
  have hfmem : MemLp f 2 :=
    hfcont.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  have henergy : Integrable (unitIntervalRawLogEnergyIntegrand f) :=
    integrable_unitIntervalRawLogEnergyIntegrand_of_lipschitzWith f
      (by simpa only [f] using hLip)
  have hcenter := fourCellOddCoupledOcticCoreLower_le_centeredCore
    w hw.continuous (by simpa only [f] using hfmem)
      (by simpa only [f] using henergy) hodd
      (intervalIntegrable_endpointPotential_mul_sq w hw.continuous)
  have hraw := centeredRawLogEnergy_div_four_eq_positiveHalf_odd
    w hlocal hodd
  have hpotential := endpointPotential_eq_two_mul_positiveHalf
    w hw.continuous (Or.inr hodd)
  have hmass := integral_sq_eq_two_mul_positiveHalf
    w hw.continuous (Or.inr hodd)
  rw [hraw, hpotential, hmass] at hcenter
  unfold fourCellOddHalfCoreReserve
  linarith

/-! ## Odd ground-state transform for the coupled raw kernels -/

/-- After writing an odd profile as `w x = x * u x`, the same-sign and
reflected raw kernels have an exact ground-state transform on the ordered
positive triangle.  The linear odd mode is the ground state, while every
deviation from it remains in the explicit positive square on the right. -/
theorem fourCellOddRawGroundStateKernel_eq
    {x y u v : ℝ} (hy : 0 ≤ y) (hxy : y < x) :
    (x * u - y * v) ^ 2 / (x - y) +
        (x * u + y * v) ^ 2 / (x + y) =
      2 * x * u ^ 2 +
        (2 * x * y ^ 2 / ((x - y) * (x + y))) * (u - v) ^ 2 := by
  have hsub : x - y ≠ 0 := ne_of_gt (sub_pos.mpr hxy)
  have hsum : x + y ≠ 0 := by
    have hx : 0 < x := hy.trans_lt hxy
    positivity
  field_simp [hsub, hsum]
  ring

/-- The positive-square consequence of the odd raw ground-state transform.
This is the pointwise source of the sharp linear-mode raw gap. -/
theorem two_mul_oddGroundState_le_coupledRawKernel
    {x y u v : ℝ} (hy : 0 ≤ y) (hxy : y < x) :
    2 * x * u ^ 2 ≤
      (x * u - y * v) ^ 2 / (x - y) +
        (x * u + y * v) ^ 2 / (x + y) := by
  rw [fourCellOddRawGroundStateKernel_eq hy hxy]
  have hx : 0 ≤ x := (hy.trans_lt hxy).le
  have hsub : 0 ≤ x - y := (sub_pos.mpr hxy).le
  have hsum : 0 ≤ x + y := add_nonneg hx hy
  have hcoefficient :
      0 ≤ 2 * x * y ^ 2 / ((x - y) * (x + y)) := by
    exact div_nonneg (by positivity) (mul_nonneg hsub hsum)
  nlinarith [mul_nonneg hcoefficient (sq_nonneg (u - v))]

/-- Coordinate-free form of the same ground-state bound.  It applies
directly to two profile values and therefore does not divide by the value of
the smaller spatial coordinate. -/
theorem two_mul_sq_div_le_coupledRawKernel
    {x y a b : ℝ} (hy : 0 ≤ y) (hxy : y < x) :
    2 * a ^ 2 / x ≤
      (a - b) ^ 2 / (x - y) + (a + b) ^ 2 / (x + y) := by
  have hx : 0 < x := hy.trans_lt hxy
  have hsub : x - y ≠ 0 := ne_of_gt (sub_pos.mpr hxy)
  have hsum : x + y ≠ 0 := by positivity
  have hxne : x ≠ 0 := hx.ne'
  rw [show
      (a - b) ^ 2 / (x - y) + (a + b) ^ 2 / (x + y) =
        2 * a ^ 2 / x +
          2 * (y * a - x * b) ^ 2 /
            (x * (x - y) * (x + y)) by
    field_simp [hxne, hsub, hsum]
    ring]
  have hden : 0 ≤ x * (x - y) * (x + y) :=
    mul_nonneg
      (mul_nonneg hx.le (sub_pos.mpr hxy).le)
      (add_pos_of_pos_of_nonneg hx hy).le
  exact le_add_of_nonneg_right (div_nonneg (by positivity) hden)

/-- On the production positive half, each ordered same/reflected raw pair
already pays twice the mass of its larger-coordinate value. -/
theorem two_mul_sq_le_coupledRawKernel
    {x y a b : ℝ} (hy : 0 ≤ y) (hxy : y < x) (hx1 : x ≤ 1) :
    2 * a ^ 2 ≤
      (a - b) ^ 2 / (x - y) + (a + b) ^ 2 / (x + y) := by
  have hx : 0 < x := hy.trans_lt hxy
  have hmass : 2 * a ^ 2 ≤ 2 * a ^ 2 / x := by
    rw [le_div_iff₀ hx]
    nlinarith [sq_nonneg a]
  exact hmass.trans (two_mul_sq_div_le_coupledRawKernel hy hxy)

/-- Same-sign plus reflected raw kernel on the positive half square. -/
def fourCellOddCoupledRawPair (w : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  (w p.1 - w p.2) ^ 2 / |p.1 - p.2| +
    (w p.1 + w p.2) ^ 2 / (p.1 + p.2)

/-- The cross rectangle between `[0,3/5]` and the endpoint strip already
pays `6/5` of the endpoint-strip mass in one orientation.  Doubling by
kernel symmetry will therefore pay `12/5` in the raw cancellation reserve.
-/
theorem six_fifths_upperStripMass_le_cross_coupledRaw
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) :
    (6 / 5 : ℝ) * (∫ x : ℝ in 3 / 5..1, w x ^ 2) ≤
      ∫ p : ℝ × ℝ in
        Icc (3 / 5 : ℝ) 1 ×ˢ Ico (0 : ℝ) (3 / 5),
          fourCellOddCoupledRawPair w p
            ∂((volume : Measure ℝ).prod volume) := by
  let A : Set ℝ := Ico (0 : ℝ) (3 / 5)
  let B : Set ℝ := Icc (3 / 5 : ℝ) 1
  let P : Set (ℝ × ℝ) := B ×ˢ A
  let K : ℝ × ℝ → ℝ := fourCellOddCoupledRawPair w
  let L : ℝ × ℝ → ℝ := fun p ↦ 2 * w p.1 ^ 2
  have hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w :=
    hw.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1)
  obtain ⟨C, hC⟩ := hlocal.exists_lipschitzOnWith_of_compact isCompact_Icc
  have hfull :=
    integrableOn_centeredLogDifferenceKernel_prod_of_lipschitzOnWith w hC
  have hBsub : B ⊆ Icc (-1 : ℝ) 1 := by
    intro x hx
    exact ⟨by linarith [hx.1], hx.2⟩
  have hAsub : A ⊆ Icc (-1 : ℝ) 1 := by
    intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hsame : IntegrableOn
      (fun p : ℝ × ℝ ↦ centeredLogDifferenceKernel w p.1 p.2) P
      ((volume : Measure ℝ).prod volume) := by
    exact hfull.mono_set (Set.prod_mono hBsub hAsub)
  let J : ℝ × ℝ → ℝ := fun p ↦
    (w p.1 + w p.2) ^ 2 / (p.1 + p.2)
  have hJcont : ContinuousOn J
      (Icc (3 / 5 : ℝ) 1 ×ˢ Icc (0 : ℝ) (3 / 5)) := by
    apply ContinuousOn.div
    · exact ((hw.continuous.comp continuous_fst).add
        (hw.continuous.comp continuous_snd)).pow 2 |>.continuousOn
    · exact (continuous_fst.add continuous_snd).continuousOn
    · intro p hp
      dsimp only
      linarith [hp.1.1, hp.2.1]
  have hJlarge : IntegrableOn J
      (Icc (3 / 5 : ℝ) 1 ×ˢ Icc (0 : ℝ) (3 / 5))
      ((volume : Measure ℝ).prod volume) :=
    hJcont.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hPsub : P ⊆ Icc (3 / 5 : ℝ) 1 ×ˢ Icc (0 : ℝ) (3 / 5) := by
    intro p hp
    exact ⟨hp.1, ⟨hp.2.1, hp.2.2.le⟩⟩
  have hJ : IntegrableOn J P ((volume : Measure ℝ).prod volume) :=
    hJlarge.mono_set hPsub
  have hK : IntegrableOn K P ((volume : Measure ℝ).prod volume) := by
    apply hsame.add hJ |>.congr
    filter_upwards [ae_restrict_mem
      (measurableSet_Icc.prod measurableSet_Ico)] with p hp
    dsimp only [K, J, P, B, A, fourCellOddCoupledRawPair]
    unfold centeredLogDifferenceKernel
    rfl
  have hLlarge : IntegrableOn L
      (Icc (3 / 5 : ℝ) 1 ×ˢ Icc (0 : ℝ) (3 / 5))
      ((volume : Measure ℝ).prod volume) := by
    exact (by fun_prop : Continuous L).continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
  have hL : IntegrableOn L P ((volume : Measure ℝ).prod volume) :=
    hLlarge.mono_set hPsub
  have hPmeas : MeasurableSet P := measurableSet_Icc.prod measurableSet_Ico
  have hpoint : ∀ p ∈ P, L p ≤ K p := by
    intro p hp
    have hy : 0 ≤ p.2 := hp.2.1
    have hxy : p.2 < p.1 := by linarith [hp.1.1, hp.2.2]
    have hx1 : p.1 ≤ 1 := hp.1.2
    dsimp only [L, K, fourCellOddCoupledRawPair]
    rw [abs_of_pos (sub_pos.mpr hxy)]
    exact two_mul_sq_le_coupledRawKernel hy hxy hx1
  have hmono :
      (∫ p : ℝ × ℝ in P, L p
        ∂((volume : Measure ℝ).prod volume)) ≤
      ∫ p : ℝ × ℝ in P, K p
        ∂((volume : Measure ℝ).prod volume) :=
    setIntegral_mono_on hL hK hPmeas hpoint
  have hBmass : (∫ x : ℝ in B, w x ^ 2) =
      ∫ x : ℝ in 3 / 5..1, w x ^ 2 := by
    dsimp only [B]
    rw [intervalIntegral.integral_of_le (by norm_num),
      ← integral_Icc_eq_integral_Ioc]
  have hLvalue :
      (∫ p : ℝ × ℝ in P, L p
        ∂((volume : Measure ℝ).prod volume)) =
      (6 / 5 : ℝ) * (∫ x : ℝ in 3 / 5..1, w x ^ 2) := by
    dsimp only [P, L, B, A]
    rw [show (fun p : ℝ × ℝ ↦ 2 * w p.1 ^ 2) =
        fun p ↦ (2 * w p.1 ^ 2) * (1 : ℝ) by
      funext p
      ring,
      setIntegral_prod_mul
        (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
        (fun x : ℝ ↦ 2 * w x ^ 2) (fun _x : ℝ ↦ (1 : ℝ))
        (Icc (3 / 5 : ℝ) 1) (Ico (0 : ℝ) (3 / 5)),
      integral_const_mul, hBmass, setIntegral_const]
    norm_num
    ring
  simpa only [P, K, B, A] using hLvalue.symm.trans_le hmono

/-- Sharp weighted version of the cross-rectangle reserve.  The factor
`1/x` is the exact odd ground-state density and is deliberately not replaced
by its coarse lower bound `1`. -/
theorem six_fifths_upperStripWeightedMass_le_cross_coupledRaw
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) :
    (6 / 5 : ℝ) * (∫ x : ℝ in 3 / 5..1, w x ^ 2 / x) ≤
      ∫ p : ℝ × ℝ in
        Icc (3 / 5 : ℝ) 1 ×ˢ Ico (0 : ℝ) (3 / 5),
          fourCellOddCoupledRawPair w p
            ∂((volume : Measure ℝ).prod volume) := by
  let A : Set ℝ := Ico (0 : ℝ) (3 / 5)
  let B : Set ℝ := Icc (3 / 5 : ℝ) 1
  let P : Set (ℝ × ℝ) := B ×ˢ A
  let K : ℝ × ℝ → ℝ := fourCellOddCoupledRawPair w
  let L : ℝ × ℝ → ℝ := fun p ↦ 2 * w p.1 ^ 2 / p.1
  have hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w :=
    hw.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1)
  obtain ⟨C, hC⟩ := hlocal.exists_lipschitzOnWith_of_compact isCompact_Icc
  have hfull :=
    integrableOn_centeredLogDifferenceKernel_prod_of_lipschitzOnWith w hC
  have hBsub : B ⊆ Icc (-1 : ℝ) 1 := by
    intro x hx
    exact ⟨by linarith [hx.1], hx.2⟩
  have hAsub : A ⊆ Icc (-1 : ℝ) 1 := by
    intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hsame : IntegrableOn
      (fun p : ℝ × ℝ ↦ centeredLogDifferenceKernel w p.1 p.2) P
      ((volume : Measure ℝ).prod volume) :=
    hfull.mono_set (Set.prod_mono hBsub hAsub)
  let J : ℝ × ℝ → ℝ := fun p ↦
    (w p.1 + w p.2) ^ 2 / (p.1 + p.2)
  have hJcont : ContinuousOn J
      (Icc (3 / 5 : ℝ) 1 ×ˢ Icc (0 : ℝ) (3 / 5)) := by
    apply ContinuousOn.div
    · exact ((hw.continuous.comp continuous_fst).add
        (hw.continuous.comp continuous_snd)).pow 2 |>.continuousOn
    · exact (continuous_fst.add continuous_snd).continuousOn
    · intro p hp
      dsimp only
      linarith [hp.1.1, hp.2.1]
  have hJlarge : IntegrableOn J
      (Icc (3 / 5 : ℝ) 1 ×ˢ Icc (0 : ℝ) (3 / 5))
      ((volume : Measure ℝ).prod volume) :=
    hJcont.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hPsub : P ⊆ Icc (3 / 5 : ℝ) 1 ×ˢ Icc (0 : ℝ) (3 / 5) := by
    intro p hp
    exact ⟨hp.1, ⟨hp.2.1, hp.2.2.le⟩⟩
  have hJ : IntegrableOn J P ((volume : Measure ℝ).prod volume) :=
    hJlarge.mono_set hPsub
  have hK : IntegrableOn K P ((volume : Measure ℝ).prod volume) := by
    apply hsame.add hJ |>.congr
    filter_upwards [ae_restrict_mem
      (measurableSet_Icc.prod measurableSet_Ico)] with p hp
    dsimp only [K, J, P, B, A, fourCellOddCoupledRawPair]
    unfold centeredLogDifferenceKernel
    rfl
  have hLcont : ContinuousOn L
      (Icc (3 / 5 : ℝ) 1 ×ˢ Icc (0 : ℝ) (3 / 5)) := by
    apply ContinuousOn.div
    · exact (continuous_const.mul
        ((hw.continuous.comp continuous_fst).pow 2)).continuousOn
    · exact continuous_fst.continuousOn
    · intro p hp
      dsimp only
      linarith [hp.1.1]
  have hLlarge : IntegrableOn L
      (Icc (3 / 5 : ℝ) 1 ×ˢ Icc (0 : ℝ) (3 / 5))
      ((volume : Measure ℝ).prod volume) :=
    hLcont.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hL : IntegrableOn L P ((volume : Measure ℝ).prod volume) :=
    hLlarge.mono_set hPsub
  have hPmeas : MeasurableSet P := measurableSet_Icc.prod measurableSet_Ico
  have hpoint : ∀ p ∈ P, L p ≤ K p := by
    intro p hp
    have hy : 0 ≤ p.2 := hp.2.1
    have hxy : p.2 < p.1 := by linarith [hp.1.1, hp.2.2]
    dsimp only [L, K, fourCellOddCoupledRawPair]
    rw [abs_of_pos (sub_pos.mpr hxy)]
    exact two_mul_sq_div_le_coupledRawKernel hy hxy
  have hmono :
      (∫ p : ℝ × ℝ in P, L p
        ∂((volume : Measure ℝ).prod volume)) ≤
      ∫ p : ℝ × ℝ in P, K p
        ∂((volume : Measure ℝ).prod volume) :=
    setIntegral_mono_on hL hK hPmeas hpoint
  have hBmass : (∫ x : ℝ in B, w x ^ 2 / x) =
      ∫ x : ℝ in 3 / 5..1, w x ^ 2 / x := by
    dsimp only [B]
    rw [intervalIntegral.integral_of_le (by norm_num),
      ← integral_Icc_eq_integral_Ioc]
  have hLvalue :
      (∫ p : ℝ × ℝ in P, L p
        ∂((volume : Measure ℝ).prod volume)) =
      (6 / 5 : ℝ) * (∫ x : ℝ in 3 / 5..1, w x ^ 2 / x) := by
    dsimp only [P, L, B, A]
    rw [show (fun p : ℝ × ℝ ↦ 2 * w p.1 ^ 2 / p.1) =
        fun p ↦ (2 * (w p.1 ^ 2 / p.1)) * (1 : ℝ) by
      funext p
      rw [mul_one]
      exact mul_div_assoc _ _ _,
      setIntegral_prod_mul
        (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
        (fun x : ℝ ↦ 2 * (w x ^ 2 / x)) (fun _x : ℝ ↦ (1 : ℝ))
        (Icc (3 / 5 : ℝ) 1) (Ico (0 : ℝ) (3 / 5)),
      integral_const_mul, hBmass, setIntegral_const]
    have hscale (m : ℝ) : (2 * m) * (3 / 5) = 6 / 5 * m := by
      norm_num
      linarith
    have hmeasure :
        (volume : Measure ℝ).real (Ico (0 : ℝ) (3 / 5)) = 3 / 5 := by
      norm_num
    rw [hmeasure, smul_eq_mul, mul_one]
    exact hscale _
  simpa only [P, K, B, A] using hLvalue.symm.trans_le hmono

private theorem intervalIntegral_integral_eq_setIntegral_square
    (F : ℝ × ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hF : IntegrableOn F (Icc a b ×ˢ Icc a b)
      ((volume : Measure ℝ).prod volume)) :
    (∫ x : ℝ in a..b, ∫ y : ℝ in a..b, F (x, y)) =
      ∫ p : ℝ × ℝ in Icc a b ×ˢ Icc a b, F p := by
  calc
    (∫ x : ℝ in a..b, ∫ y : ℝ in a..b, F (x, y)) =
        ∫ x : ℝ in Icc a b, ∫ y : ℝ in Icc a b, F (x, y) := by
      rw [intervalIntegral.integral_of_le hab,
        ← integral_Icc_eq_integral_Ioc]
      apply setIntegral_congr_fun measurableSet_Icc
      intro x _hx
      change (∫ y : ℝ in a..b, F (x, y)) =
        ∫ y : ℝ in Icc a b, F (x, y)
      rw [intervalIntegral.integral_of_le hab,
        ← integral_Icc_eq_integral_Ioc]
    _ = ∫ p : ℝ × ℝ in Icc a b ×ˢ Icc a b, F p := by
      exact (setIntegral_prod F hF).symm

private theorem integrableOn_reflectedRawKernel_of_lipschitzOnWith_odd
    {C : NNReal} (w : ℝ → ℝ) (hw : Continuous w)
    (hC : LipschitzOnWith C w (Icc (-1 : ℝ) 1))
    (hodd : Function.Odd w) :
    IntegrableOn
      (fun p : ℝ × ℝ ↦ (w p.1 + w p.2) ^ 2 / (p.1 + p.2))
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
      ((volume : Measure ℝ).prod volume) := by
  let P : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1
  let J : ℝ × ℝ → ℝ := fun p ↦
    (w p.1 + w p.2) ^ 2 / (p.1 + p.2)
  let D : ℝ × ℝ → ℝ := fun p ↦
    (C : ℝ) ^ 2 * (p.1 + p.2)
  have hw0 : w 0 = 0 := by
    have h := hodd 0
    norm_num at h ⊢
    linarith
  have hD : IntegrableOn D P ((volume : Measure ℝ).prod volume) := by
    exact (by fun_prop : Continuous D).continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
  have hJmeas : AEStronglyMeasurable J
      (((volume : Measure ℝ).prod volume).restrict P) := by
    apply Measurable.aestronglyMeasurable
    dsimp only [J]
    exact (((hw.measurable.comp measurable_fst).add
      (hw.measurable.comp measurable_snd)).pow_const 2).div
        (measurable_fst.add measurable_snd)
  have hdom : ∀ᵐ p ∂(((volume : Measure ℝ).prod volume).restrict P),
      ‖J p‖ ≤ D p := by
    filter_upwards [ae_restrict_mem
      (measurableSet_Icc.prod measurableSet_Icc)] with p hp
    have hxmem : p.1 ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hp.1.1], hp.1.2⟩
    have hymem : p.2 ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hp.2.1], hp.2.2⟩
    have hzero : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := by norm_num
    have hxbound : |w p.1| ≤ (C : ℝ) * p.1 := by
      have h := hC.dist_le_mul p.1 hxmem 0 hzero
      rw [Real.dist_eq, Real.dist_eq, hw0, sub_zero, sub_zero,
        abs_of_nonneg hp.1.1] at h
      exact h
    have hybound : |w p.2| ≤ (C : ℝ) * p.2 := by
      have h := hC.dist_le_mul p.2 hymem 0 hzero
      rw [Real.dist_eq, Real.dist_eq, hw0, sub_zero, sub_zero,
        abs_of_nonneg hp.2.1] at h
      exact h
    have hsum0 : 0 ≤ p.1 + p.2 := add_nonneg hp.1.1 hp.2.1
    have habs : |w p.1 + w p.2| ≤ (C : ℝ) * (p.1 + p.2) := by
      calc
        |w p.1 + w p.2| ≤ |w p.1| + |w p.2| := abs_add_le _ _
        _ ≤ (C : ℝ) * p.1 + (C : ℝ) * p.2 := add_le_add hxbound hybound
        _ = (C : ℝ) * (p.1 + p.2) := by ring
    dsimp only [J, D]
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) hsum0)]
    by_cases hsum : p.1 + p.2 = 0
    · have hx0 : p.1 = 0 := by linarith [hp.1.1, hp.2.1]
      have hy0 : p.2 = 0 := by linarith [hp.1.1, hp.2.1]
      simp [hx0, hy0, hw0]
    · have hsumPos : 0 < p.1 + p.2 := lt_of_le_of_ne hsum0 (Ne.symm hsum)
      rw [div_le_iff₀ hsumPos]
      have hright0 : 0 ≤ (C : ℝ) * (p.1 + p.2) :=
        mul_nonneg C.property hsum0
      have hsq := (sq_le_sq₀ (abs_nonneg (w p.1 + w p.2)) hright0).2 habs
      rw [sq_abs, mul_pow] at hsq
      nlinarith
  exact hD.mono' hJmeas hdom

/-- Abstract square-partition budget.  Any certified lower bound for the
lower/lower coupled square can be retained alongside both orientations of
the lower/upper cross rectangle. -/
private theorem lowerSquareBudget_add_two_mul_cross_le_fullRaw_sub_stripRaw
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w)
    (m : ℝ)
    (hm : m ≤
      ∫ p : ℝ × ℝ in Ico (0 : ℝ) (3 / 5) ×ˢ Ico (0 : ℝ) (3 / 5),
        fourCellOddCoupledRawPair w p
          ∂((volume : Measure ℝ).prod volume)) :
    m + 2 * (∫ p : ℝ × ℝ in
        Icc (3 / 5 : ℝ) 1 ×ˢ Ico (0 : ℝ) (3 / 5),
          fourCellOddCoupledRawPair w p
            ∂((volume : Measure ℝ).prod volume)) ≤
      fourCellPositiveHalfRawSameSignEnergy w +
        fourCellPositiveHalfRawReflectedEnergy w (-1) -
          fourCellOddEndpointStripRawEnergy w := by
  let A : Set ℝ := Ico (0 : ℝ) (3 / 5)
  let B : Set ℝ := Icc (3 / 5 : ℝ) 1
  let U : Set ℝ := Icc (0 : ℝ) 1
  let P : Set (ℝ × ℝ) := B ×ˢ A
  let Pswap : Set (ℝ × ℝ) := A ×ˢ B
  let S : ℝ × ℝ → ℝ := fun p ↦
    centeredLogDifferenceKernel w p.1 p.2
  let J : ℝ × ℝ → ℝ := fun p ↦
    (w p.1 + w p.2) ^ 2 / (p.1 + p.2)
  let K : ℝ × ℝ → ℝ := fun p ↦ S p + J p
  have hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w :=
    hw.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1)
  obtain ⟨C, hC⟩ := hlocal.exists_lipschitzOnWith_of_compact isCompact_Icc
  have hfull :=
    integrableOn_centeredLogDifferenceKernel_prod_of_lipschitzOnWith w hC
  have hUsub : U ⊆ Icc (-1 : ℝ) 1 := by
    intro x hx
    exact ⟨by linarith [hx.1], hx.2⟩
  have hS : IntegrableOn S (U ×ˢ U)
      ((volume : Measure ℝ).prod volume) := by
    simpa only [S] using hfull.mono_set (Set.prod_mono hUsub hUsub)
  have hJ : IntegrableOn J (U ×ˢ U)
      ((volume : Measure ℝ).prod volume) := by
    simpa only [J, U] using
      integrableOn_reflectedRawKernel_of_lipschitzOnWith_odd
        w hw.continuous hC hodd
  have hK : IntegrableOn K (U ×ˢ U)
      ((volume : Measure ℝ).prod volume) := by
    exact hS.add hJ
  have hAsub : A ⊆ U := by
    intro x hx
    exact ⟨hx.1, hx.2.le.trans (by norm_num)⟩
  have hBsub : B ⊆ U := by
    intro x hx
    exact ⟨by linarith [hx.1], hx.2⟩
  have hAA := hK.mono_set (Set.prod_mono hAsub hAsub)
  have hAB := hK.mono_set (Set.prod_mono hAsub hBsub)
  have hBA := hK.mono_set (Set.prod_mono hBsub hAsub)
  have hBB := hK.mono_set (Set.prod_mono hBsub hBsub)
  have hSBB := hS.mono_set (Set.prod_mono hBsub hBsub)
  have hJBB := hJ.mono_set (Set.prod_mono hBsub hBsub)
  have hm' : m ≤
      ∫ p : ℝ × ℝ in A ×ˢ A, K p
        ∂((volume : Measure ℝ).prod volume) := by
    simpa only [A, K, S, J, fourCellOddCoupledRawPair,
      centeredLogDifferenceKernel] using hm
  have hAmeas : MeasurableSet A := measurableSet_Ico
  have hBmeas : MeasurableSet B := measurableSet_Icc
  have hUmeas : MeasurableSet U := measurableSet_Icc
  have hABdisjoint : Disjoint A B := by
    rw [Set.disjoint_left]
    intro x hxA hxB
    exact (not_lt_of_ge hxB.1) hxA.2
  have hU : U = A ∪ B := by
    ext x
    simp only [U, A, B, mem_Icc, mem_Ico, mem_union]
    constructor
    · intro hx
      by_cases hxs : x < 3 / 5
      · exact Or.inl ⟨hx.1, hxs⟩
      · exact Or.inr ⟨le_of_not_gt hxs, hx.2⟩
    · rintro (hx | hx)
      · exact ⟨hx.1, hx.2.le.trans (by norm_num)⟩
      · exact ⟨by linarith [hx.1], hx.2⟩
  have houter :
      (∫ p : ℝ × ℝ in U ×ˢ U, K p
        ∂((volume : Measure ℝ).prod volume)) =
      (∫ p : ℝ × ℝ in A ×ˢ U, K p
        ∂((volume : Measure ℝ).prod volume)) +
      ∫ p : ℝ × ℝ in B ×ˢ U, K p
        ∂((volume : Measure ℝ).prod volume) := by
    rw [show U ×ˢ U = (A ×ˢ U) ∪ (B ×ˢ U) by
      rw [hU, union_prod]]
    exact setIntegral_union (hABdisjoint.set_prod_left U U)
      (hBmeas.prod hUmeas)
      (hK.mono_set (Set.prod_mono hAsub (Subset.rfl)))
      (hK.mono_set (Set.prod_mono hBsub (Subset.rfl)))
  have hleft :
      (∫ p : ℝ × ℝ in A ×ˢ U, K p
        ∂((volume : Measure ℝ).prod volume)) =
      (∫ p : ℝ × ℝ in A ×ˢ A, K p
        ∂((volume : Measure ℝ).prod volume)) +
      ∫ p : ℝ × ℝ in A ×ˢ B, K p
        ∂((volume : Measure ℝ).prod volume) := by
    rw [show A ×ˢ U = (A ×ˢ A) ∪ (A ×ˢ B) by
      rw [hU, prod_union]]
    exact setIntegral_union (hABdisjoint.set_prod_right A A)
      (hAmeas.prod hBmeas) hAA hAB
  have hright :
      (∫ p : ℝ × ℝ in B ×ˢ U, K p
        ∂((volume : Measure ℝ).prod volume)) =
      (∫ p : ℝ × ℝ in B ×ˢ A, K p
        ∂((volume : Measure ℝ).prod volume)) +
      ∫ p : ℝ × ℝ in B ×ˢ B, K p
        ∂((volume : Measure ℝ).prod volume) := by
    rw [show B ×ˢ U = (B ×ˢ A) ∪ (B ×ˢ B) by
      rw [hU, prod_union]]
    exact setIntegral_union (hABdisjoint.set_prod_right B B)
      (hBmeas.prod hBmeas) hBA hBB
  have hKswap (p : ℝ × ℝ) : K p.swap = K p := by
    rcases p with ⟨x, y⟩
    dsimp only [K, S, J]
    simp only [Prod.swap_prod_mk]
    unfold centeredLogDifferenceKernel
    rw [show y - x = -(x - y) by ring, abs_neg]
    ring
  have hcrossSwap :
      (∫ p : ℝ × ℝ in A ×ˢ B, K p
        ∂((volume : Measure ℝ).prod volume)) =
      ∫ p : ℝ × ℝ in B ×ˢ A, K p
        ∂((volume : Measure ℝ).prod volume) := by
    have hswap := MeasureTheory.setIntegral_prod_swap
      (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)) B A K
    calc
      (∫ p : ℝ × ℝ in A ×ˢ B, K p
          ∂((volume : Measure ℝ).prod volume)) =
          ∫ p : ℝ × ℝ in A ×ˢ B, K p.swap
            ∂((volume : Measure ℝ).prod volume) := by
        apply setIntegral_congr_fun (hAmeas.prod hBmeas)
        intro p _hp
        exact (hKswap p).symm
      _ = ∫ p : ℝ × ℝ in B ×ˢ A, K p
          ∂((volume : Measure ℝ).prod volume) := hswap
  have hKBBsplit :
      (∫ p : ℝ × ℝ in B ×ˢ B, K p
        ∂((volume : Measure ℝ).prod volume)) =
      (∫ p : ℝ × ℝ in B ×ˢ B, S p
        ∂((volume : Measure ℝ).prod volume)) +
      ∫ p : ℝ × ℝ in B ×ˢ B, J p
        ∂((volume : Measure ℝ).prod volume) := by
    change (∫ p : ℝ × ℝ in B ×ˢ B, S p + J p
        ∂((volume : Measure ℝ).prod volume)) = _
    exact MeasureTheory.integral_add hSBB hJBB
  have hJnonneg : ∀ p ∈ B ×ˢ B, 0 ≤ J p := by
    intro p hp
    dsimp only [J]
    exact div_nonneg (sq_nonneg _) (add_nonneg
      (by linarith [hp.1.1]) (by linarith [hp.2.1]))
  have hJBB0 : 0 ≤
      ∫ p : ℝ × ℝ in B ×ˢ B, J p
        ∂((volume : Measure ℝ).prod volume) := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem (hBmeas.prod hBmeas)] with p hp
    exact hJnonneg p hp
  have hset :
      m + 2 * (∫ p : ℝ × ℝ in P, K p
        ∂((volume : Measure ℝ).prod volume)) ≤
      (∫ p : ℝ × ℝ in U ×ˢ U, K p
        ∂((volume : Measure ℝ).prod volume)) -
      ∫ p : ℝ × ℝ in B ×ˢ B, S p
        ∂((volume : Measure ℝ).prod volume) := by
    dsimp only [P, Pswap] at hcrossSwap ⊢
    rw [houter, hleft, hright, hcrossSwap, hKBBsplit]
    linarith
  have hSfull := intervalIntegral_integral_eq_setIntegral_square
    S 0 1 (by norm_num) hS
  have hJfull := intervalIntegral_integral_eq_setIntegral_square
    J 0 1 (by norm_num) hJ
  have hKfull :
      (∫ p : ℝ × ℝ in U ×ˢ U, K p
        ∂((volume : Measure ℝ).prod volume)) =
      fourCellPositiveHalfRawSameSignEnergy w +
        fourCellPositiveHalfRawReflectedEnergy w (-1) := by
    rw [show (∫ p : ℝ × ℝ in U ×ˢ U, K p
        ∂((volume : Measure ℝ).prod volume)) =
      (∫ p : ℝ × ℝ in U ×ˢ U, S p
        ∂((volume : Measure ℝ).prod volume)) +
      ∫ p : ℝ × ℝ in U ×ˢ U, J p
        ∂((volume : Measure ℝ).prod volume) by
      change (∫ p : ℝ × ℝ in U ×ˢ U, S p + J p
          ∂((volume : Measure ℝ).prod volume)) = _
      exact MeasureTheory.integral_add hS hJ]
    unfold fourCellPositiveHalfRawSameSignEnergy
      fourCellPositiveHalfRawReflectedEnergy
    simp only [neg_mul, one_mul, sub_neg_eq_add]
    dsimp only [U, S, J] at hSfull hJfull ⊢
    unfold centeredLogDifferenceKernel at hSfull ⊢
    exact congrArg₂ (fun a b : ℝ ↦ a + b) hSfull.symm hJfull.symm
  have hSBBbridge := intervalIntegral_integral_eq_setIntegral_square
    S (3 / 5) 1 (by norm_num) hSBB
  have hSBBvalue :
      (∫ p : ℝ × ℝ in B ×ˢ B, S p
        ∂((volume : Measure ℝ).prod volume)) =
      fourCellOddEndpointStripRawEnergy w := by
    rw [fourCellOddEndpointStripRawEnergy_eq_physicalSquare]
    dsimp only [B, S] at hSBBbridge ⊢
    unfold centeredLogDifferenceKernel at hSBBbridge
    exact hSBBbridge.symm
  rw [hKfull, hSBBvalue] at hset
  simpa only [P, K, B, A, fourCellOddCoupledRawPair, S, J,
    centeredLogDifferenceKernel] using hset

/-- After the endpoint-strip same-sign square is removed, the complete raw
form still contains both orientations of the lower/upper cross rectangle.
The reflected square is essential here and is kept inside the coupled
kernel throughout the proof. -/
theorem two_mul_cross_coupledRaw_le_fullRaw_sub_stripRaw
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w) :
    2 * (∫ p : ℝ × ℝ in
        Icc (3 / 5 : ℝ) 1 ×ˢ Ico (0 : ℝ) (3 / 5),
          fourCellOddCoupledRawPair w p
            ∂((volume : Measure ℝ).prod volume)) ≤
      fourCellPositiveHalfRawSameSignEnergy w +
        fourCellPositiveHalfRawReflectedEnergy w (-1) -
          fourCellOddEndpointStripRawEnergy w := by
  have hlowerNonneg : 0 ≤
      ∫ p : ℝ × ℝ in Ico (0 : ℝ) (3 / 5) ×ˢ Ico (0 : ℝ) (3 / 5),
        fourCellOddCoupledRawPair w p
          ∂((volume : Measure ℝ).prod volume) := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem
      (measurableSet_Ico.prod measurableSet_Ico)] with p hp
    unfold fourCellOddCoupledRawPair
    exact add_nonneg (div_nonneg (sq_nonneg _) (abs_nonneg _))
      (div_nonneg (sq_nonneg _) (add_nonneg hp.1.1 hp.2.1))
  have hpartition :=
    lowerSquareBudget_add_two_mul_cross_le_fullRaw_sub_stripRaw
      w hw hodd 0 hlowerNonneg
  simpa only [zero_add] using hpartition

/-! ## A signed regular-kernel reserve on the wider four-cell range -/

private def fourCellRegularLowerPolynomial (r : ℝ) : ℝ :=
  31 * r ^ 7 - 49 * r ^ 6 + 27 * r ^ 5 - 53 * r ^ 4 +
    37 * r ^ 3 - 43 * r ^ 2 + r + 1

private theorem fourCellRegularLowerPolynomial_nonpos
    {r : ℝ} (hr1 : 1 ≤ r) (hr8 : r ≤ 8 / 5) :
    fourCellRegularLowerPolynomial r ≤ 0 := by
  let u : ℝ := (5 / 3 : ℝ) * (r - 1)
  have hu0 : 0 ≤ u := by
    have hr : 0 ≤ r - 1 := sub_nonneg.mpr hr1
    dsimp only [u]
    positivity
  have hu1 : u ≤ 1 := by
    dsimp only [u]
    linarith
  have hone : 0 ≤ 1 - u := sub_nonneg.mpr hu1
  rw [show fourCellRegularLowerPolynomial r =
      -(48 * (1 - u) ^ 7 +
        (2064 / 5 : ℝ) * u * (1 - u) ^ 6 +
        (37296 / 25 : ℝ) * u ^ 2 * (1 - u) ^ 5 +
        2904 * u ^ 3 * (1 - u) ^ 4 +
        (2011008 / 625 : ℝ) * u ^ 4 * (1 - u) ^ 3 +
        (6041808 / 3125 : ℝ) * u ^ 5 * (1 - u) ^ 2 +
        (7870008 / 15625 : ℝ) * u ^ 6 * (1 - u) +
        (788043 / 78125 : ℝ) * u ^ 7) by
    dsimp only [u, fourCellRegularLowerPolynomial]
    ring]
  apply neg_nonpos.mpr
  positivity

/-- The regular kernel remains at least `1 / 5` on every argument produced
by the four-cell positive-half fold.  The proof is structural: the two-term
logarithm lower bound leaves one polynomial, whose Bernstein coefficients
on `1 ≤ exp (t/2) ≤ 8/5` are all negative. -/
theorem one_fifth_le_yoshidaRegularKernel_fourCellRange
    {t : ℝ} (ht0 : 0 ≤ t) (ht4 : t ≤ 5 * Real.log 2 / 4) :
    (1 / 5 : ℝ) ≤ yoshidaRegularKernel t := by
  by_cases ht : t = 0
  · norm_num [yoshidaRegularKernel, ht]
  · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
    let u : ℝ := t / 2
    let r : ℝ := Real.exp u
    have hu0 : 0 ≤ u := by
      dsimp only [u]
      linarith
    have hu7 : u ≤ 7 / 16 := by
      dsimp only [u]
      have hlog := strict_log_two_bounds.2
      linarith
    have hu1 : u ≤ 1 := hu7.trans (by norm_num)
    have hexp := Real.exp_bound' hu0 hu1 (n := 4) (by norm_num)
    norm_num [Finset.sum_range_succ] at hexp
    have hexp8 : Real.exp u ≤ 8 / 5 := by
      calc
        Real.exp u ≤
            1 + u + u ^ 2 / 2 + u ^ 3 / 6 + 5 * u ^ 4 / 96 := by
          linarith
        _ ≤ 1 + (7 / 16 : ℝ) + (7 / 16 : ℝ) ^ 2 / 2 +
            (7 / 16 : ℝ) ^ 3 / 6 +
              5 * (7 / 16 : ℝ) ^ 4 / 96 := by
          gcongr
        _ ≤ 8 / 5 := by norm_num
    have hrpos : 0 < r := by
      dsimp only [r]
      positivity
    have hr1lt : 1 < r := by
      dsimp only [r, u]
      exact Real.one_lt_exp_iff.mpr (by linarith)
    have hr1 : 1 ≤ r := hr1lt.le
    have hr8 : r ≤ 8 / 5 := by
      simpa only [r] using hexp8
    have hrSq : r ^ 2 = Real.exp t := by
      dsimp only [r, u]
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    have hrSqOne : 1 < r ^ 2 := by
      nlinarith [sq_nonneg (r - 1)]
    have hrFourthOne : 1 < r ^ 4 := by
      nlinarith [sq_nonneg (r ^ 2 - 1)]
    let z : ℝ := (r ^ 2 - 1) / (r ^ 2 + 1)
    have hzden : 0 < r ^ 2 + 1 := by positivity
    have hzpos : 0 < z := by
      dsimp only [z]
      exact div_pos (sub_pos.2 hrSqOne) hzden
    have hz0 : 0 ≤ z := hzpos.le
    have hz1 : z < 1 := by
      dsimp only [z]
      rw [div_lt_one hzden]
      linarith
    have hratio : (1 + z) / (1 - z) = r ^ 2 := by
      dsimp only [z]
      field_simp [ne_of_gt hzden]
      ring
    have hseries := Real.sum_range_le_log_div hz0 hz1 2
    norm_num [Finset.sum_range_succ] at hseries
    rw [hratio, hrSq, Real.log_exp] at hseries
    let A : ℝ := z + z ^ 3 / 3
    have hApos : 0 < A := by
      dsimp only [A]
      positivity
    have hAt : 2 * A ≤ t := by
      dsimp only [A]
      linarith
    have hrecip : 1 / (2 * t) ≤ 1 / (4 * A) := by
      rw [div_le_div_iff₀ (by positivity : 0 < 2 * t)
        (by positivity : 0 < 4 * A)]
      nlinarith
    have hP := fourCellRegularLowerPolynomial_nonpos hr1 hr8
    let D : ℝ := 80 * (r + 1) * (r ^ 2 + 1) *
      (r ^ 2 - r + 1) * (r ^ 2 + r + 1)
    have hminus : 0 < r ^ 2 - r + 1 := by
      nlinarith [sq_nonneg (r - 1 / 2)]
    have hplus : 0 < r ^ 2 + r + 1 := by nlinarith
    have hmulMinus : r * (r - 1) + 1 ≠ 0 := by nlinarith
    have hmulPlus : r * (r + 1) + 1 ≠ 0 := by nlinarith
    have hDpos : 0 < D := by
      dsimp only [D]
      positivity
    have hAformula : A =
        4 * (r - 1) * (r + 1) * (r ^ 2 - r + 1) *
          (r ^ 2 + r + 1) / (3 * (r ^ 2 + 1) ^ 3) := by
      dsimp only [A, z]
      field_simp [ne_of_gt hzden]
      ring
    have hremainder :
        0 ≤ r ^ 3 / (r ^ 4 - 1) - 1 / (4 * A) - 1 / 5 := by
      rw [show r ^ 3 / (r ^ 4 - 1) - 1 / (4 * A) - 1 / 5 =
          -fourCellRegularLowerPolynomial r / D by
        rw [hAformula]
        dsimp only [D]
        unfold fourCellRegularLowerPolynomial
        field_simp [ne_of_gt hrpos, ne_of_gt hzden,
          ne_of_gt (sub_pos.2 hrFourthOne), ne_of_gt hApos,
          ne_of_gt (sub_pos.2 hr1lt)]
        field_simp [hmulMinus, hmulPlus]
        ring]
      exact div_nonneg (neg_nonneg.mpr hP) hDpos.le
    have hkernel : yoshidaRegularKernel t =
        r ^ 3 / (r ^ 4 - 1) - 1 / (2 * t) := by
      rw [yoshidaRegularKernel, if_neg ht, Real.sinh_eq, Real.exp_neg,
        ← hrSq]
      change r / (2 * ((r ^ 2 - (r ^ 2)⁻¹) / 2)) - 1 / (2 * t) =
        r ^ 3 / (r ^ 4 - 1) - 1 / (2 * t)
      field_simp [ne_of_gt hrpos, ne_of_gt (sub_pos.2 hrFourthOne)]
    rw [hkernel]
    calc
      (1 / 5 : ℝ) ≤ r ^ 3 / (r ^ 4 - 1) - 1 / (4 * A) := by
        linarith
      _ ≤ r ^ 3 / (r ^ 4 - 1) - 1 / (2 * t) :=
        sub_le_sub_left hrecip _

/-! ## A signed wide moment on the odd ground state -/

private theorem integral_polynomial_nine
    (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ l r : ℝ) :
    (∫ x : ℝ in l..r,
      a₀ * x ^ 0 + a₁ * x ^ 1 + a₂ * x ^ 2 + a₃ * x ^ 3 +
        a₄ * x ^ 4 + a₅ * x ^ 5 + a₆ * x ^ 6 + a₇ * x ^ 7 +
          a₈ * x ^ 8 + a₉ * x ^ 9) =
      a₀ * (r - l) + a₁ * (r ^ 2 - l ^ 2) / 2 +
        a₂ * (r ^ 3 - l ^ 3) / 3 + a₃ * (r ^ 4 - l ^ 4) / 4 +
          a₄ * (r ^ 5 - l ^ 5) / 5 + a₅ * (r ^ 6 - l ^ 6) / 6 +
            a₆ * (r ^ 7 - l ^ 7) / 7 + a₇ * (r ^ 8 - l ^ 8) / 8 +
              a₈ * (r ^ 9 - l ^ 9) / 9 +
                a₉ * (r ^ 10 - l ^ 10) / 10 := by
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) l r)
    (Continuous.intervalIntegrable (by fun_prop) l r)]
  repeat rw [intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  ring

private theorem integral_polynomial_thirteen
    (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ l r : ℝ) :
    (∫ x : ℝ in l..r,
      a₀ * x ^ 0 + a₁ * x ^ 1 + a₂ * x ^ 2 + a₃ * x ^ 3 +
        a₄ * x ^ 4 + a₅ * x ^ 5 + a₆ * x ^ 6 + a₇ * x ^ 7 +
          a₈ * x ^ 8 + a₉ * x ^ 9 + a₁₀ * x ^ 10 +
            a₁₁ * x ^ 11 + a₁₂ * x ^ 12 + a₁₃ * x ^ 13) =
      a₀ * (r - l) + a₁ * (r ^ 2 - l ^ 2) / 2 +
        a₂ * (r ^ 3 - l ^ 3) / 3 + a₃ * (r ^ 4 - l ^ 4) / 4 +
          a₄ * (r ^ 5 - l ^ 5) / 5 + a₅ * (r ^ 6 - l ^ 6) / 6 +
            a₆ * (r ^ 7 - l ^ 7) / 7 + a₇ * (r ^ 8 - l ^ 8) / 8 +
              a₈ * (r ^ 9 - l ^ 9) / 9 +
                a₉ * (r ^ 10 - l ^ 10) / 10 +
                  a₁₀ * (r ^ 11 - l ^ 11) / 11 +
                    a₁₁ * (r ^ 12 - l ^ 12) / 12 +
                      a₁₂ * (r ^ 13 - l ^ 13) / 13 +
                        a₁₃ * (r ^ 14 - l ^ 14) / 14 := by
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) l r)
    (Continuous.intervalIntegrable (by fun_prop) l r)]
  repeat rw [intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  ring

private theorem intervalIntegrable_fourCellRegularKernel_mul_continuous
    (C : ℝ → ℝ) (hC : Continuous C) :
    IntervalIntegrable
      (fun t : ℝ ↦
        yoshidaRegularKernel (fourCellOperatorHalfWidth * t) * C t)
      volume 0 2 := by
  let f : ℝ → ℝ := fun t ↦
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t) * C t
  let g : ℝ → ℝ := fun t ↦ (1 / 4 : ℝ) * |C t|
  have hgIcc : IntegrableOn g (Icc (0 : ℝ) 2) volume := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    exact (continuous_const.mul hC.abs).continuousOn
  have hg : Integrable g (volume.restrict (Ioc (0 : ℝ) 2)) :=
    hgIcc.mono_set Ioc_subset_Icc_self
  have hfmeas : AEStronglyMeasurable f
      (volume.restrict (Ioc (0 : ℝ) 2)) := by
    apply Measurable.aestronglyMeasurable
    dsimp only [f]
    exact (measurable_yoshidaRegularKernel.comp
      (measurable_const.mul measurable_id)).mul hC.measurable
  have hfg : ∀ᵐ t : ℝ ∂(volume.restrict (Ioc (0 : ℝ) 2)),
      ‖f t‖ ≤ g t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have harg0 : 0 ≤ fourCellOperatorHalfWidth * t :=
      mul_nonneg (by unfold fourCellOperatorHalfWidth; positivity) ht.1.le
    have harg4 : fourCellOperatorHalfWidth * t ≤ 5 * Real.log 2 / 4 := by
      have hmul := mul_le_mul_of_nonneg_left ht.2
        (by unfold fourCellOperatorHalfWidth; positivity :
          0 ≤ fourCellOperatorHalfWidth)
      calc
        fourCellOperatorHalfWidth * t ≤
            fourCellOperatorHalfWidth * 2 := hmul
        _ = 5 * Real.log 2 / 4 := by
          unfold fourCellOperatorHalfWidth
          ring
    have hk0 := yoshidaRegularKernel_nonneg_fourCellRange harg0 harg4
    have hk1 := yoshidaRegularKernel_le_quarter harg0
    dsimp only [f, g]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hk0]
    exact mul_le_mul_of_nonneg_right hk1 (abs_nonneg (C t))
  constructor
  · exact Integrable.mono' hg hfmeas hfg
  · simp

/-- The wide regular row is a small mean-zero perturbation on every odd
profile: subtracting the exact constant `1/5` leaves a kernel of size at
most `1/20`, while the absolute autocorrelation has its sharp unit energy
budget. -/
theorem abs_fourCellRegularCorrelation_le_one_twentieth_centeredMass
    (w : ℝ → ℝ) (hw : Continuous w) (hodd : Function.Odd w) :
    |(∫ t : ℝ in 0..2,
        yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
          centeredEndpointCorrelation w t)| ≤
      (1 / 20 : ℝ) * (∫ x : ℝ in -1..1, w x ^ 2) := by
  let C : ℝ → ℝ := centeredEndpointCorrelation w
  let δ : ℝ → ℝ := fun t ↦
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t) - 1 / 5
  have hC : Continuous C :=
    continuous_centeredEndpointCorrelation_of_continuous w hw
  have hCint : IntervalIntegrable C volume 0 2 := hC.intervalIntegrable _ _
  have hKC := intervalIntegrable_fourCellRegularKernel_mul_continuous C hC
  have hconst : IntervalIntegrable (fun t : ℝ ↦ (1 / 5 : ℝ) * C t)
      volume 0 2 := hCint.const_mul (1 / 5)
  have hδC : IntervalIntegrable (fun t : ℝ ↦ δ t * C t)
      volume 0 2 := by
    apply hKC.sub hconst |>.congr
    intro t _ht
    dsimp only [δ]
    ring
  have hmean : (∫ t : ℝ in 0..2, C t) = 0 := by
    simpa only [C] using
      integral_centeredEndpointCorrelation_eq_zero_of_odd w hw hodd
  have hrewrite :
      (∫ t : ℝ in 0..2,
        yoshidaRegularKernel (fourCellOperatorHalfWidth * t) * C t) =
      ∫ t : ℝ in 0..2, δ t * C t := by
    rw [show (fun t : ℝ ↦
        yoshidaRegularKernel (fourCellOperatorHalfWidth * t) * C t) =
      fun t ↦ δ t * C t + (1 / 5 : ℝ) * C t by
      funext t
      dsimp only [δ]
      ring,
      intervalIntegral.integral_add hδC hconst,
      intervalIntegral.integral_const_mul, hmean]
    ring
  have hpoint : ∀ t ∈ Icc (0 : ℝ) 2,
      |δ t * C t| ≤ (1 / 20 : ℝ) * |C t| := by
    intro t ht
    have harg0 : 0 ≤ fourCellOperatorHalfWidth * t :=
      mul_nonneg (by unfold fourCellOperatorHalfWidth; positivity) ht.1
    have harg4 : fourCellOperatorHalfWidth * t ≤ 5 * Real.log 2 / 4 := by
      have hmul := mul_le_mul_of_nonneg_left ht.2
        (by unfold fourCellOperatorHalfWidth; positivity :
          0 ≤ fourCellOperatorHalfWidth)
      calc
        fourCellOperatorHalfWidth * t ≤ fourCellOperatorHalfWidth * 2 := hmul
        _ = 5 * Real.log 2 / 4 := by
          unfold fourCellOperatorHalfWidth
          ring
    have hk0 := one_fifth_le_yoshidaRegularKernel_fourCellRange harg0 harg4
    have hk1 := yoshidaRegularKernel_le_quarter harg0
    have hδ0 : 0 ≤ δ t := by dsimp only [δ]; linarith
    have hδ1 : δ t ≤ (1 / 20 : ℝ) := by dsimp only [δ]; linarith
    rw [abs_mul, abs_of_nonneg hδ0]
    exact mul_le_mul_of_nonneg_right hδ1 (abs_nonneg _)
  have habsInt : IntervalIntegrable (fun t : ℝ ↦ |δ t * C t|)
      volume 0 2 := hδC.abs
  have hmajorInt : IntervalIntegrable (fun t : ℝ ↦
      (1 / 20 : ℝ) * |C t|) volume 0 2 :=
    (hC.abs.intervalIntegrable _ _).const_mul (1 / 20)
  have hmono :
      (∫ t : ℝ in 0..2, |δ t * C t|) ≤
      ∫ t : ℝ in 0..2, (1 / 20 : ℝ) * |C t| := by
    apply intervalIntegral.integral_mono_on (by norm_num) habsInt hmajorInt
    exact hpoint
  have hnorm := intervalIntegral.norm_integral_le_integral_norm
    (by norm_num : (0 : ℝ) ≤ 2) (f := fun t ↦ δ t * C t)
      (μ := volume)
  have hcorr := integral_abs_centeredEndpointCorrelation_le_energy w hw
  rw [intervalIntegral.integral_const_mul] at hmono
  rw [hrewrite]
  simp only [Real.norm_eq_abs] at hnorm
  dsimp only [C] at hcorr ⊢
  linarith

private theorem oddStructuralCorrelation11_nonpos_tail
    {t : ℝ} (ht : t ∈ Icc (8 / 5 : ℝ) 2) :
    oddStructuralCorrelation11 t ≤ 0 := by
  have hfirst : t - 2 ≤ 0 := by linarith [ht.2]
  have hsecond : 0 ≤ t ^ 2 + 2 * t - 2 := by
    nlinarith [sq_nonneg t, ht.1]
  have hmul := mul_nonpos_of_nonpos_of_nonneg hfirst hsecond
  unfold oddStructuralCorrelation11
  nlinarith

theorem integral_regularPolynomial6_mul_oddStructuralCorrelation11_head :
    (∫ t : ℝ in 0..8 / 5,
      yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t) *
        oddStructuralCorrelation11 t) =
      28 / 1875 + (119 / 56250 : ℝ) * Real.log 2 +
        (2 / 625 : ℝ) * Real.log 2 ^ 2 -
          (293 / 5400000 : ℝ) * Real.log 2 ^ 3 -
            (1 / 4000 : ℝ) * Real.log 2 ^ 4 +
              (30473 / 28576800000 : ℝ) * Real.log 2 ^ 5 +
                (29219 / 1512000000 : ℝ) * Real.log 2 ^ 6 := by
  rw [show (fun t : ℝ ↦
      yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t) *
        oddStructuralCorrelation11 t) =
      fun t ↦
        (1 / 6 : ℝ) * t ^ 0 +
        (-(1 / 4) - (5 / 576 : ℝ) * Real.log 2) * t ^ 1 +
        ((5 / 384 : ℝ) * Real.log 2 -
          (25 / 3072 : ℝ) * Real.log 2 ^ 2) * t ^ 2 +
        ((1 / 24 : ℝ) + (25 / 2048 : ℝ) * Real.log 2 ^ 2 +
          (175 / 1769472 : ℝ) * Real.log 2 ^ 3) * t ^ 3 +
        (-(5 / 2304 : ℝ) * Real.log 2 -
          (175 / 1179648 : ℝ) * Real.log 2 ^ 3 +
            (3125 / 9437184 : ℝ) * Real.log 2 ^ 4) * t ^ 4 +
        (-(25 / 12288 : ℝ) * Real.log 2 ^ 2 -
          (3125 / 6291456 : ℝ) * Real.log 2 ^ 4 -
            (19375 / 19025362944 : ℝ) * Real.log 2 ^ 5) * t ^ 5 +
        ((175 / 7077888 : ℝ) * Real.log 2 ^ 3 +
          (19375 / 12683575296 : ℝ) * Real.log 2 ^ 5 -
            (190625 / 14495514624 : ℝ) * Real.log 2 ^ 6) * t ^ 6 +
        ((3125 / 37748736 : ℝ) * Real.log 2 ^ 4 +
          (190625 / 9663676416 : ℝ) * Real.log 2 ^ 6) * t ^ 7 +
        (-(19375 / 76101451776 : ℝ) * Real.log 2 ^ 5) * t ^ 8 +
        (-(190625 / 57982058496 : ℝ) * Real.log 2 ^ 6) * t ^ 9 by
    funext t
    unfold yoshidaRegularKernelPolynomial6 fourCellOperatorHalfWidth
      oddStructuralCorrelation11
    ring,
    integral_polynomial_nine]
  ring

theorem integral_one_fifth_mul_oddStructuralCorrelation11_tail :
    (∫ t : ℝ in 8 / 5..2,
      (1 / 5 : ℝ) * oddStructuralCorrelation11 t) =
      (-112 / 9375 : ℝ) := by
  rw [show (fun t : ℝ ↦
      (1 / 5 : ℝ) * oddStructuralCorrelation11 t) =
      fun t ↦ (2 / 15 : ℝ) * t ^ 0 + (-1 / 5 : ℝ) * t ^ 1 +
        0 * t ^ 2 + (1 / 30 : ℝ) * t ^ 3 + 0 * t ^ 4 +
          0 * t ^ 5 + 0 * t ^ 6 + 0 * t ^ 7 + 0 * t ^ 8 +
            0 * t ^ 9 by
    funext t
    unfold oddStructuralCorrelation11
    ring,
    integral_polynomial_nine]
  norm_num

private theorem fourCellOddLowRegular11_model_le :
    (∫ t : ℝ in 0..8 / 5,
        yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t) *
          oddStructuralCorrelation11 t) +
      ∫ t : ℝ in 8 / 5..2,
        (1 / 5 : ℝ) * oddStructuralCorrelation11 t ≤
      (2997 / 500000 : ℝ) := by
  rw [integral_regularPolynomial6_mul_oddStructuralCorrelation11_head,
    integral_one_fifth_mul_oddStructuralCorrelation11_tail]
  let L₁ : ℝ := 6932 / 10000
  have hL0 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have hL1 : Real.log 2 ≤ L₁ := by
    dsimp only [L₁]
    exact strict_log_two_bounds.2.le
  have hpow2 := pow_le_pow_left₀ hL0 hL1 2
  have hpow5 := pow_le_pow_left₀ hL0 hL1 5
  have hpow6 := pow_le_pow_left₀ hL0 hL1 6
  have hpow3 : 0 ≤ Real.log 2 ^ 3 := pow_nonneg hL0 3
  have hpow4 : 0 ≤ Real.log 2 ^ 4 := pow_nonneg hL0 4
  have hdrop :
      28 / 1875 + (119 / 56250 : ℝ) * Real.log 2 +
          (2 / 625 : ℝ) * Real.log 2 ^ 2 -
            (293 / 5400000 : ℝ) * Real.log 2 ^ 3 -
              (1 / 4000 : ℝ) * Real.log 2 ^ 4 +
                (30473 / 28576800000 : ℝ) * Real.log 2 ^ 5 +
                  (29219 / 1512000000 : ℝ) * Real.log 2 ^ 6 -
                    112 / 9375 ≤
        28 / 1875 + (119 / 56250 : ℝ) * Real.log 2 +
          (2 / 625 : ℝ) * Real.log 2 ^ 2 +
            (30473 / 28576800000 : ℝ) * Real.log 2 ^ 5 +
              (29219 / 1512000000 : ℝ) * Real.log 2 ^ 6 -
                112 / 9375 := by
    nlinarith
  have hmono :
    28 / 1875 + (119 / 56250 : ℝ) * Real.log 2 +
          (2 / 625 : ℝ) * Real.log 2 ^ 2 +
            (30473 / 28576800000 : ℝ) * Real.log 2 ^ 5 +
              (29219 / 1512000000 : ℝ) * Real.log 2 ^ 6 -
                112 / 9375 ≤
        28 / 1875 + (119 / 56250 : ℝ) * L₁ +
          (2 / 625 : ℝ) * L₁ ^ 2 +
            (30473 / 28576800000 : ℝ) * L₁ ^ 5 +
              (29219 / 1512000000 : ℝ) * L₁ ^ 6 -
                112 / 9375 := by gcongr
  have hrat :
      28 / 1875 + (119 / 56250 : ℝ) * L₁ +
          (2 / 625 : ℝ) * L₁ ^ 2 +
            (30473 / 28576800000 : ℝ) * L₁ ^ 5 +
              (29219 / 1512000000 : ℝ) * L₁ ^ 6 -
                112 / 9375 ≤ 2997 / 500000 := by
    norm_num [L₁]
  have hfinal := hdrop.trans (hmono.trans hrat)
  convert hfinal using 1
  ring

/-- The exact wide regular moment of the odd ground state is still below
`3 / 500`.  The proof uses the sixth-order analytic envelope only on its
natural head interval and retains the signed kernel tail through the
structural lower bound `K ≥ 1 / 5`. -/
theorem integral_yoshidaRegularKernel_mul_oddStructuralCorrelation11_le :
    (∫ t : ℝ in 0..2,
      yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
        oddStructuralCorrelation11 t) ≤ (3 / 500 : ℝ) := by
  let C : ℝ → ℝ := oddStructuralCorrelation11
  let K : ℝ → ℝ := fun t ↦
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t)
  let P : ℝ → ℝ := fun t ↦
    yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t)
  let ε : ℝ := 1 / 500000
  have hC : Continuous C := by
    dsimp only [C]
    unfold oddStructuralCorrelation11
    fun_prop
  have hP : Continuous P := by
    dsimp only [P]
    unfold yoshidaRegularKernelPolynomial6
    fun_prop
  have hfull : IntervalIntegrable (fun t : ℝ ↦ K t * C t)
      volume 0 2 := by
    simpa only [K, C] using
      intervalIntegrable_fourCellRegularKernel_mul_continuous C hC
  have hleft : IntervalIntegrable (fun t : ℝ ↦ K t * C t)
      volume 0 (8 / 5) :=
    hfull.mono_set (by
      intro t ht
      norm_num at ht ⊢
      constructor <;> linarith :
        uIcc (0 : ℝ) (8 / 5) ⊆ uIcc (0 : ℝ) 2)
  have htail : IntervalIntegrable (fun t : ℝ ↦ K t * C t)
      volume (8 / 5) 2 :=
    hfull.mono_set (by
      intro t ht
      norm_num at ht ⊢
      constructor <;> linarith :
        uIcc (8 / 5 : ℝ) 2 ⊆ uIcc (0 : ℝ) 2)
  have hpoly : IntervalIntegrable (fun t : ℝ ↦ P t * C t)
      volume 0 (8 / 5) := (hP.mul hC).intervalIntegrable _ _
  have herr : IntervalIntegrable (fun t : ℝ ↦ ε * |C t|)
      volume 0 (8 / 5) :=
    (continuous_const.mul hC.abs).intervalIntegrable _ _
  have hmajor : IntervalIntegrable
      (fun t : ℝ ↦ P t * C t + ε * |C t|)
      volume 0 (8 / 5) := hpoly.add herr
  have hleftMono :
      (∫ t : ℝ in 0..8 / 5, K t * C t) ≤
        ∫ t : ℝ in 0..8 / 5, P t * C t + ε * |C t| := by
    apply intervalIntegral.integral_mono_on (by norm_num) hleft hmajor
    intro t ht
    have harg0 : 0 ≤ fourCellOperatorHalfWidth * t :=
      mul_nonneg (by unfold fourCellOperatorHalfWidth; positivity) ht.1
    have hargLog : fourCellOperatorHalfWidth * t ≤ Real.log 2 := by
      have hmul := mul_le_mul_of_nonneg_left ht.2
        (by unfold fourCellOperatorHalfWidth; positivity :
          0 ≤ fourCellOperatorHalfWidth)
      calc
        fourCellOperatorHalfWidth * t ≤
            fourCellOperatorHalfWidth * (8 / 5) := hmul
        _ = Real.log 2 := by
          unfold fourCellOperatorHalfWidth
          ring
    have henv := yoshidaRegularKernelPolynomial6_envelope harg0 hargLog
    calc
      K t * C t = P t * C t + (K t - P t) * C t := by ring
      _ ≤ P t * C t + |(K t - P t) * C t| := by
        linarith [le_abs_self ((K t - P t) * C t)]
      _ = P t * C t + |K t - P t| * |C t| := by rw [abs_mul]
      _ ≤ P t * C t + ε * |C t| := by
        gcongr
        rw [abs_of_nonneg]
        · simpa only [K, P, ε] using henv.2.le
        · simpa only [K, P] using henv.1
  have htailMajor : IntervalIntegrable
      (fun t : ℝ ↦ (1 / 5 : ℝ) * C t) volume (8 / 5) 2 :=
    (continuous_const.mul hC).intervalIntegrable _ _
  have htailMono :
      (∫ t : ℝ in 8 / 5..2, K t * C t) ≤
        ∫ t : ℝ in 8 / 5..2, (1 / 5 : ℝ) * C t := by
    apply intervalIntegral.integral_mono_on (by norm_num) htail htailMajor
    intro t ht
    have harg0 : 0 ≤ fourCellOperatorHalfWidth * t :=
      mul_nonneg (by unfold fourCellOperatorHalfWidth; positivity)
        (by linarith [ht.1])
    have harg4 : fourCellOperatorHalfWidth * t ≤
        5 * Real.log 2 / 4 := by
      have hmul := mul_le_mul_of_nonneg_left ht.2
        (by unfold fourCellOperatorHalfWidth; positivity :
          0 ≤ fourCellOperatorHalfWidth)
      calc
        fourCellOperatorHalfWidth * t ≤
            fourCellOperatorHalfWidth * 2 := hmul
        _ = 5 * Real.log 2 / 4 := by
          unfold fourCellOperatorHalfWidth
          ring
    have hk : (1 / 5 : ℝ) ≤ K t := by
      dsimp only [K]
      exact one_fifth_le_yoshidaRegularKernel_fourCellRange harg0 harg4
    have hCt : C t ≤ 0 := by
      dsimp only [C]
      exact oddStructuralCorrelation11_nonpos_tail ht
    exact mul_le_mul_of_nonpos_right hk hCt
  have habsSub :
      (∫ t : ℝ in 0..8 / 5, |C t|) ≤
        ∫ t : ℝ in 0..2, |C t| := by
    apply intervalIntegral.integral_mono_interval
      (c := (0 : ℝ)) (d := 2) le_rfl (by norm_num) (by norm_num)
    · filter_upwards with t
      exact abs_nonneg (C t)
    · exact hC.abs.intervalIntegrable _ _
  have habsFull :
      (∫ t : ℝ in 0..2, |C t|) ≤ (2 / 3 : ℝ) := by
    simpa only [C] using integral_abs_oddStructuralCorrelation11_le
  have hmajorEq :
      (∫ t : ℝ in 0..8 / 5, P t * C t + ε * |C t|) =
        (∫ t : ℝ in 0..8 / 5, P t * C t) +
          ε * ∫ t : ℝ in 0..8 / 5, |C t| := by
    rw [intervalIntegral.integral_add hpoly herr,
      intervalIntegral.integral_const_mul]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hleft htail
  calc
    (∫ t : ℝ in 0..2,
        yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
          oddStructuralCorrelation11 t) =
        (∫ t : ℝ in 0..8 / 5, K t * C t) +
          ∫ t : ℝ in 8 / 5..2, K t * C t := by
      simpa only [K, C] using hsplit.symm
    _ ≤ (∫ t : ℝ in 0..8 / 5, P t * C t + ε * |C t|) +
          ∫ t : ℝ in 8 / 5..2, (1 / 5 : ℝ) * C t :=
      add_le_add hleftMono htailMono
    _ = ((∫ t : ℝ in 0..8 / 5, P t * C t) +
          ∫ t : ℝ in 8 / 5..2, (1 / 5 : ℝ) * C t) +
        ε * ∫ t : ℝ in 0..8 / 5, |C t| := by
      rw [hmajorEq]
      ring
    _ ≤ (2997 / 500000 : ℝ) + (1 / 500000) * (2 / 3) := by
      apply add_le_add
      · simpa only [P, C] using fourCellOddLowRegular11_model_le
      · dsimp only [ε]
        exact mul_le_mul_of_nonneg_left (habsSub.trans habsFull) (by norm_num)
    _ ≤ 3 / 500 := by norm_num

/-- Uniform integral form of the sixth-order envelope on its natural
four-cell head interval.  It is stated symmetrically so that the same lemma
controls both signs of the polarized odd correlation. -/
private theorem abs_fourCellRegularKernel_head_sub_polynomial_le
    (C : ℝ → ℝ) (hC : Continuous C) :
    |(∫ t : ℝ in 0..8 / 5,
        yoshidaRegularKernel (fourCellOperatorHalfWidth * t) * C t) -
      ∫ t : ℝ in 0..8 / 5,
        yoshidaRegularKernelPolynomial6
          (fourCellOperatorHalfWidth * t) * C t| ≤
      (1 / 500000 : ℝ) * ∫ t : ℝ in 0..8 / 5, |C t| := by
  let K : ℝ → ℝ := fun t ↦
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t)
  let P : ℝ → ℝ := fun t ↦
    yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t)
  let f : ℝ → ℝ := fun t ↦ K t * C t - P t * C t
  let g : ℝ → ℝ := fun t ↦ (1 / 500000 : ℝ) * |C t|
  have hKfull : IntervalIntegrable (fun t : ℝ ↦ K t * C t)
      volume 0 2 := by
    simpa only [K] using
      intervalIntegrable_fourCellRegularKernel_mul_continuous C hC
  have hK : IntervalIntegrable (fun t : ℝ ↦ K t * C t)
      volume 0 (8 / 5) :=
    hKfull.mono_set (by
      intro t ht
      norm_num at ht ⊢
      constructor <;> linarith :
        uIcc (0 : ℝ) (8 / 5) ⊆ uIcc (0 : ℝ) 2)
  have hPcont : Continuous P := by
    dsimp only [P]
    unfold yoshidaRegularKernelPolynomial6
    fun_prop
  have hP : IntervalIntegrable (fun t : ℝ ↦ P t * C t)
      volume 0 (8 / 5) := (hPcont.mul hC).intervalIntegrable _ _
  have hf : IntervalIntegrable f volume 0 (8 / 5) := by
    dsimp only [f]
    exact hK.sub hP
  have hg : IntervalIntegrable g volume 0 (8 / 5) := by
    dsimp only [g]
    exact (continuous_const.mul hC.abs).intervalIntegrable _ _
  have hmono :
      (∫ t : ℝ in 0..8 / 5, |f t|) ≤
        ∫ t : ℝ in 0..8 / 5, g t := by
    apply intervalIntegral.integral_mono_on (by norm_num) hf.abs hg
    intro t ht
    have harg0 : 0 ≤ fourCellOperatorHalfWidth * t :=
      mul_nonneg (by unfold fourCellOperatorHalfWidth; positivity) ht.1
    have hargLog : fourCellOperatorHalfWidth * t ≤ Real.log 2 := by
      have hmul := mul_le_mul_of_nonneg_left ht.2
        (by unfold fourCellOperatorHalfWidth; positivity :
          0 ≤ fourCellOperatorHalfWidth)
      calc
        fourCellOperatorHalfWidth * t ≤
            fourCellOperatorHalfWidth * (8 / 5) := hmul
        _ = Real.log 2 := by
          unfold fourCellOperatorHalfWidth
          ring
    have henv := yoshidaRegularKernelPolynomial6_envelope harg0 hargLog
    dsimp only [f, g, K, P]
    rw [show
        yoshidaRegularKernel (fourCellOperatorHalfWidth * t) * C t -
            yoshidaRegularKernelPolynomial6
              (fourCellOperatorHalfWidth * t) * C t =
          (yoshidaRegularKernel (fourCellOperatorHalfWidth * t) -
            yoshidaRegularKernelPolynomial6
              (fourCellOperatorHalfWidth * t)) * C t by ring,
      abs_mul, abs_of_nonneg henv.1]
    exact mul_le_mul_of_nonneg_right henv.2.le (abs_nonneg (C t))
  calc
    |(∫ t : ℝ in 0..8 / 5,
        yoshidaRegularKernel (fourCellOperatorHalfWidth * t) * C t) -
      ∫ t : ℝ in 0..8 / 5,
        yoshidaRegularKernelPolynomial6
          (fourCellOperatorHalfWidth * t) * C t| =
        |∫ t : ℝ in 0..8 / 5, f t| := by
      dsimp only [f, K, P]
      rw [intervalIntegral.integral_sub hK hP]
    _ ≤ ∫ t : ℝ in 0..8 / 5, |f t| :=
      intervalIntegral.abs_integral_le_integral_abs (by norm_num)
    _ ≤ ∫ t : ℝ in 0..8 / 5, g t := hmono
    _ = (1 / 500000 : ℝ) *
        ∫ t : ℝ in 0..8 / 5, |C t| := by
      dsimp only [g]
      rw [intervalIntegral.integral_const_mul]

private theorem oddStructuralCorrelation13_nonpos_tail
    {t : ℝ} (ht : t ∈ Icc (8 / 5 : ℝ) 2) :
    oddStructuralCorrelation13 t ≤ 0 := by
  let u : ℝ := t - 8 / 5
  have hu : 0 ≤ u := by
    dsimp only [u]
    linarith [ht.1]
  have hq : 0 ≤ t ^ 3 + 2 * t ^ 2 - 8 * t + 4 := by
    rw [show t ^ 3 + 2 * t ^ 2 - 8 * t + 4 =
        52 / 125 + (152 / 25 : ℝ) * u +
          (34 / 5 : ℝ) * u ^ 2 + u ^ 3 by
      dsimp only [u]
      ring]
    positivity
  have ht0 : 0 ≤ t := by linarith [ht.1]
  have ht2 : t - 2 ≤ 0 := by linarith [ht.2]
  have hprod : t * (t - 2) *
      (t ^ 3 + 2 * t ^ 2 - 8 * t + 4) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos ht0 ht2) hq
  unfold oddStructuralCorrelation13
  nlinarith

theorem integral_regularPolynomial6_mul_oddStructuralCorrelation13_head :
    (∫ t : ℝ in 0..8 / 5,
      yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t) *
        oddStructuralCorrelation13 t) =
      296 / 46875 - (824 / 984375 : ℝ) * Real.log 2 -
        (31 / 31250 : ℝ) * Real.log 2 ^ 2 +
          (359 / 25312500 : ℝ) * Real.log 2 ^ 3 +
            (877 / 15750000 : ℝ) * Real.log 2 ^ 4 -
              (44299 / 218295000000 : ℝ) * Real.log 2 ^ 5 -
                (10187 / 3240000000 : ℝ) * Real.log 2 ^ 6 := by
  rw [show (fun t : ℝ ↦
      yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t) *
        oddStructuralCorrelation13 t) =
      fun t ↦
        0 * t ^ 0 + (-1 / 4 : ℝ) * t ^ 1 +
        ((5 / 8 : ℝ) + (5 / 384 : ℝ) * Real.log 2) * t ^ 2 +
        (-(3 / 8 : ℝ) - (25 / 768 : ℝ) * Real.log 2 +
          (25 / 2048 : ℝ) * Real.log 2 ^ 2) * t ^ 3 +
        ((5 / 256 : ℝ) * Real.log 2 -
          (125 / 4096 : ℝ) * Real.log 2 ^ 2 -
            (175 / 1179648 : ℝ) * Real.log 2 ^ 3) * t ^ 4 +
        ((1 / 32 : ℝ) + (75 / 4096 : ℝ) * Real.log 2 ^ 2 +
          (875 / 2359296 : ℝ) * Real.log 2 ^ 3 -
            (3125 / 6291456 : ℝ) * Real.log 2 ^ 4) * t ^ 5 +
        (-(5 / 3072 : ℝ) * Real.log 2 -
          (175 / 786432 : ℝ) * Real.log 2 ^ 3 +
            (15625 / 12582912 : ℝ) * Real.log 2 ^ 4 +
              (19375 / 12683575296 : ℝ) * Real.log 2 ^ 5) * t ^ 6 +
        (-(25 / 16384 : ℝ) * Real.log 2 ^ 2 -
          (3125 / 4194304 : ℝ) * Real.log 2 ^ 4 -
            (96875 / 25367150592 : ℝ) * Real.log 2 ^ 5 +
              (190625 / 9663676416 : ℝ) * Real.log 2 ^ 6) * t ^ 7 +
        ((175 / 9437184 : ℝ) * Real.log 2 ^ 3 +
          (19375 / 8455716864 : ℝ) * Real.log 2 ^ 5 -
            (953125 / 19327352832 : ℝ) * Real.log 2 ^ 6) * t ^ 8 +
        ((3125 / 50331648 : ℝ) * Real.log 2 ^ 4 +
          (190625 / 6442450944 : ℝ) * Real.log 2 ^ 6) * t ^ 9 +
        (-(19375 / 101468602368 : ℝ) * Real.log 2 ^ 5) * t ^ 10 +
        (-(190625 / 77309411328 : ℝ) * Real.log 2 ^ 6) * t ^ 11 +
        0 * t ^ 12 + 0 * t ^ 13 by
    funext t
    unfold yoshidaRegularKernelPolynomial6 fourCellOperatorHalfWidth
      oddStructuralCorrelation13
    ring,
    integral_polynomial_thirteen]
  ring

theorem integral_oddStructuralCorrelation13_tail :
    (∫ t : ℝ in 8 / 5..2, oddStructuralCorrelation13 t) =
      (-1184 / 46875 : ℝ) := by
  rw [show oddStructuralCorrelation13 = fun t : ℝ ↦
      0 * t ^ 0 + (-1 : ℝ) * t ^ 1 + (5 / 2 : ℝ) * t ^ 2 -
        (3 / 2 : ℝ) * t ^ 3 + 0 * t ^ 4 + (1 / 8 : ℝ) * t ^ 5 +
          0 * t ^ 6 + 0 * t ^ 7 + 0 * t ^ 8 + 0 * t ^ 9 +
            0 * t ^ 10 + 0 * t ^ 11 + 0 * t ^ 12 + 0 * t ^ 13 by
    funext t
    unfold oddStructuralCorrelation13
    ring]
  simp only
  rw [show (fun t : ℝ ↦
      0 * t ^ 0 + (-1 : ℝ) * t ^ 1 + (5 / 2 : ℝ) * t ^ 2 -
        (3 / 2 : ℝ) * t ^ 3 + 0 * t ^ 4 + (1 / 8 : ℝ) * t ^ 5 +
          0 * t ^ 6 + 0 * t ^ 7 + 0 * t ^ 8 + 0 * t ^ 9 +
            0 * t ^ 10 + 0 * t ^ 11 + 0 * t ^ 12 + 0 * t ^ 13) =
      fun t ↦
        0 * t ^ 0 + (-1 : ℝ) * t ^ 1 + (5 / 2 : ℝ) * t ^ 2 +
          (-3 / 2 : ℝ) * t ^ 3 + 0 * t ^ 4 + (1 / 8 : ℝ) * t ^ 5 +
            0 * t ^ 6 + 0 * t ^ 7 + 0 * t ^ 8 + 0 * t ^ 9 +
              0 * t ^ 10 + 0 * t ^ 11 + 0 * t ^ 12 + 0 * t ^ 13 by
    funext t
    ring,
    integral_polynomial_thirteen]
  norm_num

private theorem fourCellOddLowRegular13_upper_model :
    (∫ t : ℝ in 0..8 / 5,
        yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t) *
          oddStructuralCorrelation13 t) +
      (1 / 5 : ℝ) *
        (∫ t : ℝ in 8 / 5..2, oddStructuralCorrelation13 t) +
      (1 / 500000 : ℝ) * (1 / 6) ≤
        (21 / 20000 : ℝ) := by
  rw [integral_regularPolynomial6_mul_oddStructuralCorrelation13_head,
    integral_oddStructuralCorrelation13_tail]
  let L₀ : ℝ := 6931 / 10000
  let L₁ : ℝ := 6932 / 10000
  have hL0 : L₀ ≤ Real.log 2 := by
    dsimp only [L₀]
    exact strict_log_two_bounds.1.le
  have hL1 : Real.log 2 ≤ L₁ := by
    dsimp only [L₁]
    exact strict_log_two_bounds.2.le
  have hlog0 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have hlo2 := pow_le_pow_left₀ (by norm_num : 0 ≤ L₀) hL0 2
  have hlo3 := pow_le_pow_left₀ (by norm_num : 0 ≤ L₀) hL0 3
  have hlo4 := pow_le_pow_left₀ (by norm_num : 0 ≤ L₀) hL0 4
  have hlo5 := pow_le_pow_left₀ (by norm_num : 0 ≤ L₀) hL0 5
  have hlo6 := pow_le_pow_left₀ (by norm_num : 0 ≤ L₀) hL0 6
  have hup2 := pow_le_pow_left₀ hlog0 hL1 2
  have hup3 := pow_le_pow_left₀ hlog0 hL1 3
  have hup4 := pow_le_pow_left₀ hlog0 hL1 4
  have hup5 := pow_le_pow_left₀ hlog0 hL1 5
  have hup6 := pow_le_pow_left₀ hlog0 hL1 6
  have hrat :
      296 / 46875 - (824 / 984375 : ℝ) * L₀ -
          (31 / 31250 : ℝ) * L₀ ^ 2 +
            (359 / 25312500 : ℝ) * L₁ ^ 3 +
              (877 / 15750000 : ℝ) * L₁ ^ 4 -
                (44299 / 218295000000 : ℝ) * L₀ ^ 5 -
                  (10187 / 3240000000 : ℝ) * L₀ ^ 6 +
                    (1 / 5 : ℝ) * (-1184 / 46875) +
                      (1 / 500000 : ℝ) * (1 / 6) ≤
        21 / 20000 := by
    norm_num [L₀, L₁]
  apply le_trans ?_ hrat
  gcongr

private theorem fourCellOddLowRegular13_lower_model :
    (-21 / 20000 : ℝ) ≤
      (∫ t : ℝ in 0..8 / 5,
        yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t) *
          oddStructuralCorrelation13 t) +
      (1 / 4 : ℝ) *
        (∫ t : ℝ in 8 / 5..2, oddStructuralCorrelation13 t) -
      (1 / 500000 : ℝ) * (1 / 6) := by
  rw [integral_regularPolynomial6_mul_oddStructuralCorrelation13_head,
    integral_oddStructuralCorrelation13_tail]
  let L₀ : ℝ := 6931 / 10000
  let L₁ : ℝ := 6932 / 10000
  have hL0 : L₀ ≤ Real.log 2 := by
    dsimp only [L₀]
    exact strict_log_two_bounds.1.le
  have hL1 : Real.log 2 ≤ L₁ := by
    dsimp only [L₁]
    exact strict_log_two_bounds.2.le
  have hlog0 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have hlo2 := pow_le_pow_left₀ (by norm_num : 0 ≤ L₀) hL0 2
  have hlo3 := pow_le_pow_left₀ (by norm_num : 0 ≤ L₀) hL0 3
  have hlo4 := pow_le_pow_left₀ (by norm_num : 0 ≤ L₀) hL0 4
  have hlo5 := pow_le_pow_left₀ (by norm_num : 0 ≤ L₀) hL0 5
  have hlo6 := pow_le_pow_left₀ (by norm_num : 0 ≤ L₀) hL0 6
  have hup2 := pow_le_pow_left₀ hlog0 hL1 2
  have hup3 := pow_le_pow_left₀ hlog0 hL1 3
  have hup4 := pow_le_pow_left₀ hlog0 hL1 4
  have hup5 := pow_le_pow_left₀ hlog0 hL1 5
  have hup6 := pow_le_pow_left₀ hlog0 hL1 6
  have hrat :
      (-21 / 20000 : ℝ) ≤
        296 / 46875 - (824 / 984375 : ℝ) * L₁ -
          (31 / 31250 : ℝ) * L₁ ^ 2 +
            (359 / 25312500 : ℝ) * L₀ ^ 3 +
              (877 / 15750000 : ℝ) * L₀ ^ 4 -
                (44299 / 218295000000 : ℝ) * L₁ ^ 5 -
                  (10187 / 3240000000 : ℝ) * L₁ ^ 6 +
                    (1 / 4 : ℝ) * (-1184 / 46875) -
                      (1 / 500000 : ℝ) * (1 / 6) := by
    norm_num [L₀, L₁]
  apply hrat.trans
  gcongr

/-- The polarized wide regular moment remains uniformly tiny.  Its head is
controlled symmetrically by the analytic envelope, while its whole tail has
one sign, so the kernel interval `1 / 5 ≤ K ≤ 1 / 4` gives both sides
without locating any roots. -/
theorem abs_integral_yoshidaRegularKernel_mul_oddStructuralCorrelation13_le :
    |(∫ t : ℝ in 0..2,
      yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
        oddStructuralCorrelation13 t)| ≤ (21 / 20000 : ℝ) := by
  let C : ℝ → ℝ := oddStructuralCorrelation13
  let K : ℝ → ℝ := fun t ↦
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t)
  let P : ℝ → ℝ := fun t ↦
    yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t)
  have hC : Continuous C := by
    dsimp only [C]
    unfold oddStructuralCorrelation13
    fun_prop
  have hfull : IntervalIntegrable (fun t : ℝ ↦ K t * C t)
      volume 0 2 := by
    simpa only [K] using
      intervalIntegrable_fourCellRegularKernel_mul_continuous C hC
  have hhead : IntervalIntegrable (fun t : ℝ ↦ K t * C t)
      volume 0 (8 / 5) :=
    hfull.mono_set (by
      intro t ht
      norm_num at ht ⊢
      constructor <;> linarith :
        uIcc (0 : ℝ) (8 / 5) ⊆ uIcc (0 : ℝ) 2)
  have htail : IntervalIntegrable (fun t : ℝ ↦ K t * C t)
      volume (8 / 5) 2 :=
    hfull.mono_set (by
      intro t ht
      norm_num at ht ⊢
      constructor <;> linarith :
        uIcc (8 / 5 : ℝ) 2 ⊆ uIcc (0 : ℝ) 2)
  have hPcont : Continuous P := by
    dsimp only [P]
    unfold yoshidaRegularKernelPolynomial6
    fun_prop
  have hP : IntervalIntegrable (fun t : ℝ ↦ P t * C t)
      volume 0 (8 / 5) := (hPcont.mul hC).intervalIntegrable _ _
  have habsSub :
      (∫ t : ℝ in 0..8 / 5, |C t|) ≤ (1 / 6 : ℝ) := by
    have hmono :
        (∫ t : ℝ in 0..8 / 5, |C t|) ≤
          ∫ t : ℝ in 0..2, |C t| := by
      apply intervalIntegral.integral_mono_interval
        (c := (0 : ℝ)) (d := 2) le_rfl (by norm_num) (by norm_num)
      · filter_upwards with t
        exact abs_nonneg (C t)
      · exact hC.abs.intervalIntegrable _ _
    have hfullAbs :
        (∫ t : ℝ in 0..2, |C t|) < (1 / 6 : ℝ) := by
      simpa only [C] using integral_abs_oddStructuralCorrelation13_lt
    exact hmono.trans hfullAbs.le
  have hheadError :
      |(∫ t : ℝ in 0..8 / 5, K t * C t) -
        ∫ t : ℝ in 0..8 / 5, P t * C t| ≤
          (1 / 500000 : ℝ) *
            ∫ t : ℝ in 0..8 / 5, |C t| := by
    simpa only [K, P] using
      abs_fourCellRegularKernel_head_sub_polynomial_le C hC
  have hheadUpper :
      (∫ t : ℝ in 0..8 / 5, K t * C t) ≤
        (∫ t : ℝ in 0..8 / 5, P t * C t) +
          (1 / 500000 : ℝ) * (1 / 6) := by
    have herr := (abs_le.mp hheadError).2
    have hbudget := mul_le_mul_of_nonneg_left habsSub (by norm_num :
      (0 : ℝ) ≤ 1 / 500000)
    linarith
  have hheadLower :
      (∫ t : ℝ in 0..8 / 5, P t * C t) -
          (1 / 500000 : ℝ) * (1 / 6) ≤
        ∫ t : ℝ in 0..8 / 5, K t * C t := by
    have herr := (abs_le.mp hheadError).1
    have hbudget := mul_le_mul_of_nonneg_left habsSub (by norm_num :
      (0 : ℝ) ≤ 1 / 500000)
    linarith
  have htailFifth : IntervalIntegrable
      (fun t : ℝ ↦ (1 / 5 : ℝ) * C t) volume (8 / 5) 2 :=
    (continuous_const.mul hC).intervalIntegrable _ _
  have htailQuarter : IntervalIntegrable
      (fun t : ℝ ↦ (1 / 4 : ℝ) * C t) volume (8 / 5) 2 :=
    (continuous_const.mul hC).intervalIntegrable _ _
  have htailUpper :
      (∫ t : ℝ in 8 / 5..2, K t * C t) ≤
        (1 / 5 : ℝ) * ∫ t : ℝ in 8 / 5..2, C t := by
    calc
      (∫ t : ℝ in 8 / 5..2, K t * C t) ≤
          ∫ t : ℝ in 8 / 5..2, (1 / 5 : ℝ) * C t := by
        apply intervalIntegral.integral_mono_on
          (by norm_num) htail htailFifth
        intro t ht
        have harg0 : 0 ≤ fourCellOperatorHalfWidth * t :=
          mul_nonneg (by unfold fourCellOperatorHalfWidth; positivity)
            (by linarith [ht.1])
        have harg4 : fourCellOperatorHalfWidth * t ≤
            5 * Real.log 2 / 4 := by
          have hmul := mul_le_mul_of_nonneg_left ht.2
            (by unfold fourCellOperatorHalfWidth; positivity :
              0 ≤ fourCellOperatorHalfWidth)
          calc
            fourCellOperatorHalfWidth * t ≤
                fourCellOperatorHalfWidth * 2 := hmul
            _ = 5 * Real.log 2 / 4 := by
              unfold fourCellOperatorHalfWidth
              ring
        have hk : (1 / 5 : ℝ) ≤ K t := by
          dsimp only [K]
          exact one_fifth_le_yoshidaRegularKernel_fourCellRange harg0 harg4
        have hCt : C t ≤ 0 := by
          dsimp only [C]
          exact oddStructuralCorrelation13_nonpos_tail ht
        exact mul_le_mul_of_nonpos_right hk hCt
      _ = (1 / 5 : ℝ) * ∫ t : ℝ in 8 / 5..2, C t := by
        rw [intervalIntegral.integral_const_mul]
  have htailLower :
      (1 / 4 : ℝ) * ∫ t : ℝ in 8 / 5..2, C t ≤
        ∫ t : ℝ in 8 / 5..2, K t * C t := by
    calc
      (1 / 4 : ℝ) * ∫ t : ℝ in 8 / 5..2, C t =
          ∫ t : ℝ in 8 / 5..2, (1 / 4 : ℝ) * C t := by
        rw [intervalIntegral.integral_const_mul]
      _ ≤ ∫ t : ℝ in 8 / 5..2, K t * C t := by
        apply intervalIntegral.integral_mono_on
          (by norm_num) htailQuarter htail
        intro t ht
        have harg0 : 0 ≤ fourCellOperatorHalfWidth * t :=
          mul_nonneg (by unfold fourCellOperatorHalfWidth; positivity)
            (by linarith [ht.1])
        have hk : K t ≤ (1 / 4 : ℝ) := by
          dsimp only [K]
          exact yoshidaRegularKernel_le_quarter harg0
        have hCt : C t ≤ 0 := by
          dsimp only [C]
          exact oddStructuralCorrelation13_nonpos_tail ht
        exact mul_le_mul_of_nonpos_right hk hCt
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hhead htail
  have hUpper :
      (∫ t : ℝ in 0..2, K t * C t) ≤ (21 / 20000 : ℝ) := by
    calc
      (∫ t : ℝ in 0..2, K t * C t) =
          (∫ t : ℝ in 0..8 / 5, K t * C t) +
            ∫ t : ℝ in 8 / 5..2, K t * C t := hsplit.symm
      _ ≤ ((∫ t : ℝ in 0..8 / 5, P t * C t) +
          (1 / 500000 : ℝ) * (1 / 6)) +
            (1 / 5 : ℝ) * ∫ t : ℝ in 8 / 5..2, C t :=
        add_le_add hheadUpper htailUpper
      _ ≤ 21 / 20000 := by
        have hmodel := fourCellOddLowRegular13_upper_model
        simpa only [P, C] using (show
          ((∫ t : ℝ in 0..8 / 5, P t * C t) +
              (1 / 500000 : ℝ) * (1 / 6)) +
                (1 / 5 : ℝ) * ∫ t : ℝ in 8 / 5..2, C t ≤
              (21 / 20000 : ℝ) by
            linarith)
  have hLower :
      (-21 / 20000 : ℝ) ≤
        ∫ t : ℝ in 0..2, K t * C t := by
    calc
      (-21 / 20000 : ℝ) ≤
          (∫ t : ℝ in 0..8 / 5, P t * C t) +
            (1 / 4 : ℝ) * (∫ t : ℝ in 8 / 5..2, C t) -
              (1 / 500000 : ℝ) * (1 / 6) := by
        simpa only [P, C] using fourCellOddLowRegular13_lower_model
      _ ≤ (∫ t : ℝ in 0..8 / 5, K t * C t) +
          ∫ t : ℝ in 8 / 5..2, K t * C t := by
        calc
          (∫ t : ℝ in 0..8 / 5, P t * C t) +
                (1 / 4 : ℝ) * (∫ t : ℝ in 8 / 5..2, C t) -
              (1 / 500000 : ℝ) * (1 / 6) =
              ((∫ t : ℝ in 0..8 / 5, P t * C t) -
                (1 / 500000 : ℝ) * (1 / 6)) +
                  (1 / 4 : ℝ) * (∫ t : ℝ in 8 / 5..2, C t) := by
            ring
          _ ≤ (∫ t : ℝ in 0..8 / 5, K t * C t) +
              ∫ t : ℝ in 8 / 5..2, K t * C t :=
            add_le_add hheadLower htailLower
      _ = ∫ t : ℝ in 0..2, K t * C t := hsplit
  apply abs_le.mpr
  constructor
  · have heq : -(21 / 20000 : ℝ) = -21 / 20000 := by ring
    rw [heq]
    simpa only [K, C] using hLower
  · simpa only [K, C] using hUpper

private theorem oddStructuralCorrelation33_le_tail_envelope
    {t : ℝ} (ht : t ∈ Icc (8 / 5 : ℝ) 2) :
    oddStructuralCorrelation33 t ≤ (2 - t) / 8 := by
  let u : ℝ := t - 8 / 5
  have hu : 0 ≤ u := by
    dsimp only [u]
    linarith [ht.1]
  let q : ℝ :=
    5 * t ^ 6 + 10 * t ^ 5 - 22 * t ^ 4 - 44 * t ^ 3 +
      24 * t ^ 2 + 48 * t - 16
  have hq : (-14 : ℝ) ≤ q := by
    rw [show q =
        -41936 / 3125 + (42928 / 625 : ℝ) * u +
          376 * u ^ 2 + (2404 / 5 : ℝ) * u ^ 3 +
            250 * u ^ 4 + 58 * u ^ 5 + 5 * u ^ 6 by
      dsimp only [q, u]
      ring]
    have hnonneg : 0 ≤
        (42928 / 625 : ℝ) * u + 376 * u ^ 2 +
          (2404 / 5 : ℝ) * u ^ 3 + 250 * u ^ 4 +
            58 * u ^ 5 + 5 * u ^ 6 := by
      positivity
    nlinarith
  have htwo : 0 ≤ 2 - t := by linarith [ht.2]
  have hnegq : -q ≤ (14 : ℝ) := by linarith
  calc
    oddStructuralCorrelation33 t = (2 - t) * (-q) / 112 := by
      unfold oddStructuralCorrelation33
      dsimp only [q]
      ring
    _ ≤ (2 - t) * 14 / 112 := by gcongr
    _ = (2 - t) / 8 := by ring

theorem integral_regularPolynomial6_mul_oddStructuralCorrelation33_head :
    (∫ t : ℝ in 0..8 / 5,
      yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t) *
        oddStructuralCorrelation33 t) =
      908 / 546875 - (137 / 29531250 : ℝ) * Real.log 2 -
        (2552 / 8203125 : ℝ) * Real.log 2 ^ 2 +
          (62137 / 7425000000 : ℝ) * Real.log 2 ^ 3 +
            (499 / 10500000 : ℝ) * Real.log 2 ^ 4 -
              (38715683 / 170270100000000 : ℝ) * Real.log 2 ^ 5 -
                (43249 / 9800000000 : ℝ) * Real.log 2 ^ 6 := by
  rw [show (fun t : ℝ ↦
      yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t) *
        oddStructuralCorrelation33 t) =
      fun t ↦
        (1 / 14 : ℝ) * t ^ 0 +
        (-(1 / 4 : ℝ) - (5 / 1344 : ℝ) * Real.log 2) * t ^ 1 +
        ((5 / 384 : ℝ) * Real.log 2 -
          (25 / 7168 : ℝ) * Real.log 2 ^ 2) * t ^ 2 +
        ((1 / 4 : ℝ) + (25 / 2048 : ℝ) * Real.log 2 ^ 2 +
          (25 / 589824 : ℝ) * Real.log 2 ^ 3) * t ^ 3 +
        (-(5 / 384 : ℝ) * Real.log 2 -
          (175 / 1179648 : ℝ) * Real.log 2 ^ 3 +
            (3125 / 22020096 : ℝ) * Real.log 2 ^ 4) * t ^ 4 +
        (-(3 / 32 : ℝ) - (25 / 2048 : ℝ) * Real.log 2 ^ 2 -
          (3125 / 6291456 : ℝ) * Real.log 2 ^ 4 -
            (19375 / 44392513536 : ℝ) * Real.log 2 ^ 5) * t ^ 5 +
        ((5 / 1024 : ℝ) * Real.log 2 +
          (175 / 1179648 : ℝ) * Real.log 2 ^ 3 +
            (19375 / 12683575296 : ℝ) * Real.log 2 ^ 5 -
              (190625 / 33822867456 : ℝ) * Real.log 2 ^ 6) * t ^ 6 +
        ((5 / 448 : ℝ) + (75 / 16384 : ℝ) * Real.log 2 ^ 2 +
          (3125 / 6291456 : ℝ) * Real.log 2 ^ 4 +
            (190625 / 9663676416 : ℝ) * Real.log 2 ^ 6) * t ^ 7 +
        (-(25 / 43008 : ℝ) * Real.log 2 -
          (175 / 3145728 : ℝ) * Real.log 2 ^ 3 -
            (19375 / 12683575296 : ℝ) * Real.log 2 ^ 5) * t ^ 8 +
        (-(125 / 229376 : ℝ) * Real.log 2 ^ 2 -
          (3125 / 16777216 : ℝ) * Real.log 2 ^ 4 -
            (190625 / 9663676416 : ℝ) * Real.log 2 ^ 6) * t ^ 9 +
        ((125 / 18874368 : ℝ) * Real.log 2 ^ 3 +
          (19375 / 33822867456 : ℝ) * Real.log 2 ^ 5) * t ^ 10 +
        ((15625 / 704643072 : ℝ) * Real.log 2 ^ 4 +
          (190625 / 25769803776 : ℝ) * Real.log 2 ^ 6) * t ^ 11 +
        (-(96875 / 1420560433152 : ℝ) * Real.log 2 ^ 5) * t ^ 12 +
        (-(953125 / 1082331758592 : ℝ) * Real.log 2 ^ 6) * t ^ 13 by
    funext t
    unfold yoshidaRegularKernelPolynomial6 fourCellOperatorHalfWidth
      oddStructuralCorrelation33
    ring,
    integral_polynomial_thirteen]
  ring

theorem integral_oddStructuralCorrelation33_tail :
    (∫ t : ℝ in 8 / 5..2, oddStructuralCorrelation33 t) =
      (-3632 / 546875 : ℝ) := by
  rw [show oddStructuralCorrelation33 = fun t : ℝ ↦
      (2 / 7 : ℝ) * t ^ 0 + (-1 : ℝ) * t ^ 1 + 0 * t ^ 2 +
        1 * t ^ 3 + 0 * t ^ 4 + (-3 / 8 : ℝ) * t ^ 5 +
          0 * t ^ 6 + (5 / 112 : ℝ) * t ^ 7 + 0 * t ^ 8 +
            0 * t ^ 9 + 0 * t ^ 10 + 0 * t ^ 11 + 0 * t ^ 12 +
              0 * t ^ 13 by
    funext t
    unfold oddStructuralCorrelation33
    ring]
  simp only
  rw [integral_polynomial_thirteen]
  norm_num

private theorem integral_fourCellOdd33_tail_envelope :
    (∫ t : ℝ in 8 / 5..2, (2 - t) / 8) = (1 / 100 : ℝ) := by
  rw [show (fun t : ℝ ↦ (2 - t) / 8) = fun t ↦
      (1 / 4 : ℝ) * t ^ 0 + (-1 / 8 : ℝ) * t ^ 1 +
        0 * t ^ 2 + 0 * t ^ 3 + 0 * t ^ 4 + 0 * t ^ 5 +
          0 * t ^ 6 + 0 * t ^ 7 + 0 * t ^ 8 + 0 * t ^ 9 by
    funext t
    ring,
    integral_polynomial_nine]
  norm_num

private theorem fourCellOddLowRegular33_upper_model :
    (∫ t : ℝ in 0..8 / 5,
        yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t) *
          oddStructuralCorrelation33 t) +
      (1 / 5 : ℝ) *
        (∫ t : ℝ in 8 / 5..2, oddStructuralCorrelation33 t) +
      (1 / 20 : ℝ) *
        (∫ t : ℝ in 8 / 5..2, (2 - t) / 8) +
      (1 / 500000 : ℝ) * (2 / 7) ≤ (7 / 10000 : ℝ) := by
  rw [integral_regularPolynomial6_mul_oddStructuralCorrelation33_head,
    integral_oddStructuralCorrelation33_tail,
    integral_fourCellOdd33_tail_envelope]
  let L₀ : ℝ := 6931 / 10000
  let L₁ : ℝ := 6932 / 10000
  have hL0 : L₀ ≤ Real.log 2 := by
    dsimp only [L₀]
    exact strict_log_two_bounds.1.le
  have hL1 : Real.log 2 ≤ L₁ := by
    dsimp only [L₁]
    exact strict_log_two_bounds.2.le
  have hlog0 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have hlo2 := pow_le_pow_left₀ (by norm_num : 0 ≤ L₀) hL0 2
  have hlo3 := pow_le_pow_left₀ (by norm_num : 0 ≤ L₀) hL0 3
  have hlo4 := pow_le_pow_left₀ (by norm_num : 0 ≤ L₀) hL0 4
  have hlo5 := pow_le_pow_left₀ (by norm_num : 0 ≤ L₀) hL0 5
  have hlo6 := pow_le_pow_left₀ (by norm_num : 0 ≤ L₀) hL0 6
  have hup2 := pow_le_pow_left₀ hlog0 hL1 2
  have hup3 := pow_le_pow_left₀ hlog0 hL1 3
  have hup4 := pow_le_pow_left₀ hlog0 hL1 4
  have hup5 := pow_le_pow_left₀ hlog0 hL1 5
  have hup6 := pow_le_pow_left₀ hlog0 hL1 6
  have hrat :
      908 / 546875 - (137 / 29531250 : ℝ) * L₀ -
          (2552 / 8203125 : ℝ) * L₀ ^ 2 +
            (62137 / 7425000000 : ℝ) * L₁ ^ 3 +
              (499 / 10500000 : ℝ) * L₁ ^ 4 -
                (38715683 / 170270100000000 : ℝ) * L₀ ^ 5 -
                  (43249 / 9800000000 : ℝ) * L₀ ^ 6 +
                    (1 / 5 : ℝ) * (-3632 / 546875) +
                      (1 / 20 : ℝ) * (1 / 100) +
                        (1 / 500000 : ℝ) * (2 / 7) ≤
        7 / 10000 := by
    norm_num [L₀, L₁]
  apply le_trans ?_ hrat
  gcongr

/-- The wide `P₃/P₃` regular moment has a small positive upper
budget.  On the tail we do not isolate the correlation's internal sign
change: the single polynomial majorant `C₃₃(t) ≤ (2-t)/8` absorbs it
against the width `1/4 - 1/5` of the kernel interval. -/
theorem integral_yoshidaRegularKernel_mul_oddStructuralCorrelation33_le :
    (∫ t : ℝ in 0..2,
      yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
        oddStructuralCorrelation33 t) ≤ (7 / 10000 : ℝ) := by
  let C : ℝ → ℝ := oddStructuralCorrelation33
  let K : ℝ → ℝ := fun t ↦
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t)
  let P : ℝ → ℝ := fun t ↦
    yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t)
  let B : ℝ → ℝ := fun t ↦ (2 - t) / 8
  have hC : Continuous C := by
    dsimp only [C]
    unfold oddStructuralCorrelation33
    fun_prop
  have hB : Continuous B := by
    dsimp only [B]
    fun_prop
  have hfull : IntervalIntegrable (fun t : ℝ ↦ K t * C t)
      volume 0 2 := by
    simpa only [K] using
      intervalIntegrable_fourCellRegularKernel_mul_continuous C hC
  have hhead : IntervalIntegrable (fun t : ℝ ↦ K t * C t)
      volume 0 (8 / 5) :=
    hfull.mono_set (by
      intro t ht
      norm_num at ht ⊢
      constructor <;> linarith :
        uIcc (0 : ℝ) (8 / 5) ⊆ uIcc (0 : ℝ) 2)
  have htail : IntervalIntegrable (fun t : ℝ ↦ K t * C t)
      volume (8 / 5) 2 :=
    hfull.mono_set (by
      intro t ht
      norm_num at ht ⊢
      constructor <;> linarith :
        uIcc (8 / 5 : ℝ) 2 ⊆ uIcc (0 : ℝ) 2)
  have hPcont : Continuous P := by
    dsimp only [P]
    unfold yoshidaRegularKernelPolynomial6
    fun_prop
  have hP : IntervalIntegrable (fun t : ℝ ↦ P t * C t)
      volume 0 (8 / 5) := (hPcont.mul hC).intervalIntegrable _ _
  have habsSub :
      (∫ t : ℝ in 0..8 / 5, |C t|) ≤ (2 / 7 : ℝ) := by
    have hmono :
        (∫ t : ℝ in 0..8 / 5, |C t|) ≤
          ∫ t : ℝ in 0..2, |C t| := by
      apply intervalIntegral.integral_mono_interval
        (c := (0 : ℝ)) (d := 2) le_rfl (by norm_num) (by norm_num)
      · filter_upwards with t
        exact abs_nonneg (C t)
      · exact hC.abs.intervalIntegrable _ _
    have hfullAbs :
        (∫ t : ℝ in 0..2, |C t|) ≤ (2 / 7 : ℝ) := by
      simpa only [C] using integral_abs_oddStructuralCorrelation33_le
    exact hmono.trans hfullAbs
  have hheadError :
      |(∫ t : ℝ in 0..8 / 5, K t * C t) -
        ∫ t : ℝ in 0..8 / 5, P t * C t| ≤
          (1 / 500000 : ℝ) *
            ∫ t : ℝ in 0..8 / 5, |C t| := by
    simpa only [K, P] using
      abs_fourCellRegularKernel_head_sub_polynomial_le C hC
  have hheadUpper :
      (∫ t : ℝ in 0..8 / 5, K t * C t) ≤
        (∫ t : ℝ in 0..8 / 5, P t * C t) +
          (1 / 500000 : ℝ) * (2 / 7) := by
    have herr := (abs_le.mp hheadError).2
    have hbudget := mul_le_mul_of_nonneg_left habsSub (by norm_num :
      (0 : ℝ) ≤ 1 / 500000)
    linarith
  have htailModel : IntervalIntegrable
      (fun t : ℝ ↦
        (1 / 5 : ℝ) * C t + (1 / 20 : ℝ) * B t)
      volume (8 / 5) 2 :=
    ((continuous_const.mul hC).add
      (continuous_const.mul hB)).intervalIntegrable _ _
  have htailC : IntervalIntegrable
      (fun t : ℝ ↦ (1 / 5 : ℝ) * C t) volume (8 / 5) 2 :=
    (continuous_const.mul hC).intervalIntegrable _ _
  have htailB : IntervalIntegrable
      (fun t : ℝ ↦ (1 / 20 : ℝ) * B t) volume (8 / 5) 2 :=
    (continuous_const.mul hB).intervalIntegrable _ _
  have htailUpper :
      (∫ t : ℝ in 8 / 5..2, K t * C t) ≤
        (1 / 5 : ℝ) * (∫ t : ℝ in 8 / 5..2, C t) +
          (1 / 20 : ℝ) * (∫ t : ℝ in 8 / 5..2, B t) := by
    calc
      (∫ t : ℝ in 8 / 5..2, K t * C t) ≤
          ∫ t : ℝ in 8 / 5..2,
            (1 / 5 : ℝ) * C t + (1 / 20 : ℝ) * B t := by
        apply intervalIntegral.integral_mono_on
          (by norm_num) htail htailModel
        intro t ht
        have harg0 : 0 ≤ fourCellOperatorHalfWidth * t :=
          mul_nonneg (by unfold fourCellOperatorHalfWidth; positivity)
            (by linarith [ht.1])
        have harg4 : fourCellOperatorHalfWidth * t ≤
            5 * Real.log 2 / 4 := by
          have hmul := mul_le_mul_of_nonneg_left ht.2
            (by unfold fourCellOperatorHalfWidth; positivity :
              0 ≤ fourCellOperatorHalfWidth)
          calc
            fourCellOperatorHalfWidth * t ≤
                fourCellOperatorHalfWidth * 2 := hmul
            _ = 5 * Real.log 2 / 4 := by
              unfold fourCellOperatorHalfWidth
              ring
        have hk0 : (1 / 5 : ℝ) ≤ K t := by
          dsimp only [K]
          exact one_fifth_le_yoshidaRegularKernel_fourCellRange harg0 harg4
        have hk4 : K t ≤ (1 / 4 : ℝ) := by
          dsimp only [K]
          exact yoshidaRegularKernel_le_quarter harg0
        have hdelta0 : 0 ≤ K t - (1 / 5 : ℝ) := sub_nonneg.mpr hk0
        have hdelta4 : K t - (1 / 5 : ℝ) ≤ 1 / 20 := by
          linarith
        have hCB : C t ≤ B t := by
          dsimp only [C, B]
          exact oddStructuralCorrelation33_le_tail_envelope ht
        have hB0 : 0 ≤ B t := by
          dsimp only [B]
          exact div_nonneg (by linarith [ht.2]) (by norm_num)
        calc
          K t * C t = (1 / 5 : ℝ) * C t +
              (K t - 1 / 5) * C t := by ring
          _ ≤ (1 / 5 : ℝ) * C t +
              (K t - 1 / 5) * B t := by
            have hmul := mul_le_mul_of_nonneg_left hCB hdelta0
            linarith
          _ ≤ (1 / 5 : ℝ) * C t + (1 / 20 : ℝ) * B t := by
            have hmul := mul_le_mul_of_nonneg_right hdelta4 hB0
            linarith
      _ = (1 / 5 : ℝ) * (∫ t : ℝ in 8 / 5..2, C t) +
          (1 / 20 : ℝ) * (∫ t : ℝ in 8 / 5..2, B t) := by
        rw [intervalIntegral.integral_add htailC htailB,
          intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hhead htail
  calc
    (∫ t : ℝ in 0..2,
        yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
          oddStructuralCorrelation33 t) =
        (∫ t : ℝ in 0..8 / 5, K t * C t) +
          ∫ t : ℝ in 8 / 5..2, K t * C t := by
      simpa only [K, C] using hsplit.symm
    _ ≤ ((∫ t : ℝ in 0..8 / 5, P t * C t) +
          (1 / 500000 : ℝ) * (2 / 7)) +
        ((1 / 5 : ℝ) * (∫ t : ℝ in 8 / 5..2, C t) +
          (1 / 20 : ℝ) * (∫ t : ℝ in 8 / 5..2, B t)) :=
      add_le_add hheadUpper htailUpper
    _ ≤ 7 / 10000 := by
      have hmodel := fourCellOddLowRegular33_upper_model
      dsimp only [P, C, B]
      linarith

/-- The retained wide regular row on the intrinsic odd two-mode block. -/
def fourCellOddLowRegularQuadratic (c d : ℝ) : ℝ :=
  ∫ t : ℝ in 0..2,
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
      (c ^ 2 * oddStructuralCorrelation11 t +
        2 * c * d * oddStructuralCorrelation13 t +
        d ^ 2 * oddStructuralCorrelation33 t)

theorem fourCellOddLowRegularQuadratic_expansion (c d : ℝ) :
    fourCellOddLowRegularQuadratic c d =
      c ^ 2 * (∫ t : ℝ in 0..2,
        yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
          oddStructuralCorrelation11 t) +
      2 * c * d * (∫ t : ℝ in 0..2,
        yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
          oddStructuralCorrelation13 t) +
      d ^ 2 * (∫ t : ℝ in 0..2,
        yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
          oddStructuralCorrelation33 t) := by
  have h11 := intervalIntegrable_fourCellRegularKernel_mul_continuous
    oddStructuralCorrelation11
      (by unfold oddStructuralCorrelation11; fun_prop)
  have h13 := intervalIntegrable_fourCellRegularKernel_mul_continuous
    oddStructuralCorrelation13
      (by unfold oddStructuralCorrelation13; fun_prop)
  have h33 := intervalIntegrable_fourCellRegularKernel_mul_continuous
    oddStructuralCorrelation33
      (by unfold oddStructuralCorrelation33; fun_prop)
  unfold fourCellOddLowRegularQuadratic
  rw [show (fun t : ℝ ↦
      yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
        (c ^ 2 * oddStructuralCorrelation11 t +
          2 * c * d * oddStructuralCorrelation13 t +
          d ^ 2 * oddStructuralCorrelation33 t)) =
      fun t ↦ c ^ 2 *
          (yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
            oddStructuralCorrelation11 t) +
        (2 * c * d) *
          (yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
            oddStructuralCorrelation13 t) +
        d ^ 2 *
          (yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
            oddStructuralCorrelation33 t) by
    funext t
    ring,
    intervalIntegral.integral_add
      ((h11.const_mul (c ^ 2)).add (h13.const_mul (2 * c * d)))
      (h33.const_mul (d ^ 2)),
    intervalIntegral.integral_add (h11.const_mul (c ^ 2))
      (h13.const_mul (2 * c * d))]
  repeat rw [intervalIntegral.integral_const_mul]

/-- Coupled Loewner budget for the complete low regular row.  The polarized
entry is retained as an absolute cross term, rather than separately charged
to both diagonal coordinates. -/
theorem fourCellOddLowRegularQuadratic_le (c d : ℝ) :
    fourCellOddLowRegularQuadratic c d ≤
      (3 / 500 : ℝ) * c ^ 2 +
        (21 / 10000 : ℝ) * |c * d| +
          (7 / 10000 : ℝ) * d ^ 2 := by
  let R₁₁ : ℝ := ∫ t : ℝ in 0..2,
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
      oddStructuralCorrelation11 t
  let R₁₃ : ℝ := ∫ t : ℝ in 0..2,
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
      oddStructuralCorrelation13 t
  let R₃₃ : ℝ := ∫ t : ℝ in 0..2,
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
      oddStructuralCorrelation33 t
  have h11 : R₁₁ ≤ (3 / 500 : ℝ) := by
    simpa only [R₁₁] using
      integral_yoshidaRegularKernel_mul_oddStructuralCorrelation11_le
  have h13 : |R₁₃| ≤ (21 / 20000 : ℝ) := by
    simpa only [R₁₃] using
      abs_integral_yoshidaRegularKernel_mul_oddStructuralCorrelation13_le
  have h33 : R₃₃ ≤ (7 / 10000 : ℝ) := by
    simpa only [R₃₃] using
      integral_yoshidaRegularKernel_mul_oddStructuralCorrelation33_le
  have h11mul : c ^ 2 * R₁₁ ≤ (3 / 500 : ℝ) * c ^ 2 := by
    have := mul_le_mul_of_nonneg_left h11 (sq_nonneg c)
    linarith
  have h33mul : d ^ 2 * R₃₃ ≤ (7 / 10000 : ℝ) * d ^ 2 := by
    have := mul_le_mul_of_nonneg_left h33 (sq_nonneg d)
    linarith
  have h13mul : 2 * c * d * R₁₃ ≤
      (21 / 10000 : ℝ) * |c * d| := by
    calc
      2 * c * d * R₁₃ ≤ |2 * c * d * R₁₃| := le_abs_self _
      _ = 2 * |c * d| * |R₁₃| := by
        rw [show 2 * c * d * R₁₃ = 2 * (c * d) * R₁₃ by ring,
          abs_mul, abs_mul]
        norm_num
      _ ≤ 2 * |c * d| * (21 / 20000 : ℝ) := by gcongr
      _ = (21 / 10000 : ℝ) * |c * d| := by ring
  rw [fourCellOddLowRegularQuadratic_expansion]
  linarith

/-- After restoring the exact width factor, the complete regular cost is a
small explicit `2 × 2` budget. -/
theorem two_mul_width_mul_fourCellOddLowRegularQuadratic_le (c d : ℝ) :
    2 * fourCellOperatorHalfWidth * fourCellOddLowRegularQuadratic c d ≤
      (13 / 2500 : ℝ) * c ^ 2 +
        (91 / 50000 : ℝ) * |c * d| +
          (61 / 100000 : ℝ) * d ^ 2 := by
  let Q : ℝ := (3 / 500 : ℝ) * c ^ 2 +
    (21 / 10000 : ℝ) * |c * d| + (7 / 10000 : ℝ) * d ^ 2
  have hQ : fourCellOddLowRegularQuadratic c d ≤ Q := by
    simpa only [Q] using fourCellOddLowRegularQuadratic_le c d
  have hwidth0 : 0 ≤ 2 * fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  have hwidth : 2 * fourCellOperatorHalfWidth ≤ (1733 / 2000 : ℝ) := by
    unfold fourCellOperatorHalfWidth
    linarith [strict_log_two_bounds.2]
  have hQ0 : 0 ≤ Q := by
    dsimp only [Q]
    positivity
  calc
    2 * fourCellOperatorHalfWidth * fourCellOddLowRegularQuadratic c d ≤
        2 * fourCellOperatorHalfWidth * Q :=
      mul_le_mul_of_nonneg_left hQ hwidth0
    _ ≤ (1733 / 2000 : ℝ) * Q :=
      mul_le_mul_of_nonneg_right hwidth hQ0
    _ ≤ (13 / 2500 : ℝ) * c ^ 2 +
        (91 / 50000 : ℝ) * |c * d| +
          (61 / 100000 : ℝ) * d ^ 2 := by
      dsimp only [Q]
      nlinarith [sq_nonneg c, sq_nonneg d, abs_nonneg (c * d)]

/-! ## Exact `P₁/P₃` local-width block -/

theorem fourCellOddEndpointStripEven_oddStructuralLow
    (c d z : ℝ) :
    fourCellOddEndpointStripEven
        (factorTwoOddStructuralLowProfile c d) z =
      (2 / 25 : ℝ) * (10 * c + d + 3 * d * z ^ 2) := by
  unfold fourCellOddEndpointStripEven fourCellOddEndpointStripPullback
    factorTwoOddStructuralLowProfile centeredP1 centeredP3
  ring

theorem fourCellOddEndpointStripOdd_oddStructuralLow
    (c d z : ℝ) :
    fourCellOddEndpointStripOdd
        (factorTwoOddStructuralLowProfile c d) z =
      z * (10 * c + 33 * d + d * z ^ 2) / 50 := by
  unfold fourCellOddEndpointStripOdd fourCellOddEndpointStripPullback
    factorTwoOddStructuralLowProfile centeredP1 centeredP3
  ring

theorem fourCellOddEndpointStripEvenMass_oddStructuralLow
    (c d : ℝ) :
    fourCellOddEndpointStripEvenMass
        (factorTwoOddStructuralLowProfile c d) =
      (32 / 125 : ℝ) * c ^ 2 +
        2 * (32 / 625 : ℝ) * c * d +
        (192 / 15625 : ℝ) * d ^ 2 := by
  unfold fourCellOddEndpointStripEvenMass
  simp_rw [fourCellOddEndpointStripEven_oddStructuralLow]
  rw [show (fun z : ℝ ↦
      ((2 / 25 : ℝ) * (10 * c + d + 3 * d * z ^ 2)) ^ 2) =
      fun z ↦
        ((4 / 625 : ℝ) * (10 * c + d) ^ 2) * z ^ 0 +
          ((24 / 625 : ℝ) * (10 * c + d) * d) * z ^ 2 +
          ((36 / 625 : ℝ) * d ^ 2) * z ^ 4 by
    funext z
    ring]
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)]
  repeat rw [intervalIntegral.integral_const_mul, integral_pow_nat]
  norm_num
  ring

theorem fourCellOddEndpointStripOddMass_oddStructuralLow
    (c d : ℝ) :
    fourCellOddEndpointStripOddMass
        (factorTwoOddStructuralLowProfile c d) =
      (2 / 375 : ℝ) * c ^ 2 +
        2 * (56 / 3125 : ℝ) * c * d +
        (6586 / 109375 : ℝ) * d ^ 2 := by
  unfold fourCellOddEndpointStripOddMass
  simp_rw [fourCellOddEndpointStripOdd_oddStructuralLow]
  rw [show (fun z : ℝ ↦
      (z * (10 * c + 33 * d + d * z ^ 2) / 50) ^ 2) =
      fun z ↦
        (((10 * c + 33 * d) ^ 2 / 2500 : ℝ)) * z ^ 2 +
          (((10 * c + 33 * d) * d / 1250 : ℝ)) * z ^ 4 +
          ((d ^ 2 / 2500 : ℝ)) * z ^ 6 by
    funext z
    ring]
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)]
  repeat rw [intervalIntegral.integral_const_mul, integral_pow_nat]
  norm_num
  ring

theorem fourCellOddEndpointStripOdd_oddStructuralLow_eq_lowProfile
    (c d : ℝ) :
    fourCellOddEndpointStripOdd
        (factorTwoOddStructuralLowProfile c d) =
      factorTwoOddStructuralLowProfile
        (c / 5 + 84 * d / 125) (d / 125) := by
  funext z
  rw [fourCellOddEndpointStripOdd_oddStructuralLow]
  unfold factorTwoOddStructuralLowProfile centeredP1 centeredP3
  ring

theorem fourCellOddEndpointStripOddRawEnergy_oddStructuralLow
    (c d : ℝ) :
    fourCellOddEndpointStripOddRawEnergy
        (factorTwoOddStructuralLowProfile c d) =
      (8 / 375 : ℝ) * c ^ 2 +
        2 * (224 / 3125 : ℝ) * c * d +
        (79036 / 328125 : ℝ) * d ^ 2 := by
  unfold fourCellOddEndpointStripOddRawEnergy
  rw [fourCellOddEndpointStripOdd_oddStructuralLow_eq_lowProfile,
    centeredRawLogEnergy_factorTwoOddStructuralLowProfile]
  ring

theorem integral_zero_one_oddStructuralLow_sq
    (c d : ℝ) :
    (∫ x : ℝ in 0..1,
      factorTwoOddStructuralLowProfile c d x ^ 2) =
      (1 / 3 : ℝ) * c ^ 2 + (1 / 7 : ℝ) * d ^ 2 := by
  have hfull := integral_oddStructuralLow_sq c d
  have hhalf := integral_sq_eq_two_mul_positiveHalf
    (factorTwoOddStructuralLowProfile c d)
    (continuous_factorTwoOddStructuralLowProfile c d)
    (Or.inr (odd_factorTwoOddStructuralLowProfile c d))
  linarith

theorem integral_zero_one_endpointPotential_oddStructuralLow
    (c d : ℝ) :
    (∫ x : ℝ in 0..1,
      yoshidaEndpointPotential x *
        factorTwoOddStructuralLowProfile c d x ^ 2) =
      (4 / 9 - (1 / 3 : ℝ) * Real.log 2) * c ^ 2 +
        (1 / 5 : ℝ) * c * d +
        (289 / 1470 - (1 / 7 : ℝ) * Real.log 2) * d ^ 2 := by
  have hfull := integral_endpointPotential_oddStructuralLow c d
  have hhalf := endpointPotential_eq_two_mul_positiveHalf
    (factorTwoOddStructuralLowProfile c d)
    (continuous_factorTwoOddStructuralLowProfile c d)
    (Or.inr (odd_factorTwoOddStructuralLowProfile c d))
  linarith

/-- The residual after extracting the known sharp odd core.  It contains
exactly the endpoint-strip prime modification, the wider scalar shift, the
retained regular completion, and the diagonal allocation used by the odd
rank Schur estimate.  No sign is asserted: these terms have to remain
coupled. -/
def fourCellOddStripCoreDefect (w : ℝ → ℝ) : ℝ :=
  fourCellOddStripRetainedPrimeRawCapacity w -
    (1 / 2 : ℝ) *
      (fourCellPositiveHalfRawSameSignEnergy w +
        fourCellPositiveHalfRawReflectedEnergy w (-1)) +
    ((14 / 5 : ℝ) -
        2 * (Real.log (2 * fourCellOperatorHalfWidth) +
          Real.eulerMascheroniConstant + Real.log Real.pi) - 3 / 200) *
      (∫ x : ℝ in 0..1, w x ^ 2) -
    (7 / 50 : ℝ) *
      (∫ x : ℝ in 0..1, yoshidaEndpointPotential x * w x ^ 2) +
    fourCellOperatorHalfWidth *
      (fourCellPositiveHalfRegularSameSignSquare w
          fourCellOperatorHalfWidth +
        fourCellPositiveHalfRegularReflectedSquare w
          fourCellOperatorHalfWidth (-1)) -
    2 * fourCellOperatorHalfWidth *
      fourCellPositiveHalfRegularRowMass w fourCellOperatorHalfWidth

/-- Correlation normal form of the same coupled defect.  It keeps the exact
wide regular kernel as one signed autocorrelation row, which is the useful
form for a direct comparison with the raw logarithmic reserve. -/
def fourCellOddStripCorrelationCoreDefect (w : ℝ → ℝ) : ℝ :=
  fourCellOddStripRetainedPrimeRawCapacity w -
    (1 / 2 : ℝ) *
      (fourCellPositiveHalfRawSameSignEnergy w +
        fourCellPositiveHalfRawReflectedEnergy w (-1)) +
    ((14 / 5 : ℝ) -
        2 * (Real.log (2 * fourCellOperatorHalfWidth) +
          Real.eulerMascheroniConstant + Real.log Real.pi) - 3 / 200) *
      (∫ x : ℝ in 0..1, w x ^ 2) -
    (7 / 50 : ℝ) *
      (∫ x : ℝ in 0..1, yoshidaEndpointPotential x * w x ^ 2) -
    2 * fourCellOperatorHalfWidth *
      (∫ t : ℝ in 0..2,
        yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
          centeredEndpointCorrelation w t)

/-- Algebraic `(1,1)` entry of the exact local defect on `span(P₁,P₃)`,
before the wide regular autocorrelation is added. -/
def fourCellOddLowLocalAlgebraic11 : ℝ :=
  -(1 / 2 : ℝ) * (8 / 375) +
    Real.sqrt 2 * Real.log 2 * (32 / 125) +
    (2 - Real.sqrt 2 * Real.log 2) * (2 / 375) +
    ((14 / 5 : ℝ) -
      2 * (Real.log (2 * fourCellOperatorHalfWidth) +
        Real.eulerMascheroniConstant + Real.log Real.pi) - 3 / 200) *
      (1 / 3) -
    (7 / 50 : ℝ) * (4 / 9 - (1 / 3) * Real.log 2)

/-- Algebraic polarized `(1,3)` entry of the exact local low block. -/
def fourCellOddLowLocalAlgebraic13 : ℝ :=
  -(1 / 2 : ℝ) * (224 / 3125) +
    Real.sqrt 2 * Real.log 2 * (32 / 625) +
    (2 - Real.sqrt 2 * Real.log 2) * (56 / 3125) -
    (7 / 50 : ℝ) * (1 / 10)

/-- Algebraic `(3,3)` entry of the exact local defect on `span(P₁,P₃)`.
-/
def fourCellOddLowLocalAlgebraic33 : ℝ :=
  -(1 / 2 : ℝ) * (79036 / 328125) +
    Real.sqrt 2 * Real.log 2 * (192 / 15625) +
    (2 - Real.sqrt 2 * Real.log 2) * (6586 / 109375) +
    ((14 / 5 : ℝ) -
      2 * (Real.log (2 * fourCellOperatorHalfWidth) +
        Real.eulerMascheroniConstant + Real.log Real.pi) - 3 / 200) *
      (1 / 7) -
    (7 / 50 : ℝ) * (289 / 1470 - (1 / 7) * Real.log 2)

/-- Exact algebraic quadratic part of the local defect on the intrinsic odd
two-mode block. -/
def fourCellOddLowLocalAlgebraicQuadratic (c d : ℝ) : ℝ :=
  fourCellOddLowLocalAlgebraic11 * c ^ 2 +
    2 * fourCellOddLowLocalAlgebraic13 * c * d +
    fourCellOddLowLocalAlgebraic33 * d ^ 2

/-- Local normal form of the four-cell defect.  The global raw form cancels
exactly: only the removed strip-odd raw energy and its two retained prime
masses remain, together with the width scalar, allocation, and exact regular
correlation. -/
def fourCellOddStripLocalWidthDefect (w : ℝ → ℝ) : ℝ :=
  -(1 / 2 : ℝ) * fourCellOddEndpointStripOddRawEnergy w +
    Real.sqrt 2 * Real.log 2 * fourCellOddEndpointStripEvenMass w +
    (2 - Real.sqrt 2 * Real.log 2) *
      fourCellOddEndpointStripOddMass w +
    ((14 / 5 : ℝ) -
        2 * (Real.log (2 * fourCellOperatorHalfWidth) +
          Real.eulerMascheroniConstant + Real.log Real.pi) - 3 / 200) *
      (∫ x : ℝ in 0..1, w x ^ 2) -
    (7 / 50 : ℝ) *
      (∫ x : ℝ in 0..1, yoshidaEndpointPotential x * w x ^ 2) -
    2 * fourCellOperatorHalfWidth *
      (∫ t : ℝ in 0..2,
        yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
          centeredEndpointCorrelation w t)

/-! ## Exact raw-strip cancellation -/

/-- The part of the centered raw reserve left after the adverse strip-odd
raw energy is restored.  It keeps the unused same-sign square, the
reflection-even strip square, and the complete reflected square coupled. -/
def fourCellOddRawStripCancellationReserve (w : ℝ → ℝ) : ℝ :=
  (1 / 2 : ℝ) *
      (fourCellPositiveHalfRawSameSignEnergy w +
        fourCellPositiveHalfRawReflectedEnergy w (-1)) -
    (1 / 2 : ℝ) * fourCellOddEndpointStripOddRawEnergy w

/-- Symmetric polarization of the whole raw-strip reserve.  Keeping this as
one object prevents the unused same-sign square, reflected square, and
strip-parity compensation from being estimated independently. -/
def fourCellOddRawStripCancellationPolarization
    (u v : ℝ → ℝ) : ℝ :=
  (fourCellOddRawStripCancellationReserve (u + v) -
      fourCellOddRawStripCancellationReserve u -
      fourCellOddRawStripCancellationReserve v) / 2

/-- The exact polarization of the adverse reflection-odd endpoint-strip raw
energy.  It remains a singular positive-form bilinear object; no scalar
weight or pointwise estimate is inserted. -/
def fourCellOddEndpointStripOddRawPolarization
    (u v : ℝ → ℝ) : ℝ :=
  (fourCellOddEndpointStripOddRawEnergy (u + v) -
      fourCellOddEndpointStripOddRawEnergy u -
      fourCellOddEndpointStripOddRawEnergy v) / 2

theorem fourCellOddRawStripCancellationReserve_add
    (u v : ℝ → ℝ) :
    fourCellOddRawStripCancellationReserve (u + v) =
      fourCellOddRawStripCancellationReserve u +
        2 * fourCellOddRawStripCancellationPolarization u v +
          fourCellOddRawStripCancellationReserve v := by
  unfold fourCellOddRawStripCancellationPolarization
  ring

private def fourCellUnitIntervalRawLogCrossIntegrand
    (f g : unitInterval → ℝ) (z : unitInterval × unitInterval) : ℝ :=
  ((f z.1 - f z.2) * (g z.1 - g z.2)) /
    |(z.1 : ℝ) - (z.2 : ℝ)|

private theorem integrable_fourCellUnitIntervalRawLogCrossIntegrand
    (f g : unitInterval → ℝ) {C D : NNReal}
    (hf : LipschitzWith C f) (hg : LipschitzWith D g) :
    Integrable (fourCellUnitIntervalRawLogCrossIntegrand f g) := by
  have hfE := integrable_unitIntervalRawLogEnergyIntegrand_of_lipschitzWith f hf
  have hgE := integrable_unitIntervalRawLogEnergyIntegrand_of_lipschitzWith g hg
  have hfgE := integrable_unitIntervalRawLogEnergyIntegrand_of_lipschitzWith
    (f + g) (hf.add hg)
  have hcombo : Integrable (fun z : unitInterval × unitInterval ↦
      (1 / 2 : ℝ) *
        (unitIntervalRawLogEnergyIntegrand (f + g) z -
          unitIntervalRawLogEnergyIntegrand f z -
          unitIntervalRawLogEnergyIntegrand g z)) :=
    ((hfgE.sub hfE).sub hgE).const_mul (1 / 2 : ℝ)
  apply hcombo.congr
  filter_upwards [] with z
  unfold fourCellUnitIntervalRawLogCrossIntegrand
    unitIntervalRawLogEnergyIntegrand
  simp only [Pi.add_apply]
  ring

private theorem centeredRawLogBilinear_eq_two_mul_unitCross_local
    (u v : ℝ → ℝ)
    (hu : LocallyLipschitzOn (Icc (-1 : ℝ) 1) u)
    (hv : LocallyLipschitzOn (Icc (-1 : ℝ) 1) v) :
    centeredRawLogBilinear u v =
      2 * ∫ z : unitInterval × unitInterval,
        fourCellUnitIntervalRawLogCrossIntegrand
          (fun t ↦ centeredPullback u (t : ℝ))
          (fun t ↦ centeredPullback v (t : ℝ)) z := by
  let f : unitInterval → ℝ := fun t ↦ centeredPullback u (t : ℝ)
  let g : unitInterval → ℝ := fun t ↦ centeredPullback v (t : ℝ)
  let H : ℝ → ℝ → ℝ := fun x y ↦
    ((u x - u y) * (v x - v y)) / |x - y|
  obtain ⟨C, hf⟩ := exists_lipschitzWith_centeredPullback u hu
  obtain ⟨D, hg⟩ := exists_lipschitzWith_centeredPullback v hv
  have hInt : Integrable (fourCellUnitIntervalRawLogCrossIntegrand f g) :=
    integrable_fourCellUnitIntervalRawLogCrossIntegrand f g hf hg
  have hprod :
      (∫ z : unitInterval × unitInterval,
          fourCellUnitIntervalRawLogCrossIntegrand f g z) =
        ∫ s : unitInterval, ∫ t : unitInterval,
          fourCellUnitIntervalRawLogCrossIntegrand f g (s, t) :=
    MeasureTheory.integral_prod _ hInt
  have hpoint (s t : ℝ) :
      ((centeredPullback u s - centeredPullback u t) *
          (centeredPullback v s - centeredPullback v t)) / |s - t| =
        2 * H (2 * s - 1) (2 * t - 1) := by
    unfold H centeredPullback
    rw [show (2 * s - 1) - (2 * t - 1) = 2 * (s - t) by ring,
      abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    by_cases hst : |s - t| = 0
    · simp [hst]
    · field_simp [hst]
  have hiter :
      (∫ z : unitInterval × unitInterval,
          fourCellUnitIntervalRawLogCrossIntegrand f g z) =
        ∫ s : ℝ in 0..1, ∫ t : ℝ in 0..1,
          2 * H (2 * s - 1) (2 * t - 1) := by
    calc
      _ = ∫ s : unitInterval, ∫ t : ℝ in 0..1,
          ((centeredPullback u (s : ℝ) - centeredPullback u t) *
            (centeredPullback v (s : ℝ) - centeredPullback v t)) /
              |(s : ℝ) - t| := by
        rw [hprod]
        apply integral_congr_ae
        filter_upwards [] with s
        rw [← integral_unitInterval_eq_intervalIntegral]
        apply integral_congr_ae
        filter_upwards [] with t
        rfl
      _ = ∫ s : ℝ in 0..1, ∫ t : ℝ in 0..1,
          ((centeredPullback u s - centeredPullback u t) *
            (centeredPullback v s - centeredPullback v t)) / |s - t| := by
        rw [← integral_unitInterval_eq_intervalIntegral]
      _ = _ := by
        apply intervalIntegral.integral_congr
        intro s _hs
        apply intervalIntegral.integral_congr
        intro t _ht
        exact hpoint s t
  have hscale :
      (∫ s : ℝ in 0..1, ∫ t : ℝ in 0..1,
          2 * H (2 * s - 1) (2 * t - 1)) =
        (1 / 2 : ℝ) * centeredRawLogBilinear u v := by
    calc
      _ = 2 * (∫ s : ℝ in 0..1, ∫ t : ℝ in 0..1,
          H (2 * s - 1) (2 * t - 1)) := by
        rw [show (fun s : ℝ ↦ ∫ t : ℝ in 0..1,
            2 * H (2 * s - 1) (2 * t - 1)) =
            fun s ↦ 2 * ∫ t : ℝ in 0..1,
              H (2 * s - 1) (2 * t - 1) by
          funext s
          rw [intervalIntegral.integral_const_mul],
          intervalIntegral.integral_const_mul]
      _ = 2 * ((1 / 4 : ℝ) *
          ∫ x : ℝ in -1..1, ∫ y : ℝ in -1..1, H x y) := by
        rw [integral_integral_comp_two_mul_sub_one H]
      _ = _ := by
        unfold centeredRawLogBilinear
        dsimp only [H]
        ring
  rw [hiter, hscale]
  ring

private theorem centeredRawLogEnergy_add_eq_add_add_two_bilinear
    (u v : ℝ → ℝ)
    (hu : LocallyLipschitzOn (Icc (-1 : ℝ) 1) u)
    (hv : LocallyLipschitzOn (Icc (-1 : ℝ) 1) v) :
    centeredRawLogEnergy (u + v) =
      centeredRawLogEnergy u + centeredRawLogEnergy v +
        2 * centeredRawLogBilinear u v := by
  let f : unitInterval → ℝ := fun t ↦ centeredPullback u (t : ℝ)
  let g : unitInterval → ℝ := fun t ↦ centeredPullback v (t : ℝ)
  obtain ⟨C, hf⟩ := exists_lipschitzWith_centeredPullback u hu
  obtain ⟨D, hg⟩ := exists_lipschitzWith_centeredPullback v hv
  have hfE : Integrable (unitIntervalRawLogEnergyIntegrand f) :=
    integrable_unitIntervalRawLogEnergyIntegrand_of_lipschitzWith f hf
  have hgE : Integrable (unitIntervalRawLogEnergyIntegrand g) :=
    integrable_unitIntervalRawLogEnergyIntegrand_of_lipschitzWith g hg
  have hfgE : Integrable (unitIntervalRawLogEnergyIntegrand (f + g)) :=
    integrable_unitIntervalRawLogEnergyIntegrand_of_lipschitzWith
      (f + g) (hf.add hg)
  have hcross : Integrable
      (fourCellUnitIntervalRawLogCrossIntegrand f g) :=
    integrable_fourCellUnitIntervalRawLogCrossIntegrand f g hf hg
  have hpoint (z : unitInterval × unitInterval) :
      unitIntervalRawLogEnergyIntegrand (f + g) z =
        unitIntervalRawLogEnergyIntegrand f z +
          unitIntervalRawLogEnergyIntegrand g z +
            2 * fourCellUnitIntervalRawLogCrossIntegrand f g z := by
    unfold unitIntervalRawLogEnergyIntegrand
      fourCellUnitIntervalRawLogCrossIntegrand
    simp only [Pi.add_apply]
    ring
  have hrawExpand :
      (∫ z, unitIntervalRawLogEnergyIntegrand (f + g) z) =
        (∫ z, unitIntervalRawLogEnergyIntegrand f z) +
          (∫ z, unitIntervalRawLogEnergyIntegrand g z) +
            2 * ∫ z, fourCellUnitIntervalRawLogCrossIntegrand f g z := by
    calc
      _ = ∫ z, unitIntervalRawLogEnergyIntegrand f z +
          unitIntervalRawLogEnergyIntegrand g z +
            2 * fourCellUnitIntervalRawLogCrossIntegrand f g z := by
        apply integral_congr_ae
        filter_upwards [] with z
        exact hpoint z
      _ = (∫ z, unitIntervalRawLogEnergyIntegrand f z +
            unitIntervalRawLogEnergyIntegrand g z) +
          ∫ z, 2 * fourCellUnitIntervalRawLogCrossIntegrand f g z := by
        exact integral_add (hfE.add hgE) (hcross.const_mul 2)
      _ = _ := by
        rw [integral_add hfE hgE, integral_const_mul]
  have hunitExpand : unitIntervalLogEnergy (f + g) =
      unitIntervalLogEnergy f + unitIntervalLogEnergy g +
        ∫ z, fourCellUnitIntervalRawLogCrossIntegrand f g z := by
    unfold unitIntervalLogEnergy
    rw [hrawExpand]
    ring
  have hfgPullback : f + g = fun t : unitInterval ↦
      centeredPullback (u + v) (t : ℝ) := by
    funext t
    dsimp only [f, g, centeredPullback]
    simp only [Pi.add_apply]
  have hbridgeFG : unitIntervalLogEnergy (f + g) =
      (1 / 4 : ℝ) * centeredRawLogEnergy (u + v) := by
    rw [hfgPullback]
    exact unitIntervalLogEnergy_centeredPullback (u + v) (by
      rw [← hfgPullback]
      exact hfgE)
  have hbridgeF : unitIntervalLogEnergy f =
      (1 / 4 : ℝ) * centeredRawLogEnergy u := by
    simpa only [f] using unitIntervalLogEnergy_centeredPullback u hfE
  have hbridgeG : unitIntervalLogEnergy g =
      (1 / 4 : ℝ) * centeredRawLogEnergy v := by
    simpa only [g] using unitIntervalLogEnergy_centeredPullback v hgE
  have hcrossBridge := centeredRawLogBilinear_eq_two_mul_unitCross_local
    u v hu hv
  change centeredRawLogBilinear u v =
    2 * ∫ z : unitInterval × unitInterval,
      fourCellUnitIntervalRawLogCrossIntegrand f g z at hcrossBridge
  rw [hbridgeFG, hbridgeF, hbridgeG] at hunitExpand
  linarith

private theorem centeredRawLogBilinear_const_mul_right_local
    (u v : ℝ → ℝ) (a : ℝ) :
    centeredRawLogBilinear u (fun x ↦ a * v x) =
      a * centeredRawLogBilinear u v := by
  unfold centeredRawLogBilinear
  rw [show (fun x : ℝ ↦ ∫ y : ℝ in -1..1,
      ((u x - u y) * (a * v x - a * v y)) / |x - y|) =
      fun x ↦ a * ∫ y : ℝ in -1..1,
        ((u x - u y) * (v x - v y)) / |x - y| by
    funext x
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro y _hy
    ring,
    intervalIntegral.integral_const_mul]

private theorem contDiff_fourCellOddEndpointStripOdd_local
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) :
    ContDiff ℝ 1 (fourCellOddEndpointStripOdd w) := by
  unfold fourCellOddEndpointStripOdd fourCellOddEndpointStripPullback
  fun_prop

private theorem fourCellOddEndpointStripOdd_add_local
    (u v : ℝ → ℝ) :
    fourCellOddEndpointStripOdd (u + v) =
      fourCellOddEndpointStripOdd u +
        fourCellOddEndpointStripOdd v := by
  funext z
  unfold fourCellOddEndpointStripOdd fourCellOddEndpointStripPullback
  simp only [Pi.add_apply]
  ring

private theorem fourCellOddEndpointStripOdd_const_mul_local
    (v : ℝ → ℝ) (a : ℝ) :
    fourCellOddEndpointStripOdd (fun x ↦ a * v x) =
      fun z ↦ a * fourCellOddEndpointStripOdd v z := by
  funext z
  unfold fourCellOddEndpointStripOdd fourCellOddEndpointStripPullback
  ring

/-- The retained strip raw polarization is exactly the raw-log bilinear
form of the reflection-odd strip pullbacks, including its affine `1/5`
Jacobian. -/
theorem fourCellOddEndpointStripOddRawPolarization_eq_bilinear
    (u v : ℝ → ℝ) (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v) :
    fourCellOddEndpointStripOddRawPolarization u v =
      (1 / 5 : ℝ) * centeredRawLogBilinear
        (fourCellOddEndpointStripOdd u)
        (fourCellOddEndpointStripOdd v) := by
  let U : ℝ → ℝ := fourCellOddEndpointStripOdd u
  let V : ℝ → ℝ := fourCellOddEndpointStripOdd v
  have hU : ContDiff ℝ 1 U := by
    simpa only [U] using contDiff_fourCellOddEndpointStripOdd_local u hu
  have hV : ContDiff ℝ 1 V := by
    simpa only [V] using contDiff_fourCellOddEndpointStripOdd_local v hv
  have henergy := centeredRawLogEnergy_add_eq_add_add_two_bilinear
    U V
    (hU.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1))
    (hV.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1))
  have hadd := fourCellOddEndpointStripOdd_add_local u v
  unfold fourCellOddEndpointStripOddRawPolarization
    fourCellOddEndpointStripOddRawEnergy
  rw [hadd, henergy]
  dsimp only [U, V] at henergy ⊢
  ring

private theorem fourCellOddEndpointStripOddRawPolarization_const_mul_right
    (u v : ℝ → ℝ) (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v)
    (a : ℝ) :
    fourCellOddEndpointStripOddRawPolarization u (fun x ↦ a * v x) =
      a * fourCellOddEndpointStripOddRawPolarization u v := by
  have hav : ContDiff ℝ 1 (fun x ↦ a * v x) := contDiff_const.mul hv
  rw [fourCellOddEndpointStripOddRawPolarization_eq_bilinear u _ hu hav,
    fourCellOddEndpointStripOddRawPolarization_eq_bilinear u v hu hv,
    fourCellOddEndpointStripOdd_const_mul_local,
    centeredRawLogBilinear_const_mul_right_local]
  ring

/-- For odd profiles the raw-strip polarization is the centered raw
bilinear form minus the retained adverse strip polarization. -/
theorem fourCellOddRawStripCancellationPolarization_eq_centered_sub_strip
    (u v : ℝ → ℝ) (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v)
    (huodd : Function.Odd u) (hvodd : Function.Odd v) :
    fourCellOddRawStripCancellationPolarization u v =
      (1 / 4 : ℝ) * centeredRawLogBilinear u v -
        (1 / 2 : ℝ) *
          fourCellOddEndpointStripOddRawPolarization u v := by
  have huLocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) u :=
    hu.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1)
  have hvLocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) v :=
    hv.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1)
  have henergy := centeredRawLogEnergy_add_eq_add_add_two_bilinear
    u v huLocal hvLocal
  have hfoldU := centeredRawLogEnergy_div_four_eq_positiveHalf_odd
    u huLocal huodd
  have hfoldV := centeredRawLogEnergy_div_four_eq_positiveHalf_odd
    v hvLocal hvodd
  have hfoldAdd := centeredRawLogEnergy_div_four_eq_positiveHalf_odd
    (u + v) (huLocal.add hvLocal) (huodd.add hvodd)
  unfold fourCellOddRawStripCancellationPolarization
    fourCellOddRawStripCancellationReserve
    fourCellOddEndpointStripOddRawPolarization
  rw [← hfoldAdd, ← hfoldU, ← hfoldV, henergy]
  ring

private theorem fourCellOddRawStripCancellationPolarization_const_mul_right
    (u v : ℝ → ℝ) (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v)
    (huodd : Function.Odd u) (hvodd : Function.Odd v) (a : ℝ) :
    fourCellOddRawStripCancellationPolarization u (fun x ↦ a * v x) =
      a * fourCellOddRawStripCancellationPolarization u v := by
  have hav : ContDiff ℝ 1 (fun x ↦ a * v x) := contDiff_const.mul hv
  have havodd : Function.Odd (fun x ↦ a * v x) := by
    intro x
    change a * v (-x) = -(a * v x)
    rw [hvodd]
    ring
  rw [fourCellOddRawStripCancellationPolarization_eq_centered_sub_strip
      u _ hu hav huodd havodd,
    fourCellOddRawStripCancellationPolarization_eq_centered_sub_strip
      u v hu hv huodd hvodd,
    centeredRawLogBilinear_const_mul_right_local,
    fourCellOddEndpointStripOddRawPolarization_const_mul_right
      u v hu hv]
  ring

private theorem fourCellOddEndpointStripOddRawEnergy_const_mul
    (v : ℝ → ℝ) (a : ℝ) :
    fourCellOddEndpointStripOddRawEnergy (fun x ↦ a * v x) =
      a ^ 2 * fourCellOddEndpointStripOddRawEnergy v := by
  unfold fourCellOddEndpointStripOddRawEnergy
  rw [fourCellOddEndpointStripOdd_const_mul_local,
    centeredRawLogEnergy_const_mul]
  ring

private theorem fourCellOddRawStripCancellationReserve_const_mul
    (v : ℝ → ℝ) (hv : ContDiff ℝ 1 v) (hvodd : Function.Odd v)
    (a : ℝ) :
    fourCellOddRawStripCancellationReserve (fun x ↦ a * v x) =
      a ^ 2 * fourCellOddRawStripCancellationReserve v := by
  have hav : ContDiff ℝ 1 (fun x ↦ a * v x) := contDiff_const.mul hv
  have havodd : Function.Odd (fun x ↦ a * v x) := by
    intro x
    change a * v (-x) = -(a * v x)
    rw [hvodd]
    ring
  have hvLocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) v :=
    hv.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1)
  have havLocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1)
      (fun x ↦ a * v x) :=
    hav.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1)
  have hfoldV := centeredRawLogEnergy_div_four_eq_positiveHalf_odd
    v hvLocal hvodd
  have hfoldAV := centeredRawLogEnergy_div_four_eq_positiveHalf_odd
    (fun x ↦ a * v x) havLocal havodd
  unfold fourCellOddRawStripCancellationReserve
  rw [← hfoldAV, ← hfoldV,
    fourCellOddEndpointStripOddRawEnergy_const_mul,
    centeredRawLogEnergy_const_mul]
  ring

private theorem sq_le_mul_of_forall_quadratic_nonneg
    (a b c : ℝ) (hc : 0 ≤ c)
    (hquad : ∀ t : ℝ, 0 ≤ a + 2 * b * t + c * t ^ 2) :
    b ^ 2 ≤ a * c := by
  by_cases hc0 : c = 0
  · subst c
    have hb : b = 0 := by
      by_contra hb0
      let t : ℝ := -(a + 1) / (2 * b)
      have hq := hquad t
      have ht : 2 * b * t = -(a + 1) := by
        dsimp only [t]
        field_simp [hb0]
      simp only [zero_mul] at hq
      rw [ht] at hq
      linarith
    rw [hb]
    norm_num
  · have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
    have hq := hquad (-b / c)
    have heq :
        a + 2 * b * (-b / c) + c * (-b / c) ^ 2 =
          (a * c - b ^ 2) / c := by
      field_simp [ne_of_gt hcpos]
      ring
    rw [heq] at hq
    have hmul := mul_nonneg hq hc
    have hcancel : ((a * c - b ^ 2) / c) * c =
        a * c - b ^ 2 := by
      field_simp [ne_of_gt hcpos]
    rw [hcancel] at hmul
    linarith

/-- The canonical intrinsic low part of an arbitrary profile. -/
def fourCellOddOneThreeLowPart (w : ℝ → ℝ) : ℝ → ℝ :=
  factorTwoOddStructuralLowProfile
    (centeredOddP1Coefficient w) (centeredOddP3Coefficient w)

theorem fourCellOddOneThreeLowPart_add_residual (w : ℝ → ℝ) :
    fourCellOddOneThreeLowPart w + centeredOddOneThreeResidual w = w := by
  exact oddLow_add_oneThreeResidual_eq w

/-- Once the raw strip has been retained exactly, the remaining expression
contains no singular logarithmic energy.  In particular, the artificial
`14 / 5` mass insertion cancels out of this exact remainder. -/
def fourCellOddStripReducedRemainder (w : ℝ → ℝ) : ℝ :=
  Real.sqrt 2 * Real.log 2 * fourCellOddEndpointStripEvenMass w +
    (2 - Real.sqrt 2 * Real.log 2) *
      fourCellOddEndpointStripOddMass w +
    (93 / 50 : ℝ) *
      (∫ x : ℝ in 0..1, yoshidaEndpointPotential x * w x ^ 2) -
    (2 * (Real.log (2 * fourCellOperatorHalfWidth) +
        Real.eulerMascheroniConstant + Real.log Real.pi) + 3 / 200) *
      (∫ x : ℝ in 0..1, w x ^ 2) -
    2 * fourCellOperatorHalfWidth *
      (∫ t : ℝ in 0..2,
        yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
          centeredEndpointCorrelation w t)

/-- Polarized physical mass of the reflection-even endpoint-strip channel. -/
def fourCellOddEndpointStripEvenMassBilinear
    (u v : ℝ → ℝ) : ℝ :=
  (1 / 5 : ℝ) * ∫ z : ℝ in -1..1,
    fourCellOddEndpointStripEven u z *
      fourCellOddEndpointStripEven v z

/-- Polarized physical mass of the reflection-odd endpoint-strip channel. -/
def fourCellOddEndpointStripOddMassBilinear
    (u v : ℝ → ℝ) : ℝ :=
  (1 / 5 : ℝ) * ∫ z : ℝ in -1..1,
    fourCellOddEndpointStripOdd u z *
      fourCellOddEndpointStripOdd v z

/-- Exact symmetric bilinear form of the nonsingular reduced remainder.  In
particular, the wide regular row is retained as one symmetric correlation
instead of being bounded mode by mode. -/
def fourCellOddStripReducedBilinear (u v : ℝ → ℝ) : ℝ :=
  Real.sqrt 2 * Real.log 2 *
      fourCellOddEndpointStripEvenMassBilinear u v +
    (2 - Real.sqrt 2 * Real.log 2) *
      fourCellOddEndpointStripOddMassBilinear u v +
    (93 / 50 : ℝ) *
      (∫ x : ℝ in 0..1, yoshidaEndpointPotential x * u x * v x) -
    (2 * (Real.log (2 * fourCellOperatorHalfWidth) +
        Real.eulerMascheroniConstant + Real.log Real.pi) + 3 / 200) *
      (∫ x : ℝ in 0..1, u x * v x) -
    2 * fourCellOperatorHalfWidth *
      (∫ t : ℝ in 0..2,
        yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
          factorTwoCenteredCorrelationBilinear u v t)

/-- The full positive prime/potential quadratic form retained before the
signed scalar-mass and regular rows are treated. -/
def fourCellOddRetainedPrimePotentialQuadratic (w : ℝ → ℝ) : ℝ :=
  Real.sqrt 2 * Real.log 2 * fourCellOddEndpointStripEvenMass w +
    (2 - Real.sqrt 2 * Real.log 2) *
      fourCellOddEndpointStripOddMass w +
    (93 / 50 : ℝ) *
      (∫ x : ℝ in 0..1, yoshidaEndpointPotential x * w x ^ 2)

/-- Exact bilinear form associated with the retained positive prime and
endpoint-potential quadratic forms. -/
def fourCellOddRetainedPrimePotentialBilinear
    (u v : ℝ → ℝ) : ℝ :=
  Real.sqrt 2 * Real.log 2 *
      fourCellOddEndpointStripEvenMassBilinear u v +
    (2 - Real.sqrt 2 * Real.log 2) *
      fourCellOddEndpointStripOddMassBilinear u v +
    (93 / 50 : ℝ) *
      (∫ x : ℝ in 0..1, yoshidaEndpointPotential x * u x * v x)

/-- All positive singular, prime, and endpoint-potential forms retained as
one quadratic object. -/
def fourCellOddRetainedEndpointQuadratic (w : ℝ → ℝ) : ℝ :=
  fourCellOddRawStripCancellationReserve w +
    fourCellOddRetainedPrimePotentialQuadratic w

/-- The complete bilinear form associated with the retained positive
endpoint quadratic. -/
def fourCellOddRetainedEndpointBilinear (u v : ℝ → ℝ) : ℝ :=
  fourCellOddRawStripCancellationPolarization u v +
    fourCellOddRetainedPrimePotentialBilinear u v

/-- The remaining signed scalar-mass and wide-regular quadratic rows. -/
def fourCellOddSignedMassRegularQuadratic (w : ℝ → ℝ) : ℝ :=
  (2 * (Real.log (2 * fourCellOperatorHalfWidth) +
      Real.eulerMascheroniConstant + Real.log Real.pi) + 3 / 200) *
    (∫ x : ℝ in 0..1, w x ^ 2) +
  2 * fourCellOperatorHalfWidth *
    (∫ t : ℝ in 0..2,
      yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
        centeredEndpointCorrelation w t)

/-- Bilinear form of the signed scalar-mass and wide-regular rows. -/
def fourCellOddSignedMassRegularBilinear (u v : ℝ → ℝ) : ℝ :=
  (2 * (Real.log (2 * fourCellOperatorHalfWidth) +
      Real.eulerMascheroniConstant + Real.log Real.pi) + 3 / 200) *
    (∫ x : ℝ in 0..1, u x * v x) +
  2 * fourCellOperatorHalfWidth *
    (∫ t : ℝ in 0..2,
      yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
        factorTwoCenteredCorrelationBilinear u v t)

theorem fourCellOddStripReducedBilinear_eq_retained_sub_signed
    (u v : ℝ → ℝ) :
    fourCellOddStripReducedBilinear u v =
      fourCellOddRetainedPrimePotentialBilinear u v -
        (2 * (Real.log (2 * fourCellOperatorHalfWidth) +
          Real.eulerMascheroniConstant + Real.log Real.pi) + 3 / 200) *
          (∫ x : ℝ in 0..1, u x * v x) -
        2 * fourCellOperatorHalfWidth *
          (∫ t : ℝ in 0..2,
            yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
              factorTwoCenteredCorrelationBilinear u v t) := by
  unfold fourCellOddStripReducedBilinear
    fourCellOddRetainedPrimePotentialBilinear
  ring

theorem fourCellOddStripReducedRemainder_eq_retained_sub_signed
    (w : ℝ → ℝ) :
    fourCellOddStripReducedRemainder w =
      fourCellOddRetainedPrimePotentialQuadratic w -
        (2 * (Real.log (2 * fourCellOperatorHalfWidth) +
          Real.eulerMascheroniConstant + Real.log Real.pi) + 3 / 200) *
          (∫ x : ℝ in 0..1, w x ^ 2) -
        2 * fourCellOperatorHalfWidth *
          (∫ t : ℝ in 0..2,
            yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
              centeredEndpointCorrelation w t) := by
  unfold fourCellOddStripReducedRemainder
    fourCellOddRetainedPrimePotentialQuadratic
  ring

private theorem fourCellOddEndpointStripEvenMass_add
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    fourCellOddEndpointStripEvenMass (u + v) =
      fourCellOddEndpointStripEvenMass u +
        2 * fourCellOddEndpointStripEvenMassBilinear u v +
          fourCellOddEndpointStripEvenMass v := by
  let U : ℝ → ℝ := fourCellOddEndpointStripEven u
  let V : ℝ → ℝ := fourCellOddEndpointStripEven v
  have hU : Continuous U := by
    simpa only [U] using continuous_fourCellOddEndpointStripEven u hu
  have hV : Continuous V := by
    simpa only [V] using continuous_fourCellOddEndpointStripEven v hv
  have hUU : IntervalIntegrable (fun z : ℝ ↦ U z ^ 2)
      volume (-1) 1 := (hU.pow 2).intervalIntegrable _ _
  have hUV : IntervalIntegrable (fun z : ℝ ↦ U z * V z)
      volume (-1) 1 := (hU.mul hV).intervalIntegrable _ _
  have hVV : IntervalIntegrable (fun z : ℝ ↦ V z ^ 2)
      volume (-1) 1 := (hV.pow 2).intervalIntegrable _ _
  unfold fourCellOddEndpointStripEvenMass
    fourCellOddEndpointStripEvenMassBilinear
  rw [show (fun z : ℝ ↦ fourCellOddEndpointStripEven (u + v) z ^ 2) =
      fun z ↦ U z ^ 2 +
        (2 * (U z * V z) + V z ^ 2) by
    funext z
    dsimp only [U, V]
    unfold fourCellOddEndpointStripEven
      fourCellOddEndpointStripPullback
    simp only [Pi.add_apply]
    ring,
    intervalIntegral.integral_add hUU ((hUV.const_mul 2).add hVV),
    intervalIntegral.integral_add (hUV.const_mul 2) hVV,
    intervalIntegral.integral_const_mul]
  ring

private theorem fourCellOddEndpointStripOddMass_add
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    fourCellOddEndpointStripOddMass (u + v) =
      fourCellOddEndpointStripOddMass u +
        2 * fourCellOddEndpointStripOddMassBilinear u v +
          fourCellOddEndpointStripOddMass v := by
  let U : ℝ → ℝ := fourCellOddEndpointStripOdd u
  let V : ℝ → ℝ := fourCellOddEndpointStripOdd v
  have hU : Continuous U := by
    simpa only [U] using continuous_fourCellOddEndpointStripOdd u hu
  have hV : Continuous V := by
    simpa only [V] using continuous_fourCellOddEndpointStripOdd v hv
  have hUU : IntervalIntegrable (fun z : ℝ ↦ U z ^ 2)
      volume (-1) 1 := (hU.pow 2).intervalIntegrable _ _
  have hUV : IntervalIntegrable (fun z : ℝ ↦ U z * V z)
      volume (-1) 1 := (hU.mul hV).intervalIntegrable _ _
  have hVV : IntervalIntegrable (fun z : ℝ ↦ V z ^ 2)
      volume (-1) 1 := (hV.pow 2).intervalIntegrable _ _
  unfold fourCellOddEndpointStripOddMass
    fourCellOddEndpointStripOddMassBilinear
  rw [show (fun z : ℝ ↦ fourCellOddEndpointStripOdd (u + v) z ^ 2) =
      fun z ↦ U z ^ 2 +
        (2 * (U z * V z) + V z ^ 2) by
    funext z
    dsimp only [U, V]
    unfold fourCellOddEndpointStripOdd
      fourCellOddEndpointStripPullback
    simp only [Pi.add_apply]
    ring,
    intervalIntegral.integral_add hUU ((hUV.const_mul 2).add hVV),
    intervalIntegral.integral_add (hUV.const_mul 2) hVV,
    intervalIntegral.integral_const_mul]
  ring

private theorem integral_zero_one_endpointPotential_add_sq
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    (∫ x : ℝ in 0..1, yoshidaEndpointPotential x * (u x + v x) ^ 2) =
      (∫ x : ℝ in 0..1, yoshidaEndpointPotential x * u x ^ 2) +
        2 * (∫ x : ℝ in 0..1,
          yoshidaEndpointPotential x * u x * v x) +
        ∫ x : ℝ in 0..1, yoshidaEndpointPotential x * v x ^ 2 := by
  have hsub : uIcc (0 : ℝ) 1 ⊆ uIcc (-1 : ℝ) 1 := by
    intro x hx
    norm_num at hx ⊢
    constructor <;> linarith
  have hUU : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * u x ^ 2)
      volume 0 1 :=
    (intervalIntegrable_endpointPotential_mul_sq u hu).mono_set hsub
  have hUV : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * u x * v x)
      volume 0 1 := by
    simpa only [mul_assoc] using
      (intervalIntegrable_endpointPotential_mul (fun x ↦ u x * v x)
        (hu.mul hv)).mono_set hsub
  have hVV : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * v x ^ 2)
      volume 0 1 :=
    (intervalIntegrable_endpointPotential_mul_sq v hv).mono_set hsub
  rw [show (fun x : ℝ ↦
      yoshidaEndpointPotential x * (u x + v x) ^ 2) =
      fun x ↦ yoshidaEndpointPotential x * u x ^ 2 +
        (2 * (yoshidaEndpointPotential x * u x * v x) +
          yoshidaEndpointPotential x * v x ^ 2) by
    funext x
    ring,
    intervalIntegral.integral_add hUU ((hUV.const_mul 2).add hVV),
    intervalIntegral.integral_add (hUV.const_mul 2) hVV,
    intervalIntegral.integral_const_mul]
  ring

private theorem integral_zero_one_add_sq
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    (∫ x : ℝ in 0..1, (u x + v x) ^ 2) =
      (∫ x : ℝ in 0..1, u x ^ 2) +
        2 * (∫ x : ℝ in 0..1, u x * v x) +
          ∫ x : ℝ in 0..1, v x ^ 2 := by
  have hUU : IntervalIntegrable (fun x : ℝ ↦ u x ^ 2)
      volume 0 1 := (hu.pow 2).intervalIntegrable _ _
  have hUV : IntervalIntegrable (fun x : ℝ ↦ u x * v x)
      volume 0 1 := (hu.mul hv).intervalIntegrable _ _
  have hVV : IntervalIntegrable (fun x : ℝ ↦ v x ^ 2)
      volume 0 1 := (hv.pow 2).intervalIntegrable _ _
  rw [show (fun x : ℝ ↦ (u x + v x) ^ 2) =
      fun x ↦ u x ^ 2 + (2 * (u x * v x) + v x ^ 2) by
    funext x
    ring,
    intervalIntegral.integral_add hUU ((hUV.const_mul 2).add hVV),
    intervalIntegral.integral_add (hUV.const_mul 2) hVV,
    intervalIntegral.integral_const_mul]
  ring

/-- Genuine quadratic polarization of the reduced remainder. -/
theorem fourCellOddStripReducedRemainder_add
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    fourCellOddStripReducedRemainder (u + v) =
      fourCellOddStripReducedRemainder u +
        2 * fourCellOddStripReducedBilinear u v +
          fourCellOddStripReducedRemainder v := by
  have hCu : Continuous (centeredEndpointCorrelation u) :=
    continuous_centeredEndpointCorrelation_of_continuous u hu
  have hCv : Continuous (centeredEndpointCorrelation v) :=
    continuous_centeredEndpointCorrelation_of_continuous v hv
  have hB : Continuous (factorTwoCenteredCorrelationBilinear u v) := by
    unfold factorTwoCenteredCorrelationBilinear
    exact ((continuous_factorTwoCenteredCrossCorrelation u v hu hv).add
      (continuous_factorTwoCenteredCrossCorrelation v u hv hu)).div_const 2
  have hIu := intervalIntegrable_fourCellRegularKernel_mul_continuous
    (centeredEndpointCorrelation u) hCu
  have hIv := intervalIntegrable_fourCellRegularKernel_mul_continuous
    (centeredEndpointCorrelation v) hCv
  have hIb := intervalIntegrable_fourCellRegularKernel_mul_continuous
    (factorTwoCenteredCorrelationBilinear u v) hB
  unfold fourCellOddStripReducedRemainder
    fourCellOddStripReducedBilinear
  rw [fourCellOddEndpointStripEvenMass_add u v hu hv,
    fourCellOddEndpointStripOddMass_add u v hu hv]
  simp only [Pi.add_apply]
  rw [
    integral_zero_one_endpointPotential_add_sq u v hu hv,
    integral_zero_one_add_sq u v hu hv]
  rw [show (fun t : ℝ ↦
      yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
        centeredEndpointCorrelation (u + v) t) =
      fun t ↦
        yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
          centeredEndpointCorrelation u t +
        (2 * (yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
          factorTwoCenteredCorrelationBilinear u v t) +
        yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
          centeredEndpointCorrelation v t) by
    funext t
    rw [centeredEndpointCorrelation_add u v hu hv t]
    ring,
    intervalIntegral.integral_add hIu ((hIb.const_mul 2).add hIv),
    intervalIntegral.integral_add (hIb.const_mul 2) hIv,
    intervalIntegral.integral_const_mul]
  ring

private theorem centeredRawLogEnergy_nonneg (u : ℝ → ℝ) :
    0 ≤ centeredRawLogEnergy u := by
  unfold centeredRawLogEnergy
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro x _hx
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro y _hy
  exact div_nonneg (sq_nonneg _) (abs_nonneg _)

private theorem fourCellOddEndpointStripEvenRawEnergy_nonneg
    (w : ℝ → ℝ) :
    0 ≤ fourCellOddEndpointStripEvenRawEnergy w := by
  unfold fourCellOddEndpointStripEvenRawEnergy
  exact mul_nonneg (by norm_num) (centeredRawLogEnergy_nonneg _)

private theorem fourCellPositiveHalfRawReflectedEnergy_nonneg
    (w : ℝ → ℝ) :
    0 ≤ fourCellPositiveHalfRawReflectedEnergy w (-1) := by
  unfold fourCellPositiveHalfRawReflectedEnergy
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro x hx
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro y hy
  exact div_nonneg (sq_nonneg _) (add_nonneg hx.1 hy.1)

/-- The adverse strip-odd raw form is absorbed without a spectral truncation:
the strip embeds in the positive-half square, and strip parity supplies the
missing reflection-even square. -/
theorem fourCellOddRawStripCancellationReserve_nonneg
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) :
    0 ≤ fourCellOddRawStripCancellationReserve w := by
  have hembed := fourCellOddEndpointStripRawEnergy_le_positiveHalf w hw
  have hparity := fourCellOddEndpointStrip_rawEnergy_eq_even_add_odd w hw
  have heven := fourCellOddEndpointStripEvenRawEnergy_nonneg w
  have hreflected := fourCellPositiveHalfRawReflectedEnergy_nonneg w
  unfold fourCellOddRawStripCancellationReserve
  linarith

/-- Cauchy--Schwarz for the full retained raw-strip reserve, obtained from
its structural nonnegativity and exact quadratic homogeneity.  This keeps
the singular raw/reflected/strip form intact rather than replacing it by a
scalar tail weight. -/
theorem fourCellOddRawStripCancellationPolarization_sq_le_mul
    (u v : ℝ → ℝ) (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v)
    (huodd : Function.Odd u) (hvodd : Function.Odd v) :
    fourCellOddRawStripCancellationPolarization u v ^ 2 ≤
      fourCellOddRawStripCancellationReserve u *
        fourCellOddRawStripCancellationReserve v := by
  apply sq_le_mul_of_forall_quadratic_nonneg
    (fourCellOddRawStripCancellationReserve u)
    (fourCellOddRawStripCancellationPolarization u v)
    (fourCellOddRawStripCancellationReserve v)
    (fourCellOddRawStripCancellationReserve_nonneg v hv)
  intro t
  have htv : ContDiff ℝ 1 (fun x ↦ t * v x) := contDiff_const.mul hv
  have hnonneg := fourCellOddRawStripCancellationReserve_nonneg
    (u + fun x ↦ t * v x) (hu.add htv)
  rw [fourCellOddRawStripCancellationReserve_add,
    fourCellOddRawStripCancellationPolarization_const_mul_right
      u v hu hv huodd hvodd t,
    fourCellOddRawStripCancellationReserve_const_mul v hv hvodd t]
    at hnonneg
  convert hnonneg using 1
  all_goals ring

/-- Quantitative endpoint-strip consequence of the raw ground state.  The
retained raw reserve pays `6/5` of the upper-strip mass before any potential,
regular-kernel, or finite-dimensional estimate is used. -/
theorem six_fifths_upperStripMass_le_rawStripCancellationReserve
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w) :
    (6 / 5 : ℝ) * (∫ x : ℝ in 3 / 5..1, w x ^ 2) ≤
      fourCellOddRawStripCancellationReserve w := by
  let I : ℝ := ∫ p : ℝ × ℝ in
    Icc (3 / 5 : ℝ) 1 ×ˢ Ico (0 : ℝ) (3 / 5),
      fourCellOddCoupledRawPair w p
        ∂((volume : Measure ℝ).prod volume)
  have hmass : (6 / 5 : ℝ) * (∫ x : ℝ in 3 / 5..1, w x ^ 2) ≤ I := by
    simpa only [I] using six_fifths_upperStripMass_le_cross_coupledRaw w hw
  have hcross : 2 * I ≤
      fourCellPositiveHalfRawSameSignEnergy w +
        fourCellPositiveHalfRawReflectedEnergy w (-1) -
          fourCellOddEndpointStripRawEnergy w := by
    simpa only [I] using
      two_mul_cross_coupledRaw_le_fullRaw_sub_stripRaw w hw hodd
  have hparity := fourCellOddEndpointStrip_rawEnergy_eq_even_add_odd w hw
  have heven := fourCellOddEndpointStripEvenRawEnergy_nonneg w
  unfold fourCellOddRawStripCancellationReserve
  linarith

/-- Weighted quantitative endpoint-strip consequence of the raw ground state.
Unlike the preceding coarse estimate, this retains the exact `1/x` gain near
the inner edge of the strip. -/
theorem six_fifths_upperStripWeightedMass_le_rawStripCancellationReserve
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w) :
    (6 / 5 : ℝ) * (∫ x : ℝ in 3 / 5..1, w x ^ 2 / x) ≤
      fourCellOddRawStripCancellationReserve w := by
  let I : ℝ := ∫ p : ℝ × ℝ in
    Icc (3 / 5 : ℝ) 1 ×ˢ Ico (0 : ℝ) (3 / 5),
      fourCellOddCoupledRawPair w p
        ∂((volume : Measure ℝ).prod volume)
  have hmass :
      (6 / 5 : ℝ) * (∫ x : ℝ in 3 / 5..1, w x ^ 2 / x) ≤ I := by
    simpa only [I] using
      six_fifths_upperStripWeightedMass_le_cross_coupledRaw w hw
  have hcross : 2 * I ≤
      fourCellPositiveHalfRawSameSignEnergy w +
        fourCellPositiveHalfRawReflectedEnergy w (-1) -
          fourCellOddEndpointStripRawEnergy w := by
    simpa only [I] using
      two_mul_cross_coupledRaw_le_fullRaw_sub_stripRaw w hw hodd
  have hparity := fourCellOddEndpointStrip_rawEnergy_eq_even_add_odd w hw
  have heven := fourCellOddEndpointStripEvenRawEnergy_nonneg w
  unfold fourCellOddRawStripCancellationReserve
  linarith

/-- Coupling the preceding raw reserve to the centered regular-row estimate
leaves an explicit upper-strip payment and charges only `a/10` of the
centered mass. -/
theorem upperStripMass_sub_regularCharge_le_rawReserve_sub_regular
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w) :
    (6 / 5 : ℝ) * (∫ x : ℝ in 3 / 5..1, w x ^ 2) -
        (fourCellOperatorHalfWidth / 10) *
          (∫ x : ℝ in -1..1, w x ^ 2) ≤
      fourCellOddRawStripCancellationReserve w -
        2 * fourCellOperatorHalfWidth *
          (∫ t : ℝ in 0..2,
            yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
              centeredEndpointCorrelation w t) := by
  let R : ℝ := ∫ t : ℝ in 0..2,
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
      centeredEndpointCorrelation w t
  let M : ℝ := ∫ x : ℝ in -1..1, w x ^ 2
  have hraw := six_fifths_upperStripMass_le_rawStripCancellationReserve
    w hw hodd
  have hR : |R| ≤ (1 / 20 : ℝ) * M := by
    simpa only [R, M] using
      abs_fourCellRegularCorrelation_le_one_twentieth_centeredMass
        w hw.continuous hodd
  have ha0 : 0 ≤ 2 * fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  have hRle : R ≤ |R| := le_abs_self R
  have hmul := mul_le_mul_of_nonneg_left (hRle.trans hR) ha0
  dsimp only [R, M] at hmul ⊢
  linarith

/-- Weighted form of the coupled raw/regular reserve.  The only global charge
is the centered regular-row mass; the raw payment keeps its sharp `1/x`
endpoint density. -/
theorem upperStripWeightedMass_sub_regularCharge_le_rawReserve_sub_regular
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w) :
    (6 / 5 : ℝ) * (∫ x : ℝ in 3 / 5..1, w x ^ 2 / x) -
        (fourCellOperatorHalfWidth / 10) *
          (∫ x : ℝ in -1..1, w x ^ 2) ≤
      fourCellOddRawStripCancellationReserve w -
        2 * fourCellOperatorHalfWidth *
          (∫ t : ℝ in 0..2,
            yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
              centeredEndpointCorrelation w t) := by
  let R : ℝ := ∫ t : ℝ in 0..2,
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
      centeredEndpointCorrelation w t
  let M : ℝ := ∫ x : ℝ in -1..1, w x ^ 2
  have hraw :=
    six_fifths_upperStripWeightedMass_le_rawStripCancellationReserve
      w hw hodd
  have hR : |R| ≤ (1 / 20 : ℝ) * M := by
    simpa only [R, M] using
      abs_fourCellRegularCorrelation_le_one_twentieth_centeredMass
        w hw.continuous hodd
  have ha0 : 0 ≤ 2 * fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  have hRle : R ≤ |R| := le_abs_self R
  have hmul := mul_le_mul_of_nonneg_left (hRle.trans hR) ha0
  dsimp only [R, M] at hmul ⊢
  linarith

/-- Exact singular/nonsingular split of the universal absorption target.
All high-frequency growth is retained in the nonnegative raw-strip reserve;
the second summand is a regular-kernel and diagonal problem. -/
theorem fourCellOddHalfCoreReserve_add_localWidthDefect_eq_raw_add_reduced
    (w : ℝ → ℝ) :
    fourCellOddHalfCoreReserve w + fourCellOddStripLocalWidthDefect w =
      fourCellOddRawStripCancellationReserve w +
        fourCellOddStripReducedRemainder w := by
  unfold fourCellOddHalfCoreReserve fourCellOddStripLocalWidthDefect
    fourCellOddRawStripCancellationReserve fourCellOddStripReducedRemainder
  ring

/-- Consequently, a lower bound for the nonsingular remainder alone closes
the original local-width defect. -/
theorem neg_fourCellOddStripLocalWidthDefect_le_core_of_reduced_nonneg
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w)
    (hreduced : 0 ≤ fourCellOddStripReducedRemainder w) :
    -fourCellOddStripLocalWidthDefect w ≤ fourCellOddHalfCoreReserve w := by
  have hraw := fourCellOddRawStripCancellationReserve_nonneg w hw
  have hsplit :=
    fourCellOddHalfCoreReserve_add_localWidthDefect_eq_raw_add_reduced w
  linarith

/-- Exact `P₁/P₃` normal form of the local four-cell defect.  Every
strip, potential, and scalar term is now an explicit `2 × 2` quadratic;
the only nonalgebraic entries left are the three wide regular-kernel moments.
-/
theorem fourCellOddStripLocalWidthDefect_oddStructuralLow_eq
    (c d : ℝ) :
    fourCellOddStripLocalWidthDefect
        (factorTwoOddStructuralLowProfile c d) =
      fourCellOddLowLocalAlgebraicQuadratic c d -
        2 * fourCellOperatorHalfWidth *
          (∫ t : ℝ in 0..2,
            yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
              (c ^ 2 * oddStructuralCorrelation11 t +
                2 * c * d * oddStructuralCorrelation13 t +
                d ^ 2 * oddStructuralCorrelation33 t)) := by
  unfold fourCellOddStripLocalWidthDefect
    fourCellOddLowLocalAlgebraicQuadratic
    fourCellOddLowLocalAlgebraic11 fourCellOddLowLocalAlgebraic13
    fourCellOddLowLocalAlgebraic33
  rw [fourCellOddEndpointStripOddRawEnergy_oddStructuralLow,
    fourCellOddEndpointStripEvenMass_oddStructuralLow,
    fourCellOddEndpointStripOddMass_oddStructuralLow,
    integral_zero_one_oddStructuralLow_sq,
    integral_zero_one_endpointPotential_oddStructuralLow]
  simp_rw [centeredEndpointCorrelation_oddStructuralLow]
  ring

/-! ## Closure of the intrinsic odd low block -/

private theorem log_five_four_lt_4463_div_20000 :
    Real.log (5 / 4 : ℝ) < 4463 / 20000 := by
  have h := Real.log_div_le_sum_range_add (x := (1 / 9 : ℝ))
    (by norm_num) (by norm_num) 4
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

private theorem fourCellScalar_lt_31577_div_20000 :
    Real.log (2 * fourCellOperatorHalfWidth) +
        Real.eulerMascheroniConstant + Real.log Real.pi <
      (31577 / 20000 : ℝ) := by
  have hlogTwo : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hwidth :
      Real.log (2 * fourCellOperatorHalfWidth) =
        Real.log (5 / 4 : ℝ) + Real.log (Real.log 2) := by
    rw [show 2 * fourCellOperatorHalfWidth =
        (5 / 4 : ℝ) * Real.log 2 by
      unfold fourCellOperatorHalfWidth
      ring,
      Real.log_mul (by norm_num : (5 / 4 : ℝ) ≠ 0) hlogTwo]
  rw [hwidth]
  linarith [log_five_four_lt_4463_div_20000,
    strict_log_log_two_bounds.2, strict_euler_gamma_bounds.2,
    strict_log_pi_bounds.2]

private theorem one_lt_fourCellScalar :
    (1 : ℝ) < Real.log (2 * fourCellOperatorHalfWidth) +
      Real.eulerMascheroniConstant + Real.log Real.pi := by
  have hlogTwo : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hwidth :
      Real.log (2 * fourCellOperatorHalfWidth) =
        Real.log (5 / 4 : ℝ) + Real.log (Real.log 2) := by
    rw [show 2 * fourCellOperatorHalfWidth =
        (5 / 4 : ℝ) * Real.log 2 by
      unfold fourCellOperatorHalfWidth
      ring,
      Real.log_mul (by norm_num : (5 / 4 : ℝ) ≠ 0) hlogTwo]
  have hfive : 0 < Real.log (5 / 4 : ℝ) :=
    Real.log_pos (by norm_num)
  rw [hwidth]
  linarith [strict_log_log_two_bounds.1,
    strict_euler_gamma_bounds.1, strict_log_pi_bounds.1]

private theorem fourCellOperatorHalfWidth_le_one_half :
    fourCellOperatorHalfWidth ≤ (1 / 2 : ℝ) := by
  have hlog := strict_log_two_bounds.2
  unfold fourCellOperatorHalfWidth
  nlinarith

private theorem sqrt_two_mul_log_two_bounds :
    (141421 / 100000 : ℝ) * (6931 / 10000) <
        Real.sqrt 2 * Real.log 2 ∧
      Real.sqrt 2 * Real.log 2 <
        (70711 / 50000 : ℝ) * (6932 / 10000) := by
  have hs := sqrt_two_kernel_bounds
  have hl := strict_log_two_bounds
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hlpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  constructor
  · calc
      (141421 / 100000 : ℝ) * (6931 / 10000) <
          Real.sqrt 2 * (6931 / 10000) :=
        mul_lt_mul_of_pos_right hs.1 (by norm_num)
      _ < Real.sqrt 2 * Real.log 2 :=
        mul_lt_mul_of_pos_left hl.1 hspos
  · calc
      Real.sqrt 2 * Real.log 2 <
          (70711 / 50000 : ℝ) * Real.log 2 :=
        mul_lt_mul_of_pos_right hs.2 hlpos
      _ < (70711 / 50000 : ℝ) * (6932 / 10000) :=
        mul_lt_mul_of_pos_left hl.2 (by norm_num)

private theorem fourCellEndpointHalfMass_eq_upperStripMass
    (w : ℝ → ℝ) (hw : Continuous w) :
    fourCellEndpointHalfMass w =
      ∫ x : ℝ in 3 / 5..1, w x ^ 2 := by
  have hleft := intervalIntegral.integral_comp_add_mul
    (a := (0 : ℝ)) (b := 2 / 5) (c := (1 : ℝ))
    (fun x : ℝ ↦ w x ^ 2) (by norm_num) (3 / 5)
  have hright := intervalIntegral.integral_comp_sub_left
    (a := (0 : ℝ)) (b := 2 / 5) (fun x : ℝ ↦ w x ^ 2) 1
  norm_num at hleft hright
  have hleftInt : IntervalIntegrable
      (fun t : ℝ ↦ w (3 / 5 + t) ^ 2) volume 0 (2 / 5) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hrightInt : IntervalIntegrable
      (fun t : ℝ ↦ w (1 - t) ^ 2) volume 0 (2 / 5) := by
    apply Continuous.intervalIntegrable
    fun_prop
  unfold fourCellEndpointHalfMass
  rw [intervalIntegral.integral_add hleftInt hrightInt, hleft, hright]
  ring

private theorem fourCellOddEndpointStripEvenMass_nonneg
    (w : ℝ → ℝ) :
    0 ≤ fourCellOddEndpointStripEvenMass w := by
  unfold fourCellOddEndpointStripEvenMass
  exact mul_nonneg (by norm_num)
    (intervalIntegral.integral_nonneg (by norm_num)
      (fun z _hz ↦ sq_nonneg _))

private theorem fourCellOddEndpointStripOddMass_nonneg
    (w : ℝ → ℝ) :
    0 ≤ fourCellOddEndpointStripOddMass w := by
  unfold fourCellOddEndpointStripOddMass
  exact mul_nonneg (by norm_num)
    (intervalIntegral.integral_nonneg (by norm_num)
      (fun z _hz ↦ sq_nonneg _))

private theorem fourCellOddEndpointStripEven_const_mul_local
    (v : ℝ → ℝ) (a : ℝ) :
    fourCellOddEndpointStripEven (fun x ↦ a * v x) =
      fun z ↦ a * fourCellOddEndpointStripEven v z := by
  funext z
  unfold fourCellOddEndpointStripEven fourCellOddEndpointStripPullback
  ring

private theorem fourCellOddEndpointStripEvenMass_const_mul
    (v : ℝ → ℝ) (a : ℝ) :
    fourCellOddEndpointStripEvenMass (fun x ↦ a * v x) =
      a ^ 2 * fourCellOddEndpointStripEvenMass v := by
  unfold fourCellOddEndpointStripEvenMass
  rw [fourCellOddEndpointStripEven_const_mul_local]
  rw [show (fun z : ℝ ↦
      (a * fourCellOddEndpointStripEven v z) ^ 2) =
      fun z ↦ a ^ 2 * fourCellOddEndpointStripEven v z ^ 2 by
    funext z
    ring,
    intervalIntegral.integral_const_mul]
  ring

private theorem fourCellOddEndpointStripOddMass_const_mul
    (v : ℝ → ℝ) (a : ℝ) :
    fourCellOddEndpointStripOddMass (fun x ↦ a * v x) =
      a ^ 2 * fourCellOddEndpointStripOddMass v := by
  unfold fourCellOddEndpointStripOddMass
  rw [fourCellOddEndpointStripOdd_const_mul_local]
  rw [show (fun z : ℝ ↦
      (a * fourCellOddEndpointStripOdd v z) ^ 2) =
      fun z ↦ a ^ 2 * fourCellOddEndpointStripOdd v z ^ 2 by
    funext z
    ring,
    intervalIntegral.integral_const_mul]
  ring

private theorem endpointPotentialEnergy_const_mul
    (v : ℝ → ℝ) (a : ℝ) :
    (∫ x : ℝ in 0..1,
      yoshidaEndpointPotential x * (a * v x) ^ 2) =
      a ^ 2 * ∫ x : ℝ in 0..1,
        yoshidaEndpointPotential x * v x ^ 2 := by
  rw [show (fun x : ℝ ↦
      yoshidaEndpointPotential x * (a * v x) ^ 2) =
      fun x ↦ a ^ 2 *
        (yoshidaEndpointPotential x * v x ^ 2) by
    funext x
    ring,
    intervalIntegral.integral_const_mul]

private theorem fourCellOddRetainedPrimePotentialQuadratic_const_mul
    (v : ℝ → ℝ) (a : ℝ) :
    fourCellOddRetainedPrimePotentialQuadratic (fun x ↦ a * v x) =
      a ^ 2 * fourCellOddRetainedPrimePotentialQuadratic v := by
  unfold fourCellOddRetainedPrimePotentialQuadratic
  rw [fourCellOddEndpointStripEvenMass_const_mul,
    fourCellOddEndpointStripOddMass_const_mul,
    endpointPotentialEnergy_const_mul]
  ring

private theorem fourCellOddEndpointStripEvenMassBilinear_const_mul_right
    (u v : ℝ → ℝ) (a : ℝ) :
    fourCellOddEndpointStripEvenMassBilinear u (fun x ↦ a * v x) =
      a * fourCellOddEndpointStripEvenMassBilinear u v := by
  unfold fourCellOddEndpointStripEvenMassBilinear
  rw [fourCellOddEndpointStripEven_const_mul_local]
  rw [show (fun z : ℝ ↦ fourCellOddEndpointStripEven u z *
      (a * fourCellOddEndpointStripEven v z)) =
      fun z ↦ a * (fourCellOddEndpointStripEven u z *
        fourCellOddEndpointStripEven v z) by
    funext z
    ring,
    intervalIntegral.integral_const_mul]
  ring

private theorem fourCellOddEndpointStripOddMassBilinear_const_mul_right
    (u v : ℝ → ℝ) (a : ℝ) :
    fourCellOddEndpointStripOddMassBilinear u (fun x ↦ a * v x) =
      a * fourCellOddEndpointStripOddMassBilinear u v := by
  unfold fourCellOddEndpointStripOddMassBilinear
  rw [fourCellOddEndpointStripOdd_const_mul_local]
  rw [show (fun z : ℝ ↦ fourCellOddEndpointStripOdd u z *
      (a * fourCellOddEndpointStripOdd v z)) =
      fun z ↦ a * (fourCellOddEndpointStripOdd u z *
        fourCellOddEndpointStripOdd v z) by
    funext z
    ring,
    intervalIntegral.integral_const_mul]
  ring

private theorem endpointPotentialBilinear_const_mul_right
    (u v : ℝ → ℝ) (a : ℝ) :
    (∫ x : ℝ in 0..1,
      yoshidaEndpointPotential x * u x * (a * v x)) =
      a * ∫ x : ℝ in 0..1,
        yoshidaEndpointPotential x * u x * v x := by
  rw [show (fun x : ℝ ↦
      yoshidaEndpointPotential x * u x * (a * v x)) =
      fun x ↦ a * (yoshidaEndpointPotential x * u x * v x) by
    funext x
    ring,
    intervalIntegral.integral_const_mul]

private theorem fourCellOddRetainedPrimePotentialBilinear_const_mul_right
    (u v : ℝ → ℝ) (a : ℝ) :
    fourCellOddRetainedPrimePotentialBilinear u (fun x ↦ a * v x) =
      a * fourCellOddRetainedPrimePotentialBilinear u v := by
  unfold fourCellOddRetainedPrimePotentialBilinear
  rw [fourCellOddEndpointStripEvenMassBilinear_const_mul_right,
    fourCellOddEndpointStripOddMassBilinear_const_mul_right,
    endpointPotentialBilinear_const_mul_right]
  ring

private theorem fourCellOddRetainedPrimePotentialQuadratic_add
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    fourCellOddRetainedPrimePotentialQuadratic (u + v) =
      fourCellOddRetainedPrimePotentialQuadratic u +
        2 * fourCellOddRetainedPrimePotentialBilinear u v +
          fourCellOddRetainedPrimePotentialQuadratic v := by
  unfold fourCellOddRetainedPrimePotentialQuadratic
    fourCellOddRetainedPrimePotentialBilinear
  rw [fourCellOddEndpointStripEvenMass_add u v hu hv,
    fourCellOddEndpointStripOddMass_add u v hu hv]
  simp only [Pi.add_apply]
  rw [integral_zero_one_endpointPotential_add_sq u v hu hv]
  ring

/-- The retained prime and endpoint-potential diagonal is a positive
quadratic form without replacing any of its densities by a scalar weight. -/
theorem fourCellOddRetainedPrimePotentialQuadratic_nonneg
    (w : ℝ → ℝ) :
    0 ≤ fourCellOddRetainedPrimePotentialQuadratic w := by
  have heven := fourCellOddEndpointStripEvenMass_nonneg w
  have hodd := fourCellOddEndpointStripOddMass_nonneg w
  have hsqrt : 0 ≤ Real.sqrt 2 * Real.log 2 :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg (by norm_num))
  have hoddCoeff : 0 ≤ 2 - Real.sqrt 2 * Real.log 2 := by
    linarith [sqrt_two_mul_log_two_bounds.2]
  have hpotential : 0 ≤ ∫ x : ℝ in 0..1,
      yoshidaEndpointPotential x * w x ^ 2 := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro x hx
    exact mul_nonneg
      (YoshidaEndpointEvenMeanZeroPositive.yoshidaEndpointPotential_nonneg_on_Icc
        ⟨by linarith [hx.1], hx.2⟩)
      (sq_nonneg _)
  unfold fourCellOddRetainedPrimePotentialQuadratic
  positivity

/-- Cauchy--Schwarz for the complete retained prime/potential form.  Its
strip-even, strip-odd, and endpoint-potential channels stay coupled through
the Schur step. -/
theorem fourCellOddRetainedPrimePotentialBilinear_sq_le_mul
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    fourCellOddRetainedPrimePotentialBilinear u v ^ 2 ≤
      fourCellOddRetainedPrimePotentialQuadratic u *
        fourCellOddRetainedPrimePotentialQuadratic v := by
  apply sq_le_mul_of_forall_quadratic_nonneg
    (fourCellOddRetainedPrimePotentialQuadratic u)
    (fourCellOddRetainedPrimePotentialBilinear u v)
    (fourCellOddRetainedPrimePotentialQuadratic v)
    (fourCellOddRetainedPrimePotentialQuadratic_nonneg v)
  intro t
  let tv : ℝ → ℝ := fun x ↦ t * v x
  have htv : Continuous tv := by
    dsimp only [tv]
    fun_prop
  have hnonneg := fourCellOddRetainedPrimePotentialQuadratic_nonneg
    (u + tv)
  rw [fourCellOddRetainedPrimePotentialQuadratic_add u tv hu htv]
    at hnonneg
  dsimp only [tv] at hnonneg
  rw [fourCellOddRetainedPrimePotentialBilinear_const_mul_right,
    fourCellOddRetainedPrimePotentialQuadratic_const_mul] at hnonneg
  convert hnonneg using 1
  all_goals ring

private theorem fourCellOddRetainedEndpointQuadratic_add
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    fourCellOddRetainedEndpointQuadratic (u + v) =
      fourCellOddRetainedEndpointQuadratic u +
        2 * fourCellOddRetainedEndpointBilinear u v +
          fourCellOddRetainedEndpointQuadratic v := by
  unfold fourCellOddRetainedEndpointQuadratic
    fourCellOddRetainedEndpointBilinear
  rw [fourCellOddRawStripCancellationReserve_add,
    fourCellOddRetainedPrimePotentialQuadratic_add u v hu hv]
  ring

private theorem fourCellOddRetainedEndpointQuadratic_const_mul
    (v : ℝ → ℝ) (hv : ContDiff ℝ 1 v) (hvodd : Function.Odd v)
    (a : ℝ) :
    fourCellOddRetainedEndpointQuadratic (fun x ↦ a * v x) =
      a ^ 2 * fourCellOddRetainedEndpointQuadratic v := by
  unfold fourCellOddRetainedEndpointQuadratic
  rw [fourCellOddRawStripCancellationReserve_const_mul v hv hvodd,
    fourCellOddRetainedPrimePotentialQuadratic_const_mul]
  ring

private theorem fourCellOddRetainedEndpointBilinear_const_mul_right
    (u v : ℝ → ℝ) (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v)
    (huodd : Function.Odd u) (hvodd : Function.Odd v) (a : ℝ) :
    fourCellOddRetainedEndpointBilinear u (fun x ↦ a * v x) =
      a * fourCellOddRetainedEndpointBilinear u v := by
  unfold fourCellOddRetainedEndpointBilinear
  rw [fourCellOddRawStripCancellationPolarization_const_mul_right
      u v hu hv huodd hvodd,
    fourCellOddRetainedPrimePotentialBilinear_const_mul_right]
  ring

theorem fourCellOddRetainedEndpointQuadratic_nonneg
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) :
    0 ≤ fourCellOddRetainedEndpointQuadratic w := by
  unfold fourCellOddRetainedEndpointQuadratic
  exact add_nonneg (fourCellOddRawStripCancellationReserve_nonneg w hw)
    (fourCellOddRetainedPrimePotentialQuadratic_nonneg w)

/-- One exact Cauchy--Schwarz inequality for the complete retained endpoint
form.  Raw same/reflected/strip energy and both prime channels and the full
endpoint potential remain coupled; only the signed scalar/regular rows lie
outside this square completion. -/
theorem fourCellOddRetainedEndpointBilinear_sq_le_mul
    (u v : ℝ → ℝ) (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v)
    (huodd : Function.Odd u) (hvodd : Function.Odd v) :
    fourCellOddRetainedEndpointBilinear u v ^ 2 ≤
      fourCellOddRetainedEndpointQuadratic u *
        fourCellOddRetainedEndpointQuadratic v := by
  apply sq_le_mul_of_forall_quadratic_nonneg
    (fourCellOddRetainedEndpointQuadratic u)
    (fourCellOddRetainedEndpointBilinear u v)
    (fourCellOddRetainedEndpointQuadratic v)
    (fourCellOddRetainedEndpointQuadratic_nonneg v hv)
  intro t
  let tv : ℝ → ℝ := fun x ↦ t * v x
  have htv : ContDiff ℝ 1 tv := by
    dsimp only [tv]
    fun_prop
  have hnonneg := fourCellOddRetainedEndpointQuadratic_nonneg
    (u + tv) (hu.add htv)
  rw [fourCellOddRetainedEndpointQuadratic_add u tv hu.continuous
      htv.continuous] at hnonneg
  dsimp only [tv] at hnonneg
  rw [fourCellOddRetainedEndpointBilinear_const_mul_right
      u v hu hv huodd hvodd,
    fourCellOddRetainedEndpointQuadratic_const_mul v hv hvodd] at hnonneg
  convert hnonneg using 1
  all_goals ring

/-- The isolated scalar-mass plus wide-regular diagonal is itself
nonnegative on odd profiles.  The regular correlation is a small signed
perturbation of the strictly positive scalar mass. -/
theorem fourCellOddSignedMassRegularQuadratic_nonneg_of_odd
    (w : ℝ → ℝ) (hw : Continuous w) (hodd : Function.Odd w) :
    0 ≤ fourCellOddSignedMassRegularQuadratic w := by
  let H : ℝ := ∫ x : ℝ in 0..1, w x ^ 2
  let R : ℝ := ∫ t : ℝ in 0..2,
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
      centeredEndpointCorrelation w t
  let C : ℝ := 2 * (Real.log (2 * fourCellOperatorHalfWidth) +
    Real.eulerMascheroniConstant + Real.log Real.pi) + 3 / 200
  have hH : 0 ≤ H := by
    dsimp only [H]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun x _hx ↦ sq_nonneg _)
  have hcentered : (∫ x : ℝ in -1..1, w x ^ 2) = 2 * H := by
    simpa only [H] using integral_sq_eq_two_mul_positiveHalf
      w hw (Or.inr hodd)
  have hRabs : |R| ≤ (1 / 20 : ℝ) *
      (∫ x : ℝ in -1..1, w x ^ 2) := by
    simpa only [R] using
      abs_fourCellRegularCorrelation_le_one_twentieth_centeredMass
        w hw hodd
  rw [hcentered] at hRabs
  have hRlower : -(1 / 10 : ℝ) * H ≤ R := by
    have hneg := neg_abs_le R
    linarith
  have ha0 : 0 ≤ 2 * fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  have hregular := mul_le_mul_of_nonneg_left hRlower ha0
  have hC : (2 : ℝ) ≤ C := by
    dsimp only [C]
    linarith [one_lt_fourCellScalar]
  have ha : fourCellOperatorHalfWidth / 5 ≤ (1 / 10 : ℝ) := by
    linarith [fourCellOperatorHalfWidth_le_one_half]
  have hac : fourCellOperatorHalfWidth / 5 ≤ C := by
    linarith [ha, hC]
  have hmass := mul_le_mul_of_nonneg_right hac hH
  unfold fourCellOddSignedMassRegularQuadratic
  dsimp only [H, R, C] at hregular hmass ⊢
  linarith

private theorem fourCellOddSignedMassRegularQuadratic_add
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    fourCellOddSignedMassRegularQuadratic (u + v) =
      fourCellOddSignedMassRegularQuadratic u +
        2 * fourCellOddSignedMassRegularBilinear u v +
          fourCellOddSignedMassRegularQuadratic v := by
  have hreduced := fourCellOddStripReducedRemainder_add u v hu hv
  have hpositive := fourCellOddRetainedPrimePotentialQuadratic_add u v hu hv
  have hq (w : ℝ → ℝ) :
      fourCellOddStripReducedRemainder w =
        fourCellOddRetainedPrimePotentialQuadratic w -
          fourCellOddSignedMassRegularQuadratic w := by
    rw [fourCellOddStripReducedRemainder_eq_retained_sub_signed]
    unfold fourCellOddSignedMassRegularQuadratic
    ring
  have hb : fourCellOddStripReducedBilinear u v =
      fourCellOddRetainedPrimePotentialBilinear u v -
        fourCellOddSignedMassRegularBilinear u v := by
    rw [fourCellOddStripReducedBilinear_eq_retained_sub_signed]
    unfold fourCellOddSignedMassRegularBilinear
    ring
  rw [hq, hq, hq, hb, hpositive] at hreduced
  linarith

private theorem integral_zero_one_const_mul_sq
    (v : ℝ → ℝ) (a : ℝ) :
    (∫ x : ℝ in 0..1, (a * v x) ^ 2) =
      a ^ 2 * ∫ x : ℝ in 0..1, v x ^ 2 := by
  rw [show (fun x : ℝ ↦ (a * v x) ^ 2) =
      fun x ↦ a ^ 2 * v x ^ 2 by
    funext x
    ring,
    intervalIntegral.integral_const_mul]

private theorem centeredEndpointCorrelation_const_mul_local
    (v : ℝ → ℝ) (a t : ℝ) :
    centeredEndpointCorrelation (fun x ↦ a * v x) t =
      a ^ 2 * centeredEndpointCorrelation v t := by
  have hav : (fun x ↦ a * v x) = a • v := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul]
  rw [hav, ← factorTwoCenteredCorrelationBilinear_self,
    factorTwoCenteredCorrelationBilinear_smul_smul,
    factorTwoCenteredCorrelationBilinear_self]
  ring

private theorem fourCellOddSignedMassRegularQuadratic_const_mul
    (v : ℝ → ℝ) (a : ℝ) :
    fourCellOddSignedMassRegularQuadratic (fun x ↦ a * v x) =
      a ^ 2 * fourCellOddSignedMassRegularQuadratic v := by
  unfold fourCellOddSignedMassRegularQuadratic
  rw [integral_zero_one_const_mul_sq]
  rw [show (fun t : ℝ ↦
      yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
        centeredEndpointCorrelation (fun x ↦ a * v x) t) =
      fun t ↦ a ^ 2 *
        (yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
          centeredEndpointCorrelation v t) by
    funext t
    rw [centeredEndpointCorrelation_const_mul_local]
    ring,
    intervalIntegral.integral_const_mul]
  ring

private theorem integral_zero_one_mul_const_mul_right
    (u v : ℝ → ℝ) (a : ℝ) :
    (∫ x : ℝ in 0..1, u x * (a * v x)) =
      a * ∫ x : ℝ in 0..1, u x * v x := by
  rw [show (fun x : ℝ ↦ u x * (a * v x)) =
      fun x ↦ a * (u x * v x) by
    funext x
    ring,
    intervalIntegral.integral_const_mul]

private theorem factorTwoCenteredCorrelationBilinear_const_mul_right_local
    (u v : ℝ → ℝ) (a t : ℝ) :
    factorTwoCenteredCorrelationBilinear u (fun x ↦ a * v x) t =
      a * factorTwoCenteredCorrelationBilinear u v t := by
  have hv : (fun x ↦ a * v x) = a • v := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul]
  rw [hv]
  simpa only [one_mul, one_smul] using
    factorTwoCenteredCorrelationBilinear_smul_smul 1 a u v t

private theorem fourCellOddSignedMassRegularBilinear_const_mul_right
    (u v : ℝ → ℝ) (a : ℝ) :
    fourCellOddSignedMassRegularBilinear u (fun x ↦ a * v x) =
      a * fourCellOddSignedMassRegularBilinear u v := by
  unfold fourCellOddSignedMassRegularBilinear
  rw [integral_zero_one_mul_const_mul_right]
  rw [show (fun t : ℝ ↦
      yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
        factorTwoCenteredCorrelationBilinear u (fun x ↦ a * v x) t) =
      fun t ↦ a *
        (yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
          factorTwoCenteredCorrelationBilinear u v t) by
    funext t
    rw [factorTwoCenteredCorrelationBilinear_const_mul_right_local]
    ring,
    intervalIntegral.integral_const_mul]
  ring

/-- Cauchy--Schwarz for the isolated positive scalar-mass/regular form. -/
theorem fourCellOddSignedMassRegularBilinear_sq_le_mul
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    (huodd : Function.Odd u) (hvodd : Function.Odd v) :
    fourCellOddSignedMassRegularBilinear u v ^ 2 ≤
      fourCellOddSignedMassRegularQuadratic u *
        fourCellOddSignedMassRegularQuadratic v := by
  apply sq_le_mul_of_forall_quadratic_nonneg
    (fourCellOddSignedMassRegularQuadratic u)
    (fourCellOddSignedMassRegularBilinear u v)
    (fourCellOddSignedMassRegularQuadratic v)
    (fourCellOddSignedMassRegularQuadratic_nonneg_of_odd v hv hvodd)
  intro t
  let tv : ℝ → ℝ := fun x ↦ t * v x
  have htv : Continuous tv := by
    dsimp only [tv]
    fun_prop
  have htvodd : Function.Odd tv := by
    intro x
    change t * v (-x) = -(t * v x)
    rw [hvodd]
    ring
  have hnonneg := fourCellOddSignedMassRegularQuadratic_nonneg_of_odd
    (u + tv) (hu.add htv) (huodd.add htvodd)
  rw [fourCellOddSignedMassRegularQuadratic_add u tv hu htv] at hnonneg
  dsimp only [tv] at hnonneg
  rw [fourCellOddSignedMassRegularBilinear_const_mul_right,
    fourCellOddSignedMassRegularQuadratic_const_mul] at hnonneg
  convert hnonneg using 1
  all_goals ring

private theorem integral_factorTwoCenteredCorrelationBilinear_eq_zero_of_odd
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    (huodd : Function.Odd u) (hvodd : Function.Odd v) :
    (∫ t : ℝ in 0..2,
      factorTwoCenteredCorrelationBilinear u v t) = 0 := by
  have hsum : Function.Odd (u + v) := huodd.add hvodd
  have hu0 := integral_centeredEndpointCorrelation_eq_zero_of_odd
    u hu huodd
  have hv0 := integral_centeredEndpointCorrelation_eq_zero_of_odd
    v hv hvodd
  have huv0 := integral_centeredEndpointCorrelation_eq_zero_of_odd
    (u + v) (hu.add hv) hsum
  have hCu : Continuous (centeredEndpointCorrelation u) :=
    continuous_centeredEndpointCorrelation_of_continuous u hu
  have hCv : Continuous (centeredEndpointCorrelation v) :=
    continuous_centeredEndpointCorrelation_of_continuous v hv
  have hB : Continuous (factorTwoCenteredCorrelationBilinear u v) := by
    unfold factorTwoCenteredCorrelationBilinear
    exact ((continuous_factorTwoCenteredCrossCorrelation u v hu hv).add
      (continuous_factorTwoCenteredCrossCorrelation v u hv hu)).div_const 2
  have hCuInt : IntervalIntegrable (centeredEndpointCorrelation u)
      volume 0 2 := hCu.intervalIntegrable _ _
  have hCvInt : IntervalIntegrable (centeredEndpointCorrelation v)
      volume 0 2 := hCv.intervalIntegrable _ _
  have hBInt : IntervalIntegrable
      (fun t : ℝ ↦ 2 * factorTwoCenteredCorrelationBilinear u v t)
      volume 0 2 := (hB.const_mul 2).intervalIntegrable _ _
  have hCuBInt : IntervalIntegrable
      (fun t : ℝ ↦ centeredEndpointCorrelation u t +
        2 * factorTwoCenteredCorrelationBilinear u v t)
      volume 0 2 := hCuInt.add hBInt
  have hexpand :
      (∫ t : ℝ in 0..2, centeredEndpointCorrelation (u + v) t) =
        (∫ t : ℝ in 0..2, centeredEndpointCorrelation u t) +
          2 * (∫ t : ℝ in 0..2,
            factorTwoCenteredCorrelationBilinear u v t) +
          ∫ t : ℝ in 0..2, centeredEndpointCorrelation v t := by
    rw [show (fun t : ℝ ↦ centeredEndpointCorrelation (u + v) t) =
        fun t ↦ centeredEndpointCorrelation u t +
          2 * factorTwoCenteredCorrelationBilinear u v t +
            centeredEndpointCorrelation v t by
      funext t
      rw [centeredEndpointCorrelation_add u v hu hv t]]
    calc
      _ = (∫ t : ℝ in 0..2,
            centeredEndpointCorrelation u t +
              2 * factorTwoCenteredCorrelationBilinear u v t) +
          ∫ t : ℝ in 0..2, centeredEndpointCorrelation v t :=
        intervalIntegral.integral_add hCuBInt hCvInt
      _ = ((∫ t : ℝ in 0..2, centeredEndpointCorrelation u t) +
            ∫ t : ℝ in 0..2,
              2 * factorTwoCenteredCorrelationBilinear u v t) +
          ∫ t : ℝ in 0..2, centeredEndpointCorrelation v t := by
        rw [intervalIntegral.integral_add hCuInt hBInt]
      _ = _ := by
        rw [intervalIntegral.integral_const_mul]
  linarith

/-- After the constant `1/5` regular-kernel row is annihilated by oddness,
the complete mixed regular row costs only the `1/20` kernel fluctuation. -/
theorem abs_fourCellRegularBilinear_le_one_twentieth_integral_abs
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    (huodd : Function.Odd u) (hvodd : Function.Odd v) :
    |(∫ t : ℝ in 0..2,
        yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
          factorTwoCenteredCorrelationBilinear u v t)| ≤
      (1 / 20 : ℝ) * ∫ t : ℝ in 0..2,
        |factorTwoCenteredCorrelationBilinear u v t| := by
  let B : ℝ → ℝ := factorTwoCenteredCorrelationBilinear u v
  let δ : ℝ → ℝ := fun t ↦
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t) - 1 / 5
  have hB : Continuous B := by
    dsimp only [B]
    unfold factorTwoCenteredCorrelationBilinear
    exact ((continuous_factorTwoCenteredCrossCorrelation u v hu hv).add
      (continuous_factorTwoCenteredCrossCorrelation v u hv hu)).div_const 2
  have hBint : IntervalIntegrable B volume 0 2 :=
    hB.intervalIntegrable _ _
  have hKB := intervalIntegrable_fourCellRegularKernel_mul_continuous B hB
  have hconst : IntervalIntegrable (fun t : ℝ ↦ (1 / 5 : ℝ) * B t)
      volume 0 2 := hBint.const_mul (1 / 5)
  have hδB : IntervalIntegrable (fun t : ℝ ↦ δ t * B t)
      volume 0 2 := by
    apply hKB.sub hconst |>.congr
    intro t _ht
    dsimp only [δ]
    ring
  have hmean : (∫ t : ℝ in 0..2, B t) = 0 := by
    simpa only [B] using
      integral_factorTwoCenteredCorrelationBilinear_eq_zero_of_odd
        u v hu hv huodd hvodd
  have hrewrite :
      (∫ t : ℝ in 0..2,
        yoshidaRegularKernel (fourCellOperatorHalfWidth * t) * B t) =
      ∫ t : ℝ in 0..2, δ t * B t := by
    rw [show (fun t : ℝ ↦
        yoshidaRegularKernel (fourCellOperatorHalfWidth * t) * B t) =
      fun t ↦ δ t * B t + (1 / 5 : ℝ) * B t by
      funext t
      dsimp only [δ]
      ring,
      intervalIntegral.integral_add hδB hconst,
      intervalIntegral.integral_const_mul, hmean]
    ring
  have hpoint : ∀ t ∈ Icc (0 : ℝ) 2,
      |δ t * B t| ≤ (1 / 20 : ℝ) * |B t| := by
    intro t ht
    have harg0 : 0 ≤ fourCellOperatorHalfWidth * t :=
      mul_nonneg (by unfold fourCellOperatorHalfWidth; positivity) ht.1
    have harg4 : fourCellOperatorHalfWidth * t ≤ 5 * Real.log 2 / 4 := by
      have hmul := mul_le_mul_of_nonneg_left ht.2
        (by unfold fourCellOperatorHalfWidth; positivity :
          0 ≤ fourCellOperatorHalfWidth)
      calc
        fourCellOperatorHalfWidth * t ≤ fourCellOperatorHalfWidth * 2 := hmul
        _ = 5 * Real.log 2 / 4 := by
          unfold fourCellOperatorHalfWidth
          ring
    have hk0 := one_fifth_le_yoshidaRegularKernel_fourCellRange harg0 harg4
    have hk1 := yoshidaRegularKernel_le_quarter harg0
    have hδ0 : 0 ≤ δ t := by dsimp only [δ]; linarith
    have hδ1 : δ t ≤ (1 / 20 : ℝ) := by dsimp only [δ]; linarith
    rw [abs_mul, abs_of_nonneg hδ0]
    exact mul_le_mul_of_nonneg_right hδ1 (abs_nonneg _)
  have habsInt : IntervalIntegrable (fun t : ℝ ↦ |δ t * B t|)
      volume 0 2 := hδB.abs
  have hmajorInt : IntervalIntegrable (fun t : ℝ ↦
      (1 / 20 : ℝ) * |B t|) volume 0 2 :=
    (hB.abs.intervalIntegrable _ _).const_mul (1 / 20)
  have hmono :
      (∫ t : ℝ in 0..2, |δ t * B t|) ≤
        ∫ t : ℝ in 0..2, (1 / 20 : ℝ) * |B t| := by
    apply intervalIntegral.integral_mono_on (by norm_num) habsInt hmajorInt
    exact hpoint
  have hnorm := intervalIntegral.norm_integral_le_integral_norm
    (by norm_num : (0 : ℝ) ≤ 2) (f := fun t ↦ δ t * B t)
      (μ := volume)
  rw [intervalIntegral.integral_const_mul] at hmono
  rw [hrewrite]
  simp only [Real.norm_eq_abs] at hnorm
  dsimp only [B] at hmono hnorm ⊢
  linarith

/-- The exact strip-prime diagonal dominates `49/50` of the physical
endpoint mass.  Both parity coefficients are kept; the rational constant is
only a common lower bound. -/
theorem forty_nine_fiftieths_upperStripMass_le_primeDiagonal
    (w : ℝ → ℝ) (hw : Continuous w) :
    (49 / 50 : ℝ) * (∫ x : ℝ in 3 / 5..1, w x ^ 2) ≤
      Real.sqrt 2 * Real.log 2 * fourCellOddEndpointStripEvenMass w +
        (2 - Real.sqrt 2 * Real.log 2) *
          fourCellOddEndpointStripOddMass w := by
  have hpLower : (49 / 50 : ℝ) ≤ Real.sqrt 2 * Real.log 2 := by
    linarith [sqrt_two_mul_log_two_bounds.1]
  have hpUpper :
      Real.sqrt 2 * Real.log 2 ≤ (51 / 50 : ℝ) := by
    linarith [sqrt_two_mul_log_two_bounds.2]
  have heven := fourCellOddEndpointStripEvenMass_nonneg w
  have hodd := fourCellOddEndpointStripOddMass_nonneg w
  have hevenMul := mul_le_mul_of_nonneg_right hpLower heven
  have hoddMul := mul_le_mul_of_nonneg_right
    (by linarith : (49 / 50 : ℝ) ≤
      2 - Real.sqrt 2 * Real.log 2) hodd
  have hsplit := fourCellEndpointHalfMass_eq_evenMass_add_oddMass w hw
  rw [fourCellEndpointHalfMass_eq_upperStripMass w hw] at hsplit
  linarith

private theorem endpointStripOcticDensity_gap_nonneg
    {x : ℝ} (hx0 : (3 / 5 : ℝ) ≤ x) (hx1 : x ≤ 1) :
    0 ≤ (6 / 5 : ℝ) - (57 / 25) * x +
      (93 / 50) * x * yoshidaEndpointOctic x := by
  let t : ℝ := (5 * x - 3) / 2
  have ht0 : 0 ≤ t := by
    dsimp only [t]
    linarith
  have ht1 : t ≤ 1 := by
    dsimp only [t]
    linarith
  have hcomp : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  rw [show
      (6 / 5 : ℝ) - (57 / 25) * x +
          (93 / 50) * x * yoshidaEndpointOctic x =
        (62546469 / 781250000 : ℝ) * (1 - t) ^ 9 +
        (60215487 / 156250000 : ℝ) * t * (1 - t) ^ 8 +
        (5843121 / 7812500 : ℝ) * t ^ 2 * (1 - t) ^ 7 +
        (92799 / 62500 : ℝ) * t ^ 3 * (1 - t) ^ 6 +
        (3031347 / 625000 : ℝ) * t ^ 4 * (1 - t) ^ 5 +
        (1416849 / 125000 : ℝ) * t ^ 5 * (1 - t) ^ 4 +
        (190437 / 12500 : ℝ) * t ^ 6 * (1 - t) ^ 3 +
        (29323 / 2500 : ℝ) * t ^ 7 * (1 - t) ^ 2 +
        (9757 / 2000 : ℝ) * t ^ 8 * (1 - t) +
        (343 / 400 : ℝ) * t ^ 9 by
    dsimp only [t]
    unfold yoshidaEndpointOctic
    ring]
  positivity

/-- Pointwise endpoint diagonal certificate.  The weighted raw density,
the common prime density, and the octic part of the endpoint potential
together dominate the complete rational scalar budget on the open strip. -/
private theorem one_hundred_sixty_three_fiftieths_le_endpointStripDensity
    {x : ℝ} (hx0 : (3 / 5 : ℝ) < x) (hx1 : x < 1) :
    (163 / 50 : ℝ) ≤
      6 / (5 * x) + 49 / 50 +
        (93 / 50) * yoshidaEndpointPotential x := by
  have hxpos : 0 < x := by linarith
  have hpoly := endpointStripOcticDensity_gap_nonneg hx0.le hx1.le
  have hoctic : yoshidaEndpointOctic x ≤ yoshidaEndpointPotential x := by
    apply octic_le_endpointPotential
    rw [abs_lt]
    constructor <;> linarith
  have hpotential := mul_le_mul_of_nonneg_left hoctic
    (by positivity : 0 ≤ (93 / 50 : ℝ) * x)
  apply le_of_mul_le_mul_right ?_ hxpos
  rw [show
      (6 / (5 * x) + 49 / 50 +
          (93 / 50) * yoshidaEndpointPotential x) * x =
        6 / 5 + (49 / 50) * x +
          ((93 / 50) * x) * yoshidaEndpointPotential x by
    field_simp [hxpos.ne']]
  nlinarith

/-- Integrated endpoint certificate.  This is a single interval inequality:
the `1/x` raw gain and the increasing endpoint potential are never minimized
separately. -/
theorem endpointStripScalarMass_le_weightedRaw_prime_potential
    (w : ℝ → ℝ) (hw : Continuous w) :
    (163 / 50 : ℝ) * (∫ x : ℝ in 3 / 5..1, w x ^ 2) ≤
      (6 / 5 : ℝ) * (∫ x : ℝ in 3 / 5..1, w x ^ 2 / x) +
        (49 / 50 : ℝ) * (∫ x : ℝ in 3 / 5..1, w x ^ 2) +
          (93 / 50 : ℝ) *
            (∫ x : ℝ in 3 / 5..1,
              yoshidaEndpointPotential x * w x ^ 2) := by
  have hmass : IntervalIntegrable (fun x : ℝ ↦ w x ^ 2)
      volume (3 / 5) 1 := by
    exact (hw.pow 2).intervalIntegrable _ _
  have hweighted : IntervalIntegrable (fun x : ℝ ↦ w x ^ 2 / x)
      volume (3 / 5) 1 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div (hw.pow 2).continuousOn continuous_id.continuousOn
    intro x hx
    rw [uIcc_of_le (by norm_num : (3 / 5 : ℝ) ≤ 1)] at hx
    simpa only [id_eq] using (by linarith [hx.1] : x ≠ 0)
  have hpotential : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * w x ^ 2)
      volume (3 / 5) 1 := by
    apply (intervalIntegrable_endpointPotential_mul_sq w hw).mono_set
    intro x hx
    rw [uIcc_of_le (by norm_num : (3 / 5 : ℝ) ≤ 1)] at hx
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact ⟨by linarith [hx.1], hx.2⟩
  have hmono :
      (∫ x : ℝ in 3 / 5..1, (163 / 50 : ℝ) * w x ^ 2) ≤
        ∫ x : ℝ in 3 / 5..1,
          ((6 / 5 : ℝ) * (w x ^ 2 / x) +
            (49 / 50 : ℝ) * w x ^ 2) +
              (93 / 50 : ℝ) *
                (yoshidaEndpointPotential x * w x ^ 2) := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num)
      (hmass.const_mul _) ((hweighted.const_mul _).add
        (hmass.const_mul _) |>.add (hpotential.const_mul _))
    intro x hx
    have hdensity :=
      one_hundred_sixty_three_fiftieths_le_endpointStripDensity hx.1 hx.2
    have hmul := mul_le_mul_of_nonneg_right hdensity (sq_nonneg (w x))
    convert hmul using 1
    field_simp [ne_of_gt (by linarith [hx.1] : 0 < x)]
  rw [intervalIntegral.integral_const_mul] at hmono
  rw [intervalIntegral.integral_add
      ((hweighted.const_mul _).add (hmass.const_mul _))
      (hpotential.const_mul _),
    intervalIntegral.integral_add (hweighted.const_mul _)
      (hmass.const_mul _),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hmono
  exact hmono

private theorem upperStripPotential_le_positiveHalfPotential
    (w : ℝ → ℝ) (hw : Continuous w) :
    (∫ x : ℝ in 3 / 5..1,
        yoshidaEndpointPotential x * w x ^ 2) ≤
      ∫ x : ℝ in 0..1,
        yoshidaEndpointPotential x * w x ^ 2 := by
  have hfull := intervalIntegrable_endpointPotential_mul_sq w hw
  have hleft : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * w x ^ 2)
      volume 0 (3 / 5) := by
    apply hfull.mono_set
    intro x hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 3 / 5)] at hx
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hright : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * w x ^ 2)
      volume (3 / 5) 1 := by
    apply hfull.mono_set
    intro x hx
    rw [uIcc_of_le (by norm_num : (3 / 5 : ℝ) ≤ 1)] at hx
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact ⟨by linarith [hx.1], hx.2⟩
  have hleftNonneg : 0 ≤
      ∫ x : ℝ in 0..3 / 5,
        yoshidaEndpointPotential x * w x ^ 2 := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro x hx
    have hoctic :
        yoshidaEndpointOctic x ≤ yoshidaEndpointPotential x := by
      apply octic_le_endpointPotential
      rw [abs_lt]
      constructor <;> linarith [hx.1, hx.2]
    have hocticNonneg : 0 ≤ yoshidaEndpointOctic x := by
      unfold yoshidaEndpointOctic
      positivity
    exact mul_nonneg (hocticNonneg.trans hoctic) (sq_nonneg _)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hleft hright
  linarith

/-- Complete endpoint-strip closure inside the universal defect.  After the
weighted raw and centered regular rows are coupled, the exact prime and
potential diagonals pay `163/50` of the physical upper-strip mass. -/
theorem endpointStripScalarMass_sub_regularCharge_le_coupledReserve
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w) :
    (163 / 50 : ℝ) * (∫ x : ℝ in 3 / 5..1, w x ^ 2) -
        (fourCellOperatorHalfWidth / 10) *
          (∫ x : ℝ in -1..1, w x ^ 2) ≤
      fourCellOddRawStripCancellationReserve w +
        Real.sqrt 2 * Real.log 2 * fourCellOddEndpointStripEvenMass w +
        (2 - Real.sqrt 2 * Real.log 2) *
          fourCellOddEndpointStripOddMass w +
        (93 / 50 : ℝ) *
          (∫ x : ℝ in 0..1,
            yoshidaEndpointPotential x * w x ^ 2) -
        2 * fourCellOperatorHalfWidth *
          (∫ t : ℝ in 0..2,
            yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
              centeredEndpointCorrelation w t) := by
  have hdiagonal := endpointStripScalarMass_le_weightedRaw_prime_potential
    w hw.continuous
  have hraw :=
    upperStripWeightedMass_sub_regularCharge_le_rawReserve_sub_regular
      w hw hodd
  have hprime := forty_nine_fiftieths_upperStripMass_le_primeDiagonal
    w hw.continuous
  have hpotential := upperStripPotential_le_positiveHalfPotential
    w hw.continuous
  have hpotentialMul := mul_le_mul_of_nonneg_left hpotential
    (by norm_num : (0 : ℝ) ≤ 93 / 50)
  linarith

private theorem fourCellScalar_add_regularCharge_lt_163_div_50 :
    2 * (Real.log (2 * fourCellOperatorHalfWidth) +
          Real.eulerMascheroniConstant + Real.log Real.pi) +
        (3 / 200 : ℝ) + fourCellOperatorHalfWidth / 5 < 163 / 50 := by
  have hscalar := fourCellScalar_lt_31577_div_20000
  have hlog := strict_log_two_bounds.2
  have hwidth : fourCellOperatorHalfWidth / 5 < (1733 / 20000 : ℝ) := by
    unfold fourCellOperatorHalfWidth
    nlinarith
  nlinarith [hscalar, hwidth]

/-- Quantitative form of the same scalar estimate.  Keeping the rational
gap instead of rounding all the way to `163/50` leaves `13/20000` of the
complete positive-half mass available to the tail Schur norm. -/
private theorem fourCellScalar_add_regularCharge_le_65187_div_20000 :
    2 * (Real.log (2 * fourCellOperatorHalfWidth) +
          Real.eulerMascheroniConstant + Real.log Real.pi) +
        (3 / 200 : ℝ) + fourCellOperatorHalfWidth / 5 ≤
      65187 / 20000 := by
  have hscalar := fourCellScalar_lt_31577_div_20000.le
  have hlog := strict_log_two_bounds.2
  have hwidth : fourCellOperatorHalfWidth / 5 ≤
      (1733 / 20000 : ℝ) := by
    unfold fourCellOperatorHalfWidth
    nlinarith
  nlinarith

/-- Structural localization of the remaining universal defect.  The entire
endpoint strip is now paid; without using any further raw square, a possible
negative part is confined to the physical lower interval `[0,3/5]`. -/
theorem neg_lowerIntervalScalarMass_le_core_add_localWidthDefect
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w) :
    -(163 / 50 : ℝ) * (∫ x : ℝ in 0..3 / 5, w x ^ 2) ≤
      fourCellOddHalfCoreReserve w +
        fourCellOddStripLocalWidthDefect w := by
  let L : ℝ := ∫ x : ℝ in 0..3 / 5, w x ^ 2
  let U : ℝ := ∫ x : ℝ in 3 / 5..1, w x ^ 2
  let H : ℝ := ∫ x : ℝ in 0..1, w x ^ 2
  let C : ℝ :=
    2 * (Real.log (2 * fourCellOperatorHalfWidth) +
      Real.eulerMascheroniConstant + Real.log Real.pi) + 3 / 200
  let E : ℝ :=
    fourCellOddRawStripCancellationReserve w +
      Real.sqrt 2 * Real.log 2 * fourCellOddEndpointStripEvenMass w +
      (2 - Real.sqrt 2 * Real.log 2) *
        fourCellOddEndpointStripOddMass w +
      (93 / 50 : ℝ) *
        (∫ x : ℝ in 0..1, yoshidaEndpointPotential x * w x ^ 2) -
      2 * fourCellOperatorHalfWidth *
        (∫ t : ℝ in 0..2,
          yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
            centeredEndpointCorrelation w t)
  have hendpoint :
      (163 / 50 : ℝ) * U - fourCellOperatorHalfWidth / 10 *
          (∫ x : ℝ in -1..1, w x ^ 2) ≤ E := by
    simpa only [U, E] using
      endpointStripScalarMass_sub_regularCharge_le_coupledReserve
        w hw hodd
  have hcentered : (∫ x : ℝ in -1..1, w x ^ 2) = 2 * H := by
    simpa only [H] using integral_sq_eq_two_mul_positiveHalf
      w hw.continuous (Or.inr hodd)
  have hlowerInt : IntervalIntegrable (fun x : ℝ ↦ w x ^ 2)
      volume 0 (3 / 5) := (hw.continuous.pow 2).intervalIntegrable _ _
  have hupperInt : IntervalIntegrable (fun x : ℝ ↦ w x ^ 2)
      volume (3 / 5) 1 := (hw.continuous.pow 2).intervalIntegrable _ _
  have hhalfSplit : L + U = H := by
    simpa only [L, U, H] using
      intervalIntegral.integral_add_adjacent_intervals hlowerInt hupperInt
  have hhalfNonneg : 0 ≤ H := by
    dsimp only [H]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun x _hx ↦ sq_nonneg _)
  have hcoefficient : C + fourCellOperatorHalfWidth / 5 ≤ 163 / 50 := by
    simpa only [C] using fourCellScalar_add_regularCharge_lt_163_div_50.le
  have hcoefficientMul :=
    mul_le_mul_of_nonneg_right hcoefficient hhalfNonneg
  have hcharge (a m : ℝ) : a / 10 * (2 * m) = a / 5 * m := by
    ring
  rw [hcentered, hcharge] at hendpoint
  have hbudget :
      C * H + fourCellOperatorHalfWidth / 5 * H ≤
        (163 / 50 : ℝ) * H := by
    calc
      C * H + fourCellOperatorHalfWidth / 5 * H =
          (C + fourCellOperatorHalfWidth / 5) * H := by ring
      _ ≤ (163 / 50 : ℝ) * H := hcoefficientMul
  rw [fourCellOddHalfCoreReserve_add_localWidthDefect_eq_raw_add_reduced]
  unfold fourCellOddStripReducedRemainder
  dsimp only [L, U, H, C, E] at hendpoint hhalfSplit hbudget ⊢
  linarith

/-- Universal positive-half raw gap in the odd sector.  This is the centered
mean-zero logarithmic gap transported through the exact parity fold; it is
the scale-invariant input for the remaining lower-square reserve. -/
theorem four_mul_positiveHalfMass_le_coupledRawEnergy
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w) :
    4 * (∫ x : ℝ in 0..1, w x ^ 2) ≤
      fourCellPositiveHalfRawSameSignEnergy w +
        fourCellPositiveHalfRawReflectedEnergy w (-1) := by
  let f : unitInterval → ℝ := fun t ↦ centeredPullback w (t : ℝ)
  have hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w :=
    hw.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1)
  obtain ⟨C, hLip⟩ := exists_lipschitzWith_centeredPullback w hlocal
  have hfcont : Continuous f := by
    dsimp only [f, centeredPullback]
    fun_prop
  have hfmem : MemLp f 2 :=
    hfcont.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  have henergy : Integrable (unitIntervalRawLogEnergyIntegrand f) :=
    integrable_unitIntervalRawLogEnergyIntegrand_of_lipschitzWith f
      (by simpa only [f] using hLip)
  have hreflect := intervalIntegral.integral_comp_neg
    (f := w) (a := (-1 : ℝ)) (b := 1)
  have hneg : (∫ x : ℝ in -1..1, w (-x)) =
      -(∫ x : ℝ in -1..1, w x) := by
    rw [show (fun x : ℝ ↦ w (-x)) = fun x ↦ -w x by
      funext x
      exact hodd x]
    exact intervalIntegral.integral_neg
  have hmean : (∫ x : ℝ in -1..1, w x) = 0 := by
    rw [hneg] at hreflect
    norm_num at hreflect
    linarith
  have hgap :=
    CenteredLogEnergyGap.four_mul_integral_sq_le_centeredRawLogEnergy
      w (by simpa only [f] using hfmem)
        (by simpa only [f] using henergy) hmean
  have hraw := centeredRawLogEnergy_div_four_eq_positiveHalf_odd
    w hlocal hodd
  have hmass := integral_sq_eq_two_mul_positiveHalf
    w hw.continuous (Or.inr hodd)
  linarith

private theorem integral_lowerRescale_sq (w : ℝ → ℝ) :
    (∫ x : ℝ in 0..1, w ((3 / 5 : ℝ) * x) ^ 2) =
      (5 / 3 : ℝ) * ∫ x : ℝ in 0..3 / 5, w x ^ 2 := by
  have hscale := intervalIntegral.integral_comp_mul_left
    (a := (0 : ℝ)) (b := 1) (c := (3 / 5 : ℝ))
    (fun x : ℝ ↦ w x ^ 2) (by norm_num)
  norm_num at hscale ⊢
  exact hscale

private theorem lowerRescale_sameSignEnergy (w : ℝ → ℝ) :
    fourCellPositiveHalfRawSameSignEnergy
        (fun x : ℝ ↦ w ((3 / 5 : ℝ) * x)) =
      (5 / 3 : ℝ) *
        (∫ x : ℝ in 0..3 / 5, ∫ y : ℝ in 0..3 / 5,
          (w x - w y) ^ 2 / |x - y|) := by
  unfold fourCellPositiveHalfRawSameSignEnergy
  calc
    (∫ x : ℝ in 0..1, ∫ y : ℝ in 0..1,
        (w ((3 / 5 : ℝ) * x) - w ((3 / 5 : ℝ) * y)) ^ 2 /
          |x - y|) =
      ∫ x : ℝ in 0..1, ∫ y : ℝ in 0..1,
        (3 / 5 : ℝ) *
          ((w ((3 / 5 : ℝ) * x) - w ((3 / 5 : ℝ) * y)) ^ 2 /
            |(3 / 5 : ℝ) * x - (3 / 5 : ℝ) * y|) := by
      apply intervalIntegral.integral_congr
      intro x _hx
      apply intervalIntegral.integral_congr
      intro y _hy
      change
        (w ((3 / 5 : ℝ) * x) - w ((3 / 5 : ℝ) * y)) ^ 2 /
            |x - y| =
          (3 / 5 : ℝ) *
            ((w ((3 / 5 : ℝ) * x) - w ((3 / 5 : ℝ) * y)) ^ 2 /
              |(3 / 5 : ℝ) * x - (3 / 5 : ℝ) * y|)
      rw [show (3 / 5 : ℝ) * x - (3 / 5 : ℝ) * y =
          (3 / 5 : ℝ) * (x - y) by ring, abs_mul]
      norm_num
      ring
    _ = ∫ x : ℝ in 0..1, ∫ y : ℝ in 0..3 / 5,
        (w ((3 / 5 : ℝ) * x) - w y) ^ 2 /
          |(3 / 5 : ℝ) * x - y| := by
      apply intervalIntegral.integral_congr
      intro x _hx
      change
        (∫ y : ℝ in 0..1, (3 / 5 : ℝ) *
          ((w ((3 / 5 : ℝ) * x) - w ((3 / 5 : ℝ) * y)) ^ 2 /
            |(3 / 5 : ℝ) * x - (3 / 5 : ℝ) * y|)) =
        ∫ y : ℝ in 0..3 / 5,
          (w ((3 / 5 : ℝ) * x) - w y) ^ 2 /
            |(3 / 5 : ℝ) * x - y|
      rw [intervalIntegral.integral_const_mul]
      have hscale := intervalIntegral.integral_comp_mul_left
        (a := (0 : ℝ)) (b := 1) (c := (3 / 5 : ℝ))
        (fun y : ℝ ↦
          (w ((3 / 5 : ℝ) * x) - w y) ^ 2 /
            |(3 / 5 : ℝ) * x - y|) (by norm_num)
      norm_num at hscale ⊢
      rw [hscale]
      ring
    _ = (5 / 3 : ℝ) *
        (∫ x : ℝ in 0..3 / 5, ∫ y : ℝ in 0..3 / 5,
          (w x - w y) ^ 2 / |x - y|) := by
      have hscale := intervalIntegral.integral_comp_mul_left
        (a := (0 : ℝ)) (b := 1) (c := (3 / 5 : ℝ))
        (fun x : ℝ ↦ ∫ y : ℝ in 0..3 / 5,
          (w x - w y) ^ 2 / |x - y|) (by norm_num)
      norm_num at hscale ⊢
      exact hscale

private theorem lowerRescale_reflectedEnergy (w : ℝ → ℝ) :
    fourCellPositiveHalfRawReflectedEnergy
        (fun x : ℝ ↦ w ((3 / 5 : ℝ) * x)) (-1) =
      (5 / 3 : ℝ) *
        (∫ x : ℝ in 0..3 / 5, ∫ y : ℝ in 0..3 / 5,
          (w x + w y) ^ 2 / (x + y)) := by
  unfold fourCellPositiveHalfRawReflectedEnergy
  norm_num
  calc
    (∫ x : ℝ in 0..1, ∫ y : ℝ in 0..1,
        (w ((3 / 5 : ℝ) * x) + w ((3 / 5 : ℝ) * y)) ^ 2 /
          (x + y)) =
      ∫ x : ℝ in 0..1, ∫ y : ℝ in 0..1,
        (3 / 5 : ℝ) *
          ((w ((3 / 5 : ℝ) * x) + w ((3 / 5 : ℝ) * y)) ^ 2 /
            ((3 / 5 : ℝ) * x + (3 / 5 : ℝ) * y)) := by
      apply intervalIntegral.integral_congr
      intro x _hx
      apply intervalIntegral.integral_congr
      intro y _hy
      change
        (w ((3 / 5 : ℝ) * x) + w ((3 / 5 : ℝ) * y)) ^ 2 /
            (x + y) =
          (3 / 5 : ℝ) *
            ((w ((3 / 5 : ℝ) * x) + w ((3 / 5 : ℝ) * y)) ^ 2 /
              ((3 / 5 : ℝ) * x + (3 / 5 : ℝ) * y))
      rw [show (3 / 5 : ℝ) * x + (3 / 5 : ℝ) * y =
          (3 / 5 : ℝ) * (x + y) by ring]
      simp only [div_eq_mul_inv, mul_inv_rev]
      norm_num
      ring
    _ = ∫ x : ℝ in 0..1, ∫ y : ℝ in 0..3 / 5,
        (w ((3 / 5 : ℝ) * x) + w y) ^ 2 /
          ((3 / 5 : ℝ) * x + y) := by
      apply intervalIntegral.integral_congr
      intro x _hx
      change
        (∫ y : ℝ in 0..1, (3 / 5 : ℝ) *
          ((w ((3 / 5 : ℝ) * x) + w ((3 / 5 : ℝ) * y)) ^ 2 /
            ((3 / 5 : ℝ) * x + (3 / 5 : ℝ) * y))) =
        ∫ y : ℝ in 0..3 / 5,
          (w ((3 / 5 : ℝ) * x) + w y) ^ 2 /
            ((3 / 5 : ℝ) * x + y)
      rw [intervalIntegral.integral_const_mul]
      have hscale := intervalIntegral.integral_comp_mul_left
        (a := (0 : ℝ)) (b := 1) (c := (3 / 5 : ℝ))
        (fun y : ℝ ↦
          (w ((3 / 5 : ℝ) * x) + w y) ^ 2 /
            ((3 / 5 : ℝ) * x + y)) (by norm_num)
      norm_num at hscale ⊢
      rw [hscale]
      ring
    _ = (5 / 3 : ℝ) *
        (∫ x : ℝ in 0..3 / 5, ∫ y : ℝ in 0..3 / 5,
          (w x + w y) ^ 2 / (x + y)) := by
      have hscale := intervalIntegral.integral_comp_mul_left
        (a := (0 : ℝ)) (b := 1) (c := (3 / 5 : ℝ))
        (fun x : ℝ ↦ ∫ y : ℝ in 0..3 / 5,
          (w x + w y) ^ 2 / (x + y)) (by norm_num)
      norm_num at hscale ⊢
      exact hscale

/-- Sharp scale-invariant raw gap on the lower positive-half square. -/
theorem four_mul_lowerIntervalMass_le_lowerNestedCoupledRaw
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w) :
    4 * (∫ x : ℝ in 0..3 / 5, w x ^ 2) ≤
      (∫ x : ℝ in 0..3 / 5, ∫ y : ℝ in 0..3 / 5,
        (w x - w y) ^ 2 / |x - y|) +
      ∫ x : ℝ in 0..3 / 5, ∫ y : ℝ in 0..3 / 5,
        (w x + w y) ^ 2 / (x + y) := by
  let r : ℝ → ℝ := fun x ↦ w ((3 / 5 : ℝ) * x)
  have hr : ContDiff ℝ 1 r := by
    dsimp only [r]
    fun_prop
  have hrodd : Function.Odd r := by
    intro x
    dsimp only [r]
    rw [show (3 / 5 : ℝ) * -x = -((3 / 5 : ℝ) * x) by ring, hodd]
  have hgap := four_mul_positiveHalfMass_le_coupledRawEnergy r hr hrodd
  rw [show (∫ x : ℝ in 0..1, r x ^ 2) =
        (5 / 3 : ℝ) * ∫ x : ℝ in 0..3 / 5, w x ^ 2 by
      simpa only [r] using integral_lowerRescale_sq w,
    show fourCellPositiveHalfRawSameSignEnergy r =
        (5 / 3 : ℝ) *
          (∫ x : ℝ in 0..3 / 5, ∫ y : ℝ in 0..3 / 5,
            (w x - w y) ^ 2 / |x - y|) by
      simpa only [r] using lowerRescale_sameSignEnergy w,
    show fourCellPositiveHalfRawReflectedEnergy r (-1) =
        (5 / 3 : ℝ) *
          (∫ x : ℝ in 0..3 / 5, ∫ y : ℝ in 0..3 / 5,
            (w x + w y) ^ 2 / (x + y)) by
      simpa only [r] using lowerRescale_reflectedEnergy w] at hgap
  linarith

/-- The lower-square raw gap has a quantitative surplus away from its
linear odd ground state.  The coefficient is obtained from the exact
degree-one/odd-tail spectral split after rescaling `[0,3/5]` to `[0,1]`;
all odd degrees at least three retain their `11/6` harmonic weight. -/
theorem lowerIntervalP1Surplus_le_half_lowerNestedCoupledRaw
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w) :
    (11 / 3 : ℝ) * (∫ x : ℝ in 0..3 / 5, w x ^ 2) -
        (625 / 27 : ℝ) *
          (∫ x : ℝ in 0..3 / 5, x * w x) ^ 2 ≤
      (1 / 2 : ℝ) *
        ((∫ x : ℝ in 0..3 / 5, ∫ y : ℝ in 0..3 / 5,
            (w x - w y) ^ 2 / |x - y|) +
          ∫ x : ℝ in 0..3 / 5, ∫ y : ℝ in 0..3 / 5,
            (w x + w y) ^ 2 / (x + y)) := by
  let r : ℝ → ℝ := fun x ↦ w ((3 / 5 : ℝ) * x)
  let f : unitInterval → ℝ := fun t ↦ centeredPullback r (t : ℝ)
  let A : ℝ := ∫ x : ℝ in 0..3 / 5, x * w x
  have hr : ContDiff ℝ 1 r := by
    dsimp only [r]
    fun_prop
  have hrodd : Function.Odd r := by
    intro x
    dsimp only [r]
    rw [show (3 / 5 : ℝ) * -x = -((3 / 5 : ℝ) * x) by ring, hodd]
  have hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) r :=
    hr.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1)
  obtain ⟨C, hLip⟩ := exists_lipschitzWith_centeredPullback r hlocal
  have hfcont : Continuous f := by
    dsimp only [f, centeredPullback]
    fun_prop
  have hfmem : MemLp f 2 :=
    hfcont.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  have henergy : Integrable (unitIntervalRawLogEnergyIntegrand f) :=
    integrable_unitIntervalRawLogEnergyIntegrand_of_lipschitzWith f
      (by simpa only [f] using hLip)
  have hspectral := centered_odd_one_three_tail_energy_le
    r hr.continuous (by simpa only [f] using hfmem)
      (by simpa only [f] using henergy) hrodd
  have hmass0 := integral_centeredOddOneThreeResidual_sq r hr.continuous
  have hmassFold := integral_sq_eq_two_mul_positiveHalf
    r hr.continuous (Or.inr hrodd)
  have hmassScale :
      (∫ x : ℝ in 0..1, r x ^ 2) =
        (5 / 3 : ℝ) * ∫ x : ℝ in 0..3 / 5, w x ^ 2 := by
    simpa only [r] using integral_lowerRescale_sq w
  have hrxEven : Function.Even (fun x : ℝ ↦ r x * centeredP1 x) := by
    intro x
    unfold centeredP1
    change r (-x) * (-x) = r x * x
    rw [hrodd]
    ring
  have hrxInt : IntervalIntegrable (fun x : ℝ ↦ r x * centeredP1 x)
      volume (-1) 1 := by
    exact (hr.continuous.mul (by
      unfold centeredP1
      fun_prop)).intervalIntegrable _ _
  have hmomentFold :
      (∫ x : ℝ in -1..1, r x * centeredP1 x) =
        2 * ∫ x : ℝ in 0..1, r x * centeredP1 x :=
    integral_neg_one_one_eq_two_mul_zero_one_of_even
      (fun x : ℝ ↦ r x * centeredP1 x) hrxInt hrxEven
  have hmomentScale :
      (∫ x : ℝ in 0..1, r x * centeredP1 x) =
        (25 / 9 : ℝ) * A := by
    have hscale := intervalIntegral.integral_comp_mul_left
      (a := (0 : ℝ)) (b := 1) (c := (3 / 5 : ℝ))
      (fun x : ℝ ↦ x * w x) (by norm_num)
    norm_num at hscale ⊢
    dsimp only [r, A]
    unfold centeredP1
    rw [show (fun x : ℝ ↦ w ((3 / 5 : ℝ) * x) * x) =
        fun x ↦ (5 / 3 : ℝ) *
          (((3 / 5 : ℝ) * x) * w ((3 / 5 : ℝ) * x)) by
      funext x
      ring,
      intervalIntegral.integral_const_mul, hscale]
    ring
  have hcoeff : centeredOddP1Coefficient r = (25 / 3 : ℝ) * A := by
    unfold centeredOddP1Coefficient
    rw [hmomentFold, hmomentScale]
    ring
  have hmass :
      (∫ x : ℝ in -1..1, r x ^ 2) =
        (2 / 3 : ℝ) * centeredOddP1Coefficient r ^ 2 +
          (2 / 7 : ℝ) * centeredOddP3Coefficient r ^ 2 +
            ∫ x : ℝ in -1..1,
              centeredOddOneThreeResidual r x ^ 2 := by
    linarith
  have htail :
      (11 / 6 : ℝ) * (∫ x : ℝ in -1..1, r x ^ 2) -
          (5 / 9 : ℝ) * centeredOddP1Coefficient r ^ 2 ≤
        centeredRawLogEnergy r / 4 := by
    have hres0 : 0 ≤ ∫ x : ℝ in -1..1,
        centeredOddOneThreeResidual r x ^ 2 :=
      intervalIntegral.integral_nonneg (by norm_num)
        (fun x _hx ↦ sq_nonneg _)
    nlinarith
  have hraw := centeredRawLogEnergy_div_four_eq_positiveHalf_odd
    r hlocal hrodd
  have hsame := lowerRescale_sameSignEnergy w
  have hreflected := lowerRescale_reflectedEnergy w
  rw [hraw, hmassFold, hmassScale, hcoeff] at htail
  rw [show fourCellPositiveHalfRawSameSignEnergy r =
        (5 / 3 : ℝ) *
          (∫ x : ℝ in 0..3 / 5, ∫ y : ℝ in 0..3 / 5,
            (w x - w y) ^ 2 / |x - y|) by
      simpa only [r] using hsame,
    show fourCellPositiveHalfRawReflectedEnergy r (-1) =
        (5 / 3 : ℝ) *
          (∫ x : ℝ in 0..3 / 5, ∫ y : ℝ in 0..3 / 5,
            (w x + w y) ^ 2 / (x + y)) by
      simpa only [r] using hreflected] at htail
  dsimp only [A] at htail ⊢
  nlinarith

private theorem sq_intervalIntegral_mul_le_zero_three_fifths
    (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    (∫ x : ℝ in 0..3 / 5, f x * g x) ^ 2 ≤
      (∫ x : ℝ in 0..3 / 5, f x ^ 2) *
        (∫ x : ℝ in 0..3 / 5, g x ^ 2) := by
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) (3 / 5))
  have hfMeas : AEStronglyMeasurable f μ :=
    hf.aestronglyMeasurable.restrict
  have hgMeas : AEStronglyMeasurable g μ :=
    hg.aestronglyMeasurable.restrict
  have hfLp : MemLp f 2 μ := by
    rw [memLp_two_iff_integrable_sq_norm hfMeas]
    have hcompact : IntegrableOn (fun x : ℝ ↦ ‖f x‖ ^ 2)
        (Icc (0 : ℝ) (3 / 5)) :=
      (hf.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
    exact hcompact.mono_set Ioc_subset_Icc_self
  have hgLp : MemLp g 2 μ := by
    rw [memLp_two_iff_integrable_sq_norm hgMeas]
    have hcompact : IntegrableOn (fun x : ℝ ↦ ‖g x‖ ^ 2)
        (Icc (0 : ℝ) (3 / 5)) :=
      (hg.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
    exact hcompact.mono_set Ioc_subset_Icc_self
  have h := sq_integral_mul_le_weighted μ (fun _ : ℝ ↦ 1) f g
    (by simp) (by simpa using hfLp) (by simpa using hgLp)
  repeat rw [intervalIntegral.integral_of_le (by norm_num)]
  simpa only [μ, div_one, one_mul] using h

/-- Explicit positive square left by the cross-rectangle odd ground-state
transform after its sharp `6/(5x)` endpoint diagonal is removed. -/
def fourCellOddCrossP1Square (w : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ in 3 / 5..1, ∫ y : ℝ in 0..3 / 5,
    2 * (y * w x - x * w y) ^ 2 / x ^ 3

/-- Pointwise form of the strengthened cross ground-state payment.  The
exact remainder has denominator `x (x-y) (x+y) ≤ x³`, so the simpler
inverse-cube square is retained together with the full `2 a²/x` diagonal. -/
theorem two_mul_sq_div_add_crossP1Square_le_coupledRawKernel
    {x y a b : ℝ} (hy : 0 ≤ y) (hxy : y < x) :
    2 * a ^ 2 / x + 2 * (y * a - x * b) ^ 2 / x ^ 3 ≤
      (a - b) ^ 2 / (x - y) + (a + b) ^ 2 / (x + y) := by
  have hx : 0 < x := hy.trans_lt hxy
  have hsub : 0 < x - y := sub_pos.mpr hxy
  have hsum : 0 < x + y := add_pos_of_pos_of_nonneg hx hy
  have hden : 0 < x * (x - y) * (x + y) := by positivity
  have hx3 : 0 < x ^ 3 := pow_pos hx 3
  have hdenle : x * (x - y) * (x + y) ≤ x ^ 3 := by
    have hxy2 : 0 ≤ x * y ^ 2 := mul_nonneg hx.le (sq_nonneg y)
    nlinarith
  have hrem :
      2 * (y * a - x * b) ^ 2 / x ^ 3 ≤
        2 * (y * a - x * b) ^ 2 /
          (x * (x - y) * (x + y)) :=
    div_le_div_of_nonneg_left (by positivity) hden hdenle
  rw [show
      (a - b) ^ 2 / (x - y) + (a + b) ^ 2 / (x + y) =
        2 * a ^ 2 / x +
          2 * (y * a - x * b) ^ 2 /
            (x * (x - y) * (x + y)) by
    field_simp [hx.ne', hsub.ne', hsum.ne']
    ring]
  linarith

private theorem intervalIntegral_integral_eq_setIntegral_rectangle
    (F : ℝ × ℝ → ℝ) (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d)
    (hF : IntegrableOn F (Icc a b ×ˢ Icc c d)
      ((volume : Measure ℝ).prod volume)) :
    (∫ x : ℝ in a..b, ∫ y : ℝ in c..d, F (x, y)) =
      ∫ p : ℝ × ℝ in Icc a b ×ˢ Icc c d, F p
        ∂((volume : Measure ℝ).prod volume) := by
  calc
    (∫ x : ℝ in a..b, ∫ y : ℝ in c..d, F (x, y)) =
        ∫ x : ℝ in Icc a b, ∫ y : ℝ in Icc c d, F (x, y) := by
      rw [intervalIntegral.integral_of_le hab,
        ← integral_Icc_eq_integral_Ioc]
      apply setIntegral_congr_fun measurableSet_Icc
      intro x _hx
      change (∫ y : ℝ in c..d, F (x, y)) =
        ∫ y : ℝ in Icc c d, F (x, y)
      rw [intervalIntegral.integral_of_le hcd,
        ← integral_Icc_eq_integral_Ioc]
    _ = ∫ p : ℝ × ℝ in Icc a b ×ˢ Icc c d, F p
          ∂((volume : Measure ℝ).prod volume) := by
      exact (setIntegral_prod F hF).symm

/-- The cross rectangle retains both the sharp weighted endpoint diagonal
and the complete inverse-cube P₁ ground-state square. -/
theorem six_fifths_upperStripWeightedMass_add_crossP1Square_le_cross_coupledRaw
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) :
    (6 / 5 : ℝ) * (∫ x : ℝ in 3 / 5..1, w x ^ 2 / x) +
        fourCellOddCrossP1Square w ≤
      ∫ p : ℝ × ℝ in
        Icc (3 / 5 : ℝ) 1 ×ˢ Ico (0 : ℝ) (3 / 5),
          fourCellOddCoupledRawPair w p
            ∂((volume : Measure ℝ).prod volume) := by
  let A : Set ℝ := Ico (0 : ℝ) (3 / 5)
  let A' : Set ℝ := Icc (0 : ℝ) (3 / 5)
  let B : Set ℝ := Icc (3 / 5 : ℝ) 1
  let P : Set (ℝ × ℝ) := B ×ˢ A
  let P' : Set (ℝ × ℝ) := B ×ˢ A'
  let K : ℝ × ℝ → ℝ := fourCellOddCoupledRawPair w
  let D : ℝ × ℝ → ℝ := fun p ↦ 2 * w p.1 ^ 2 / p.1
  let S : ℝ × ℝ → ℝ := fun p ↦
    2 * (p.2 * w p.1 - p.1 * w p.2) ^ 2 / p.1 ^ 3
  let L : ℝ × ℝ → ℝ := fun p ↦ D p + S p
  have hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w :=
    hw.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1)
  obtain ⟨C, hC⟩ := hlocal.exists_lipschitzOnWith_of_compact isCompact_Icc
  have hfull :=
    integrableOn_centeredLogDifferenceKernel_prod_of_lipschitzOnWith w hC
  have hBsub : B ⊆ Icc (-1 : ℝ) 1 := by
    intro x hx
    exact ⟨by linarith [hx.1], hx.2⟩
  have hAsub : A ⊆ Icc (-1 : ℝ) 1 := by
    intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hsame : IntegrableOn
      (fun p : ℝ × ℝ ↦ centeredLogDifferenceKernel w p.1 p.2) P
      ((volume : Measure ℝ).prod volume) :=
    hfull.mono_set (Set.prod_mono hBsub hAsub)
  let J : ℝ × ℝ → ℝ := fun p ↦
    (w p.1 + w p.2) ^ 2 / (p.1 + p.2)
  have hJcont : ContinuousOn J P' := by
    dsimp only [J, P', B, A']
    apply ContinuousOn.div
    · exact ((hw.continuous.comp continuous_fst).add
        (hw.continuous.comp continuous_snd)).pow 2 |>.continuousOn
    · exact (continuous_fst.add continuous_snd).continuousOn
    · intro p hp
      dsimp only
      linarith [hp.1.1, hp.2.1]
  have hPsub : P ⊆ P' := by
    intro p hp
    exact ⟨hp.1, ⟨hp.2.1, hp.2.2.le⟩⟩
  have hP'compact : IsCompact P' := by
    dsimp only [P', B, A']
    exact isCompact_Icc.prod isCompact_Icc
  have hJ : IntegrableOn J P ((volume : Measure ℝ).prod volume) :=
    (hJcont.integrableOn_compact hP'compact).mono_set hPsub
  have hK : IntegrableOn K P ((volume : Measure ℝ).prod volume) := by
    apply hsame.add hJ |>.congr
    filter_upwards [ae_restrict_mem
      (measurableSet_Icc.prod measurableSet_Ico)] with p hp
    dsimp only [K, J, P, B, A, fourCellOddCoupledRawPair]
    unfold centeredLogDifferenceKernel
    rfl
  have hDcont : ContinuousOn D P' := by
    dsimp only [D, P', B, A']
    apply ContinuousOn.div
    · exact (continuous_const.mul
        ((hw.continuous.comp continuous_fst).pow 2)).continuousOn
    · exact continuous_fst.continuousOn
    · intro p hp
      dsimp only
      linarith [hp.1.1]
  have hScont : ContinuousOn S P' := by
    dsimp only [S, P', B, A']
    apply ContinuousOn.div
    · exact (continuous_const.mul
        (((continuous_snd.mul (hw.continuous.comp continuous_fst)).sub
          (continuous_fst.mul (hw.continuous.comp continuous_snd))).pow 2))
            |>.continuousOn
    · exact ((continuous_fst.pow 3).continuousOn)
    · intro p hp
      exact pow_ne_zero 3 (by linarith [hp.1.1] : p.1 ≠ 0)
  have hDlarge : IntegrableOn D P' ((volume : Measure ℝ).prod volume) :=
    hDcont.integrableOn_compact hP'compact
  have hSlarge : IntegrableOn S P' ((volume : Measure ℝ).prod volume) :=
    hScont.integrableOn_compact hP'compact
  have hD : IntegrableOn D P ((volume : Measure ℝ).prod volume) :=
    hDlarge.mono_set hPsub
  have hS : IntegrableOn S P ((volume : Measure ℝ).prod volume) :=
    hSlarge.mono_set hPsub
  have hL : IntegrableOn L P ((volume : Measure ℝ).prod volume) := by
    dsimp only [L]
    exact hD.add hS
  have hPmeas : MeasurableSet P := by
    dsimp only [P, B, A]
    exact measurableSet_Icc.prod measurableSet_Ico
  have hpoint : ∀ p ∈ P, L p ≤ K p := by
    intro p hp
    have hy : 0 ≤ p.2 := hp.2.1
    have hxy : p.2 < p.1 := by linarith [hp.1.1, hp.2.2]
    dsimp only [L, D, S, K, fourCellOddCoupledRawPair]
    rw [abs_of_pos (sub_pos.mpr hxy)]
    exact two_mul_sq_div_add_crossP1Square_le_coupledRawKernel hy hxy
  have hmono :
      (∫ p : ℝ × ℝ in P, L p
        ∂((volume : Measure ℝ).prod volume)) ≤
      ∫ p : ℝ × ℝ in P, K p
        ∂((volume : Measure ℝ).prod volume) :=
    setIntegral_mono_on hL hK hPmeas hpoint
  have hBmass : (∫ x : ℝ in B, w x ^ 2 / x) =
      ∫ x : ℝ in 3 / 5..1, w x ^ 2 / x := by
    dsimp only [B]
    rw [intervalIntegral.integral_of_le (by norm_num),
      ← integral_Icc_eq_integral_Ioc]
  have hDvalue :
      (∫ p : ℝ × ℝ in P, D p
        ∂((volume : Measure ℝ).prod volume)) =
      (6 / 5 : ℝ) * (∫ x : ℝ in 3 / 5..1, w x ^ 2 / x) := by
    dsimp only [P, D, B, A]
    rw [show (fun p : ℝ × ℝ ↦ 2 * w p.1 ^ 2 / p.1) =
        fun p ↦ (2 * (w p.1 ^ 2 / p.1)) * (1 : ℝ) by
      funext p
      rw [mul_one]
      exact mul_div_assoc _ _ _,
      setIntegral_prod_mul
        (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
        (fun x : ℝ ↦ 2 * (w x ^ 2 / x)) (fun _x : ℝ ↦ (1 : ℝ))
        (Icc (3 / 5 : ℝ) 1) (Ico (0 : ℝ) (3 / 5)),
      integral_const_mul, hBmass, setIntegral_const]
    have hmeasure :
        (volume : Measure ℝ).real (Ico (0 : ℝ) (3 / 5)) = 3 / 5 := by
      norm_num
    rw [hmeasure, smul_eq_mul, mul_one]
    ring
  have hsets : P =ᵐ[((volume : Measure ℝ).prod volume)] P' := by
    dsimp only [P, P', B, A, A']
    exact Measure.set_prod_ae_eq (Filter.EventuallyEq.rfl) Ico_ae_eq_Icc
  have hSset :
      (∫ p : ℝ × ℝ in P, S p
          ∂((volume : Measure ℝ).prod volume)) =
        ∫ p : ℝ × ℝ in P', S p
          ∂((volume : Measure ℝ).prod volume) :=
    setIntegral_congr_set hsets
  have hSbridge := intervalIntegral_integral_eq_setIntegral_rectangle
    S (3 / 5) 1 0 (3 / 5) (by norm_num) (by norm_num) hSlarge
  have hSvalue :
      (∫ p : ℝ × ℝ in P, S p
        ∂((volume : Measure ℝ).prod volume)) =
      fourCellOddCrossP1Square w := by
    rw [hSset]
    change (∫ p : ℝ × ℝ in
        Icc (3 / 5 : ℝ) 1 ×ˢ Icc (0 : ℝ) (3 / 5), S p
          ∂((volume : Measure ℝ).prod volume)) =
      fourCellOddCrossP1Square w
    rw [← hSbridge]
    unfold fourCellOddCrossP1Square S
    rfl
  have hLvalue :
      (∫ p : ℝ × ℝ in P, L p
        ∂((volume : Measure ℝ).prod volume)) =
      (6 / 5 : ℝ) * (∫ x : ℝ in 3 / 5..1, w x ^ 2 / x) +
        fourCellOddCrossP1Square w := by
    dsimp only [L]
    rw [MeasureTheory.integral_add hD hS, hDvalue, hSvalue]
  simpa only [P, K, B, A] using hLvalue.symm.trans_le hmono

private theorem sq_upperP1Moment_le_invCubeMass
    (h : ℝ → ℝ) (hh : Continuous h) :
    (∫ x : ℝ in 3 / 5..1, x * h x) ^ 2 ≤
      (7448 / 46875 : ℝ) *
        ∫ x : ℝ in 3 / 5..1, h x ^ 2 / x ^ 3 := by
  let μ : Measure ℝ := volume.restrict (Ioc (3 / 5 : ℝ) 1)
  let W : ℝ → ℝ := fun x ↦ 1 / x ^ 3
  let G : ℝ → ℝ := fun x ↦ x
  have hW : ∀ᵐ x ∂μ, 0 < W x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    dsimp only [W]
    exact one_div_pos.mpr (pow_pos (by linarith [hx.1] : 0 < x) 3)
  have hdualMeas : AEStronglyMeasurable
      (fun x ↦ G x / Real.sqrt (W x)) μ := by
    apply Measurable.aestronglyMeasurable
    dsimp only [G, W, μ]
    fun_prop
  have hdualDensity : IntegrableOn (fun x : ℝ ↦ x ^ 5)
      (Ioc (3 / 5 : ℝ) 1) := by
    exact ((by fun_prop : Continuous (fun x : ℝ ↦ x ^ 5))
      |>.continuousOn.integrableOn_compact isCompact_Icc).mono_set
        Ioc_subset_Icc_self
  have hdual : MemLp (fun x ↦ G x / Real.sqrt (W x)) 2 μ := by
    rw [memLp_two_iff_integrable_sq_norm hdualMeas]
    have hInt : Integrable (fun x : ℝ ↦ x ^ 5) μ := by
      simpa only [μ] using hdualDensity
    apply hInt.congr
    filter_upwards [hW] with x hx
    have hx0 : 0 < x := by
      dsimp only [W] at hx
      have hx3 : 0 < x ^ 3 := one_div_pos.mp hx
      nlinarith [sq_nonneg x]
    rw [Real.norm_eq_abs, sq_abs, div_pow, Real.sq_sqrt hx.le]
    dsimp only [G, W]
    field_simp [hx0.ne']
  have hprimalMeas : AEStronglyMeasurable
      (fun x ↦ Real.sqrt (W x) * h x) μ := by
    apply Measurable.aestronglyMeasurable
    dsimp only [W, μ]
    fun_prop
  have hprimalDensity : IntegrableOn
      (fun x : ℝ ↦ h x ^ 2 / x ^ 3) (Ioc (3 / 5 : ℝ) 1) := by
    have hcont : ContinuousOn (fun x : ℝ ↦ h x ^ 2 / x ^ 3)
        (Icc (3 / 5 : ℝ) 1) := by
      apply ContinuousOn.div (hh.pow 2).continuousOn
        (by fun_prop : Continuous (fun x : ℝ ↦ x ^ 3)).continuousOn
      intro x hx
      exact pow_ne_zero 3 (by linarith [hx.1] : x ≠ 0)
    exact (hcont.integrableOn_compact isCompact_Icc).mono_set
      Ioc_subset_Icc_self
  have hprimal : MemLp (fun x ↦ Real.sqrt (W x) * h x) 2 μ := by
    rw [memLp_two_iff_integrable_sq_norm hprimalMeas]
    have hInt : Integrable (fun x : ℝ ↦ h x ^ 2 / x ^ 3) μ := by
      simpa only [μ] using hprimalDensity
    apply hInt.congr
    filter_upwards [hW] with x hx
    rw [Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt hx.le]
    dsimp only [W]
    ring
  have hcauchy := sq_integral_mul_le_weighted μ W G h
    hW hdual hprimal
  dsimp only [μ] at hcauchy
  repeat rw [← intervalIntegral.integral_of_le (by norm_num)] at hcauchy
  have hdualValue :
      (∫ x : ℝ in 3 / 5..1, G x ^ 2 / W x) =
        (7448 / 46875 : ℝ) := by
    rw [show (fun x : ℝ ↦ G x ^ 2 / W x) = fun x ↦ x ^ 5 by
      funext x
      dsimp only [G, W]
      by_cases hx : x = 0
      · simp [hx]
      · field_simp [hx]
    , integral_pow]
    norm_num
  have hprimalValue :
      (∫ x : ℝ in 3 / 5..1, W x * h x ^ 2) =
        ∫ x : ℝ in 3 / 5..1, h x ^ 2 / x ^ 3 := by
    apply intervalIntegral.integral_congr
    intro x _hx
    dsimp only [W]
    ring
  dsimp only [G] at hcauchy
  rw [hdualValue, hprimalValue] at hcauchy
  exact hcauchy

private theorem integral_lower_crossP1Difference_sq
    (w : ℝ → ℝ) (hw : Continuous w) (x : ℝ) :
    (∫ y : ℝ in 0..3 / 5, (y * w x - x * w y) ^ 2) =
      (9 / 125 : ℝ) * w x ^ 2 -
        2 * x * w x * (∫ y : ℝ in 0..3 / 5, y * w y) +
          x ^ 2 * (∫ y : ℝ in 0..3 / 5, w y ^ 2) := by
  have h2 : IntervalIntegrable (fun y : ℝ ↦ y ^ 2 * w x ^ 2)
      volume 0 (3 / 5) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hcross : IntervalIntegrable
      (fun y : ℝ ↦ 2 * x * w x * (y * w y)) volume 0 (3 / 5) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hw2 : IntervalIntegrable (fun y : ℝ ↦ x ^ 2 * w y ^ 2)
      volume 0 (3 / 5) := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [show (fun y : ℝ ↦ (y * w x - x * w y) ^ 2) =
      fun y ↦ y ^ 2 * w x ^ 2 - 2 * x * w x * (y * w y) +
        x ^ 2 * w y ^ 2 by
    funext y
    ring,
    intervalIntegral.integral_add (h2.sub hcross) hw2,
    intervalIntegral.integral_sub h2 hcross]
  rw [show (∫ y : ℝ in 0..3 / 5, y ^ 2 * w x ^ 2) =
      w x ^ 2 * ∫ y : ℝ in 0..3 / 5, y ^ 2 by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro y _hy
    ring,
    show (∫ y : ℝ in 0..3 / 5, 2 * x * w x * (y * w y)) =
      (2 * x * w x) * ∫ y : ℝ in 0..3 / 5, y * w y by
    rw [intervalIntegral.integral_const_mul],
    show (∫ y : ℝ in 0..3 / 5, x ^ 2 * w y ^ 2) =
      x ^ 2 * ∫ y : ℝ in 0..3 / 5, w y ^ 2 by
    rw [intervalIntegral.integral_const_mul],
    integral_pow]
  norm_num
  ring

/-- Global P₁ orthogonality forces the upper/lower raw cross rectangle to
pay the linear component left invisible by the lower-square spectral gap.
The rational constant `19` is below the exact weighted-Cauchy value
`1953125/100548`; no mode cutoff is involved. -/
theorem nineteen_mul_lowerP1Moment_sq_le_crossP1Square
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w)
    (hone : centeredOddP1Coefficient w = 0) :
    19 * (∫ x : ℝ in 0..3 / 5, x * w x) ^ 2 ≤
      fourCellOddCrossP1Square w := by
  let A : ℝ := ∫ x : ℝ in 0..3 / 5, x * w x
  let L : ℝ := ∫ x : ℝ in 0..3 / 5, w x ^ 2
  let k : ℝ := (125 / 9 : ℝ) * A
  let h : ℝ → ℝ := fun x ↦ w x - k * x
  have hwcont : Continuous w := hw.continuous
  have hh : Continuous h := by
    dsimp only [h, k]
    fun_prop
  have hinner (x : ℝ) :
      (9 / 125 : ℝ) * h x ^ 2 ≤
        ∫ y : ℝ in 0..3 / 5, (y * w x - x * w y) ^ 2 := by
    have hcauchy := sq_intervalIntegral_mul_le_zero_three_fifths
      (fun y : ℝ ↦ y) (fun y ↦ y * w x - x * w y)
      (by fun_prop) (by fun_prop)
    have hmoment :
        (∫ y : ℝ in 0..3 / 5, y * (y * w x - x * w y)) =
          (9 / 125 : ℝ) * h x := by
      have hpow : (∫ y : ℝ in 0..3 / 5, y ^ 2) = 9 / 125 := by
        rw [integral_pow]
        norm_num
      rw [show (fun y : ℝ ↦ y * (y * w x - x * w y)) =
          fun y ↦ w x * y ^ 2 - x * (y * w y) by
        funext y
        ring,
        intervalIntegral.integral_sub
          (Continuous.intervalIntegrable (by fun_prop) 0 (3 / 5))
          (Continuous.intervalIntegrable (by fun_prop) 0 (3 / 5)),
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul, hpow]
      dsimp only [h, k, A]
      ring
    have hy2 : (∫ y : ℝ in 0..3 / 5, y ^ 2) = 9 / 125 := by
      rw [integral_pow]
      norm_num
    rw [hmoment, hy2] at hcauchy
    nlinarith
  have hcenterMoment :
      (∫ x : ℝ in -1..1, w x * centeredP1 x) = 0 := by
    rw [integral_mul_centeredP1_eq, hone]
    ring
  have heven : Function.Even (fun x : ℝ ↦ w x * centeredP1 x) := by
    intro x
    unfold centeredP1
    change w (-x) * (-x) = w x * x
    rw [hodd]
    ring
  have hcenterInt : IntervalIntegrable (fun x : ℝ ↦ w x * centeredP1 x)
      volume (-1) 1 := by
    exact (hwcont.mul (by unfold centeredP1; fun_prop)).intervalIntegrable _ _
  have hfold := integral_neg_one_one_eq_two_mul_zero_one_of_even
    (fun x : ℝ ↦ w x * centeredP1 x) hcenterInt heven
  have hpositiveMoment : (∫ x : ℝ in 0..1, x * w x) = 0 := by
    unfold centeredP1 at hcenterMoment hfold
    rw [show (fun x : ℝ ↦ w x * x) = fun x ↦ x * w x by
      funext x
      ring] at hcenterMoment hfold
    linarith
  have hlowerInt : IntervalIntegrable (fun x : ℝ ↦ x * w x)
      volume 0 (3 / 5) := (by fun_prop : Continuous (fun x : ℝ ↦ x * w x))
        |>.intervalIntegrable _ _
  have hupperInt : IntervalIntegrable (fun x : ℝ ↦ x * w x)
      volume (3 / 5) 1 := (by fun_prop : Continuous (fun x : ℝ ↦ x * w x))
        |>.intervalIntegrable _ _
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    hlowerInt hupperInt
  have hupperMoment :
      (∫ x : ℝ in 3 / 5..1, x * w x) = -A := by
    dsimp only [A]
    linarith
  have hx2 : (∫ x : ℝ in 3 / 5..1, x ^ 2) = 98 / 375 := by
    rw [integral_pow]
    norm_num
  have hhMoment :
      (∫ x : ℝ in 3 / 5..1, x * h x) =
        -(125 / 27 : ℝ) * A := by
    rw [show (fun x : ℝ ↦ x * h x) =
        fun x ↦ x * w x - k * x ^ 2 by
      funext x
      dsimp only [h]
      ring,
      intervalIntegral.integral_sub hupperInt
        ((Continuous.const_mul (by fun_prop : Continuous (fun x : ℝ ↦ x ^ 2)) k)
          |>.intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, hupperMoment, hx2]
    dsimp only [k]
    ring
  have houter := sq_upperP1Moment_le_invCubeMass h hh
  rw [hhMoment] at houter
  have hintegrated :
      (18 / 125 : ℝ) *
          (∫ x : ℝ in 3 / 5..1, h x ^ 2 / x ^ 3) ≤
        fourCellOddCrossP1Square w := by
    have hleftInt : IntervalIntegrable
        (fun x : ℝ ↦ (18 / 125 : ℝ) * (h x ^ 2 / x ^ 3))
        volume (3 / 5) 1 := by
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.const_mul
      apply ContinuousOn.div (hh.pow 2).continuousOn
        (by fun_prop : Continuous (fun x : ℝ ↦ x ^ 3)).continuousOn
      intro x hx
      rw [uIcc_of_le (by norm_num : (3 / 5 : ℝ) ≤ 1)] at hx
      exact pow_ne_zero 3 (by linarith [hx.1] : x ≠ 0)
    have hrightEq : fourCellOddCrossP1Square w =
        ∫ x : ℝ in 3 / 5..1,
          (2 / x ^ 3) *
            (∫ y : ℝ in 0..3 / 5, (y * w x - x * w y) ^ 2) := by
      unfold fourCellOddCrossP1Square
      apply intervalIntegral.integral_congr
      intro x _hx
      change (∫ y : ℝ in 0..3 / 5,
          2 * (y * w x - x * w y) ^ 2 / x ^ 3) =
        (2 / x ^ 3) *
          ∫ y : ℝ in 0..3 / 5, (y * w x - x * w y) ^ 2
      rw [show (fun y : ℝ ↦ 2 * (y * w x - x * w y) ^ 2 / x ^ 3) =
          fun y ↦ (2 / x ^ 3) * (y * w x - x * w y) ^ 2 by
        funext y
        ring,
        intervalIntegral.integral_const_mul]
    rw [hrightEq]
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on_of_le_Ioo
      (by norm_num) hleftInt
    · apply ContinuousOn.intervalIntegrable
      rw [show (fun x : ℝ ↦ (2 / x ^ 3) *
          (∫ y : ℝ in 0..3 / 5, (y * w x - x * w y) ^ 2)) =
        fun x ↦ (2 / x ^ 3) *
          ((9 / 125 : ℝ) * w x ^ 2 - 2 * x * w x * A + x ^ 2 * L) by
        funext x
        rw [integral_lower_crossP1Difference_sq w hwcont x]]
      apply ContinuousOn.mul
      · apply ContinuousOn.div continuousOn_const
          (by fun_prop : Continuous (fun x : ℝ ↦ x ^ 3)).continuousOn
        intro x hx
        rw [uIcc_of_le (by norm_num : (3 / 5 : ℝ) ≤ 1)] at hx
        exact pow_ne_zero 3 (by linarith [hx.1] : x ≠ 0)
      · dsimp only [A, L]
        fun_prop
    · intro x hx
      have hx0 : 0 < x := by linarith [hx.1]
      have hmul := mul_le_mul_of_nonneg_left (hinner x)
        (div_nonneg (by norm_num : (0 : ℝ) ≤ 2)
          (pow_nonneg hx0.le 3))
      calc
        (18 / 125 : ℝ) * (h x ^ 2 / x ^ 3) =
            (2 / x ^ 3) * ((9 / 125 : ℝ) * h x ^ 2) := by ring
        _ ≤ (2 / x ^ 3) *
            (∫ y : ℝ in 0..3 / 5, (y * w x - x * w y) ^ 2) := hmul
  dsimp only [fourCellOddCrossP1Square] at hintegrated ⊢
  have hcoefficient :
      (19 : ℝ) * A ^ 2 ≤
        (18 / 125 : ℝ) *
          (∫ x : ℝ in 3 / 5..1, h x ^ 2 / x ^ 3) := by
    nlinarith
  exact hcoefficient.trans hintegrated

/-- Set-integral form of the sharp lower-square raw gap, ready for the exact
`[0,3/5] ∪ [3/5,1]` partition of the retained reserve. -/
theorem four_mul_lowerIntervalMass_le_lowerSquare_coupledRaw
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w) :
    4 * (∫ x : ℝ in 0..3 / 5, w x ^ 2) ≤
      ∫ p : ℝ × ℝ in Ico (0 : ℝ) (3 / 5) ×ˢ Ico (0 : ℝ) (3 / 5),
        fourCellOddCoupledRawPair w p
          ∂((volume : Measure ℝ).prod volume) := by
  let A : Set ℝ := Icc (0 : ℝ) (3 / 5)
  let S : ℝ × ℝ → ℝ := fun p ↦ centeredLogDifferenceKernel w p.1 p.2
  let J : ℝ × ℝ → ℝ := fun p ↦
    (w p.1 + w p.2) ^ 2 / (p.1 + p.2)
  let K : ℝ × ℝ → ℝ := fourCellOddCoupledRawPair w
  have hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w :=
    hw.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1)
  obtain ⟨C, hC⟩ := hlocal.exists_lipschitzOnWith_of_compact isCompact_Icc
  have hAsub : A ⊆ Icc (-1 : ℝ) 1 := by
    intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hsame : IntegrableOn S (A ×ˢ A)
      ((volume : Measure ℝ).prod volume) := by
    exact (integrableOn_centeredLogDifferenceKernel_prod_of_lipschitzOnWith
      w hC).mono_set (Set.prod_mono hAsub hAsub)
  have hJsub : A ⊆ Icc (0 : ℝ) 1 := by
    intro x hx
    exact ⟨hx.1, hx.2.trans (by norm_num)⟩
  have hJ : IntegrableOn J (A ×ˢ A)
      ((volume : Measure ℝ).prod volume) := by
    exact (integrableOn_reflectedRawKernel_of_lipschitzOnWith_odd
      w hw.continuous hC hodd).mono_set (Set.prod_mono hJsub hJsub)
  have hK : IntegrableOn K (A ×ˢ A)
      ((volume : Measure ℝ).prod volume) := by
    apply hsame.add hJ |>.congr
    filter_upwards [ae_restrict_mem
      (measurableSet_Icc.prod measurableSet_Icc)] with p hp
    dsimp only [K, S, J, A, fourCellOddCoupledRawPair]
    rfl
  have hSbridge := intervalIntegral_integral_eq_setIntegral_square
    S 0 (3 / 5) (by norm_num) hsame
  have hJbridge := intervalIntegral_integral_eq_setIntegral_square
    J 0 (3 / 5) (by norm_num) hJ
  have hgap := four_mul_lowerIntervalMass_le_lowerNestedCoupledRaw
    w hw hodd
  change 4 * (∫ x : ℝ in 0..3 / 5, w x ^ 2) ≤
    (∫ x : ℝ in 0..3 / 5, ∫ y : ℝ in 0..3 / 5, S (x, y)) +
      ∫ x : ℝ in 0..3 / 5, ∫ y : ℝ in 0..3 / 5, J (x, y) at hgap
  rw [hSbridge, hJbridge] at hgap
  have hsum :
      (∫ p : ℝ × ℝ in A ×ˢ A, S p
          ∂((volume : Measure ℝ).prod volume)) +
        (∫ p : ℝ × ℝ in A ×ˢ A, J p
          ∂((volume : Measure ℝ).prod volume)) =
      ∫ p : ℝ × ℝ in A ×ˢ A, K p
        ∂((volume : Measure ℝ).prod volume) := by
    calc
      _ = ∫ p : ℝ × ℝ in A ×ˢ A, S p + J p
          ∂((volume : Measure ℝ).prod volume) :=
        (MeasureTheory.integral_add hsame hJ).symm
      _ = _ := by
        apply setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc)
        intro p _hp
        dsimp only [K, S, J, fourCellOddCoupledRawPair]
        rfl
  have hsum' := hsum
  dsimp only [A] at hsum'
  have hgapK := hgap.trans_eq hsum'
  have hsets :
      Ico (0 : ℝ) (3 / 5) ×ˢ Ico (0 : ℝ) (3 / 5) =ᵐ[
        (volume : Measure ℝ).prod volume]
      A ×ˢ A := by
    exact Measure.set_prod_ae_eq Ico_ae_eq_Icc Ico_ae_eq_Icc
  have hsetIntegral := setIntegral_congr_set (f := K) hsets
  simpa only [A, K] using hgapK.trans_eq hsetIntegral.symm

/-- Set-integral form of the lower P₁ spectral surplus, ready to be kept
alongside both orientations of the strengthened cross rectangle. -/
theorem lowerIntervalP1Surplus_le_half_lowerSquare_coupledRaw
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w) :
    (11 / 3 : ℝ) * (∫ x : ℝ in 0..3 / 5, w x ^ 2) -
        (625 / 27 : ℝ) * (∫ x : ℝ in 0..3 / 5, x * w x) ^ 2 ≤
      (1 / 2 : ℝ) *
        ∫ p : ℝ × ℝ in
          Ico (0 : ℝ) (3 / 5) ×ˢ Ico (0 : ℝ) (3 / 5),
            fourCellOddCoupledRawPair w p
              ∂((volume : Measure ℝ).prod volume) := by
  let A : Set ℝ := Icc (0 : ℝ) (3 / 5)
  let S : ℝ × ℝ → ℝ := fun p ↦ centeredLogDifferenceKernel w p.1 p.2
  let J : ℝ × ℝ → ℝ := fun p ↦
    (w p.1 + w p.2) ^ 2 / (p.1 + p.2)
  let K : ℝ × ℝ → ℝ := fourCellOddCoupledRawPair w
  have hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w :=
    hw.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1)
  obtain ⟨C, hC⟩ := hlocal.exists_lipschitzOnWith_of_compact isCompact_Icc
  have hAsub : A ⊆ Icc (-1 : ℝ) 1 := by
    intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hsame : IntegrableOn S (A ×ˢ A)
      ((volume : Measure ℝ).prod volume) := by
    exact (integrableOn_centeredLogDifferenceKernel_prod_of_lipschitzOnWith
      w hC).mono_set (Set.prod_mono hAsub hAsub)
  have hJsub : A ⊆ Icc (0 : ℝ) 1 := by
    intro x hx
    exact ⟨hx.1, hx.2.trans (by norm_num)⟩
  have hJ : IntegrableOn J (A ×ˢ A)
      ((volume : Measure ℝ).prod volume) := by
    exact (integrableOn_reflectedRawKernel_of_lipschitzOnWith_odd
      w hw.continuous hC hodd).mono_set (Set.prod_mono hJsub hJsub)
  have hSbridge := intervalIntegral_integral_eq_setIntegral_square
    S 0 (3 / 5) (by norm_num) hsame
  have hJbridge := intervalIntegral_integral_eq_setIntegral_square
    J 0 (3 / 5) (by norm_num) hJ
  have hgap := lowerIntervalP1Surplus_le_half_lowerNestedCoupledRaw w hw hodd
  change (11 / 3 : ℝ) * (∫ x : ℝ in 0..3 / 5, w x ^ 2) -
      (625 / 27 : ℝ) * (∫ x : ℝ in 0..3 / 5, x * w x) ^ 2 ≤
    (1 / 2 : ℝ) *
      ((∫ x : ℝ in 0..3 / 5, ∫ y : ℝ in 0..3 / 5, S (x, y)) +
        ∫ x : ℝ in 0..3 / 5, ∫ y : ℝ in 0..3 / 5, J (x, y))
    at hgap
  rw [hSbridge, hJbridge] at hgap
  have hsum :
      (∫ p : ℝ × ℝ in A ×ˢ A, S p
          ∂((volume : Measure ℝ).prod volume)) +
        (∫ p : ℝ × ℝ in A ×ˢ A, J p
          ∂((volume : Measure ℝ).prod volume)) =
      ∫ p : ℝ × ℝ in A ×ˢ A, K p
        ∂((volume : Measure ℝ).prod volume) := by
    calc
      _ = ∫ p : ℝ × ℝ in A ×ˢ A, S p + J p
          ∂((volume : Measure ℝ).prod volume) :=
        (MeasureTheory.integral_add hsame hJ).symm
      _ = _ := by
        apply setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc)
        intro p _hp
        dsimp only [K, S, J, fourCellOddCoupledRawPair]
        rfl
  have hsum' := hsum
  dsimp only [A] at hsum'
  have hgapK :
      (11 / 3 : ℝ) * (∫ x : ℝ in 0..3 / 5, w x ^ 2) -
          (625 / 27 : ℝ) * (∫ x : ℝ in 0..3 / 5, x * w x) ^ 2 ≤
        (1 / 2 : ℝ) *
          ∫ p : ℝ × ℝ in
            Icc (0 : ℝ) (3 / 5) ×ˢ Icc (0 : ℝ) (3 / 5), K p
              ∂((volume : Measure ℝ).prod volume) := by
    rw [← hsum']
    exact hgap
  have hsets :
      Ico (0 : ℝ) (3 / 5) ×ˢ Ico (0 : ℝ) (3 / 5) =ᵐ[
        (volume : Measure ℝ).prod volume]
      A ×ˢ A := by
    exact Measure.set_prod_ae_eq Ico_ae_eq_Icc Ico_ae_eq_Icc
  have hsetIntegral := setIntegral_congr_set (f := K) hsets
  simpa only [A, K] using hgapK.trans_eq (congrArg ((1 / 2 : ℝ) * ·)
    hsetIntegral.symm)

/-- The exact square partition retains the sharp lower-square payment and
both orientations of the weighted lower/upper cross rectangle. -/
theorem lowerMass_add_cross_le_fullRaw_sub_stripRaw
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w) :
    4 * (∫ x : ℝ in 0..3 / 5, w x ^ 2) +
        2 * (∫ p : ℝ × ℝ in
          Icc (3 / 5 : ℝ) 1 ×ˢ Ico (0 : ℝ) (3 / 5),
            fourCellOddCoupledRawPair w p
              ∂((volume : Measure ℝ).prod volume)) ≤
      fourCellPositiveHalfRawSameSignEnergy w +
        fourCellPositiveHalfRawReflectedEnergy w (-1) -
          fourCellOddEndpointStripRawEnergy w := by
  exact lowerSquareBudget_add_two_mul_cross_le_fullRaw_sub_stripRaw
    w hw hodd _
      (four_mul_lowerIntervalMass_le_lowerSquare_coupledRaw w hw hodd)

/-- Full raw reserve with the lower P₁ spectral surplus and the cross P₁
square simultaneously retained. -/
theorem lowerP1Surplus_add_weightedUpperMass_add_crossP1Square_le_rawReserve
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w) :
    (11 / 3 : ℝ) * (∫ x : ℝ in 0..3 / 5, w x ^ 2) -
        (625 / 27 : ℝ) * (∫ x : ℝ in 0..3 / 5, x * w x) ^ 2 +
      (6 / 5 : ℝ) * (∫ x : ℝ in 3 / 5..1, w x ^ 2 / x) +
        fourCellOddCrossP1Square w ≤
      fourCellOddRawStripCancellationReserve w := by
  let T : ℝ :=
    (11 / 3 : ℝ) * (∫ x : ℝ in 0..3 / 5, w x ^ 2) -
      (625 / 27 : ℝ) * (∫ x : ℝ in 0..3 / 5, x * w x) ^ 2
  let I : ℝ := ∫ p : ℝ × ℝ in
    Icc (3 / 5 : ℝ) 1 ×ˢ Ico (0 : ℝ) (3 / 5),
      fourCellOddCoupledRawPair w p
        ∂((volume : Measure ℝ).prod volume)
  have hlower := lowerIntervalP1Surplus_le_half_lowerSquare_coupledRaw
    w hw hodd
  have hlower' : 2 * T ≤
      ∫ p : ℝ × ℝ in
        Ico (0 : ℝ) (3 / 5) ×ˢ Ico (0 : ℝ) (3 / 5),
          fourCellOddCoupledRawPair w p
            ∂((volume : Measure ℝ).prod volume) := by
    dsimp only [T]
    linarith
  have hpartition := lowerSquareBudget_add_two_mul_cross_le_fullRaw_sub_stripRaw
    w hw hodd (2 * T) hlower'
  have hcross :=
    six_fifths_upperStripWeightedMass_add_crossP1Square_le_cross_coupledRaw
      w hw
  have hparity := fourCellOddEndpointStrip_rawEnergy_eq_even_add_odd w hw
  have heven := fourCellOddEndpointStripEvenRawEnergy_nonneg w
  unfold fourCellOddRawStripCancellationReserve
  dsimp only [T, I] at hpartition hcross ⊢
  linarith

/-- Full quantitative raw reserve with no discarded physical square: it pays
twice the lower mass and keeps the exact `1/x` endpoint payment. -/
theorem lowerMass_add_weightedUpperMass_le_rawStripCancellationReserve
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w) :
    2 * (∫ x : ℝ in 0..3 / 5, w x ^ 2) +
        (6 / 5 : ℝ) * (∫ x : ℝ in 3 / 5..1, w x ^ 2 / x) ≤
      fourCellOddRawStripCancellationReserve w := by
  let I : ℝ := ∫ p : ℝ × ℝ in
    Icc (3 / 5 : ℝ) 1 ×ˢ Ico (0 : ℝ) (3 / 5),
      fourCellOddCoupledRawPair w p
        ∂((volume : Measure ℝ).prod volume)
  have hmass :
      (6 / 5 : ℝ) * (∫ x : ℝ in 3 / 5..1, w x ^ 2 / x) ≤ I := by
    simpa only [I] using
      six_fifths_upperStripWeightedMass_le_cross_coupledRaw w hw
  have hpartition :
      4 * (∫ x : ℝ in 0..3 / 5, w x ^ 2) + 2 * I ≤
        fourCellPositiveHalfRawSameSignEnergy w +
          fourCellPositiveHalfRawReflectedEnergy w (-1) -
            fourCellOddEndpointStripRawEnergy w := by
    simpa only [I] using lowerMass_add_cross_le_fullRaw_sub_stripRaw
      w hw hodd
  have hparity := fourCellOddEndpointStrip_rawEnergy_eq_even_add_odd w hw
  have heven := fourCellOddEndpointStripEvenRawEnergy_nonneg w
  unfold fourCellOddRawStripCancellationReserve
  linarith

/-- The complete physical raw payment coupled to the centered regular row. -/
theorem lowerMass_add_weightedUpperMass_sub_regularCharge_le_coupledRaw
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w) :
    2 * (∫ x : ℝ in 0..3 / 5, w x ^ 2) +
        (6 / 5 : ℝ) * (∫ x : ℝ in 3 / 5..1, w x ^ 2 / x) -
        (fourCellOperatorHalfWidth / 10) *
          (∫ x : ℝ in -1..1, w x ^ 2) ≤
      fourCellOddRawStripCancellationReserve w -
        2 * fourCellOperatorHalfWidth *
          (∫ t : ℝ in 0..2,
            yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
              centeredEndpointCorrelation w t) := by
  let R : ℝ := ∫ t : ℝ in 0..2,
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
      centeredEndpointCorrelation w t
  let M : ℝ := ∫ x : ℝ in -1..1, w x ^ 2
  have hraw := lowerMass_add_weightedUpperMass_le_rawStripCancellationReserve
    w hw hodd
  have hR : |R| ≤ (1 / 20 : ℝ) * M := by
    simpa only [R, M] using
      abs_fourCellRegularCorrelation_le_one_twentieth_centeredMass
        w hw.continuous hodd
  have ha0 : 0 ≤ 2 * fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  have hRle : R ≤ |R| := le_abs_self R
  have hmul := mul_le_mul_of_nonneg_left (hRle.trans hR) ha0
  dsimp only [R, M] at hmul ⊢
  linarith

/-- The strengthened lower P₁/cross reserve remains coupled after charging
the complete centered regular row. -/
theorem lowerP1Surplus_add_weightedUpperMass_add_crossP1Square_sub_regular_le
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w) :
    (11 / 3 : ℝ) * (∫ x : ℝ in 0..3 / 5, w x ^ 2) -
        (625 / 27 : ℝ) * (∫ x : ℝ in 0..3 / 5, x * w x) ^ 2 +
      (6 / 5 : ℝ) * (∫ x : ℝ in 3 / 5..1, w x ^ 2 / x) +
        fourCellOddCrossP1Square w -
      (fourCellOperatorHalfWidth / 10) *
        (∫ x : ℝ in -1..1, w x ^ 2) ≤
      fourCellOddRawStripCancellationReserve w -
        2 * fourCellOperatorHalfWidth *
          (∫ t : ℝ in 0..2,
            yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
              centeredEndpointCorrelation w t) := by
  let R : ℝ := ∫ t : ℝ in 0..2,
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
      centeredEndpointCorrelation w t
  let M : ℝ := ∫ x : ℝ in -1..1, w x ^ 2
  have hraw :=
    lowerP1Surplus_add_weightedUpperMass_add_crossP1Square_le_rawReserve
      w hw hodd
  have hR : |R| ≤ (1 / 20 : ℝ) * M := by
    simpa only [R, M] using
      abs_fourCellRegularCorrelation_le_one_twentieth_centeredMass
        w hw.continuous hodd
  have ha0 : 0 ≤ 2 * fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  have hRle : R ≤ |R| := le_abs_self R
  have hmul := mul_le_mul_of_nonneg_left (hRle.trans hR) ha0
  dsimp only [R, M] at hmul ⊢
  linarith

/-- Strong endpoint closure with the sharp lower-square payment retained. -/
theorem lowerMass_add_endpointScalar_sub_regularCharge_le_coupledReserve
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w) :
    2 * (∫ x : ℝ in 0..3 / 5, w x ^ 2) +
        (163 / 50 : ℝ) * (∫ x : ℝ in 3 / 5..1, w x ^ 2) -
        (fourCellOperatorHalfWidth / 10) *
          (∫ x : ℝ in -1..1, w x ^ 2) ≤
      fourCellOddRawStripCancellationReserve w +
        Real.sqrt 2 * Real.log 2 * fourCellOddEndpointStripEvenMass w +
        (2 - Real.sqrt 2 * Real.log 2) *
          fourCellOddEndpointStripOddMass w +
        (93 / 50 : ℝ) *
          (∫ x : ℝ in 0..1,
            yoshidaEndpointPotential x * w x ^ 2) -
        2 * fourCellOperatorHalfWidth *
          (∫ t : ℝ in 0..2,
            yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
              centeredEndpointCorrelation w t) := by
  have hdiagonal := endpointStripScalarMass_le_weightedRaw_prime_potential
    w hw.continuous
  have hraw :=
    lowerMass_add_weightedUpperMass_sub_regularCharge_le_coupledRaw
      w hw hodd
  have hprime := forty_nine_fiftieths_upperStripMass_le_primeDiagonal
    w hw.continuous
  have hpotential := upperStripPotential_le_positiveHalfPotential
    w hw.continuous
  have hpotentialMul := mul_le_mul_of_nonneg_left hpotential
    (by norm_num : (0 : ℝ) ≤ 93 / 50)
  linarith

/-- Endpoint closure with the complete lower P₁ and cross-square surplus
still visible. -/
theorem lowerP1Surplus_add_endpointScalar_add_crossP1Square_sub_regular_le
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w) :
    (11 / 3 : ℝ) * (∫ x : ℝ in 0..3 / 5, w x ^ 2) -
        (625 / 27 : ℝ) * (∫ x : ℝ in 0..3 / 5, x * w x) ^ 2 +
      fourCellOddCrossP1Square w +
      (163 / 50 : ℝ) * (∫ x : ℝ in 3 / 5..1, w x ^ 2) -
      (fourCellOperatorHalfWidth / 10) *
        (∫ x : ℝ in -1..1, w x ^ 2) ≤
      fourCellOddRawStripCancellationReserve w +
        Real.sqrt 2 * Real.log 2 * fourCellOddEndpointStripEvenMass w +
        (2 - Real.sqrt 2 * Real.log 2) *
          fourCellOddEndpointStripOddMass w +
        (93 / 50 : ℝ) *
          (∫ x : ℝ in 0..1,
            yoshidaEndpointPotential x * w x ^ 2) -
        2 * fourCellOperatorHalfWidth *
          (∫ t : ℝ in 0..2,
            yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
              centeredEndpointCorrelation w t) := by
  have hdiagonal := endpointStripScalarMass_le_weightedRaw_prime_potential
    w hw.continuous
  have hraw :=
    lowerP1Surplus_add_weightedUpperMass_add_crossP1Square_sub_regular_le
      w hw hodd
  have hprime := forty_nine_fiftieths_upperStripMass_le_primeDiagonal
    w hw.continuous
  have hpotential := upperStripPotential_le_positiveHalfPotential
    w hw.continuous
  have hpotentialMul := mul_le_mul_of_nonneg_left hpotential
    (by norm_num : (0 : ℝ) ≤ 93 / 50)
  linarith

/-- The remaining universal defect is at worst `63/50` of the lower physical
mass.  This is the exact residual after retaining every raw square and closing
the endpoint diagonal; no spectral truncation is used. -/
theorem neg_sixty_three_fiftieths_lowerMass_le_core_add_localWidthDefect
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w) :
    -(63 / 50 : ℝ) * (∫ x : ℝ in 0..3 / 5, w x ^ 2) ≤
      fourCellOddHalfCoreReserve w +
        fourCellOddStripLocalWidthDefect w := by
  let L : ℝ := ∫ x : ℝ in 0..3 / 5, w x ^ 2
  let U : ℝ := ∫ x : ℝ in 3 / 5..1, w x ^ 2
  let H : ℝ := ∫ x : ℝ in 0..1, w x ^ 2
  let C : ℝ :=
    2 * (Real.log (2 * fourCellOperatorHalfWidth) +
      Real.eulerMascheroniConstant + Real.log Real.pi) + 3 / 200
  let E : ℝ :=
    fourCellOddRawStripCancellationReserve w +
      Real.sqrt 2 * Real.log 2 * fourCellOddEndpointStripEvenMass w +
      (2 - Real.sqrt 2 * Real.log 2) *
        fourCellOddEndpointStripOddMass w +
      (93 / 50 : ℝ) *
        (∫ x : ℝ in 0..1, yoshidaEndpointPotential x * w x ^ 2) -
      2 * fourCellOperatorHalfWidth *
        (∫ t : ℝ in 0..2,
          yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
            centeredEndpointCorrelation w t)
  have hendpoint :
      2 * L + (163 / 50 : ℝ) * U -
          fourCellOperatorHalfWidth / 10 *
            (∫ x : ℝ in -1..1, w x ^ 2) ≤ E := by
    simpa only [L, U, E] using
      lowerMass_add_endpointScalar_sub_regularCharge_le_coupledReserve
        w hw hodd
  have hcentered : (∫ x : ℝ in -1..1, w x ^ 2) = 2 * H := by
    simpa only [H] using integral_sq_eq_two_mul_positiveHalf
      w hw.continuous (Or.inr hodd)
  have hlowerInt : IntervalIntegrable (fun x : ℝ ↦ w x ^ 2)
      volume 0 (3 / 5) := (hw.continuous.pow 2).intervalIntegrable _ _
  have hupperInt : IntervalIntegrable (fun x : ℝ ↦ w x ^ 2)
      volume (3 / 5) 1 := (hw.continuous.pow 2).intervalIntegrable _ _
  have hhalfSplit : L + U = H := by
    simpa only [L, U, H] using
      intervalIntegral.integral_add_adjacent_intervals hlowerInt hupperInt
  have hhalfNonneg : 0 ≤ H := by
    dsimp only [H]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun x _hx ↦ sq_nonneg _)
  have hcoefficient : C + fourCellOperatorHalfWidth / 5 ≤ 163 / 50 := by
    simpa only [C] using fourCellScalar_add_regularCharge_lt_163_div_50.le
  have hcoefficientMul :=
    mul_le_mul_of_nonneg_right hcoefficient hhalfNonneg
  have hcharge (a m : ℝ) : a / 10 * (2 * m) = a / 5 * m := by
    ring
  rw [hcentered, hcharge] at hendpoint
  have hbudget :
      C * H + fourCellOperatorHalfWidth / 5 * H ≤
        (163 / 50 : ℝ) * H := by
    calc
      C * H + fourCellOperatorHalfWidth / 5 * H =
          (C + fourCellOperatorHalfWidth / 5) * H := by ring
      _ ≤ (163 / 50 : ℝ) * H := hcoefficientMul
  rw [fourCellOddHalfCoreReserve_add_localWidthDefect_eq_raw_add_reduced]
  unfold fourCellOddStripReducedRemainder
  dsimp only [L, U, H, C, E] at hendpoint hhalfSplit hbudget ⊢
  linarith

/-- Refined universal lower bound retaining the local P₁ spectral defect
and its compensating cross-rectangle square. -/
theorem lowerP1RefinedMargin_le_core_add_localWidthDefect
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w) :
    (61 / 150 : ℝ) * (∫ x : ℝ in 0..3 / 5, w x ^ 2) -
        (625 / 27 : ℝ) * (∫ x : ℝ in 0..3 / 5, x * w x) ^ 2 +
          fourCellOddCrossP1Square w ≤
      fourCellOddHalfCoreReserve w +
        fourCellOddStripLocalWidthDefect w := by
  let L : ℝ := ∫ x : ℝ in 0..3 / 5, w x ^ 2
  let U : ℝ := ∫ x : ℝ in 3 / 5..1, w x ^ 2
  let H : ℝ := ∫ x : ℝ in 0..1, w x ^ 2
  let A : ℝ := ∫ x : ℝ in 0..3 / 5, x * w x
  let C : ℝ :=
    2 * (Real.log (2 * fourCellOperatorHalfWidth) +
      Real.eulerMascheroniConstant + Real.log Real.pi) + 3 / 200
  let E : ℝ :=
    fourCellOddRawStripCancellationReserve w +
      Real.sqrt 2 * Real.log 2 * fourCellOddEndpointStripEvenMass w +
      (2 - Real.sqrt 2 * Real.log 2) *
        fourCellOddEndpointStripOddMass w +
      (93 / 50 : ℝ) *
        (∫ x : ℝ in 0..1, yoshidaEndpointPotential x * w x ^ 2) -
      2 * fourCellOperatorHalfWidth *
        (∫ t : ℝ in 0..2,
          yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
            centeredEndpointCorrelation w t)
  have hendpoint :
      (11 / 3 : ℝ) * L - (625 / 27 : ℝ) * A ^ 2 +
          fourCellOddCrossP1Square w + (163 / 50 : ℝ) * U -
          fourCellOperatorHalfWidth / 10 *
            (∫ x : ℝ in -1..1, w x ^ 2) ≤ E := by
    simpa only [L, U, A, E] using
      lowerP1Surplus_add_endpointScalar_add_crossP1Square_sub_regular_le
        w hw hodd
  have hcentered : (∫ x : ℝ in -1..1, w x ^ 2) = 2 * H := by
    simpa only [H] using integral_sq_eq_two_mul_positiveHalf
      w hw.continuous (Or.inr hodd)
  have hlowerInt : IntervalIntegrable (fun x : ℝ ↦ w x ^ 2)
      volume 0 (3 / 5) := (hw.continuous.pow 2).intervalIntegrable _ _
  have hupperInt : IntervalIntegrable (fun x : ℝ ↦ w x ^ 2)
      volume (3 / 5) 1 := (hw.continuous.pow 2).intervalIntegrable _ _
  have hhalfSplit : L + U = H := by
    simpa only [L, U, H] using
      intervalIntegral.integral_add_adjacent_intervals hlowerInt hupperInt
  have hhalfNonneg : 0 ≤ H := by
    dsimp only [H]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun x _hx ↦ sq_nonneg _)
  have hcoefficient : C + fourCellOperatorHalfWidth / 5 ≤ 163 / 50 := by
    simpa only [C] using fourCellScalar_add_regularCharge_lt_163_div_50.le
  have hbudget :
      C * H + fourCellOperatorHalfWidth / 5 * H ≤
        (163 / 50 : ℝ) * H := by
    calc
      C * H + fourCellOperatorHalfWidth / 5 * H =
          (C + fourCellOperatorHalfWidth / 5) * H := by ring
      _ ≤ (163 / 50 : ℝ) * H :=
        mul_le_mul_of_nonneg_right hcoefficient hhalfNonneg
  have hcharge (a m : ℝ) : a / 10 * (2 * m) = a / 5 * m := by ring
  rw [hcentered, hcharge] at hendpoint
  rw [fourCellOddHalfCoreReserve_add_localWidthDefect_eq_raw_add_reduced]
  unfold fourCellOddStripReducedRemainder
  dsimp only [L, U, H, A, C, E] at hendpoint hhalfSplit hbudget ⊢
  linarith

/-- Nondegenerate refinement of the `P₁` margin.  The quantitative scalar
gap retains `13/20000` of the complete positive-half mass, so the resulting
tail norm still sees profiles supported entirely in the endpoint strip. -/
theorem lowerP1RefinedGlobalMargin_le_core_add_localWidthDefect
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w) :
    (61 / 150 : ℝ) * (∫ x : ℝ in 0..3 / 5, w x ^ 2) +
        (13 / 20000 : ℝ) * (∫ x : ℝ in 0..1, w x ^ 2) -
        (625 / 27 : ℝ) * (∫ x : ℝ in 0..3 / 5, x * w x) ^ 2 +
          fourCellOddCrossP1Square w ≤
      fourCellOddHalfCoreReserve w +
        fourCellOddStripLocalWidthDefect w := by
  let L : ℝ := ∫ x : ℝ in 0..3 / 5, w x ^ 2
  let U : ℝ := ∫ x : ℝ in 3 / 5..1, w x ^ 2
  let H : ℝ := ∫ x : ℝ in 0..1, w x ^ 2
  let A : ℝ := ∫ x : ℝ in 0..3 / 5, x * w x
  let C : ℝ :=
    2 * (Real.log (2 * fourCellOperatorHalfWidth) +
      Real.eulerMascheroniConstant + Real.log Real.pi) + 3 / 200
  let E : ℝ :=
    fourCellOddRawStripCancellationReserve w +
      Real.sqrt 2 * Real.log 2 * fourCellOddEndpointStripEvenMass w +
      (2 - Real.sqrt 2 * Real.log 2) *
        fourCellOddEndpointStripOddMass w +
      (93 / 50 : ℝ) *
        (∫ x : ℝ in 0..1, yoshidaEndpointPotential x * w x ^ 2) -
      2 * fourCellOperatorHalfWidth *
        (∫ t : ℝ in 0..2,
          yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
            centeredEndpointCorrelation w t)
  have hendpoint :
      (11 / 3 : ℝ) * L - (625 / 27 : ℝ) * A ^ 2 +
          fourCellOddCrossP1Square w + (163 / 50 : ℝ) * U -
          fourCellOperatorHalfWidth / 10 *
            (∫ x : ℝ in -1..1, w x ^ 2) ≤ E := by
    simpa only [L, U, A, E] using
      lowerP1Surplus_add_endpointScalar_add_crossP1Square_sub_regular_le
        w hw hodd
  have hcentered : (∫ x : ℝ in -1..1, w x ^ 2) = 2 * H := by
    simpa only [H] using integral_sq_eq_two_mul_positiveHalf
      w hw.continuous (Or.inr hodd)
  have hlowerInt : IntervalIntegrable (fun x : ℝ ↦ w x ^ 2)
      volume 0 (3 / 5) := (hw.continuous.pow 2).intervalIntegrable _ _
  have hupperInt : IntervalIntegrable (fun x : ℝ ↦ w x ^ 2)
      volume (3 / 5) 1 := (hw.continuous.pow 2).intervalIntegrable _ _
  have hhalfSplit : L + U = H := by
    simpa only [L, U, H] using
      intervalIntegral.integral_add_adjacent_intervals hlowerInt hupperInt
  have hhalfNonneg : 0 ≤ H := by
    dsimp only [H]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun x _hx ↦ sq_nonneg _)
  have hcoefficient : C + fourCellOperatorHalfWidth / 5 ≤
      (65187 / 20000 : ℝ) := by
    simpa only [C] using
      fourCellScalar_add_regularCharge_le_65187_div_20000
  have hbudget :
      C * H + fourCellOperatorHalfWidth / 5 * H ≤
        (65187 / 20000 : ℝ) * H := by
    calc
      C * H + fourCellOperatorHalfWidth / 5 * H =
          (C + fourCellOperatorHalfWidth / 5) * H := by ring
      _ ≤ (65187 / 20000 : ℝ) * H :=
        mul_le_mul_of_nonneg_right hcoefficient hhalfNonneg
  have hcharge (a m : ℝ) : a / 10 * (2 * m) = a / 5 * m := by ring
  rw [hcentered, hcharge] at hendpoint
  rw [fourCellOddHalfCoreReserve_add_localWidthDefect_eq_raw_add_reduced]
  unfold fourCellOddStripReducedRemainder
  dsimp only [L, U, H, A, C, E] at hendpoint hhalfSplit hbudget ⊢
  linarith

private theorem lowerP1Moment_sq_le_nine_one_twenty_fifths_lowerMass
    (w : ℝ → ℝ) (hw : Continuous w) :
    (∫ x : ℝ in 0..3 / 5, x * w x) ^ 2 ≤
      (9 / 125 : ℝ) * ∫ x : ℝ in 0..3 / 5, w x ^ 2 := by
  have hcauchy := sq_intervalIntegral_mul_le_zero_three_fifths
    (fun x : ℝ ↦ x) w (by fun_prop) hw
  have hx2 : (∫ x : ℝ in 0..3 / 5, x ^ 2) = 9 / 125 := by
    rw [integral_pow]
    norm_num
  rw [hx2] at hcauchy
  exact hcauchy

/-- Quantitative closure of the complete odd tail block.  Global P₁
orthogonality turns the cross square into `19 A²`; together with the local
spectral surplus this leaves the exact rational margin `27/250` of the
lower physical mass. -/
theorem twenty_seven_two_fiftieths_lowerMass_le_core_add_localWidthDefect_of_P1
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w)
    (hone : centeredOddP1Coefficient w = 0) :
    (27 / 250 : ℝ) * (∫ x : ℝ in 0..3 / 5, w x ^ 2) ≤
      fourCellOddHalfCoreReserve w +
        fourCellOddStripLocalWidthDefect w := by
  have hrefined := lowerP1RefinedMargin_le_core_add_localWidthDefect
    w hw hodd
  have hcross := nineteen_mul_lowerP1Moment_sq_le_crossP1Square
    w hw hodd hone
  have hmoment := lowerP1Moment_sq_le_nine_one_twenty_fifths_lowerMass
    w hw.continuous
  nlinarith

/-- The nondegenerate `P₁`-orthogonal tail margin.  In addition to the sharp
`27/250` lower-strip reserve it retains `13/20000` of the complete
positive-half mass, which is the coercive weight needed by the Riesz row. -/
theorem lowerTailMargin_add_globalMass_le_core_add_localWidthDefect_of_P1
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w)
    (hone : centeredOddP1Coefficient w = 0) :
    (27 / 250 : ℝ) * (∫ x : ℝ in 0..3 / 5, w x ^ 2) +
        (13 / 20000 : ℝ) * (∫ x : ℝ in 0..1, w x ^ 2) ≤
      fourCellOddHalfCoreReserve w +
        fourCellOddStripLocalWidthDefect w := by
  have hrefined := lowerP1RefinedGlobalMargin_le_core_add_localWidthDefect
    w hw hodd
  have hcross := nineteen_mul_lowerP1Moment_sq_le_crossP1Square
    w hw hodd hone
  have hmoment := lowerP1Moment_sq_le_nine_one_twenty_fifths_lowerMass
    w hw.continuous
  nlinarith

private theorem positiveHalfOcticEnergy_le_endpointPotentialEnergy
    (w : ℝ → ℝ) (hw : Continuous w) :
    (∫ x : ℝ in 0..1, yoshidaEndpointOctic x * w x ^ 2) ≤
      ∫ x : ℝ in 0..1, yoshidaEndpointPotential x * w x ^ 2 := by
  have hoctic : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointOctic x * w x ^ 2)
      volume 0 1 := by
    apply Continuous.intervalIntegrable
    unfold yoshidaEndpointOctic
    fun_prop
  have hpotential : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * w x ^ 2)
      volume 0 1 := by
    apply (intervalIntegrable_endpointPotential_mul_sq w hw).mono_set
    intro x hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact ⟨by linarith [hx.1], hx.2⟩
  apply intervalIntegral.integral_mono_on_of_le_Ioo
    (by norm_num : (0 : ℝ) ≤ 1) hoctic hpotential
  intro x hx
  exact mul_le_mul_of_nonneg_right
    (octic_le_endpointPotential (by
      rw [abs_lt]
      constructor <;> linarith [hx.1, hx.2]))
    (sq_nonneg (w x))

/-- Strong `P₁`-orthogonal tail reserve before minimizing the endpoint
density.  It retains the exact weighted raw gain, prime mass, and octic
potential on `[3/5,1]`; unlike a scalar global gap, this is quantitatively
large enough to support the exact low--tail Riesz row. -/
theorem rawPrimePotentialTailWeight_le_core_add_localWidthDefect_of_P1
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w)
    (hone : centeredOddP1Coefficient w = 0) :
    (27 / 250 : ℝ) * (∫ x : ℝ in 0..3 / 5, w x ^ 2) +
        (93 / 50 : ℝ) *
          (∫ x : ℝ in 0..1, yoshidaEndpointOctic x * w x ^ 2) +
        (6 / 5 : ℝ) * (∫ x : ℝ in 3 / 5..1, w x ^ 2 / x) -
        (57 / 25 : ℝ) * (∫ x : ℝ in 3 / 5..1, w x ^ 2) ≤
      fourCellOddHalfCoreReserve w +
        fourCellOddStripLocalWidthDefect w := by
  let L : ℝ := ∫ x : ℝ in 0..3 / 5, w x ^ 2
  let U : ℝ := ∫ x : ℝ in 3 / 5..1, w x ^ 2
  let H : ℝ := ∫ x : ℝ in 0..1, w x ^ 2
  let A : ℝ := ∫ x : ℝ in 0..3 / 5, x * w x
  let J : ℝ := ∫ x : ℝ in 3 / 5..1, w x ^ 2 / x
  let P : ℝ := ∫ x : ℝ in 0..1,
    yoshidaEndpointOctic x * w x ^ 2
  let C : ℝ :=
    2 * (Real.log (2 * fourCellOperatorHalfWidth) +
      Real.eulerMascheroniConstant + Real.log Real.pi) + 3 / 200
  let E : ℝ :=
    fourCellOddRawStripCancellationReserve w +
      Real.sqrt 2 * Real.log 2 * fourCellOddEndpointStripEvenMass w +
      (2 - Real.sqrt 2 * Real.log 2) *
        fourCellOddEndpointStripOddMass w +
      (93 / 50 : ℝ) *
        (∫ x : ℝ in 0..1, yoshidaEndpointPotential x * w x ^ 2) -
      2 * fourCellOperatorHalfWidth *
        (∫ t : ℝ in 0..2,
          yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
            centeredEndpointCorrelation w t)
  have hraw :=
    lowerP1Surplus_add_weightedUpperMass_add_crossP1Square_sub_regular_le
      w hw hodd
  have hprime := forty_nine_fiftieths_upperStripMass_le_primeDiagonal
    w hw.continuous
  have hpotential := positiveHalfOcticEnergy_le_endpointPotentialEnergy
    w hw.continuous
  have hpotentialMul := mul_le_mul_of_nonneg_left hpotential
    (by norm_num : (0 : ℝ) ≤ 93 / 50)
  have hcombined :
      (11 / 3 : ℝ) * L - (625 / 27 : ℝ) * A ^ 2 +
          (6 / 5 : ℝ) * J + fourCellOddCrossP1Square w +
          (49 / 50 : ℝ) * U + (93 / 50 : ℝ) * P -
          (fourCellOperatorHalfWidth / 10) *
            (∫ x : ℝ in -1..1, w x ^ 2) ≤ E := by
    dsimp only [L, U, A, J, P, E]
    linarith
  have hcentered : (∫ x : ℝ in -1..1, w x ^ 2) = 2 * H := by
    simpa only [H] using integral_sq_eq_two_mul_positiveHalf
      w hw.continuous (Or.inr hodd)
  have hlowerInt : IntervalIntegrable (fun x : ℝ ↦ w x ^ 2)
      volume 0 (3 / 5) := (hw.continuous.pow 2).intervalIntegrable _ _
  have hupperInt : IntervalIntegrable (fun x : ℝ ↦ w x ^ 2)
      volume (3 / 5) 1 := (hw.continuous.pow 2).intervalIntegrable _ _
  have hhalfSplit : L + U = H := by
    simpa only [L, U, H] using
      intervalIntegral.integral_add_adjacent_intervals hlowerInt hupperInt
  have hhalfNonneg : 0 ≤ H := by
    dsimp only [H]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun x _hx ↦ sq_nonneg _)
  have hcoefficient : C + fourCellOperatorHalfWidth / 5 ≤
      (163 / 50 : ℝ) := by
    simpa only [C] using fourCellScalar_add_regularCharge_lt_163_div_50.le
  have hbudget :
      C * H + fourCellOperatorHalfWidth / 5 * H ≤
        (163 / 50 : ℝ) * H := by
    calc
      C * H + fourCellOperatorHalfWidth / 5 * H =
          (C + fourCellOperatorHalfWidth / 5) * H := by ring
      _ ≤ (163 / 50 : ℝ) * H :=
        mul_le_mul_of_nonneg_right hcoefficient hhalfNonneg
  have hcharge (a m : ℝ) : a / 10 * (2 * m) = a / 5 * m := by ring
  rw [hcentered, hcharge] at hcombined
  have hcross := nineteen_mul_lowerP1Moment_sq_le_crossP1Square
    w hw hodd hone
  have hmoment := lowerP1Moment_sq_le_nine_one_twenty_fifths_lowerMass
    w hw.continuous
  rw [fourCellOddHalfCoreReserve_add_localWidthDefect_eq_raw_add_reduced]
  unfold fourCellOddStripReducedRemainder
  dsimp only [L, U, H, A, J, P, C, E]
    at hcombined hhalfSplit hbudget ⊢
  nlinarith

/-- Full-potential version of the strong `P₁`-orthogonal tail reserve.  The
logarithmic endpoint potential is retained exactly, rather than replaced by
its octic lower model, so it can serve as the natural Riesz weight for the
retained endpoint mixed row. -/
theorem rawPrimeExactPotentialTailWeight_le_core_add_localWidthDefect_of_P1
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w)
    (hone : centeredOddP1Coefficient w = 0) :
    (27 / 250 : ℝ) * (∫ x : ℝ in 0..3 / 5, w x ^ 2) +
        (93 / 50 : ℝ) *
          (∫ x : ℝ in 0..1, yoshidaEndpointPotential x * w x ^ 2) +
        (6 / 5 : ℝ) * (∫ x : ℝ in 3 / 5..1, w x ^ 2 / x) -
        (57 / 25 : ℝ) * (∫ x : ℝ in 3 / 5..1, w x ^ 2) ≤
      fourCellOddHalfCoreReserve w +
        fourCellOddStripLocalWidthDefect w := by
  let L : ℝ := ∫ x : ℝ in 0..3 / 5, w x ^ 2
  let U : ℝ := ∫ x : ℝ in 3 / 5..1, w x ^ 2
  let H : ℝ := ∫ x : ℝ in 0..1, w x ^ 2
  let A : ℝ := ∫ x : ℝ in 0..3 / 5, x * w x
  let J : ℝ := ∫ x : ℝ in 3 / 5..1, w x ^ 2 / x
  let P : ℝ := ∫ x : ℝ in 0..1,
    yoshidaEndpointPotential x * w x ^ 2
  let C : ℝ :=
    2 * (Real.log (2 * fourCellOperatorHalfWidth) +
      Real.eulerMascheroniConstant + Real.log Real.pi) + 3 / 200
  let E : ℝ :=
    fourCellOddRawStripCancellationReserve w +
      Real.sqrt 2 * Real.log 2 * fourCellOddEndpointStripEvenMass w +
      (2 - Real.sqrt 2 * Real.log 2) *
        fourCellOddEndpointStripOddMass w +
      (93 / 50 : ℝ) *
        (∫ x : ℝ in 0..1, yoshidaEndpointPotential x * w x ^ 2) -
      2 * fourCellOperatorHalfWidth *
        (∫ t : ℝ in 0..2,
          yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
            centeredEndpointCorrelation w t)
  have hraw :=
    lowerP1Surplus_add_weightedUpperMass_add_crossP1Square_sub_regular_le
      w hw hodd
  have hprime := forty_nine_fiftieths_upperStripMass_le_primeDiagonal
    w hw.continuous
  have hcombined :
      (11 / 3 : ℝ) * L - (625 / 27 : ℝ) * A ^ 2 +
          (6 / 5 : ℝ) * J + fourCellOddCrossP1Square w +
          (49 / 50 : ℝ) * U + (93 / 50 : ℝ) * P -
          (fourCellOperatorHalfWidth / 10) *
            (∫ x : ℝ in -1..1, w x ^ 2) ≤ E := by
    dsimp only [L, U, A, J, P, E]
    linarith
  have hcentered : (∫ x : ℝ in -1..1, w x ^ 2) = 2 * H := by
    simpa only [H] using integral_sq_eq_two_mul_positiveHalf
      w hw.continuous (Or.inr hodd)
  have hlowerInt : IntervalIntegrable (fun x : ℝ ↦ w x ^ 2)
      volume 0 (3 / 5) := (hw.continuous.pow 2).intervalIntegrable _ _
  have hupperInt : IntervalIntegrable (fun x : ℝ ↦ w x ^ 2)
      volume (3 / 5) 1 := (hw.continuous.pow 2).intervalIntegrable _ _
  have hhalfSplit : L + U = H := by
    simpa only [L, U, H] using
      intervalIntegral.integral_add_adjacent_intervals hlowerInt hupperInt
  have hhalfNonneg : 0 ≤ H := by
    dsimp only [H]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun x _hx ↦ sq_nonneg _)
  have hcoefficient : C + fourCellOperatorHalfWidth / 5 ≤
      (163 / 50 : ℝ) := by
    simpa only [C] using fourCellScalar_add_regularCharge_lt_163_div_50.le
  have hbudget :
      C * H + fourCellOperatorHalfWidth / 5 * H ≤
        (163 / 50 : ℝ) * H := by
    calc
      C * H + fourCellOperatorHalfWidth / 5 * H =
          (C + fourCellOperatorHalfWidth / 5) * H := by ring
      _ ≤ (163 / 50 : ℝ) * H :=
        mul_le_mul_of_nonneg_right hcoefficient hhalfNonneg
  have hcharge (a m : ℝ) : a / 10 * (2 * m) = a / 5 * m := by ring
  rw [hcentered, hcharge] at hcombined
  have hcross := nineteen_mul_lowerP1Moment_sq_le_crossP1Square
    w hw hodd hone
  have hmoment := lowerP1Moment_sq_le_nine_one_twenty_fifths_lowerMass
    w hw.continuous
  rw [fourCellOddHalfCoreReserve_add_localWidthDefect_eq_raw_add_reduced]
  unfold fourCellOddStripReducedRemainder
  dsimp only [L, U, H, A, J, P, C, E]
    at hcombined hhalfSplit hbudget ⊢
  nlinarith

/-- The coupled upper-strip octic density retains a uniform `1/50` margin.
The proof is one Bernstein-positive polynomial identity on the complete
strip, not separate minimizations of the raw and potential terms. -/
private theorem one_fiftieth_mul_x_le_endpointStripOcticDensity_gap
    {x : ℝ} (hx0 : (3 / 5 : ℝ) ≤ x) (hx1 : x ≤ 1) :
    (1 / 50 : ℝ) * x ≤
      (6 / 5 : ℝ) - (57 / 25) * x +
        (93 / 50) * x * yoshidaEndpointOctic x := by
  let t : ℝ := (5 * x - 3) / 2
  have ht0 : 0 ≤ t := by dsimp only [t]; linarith
  have ht1 : t ≤ 1 := by dsimp only [t]; linarith
  have hcomp : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  rw [← sub_nonneg]
  rw [show
      (6 / 5 : ℝ) - (57 / 25) * x +
          (93 / 50) * x * yoshidaEndpointOctic x - (1 / 50) * x =
        (53171469 / 781250000 : ℝ) * (1 - t) ^ 9 +
        (42090487 / 156250000 : ℝ) * t * (1 - t) ^ 8 +
        (1968121 / 7812500 : ℝ) * t ^ 2 * (1 - t) ^ 7 +
        (15799 / 62500 : ℝ) * t ^ 3 * (1 - t) ^ 6 +
        (1806347 / 625000 : ℝ) * t ^ 4 * (1 - t) ^ 5 +
        (1157849 / 125000 : ℝ) * t ^ 5 * (1 - t) ^ 4 +
        (172237 / 12500 : ℝ) * t ^ 6 * (1 - t) ^ 3 +
        (27683 / 2500 : ℝ) * t ^ 7 * (1 - t) ^ 2 +
        (9413 / 2000 : ℝ) * t ^ 8 * (1 - t) +
        (67 / 80 : ℝ) * t ^ 9 by
    dsimp only [t]
    unfold yoshidaEndpointOctic
    ring]
  positivity

private theorem one_fiftieth_le_endpointStripOcticTailDensity
    {x : ℝ} (hx0 : (3 / 5 : ℝ) < x) (hx1 : x < 1) :
    (1 / 50 : ℝ) ≤
      (6 / 5 : ℝ) / x - 57 / 25 +
        (93 / 50) * yoshidaEndpointOctic x := by
  have hxpos : 0 < x := by linarith
  have hgap := one_fiftieth_mul_x_le_endpointStripOcticDensity_gap
    hx0.le hx1.le
  apply le_of_mul_le_mul_right ?_ hxpos
  rw [show
      ((6 / 5 : ℝ) / x - 57 / 25 +
          (93 / 50) * yoshidaEndpointOctic x) * x =
        (6 / 5 : ℝ) - (57 / 25) * x +
          (93 / 50) * x * yoshidaEndpointOctic x by
    field_simp [hxpos.ne']]
  simpa only [mul_comm (1 / 50 : ℝ) x] using hgap

/-- Scalar consequence of the retained raw/prime/octic tail density.  It
keeps `1/50` of the full positive-half mass, including endpoint-supported
tails that are invisible to the lower-strip reserve alone. -/
theorem one_fiftieth_positiveHalfMass_le_rawPrimePotentialTailWeight
    (w : ℝ → ℝ) (hw : Continuous w) :
    (1 / 50 : ℝ) * (∫ x : ℝ in 0..1, w x ^ 2) ≤
      (27 / 250 : ℝ) * (∫ x : ℝ in 0..3 / 5, w x ^ 2) +
        (93 / 50 : ℝ) *
          (∫ x : ℝ in 0..1, yoshidaEndpointOctic x * w x ^ 2) +
        (6 / 5 : ℝ) * (∫ x : ℝ in 3 / 5..1, w x ^ 2 / x) -
        (57 / 25 : ℝ) * (∫ x : ℝ in 3 / 5..1, w x ^ 2) := by
  have hmassLower : IntervalIntegrable (fun x : ℝ ↦ w x ^ 2)
      volume 0 (3 / 5) := (hw.pow 2).intervalIntegrable _ _
  have hmassUpper : IntervalIntegrable (fun x : ℝ ↦ w x ^ 2)
      volume (3 / 5) 1 := (hw.pow 2).intervalIntegrable _ _
  have hocticLower : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointOctic x * w x ^ 2)
      volume 0 (3 / 5) := by
    apply Continuous.intervalIntegrable
    unfold yoshidaEndpointOctic
    fun_prop
  have hocticUpper : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointOctic x * w x ^ 2)
      volume (3 / 5) 1 := by
    apply Continuous.intervalIntegrable
    unfold yoshidaEndpointOctic
    fun_prop
  have hweighted : IntervalIntegrable (fun x : ℝ ↦ w x ^ 2 / x)
      volume (3 / 5) 1 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div (hw.pow 2).continuousOn continuous_id.continuousOn
    intro x hx
    rw [uIcc_of_le (by norm_num : (3 / 5 : ℝ) ≤ 1)] at hx
    simpa only [id_eq] using (by linarith [hx.1] : x ≠ 0)
  have hlower :
      (∫ x : ℝ in 0..3 / 5, (1 / 50 : ℝ) * w x ^ 2) ≤
        ∫ x : ℝ in 0..3 / 5,
          (27 / 250 : ℝ) * w x ^ 2 +
            (93 / 50 : ℝ) *
              (yoshidaEndpointOctic x * w x ^ 2) := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num)
      (hmassLower.const_mul _)
      ((hmassLower.const_mul _).add (hocticLower.const_mul _))
    intro x _hx
    have hoctic : 0 ≤ yoshidaEndpointOctic x := by
      unfold yoshidaEndpointOctic
      positivity
    have hmul := mul_nonneg hoctic (sq_nonneg (w x))
    nlinarith
  have hupper :
      (∫ x : ℝ in 3 / 5..1, (1 / 50 : ℝ) * w x ^ 2) ≤
        ∫ x : ℝ in 3 / 5..1,
          ((6 / 5 : ℝ) * (w x ^ 2 / x) -
            (57 / 25 : ℝ) * w x ^ 2) +
              (93 / 50 : ℝ) *
                (yoshidaEndpointOctic x * w x ^ 2) := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num)
      (hmassUpper.const_mul _)
      (((hweighted.const_mul _).sub (hmassUpper.const_mul _)).add
        (hocticUpper.const_mul _))
    intro x hx
    have hdensity := one_fiftieth_le_endpointStripOcticTailDensity
      hx.1 hx.2
    have hmul := mul_le_mul_of_nonneg_right hdensity (sq_nonneg (w x))
    convert hmul using 1
    field_simp [ne_of_gt (by linarith [hx.1] : 0 < x)]
  repeat rw [intervalIntegral.integral_const_mul] at hlower hupper
  rw [intervalIntegral.integral_add
      (hmassLower.const_mul _) (hocticLower.const_mul _),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hlower
  rw [intervalIntegral.integral_add
      ((hweighted.const_mul _).sub (hmassUpper.const_mul _))
      (hocticUpper.const_mul _),
    intervalIntegral.integral_sub
      (hweighted.const_mul _) (hmassUpper.const_mul _),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hupper
  have hmassSplit := intervalIntegral.integral_add_adjacent_intervals
    hmassLower hmassUpper
  have hocticSplit := intervalIntegral.integral_add_adjacent_intervals
    hocticLower hocticUpper
  nlinarith

/-- Strong scalar tail coercivity obtained from the retained form-level
density.  This replaces the fallback `13/20000` global mass gap by `1/50`
without discarding the raw/prime/potential coupling used to prove it. -/
theorem one_fiftieth_positiveHalfMass_le_core_add_localWidthDefect_of_P1
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w)
    (hone : centeredOddP1Coefficient w = 0) :
    (1 / 50 : ℝ) * (∫ x : ℝ in 0..1, w x ^ 2) ≤
      fourCellOddHalfCoreReserve w + fourCellOddStripLocalWidthDefect w := by
  exact (one_fiftieth_positiveHalfMass_le_rawPrimePotentialTailWeight
    w hw.continuous).trans
      (rawPrimePotentialTailWeight_le_core_add_localWidthDefect_of_P1
        w hw hodd hone)

theorem fourCellOddHalfCoreReserve_oddStructuralLow (c d : ℝ) :
    fourCellOddHalfCoreReserve (factorTwoOddStructuralLowProfile c d) =
      (28 / 45 - (2 / 3 : ℝ) * Real.log 2) * c ^ 2 +
        (2 / 5 : ℝ) * c * d +
          (76 / 147 - (2 / 7 : ℝ) * Real.log 2) * d ^ 2 := by
  let w : ℝ → ℝ := factorTwoOddStructuralLowProfile c d
  have hw : ContDiff ℝ 1 w := by
    dsimp only [w]
    unfold factorTwoOddStructuralLowProfile centeredP1 centeredP3
    fun_prop
  have hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w :=
    hw.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1)
  have hraw := centeredRawLogEnergy_div_four_eq_positiveHalf_odd
    w hlocal (by simpa only [w] using odd_factorTwoOddStructuralLowProfile c d)
  unfold fourCellOddHalfCoreReserve
  rw [← hraw]
  dsimp only [w]
  rw [centeredRawLogEnergy_factorTwoOddStructuralLowProfile,
    integral_zero_one_endpointPotential_oddStructuralLow,
    integral_zero_one_oddStructuralLow_sq]
  ring

/-- `(1,1)` entry of the exact core plus local algebraic block. -/
def fourCellOddLowCombined11 : ℝ :=
  28 / 45 - (2 / 3 : ℝ) * Real.log 2 +
    fourCellOddLowLocalAlgebraic11

/-- Polarized `(1,3)` entry of the exact core plus local algebraic block. -/
def fourCellOddLowCombined13 : ℝ :=
  1 / 5 + fourCellOddLowLocalAlgebraic13

/-- `(3,3)` entry of the exact core plus local algebraic block. -/
def fourCellOddLowCombined33 : ℝ :=
  76 / 147 - (2 / 7 : ℝ) * Real.log 2 +
    fourCellOddLowLocalAlgebraic33

private theorem one_fourth_le_fourCellOddLowCombined11 :
    (1 / 4 : ℝ) ≤ fourCellOddLowCombined11 := by
  have hscalar := fourCellScalar_lt_31577_div_20000
  have hp := sqrt_two_mul_log_two_bounds.1
  have hl := strict_log_two_bounds.2
  rw [show fourCellOddLowCombined11 =
      893 / 600 - (31 / 50 : ℝ) * Real.log 2 +
        (94 / 375 : ℝ) * (Real.sqrt 2 * Real.log 2) -
          (2 / 3 : ℝ) *
            (Real.log (2 * fourCellOperatorHalfWidth) +
              Real.eulerMascheroniConstant + Real.log Real.pi) by
    unfold fourCellOddLowCombined11 fourCellOddLowLocalAlgebraic11
    ring]
  nlinarith

private theorem fourCellOddLowCombined13_nonneg :
    0 ≤ fourCellOddLowCombined13 := by
  rw [show fourCellOddLowCombined13 =
      93 / 500 + (104 / 3125 : ℝ) *
        (Real.sqrt 2 * Real.log 2) by
    unfold fourCellOddLowCombined13 fourCellOddLowLocalAlgebraic13
    ring]
  positivity

private theorem fourCellOddLowCombined13_le_eleven_fiftieths :
    fourCellOddLowCombined13 ≤ (11 / 50 : ℝ) := by
  have hp := sqrt_two_mul_log_two_bounds.2
  rw [show fourCellOddLowCombined13 =
      93 / 500 + (104 / 3125 : ℝ) *
        (Real.sqrt 2 * Real.log 2) by
    unfold fourCellOddLowCombined13 fourCellOddLowLocalAlgebraic13
    ring]
  nlinarith

private theorem one_fifth_le_fourCellOddLowCombined33 :
    (1 / 5 : ℝ) ≤ fourCellOddLowCombined33 := by
  have hscalar := fourCellScalar_lt_31577_div_20000
  have hp := sqrt_two_mul_log_two_bounds.2
  have hl := strict_log_two_bounds.2
  rw [show fourCellOddLowCombined33 =
      5434921 / 6125000 - (5242 / 109375 : ℝ) *
          (Real.sqrt 2 * Real.log 2) -
        (93 / 350 : ℝ) * Real.log 2 -
          (2 / 7 : ℝ) *
            (Real.log (2 * fourCellOperatorHalfWidth) +
              Real.eulerMascheroniConstant + Real.log Real.pi) by
    unfold fourCellOddLowCombined33 fourCellOddLowLocalAlgebraic33
    ring]
  nlinarith

theorem fourCellOddHalfCoreReserve_add_lowAlgebraic_eq (c d : ℝ) :
    fourCellOddHalfCoreReserve (factorTwoOddStructuralLowProfile c d) +
        fourCellOddLowLocalAlgebraicQuadratic c d =
      fourCellOddLowCombined11 * c ^ 2 +
        2 * fourCellOddLowCombined13 * c * d +
          fourCellOddLowCombined33 * d ^ 2 := by
  rw [fourCellOddHalfCoreReserve_oddStructuralLow]
  unfold fourCellOddLowLocalAlgebraicQuadratic
    fourCellOddLowCombined11 fourCellOddLowCombined13
    fourCellOddLowCombined33
  ring

/-- The exact combined low block dominates the complete regular budget.  A
single weighted square with ratio `277 / 250` certifies the residual
determinant after the absolute cross term is retained. -/
theorem fourCellOddLowRegularBudget_le_combined (c d : ℝ) :
    (13 / 2500 : ℝ) * c ^ 2 +
        (91 / 50000 : ℝ) * |c * d| +
          (61 / 100000 : ℝ) * d ^ 2 ≤
      fourCellOddLowCombined11 * c ^ 2 +
        2 * fourCellOddLowCombined13 * c * d +
          fourCellOddLowCombined33 * d ^ 2 := by
  let A : ℝ := fourCellOddLowCombined11
  let B : ℝ := fourCellOddLowCombined13
  let D : ℝ := fourCellOddLowCombined33
  have hA : (1 / 4 : ℝ) ≤ A := by
    simpa only [A] using one_fourth_le_fourCellOddLowCombined11
  have hB0 : 0 ≤ B := by
    simpa only [B] using fourCellOddLowCombined13_nonneg
  have hB1 : B ≤ (11 / 50 : ℝ) := by
    simpa only [B] using fourCellOddLowCombined13_le_eleven_fiftieths
  have hD : (1 / 5 : ℝ) ≤ D := by
    simpa only [D] using one_fifth_le_fourCellOddLowCombined33
  have hBabs : |B| ≤ (11 / 50 : ℝ) := by
    apply abs_le.mpr
    constructor <;> linarith
  have hAcross : |2 * B * c * d| ≤ (11 / 25 : ℝ) * |c * d| := by
    calc
      |2 * B * c * d| = 2 * |B| * |c * d| := by
        rw [show 2 * B * c * d = 2 * B * (c * d) by ring,
          abs_mul, abs_mul]
        norm_num
      _ ≤ 2 * (11 / 50 : ℝ) * |c * d| := by gcongr
      _ = (11 / 25 : ℝ) * |c * d| := by ring
  have hcross : -(11 / 25 : ℝ) * |c * d| ≤ 2 * B * c * d := by
    have h := (abs_le.mp hAcross).1
    linarith
  have hAmul : (1 / 4 : ℝ) * c ^ 2 ≤ A * c ^ 2 :=
    mul_le_mul_of_nonneg_right hA (sq_nonneg c)
  have hDmul : (1 / 5 : ℝ) * d ^ 2 ≤ D * d ^ 2 :=
    mul_le_mul_of_nonneg_right hD (sq_nonneg d)
  let A₀ : ℝ := 1 / 4 - 13 / 2500
  let D₀ : ℝ := 1 / 5 - 61 / 100000
  let K₀ : ℝ := 22091 / 50000
  have hreduce :
      A₀ * c ^ 2 + D₀ * d ^ 2 - K₀ * |c * d| ≤
        A * c ^ 2 + 2 * B * c * d + D * d ^ 2 -
          ((13 / 2500 : ℝ) * c ^ 2 +
            (91 / 50000 : ℝ) * |c * d| +
              (61 / 100000 : ℝ) * d ^ 2) := by
    dsimp only [A₀, D₀, K₀]
    linarith
  have hsquare : 0 ≤ (277 * |c| - 250 * |d|) ^ 2 := sq_nonneg _
  have hyoung :
      2 * |c * d| ≤ (277 / 250 : ℝ) * c ^ 2 +
        (250 / 277 : ℝ) * d ^ 2 := by
    rw [abs_mul]
    have hc : |c| ^ 2 = c ^ 2 := sq_abs c
    have hd : |d| ^ 2 = d ^ 2 := sq_abs d
    nlinarith
  have hweighted := mul_le_mul_of_nonneg_left hyoung
    (by norm_num : (0 : ℝ) ≤ 22091 / 100000)
  have hcCoeff :
      (22091 / 100000 : ℝ) * (277 / 250) ≤ A₀ := by
    norm_num [A₀]
  have hdCoeff :
      (22091 / 100000 : ℝ) * (250 / 277) ≤ D₀ := by
    norm_num [D₀]
  have hcMul := mul_le_mul_of_nonneg_right hcCoeff (sq_nonneg c)
  have hdMul := mul_le_mul_of_nonneg_right hdCoeff (sq_nonneg d)
  have hpositive : 0 ≤
      A₀ * c ^ 2 + D₀ * d ^ 2 - K₀ * |c * d| := by
    dsimp only [K₀] at hweighted ⊢
    linarith
  have hfinal := hpositive.trans hreduce
  dsimp only [A, B, D] at hfinal
  linarith

/-- Complete closure of the outstanding defect on `span(P₁,P₃)`.
This is the first exact nontrivial block of the desired universal absorption
inequality. -/
theorem fourCellOddHalfCoreReserve_add_localWidthDefect_low_nonneg
    (c d : ℝ) :
    0 ≤ fourCellOddHalfCoreReserve
          (factorTwoOddStructuralLowProfile c d) +
        fourCellOddStripLocalWidthDefect
          (factorTwoOddStructuralLowProfile c d) := by
  rw [fourCellOddStripLocalWidthDefect_oddStructuralLow_eq]
  change 0 ≤
    fourCellOddHalfCoreReserve (factorTwoOddStructuralLowProfile c d) +
      (fourCellOddLowLocalAlgebraicQuadratic c d -
        2 * fourCellOperatorHalfWidth *
          fourCellOddLowRegularQuadratic c d)
  have hcore := fourCellOddHalfCoreReserve_add_lowAlgebraic_eq c d
  have hregular :=
    two_mul_width_mul_fourCellOddLowRegularQuadratic_le c d
  have hbudget := fourCellOddLowRegularBudget_le_combined c d
  linarith

theorem neg_fourCellOddStripLocalWidthDefect_low_le_core
    (c d : ℝ) :
    -fourCellOddStripLocalWidthDefect
        (factorTwoOddStructuralLowProfile c d) ≤
      fourCellOddHalfCoreReserve
        (factorTwoOddStructuralLowProfile c d) := by
  linarith [fourCellOddHalfCoreReserve_add_localWidthDefect_low_nonneg c d]

/-! ## Exact universal low--tail reduction -/

/-- Exact decomposition of the full absorption target into the already
closed intrinsic low block, one coupled low--tail polarization, and the
genuine tail block.  The raw strip terms remain coupled in
`fourCellOddRawStripCancellationPolarization`, while the complete regular
correlation remains coupled in `fourCellOddStripReducedBilinear`. -/
theorem fourCellOddCoreLocal_lowTail_decomposition
    (w : ℝ → ℝ) (hw : Continuous w) :
    fourCellOddHalfCoreReserve w + fourCellOddStripLocalWidthDefect w =
      fourCellOddHalfCoreReserve (fourCellOddOneThreeLowPart w) +
        fourCellOddStripLocalWidthDefect (fourCellOddOneThreeLowPart w) +
      2 * (fourCellOddRawStripCancellationPolarization
          (fourCellOddOneThreeLowPart w)
          (centeredOddOneThreeResidual w) +
        fourCellOddStripReducedBilinear
          (fourCellOddOneThreeLowPart w)
          (centeredOddOneThreeResidual w)) +
      fourCellOddRawStripCancellationReserve
        (centeredOddOneThreeResidual w) +
      fourCellOddStripReducedRemainder
        (centeredOddOneThreeResidual w) := by
  let p : ℝ → ℝ := fourCellOddOneThreeLowPart w
  let v : ℝ → ℝ := centeredOddOneThreeResidual w
  have hp : Continuous p := by
    dsimp only [p, fourCellOddOneThreeLowPart]
    exact continuous_factorTwoOddStructuralLowProfile _ _
  have hv : Continuous v := by
    dsimp only [v]
    exact continuous_centeredOddOneThreeResidual w hw
  have hreconstruct : p + v = w := by
    dsimp only [p, v]
    exact fourCellOddOneThreeLowPart_add_residual w
  have hsplitP :=
    fourCellOddHalfCoreReserve_add_localWidthDefect_eq_raw_add_reduced p
  have hraw := fourCellOddRawStripCancellationReserve_add p v
  have hreduced := fourCellOddStripReducedRemainder_add p v hp hv
  change fourCellOddHalfCoreReserve w + fourCellOddStripLocalWidthDefect w =
    fourCellOddHalfCoreReserve p + fourCellOddStripLocalWidthDefect p +
      2 * (fourCellOddRawStripCancellationPolarization p v +
        fourCellOddStripReducedBilinear p v) +
      fourCellOddRawStripCancellationReserve v +
        fourCellOddStripReducedRemainder v
  calc
    fourCellOddHalfCoreReserve w + fourCellOddStripLocalWidthDefect w =
        fourCellOddRawStripCancellationReserve w +
          fourCellOddStripReducedRemainder w :=
      fourCellOddHalfCoreReserve_add_localWidthDefect_eq_raw_add_reduced w
    _ = fourCellOddRawStripCancellationReserve (p + v) +
          fourCellOddStripReducedRemainder (p + v) := by rw [hreconstruct]
    _ = (fourCellOddRawStripCancellationReserve p +
          fourCellOddStripReducedRemainder p) +
        2 * (fourCellOddRawStripCancellationPolarization p v +
          fourCellOddStripReducedBilinear p v) +
        fourCellOddRawStripCancellationReserve v +
          fourCellOddStripReducedRemainder v := by
      rw [hraw, hreduced]
      ring
    _ = _ := by rw [← hsplitP]

/-- Thus the universal theorem has one remaining, genuinely coupled
low--tail obligation; no finite cutoff or separate correlation estimate is
built into this reduction. -/
theorem neg_fourCellOddStripLocalWidthDefect_le_core_of_lowTail_nonneg
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w)
    (htail :
      0 ≤ 2 * (fourCellOddRawStripCancellationPolarization
            (fourCellOddOneThreeLowPart w)
            (centeredOddOneThreeResidual w) +
          fourCellOddStripReducedBilinear
            (fourCellOddOneThreeLowPart w)
            (centeredOddOneThreeResidual w)) +
        fourCellOddRawStripCancellationReserve
          (centeredOddOneThreeResidual w) +
        fourCellOddStripReducedRemainder
          (centeredOddOneThreeResidual w)) :
    -fourCellOddStripLocalWidthDefect w ≤ fourCellOddHalfCoreReserve w := by
  have hlow := fourCellOddHalfCoreReserve_add_localWidthDefect_low_nonneg
    (centeredOddP1Coefficient w) (centeredOddP3Coefficient w)
  have hdecomp := fourCellOddCoreLocal_lowTail_decomposition w hw.continuous
  unfold fourCellOddOneThreeLowPart at hdecomp htail
  linarith

/-! ## Exact `P₁/P₃/P₅`--`P₇+` Schur reduction

The endpoint-zero production profile has one more exceptional odd direction
than the preceding two-mode reduction can absorb.  We therefore extract the
exact `P₅` coefficient from the `P₁/P₃` residual.  What remains is genuinely
orthogonal to all three odd Legendre modes.  The theorem at the end of this
section reduces universal endpoint-zero positivity to a finite three-mode
block and one weighted dual-norm inequality on this infinite tail.
-/

/-- The normalized centered `P₅` coefficient. -/
def centeredOddP5Coefficient (w : ℝ → ℝ) : ℝ :=
  (11 / 2 : ℝ) * ∫ x : ℝ in -1..1,
    w x * factorTwoCenteredP5 x

private theorem shiftedLegendreReal_five_eval (t : ℝ) :
    (shiftedLegendreReal 5).eval t =
      1 - 30 * t + 210 * t ^ 2 - 560 * t ^ 3 +
        630 * t ^ 4 - 252 * t ^ 5 := by
  norm_num [shiftedLegendreReal, Polynomial.shiftedLegendre,
    Polynomial.eval_map, Polynomial.eval_finset_sum,
    Finset.sum_range_succ, Nat.choose]
  ring

private theorem centeredPullback_factorTwoCenteredP5_eq_neg_shiftedLegendre
    (t : ℝ) :
    centeredPullback factorTwoCenteredP5 t =
      -(shiftedLegendreReal 5).eval t := by
  rw [shiftedLegendreReal_five_eval]
  unfold centeredPullback factorTwoCenteredP5
  ring

private theorem centeredPullback_centeredP1_eq_neg_shiftedLegendre_local
    (t : ℝ) :
    centeredPullback centeredP1 t =
      -(shiftedLegendreReal 1).eval t := by
  unfold centeredPullback centeredP1
  calc
    2 * t - 1 =
        -(centeredShiftedLegendreReal 1).eval (2 * t - 1) := by
      rw [eval_centeredShiftedLegendreReal_one]
      ring
    _ = -(shiftedLegendreReal 1).eval (((2 * t - 1) + 1) / 2) := by
      rw [eval_centeredShiftedLegendreReal]
    _ = -(shiftedLegendreReal 1).eval t := by
      congr 2
      ring

private theorem centeredPullback_centeredP3_eq_neg_shiftedLegendre_local
    (t : ℝ) :
    centeredPullback centeredP3 t =
      -(shiftedLegendreReal 3).eval t := by
  unfold centeredPullback centeredP3
  calc
    (5 * (2 * t - 1) ^ 3 - 3 * (2 * t - 1)) / 2 =
        -(centeredShiftedLegendreReal 3).eval (2 * t - 1) := by
      rw [eval_centeredShiftedLegendreReal_three]
      ring
    _ = -(shiftedLegendreReal 3).eval (((2 * t - 1) + 1) / 2) := by
      rw [eval_centeredShiftedLegendreReal]
    _ = -(shiftedLegendreReal 3).eval t := by
      congr 2
      ring

private theorem integral_centeredPullback_mul_shiftedLegendre_eq_neg_half_local
    (n : ℕ) (q r : ℝ → ℝ)
    (hmode : ∀ t : ℝ, centeredPullback q t =
      -(shiftedLegendreReal n).eval t) :
    (∫ t : unitInterval,
      centeredPullback r (t : ℝ) *
        (shiftedLegendreReal n).eval (t : ℝ)) =
      -(1 / 2 : ℝ) * ∫ x : ℝ in -1..1,
        r x * q x := by
  calc
    (∫ t : unitInterval,
        centeredPullback r (t : ℝ) *
          (shiftedLegendreReal n).eval (t : ℝ)) =
        ∫ t : ℝ in 0..1,
          centeredPullback r t * (shiftedLegendreReal n).eval t := by
      change (∫ t : unitInterval,
        (fun s : ℝ ↦ centeredPullback r s *
          (shiftedLegendreReal n).eval s) (t : ℝ)) = _
      simpa only using integral_unitInterval_eq_intervalIntegral
        (fun s : ℝ ↦ centeredPullback r s *
          (shiftedLegendreReal n).eval s)
    _ = ∫ t : ℝ in 0..1,
        -((fun x : ℝ ↦ r x * q x) (2 * t - 1)) := by
      apply intervalIntegral.integral_congr
      intro t _ht
      have hpull := hmode t
      unfold centeredPullback at hpull ⊢
      have hp : (shiftedLegendreReal n).eval t =
          -q (2 * t - 1) := by
        linarith
      change r (2 * t - 1) * (shiftedLegendreReal n).eval t =
        -(r (2 * t - 1) * q (2 * t - 1))
      rw [hp]
      ring
    _ = -(∫ t : ℝ in 0..1,
        (fun x : ℝ ↦ r x * q x) (2 * t - 1)) := by
      rw [intervalIntegral.integral_neg]
    _ = -((1 / 2 : ℝ) * ∫ x : ℝ in -1..1,
        r x * q x) := by
      rw [integral_comp_two_mul_sub_one
        (fun x : ℝ ↦ r x * q x)]
    _ = _ := by ring

private theorem centeredRawLogBilinear_polynomialMode_eq_four_mul_pair
    (p : ℝ[X]) (q r : ℝ → ℝ) (hr : Continuous r)
    (hmode : ∀ t : ℝ, centeredPullback q t = p.eval t) :
    centeredRawLogBilinear q r =
      4 * ∫ t : unitInterval,
        centeredPullback r (t : ℝ) *
          (shiftedLogKernel p).eval (t : ℝ) := by
  let f : unitInterval → ℝ := fun t ↦ centeredPullback r (t : ℝ)
  let U : unitInterval × unitInterval → ℝ := fun z ↦
    (f z.1 - f z.2) * unitIntervalRawPolynomialLogKernel p z
  have hfcont : Continuous f := by
    dsimp only [f, centeredPullback]
    exact hr.comp (by fun_prop)
  have hf : Integrable f :=
    hfcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hUInt : Integrable U := by
    simpa only [U] using
      integrable_sub_mul_unitIntervalRawPolynomialLogKernel f hf p
  have hcross :=
    integral_sub_mul_unitIntervalRawPolynomialLogKernel_eq f hf p
  have hUpair : (∫ z, U z) =
      2 * ∫ t : unitInterval,
        centeredPullback r (t : ℝ) *
          (shiftedLogKernel p).eval (t : ℝ) := by
    simpa only [U, f] using hcross
  have hiter : (∫ z, U z) =
      ∫ s : ℝ in 0..1, ∫ t : ℝ in 0..1,
        (centeredPullback r s - centeredPullback r t) *
          ((p.eval s - p.eval t) / |s - t|) := by
    calc
      (∫ z, U z) = ∫ s : unitInterval, ∫ t : unitInterval, U (s, t) :=
        MeasureTheory.integral_prod _ hUInt
      _ = ∫ s : unitInterval, ∫ t : ℝ in 0..1,
          (centeredPullback r (s : ℝ) - centeredPullback r t) *
            ((p.eval (s : ℝ) - p.eval t) / |(s : ℝ) - t|) := by
        apply integral_congr_ae
        filter_upwards [] with s
        rw [← integral_unitInterval_eq_intervalIntegral]
        apply integral_congr_ae
        filter_upwards [] with t
        rfl
      _ = _ := by
        rw [← integral_unitInterval_eq_intervalIntegral]
  rw [hiter] at hUpair
  have hpoint (s t : ℝ) :
      (centeredPullback r s - centeredPullback r t) *
          ((p.eval s - p.eval t) / |s - t|) =
        2 * (((q (2 * s - 1) - q (2 * t - 1)) *
          (r (2 * s - 1) - r (2 * t - 1))) /
            |(2 * s - 1) - (2 * t - 1)|) := by
    have hms := hmode s
    have hmt := hmode t
    unfold centeredPullback at hms hmt ⊢
    rw [← hms, ← hmt,
      show (2 * s - 1) - (2 * t - 1) = 2 * (s - t) by ring,
      abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    by_cases hst : |s - t| = 0
    · simp [hst]
    · field_simp [hst]
  have hscaled :
      (∫ s : ℝ in 0..1, ∫ t : ℝ in 0..1,
        (centeredPullback r s - centeredPullback r t) *
          ((p.eval s - p.eval t) / |s - t|)) =
        (1 / 2 : ℝ) * centeredRawLogBilinear q r := by
    let H : ℝ → ℝ → ℝ := fun x y ↦
      ((q x - q y) * (r x - r y)) / |x - y|
    calc
      _ = ∫ s : ℝ in 0..1, ∫ t : ℝ in 0..1,
          2 * H (2 * s - 1) (2 * t - 1) := by
        apply intervalIntegral.integral_congr
        intro s _hs
        apply intervalIntegral.integral_congr
        intro t _ht
        exact hpoint s t
      _ = 2 * (∫ s : ℝ in 0..1, ∫ t : ℝ in 0..1,
          H (2 * s - 1) (2 * t - 1)) := by
        rw [show (fun s : ℝ ↦ ∫ t : ℝ in 0..1,
            2 * H (2 * s - 1) (2 * t - 1)) =
            fun s ↦ 2 * ∫ t : ℝ in 0..1,
              H (2 * s - 1) (2 * t - 1) by
          funext s
          rw [intervalIntegral.integral_const_mul],
          intervalIntegral.integral_const_mul]
      _ = 2 * ((1 / 4 : ℝ) *
          ∫ x : ℝ in -1..1, ∫ y : ℝ in -1..1, H x y) := by
        rw [integral_integral_comp_two_mul_sub_one H]
      _ = _ := by
        unfold centeredRawLogBilinear
        dsimp only [H]
        ring
  rw [hscaled] at hUpair
  linarith

private theorem centeredRawLogBilinear_polynomialMode_tail_eq_zero
    (p : ℝ[X]) (q r : ℝ → ℝ) (hr : Continuous r)
    (hmode : ∀ t : ℝ, centeredPullback q t = p.eval t)
    (hpair : (∫ t : unitInterval,
      centeredPullback r (t : ℝ) *
        (shiftedLogKernel p).eval (t : ℝ)) = 0) :
    centeredRawLogBilinear q r = 0 := by
  rw [centeredRawLogBilinear_polynomialMode_eq_four_mul_pair
    p q r hr hmode, hpair]
  ring

/-- Exact all-degree raw-log orthogonality of the centered fifth Legendre
mode and a continuous residual with vanishing fifth coefficient.  This is
the missing singular-form identity needed to retain the full raw form in
the `P₁/P₃/P₅` Schur reduction. -/
theorem centeredRawLogBilinear_factorTwoCenteredP5_tail_eq_zero
    (r : ℝ → ℝ) (hr : Continuous r)
    (hfive : centeredOddP5Coefficient r = 0) :
    centeredRawLogBilinear factorTwoCenteredP5 r = 0 := by
  let f : unitInterval → ℝ := fun t ↦ centeredPullback r (t : ℝ)
  let p : ℝ[X] := shiftedLegendreReal 5
  let U : unitInterval × unitInterval → ℝ := fun z ↦
    (f z.1 - f z.2) * unitIntervalRawPolynomialLogKernel p z
  have hfcont : Continuous f := by
    dsimp only [f, centeredPullback]
    exact hr.comp (by fun_prop)
  have hf : Integrable f :=
    hfcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hUInt : Integrable U := by
    simpa only [U] using
      integrable_sub_mul_unitIntervalRawPolynomialLogKernel f hf p
  have hcross :=
    integral_sub_mul_unitIntervalRawPolynomialLogKernel_eq f hf p
  have hpull : (∫ t : unitInterval, f t * p.eval (t : ℝ)) = 0 := by
    rw [show (∫ t : unitInterval, f t * p.eval (t : ℝ)) =
        -(1 / 2 : ℝ) * ∫ x : ℝ in -1..1,
          r x * factorTwoCenteredP5 x by
      simpa only [f, p] using
        integral_centeredPullback_mul_shiftedLegendre_eq_neg_half_local
          5 factorTwoCenteredP5 r
            centeredPullback_factorTwoCenteredP5_eq_neg_shiftedLegendre]
    unfold centeredOddP5Coefficient at hfive
    have horth : (∫ x : ℝ in -1..1,
        r x * factorTwoCenteredP5 x) = 0 := by
      nlinarith
    rw [horth]
    ring
  have hpair : (∫ t : unitInterval,
      f t * (shiftedLogKernel p).eval (t : ℝ)) = 0 := by
    rw [show shiftedLogKernel p =
        Polynomial.C (2 * (harmonic 5 : ℝ)) * p by
      dsimp only [p]
      exact shiftedLogKernel_shiftedLegendreReal 5]
    simp only [Polynomial.eval_mul, Polynomial.eval_C]
    rw [show (∫ t : unitInterval,
        f t * ((2 * (harmonic 5 : ℝ)) * p.eval (t : ℝ))) =
        (2 * (harmonic 5 : ℝ)) *
          ∫ t : unitInterval, f t * p.eval (t : ℝ) by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with t
      ring,
      hpull]
    ring
  rw [hpair] at hcross
  norm_num at hcross
  have hUzero : (∫ z, U z) = 0 := by
    simpa only [U] using hcross
  have hiter : (∫ z, U z) =
      ∫ s : ℝ in 0..1, ∫ t : ℝ in 0..1,
        (centeredPullback r s - centeredPullback r t) *
          ((p.eval s - p.eval t) / |s - t|) := by
    calc
      (∫ z, U z) = ∫ s : unitInterval, ∫ t : unitInterval, U (s, t) :=
        MeasureTheory.integral_prod _ hUInt
      _ = ∫ s : unitInterval, ∫ t : ℝ in 0..1,
          (centeredPullback r (s : ℝ) - centeredPullback r t) *
            ((p.eval (s : ℝ) - p.eval t) / |(s : ℝ) - t|) := by
        apply integral_congr_ae
        filter_upwards [] with s
        rw [← integral_unitInterval_eq_intervalIntegral]
        apply integral_congr_ae
        filter_upwards [] with t
        rfl
      _ = _ := by
        rw [← integral_unitInterval_eq_intervalIntegral]
  rw [hiter] at hUzero
  have hpoint (s t : ℝ) :
      (centeredPullback r s - centeredPullback r t) *
          ((p.eval s - p.eval t) / |s - t|) =
        -2 * (((factorTwoCenteredP5 (2 * s - 1) -
            factorTwoCenteredP5 (2 * t - 1)) *
          (r (2 * s - 1) - r (2 * t - 1))) /
            |(2 * s - 1) - (2 * t - 1)|) := by
    have hms :=
      centeredPullback_factorTwoCenteredP5_eq_neg_shiftedLegendre s
    have hmt :=
      centeredPullback_factorTwoCenteredP5_eq_neg_shiftedLegendre t
    unfold centeredPullback at hms hmt ⊢
    have hps : p.eval s = -factorTwoCenteredP5 (2 * s - 1) := by
      dsimp only [p]
      linarith
    have hpt : p.eval t = -factorTwoCenteredP5 (2 * t - 1) := by
      dsimp only [p]
      linarith
    rw [hps, hpt,
      show (2 * s - 1) - (2 * t - 1) = 2 * (s - t) by ring,
      abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    by_cases hst : |s - t| = 0
    · simp [hst]
    · field_simp [hst]
      ring
  have hscaled :
      (∫ s : ℝ in 0..1, ∫ t : ℝ in 0..1,
        (centeredPullback r s - centeredPullback r t) *
          ((p.eval s - p.eval t) / |s - t|)) =
        -(1 / 2 : ℝ) *
          centeredRawLogBilinear factorTwoCenteredP5 r := by
    let H : ℝ → ℝ → ℝ := fun x y ↦
      ((factorTwoCenteredP5 x - factorTwoCenteredP5 y) *
        (r x - r y)) / |x - y|
    calc
      _ = ∫ s : ℝ in 0..1, ∫ t : ℝ in 0..1,
          -2 * H (2 * s - 1) (2 * t - 1) := by
        apply intervalIntegral.integral_congr
        intro s _hs
        apply intervalIntegral.integral_congr
        intro t _ht
        exact hpoint s t
      _ = -2 * (∫ s : ℝ in 0..1, ∫ t : ℝ in 0..1,
          H (2 * s - 1) (2 * t - 1)) := by
        rw [show (fun s : ℝ ↦ ∫ t : ℝ in 0..1,
            -2 * H (2 * s - 1) (2 * t - 1)) =
            fun s ↦ -2 * ∫ t : ℝ in 0..1,
              H (2 * s - 1) (2 * t - 1) by
          funext s
          rw [intervalIntegral.integral_const_mul],
          intervalIntegral.integral_const_mul]
      _ = -2 * ((1 / 4 : ℝ) *
          ∫ x : ℝ in -1..1, ∫ y : ℝ in -1..1, H x y) := by
        rw [integral_integral_comp_two_mul_sub_one H]
      _ = _ := by
        unfold centeredRawLogBilinear
        dsimp only [H]
        ring
  rw [hscaled] at hUzero
  linarith

/-- The `P₅` coefficient left after the exact `P₁/P₃` projection. -/
def fourCellOddP5TailCoefficient (w : ℝ → ℝ) : ℝ :=
  centeredOddP5Coefficient (centeredOddOneThreeResidual w)

/-- The exact finite odd pivot retained by the endpoint-zero Schur split. -/
def fourCellOddOneThreeFiveLowProfile (c d e : ℝ) : ℝ → ℝ := fun x ↦
  factorTwoOddStructuralLowProfile c d x + e * factorTwoCenteredP5 x

/-- The complete centered raw-log cross between the exact `P₁/P₃/P₅`
pivot and an infinite tail orthogonal to those three modes is zero.  The
three distinct harmonic eigenvalues are retained exactly; this is not a
finite cutoff estimate. -/
theorem centeredRawLogBilinear_oneThreeFiveLowProfile_tail_eq_zero
    (r : ℝ → ℝ) (hr : Continuous r)
    (hone : centeredOddP1Coefficient r = 0)
    (hthree : centeredOddP3Coefficient r = 0)
    (hfive : centeredOddP5Coefficient r = 0)
    (c d e : ℝ) :
    centeredRawLogBilinear
      (fourCellOddOneThreeFiveLowProfile c d e) r = 0 := by
  let p : ℝ[X] := -(c • shiftedLegendreReal 1 +
    d • shiftedLegendreReal 3 + e • shiftedLegendreReal 5)
  have hmode (t : ℝ) :
      centeredPullback (fourCellOddOneThreeFiveLowProfile c d e) t =
        p.eval t := by
    have h1 := centeredPullback_centeredP1_eq_neg_shiftedLegendre_local t
    have h3 := centeredPullback_centeredP3_eq_neg_shiftedLegendre_local t
    have h5 :=
      centeredPullback_factorTwoCenteredP5_eq_neg_shiftedLegendre t
    dsimp only [p]
    simp only [Polynomial.eval_neg, Polynomial.eval_add,
      Polynomial.eval_smul, smul_eq_mul]
    unfold centeredPullback at h1 h3 h5 ⊢
    unfold fourCellOddOneThreeFiveLowProfile
      factorTwoOddStructuralLowProfile
    rw [h1, h3, h5]
    ring
  have hunitOne : (∫ t : unitInterval,
      centeredPullback r (t : ℝ) *
        (shiftedLegendreReal 1).eval (t : ℝ)) = 0 := by
    rw [integral_centeredPullback_mul_shiftedLegendre_eq_neg_half_local
      1 centeredP1 r
        centeredPullback_centeredP1_eq_neg_shiftedLegendre_local,
      integral_mul_centeredP1_eq, hone]
    ring
  have hunitThree : (∫ t : unitInterval,
      centeredPullback r (t : ℝ) *
        (shiftedLegendreReal 3).eval (t : ℝ)) = 0 := by
    rw [integral_centeredPullback_mul_shiftedLegendre_eq_neg_half_local
      3 centeredP3 r
        centeredPullback_centeredP3_eq_neg_shiftedLegendre_local,
      integral_mul_centeredP3_eq, hthree]
    ring
  have horthFive : (∫ x : ℝ in -1..1,
      r x * factorTwoCenteredP5 x) = 0 := by
    unfold centeredOddP5Coefficient at hfive
    nlinarith
  have hunitFive : (∫ t : unitInterval,
      centeredPullback r (t : ℝ) *
        (shiftedLegendreReal 5).eval (t : ℝ)) = 0 := by
    rw [integral_centeredPullback_mul_shiftedLegendre_eq_neg_half_local
      5 factorTwoCenteredP5 r
        centeredPullback_factorTwoCenteredP5_eq_neg_shiftedLegendre,
      horthFive]
    ring
  have hpLog : shiftedLogKernel p =
      -(c • (Polynomial.C (2 * (harmonic 1 : ℝ)) *
          shiftedLegendreReal 1) +
        d • (Polynomial.C (2 * (harmonic 3 : ℝ)) *
          shiftedLegendreReal 3) +
        e • (Polynomial.C (2 * (harmonic 5 : ℝ)) *
          shiftedLegendreReal 5)) := by
    dsimp only [p]
    rw [map_neg, map_add, map_add, map_smul, map_smul, map_smul,
      shiftedLogKernel_shiftedLegendreReal,
      shiftedLogKernel_shiftedLegendreReal,
      shiftedLogKernel_shiftedLegendreReal]
  have hfcont : Continuous (fun t : unitInterval ↦
      centeredPullback r (t : ℝ)) := by
    unfold centeredPullback
    fun_prop
  have hOneInt : Integrable (fun t : unitInterval ↦
      centeredPullback r (t : ℝ) *
        (shiftedLegendreReal 1).eval (t : ℝ)) :=
    (hfcont.mul ((shiftedLegendreReal 1).continuous.comp
      continuous_subtype_val)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hThreeInt : Integrable (fun t : unitInterval ↦
      centeredPullback r (t : ℝ) *
        (shiftedLegendreReal 3).eval (t : ℝ)) :=
    (hfcont.mul ((shiftedLegendreReal 3).continuous.comp
      continuous_subtype_val)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hFiveInt : Integrable (fun t : unitInterval ↦
      centeredPullback r (t : ℝ) *
        (shiftedLegendreReal 5).eval (t : ℝ)) :=
    (hfcont.mul ((shiftedLegendreReal 5).continuous.comp
      continuous_subtype_val)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hpair : (∫ t : unitInterval,
      centeredPullback r (t : ℝ) *
        (shiftedLogKernel p).eval (t : ℝ)) = 0 := by
    rw [hpLog]
    simp only [Polynomial.eval_neg, Polynomial.eval_add,
      Polynomial.eval_smul, Polynomial.eval_mul, Polynomial.eval_C,
      smul_eq_mul]
    rw [show (fun t : unitInterval ↦ centeredPullback r (t : ℝ) *
        -(c * (2 * (harmonic 1 : ℝ) *
            (shiftedLegendreReal 1).eval (t : ℝ)) +
          d * (2 * (harmonic 3 : ℝ) *
            (shiftedLegendreReal 3).eval (t : ℝ)) +
          e * (2 * (harmonic 5 : ℝ) *
            (shiftedLegendreReal 5).eval (t : ℝ)))) =
        fun t : unitInterval ↦
          (-2 * c * (harmonic 1 : ℝ)) *
              (centeredPullback r (t : ℝ) *
                (shiftedLegendreReal 1).eval (t : ℝ)) +
            (-2 * d * (harmonic 3 : ℝ)) *
              (centeredPullback r (t : ℝ) *
                (shiftedLegendreReal 3).eval (t : ℝ)) +
            (-2 * e * (harmonic 5 : ℝ)) *
              (centeredPullback r (t : ℝ) *
                (shiftedLegendreReal 5).eval (t : ℝ)) by
      funext t
      ring]
    let gOne : unitInterval → ℝ := fun t ↦
      (-2 * c * (harmonic 1 : ℝ)) *
        (centeredPullback r (t : ℝ) *
          (shiftedLegendreReal 1).eval (t : ℝ))
    let gThree : unitInterval → ℝ := fun t ↦
      (-2 * d * (harmonic 3 : ℝ)) *
        (centeredPullback r (t : ℝ) *
          (shiftedLegendreReal 3).eval (t : ℝ))
    let gFive : unitInterval → ℝ := fun t ↦
      (-2 * e * (harmonic 5 : ℝ)) *
        (centeredPullback r (t : ℝ) *
          (shiftedLegendreReal 5).eval (t : ℝ))
    have hgOne : Integrable gOne := by
      simpa only [gOne] using
        hOneInt.const_mul (-2 * c * (harmonic 1 : ℝ))
    have hgThree : Integrable gThree := by
      simpa only [gThree] using
        hThreeInt.const_mul (-2 * d * (harmonic 3 : ℝ))
    have hgFive : Integrable gFive := by
      simpa only [gFive] using
        hFiveInt.const_mul (-2 * e * (harmonic 5 : ℝ))
    change (∫ t : unitInterval, (gOne + gThree + gFive) t) = 0
    calc
      (∫ t : unitInterval, (gOne + gThree + gFive) t) =
          (∫ t : unitInterval, gOne t) +
            (∫ t : unitInterval, gThree t) +
              ∫ t : unitInterval, gFive t := by
        rw [show (∫ t : unitInterval, (gOne + gThree + gFive) t) =
            (∫ t : unitInterval, (gOne + gThree) t) +
              ∫ t : unitInterval, gFive t by
          simpa only using integral_add (hgOne.add hgThree) hgFive,
          show (∫ t : unitInterval, (gOne + gThree) t) =
            (∫ t : unitInterval, gOne t) +
              ∫ t : unitInterval, gThree t by
            simpa only using integral_add hgOne hgThree]
      _ = 0 := by
        dsimp only [gOne, gThree, gFive]
        rw [integral_const_mul, integral_const_mul, integral_const_mul,
          hunitOne, hunitThree, hunitFive]
        ring
  exact centeredRawLogBilinear_polynomialMode_tail_eq_zero
    p (fourCellOddOneThreeFiveLowProfile c d e) r hr hmode hpair

/-- Exact logarithmic representer of the retained odd three-mode pivot.
The raw operator is diagonal on `P₁/P₃/P₅`, with the three harmonic
eigenvalues kept symbolically until the final rational identity. -/
theorem centeredRawLogBilinear_oneThreeFiveLowProfile_eq_moments
    (r : ℝ → ℝ) (hr : Continuous r) (c d e : ℝ) :
    centeredRawLogBilinear
        (fourCellOddOneThreeFiveLowProfile c d e) r =
      4 * c * (∫ x : ℝ in -1..1, r x * centeredP1 x) +
        (22 / 3 : ℝ) * d *
          (∫ x : ℝ in -1..1, r x * centeredP3 x) +
        (137 / 15 : ℝ) * e *
          (∫ x : ℝ in -1..1, r x * factorTwoCenteredP5 x) := by
  let p : ℝ[X] := -(c • shiftedLegendreReal 1 +
    d • shiftedLegendreReal 3 + e • shiftedLegendreReal 5)
  have hmode (t : ℝ) :
      centeredPullback (fourCellOddOneThreeFiveLowProfile c d e) t =
        p.eval t := by
    have h1 := centeredPullback_centeredP1_eq_neg_shiftedLegendre_local t
    have h3 := centeredPullback_centeredP3_eq_neg_shiftedLegendre_local t
    have h5 := centeredPullback_factorTwoCenteredP5_eq_neg_shiftedLegendre t
    dsimp only [p]
    simp only [Polynomial.eval_neg, Polynomial.eval_add,
      Polynomial.eval_smul, smul_eq_mul]
    unfold centeredPullback at h1 h3 h5 ⊢
    unfold fourCellOddOneThreeFiveLowProfile
      factorTwoOddStructuralLowProfile
    rw [h1, h3, h5]
    ring
  have hunitOne : (∫ t : unitInterval,
      centeredPullback r (t : ℝ) *
        (shiftedLegendreReal 1).eval (t : ℝ)) =
      -(1 / 2 : ℝ) * ∫ x : ℝ in -1..1, r x * centeredP1 x :=
    integral_centeredPullback_mul_shiftedLegendre_eq_neg_half_local
      1 centeredP1 r
        centeredPullback_centeredP1_eq_neg_shiftedLegendre_local
  have hunitThree : (∫ t : unitInterval,
      centeredPullback r (t : ℝ) *
        (shiftedLegendreReal 3).eval (t : ℝ)) =
      -(1 / 2 : ℝ) * ∫ x : ℝ in -1..1, r x * centeredP3 x :=
    integral_centeredPullback_mul_shiftedLegendre_eq_neg_half_local
      3 centeredP3 r
        centeredPullback_centeredP3_eq_neg_shiftedLegendre_local
  have hunitFive : (∫ t : unitInterval,
      centeredPullback r (t : ℝ) *
        (shiftedLegendreReal 5).eval (t : ℝ)) =
      -(1 / 2 : ℝ) * ∫ x : ℝ in -1..1,
        r x * factorTwoCenteredP5 x :=
    integral_centeredPullback_mul_shiftedLegendre_eq_neg_half_local
      5 factorTwoCenteredP5 r
        centeredPullback_factorTwoCenteredP5_eq_neg_shiftedLegendre
  have hpLog : shiftedLogKernel p =
      -(c • (Polynomial.C (2 * (harmonic 1 : ℝ)) *
          shiftedLegendreReal 1) +
        d • (Polynomial.C (2 * (harmonic 3 : ℝ)) *
          shiftedLegendreReal 3) +
        e • (Polynomial.C (2 * (harmonic 5 : ℝ)) *
          shiftedLegendreReal 5)) := by
    dsimp only [p]
    rw [map_neg, map_add, map_add, map_smul, map_smul, map_smul,
      shiftedLogKernel_shiftedLegendreReal,
      shiftedLogKernel_shiftedLegendreReal,
      shiftedLogKernel_shiftedLegendreReal]
  have hfcont : Continuous (fun t : unitInterval ↦
      centeredPullback r (t : ℝ)) := by
    unfold centeredPullback
    fun_prop
  have hOneInt : Integrable (fun t : unitInterval ↦
      centeredPullback r (t : ℝ) *
        (shiftedLegendreReal 1).eval (t : ℝ)) :=
    (hfcont.mul ((shiftedLegendreReal 1).continuous.comp
      continuous_subtype_val)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hThreeInt : Integrable (fun t : unitInterval ↦
      centeredPullback r (t : ℝ) *
        (shiftedLegendreReal 3).eval (t : ℝ)) :=
    (hfcont.mul ((shiftedLegendreReal 3).continuous.comp
      continuous_subtype_val)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hFiveInt : Integrable (fun t : unitInterval ↦
      centeredPullback r (t : ℝ) *
        (shiftedLegendreReal 5).eval (t : ℝ)) :=
    (hfcont.mul ((shiftedLegendreReal 5).continuous.comp
      continuous_subtype_val)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  let gOne : unitInterval → ℝ := fun t ↦
    (-2 * c * (harmonic 1 : ℝ)) *
      (centeredPullback r (t : ℝ) *
        (shiftedLegendreReal 1).eval (t : ℝ))
  let gThree : unitInterval → ℝ := fun t ↦
    (-2 * d * (harmonic 3 : ℝ)) *
      (centeredPullback r (t : ℝ) *
        (shiftedLegendreReal 3).eval (t : ℝ))
  let gFive : unitInterval → ℝ := fun t ↦
    (-2 * e * (harmonic 5 : ℝ)) *
      (centeredPullback r (t : ℝ) *
        (shiftedLegendreReal 5).eval (t : ℝ))
  have hgOne : Integrable gOne := by
    simpa only [gOne] using
      hOneInt.const_mul (-2 * c * (harmonic 1 : ℝ))
  have hgThree : Integrable gThree := by
    simpa only [gThree] using
      hThreeInt.const_mul (-2 * d * (harmonic 3 : ℝ))
  have hgFive : Integrable gFive := by
    simpa only [gFive] using
      hFiveInt.const_mul (-2 * e * (harmonic 5 : ℝ))
  have hraw := centeredRawLogBilinear_polynomialMode_eq_four_mul_pair
    p (fourCellOddOneThreeFiveLowProfile c d e) r hr hmode
  rw [hpLog] at hraw
  simp only [Polynomial.eval_neg, Polynomial.eval_add,
    Polynomial.eval_smul, Polynomial.eval_mul, Polynomial.eval_C,
    smul_eq_mul] at hraw
  rw [show (fun t : unitInterval ↦ centeredPullback r (t : ℝ) *
      -(c * (2 * (harmonic 1 : ℝ) *
          (shiftedLegendreReal 1).eval (t : ℝ)) +
        d * (2 * (harmonic 3 : ℝ) *
          (shiftedLegendreReal 3).eval (t : ℝ)) +
        e * (2 * (harmonic 5 : ℝ) *
          (shiftedLegendreReal 5).eval (t : ℝ)))) =
      fun t : unitInterval ↦ (gOne + gThree + gFive) t by
    funext t
    dsimp only [gOne, gThree, gFive]
    simp only [Pi.add_apply]
    ring] at hraw
  rw [show (∫ t : unitInterval, (gOne + gThree + gFive) t) =
      (∫ t : unitInterval, gOne t) +
        (∫ t : unitInterval, gThree t) +
          ∫ t : unitInterval, gFive t by
    rw [show (∫ t : unitInterval, (gOne + gThree + gFive) t) =
        (∫ t : unitInterval, (gOne + gThree) t) +
          ∫ t : unitInterval, gFive t by
      simpa only using integral_add (hgOne.add hgThree) hgFive,
      show (∫ t : unitInterval, (gOne + gThree) t) =
        (∫ t : unitInterval, gOne t) +
          ∫ t : unitInterval, gThree t by
        simpa only using integral_add hgOne hgThree]] at hraw
  dsimp only [gOne, gThree, gFive] at hraw
  rw [integral_const_mul, integral_const_mul, integral_const_mul,
    hunitOne, hunitThree, hunitFive] at hraw
  norm_num [harmonic] at hraw ⊢
  linarith

/-- The canonical `P₁/P₃/P₅` part of an arbitrary profile. -/
def fourCellOddOneThreeFiveLowPart (w : ℝ → ℝ) : ℝ → ℝ :=
  fourCellOddOneThreeFiveLowProfile
    (centeredOddP1Coefficient w) (centeredOddP3Coefficient w)
      (fourCellOddP5TailCoefficient w)

/-- The infinite odd tail after the exact `P₁/P₃/P₅` projection. -/
def fourCellOddOneThreeFiveResidual (w : ℝ → ℝ) : ℝ → ℝ := fun x ↦
  centeredOddOneThreeResidual w x -
    fourCellOddP5TailCoefficient w * factorTwoCenteredP5 x

theorem fourCellOddOneThreeFiveLowPart_add_residual (w : ℝ → ℝ) :
    fourCellOddOneThreeFiveLowPart w +
        fourCellOddOneThreeFiveResidual w = w := by
  funext x
  unfold fourCellOddOneThreeFiveLowPart
    fourCellOddOneThreeFiveLowProfile
    fourCellOddOneThreeFiveResidual centeredOddOneThreeResidual
    factorTwoOddStructuralLowProfile
  simp only [Pi.add_apply]
  ring

theorem contDiff_fourCellOddOneThreeFiveLowProfile (c d e : ℝ) :
    ContDiff ℝ 1 (fourCellOddOneThreeFiveLowProfile c d e) := by
  unfold fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
    centeredP1 centeredP3 factorTwoCenteredP5
  fun_prop

theorem odd_fourCellOddOneThreeFiveLowProfile (c d e : ℝ) :
    Function.Odd (fourCellOddOneThreeFiveLowProfile c d e) := by
  intro x
  unfold fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
    centeredP1 centeredP3 factorTwoCenteredP5
  ring

/-- Exact affine-strip transform of the retained odd `P₁/P₃/P₅` pivot.
The endpoint reflection-odd channel is again a three-mode Legendre profile;
in particular, no higher mode is created by the strip rescaling. -/
theorem fourCellOddEndpointStripOdd_oneThreeFiveLowProfile_eq_lowProfile
    (c d e : ℝ) :
    fourCellOddEndpointStripOdd
        (fourCellOddOneThreeFiveLowProfile c d e) =
      fourCellOddOneThreeFiveLowProfile
        (c / 5 + 84 * d / 125 + 276 * e / 625)
        (d / 125 + 84 * e / 625) (e / 3125) := by
  funext z
  unfold fourCellOddEndpointStripOdd fourCellOddEndpointStripPullback
    fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
    centeredP1 centeredP3 factorTwoCenteredP5
  ring

/-- Polynomial normal form of the reflection-even strip channel of the
retained `P₁/P₃/P₅` pivot. -/
theorem fourCellOddEndpointStripEven_oneThreeFiveLowProfile
    (c d e z : ℝ) :
    fourCellOddEndpointStripEven
        (fourCellOddOneThreeFiveLowProfile c d e) z =
      4 * c / 5 + 2 * d / 25 - 2497 * e / 6250 +
        (6 * d / 25 + 483 * e / 625) * z ^ 2 +
          (63 * e / 1250) * z ^ 4 := by
  unfold fourCellOddEndpointStripEven fourCellOddEndpointStripPullback
    fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
    centeredP1 centeredP3 factorTwoCenteredP5
  ring

private theorem factorTwoCenteredCorrelationBilinear_add_left_oneThreeFive
    (u v w : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    (hw : Continuous w) (t : ℝ) :
    factorTwoCenteredCorrelationBilinear (u + v) w t =
      factorTwoCenteredCorrelationBilinear u w t +
        factorTwoCenteredCorrelationBilinear v w t := by
  unfold factorTwoCenteredCorrelationBilinear
  rw [factorTwoCenteredCrossCorrelation_add_left u v w hu hv hw t,
    factorTwoCenteredCrossCorrelation_add_right w u v hw hu hv t]
  ring

/-- Exact six-entry endpoint-correlation polynomial of the retained
`P₁/P₃/P₅` pivot. -/
theorem centeredEndpointCorrelation_oneThreeFiveLowProfile
    (c d e t : ℝ) :
    centeredEndpointCorrelation
        (fourCellOddOneThreeFiveLowProfile c d e) t =
      c ^ 2 * oddStructuralCorrelation11 t +
        2 * c * d * oddStructuralCorrelation13 t +
        d ^ 2 * oddStructuralCorrelation33 t +
        2 * c * e * oddP5Correlation15 t +
        2 * d * e * oddP5Correlation35 t +
        e ^ 2 * oddP5Correlation55 t := by
  let q : ℝ → ℝ := factorTwoOddStructuralLowProfile c d
  let v : ℝ → ℝ := fun x ↦ e * factorTwoCenteredP5 x
  have hq : Continuous q := by
    simpa only [q] using continuous_factorTwoOddStructuralLowProfile c d
  have hv : Continuous v := by
    dsimp only [v]
    exact continuous_const.mul continuous_factorTwoCenteredP5
  have hprofile : fourCellOddOneThreeFiveLowProfile c d e = q + v := by
    funext x
    dsimp only [q, v]
    unfold fourCellOddOneThreeFiveLowProfile
    simp only [Pi.add_apply]
  have hcross : factorTwoCenteredCorrelationBilinear q v t =
      c * e * oddP5Correlation15 t +
        d * e * oddP5Correlation35 t := by
    rw [show q = c • centeredP1 + d • centeredP3 by
      funext x
      dsimp only [q]
      unfold factorTwoOddStructuralLowProfile
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul],
      show v = e • factorTwoCenteredP5 by
        funext x
        simp only [v, Pi.smul_apply, smul_eq_mul],
      factorTwoCenteredCorrelationBilinear_add_left_oneThreeFive
        (c • centeredP1) (d • centeredP3) (e • factorTwoCenteredP5)
        ((by unfold centeredP1; fun_prop : Continuous centeredP1).const_smul c)
        ((by unfold centeredP3; fun_prop : Continuous centeredP3).const_smul d)
        (continuous_factorTwoCenteredP5.const_smul e),
      factorTwoCenteredCorrelationBilinear_smul_smul,
      factorTwoCenteredCorrelationBilinear_smul_smul,
      factorTwoCenteredCorrelationBilinear_p1_p5,
      factorTwoCenteredCorrelationBilinear_p3_p5]
  have hself : centeredEndpointCorrelation v t =
      e ^ 2 * oddP5Correlation55 t := by
    rw [← factorTwoCenteredCorrelationBilinear_self,
      show v = e • factorTwoCenteredP5 by
        funext x
        simp only [v, Pi.smul_apply, smul_eq_mul],
      factorTwoCenteredCorrelationBilinear_smul_smul,
      factorTwoCenteredCorrelationBilinear_self,
      centeredEndpointCorrelation_p5]
    ring
  rw [hprofile, centeredEndpointCorrelation_add q v hq hv t,
    show centeredEndpointCorrelation q t =
        c ^ 2 * oddStructuralCorrelation11 t +
          2 * c * d * oddStructuralCorrelation13 t +
            d ^ 2 * oddStructuralCorrelation33 t by
      simpa only [q] using centeredEndpointCorrelation_oddStructuralLow c d t,
    hcross, hself]
  ring

/-! ### A full-width analytic regular-kernel envelope

The standalone wide-envelope module carries this analytic estimate so even
remainder arguments need not import the complete odd closure. -/

/-- Compatibility re-export of the standalone full-width regular-kernel
envelope. -/
theorem fourCell_yoshidaRegularKernelPolynomial6_wide_envelope
    {t : ℝ} (ht0 : 0 ≤ t) (htlog : t ≤ 2 * Real.log 2) :
    0 ≤ yoshidaRegularKernel t - yoshidaRegularKernelPolynomial6 t ∧
      yoshidaRegularKernel t - yoshidaRegularKernelPolynomial6 t <
        (1 / 1900 : ℝ) :=
  YoshidaFourCellRegularKernelWideEnvelope.fourCell_yoshidaRegularKernelPolynomial6_wide_envelope
    ht0 htlog

/-- Signed remainder after replacing the full-width regular kernel by its
sixth-order polynomial. -/
def fourCellWideRegularEnvelopeError (C : ℝ → ℝ) : ℝ :=
  ∫ t : ℝ in 0..2,
    (yoshidaRegularKernel (fourCellOperatorHalfWidth * t) -
      yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t)) * C t

private theorem fourCellWideRegularEnvelope_pointwise
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 2) :
    0 ≤ yoshidaRegularKernel (fourCellOperatorHalfWidth * t) -
        yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t) ∧
      yoshidaRegularKernel (fourCellOperatorHalfWidth * t) -
          yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t) <
        (1 / 1900 : ℝ) := by
  apply fourCell_yoshidaRegularKernelPolynomial6_wide_envelope
  · exact mul_nonneg
      (by unfold fourCellOperatorHalfWidth; positivity) ht.1
  · have hmul := mul_le_mul_of_nonneg_left ht.2
        (by unfold fourCellOperatorHalfWidth; positivity :
          0 ≤ fourCellOperatorHalfWidth)
    have hlog : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
    calc
      fourCellOperatorHalfWidth * t ≤
          fourCellOperatorHalfWidth * 2 := hmul
      _ = 5 * Real.log 2 / 4 := by
        unfold fourCellOperatorHalfWidth
        ring
      _ ≤ 2 * Real.log 2 := by nlinarith

private theorem intervalIntegrable_fourCellWideRegularEnvelope_mul
    (C : ℝ → ℝ) (hC : Continuous C) :
    IntervalIntegrable
      (fun t ↦
        (yoshidaRegularKernel (fourCellOperatorHalfWidth * t) -
          yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t)) *
            C t)
      volume 0 2 := by
  let f : ℝ → ℝ := fun t ↦
    (yoshidaRegularKernel (fourCellOperatorHalfWidth * t) -
      yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t)) * C t
  let g : ℝ → ℝ := fun t ↦ (1 / 1900 : ℝ) * |C t|
  have hgIcc : IntegrableOn g (Icc (0 : ℝ) 2) volume := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    exact (continuous_const.mul hC.abs).continuousOn
  have hg : Integrable g (volume.restrict (Ioc (0 : ℝ) 2)) :=
    hgIcc.mono_set Ioc_subset_Icc_self
  have hfmeas : AEStronglyMeasurable f
      (volume.restrict (Ioc (0 : ℝ) 2)) := by
    apply Measurable.aestronglyMeasurable
    dsimp only [f]
    exact ((measurable_yoshidaRegularKernel.comp
      (measurable_const.mul measurable_id)).sub
        (by unfold yoshidaRegularKernelPolynomial6; fun_prop)).mul
          hC.measurable
  have hfg : ∀ᵐ t : ℝ ∂(volume.restrict (Ioc (0 : ℝ) 2)),
      ‖f t‖ ≤ g t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have htIcc : t ∈ Icc (0 : ℝ) 2 := ⟨ht.1.le, ht.2⟩
    have henv := fourCellWideRegularEnvelope_pointwise htIcc
    dsimp only [f, g]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg henv.1]
    exact mul_le_mul_of_nonneg_right henv.2.le (abs_nonneg (C t))
  constructor
  · exact Integrable.mono' hg hfmeas hfg
  · simp

/-- The full-width polynomial replacement loses at most `1/1900` times
the exact correlation `L¹` mass. -/
theorem abs_fourCellWideRegularEnvelopeError_le
    (C : ℝ → ℝ) (hC : Continuous C) :
    |fourCellWideRegularEnvelopeError C| ≤
      (1 / 1900 : ℝ) * (∫ t : ℝ in 0..2, |C t|) := by
  let f : ℝ → ℝ := fun t ↦
    (yoshidaRegularKernel (fourCellOperatorHalfWidth * t) -
      yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t)) * C t
  let g : ℝ → ℝ := fun t ↦ (1 / 1900 : ℝ) * |C t|
  have hf : IntervalIntegrable f volume 0 2 := by
    dsimp only [f]
    exact intervalIntegrable_fourCellWideRegularEnvelope_mul C hC
  have hg : IntervalIntegrable g volume 0 2 := by
    dsimp only [g]
    exact (hC.abs.const_mul (1 / 1900 : ℝ)).intervalIntegrable 0 2
  have hmono :
      (∫ t : ℝ in 0..2, |f t|) ≤ ∫ t : ℝ in 0..2, g t := by
    apply intervalIntegral.integral_mono_on (by norm_num) hf.abs hg
    intro t ht
    have henv := fourCellWideRegularEnvelope_pointwise ht
    dsimp only [f, g]
    rw [abs_mul, abs_of_nonneg henv.1]
    exact mul_le_mul_of_nonneg_right henv.2.le (abs_nonneg (C t))
  calc
    |fourCellWideRegularEnvelopeError C| =
        |∫ t : ℝ in 0..2, f t| := by
      unfold fourCellWideRegularEnvelopeError
      rfl
    _ ≤ ∫ t : ℝ in 0..2, |f t| :=
      intervalIntegral.abs_integral_le_integral_abs (by norm_num)
    _ ≤ ∫ t : ℝ in 0..2, g t := hmono
    _ = (1 / 1900 : ℝ) * (∫ t : ℝ in 0..2, |C t|) := by
      dsimp only [g]
      rw [intervalIntegral.integral_const_mul]

private theorem fourCellWideRegularEnvelope_pointwise_sevenEighths
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 2) :
    0 ≤ yoshidaRegularKernel (fourCellOperatorHalfWidth * t) -
        yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t) ∧
      yoshidaRegularKernel (fourCellOperatorHalfWidth * t) -
          yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t) <
        (1 / 80000 : ℝ) := by
  apply fourCell_yoshidaRegularKernelPolynomial6_sevenEighths_envelope
  · exact mul_nonneg
      (by unfold fourCellOperatorHalfWidth; positivity) ht.1
  · have hmul := mul_le_mul_of_nonneg_left ht.2
        (by unfold fourCellOperatorHalfWidth; positivity :
          0 ≤ fourCellOperatorHalfWidth)
    have hlog := strict_log_two_bounds.2
    calc
      fourCellOperatorHalfWidth * t ≤
          fourCellOperatorHalfWidth * 2 := hmul
      _ = 5 * Real.log 2 / 4 := by
        unfold fourCellOperatorHalfWidth
        ring
      _ ≤ (7 / 8 : ℝ) := by linarith

/-- On the actual four-cell range the global polynomial remainder is at
most `1/80000` times the exact correlation `L¹` mass.  This is the common
analytic input for the finite five-mode certificate. -/
theorem abs_fourCellWideRegularEnvelopeError_le_sevenEighths
    (C : ℝ → ℝ) (hC : Continuous C) :
    |fourCellWideRegularEnvelopeError C| ≤
      (1 / 80000 : ℝ) * (∫ t : ℝ in 0..2, |C t|) := by
  let f : ℝ → ℝ := fun t ↦
    (yoshidaRegularKernel (fourCellOperatorHalfWidth * t) -
      yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t)) * C t
  let g : ℝ → ℝ := fun t ↦ (1 / 80000 : ℝ) * |C t|
  have hf : IntervalIntegrable f volume 0 2 := by
    dsimp only [f]
    exact intervalIntegrable_fourCellWideRegularEnvelope_mul C hC
  have hg : IntervalIntegrable g volume 0 2 := by
    dsimp only [g]
    exact (hC.abs.const_mul (1 / 80000 : ℝ)).intervalIntegrable 0 2
  have hmono :
      (∫ t : ℝ in 0..2, |f t|) ≤ ∫ t : ℝ in 0..2, g t := by
    apply intervalIntegral.integral_mono_on (by norm_num) hf.abs hg
    intro t ht
    have henv := fourCellWideRegularEnvelope_pointwise_sevenEighths ht
    dsimp only [f, g]
    rw [abs_mul, abs_of_nonneg henv.1]
    exact mul_le_mul_of_nonneg_right henv.2.le (abs_nonneg (C t))
  calc
    |fourCellWideRegularEnvelopeError C| =
        |∫ t : ℝ in 0..2, f t| := by
      unfold fourCellWideRegularEnvelopeError
      rfl
    _ ≤ ∫ t : ℝ in 0..2, |f t| :=
      intervalIntegral.abs_integral_le_integral_abs (by norm_num)
    _ ≤ ∫ t : ℝ in 0..2, g t := hmono
    _ = (1 / 80000 : ℝ) * (∫ t : ℝ in 0..2, |C t|) := by
      dsimp only [g]
      rw [intervalIntegral.integral_const_mul]

private theorem fourCellRegularIntegral_eq_polynomial_add_error
    (C : ℝ → ℝ) (hC : Continuous C) :
    (∫ t : ℝ in 0..2,
      yoshidaRegularKernel (fourCellOperatorHalfWidth * t) * C t) =
      (∫ t : ℝ in 0..2,
        yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t) *
          C t) +
        fourCellWideRegularEnvelopeError C := by
  have herr := intervalIntegrable_fourCellWideRegularEnvelope_mul C hC
  have hpoly : IntervalIntegrable
      (fun t : ℝ ↦
        yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t) *
          C t) volume 0 2 := by
    exact (by
      unfold yoshidaRegularKernelPolynomial6
      fun_prop : Continuous (fun t : ℝ ↦
        yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t) *
          C t)).intervalIntegrable 0 2
  rw [show (fun t : ℝ ↦
      yoshidaRegularKernel (fourCellOperatorHalfWidth * t) * C t) =
      fun t ↦
        yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t) *
            C t +
          (yoshidaRegularKernel (fourCellOperatorHalfWidth * t) -
            yoshidaRegularKernelPolynomial6
              (fourCellOperatorHalfWidth * t)) * C t by
    funext t
    ring,
    intervalIntegral.integral_add hpoly herr]
  unfold fourCellWideRegularEnvelopeError
  ring

theorem abs_fourCellWideRegularEnvelopeError11_le :
    |fourCellWideRegularEnvelopeError oddStructuralCorrelation11| ≤
      (1 / 2850 : ℝ) := by
  have herr := abs_fourCellWideRegularEnvelopeError_le
    oddStructuralCorrelation11
      (by unfold oddStructuralCorrelation11; fun_prop)
  have hmass := integral_abs_oddStructuralCorrelation11_le
  nlinarith

theorem abs_fourCellWideRegularEnvelopeError13_lt :
    |fourCellWideRegularEnvelopeError oddStructuralCorrelation13| <
      (1 / 11400 : ℝ) := by
  have herr := abs_fourCellWideRegularEnvelopeError_le
    oddStructuralCorrelation13
      (by unfold oddStructuralCorrelation13; fun_prop)
  have hmass := integral_abs_oddStructuralCorrelation13_lt
  nlinarith

theorem abs_fourCellWideRegularEnvelopeError33_le :
    |fourCellWideRegularEnvelopeError oddStructuralCorrelation33| ≤
      (1 / 6650 : ℝ) := by
  have herr := abs_fourCellWideRegularEnvelopeError_le
    oddStructuralCorrelation33
      (by unfold oddStructuralCorrelation33; fun_prop)
  have hmass := integral_abs_oddStructuralCorrelation33_le
  nlinarith

theorem abs_fourCellWideRegularEnvelopeError15_lt :
    |fourCellWideRegularEnvelopeError oddP5Correlation15| <
      (1 / 23750 : ℝ) := by
  have herr := abs_fourCellWideRegularEnvelopeError_le oddP5Correlation15
    (by unfold oddP5Correlation15; fun_prop)
  have hmass := integral_abs_oddP5Correlation15_lt
  nlinarith

theorem abs_fourCellWideRegularEnvelopeError35_lt :
    |fourCellWideRegularEnvelopeError oddP5Correlation35| <
      (11 / 237500 : ℝ) := by
  have herr := abs_fourCellWideRegularEnvelopeError_le oddP5Correlation35
    (by unfold oddP5Correlation35; fun_prop)
  have hmass := integral_abs_oddP5Correlation35_lt
  nlinarith

theorem abs_fourCellWideRegularEnvelopeError55_le :
    |fourCellWideRegularEnvelopeError oddP5Correlation55| ≤
      (1 / 10450 : ℝ) := by
  have herr := abs_fourCellWideRegularEnvelopeError_le oddP5Correlation55
    continuous_oddP5Correlation55
  have hmass := integral_abs_oddP5Correlation55_le
  nlinarith

/-! ### Exact full-width polynomial moments -/

def fourCellWideRegularPolynomial11 : ℝ :=
  (1 / 288 : ℝ) * Real.log 2 +
    (25 / 4608 : ℝ) * Real.log 2 ^ 2 -
      (5 / 49152 : ℝ) * Real.log 2 ^ 3 -
        (625 / 1179648 : ℝ) * Real.log 2 ^ 4 +
          (96875 / 37456183296 : ℝ) * Real.log 2 ^ 5 +
            (38125 / 704643072 : ℝ) * Real.log 2 ^ 6

def fourCellWideRegularPolynomial13 : ℝ :=
  -(1 / 4032 : ℝ) * Real.log 2 -
    (5 / 663552 : ℝ) * Real.log 2 ^ 3 -
      (625 / 8257536 : ℝ) * Real.log 2 ^ 4 +
        (96875 / 183119118336 : ℝ) * Real.log 2 ^ 5 +
          (38125 / 2717908992 : ℝ) * Real.log 2 ^ 6

def fourCellWideRegularPolynomial33 : ℝ :=
  (1 / 6048 : ℝ) * Real.log 2 +
    (5 / 4866048 : ℝ) * Real.log 2 ^ 3 +
      (96875 / 1785411403776 : ℝ) * Real.log 2 ^ 5 +
        (38125 / 14797504512 : ℝ) * Real.log 2 ^ 6

def fourCellWideRegularPolynomial15 : ℝ :=
  (5 / 29196288 : ℝ) * Real.log 2 ^ 3 +
    (19375 / 1190274269184 : ℝ) * Real.log 2 ^ 5 +
      (190625 / 209278992384 : ℝ) * Real.log 2 ^ 6

def fourCellWideRegularPolynomial35 : ℝ :=
  -(5 / 133056 : ℝ) * Real.log 2 -
    (5 / 31629312 : ℝ) * Real.log 2 ^ 3 -
      (19375 / 7141645615104 : ℝ) * Real.log 2 ^ 5

def fourCellWideRegularPolynomial55 : ℝ :=
  (5 / 123552 : ℝ) * Real.log 2 +
    (5 / 63258624 : ℝ) * Real.log 2 ^ 3 +
      (19375 / 30351993864192 : ℝ) * Real.log 2 ^ 5

theorem integral_fourCellRegularPolynomial_mul_oddStructuralCorrelation11 :
    (∫ t : ℝ in 0..2,
      yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t) *
        oddStructuralCorrelation11 t) =
      fourCellWideRegularPolynomial11 := by
  unfold yoshidaRegularKernelPolynomial6 fourCellOperatorHalfWidth
    oddStructuralCorrelation11 fourCellWideRegularPolynomial11
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [intervalIntegral.integral_const_mul]
  repeat rw [integral_pow]
  norm_num
  ring

theorem integral_fourCellRegularPolynomial_mul_oddStructuralCorrelation13 :
    (∫ t : ℝ in 0..2,
      yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t) *
        oddStructuralCorrelation13 t) =
      fourCellWideRegularPolynomial13 := by
  unfold yoshidaRegularKernelPolynomial6 fourCellOperatorHalfWidth
    oddStructuralCorrelation13 fourCellWideRegularPolynomial13
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [intervalIntegral.integral_const_mul]
  repeat rw [integral_pow]
  norm_num
  ring

theorem integral_fourCellRegularPolynomial_mul_oddStructuralCorrelation33 :
    (∫ t : ℝ in 0..2,
      yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t) *
        oddStructuralCorrelation33 t) =
      fourCellWideRegularPolynomial33 := by
  unfold yoshidaRegularKernelPolynomial6 fourCellOperatorHalfWidth
    oddStructuralCorrelation33 fourCellWideRegularPolynomial33
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [intervalIntegral.integral_const_mul]
  repeat rw [integral_pow]
  norm_num
  ring

theorem integral_fourCellRegularPolynomial_mul_oddP5Correlation15 :
    (∫ t : ℝ in 0..2,
      yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t) *
        oddP5Correlation15 t) =
      fourCellWideRegularPolynomial15 := by
  unfold yoshidaRegularKernelPolynomial6 fourCellOperatorHalfWidth
    oddP5Correlation15 fourCellWideRegularPolynomial15
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [intervalIntegral.integral_const_mul]
  repeat rw [integral_pow]
  norm_num
  ring

theorem integral_fourCellRegularPolynomial_mul_oddP5Correlation35 :
    (∫ t : ℝ in 0..2,
      yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t) *
        oddP5Correlation35 t) =
      fourCellWideRegularPolynomial35 := by
  unfold yoshidaRegularKernelPolynomial6 fourCellOperatorHalfWidth
    oddP5Correlation35 fourCellWideRegularPolynomial35
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [intervalIntegral.integral_const_mul]
  repeat rw [integral_pow]
  norm_num
  ring

set_option maxHeartbeats 800000 in
theorem integral_fourCellRegularPolynomial_mul_oddP5Correlation55 :
    (∫ t : ℝ in 0..2,
      yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t) *
        oddP5Correlation55 t) =
      fourCellWideRegularPolynomial55 := by
  unfold yoshidaRegularKernelPolynomial6 fourCellOperatorHalfWidth
    oddP5Correlation55 fourCellWideRegularPolynomial55
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [intervalIntegral.integral_const_mul]
  repeat rw [integral_pow]
  norm_num
  ring

private theorem fourCell_log_two_pow_fine_bounds
    (n : ℕ) (hn : n ≠ 0) :
    (69314718055 / 100000000000 : ℝ) ^ n < Real.log 2 ^ n ∧
      Real.log 2 ^ n < (69314718057 / 100000000000 : ℝ) ^ n := by
  have hL := strict_log_two_fine_bounds
  constructor
  · exact pow_lt_pow_left₀ hL.1 (by norm_num) hn
  · exact pow_lt_pow_left₀ hL.2
      (Real.log_pos (by norm_num)).le hn

set_option maxHeartbeats 1000000 in
/-- Tight rational boxes for the six exact polynomial moments.  The
off-diagonal `P₃/P₅` model is certified negative here, before any
absolute envelope error is added. -/
theorem fourCellWideRegularPolynomial_entry_bounds :
    (48636 / 10000000 : ℝ) < fourCellWideRegularPolynomial11 ∧
    fourCellWideRegularPolynomial11 < (48637 / 10000000 : ℝ) ∧
    (-1903 / 10000000 : ℝ) < fourCellWideRegularPolynomial13 ∧
    fourCellWideRegularPolynomial13 < (-1902 / 10000000 : ℝ) ∧
    (1152 / 10000000 : ℝ) < fourCellWideRegularPolynomial33 ∧
    fourCellWideRegularPolynomial33 < (1153 / 10000000 : ℝ) ∧
    (1 / 10000000 : ℝ) < fourCellWideRegularPolynomial15 ∧
    fourCellWideRegularPolynomial15 < (2 / 10000000 : ℝ) ∧
    (-262 / 10000000 : ℝ) < fourCellWideRegularPolynomial35 ∧
    fourCellWideRegularPolynomial35 < (-260 / 10000000 : ℝ) ∧
    (280 / 10000000 : ℝ) < fourCellWideRegularPolynomial55 ∧
    fourCellWideRegularPolynomial55 < (281 / 10000000 : ℝ) := by
  have h1 := strict_log_two_fine_bounds
  have h2 := fourCell_log_two_pow_fine_bounds 2 (by norm_num)
  have h3 := fourCell_log_two_pow_fine_bounds 3 (by norm_num)
  have h4 := fourCell_log_two_pow_fine_bounds 4 (by norm_num)
  have h5 := fourCell_log_two_pow_fine_bounds 5 (by norm_num)
  have h6 := fourCell_log_two_pow_fine_bounds 6 (by norm_num)
  unfold fourCellWideRegularPolynomial11 fourCellWideRegularPolynomial13
    fourCellWideRegularPolynomial33 fourCellWideRegularPolynomial15
    fourCellWideRegularPolynomial35 fourCellWideRegularPolynomial55
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

/-- Wide four-cell regular `P₁/P₁` entry. -/
def fourCellOddOneThreeFiveRegular11 : ℝ :=
  ∫ t : ℝ in 0..2,
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
      oddStructuralCorrelation11 t

/-- Wide four-cell regular `P₁/P₃` entry. -/
def fourCellOddOneThreeFiveRegular13 : ℝ :=
  ∫ t : ℝ in 0..2,
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
      oddStructuralCorrelation13 t

/-- Wide four-cell regular `P₃/P₃` entry. -/
def fourCellOddOneThreeFiveRegular33 : ℝ :=
  ∫ t : ℝ in 0..2,
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
      oddStructuralCorrelation33 t

/-- Wide four-cell regular entry coupling `P₁` to `P₅`. -/
def fourCellOddOneThreeFiveRegular15 : ℝ :=
  ∫ t : ℝ in 0..2,
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
      oddP5Correlation15 t

/-- Wide four-cell regular entry coupling `P₃` to `P₅`. -/
def fourCellOddOneThreeFiveRegular35 : ℝ :=
  ∫ t : ℝ in 0..2,
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
      oddP5Correlation35 t

/-- Wide four-cell regular diagonal of `P₅`. -/
def fourCellOddOneThreeFiveRegular55 : ℝ :=
  ∫ t : ℝ in 0..2,
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
      oddP5Correlation55 t

/-- Each actual full-width regular entry is its exact polynomial moment
plus one controlled global analytic remainder. -/
theorem fourCellOddOneThreeFiveRegular_entries_eq :
    fourCellOddOneThreeFiveRegular11 =
        fourCellWideRegularPolynomial11 +
          fourCellWideRegularEnvelopeError oddStructuralCorrelation11 ∧
    fourCellOddOneThreeFiveRegular13 =
        fourCellWideRegularPolynomial13 +
          fourCellWideRegularEnvelopeError oddStructuralCorrelation13 ∧
    fourCellOddOneThreeFiveRegular33 =
        fourCellWideRegularPolynomial33 +
          fourCellWideRegularEnvelopeError oddStructuralCorrelation33 ∧
    fourCellOddOneThreeFiveRegular15 =
        fourCellWideRegularPolynomial15 +
          fourCellWideRegularEnvelopeError oddP5Correlation15 ∧
    fourCellOddOneThreeFiveRegular35 =
        fourCellWideRegularPolynomial35 +
          fourCellWideRegularEnvelopeError oddP5Correlation35 ∧
    fourCellOddOneThreeFiveRegular55 =
        fourCellWideRegularPolynomial55 +
          fourCellWideRegularEnvelopeError oddP5Correlation55 := by
  constructor
  · unfold fourCellOddOneThreeFiveRegular11
    rw [fourCellRegularIntegral_eq_polynomial_add_error
      oddStructuralCorrelation11
        (by unfold oddStructuralCorrelation11; fun_prop),
      integral_fourCellRegularPolynomial_mul_oddStructuralCorrelation11]
  constructor
  · unfold fourCellOddOneThreeFiveRegular13
    rw [fourCellRegularIntegral_eq_polynomial_add_error
      oddStructuralCorrelation13
        (by unfold oddStructuralCorrelation13; fun_prop),
      integral_fourCellRegularPolynomial_mul_oddStructuralCorrelation13]
  constructor
  · unfold fourCellOddOneThreeFiveRegular33
    rw [fourCellRegularIntegral_eq_polynomial_add_error
      oddStructuralCorrelation33
        (by unfold oddStructuralCorrelation33; fun_prop),
      integral_fourCellRegularPolynomial_mul_oddStructuralCorrelation33]
  constructor
  · unfold fourCellOddOneThreeFiveRegular15
    rw [fourCellRegularIntegral_eq_polynomial_add_error oddP5Correlation15
      (by unfold oddP5Correlation15; fun_prop),
      integral_fourCellRegularPolynomial_mul_oddP5Correlation15]
  constructor
  · unfold fourCellOddOneThreeFiveRegular35
    rw [fourCellRegularIntegral_eq_polynomial_add_error oddP5Correlation35
      (by unfold oddP5Correlation35; fun_prop),
      integral_fourCellRegularPolynomial_mul_oddP5Correlation35]
  · unfold fourCellOddOneThreeFiveRegular55
    rw [fourCellRegularIntegral_eq_polynomial_add_error oddP5Correlation55
      continuous_oddP5Correlation55,
      integral_fourCellRegularPolynomial_mul_oddP5Correlation55]

set_option maxHeartbeats 1000000 in
/-- Tight structural intervals for all six actual wide-regular entries.
In particular `R₁₃` stays strictly negative and the difficult `R₃₅`
entry is only of order `10⁻⁵`; this is the coupled sign information lost by
the earlier independent absolute estimates. -/
theorem fourCellOddOneThreeFiveRegular_entry_bounds :
    (45 / 10000 : ℝ) < fourCellOddOneThreeFiveRegular11 ∧
    fourCellOddOneThreeFiveRegular11 < (523 / 100000 : ℝ) ∧
    (-28 / 100000 : ℝ) < fourCellOddOneThreeFiveRegular13 ∧
    fourCellOddOneThreeFiveRegular13 < (-1 / 10000 : ℝ) ∧
    (-1 / 25000 : ℝ) < fourCellOddOneThreeFiveRegular33 ∧
    fourCellOddOneThreeFiveRegular33 < (27 / 100000 : ℝ) ∧
    (-43 / 1000000 : ℝ) < fourCellOddOneThreeFiveRegular15 ∧
    fourCellOddOneThreeFiveRegular15 < (43 / 1000000 : ℝ) ∧
    (-73 / 1000000 : ℝ) < fourCellOddOneThreeFiveRegular35 ∧
    fourCellOddOneThreeFiveRegular35 < (21 / 1000000 : ℝ) ∧
    (-68 / 1000000 : ℝ) < fourCellOddOneThreeFiveRegular55 ∧
    fourCellOddOneThreeFiveRegular55 < (124 / 1000000 : ℝ) := by
  rcases fourCellWideRegularPolynomial_entry_bounds with
    ⟨hP11lo, hP11hi, hP13lo, hP13hi, hP33lo, hP33hi,
      hP15lo, hP15hi, hP35lo, hP35hi, hP55lo, hP55hi⟩
  rcases fourCellOddOneThreeFiveRegular_entries_eq with
    ⟨h11, h13, h33, h15, h35, h55⟩
  have he11 := abs_le.mp abs_fourCellWideRegularEnvelopeError11_le
  have he13 := abs_lt.mp abs_fourCellWideRegularEnvelopeError13_lt
  have he33 := abs_le.mp abs_fourCellWideRegularEnvelopeError33_le
  have he15 := abs_lt.mp abs_fourCellWideRegularEnvelopeError15_lt
  have he35 := abs_lt.mp abs_fourCellWideRegularEnvelopeError35_lt
  have he55 := abs_le.mp abs_fourCellWideRegularEnvelopeError55_le
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

/-- The mean-zero wide-kernel fluctuation and exact correlation `L¹` mass
give a cutoff-free rational bound for the `P₁`--`P₅` regular entry. -/
theorem abs_fourCellOddOneThreeFiveRegular15_lt :
    |fourCellOddOneThreeFiveRegular15| < (1 / 250 : ℝ) := by
  have hbound := abs_fourCellRegularBilinear_le_one_twentieth_integral_abs
    centeredP1 factorTwoCenteredP5
    (by unfold centeredP1; fun_prop) continuous_factorTwoCenteredP5
    (by intro x; unfold centeredP1; ring) odd_factorTwoCenteredP5
  have hcorr : factorTwoCenteredCorrelationBilinear
      centeredP1 factorTwoCenteredP5 = oddP5Correlation15 := by
    funext t
    exact factorTwoCenteredCorrelationBilinear_p1_p5 t
  rw [hcorr] at hbound
  have hmass := integral_abs_oddP5Correlation15_lt
  dsimp only [fourCellOddOneThreeFiveRegular15]
  nlinarith

/-- The analogous structural `P₃`--`P₅` wide regular bound. -/
theorem abs_fourCellOddOneThreeFiveRegular35_lt :
    |fourCellOddOneThreeFiveRegular35| < (11 / 2500 : ℝ) := by
  have hbound := abs_fourCellRegularBilinear_le_one_twentieth_integral_abs
    centeredP3 factorTwoCenteredP5
    (by unfold centeredP3; fun_prop) continuous_factorTwoCenteredP5
    (by intro x; unfold centeredP3; ring) odd_factorTwoCenteredP5
  have hcorr : factorTwoCenteredCorrelationBilinear
      centeredP3 factorTwoCenteredP5 = oddP5Correlation35 := by
    funext t
    exact factorTwoCenteredCorrelationBilinear_p3_p5 t
  rw [hcorr] at hbound
  have hmass := integral_abs_oddP5Correlation35_lt
  dsimp only [fourCellOddOneThreeFiveRegular35]
  nlinarith

/-- The `P₅` wide regular diagonal costs at most `1/20` of its exact
centered mass. -/
theorem abs_fourCellOddOneThreeFiveRegular55_le :
    |fourCellOddOneThreeFiveRegular55| ≤ (1 / 110 : ℝ) := by
  have hbound := abs_fourCellRegularCorrelation_le_one_twentieth_centeredMass
    factorTwoCenteredP5 continuous_factorTwoCenteredP5
      odd_factorTwoCenteredP5
  rw [show centeredEndpointCorrelation factorTwoCenteredP5 =
      oddP5Correlation55 by
    funext t
    exact centeredEndpointCorrelation_p5 t,
    integral_factorTwoCenteredP5_sq] at hbound
  dsimp only [fourCellOddOneThreeFiveRegular55]
  norm_num at hbound ⊢
  exact hbound

/-- Complete wide regular quadratic on the retained P135 pivot. -/
def fourCellOddOneThreeFiveRegularQuadratic (c d e : ℝ) : ℝ :=
  ∫ t : ℝ in 0..2,
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
      centeredEndpointCorrelation
        (fourCellOddOneThreeFiveLowProfile c d e) t

/-- Exact six-entry expansion of the retained wide regular quadratic. -/
theorem fourCellOddOneThreeFiveRegularQuadratic_expansion
    (c d e : ℝ) :
    fourCellOddOneThreeFiveRegularQuadratic c d e =
      fourCellOddLowRegularQuadratic c d +
        2 * c * e * fourCellOddOneThreeFiveRegular15 +
        2 * d * e * fourCellOddOneThreeFiveRegular35 +
        e ^ 2 * fourCellOddOneThreeFiveRegular55 := by
  let C13 : ℝ → ℝ := fun t ↦
    c ^ 2 * oddStructuralCorrelation11 t +
      2 * c * d * oddStructuralCorrelation13 t +
        d ^ 2 * oddStructuralCorrelation33 t
  have hC13 : Continuous C13 := by
    dsimp only [C13]
    unfold oddStructuralCorrelation11 oddStructuralCorrelation13
      oddStructuralCorrelation33
    fun_prop
  have hlow := intervalIntegrable_fourCellRegularKernel_mul_continuous
    C13 hC13
  have h15 := intervalIntegrable_fourCellRegularKernel_mul_continuous
    oddP5Correlation15 (by unfold oddP5Correlation15; fun_prop)
  have h35 := intervalIntegrable_fourCellRegularKernel_mul_continuous
    oddP5Correlation35 (by unfold oddP5Correlation35; fun_prop)
  have h55 := intervalIntegrable_fourCellRegularKernel_mul_continuous
    oddP5Correlation55 continuous_oddP5Correlation55
  unfold fourCellOddOneThreeFiveRegularQuadratic
  simp_rw [centeredEndpointCorrelation_oneThreeFiveLowProfile]
  rw [show (fun t : ℝ ↦
      yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
        (c ^ 2 * oddStructuralCorrelation11 t +
          2 * c * d * oddStructuralCorrelation13 t +
          d ^ 2 * oddStructuralCorrelation33 t +
          2 * c * e * oddP5Correlation15 t +
          2 * d * e * oddP5Correlation35 t +
          e ^ 2 * oddP5Correlation55 t)) = fun t ↦
      yoshidaRegularKernel (fourCellOperatorHalfWidth * t) * C13 t +
        (2 * c * e) *
          (yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
            oddP5Correlation15 t) +
        (2 * d * e) *
          (yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
            oddP5Correlation35 t) +
        e ^ 2 *
          (yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
            oddP5Correlation55 t) by
    funext t
    dsimp only [C13]
    ring,
    intervalIntegral.integral_add
      ((hlow.add (h15.const_mul (2 * c * e))).add
        (h35.const_mul (2 * d * e))) (h55.const_mul (e ^ 2)),
    intervalIntegral.integral_add
      (hlow.add (h15.const_mul (2 * c * e)))
      (h35.const_mul (2 * d * e)),
    intervalIntegral.integral_add hlow (h15.const_mul (2 * c * e))]
  repeat rw [intervalIntegral.integral_const_mul]
  unfold fourCellOddLowRegularQuadratic
    fourCellOddOneThreeFiveRegular15 fourCellOddOneThreeFiveRegular35
    fourCellOddOneThreeFiveRegular55
  rfl

/-- Positive-half potential cross of `P₁` and `P₅`. -/
theorem integral_zero_one_endpointPotential_mul_centeredP1_mul_P5 :
    (∫ x : ℝ in 0..1,
      yoshidaEndpointPotential x * centeredP1 x *
        factorTwoCenteredP5 x) = (1 / 28 : ℝ) := by
  let f : ℝ → ℝ := fun x ↦
    yoshidaEndpointPotential x * centeredP1 x * factorTwoCenteredP5 x
  have hf : IntervalIntegrable f volume (-1) 1 := by
    dsimp only [f]
    simpa only [mul_assoc] using
      intervalIntegrable_endpointPotential_mul
        (fun x : ℝ ↦ centeredP1 x * factorTwoCenteredP5 x)
        (by unfold centeredP1 factorTwoCenteredP5; fun_prop)
  have hfeven : Function.Even f := by
    intro x
    dsimp only [f]
    unfold yoshidaEndpointPotential centeredP1 factorTwoCenteredP5
    ring_nf
  have hfold := integral_neg_one_one_eq_two_mul_zero_one_of_even
    f hf hfeven
  have hfull := integral_endpointPotential_mul_centeredP1_mul_P5
  dsimp only [f] at hfold
  rw [hfull] at hfold
  linarith

/-- Positive-half potential cross of `P₃` and `P₅`. -/
theorem integral_zero_one_endpointPotential_mul_centeredP3_mul_P5 :
    (∫ x : ℝ in 0..1,
      yoshidaEndpointPotential x * centeredP3 x *
        factorTwoCenteredP5 x) = (1 / 18 : ℝ) := by
  let f : ℝ → ℝ := fun x ↦
    yoshidaEndpointPotential x * centeredP3 x * factorTwoCenteredP5 x
  have hf : IntervalIntegrable f volume (-1) 1 := by
    dsimp only [f]
    simpa only [mul_assoc] using
      intervalIntegrable_endpointPotential_mul
        (fun x : ℝ ↦ centeredP3 x * factorTwoCenteredP5 x)
        (by unfold centeredP3 factorTwoCenteredP5; fun_prop)
  have hfeven : Function.Even f := by
    intro x
    dsimp only [f]
    unfold yoshidaEndpointPotential centeredP3 factorTwoCenteredP5
    ring_nf
  have hfold := integral_neg_one_one_eq_two_mul_zero_one_of_even
    f hf hfeven
  have hfull := integral_endpointPotential_mul_centeredP3_mul_P5
  dsimp only [f] at hfold
  rw [hfull] at hfold
  linarith

/-- Positive-half endpoint-potential diagonal of `P₅`. -/
theorem integral_zero_one_endpointPotential_mul_factorTwoCenteredP5_sq :
    (∫ x : ℝ in 0..1,
      yoshidaEndpointPotential x * factorTwoCenteredP5 x ^ 2) =
      19157 / 152460 - (1 / 11 : ℝ) * Real.log 2 := by
  have hfold := endpointPotential_eq_two_mul_positiveHalf
    factorTwoCenteredP5 continuous_factorTwoCenteredP5
      (Or.inr odd_factorTwoCenteredP5)
  rw [integral_endpointPotential_mul_factorTwoCenteredP5_sq] at hfold
  linarith

/-- Exact endpoint-potential quadratic on the retained odd three-mode
pivot.  All logarithmic diagonal terms and both rational cross moments are
kept in closed form. -/
theorem integral_zero_one_endpointPotential_oneThreeFiveLowProfile
    (c d e : ℝ) :
    (∫ x : ℝ in 0..1,
      yoshidaEndpointPotential x *
        fourCellOddOneThreeFiveLowProfile c d e x ^ 2) =
      (4 / 9 - (1 / 3 : ℝ) * Real.log 2) * c ^ 2 +
        (1 / 5 : ℝ) * c * d +
        (289 / 1470 - (1 / 7 : ℝ) * Real.log 2) * d ^ 2 +
        (1 / 14 : ℝ) * c * e + (1 / 9 : ℝ) * d * e +
        (19157 / 152460 - (1 / 11 : ℝ) * Real.log 2) * e ^ 2 := by
  let q : ℝ → ℝ := factorTwoOddStructuralLowProfile c d
  let v : ℝ → ℝ := fun x ↦ e * factorTwoCenteredP5 x
  have hq : Continuous q := by
    simpa only [q] using continuous_factorTwoOddStructuralLowProfile c d
  have hv : Continuous v := by
    dsimp only [v]
    exact continuous_const.mul continuous_factorTwoCenteredP5
  have hadd := integral_zero_one_endpointPotential_add_sq q v hq hv
  have h15Full := intervalIntegrable_endpointPotential_mul
    (fun x : ℝ ↦ centeredP1 x * factorTwoCenteredP5 x)
    (by unfold centeredP1 factorTwoCenteredP5; fun_prop)
  have h35Full := intervalIntegrable_endpointPotential_mul
    (fun x : ℝ ↦ centeredP3 x * factorTwoCenteredP5 x)
    (by unfold centeredP3 factorTwoCenteredP5; fun_prop)
  have hsub : uIcc (0 : ℝ) 1 ⊆ uIcc (-1 : ℝ) 1 := by
    intro x hx
    norm_num at hx ⊢
    constructor <;> linarith
  have h15 := h15Full.mono_set hsub
  have h35 := h35Full.mono_set hsub
  have h15' : IntervalIntegrable
    (fun x : ℝ ↦ yoshidaEndpointPotential x * centeredP1 x *
      factorTwoCenteredP5 x) volume 0 1 := by
    apply h15.congr
    intro x _hx
    ring
  have h35' : IntervalIntegrable
    (fun x : ℝ ↦ yoshidaEndpointPotential x * centeredP3 x *
      factorTwoCenteredP5 x) volume 0 1 := by
    apply h35.congr
    intro x _hx
    ring
  have hcross :
      (∫ x : ℝ in 0..1,
        yoshidaEndpointPotential x * q x * v x) =
        e * (c / 28 + d / 18) := by
    rw [show (fun x : ℝ ↦ yoshidaEndpointPotential x * q x * v x) =
        fun x ↦ (e * c) *
            (yoshidaEndpointPotential x * centeredP1 x *
              factorTwoCenteredP5 x) +
          (e * d) *
            (yoshidaEndpointPotential x * centeredP3 x *
              factorTwoCenteredP5 x) by
      funext x
      dsimp only [q, v]
      unfold factorTwoOddStructuralLowProfile
      ring,
      intervalIntegral.integral_add (h15'.const_mul (e * c))
        (h35'.const_mul (e * d)),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      integral_zero_one_endpointPotential_mul_centeredP1_mul_P5,
      integral_zero_one_endpointPotential_mul_centeredP3_mul_P5]
    ring
  have hvSq :
      (∫ x : ℝ in 0..1,
        yoshidaEndpointPotential x * v x ^ 2) =
        e ^ 2 *
          (19157 / 152460 - (1 / 11 : ℝ) * Real.log 2) := by
    rw [show (fun x : ℝ ↦ yoshidaEndpointPotential x * v x ^ 2) =
        fun x ↦ e ^ 2 *
          (yoshidaEndpointPotential x * factorTwoCenteredP5 x ^ 2) by
      funext x
      dsimp only [v]
      ring,
      intervalIntegral.integral_const_mul,
      integral_zero_one_endpointPotential_mul_factorTwoCenteredP5_sq]
  change (∫ x : ℝ in 0..1,
      yoshidaEndpointPotential x * (q x + v x) ^ 2) = _
  rw [hadd, hcross, hvSq]
  dsimp only [q]
  rw [integral_zero_one_endpointPotential_oddStructuralLow]
  ring

theorem contDiff_fourCellOddOneThreeFiveResidual
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) :
    ContDiff ℝ 1 (fourCellOddOneThreeFiveResidual w) := by
  unfold fourCellOddOneThreeFiveResidual centeredOddOneThreeResidual
    centeredP1 centeredP3 factorTwoCenteredP5
  fun_prop

theorem odd_fourCellOddOneThreeFiveResidual
    (w : ℝ → ℝ) (hodd : Function.Odd w) :
    Function.Odd (fourCellOddOneThreeFiveResidual w) := by
  intro x
  unfold fourCellOddOneThreeFiveResidual centeredOddOneThreeResidual
    centeredP1 centeredP3 factorTwoCenteredP5
  rw [hodd]
  ring

private theorem intervalIntegral_sub_const_mul_mul
    (u v p : ℝ → ℝ) (a l r : ℝ)
    (hu : Continuous u) (hv : Continuous v) (hp : Continuous p) :
    (∫ x : ℝ in l..r, (u x - a * v x) * p x) =
      (∫ x : ℝ in l..r, u x * p x) -
        a * ∫ x : ℝ in l..r, v x * p x := by
  have hup : IntervalIntegrable (fun x : ℝ ↦ u x * p x)
      volume l r := (hu.mul hp).intervalIntegrable l r
  have havp : IntervalIntegrable (fun x : ℝ ↦ a * (v x * p x))
      volume l r := (continuous_const.mul (hv.mul hp)).intervalIntegrable l r
  rw [show (fun x : ℝ ↦ (u x - a * v x) * p x) =
      fun x ↦ u x * p x - a * (v x * p x) by
    funext x
    ring,
    intervalIntegral.integral_sub hup havp,
    intervalIntegral.integral_const_mul]

theorem centeredOddP1Coefficient_oneThreeFiveResidual_eq_zero
    (w : ℝ → ℝ) (hw : Continuous w) :
    centeredOddP1Coefficient (fourCellOddOneThreeFiveResidual w) = 0 := by
  have hsplit := intervalIntegral_sub_const_mul_mul
    (centeredOddOneThreeResidual w) factorTwoCenteredP5 centeredP1
    (fourCellOddP5TailCoefficient w) (-1) 1
    (continuous_centeredOddOneThreeResidual w hw)
    continuous_factorTwoCenteredP5 (by unfold centeredP1; fun_prop)
  have htail := centeredOddP1Coefficient_oneThreeResidual_eq_zero w hw
  have hp5 := factorTwoCenteredP5_intrinsic_coefficients_zero.1
  unfold centeredOddP1Coefficient fourCellOddOneThreeFiveResidual
  unfold centeredOddP1Coefficient at htail hp5
  rw [hsplit]
  have htail' : (∫ x : ℝ in -1..1,
      centeredOddOneThreeResidual w x * centeredP1 x) = 0 := by
    nlinarith
  have hp5' : (∫ x : ℝ in -1..1,
      factorTwoCenteredP5 x * centeredP1 x) = 0 := by
    nlinarith
  rw [htail', hp5']
  ring

theorem centeredOddP3Coefficient_oneThreeFiveResidual_eq_zero
    (w : ℝ → ℝ) (hw : Continuous w) :
    centeredOddP3Coefficient (fourCellOddOneThreeFiveResidual w) = 0 := by
  have hsplit := intervalIntegral_sub_const_mul_mul
    (centeredOddOneThreeResidual w) factorTwoCenteredP5 centeredP3
    (fourCellOddP5TailCoefficient w) (-1) 1
    (continuous_centeredOddOneThreeResidual w hw)
    continuous_factorTwoCenteredP5 (by unfold centeredP3; fun_prop)
  have htail := centeredOddP3Coefficient_oneThreeResidual_eq_zero w hw
  have hp5 := factorTwoCenteredP5_intrinsic_coefficients_zero.2
  unfold centeredOddP3Coefficient fourCellOddOneThreeFiveResidual
  unfold centeredOddP3Coefficient at htail hp5
  rw [hsplit]
  have htail' : (∫ x : ℝ in -1..1,
      centeredOddOneThreeResidual w x * centeredP3 x) = 0 := by
    nlinarith
  have hp5' : (∫ x : ℝ in -1..1,
      factorTwoCenteredP5 x * centeredP3 x) = 0 := by
    nlinarith
  rw [htail', hp5']
  ring

theorem centeredOddP5Coefficient_oneThreeFiveResidual_eq_zero
    (w : ℝ → ℝ) (hw : Continuous w) :
    centeredOddP5Coefficient (fourCellOddOneThreeFiveResidual w) = 0 := by
  have hsplit := intervalIntegral_sub_const_mul_mul
    (centeredOddOneThreeResidual w) factorTwoCenteredP5
    factorTwoCenteredP5 (fourCellOddP5TailCoefficient w) (-1) 1
    (continuous_centeredOddOneThreeResidual w hw)
    continuous_factorTwoCenteredP5 continuous_factorTwoCenteredP5
  change (11 / 2 : ℝ) * (∫ x : ℝ in -1..1,
    (centeredOddOneThreeResidual w x -
      fourCellOddP5TailCoefficient w * factorTwoCenteredP5 x) *
        factorTwoCenteredP5 x) = 0
  have hnorm : (∫ x : ℝ in -1..1,
      factorTwoCenteredP5 x * factorTwoCenteredP5 x) = 2 / 11 := by
    simpa only [pow_two] using integral_factorTwoCenteredP5_sq
  rw [hsplit, hnorm]
  unfold fourCellOddP5TailCoefficient centeredOddP5Coefficient
  ring

/-- Exact positive-half `L²` orthogonality of the `P₁/P₃/P₅` pivot and its
infinite tail.  In particular, the large scalar-mass row contributes no
mixed Schur term. -/
theorem integral_zero_one_oneThreeFiveLowProfile_mul_tail_eq_zero
    (r : ℝ → ℝ) (hr : Continuous r) (hodd : Function.Odd r)
    (hone : centeredOddP1Coefficient r = 0)
    (hthree : centeredOddP3Coefficient r = 0)
    (hfive : centeredOddP5Coefficient r = 0)
    (c d e : ℝ) :
    (∫ x : ℝ in 0..1,
      fourCellOddOneThreeFiveLowProfile c d e x * r x) = 0 := by
  have honeInt : (∫ x : ℝ in -1..1, r x * centeredP1 x) = 0 := by
    rw [integral_mul_centeredP1_eq, hone]
    ring
  have hthreeInt : (∫ x : ℝ in -1..1, r x * centeredP3 x) = 0 := by
    rw [integral_mul_centeredP3_eq, hthree]
    ring
  have hfiveInt :
      (∫ x : ℝ in -1..1, r x * factorTwoCenteredP5 x) = 0 := by
    unfold centeredOddP5Coefficient at hfive
    nlinarith
  have hrOne : IntervalIntegrable (fun x : ℝ ↦ r x * centeredP1 x)
      volume (-1) 1 :=
    (hr.mul (by unfold centeredP1; fun_prop)).intervalIntegrable _ _
  have hrThree : IntervalIntegrable (fun x : ℝ ↦ r x * centeredP3 x)
      volume (-1) 1 :=
    (hr.mul (by unfold centeredP3; fun_prop)).intervalIntegrable _ _
  have hrFive : IntervalIntegrable
      (fun x : ℝ ↦ r x * factorTwoCenteredP5 x) volume (-1) 1 :=
    (hr.mul continuous_factorTwoCenteredP5).intervalIntegrable _ _
  let p : ℝ → ℝ := fourCellOddOneThreeFiveLowProfile c d e
  have hp : Continuous p := by
    simpa only [p] using
      (contDiff_fourCellOddOneThreeFiveLowProfile c d e).continuous
  have hpodd : Function.Odd p := by
    simpa only [p] using odd_fourCellOddOneThreeFiveLowProfile c d e
  have hfull : (∫ x : ℝ in -1..1, p x * r x) = 0 := by
    rw [show (fun x : ℝ ↦ p x * r x) =
        fun x ↦ c * (r x * centeredP1 x) +
          d * (r x * centeredP3 x) +
            e * (r x * factorTwoCenteredP5 x) by
      funext x
      dsimp only [p]
      unfold fourCellOddOneThreeFiveLowProfile
        factorTwoOddStructuralLowProfile
      ring,
      intervalIntegral.integral_add
        ((hrOne.const_mul c).add (hrThree.const_mul d))
        (hrFive.const_mul e),
      intervalIntegral.integral_add
        (hrOne.const_mul c) (hrThree.const_mul d)]
    repeat rw [intervalIntegral.integral_const_mul]
    rw [honeInt, hthreeInt, hfiveInt]
    ring
  have hproductEven : Function.Even (fun x : ℝ ↦ p x * r x) := by
    intro x
    change p (-x) * r (-x) = p x * r x
    rw [hpodd, hodd]
    ring
  have hproductInt : IntervalIntegrable (fun x : ℝ ↦ p x * r x)
      volume (-1) 1 := (hp.mul hr).intervalIntegrable _ _
  have hfold :
      (∫ x : ℝ in -1..1, p x * r x) =
        2 * ∫ x : ℝ in 0..1, p x * r x :=
    integral_neg_one_one_eq_two_mul_zero_one_of_even
      (fun x : ℝ ↦ p x * r x) hproductInt hproductEven
  linarith

/-- Exact `L²` energy of the three retained odd Legendre modes. -/
theorem factorTwoIntrinsicEnergy_oneThreeFiveLowProfile
    (c d e : ℝ) :
    factorTwoIntrinsicEnergy (fourCellOddOneThreeFiveLowProfile c d e) =
      (2 / 3 : ℝ) * c ^ 2 + (2 / 7 : ℝ) * d ^ 2 +
        (2 / 11 : ℝ) * e ^ 2 := by
  let q : ℝ → ℝ := factorTwoOddStructuralLowProfile c d
  have hq : Continuous q := by
    dsimp only [q]
    exact continuous_factorTwoOddStructuralLowProfile c d
  have hqSq : IntervalIntegrable (fun x : ℝ ↦ q x ^ 2)
      volume (-1) 1 := (hq.pow 2).intervalIntegrable _ _
  have hcrossInt : IntervalIntegrable
      (fun x : ℝ ↦ q x * factorTwoCenteredP5 x) volume (-1) 1 :=
    (hq.mul continuous_factorTwoCenteredP5).intervalIntegrable _ _
  have hp5Sq : IntervalIntegrable
      (fun x : ℝ ↦ factorTwoCenteredP5 x ^ 2) volume (-1) 1 :=
    (continuous_factorTwoCenteredP5.pow 2).intervalIntegrable _ _
  have hcross :
      (∫ x : ℝ in -1..1, q x * factorTwoCenteredP5 x) = 0 := by
    have h15 : IntervalIntegrable
        (fun x : ℝ ↦ factorTwoCenteredP5 x * centeredP1 x)
        volume (-1) 1 :=
      (continuous_factorTwoCenteredP5.mul
        (by unfold centeredP1; fun_prop)).intervalIntegrable _ _
    have h35 : IntervalIntegrable
        (fun x : ℝ ↦ factorTwoCenteredP5 x * centeredP3 x)
        volume (-1) 1 :=
      (continuous_factorTwoCenteredP5.mul
        (by unfold centeredP3; fun_prop)).intervalIntegrable _ _
    rw [show (fun x : ℝ ↦ q x * factorTwoCenteredP5 x) =
        fun x ↦ c * (factorTwoCenteredP5 x * centeredP1 x) +
          d * (factorTwoCenteredP5 x * centeredP3 x) by
      funext x
      dsimp only [q]
      unfold factorTwoOddStructuralLowProfile
      ring,
      intervalIntegral.integral_add
        (h15.const_mul c) (h35.const_mul d),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      integral_factorTwoCenteredP5_mul_centeredP1,
      integral_factorTwoCenteredP5_mul_centeredP3]
    ring
  unfold factorTwoIntrinsicEnergy fourCellOddOneThreeFiveLowProfile
  rw [show (fun x : ℝ ↦
      (factorTwoOddStructuralLowProfile c d x +
        e * factorTwoCenteredP5 x) ^ 2) =
      fun x ↦ q x ^ 2 +
        2 * e * (q x * factorTwoCenteredP5 x) +
          e ^ 2 * factorTwoCenteredP5 x ^ 2 by
    funext x
    dsimp only [q]
    ring,
    intervalIntegral.integral_add
      (hqSq.add (hcrossInt.const_mul (2 * e)))
      (hp5Sq.const_mul (e ^ 2)),
    intervalIntegral.integral_add
      hqSq (hcrossInt.const_mul (2 * e)),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  dsimp only [q]
  rw [integral_oddStructuralLow_sq, hcross,
    integral_factorTwoCenteredP5_sq]
  ring

/-- Exact positive-half mass of the retained odd three-mode pivot. -/
theorem integral_zero_one_oneThreeFiveLowProfile_sq
    (c d e : ℝ) :
    (∫ x : ℝ in 0..1,
      fourCellOddOneThreeFiveLowProfile c d e x ^ 2) =
      (1 / 3 : ℝ) * c ^ 2 + (1 / 7 : ℝ) * d ^ 2 +
        (1 / 11 : ℝ) * e ^ 2 := by
  let p : ℝ → ℝ := fourCellOddOneThreeFiveLowProfile c d e
  have hfull := factorTwoIntrinsicEnergy_oneThreeFiveLowProfile c d e
  have hhalf := integral_sq_eq_two_mul_positiveHalf
    p (by dsimp only [p]; exact
      (contDiff_fourCellOddOneThreeFiveLowProfile c d e).continuous)
    (Or.inr (by simpa only [p] using
      odd_fourCellOddOneThreeFiveLowProfile c d e))
  unfold factorTwoIntrinsicEnergy at hfull
  dsimp only [p] at hhalf
  linarith

/-- Exact centered raw-log energy of the retained `P₁/P₃/P₅` pivot. -/
theorem centeredRawLogEnergy_oneThreeFiveLowProfile
    (c d e : ℝ) :
    centeredRawLogEnergy (fourCellOddOneThreeFiveLowProfile c d e) =
      (8 / 3 : ℝ) * c ^ 2 + (44 / 21 : ℝ) * d ^ 2 +
        (274 / 165 : ℝ) * e ^ 2 := by
  let p : ℝ → ℝ := fourCellOddOneThreeFiveLowProfile c d e
  have h11 : IntervalIntegrable (fun x : ℝ ↦ centeredP1 x ^ 2)
      volume (-1) 1 := (by unfold centeredP1; fun_prop : Continuous fun x : ℝ ↦
        centeredP1 x ^ 2).intervalIntegrable _ _
  have h13 : IntervalIntegrable
      (fun x : ℝ ↦ centeredP1 x * centeredP3 x) volume (-1) 1 :=
    (by unfold centeredP1 centeredP3; fun_prop : Continuous fun x : ℝ ↦
      centeredP1 x * centeredP3 x).intervalIntegrable _ _
  have h33 : IntervalIntegrable (fun x : ℝ ↦ centeredP3 x ^ 2)
      volume (-1) 1 := (by unfold centeredP3; fun_prop : Continuous fun x : ℝ ↦
        centeredP3 x ^ 2).intervalIntegrable _ _
  have h51 : IntervalIntegrable
      (fun x : ℝ ↦ factorTwoCenteredP5 x * centeredP1 x)
      volume (-1) 1 := (continuous_factorTwoCenteredP5.mul
        (by unfold centeredP1; fun_prop)).intervalIntegrable _ _
  have h53 : IntervalIntegrable
      (fun x : ℝ ↦ factorTwoCenteredP5 x * centeredP3 x)
      volume (-1) 1 := (continuous_factorTwoCenteredP5.mul
        (by unfold centeredP3; fun_prop)).intervalIntegrable _ _
  have h55 : IntervalIntegrable
      (fun x : ℝ ↦ factorTwoCenteredP5 x ^ 2) volume (-1) 1 :=
    (continuous_factorTwoCenteredP5.pow 2).intervalIntegrable _ _
  have hone : (∫ x : ℝ in -1..1, p x * centeredP1 x) =
      (2 / 3 : ℝ) * c := by
    rw [show (fun x : ℝ ↦ p x * centeredP1 x) = fun x ↦
        c * centeredP1 x ^ 2 +
          d * (centeredP1 x * centeredP3 x) +
            e * (factorTwoCenteredP5 x * centeredP1 x) by
      funext x
      dsimp only [p]
      unfold fourCellOddOneThreeFiveLowProfile
        factorTwoOddStructuralLowProfile
      ring,
      intervalIntegral.integral_add
        ((h11.const_mul c).add (h13.const_mul d)) (h51.const_mul e),
      intervalIntegral.integral_add (h11.const_mul c) (h13.const_mul d)]
    repeat rw [intervalIntegral.integral_const_mul]
    rw [integral_centeredP1_sq, integral_centeredP1_mul_p3,
      integral_factorTwoCenteredP5_mul_centeredP1]
    ring
  have hthree : (∫ x : ℝ in -1..1, p x * centeredP3 x) =
      (2 / 7 : ℝ) * d := by
    rw [show (fun x : ℝ ↦ p x * centeredP3 x) = fun x ↦
        c * (centeredP1 x * centeredP3 x) +
          d * centeredP3 x ^ 2 +
            e * (factorTwoCenteredP5 x * centeredP3 x) by
      funext x
      dsimp only [p]
      unfold fourCellOddOneThreeFiveLowProfile
        factorTwoOddStructuralLowProfile
      ring,
      intervalIntegral.integral_add
        ((h13.const_mul c).add (h33.const_mul d)) (h53.const_mul e),
      intervalIntegral.integral_add (h13.const_mul c) (h33.const_mul d)]
    repeat rw [intervalIntegral.integral_const_mul]
    rw [integral_centeredP1_mul_p3, integral_centeredP3_sq,
      integral_factorTwoCenteredP5_mul_centeredP3]
    ring
  have hfive : (∫ x : ℝ in -1..1, p x * factorTwoCenteredP5 x) =
      (2 / 11 : ℝ) * e := by
    rw [show (fun x : ℝ ↦ p x * factorTwoCenteredP5 x) = fun x ↦
        c * (factorTwoCenteredP5 x * centeredP1 x) +
          d * (factorTwoCenteredP5 x * centeredP3 x) +
            e * factorTwoCenteredP5 x ^ 2 by
      funext x
      dsimp only [p]
      unfold fourCellOddOneThreeFiveLowProfile
        factorTwoOddStructuralLowProfile
      ring,
      intervalIntegral.integral_add
        ((h51.const_mul c).add (h53.const_mul d)) (h55.const_mul e),
      intervalIntegral.integral_add (h51.const_mul c) (h53.const_mul d)]
    repeat rw [intervalIntegral.integral_const_mul]
    rw [integral_factorTwoCenteredP5_mul_centeredP1,
      integral_factorTwoCenteredP5_mul_centeredP3,
      integral_factorTwoCenteredP5_sq]
    ring
  have hraw := centeredRawLogBilinear_oneThreeFiveLowProfile_eq_moments
    p (by dsimp only [p]; exact
      (contDiff_fourCellOddOneThreeFiveLowProfile c d e).continuous) c d e
  have hself : centeredRawLogBilinear p p = centeredRawLogEnergy p := by
    unfold centeredRawLogBilinear centeredRawLogEnergy
    apply intervalIntegral.integral_congr
    intro x _hx
    apply intervalIntegral.integral_congr
    intro y _hy
    ring
  rw [hself, hone, hthree, hfive] at hraw
  simpa only [p] using (by nlinarith [hraw] :
    centeredRawLogEnergy p =
      (8 / 3 : ℝ) * c ^ 2 + (44 / 21 : ℝ) * d ^ 2 +
        (274 / 165 : ℝ) * e ^ 2)

/-- Exact adverse raw quadratic created by the affine endpoint strip on the
retained `P₁/P₃/P₅` pivot. -/
theorem fourCellOddEndpointStripOddRawEnergy_oneThreeFiveLowProfile
    (c d e : ℝ) :
    fourCellOddEndpointStripOddRawEnergy
        (fourCellOddOneThreeFiveLowProfile c d e) =
      (8 / 375 : ℝ) * c ^ 2 +
        2 * (224 / 3125 : ℝ) * c * d +
        2 * (736 / 15625 : ℝ) * c * e +
        (79036 / 328125 : ℝ) * d ^ 2 +
        2 * (496 / 3125 : ℝ) * d * e +
        (898920274 / 8056640625 : ℝ) * e ^ 2 := by
  unfold fourCellOddEndpointStripOddRawEnergy
  rw [fourCellOddEndpointStripOdd_oneThreeFiveLowProfile_eq_lowProfile,
    centeredRawLogEnergy_oneThreeFiveLowProfile]
  ring

/-- Exact `L²` mass matrix of the reflection-odd affine strip channel on
the retained `P₁/P₃/P₅` pivot. -/
theorem fourCellOddEndpointStripOddMass_oneThreeFiveLowProfile
    (c d e : ℝ) :
    fourCellOddEndpointStripOddMass
        (fourCellOddOneThreeFiveLowProfile c d e) =
      (2 / 375 : ℝ) * c ^ 2 +
        2 * (56 / 3125 : ℝ) * c * d +
        2 * (184 / 15625 : ℝ) * c * e +
        (6586 / 109375 : ℝ) * d ^ 2 +
        2 * (3096 / 78125 : ℝ) * d * e +
        (14520002 / 537109375 : ℝ) * e ^ 2 := by
  unfold fourCellOddEndpointStripOddMass
  rw [fourCellOddEndpointStripOdd_oneThreeFiveLowProfile_eq_lowProfile]
  change (1 / 5 : ℝ) * factorTwoIntrinsicEnergy
      (fourCellOddOneThreeFiveLowProfile
        (c / 5 + 84 * d / 125 + 276 * e / 625)
        (d / 125 + 84 * e / 625) (e / 3125)) = _
  rw [factorTwoIntrinsicEnergy_oneThreeFiveLowProfile]
  ring

/-- Exact `L²` mass matrix of the reflection-even affine strip channel on
the retained `P₁/P₃/P₅` pivot. -/
theorem fourCellOddEndpointStripEvenMass_oneThreeFiveLowProfile
    (c d e : ℝ) :
    fourCellOddEndpointStripEvenMass
        (fourCellOddOneThreeFiveLowProfile c d e) =
      (32 / 125 : ℝ) * c ^ 2 +
        2 * (32 / 625 : ℝ) * c * d -
        2 * (3296 / 78125 : ℝ) * c * e +
        (192 / 15625 : ℝ) * d ^ 2 -
        2 * (576 / 390625 : ℝ) * d * e +
        (1495776 / 48828125 : ℝ) * e ^ 2 := by
  unfold fourCellOddEndpointStripEvenMass
  simp_rw [fourCellOddEndpointStripEven_oneThreeFiveLowProfile]
  let A : ℝ := 4 * c / 5 + 2 * d / 25 - 2497 * e / 6250
  let B : ℝ := 6 * d / 25 + 483 * e / 625
  let C : ℝ := 63 * e / 1250
  change (1 / 5 : ℝ) * (∫ z : ℝ in -1..1,
    (A + B * z ^ 2 + C * z ^ 4) ^ 2) = _
  rw [show (fun z : ℝ ↦ (A + B * z ^ 2 + C * z ^ 4) ^ 2) =
      fun z ↦
        A ^ 2 * z ^ 0 + 0 * z ^ 1 + (2 * A * B) * z ^ 2 +
          0 * z ^ 3 + (B ^ 2 + 2 * A * C) * z ^ 4 +
            0 * z ^ 5 + (2 * B * C) * z ^ 6 +
              0 * z ^ 7 + C ^ 2 * z ^ 8 + 0 * z ^ 9 by
    funext z
    ring,
    integral_polynomial_nine]
  dsimp only [A, B, C]
  norm_num
  ring

/-- Exact core reserve on the retained three-mode pivot.  The only
transcendental coefficient is the common endpoint-potential `log 2`
diagonal; all cross entries are rational. -/
theorem fourCellOddHalfCoreReserve_oneThreeFiveLowProfile
    (c d e : ℝ) :
    fourCellOddHalfCoreReserve
        (fourCellOddOneThreeFiveLowProfile c d e) =
      (28 / 45 - (2 / 3 : ℝ) * Real.log 2) * c ^ 2 +
        (2 / 5 : ℝ) * c * d + (1 / 7 : ℝ) * c * e +
        (76 / 147 - (2 / 7 : ℝ) * Real.log 2) * d ^ 2 +
        (2 / 9 : ℝ) * d * e +
        (3140 / 7623 - (2 / 11 : ℝ) * Real.log 2) * e ^ 2 := by
  let p : ℝ → ℝ := fourCellOddOneThreeFiveLowProfile c d e
  have hp : ContDiff ℝ 1 p := by
    simpa only [p] using contDiff_fourCellOddOneThreeFiveLowProfile c d e
  have hpLocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) p :=
    hp.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1)
  have hpOdd : Function.Odd p := by
    simpa only [p] using odd_fourCellOddOneThreeFiveLowProfile c d e
  have hraw := centeredRawLogEnergy_div_four_eq_positiveHalf_odd
    p hpLocal hpOdd
  have hmass := integral_sq_eq_two_mul_positiveHalf
    p hp.continuous (Or.inr hpOdd)
  unfold fourCellOddHalfCoreReserve
  rw [← hraw]
  have hhalfMassP : (∫ x : ℝ in 0..1, p x ^ 2) =
      (1 / 2 : ℝ) * factorTwoIntrinsicEnergy p := by
    unfold factorTwoIntrinsicEnergy
    linarith
  have hhalfMass : (∫ x : ℝ in 0..1,
      fourCellOddOneThreeFiveLowProfile c d e x ^ 2) =
      (1 / 2 : ℝ) * factorTwoIntrinsicEnergy
        (fourCellOddOneThreeFiveLowProfile c d e) := by
    simpa only [p] using hhalfMassP
  rw [hhalfMass]
  dsimp only [p] at *
  rw [centeredRawLogEnergy_oneThreeFiveLowProfile,
    integral_zero_one_endpointPotential_oneThreeFiveLowProfile,
    factorTwoIntrinsicEnergy_oneThreeFiveLowProfile]
  ring

/-- Polarized `(1,5)` entry of the exact local algebraic P135 block. -/
def fourCellOddOneThreeFiveLocalAlgebraic15 : ℝ :=
  -(1 / 2 : ℝ) * (736 / 15625) +
    Real.sqrt 2 * Real.log 2 * (-3296 / 78125) +
    (2 - Real.sqrt 2 * Real.log 2) * (184 / 15625) -
    (7 / 50 : ℝ) * (1 / 28)

/-- Polarized `(3,5)` entry of the exact local algebraic P135 block. -/
def fourCellOddOneThreeFiveLocalAlgebraic35 : ℝ :=
  -(1 / 2 : ℝ) * (496 / 3125) +
    Real.sqrt 2 * Real.log 2 * (-576 / 390625) +
    (2 - Real.sqrt 2 * Real.log 2) * (3096 / 78125) -
    (7 / 50 : ℝ) * (1 / 18)

/-- `(5,5)` entry of the exact local algebraic P135 block. -/
def fourCellOddOneThreeFiveLocalAlgebraic55 : ℝ :=
  -(1 / 2 : ℝ) * (898920274 / 8056640625) +
    Real.sqrt 2 * Real.log 2 * (1495776 / 48828125) +
    (2 - Real.sqrt 2 * Real.log 2) * (14520002 / 537109375) +
    ((14 / 5 : ℝ) -
      2 * (Real.log (2 * fourCellOperatorHalfWidth) +
        Real.eulerMascheroniConstant + Real.log Real.pi) - 3 / 200) *
      (1 / 11) -
    (7 / 50 : ℝ) *
      (19157 / 152460 - (1 / 11 : ℝ) * Real.log 2)

/-- Exact algebraic part of the local defect on `span(P₁,P₃,P₅)`. -/
def fourCellOddOneThreeFiveLocalAlgebraicQuadratic
    (c d e : ℝ) : ℝ :=
  fourCellOddLowLocalAlgebraicQuadratic c d +
    2 * fourCellOddOneThreeFiveLocalAlgebraic15 * c * e +
    2 * fourCellOddOneThreeFiveLocalAlgebraic35 * d * e +
    fourCellOddOneThreeFiveLocalAlgebraic55 * e ^ 2

/-- Exact P135 local-width normal form.  All strip, scalar, and potential
terms are explicit; the wide regular-kernel quadratic remains intact as the
single nonsingular form that must be certified in the finite block. -/
theorem fourCellOddStripLocalWidthDefect_oneThreeFiveLowProfile_eq
    (c d e : ℝ) :
    fourCellOddStripLocalWidthDefect
        (fourCellOddOneThreeFiveLowProfile c d e) =
      fourCellOddOneThreeFiveLocalAlgebraicQuadratic c d e -
        2 * fourCellOperatorHalfWidth *
          (∫ t : ℝ in 0..2,
            yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
              centeredEndpointCorrelation
                (fourCellOddOneThreeFiveLowProfile c d e) t) := by
  unfold fourCellOddStripLocalWidthDefect
    fourCellOddOneThreeFiveLocalAlgebraicQuadratic
    fourCellOddOneThreeFiveLocalAlgebraic15
    fourCellOddOneThreeFiveLocalAlgebraic35
    fourCellOddOneThreeFiveLocalAlgebraic55
    fourCellOddLowLocalAlgebraicQuadratic
    fourCellOddLowLocalAlgebraic11 fourCellOddLowLocalAlgebraic13
    fourCellOddLowLocalAlgebraic33
  rw [fourCellOddEndpointStripOddRawEnergy_oneThreeFiveLowProfile,
    fourCellOddEndpointStripEvenMass_oneThreeFiveLowProfile,
    fourCellOddEndpointStripOddMass_oneThreeFiveLowProfile,
    integral_zero_one_oneThreeFiveLowProfile_sq,
    integral_zero_one_endpointPotential_oneThreeFiveLowProfile]
  ring

/-- Polarized `(1,5)` entry after adding the exact core reserve to the
local algebraic block. -/
def fourCellOddOneThreeFiveCombined15 : ℝ :=
  1 / 14 + fourCellOddOneThreeFiveLocalAlgebraic15

/-- Polarized `(3,5)` entry of the exact combined P135 algebraic block. -/
def fourCellOddOneThreeFiveCombined35 : ℝ :=
  1 / 9 + fourCellOddOneThreeFiveLocalAlgebraic35

/-- `(5,5)` entry of the exact combined P135 algebraic block. -/
def fourCellOddOneThreeFiveCombined55 : ℝ :=
  3140 / 7623 - (2 / 11 : ℝ) * Real.log 2 +
    fourCellOddOneThreeFiveLocalAlgebraic55

/-- Exact finite algebraic P135 block before the wide regular quadratic is
subtracted. -/
def fourCellOddOneThreeFiveCombinedQuadratic (c d e : ℝ) : ℝ :=
  fourCellOddLowCombined11 * c ^ 2 +
    2 * fourCellOddLowCombined13 * c * d +
    fourCellOddLowCombined33 * d ^ 2 +
    2 * fourCellOddOneThreeFiveCombined15 * c * e +
    2 * fourCellOddOneThreeFiveCombined35 * d * e +
    fourCellOddOneThreeFiveCombined55 * e ^ 2

private theorem fourCell_sqrt_two_fine_bounds :
    (1414213562 / 1000000000 : ℝ) < Real.sqrt 2 ∧
      Real.sqrt 2 < (1414213563 / 1000000000 : ℝ) := by
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs2 : Real.sqrt 2 ^ 2 = 2 := by
    simpa only using Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  constructor
  · have hrat : (1414213562 / 1000000000 : ℝ) ^ 2 < 2 := by
      norm_num
    nlinarith
  · have hrat : (2 : ℝ) <
        (1414213563 / 1000000000 : ℝ) ^ 2 := by
      norm_num
    nlinarith

private theorem fourCell_sqrt_two_mul_log_two_fine_bounds :
    (1414213562 / 1000000000 : ℝ) *
        (69314718055 / 100000000000 : ℝ) <
          Real.sqrt 2 * Real.log 2 ∧
      Real.sqrt 2 * Real.log 2 <
        (1414213563 / 1000000000 : ℝ) *
          (69314718057 / 100000000000 : ℝ) := by
  have hs := fourCell_sqrt_two_fine_bounds
  have hL := strict_log_two_fine_bounds
  have hs0 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hL0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  constructor
  · calc
      (1414213562 / 1000000000 : ℝ) *
          (69314718055 / 100000000000 : ℝ) <
          Real.sqrt 2 * (69314718055 / 100000000000 : ℝ) :=
        mul_lt_mul_of_pos_right hs.1 (by norm_num)
      _ < Real.sqrt 2 * Real.log 2 :=
        mul_lt_mul_of_pos_left hL.1 hs0
  · calc
      Real.sqrt 2 * Real.log 2 <
          (1414213563 / 1000000000 : ℝ) * Real.log 2 :=
        mul_lt_mul_of_pos_right hs.2 hL0
      _ < (1414213563 / 1000000000 : ℝ) *
          (69314718057 / 100000000000 : ℝ) :=
        mul_lt_mul_of_pos_left hL.2 (by norm_num)

private theorem fourCell_log_five_four_fine_bounds :
    (223143 / 1000000 : ℝ) < Real.log (5 / 4 : ℝ) ∧
      Real.log (5 / 4 : ℝ) < (223144 / 1000000 : ℝ) := by
  have hlo := Real.sum_range_le_log_div (x := (1 / 9 : ℝ))
    (by norm_num) (by norm_num) 4
  have hup := Real.log_div_le_sum_range_add (x := (1 / 9 : ℝ))
    (by norm_num) (by norm_num) 4
  norm_num [Finset.sum_range_succ] at hlo hup ⊢
  constructor <;> linarith

private theorem fourCell_log_inv_log_two_lower_model_upper :
    Real.log (100000000000 / 69314718055 : ℝ) <
      (36652 / 100000 : ℝ) := by
  have h := Real.log_div_le_sum_range_add
    (x := (30685281945 / 169314718055 : ℝ))
      (by norm_num) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

private theorem fourCell_log_inv_log_two_upper_model_lower :
    (36651 / 100000 : ℝ) <
      Real.log (100000000000 / 69314718057 : ℝ) := by
  have h := Real.sum_range_le_log_div
    (x := (30685281943 / 169314718057 : ℝ))
      (by norm_num) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

private theorem fourCell_log_log_two_fine_bounds :
    (-36652 / 100000 : ℝ) < Real.log (Real.log 2) ∧
      Real.log (Real.log 2) < (-36651 / 100000 : ℝ) := by
  have hL := strict_log_two_fine_bounds
  have hLpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hloRat :
      (-36652 / 100000 : ℝ) <
        Real.log (69314718055 / 100000000000 : ℝ) := by
    rw [show (69314718055 / 100000000000 : ℝ) =
        (100000000000 / 69314718055 : ℝ)⁻¹ by norm_num,
      Real.log_inv]
    linarith [fourCell_log_inv_log_two_lower_model_upper]
  have hhiRat :
      Real.log (69314718057 / 100000000000 : ℝ) <
        (-36651 / 100000 : ℝ) := by
    rw [show (69314718057 / 100000000000 : ℝ) =
        (100000000000 / 69314718057 : ℝ)⁻¹ by norm_num,
      Real.log_inv]
    linarith [fourCell_log_inv_log_two_upper_model_lower]
  constructor
  · exact hloRat.trans (Real.log_lt_log (by norm_num) hL.1)
  · exact (Real.log_lt_log hLpos hL.2).trans hhiRat

private theorem fourCell_log_four_hundred_fine_bounds :
    (59914645469 / 10000000000 : ℝ) < Real.log 400 ∧
      Real.log 400 < (59914645474 / 10000000000 : ℝ) := by
  have htwo := strict_log_two_fine_bounds
  have hhundred := strict_log_one_hundred_bounds
  have hid : Real.log (400 : ℝ) =
      2 * Real.log 2 + Real.log 100 := by
    calc
      Real.log (400 : ℝ) = Real.log ((2 : ℝ) ^ 2 * 100) := by
        norm_num
      _ = Real.log ((2 : ℝ) ^ 2) + Real.log 100 := by
        rw [Real.log_mul (by norm_num) (by norm_num)]
      _ = 2 * Real.log 2 + Real.log 100 := by
        rw [Real.log_pow]
        norm_num
  rw [hid]
  constructor <;> linarith

set_option maxRecDepth 100000 in
private theorem fourCell_euler_gamma_fine_bounds :
    (577215 / 1000000 : ℝ) < Real.eulerMascheroniConstant ∧
      Real.eulerMascheroniConstant < (577216 / 1000000 : ℝ) := by
  have hlower := gammaLowerApprox_le_eulerGamma 399
  have hupper := eulerGamma_le_gammaUpperApprox 399
  have hlog := fourCell_log_four_hundred_fine_bounds
  constructor
  · apply lt_of_lt_of_le ?_ hlower
    simp only [gammaLowerApprox]
    norm_num [harmonic, Finset.sum_range_succ] at ⊢
    linarith [hlog.2]
  · apply lt_of_le_of_lt hupper
    simp only [gammaUpperApprox, gammaLowerApprox]
    norm_num [harmonic, Finset.sum_range_succ] at ⊢
    linarith [hlog.1]

private theorem fourCell_log_pi_rational_fine_lower :
    (1144729 / 1000000 : ℝ) <
      Real.log (3141592 / 1000000 : ℝ) := by
  have h := Real.sum_range_le_log_div
    (x := (267699 / 517699 : ℝ)) (by norm_num) (by norm_num) 14
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

private theorem fourCell_log_pi_rational_fine_upper :
    Real.log (3141593 / 1000000 : ℝ) <
      (1144730 / 1000000 : ℝ) := by
  have h := Real.log_div_le_sum_range_add
    (x := (2141593 / 4141593 : ℝ)) (by norm_num) (by norm_num) 16
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

private theorem fourCell_log_pi_fine_bounds :
    (1144729 / 1000000 : ℝ) < Real.log Real.pi ∧
      Real.log Real.pi < (1144730 / 1000000 : ℝ) := by
  constructor
  · have hpi := Real.pi_gt_d6
    have hlog := fourCell_log_pi_rational_fine_lower
    norm_num at hpi hlog ⊢
    exact hlog.trans (Real.log_lt_log (by norm_num) hpi)
  · have hpi := Real.pi_lt_d6
    have hlog := fourCell_log_pi_rational_fine_upper
    norm_num at hpi hlog ⊢
    exact (Real.log_lt_log Real.pi_pos hpi).trans hlog

/-- Fine enclosure of the one shared transcendental scalar occurring in
the three diagonal algebraic entries. -/
theorem fourCellScalar_fine_bounds :
    (1578567 / 1000000 : ℝ) <
        Real.log (2 * fourCellOperatorHalfWidth) +
          Real.eulerMascheroniConstant + Real.log Real.pi ∧
      Real.log (2 * fourCellOperatorHalfWidth) +
          Real.eulerMascheroniConstant + Real.log Real.pi <
        (1578580 / 1000000 : ℝ) := by
  have hlogTwo : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hwidth :
      Real.log (2 * fourCellOperatorHalfWidth) =
        Real.log (5 / 4 : ℝ) + Real.log (Real.log 2) := by
    rw [show 2 * fourCellOperatorHalfWidth =
        (5 / 4 : ℝ) * Real.log 2 by
      unfold fourCellOperatorHalfWidth
      ring,
      Real.log_mul (by norm_num : (5 / 4 : ℝ) ≠ 0) hlogTwo]
  rw [hwidth]
  rcases fourCell_log_five_four_fine_bounds with ⟨h54lo, h54hi⟩
  rcases fourCell_log_log_two_fine_bounds with ⟨hLlo, hLhi⟩
  rcases fourCell_euler_gamma_fine_bounds with ⟨hγlo, hγhi⟩
  rcases fourCell_log_pi_fine_bounds with ⟨hπlo, hπhi⟩
  constructor <;> linarith

private theorem log_five_four_gt_2231_div_10000_oneThreeFive :
    (2231 / 10000 : ℝ) < Real.log (5 / 4 : ℝ) := by
  have h := Real.sum_range_le_log_div (x := (1 / 9 : ℝ))
    (by norm_num) (by norm_num) 3
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

private theorem fourCellScalar_gt_15783_div_10000_oneThreeFive :
    (15783 / 10000 : ℝ) <
      Real.log (2 * fourCellOperatorHalfWidth) +
        Real.eulerMascheroniConstant + Real.log Real.pi := by
  have hlogTwo : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hwidth :
      Real.log (2 * fourCellOperatorHalfWidth) =
        Real.log (5 / 4 : ℝ) + Real.log (Real.log 2) := by
    rw [show 2 * fourCellOperatorHalfWidth =
        (5 / 4 : ℝ) * Real.log 2 by
      unfold fourCellOperatorHalfWidth
      ring,
      Real.log_mul (by norm_num : (5 / 4 : ℝ) ≠ 0) hlogTwo]
  rw [hwidth]
  linarith [log_five_four_gt_2231_div_10000_oneThreeFive,
    strict_log_log_two_bounds.1, strict_euler_gamma_bounds.1,
    strict_log_pi_bounds.1]

/-- Tight rational enclosure of all six entries of the algebraic P135
matrix.  These intervals are only used to certify its principal minors. -/
theorem fourCellOddOneThreeFiveCombined_entry_bounds :
    (629 / 2500 : ℝ) < fourCellOddLowCombined11 ∧
    fourCellOddLowCombined11 < (1261 / 5000 : ℝ) ∧
    (1093 / 5000 : ℝ) < fourCellOddLowCombined13 ∧
    fourCellOddLowCombined13 < (2187 / 10000 : ℝ) ∧
    (41 / 200 : ℝ) < fourCellOddLowCombined33 ∧
    fourCellOddLowCombined33 < (2053 / 10000 : ℝ) ∧
    (169 / 12500 : ℝ) < fourCellOddOneThreeFiveCombined15 ∧
    fourCellOddOneThreeFiveCombined15 < (677 / 50000 : ℝ) ∧
    (6293 / 100000 : ℝ) < fourCellOddOneThreeFiveCombined35 ∧
    fourCellOddOneThreeFiveCombined35 < (1259 / 20000 : ℝ) ∧
    (49 / 200 : ℝ) < fourCellOddOneThreeFiveCombined55 ∧
    fourCellOddOneThreeFiveCombined55 < (613 / 2500 : ℝ) := by
  have hL := strict_log_two_bounds
  have hS := sqrt_two_mul_log_two_bounds
  have hTlo := fourCellScalar_gt_15783_div_10000_oneThreeFive
  have hThi := fourCellScalar_lt_31577_div_20000
  have h11 : fourCellOddLowCombined11 =
      893 / 600 - (31 / 50 : ℝ) * Real.log 2 +
        (94 / 375 : ℝ) * (Real.sqrt 2 * Real.log 2) -
          (2 / 3 : ℝ) *
            (Real.log (2 * fourCellOperatorHalfWidth) +
              Real.eulerMascheroniConstant + Real.log Real.pi) := by
    unfold fourCellOddLowCombined11 fourCellOddLowLocalAlgebraic11
    ring
  have h13 : fourCellOddLowCombined13 =
      93 / 500 + (104 / 3125 : ℝ) *
        (Real.sqrt 2 * Real.log 2) := by
    unfold fourCellOddLowCombined13 fourCellOddLowLocalAlgebraic13
    ring
  have h33 : fourCellOddLowCombined33 =
      5434921 / 6125000 - (5242 / 109375 : ℝ) *
          (Real.sqrt 2 * Real.log 2) -
        (93 / 350 : ℝ) * Real.log 2 -
        (2 / 7 : ℝ) *
          (Real.log (2 * fourCellOperatorHalfWidth) +
            Real.eulerMascheroniConstant + Real.log Real.pi) := by
    unfold fourCellOddLowCombined33 fourCellOddLowLocalAlgebraic33
    ring
  have h15 : fourCellOddOneThreeFiveCombined15 =
      93 / 1400 - (4216 / 78125 : ℝ) *
        (Real.sqrt 2 * Real.log 2) := by
    unfold fourCellOddOneThreeFiveCombined15
      fourCellOddOneThreeFiveLocalAlgebraic15
    ring
  have h35 : fourCellOddOneThreeFiveCombined35 =
      96779 / 937500 - (16056 / 390625 : ℝ) *
        (Real.sqrt 2 * Real.log 2) := by
    unfold fourCellOddOneThreeFiveCombined35
      fourCellOddOneThreeFiveLocalAlgebraic35
    ring
  have h55 : fourCellOddOneThreeFiveCombined55 =
      1602471330659 / 2481445312500 +
        (1933534 / 537109375 : ℝ) *
          (Real.sqrt 2 * Real.log 2) -
        (93 / 550 : ℝ) * Real.log 2 -
        (2 / 11 : ℝ) *
          (Real.log (2 * fourCellOperatorHalfWidth) +
            Real.eulerMascheroniConstant + Real.log Real.pi) := by
    unfold fourCellOddOneThreeFiveCombined55
      fourCellOddOneThreeFiveLocalAlgebraic55
    ring
  rw [h11, h13, h33, h15, h35, h55]
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

/-- Fine algebraic entry box used for the perturbed determinant.  The
shared scalar is enclosed once, so the later determinant estimate does not
discard its structural correlation across the three diagonal entries. -/
theorem fourCellOddOneThreeFiveCombined_entry_fine_bounds :
    (2519 / 10000 : ℝ) < fourCellOddLowCombined11 ∧
    fourCellOddLowCombined11 < (2520 / 10000 : ℝ) ∧
    (21862 / 100000 : ℝ) < fourCellOddLowCombined13 ∧
    fourCellOddLowCombined13 < (21863 / 100000 : ℝ) ∧
    (20515 / 100000 : ℝ) < fourCellOddLowCombined33 ∧
    fourCellOddLowCombined33 < (20516 / 100000 : ℝ) ∧
    (13529 / 1000000 : ℝ) < fourCellOddOneThreeFiveCombined15 ∧
    fourCellOddOneThreeFiveCombined15 < (13530 / 1000000 : ℝ) ∧
    (62939 / 1000000 : ℝ) < fourCellOddOneThreeFiveCombined35 ∧
    fourCellOddOneThreeFiveCombined35 < (62940 / 1000000 : ℝ) ∧
    (24509 / 100000 : ℝ) < fourCellOddOneThreeFiveCombined55 ∧
    fourCellOddOneThreeFiveCombined55 < (24510 / 100000 : ℝ) := by
  have hL := strict_log_two_fine_bounds
  have hP := fourCell_sqrt_two_mul_log_two_fine_bounds
  have hT := fourCellScalar_fine_bounds
  have h11 : fourCellOddLowCombined11 =
      893 / 600 - (31 / 50 : ℝ) * Real.log 2 +
        (94 / 375 : ℝ) * (Real.sqrt 2 * Real.log 2) -
          (2 / 3 : ℝ) *
            (Real.log (2 * fourCellOperatorHalfWidth) +
              Real.eulerMascheroniConstant + Real.log Real.pi) := by
    unfold fourCellOddLowCombined11 fourCellOddLowLocalAlgebraic11
    ring
  have h13 : fourCellOddLowCombined13 =
      93 / 500 + (104 / 3125 : ℝ) *
        (Real.sqrt 2 * Real.log 2) := by
    unfold fourCellOddLowCombined13 fourCellOddLowLocalAlgebraic13
    ring
  have h33 : fourCellOddLowCombined33 =
      5434921 / 6125000 - (5242 / 109375 : ℝ) *
          (Real.sqrt 2 * Real.log 2) -
        (93 / 350 : ℝ) * Real.log 2 -
        (2 / 7 : ℝ) *
          (Real.log (2 * fourCellOperatorHalfWidth) +
            Real.eulerMascheroniConstant + Real.log Real.pi) := by
    unfold fourCellOddLowCombined33 fourCellOddLowLocalAlgebraic33
    ring
  have h15 : fourCellOddOneThreeFiveCombined15 =
      93 / 1400 - (4216 / 78125 : ℝ) *
        (Real.sqrt 2 * Real.log 2) := by
    unfold fourCellOddOneThreeFiveCombined15
      fourCellOddOneThreeFiveLocalAlgebraic15
    ring
  have h35 : fourCellOddOneThreeFiveCombined35 =
      96779 / 937500 - (16056 / 390625 : ℝ) *
        (Real.sqrt 2 * Real.log 2) := by
    unfold fourCellOddOneThreeFiveCombined35
      fourCellOddOneThreeFiveLocalAlgebraic35
    ring
  have h55 : fourCellOddOneThreeFiveCombined55 =
      1602471330659 / 2481445312500 +
        (1933534 / 537109375 : ℝ) *
          (Real.sqrt 2 * Real.log 2) -
        (93 / 550 : ℝ) * Real.log 2 -
        (2 / 11 : ℝ) *
          (Real.log (2 * fourCellOperatorHalfWidth) +
            Real.eulerMascheroniConstant + Real.log Real.pi) := by
    unfold fourCellOddOneThreeFiveCombined55
      fourCellOddOneThreeFiveLocalAlgebraic55
    ring
  rw [h11, h13, h33, h15, h35, h55]
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

/-- Leading `P₁/P₃` principal minor of the exact algebraic block. -/
def fourCellOddOneThreeFiveCombinedMinor13 : ℝ :=
  fourCellOddLowCombined11 * fourCellOddLowCombined33 -
    fourCellOddLowCombined13 ^ 2

/-- Determinant of the exact algebraic P135 block. -/
def fourCellOddOneThreeFiveCombinedDeterminant : ℝ :=
  fourCellOddLowCombined11 * fourCellOddLowCombined33 *
      fourCellOddOneThreeFiveCombined55 +
    2 * fourCellOddLowCombined13 *
      fourCellOddOneThreeFiveCombined15 *
        fourCellOddOneThreeFiveCombined35 -
    fourCellOddLowCombined11 * fourCellOddOneThreeFiveCombined35 ^ 2 -
    fourCellOddLowCombined33 * fourCellOddOneThreeFiveCombined15 ^ 2 -
    fourCellOddOneThreeFiveCombined55 * fourCellOddLowCombined13 ^ 2

/-- Strict Sylvester data for the exact algebraic P135 block. -/
theorem fourCellOddOneThreeFiveCombined_principal_data :
    0 < fourCellOddLowCombined11 ∧
      0 < fourCellOddOneThreeFiveCombinedMinor13 ∧
        (1 / 5000 : ℝ) <
          fourCellOddOneThreeFiveCombinedDeterminant := by
  let A : ℝ := fourCellOddLowCombined11
  let B : ℝ := fourCellOddLowCombined13
  let D : ℝ := fourCellOddLowCombined33
  let E : ℝ := fourCellOddOneThreeFiveCombined15
  let F : ℝ := fourCellOddOneThreeFiveCombined35
  let G : ℝ := fourCellOddOneThreeFiveCombined55
  rcases fourCellOddOneThreeFiveCombined_entry_bounds with
    ⟨hAlo, hAhi, hBlo, hBhi, hDlo, hDhi,
      hElo, hEhi, hFlo, hFhi, hGlo, hGhi⟩
  change (629 / 2500 : ℝ) < A at hAlo
  change A < (1261 / 5000 : ℝ) at hAhi
  change (1093 / 5000 : ℝ) < B at hBlo
  change B < (2187 / 10000 : ℝ) at hBhi
  change (41 / 200 : ℝ) < D at hDlo
  change D < (2053 / 10000 : ℝ) at hDhi
  change (169 / 12500 : ℝ) < E at hElo
  change E < (677 / 50000 : ℝ) at hEhi
  change (6293 / 100000 : ℝ) < F at hFlo
  change F < (1259 / 20000 : ℝ) at hFhi
  change (49 / 200 : ℝ) < G at hGlo
  change G < (613 / 2500 : ℝ) at hGhi
  have hA0 : 0 ≤ A := by linarith
  have hB0 : 0 ≤ B := by linarith
  have hD0 : 0 ≤ D := by linarith
  have hE0 : 0 ≤ E := by linarith
  have hF0 : 0 ≤ F := by linarith
  have hG0 : 0 ≤ G := by linarith
  have hBsq : B ^ 2 ≤ (2187 / 10000 : ℝ) ^ 2 := by
    nlinarith [mul_nonneg hB0 (sub_nonneg.mpr hBhi.le)]
  have hEsq : E ^ 2 ≤ (677 / 50000 : ℝ) ^ 2 := by
    nlinarith [mul_nonneg hE0 (sub_nonneg.mpr hEhi.le)]
  have hFsq : F ^ 2 ≤ (1259 / 20000 : ℝ) ^ 2 := by
    nlinarith [mul_nonneg hF0 (sub_nonneg.mpr hFhi.le)]
  have hADlo : (629 / 2500 : ℝ) * (41 / 200) ≤ A * D := by
    calc
      (629 / 2500 : ℝ) * (41 / 200) ≤ A * (41 / 200) :=
        mul_le_mul_of_nonneg_right hAlo.le (by norm_num)
      _ ≤ A * D := mul_le_mul_of_nonneg_left hDlo.le hA0
  have hADGlo :
      (629 / 2500 : ℝ) * (41 / 200) * (49 / 200) ≤ A * D * G := by
    calc
      (629 / 2500 : ℝ) * (41 / 200) * (49 / 200) ≤
          (A * D) * (49 / 200) :=
        mul_le_mul_of_nonneg_right hADlo (by norm_num)
      _ ≤ A * D * G :=
        mul_le_mul_of_nonneg_left hGlo.le (mul_nonneg hA0 hD0)
  have hBElo :
      (1093 / 5000 : ℝ) * (169 / 12500) ≤ B * E := by
    calc
      (1093 / 5000 : ℝ) * (169 / 12500) ≤
          B * (169 / 12500) :=
        mul_le_mul_of_nonneg_right hBlo.le (by norm_num)
      _ ≤ B * E := mul_le_mul_of_nonneg_left hElo.le hB0
  have hBEFlo :
      (1093 / 5000 : ℝ) * (169 / 12500) * (6293 / 100000) ≤
        B * E * F := by
    calc
      (1093 / 5000 : ℝ) * (169 / 12500) * (6293 / 100000) ≤
          (B * E) * (6293 / 100000) :=
        mul_le_mul_of_nonneg_right hBElo (by norm_num)
      _ ≤ B * E * F :=
        mul_le_mul_of_nonneg_left hFlo.le (mul_nonneg hB0 hE0)
  have hAFsq : A * F ^ 2 ≤
      (1261 / 5000 : ℝ) * (1259 / 20000) ^ 2 := by
    calc
      A * F ^ 2 ≤ (1261 / 5000 : ℝ) * F ^ 2 :=
        mul_le_mul_of_nonneg_right hAhi.le (sq_nonneg F)
      _ ≤ (1261 / 5000 : ℝ) * (1259 / 20000) ^ 2 :=
        mul_le_mul_of_nonneg_left hFsq (by norm_num)
  have hDEsq : D * E ^ 2 ≤
      (2053 / 10000 : ℝ) * (677 / 50000) ^ 2 := by
    calc
      D * E ^ 2 ≤ (2053 / 10000 : ℝ) * E ^ 2 :=
        mul_le_mul_of_nonneg_right hDhi.le (sq_nonneg E)
      _ ≤ (2053 / 10000 : ℝ) * (677 / 50000) ^ 2 :=
        mul_le_mul_of_nonneg_left hEsq (by norm_num)
  have hGBsq : G * B ^ 2 ≤
      (613 / 2500 : ℝ) * (2187 / 10000) ^ 2 := by
    calc
      G * B ^ 2 ≤ (613 / 2500 : ℝ) * B ^ 2 :=
        mul_le_mul_of_nonneg_right hGhi.le (sq_nonneg B)
      _ ≤ (613 / 2500 : ℝ) * (2187 / 10000) ^ 2 :=
        mul_le_mul_of_nonneg_left hBsq (by norm_num)
  change 0 < A ∧ 0 < A * D - B ^ 2 ∧
    (1 / 5000 : ℝ) <
      A * D * G + 2 * B * E * F - A * F ^ 2 - D * E ^ 2 - G * B ^ 2
  constructor
  · exact hAlo.trans' (by norm_num)
  constructor
  · nlinarith [hADlo, hBsq]
  · nlinarith [hADGlo, hBEFlo, hAFsq, hDEsq, hGBsq]

/-- The exact algebraic P135 block is positive semidefinite.  The proof is
an explicit `LDLᵀ` identity driven by the strict principal-minor data. -/
theorem fourCellOddOneThreeFiveCombinedQuadratic_nonneg
    (c d e : ℝ) :
    0 ≤ fourCellOddOneThreeFiveCombinedQuadratic c d e := by
  let A : ℝ := fourCellOddLowCombined11
  let B : ℝ := fourCellOddLowCombined13
  let D : ℝ := fourCellOddLowCombined33
  let E : ℝ := fourCellOddOneThreeFiveCombined15
  let F : ℝ := fourCellOddOneThreeFiveCombined35
  let G : ℝ := fourCellOddOneThreeFiveCombined55
  let Δ : ℝ := A * D - B ^ 2
  let det : ℝ :=
    A * D * G + 2 * B * E * F - A * F ^ 2 - D * E ^ 2 - G * B ^ 2
  rcases fourCellOddOneThreeFiveCombined_principal_data with
    ⟨hA, hΔ, hdet⟩
  change 0 < A at hA
  change 0 < Δ at hΔ
  change (1 / 5000 : ℝ) < det at hdet
  change 0 ≤
    A * c ^ 2 + 2 * B * c * d + D * d ^ 2 +
      2 * E * c * e + 2 * F * d * e + G * e ^ 2
  let Q : ℝ :=
    A * c ^ 2 + 2 * B * c * d + D * d ^ 2 +
      2 * E * c * e + 2 * F * d * e + G * e ^ 2
  have hid : A * Δ * Q =
      Δ * (A * c + B * d + E * e) ^ 2 +
        (Δ * d + (A * F - B * E) * e) ^ 2 +
          A * det * e ^ 2 := by
    dsimp only [Q, Δ, det]
    ring
  have hrhs : 0 ≤
      Δ * (A * c + B * d + E * e) ^ 2 +
        (Δ * d + (A * F - B * E) * e) ^ 2 +
          A * det * e ^ 2 := by
    have hdet0 : 0 ≤ det := by linarith
    positivity
  have hprod : 0 ≤ A * Δ * Q := by
    rw [hid]
    exact hrhs
  have hcoef : 0 < A * Δ := mul_pos hA hΔ
  have hQ : 0 ≤ Q := by
    by_contra hneg
    have hQneg : Q < 0 := lt_of_not_ge hneg
    have hmulNeg : A * Δ * Q < 0 := by
      exact mul_neg_of_pos_of_neg hcoef hQneg
    linarith
  exact hQ

/-! ### The actual finite block after the wide-regular perturbation -/

def fourCellOddOneThreeFivePerturbed11 : ℝ :=
  fourCellOddLowCombined11 -
    2 * fourCellOperatorHalfWidth * fourCellOddOneThreeFiveRegular11

def fourCellOddOneThreeFivePerturbed13 : ℝ :=
  fourCellOddLowCombined13 -
    2 * fourCellOperatorHalfWidth * fourCellOddOneThreeFiveRegular13

def fourCellOddOneThreeFivePerturbed33 : ℝ :=
  fourCellOddLowCombined33 -
    2 * fourCellOperatorHalfWidth * fourCellOddOneThreeFiveRegular33

def fourCellOddOneThreeFivePerturbed15 : ℝ :=
  fourCellOddOneThreeFiveCombined15 -
    2 * fourCellOperatorHalfWidth * fourCellOddOneThreeFiveRegular15

def fourCellOddOneThreeFivePerturbed35 : ℝ :=
  fourCellOddOneThreeFiveCombined35 -
    2 * fourCellOperatorHalfWidth * fourCellOddOneThreeFiveRegular35

def fourCellOddOneThreeFivePerturbed55 : ℝ :=
  fourCellOddOneThreeFiveCombined55 -
    2 * fourCellOperatorHalfWidth * fourCellOddOneThreeFiveRegular55

/-- Exact actual `P₁/P₃/P₅` quadratic after the full wide regular
form is subtracted. -/
def fourCellOddOneThreeFivePerturbedQuadratic (c d e : ℝ) : ℝ :=
  fourCellOddOneThreeFivePerturbed11 * c ^ 2 +
    2 * fourCellOddOneThreeFivePerturbed13 * c * d +
    fourCellOddOneThreeFivePerturbed33 * d ^ 2 +
    2 * fourCellOddOneThreeFivePerturbed15 * c * e +
    2 * fourCellOddOneThreeFivePerturbed35 * d * e +
    fourCellOddOneThreeFivePerturbed55 * e ^ 2

private theorem two_mul_fourCellOperatorHalfWidth_fine_bounds :
    (8664 / 10000 : ℝ) < 2 * fourCellOperatorHalfWidth ∧
      2 * fourCellOperatorHalfWidth < (8665 / 10000 : ℝ) := by
  have hL := strict_log_two_fine_bounds
  unfold fourCellOperatorHalfWidth
  constructor <;> nlinarith

set_option maxHeartbeats 1000000 in
/-- Tight rational box for the six entries of the actual perturbed block.
The positive `P₁/P₃` cross is strengthened by the certified negative
sign of `R₁₃`; the `P₃/P₅` entry is retained one-sided. -/
theorem fourCellOddOneThreeFivePerturbed_entry_bounds :
    (247368 / 1000000 : ℝ) < fourCellOddOneThreeFivePerturbed11 ∧
    fourCellOddOneThreeFivePerturbed11 < (248102 / 1000000 : ℝ) ∧
    (218706 / 1000000 : ℝ) < fourCellOddOneThreeFivePerturbed13 ∧
    fourCellOddOneThreeFivePerturbed13 < (218873 / 1000000 : ℝ) ∧
    (204916 / 1000000 : ℝ) < fourCellOddOneThreeFivePerturbed33 ∧
    fourCellOddOneThreeFivePerturbed33 < (205195 / 1000000 : ℝ) ∧
    (134917 / 10000000 : ℝ) < fourCellOddOneThreeFivePerturbed15 ∧
    fourCellOddOneThreeFivePerturbed15 < (135673 / 10000000 : ℝ) ∧
    (629208 / 10000000 : ℝ) < fourCellOddOneThreeFivePerturbed35 ∧
    fourCellOddOneThreeFivePerturbed35 < (630033 / 10000000 : ℝ) ∧
    (2449825 / 10000000 : ℝ) < fourCellOddOneThreeFivePerturbed55 ∧
    fourCellOddOneThreeFivePerturbed55 < (245159 / 1000000 : ℝ) := by
  let W : ℝ := 2 * fourCellOperatorHalfWidth
  rcases two_mul_fourCellOperatorHalfWidth_fine_bounds with ⟨hWlo, hWhi⟩
  change (8664 / 10000 : ℝ) < W at hWlo
  change W < (8665 / 10000 : ℝ) at hWhi
  have hW0 : 0 < W := hWlo.trans' (by norm_num)
  rcases fourCellOddOneThreeFiveCombined_entry_fine_bounds with
    ⟨hAlo, hAhi, hBlo, hBhi, hDlo, hDhi,
      hElo, hEhi, hFlo, hFhi, hGlo, hGhi⟩
  rcases fourCellOddOneThreeFiveRegular_entry_bounds with
    ⟨h11lo, h11hi, h13lo, h13hi, h33lo, h33hi,
      h15lo, h15hi, h35lo, h35hi, h55lo, h55hi⟩
  have hW11lo :
      (8664 / 10000 : ℝ) * (45 / 10000) <
        W * fourCellOddOneThreeFiveRegular11 := by
    calc
      (8664 / 10000 : ℝ) * (45 / 10000) < W * (45 / 10000) :=
        mul_lt_mul_of_pos_right hWlo (by norm_num)
      _ < W * fourCellOddOneThreeFiveRegular11 :=
        mul_lt_mul_of_pos_left h11lo hW0
  have hW11hi :
      W * fourCellOddOneThreeFiveRegular11 <
        (8665 / 10000 : ℝ) * (523 / 100000) := by
    calc
      W * fourCellOddOneThreeFiveRegular11 < W * (523 / 100000) :=
        mul_lt_mul_of_pos_left h11hi hW0
      _ < (8665 / 10000 : ℝ) * (523 / 100000) :=
        mul_lt_mul_of_pos_right hWhi (by norm_num)
  have hW13lo :
      (8665 / 10000 : ℝ) * (-28 / 100000) <
        W * fourCellOddOneThreeFiveRegular13 := by
    calc
      (8665 / 10000 : ℝ) * (-28 / 100000) <
          W * (-28 / 100000) :=
        mul_lt_mul_of_neg_right hWhi (by norm_num)
      _ < W * fourCellOddOneThreeFiveRegular13 :=
        mul_lt_mul_of_pos_left h13lo hW0
  have hW13hi :
      W * fourCellOddOneThreeFiveRegular13 <
        (8664 / 10000 : ℝ) * (-1 / 10000) := by
    calc
      W * fourCellOddOneThreeFiveRegular13 < W * (-1 / 10000) :=
        mul_lt_mul_of_pos_left h13hi hW0
      _ < (8664 / 10000 : ℝ) * (-1 / 10000) :=
        mul_lt_mul_of_neg_right hWlo (by norm_num)
  have hcrossProduct
      {R lo hi : ℝ} (hlo : lo < R) (hhi : R < hi)
      (hlo0 : lo < 0) (hhi0 : 0 < hi) :
      (8665 / 10000 : ℝ) * lo < W * R ∧
        W * R < (8665 / 10000 : ℝ) * hi := by
    constructor
    · calc
        (8665 / 10000 : ℝ) * lo < W * lo :=
          mul_lt_mul_of_neg_right hWhi hlo0
        _ < W * R := mul_lt_mul_of_pos_left hlo hW0
    · calc
        W * R < W * hi := mul_lt_mul_of_pos_left hhi hW0
        _ < (8665 / 10000 : ℝ) * hi :=
          mul_lt_mul_of_pos_right hWhi hhi0
  have hW33 := hcrossProduct h33lo h33hi (by norm_num) (by norm_num)
  have hW15 := hcrossProduct h15lo h15hi (by norm_num) (by norm_num)
  have hW35 := hcrossProduct h35lo h35hi (by norm_num) (by norm_num)
  have hW55 := hcrossProduct h55lo h55hi (by norm_num) (by norm_num)
  unfold fourCellOddOneThreeFivePerturbed11
    fourCellOddOneThreeFivePerturbed13
    fourCellOddOneThreeFivePerturbed33
    fourCellOddOneThreeFivePerturbed15
    fourCellOddOneThreeFivePerturbed35
    fourCellOddOneThreeFivePerturbed55
  change
    (247368 / 1000000 : ℝ) <
        fourCellOddLowCombined11 - W * fourCellOddOneThreeFiveRegular11 ∧ _
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

def fourCellOddOneThreeFivePerturbedMinor13 : ℝ :=
  fourCellOddOneThreeFivePerturbed11 *
      fourCellOddOneThreeFivePerturbed33 -
    fourCellOddOneThreeFivePerturbed13 ^ 2

def fourCellOddOneThreeFivePerturbedDeterminant : ℝ :=
  fourCellOddOneThreeFivePerturbed11 *
      fourCellOddOneThreeFivePerturbed33 *
        fourCellOddOneThreeFivePerturbed55 +
    2 * fourCellOddOneThreeFivePerturbed13 *
      fourCellOddOneThreeFivePerturbed15 *
        fourCellOddOneThreeFivePerturbed35 -
    fourCellOddOneThreeFivePerturbed11 *
      fourCellOddOneThreeFivePerturbed35 ^ 2 -
    fourCellOddOneThreeFivePerturbed33 *
      fourCellOddOneThreeFivePerturbed15 ^ 2 -
    fourCellOddOneThreeFivePerturbed55 *
      fourCellOddOneThreeFivePerturbed13 ^ 2

/-- The actual wide-perturbed block retains a strictly positive determinant.
The lower bound keeps the favorable `2 B E F` interaction, so the small
`P₃/P₅` row is never charged independently against both diagonals. -/
theorem fourCellOddOneThreeFivePerturbed_principal_data :
    0 < fourCellOddOneThreeFivePerturbed11 ∧
      0 < fourCellOddOneThreeFivePerturbedMinor13 ∧
        (1 / 50000 : ℝ) <
          fourCellOddOneThreeFivePerturbedDeterminant := by
  let A : ℝ := fourCellOddOneThreeFivePerturbed11
  let B : ℝ := fourCellOddOneThreeFivePerturbed13
  let D : ℝ := fourCellOddOneThreeFivePerturbed33
  let E : ℝ := fourCellOddOneThreeFivePerturbed15
  let F : ℝ := fourCellOddOneThreeFivePerturbed35
  let G : ℝ := fourCellOddOneThreeFivePerturbed55
  rcases fourCellOddOneThreeFivePerturbed_entry_bounds with
    ⟨hAlo, hAhi, hBlo, hBhi, hDlo, hDhi,
      hElo, hEhi, hFlo, hFhi, hGlo, hGhi⟩
  change (247368 / 1000000 : ℝ) < A at hAlo
  change A < (248102 / 1000000 : ℝ) at hAhi
  change (218706 / 1000000 : ℝ) < B at hBlo
  change B < (218873 / 1000000 : ℝ) at hBhi
  change (204916 / 1000000 : ℝ) < D at hDlo
  change D < (205195 / 1000000 : ℝ) at hDhi
  change (134917 / 10000000 : ℝ) < E at hElo
  change E < (135673 / 10000000 : ℝ) at hEhi
  change (629208 / 10000000 : ℝ) < F at hFlo
  change F < (630033 / 10000000 : ℝ) at hFhi
  change (2449825 / 10000000 : ℝ) < G at hGlo
  change G < (245159 / 1000000 : ℝ) at hGhi
  have hA0 : 0 ≤ A := by linarith
  have hB0 : 0 ≤ B := by linarith
  have hD0 : 0 ≤ D := by linarith
  have hE0 : 0 ≤ E := by linarith
  have hF0 : 0 ≤ F := by linarith
  have hG0 : 0 ≤ G := by linarith
  have hBsq : B ^ 2 ≤ (218873 / 1000000 : ℝ) ^ 2 := by
    nlinarith [mul_nonneg hB0 (sub_nonneg.mpr hBhi.le)]
  have hEsq : E ^ 2 ≤ (135673 / 10000000 : ℝ) ^ 2 := by
    nlinarith [mul_nonneg hE0 (sub_nonneg.mpr hEhi.le)]
  have hFsq : F ^ 2 ≤ (630033 / 10000000 : ℝ) ^ 2 := by
    nlinarith [mul_nonneg hF0 (sub_nonneg.mpr hFhi.le)]
  have hADlo :
      (247368 / 1000000 : ℝ) * (204916 / 1000000) ≤ A * D := by
    calc
      (247368 / 1000000 : ℝ) * (204916 / 1000000) ≤
          A * (204916 / 1000000) :=
        mul_le_mul_of_nonneg_right hAlo.le (by norm_num)
      _ ≤ A * D := mul_le_mul_of_nonneg_left hDlo.le hA0
  have hADGlo :
      (247368 / 1000000 : ℝ) * (204916 / 1000000) *
          (2449825 / 10000000) ≤ A * D * G := by
    calc
      (247368 / 1000000 : ℝ) * (204916 / 1000000) *
          (2449825 / 10000000) ≤
          (A * D) * (2449825 / 10000000) :=
        mul_le_mul_of_nonneg_right hADlo (by norm_num)
      _ ≤ A * D * G :=
        mul_le_mul_of_nonneg_left hGlo.le (mul_nonneg hA0 hD0)
  have hBElo :
      (218706 / 1000000 : ℝ) * (134917 / 10000000) ≤ B * E := by
    calc
      (218706 / 1000000 : ℝ) * (134917 / 10000000) ≤
          B * (134917 / 10000000) :=
        mul_le_mul_of_nonneg_right hBlo.le (by norm_num)
      _ ≤ B * E := mul_le_mul_of_nonneg_left hElo.le hB0
  have hBEFlo :
      (218706 / 1000000 : ℝ) * (134917 / 10000000) *
          (629208 / 10000000) ≤ B * E * F := by
    calc
      (218706 / 1000000 : ℝ) * (134917 / 10000000) *
          (629208 / 10000000) ≤
          (B * E) * (629208 / 10000000) :=
        mul_le_mul_of_nonneg_right hBElo (by norm_num)
      _ ≤ B * E * F :=
        mul_le_mul_of_nonneg_left hFlo.le (mul_nonneg hB0 hE0)
  have hAFsq : A * F ^ 2 ≤
      (248102 / 1000000 : ℝ) * (630033 / 10000000) ^ 2 := by
    calc
      A * F ^ 2 ≤ (248102 / 1000000 : ℝ) * F ^ 2 :=
        mul_le_mul_of_nonneg_right hAhi.le (sq_nonneg F)
      _ ≤ (248102 / 1000000 : ℝ) * (630033 / 10000000) ^ 2 :=
        mul_le_mul_of_nonneg_left hFsq (by norm_num)
  have hDEsq : D * E ^ 2 ≤
      (205195 / 1000000 : ℝ) * (135673 / 10000000) ^ 2 := by
    calc
      D * E ^ 2 ≤ (205195 / 1000000 : ℝ) * E ^ 2 :=
        mul_le_mul_of_nonneg_right hDhi.le (sq_nonneg E)
      _ ≤ (205195 / 1000000 : ℝ) * (135673 / 10000000) ^ 2 :=
        mul_le_mul_of_nonneg_left hEsq (by norm_num)
  have hGBsq : G * B ^ 2 ≤
      (245159 / 1000000 : ℝ) * (218873 / 1000000) ^ 2 := by
    calc
      G * B ^ 2 ≤ (245159 / 1000000 : ℝ) * B ^ 2 :=
        mul_le_mul_of_nonneg_right hGhi.le (sq_nonneg B)
      _ ≤ (245159 / 1000000 : ℝ) * (218873 / 1000000) ^ 2 :=
        mul_le_mul_of_nonneg_left hBsq (by norm_num)
  change 0 < A ∧ 0 < A * D - B ^ 2 ∧
    (1 / 50000 : ℝ) <
      A * D * G + 2 * B * E * F - A * F ^ 2 - D * E ^ 2 - G * B ^ 2
  constructor
  · exact hAlo.trans' (by norm_num)
  constructor
  · nlinarith [hADlo, hBsq]
  · nlinarith [hADGlo, hBEFlo, hAFsq, hDEsq, hGBsq]

/-- Structural positivity of the actual finite block.  This is an explicit
`LDLᵀ` certificate driven by the perturbed determinant, rather than a
finite grid or sign-octant enumeration. -/
theorem fourCellOddOneThreeFivePerturbedQuadratic_nonneg
    (c d e : ℝ) :
    0 ≤ fourCellOddOneThreeFivePerturbedQuadratic c d e := by
  let A : ℝ := fourCellOddOneThreeFivePerturbed11
  let B : ℝ := fourCellOddOneThreeFivePerturbed13
  let D : ℝ := fourCellOddOneThreeFivePerturbed33
  let E : ℝ := fourCellOddOneThreeFivePerturbed15
  let F : ℝ := fourCellOddOneThreeFivePerturbed35
  let G : ℝ := fourCellOddOneThreeFivePerturbed55
  let Δ : ℝ := A * D - B ^ 2
  let det : ℝ :=
    A * D * G + 2 * B * E * F - A * F ^ 2 - D * E ^ 2 - G * B ^ 2
  rcases fourCellOddOneThreeFivePerturbed_principal_data with
    ⟨hA, hΔ, hdet⟩
  change 0 < A at hA
  change 0 < Δ at hΔ
  change (1 / 50000 : ℝ) < det at hdet
  change 0 ≤
    A * c ^ 2 + 2 * B * c * d + D * d ^ 2 +
      2 * E * c * e + 2 * F * d * e + G * e ^ 2
  let Q : ℝ :=
    A * c ^ 2 + 2 * B * c * d + D * d ^ 2 +
      2 * E * c * e + 2 * F * d * e + G * e ^ 2
  have hid : A * Δ * Q =
      Δ * (A * c + B * d + E * e) ^ 2 +
        (Δ * d + (A * F - B * E) * e) ^ 2 +
          A * det * e ^ 2 := by
    dsimp only [Q, Δ, det]
    ring
  have hrhs : 0 ≤
      Δ * (A * c + B * d + E * e) ^ 2 +
        (Δ * d + (A * F - B * E) * e) ^ 2 +
          A * det * e ^ 2 := by
    have hdet0 : 0 ≤ det := by linarith
    positivity
  have hprod : 0 ≤ A * Δ * Q := by
    rw [hid]
    exact hrhs
  have hcoef : 0 < A * Δ := mul_pos hA hΔ
  have hQ : 0 ≤ Q := by
    by_contra hneg
    have hQneg : Q < 0 := lt_of_not_ge hneg
    have hmulNeg : A * Δ * Q < 0 :=
      mul_neg_of_pos_of_neg hcoef hQneg
    linarith
  exact hQ

theorem fourCellOddOneThreeFiveCombined_sub_regular_eq_perturbed
    (c d e : ℝ) :
    fourCellOddOneThreeFiveCombinedQuadratic c d e -
        2 * fourCellOperatorHalfWidth *
          fourCellOddOneThreeFiveRegularQuadratic c d e =
      fourCellOddOneThreeFivePerturbedQuadratic c d e := by
  rw [fourCellOddOneThreeFiveRegularQuadratic_expansion,
    fourCellOddLowRegularQuadratic_expansion]
  unfold fourCellOddOneThreeFiveCombinedQuadratic
    fourCellOddOneThreeFivePerturbedQuadratic
    fourCellOddOneThreeFivePerturbed11
    fourCellOddOneThreeFivePerturbed13
    fourCellOddOneThreeFivePerturbed33
    fourCellOddOneThreeFivePerturbed15
    fourCellOddOneThreeFivePerturbed35
    fourCellOddOneThreeFivePerturbed55
    fourCellOddOneThreeFiveRegular11
    fourCellOddOneThreeFiveRegular13
    fourCellOddOneThreeFiveRegular33
  ring

/-- Closure of the exact finite `P₁/P₃/P₅` diagonal after the wide
regular perturbation. -/
theorem fourCellOddOneThreeFiveCombined_sub_regular_nonneg
    (c d e : ℝ) :
    0 ≤ fourCellOddOneThreeFiveCombinedQuadratic c d e -
      2 * fourCellOperatorHalfWidth *
        fourCellOddOneThreeFiveRegularQuadratic c d e := by
  rw [fourCellOddOneThreeFiveCombined_sub_regular_eq_perturbed]
  exact fourCellOddOneThreeFivePerturbedQuadratic_nonneg c d e

/-- Exact P135 diagonal of the complete core-plus-local target.  This is
the finite `3 × 3` block minus one fully expanded wide regular form. -/
theorem fourCellOddHalfCoreReserve_add_localWidthDefect_oneThreeFive_eq
    (c d e : ℝ) :
    fourCellOddHalfCoreReserve
        (fourCellOddOneThreeFiveLowProfile c d e) +
      fourCellOddStripLocalWidthDefect
        (fourCellOddOneThreeFiveLowProfile c d e) =
      fourCellOddOneThreeFiveCombinedQuadratic c d e -
        2 * fourCellOperatorHalfWidth *
          fourCellOddOneThreeFiveRegularQuadratic c d e := by
  rw [fourCellOddHalfCoreReserve_oneThreeFiveLowProfile,
    fourCellOddStripLocalWidthDefect_oneThreeFiveLowProfile_eq]
  unfold fourCellOddOneThreeFiveCombinedQuadratic
    fourCellOddOneThreeFiveCombined15
    fourCellOddOneThreeFiveCombined35
    fourCellOddOneThreeFiveCombined55
    fourCellOddOneThreeFiveLocalAlgebraicQuadratic
    fourCellOddLowLocalAlgebraicQuadratic
    fourCellOddLowCombined11 fourCellOddLowCombined13
    fourCellOddLowCombined33
    fourCellOddOneThreeFiveRegularQuadratic
  ring

/-- The complete finite `P₁/P₃/P₅` core-plus-local diagonal is
nonnegative after the actual full-width regular perturbation. -/
theorem fourCellOddHalfCoreReserve_add_localWidthDefect_oneThreeFive_nonneg
    (c d e : ℝ) :
    0 ≤ fourCellOddHalfCoreReserve
        (fourCellOddOneThreeFiveLowProfile c d e) +
      fourCellOddStripLocalWidthDefect
        (fourCellOddOneThreeFiveLowProfile c d e) := by
  rw [fourCellOddHalfCoreReserve_add_localWidthDefect_oneThreeFive_eq]
  exact fourCellOddOneThreeFiveCombined_sub_regular_nonneg c d e

/-- The signed `P₁/P₃/P₅`--tail row has no scalar-mass contribution and its
remaining wide-regular term is controlled by the product `L²` energy. -/
theorem fourCellOddSignedMassRegularBilinear_oneThreeFive_tail_sq_le_energy_mul
    (r : ℝ → ℝ) (hr : Continuous r) (hodd : Function.Odd r)
    (hone : centeredOddP1Coefficient r = 0)
    (hthree : centeredOddP3Coefficient r = 0)
    (hfive : centeredOddP5Coefficient r = 0)
    (c d e : ℝ) :
    fourCellOddSignedMassRegularBilinear
        (fourCellOddOneThreeFiveLowProfile c d e) r ^ 2 ≤
      (fourCellOperatorHalfWidth / 10) ^ 2 *
        factorTwoIntrinsicEnergy
          (fourCellOddOneThreeFiveLowProfile c d e) *
        factorTwoIntrinsicEnergy r := by
  let p : ℝ → ℝ := fourCellOddOneThreeFiveLowProfile c d e
  let I : ℝ := ∫ t : ℝ in 0..2,
    |factorTwoCenteredCorrelationBilinear p r t|
  let R : ℝ := ∫ t : ℝ in 0..2,
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
      factorTwoCenteredCorrelationBilinear p r t
  let Eₚ : ℝ := factorTwoIntrinsicEnergy p
  let Eᵣ : ℝ := factorTwoIntrinsicEnergy r
  have hp : Continuous p := by
    simpa only [p] using
      (contDiff_fourCellOddOneThreeFiveLowProfile c d e).continuous
  have hpodd : Function.Odd p := by
    simpa only [p] using odd_fourCellOddOneThreeFiveLowProfile c d e
  have hmass : (∫ x : ℝ in 0..1, p x * r x) = 0 := by
    simpa only [p] using
      integral_zero_one_oneThreeFiveLowProfile_mul_tail_eq_zero
        r hr hodd hone hthree hfive c d e
  have hregular : |R| ≤ (1 / 20 : ℝ) * I := by
    simpa only [R, I, p] using
      abs_fourCellRegularBilinear_le_one_twentieth_integral_abs
        p r hp hr hpodd hodd
  have hrow :
      fourCellOddSignedMassRegularBilinear p r =
        2 * fourCellOperatorHalfWidth * R := by
    unfold fourCellOddSignedMassRegularBilinear
    rw [hmass]
    dsimp only [R]
    ring
  have ha0 : 0 ≤ fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  have hI0 : 0 ≤ I := by
    dsimp only [I]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun _t _ht ↦ abs_nonneg _)
  have habs :
      |fourCellOddSignedMassRegularBilinear p r| ≤
        (fourCellOperatorHalfWidth / 10) * I := by
    rw [hrow, abs_mul, abs_of_nonneg (by positivity :
      0 ≤ 2 * fourCellOperatorHalfWidth)]
    nlinarith
  have hI : I ^ 2 ≤ Eₚ * Eᵣ := by
    dsimp only [I, Eₚ, Eᵣ]
    exact
      ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP67ResidualAnalyticSchurStructural.integral_abs_factorTwoCenteredCorrelationBilinear_sq_le_energy_mul
        p r hp hr
  calc
    fourCellOddSignedMassRegularBilinear p r ^ 2 =
        |fourCellOddSignedMassRegularBilinear p r| ^ 2 := by
      rw [sq_abs]
    _ ≤ ((fourCellOperatorHalfWidth / 10) * I) ^ 2 :=
      (sq_le_sq₀ (abs_nonneg _)
        (mul_nonneg (div_nonneg ha0 (by norm_num)) hI0)).2 habs
    _ = (fourCellOperatorHalfWidth / 10) ^ 2 * I ^ 2 := by ring
    _ ≤ (fourCellOperatorHalfWidth / 10) ^ 2 * (Eₚ * Eᵣ) :=
      mul_le_mul_of_nonneg_left hI (sq_nonneg _)
    _ = (fourCellOperatorHalfWidth / 10) ^ 2 * Eₚ * Eᵣ := by ring

/-- After the exact `P₁/P₃/P₅` raw-log orthogonality is used, the global
same-sign/reflected raw polarization vanishes.  The raw part of the Schur
mixed row is therefore exactly minus one half of the adverse endpoint-strip
raw polarization, with that singular form still retained intact. -/
theorem fourCellOddRawStripCancellationPolarization_oneThreeFive_tail_eq
    (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r)
    (hone : centeredOddP1Coefficient r = 0)
    (hthree : centeredOddP3Coefficient r = 0)
    (hfive : centeredOddP5Coefficient r = 0)
    (c d e : ℝ) :
    fourCellOddRawStripCancellationPolarization
        (fourCellOddOneThreeFiveLowProfile c d e) r =
      -(1 / 2 : ℝ) *
        fourCellOddEndpointStripOddRawPolarization
          (fourCellOddOneThreeFiveLowProfile c d e) r := by
  let p : ℝ → ℝ := fourCellOddOneThreeFiveLowProfile c d e
  have hpDiff : ContDiff ℝ 1 p := by
    simpa only [p] using contDiff_fourCellOddOneThreeFiveLowProfile c d e
  have hpLocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) p :=
    hpDiff.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1)
  have hrLocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) r :=
    hr.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1)
  have hpOdd : Function.Odd p := by
    simpa only [p] using odd_fourCellOddOneThreeFiveLowProfile c d e
  have hcross : centeredRawLogBilinear p r = 0 := by
    simpa only [p] using
      centeredRawLogBilinear_oneThreeFiveLowProfile_tail_eq_zero
        r hr.continuous hone hthree hfive c d e
  have henergy := centeredRawLogEnergy_add_eq_add_add_two_bilinear
    p r hpLocal hrLocal
  rw [hcross] at henergy
  norm_num at henergy
  have hfoldP := centeredRawLogEnergy_div_four_eq_positiveHalf_odd
    p hpLocal hpOdd
  have hfoldR := centeredRawLogEnergy_div_four_eq_positiveHalf_odd
    r hrLocal hodd
  have hfoldAdd := centeredRawLogEnergy_div_four_eq_positiveHalf_odd
    (p + r) (hpLocal.add hrLocal) (hpOdd.add hodd)
  change fourCellOddRawStripCancellationPolarization p r =
    -(1 / 2 : ℝ) * fourCellOddEndpointStripOddRawPolarization p r
  unfold fourCellOddRawStripCancellationPolarization
    fourCellOddRawStripCancellationReserve
    fourCellOddEndpointStripOddRawPolarization
  rw [← hfoldAdd, ← hfoldP, ← hfoldR, henergy]
  ring

/-- The adverse endpoint-strip raw row of the retained `P₁/P₃/P₅`
pivot is an explicit three-moment functional of the strip-odd tail. -/
theorem fourCellOddEndpointStripOddRawPolarization_oneThreeFive_eq_moments
    (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r) (c d e : ℝ) :
    fourCellOddEndpointStripOddRawPolarization
        (fourCellOddOneThreeFiveLowProfile c d e) r =
      (1 / 5 : ℝ) *
        (4 * (c / 5 + 84 * d / 125 + 276 * e / 625) *
            (∫ z : ℝ in -1..1,
              fourCellOddEndpointStripOdd r z * centeredP1 z) +
          (22 / 3 : ℝ) * (d / 125 + 84 * e / 625) *
            (∫ z : ℝ in -1..1,
              fourCellOddEndpointStripOdd r z * centeredP3 z) +
          (137 / 15 : ℝ) * (e / 3125) *
            (∫ z : ℝ in -1..1,
              fourCellOddEndpointStripOdd r z *
                factorTwoCenteredP5 z)) := by
  have hp := contDiff_fourCellOddOneThreeFiveLowProfile c d e
  have hrStrip : Continuous (fourCellOddEndpointStripOdd r) :=
    (contDiff_fourCellOddEndpointStripOdd_local r hr).continuous
  rw [fourCellOddEndpointStripOddRawPolarization_eq_bilinear
      _ _ hp hr,
    fourCellOddEndpointStripOdd_oneThreeFiveLowProfile_eq_lowProfile,
    centeredRawLogBilinear_oneThreeFiveLowProfile_eq_moments
      (fourCellOddEndpointStripOdd r) hrStrip]

/-- Exact nonsingular normal form of the retained endpoint mixed row.  The
global raw cross has vanished by `P₁/P₃/P₅` orthogonality, and the only
raw term left is the displayed three-moment endpoint-strip functional. -/
theorem fourCellOddRetainedEndpointBilinear_oneThreeFive_tail_eq_moments
    (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r)
    (hone : centeredOddP1Coefficient r = 0)
    (hthree : centeredOddP3Coefficient r = 0)
    (hfive : centeredOddP5Coefficient r = 0)
    (c d e : ℝ) :
    fourCellOddRetainedEndpointBilinear
        (fourCellOddOneThreeFiveLowProfile c d e) r =
      -(1 / 10 : ℝ) *
          (4 * (c / 5 + 84 * d / 125 + 276 * e / 625) *
              (∫ z : ℝ in -1..1,
                fourCellOddEndpointStripOdd r z * centeredP1 z) +
            (22 / 3 : ℝ) * (d / 125 + 84 * e / 625) *
              (∫ z : ℝ in -1..1,
                fourCellOddEndpointStripOdd r z * centeredP3 z) +
            (137 / 15 : ℝ) * (e / 3125) *
              (∫ z : ℝ in -1..1,
                fourCellOddEndpointStripOdd r z *
                  factorTwoCenteredP5 z)) +
        fourCellOddRetainedPrimePotentialBilinear
          (fourCellOddOneThreeFiveLowProfile c d e) r := by
  unfold fourCellOddRetainedEndpointBilinear
  rw [fourCellOddRawStripCancellationPolarization_oneThreeFive_tail_eq
      r hr hodd hone hthree hfive c d e,
    fourCellOddEndpointStripOddRawPolarization_oneThreeFive_eq_moments
      r hr c d e]
  ring

theorem fourCellOddOneThreeFiveLowProfile_one (c d e : ℝ) :
    fourCellOddOneThreeFiveLowProfile c d e 1 = c + d + e := by
  unfold fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
    centeredP1 centeredP3 factorTwoCenteredP5
  norm_num

theorem fourCellOddOneThreeFiveResidual_one_of_endpoint_zero
    (w : ℝ → ℝ) (hendpoint : w 1 = 0) :
    fourCellOddOneThreeFiveResidual w 1 =
      -(centeredOddP1Coefficient w + centeredOddP3Coefficient w +
        fourCellOddP5TailCoefficient w) := by
  have hreconstruct := congrFun (fourCellOddOneThreeFiveLowPart_add_residual w) 1
  rw [hendpoint] at hreconstruct
  unfold fourCellOddOneThreeFiveLowPart at hreconstruct
  change fourCellOddOneThreeFiveLowProfile
      (centeredOddP1Coefficient w) (centeredOddP3Coefficient w)
        (fourCellOddP5TailCoefficient w) 1 +
      fourCellOddOneThreeFiveResidual w 1 = 0 at hreconstruct
  rw [fourCellOddOneThreeFiveLowProfile_one] at hreconstruct
  linarith

/-- The complete quadratic target and its exact symmetric polarization. -/
def fourCellOddCoreLocalQuadratic (w : ℝ → ℝ) : ℝ :=
  fourCellOddHalfCoreReserve w + fourCellOddStripLocalWidthDefect w

def fourCellOddCoreLocalBilinear (u v : ℝ → ℝ) : ℝ :=
  fourCellOddRawStripCancellationPolarization u v +
    fourCellOddStripReducedBilinear u v

/-- Exact diagonal split into the complete retained positive endpoint form
and the only remaining signed scalar-mass/regular form. -/
theorem fourCellOddCoreLocalQuadratic_eq_retained_sub_signed
    (w : ℝ → ℝ) :
    fourCellOddCoreLocalQuadratic w =
      fourCellOddRetainedEndpointQuadratic w -
        fourCellOddSignedMassRegularQuadratic w := by
  unfold fourCellOddCoreLocalQuadratic
  rw [fourCellOddHalfCoreReserve_add_localWidthDefect_eq_raw_add_reduced,
    fourCellOddStripReducedRemainder_eq_retained_sub_signed]
  unfold fourCellOddRetainedEndpointQuadratic
    fourCellOddSignedMassRegularQuadratic
  ring

/-- Exact bilinear counterpart of the retained-minus-signed diagonal split.
-/
theorem fourCellOddCoreLocalBilinear_eq_retained_sub_signed
    (u v : ℝ → ℝ) :
    fourCellOddCoreLocalBilinear u v =
      fourCellOddRetainedEndpointBilinear u v -
        fourCellOddSignedMassRegularBilinear u v := by
  unfold fourCellOddCoreLocalBilinear
  rw [fourCellOddStripReducedBilinear_eq_retained_sub_signed]
  unfold fourCellOddRetainedEndpointBilinear
    fourCellOddSignedMassRegularBilinear
  ring

/-- Complete Schur absorption of the signed low--tail row.  Exact mass
orthogonality removes the scalar row; the centered regular fluctuation and
the retained `1/50` tail margin leave the finite cost `a² ‖p‖₂²`. -/
theorem fourCellOddSignedMassRegularBilinear_oneThreeFive_tail_sq_le_lowEnergy_mul_core
    (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r)
    (hone : centeredOddP1Coefficient r = 0)
    (hthree : centeredOddP3Coefficient r = 0)
    (hfive : centeredOddP5Coefficient r = 0)
    (c d e : ℝ) :
    fourCellOddSignedMassRegularBilinear
        (fourCellOddOneThreeFiveLowProfile c d e) r ^ 2 ≤
      fourCellOperatorHalfWidth ^ 2 *
        ((2 / 3 : ℝ) * c ^ 2 + (2 / 7 : ℝ) * d ^ 2 +
          (2 / 11 : ℝ) * e ^ 2) *
        fourCellOddCoreLocalQuadratic r := by
  let E : ℝ := (2 / 3 : ℝ) * c ^ 2 + (2 / 7 : ℝ) * d ^ 2 +
    (2 / 11 : ℝ) * e ^ 2
  have hsigned :=
    fourCellOddSignedMassRegularBilinear_oneThreeFive_tail_sq_le_energy_mul
      r hr.continuous hodd hone hthree hfive c d e
  rw [factorTwoIntrinsicEnergy_oneThreeFiveLowProfile] at hsigned
  change fourCellOddSignedMassRegularBilinear
      (fourCellOddOneThreeFiveLowProfile c d e) r ^ 2 ≤
    (fourCellOperatorHalfWidth / 10) ^ 2 * E *
      factorTwoIntrinsicEnergy r at hsigned
  have htail :=
    one_fiftieth_positiveHalfMass_le_core_add_localWidthDefect_of_P1
      r hr hodd hone
  change (1 / 50 : ℝ) * (∫ x : ℝ in 0..1, r x ^ 2) ≤
    fourCellOddCoreLocalQuadratic r at htail
  have hmass := integral_sq_eq_two_mul_positiveHalf
    r hr.continuous (Or.inr hodd)
  have henergy : factorTwoIntrinsicEnergy r =
      2 * ∫ x : ℝ in 0..1, r x ^ 2 := by
    unfold factorTwoIntrinsicEnergy
    exact hmass
  have henergyLe : factorTwoIntrinsicEnergy r ≤
      100 * fourCellOddCoreLocalQuadratic r := by
    rw [henergy]
    linarith
  have hE0 : 0 ≤ E := by
    dsimp only [E]
    positivity
  have hcoefficient0 :
      0 ≤ (fourCellOperatorHalfWidth / 10) ^ 2 * E :=
    mul_nonneg (sq_nonneg _) hE0
  have hmul := mul_le_mul_of_nonneg_left henergyLe hcoefficient0
  calc
    fourCellOddSignedMassRegularBilinear
        (fourCellOddOneThreeFiveLowProfile c d e) r ^ 2 ≤
      (fourCellOperatorHalfWidth / 10) ^ 2 * E *
        factorTwoIntrinsicEnergy r := hsigned
    _ ≤ (fourCellOperatorHalfWidth / 10) ^ 2 * E *
        (100 * fourCellOddCoreLocalQuadratic r) := hmul
    _ = fourCellOperatorHalfWidth ^ 2 * E *
        fourCellOddCoreLocalQuadratic r := by ring
    _ = fourCellOperatorHalfWidth ^ 2 *
        ((2 / 3 : ℝ) * c ^ 2 + (2 / 7 : ℝ) * d ^ 2 +
          (2 / 11 : ℝ) * e ^ 2) *
        fourCellOddCoreLocalQuadratic r := by rfl

/-- Exact form-level normal form of the `P₁/P₃/P₅`--tail mixed row.  The
global singular raw form has disappeared; the remaining terms are the
adverse endpoint-strip raw polarization and the uncollapsed prime,
potential, mass, and regular bilinear forms. -/
theorem fourCellOddCoreLocalBilinear_oneThreeFive_tail_eq_endpointForms
    (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r)
    (hone : centeredOddP1Coefficient r = 0)
    (hthree : centeredOddP3Coefficient r = 0)
    (hfive : centeredOddP5Coefficient r = 0)
    (c d e : ℝ) :
    fourCellOddCoreLocalBilinear
        (fourCellOddOneThreeFiveLowProfile c d e) r =
      -(1 / 2 : ℝ) *
          fourCellOddEndpointStripOddRawPolarization
            (fourCellOddOneThreeFiveLowProfile c d e) r +
        fourCellOddStripReducedBilinear
          (fourCellOddOneThreeFiveLowProfile c d e) r := by
  unfold fourCellOddCoreLocalBilinear
  rw [fourCellOddRawStripCancellationPolarization_oneThreeFive_tail_eq
    r hr hodd hone hthree hfive c d e]

/-! ### A structural `P₅/P₇` test of scalar tail norms -/

private theorem integral_polynomial_fifteen_local
    (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ l r : ℝ) :
    (∫ x : ℝ in l..r,
      a₀ * x ^ 0 + a₁ * x ^ 1 + a₂ * x ^ 2 + a₃ * x ^ 3 +
        a₄ * x ^ 4 + a₅ * x ^ 5 + a₆ * x ^ 6 + a₇ * x ^ 7 +
          a₈ * x ^ 8 + a₉ * x ^ 9 + a₁₀ * x ^ 10 +
            a₁₁ * x ^ 11 + a₁₂ * x ^ 12 + a₁₃ * x ^ 13 +
              a₁₄ * x ^ 14 + a₁₅ * x ^ 15) =
      a₀ * (r - l) + a₁ * (r ^ 2 - l ^ 2) / 2 +
        a₂ * (r ^ 3 - l ^ 3) / 3 + a₃ * (r ^ 4 - l ^ 4) / 4 +
          a₄ * (r ^ 5 - l ^ 5) / 5 + a₅ * (r ^ 6 - l ^ 6) / 6 +
            a₆ * (r ^ 7 - l ^ 7) / 7 + a₇ * (r ^ 8 - l ^ 8) / 8 +
              a₈ * (r ^ 9 - l ^ 9) / 9 +
                a₉ * (r ^ 10 - l ^ 10) / 10 +
                  a₁₀ * (r ^ 11 - l ^ 11) / 11 +
                    a₁₁ * (r ^ 12 - l ^ 12) / 12 +
                      a₁₂ * (r ^ 13 - l ^ 13) / 13 +
                        a₁₃ * (r ^ 14 - l ^ 14) / 14 +
                          a₁₄ * (r ^ 15 - l ^ 15) / 15 +
                            a₁₅ * (r ^ 16 - l ^ 16) / 16 := by
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) l r)
    (Continuous.intervalIntegrable (by fun_prop) l r)]
  repeat rw [intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  ring

private theorem integral_polynomial_nineteen_local
    (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a₁₇ a₁₈ a₁₉
      l r : ℝ) :
    (∫ x : ℝ in l..r,
      a₀ * x ^ 0 + a₁ * x ^ 1 + a₂ * x ^ 2 + a₃ * x ^ 3 +
        a₄ * x ^ 4 + a₅ * x ^ 5 + a₆ * x ^ 6 + a₇ * x ^ 7 +
          a₈ * x ^ 8 + a₉ * x ^ 9 + a₁₀ * x ^ 10 +
            a₁₁ * x ^ 11 + a₁₂ * x ^ 12 + a₁₃ * x ^ 13 +
              a₁₄ * x ^ 14 + a₁₅ * x ^ 15 + a₁₆ * x ^ 16 +
                a₁₇ * x ^ 17 + a₁₈ * x ^ 18 + a₁₉ * x ^ 19) =
      a₀ * (r - l) + a₁ * (r ^ 2 - l ^ 2) / 2 +
        a₂ * (r ^ 3 - l ^ 3) / 3 + a₃ * (r ^ 4 - l ^ 4) / 4 +
          a₄ * (r ^ 5 - l ^ 5) / 5 + a₅ * (r ^ 6 - l ^ 6) / 6 +
            a₆ * (r ^ 7 - l ^ 7) / 7 + a₇ * (r ^ 8 - l ^ 8) / 8 +
              a₈ * (r ^ 9 - l ^ 9) / 9 +
                a₉ * (r ^ 10 - l ^ 10) / 10 +
                  a₁₀ * (r ^ 11 - l ^ 11) / 11 +
                    a₁₁ * (r ^ 12 - l ^ 12) / 12 +
                      a₁₂ * (r ^ 13 - l ^ 13) / 13 +
                        a₁₃ * (r ^ 14 - l ^ 14) / 14 +
                          a₁₄ * (r ^ 15 - l ^ 15) / 15 +
                            a₁₅ * (r ^ 16 - l ^ 16) / 16 +
                              a₁₆ * (r ^ 17 - l ^ 17) / 17 +
                                a₁₇ * (r ^ 18 - l ^ 18) / 18 +
                                  a₁₈ * (r ^ 19 - l ^ 19) / 19 +
                                    a₁₉ * (r ^ 20 - l ^ 20) / 20 := by
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) l r)
    (Continuous.intervalIntegrable (by fun_prop) l r)]
  repeat rw [intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  ring

/-- The adjacent odd Legendre modes have a rational endpoint-potential
cross.  All logarithmic moments cancel in the Legendre combination. -/
private theorem integral_zero_one_endpointPotential_mul_P5_mul_P7 :
    (∫ x : ℝ in 0..1,
      yoshidaEndpointPotential x * factorTwoCenteredP5 x *
        factorTwoCenteredP7 x) = (1 / 26 : ℝ) := by
  let f : ℝ → ℝ := fun x ↦
    yoshidaEndpointPotential x * factorTwoCenteredP5 x *
      factorTwoCenteredP7 x
  have hf : IntervalIntegrable f volume (-1) 1 := by
    dsimp only [f]
    simpa only [mul_assoc] using
      intervalIntegrable_endpointPotential_mul
        (fun x : ℝ ↦ factorTwoCenteredP5 x * factorTwoCenteredP7 x)
        (by
          rw [show factorTwoCenteredP7 = fun x ↦
              (429 * x ^ 7 - 693 * x ^ 5 + 315 * x ^ 3 - 35 * x) / 16 by
            funext x
            exact factorTwoCenteredP7_eq x]
          unfold factorTwoCenteredP5
          fun_prop)
  have hfeven : Function.Even f := by
    intro x
    dsimp only [f]
    have hpotential : yoshidaEndpointPotential (-x) =
        yoshidaEndpointPotential x := by
      unfold yoshidaEndpointPotential
      congr 2
      ring
    rw [hpotential, odd_factorTwoCenteredP5 x,
      odd_factorTwoCenteredP7 x]
    ring
  have hfold := integral_neg_one_one_eq_two_mul_zero_one_of_even
    f hf hfeven
  have h2 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 2)
      volume (-1) 1 := by
    exact intervalIntegrable_endpointPotential_mul (fun x : ℝ ↦ x ^ 2)
      (by fun_prop)
  have h4 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 4)
      volume (-1) 1 := by
    exact intervalIntegrable_endpointPotential_mul (fun x : ℝ ↦ x ^ 4)
      (by fun_prop)
  have h6 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 6)
      volume (-1) 1 := by
    exact intervalIntegrable_endpointPotential_mul (fun x : ℝ ↦ x ^ 6)
      (by fun_prop)
  have h8 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 8)
      volume (-1) 1 := by
    exact intervalIntegrable_endpointPotential_mul (fun x : ℝ ↦ x ^ 8)
      (by fun_prop)
  have h10 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 10)
      volume (-1) 1 := by
    exact intervalIntegrable_endpointPotential_mul (fun x : ℝ ↦ x ^ 10)
      (by fun_prop)
  have h12 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 12)
      volume (-1) 1 := by
    exact intervalIntegrable_endpointPotential_mul (fun x : ℝ ↦ x ^ 12)
      (by fun_prop)
  have hfull : (∫ x : ℝ in -1..1, f x) = (1 / 13 : ℝ) := by
    dsimp only [f]
    rw [show (fun x : ℝ ↦
        yoshidaEndpointPotential x * factorTwoCenteredP5 x *
          factorTwoCenteredP7 x) = fun x ↦
        (27027 / 128 : ℝ) *
            (yoshidaEndpointPotential x * x ^ 12) -
          (73689 / 128 : ℝ) *
            (yoshidaEndpointPotential x * x ^ 10) +
          (37395 / 64 : ℝ) *
            (yoshidaEndpointPotential x * x ^ 8) -
          (17325 / 64 : ℝ) *
            (yoshidaEndpointPotential x * x ^ 6) +
          (7175 / 128 : ℝ) *
            (yoshidaEndpointPotential x * x ^ 4) -
          (525 / 128 : ℝ) *
            (yoshidaEndpointPotential x * x ^ 2) by
      funext x
      rw [factorTwoCenteredP7_eq]
      unfold factorTwoCenteredP5
      ring]
    rw [intervalIntegral.integral_sub
        (((((h12.const_mul (27027 / 128 : ℝ)).sub
          (h10.const_mul (73689 / 128 : ℝ))).add
          (h8.const_mul (37395 / 64 : ℝ))).sub
          (h6.const_mul (17325 / 64 : ℝ))).add
          (h4.const_mul (7175 / 128 : ℝ)))
        (h2.const_mul (525 / 128 : ℝ)),
      intervalIntegral.integral_add
        ((((h12.const_mul (27027 / 128 : ℝ)).sub
          (h10.const_mul (73689 / 128 : ℝ))).add
          (h8.const_mul (37395 / 64 : ℝ))).sub
          (h6.const_mul (17325 / 64 : ℝ)))
        (h4.const_mul (7175 / 128 : ℝ)),
      intervalIntegral.integral_sub
        (((h12.const_mul (27027 / 128 : ℝ)).sub
          (h10.const_mul (73689 / 128 : ℝ))).add
          (h8.const_mul (37395 / 64 : ℝ)))
        (h6.const_mul (17325 / 64 : ℝ)),
      intervalIntegral.integral_add
        ((h12.const_mul (27027 / 128 : ℝ)).sub
          (h10.const_mul (73689 / 128 : ℝ)))
        (h8.const_mul (37395 / 64 : ℝ)),
      intervalIntegral.integral_sub
        (h12.const_mul (27027 / 128 : ℝ))
        (h10.const_mul (73689 / 128 : ℝ))]
    repeat rw [intervalIntegral.integral_const_mul]
    rw [integral_endpointPotential_mul_pow_twelve,
      integral_endpointPotential_mul_pow_ten,
      integral_endpointPotential_mul_pow_eight,
      integral_endpointPotential_mul_pow_six,
      integral_endpointPotential_mul_pow_four,
      integral_endpointPotential_mul_sq]
    ring
  dsimp only [f] at hfold
  rw [hfull] at hfold
  linarith

private theorem fourCellOddEndpointStripEven_P5 (z : ℝ) :
    fourCellOddEndpointStripEven factorTwoCenteredP5 z =
      (63 / 1250 : ℝ) * z ^ 4 + (483 / 625 : ℝ) * z ^ 2 -
        2497 / 6250 := by
  unfold fourCellOddEndpointStripEven fourCellOddEndpointStripPullback
    factorTwoCenteredP5
  ring

private theorem fourCellOddEndpointStripOdd_P5 (z : ℝ) :
    fourCellOddEndpointStripOdd factorTwoCenteredP5 z =
      (63 / 25000 : ℝ) * z ^ 5 + (833 / 2500 : ℝ) * z ^ 3 +
        (1203 / 5000 : ℝ) * z := by
  unfold fourCellOddEndpointStripOdd fourCellOddEndpointStripPullback
    factorTwoCenteredP5
  ring

private theorem fourCellOddEndpointStripEven_P7 (z : ℝ) :
    fourCellOddEndpointStripEven factorTwoCenteredP7 z =
      (3003 / 312500 : ℝ) * z ^ 6 +
        (30723 / 62500 : ℝ) * z ^ 4 +
          (124929 / 312500 : ℝ) * z ^ 2 - 74891 / 312500 := by
  unfold fourCellOddEndpointStripEven fourCellOddEndpointStripPullback
  rw [factorTwoCenteredP7_eq, factorTwoCenteredP7_eq]
  ring

private theorem fourCellOddEndpointStripOdd_P7 (z : ℝ) :
    fourCellOddEndpointStripOdd factorTwoCenteredP7 z =
      (429 / 1250000 : ℝ) * z ^ 7 +
        (126819 / 1250000 : ℝ) * z ^ 5 +
          (253743 / 250000 : ℝ) * z ^ 3 -
            (972587 / 1250000 : ℝ) * z := by
  unfold fourCellOddEndpointStripOdd fourCellOddEndpointStripPullback
  rw [factorTwoCenteredP7_eq, factorTwoCenteredP7_eq]
  ring

private theorem fourCellOddEndpointStripEvenMassBilinear_P5_P7 :
    fourCellOddEndpointStripEvenMassBilinear
        factorTwoCenteredP5 factorTwoCenteredP7 =
      (29828192 / 1220703125 : ℝ) := by
  unfold fourCellOddEndpointStripEvenMassBilinear
  simp_rw [fourCellOddEndpointStripEven_P5,
    fourCellOddEndpointStripEven_P7]
  rw [show (fun z : ℝ ↦
      ((63 / 1250 : ℝ) * z ^ 4 + (483 / 625 : ℝ) * z ^ 2 -
          2497 / 6250) *
        ((3003 / 312500 : ℝ) * z ^ 6 +
          (30723 / 62500 : ℝ) * z ^ 4 +
          (124929 / 312500 : ℝ) * z ^ 2 - 74891 / 312500)) =
      fun z ↦
        (187002827 / 1953125000 : ℝ) * z ^ 0 + 0 * z ^ 1 +
          (-673671243 / 1953125000 : ℝ) * z ^ 2 + 0 * z ^ 3 +
          (784959 / 7812500 : ℝ) * z ^ 4 + 0 * z ^ 5 +
          (386907297 / 976562500 : ℝ) * z ^ 6 + 0 * z ^ 7 +
          (12578643 / 390625000 : ℝ) * z ^ 8 + 0 * z ^ 9 +
          (189189 / 390625000 : ℝ) * z ^ 10 + 0 * z ^ 11 +
          0 * z ^ 12 + 0 * z ^ 13 by
    funext z
    ring,
    integral_polynomial_thirteen]
  norm_num

private theorem fourCellOddEndpointStripOddMassBilinear_P5_P7 :
    fourCellOddEndpointStripOddMassBilinear
        factorTwoCenteredP5 factorTwoCenteredP7 =
      (-4789256 / 1220703125 : ℝ) := by
  unfold fourCellOddEndpointStripOddMassBilinear
  simp_rw [fourCellOddEndpointStripOdd_P5,
    fourCellOddEndpointStripOdd_P7]
  rw [show (fun z : ℝ ↦
      ((63 / 25000 : ℝ) * z ^ 5 + (833 / 2500 : ℝ) * z ^ 3 +
          (1203 / 5000 : ℝ) * z) *
        ((429 / 1250000 : ℝ) * z ^ 7 +
          (126819 / 1250000 : ℝ) * z ^ 5 +
          (253743 / 250000 : ℝ) * z ^ 3 -
          (972587 / 1250000 : ℝ) * z)) =
      fun z ↦
        0 * z ^ 0 + 0 * z ^ 1 +
          (-1170022161 / 6250000000 : ℝ) * z ^ 2 + 0 * z ^ 3 +
          (-94065797 / 6250000000 : ℝ) * z ^ 4 + 0 * z ^ 5 +
          (5634969627 / 15625000000 : ℝ) * z ^ 6 + 0 * z ^ 7 +
          (4555647 / 125000000 : ℝ) * z ^ 8 + 0 * z ^ 9 +
          (11563167 / 31250000000 : ℝ) * z ^ 10 + 0 * z ^ 11 +
          (27027 / 31250000000 : ℝ) * z ^ 12 + 0 * z ^ 13 by
    funext z
    ring,
    integral_polynomial_thirteen]
  norm_num

private theorem contDiff_factorTwoCenteredP7_local :
    ContDiff ℝ 1 factorTwoCenteredP7 := by
  rw [show factorTwoCenteredP7 = fun x ↦
      (429 * x ^ 7 - 693 * x ^ 5 + 315 * x ^ 3 - 35 * x) / 16 by
    funext x
    exact factorTwoCenteredP7_eq x]
  fun_prop

private theorem endpointStripOdd_P7_moments :
    (∫ z : ℝ in -1..1,
        fourCellOddEndpointStripOdd factorTwoCenteredP7 z * centeredP1 z) =
        (-6536 / 78125 : ℝ) ∧
      (∫ z : ℝ in -1..1,
        fourCellOddEndpointStripOdd factorTwoCenteredP7 z * centeredP3 z) =
        (10072 / 78125 : ℝ) ∧
      (∫ z : ℝ in -1..1,
        fourCellOddEndpointStripOdd factorTwoCenteredP7 z *
          factorTwoCenteredP5 z) = (184 / 78125 : ℝ) := by
  constructor
  · simp_rw [fourCellOddEndpointStripOdd_P7]
    unfold centeredP1
    rw [show (fun z : ℝ ↦
        ((429 / 1250000 : ℝ) * z ^ 7 +
          (126819 / 1250000 : ℝ) * z ^ 5 +
          (253743 / 250000 : ℝ) * z ^ 3 -
          (972587 / 1250000 : ℝ) * z) * z) = fun z ↦
        0 * z ^ 0 + 0 * z ^ 1 +
          (-972587 / 1250000 : ℝ) * z ^ 2 + 0 * z ^ 3 +
          (253743 / 250000 : ℝ) * z ^ 4 + 0 * z ^ 5 +
          (126819 / 1250000 : ℝ) * z ^ 6 + 0 * z ^ 7 +
          (429 / 1250000 : ℝ) * z ^ 8 + 0 * z ^ 9 +
          0 * z ^ 10 + 0 * z ^ 11 + 0 * z ^ 12 + 0 * z ^ 13 by
      funext z
      ring,
      integral_polynomial_thirteen]
    norm_num
  constructor
  · simp_rw [fourCellOddEndpointStripOdd_P7]
    unfold centeredP3
    rw [show (fun z : ℝ ↦
        ((429 / 1250000 : ℝ) * z ^ 7 +
          (126819 / 1250000 : ℝ) * z ^ 5 +
          (253743 / 250000 : ℝ) * z ^ 3 -
          (972587 / 1250000 : ℝ) * z) * ((5 * z ^ 3 - 3 * z) / 2)) =
        fun z ↦
          0 * z ^ 0 + 0 * z ^ 1 +
            (2917761 / 2500000 : ℝ) * z ^ 2 + 0 * z ^ 3 +
            (-216727 / 62500 : ℝ) * z ^ 4 + 0 * z ^ 5 +
            (2981559 / 1250000 : ℝ) * z ^ 6 + 0 * z ^ 7 +
            (79101 / 312500 : ℝ) * z ^ 8 + 0 * z ^ 9 +
            (429 / 500000 : ℝ) * z ^ 10 + 0 * z ^ 11 +
            0 * z ^ 12 + 0 * z ^ 13 by
      funext z
      ring,
      integral_polynomial_thirteen]
    norm_num
  · simp_rw [fourCellOddEndpointStripOdd_P7]
    unfold factorTwoCenteredP5
    rw [show (fun z : ℝ ↦
        ((429 / 1250000 : ℝ) * z ^ 7 +
          (126819 / 1250000 : ℝ) * z ^ 5 +
          (253743 / 250000 : ℝ) * z ^ 3 -
          (972587 / 1250000 : ℝ) * z) *
          ((63 * z ^ 5 - 70 * z ^ 3 + 15 * z) / 8)) = fun z ↦
        0 * z ^ 0 + 0 * z ^ 1 +
          (-2917761 / 2000000 : ℝ) * z ^ 2 + 0 * z ^ 3 +
          (17422363 / 2000000 : ℝ) * z ^ 4 + 0 * z ^ 5 +
          (-74090373 / 5000000 : ℝ) * z ^ 6 + 0 * z ^ 7 +
          (1421163 / 200000 : ℝ) * z ^ 8 + 0 * z ^ 9 +
          (7959567 / 10000000 : ℝ) * z ^ 10 + 0 * z ^ 11 +
          (27027 / 10000000 : ℝ) * z ^ 12 + 0 * z ^ 13 by
      funext z
      ring,
      integral_polynomial_thirteen]
    norm_num

private theorem fourCellOddEndpointStripOddRawPolarization_P5_P7 :
    fourCellOddEndpointStripOddRawPolarization
        factorTwoCenteredP5 factorTwoCenteredP7 =
      (-75829192 / 18310546875 : ℝ) := by
  have h :=
    fourCellOddEndpointStripOddRawPolarization_oneThreeFive_eq_moments
      factorTwoCenteredP7 contDiff_factorTwoCenteredP7_local 0 0 1
  have hp : fourCellOddOneThreeFiveLowProfile 0 0 1 =
      factorTwoCenteredP5 := by
    funext x
    unfold fourCellOddOneThreeFiveLowProfile
      factorTwoOddStructuralLowProfile centeredP1 centeredP3
    simp
  rw [hp] at h
  rcases endpointStripOdd_P7_moments with ⟨h1, h3, h5⟩
  rw [h1, h3, h5] at h
  norm_num at h ⊢
  exact h

private theorem centeredOddCoefficients_P7_eq_zero :
    centeredOddP1Coefficient factorTwoCenteredP7 = 0 ∧
      centeredOddP3Coefficient factorTwoCenteredP7 = 0 ∧
        centeredOddP5Coefficient factorTwoCenteredP7 = 0 := by
  have h1 := factorTwoCenteredP7_momentsVanishBelow 1 (by norm_num)
  have h3 := factorTwoCenteredP7_momentsVanishBelow 3 (by norm_num)
  have h5 := factorTwoCenteredP7_momentsVanishBelow 5 (by norm_num)
  rw [integral_centeredPullback_mul_shiftedLegendre_eq_neg_half_local
      1 centeredP1 factorTwoCenteredP7
        centeredPullback_centeredP1_eq_neg_shiftedLegendre_local] at h1
  rw [integral_centeredPullback_mul_shiftedLegendre_eq_neg_half_local
      3 centeredP3 factorTwoCenteredP7
        centeredPullback_centeredP3_eq_neg_shiftedLegendre_local] at h3
  rw [integral_centeredPullback_mul_shiftedLegendre_eq_neg_half_local
      5 factorTwoCenteredP5 factorTwoCenteredP7
        centeredPullback_factorTwoCenteredP5_eq_neg_shiftedLegendre] at h5
  unfold centeredOddP1Coefficient centeredOddP3Coefficient
    centeredOddP5Coefficient
  constructor
  · nlinarith
  constructor <;> nlinarith

private theorem fourCellOddRetainedPrimePotentialBilinear_P5_P7 :
    fourCellOddRetainedPrimePotentialBilinear
        factorTwoCenteredP5 factorTwoCenteredP7 =
      Real.sqrt 2 * Real.log 2 * (29828192 / 1220703125 : ℝ) +
        (2 - Real.sqrt 2 * Real.log 2) *
          (-4789256 / 1220703125 : ℝ) +
        (93 / 50 : ℝ) * (1 / 26) := by
  unfold fourCellOddRetainedPrimePotentialBilinear
  rw [fourCellOddEndpointStripEvenMassBilinear_P5_P7,
    fourCellOddEndpointStripOddMassBilinear_P5_P7,
    integral_zero_one_endpointPotential_mul_P5_mul_P7]

private theorem fourCellOddRetainedEndpointBilinear_P5_P7_eq :
    fourCellOddRetainedEndpointBilinear
        factorTwoCenteredP5 factorTwoCenteredP7 =
      (27001609440 * (Real.sqrt 2 * Real.log 2) + 62615554007) /
        952148437500 := by
  rcases centeredOddCoefficients_P7_eq_zero with ⟨h1, h3, h5⟩
  have hraw :=
    fourCellOddRawStripCancellationPolarization_oneThreeFive_tail_eq
      factorTwoCenteredP7 contDiff_factorTwoCenteredP7_local
        odd_factorTwoCenteredP7 h1 h3 h5 0 0 1
  have hp : fourCellOddOneThreeFiveLowProfile 0 0 1 =
      factorTwoCenteredP5 := by
    funext x
    unfold fourCellOddOneThreeFiveLowProfile
      factorTwoOddStructuralLowProfile centeredP1 centeredP3
    simp
  rw [hp] at hraw
  unfold fourCellOddRetainedEndpointBilinear
  rw [hraw, fourCellOddEndpointStripOddRawPolarization_P5_P7,
    fourCellOddRetainedPrimePotentialBilinear_P5_P7]
  ring

private theorem nine_hundredths_lt_fourCellOddRetainedEndpointBilinear_P5_P7 :
    (9 / 100 : ℝ) < fourCellOddRetainedEndpointBilinear
      factorTwoCenteredP5 factorTwoCenteredP7 := by
  rw [fourCellOddRetainedEndpointBilinear_P5_P7_eq]
  have hk := sqrt_two_mul_log_two_bounds.1
  nlinarith

private theorem abs_fourCellOddSignedMassRegularBilinear_P5_P7_lt_one_hundredth :
    |fourCellOddSignedMassRegularBilinear
        factorTwoCenteredP5 factorTwoCenteredP7| < (1 / 100 : ℝ) := by
  rcases centeredOddCoefficients_P7_eq_zero with ⟨h1, h3, h5⟩
  have hsigned :=
    fourCellOddSignedMassRegularBilinear_oneThreeFive_tail_sq_le_energy_mul
      factorTwoCenteredP7 continuous_factorTwoCenteredP7
        odd_factorTwoCenteredP7 h1 h3 h5 0 0 1
  have hp : fourCellOddOneThreeFiveLowProfile 0 0 1 =
      factorTwoCenteredP5 := by
    funext x
    unfold fourCellOddOneThreeFiveLowProfile
      factorTwoOddStructuralLowProfile centeredP1 centeredP3
    simp
  rw [factorTwoIntrinsicEnergy_oneThreeFiveLowProfile, hp,
    factorTwoCenteredP7_energy] at hsigned
  norm_num at hsigned
  have ha0 : 0 ≤ fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  have ha := fourCellOperatorHalfWidth_le_one_half
  have hsquare :
      fourCellOddSignedMassRegularBilinear
          factorTwoCenteredP5 factorTwoCenteredP7 ^ 2 <
        (1 / 100 : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (fourCellOperatorHalfWidth - 1 / 2)]
  rw [← sq_abs] at hsquare
  nlinarith [abs_nonneg (fourCellOddSignedMassRegularBilinear
    factorTwoCenteredP5 factorTwoCenteredP7)]

private theorem two_twenty_fifths_lt_fourCellOddCoreLocalBilinear_P5_P7 :
    (2 / 25 : ℝ) < fourCellOddCoreLocalBilinear
      factorTwoCenteredP5 factorTwoCenteredP7 := by
  rw [fourCellOddCoreLocalBilinear_eq_retained_sub_signed]
  have hretained :=
    nine_hundredths_lt_fourCellOddRetainedEndpointBilinear_P5_P7
  have hsigned :=
    abs_fourCellOddSignedMassRegularBilinear_P5_P7_lt_one_hundredth
  have hle := le_abs_self (fourCellOddSignedMassRegularBilinear
    factorTwoCenteredP5 factorTwoCenteredP7)
  linarith

private theorem integral_zero_three_fifths_P7_sq_eq :
    (∫ x : ℝ in 0..3 / 5, factorTwoCenteredP7 x ^ 2) =
      (4263562809 / 152587890625 : ℝ) := by
  rw [show (fun x : ℝ ↦ factorTwoCenteredP7 x ^ 2) = fun x ↦
      0 * x ^ 0 + 0 * x ^ 1 + (1225 / 256 : ℝ) * x ^ 2 +
        0 * x ^ 3 + (-11025 / 128 : ℝ) * x ^ 4 + 0 * x ^ 5 +
          (147735 / 256 : ℝ) * x ^ 6 + 0 * x ^ 7 +
            (-116655 / 64 : ℝ) * x ^ 8 + 0 * x ^ 9 +
              (750519 / 256 : ℝ) * x ^ 10 + 0 * x ^ 11 +
                (-297297 / 128 : ℝ) * x ^ 12 + 0 * x ^ 13 +
                  (184041 / 256 : ℝ) * x ^ 14 + 0 * x ^ 15 by
    funext x
    rw [factorTwoCenteredP7_eq]
    ring,
    integral_polynomial_fifteen_local]
  norm_num

private theorem integral_three_fifths_one_P7_sq_eq :
    (∫ x : ℝ in 3 / 5..1, factorTwoCenteredP7 x ^ 2) =
      (17726889698 / 457763671875 : ℝ) := by
  rw [show (fun x : ℝ ↦ factorTwoCenteredP7 x ^ 2) = fun x ↦
      0 * x ^ 0 + 0 * x ^ 1 + (1225 / 256 : ℝ) * x ^ 2 +
        0 * x ^ 3 + (-11025 / 128 : ℝ) * x ^ 4 + 0 * x ^ 5 +
          (147735 / 256 : ℝ) * x ^ 6 + 0 * x ^ 7 +
            (-116655 / 64 : ℝ) * x ^ 8 + 0 * x ^ 9 +
              (750519 / 256 : ℝ) * x ^ 10 + 0 * x ^ 11 +
                (-297297 / 128 : ℝ) * x ^ 12 + 0 * x ^ 13 +
                  (184041 / 256 : ℝ) * x ^ 14 + 0 * x ^ 15 by
    funext x
    rw [factorTwoCenteredP7_eq]
    ring,
    integral_polynomial_fifteen_local]
  norm_num

private theorem integral_three_fifths_one_P7_sq_div_x_eq :
    (∫ x : ℝ in 3 / 5..1, factorTwoCenteredP7 x ^ 2 / x) =
      (1959846008 / 42724609375 : ℝ) := by
  rw [show (fun x : ℝ ↦ factorTwoCenteredP7 x ^ 2 / x) = fun x ↦
      0 * x ^ 0 + (1225 / 256 : ℝ) * x ^ 1 + 0 * x ^ 2 +
        (-11025 / 128 : ℝ) * x ^ 3 + 0 * x ^ 4 +
          (147735 / 256 : ℝ) * x ^ 5 + 0 * x ^ 6 +
            (-116655 / 64 : ℝ) * x ^ 7 + 0 * x ^ 8 +
              (750519 / 256 : ℝ) * x ^ 9 + 0 * x ^ 10 +
                (-297297 / 128 : ℝ) * x ^ 11 + 0 * x ^ 12 +
                  (184041 / 256 : ℝ) * x ^ 13 + 0 * x ^ 14 +
                    0 * x ^ 15 by
    funext x
    rw [factorTwoCenteredP7_eq]
    by_cases hx : x = 0
    · simp [hx]
    · field_simp [hx]
      ring,
    integral_polynomial_fifteen_local]
  norm_num

private theorem integral_zero_one_endpointPotential_mul_P7_sq_eq :
    (∫ x : ℝ in 0..1,
      yoshidaEndpointPotential x * factorTwoCenteredP7 x ^ 2) =
      249383 / 2702700 - (1 / 15 : ℝ) * Real.log 2 := by
  let f : ℝ → ℝ := fun x ↦
    yoshidaEndpointPotential x * factorTwoCenteredP7 x ^ 2
  have hf : IntervalIntegrable f volume (-1) 1 := by
    dsimp only [f]
    exact intervalIntegrable_endpointPotential_mul_sq
      factorTwoCenteredP7 continuous_factorTwoCenteredP7
  have hfeven : Function.Even f := by
    intro x
    dsimp only [f]
    have hp : yoshidaEndpointPotential (-x) = yoshidaEndpointPotential x := by
      unfold yoshidaEndpointPotential
      congr 2
      ring
    rw [hp, odd_factorTwoCenteredP7]
    ring
  have hfold := integral_neg_one_one_eq_two_mul_zero_one_of_even f hf hfeven
  dsimp only [f] at hfold
  rw [integral_endpointPotential_mul_factorTwoCenteredP7_sq] at hfold
  linarith

private theorem six_twenty_fifths_lt_fourCellOddCoreLocalQuadratic_P5 :
    (6 / 25 : ℝ) < fourCellOddCoreLocalQuadratic factorTwoCenteredP5 := by
  have hp : fourCellOddOneThreeFiveLowProfile 0 0 1 =
      factorTwoCenteredP5 := by
    funext x
    unfold fourCellOddOneThreeFiveLowProfile
      factorTwoOddStructuralLowProfile centeredP1 centeredP3
    simp
  have hdiag :=
    fourCellOddHalfCoreReserve_add_localWidthDefect_oneThreeFive_eq 0 0 1
  rw [fourCellOddOneThreeFiveCombined_sub_regular_eq_perturbed] at hdiag
  unfold fourCellOddOneThreeFivePerturbedQuadratic at hdiag
  norm_num at hdiag
  rcases fourCellOddOneThreeFivePerturbed_entry_bounds with
    ⟨_h11lo, _h11hi, _h13lo, _h13hi, _h33lo, _h33hi,
      _h15lo, _h15hi, _h35lo, _h35hi, h55lo, _h55hi⟩
  rw [fourCellOddCoreLocalQuadratic, ← hp]
  linarith

private theorem one_twentieth_lt_fourCellOddCoreLocalQuadratic_P7 :
    (1 / 20 : ℝ) < fourCellOddCoreLocalQuadratic factorTwoCenteredP7 := by
  have htail := rawPrimeExactPotentialTailWeight_le_core_add_localWidthDefect_of_P1
    factorTwoCenteredP7 contDiff_factorTwoCenteredP7_local
      odd_factorTwoCenteredP7 centeredOddCoefficients_P7_eq_zero.1
  rw [integral_zero_three_fifths_P7_sq_eq,
    integral_three_fifths_one_P7_sq_eq,
    integral_three_fifths_one_P7_sq_div_x_eq,
    integral_zero_one_endpointPotential_mul_P7_sq_eq] at htail
  change _ ≤ fourCellOddCoreLocalQuadratic factorTwoCenteredP7 at htail
  have hlog := strict_log_two_bounds.2
  nlinarith

private theorem fourCellOddRetainedEndpointBilinear_P5_P7_lt_nineteen_two_hundredths :
    fourCellOddRetainedEndpointBilinear
      factorTwoCenteredP5 factorTwoCenteredP7 < (19 / 200 : ℝ) := by
  rw [fourCellOddRetainedEndpointBilinear_P5_P7_eq]
  have hk := sqrt_two_mul_log_two_bounds.2
  nlinarith

private theorem abs_fourCellOddCoreLocalBilinear_P5_P7_lt_twenty_one_two_hundredths :
    |fourCellOddCoreLocalBilinear
      factorTwoCenteredP5 factorTwoCenteredP7| < (21 / 200 : ℝ) := by
  rw [fourCellOddCoreLocalBilinear_eq_retained_sub_signed]
  have hlo := nine_hundredths_lt_fourCellOddRetainedEndpointBilinear_P5_P7
  have hhi :=
    fourCellOddRetainedEndpointBilinear_P5_P7_lt_nineteen_two_hundredths
  have hsigned :=
    abs_fourCellOddSignedMassRegularBilinear_P5_P7_lt_one_hundredth
  calc
    |fourCellOddRetainedEndpointBilinear factorTwoCenteredP5
          factorTwoCenteredP7 -
        fourCellOddSignedMassRegularBilinear factorTwoCenteredP5
          factorTwoCenteredP7| ≤
        |fourCellOddRetainedEndpointBilinear factorTwoCenteredP5
          factorTwoCenteredP7| +
        |fourCellOddSignedMassRegularBilinear factorTwoCenteredP5
          factorTwoCenteredP7| := abs_sub _ _
    _ = fourCellOddRetainedEndpointBilinear factorTwoCenteredP5
          factorTwoCenteredP7 +
        |fourCellOddSignedMassRegularBilinear factorTwoCenteredP5
          factorTwoCenteredP7| := by rw [abs_of_pos (by linarith)]
    _ < (19 / 200 : ℝ) + 1 / 100 := add_lt_add hhi hsigned
    _ = (21 / 200 : ℝ) := by norm_num

/-- The first genuine form-level tail certificate.  On the adjacent
`P₅/P₇` pair the complete core form, including its singular raw strip and
wide regular row, satisfies the exact Schur inequality. -/
theorem fourCellOddCoreLocalBilinear_P5_P7_sq_le_mul :
    fourCellOddCoreLocalBilinear
        factorTwoCenteredP5 factorTwoCenteredP7 ^ 2 ≤
      fourCellOddCoreLocalQuadratic factorTwoCenteredP5 *
        fourCellOddCoreLocalQuadratic factorTwoCenteredP7 := by
  let B := fourCellOddCoreLocalBilinear
    factorTwoCenteredP5 factorTwoCenteredP7
  let Q5 := fourCellOddCoreLocalQuadratic factorTwoCenteredP5
  let Q7 := fourCellOddCoreLocalQuadratic factorTwoCenteredP7
  have hQ5 : (6 / 25 : ℝ) < Q5 :=
    six_twenty_fifths_lt_fourCellOddCoreLocalQuadratic_P5
  have hQ7 : (1 / 20 : ℝ) < Q7 :=
    one_twentieth_lt_fourCellOddCoreLocalQuadratic_P7
  have hB : |B| < (21 / 200 : ℝ) :=
    abs_fourCellOddCoreLocalBilinear_P5_P7_lt_twenty_one_two_hundredths
  have hBsq : B ^ 2 < (21 / 200 : ℝ) ^ 2 := by
    rw [← sq_abs]
    exact (sq_lt_sq₀ (abs_nonneg B) (by norm_num)).2 hB
  have hQ5pos : 0 < Q5 := by linarith
  have hprod : (3 / 250 : ℝ) < Q5 * Q7 := by
    calc
      (3 / 250 : ℝ) = (6 / 25 : ℝ) * (1 / 20) := by norm_num
      _ < Q5 * (1 / 20 : ℝ) := mul_lt_mul_of_pos_right hQ5 (by norm_num)
      _ < Q5 * Q7 := mul_lt_mul_of_pos_left hQ7 hQ5pos
  dsimp only [B, Q5, Q7] at hBsq hprod ⊢
  nlinarith

/-! ### The adjacent `P₉` tail direction -/

private theorem contDiff_factorTwoCenteredP9_local :
    ContDiff ℝ 1 factorTwoCenteredP9 := by
  rw [show factorTwoCenteredP9 = fun x ↦
      (12155 * x ^ 9 - 25740 * x ^ 7 + 18018 * x ^ 5 -
        4620 * x ^ 3 + 315 * x) / 128 by
    funext x
    exact factorTwoCenteredP9_eq x]
  fun_prop

private theorem centeredOddCoefficients_P9_eq_zero :
    centeredOddP1Coefficient factorTwoCenteredP9 = 0 ∧
      centeredOddP3Coefficient factorTwoCenteredP9 = 0 ∧
        centeredOddP5Coefficient factorTwoCenteredP9 = 0 := by
  have h1 := factorTwoCenteredP9_momentsVanishBelow 1 (by norm_num)
  have h3 := factorTwoCenteredP9_momentsVanishBelow 3 (by norm_num)
  have h5 := factorTwoCenteredP9_momentsVanishBelow 5 (by norm_num)
  rw [integral_centeredPullback_mul_shiftedLegendre_eq_neg_half_local
      1 centeredP1 factorTwoCenteredP9
        centeredPullback_centeredP1_eq_neg_shiftedLegendre_local] at h1
  rw [integral_centeredPullback_mul_shiftedLegendre_eq_neg_half_local
      3 centeredP3 factorTwoCenteredP9
        centeredPullback_centeredP3_eq_neg_shiftedLegendre_local] at h3
  rw [integral_centeredPullback_mul_shiftedLegendre_eq_neg_half_local
      5 factorTwoCenteredP5 factorTwoCenteredP9
        centeredPullback_factorTwoCenteredP5_eq_neg_shiftedLegendre] at h5
  unfold centeredOddP1Coefficient centeredOddP3Coefficient
    centeredOddP5Coefficient
  constructor
  · nlinarith
  constructor <;> nlinarith

private theorem integral_zero_three_fifths_P9_sq_eq :
    (∫ x : ℝ in 0..3 / 5, factorTwoCenteredP9 x ^ 2) =
      (320073185043 / 14495849609375 : ℝ) := by
  rw [show (fun x : ℝ ↦ factorTwoCenteredP9 x ^ 2) = fun x ↦
      0 * x ^ 0 + 0 * x ^ 1 + (99225 / 16384 : ℝ) * x ^ 2 +
        0 * x ^ 3 + (-363825 / 2048 : ℝ) * x ^ 4 + 0 * x ^ 5 +
          (8173935 / 4096 : ℝ) * x ^ 6 + 0 * x ^ 7 +
            (-22837815 / 2048 : ℝ) * x ^ 8 + 0 * x ^ 9 +
              (285071787 / 8192 : ℝ) * x ^ 10 + 0 * x ^ 11 +
                (-129984855 / 2048 : ℝ) * x ^ 12 + 0 * x ^ 13 +
                  (275141295 / 4096 : ℝ) * x ^ 14 + 0 * x ^ 15 +
                    (-78217425 / 2048 : ℝ) * x ^ 16 + 0 * x ^ 17 +
                      (147744025 / 16384 : ℝ) * x ^ 18 + 0 * x ^ 19 by
    funext x
    rw [factorTwoCenteredP9_eq]
    ring,
    integral_polynomial_nineteen_local]
  norm_num

private theorem integral_three_fifths_one_P9_sq_eq :
    (∫ x : ℝ in 3 / 5..1, factorTwoCenteredP9 x ^ 2) =
      (442866268082 / 14495849609375 : ℝ) := by
  rw [show (fun x : ℝ ↦ factorTwoCenteredP9 x ^ 2) = fun x ↦
      0 * x ^ 0 + 0 * x ^ 1 + (99225 / 16384 : ℝ) * x ^ 2 +
        0 * x ^ 3 + (-363825 / 2048 : ℝ) * x ^ 4 + 0 * x ^ 5 +
          (8173935 / 4096 : ℝ) * x ^ 6 + 0 * x ^ 7 +
            (-22837815 / 2048 : ℝ) * x ^ 8 + 0 * x ^ 9 +
              (285071787 / 8192 : ℝ) * x ^ 10 + 0 * x ^ 11 +
                (-129984855 / 2048 : ℝ) * x ^ 12 + 0 * x ^ 13 +
                  (275141295 / 4096 : ℝ) * x ^ 14 + 0 * x ^ 15 +
                    (-78217425 / 2048 : ℝ) * x ^ 16 + 0 * x ^ 17 +
                      (147744025 / 16384 : ℝ) * x ^ 18 + 0 * x ^ 19 by
    funext x
    rw [factorTwoCenteredP9_eq]
    ring,
    integral_polynomial_nineteen_local]
  norm_num

private theorem integral_three_fifths_one_P9_sq_div_x_eq :
    (∫ x : ℝ in 3 / 5..1, factorTwoCenteredP9 x ^ 2 / x) =
      (343361778104 / 9613037109375 : ℝ) := by
  rw [show (fun x : ℝ ↦ factorTwoCenteredP9 x ^ 2 / x) = fun x ↦
      0 * x ^ 0 + (99225 / 16384 : ℝ) * x ^ 1 + 0 * x ^ 2 +
        (-363825 / 2048 : ℝ) * x ^ 3 + 0 * x ^ 4 +
          (8173935 / 4096 : ℝ) * x ^ 5 + 0 * x ^ 6 +
            (-22837815 / 2048 : ℝ) * x ^ 7 + 0 * x ^ 8 +
              (285071787 / 8192 : ℝ) * x ^ 9 + 0 * x ^ 10 +
                (-129984855 / 2048 : ℝ) * x ^ 11 + 0 * x ^ 12 +
                  (275141295 / 4096 : ℝ) * x ^ 13 + 0 * x ^ 14 +
                    (-78217425 / 2048 : ℝ) * x ^ 15 + 0 * x ^ 16 +
                      (147744025 / 16384 : ℝ) * x ^ 17 + 0 * x ^ 18 +
                        0 * x ^ 19 by
    funext x
    rw [factorTwoCenteredP9_eq]
    by_cases hx : x = 0
    · simp [hx]
    · field_simp [hx]
      ring,
    integral_polynomial_nineteen_local]
  norm_num

private theorem integral_zero_one_endpointPotential_mul_P9_sq_eq :
    (∫ x : ℝ in 0..1,
      yoshidaEndpointPotential x * factorTwoCenteredP9 x ^ 2) =
      32239703 / 442305864 - (1 / 19 : ℝ) * Real.log 2 := by
  let f : ℝ → ℝ := fun x ↦
    yoshidaEndpointPotential x * factorTwoCenteredP9 x ^ 2
  have hf : IntervalIntegrable f volume (-1) 1 := by
    dsimp only [f]
    exact intervalIntegrable_endpointPotential_mul_sq
      factorTwoCenteredP9 continuous_factorTwoCenteredP9
  have hfeven : Function.Even f := by
    intro x
    dsimp only [f]
    have hp : yoshidaEndpointPotential (-x) = yoshidaEndpointPotential x := by
      unfold yoshidaEndpointPotential
      congr 2
      ring
    rw [hp, odd_factorTwoCenteredP9]
    ring
  have hfold := integral_neg_one_one_eq_two_mul_zero_one_of_even f hf hfeven
  have hfull := factorTwoCenteredP9_potential_exact
  unfold factorTwoIntrinsicPotentialEnergy at hfull
  dsimp only [f] at hfold
  rw [hfull] at hfold
  linarith

private theorem one_twenty_fifth_lt_fourCellOddCoreLocalQuadratic_P9 :
    (1 / 25 : ℝ) < fourCellOddCoreLocalQuadratic factorTwoCenteredP9 := by
  have htail := rawPrimeExactPotentialTailWeight_le_core_add_localWidthDefect_of_P1
    factorTwoCenteredP9 contDiff_factorTwoCenteredP9_local
      odd_factorTwoCenteredP9 centeredOddCoefficients_P9_eq_zero.1
  rw [integral_zero_three_fifths_P9_sq_eq,
    integral_three_fifths_one_P9_sq_eq,
    integral_three_fifths_one_P9_sq_div_x_eq,
    integral_zero_one_endpointPotential_mul_P9_sq_eq] at htail
  change _ ≤ fourCellOddCoreLocalQuadratic factorTwoCenteredP9 at htail
  have hlog := strict_log_two_bounds.2
  nlinarith

private theorem fourCellOddEndpointStripEven_P9 (z : ℝ) :
    fourCellOddEndpointStripEven factorTwoCenteredP9 z =
      (21879 / 12500000 : ℝ) * z ^ 8 +
        (591591 / 3125000 : ℝ) * z ^ 6 +
          (8801793 / 6250000 : ℝ) * z ^ 4 -
            (4094541 / 3125000 : ℝ) * z ^ 2 +
              2348191 / 12500000 := by
  unfold fourCellOddEndpointStripEven fourCellOddEndpointStripPullback
  rw [factorTwoCenteredP9_eq, factorTwoCenteredP9_eq]
  ring

private theorem fourCellOddEndpointStripOdd_P9 (z : ℝ) :
    fourCellOddEndpointStripOdd factorTwoCenteredP9 z =
      (2431 / 50000000 : ℝ) * z ^ 9 +
        (317889 / 12500000 : ℝ) * z ^ 7 +
          (18711693 / 25000000 : ℝ) * z ^ 5 +
            (7297521 / 12500000 : ℝ) * z ^ 3 -
              (41734881 / 50000000 : ℝ) * z := by
  unfold fourCellOddEndpointStripOdd fourCellOddEndpointStripPullback
  rw [factorTwoCenteredP9_eq, factorTwoCenteredP9_eq]
  ring

private theorem fourCellOddEndpointStripEvenMassBilinear_P5_P9 :
    fourCellOddEndpointStripEvenMassBilinear
        factorTwoCenteredP5 factorTwoCenteredP9 =
      (-61266976 / 30517578125 : ℝ) := by
  unfold fourCellOddEndpointStripEvenMassBilinear
  simp_rw [fourCellOddEndpointStripEven_P5,
    fourCellOddEndpointStripEven_P9]
  rw [show (fun z : ℝ ↦
      ((63 / 1250 : ℝ) * z ^ 4 + (483 / 625 : ℝ) * z ^ 2 -
          2497 / 6250) *
        ((21879 / 12500000 : ℝ) * z ^ 8 +
          (591591 / 3125000 : ℝ) * z ^ 6 +
          (8801793 / 6250000 : ℝ) * z ^ 4 -
          (4094541 / 3125000 : ℝ) * z ^ 2 +
          2348191 / 12500000)) = fun z ↦
        (-5863432927 / 78125000000 : ℝ) * z ^ 0 + 0 * z ^ 1 +
          (26119019019 / 39062500000 : ℝ) * z ^ 2 + 0 * z ^ 3 +
          (-122323006197 / 78125000000 : ℝ) * z ^ 4 + 0 * z ^ 5 +
          (18489346953 / 19531250000 : ℝ) * z ^ 6 + 0 * z ^ 7 +
          (16920035847 / 78125000000 : ℝ) * z ^ 8 + 0 * z ^ 9 +
          (85108023 / 7812500000 : ℝ) * z ^ 10 + 0 * z ^ 11 +
          (1378377 / 15625000000 : ℝ) * z ^ 12 + 0 * z ^ 13 +
          0 * z ^ 14 + 0 * z ^ 15 by
    funext z
    ring,
    integral_polynomial_fifteen_local]
  norm_num

private theorem fourCellOddEndpointStripOddMassBilinear_P5_P9 :
    fourCellOddEndpointStripOddMassBilinear
        factorTwoCenteredP5 factorTwoCenteredP9 =
      (-143527592 / 30517578125 : ℝ) := by
  unfold fourCellOddEndpointStripOddMassBilinear
  simp_rw [fourCellOddEndpointStripOdd_P5,
    fourCellOddEndpointStripOdd_P9]
  rw [show (fun z : ℝ ↦
      ((63 / 25000 : ℝ) * z ^ 5 + (833 / 2500 : ℝ) * z ^ 3 +
          (1203 / 5000 : ℝ) * z) *
        ((2431 / 50000000 : ℝ) * z ^ 9 +
          (317889 / 12500000 : ℝ) * z ^ 7 +
          (18711693 / 25000000 : ℝ) * z ^ 5 +
          (7297521 / 12500000 : ℝ) * z ^ 3 -
          (41734881 / 50000000 : ℝ) * z)) = fun z ↦
        0 * z ^ 0 + 0 * z ^ 1 +
          (-50207061843 / 250000000000 : ℝ) * z ^ 2 + 0 * z ^ 3 +
          (-17207320347 / 125000000000 : ℝ) * z ^ 4 + 0 * z ^ 5 +
          (465625769007 / 1250000000000 : ℝ) * z ^ 6 + 0 * z ^ 7 +
          (80306047503 / 312500000000 : ℝ) * z ^ 8 + 0 * z ^ 9 +
          (12964357263 / 1250000000000 : ℝ) * z ^ 10 + 0 * z ^ 11 +
          (50179129 / 625000000000 : ℝ) * z ^ 12 + 0 * z ^ 13 +
          (153153 / 1250000000000 : ℝ) * z ^ 14 + 0 * z ^ 15 by
    funext z
    ring,
    integral_polynomial_fifteen_local]
  norm_num

private theorem endpointStripOdd_P9_moments :
    (∫ z : ℝ in -1..1,
        fourCellOddEndpointStripOdd factorTwoCenteredP9 z * centeredP1 z) =
        (-202024 / 1953125 : ℝ) ∧
      (∫ z : ℝ in -1..1,
        fourCellOddEndpointStripOdd factorTwoCenteredP9 z * centeredP3 z) =
        (321976 / 1953125 : ℝ) ∧
      (∫ z : ℝ in -1..1,
        fourCellOddEndpointStripOdd factorTwoCenteredP9 z *
          factorTwoCenteredP5 z) = (35608 / 1953125 : ℝ) := by
  constructor
  · simp_rw [fourCellOddEndpointStripOdd_P9]
    unfold centeredP1
    rw [show (fun z : ℝ ↦
        ((2431 / 50000000 : ℝ) * z ^ 9 +
          (317889 / 12500000 : ℝ) * z ^ 7 +
          (18711693 / 25000000 : ℝ) * z ^ 5 +
          (7297521 / 12500000 : ℝ) * z ^ 3 -
          (41734881 / 50000000 : ℝ) * z) * z) = fun z ↦
        0 * z ^ 0 + 0 * z ^ 1 +
          (-41734881 / 50000000 : ℝ) * z ^ 2 + 0 * z ^ 3 +
          (7297521 / 12500000 : ℝ) * z ^ 4 + 0 * z ^ 5 +
          (18711693 / 25000000 : ℝ) * z ^ 6 + 0 * z ^ 7 +
          (317889 / 12500000 : ℝ) * z ^ 8 + 0 * z ^ 9 +
          (2431 / 50000000 : ℝ) * z ^ 10 + 0 * z ^ 11 +
          0 * z ^ 12 + 0 * z ^ 13 + 0 * z ^ 14 + 0 * z ^ 15 by
      funext z
      ring,
      integral_polynomial_fifteen_local]
    norm_num
  constructor
  · simp_rw [fourCellOddEndpointStripOdd_P9]
    unfold centeredP3
    rw [show (fun z : ℝ ↦
        ((2431 / 50000000 : ℝ) * z ^ 9 +
          (317889 / 12500000 : ℝ) * z ^ 7 +
          (18711693 / 25000000 : ℝ) * z ^ 5 +
          (7297521 / 12500000 : ℝ) * z ^ 3 -
          (41734881 / 50000000 : ℝ) * z) *
            ((5 * z ^ 3 - 3 * z) / 2)) = fun z ↦
        0 * z ^ 0 + 0 * z ^ 1 +
          (125204643 / 100000000 : ℝ) * z ^ 2 + 0 * z ^ 3 +
          (-296244657 / 100000000 : ℝ) * z ^ 4 + 0 * z ^ 5 +
          (16840131 / 50000000 : ℝ) * z ^ 6 + 0 * z ^ 7 +
          (91651131 / 50000000 : ℝ) * z ^ 8 + 0 * z ^ 9 +
          (6350487 / 100000000 : ℝ) * z ^ 10 + 0 * z ^ 11 +
          (2431 / 20000000 : ℝ) * z ^ 12 + 0 * z ^ 13 +
          0 * z ^ 14 + 0 * z ^ 15 by
      funext z
      ring,
      integral_polynomial_fifteen_local]
    norm_num
  · simp_rw [fourCellOddEndpointStripOdd_P9]
    unfold factorTwoCenteredP5
    rw [show (fun z : ℝ ↦
        ((2431 / 50000000 : ℝ) * z ^ 9 +
          (317889 / 12500000 : ℝ) * z ^ 7 +
          (18711693 / 25000000 : ℝ) * z ^ 5 +
          (7297521 / 12500000 : ℝ) * z ^ 3 -
          (41734881 / 50000000 : ℝ) * z) *
            ((63 * z ^ 5 - 70 * z ^ 3 + 15 * z) / 8)) = fun z ↦
        0 * z ^ 0 + 0 * z ^ 1 +
          (-125204643 / 80000000 : ℝ) * z ^ 2 + 0 * z ^ 3 +
          (335929293 / 40000000 : ℝ) * z ^ 4 + 0 * z ^ 5 +
          (-4111252593 / 400000000 : ℝ) * z ^ 6 + 0 * z ^ 7 +
          (-190397097 / 100000000 : ℝ) * z ^ 8 + 0 * z ^ 9 +
          (2268700863 / 400000000 : ℝ) * z ^ 10 + 0 * z ^ 11 +
          (39968929 / 200000000 : ℝ) * z ^ 12 + 0 * z ^ 13 +
          (153153 / 400000000 : ℝ) * z ^ 14 + 0 * z ^ 15 by
      funext z
      ring,
      integral_polynomial_fifteen_local]
    norm_num

private theorem fourCellOddEndpointStripOddRawPolarization_P5_P9 :
    fourCellOddEndpointStripOddRawPolarization
        factorTwoCenteredP5 factorTwoCenteredP9 =
      (-1847417704 / 457763671875 : ℝ) := by
  have h :=
    fourCellOddEndpointStripOddRawPolarization_oneThreeFive_eq_moments
      factorTwoCenteredP9 contDiff_factorTwoCenteredP9_local 0 0 1
  have hp : fourCellOddOneThreeFiveLowProfile 0 0 1 =
      factorTwoCenteredP5 := by
    funext x
    unfold fourCellOddOneThreeFiveLowProfile
      factorTwoOddStructuralLowProfile centeredP1 centeredP3
    simp
  rw [hp] at h
  rcases endpointStripOdd_P9_moments with ⟨h1, h3, h5⟩
  rw [h1, h3, h5] at h
  norm_num at h ⊢
  exact h

private theorem integral_zero_one_endpointPotential_mul_P5_mul_P9 :
    (∫ x : ℝ in 0..1,
      yoshidaEndpointPotential x * factorTwoCenteredP5 x *
        factorTwoCenteredP9 x) = (1 / 60 : ℝ) := by
  have h5 : factorTwoCenteredP5 =
      fun x ↦ -(centeredShiftedLegendreReal 5).eval x := by
    funext x
    rw [eval_centeredShiftedLegendreReal]
    have h := centeredPullback_factorTwoCenteredP5_eq_neg_shiftedLegendre
      ((x + 1) / 2)
    unfold centeredPullback at h
    convert h using 1
    all_goals ring
  have h9 : factorTwoCenteredP9 =
      fun x ↦ -(centeredShiftedLegendreReal 9).eval x := by
    funext x
    rw [eval_centeredShiftedLegendreReal]
    rfl
  have hfull :=
    YoshidaEndpointPotentialLegendreOffDiagonalStructural.integral_endpointPotential_mul_centeredShiftedLegendreReal_of_even
    (m := 5) (n := 9) (by norm_num) (by norm_num)
  norm_num at hfull
  have hfullActual : (∫ x : ℝ in -1..1,
      yoshidaEndpointPotential x * factorTwoCenteredP5 x *
        factorTwoCenteredP9 x) = (1 / 30 : ℝ) := by
    rw [h5, h9]
    simpa only [mul_neg, neg_mul, neg_neg] using hfull
  let f : ℝ → ℝ := fun x ↦
    yoshidaEndpointPotential x * factorTwoCenteredP5 x *
      factorTwoCenteredP9 x
  have hf : IntervalIntegrable f volume (-1) 1 := by
    dsimp only [f]
    simpa only [mul_assoc] using
      intervalIntegrable_endpointPotential_mul
        (fun x : ℝ ↦ factorTwoCenteredP5 x * factorTwoCenteredP9 x)
        (continuous_factorTwoCenteredP5.mul continuous_factorTwoCenteredP9)
  have hfeven : Function.Even f := by
    intro x
    dsimp only [f]
    have hp : yoshidaEndpointPotential (-x) = yoshidaEndpointPotential x := by
      unfold yoshidaEndpointPotential
      congr 2
      ring
    rw [hp, odd_factorTwoCenteredP5, odd_factorTwoCenteredP9]
    ring
  have hfold := integral_neg_one_one_eq_two_mul_zero_one_of_even f hf hfeven
  dsimp only [f] at hfold
  rw [hfullActual] at hfold
  linarith

private theorem fourCellOddRetainedEndpointBilinear_P5_P9_eq :
    fourCellOddRetainedEndpointBilinear
        factorTwoCenteredP5 factorTwoCenteredP9 =
      -(1 / 2 : ℝ) * (-1847417704 / 457763671875) +
        Real.sqrt 2 * Real.log 2 * (-61266976 / 30517578125 : ℝ) +
        (2 - Real.sqrt 2 * Real.log 2) *
          (-143527592 / 30517578125 : ℝ) +
        (93 / 50 : ℝ) * (1 / 60) := by
  rcases centeredOddCoefficients_P9_eq_zero with ⟨h1, h3, h5⟩
  have hraw :=
    fourCellOddRawStripCancellationPolarization_oneThreeFive_tail_eq
      factorTwoCenteredP9 contDiff_factorTwoCenteredP9_local
        odd_factorTwoCenteredP9 h1 h3 h5 0 0 1
  have hp : fourCellOddOneThreeFiveLowProfile 0 0 1 =
      factorTwoCenteredP5 := by
    funext x
    unfold fourCellOddOneThreeFiveLowProfile
      factorTwoOddStructuralLowProfile centeredP1 centeredP3
    simp
  rw [hp] at hraw
  unfold fourCellOddRetainedEndpointBilinear
    fourCellOddRetainedPrimePotentialBilinear
  rw [hraw, fourCellOddEndpointStripOddRawPolarization_P5_P9,
    fourCellOddEndpointStripEvenMassBilinear_P5_P9,
    fourCellOddEndpointStripOddMassBilinear_P5_P9,
    integral_zero_one_endpointPotential_mul_P5_mul_P9]
  ring

private theorem fourCellOddRetainedEndpointBilinear_P5_P9_bounds :
    0 < fourCellOddRetainedEndpointBilinear
        factorTwoCenteredP5 factorTwoCenteredP9 ∧
      fourCellOddRetainedEndpointBilinear
        factorTwoCenteredP5 factorTwoCenteredP9 < (7 / 250 : ℝ) := by
  rw [fourCellOddRetainedEndpointBilinear_P5_P9_eq]
  rcases sqrt_two_mul_log_two_bounds with ⟨hlo, hhi⟩
  constructor <;> nlinarith

private theorem abs_fourCellOddSignedMassRegularBilinear_P5_P9_lt_seven_thousandths :
    |fourCellOddSignedMassRegularBilinear
        factorTwoCenteredP5 factorTwoCenteredP9| < (7 / 1000 : ℝ) := by
  rcases centeredOddCoefficients_P9_eq_zero with ⟨h1, h3, h5⟩
  have hsigned :=
    fourCellOddSignedMassRegularBilinear_oneThreeFive_tail_sq_le_energy_mul
      factorTwoCenteredP9 continuous_factorTwoCenteredP9
        odd_factorTwoCenteredP9 h1 h3 h5 0 0 1
  have hp : fourCellOddOneThreeFiveLowProfile 0 0 1 =
      factorTwoCenteredP5 := by
    funext x
    unfold fourCellOddOneThreeFiveLowProfile
      factorTwoOddStructuralLowProfile centeredP1 centeredP3
    simp
  rw [factorTwoIntrinsicEnergy_oneThreeFiveLowProfile, hp,
    factorTwoCenteredP9_energy] at hsigned
  norm_num at hsigned
  have ha0 : 0 ≤ fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  have ha := fourCellOperatorHalfWidth_le_one_half
  have hsquare :
      fourCellOddSignedMassRegularBilinear
          factorTwoCenteredP5 factorTwoCenteredP9 ^ 2 <
        (7 / 1000 : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (fourCellOperatorHalfWidth - 1 / 2)]
  rw [← sq_abs] at hsquare
  nlinarith [abs_nonneg (fourCellOddSignedMassRegularBilinear
    factorTwoCenteredP5 factorTwoCenteredP9)]

private theorem abs_fourCellOddCoreLocalBilinear_P5_P9_lt_seven_two_hundredths :
    |fourCellOddCoreLocalBilinear
      factorTwoCenteredP5 factorTwoCenteredP9| < (7 / 200 : ℝ) := by
  rw [fourCellOddCoreLocalBilinear_eq_retained_sub_signed]
  rcases fourCellOddRetainedEndpointBilinear_P5_P9_bounds with ⟨hlo, hhi⟩
  have hsigned :=
    abs_fourCellOddSignedMassRegularBilinear_P5_P9_lt_seven_thousandths
  calc
    |fourCellOddRetainedEndpointBilinear factorTwoCenteredP5
          factorTwoCenteredP9 -
        fourCellOddSignedMassRegularBilinear factorTwoCenteredP5
          factorTwoCenteredP9| ≤
        |fourCellOddRetainedEndpointBilinear factorTwoCenteredP5
          factorTwoCenteredP9| +
        |fourCellOddSignedMassRegularBilinear factorTwoCenteredP5
          factorTwoCenteredP9| := abs_sub _ _
    _ = fourCellOddRetainedEndpointBilinear factorTwoCenteredP5
          factorTwoCenteredP9 +
        |fourCellOddSignedMassRegularBilinear factorTwoCenteredP5
          factorTwoCenteredP9| := by rw [abs_of_pos hlo]
    _ < (7 / 250 : ℝ) + 7 / 1000 := add_lt_add hhi hsigned
    _ = (7 / 200 : ℝ) := by norm_num

/-- The farther adjacent tail mode also satisfies the honest complete-form
Schur inequality against the retained `P₅` pivot. -/
theorem fourCellOddCoreLocalBilinear_P5_P9_sq_le_mul :
    fourCellOddCoreLocalBilinear
        factorTwoCenteredP5 factorTwoCenteredP9 ^ 2 ≤
      fourCellOddCoreLocalQuadratic factorTwoCenteredP5 *
        fourCellOddCoreLocalQuadratic factorTwoCenteredP9 := by
  let B := fourCellOddCoreLocalBilinear
    factorTwoCenteredP5 factorTwoCenteredP9
  let Q5 := fourCellOddCoreLocalQuadratic factorTwoCenteredP5
  let Q9 := fourCellOddCoreLocalQuadratic factorTwoCenteredP9
  have hQ5 : (6 / 25 : ℝ) < Q5 :=
    six_twenty_fifths_lt_fourCellOddCoreLocalQuadratic_P5
  have hQ9 : (1 / 25 : ℝ) < Q9 :=
    one_twenty_fifth_lt_fourCellOddCoreLocalQuadratic_P9
  have hB : |B| < (7 / 200 : ℝ) :=
    abs_fourCellOddCoreLocalBilinear_P5_P9_lt_seven_two_hundredths
  have hBsq : B ^ 2 < (7 / 200 : ℝ) ^ 2 := by
    rw [← sq_abs]
    exact (sq_lt_sq₀ (abs_nonneg B) (by norm_num)).2 hB
  have hQ5pos : 0 < Q5 := by linarith
  have hprod : (6 / 625 : ℝ) < Q5 * Q9 := by
    calc
      (6 / 625 : ℝ) = (6 / 25 : ℝ) * (1 / 25) := by norm_num
      _ < Q5 * (1 / 25 : ℝ) := mul_lt_mul_of_pos_right hQ5 (by norm_num)
      _ < Q5 * Q9 := mul_lt_mul_of_pos_left hQ9 hQ5pos
  dsimp only [B, Q5, Q9] at hBsq hprod ⊢
  nlinarith

private theorem endpointStripOdd_P9_P7_moment :
    (∫ z : ℝ in -1..1,
      fourCellOddEndpointStripOdd factorTwoCenteredP9 z *
        factorTwoCenteredP7 z) = (248 / 1953125 : ℝ) := by
  simp_rw [fourCellOddEndpointStripOdd_P9, factorTwoCenteredP7_eq]
  rw [show (fun z : ℝ ↦
      ((2431 / 50000000 : ℝ) * z ^ 9 +
        (317889 / 12500000 : ℝ) * z ^ 7 +
        (18711693 / 25000000 : ℝ) * z ^ 5 +
        (7297521 / 12500000 : ℝ) * z ^ 3 -
        (41734881 / 50000000 : ℝ) * z) *
          ((429 * z ^ 7 - 693 * z ^ 5 + 315 * z ^ 3 - 35 * z) / 16)) =
      fun z ↦
        0 * z ^ 0 + 0 * z ^ 1 +
          (292144167 / 160000000 : ℝ) * z ^ 2 + 0 * z ^ 3 +
          (-2833628091 / 160000000 : ℝ) * z ^ 4 + 0 * z ^ 5 +
          (36807330483 / 800000000 : ℝ) * z ^ 6 + 0 * z ^ 7 +
          (-26389130031 / 800000000 : ℝ) * z ^ 8 + 0 * z ^ 9 +
          (-13011405407 / 800000000 : ℝ) * z ^ 10 + 0 * z ^ 11 +
          (15174210051 / 800000000 : ℝ) * z ^ 12 + 0 * z ^ 13 +
          (543812841 / 800000000 : ℝ) * z ^ 14 + 0 * z ^ 15 +
          (1042899 / 800000000 : ℝ) * z ^ 16 + 0 * z ^ 17 +
          0 * z ^ 18 + 0 * z ^ 19 by
    funext z
    ring,
    integral_polynomial_nineteen_local]
  norm_num

private theorem fourCellOddEndpointStripOdd_P7_eq_legendreFour :
    fourCellOddEndpointStripOdd factorTwoCenteredP7 =
      fourCellOddOneThreeFiveLowProfile
        (-9804 / 78125) (35252 / 78125) (1012 / 78125) +
        fun x ↦ (1 / 78125 : ℝ) * factorTwoCenteredP7 x := by
  funext x
  rw [fourCellOddEndpointStripOdd_P7]
  unfold fourCellOddOneThreeFiveLowProfile
    factorTwoOddStructuralLowProfile centeredP1 centeredP3
    factorTwoCenteredP5
  simp only [Pi.add_apply]
  rw [factorTwoCenteredP7_eq]
  ring

private theorem centeredRawLogBilinear_endpointStripOdd_P7_P9_eq :
    centeredRawLogBilinear
        (fourCellOddEndpointStripOdd factorTwoCenteredP7)
        (fourCellOddEndpointStripOdd factorTwoCenteredP9) =
      (3202052575432 / 5340576171875 : ℝ) := by
  let p : ℝ[X] := -(
    (-9804 / 78125 : ℝ) • shiftedLegendreReal 1 +
      (35252 / 78125 : ℝ) • shiftedLegendreReal 3 +
      (1012 / 78125 : ℝ) • shiftedLegendreReal 5 +
      (1 / 78125 : ℝ) • shiftedLegendreReal 7)
  let r : ℝ → ℝ := fourCellOddEndpointStripOdd factorTwoCenteredP9
  have hmode (t : ℝ) :
      centeredPullback (fourCellOddEndpointStripOdd factorTwoCenteredP7) t =
        p.eval t := by
    have h1 := centeredPullback_centeredP1_eq_neg_shiftedLegendre_local t
    have h3 := centeredPullback_centeredP3_eq_neg_shiftedLegendre_local t
    have h5 := centeredPullback_factorTwoCenteredP5_eq_neg_shiftedLegendre t
    have h7 := centeredPullback_factorTwoCenteredP7 t
    have hdecomp := congrFun fourCellOddEndpointStripOdd_P7_eq_legendreFour
      (2 * t - 1)
    dsimp only [p]
    simp only [Polynomial.eval_neg, Polynomial.eval_add,
      Polynomial.eval_smul, smul_eq_mul]
    unfold centeredPullback at h1 h3 h5 h7 ⊢
    rw [hdecomp]
    simp only [Pi.add_apply]
    unfold fourCellOddOneThreeFiveLowProfile
      factorTwoOddStructuralLowProfile
    rw [h1, h3, h5, h7]
    ring
  have hunitOne : (∫ t : unitInterval,
      centeredPullback r (t : ℝ) *
        (shiftedLegendreReal 1).eval (t : ℝ)) =
      -(1 / 2 : ℝ) * (-202024 / 1953125) := by
    have h := integral_centeredPullback_mul_shiftedLegendre_eq_neg_half_local
      1 centeredP1 r centeredPullback_centeredP1_eq_neg_shiftedLegendre_local
    rw [endpointStripOdd_P9_moments.1] at h
    exact h
  have hunitThree : (∫ t : unitInterval,
      centeredPullback r (t : ℝ) *
        (shiftedLegendreReal 3).eval (t : ℝ)) =
      -(1 / 2 : ℝ) * (321976 / 1953125) := by
    have h := integral_centeredPullback_mul_shiftedLegendre_eq_neg_half_local
      3 centeredP3 r centeredPullback_centeredP3_eq_neg_shiftedLegendre_local
    rw [endpointStripOdd_P9_moments.2.1] at h
    exact h
  have hunitFive : (∫ t : unitInterval,
      centeredPullback r (t : ℝ) *
        (shiftedLegendreReal 5).eval (t : ℝ)) =
      -(1 / 2 : ℝ) * (35608 / 1953125) := by
    have h := integral_centeredPullback_mul_shiftedLegendre_eq_neg_half_local
      5 factorTwoCenteredP5 r
        centeredPullback_factorTwoCenteredP5_eq_neg_shiftedLegendre
    rw [endpointStripOdd_P9_moments.2.2] at h
    exact h
  have hunitSeven : (∫ t : unitInterval,
      centeredPullback r (t : ℝ) *
        (shiftedLegendreReal 7).eval (t : ℝ)) =
      -(1 / 2 : ℝ) * (248 / 1953125) := by
    have h := integral_centeredPullback_mul_shiftedLegendre_eq_neg_half_local
      7 factorTwoCenteredP7 r centeredPullback_factorTwoCenteredP7
    rw [endpointStripOdd_P9_P7_moment] at h
    exact h
  have hpLog : shiftedLogKernel p = -(
      (-9804 / 78125 : ℝ) •
          (Polynomial.C (2 * (harmonic 1 : ℝ)) * shiftedLegendreReal 1) +
        (35252 / 78125 : ℝ) •
          (Polynomial.C (2 * (harmonic 3 : ℝ)) * shiftedLegendreReal 3) +
        (1012 / 78125 : ℝ) •
          (Polynomial.C (2 * (harmonic 5 : ℝ)) * shiftedLegendreReal 5) +
        (1 / 78125 : ℝ) •
          (Polynomial.C (2 * (harmonic 7 : ℝ)) * shiftedLegendreReal 7)) := by
    dsimp only [p]
    rw [map_neg, map_add, map_add, map_add,
      map_smul, map_smul, map_smul, map_smul,
      shiftedLogKernel_shiftedLegendreReal,
      shiftedLogKernel_shiftedLegendreReal,
      shiftedLogKernel_shiftedLegendreReal,
      shiftedLogKernel_shiftedLegendreReal]
  have hrbase : Continuous r := by
    dsimp only [r]
    exact (contDiff_fourCellOddEndpointStripOdd_local
      factorTwoCenteredP9 contDiff_factorTwoCenteredP9_local).continuous
  have hrcont : Continuous (fun t : unitInterval ↦
      centeredPullback r (t : ℝ)) := by
    unfold centeredPullback
    exact hrbase.comp (by fun_prop)
  have hInt (n : ℕ) : Integrable (fun t : unitInterval ↦
      centeredPullback r (t : ℝ) *
        (shiftedLegendreReal n).eval (t : ℝ)) :=
    (hrcont.mul ((shiftedLegendreReal n).continuous.comp
      continuous_subtype_val)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hpair : (∫ t : unitInterval,
      centeredPullback r (t : ℝ) * (shiftedLogKernel p).eval (t : ℝ)) =
      (800513143858 / 5340576171875 : ℝ) := by
    rw [hpLog]
    simp only [Polynomial.eval_neg, Polynomial.eval_add,
      Polynomial.eval_smul, Polynomial.eval_mul, Polynomial.eval_C,
      smul_eq_mul]
    rw [show (fun t : unitInterval ↦ centeredPullback r (t : ℝ) *
        -((-9804 / 78125 : ℝ) *
            (2 * (harmonic 1 : ℝ) * (shiftedLegendreReal 1).eval (t : ℝ)) +
          (35252 / 78125 : ℝ) *
            (2 * (harmonic 3 : ℝ) * (shiftedLegendreReal 3).eval (t : ℝ)) +
          (1012 / 78125 : ℝ) *
            (2 * (harmonic 5 : ℝ) * (shiftedLegendreReal 5).eval (t : ℝ)) +
          (1 / 78125 : ℝ) *
            (2 * (harmonic 7 : ℝ) * (shiftedLegendreReal 7).eval (t : ℝ)))) =
        fun t : unitInterval ↦
          (19608 / 78125 * (harmonic 1 : ℝ)) *
              (centeredPullback r (t : ℝ) *
                (shiftedLegendreReal 1).eval (t : ℝ)) +
          (((-70504 / 78125 : ℝ) * harmonic 3) *
              (centeredPullback r (t : ℝ) *
                (shiftedLegendreReal 3).eval (t : ℝ)) +
          (((-2024 / 78125 : ℝ) * harmonic 5) *
              (centeredPullback r (t : ℝ) *
                (shiftedLegendreReal 5).eval (t : ℝ)) +
          ((-2 / 78125 : ℝ) * harmonic 7) *
              (centeredPullback r (t : ℝ) *
                (shiftedLegendreReal 7).eval (t : ℝ)))) by
      funext t
      ring]
    calc
      _ = (∫ t : unitInterval,
            (19608 / 78125 * (harmonic 1 : ℝ)) *
              (centeredPullback r (t : ℝ) *
                (shiftedLegendreReal 1).eval (t : ℝ))) +
          ∫ t : unitInterval,
            ((-70504 / 78125 : ℝ) * harmonic 3) *
                (centeredPullback r (t : ℝ) *
                  (shiftedLegendreReal 3).eval (t : ℝ)) +
              (((-2024 / 78125 : ℝ) * harmonic 5) *
                  (centeredPullback r (t : ℝ) *
                    (shiftedLegendreReal 5).eval (t : ℝ)) +
                ((-2 / 78125 : ℝ) * harmonic 7) *
                  (centeredPullback r (t : ℝ) *
                    (shiftedLegendreReal 7).eval (t : ℝ))) := by
            exact integral_add
              ((hInt 1).const_mul
                (19608 / 78125 * (harmonic 1 : ℝ)))
              (((hInt 3).const_mul
                  ((-70504 / 78125 : ℝ) * harmonic 3)).add
                (((hInt 5).const_mul
                    ((-2024 / 78125 : ℝ) * harmonic 5)).add
                  ((hInt 7).const_mul
                    ((-2 / 78125 : ℝ) * harmonic 7))))
      _ = (∫ t : unitInterval,
            (19608 / 78125 * (harmonic 1 : ℝ)) *
              (centeredPullback r (t : ℝ) *
                (shiftedLegendreReal 1).eval (t : ℝ))) +
          ((∫ t : unitInterval,
              ((-70504 / 78125 : ℝ) * harmonic 3) *
                (centeredPullback r (t : ℝ) *
                  (shiftedLegendreReal 3).eval (t : ℝ))) +
            ∫ t : unitInterval,
              ((-2024 / 78125 : ℝ) * harmonic 5) *
                  (centeredPullback r (t : ℝ) *
                    (shiftedLegendreReal 5).eval (t : ℝ)) +
                ((-2 / 78125 : ℝ) * harmonic 7) *
                  (centeredPullback r (t : ℝ) *
                    (shiftedLegendreReal 7).eval (t : ℝ))) := by
            congr 1
            exact integral_add
              ((hInt 3).const_mul
                ((-70504 / 78125 : ℝ) * harmonic 3))
              (((hInt 5).const_mul
                  ((-2024 / 78125 : ℝ) * harmonic 5)).add
                ((hInt 7).const_mul
                  ((-2 / 78125 : ℝ) * harmonic 7)))
      _ = (∫ t : unitInterval,
            (19608 / 78125 * (harmonic 1 : ℝ)) *
              (centeredPullback r (t : ℝ) *
                (shiftedLegendreReal 1).eval (t : ℝ))) +
          ((∫ t : unitInterval,
              ((-70504 / 78125 : ℝ) * harmonic 3) *
                (centeredPullback r (t : ℝ) *
                  (shiftedLegendreReal 3).eval (t : ℝ))) +
            ((∫ t : unitInterval,
                ((-2024 / 78125 : ℝ) * harmonic 5) *
                  (centeredPullback r (t : ℝ) *
                    (shiftedLegendreReal 5).eval (t : ℝ))) +
              ∫ t : unitInterval,
                ((-2 / 78125 : ℝ) * harmonic 7) *
                  (centeredPullback r (t : ℝ) *
                    (shiftedLegendreReal 7).eval (t : ℝ)))) := by
            congr 1
            congr 1
            exact integral_add
              ((hInt 5).const_mul
                ((-2024 / 78125 : ℝ) * harmonic 5))
              ((hInt 7).const_mul
                ((-2 / 78125 : ℝ) * harmonic 7))
      _ = (800513143858 / 5340576171875 : ℝ) := by
            repeat rw [integral_const_mul]
            rw [hunitOne, hunitThree, hunitFive, hunitSeven]
            norm_num [harmonic, Finset.sum_range_succ]
  have h := centeredRawLogBilinear_polynomialMode_eq_four_mul_pair
    p (fourCellOddEndpointStripOdd factorTwoCenteredP7) r
      hrbase hmode
  rw [hpair] at h
  dsimp only [r] at h ⊢
  linarith

private theorem fourCellOddEndpointStripOddRawPolarization_P7_P9 :
    fourCellOddEndpointStripOddRawPolarization
        factorTwoCenteredP7 factorTwoCenteredP9 =
      (3202052575432 / 26702880859375 : ℝ) := by
  rw [fourCellOddEndpointStripOddRawPolarization_eq_bilinear
    factorTwoCenteredP7 factorTwoCenteredP9
      contDiff_factorTwoCenteredP7_local contDiff_factorTwoCenteredP9_local,
    centeredRawLogBilinear_endpointStripOdd_P7_P9_eq]
  ring

private theorem fourCellOddEndpointStripEvenMassBilinear_P7_P9 :
    fourCellOddEndpointStripEvenMassBilinear
        factorTwoCenteredP7 factorTwoCenteredP9 =
      (2113714048 / 762939453125 : ℝ) := by
  unfold fourCellOddEndpointStripEvenMassBilinear
  simp_rw [fourCellOddEndpointStripEven_P7,
    fourCellOddEndpointStripEven_P9]
  rw [show (fun z : ℝ ↦
      ((3003 / 312500 : ℝ) * z ^ 6 +
          (30723 / 62500 : ℝ) * z ^ 4 +
          (124929 / 312500 : ℝ) * z ^ 2 - 74891 / 312500) *
        ((21879 / 12500000 : ℝ) * z ^ 8 +
          (591591 / 3125000 : ℝ) * z ^ 6 +
          (8801793 / 6250000 : ℝ) * z ^ 4 -
          (4094541 / 3125000 : ℝ) * z ^ 2 +
          2348191 / 12500000)) = fun z ↦
        (-175858372181 / 3906250000000 : ℝ) * z ^ 0 + 0 * z ^ 1 +
          (1519934233563 / 3906250000000 : ℝ) * z ^ 2 + 0 * z ^ 3 +
          (-3003740449017 / 3906250000000 : ℝ) * z ^ 4 + 0 * z ^ 5 +
          (-486901016217 / 3906250000000 : ℝ) * z ^ 6 + 0 * z ^ 7 +
          (589796036973 / 781250000000 : ℝ) * z ^ 8 + 0 * z ^ 9 +
          (419105896209 / 3906250000000 : ℝ) * z ^ 10 + 0 * z ^ 11 +
          (10467133677 / 3906250000000 : ℝ) * z ^ 12 + 0 * z ^ 13 +
          (65702637 / 3906250000000 : ℝ) * z ^ 14 + 0 * z ^ 15 +
          0 * z ^ 16 + 0 * z ^ 17 + 0 * z ^ 18 + 0 * z ^ 19 by
    funext z
    ring,
    integral_polynomial_nineteen_local]
  norm_num

private theorem fourCellOddEndpointStripOddMassBilinear_P7_P9 :
    fourCellOddEndpointStripOddMassBilinear
        factorTwoCenteredP7 factorTwoCenteredP9 =
      (13366976792 / 762939453125 : ℝ) := by
  unfold fourCellOddEndpointStripOddMassBilinear
  simp_rw [fourCellOddEndpointStripOdd_P7,
    fourCellOddEndpointStripOdd_P9]
  rw [show (fun z : ℝ ↦
      ((429 / 1250000 : ℝ) * z ^ 7 +
          (126819 / 1250000 : ℝ) * z ^ 5 +
          (253743 / 250000 : ℝ) * z ^ 3 -
          (972587 / 1250000 : ℝ) * z) *
        ((2431 / 50000000 : ℝ) * z ^ 9 +
          (317889 / 12500000 : ℝ) * z ^ 7 +
          (18711693 / 25000000 : ℝ) * z ^ 5 +
          (7297521 / 12500000 : ℝ) * z ^ 3 -
          (41734881 / 50000000 : ℝ) * z)) = fun z ↦
        0 * z ^ 0 + 0 * z ^ 1 +
          (40590802707147 / 62500000000000 : ℝ) * z ^ 2 + 0 * z ^ 3 +
          (-81339565775223 / 62500000000000 : ℝ) * z ^ 4 + 0 * z ^ 5 +
          (-4656377171061 / 62500000000000 : ℝ) * z ^ 6 + 0 * z ^ 7 +
          (9985373066493 / 12500000000000 : ℝ) * z ^ 8 + 0 * z ^ 9 +
          (6369396746713 / 62500000000000 : ℝ) * z ^ 10 + 0 * z ^ 11 +
          (180396339123 / 62500000000000 : ℝ) * z ^ 12 + 0 * z ^ 13 +
          (853794513 / 62500000000000 : ℝ) * z ^ 14 + 0 * z ^ 15 +
          (1042899 / 62500000000000 : ℝ) * z ^ 16 + 0 * z ^ 17 +
          0 * z ^ 18 + 0 * z ^ 19 by
    funext z
    ring,
    integral_polynomial_nineteen_local]
  norm_num

private theorem integral_zero_one_endpointPotential_mul_P7_mul_P9 :
    (∫ x : ℝ in 0..1,
      yoshidaEndpointPotential x * factorTwoCenteredP7 x *
        factorTwoCenteredP9 x) = (1 / 34 : ℝ) := by
  have h7 : factorTwoCenteredP7 =
      fun x ↦ -(centeredShiftedLegendreReal 7).eval x := by
    funext x
    rw [eval_centeredShiftedLegendreReal]
    rfl
  have h9 : factorTwoCenteredP9 =
      fun x ↦ -(centeredShiftedLegendreReal 9).eval x := by
    funext x
    rw [eval_centeredShiftedLegendreReal]
    rfl
  have hfull :=
    YoshidaEndpointPotentialLegendreOffDiagonalStructural.integral_endpointPotential_mul_centeredShiftedLegendreReal_of_even
      (m := 7) (n := 9) (by norm_num) (by norm_num)
  norm_num at hfull
  have hfullActual : (∫ x : ℝ in -1..1,
      yoshidaEndpointPotential x * factorTwoCenteredP7 x *
        factorTwoCenteredP9 x) = (1 / 17 : ℝ) := by
    rw [h7, h9]
    simpa only [mul_neg, neg_mul, neg_neg] using hfull
  let f : ℝ → ℝ := fun x ↦
    yoshidaEndpointPotential x * factorTwoCenteredP7 x *
      factorTwoCenteredP9 x
  have hf : IntervalIntegrable f volume (-1) 1 := by
    dsimp only [f]
    simpa only [mul_assoc] using
      intervalIntegrable_endpointPotential_mul
        (fun x : ℝ ↦ factorTwoCenteredP7 x * factorTwoCenteredP9 x)
        (continuous_factorTwoCenteredP7.mul continuous_factorTwoCenteredP9)
  have hfeven : Function.Even f := by
    intro x
    dsimp only [f]
    have hp : yoshidaEndpointPotential (-x) = yoshidaEndpointPotential x := by
      unfold yoshidaEndpointPotential
      congr 2
      ring
    rw [hp, odd_factorTwoCenteredP7, odd_factorTwoCenteredP9]
    ring
  have hfold := integral_neg_one_one_eq_two_mul_zero_one_of_even f hf hfeven
  dsimp only [f] at hfold
  rw [hfullActual] at hfold
  linarith

private theorem centeredRawLogBilinear_P7_P9_eq_zero :
    centeredRawLogBilinear factorTwoCenteredP7 factorTwoCenteredP9 = 0 := by
  let p : ℝ[X] := -(shiftedLegendreReal 7)
  have hmode (t : ℝ) :
      centeredPullback factorTwoCenteredP7 t = p.eval t := by
    dsimp only [p]
    rw [Polynomial.eval_neg, centeredPullback_factorTwoCenteredP7]
  have horth := factorTwoCenteredP9_momentsVanishBelow 7 (by norm_num)
  have hpLog : shiftedLogKernel p =
      -(Polynomial.C (2 * (harmonic 7 : ℝ)) * shiftedLegendreReal 7) := by
    dsimp only [p]
    rw [map_neg, shiftedLogKernel_shiftedLegendreReal]
  have hpair : (∫ t : unitInterval,
      centeredPullback factorTwoCenteredP9 (t : ℝ) *
        (shiftedLogKernel p).eval (t : ℝ)) = 0 := by
    rw [hpLog]
    simp only [Polynomial.eval_neg, Polynomial.eval_mul,
      Polynomial.eval_C]
    rw [show (fun t : unitInterval ↦
        centeredPullback factorTwoCenteredP9 (t : ℝ) *
          -(2 * (harmonic 7 : ℝ) *
            (shiftedLegendreReal 7).eval (t : ℝ))) =
        fun t : unitInterval ↦ -(2 * (harmonic 7 : ℝ)) *
          (centeredPullback factorTwoCenteredP9 (t : ℝ) *
            (shiftedLegendreReal 7).eval (t : ℝ)) by
      funext t
      ring,
      integral_const_mul, horth]
    ring
  exact centeredRawLogBilinear_polynomialMode_tail_eq_zero
    p factorTwoCenteredP7 factorTwoCenteredP9
      continuous_factorTwoCenteredP9 hmode hpair

private theorem fourCellOddRawStripCancellationPolarization_P7_P9_eq :
    fourCellOddRawStripCancellationPolarization
        factorTwoCenteredP7 factorTwoCenteredP9 =
      -(1 / 2 : ℝ) * (3202052575432 / 26702880859375 : ℝ) := by
  rw [fourCellOddRawStripCancellationPolarization_eq_centered_sub_strip
      factorTwoCenteredP7 factorTwoCenteredP9
      contDiff_factorTwoCenteredP7_local contDiff_factorTwoCenteredP9_local
      odd_factorTwoCenteredP7 odd_factorTwoCenteredP9,
    centeredRawLogBilinear_P7_P9_eq_zero,
    fourCellOddEndpointStripOddRawPolarization_P7_P9]
  ring

private theorem integral_zero_one_P7_mul_P9_eq_zero :
    (∫ x : ℝ in 0..1,
      factorTwoCenteredP7 x * factorTwoCenteredP9 x) = 0 := by
  have hunit := factorTwoCenteredP9_momentsVanishBelow 7 (by norm_num)
  rw [integral_centeredPullback_mul_shiftedLegendre_eq_neg_half_local
      7 factorTwoCenteredP7 factorTwoCenteredP9
        centeredPullback_factorTwoCenteredP7] at hunit
  have hfullReverse : (∫ x : ℝ in -1..1,
      factorTwoCenteredP9 x * factorTwoCenteredP7 x) = 0 := by
    nlinarith
  have hfull : (∫ x : ℝ in -1..1,
      factorTwoCenteredP7 x * factorTwoCenteredP9 x) = 0 := by
    calc
      _ = ∫ x : ℝ in -1..1,
          factorTwoCenteredP9 x * factorTwoCenteredP7 x := by
        apply intervalIntegral.integral_congr
        intro x _hx
        ring
      _ = 0 := hfullReverse
  let f : ℝ → ℝ := fun x ↦
    factorTwoCenteredP7 x * factorTwoCenteredP9 x
  have hf : IntervalIntegrable f volume (-1) 1 := by
    dsimp only [f]
    exact (continuous_factorTwoCenteredP7.mul
      continuous_factorTwoCenteredP9).intervalIntegrable _ _
  have hfeven : Function.Even f := by
    intro x
    dsimp only [f]
    rw [odd_factorTwoCenteredP7, odd_factorTwoCenteredP9]
    ring
  have hfold := integral_neg_one_one_eq_two_mul_zero_one_of_even f hf hfeven
  dsimp only [f] at hfold
  rw [hfull] at hfold
  linarith

private theorem fourCellOddRetainedEndpointBilinear_P7_P9_eq :
    fourCellOddRetainedEndpointBilinear
        factorTwoCenteredP7 factorTwoCenteredP9 =
      -(1 / 2 : ℝ) * (3202052575432 / 26702880859375) +
        Real.sqrt 2 * Real.log 2 *
          (2113714048 / 762939453125 : ℝ) +
        (2 - Real.sqrt 2 * Real.log 2) *
          (13366976792 / 762939453125 : ℝ) +
        (93 / 50 : ℝ) * (1 / 34) := by
  unfold fourCellOddRetainedEndpointBilinear
    fourCellOddRetainedPrimePotentialBilinear
  rw [fourCellOddRawStripCancellationPolarization_P7_P9_eq,
    fourCellOddEndpointStripEvenMassBilinear_P7_P9,
    fourCellOddEndpointStripOddMassBilinear_P7_P9,
    integral_zero_one_endpointPotential_mul_P7_mul_P9]
  ring

private theorem fourCellOddRetainedEndpointBilinear_P7_P9_bounds :
    0 < fourCellOddRetainedEndpointBilinear
        factorTwoCenteredP7 factorTwoCenteredP9 ∧
      fourCellOddRetainedEndpointBilinear
        factorTwoCenteredP7 factorTwoCenteredP9 < (2 / 125 : ℝ) := by
  rw [fourCellOddRetainedEndpointBilinear_P7_P9_eq]
  rcases sqrt_two_mul_log_two_bounds with ⟨hlo, hhi⟩
  constructor <;> nlinarith

private theorem fourCellOddSignedMassRegularBilinear_sq_le_energy_mul_of_mass_eq_zero
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    (huodd : Function.Odd u) (hvodd : Function.Odd v)
    (hmass : (∫ x : ℝ in 0..1, u x * v x) = 0) :
    fourCellOddSignedMassRegularBilinear u v ^ 2 ≤
      (fourCellOperatorHalfWidth / 10) ^ 2 *
        factorTwoIntrinsicEnergy u * factorTwoIntrinsicEnergy v := by
  let I : ℝ := ∫ t : ℝ in 0..2,
    |factorTwoCenteredCorrelationBilinear u v t|
  let R : ℝ := ∫ t : ℝ in 0..2,
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
      factorTwoCenteredCorrelationBilinear u v t
  let Eᵤ : ℝ := factorTwoIntrinsicEnergy u
  let Eᵥ : ℝ := factorTwoIntrinsicEnergy v
  have hregular : |R| ≤ (1 / 20 : ℝ) * I := by
    simpa only [R, I] using
      abs_fourCellRegularBilinear_le_one_twentieth_integral_abs
        u v hu hv huodd hvodd
  have hrow :
      fourCellOddSignedMassRegularBilinear u v =
        2 * fourCellOperatorHalfWidth * R := by
    unfold fourCellOddSignedMassRegularBilinear
    rw [hmass]
    dsimp only [R]
    ring
  have ha0 : 0 ≤ fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  have hI0 : 0 ≤ I := by
    dsimp only [I]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun _t _ht ↦ abs_nonneg _)
  have habs :
      |fourCellOddSignedMassRegularBilinear u v| ≤
        (fourCellOperatorHalfWidth / 10) * I := by
    rw [hrow, abs_mul, abs_of_nonneg (by positivity :
      0 ≤ 2 * fourCellOperatorHalfWidth)]
    nlinarith
  have hI : I ^ 2 ≤ Eᵤ * Eᵥ := by
    dsimp only [I, Eᵤ, Eᵥ]
    exact
      ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP67ResidualAnalyticSchurStructural.integral_abs_factorTwoCenteredCorrelationBilinear_sq_le_energy_mul
        u v hu hv
  calc
    fourCellOddSignedMassRegularBilinear u v ^ 2 =
        |fourCellOddSignedMassRegularBilinear u v| ^ 2 := by
      rw [sq_abs]
    _ ≤ ((fourCellOperatorHalfWidth / 10) * I) ^ 2 :=
      (sq_le_sq₀ (abs_nonneg _)
        (mul_nonneg (div_nonneg ha0 (by norm_num)) hI0)).2 habs
    _ = (fourCellOperatorHalfWidth / 10) ^ 2 * I ^ 2 := by ring
    _ ≤ (fourCellOperatorHalfWidth / 10) ^ 2 * (Eᵤ * Eᵥ) :=
      mul_le_mul_of_nonneg_left hI (sq_nonneg _)
    _ = (fourCellOperatorHalfWidth / 10) ^ 2 * Eᵤ * Eᵥ := by ring

private theorem abs_fourCellOddSignedMassRegularBilinear_P7_P9_lt_three_five_hundredths :
    |fourCellOddSignedMassRegularBilinear
        factorTwoCenteredP7 factorTwoCenteredP9| < (3 / 500 : ℝ) := by
  have hsigned :=
    fourCellOddSignedMassRegularBilinear_sq_le_energy_mul_of_mass_eq_zero
      factorTwoCenteredP7 factorTwoCenteredP9
        continuous_factorTwoCenteredP7 continuous_factorTwoCenteredP9
        odd_factorTwoCenteredP7 odd_factorTwoCenteredP9
        integral_zero_one_P7_mul_P9_eq_zero
  rw [factorTwoCenteredP7_energy, factorTwoCenteredP9_energy] at hsigned
  norm_num at hsigned
  have ha0 : 0 ≤ fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  have ha := fourCellOperatorHalfWidth_le_one_half
  have hsquare :
      fourCellOddSignedMassRegularBilinear
          factorTwoCenteredP7 factorTwoCenteredP9 ^ 2 <
        (3 / 500 : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (fourCellOperatorHalfWidth - 1 / 2)]
  rw [← sq_abs] at hsquare
  nlinarith [abs_nonneg (fourCellOddSignedMassRegularBilinear
    factorTwoCenteredP7 factorTwoCenteredP9)]

private theorem abs_fourCellOddCoreLocalBilinear_P7_P9_lt_eleven_five_hundredths :
    |fourCellOddCoreLocalBilinear
      factorTwoCenteredP7 factorTwoCenteredP9| < (11 / 500 : ℝ) := by
  rw [fourCellOddCoreLocalBilinear_eq_retained_sub_signed]
  rcases fourCellOddRetainedEndpointBilinear_P7_P9_bounds with ⟨hlo, hhi⟩
  have hsigned :=
    abs_fourCellOddSignedMassRegularBilinear_P7_P9_lt_three_five_hundredths
  calc
    |fourCellOddRetainedEndpointBilinear factorTwoCenteredP7
          factorTwoCenteredP9 -
        fourCellOddSignedMassRegularBilinear factorTwoCenteredP7
          factorTwoCenteredP9| ≤
        |fourCellOddRetainedEndpointBilinear factorTwoCenteredP7
          factorTwoCenteredP9| +
        |fourCellOddSignedMassRegularBilinear factorTwoCenteredP7
          factorTwoCenteredP9| := abs_sub _ _
    _ = fourCellOddRetainedEndpointBilinear factorTwoCenteredP7
          factorTwoCenteredP9 +
        |fourCellOddSignedMassRegularBilinear factorTwoCenteredP7
          factorTwoCenteredP9| := by rw [abs_of_pos hlo]
    _ < (2 / 125 : ℝ) + 3 / 500 := add_lt_add hhi hsigned
    _ = (11 / 500 : ℝ) := by norm_num

/-- The first adjacent tail--tail block also satisfies the complete-form
Schur inequality.  Its singular endpoint cross is kept exactly throughout. -/
theorem fourCellOddCoreLocalBilinear_P7_P9_sq_le_mul :
    fourCellOddCoreLocalBilinear
        factorTwoCenteredP7 factorTwoCenteredP9 ^ 2 ≤
      fourCellOddCoreLocalQuadratic factorTwoCenteredP7 *
        fourCellOddCoreLocalQuadratic factorTwoCenteredP9 := by
  let B := fourCellOddCoreLocalBilinear
    factorTwoCenteredP7 factorTwoCenteredP9
  let Q7 := fourCellOddCoreLocalQuadratic factorTwoCenteredP7
  let Q9 := fourCellOddCoreLocalQuadratic factorTwoCenteredP9
  have hQ7 : (1 / 20 : ℝ) < Q7 :=
    one_twentieth_lt_fourCellOddCoreLocalQuadratic_P7
  have hQ9 : (1 / 25 : ℝ) < Q9 :=
    one_twenty_fifth_lt_fourCellOddCoreLocalQuadratic_P9
  have hB : |B| < (11 / 500 : ℝ) :=
    abs_fourCellOddCoreLocalBilinear_P7_P9_lt_eleven_five_hundredths
  have hBsq : B ^ 2 < (11 / 500 : ℝ) ^ 2 := by
    rw [← sq_abs]
    exact (sq_lt_sq₀ (abs_nonneg B) (by norm_num)).2 hB
  have hQ7pos : 0 < Q7 := by linarith
  have hprod : (1 / 500 : ℝ) < Q7 * Q9 := by
    calc
      (1 / 500 : ℝ) = (1 / 20 : ℝ) * (1 / 25) := by norm_num
      _ < Q7 * (1 / 25 : ℝ) := mul_lt_mul_of_pos_right hQ7 (by norm_num)
      _ < Q7 * Q9 := mul_lt_mul_of_pos_left hQ9 hQ7pos
  dsimp only [B, Q7, Q9] at hBsq hprod ⊢
  nlinarith

private theorem centeredRawLogEnergy_eq_bilinear_self_local
    (w : ℝ → ℝ) :
    centeredRawLogEnergy w = centeredRawLogBilinear w w := by
  unfold centeredRawLogEnergy centeredRawLogBilinear
  apply intervalIntegral.integral_congr
  intro x _hx
  apply intervalIntegral.integral_congr
  intro y _hy
  ring

private theorem integral_shiftedLegendreReal_sq_of_centeredMode_local
    (n : ℕ) (q : ℝ → ℝ) (r : ℝ)
    (hmode : ∀ t : ℝ, centeredPullback q t =
      -(shiftedLegendreReal n).eval t)
    (henergy : factorTwoIntrinsicEnergy q = 2 * r) :
    (∫ t : unitInterval,
      (shiftedLegendreReal n).eval (t : ℝ) *
        (shiftedLegendreReal n).eval (t : ℝ)) = r := by
  have hbridge := integral_centeredPullback_mul_shiftedLegendre_eq_neg_half_local
    n q q hmode
  have hsq : (∫ x : ℝ in -1..1, q x * q x) =
      factorTwoIntrinsicEnergy q := by
    unfold factorTwoIntrinsicEnergy
    apply intervalIntegral.integral_congr
    intro x _hx
    ring
  rw [hsq, henergy] at hbridge
  calc
    (∫ t : unitInterval,
        (shiftedLegendreReal n).eval (t : ℝ) *
          (shiftedLegendreReal n).eval (t : ℝ)) =
        -(∫ t : unitInterval,
          centeredPullback q (t : ℝ) *
            (shiftedLegendreReal n).eval (t : ℝ)) := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards [] with t
      rw [hmode]
      ring
    _ = r := by rw [hbridge]; ring

private theorem shiftedLogEnergyBilinear_shiftedLegendreReal_ne_local
    {m n : ℕ} (hmn : m ≠ n) :
    ShiftedLegendrePolynomialGap.shiftedLogEnergyBilinear
        (shiftedLegendreReal m) (shiftedLegendreReal n) = 0 := by
  rw [ShiftedLegendrePolynomialGap.shiftedLogEnergyBilinear_apply,
    shiftedLogKernel_shiftedLegendreReal]
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  rw [show (fun x : ℝ ↦
      (shiftedLegendreReal m).eval x *
        (2 * (harmonic n : ℝ) *
          (shiftedLegendreReal n).eval x)) =
      fun x : ℝ ↦ (2 * (harmonic n : ℝ)) *
        ((shiftedLegendreReal m).eval x *
          (shiftedLegendreReal n).eval x) by
    funext x
    ring,
    intervalIntegral.integral_const_mul,
    ShiftedLegendreBasis.integral_shiftedLegendreReal_mul_eq_zero hmn]
  ring

private theorem shiftedLogEnergyBilinear_shiftedLegendreReal_self_local
    (n : ℕ) (r : ℝ)
    (hsq : (∫ t : unitInterval,
      (shiftedLegendreReal n).eval (t : ℝ) *
        (shiftedLegendreReal n).eval (t : ℝ)) = r) :
    ShiftedLegendrePolynomialGap.shiftedLogEnergyBilinear
        (shiftedLegendreReal n) (shiftedLegendreReal n) =
      2 * (harmonic n : ℝ) * r := by
  rw [ShiftedLegendrePolynomialGap.shiftedLogEnergyBilinear_apply,
    shiftedLogKernel_shiftedLegendreReal]
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  have hsq' : (∫ x : ℝ in 0..1,
      (shiftedLegendreReal n).eval x *
        (shiftedLegendreReal n).eval x) = r := by
    rw [← integral_unitInterval_eq_intervalIntegral]
    exact hsq
  rw [show (fun x : ℝ ↦
      (shiftedLegendreReal n).eval x *
        (2 * (harmonic n : ℝ) *
          (shiftedLegendreReal n).eval x)) =
      fun x : ℝ ↦ (2 * (harmonic n : ℝ)) *
        ((shiftedLegendreReal n).eval x *
          (shiftedLegendreReal n).eval x) by
    funext x
    ring,
    intervalIntegral.integral_const_mul, hsq']

private theorem shiftedLegendreOddMode_sq_values_local :
    (∫ t : unitInterval,
      (shiftedLegendreReal 1).eval (t : ℝ) ^ 2) = (1 / 3 : ℝ) ∧
    (∫ t : unitInterval,
      (shiftedLegendreReal 3).eval (t : ℝ) ^ 2) = (1 / 7 : ℝ) ∧
    (∫ t : unitInterval,
      (shiftedLegendreReal 5).eval (t : ℝ) ^ 2) = (1 / 11 : ℝ) ∧
    (∫ t : unitInterval,
      (shiftedLegendreReal 7).eval (t : ℝ) ^ 2) = (1 / 15 : ℝ) ∧
    (∫ t : unitInterval,
      (shiftedLegendreReal 9).eval (t : ℝ) ^ 2) = (1 / 19 : ℝ) := by
  have h1Energy : factorTwoIntrinsicEnergy centeredP1 = 2 * (1 / 3 : ℝ) := by
    unfold factorTwoIntrinsicEnergy
    rw [integral_centeredP1_sq]
    norm_num
  have h3Energy : factorTwoIntrinsicEnergy centeredP3 = 2 * (1 / 7 : ℝ) := by
    unfold factorTwoIntrinsicEnergy
    rw [integral_centeredP3_sq]
    norm_num
  have h5Energy : factorTwoIntrinsicEnergy factorTwoCenteredP5 =
      2 * (1 / 11 : ℝ) := by
    have h := factorTwoIntrinsicEnergy_oneThreeFiveLowProfile 0 0 1
    have hp : fourCellOddOneThreeFiveLowProfile 0 0 1 =
        factorTwoCenteredP5 := by
      funext x
      unfold fourCellOddOneThreeFiveLowProfile
        factorTwoOddStructuralLowProfile centeredP1 centeredP3
      simp
    rw [hp] at h
    norm_num at h ⊢
    exact h
  have h7Energy : factorTwoIntrinsicEnergy factorTwoCenteredP7 =
      2 * (1 / 15 : ℝ) := by
    rw [factorTwoCenteredP7_energy]
    norm_num
  have h9Energy : factorTwoIntrinsicEnergy factorTwoCenteredP9 =
      2 * (1 / 19 : ℝ) := by
    rw [factorTwoCenteredP9_energy]
    norm_num
  have h1 := integral_shiftedLegendreReal_sq_of_centeredMode_local
    1 centeredP1 (1 / 3) centeredPullback_centeredP1_eq_neg_shiftedLegendre_local
      h1Energy
  have h3 := integral_shiftedLegendreReal_sq_of_centeredMode_local
    3 centeredP3 (1 / 7) centeredPullback_centeredP3_eq_neg_shiftedLegendre_local
      h3Energy
  have h5 := integral_shiftedLegendreReal_sq_of_centeredMode_local
    5 factorTwoCenteredP5 (1 / 11)
      centeredPullback_factorTwoCenteredP5_eq_neg_shiftedLegendre h5Energy
  have h7 := integral_shiftedLegendreReal_sq_of_centeredMode_local
    7 factorTwoCenteredP7 (1 / 15) centeredPullback_factorTwoCenteredP7 h7Energy
  have h9 := integral_shiftedLegendreReal_sq_of_centeredMode_local
    9 factorTwoCenteredP9 (1 / 19) centeredPullback_factorTwoCenteredP9 h9Energy
  simpa only [pow_two] using ⟨h1, h3, h5, h7, h9⟩

private theorem fourCellOddEndpointStripOdd_P9_eq_legendreFive :
    fourCellOddEndpointStripOdd factorTwoCenteredP9 =
      fourCellOddOneThreeFiveLowProfile
        (-303036 / 1953125) (1126916 / 1953125) (195844 / 1953125) +
        fun x ↦ (372 / 390625 : ℝ) * factorTwoCenteredP7 x +
          (1 / 1953125 : ℝ) * factorTwoCenteredP9 x := by
  funext x
  rw [fourCellOddEndpointStripOdd_P9]
  unfold fourCellOddOneThreeFiveLowProfile
    factorTwoOddStructuralLowProfile centeredP1 centeredP3
    factorTwoCenteredP5
  simp only [Pi.add_apply]
  rw [factorTwoCenteredP7_eq, factorTwoCenteredP9_eq]
  ring

private theorem centeredRawLogEnergy_endpointStripOdd_P7_eq :
    centeredRawLogEnergy
        (fourCellOddEndpointStripOdd factorTwoCenteredP7) =
      (500810834962 / 1068115234375 : ℝ) := by
  let p : ℝ[X] := -(
    (-9804 / 78125 : ℝ) • shiftedLegendreReal 1 +
      (35252 / 78125 : ℝ) • shiftedLegendreReal 3 +
      (1012 / 78125 : ℝ) • shiftedLegendreReal 5 +
      (1 / 78125 : ℝ) • shiftedLegendreReal 7)
  let q : ℝ → ℝ := fourCellOddEndpointStripOdd factorTwoCenteredP7
  have hmode (t : ℝ) : centeredPullback q t = p.eval t := by
    have h1 := centeredPullback_centeredP1_eq_neg_shiftedLegendre_local t
    have h3 := centeredPullback_centeredP3_eq_neg_shiftedLegendre_local t
    have h5 := centeredPullback_factorTwoCenteredP5_eq_neg_shiftedLegendre t
    have h7 := centeredPullback_factorTwoCenteredP7 t
    have hdecomp := congrFun fourCellOddEndpointStripOdd_P7_eq_legendreFour
      (2 * t - 1)
    dsimp only [p, q]
    simp only [Polynomial.eval_neg, Polynomial.eval_add,
      Polynomial.eval_smul, smul_eq_mul]
    unfold centeredPullback at h1 h3 h5 h7 ⊢
    rw [hdecomp]
    simp only [Pi.add_apply]
    unfold fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
    rw [h1, h3, h5, h7]
    ring
  rcases shiftedLegendreOddMode_sq_values_local with
    ⟨hsq1, hsq3, hsq5, hsq7, _hsq9⟩
  simp only [pow_two] at hsq1 hsq3 hsq5 hsq7
  have h11 := shiftedLogEnergyBilinear_shiftedLegendreReal_self_local
    1 (1 / 3) hsq1
  have h33 := shiftedLogEnergyBilinear_shiftedLegendreReal_self_local
    3 (1 / 7) hsq3
  have h55 := shiftedLogEnergyBilinear_shiftedLegendreReal_self_local
    5 (1 / 11) hsq5
  have h77 := shiftedLogEnergyBilinear_shiftedLegendreReal_self_local
    7 (1 / 15) hsq7
  norm_num [harmonic, Finset.sum_range_succ] at h11 h33 h55 h77
  change ShiftedLegendrePolynomialGap.shiftedLogEnergyBilinear
    (shiftedLegendreReal 1) (shiftedLegendreReal 1) = 2 / 3 at h11
  change ShiftedLegendrePolynomialGap.shiftedLogEnergyBilinear
    (shiftedLegendreReal 3) (shiftedLegendreReal 3) = 11 / 21 at h33
  change ShiftedLegendrePolynomialGap.shiftedLogEnergyBilinear
    (shiftedLegendreReal 5) (shiftedLegendreReal 5) = 137 / 330 at h55
  change ShiftedLegendrePolynomialGap.shiftedLogEnergyBilinear
    (shiftedLegendreReal 7) (shiftedLegendreReal 7) = 121 / 350 at h77
  have h13 := shiftedLogEnergyBilinear_shiftedLegendreReal_ne_local
    (by norm_num : 1 ≠ 3)
  have h15 := shiftedLogEnergyBilinear_shiftedLegendreReal_ne_local
    (by norm_num : 1 ≠ 5)
  have h17 := shiftedLogEnergyBilinear_shiftedLegendreReal_ne_local
    (by norm_num : 1 ≠ 7)
  have h31 := shiftedLogEnergyBilinear_shiftedLegendreReal_ne_local
    (by norm_num : 3 ≠ 1)
  have h35 := shiftedLogEnergyBilinear_shiftedLegendreReal_ne_local
    (by norm_num : 3 ≠ 5)
  have h37 := shiftedLogEnergyBilinear_shiftedLegendreReal_ne_local
    (by norm_num : 3 ≠ 7)
  have h51 := shiftedLogEnergyBilinear_shiftedLegendreReal_ne_local
    (by norm_num : 5 ≠ 1)
  have h53 := shiftedLogEnergyBilinear_shiftedLegendreReal_ne_local
    (by norm_num : 5 ≠ 3)
  have h57 := shiftedLogEnergyBilinear_shiftedLegendreReal_ne_local
    (by norm_num : 5 ≠ 7)
  have h71 := shiftedLogEnergyBilinear_shiftedLegendreReal_ne_local
    (by norm_num : 7 ≠ 1)
  have h73 := shiftedLogEnergyBilinear_shiftedLegendreReal_ne_local
    (by norm_num : 7 ≠ 3)
  have h75 := shiftedLogEnergyBilinear_shiftedLegendreReal_ne_local
    (by norm_num : 7 ≠ 5)
  have hpEnergy :
      ShiftedLegendrePolynomialGap.shiftedLogEnergyBilinear p p =
        (250405417481 / 2136230468750 : ℝ) := by
    dsimp only [p]
    simp only [map_neg, map_add, map_smul, smul_eq_mul]
    simp only [LinearMap.neg_apply, LinearMap.add_apply,
      LinearMap.smul_apply, smul_eq_mul]
    rw [h11, h13, h15, h17, h31, h33, h35, h37,
      h51, h53, h55, h57, h71, h73, h75, h77]
    norm_num
  have hpair : (∫ t : unitInterval,
      centeredPullback q (t : ℝ) *
        (shiftedLogKernel p).eval (t : ℝ)) =
      ShiftedLegendrePolynomialGap.shiftedLogEnergyBilinear p p := by
    rw [ShiftedLegendrePolynomialGap.shiftedLogEnergyBilinear_apply]
    calc
      _ = ∫ t : unitInterval,
          p.eval (t : ℝ) * (shiftedLogKernel p).eval (t : ℝ) := by
        apply integral_congr_ae
        filter_upwards [] with t
        rw [hmode]
      _ = _ := integral_unitInterval_eq_intervalIntegral
        (fun t : ℝ ↦ p.eval t * (shiftedLogKernel p).eval t)
  have hqcont : Continuous q := by
    dsimp only [q]
    exact (contDiff_fourCellOddEndpointStripOdd_local
      factorTwoCenteredP7 contDiff_factorTwoCenteredP7_local).continuous
  have h := centeredRawLogBilinear_polynomialMode_eq_four_mul_pair
    p q q hqcont hmode
  rw [hpair, hpEnergy] at h
  rw [centeredRawLogEnergy_eq_bilinear_self_local]
  norm_num at h ⊢
  exact h

private theorem centeredRawLogEnergy_endpointStripOdd_P9_eq :
    centeredRawLogEnergy
        (fourCellOddEndpointStripOdd factorTwoCenteredP9) =
      (507768301938707 / 652313232421875 : ℝ) := by
  let p : ℝ[X] := -(
    (-303036 / 1953125 : ℝ) • shiftedLegendreReal 1 +
      (1126916 / 1953125 : ℝ) • shiftedLegendreReal 3 +
      (195844 / 1953125 : ℝ) • shiftedLegendreReal 5 +
      (372 / 390625 : ℝ) • shiftedLegendreReal 7 +
      (1 / 1953125 : ℝ) • shiftedLegendreReal 9)
  let q : ℝ → ℝ := fourCellOddEndpointStripOdd factorTwoCenteredP9
  have hmode (t : ℝ) : centeredPullback q t = p.eval t := by
    have h1 := centeredPullback_centeredP1_eq_neg_shiftedLegendre_local t
    have h3 := centeredPullback_centeredP3_eq_neg_shiftedLegendre_local t
    have h5 := centeredPullback_factorTwoCenteredP5_eq_neg_shiftedLegendre t
    have h7 := centeredPullback_factorTwoCenteredP7 t
    have h9 := centeredPullback_factorTwoCenteredP9 t
    have hdecomp := congrFun fourCellOddEndpointStripOdd_P9_eq_legendreFive
      (2 * t - 1)
    dsimp only [p, q]
    simp only [Polynomial.eval_neg, Polynomial.eval_add,
      Polynomial.eval_smul, smul_eq_mul]
    unfold centeredPullback at h1 h3 h5 h7 h9 ⊢
    rw [hdecomp]
    simp only [Pi.add_apply]
    unfold fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
    rw [h1, h3, h5, h7, h9]
    ring
  rcases shiftedLegendreOddMode_sq_values_local with
    ⟨hsq1, hsq3, hsq5, hsq7, hsq9⟩
  simp only [pow_two] at hsq1 hsq3 hsq5 hsq7 hsq9
  have h11 := shiftedLogEnergyBilinear_shiftedLegendreReal_self_local
    1 (1 / 3) hsq1
  have h33 := shiftedLogEnergyBilinear_shiftedLegendreReal_self_local
    3 (1 / 7) hsq3
  have h55 := shiftedLogEnergyBilinear_shiftedLegendreReal_self_local
    5 (1 / 11) hsq5
  have h77 := shiftedLogEnergyBilinear_shiftedLegendreReal_self_local
    7 (1 / 15) hsq7
  have h99 := shiftedLogEnergyBilinear_shiftedLegendreReal_self_local
    9 (1 / 19) hsq9
  norm_num [harmonic, Finset.sum_range_succ] at h11 h33 h55 h77 h99
  change ShiftedLegendrePolynomialGap.shiftedLogEnergyBilinear
    (shiftedLegendreReal 1) (shiftedLegendreReal 1) = 2 / 3 at h11
  change ShiftedLegendrePolynomialGap.shiftedLogEnergyBilinear
    (shiftedLegendreReal 3) (shiftedLegendreReal 3) = 11 / 21 at h33
  change ShiftedLegendrePolynomialGap.shiftedLogEnergyBilinear
    (shiftedLegendreReal 5) (shiftedLegendreReal 5) = 137 / 330 at h55
  change ShiftedLegendrePolynomialGap.shiftedLogEnergyBilinear
    (shiftedLegendreReal 7) (shiftedLegendreReal 7) = 121 / 350 at h77
  change ShiftedLegendrePolynomialGap.shiftedLogEnergyBilinear
    (shiftedLegendreReal 9) (shiftedLegendreReal 9) = 7129 / 23940 at h99
  have h13 := shiftedLogEnergyBilinear_shiftedLegendreReal_ne_local
    (by norm_num : 1 ≠ 3)
  have h15 := shiftedLogEnergyBilinear_shiftedLegendreReal_ne_local
    (by norm_num : 1 ≠ 5)
  have h17 := shiftedLogEnergyBilinear_shiftedLegendreReal_ne_local
    (by norm_num : 1 ≠ 7)
  have h19 := shiftedLogEnergyBilinear_shiftedLegendreReal_ne_local
    (by norm_num : 1 ≠ 9)
  have h31 := shiftedLogEnergyBilinear_shiftedLegendreReal_ne_local
    (by norm_num : 3 ≠ 1)
  have h35 := shiftedLogEnergyBilinear_shiftedLegendreReal_ne_local
    (by norm_num : 3 ≠ 5)
  have h37 := shiftedLogEnergyBilinear_shiftedLegendreReal_ne_local
    (by norm_num : 3 ≠ 7)
  have h39 := shiftedLogEnergyBilinear_shiftedLegendreReal_ne_local
    (by norm_num : 3 ≠ 9)
  have h51 := shiftedLogEnergyBilinear_shiftedLegendreReal_ne_local
    (by norm_num : 5 ≠ 1)
  have h53 := shiftedLogEnergyBilinear_shiftedLegendreReal_ne_local
    (by norm_num : 5 ≠ 3)
  have h57 := shiftedLogEnergyBilinear_shiftedLegendreReal_ne_local
    (by norm_num : 5 ≠ 7)
  have h59 := shiftedLogEnergyBilinear_shiftedLegendreReal_ne_local
    (by norm_num : 5 ≠ 9)
  have h71 := shiftedLogEnergyBilinear_shiftedLegendreReal_ne_local
    (by norm_num : 7 ≠ 1)
  have h73 := shiftedLogEnergyBilinear_shiftedLegendreReal_ne_local
    (by norm_num : 7 ≠ 3)
  have h75 := shiftedLogEnergyBilinear_shiftedLegendreReal_ne_local
    (by norm_num : 7 ≠ 5)
  have h79 := shiftedLogEnergyBilinear_shiftedLegendreReal_ne_local
    (by norm_num : 7 ≠ 9)
  have h91 := shiftedLogEnergyBilinear_shiftedLegendreReal_ne_local
    (by norm_num : 9 ≠ 1)
  have h93 := shiftedLogEnergyBilinear_shiftedLegendreReal_ne_local
    (by norm_num : 9 ≠ 3)
  have h95 := shiftedLogEnergyBilinear_shiftedLegendreReal_ne_local
    (by norm_num : 9 ≠ 5)
  have h97 := shiftedLogEnergyBilinear_shiftedLegendreReal_ne_local
    (by norm_num : 9 ≠ 7)
  have hpEnergy :
      ShiftedLegendrePolynomialGap.shiftedLogEnergyBilinear p p =
        (507768301938707 / 2609252929687500 : ℝ) := by
    dsimp only [p]
    simp only [map_neg, map_add, map_smul, smul_eq_mul]
    simp only [LinearMap.neg_apply, LinearMap.add_apply,
      LinearMap.smul_apply, smul_eq_mul]
    rw [h11, h13, h15, h17, h19,
      h31, h33, h35, h37, h39,
      h51, h53, h55, h57, h59,
      h71, h73, h75, h77, h79,
      h91, h93, h95, h97, h99]
    norm_num
  have hpair : (∫ t : unitInterval,
      centeredPullback q (t : ℝ) *
        (shiftedLogKernel p).eval (t : ℝ)) =
      ShiftedLegendrePolynomialGap.shiftedLogEnergyBilinear p p := by
    rw [ShiftedLegendrePolynomialGap.shiftedLogEnergyBilinear_apply]
    calc
      _ = ∫ t : unitInterval,
          p.eval (t : ℝ) * (shiftedLogKernel p).eval (t : ℝ) := by
        apply integral_congr_ae
        filter_upwards [] with t
        rw [hmode]
      _ = _ := integral_unitInterval_eq_intervalIntegral
        (fun t : ℝ ↦ p.eval t * (shiftedLogKernel p).eval t)
  have hqcont : Continuous q := by
    dsimp only [q]
    exact (contDiff_fourCellOddEndpointStripOdd_local
      factorTwoCenteredP9 contDiff_factorTwoCenteredP9_local).continuous
  have h := centeredRawLogBilinear_polynomialMode_eq_four_mul_pair
    p q q hqcont hmode
  rw [hpair, hpEnergy] at h
  rw [centeredRawLogEnergy_eq_bilinear_self_local]
  norm_num at h ⊢
  exact h

private theorem centeredRawLogEnergy_of_neg_shiftedLegendre_local
    (n : ℕ) (q : ℝ → ℝ) (r : ℝ)
    (hq : Continuous q)
    (hmode : ∀ t : ℝ, centeredPullback q t =
      -(shiftedLegendreReal n).eval t)
    (hsq : (∫ t : unitInterval,
      (shiftedLegendreReal n).eval (t : ℝ) *
        (shiftedLegendreReal n).eval (t : ℝ)) = r) :
    centeredRawLogEnergy q = 8 * (harmonic n : ℝ) * r := by
  let p : ℝ[X] := -(shiftedLegendreReal n)
  have hmode' (t : ℝ) : centeredPullback q t = p.eval t := by
    dsimp only [p]
    rw [Polynomial.eval_neg, hmode]
  have hself := shiftedLogEnergyBilinear_shiftedLegendreReal_self_local
    n r hsq
  have hpEnergy :
    ShiftedLegendrePolynomialGap.shiftedLogEnergyBilinear p p =
        2 * (harmonic n : ℝ) * r := by
    dsimp only [p]
    simp only [map_neg]
    simp only [LinearMap.neg_apply, neg_neg]
    exact hself
  have hpair : (∫ t : unitInterval,
      centeredPullback q (t : ℝ) *
        (shiftedLogKernel p).eval (t : ℝ)) =
      ShiftedLegendrePolynomialGap.shiftedLogEnergyBilinear p p := by
    rw [ShiftedLegendrePolynomialGap.shiftedLogEnergyBilinear_apply]
    calc
      _ = ∫ t : unitInterval,
          p.eval (t : ℝ) * (shiftedLogKernel p).eval (t : ℝ) := by
        apply integral_congr_ae
        filter_upwards [] with t
        rw [hmode']
      _ = _ := integral_unitInterval_eq_intervalIntegral
        (fun t : ℝ ↦ p.eval t * (shiftedLogKernel p).eval t)
  have h := centeredRawLogBilinear_polynomialMode_eq_four_mul_pair
    p q q hq hmode'
  rw [hpair, hpEnergy] at h
  rw [centeredRawLogEnergy_eq_bilinear_self_local]
  nlinarith

private theorem centeredRawLogEnergy_factorTwoCenteredP7_eq_local :
    centeredRawLogEnergy factorTwoCenteredP7 = (242 / 175 : ℝ) := by
  rcases shiftedLegendreOddMode_sq_values_local with
    ⟨_hsq1, _hsq3, _hsq5, hsq7, _hsq9⟩
  simp only [pow_two] at hsq7
  have h := centeredRawLogEnergy_of_neg_shiftedLegendre_local
    7 factorTwoCenteredP7 (1 / 15) continuous_factorTwoCenteredP7
      centeredPullback_factorTwoCenteredP7 hsq7
  norm_num [harmonic, Finset.sum_range_succ] at h ⊢
  exact h

private theorem centeredRawLogEnergy_factorTwoCenteredP9_eq_local :
    centeredRawLogEnergy factorTwoCenteredP9 = (7129 / 5985 : ℝ) := by
  rcases shiftedLegendreOddMode_sq_values_local with
    ⟨_hsq1, _hsq3, _hsq5, _hsq7, hsq9⟩
  simp only [pow_two] at hsq9
  have h := centeredRawLogEnergy_of_neg_shiftedLegendre_local
    9 factorTwoCenteredP9 (1 / 19) continuous_factorTwoCenteredP9
      centeredPullback_factorTwoCenteredP9 hsq9
  norm_num [harmonic, Finset.sum_range_succ] at h ⊢
  exact h

private theorem fourCellOddRawStripCancellationReserve_eq_raw_sub_strip
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w) :
    fourCellOddRawStripCancellationReserve w =
      (1 / 4 : ℝ) * centeredRawLogEnergy w -
        (1 / 2 : ℝ) * fourCellOddEndpointStripOddRawEnergy w := by
  have hwLocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w :=
    hw.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1)
  have hfold := centeredRawLogEnergy_div_four_eq_positiveHalf_odd
    w hwLocal hodd
  unfold fourCellOddRawStripCancellationReserve
  rw [← hfold]
  ring

private theorem fourCellOddRawStripCancellationReserve_P7_eq :
    fourCellOddRawStripCancellationReserve factorTwoCenteredP7 =
      (121 / 350 : ℝ) -
        (1 / 2 : ℝ) * (500810834962 / 5340576171875 : ℝ) := by
  rw [fourCellOddRawStripCancellationReserve_eq_raw_sub_strip
      factorTwoCenteredP7 contDiff_factorTwoCenteredP7_local
        odd_factorTwoCenteredP7,
    centeredRawLogEnergy_factorTwoCenteredP7_eq_local]
  unfold fourCellOddEndpointStripOddRawEnergy
  rw [centeredRawLogEnergy_endpointStripOdd_P7_eq]
  ring

private theorem fourCellOddRawStripCancellationReserve_P9_eq :
    fourCellOddRawStripCancellationReserve factorTwoCenteredP9 =
      (7129 / 23940 : ℝ) -
        (1 / 2 : ℝ) *
          (507768301938707 / 3261566162109375 : ℝ) := by
  rw [fourCellOddRawStripCancellationReserve_eq_raw_sub_strip
      factorTwoCenteredP9 contDiff_factorTwoCenteredP9_local
        odd_factorTwoCenteredP9,
    centeredRawLogEnergy_factorTwoCenteredP9_eq_local]
  unfold fourCellOddEndpointStripOddRawEnergy
  rw [centeredRawLogEnergy_endpointStripOdd_P9_eq]
  ring

private theorem fourCellOddEndpointStripEvenMass_P7_eq :
    fourCellOddEndpointStripEvenMass factorTwoCenteredP7 =
      (3812346752 / 152587890625 : ℝ) := by
  unfold fourCellOddEndpointStripEvenMass
  simp_rw [fourCellOddEndpointStripEven_P7]
  rw [show (fun z : ℝ ↦
      ((3003 / 312500 : ℝ) * z ^ 6 +
        (30723 / 62500 : ℝ) * z ^ 4 +
        (124929 / 312500 : ℝ) * z ^ 2 - 74891 / 312500) ^ 2) =
      fun z ↦
        (5608661881 / 97656250000 : ℝ) * z ^ 0 + 0 * z ^ 1 +
          (-9356057739 / 48828125000 : ℝ) * z ^ 2 + 0 * z ^ 3 +
          (-7401506889 / 97656250000 : ℝ) * z ^ 4 + 0 * z ^ 5 +
          (9483035331 / 24414062500 : ℝ) * z ^ 6 + 0 * z ^ 7 +
          (24347891799 / 97656250000 : ℝ) * z ^ 8 + 0 * z ^ 9 +
          (92261169 / 9765625000 : ℝ) * z ^ 10 + 0 * z ^ 11 +
          (9018009 / 97656250000 : ℝ) * z ^ 12 + 0 * z ^ 13 +
          0 * z ^ 14 + 0 * z ^ 15 + 0 * z ^ 16 + 0 * z ^ 17 +
          0 * z ^ 18 + 0 * z ^ 19 by
    funext z
    ring,
    integral_polynomial_nineteen_local]
  norm_num

private theorem fourCellOddEndpointStripOddMass_P7_eq :
    fourCellOddEndpointStripOddMass factorTwoCenteredP7 =
      (6289849442 / 457763671875 : ℝ) := by
  unfold fourCellOddEndpointStripOddMass
  simp_rw [fourCellOddEndpointStripOdd_P7]
  rw [show (fun z : ℝ ↦
      ((429 / 1250000 : ℝ) * z ^ 7 +
        (126819 / 1250000 : ℝ) * z ^ 5 +
        (253743 / 250000 : ℝ) * z ^ 3 -
        (972587 / 1250000 : ℝ) * z) ^ 2) = fun z ↦
        0 * z ^ 0 + 0 * z ^ 1 +
          (945925472569 / 1562500000000 : ℝ) * z ^ 2 + 0 * z ^ 3 +
          (-246787143141 / 156250000000 : ℝ) * z ^ 4 + 0 * z ^ 5 +
          (1362952729719 / 1562500000000 : ℝ) * z ^ 6 + 0 * z ^ 7 +
          (80239963881 / 390625000000 : ℝ) * z ^ 8 + 0 * z ^ 9 +
          (17171616231 / 1562500000000 : ℝ) * z ^ 10 + 0 * z ^ 11 +
          (54405351 / 781250000000 : ℝ) * z ^ 12 + 0 * z ^ 13 +
          (184041 / 1562500000000 : ℝ) * z ^ 14 + 0 * z ^ 15 +
          0 * z ^ 16 + 0 * z ^ 17 + 0 * z ^ 18 + 0 * z ^ 19 by
    funext z
    ring,
    integral_polynomial_nineteen_local]
  norm_num

private theorem fourCellOddEndpointStripEvenMass_P9_eq :
    fourCellOddEndpointStripEvenMass factorTwoCenteredP9 =
      (30336849696 / 3814697265625 : ℝ) := by
  unfold fourCellOddEndpointStripEvenMass
  simp_rw [fourCellOddEndpointStripEven_P9]
  rw [show (fun z : ℝ ↦
      ((21879 / 12500000 : ℝ) * z ^ 8 +
        (591591 / 3125000 : ℝ) * z ^ 6 +
        (8801793 / 6250000 : ℝ) * z ^ 4 -
        (4094541 / 3125000 : ℝ) * z ^ 2 +
        2348191 / 12500000) ^ 2) = fun z ↦
        (5514000972481 / 156250000000000 : ℝ) * z ^ 0 + 0 * z ^ 1 +
          (-9614764325331 / 19531250000000 : ℝ) * z ^ 2 + 0 * z ^ 3 +
          (87729355109187 / 39062500000000 : ℝ) * z ^ 4 + 0 * z ^ 5 +
          (-14137887192429 / 3906250000000 : ℝ) * z ^ 6 + 0 * z ^ 7 +
          (116237798424891 / 78125000000000 : ℝ) * z ^ 8 + 0 * z ^ 9 +
          (10324538582787 / 19531250000000 : ℝ) * z ^ 10 + 0 * z ^ 11 +
          (1592494074171 / 39062500000000 : ℝ) * z ^ 12 + 0 * z ^ 13 +
          (12943419489 / 19531250000000 : ℝ) * z ^ 14 + 0 * z ^ 15 +
          (478690641 / 156250000000000 : ℝ) * z ^ 16 + 0 * z ^ 17 +
          0 * z ^ 18 + 0 * z ^ 19 by
    funext z
    ring,
    integral_polynomial_nineteen_local]
  norm_num

private theorem fourCellOddEndpointStripOddMass_P9_eq :
    fourCellOddEndpointStripOddMass factorTwoCenteredP9 =
      (1637931196186 / 72479248046875 : ℝ) := by
  unfold fourCellOddEndpointStripOddMass
  simp_rw [fourCellOddEndpointStripOdd_P9]
  rw [show (fun z : ℝ ↦
      ((2431 / 50000000 : ℝ) * z ^ 9 +
        (317889 / 12500000 : ℝ) * z ^ 7 +
        (18711693 / 25000000 : ℝ) * z ^ 5 +
        (7297521 / 12500000 : ℝ) * z ^ 3 -
        (41734881 / 50000000 : ℝ) * z) ^ 2) = fun z ↦
        0 * z ^ 0 + 0 * z ^ 1 +
          (1741800292084161 / 2500000000000000 : ℝ) * z ^ 2 + 0 * z ^ 3 +
          (-304561170530001 / 312500000000000 : ℝ) * z ^ 4 + 0 * z ^ 5 +
          (-567915029681769 / 625000000000000 : ℝ) * z ^ 6 + 0 * z ^ 7 +
          (259830885639897 / 312500000000000 : ℝ) * z ^ 8 + 0 * z ^ 9 +
          (737270278807491 / 1250000000000000 : ℝ) * z ^ 10 + 0 * z ^ 11 +
          (2382844605141 / 62500000000000 : ℝ) * z ^ 12 + 0 * z ^ 13 +
          (449701790967 / 625000000000000 : ℝ) * z ^ 14 + 0 * z ^ 15 +
          (772788159 / 312500000000000 : ℝ) * z ^ 16 + 0 * z ^ 17 +
          (5909761 / 2500000000000000 : ℝ) * z ^ 18 + 0 * z ^ 19 by
    funext z
    ring,
    integral_polynomial_nineteen_local]
  norm_num

theorem fourCellOddCoreLocalQuadratic_add
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    fourCellOddCoreLocalQuadratic (u + v) =
      fourCellOddCoreLocalQuadratic u +
        2 * fourCellOddCoreLocalBilinear u v +
          fourCellOddCoreLocalQuadratic v := by
  unfold fourCellOddCoreLocalQuadratic fourCellOddCoreLocalBilinear
  rw [fourCellOddHalfCoreReserve_add_localWidthDefect_eq_raw_add_reduced,
    fourCellOddHalfCoreReserve_add_localWidthDefect_eq_raw_add_reduced,
    fourCellOddHalfCoreReserve_add_localWidthDefect_eq_raw_add_reduced,
    fourCellOddRawStripCancellationReserve_add,
    fourCellOddStripReducedRemainder_add u v hu hv]
  ring

theorem fourCellOddCoreLocal_oneThreeFive_decomposition
    (w : ℝ → ℝ) (hw : Continuous w) :
    fourCellOddCoreLocalQuadratic w =
      fourCellOddCoreLocalQuadratic (fourCellOddOneThreeFiveLowPart w) +
        2 * fourCellOddCoreLocalBilinear
          (fourCellOddOneThreeFiveLowPart w)
          (fourCellOddOneThreeFiveResidual w) +
        fourCellOddCoreLocalQuadratic
          (fourCellOddOneThreeFiveResidual w) := by
  let p := fourCellOddOneThreeFiveLowPart w
  let v := fourCellOddOneThreeFiveResidual w
  have hp : Continuous p := by
    dsimp only [p, fourCellOddOneThreeFiveLowPart]
    exact (contDiff_fourCellOddOneThreeFiveLowProfile _ _ _).continuous
  have hv : Continuous v := by
    dsimp only [v]
    unfold fourCellOddOneThreeFiveResidual centeredOddOneThreeResidual
      centeredP1 centeredP3 factorTwoCenteredP5
    fun_prop
  have hadd := fourCellOddCoreLocalQuadratic_add p v hp hv
  have hreconstruct : p + v = w := by
    dsimp only [p, v]
    exact fourCellOddOneThreeFiveLowPart_add_residual w
  rw [hreconstruct] at hadd
  exact hadd

/-- The positive tail weight supplied by the structural `P₁`-orthogonal
raw-square argument.  This is a genuine integral weight, not a cutoff norm. -/
def fourCellOddP7TailWeight (v : ℝ → ℝ) : ℝ :=
  (27 / 250 : ℝ) * ∫ x : ℝ in 0..3 / 5, v x ^ 2

theorem fourCellOddP7TailWeight_nonneg
    (v : ℝ → ℝ) :
    0 ≤ fourCellOddP7TailWeight v := by
  unfold fourCellOddP7TailWeight
  exact mul_nonneg (by norm_num) (intervalIntegral.integral_nonneg
    (by norm_num) (fun x _hx ↦ sq_nonneg (v x)))

/-- The lower-only candidate weight vanishes on every tail supported in the
endpoint strip.  Hence it cannot serve as a dual norm unless the exact mixed
row annihilates that entire infinite-dimensional subspace. -/
theorem fourCellOddP7TailWeight_eq_zero_of_zero_on_lower
    (v : ℝ → ℝ)
    (hzero : ∀ x ∈ Icc (0 : ℝ) (3 / 5), v x = 0) :
    fourCellOddP7TailWeight v = 0 := by
  unfold fourCellOddP7TailWeight
  have hint : (∫ x : ℝ in 0..3 / 5, v x ^ 2) = 0 := by
    calc
      (∫ x : ℝ in 0..3 / 5, v x ^ 2) =
          ∫ _x : ℝ in 0..3 / 5, 0 := by
        apply intervalIntegral.integral_congr
        intro x hx
        have hx' : x ∈ Icc (0 : ℝ) (3 / 5) := by
          simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 3 / 5)] using hx
        change v x ^ 2 = 0
        rw [hzero x hx']
        norm_num
      _ = 0 := by simp
  rw [hint, mul_zero]

/-- The formally too-strong lower-only dual claim.  It is retained solely
to state its exact degeneracy consequence below. -/
def fourCellOddOneThreeFiveEndpointWeightedDualBound : Prop :=
  ∀ (c d e : ℝ) (v : ℝ → ℝ),
    ContDiff ℝ 1 v → Function.Odd v →
    centeredOddP1Coefficient v = 0 →
    centeredOddP3Coefficient v = 0 →
    centeredOddP5Coefficient v = 0 →
    v 1 = -(c + d + e) →
    fourCellOddCoreLocalBilinear
        (fourCellOddOneThreeFiveLowProfile c d e) v ^ 2 ≤
      fourCellOddCoreLocalQuadratic
          (fourCellOddOneThreeFiveLowProfile c d e) *
        fourCellOddP7TailWeight v

/-- A lower-only dual claim forces the mixed row to vanish whenever the
lower weight vanishes.  This is the structural obstruction that necessitates
retaining a positive amount of the complete-half raw reserve. -/
theorem fourCellOddCoreLocalBilinear_eq_zero_of_lowerOnlyDual
    (hdual : fourCellOddOneThreeFiveEndpointWeightedDualBound)
    (c d e : ℝ) (v : ℝ → ℝ)
    (hv : ContDiff ℝ 1 v) (hvodd : Function.Odd v)
    (hvone : centeredOddP1Coefficient v = 0)
    (hvthree : centeredOddP3Coefficient v = 0)
    (hvfive : centeredOddP5Coefficient v = 0)
    (hendpoint : v 1 = -(c + d + e))
    (hweight : fourCellOddP7TailWeight v = 0) :
    fourCellOddCoreLocalBilinear
        (fourCellOddOneThreeFiveLowProfile c d e) v = 0 := by
  have h := hdual c d e v hv hvodd hvone hvthree hvfive hendpoint
  rw [hweight, mul_zero] at h
  nlinarith [sq_nonneg (fourCellOddCoreLocalBilinear
    (fourCellOddOneThreeFiveLowProfile c d e) v)]

/-- Nondegenerate Riesz weight: the sharp lower reserve plus the rational
global gap left by the exact scalar budget. -/
def fourCellOddP7GlobalTailWeight (v : ℝ → ℝ) : ℝ :=
  fourCellOddP7TailWeight v +
    (13 / 20000 : ℝ) * ∫ x : ℝ in 0..1, v x ^ 2

theorem fourCellOddP7GlobalTailWeight_nonneg (v : ℝ → ℝ) :
    0 ≤ fourCellOddP7GlobalTailWeight v := by
  unfold fourCellOddP7GlobalTailWeight
  have hhalf : 0 ≤ (∫ x : ℝ in 0..1, v x ^ 2) :=
    intervalIntegral.integral_nonneg (by norm_num)
      (fun x _hx ↦ sq_nonneg (v x))
  exact add_nonneg (fourCellOddP7TailWeight_nonneg v)
    (mul_nonneg (by norm_num) hhalf)

private theorem integral_zero_one_P7_sq :
    (∫ x : ℝ in 0..1, factorTwoCenteredP7 x ^ 2) = (1 / 15 : ℝ) := by
  have hfold := integral_sq_eq_two_mul_positiveHalf
    factorTwoCenteredP7 continuous_factorTwoCenteredP7
      (Or.inr odd_factorTwoCenteredP7)
  rw [integral_factorTwoCenteredP7_sq] at hfold
  linarith

private theorem integral_zero_one_P9_sq :
    (∫ x : ℝ in 0..1, factorTwoCenteredP9 x ^ 2) = (1 / 19 : ℝ) := by
  have hfold := integral_sq_eq_two_mul_positiveHalf
    factorTwoCenteredP9 continuous_factorTwoCenteredP9
      (Or.inr odd_factorTwoCenteredP9)
  have henergy := factorTwoCenteredP9_energy
  unfold factorTwoIntrinsicEnergy at henergy
  rw [henergy] at hfold
  linarith

private theorem two_hundred_eleven_five_hundredths_lt_retained_P7 :
    (211 / 500 : ℝ) <
      fourCellOddRetainedEndpointQuadratic factorTwoCenteredP7 := by
  unfold fourCellOddRetainedEndpointQuadratic
    fourCellOddRetainedPrimePotentialQuadratic
  rw [fourCellOddRawStripCancellationReserve_P7_eq,
    fourCellOddEndpointStripEvenMass_P7_eq,
    fourCellOddEndpointStripOddMass_P7_eq,
    integral_zero_one_endpointPotential_mul_P7_sq_eq]
  have hk := sqrt_two_mul_log_two_bounds.1
  have hlog := strict_log_two_bounds.2
  nlinarith

private theorem one_hundred_fifty_nine_five_hundredths_lt_retained_P9 :
    (159 / 500 : ℝ) <
      fourCellOddRetainedEndpointQuadratic factorTwoCenteredP9 := by
  unfold fourCellOddRetainedEndpointQuadratic
    fourCellOddRetainedPrimePotentialQuadratic
  rw [fourCellOddRawStripCancellationReserve_P9_eq,
    fourCellOddEndpointStripEvenMass_P9_eq,
    fourCellOddEndpointStripOddMass_P9_eq,
    integral_zero_one_endpointPotential_mul_P9_sq_eq]
  have hk := sqrt_two_mul_log_two_bounds.2
  have hlog := strict_log_two_bounds.2
  nlinarith

private theorem fourCellOddSignedMassRegularQuadratic_P7_lt_eleven_fiftieths :
    fourCellOddSignedMassRegularQuadratic factorTwoCenteredP7 <
      (11 / 50 : ℝ) := by
  let R : ℝ := ∫ t : ℝ in 0..2,
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
      centeredEndpointCorrelation factorTwoCenteredP7 t
  have hcorr := abs_fourCellRegularCorrelation_le_one_twentieth_centeredMass
    factorTwoCenteredP7 continuous_factorTwoCenteredP7
      odd_factorTwoCenteredP7
  rw [integral_factorTwoCenteredP7_sq] at hcorr
  change |R| ≤ (1 / 20 : ℝ) * (2 / 15) at hcorr
  norm_num at hcorr
  have ha0 : 0 ≤ fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  have ha := fourCellOperatorHalfWidth_le_one_half
  have hregular : 2 * fourCellOperatorHalfWidth * R ≤ (1 / 150 : ℝ) := by
    calc
      2 * fourCellOperatorHalfWidth * R ≤
          2 * fourCellOperatorHalfWidth * |R| :=
        mul_le_mul_of_nonneg_left (le_abs_self R)
          (mul_nonneg (by norm_num) ha0)
      _ ≤ 2 * (1 / 2 : ℝ) * |R| := by
        exact mul_le_mul_of_nonneg_right (by nlinarith) (abs_nonneg R)
      _ ≤ 2 * (1 / 2 : ℝ) * (1 / 150 : ℝ) := by
        exact mul_le_mul_of_nonneg_left hcorr (by norm_num)
      _ = (1 / 150 : ℝ) := by norm_num
  have hscalar := fourCellScalar_lt_31577_div_20000
  unfold fourCellOddSignedMassRegularQuadratic
  rw [integral_zero_one_P7_sq]
  change
    (2 * (Real.log (2 * fourCellOperatorHalfWidth) +
        Real.eulerMascheroniConstant + Real.log Real.pi) + 3 / 200) *
        (1 / 15 : ℝ) + 2 * fourCellOperatorHalfWidth * R < 11 / 50
  nlinarith

private theorem fourCellOddSignedMassRegularQuadratic_P9_lt_one_hundred_seventy_three_thousandths :
    fourCellOddSignedMassRegularQuadratic factorTwoCenteredP9 <
      (173 / 1000 : ℝ) := by
  let R : ℝ := ∫ t : ℝ in 0..2,
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
      centeredEndpointCorrelation factorTwoCenteredP9 t
  have hcorr := abs_fourCellRegularCorrelation_le_one_twentieth_centeredMass
    factorTwoCenteredP9 continuous_factorTwoCenteredP9
      odd_factorTwoCenteredP9
  have henergy := factorTwoCenteredP9_energy
  unfold factorTwoIntrinsicEnergy at henergy
  rw [henergy] at hcorr
  change |R| ≤ (1 / 20 : ℝ) * (2 / 19) at hcorr
  norm_num at hcorr
  have ha0 : 0 ≤ fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  have ha := fourCellOperatorHalfWidth_le_one_half
  have hregular : 2 * fourCellOperatorHalfWidth * R ≤ (1 / 190 : ℝ) := by
    calc
      2 * fourCellOperatorHalfWidth * R ≤
          2 * fourCellOperatorHalfWidth * |R| :=
        mul_le_mul_of_nonneg_left (le_abs_self R)
          (mul_nonneg (by norm_num) ha0)
      _ ≤ 2 * (1 / 2 : ℝ) * |R| := by
        exact mul_le_mul_of_nonneg_right (by nlinarith) (abs_nonneg R)
      _ ≤ 2 * (1 / 2 : ℝ) * (1 / 190 : ℝ) := by
        exact mul_le_mul_of_nonneg_left hcorr (by norm_num)
      _ = (1 / 190 : ℝ) := by norm_num
  have hscalar := fourCellScalar_lt_31577_div_20000
  unfold fourCellOddSignedMassRegularQuadratic
  rw [integral_zero_one_P9_sq]
  change
    (2 * (Real.log (2 * fourCellOperatorHalfWidth) +
        Real.eulerMascheroniConstant + Real.log Real.pi) + 3 / 200) *
        (1 / 19 : ℝ) + 2 * fourCellOperatorHalfWidth * R < 173 / 1000
  nlinarith

private theorem one_fifth_lt_fourCellOddCoreLocalQuadratic_P7 :
    (1 / 5 : ℝ) < fourCellOddCoreLocalQuadratic factorTwoCenteredP7 := by
  rw [fourCellOddCoreLocalQuadratic_eq_retained_sub_signed]
  linarith [two_hundred_eleven_five_hundredths_lt_retained_P7,
    fourCellOddSignedMassRegularQuadratic_P7_lt_eleven_fiftieths]

private theorem twenty_nine_two_hundredths_lt_fourCellOddCoreLocalQuadratic_P9 :
    (29 / 200 : ℝ) < fourCellOddCoreLocalQuadratic factorTwoCenteredP9 := by
  rw [fourCellOddCoreLocalQuadratic_eq_retained_sub_signed]
  linarith [one_hundred_fifty_nine_five_hundredths_lt_retained_P9,
    fourCellOddSignedMassRegularQuadratic_P9_lt_one_hundred_seventy_three_thousandths]

/-! ### Tight finite-core boxes for the five-mode certificate -/

private theorem abs_fourCellWideRegularEnvelopeError11_tight_le :
    |fourCellWideRegularEnvelopeError oddStructuralCorrelation11| ≤
      (1 / 120000 : ℝ) := by
  have herr := abs_fourCellWideRegularEnvelopeError_le_sevenEighths
    oddStructuralCorrelation11
      (by unfold oddStructuralCorrelation11; fun_prop)
  have hmass := integral_abs_oddStructuralCorrelation11_le
  nlinarith

private theorem abs_fourCellWideRegularEnvelopeError13_tight_lt :
    |fourCellWideRegularEnvelopeError oddStructuralCorrelation13| <
      (1 / 480000 : ℝ) := by
  have herr := abs_fourCellWideRegularEnvelopeError_le_sevenEighths
    oddStructuralCorrelation13
      (by unfold oddStructuralCorrelation13; fun_prop)
  have hmass := integral_abs_oddStructuralCorrelation13_lt
  nlinarith

private theorem abs_fourCellWideRegularEnvelopeError33_tight_le :
    |fourCellWideRegularEnvelopeError oddStructuralCorrelation33| ≤
      (1 / 280000 : ℝ) := by
  have herr := abs_fourCellWideRegularEnvelopeError_le_sevenEighths
    oddStructuralCorrelation33
      (by unfold oddStructuralCorrelation33; fun_prop)
  have hmass := integral_abs_oddStructuralCorrelation33_le
  nlinarith

private theorem abs_fourCellWideRegularEnvelopeError15_tight_lt :
    |fourCellWideRegularEnvelopeError oddP5Correlation15| <
      (1 / 1000000 : ℝ) := by
  have herr := abs_fourCellWideRegularEnvelopeError_le_sevenEighths
    oddP5Correlation15 (by unfold oddP5Correlation15; fun_prop)
  have hmass := integral_abs_oddP5Correlation15_lt
  nlinarith

private theorem abs_fourCellWideRegularEnvelopeError35_tight_lt :
    |fourCellWideRegularEnvelopeError oddP5Correlation35| <
      (11 / 10000000 : ℝ) := by
  have herr := abs_fourCellWideRegularEnvelopeError_le_sevenEighths
    oddP5Correlation35 (by unfold oddP5Correlation35; fun_prop)
  have hmass := integral_abs_oddP5Correlation35_lt
  nlinarith

private theorem abs_fourCellWideRegularEnvelopeError55_tight_le :
    |fourCellWideRegularEnvelopeError oddP5Correlation55| ≤
      (1 / 440000 : ℝ) := by
  have herr := abs_fourCellWideRegularEnvelopeError_le_sevenEighths
    oddP5Correlation55 continuous_oddP5Correlation55
  have hmass := integral_abs_oddP5Correlation55_le
  nlinarith

set_option maxHeartbeats 1000000 in
private theorem fourCellOddOneThreeFiveRegular_entry_tight_bounds :
    (4855 / 1000000 : ℝ) < fourCellOddOneThreeFiveRegular11 ∧
    fourCellOddOneThreeFiveRegular11 < (4873 / 1000000 : ℝ) ∧
    (-193 / 1000000 : ℝ) < fourCellOddOneThreeFiveRegular13 ∧
    fourCellOddOneThreeFiveRegular13 < (-188 / 1000000 : ℝ) ∧
    (111 / 1000000 : ℝ) < fourCellOddOneThreeFiveRegular33 ∧
    fourCellOddOneThreeFiveRegular33 < (120 / 1000000 : ℝ) ∧
    (-1 / 1000000 : ℝ) < fourCellOddOneThreeFiveRegular15 ∧
    fourCellOddOneThreeFiveRegular15 < (2 / 1000000 : ℝ) ∧
    (-28 / 1000000 : ℝ) < fourCellOddOneThreeFiveRegular35 ∧
    fourCellOddOneThreeFiveRegular35 < (-24 / 1000000 : ℝ) ∧
    (25 / 1000000 : ℝ) < fourCellOddOneThreeFiveRegular55 ∧
    fourCellOddOneThreeFiveRegular55 < (31 / 1000000 : ℝ) := by
  rcases fourCellWideRegularPolynomial_entry_bounds with
    ⟨hP11lo, hP11hi, hP13lo, hP13hi, hP33lo, hP33hi,
      hP15lo, hP15hi, hP35lo, hP35hi, hP55lo, hP55hi⟩
  rcases fourCellOddOneThreeFiveRegular_entries_eq with
    ⟨h11, h13, h33, h15, h35, h55⟩
  have he11 := abs_le.mp abs_fourCellWideRegularEnvelopeError11_tight_le
  have he13 := abs_lt.mp abs_fourCellWideRegularEnvelopeError13_tight_lt
  have he33 := abs_le.mp abs_fourCellWideRegularEnvelopeError33_tight_le
  have he15 := abs_lt.mp abs_fourCellWideRegularEnvelopeError15_tight_lt
  have he35 := abs_lt.mp abs_fourCellWideRegularEnvelopeError35_tight_lt
  have he55 := abs_le.mp abs_fourCellWideRegularEnvelopeError55_tight_le
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

set_option maxHeartbeats 1000000 in
private theorem fourCellOddOneThreeFiveCombined_entry_certificate_bounds :
    (251905 / 1000000 : ℝ) < fourCellOddLowCombined11 ∧
    fourCellOddLowCombined11 < (251925 / 1000000 : ℝ) ∧
    (218622 / 1000000 : ℝ) < fourCellOddLowCombined13 ∧
    fourCellOddLowCombined13 < (218624 / 1000000 : ℝ) ∧
    (205150 / 1000000 : ℝ) < fourCellOddLowCombined33 ∧
    fourCellOddLowCombined33 < (205156 / 1000000 : ℝ) ∧
    (135290 / 10000000 : ℝ) < fourCellOddOneThreeFiveCombined15 ∧
    fourCellOddOneThreeFiveCombined15 < (135293 / 10000000 : ℝ) ∧
    (629389 / 10000000 : ℝ) < fourCellOddOneThreeFiveCombined35 ∧
    fourCellOddOneThreeFiveCombined35 < (629392 / 10000000 : ℝ) ∧
    (245090 / 1000000 : ℝ) < fourCellOddOneThreeFiveCombined55 ∧
    fourCellOddOneThreeFiveCombined55 < (245094 / 1000000 : ℝ) := by
  have hL := strict_log_two_fine_bounds
  have hP := fourCell_sqrt_two_mul_log_two_fine_bounds
  have hT := fourCellScalar_fine_bounds
  have h11 : fourCellOddLowCombined11 =
      893 / 600 - (31 / 50 : ℝ) * Real.log 2 +
        (94 / 375 : ℝ) * (Real.sqrt 2 * Real.log 2) -
          (2 / 3 : ℝ) *
            (Real.log (2 * fourCellOperatorHalfWidth) +
              Real.eulerMascheroniConstant + Real.log Real.pi) := by
    unfold fourCellOddLowCombined11 fourCellOddLowLocalAlgebraic11
    ring
  have h13 : fourCellOddLowCombined13 =
      93 / 500 + (104 / 3125 : ℝ) *
        (Real.sqrt 2 * Real.log 2) := by
    unfold fourCellOddLowCombined13 fourCellOddLowLocalAlgebraic13
    ring
  have h33 : fourCellOddLowCombined33 =
      5434921 / 6125000 - (5242 / 109375 : ℝ) *
          (Real.sqrt 2 * Real.log 2) -
        (93 / 350 : ℝ) * Real.log 2 -
        (2 / 7 : ℝ) *
          (Real.log (2 * fourCellOperatorHalfWidth) +
            Real.eulerMascheroniConstant + Real.log Real.pi) := by
    unfold fourCellOddLowCombined33 fourCellOddLowLocalAlgebraic33
    ring
  have h15 : fourCellOddOneThreeFiveCombined15 =
      93 / 1400 - (4216 / 78125 : ℝ) *
        (Real.sqrt 2 * Real.log 2) := by
    unfold fourCellOddOneThreeFiveCombined15
      fourCellOddOneThreeFiveLocalAlgebraic15
    ring
  have h35 : fourCellOddOneThreeFiveCombined35 =
      96779 / 937500 - (16056 / 390625 : ℝ) *
        (Real.sqrt 2 * Real.log 2) := by
    unfold fourCellOddOneThreeFiveCombined35
      fourCellOddOneThreeFiveLocalAlgebraic35
    ring
  have h55 : fourCellOddOneThreeFiveCombined55 =
      1602471330659 / 2481445312500 +
        (1933534 / 537109375 : ℝ) *
          (Real.sqrt 2 * Real.log 2) -
        (93 / 550 : ℝ) * Real.log 2 -
        (2 / 11 : ℝ) *
          (Real.log (2 * fourCellOperatorHalfWidth) +
            Real.eulerMascheroniConstant + Real.log Real.pi) := by
    unfold fourCellOddOneThreeFiveCombined55
      fourCellOddOneThreeFiveLocalAlgebraic55
    ring
  rw [h11, h13, h33, h15, h35, h55]
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

set_option maxHeartbeats 1000000 in
private theorem fourCellOddOneThreeFivePerturbed_entry_certificate_bounds :
    (247682 / 1000000 : ℝ) < fourCellOddOneThreeFivePerturbed11 ∧
    fourCellOddOneThreeFivePerturbed11 < (247719 / 1000000 : ℝ) ∧
    (218784 / 1000000 : ℝ) < fourCellOddOneThreeFivePerturbed13 ∧
    fourCellOddOneThreeFivePerturbed13 < (218792 / 1000000 : ℝ) ∧
    (205046 / 1000000 : ℝ) < fourCellOddOneThreeFivePerturbed33 ∧
    fourCellOddOneThreeFivePerturbed33 < (205060 / 1000000 : ℝ) ∧
    (13527 / 1000000 : ℝ) < fourCellOddOneThreeFivePerturbed15 ∧
    fourCellOddOneThreeFivePerturbed15 < (13531 / 1000000 : ℝ) ∧
    (62959 / 1000000 : ℝ) < fourCellOddOneThreeFivePerturbed35 ∧
    fourCellOddOneThreeFivePerturbed35 < (62964 / 1000000 : ℝ) ∧
    (245063 / 1000000 : ℝ) < fourCellOddOneThreeFivePerturbed55 ∧
    fourCellOddOneThreeFivePerturbed55 < (245073 / 1000000 : ℝ) := by
  let W : ℝ := 2 * fourCellOperatorHalfWidth
  rcases two_mul_fourCellOperatorHalfWidth_fine_bounds with ⟨hWlo, hWhi⟩
  change (8664 / 10000 : ℝ) < W at hWlo
  change W < (8665 / 10000 : ℝ) at hWhi
  have hW0 : 0 < W := hWlo.trans' (by norm_num)
  rcases fourCellOddOneThreeFiveCombined_entry_certificate_bounds with
    ⟨hAlo, hAhi, hBlo, hBhi, hDlo, hDhi,
      hElo, hEhi, hFlo, hFhi, hGlo, hGhi⟩
  rcases fourCellOddOneThreeFiveRegular_entry_tight_bounds with
    ⟨h11lo, h11hi, h13lo, h13hi, h33lo, h33hi,
      h15lo, h15hi, h35lo, h35hi, h55lo, h55hi⟩
  have hpositiveProduct {R lo hi : ℝ}
      (hlo : lo < R) (hhi : R < hi) (hlo0 : 0 < lo) :
      (8664 / 10000 : ℝ) * lo < W * R ∧
        W * R < (8665 / 10000 : ℝ) * hi := by
    have hR0 : 0 < R := hlo0.trans hlo
    constructor
    · exact (mul_lt_mul_of_pos_right hWlo hlo0).trans
        (mul_lt_mul_of_pos_left hlo hW0)
    · exact (mul_lt_mul_of_pos_left hhi hW0).trans
        (mul_lt_mul_of_pos_right hWhi (by linarith))
  have hnegativeProduct {R lo hi : ℝ}
      (hlo : lo < R) (hhi : R < hi) (hhi0 : hi < 0) :
      (8665 / 10000 : ℝ) * lo < W * R ∧
        W * R < (8664 / 10000 : ℝ) * hi := by
    constructor
    · exact (mul_lt_mul_of_neg_right hWhi (by linarith)).trans
        (mul_lt_mul_of_pos_left hlo hW0)
    · exact (mul_lt_mul_of_pos_left hhi hW0).trans
        (mul_lt_mul_of_neg_right hWlo hhi0)
  have hcrossProduct {R lo hi : ℝ}
      (hlo : lo < R) (hhi : R < hi) (hlo0 : lo < 0) (hhi0 : 0 < hi) :
      (8665 / 10000 : ℝ) * lo < W * R ∧
        W * R < (8665 / 10000 : ℝ) * hi := by
    constructor
    · exact (mul_lt_mul_of_neg_right hWhi hlo0).trans
        (mul_lt_mul_of_pos_left hlo hW0)
    · exact (mul_lt_mul_of_pos_left hhi hW0).trans
        (mul_lt_mul_of_pos_right hWhi hhi0)
  have hW11 := hpositiveProduct h11lo h11hi (by norm_num)
  have hW13 := hnegativeProduct h13lo h13hi (by norm_num)
  have hW33 := hpositiveProduct h33lo h33hi (by norm_num)
  have hW15 := hcrossProduct h15lo h15hi (by norm_num) (by norm_num)
  have hW35 := hnegativeProduct h35lo h35hi (by norm_num)
  have hW55 := hpositiveProduct h55lo h55hi (by norm_num)
  unfold fourCellOddOneThreeFivePerturbed11
    fourCellOddOneThreeFivePerturbed13
    fourCellOddOneThreeFivePerturbed33
    fourCellOddOneThreeFivePerturbed15
    fourCellOddOneThreeFivePerturbed35
    fourCellOddOneThreeFivePerturbed55
  change
    (247682 / 1000000 : ℝ) <
        fourCellOddLowCombined11 - W * fourCellOddOneThreeFiveRegular11 ∧ _
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

private def oddP5P7CorrelationLocal (t : ℝ) : ℝ :=
  -t + (13 / 2 : ℝ) * t ^ 2 - (21 / 2 : ℝ) * t ^ 3 +
    (35 / 4 : ℝ) * t ^ 5 - (21 / 4 : ℝ) * t ^ 7 +
    (225 / 128 : ℝ) * t ^ 9 - (77 / 256 : ℝ) * t ^ 11 +
    (21 / 1024 : ℝ) * t ^ 13

private def oddP5P9CorrelationLocal (t : ℝ) : ℝ :=
  -t + 15 * t ^ 2 - 70 * t ^ 3 + (1105 / 8 : ℝ) * t ^ 4 -
    (441 / 4 : ℝ) * t ^ 5 + (315 / 8 : ℝ) * t ^ 7 -
    (1815 / 128 : ℝ) * t ^ 9 + (429 / 128 : ℝ) * t ^ 11 -
    (455 / 1024 : ℝ) * t ^ 13 + (51 / 2048 : ℝ) * t ^ 15

set_option maxHeartbeats 1000000 in
private theorem factorTwoCenteredCorrelationBilinear_P5_P7_local
    (t : ℝ) :
    factorTwoCenteredCorrelationBilinear
        factorTwoCenteredP5 factorTwoCenteredP7 t =
      oddP5P7CorrelationLocal t := by
  unfold factorTwoCenteredCorrelationBilinear
  rw [factorTwoCenteredCrossCorrelation_swap_of_odd_odd
    odd_factorTwoCenteredP5 odd_factorTwoCenteredP7]
  unfold factorTwoCenteredCrossCorrelation factorTwoCenteredP5
  simp_rw [factorTwoCenteredP7_eq]
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (-1) (1 - t))
    (Continuous.intervalIntegrable (by fun_prop) (-1) (1 - t))]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [intervalIntegral.integral_const_mul]
  repeat rw [integral_pow]
  repeat rw [integral_id]
  unfold oddP5P7CorrelationLocal
  ring

set_option maxHeartbeats 1000000 in
private theorem factorTwoCenteredCorrelationBilinear_P5_P9_local
    (t : ℝ) :
    factorTwoCenteredCorrelationBilinear
        factorTwoCenteredP5 factorTwoCenteredP9 t =
      oddP5P9CorrelationLocal t := by
  unfold factorTwoCenteredCorrelationBilinear
  rw [factorTwoCenteredCrossCorrelation_swap_of_odd_odd
    odd_factorTwoCenteredP5 odd_factorTwoCenteredP9]
  unfold factorTwoCenteredCrossCorrelation factorTwoCenteredP5
  simp_rw [factorTwoCenteredP9_eq]
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (-1) (1 - t))
    (Continuous.intervalIntegrable (by fun_prop) (-1) (1 - t))]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [intervalIntegral.integral_const_mul]
  repeat rw [integral_pow]
  repeat rw [integral_id]
  unfold oddP5P9CorrelationLocal
  ring

private theorem neg_beta_sq_sum_le_two_mul_of_abs_le
    (B β x y : ℝ) (hB : |B| ≤ β) (hβ : 0 ≤ β) :
    -β * (x ^ 2 + y ^ 2) ≤ 2 * B * x * y := by
  have hxy : 2 * |x * y| ≤ x ^ 2 + y ^ 2 := by
    rw [abs_mul]
    nlinarith [sq_nonneg (|x| - |y|), sq_abs x, sq_abs y]
  have habs : |2 * B * x * y| ≤ β * (x ^ 2 + y ^ 2) := by
    calc
      |2 * B * x * y| = 2 * |B| * |x * y| := by
        rw [abs_mul (2 * B * x) y, abs_mul (2 * B) x,
          abs_mul 2 B, abs_mul x y,
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        ring
      _ ≤ 2 * β * |x * y| := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hB (by norm_num)) (abs_nonneg _)
      _ = β * (2 * |x * y|) := by ring
      _ ≤ β * (x ^ 2 + y ^ 2) :=
        mul_le_mul_of_nonneg_left hxy hβ
  calc
    -β * (x ^ 2 + y ^ 2) ≤ -|2 * B * x * y| := by
      linarith
    _ ≤ 2 * B * x * y := neg_abs_le _

/-- The actual `P₅/P₇/P₉` complete-form matrix is positive
semidefinite.  This is a symbolic diagonal-dominance certificate for the
true quadratic and cross entries, not a sampled or truncated surrogate. -/
theorem fourCellOddCoreLocal_P5_P7_P9_matrix_nonneg (c d e : ℝ) :
    0 ≤
      fourCellOddCoreLocalQuadratic factorTwoCenteredP5 * c ^ 2 +
        2 * fourCellOddCoreLocalBilinear
            factorTwoCenteredP5 factorTwoCenteredP7 * c * d +
        fourCellOddCoreLocalQuadratic factorTwoCenteredP7 * d ^ 2 +
        2 * fourCellOddCoreLocalBilinear
            factorTwoCenteredP5 factorTwoCenteredP9 * c * e +
        2 * fourCellOddCoreLocalBilinear
            factorTwoCenteredP7 factorTwoCenteredP9 * d * e +
        fourCellOddCoreLocalQuadratic factorTwoCenteredP9 * e ^ 2 := by
  let Q5 := fourCellOddCoreLocalQuadratic factorTwoCenteredP5
  let Q7 := fourCellOddCoreLocalQuadratic factorTwoCenteredP7
  let Q9 := fourCellOddCoreLocalQuadratic factorTwoCenteredP9
  let B57 := fourCellOddCoreLocalBilinear
    factorTwoCenteredP5 factorTwoCenteredP7
  let B59 := fourCellOddCoreLocalBilinear
    factorTwoCenteredP5 factorTwoCenteredP9
  let B79 := fourCellOddCoreLocalBilinear
    factorTwoCenteredP7 factorTwoCenteredP9
  have hQ5 : (6 / 25 : ℝ) < Q5 :=
    six_twenty_fifths_lt_fourCellOddCoreLocalQuadratic_P5
  have hQ7 : (1 / 5 : ℝ) < Q7 :=
    one_fifth_lt_fourCellOddCoreLocalQuadratic_P7
  have hQ9 : (29 / 200 : ℝ) < Q9 :=
    twenty_nine_two_hundredths_lt_fourCellOddCoreLocalQuadratic_P9
  have h57abs : |B57| ≤ (21 / 200 : ℝ) :=
    abs_fourCellOddCoreLocalBilinear_P5_P7_lt_twenty_one_two_hundredths.le
  have h59abs : |B59| ≤ (7 / 200 : ℝ) :=
    abs_fourCellOddCoreLocalBilinear_P5_P9_lt_seven_two_hundredths.le
  have h79abs : |B79| ≤ (11 / 500 : ℝ) :=
    abs_fourCellOddCoreLocalBilinear_P7_P9_lt_eleven_five_hundredths.le
  have hQ5c : (6 / 25 : ℝ) * c ^ 2 ≤ Q5 * c ^ 2 :=
    mul_le_mul_of_nonneg_right hQ5.le (sq_nonneg c)
  have hQ7d : (1 / 5 : ℝ) * d ^ 2 ≤ Q7 * d ^ 2 :=
    mul_le_mul_of_nonneg_right hQ7.le (sq_nonneg d)
  have hQ9e : (29 / 200 : ℝ) * e ^ 2 ≤ Q9 * e ^ 2 :=
    mul_le_mul_of_nonneg_right hQ9.le (sq_nonneg e)
  have h57 := neg_beta_sq_sum_le_two_mul_of_abs_le
    B57 (21 / 200) c d h57abs (by norm_num)
  have h59 := neg_beta_sq_sum_le_two_mul_of_abs_le
    B59 (7 / 200) c e h59abs (by norm_num)
  have h79 := neg_beta_sq_sum_le_two_mul_of_abs_le
    B79 (11 / 500) d e h79abs (by norm_num)
  have hmargin : 0 ≤
      ((6 / 25 : ℝ) - 21 / 200 - 7 / 200) * c ^ 2 +
        ((1 / 5 : ℝ) - 21 / 200 - 11 / 500) * d ^ 2 +
        ((29 / 200 : ℝ) - 7 / 200 - 11 / 500) * e ^ 2 := by
    positivity
  dsimp only [Q5, Q7, Q9, B57, B59, B79] at hQ5c hQ7d hQ9e h57 h59 h79 ⊢
  linarith

/-! ### The missing `P₁/P₃`--`P₇/P₉` finite cross block -/

private theorem fourCellOddEndpointStripEvenMassBilinear_P1_P7 :
    fourCellOddEndpointStripEvenMassBilinear
        centeredP1 factorTwoCenteredP7 =
      (-4192 / 1953125 : ℝ) := by
  unfold fourCellOddEndpointStripEvenMassBilinear centeredP1
  simp_rw [fourCellOddEndpointStripEven_P7]
  rw [show (fun z : ℝ ↦
      fourCellOddEndpointStripEven (fun x : ℝ ↦ x) z *
        ((3003 / 312500 : ℝ) * z ^ 6 +
          (30723 / 62500 : ℝ) * z ^ 4 +
          (124929 / 312500 : ℝ) * z ^ 2 - 74891 / 312500)) =
      fun z ↦
        (-299564 / 1562500 : ℝ) * z ^ 0 + 0 * z ^ 1 +
          (499716 / 1562500 : ℝ) * z ^ 2 + 0 * z ^ 3 +
          (122892 / 312500 : ℝ) * z ^ 4 + 0 * z ^ 5 +
          (12012 / 1562500 : ℝ) * z ^ 6 + 0 * z ^ 7 +
          0 * z ^ 8 + 0 * z ^ 9 + 0 * z ^ 10 + 0 * z ^ 11 +
          0 * z ^ 12 + 0 * z ^ 13 by
    funext z
    unfold fourCellOddEndpointStripEven fourCellOddEndpointStripPullback
    ring,
    integral_polynomial_thirteen]
  norm_num

private theorem fourCellOddEndpointStripOddMassBilinear_P1_P7 :
    fourCellOddEndpointStripOddMassBilinear
        centeredP1 factorTwoCenteredP7 =
      (-6536 / 1953125 : ℝ) := by
  rcases endpointStripOdd_P7_moments with ⟨h1, _h3, _h5⟩
  unfold fourCellOddEndpointStripOddMassBilinear centeredP1
  rw [show fourCellOddEndpointStripOdd (fun x : ℝ ↦ x) =
      fun z ↦ z / 5 by
    funext z
    unfold fourCellOddEndpointStripOdd fourCellOddEndpointStripPullback
    ring]
  have hrewrite :
      (∫ z : ℝ in -1..1,
        (z / 5) * fourCellOddEndpointStripOdd factorTwoCenteredP7 z) =
        (1 / 5 : ℝ) *
          ∫ z : ℝ in -1..1,
            fourCellOddEndpointStripOdd factorTwoCenteredP7 z * z := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro z _hz
    ring
  rw [hrewrite]
  unfold centeredP1 at h1
  rw [h1]
  norm_num

private theorem integral_zero_one_endpointPotential_mul_P1_mul_P7 :
    (∫ x : ℝ in 0..1,
      yoshidaEndpointPotential x * centeredP1 x *
        factorTwoCenteredP7 x) = (1 / 54 : ℝ) := by
  have h7 : factorTwoCenteredP7 =
      fun x ↦ -(centeredShiftedLegendreReal 7).eval x := by
    funext x
    rw [eval_centeredShiftedLegendreReal]
    rfl
  have hfull :=
    YoshidaEndpointPotentialLegendreOffDiagonalStructural.integral_endpointPotential_mul_centeredShiftedLegendreReal_of_even
      (m := 1) (n := 7) (by norm_num) (by norm_num)
  norm_num at hfull
  have hfullActual : (∫ x : ℝ in -1..1,
      yoshidaEndpointPotential x * centeredP1 x *
        factorTwoCenteredP7 x) = (1 / 27 : ℝ) := by
    unfold centeredP1
    rw [h7]
    rw [show (fun x : ℝ ↦
        yoshidaEndpointPotential x * x *
          (-(centeredShiftedLegendreReal 7).eval x)) =
        fun x ↦ -(yoshidaEndpointPotential x * x *
          (centeredShiftedLegendreReal 7).eval x) by
      funext x
      ring,
      intervalIntegral.integral_neg]
    exact hfull
  let q : ℝ → ℝ := fun x ↦
    yoshidaEndpointPotential x * centeredP1 x * factorTwoCenteredP7 x
  have hq : IntervalIntegrable q volume (-1) 1 := by
    dsimp only [q]
    simpa only [mul_assoc] using
      YoshidaEndpointPotentialIntegrable.intervalIntegrable_endpointPotential_mul
        (fun x : ℝ ↦ centeredP1 x * factorTwoCenteredP7 x)
        ((by unfold centeredP1; fun_prop : Continuous centeredP1).mul
          continuous_factorTwoCenteredP7)
  have hqeven : Function.Even q := by
    intro x
    dsimp only [q]
    have hp : yoshidaEndpointPotential (-x) =
        yoshidaEndpointPotential x := by
      unfold yoshidaEndpointPotential
      congr 2
      ring
    rw [hp, odd_factorTwoCenteredP7]
    unfold centeredP1
    ring
  have hfold := integral_neg_one_one_eq_two_mul_zero_one_of_even q hq hqeven
  dsimp only [q] at hfold
  rw [hfullActual] at hfold
  linarith

private theorem fourCellOddRetainedPrimePotentialBilinear_P1_P7 :
    fourCellOddRetainedPrimePotentialBilinear
        centeredP1 factorTwoCenteredP7 =
      Real.sqrt 2 * Real.log 2 * (-4192 / 1953125 : ℝ) +
        (2 - Real.sqrt 2 * Real.log 2) *
          (-6536 / 1953125 : ℝ) +
        (93 / 50 : ℝ) * (1 / 54) := by
  unfold fourCellOddRetainedPrimePotentialBilinear
  rw [fourCellOddEndpointStripEvenMassBilinear_P1_P7,
    fourCellOddEndpointStripOddMassBilinear_P1_P7,
    integral_zero_one_endpointPotential_mul_P1_mul_P7]

/-- Exact retained endpoint entry on the first previously missing finite
row.  The global raw form vanishes by shifted-Legendre orthogonality; the
display contains only the affine-strip raw moment, two prime channels, and
the all-degree endpoint-potential Green entry. -/
theorem fourCellOddRetainedEndpointBilinear_P1_P7_eq :
    fourCellOddRetainedEndpointBilinear
        centeredP1 factorTwoCenteredP7 =
      (13072 / 1953125 : ℝ) +
        Real.sqrt 2 * Real.log 2 * (-4192 / 1953125 : ℝ) +
        (2 - Real.sqrt 2 * Real.log 2) *
          (-6536 / 1953125 : ℝ) +
        (93 / 50 : ℝ) * (1 / 54) := by
  rcases centeredOddCoefficients_P7_eq_zero with ⟨h1, h3, h5⟩
  have h := fourCellOddRetainedEndpointBilinear_oneThreeFive_tail_eq_moments
    factorTwoCenteredP7 contDiff_factorTwoCenteredP7_local
      odd_factorTwoCenteredP7 h1 h3 h5 1 0 0
  have hp : fourCellOddOneThreeFiveLowProfile 1 0 0 = centeredP1 := by
    funext x
    unfold fourCellOddOneThreeFiveLowProfile
      factorTwoOddStructuralLowProfile
    simp
  rw [hp, fourCellOddRetainedPrimePotentialBilinear_P1_P7] at h
  rcases endpointStripOdd_P7_moments with ⟨hm1, hm3, hm5⟩
  rw [hm1, hm3, hm5] at h
  norm_num at h ⊢
  convert h using 1
  ring

private def oddP7Correlation17Local (t : ℝ) : ℝ :=
  -t + (27 / 2 : ℝ) * t ^ 2 - (175 / 3 : ℝ) * t ^ 3 +
    (231 / 2 : ℝ) * t ^ 4 - (945 / 8 : ℝ) * t ^ 5 +
      (1001 / 16 : ℝ) * t ^ 6 - (231 / 16 : ℝ) * t ^ 7 +
        (143 / 384 : ℝ) * t ^ 9

private theorem factorTwoCenteredCorrelationBilinear_P1_P7
    (t : ℝ) :
    factorTwoCenteredCorrelationBilinear centeredP1 factorTwoCenteredP7 t =
      oddP7Correlation17Local t := by
  unfold factorTwoCenteredCorrelationBilinear
    factorTwoCenteredCrossCorrelation centeredP1
  rw [show (fun x : ℝ ↦ (t + x) * factorTwoCenteredP7 x) =
      fun x ↦
        0 * x ^ 0 + (-35 * t / 16 : ℝ) * x ^ 1 +
          (-35 / 16 : ℝ) * x ^ 2 + (315 * t / 16 : ℝ) * x ^ 3 +
          (315 / 16 : ℝ) * x ^ 4 + (-693 * t / 16 : ℝ) * x ^ 5 +
          (-693 / 16 : ℝ) * x ^ 6 + (429 * t / 16 : ℝ) * x ^ 7 +
          (429 / 16 : ℝ) * x ^ 8 + 0 * x ^ 9 + 0 * x ^ 10 +
          0 * x ^ 11 + 0 * x ^ 12 + 0 * x ^ 13 by
    funext x
    rw [factorTwoCenteredP7_eq]
    ring,
    integral_polynomial_thirteen]
  rw [show (fun x : ℝ ↦ factorTwoCenteredP7 (t + x) * x) =
      fun x ↦
        0 * x ^ 0 +
          (-35 * t / 16 + 315 * t ^ 3 / 16 - 693 * t ^ 5 / 16 +
            429 * t ^ 7 / 16 : ℝ) * x ^ 1 +
          (-35 / 16 + 945 * t ^ 2 / 16 - 3465 * t ^ 4 / 16 +
            3003 * t ^ 6 / 16 : ℝ) * x ^ 2 +
          (945 * t / 16 - 3465 * t ^ 3 / 8 +
            9009 * t ^ 5 / 16 : ℝ) * x ^ 3 +
          (315 / 16 - 3465 * t ^ 2 / 8 +
            15015 * t ^ 4 / 16 : ℝ) * x ^ 4 +
          (-3465 * t / 16 + 15015 * t ^ 3 / 16 : ℝ) * x ^ 5 +
          (-693 / 16 + 9009 * t ^ 2 / 16 : ℝ) * x ^ 6 +
          (3003 * t / 16 : ℝ) * x ^ 7 +
          (429 / 16 : ℝ) * x ^ 8 + 0 * x ^ 9 + 0 * x ^ 10 +
          0 * x ^ 11 + 0 * x ^ 12 + 0 * x ^ 13 by
    funext x
    rw [factorTwoCenteredP7_eq]
    ring,
    integral_polynomial_thirteen]
  unfold oddP7Correlation17Local
  ring

set_option maxHeartbeats 1000000 in
private theorem integral_fourCellRegularPolynomial_mul_oddP7Correlation17Local :
    (∫ t : ℝ in 0..2,
      yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t) *
        oddP7Correlation17Local t) =
      -(3875 / 21424936845312 : ℝ) * Real.log 2 ^ 5 := by
  unfold yoshidaRegularKernelPolynomial6 fourCellOperatorHalfWidth
    oddP7Correlation17Local
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [intervalIntegral.integral_const_mul]
  repeat rw [integral_pow]
  norm_num
  ring

/-- The smooth wide-kernel correction to the exact `P₁/P₇` endpoint
row is two orders of magnitude smaller than the endpoint entry.  The proof
uses the global sixth-order analytic envelope and exact correlation moments;
there is no quadrature or sampled kernel bound. -/
theorem abs_integral_fourCellRegularKernel_mul_correlation_P1_P7_lt :
    |∫ t : ℝ in 0..2,
      yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
        factorTwoCenteredCorrelationBilinear
          centeredP1 factorTwoCenteredP7 t| < (1 / 5000 : ℝ) := by
  let C : ℝ → ℝ := oddP7Correlation17Local
  let I : ℝ := ∫ t : ℝ in 0..2, |C t|
  let P : ℝ := -(3875 / 21424936845312 : ℝ) * Real.log 2 ^ 5
  let E : ℝ := fourCellWideRegularEnvelopeError C
  have hC : Continuous C := by
    dsimp only [C]
    unfold oddP7Correlation17Local
    fun_prop
  have hdecomp := fourCellRegularIntegral_eq_polynomial_add_error C hC
  rw [integral_fourCellRegularPolynomial_mul_oddP7Correlation17Local]
    at hdecomp
  change (∫ t : ℝ in 0..2,
      yoshidaRegularKernel (fourCellOperatorHalfWidth * t) * C t) =
        P + E at hdecomp
  have hI0 : 0 ≤ I := by
    dsimp only [I]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun _t _ht ↦ abs_nonneg _)
  have hE1 : factorTwoIntrinsicEnergy centeredP1 = (2 / 3 : ℝ) := by
    unfold factorTwoIntrinsicEnergy centeredP1
    rw [integral_pow]
    norm_num
  have hI2 : I ^ 2 ≤ (2 / 3 : ℝ) * (2 / 15) := by
    have h :=
      ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP67ResidualAnalyticSchurStructural.integral_abs_factorTwoCenteredCorrelationBilinear_sq_le_energy_mul
        centeredP1 factorTwoCenteredP7
          (by unfold centeredP1; fun_prop) continuous_factorTwoCenteredP7
    rw [hE1, factorTwoCenteredP7_energy] at h
    simp_rw [factorTwoCenteredCorrelationBilinear_P1_P7] at h
    simpa only [I, C] using h
  have hIlt : I < (3 / 10 : ℝ) := by
    nlinarith
  have herr := abs_fourCellWideRegularEnvelopeError_le C hC
  change |E| ≤ (1 / 1900 : ℝ) * I at herr
  have herrlt : |E| < (3 / 19000 : ℝ) := by
    calc
      |E| ≤ (1 / 1900 : ℝ) * I := herr
      _ < (1 / 1900 : ℝ) * (3 / 10) :=
        mul_lt_mul_of_pos_left hIlt (by norm_num)
      _ = (3 / 19000 : ℝ) := by norm_num
  have hpow := (fourCell_log_two_pow_fine_bounds 5 (by norm_num)).2
  have hlog0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogPow0 : 0 < Real.log 2 ^ 5 := pow_pos hlog0 5
  have hPneg : P < 0 := by
    dsimp only [P]
    nlinarith
  have hPabs : |P| < (1 / 1000000 : ℝ) := by
    rw [abs_of_neg hPneg]
    dsimp only [P]
    nlinarith
  simp_rw [factorTwoCenteredCorrelationBilinear_P1_P7]
  change |(∫ t : ℝ in 0..2,
      yoshidaRegularKernel (fourCellOperatorHalfWidth * t) * C t)| < _
  rw [hdecomp]
  calc
    |P + E| ≤ |P| + |E| := abs_add_le P E
    _ < (1 / 1000000 : ℝ) + 3 / 19000 :=
      add_lt_add hPabs herrlt
    _ < (1 / 5000 : ℝ) := by norm_num

private theorem integral_zero_one_P1_mul_P7 :
    (∫ x : ℝ in 0..1, centeredP1 x * factorTwoCenteredP7 x) = 0 := by
  rcases centeredOddCoefficients_P7_eq_zero with ⟨h1, h3, h5⟩
  have h := integral_zero_one_oneThreeFiveLowProfile_mul_tail_eq_zero
    factorTwoCenteredP7 continuous_factorTwoCenteredP7
      odd_factorTwoCenteredP7 h1 h3 h5 1 0 0
  have hp : fourCellOddOneThreeFiveLowProfile 1 0 0 = centeredP1 := by
    funext x
    unfold fourCellOddOneThreeFiveLowProfile
      factorTwoOddStructuralLowProfile
    simp
  simpa only [hp] using h

private theorem fourCellOddSignedMassRegularBilinear_P1_P7_eq :
    fourCellOddSignedMassRegularBilinear centeredP1 factorTwoCenteredP7 =
      2 * fourCellOperatorHalfWidth *
        (∫ t : ℝ in 0..2,
          yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
            factorTwoCenteredCorrelationBilinear
              centeredP1 factorTwoCenteredP7 t) := by
  unfold fourCellOddSignedMassRegularBilinear
  rw [integral_zero_one_P1_mul_P7]
  ring

private theorem abs_fourCellOddSignedMassRegularBilinear_P1_P7_lt :
    |fourCellOddSignedMassRegularBilinear centeredP1 factorTwoCenteredP7| <
      (1 / 5000 : ℝ) := by
  let R : ℝ := ∫ t : ℝ in 0..2,
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
      factorTwoCenteredCorrelationBilinear centeredP1 factorTwoCenteredP7 t
  have hR : |R| < (1 / 5000 : ℝ) := by
    simpa only [R] using
      abs_integral_fourCellRegularKernel_mul_correlation_P1_P7_lt
  have ha0 : 0 ≤ 2 * fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  have ha : 2 * fourCellOperatorHalfWidth ≤ (1 : ℝ) := by
    linarith [fourCellOperatorHalfWidth_le_one_half]
  rw [fourCellOddSignedMassRegularBilinear_P1_P7_eq]
  change |2 * fourCellOperatorHalfWidth * R| < _
  rw [abs_mul, abs_of_nonneg ha0]
  calc
    2 * fourCellOperatorHalfWidth * |R| ≤ 1 * |R| :=
      mul_le_mul_of_nonneg_right ha (abs_nonneg R)
    _ < 1 * (1 / 5000 : ℝ) :=
      mul_lt_mul_of_pos_left hR (by norm_num)
    _ = (1 / 5000 : ℝ) := one_mul _

private theorem fourCellOddRetainedEndpointBilinear_P1_P7_bounds :
    (89 / 2500 : ℝ) <
        fourCellOddRetainedEndpointBilinear centeredP1 factorTwoCenteredP7 ∧
      fourCellOddRetainedEndpointBilinear centeredP1 factorTwoCenteredP7 <
        (357 / 10000 : ℝ) := by
  rw [fourCellOddRetainedEndpointBilinear_P1_P7_eq]
  rcases sqrt_two_mul_log_two_bounds with ⟨hklo, hkhi⟩
  constructor <;> nlinarith

/-- Tight complete-form enclosure for the first missing finite entry.  The
interval combines the exact endpoint row with the preceding analytic
wide-kernel remainder; no independent raw or prime estimates are inserted.
-/
theorem fourCellOddCoreLocalBilinear_P1_P7_bounds :
    (177 / 5000 : ℝ) <
        fourCellOddCoreLocalBilinear centeredP1 factorTwoCenteredP7 ∧
      fourCellOddCoreLocalBilinear centeredP1 factorTwoCenteredP7 <
        (18 / 500 : ℝ) := by
  rw [fourCellOddCoreLocalBilinear_eq_retained_sub_signed]
  rcases fourCellOddRetainedEndpointBilinear_P1_P7_bounds with
    ⟨hretlo, hrethi⟩
  have hsigned := abs_fourCellOddSignedMassRegularBilinear_P1_P7_lt
  have hsignedLo := neg_abs_le
    (fourCellOddSignedMassRegularBilinear centeredP1 factorTwoCenteredP7)
  have hsignedHi := le_abs_self
    (fourCellOddSignedMassRegularBilinear centeredP1 factorTwoCenteredP7)
  constructor <;> linarith

private theorem fourCellOddEndpointStripEvenMassBilinear_P3_P7 :
    fourCellOddEndpointStripEvenMassBilinear
        centeredP3 factorTwoCenteredP7 =
      (324032 / 48828125 : ℝ) := by
  unfold fourCellOddEndpointStripEvenMassBilinear
  rw [show fourCellOddEndpointStripEven centeredP3 = fun z : ℝ ↦
      (2 / 25 : ℝ) + (6 / 25 : ℝ) * z ^ 2 by
    funext z
    unfold fourCellOddEndpointStripEven fourCellOddEndpointStripPullback
      centeredP3
    ring]
  simp_rw [fourCellOddEndpointStripEven_P7]
  rw [show (fun z : ℝ ↦
      ((2 / 25 : ℝ) + (6 / 25 : ℝ) * z ^ 2) *
        ((3003 / 312500 : ℝ) * z ^ 6 +
          (30723 / 62500 : ℝ) * z ^ 4 +
          (124929 / 312500 : ℝ) * z ^ 2 - 74891 / 312500)) =
      fun z ↦
        (-74891 / 3906250 : ℝ) * z ^ 0 + 0 * z ^ 1 +
          (-49872 / 1953125 : ℝ) * z ^ 2 + 0 * z ^ 3 +
          (264201 / 1953125 : ℝ) * z ^ 4 + 0 * z ^ 5 +
          (231924 / 1953125 : ℝ) * z ^ 6 + 0 * z ^ 7 +
          (9009 / 3906250 : ℝ) * z ^ 8 + 0 * z ^ 9 +
          0 * z ^ 10 + 0 * z ^ 11 + 0 * z ^ 12 + 0 * z ^ 13 by
    funext z
    ring,
    integral_polynomial_thirteen]
  norm_num

private theorem fourCellOddEndpointStripOddMassBilinear_P3_P7 :
    fourCellOddEndpointStripOddMassBilinear
        centeredP3 factorTwoCenteredP7 =
      (-538952 / 48828125 : ℝ) := by
  unfold fourCellOddEndpointStripOddMassBilinear
  rw [show fourCellOddEndpointStripOdd centeredP3 = fun z : ℝ ↦
      (33 / 50 : ℝ) * z + (1 / 50 : ℝ) * z ^ 3 by
    funext z
    unfold fourCellOddEndpointStripOdd fourCellOddEndpointStripPullback
      centeredP3
    ring]
  simp_rw [fourCellOddEndpointStripOdd_P7]
  rw [show (fun z : ℝ ↦
      ((33 / 50 : ℝ) * z + (1 / 50 : ℝ) * z ^ 3) *
        ((429 / 1250000 : ℝ) * z ^ 7 +
          (126819 / 1250000 : ℝ) * z ^ 5 +
          (253743 / 250000 : ℝ) * z ^ 3 -
          (972587 / 1250000 : ℝ) * z)) =
      fun z ↦
        0 * z ^ 0 + 0 * z ^ 1 +
          (-32095371 / 62500000 : ℝ) * z ^ 2 + 0 * z ^ 3 +
          (1277969 / 1953125 : ℝ) * z ^ 4 + 0 * z ^ 5 +
          (2726871 / 31250000 : ℝ) * z ^ 6 + 0 * z ^ 7 +
          (8811 / 3906250 : ℝ) * z ^ 8 + 0 * z ^ 9 +
          (429 / 62500000 : ℝ) * z ^ 10 + 0 * z ^ 11 +
          0 * z ^ 12 + 0 * z ^ 13 by
    funext z
    ring,
    integral_polynomial_thirteen]
  norm_num

private theorem integral_zero_one_endpointPotential_mul_P3_mul_P7 :
    (∫ x : ℝ in 0..1,
      yoshidaEndpointPotential x * centeredP3 x *
        factorTwoCenteredP7 x) = (1 / 44 : ℝ) := by
  have h7 : factorTwoCenteredP7 =
      fun x ↦ -(centeredShiftedLegendreReal 7).eval x := by
    funext x
    rw [eval_centeredShiftedLegendreReal]
    rfl
  have hfull :=
    YoshidaEndpointPotentialLegendreOffDiagonalStructural.integral_endpointPotential_mul_centeredShiftedLegendreReal_of_even
      (m := 3) (n := 7) (by norm_num) (by norm_num)
  norm_num at hfull
  have hfullActual : (∫ x : ℝ in -1..1,
      yoshidaEndpointPotential x * centeredP3 x *
        factorTwoCenteredP7 x) = (1 / 22 : ℝ) := by
    rw [h7]
    unfold centeredP3
    rw [show (fun x : ℝ ↦
        yoshidaEndpointPotential x * ((5 * x ^ 3 - 3 * x) / 2) *
          (-(centeredShiftedLegendreReal 7).eval x)) = fun x ↦
        -(yoshidaEndpointPotential x *
          (1 / 2 * (5 * x ^ 3 - 3 * x)) *
            (centeredShiftedLegendreReal 7).eval x) by
      funext x
      ring,
      intervalIntegral.integral_neg]
    exact hfull
  let f : ℝ → ℝ := fun x ↦
    yoshidaEndpointPotential x * centeredP3 x * factorTwoCenteredP7 x
  have hf : IntervalIntegrable f volume (-1) 1 := by
    dsimp only [f]
    simpa only [mul_assoc] using
      intervalIntegrable_endpointPotential_mul
        (fun x : ℝ ↦ centeredP3 x * factorTwoCenteredP7 x)
        ((by unfold centeredP3; fun_prop : Continuous centeredP3).mul
          continuous_factorTwoCenteredP7)
  have hfeven : Function.Even f := by
    intro x
    dsimp only [f]
    have hp : yoshidaEndpointPotential (-x) =
        yoshidaEndpointPotential x := by
      unfold yoshidaEndpointPotential
      congr 2
      ring
    rw [hp, odd_factorTwoCenteredP7]
    unfold centeredP3
    ring
  have hfold := integral_neg_one_one_eq_two_mul_zero_one_of_even f hf hfeven
  dsimp only [f] at hfold
  rw [hfullActual] at hfold
  linarith

private theorem fourCellOddRetainedPrimePotentialBilinear_P3_P7 :
    fourCellOddRetainedPrimePotentialBilinear
        centeredP3 factorTwoCenteredP7 =
      Real.sqrt 2 * Real.log 2 * (324032 / 48828125 : ℝ) +
        (2 - Real.sqrt 2 * Real.log 2) *
          (-538952 / 48828125 : ℝ) +
        (93 / 50 : ℝ) * (1 / 44) := by
  unfold fourCellOddRetainedPrimePotentialBilinear
  rw [fourCellOddEndpointStripEvenMassBilinear_P3_P7,
    fourCellOddEndpointStripOddMassBilinear_P3_P7,
    integral_zero_one_endpointPotential_mul_P3_mul_P7]

/-- Exact retained endpoint entry on the `P₃/P₇` row.  Its raw part is
reduced to the two endpoint-strip moments and its potential part to the
all-degree Legendre Green formula. -/
theorem fourCellOddRetainedEndpointBilinear_P3_P7_eq :
    fourCellOddRetainedEndpointBilinear
        centeredP3 factorTwoCenteredP7 =
      (3183352 / 146484375 : ℝ) +
        Real.sqrt 2 * Real.log 2 * (324032 / 48828125 : ℝ) +
        (2 - Real.sqrt 2 * Real.log 2) *
          (-538952 / 48828125 : ℝ) +
        (93 / 50 : ℝ) * (1 / 44) := by
  rcases centeredOddCoefficients_P7_eq_zero with ⟨h1, h3, h5⟩
  have h := fourCellOddRetainedEndpointBilinear_oneThreeFive_tail_eq_moments
    factorTwoCenteredP7 contDiff_factorTwoCenteredP7_local
      odd_factorTwoCenteredP7 h1 h3 h5 0 1 0
  have hp : fourCellOddOneThreeFiveLowProfile 0 1 0 = centeredP3 := by
    funext x
    unfold fourCellOddOneThreeFiveLowProfile
      factorTwoOddStructuralLowProfile
    simp
  rw [hp, fourCellOddRetainedPrimePotentialBilinear_P3_P7] at h
  rcases endpointStripOdd_P7_moments with ⟨hm1, hm3, hm5⟩
  rw [hm1, hm3, hm5] at h
  norm_num at h ⊢
  convert h using 1
  ring

private theorem integral_zero_one_P3_mul_P7 :
    (∫ x : ℝ in 0..1, centeredP3 x * factorTwoCenteredP7 x) = 0 := by
  rcases centeredOddCoefficients_P7_eq_zero with ⟨h1, h3, h5⟩
  have h := integral_zero_one_oneThreeFiveLowProfile_mul_tail_eq_zero
    factorTwoCenteredP7 continuous_factorTwoCenteredP7
      odd_factorTwoCenteredP7 h1 h3 h5 0 1 0
  have hp : fourCellOddOneThreeFiveLowProfile 0 1 0 = centeredP3 := by
    funext x
    unfold fourCellOddOneThreeFiveLowProfile
      factorTwoOddStructuralLowProfile
    simp
  simpa only [hp] using h

private theorem fourCellOddSignedMassRegularBilinear_P3_P7_eq :
    fourCellOddSignedMassRegularBilinear centeredP3 factorTwoCenteredP7 =
      2 * fourCellOperatorHalfWidth *
        (∫ t : ℝ in 0..2,
          yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
            factorTwoCenteredCorrelationBilinear
              centeredP3 factorTwoCenteredP7 t) := by
  unfold fourCellOddSignedMassRegularBilinear
  rw [integral_zero_one_P3_mul_P7]
  ring

private theorem abs_fourCellOddSignedMassRegularBilinear_P3_P7_lt :
    |fourCellOddSignedMassRegularBilinear centeredP3 factorTwoCenteredP7| <
      (1 / 100000 : ℝ) := by
  let R : ℝ := ∫ t : ℝ in 0..2,
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
      factorTwoCenteredCorrelationBilinear centeredP3 factorTwoCenteredP7 t
  have hR : |R| < (1 / 100000 : ℝ) := by
    simpa only [R] using
      abs_integral_fourCellRegularKernel_mul_correlation_P3_P7_lt
  have ha0 : 0 ≤ 2 * fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  have ha : 2 * fourCellOperatorHalfWidth ≤ (1 : ℝ) := by
    linarith [fourCellOperatorHalfWidth_le_one_half]
  rw [fourCellOddSignedMassRegularBilinear_P3_P7_eq]
  change |2 * fourCellOperatorHalfWidth * R| < _
  rw [abs_mul, abs_of_nonneg ha0]
  calc
    2 * fourCellOperatorHalfWidth * |R| ≤ 1 * |R| :=
      mul_le_mul_of_nonneg_right ha (abs_nonneg R)
    _ < 1 * (1 / 100000 : ℝ) :=
      mul_lt_mul_of_pos_left hR (by norm_num)
    _ = (1 / 100000 : ℝ) := one_mul _

private theorem fourCellOddRetainedEndpointBilinear_P3_P7_bounds :
    (237 / 4000 : ℝ) <
        fourCellOddRetainedEndpointBilinear centeredP3 factorTwoCenteredP7 ∧
      fourCellOddRetainedEndpointBilinear centeredP3 factorTwoCenteredP7 <
        (2963 / 50000 : ℝ) := by
  rw [fourCellOddRetainedEndpointBilinear_P3_P7_eq]
  rcases sqrt_two_mul_log_two_bounds with ⟨hklo, hkhi⟩
  constructor <;> nlinarith

/-- Tight complete-form enclosure for the `P₃/P₇` row.  The only
non-endpoint correction is the analytic regular-kernel envelope imported
above. -/
theorem fourCellOddCoreLocalBilinear_P3_P7_bounds :
    (1481 / 25000 : ℝ) <
        fourCellOddCoreLocalBilinear centeredP3 factorTwoCenteredP7 ∧
      fourCellOddCoreLocalBilinear centeredP3 factorTwoCenteredP7 <
        (5927 / 100000 : ℝ) := by
  rw [fourCellOddCoreLocalBilinear_eq_retained_sub_signed]
  rcases fourCellOddRetainedEndpointBilinear_P3_P7_bounds with
    ⟨hretlo, hrethi⟩
  have hsigned := abs_fourCellOddSignedMassRegularBilinear_P3_P7_lt
  have hsignedLo := neg_abs_le
    (fourCellOddSignedMassRegularBilinear centeredP3 factorTwoCenteredP7)
  have hsignedHi := le_abs_self
    (fourCellOddSignedMassRegularBilinear centeredP3 factorTwoCenteredP7)
  constructor <;> linarith

private theorem fourCellOddEndpointStripEvenMassBilinear_P1_P9 :
    fourCellOddEndpointStripEvenMassBilinear
        centeredP1 factorTwoCenteredP9 =
      (937504 / 48828125 : ℝ) := by
  unfold fourCellOddEndpointStripEvenMassBilinear
  rw [show fourCellOddEndpointStripEven centeredP1 = fun _z : ℝ ↦
      (4 / 5 : ℝ) by
    funext z
    unfold fourCellOddEndpointStripEven fourCellOddEndpointStripPullback
      centeredP1
    ring]
  simp_rw [fourCellOddEndpointStripEven_P9]
  rw [show (fun z : ℝ ↦
      (4 / 5 : ℝ) *
        ((21879 / 12500000 : ℝ) * z ^ 8 +
          (591591 / 3125000 : ℝ) * z ^ 6 +
          (8801793 / 6250000 : ℝ) * z ^ 4 -
          (4094541 / 3125000 : ℝ) * z ^ 2 +
          2348191 / 12500000)) = fun z ↦
      (2348191 / 15625000 : ℝ) * z ^ 0 + 0 * z ^ 1 +
        (-4094541 / 3906250 : ℝ) * z ^ 2 + 0 * z ^ 3 +
        (8801793 / 7812500 : ℝ) * z ^ 4 + 0 * z ^ 5 +
        (591591 / 3906250 : ℝ) * z ^ 6 + 0 * z ^ 7 +
        (21879 / 15625000 : ℝ) * z ^ 8 + 0 * z ^ 9 +
        0 * z ^ 10 + 0 * z ^ 11 + 0 * z ^ 12 + 0 * z ^ 13 +
        0 * z ^ 14 + 0 * z ^ 15 by
    funext z
    ring,
    integral_polynomial_fifteen_local]
  norm_num

private theorem fourCellOddEndpointStripOddMassBilinear_P1_P9 :
    fourCellOddEndpointStripOddMassBilinear
        centeredP1 factorTwoCenteredP9 =
      (-202024 / 48828125 : ℝ) := by
  rcases endpointStripOdd_P9_moments with ⟨h1, _h3, _h5⟩
  unfold fourCellOddEndpointStripOddMassBilinear centeredP1
  rw [show fourCellOddEndpointStripOdd (fun x : ℝ ↦ x) =
      fun z ↦ z / 5 by
    funext z
    unfold fourCellOddEndpointStripOdd fourCellOddEndpointStripPullback
    ring]
  have hrewrite :
      (∫ z : ℝ in -1..1,
        (z / 5) * fourCellOddEndpointStripOdd factorTwoCenteredP9 z) =
        (1 / 5 : ℝ) *
          ∫ z : ℝ in -1..1,
            fourCellOddEndpointStripOdd factorTwoCenteredP9 z * z := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro z _hz
    ring
  rw [hrewrite]
  unfold centeredP1 at h1
  rw [h1]
  norm_num

private theorem integral_zero_one_endpointPotential_mul_P1_mul_P9 :
    (∫ x : ℝ in 0..1,
      yoshidaEndpointPotential x * centeredP1 x *
        factorTwoCenteredP9 x) = (1 / 88 : ℝ) := by
  have h9 : factorTwoCenteredP9 =
      fun x ↦ -(centeredShiftedLegendreReal 9).eval x := by
    funext x
    rw [eval_centeredShiftedLegendreReal]
    rfl
  have hfull :=
    YoshidaEndpointPotentialLegendreOffDiagonalStructural.integral_endpointPotential_mul_centeredShiftedLegendreReal_of_even
      (m := 1) (n := 9) (by norm_num) (by norm_num)
  norm_num at hfull
  have hfullActual : (∫ x : ℝ in -1..1,
      yoshidaEndpointPotential x * centeredP1 x *
        factorTwoCenteredP9 x) = (1 / 44 : ℝ) := by
    unfold centeredP1
    rw [h9]
    rw [show (fun x : ℝ ↦
        yoshidaEndpointPotential x * x *
          (-(centeredShiftedLegendreReal 9).eval x)) = fun x ↦
        -(yoshidaEndpointPotential x * x *
          (centeredShiftedLegendreReal 9).eval x) by
      funext x
      ring,
      intervalIntegral.integral_neg]
    exact hfull
  let f : ℝ → ℝ := fun x ↦
    yoshidaEndpointPotential x * centeredP1 x * factorTwoCenteredP9 x
  have hf : IntervalIntegrable f volume (-1) 1 := by
    dsimp only [f]
    simpa only [mul_assoc] using
      intervalIntegrable_endpointPotential_mul
        (fun x : ℝ ↦ centeredP1 x * factorTwoCenteredP9 x)
        ((by unfold centeredP1; fun_prop : Continuous centeredP1).mul
          continuous_factorTwoCenteredP9)
  have hfeven : Function.Even f := by
    intro x
    dsimp only [f]
    have hp : yoshidaEndpointPotential (-x) =
        yoshidaEndpointPotential x := by
      unfold yoshidaEndpointPotential
      congr 2
      ring
    rw [hp, odd_factorTwoCenteredP9]
    unfold centeredP1
    ring
  have hfold := integral_neg_one_one_eq_two_mul_zero_one_of_even f hf hfeven
  dsimp only [f] at hfold
  rw [hfullActual] at hfold
  linarith

private theorem fourCellOddRetainedPrimePotentialBilinear_P1_P9 :
    fourCellOddRetainedPrimePotentialBilinear
        centeredP1 factorTwoCenteredP9 =
      Real.sqrt 2 * Real.log 2 * (937504 / 48828125 : ℝ) +
        (2 - Real.sqrt 2 * Real.log 2) *
          (-202024 / 48828125 : ℝ) +
        (93 / 50 : ℝ) * (1 / 88) := by
  unfold fourCellOddRetainedPrimePotentialBilinear
  rw [fourCellOddEndpointStripEvenMassBilinear_P1_P9,
    fourCellOddEndpointStripOddMassBilinear_P1_P9,
    integral_zero_one_endpointPotential_mul_P1_mul_P9]

/-- Exact retained endpoint entry on the `P₁/P₉` row. -/
theorem fourCellOddRetainedEndpointBilinear_P1_P9_eq :
    fourCellOddRetainedEndpointBilinear
        centeredP1 factorTwoCenteredP9 =
      (404048 / 48828125 : ℝ) +
        Real.sqrt 2 * Real.log 2 * (937504 / 48828125 : ℝ) +
        (2 - Real.sqrt 2 * Real.log 2) *
          (-202024 / 48828125 : ℝ) +
        (93 / 50 : ℝ) * (1 / 88) := by
  rcases centeredOddCoefficients_P9_eq_zero with ⟨h1, h3, h5⟩
  have h := fourCellOddRetainedEndpointBilinear_oneThreeFive_tail_eq_moments
    factorTwoCenteredP9 contDiff_factorTwoCenteredP9_local
      odd_factorTwoCenteredP9 h1 h3 h5 1 0 0
  have hp : fourCellOddOneThreeFiveLowProfile 1 0 0 = centeredP1 := by
    funext x
    unfold fourCellOddOneThreeFiveLowProfile
      factorTwoOddStructuralLowProfile
    simp
  rw [hp, fourCellOddRetainedPrimePotentialBilinear_P1_P9] at h
  rcases endpointStripOdd_P9_moments with ⟨hm1, hm3, hm5⟩
  rw [hm1, hm3, hm5] at h
  norm_num at h ⊢
  convert h using 1
  ring

private def oddP9Correlation19Local (t : ℝ) : ℝ :=
  -t + 22 * t ^ 2 - (315 / 2 : ℝ) * t ^ 3 +
    (2145 / 4 : ℝ) * t ^ 4 - (8085 / 8 : ℝ) * t ^ 5 +
      (9009 / 8 : ℝ) * t ^ 6 - (3003 / 4 : ℝ) * t ^ 7 +
        (36465 / 128 : ℝ) * t ^ 8 - (6435 / 128 : ℝ) * t ^ 9 +
          (221 / 256 : ℝ) * t ^ 11

private theorem factorTwoCenteredCorrelationBilinear_P1_P9
    (t : ℝ) :
    factorTwoCenteredCorrelationBilinear centeredP1 factorTwoCenteredP9 t =
      oddP9Correlation19Local t := by
  unfold factorTwoCenteredCorrelationBilinear
    factorTwoCenteredCrossCorrelation centeredP1
  rw [show (fun x : ℝ ↦ (t + x) * factorTwoCenteredP9 x) =
      fun x ↦
        0 * x ^ 0 + (315 * t / 128 : ℝ) * x ^ 1 +
          (315 / 128 : ℝ) * x ^ 2 +
          (-1155 * t / 32 : ℝ) * x ^ 3 +
          (-1155 / 32 : ℝ) * x ^ 4 +
          (9009 * t / 64 : ℝ) * x ^ 5 +
          (9009 / 64 : ℝ) * x ^ 6 +
          (-6435 * t / 32 : ℝ) * x ^ 7 +
          (-6435 / 32 : ℝ) * x ^ 8 +
          (12155 * t / 128 : ℝ) * x ^ 9 +
          (12155 / 128 : ℝ) * x ^ 10 + 0 * x ^ 11 +
          0 * x ^ 12 + 0 * x ^ 13 by
    funext x
    rw [factorTwoCenteredP9_eq]
    ring,
    integral_polynomial_thirteen]
  rw [show (fun x : ℝ ↦ factorTwoCenteredP9 (t + x) * x) =
      fun x ↦
        0 * x ^ 0 +
          (315 * t / 128 - 1155 * t ^ 3 / 32 +
            9009 * t ^ 5 / 64 - 6435 * t ^ 7 / 32 +
            12155 * t ^ 9 / 128 : ℝ) * x ^ 1 +
          (315 / 128 - 3465 * t ^ 2 / 32 +
            45045 * t ^ 4 / 64 - 45045 * t ^ 6 / 32 +
            109395 * t ^ 8 / 128 : ℝ) * x ^ 2 +
          (-3465 * t / 32 + 45045 * t ^ 3 / 32 -
            135135 * t ^ 5 / 32 + 109395 * t ^ 7 / 32 : ℝ) * x ^ 3 +
          (-1155 / 32 + 45045 * t ^ 2 / 32 -
            225225 * t ^ 4 / 32 + 255255 * t ^ 6 / 32 : ℝ) * x ^ 4 +
          (45045 * t / 64 - 225225 * t ^ 3 / 32 +
            765765 * t ^ 5 / 64 : ℝ) * x ^ 5 +
          (9009 / 64 - 135135 * t ^ 2 / 32 +
            765765 * t ^ 4 / 64 : ℝ) * x ^ 6 +
          (-45045 * t / 32 + 255255 * t ^ 3 / 32 : ℝ) * x ^ 7 +
          (-6435 / 32 + 109395 * t ^ 2 / 32 : ℝ) * x ^ 8 +
          (109395 * t / 128 : ℝ) * x ^ 9 +
          (12155 / 128 : ℝ) * x ^ 10 + 0 * x ^ 11 +
          0 * x ^ 12 + 0 * x ^ 13 by
    funext x
    rw [factorTwoCenteredP9_eq]
    ring,
    integral_polynomial_thirteen]
  unfold oddP9Correlation19Local
  ring

set_option maxHeartbeats 1000000 in
private theorem integral_fourCellRegularPolynomial_mul_oddP9Correlation19Local :
    (∫ t : ℝ in 0..2,
      yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t) *
        oddP9Correlation19Local t) = 0 := by
  unfold yoshidaRegularKernelPolynomial6 fourCellOperatorHalfWidth
    oddP9Correlation19Local
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [intervalIntegral.integral_const_mul]
  repeat rw [integral_pow]
  norm_num
  ring

/-- The `P₁/P₉` smooth row is small because every moment seen by the
sixth-order kernel polynomial vanishes exactly.  Only the global analytic
envelope remains. -/
theorem abs_integral_fourCellRegularKernel_mul_correlation_P1_P9_lt :
    |∫ t : ℝ in 0..2,
      yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
        factorTwoCenteredCorrelationBilinear
          centeredP1 factorTwoCenteredP9 t| < (1 / 7000 : ℝ) := by
  let C : ℝ → ℝ := oddP9Correlation19Local
  let I : ℝ := ∫ t : ℝ in 0..2, |C t|
  let E : ℝ := fourCellWideRegularEnvelopeError C
  have hC : Continuous C := by
    dsimp only [C]
    unfold oddP9Correlation19Local
    fun_prop
  have hdecomp := fourCellRegularIntegral_eq_polynomial_add_error C hC
  rw [integral_fourCellRegularPolynomial_mul_oddP9Correlation19Local]
    at hdecomp
  change (∫ t : ℝ in 0..2,
      yoshidaRegularKernel (fourCellOperatorHalfWidth * t) * C t) =
        0 + E at hdecomp
  have hI0 : 0 ≤ I := by
    dsimp only [I]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun _t _ht ↦ abs_nonneg _)
  have hE1 : factorTwoIntrinsicEnergy centeredP1 = (2 / 3 : ℝ) := by
    unfold factorTwoIntrinsicEnergy centeredP1
    rw [integral_pow]
    norm_num
  have hI2 : I ^ 2 ≤ (2 / 3 : ℝ) * (2 / 19) := by
    have h :=
      ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP67ResidualAnalyticSchurStructural.integral_abs_factorTwoCenteredCorrelationBilinear_sq_le_energy_mul
        centeredP1 factorTwoCenteredP9
          (by unfold centeredP1; fun_prop) continuous_factorTwoCenteredP9
    rw [hE1, factorTwoCenteredP9_energy] at h
    simp_rw [factorTwoCenteredCorrelationBilinear_P1_P9] at h
    simpa only [I, C] using h
  have hIlt : I < (27 / 100 : ℝ) := by
    nlinarith
  have herr := abs_fourCellWideRegularEnvelopeError_le C hC
  change |E| ≤ (1 / 1900 : ℝ) * I at herr
  have herrlt : |E| < (27 / 190000 : ℝ) := by
    calc
      |E| ≤ (1 / 1900 : ℝ) * I := herr
      _ < (1 / 1900 : ℝ) * (27 / 100) :=
        mul_lt_mul_of_pos_left hIlt (by norm_num)
      _ = (27 / 190000 : ℝ) := by norm_num
  simp_rw [factorTwoCenteredCorrelationBilinear_P1_P9]
  change |(∫ t : ℝ in 0..2,
      yoshidaRegularKernel (fourCellOperatorHalfWidth * t) * C t)| < _
  rw [hdecomp, zero_add]
  exact herrlt.trans (by norm_num)

private theorem integral_zero_one_P1_mul_P9 :
    (∫ x : ℝ in 0..1, centeredP1 x * factorTwoCenteredP9 x) = 0 := by
  rcases centeredOddCoefficients_P9_eq_zero with ⟨h1, h3, h5⟩
  have h := integral_zero_one_oneThreeFiveLowProfile_mul_tail_eq_zero
    factorTwoCenteredP9 continuous_factorTwoCenteredP9
      odd_factorTwoCenteredP9 h1 h3 h5 1 0 0
  have hp : fourCellOddOneThreeFiveLowProfile 1 0 0 = centeredP1 := by
    funext x
    unfold fourCellOddOneThreeFiveLowProfile
      factorTwoOddStructuralLowProfile
    simp
  simpa only [hp] using h

private theorem fourCellOddSignedMassRegularBilinear_P1_P9_eq :
    fourCellOddSignedMassRegularBilinear centeredP1 factorTwoCenteredP9 =
      2 * fourCellOperatorHalfWidth *
        (∫ t : ℝ in 0..2,
          yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
            factorTwoCenteredCorrelationBilinear
              centeredP1 factorTwoCenteredP9 t) := by
  unfold fourCellOddSignedMassRegularBilinear
  rw [integral_zero_one_P1_mul_P9]
  ring

private theorem abs_fourCellOddSignedMassRegularBilinear_P1_P9_lt :
    |fourCellOddSignedMassRegularBilinear centeredP1 factorTwoCenteredP9| <
      (1 / 7000 : ℝ) := by
  let R : ℝ := ∫ t : ℝ in 0..2,
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
      factorTwoCenteredCorrelationBilinear centeredP1 factorTwoCenteredP9 t
  have hR : |R| < (1 / 7000 : ℝ) := by
    simpa only [R] using
      abs_integral_fourCellRegularKernel_mul_correlation_P1_P9_lt
  have ha0 : 0 ≤ 2 * fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  have ha : 2 * fourCellOperatorHalfWidth ≤ (1 : ℝ) := by
    linarith [fourCellOperatorHalfWidth_le_one_half]
  rw [fourCellOddSignedMassRegularBilinear_P1_P9_eq]
  change |2 * fourCellOperatorHalfWidth * R| < _
  rw [abs_mul, abs_of_nonneg ha0]
  calc
    2 * fourCellOperatorHalfWidth * |R| ≤ 1 * |R| :=
      mul_le_mul_of_nonneg_right ha (abs_nonneg R)
    _ < 1 * (1 / 7000 : ℝ) :=
      mul_lt_mul_of_pos_left hR (by norm_num)
    _ = (1 / 7000 : ℝ) := one_mul _

private theorem fourCellOddRetainedEndpointBilinear_P1_P9_bounds :
    (11 / 250 : ℝ) <
        fourCellOddRetainedEndpointBilinear centeredP1 factorTwoCenteredP9 ∧
      fourCellOddRetainedEndpointBilinear centeredP1 factorTwoCenteredP9 <
        (2201 / 50000 : ℝ) := by
  rw [fourCellOddRetainedEndpointBilinear_P1_P9_eq]
  rcases sqrt_two_mul_log_two_bounds with ⟨hklo, hkhi⟩
  constructor <;> nlinarith

/-- Complete-form enclosure for the `P₁/P₉` row. -/
theorem fourCellOddCoreLocalBilinear_P1_P9_bounds :
    (219 / 5000 : ℝ) <
        fourCellOddCoreLocalBilinear centeredP1 factorTwoCenteredP9 ∧
      fourCellOddCoreLocalBilinear centeredP1 factorTwoCenteredP9 <
        (111 / 2500 : ℝ) := by
  rw [fourCellOddCoreLocalBilinear_eq_retained_sub_signed]
  rcases fourCellOddRetainedEndpointBilinear_P1_P9_bounds with
    ⟨hretlo, hrethi⟩
  have hsigned := abs_fourCellOddSignedMassRegularBilinear_P1_P9_lt
  have hsignedLo := neg_abs_le
    (fourCellOddSignedMassRegularBilinear centeredP1 factorTwoCenteredP9)
  have hsignedHi := le_abs_self
    (fourCellOddSignedMassRegularBilinear centeredP1 factorTwoCenteredP9)
  constructor <;> linarith

private theorem fourCellOddEndpointStripEvenMassBilinear_P3_P9 :
    fourCellOddEndpointStripEvenMassBilinear
        centeredP3 factorTwoCenteredP9 =
      (1006528 / 244140625 : ℝ) := by
  unfold fourCellOddEndpointStripEvenMassBilinear
  rw [show fourCellOddEndpointStripEven centeredP3 = fun z : ℝ ↦
      (2 / 25 : ℝ) + (6 / 25 : ℝ) * z ^ 2 by
    funext z
    unfold fourCellOddEndpointStripEven fourCellOddEndpointStripPullback
      centeredP3
    ring]
  simp_rw [fourCellOddEndpointStripEven_P9]
  rw [show (fun z : ℝ ↦
      ((2 / 25 : ℝ) + (6 / 25 : ℝ) * z ^ 2) *
        ((21879 / 12500000 : ℝ) * z ^ 8 +
          (591591 / 3125000 : ℝ) * z ^ 6 +
          (8801793 / 6250000 : ℝ) * z ^ 4 -
          (4094541 / 3125000 : ℝ) * z ^ 2 +
          2348191 / 12500000)) = fun z ↦
      (2348191 / 156250000 : ℝ) * z ^ 0 + 0 * z ^ 1 +
        (-9333591 / 156250000 : ℝ) * z ^ 2 + 0 * z ^ 3 +
        (-15765453 / 78125000 : ℝ) * z ^ 4 + 0 * z ^ 5 +
        (27588561 / 78125000 : ℝ) * z ^ 6 + 0 * z ^ 7 +
        (7120971 / 156250000 : ℝ) * z ^ 8 + 0 * z ^ 9 +
        (65637 / 156250000 : ℝ) * z ^ 10 + 0 * z ^ 11 +
        0 * z ^ 12 + 0 * z ^ 13 + 0 * z ^ 14 + 0 * z ^ 15 by
    funext z
    ring,
    integral_polynomial_fifteen_local]
  norm_num

private theorem fourCellOddEndpointStripOddMassBilinear_P3_P9 :
    fourCellOddEndpointStripOddMassBilinear
        centeredP3 factorTwoCenteredP9 =
      (-3329608 / 244140625 : ℝ) := by
  unfold fourCellOddEndpointStripOddMassBilinear
  rw [show fourCellOddEndpointStripOdd centeredP3 = fun z : ℝ ↦
      (33 / 50 : ℝ) * z + (1 / 50 : ℝ) * z ^ 3 by
    funext z
    unfold fourCellOddEndpointStripOdd fourCellOddEndpointStripPullback
      centeredP3
    ring]
  simp_rw [fourCellOddEndpointStripOdd_P9]
  rw [show (fun z : ℝ ↦
      ((33 / 50 : ℝ) * z + (1 / 50 : ℝ) * z ^ 3) *
        ((2431 / 50000000 : ℝ) * z ^ 9 +
          (317889 / 12500000 : ℝ) * z ^ 7 +
          (18711693 / 25000000 : ℝ) * z ^ 5 +
          (7297521 / 12500000 : ℝ) * z ^ 3 -
          (41734881 / 50000000 : ℝ) * z)) = fun z ↦
      0 * z ^ 0 + 0 * z ^ 1 +
        (-1377251073 / 2500000000 : ℝ) * z ^ 2 + 0 * z ^ 3 +
        (921537891 / 2500000000 : ℝ) * z ^ 4 + 0 * z ^ 5 +
        (632080911 / 1250000000 : ℝ) * z ^ 6 + 0 * z ^ 7 +
        (39692367 / 1250000000 : ℝ) * z ^ 8 + 0 * z ^ 9 +
        (1351779 / 2500000000 : ℝ) * z ^ 10 + 0 * z ^ 11 +
        (2431 / 2500000000 : ℝ) * z ^ 12 + 0 * z ^ 13 +
        0 * z ^ 14 + 0 * z ^ 15 by
    funext z
    ring,
    integral_polynomial_fifteen_local]
  norm_num

private theorem integral_zero_one_endpointPotential_mul_P3_mul_P9 :
    (∫ x : ℝ in 0..1,
      yoshidaEndpointPotential x * centeredP3 x *
        factorTwoCenteredP9 x) = (1 / 78 : ℝ) := by
  have h9 : factorTwoCenteredP9 =
      fun x ↦ -(centeredShiftedLegendreReal 9).eval x := by
    funext x
    rw [eval_centeredShiftedLegendreReal]
    rfl
  have hfull :=
    YoshidaEndpointPotentialLegendreOffDiagonalStructural.integral_endpointPotential_mul_centeredShiftedLegendreReal_of_even
      (m := 3) (n := 9) (by norm_num) (by norm_num)
  norm_num at hfull
  have hfullActual : (∫ x : ℝ in -1..1,
      yoshidaEndpointPotential x * centeredP3 x *
        factorTwoCenteredP9 x) = (1 / 39 : ℝ) := by
    rw [h9]
    unfold centeredP3
    rw [show (fun x : ℝ ↦
        yoshidaEndpointPotential x * ((5 * x ^ 3 - 3 * x) / 2) *
          (-(centeredShiftedLegendreReal 9).eval x)) = fun x ↦
        -(yoshidaEndpointPotential x *
          (1 / 2 * (5 * x ^ 3 - 3 * x)) *
            (centeredShiftedLegendreReal 9).eval x) by
      funext x
      ring,
      intervalIntegral.integral_neg]
    exact hfull
  let q : ℝ → ℝ := fun x ↦
    yoshidaEndpointPotential x * centeredP3 x * factorTwoCenteredP9 x
  have hq : IntervalIntegrable q volume (-1) 1 := by
    dsimp only [q]
    simpa only [mul_assoc] using
      intervalIntegrable_endpointPotential_mul
        (fun x : ℝ ↦ centeredP3 x * factorTwoCenteredP9 x)
        ((by unfold centeredP3; fun_prop : Continuous centeredP3).mul
          continuous_factorTwoCenteredP9)
  have hqeven : Function.Even q := by
    intro x
    dsimp only [q]
    have hp : yoshidaEndpointPotential (-x) =
        yoshidaEndpointPotential x := by
      unfold yoshidaEndpointPotential
      congr 2
      ring
    rw [hp, odd_factorTwoCenteredP9]
    unfold centeredP3
    ring
  have hfold := integral_neg_one_one_eq_two_mul_zero_one_of_even q hq hqeven
  dsimp only [q] at hfold
  rw [hfullActual] at hfold
  linarith

private theorem fourCellOddRetainedPrimePotentialBilinear_P3_P9 :
    fourCellOddRetainedPrimePotentialBilinear
        centeredP3 factorTwoCenteredP9 =
      Real.sqrt 2 * Real.log 2 * (1006528 / 244140625 : ℝ) +
        (2 - Real.sqrt 2 * Real.log 2) *
          (-3329608 / 244140625 : ℝ) +
        (93 / 50 : ℝ) * (1 / 78) := by
  unfold fourCellOddRetainedPrimePotentialBilinear
  rw [fourCellOddEndpointStripEvenMassBilinear_P3_P9,
    fourCellOddEndpointStripOddMassBilinear_P3_P9,
    integral_zero_one_endpointPotential_mul_P3_mul_P9]

/-- Exact retained endpoint entry on the final missing low/high row. -/
theorem fourCellOddRetainedEndpointBilinear_P3_P9_eq :
    fourCellOddRetainedEndpointBilinear
        centeredP3 factorTwoCenteredP9 =
      (19655672 / 732421875 : ℝ) +
        Real.sqrt 2 * Real.log 2 * (1006528 / 244140625 : ℝ) +
        (2 - Real.sqrt 2 * Real.log 2) *
          (-3329608 / 244140625 : ℝ) +
        (93 / 50 : ℝ) * (1 / 78) := by
  rcases centeredOddCoefficients_P9_eq_zero with ⟨h1, h3, h5⟩
  have h := fourCellOddRetainedEndpointBilinear_oneThreeFive_tail_eq_moments
    factorTwoCenteredP9 contDiff_factorTwoCenteredP9_local
      odd_factorTwoCenteredP9 h1 h3 h5 0 1 0
  have hp : fourCellOddOneThreeFiveLowProfile 0 1 0 = centeredP3 := by
    funext x
    unfold fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
    simp
  rw [hp, fourCellOddRetainedPrimePotentialBilinear_P3_P9] at h
  rcases endpointStripOdd_P9_moments with ⟨hm1, hm3, hm5⟩
  rw [hm1, hm3, hm5] at h
  norm_num at h ⊢
  convert h using 1
  ring

private theorem integral_zero_one_P3_mul_P9 :
    (∫ x : ℝ in 0..1, centeredP3 x * factorTwoCenteredP9 x) = 0 := by
  rcases centeredOddCoefficients_P9_eq_zero with ⟨h1, h3, h5⟩
  have h := integral_zero_one_oneThreeFiveLowProfile_mul_tail_eq_zero
    factorTwoCenteredP9 continuous_factorTwoCenteredP9
      odd_factorTwoCenteredP9 h1 h3 h5 0 1 0
  have hp : fourCellOddOneThreeFiveLowProfile 0 1 0 = centeredP3 := by
    funext x
    unfold fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
    simp
  simpa only [hp] using h

private theorem fourCellOddSignedMassRegularBilinear_P3_P9_eq :
    fourCellOddSignedMassRegularBilinear centeredP3 factorTwoCenteredP9 =
      2 * fourCellOperatorHalfWidth *
        (∫ t : ℝ in 0..2,
          yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
            factorTwoCenteredCorrelationBilinear
              centeredP3 factorTwoCenteredP9 t) := by
  unfold fourCellOddSignedMassRegularBilinear
  rw [integral_zero_one_P3_mul_P9]
  ring

private theorem abs_fourCellOddSignedMassRegularBilinear_P3_P9_lt :
    |fourCellOddSignedMassRegularBilinear centeredP3 factorTwoCenteredP9| <
      (1 / 100000 : ℝ) := by
  let R : ℝ := ∫ t : ℝ in 0..2,
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
      factorTwoCenteredCorrelationBilinear centeredP3 factorTwoCenteredP9 t
  have hR : |R| < (1 / 100000 : ℝ) := by
    simpa only [R] using
      abs_integral_fourCellRegularKernel_mul_correlation_P3_P9_lt
  have ha0 : 0 ≤ 2 * fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  have ha : 2 * fourCellOperatorHalfWidth ≤ (1 : ℝ) := by
    linarith [fourCellOperatorHalfWidth_le_one_half]
  rw [fourCellOddSignedMassRegularBilinear_P3_P9_eq]
  change |2 * fourCellOperatorHalfWidth * R| < _
  rw [abs_mul, abs_of_nonneg ha0]
  calc
    2 * fourCellOperatorHalfWidth * |R| ≤ 1 * |R| :=
      mul_le_mul_of_nonneg_right ha (abs_nonneg R)
    _ < 1 * (1 / 100000 : ℝ) :=
      mul_lt_mul_of_pos_left hR (by norm_num)
    _ = (1 / 100000 : ℝ) := one_mul _

private theorem fourCellOddRetainedEndpointBilinear_P3_P9_bounds :
    (4081 / 100000 : ℝ) <
        fourCellOddRetainedEndpointBilinear centeredP3 factorTwoCenteredP9 ∧
      fourCellOddRetainedEndpointBilinear centeredP3 factorTwoCenteredP9 <
        (2041 / 50000 : ℝ) := by
  rw [fourCellOddRetainedEndpointBilinear_P3_P9_eq]
  rcases sqrt_two_mul_log_two_bounds with ⟨hklo, hkhi⟩
  constructor <;> nlinarith

/-- Tight complete-form enclosure for the `P₃/P₉` row.  Together with
the preceding three cross enclosures this completes the exact rational
description of the `P₁/P₃`--`P₇/P₉` block. -/
theorem fourCellOddCoreLocalBilinear_P3_P9_bounds :
    (102 / 2500 : ℝ) <
        fourCellOddCoreLocalBilinear centeredP3 factorTwoCenteredP9 ∧
      fourCellOddCoreLocalBilinear centeredP3 factorTwoCenteredP9 <
        (4083 / 100000 : ℝ) := by
  rw [fourCellOddCoreLocalBilinear_eq_retained_sub_signed]
  rcases fourCellOddRetainedEndpointBilinear_P3_P9_bounds with
    ⟨hretlo, hrethi⟩
  have hsigned := abs_fourCellOddSignedMassRegularBilinear_P3_P9_lt
  have hsignedLo := neg_abs_le
    (fourCellOddSignedMassRegularBilinear centeredP3 factorTwoCenteredP9)
  have hsignedHi := le_abs_self
    (fourCellOddSignedMassRegularBilinear centeredP3 factorTwoCenteredP9)
  constructor <;> linarith

/-! ### Tight high-cross entries for the rational five-mode certificate -/

set_option maxHeartbeats 800000 in
private theorem integral_fourCellRegularPolynomial_mul_P5P7CorrelationLocal :
    (∫ t : ℝ in 0..2,
      yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t) *
        oddP5P7CorrelationLocal t) =
      -(1 / 82368 : ℝ) * Real.log 2 -
        (35 / 1613094912 : ℝ) * Real.log 2 ^ 3 -
        (96875 / 768917177892864 : ℝ) * Real.log 2 ^ 5 := by
  unfold yoshidaRegularKernelPolynomial6 fourCellOperatorHalfWidth
    oddP5P7CorrelationLocal
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [intervalIntegral.integral_const_mul]
  repeat rw [integral_pow]
  norm_num
  ring

set_option maxHeartbeats 800000 in
private theorem integral_fourCellRegularPolynomial_mul_P5P9CorrelationLocal :
    (∫ t : ℝ in 0..2,
      yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t) *
        oddP5P9CorrelationLocal t) =
      (35 / 13621690368 : ℝ) * Real.log 2 ^ 3 +
        (19375 / 1153375766839296 : ℝ) * Real.log 2 ^ 5 := by
  unfold yoshidaRegularKernelPolynomial6 fourCellOperatorHalfWidth
    oddP5P9CorrelationLocal
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [intervalIntegral.integral_const_mul]
  repeat rw [integral_pow]
  norm_num
  ring

set_option maxHeartbeats 800000 in
private theorem integral_fourCellRegularPolynomial_mul_P7P9Correlation :
    (∫ t : ℝ in 0..2,
      yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t) *
        factorTwoP7P9Correlation t) =
      -(1 / 186048 : ℝ) * Real.log 2 -
        (5 / 928751616 : ℝ) * Real.log 2 ^ 3 -
        (96875 / 5895031697178624 : ℝ) * Real.log 2 ^ 5 := by
  unfold yoshidaRegularKernelPolynomial6 fourCellOperatorHalfWidth
    factorTwoP7P9Correlation
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [intervalIntegral.integral_const_mul]
  repeat rw [integral_pow]
  norm_num
  ring

private theorem fourCellOddHighCrossRegularPolynomial_bounds :
    (-843 / 100000000 : ℝ) <
        (∫ t : ℝ in 0..2,
          yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t) *
            oddP5P7CorrelationLocal t) ∧
      (∫ t : ℝ in 0..2,
          yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t) *
            oddP5P7CorrelationLocal t) < (-842 / 100000000 : ℝ) ∧
      (8 / 10000000000 : ℝ) <
        (∫ t : ℝ in 0..2,
          yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t) *
            oddP5P9CorrelationLocal t) ∧
      (∫ t : ℝ in 0..2,
          yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t) *
            oddP5P9CorrelationLocal t) < (9 / 10000000000 : ℝ) ∧
      (-373 / 100000000 : ℝ) <
        (∫ t : ℝ in 0..2,
          yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t) *
            factorTwoP7P9Correlation t) ∧
      (∫ t : ℝ in 0..2,
          yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t) *
            factorTwoP7P9Correlation t) < (-372 / 100000000 : ℝ) := by
  rw [integral_fourCellRegularPolynomial_mul_P5P7CorrelationLocal,
    integral_fourCellRegularPolynomial_mul_P5P9CorrelationLocal,
    integral_fourCellRegularPolynomial_mul_P7P9Correlation]
  have h1 := fourCell_log_two_pow_fine_bounds 1 (by norm_num)
  have h3 := fourCell_log_two_pow_fine_bounds 3 (by norm_num)
  have h5 := fourCell_log_two_pow_fine_bounds 5 (by norm_num)
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

private theorem abs_fourCellWideRegularEnvelopeError_P5P7_lt :
    |fourCellWideRegularEnvelopeError oddP5P7CorrelationLocal| <
      (2 / 1000000 : ℝ) := by
  let I : ℝ := ∫ t : ℝ in 0..2, |oddP5P7CorrelationLocal t|
  have hI0 : 0 ≤ I := by
    dsimp only [I]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun _t _ht ↦ abs_nonneg _)
  have hE5 : factorTwoIntrinsicEnergy factorTwoCenteredP5 =
      (2 / 11 : ℝ) := by
    unfold factorTwoIntrinsicEnergy
    simpa only [pow_two] using integral_factorTwoCenteredP5_sq
  have hI2 : I ^ 2 ≤ (2 / 11 : ℝ) * (2 / 15) := by
    have h :=
      ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP67ResidualAnalyticSchurStructural.integral_abs_factorTwoCenteredCorrelationBilinear_sq_le_energy_mul
        factorTwoCenteredP5 factorTwoCenteredP7
          continuous_factorTwoCenteredP5 continuous_factorTwoCenteredP7
    rw [hE5, factorTwoCenteredP7_energy] at h
    simp_rw [factorTwoCenteredCorrelationBilinear_P5_P7_local] at h
    simpa only [I] using h
  have hIlt : I < (157 / 1000 : ℝ) := by
    nlinarith
  have herr := abs_fourCellWideRegularEnvelopeError_le_sevenEighths
    oddP5P7CorrelationLocal
      (by unfold oddP5P7CorrelationLocal; fun_prop)
  change |fourCellWideRegularEnvelopeError oddP5P7CorrelationLocal| ≤
    (1 / 80000 : ℝ) * I at herr
  calc
    |fourCellWideRegularEnvelopeError oddP5P7CorrelationLocal| ≤
        (1 / 80000 : ℝ) * I := herr
    _ < (1 / 80000 : ℝ) * (157 / 1000) :=
      mul_lt_mul_of_pos_left hIlt (by norm_num)
    _ < (2 / 1000000 : ℝ) := by norm_num

private theorem abs_fourCellWideRegularEnvelopeError_P5P9_lt :
    |fourCellWideRegularEnvelopeError oddP5P9CorrelationLocal| <
      (2 / 1000000 : ℝ) := by
  let I : ℝ := ∫ t : ℝ in 0..2, |oddP5P9CorrelationLocal t|
  have hI0 : 0 ≤ I := by
    dsimp only [I]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun _t _ht ↦ abs_nonneg _)
  have hE5 : factorTwoIntrinsicEnergy factorTwoCenteredP5 =
      (2 / 11 : ℝ) := by
    unfold factorTwoIntrinsicEnergy
    simpa only [pow_two] using integral_factorTwoCenteredP5_sq
  have hI2 : I ^ 2 ≤ (2 / 11 : ℝ) * (2 / 19) := by
    have h :=
      ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP67ResidualAnalyticSchurStructural.integral_abs_factorTwoCenteredCorrelationBilinear_sq_le_energy_mul
        factorTwoCenteredP5 factorTwoCenteredP9
          continuous_factorTwoCenteredP5 continuous_factorTwoCenteredP9
    rw [hE5, factorTwoCenteredP9_energy] at h
    simp_rw [factorTwoCenteredCorrelationBilinear_P5_P9_local] at h
    simpa only [I] using h
  have hIlt : I < (14 / 100 : ℝ) := by
    nlinarith
  have herr := abs_fourCellWideRegularEnvelopeError_le_sevenEighths
    oddP5P9CorrelationLocal
      (by unfold oddP5P9CorrelationLocal; fun_prop)
  change |fourCellWideRegularEnvelopeError oddP5P9CorrelationLocal| ≤
    (1 / 80000 : ℝ) * I at herr
  calc
    |fourCellWideRegularEnvelopeError oddP5P9CorrelationLocal| ≤
        (1 / 80000 : ℝ) * I := herr
    _ < (1 / 80000 : ℝ) * (14 / 100) :=
      mul_lt_mul_of_pos_left hIlt (by norm_num)
    _ < (2 / 1000000 : ℝ) := by norm_num

private theorem abs_fourCellWideRegularEnvelopeError_P7P9_lt :
    |fourCellWideRegularEnvelopeError factorTwoP7P9Correlation| <
      (3 / 2000000 : ℝ) := by
  let I : ℝ := ∫ t : ℝ in 0..2, |factorTwoP7P9Correlation t|
  have hI0 : 0 ≤ I := by
    dsimp only [I]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun _t _ht ↦ abs_nonneg _)
  have hI2 : I ^ 2 ≤ (2 / 15 : ℝ) * (2 / 19) := by
    have h :=
      ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP67ResidualAnalyticSchurStructural.integral_abs_factorTwoCenteredCorrelationBilinear_sq_le_energy_mul
        factorTwoCenteredP7 factorTwoCenteredP9
          continuous_factorTwoCenteredP7 continuous_factorTwoCenteredP9
    rw [factorTwoCenteredP7_energy, factorTwoCenteredP9_energy] at h
    simp_rw [factorTwoCenteredCorrelationBilinear_P7_P9] at h
    simpa only [I] using h
  have hIlt : I < (12 / 100 : ℝ) := by
    nlinarith
  have herr := abs_fourCellWideRegularEnvelopeError_le_sevenEighths
    factorTwoP7P9Correlation
      (by unfold factorTwoP7P9Correlation; fun_prop)
  change |fourCellWideRegularEnvelopeError factorTwoP7P9Correlation| ≤
    (1 / 80000 : ℝ) * I at herr
  calc
    |fourCellWideRegularEnvelopeError factorTwoP7P9Correlation| ≤
        (1 / 80000 : ℝ) * I := herr
    _ < (1 / 80000 : ℝ) * (12 / 100) :=
      mul_lt_mul_of_pos_left hIlt (by norm_num)
    _ = (3 / 2000000 : ℝ) := by norm_num

private theorem fourCellOddHighCrossRegularIntegral_bounds :
    (-11 / 1000000 : ℝ) <
        (∫ t : ℝ in 0..2,
          yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
            factorTwoCenteredCorrelationBilinear
              factorTwoCenteredP5 factorTwoCenteredP7 t) ∧
      (∫ t : ℝ in 0..2,
          yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
            factorTwoCenteredCorrelationBilinear
              factorTwoCenteredP5 factorTwoCenteredP7 t) <
        (-6 / 1000000 : ℝ) ∧
      (-3 / 1000000 : ℝ) <
        (∫ t : ℝ in 0..2,
          yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
            factorTwoCenteredCorrelationBilinear
              factorTwoCenteredP5 factorTwoCenteredP9 t) ∧
      (∫ t : ℝ in 0..2,
          yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
            factorTwoCenteredCorrelationBilinear
              factorTwoCenteredP5 factorTwoCenteredP9 t) <
        (3 / 1000000 : ℝ) ∧
      (-6 / 1000000 : ℝ) <
        (∫ t : ℝ in 0..2,
          yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
            factorTwoCenteredCorrelationBilinear
              factorTwoCenteredP7 factorTwoCenteredP9 t) ∧
      (∫ t : ℝ in 0..2,
          yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
            factorTwoCenteredCorrelationBilinear
              factorTwoCenteredP7 factorTwoCenteredP9 t) <
        (-2 / 1000000 : ℝ) := by
  rcases fourCellOddHighCrossRegularPolynomial_bounds with
    ⟨h57lo, h57hi, h59lo, h59hi, h79lo, h79hi⟩
  have he57 := abs_lt.mp abs_fourCellWideRegularEnvelopeError_P5P7_lt
  have he59 := abs_lt.mp abs_fourCellWideRegularEnvelopeError_P5P9_lt
  have he79 := abs_lt.mp abs_fourCellWideRegularEnvelopeError_P7P9_lt
  have hd57 := fourCellRegularIntegral_eq_polynomial_add_error
    oddP5P7CorrelationLocal
      (by unfold oddP5P7CorrelationLocal; fun_prop)
  have hd59 := fourCellRegularIntegral_eq_polynomial_add_error
    oddP5P9CorrelationLocal
      (by unfold oddP5P9CorrelationLocal; fun_prop)
  have hd79 := fourCellRegularIntegral_eq_polynomial_add_error
    factorTwoP7P9Correlation
      (by unfold factorTwoP7P9Correlation; fun_prop)
  simp_rw [factorTwoCenteredCorrelationBilinear_P5_P7_local,
    factorTwoCenteredCorrelationBilinear_P5_P9_local,
    factorTwoCenteredCorrelationBilinear_P7_P9]
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

private theorem fourCellOddHighCrossRetained_certificate_bounds :
    (935611 / 10000000 : ℝ) <
        fourCellOddRetainedEndpointBilinear
          factorTwoCenteredP5 factorTwoCenteredP7 ∧
      fourCellOddRetainedEndpointBilinear
          factorTwoCenteredP5 factorTwoCenteredP7 <
        (935612 / 10000000 : ℝ) ∧
      (262539 / 10000000 : ℝ) <
        fourCellOddRetainedEndpointBilinear
          factorTwoCenteredP5 factorTwoCenteredP9 ∧
      fourCellOddRetainedEndpointBilinear
          factorTwoCenteredP5 factorTwoCenteredP9 <
        (262540 / 10000000 : ℝ) ∧
      (153308 / 10000000 : ℝ) <
        fourCellOddRetainedEndpointBilinear
          factorTwoCenteredP7 factorTwoCenteredP9 ∧
      fourCellOddRetainedEndpointBilinear
          factorTwoCenteredP7 factorTwoCenteredP9 <
        (153310 / 10000000 : ℝ) := by
  rw [fourCellOddRetainedEndpointBilinear_P5_P7_eq,
    fourCellOddRetainedEndpointBilinear_P5_P9_eq,
    fourCellOddRetainedEndpointBilinear_P7_P9_eq]
  have hP := fourCell_sqrt_two_mul_log_two_fine_bounds
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

private theorem integral_zero_one_P5_mul_P7_tight :
    (∫ x : ℝ in 0..1,
      factorTwoCenteredP5 x * factorTwoCenteredP7 x) = 0 := by
  rcases centeredOddCoefficients_P7_eq_zero with ⟨h1, h3, h5⟩
  have h := integral_zero_one_oneThreeFiveLowProfile_mul_tail_eq_zero
    factorTwoCenteredP7 continuous_factorTwoCenteredP7
      odd_factorTwoCenteredP7 h1 h3 h5 0 0 1
  have hp : fourCellOddOneThreeFiveLowProfile 0 0 1 =
      factorTwoCenteredP5 := by
    funext x
    unfold fourCellOddOneThreeFiveLowProfile
      factorTwoOddStructuralLowProfile centeredP1 centeredP3
    simp
  simpa only [hp] using h

private theorem integral_zero_one_P5_mul_P9_tight :
    (∫ x : ℝ in 0..1,
      factorTwoCenteredP5 x * factorTwoCenteredP9 x) = 0 := by
  rcases centeredOddCoefficients_P9_eq_zero with ⟨h1, h3, h5⟩
  have h := integral_zero_one_oneThreeFiveLowProfile_mul_tail_eq_zero
    factorTwoCenteredP9 continuous_factorTwoCenteredP9
      odd_factorTwoCenteredP9 h1 h3 h5 0 0 1
  have hp : fourCellOddOneThreeFiveLowProfile 0 0 1 =
      factorTwoCenteredP5 := by
    funext x
    unfold fourCellOddOneThreeFiveLowProfile
      factorTwoOddStructuralLowProfile centeredP1 centeredP3
    simp
  simpa only [hp] using h

private theorem fourCellOddSignedMassRegularBilinear_eq_width_integral_of_mass_zero
    (u v : ℝ → ℝ)
    (hmass : (∫ x : ℝ in 0..1, u x * v x) = 0) :
    fourCellOddSignedMassRegularBilinear u v =
      2 * fourCellOperatorHalfWidth *
        (∫ t : ℝ in 0..2,
          yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
            factorTwoCenteredCorrelationBilinear u v t) := by
  unfold fourCellOddSignedMassRegularBilinear
  rw [hmass]
  ring

private theorem abs_fourCellOddSignedMassRegularBilinear_highCross_bounds :
    |fourCellOddSignedMassRegularBilinear
        factorTwoCenteredP5 factorTwoCenteredP7| <
        (11 / 1000000 : ℝ) ∧
      |fourCellOddSignedMassRegularBilinear
        factorTwoCenteredP5 factorTwoCenteredP9| <
        (3 / 1000000 : ℝ) ∧
      |fourCellOddSignedMassRegularBilinear
        factorTwoCenteredP7 factorTwoCenteredP9| <
        (6 / 1000000 : ℝ) := by
  rcases fourCellOddHighCrossRegularIntegral_bounds with
    ⟨h57lo, h57hi, h59lo, h59hi, h79lo, h79hi⟩
  let R57 : ℝ := ∫ t : ℝ in 0..2,
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
      factorTwoCenteredCorrelationBilinear
        factorTwoCenteredP5 factorTwoCenteredP7 t
  let R59 : ℝ := ∫ t : ℝ in 0..2,
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
      factorTwoCenteredCorrelationBilinear
        factorTwoCenteredP5 factorTwoCenteredP9 t
  let R79 : ℝ := ∫ t : ℝ in 0..2,
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
      factorTwoCenteredCorrelationBilinear
        factorTwoCenteredP7 factorTwoCenteredP9 t
  change (-11 / 1000000 : ℝ) < R57 at h57lo
  change R57 < (-6 / 1000000 : ℝ) at h57hi
  change (-3 / 1000000 : ℝ) < R59 at h59lo
  change R59 < (3 / 1000000 : ℝ) at h59hi
  change (-6 / 1000000 : ℝ) < R79 at h79lo
  change R79 < (-2 / 1000000 : ℝ) at h79hi
  have hR57 : |R57| < (11 / 1000000 : ℝ) := by
    rw [abs_of_neg (h57hi.trans (by norm_num))]
    linarith
  have hR59 : |R59| < (3 / 1000000 : ℝ) := by
    rw [abs_lt]
    constructor <;> nlinarith
  have hR79 : |R79| < (6 / 1000000 : ℝ) := by
    rw [abs_of_neg (h79hi.trans (by norm_num))]
    linarith
  have hW0 : 0 ≤ 2 * fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  have hW : 2 * fourCellOperatorHalfWidth ≤ (1 : ℝ) := by
    linarith [fourCellOperatorHalfWidth_le_one_half]
  rw [fourCellOddSignedMassRegularBilinear_eq_width_integral_of_mass_zero
      factorTwoCenteredP5 factorTwoCenteredP7
        integral_zero_one_P5_mul_P7_tight,
    fourCellOddSignedMassRegularBilinear_eq_width_integral_of_mass_zero
      factorTwoCenteredP5 factorTwoCenteredP9
        integral_zero_one_P5_mul_P9_tight,
    fourCellOddSignedMassRegularBilinear_eq_width_integral_of_mass_zero
      factorTwoCenteredP7 factorTwoCenteredP9
        integral_zero_one_P7_mul_P9_eq_zero]
  change |2 * fourCellOperatorHalfWidth * R57| < _ ∧
    |2 * fourCellOperatorHalfWidth * R59| < _ ∧
    |2 * fourCellOperatorHalfWidth * R79| < _
  simp only [abs_mul, abs_of_nonneg hW0]
  constructor
  · calc
      2 * fourCellOperatorHalfWidth * |R57| ≤ 1 * |R57| :=
        mul_le_mul_of_nonneg_right hW (abs_nonneg R57)
      _ < 1 * (11 / 1000000 : ℝ) :=
        mul_lt_mul_of_pos_left hR57 (by norm_num)
      _ = (11 / 1000000 : ℝ) := one_mul _
  constructor
  · calc
      2 * fourCellOperatorHalfWidth * |R59| ≤ 1 * |R59| :=
        mul_le_mul_of_nonneg_right hW (abs_nonneg R59)
      _ < 1 * (3 / 1000000 : ℝ) :=
        mul_lt_mul_of_pos_left hR59 (by norm_num)
      _ = (3 / 1000000 : ℝ) := one_mul _
  · calc
      2 * fourCellOperatorHalfWidth * |R79| ≤ 1 * |R79| :=
        mul_le_mul_of_nonneg_right hW (abs_nonneg R79)
      _ < 1 * (6 / 1000000 : ℝ) :=
        mul_lt_mul_of_pos_left hR79 (by norm_num)
      _ = (6 / 1000000 : ℝ) := one_mul _

/-- Exact complete-core boxes for the three cross entries inside the
`P₅/P₇/P₉` corner.  The widths come from exact Legendre moments plus the
common analytic kernel envelope, not from evaluating the matrix. -/
theorem fourCellOddCoreLocal_highCross_certificate_bounds :
    (93550 / 1000000 : ℝ) <
        fourCellOddCoreLocalBilinear
          factorTwoCenteredP5 factorTwoCenteredP7 ∧
      fourCellOddCoreLocalBilinear
          factorTwoCenteredP5 factorTwoCenteredP7 <
        (93573 / 1000000 : ℝ) ∧
      (26250 / 1000000 : ℝ) <
        fourCellOddCoreLocalBilinear
          factorTwoCenteredP5 factorTwoCenteredP9 ∧
      fourCellOddCoreLocalBilinear
          factorTwoCenteredP5 factorTwoCenteredP9 <
        (26258 / 1000000 : ℝ) ∧
      (15324 / 1000000 : ℝ) <
        fourCellOddCoreLocalBilinear
          factorTwoCenteredP7 factorTwoCenteredP9 ∧
      fourCellOddCoreLocalBilinear
          factorTwoCenteredP7 factorTwoCenteredP9 <
        (15338 / 1000000 : ℝ) := by
  rcases fourCellOddHighCrossRetained_certificate_bounds with
    ⟨h57retlo, h57rethi, h59retlo, h59rethi, h79retlo, h79rethi⟩
  rcases abs_fourCellOddSignedMassRegularBilinear_highCross_bounds with
    ⟨h57signed, h59signed, h79signed⟩
  have h57signedlo := neg_abs_le
    (fourCellOddSignedMassRegularBilinear
      factorTwoCenteredP5 factorTwoCenteredP7)
  have h57signedhi := le_abs_self
    (fourCellOddSignedMassRegularBilinear
      factorTwoCenteredP5 factorTwoCenteredP7)
  have h59signedlo := neg_abs_le
    (fourCellOddSignedMassRegularBilinear
      factorTwoCenteredP5 factorTwoCenteredP9)
  have h59signedhi := le_abs_self
    (fourCellOddSignedMassRegularBilinear
      factorTwoCenteredP5 factorTwoCenteredP9)
  have h79signedlo := neg_abs_le
    (fourCellOddSignedMassRegularBilinear
      factorTwoCenteredP7 factorTwoCenteredP9)
  have h79signedhi := le_abs_self
    (fourCellOddSignedMassRegularBilinear
      factorTwoCenteredP7 factorTwoCenteredP9)
  simp only [fourCellOddCoreLocalBilinear_eq_retained_sub_signed]
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

private theorem abs_integral_fourCellRegularKernel_P1P7_certificate_lt :
    |∫ t : ℝ in 0..2,
      yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
        factorTwoCenteredCorrelationBilinear
          centeredP1 factorTwoCenteredP7 t| < (4 / 1000000 : ℝ) := by
  let C : ℝ → ℝ := oddP7Correlation17Local
  let I : ℝ := ∫ t : ℝ in 0..2, |C t|
  let E : ℝ := fourCellWideRegularEnvelopeError C
  have hC : Continuous C := by
    dsimp only [C]
    unfold oddP7Correlation17Local
    fun_prop
  have hI0 : 0 ≤ I := by
    dsimp only [I]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun _t _ht ↦ abs_nonneg _)
  have hE1 : factorTwoIntrinsicEnergy centeredP1 = (2 / 3 : ℝ) := by
    unfold factorTwoIntrinsicEnergy centeredP1
    rw [integral_pow]
    norm_num
  have hI2 : I ^ 2 ≤ (2 / 3 : ℝ) * (2 / 15) := by
    have h :=
      ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP67ResidualAnalyticSchurStructural.integral_abs_factorTwoCenteredCorrelationBilinear_sq_le_energy_mul
        centeredP1 factorTwoCenteredP7
          (by unfold centeredP1; fun_prop) continuous_factorTwoCenteredP7
    rw [hE1, factorTwoCenteredP7_energy] at h
    simp_rw [factorTwoCenteredCorrelationBilinear_P1_P7] at h
    simpa only [I, C] using h
  have hIlt : I < (3 / 10 : ℝ) := by
    nlinarith
  have herr := abs_fourCellWideRegularEnvelopeError_le_sevenEighths C hC
  change |E| ≤ (1 / 80000 : ℝ) * I at herr
  have herrlt : |E| < (3 / 800000 : ℝ) := by
    calc
      |E| ≤ (1 / 80000 : ℝ) * I := herr
      _ < (1 / 80000 : ℝ) * (3 / 10) :=
        mul_lt_mul_of_pos_left hIlt (by norm_num)
      _ = (3 / 800000 : ℝ) := by norm_num
  have hpabs :
      |∫ t : ℝ in 0..2,
        yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t) *
          C t| < (1 / 1000000000 : ℝ) := by
    dsimp only [C]
    rw [integral_fourCellRegularPolynomial_mul_oddP7Correlation17Local]
    have hpow := (fourCell_log_two_pow_fine_bounds 5 (by norm_num)).2
    have hlog0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hneg :
        -(3875 / 21424936845312 : ℝ) * Real.log 2 ^ 5 < 0 := by
      exact mul_neg_of_neg_of_pos (by norm_num) (pow_pos hlog0 5)
    rw [abs_of_neg hneg]
    nlinarith
  have hdecomp := fourCellRegularIntegral_eq_polynomial_add_error C hC
  simp_rw [factorTwoCenteredCorrelationBilinear_P1_P7]
  change |∫ t : ℝ in 0..2,
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t) * C t| < _
  rw [hdecomp]
  calc
    |(∫ t : ℝ in 0..2,
        yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t) *
          C t) + E| ≤
        |∫ t : ℝ in 0..2,
          yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t) *
            C t| + |E| := abs_add_le _ _
    _ < (1 / 1000000000 : ℝ) + 3 / 800000 :=
      add_lt_add hpabs herrlt
    _ < (4 / 1000000 : ℝ) := by norm_num

private theorem abs_integral_fourCellRegularKernel_P1P9_certificate_lt :
    |∫ t : ℝ in 0..2,
      yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
        factorTwoCenteredCorrelationBilinear
          centeredP1 factorTwoCenteredP9 t| < (4 / 1000000 : ℝ) := by
  let C : ℝ → ℝ := oddP9Correlation19Local
  let I : ℝ := ∫ t : ℝ in 0..2, |C t|
  let E : ℝ := fourCellWideRegularEnvelopeError C
  have hC : Continuous C := by
    dsimp only [C]
    unfold oddP9Correlation19Local
    fun_prop
  have hI0 : 0 ≤ I := by
    dsimp only [I]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun _t _ht ↦ abs_nonneg _)
  have hE1 : factorTwoIntrinsicEnergy centeredP1 = (2 / 3 : ℝ) := by
    unfold factorTwoIntrinsicEnergy centeredP1
    rw [integral_pow]
    norm_num
  have hI2 : I ^ 2 ≤ (2 / 3 : ℝ) * (2 / 19) := by
    have h :=
      ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP67ResidualAnalyticSchurStructural.integral_abs_factorTwoCenteredCorrelationBilinear_sq_le_energy_mul
        centeredP1 factorTwoCenteredP9
          (by unfold centeredP1; fun_prop) continuous_factorTwoCenteredP9
    rw [hE1, factorTwoCenteredP9_energy] at h
    simp_rw [factorTwoCenteredCorrelationBilinear_P1_P9] at h
    simpa only [I, C] using h
  have hIlt : I < (27 / 100 : ℝ) := by
    nlinarith
  have herr := abs_fourCellWideRegularEnvelopeError_le_sevenEighths C hC
  change |E| ≤ (1 / 80000 : ℝ) * I at herr
  have herrlt : |E| < (27 / 8000000 : ℝ) := by
    calc
      |E| ≤ (1 / 80000 : ℝ) * I := herr
      _ < (1 / 80000 : ℝ) * (27 / 100) :=
        mul_lt_mul_of_pos_left hIlt (by norm_num)
      _ = (27 / 8000000 : ℝ) := by norm_num
  have hdecomp := fourCellRegularIntegral_eq_polynomial_add_error C hC
  have hpoly :
      (∫ t : ℝ in 0..2,
        yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t) *
          C t) = 0 := by
    simpa only [C] using
      integral_fourCellRegularPolynomial_mul_oddP9Correlation19Local
  simp_rw [factorTwoCenteredCorrelationBilinear_P1_P9]
  change |∫ t : ℝ in 0..2,
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t) * C t| < _
  rw [hdecomp, hpoly, zero_add]
  exact herrlt.trans (by norm_num)

private theorem abs_fourCellOddSignedMassRegularBilinear_P1_high_certificate_lt :
    |fourCellOddSignedMassRegularBilinear
        centeredP1 factorTwoCenteredP7| < (4 / 1000000 : ℝ) ∧
      |fourCellOddSignedMassRegularBilinear
        centeredP1 factorTwoCenteredP9| < (4 / 1000000 : ℝ) := by
  let R17 : ℝ := ∫ t : ℝ in 0..2,
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
      factorTwoCenteredCorrelationBilinear centeredP1 factorTwoCenteredP7 t
  let R19 : ℝ := ∫ t : ℝ in 0..2,
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
      factorTwoCenteredCorrelationBilinear centeredP1 factorTwoCenteredP9 t
  have hR17 : |R17| < (4 / 1000000 : ℝ) := by
    simpa only [R17] using
      abs_integral_fourCellRegularKernel_P1P7_certificate_lt
  have hR19 : |R19| < (4 / 1000000 : ℝ) := by
    simpa only [R19] using
      abs_integral_fourCellRegularKernel_P1P9_certificate_lt
  have hW0 : 0 ≤ 2 * fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  have hW : 2 * fourCellOperatorHalfWidth ≤ (1 : ℝ) := by
    linarith [fourCellOperatorHalfWidth_le_one_half]
  rw [fourCellOddSignedMassRegularBilinear_P1_P7_eq,
    fourCellOddSignedMassRegularBilinear_P1_P9_eq]
  change |2 * fourCellOperatorHalfWidth * R17| < _ ∧
    |2 * fourCellOperatorHalfWidth * R19| < _
  simp only [abs_mul, abs_of_nonneg hW0]
  constructor
  · calc
      2 * fourCellOperatorHalfWidth * |R17| ≤ 1 * |R17| :=
        mul_le_mul_of_nonneg_right hW (abs_nonneg R17)
      _ < 1 * (4 / 1000000 : ℝ) :=
        mul_lt_mul_of_pos_left hR17 (by norm_num)
      _ = (4 / 1000000 : ℝ) := one_mul _
  · calc
      2 * fourCellOperatorHalfWidth * |R19| ≤ 1 * |R19| :=
        mul_le_mul_of_nonneg_right hW (abs_nonneg R19)
      _ < 1 * (4 / 1000000 : ℝ) :=
        mul_lt_mul_of_pos_left hR19 (by norm_num)
      _ = (4 / 1000000 : ℝ) := one_mul _

private theorem fourCellOddRetainedEndpointBilinear_P1_high_certificate_bounds :
    (356208 / 10000000 : ℝ) <
        fourCellOddRetainedEndpointBilinear centeredP1 factorTwoCenteredP7 ∧
      fourCellOddRetainedEndpointBilinear centeredP1 factorTwoCenteredP7 <
        (356210 / 10000000 : ℝ) ∧
      (440131 / 10000000 : ℝ) <
        fourCellOddRetainedEndpointBilinear centeredP1 factorTwoCenteredP9 ∧
      fourCellOddRetainedEndpointBilinear centeredP1 factorTwoCenteredP9 <
        (440132 / 10000000 : ℝ) := by
  rw [fourCellOddRetainedEndpointBilinear_P1_P7_eq,
    fourCellOddRetainedEndpointBilinear_P1_P9_eq]
  have hP := fourCell_sqrt_two_mul_log_two_fine_bounds
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

/-- Certificate-width complete-core boxes for the two `P₁` high rows. -/
theorem fourCellOddCoreLocalBilinear_P1_high_certificate_bounds :
    (35616 / 1000000 : ℝ) <
        fourCellOddCoreLocalBilinear centeredP1 factorTwoCenteredP7 ∧
      fourCellOddCoreLocalBilinear centeredP1 factorTwoCenteredP7 <
        (35626 / 1000000 : ℝ) ∧
      (44009 / 1000000 : ℝ) <
        fourCellOddCoreLocalBilinear centeredP1 factorTwoCenteredP9 ∧
      fourCellOddCoreLocalBilinear centeredP1 factorTwoCenteredP9 <
        (44018 / 1000000 : ℝ) := by
  rcases fourCellOddRetainedEndpointBilinear_P1_high_certificate_bounds with
    ⟨h17retlo, h17rethi, h19retlo, h19rethi⟩
  rcases abs_fourCellOddSignedMassRegularBilinear_P1_high_certificate_lt with
    ⟨h17signed, h19signed⟩
  have h17signedlo := neg_abs_le
    (fourCellOddSignedMassRegularBilinear centeredP1 factorTwoCenteredP7)
  have h17signedhi := le_abs_self
    (fourCellOddSignedMassRegularBilinear centeredP1 factorTwoCenteredP7)
  have h19signedlo := neg_abs_le
    (fourCellOddSignedMassRegularBilinear centeredP1 factorTwoCenteredP9)
  have h19signedhi := le_abs_self
    (fourCellOddSignedMassRegularBilinear centeredP1 factorTwoCenteredP9)
  simp only [fourCellOddCoreLocalBilinear_eq_retained_sub_signed]
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

/-! ### Exact `P₁₁+` Riesz endpoint -/

/-- Normalized centered `P₇` coefficient. -/
def centeredOddP7Coefficient (w : ℝ → ℝ) : ℝ :=
  (15 / 2 : ℝ) * ∫ x : ℝ in -1..1,
    w x * factorTwoCenteredP7 x

/-- Normalized centered `P₉` coefficient. -/
def centeredOddP9Coefficient (w : ℝ → ℝ) : ℝ :=
  (19 / 2 : ℝ) * ∫ x : ℝ in -1..1,
    w x * factorTwoCenteredP9 x

/-- The exact first five odd shifted-Legendre modes retained before the
arbitrary `P₁₁+` residual. -/
def fourCellOddOneThreeFiveSevenNineLowProfile
    (c d e f g : ℝ) : ℝ → ℝ := fun x ↦
  fourCellOddOneThreeFiveLowProfile c d e x +
    f * factorTwoCenteredP7 x + g * factorTwoCenteredP9 x

theorem contDiff_fourCellOddOneThreeFiveSevenNineLowProfile
    (c d e f g : ℝ) :
    ContDiff ℝ 1 (fourCellOddOneThreeFiveSevenNineLowProfile c d e f g) := by
  unfold fourCellOddOneThreeFiveSevenNineLowProfile
    fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
    centeredP1 centeredP3 factorTwoCenteredP5
  rw [show factorTwoCenteredP7 = fun x ↦
      (429 * x ^ 7 - 693 * x ^ 5 + 315 * x ^ 3 - 35 * x) / 16 by
    funext x
    exact factorTwoCenteredP7_eq x,
    show factorTwoCenteredP9 = fun x ↦
      (12155 * x ^ 9 - 25740 * x ^ 7 + 18018 * x ^ 5 -
        4620 * x ^ 3 + 315 * x) / 128 by
      funext x
      exact factorTwoCenteredP9_eq x]
  fun_prop

theorem odd_fourCellOddOneThreeFiveSevenNineLowProfile
    (c d e f g : ℝ) :
    Function.Odd (fourCellOddOneThreeFiveSevenNineLowProfile c d e f g) := by
  intro x
  unfold fourCellOddOneThreeFiveSevenNineLowProfile
  rw [odd_fourCellOddOneThreeFiveLowProfile c d e,
    odd_factorTwoCenteredP7, odd_factorTwoCenteredP9]
  ring

theorem fourCellOddOneThreeFiveSevenNineLowProfile_one
    (c d e f g : ℝ) :
    fourCellOddOneThreeFiveSevenNineLowProfile c d e f g 1 =
      c + d + e + f + g := by
  unfold fourCellOddOneThreeFiveSevenNineLowProfile
  rw [fourCellOddOneThreeFiveLowProfile_one,
    factorTwoCenteredP7_eq, factorTwoCenteredP9_eq]
  norm_num

/-- The sole genuinely arbitrary-tail Schur statement after retaining
`P₁/P₃/P₅/P₇/P₉`.  The residual hypotheses say exactly that its
shifted-Legendre expansion starts at `P₁₁`; the endpoint equation is the
uncollapsed trace forced by endpoint zero.  The right-hand side keeps the
complete local quadratic form, so this is a form/Riesz assertion rather
than a scalar-weight surrogate. -/
def fourCellOddOneThreeFiveSevenNineEndpointFormDualBound : Prop :=
  ∀ (c d e f g : ℝ) (r : ℝ → ℝ),
    ContDiff ℝ 1 r → Function.Odd r →
    centeredOddP1Coefficient r = 0 →
    centeredOddP3Coefficient r = 0 →
    centeredOddP5Coefficient r = 0 →
    centeredOddP7Coefficient r = 0 →
    centeredOddP9Coefficient r = 0 →
    r 1 = -(c + d + e + f + g) →
    fourCellOddCoreLocalBilinear
        (fourCellOddOneThreeFiveSevenNineLowProfile c d e f g) r ^ 2 ≤
      fourCellOddCoreLocalQuadratic
          (fourCellOddOneThreeFiveSevenNineLowProfile c d e f g) *
        fourCellOddCoreLocalQuadratic r

/-- Every `P₁₁+` residual already has a strictly controlled diagonal.
Thus the preceding mixed Riesz inequality, not tail positivity, is the
remaining infinite-dimensional issue. -/
theorem fourCellOddCoreLocalQuadratic_nonneg_of_P11Plus
    (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r)
    (hone : centeredOddP1Coefficient r = 0)
    (_hthree : centeredOddP3Coefficient r = 0)
    (_hfive : centeredOddP5Coefficient r = 0)
    (_hseven : centeredOddP7Coefficient r = 0)
    (_hnine : centeredOddP9Coefficient r = 0) :
    0 ≤ fourCellOddCoreLocalQuadratic r := by
  have htail := one_fiftieth_positiveHalfMass_le_core_add_localWidthDefect_of_P1
    r hr hodd hone
  have hmass : 0 ≤ ∫ x : ℝ in 0..1, r x ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num)
      (fun x _hx ↦ sq_nonneg (r x))
  change (1 / 50 : ℝ) * (∫ x : ℝ in 0..1, r x ^ 2) ≤
    fourCellOddCoreLocalQuadratic r at htail
  nlinarith

/-- `P₇` coefficient of the tail left after the canonical `P₁/P₃/P₅`
projection. -/
def fourCellOddP7TailCoefficient (w : ℝ → ℝ) : ℝ :=
  centeredOddP7Coefficient (fourCellOddOneThreeFiveResidual w)

/-- Residual after additionally removing the exact `P₇` direction. -/
def fourCellOddOneThreeFiveSevenResidual (w : ℝ → ℝ) : ℝ → ℝ :=
  fun x ↦ fourCellOddOneThreeFiveResidual w x -
    fourCellOddP7TailCoefficient w * factorTwoCenteredP7 x

/-- `P₉` coefficient of the residual already orthogonal through `P₇`. -/
def fourCellOddP9TailCoefficient (w : ℝ → ℝ) : ℝ :=
  centeredOddP9Coefficient (fourCellOddOneThreeFiveSevenResidual w)

/-- Canonical residual whose odd shifted-Legendre expansion starts at
`P₁₁`. -/
def fourCellOddOneThreeFiveSevenNineResidual (w : ℝ → ℝ) : ℝ → ℝ :=
  fun x ↦ fourCellOddOneThreeFiveSevenResidual w x -
    fourCellOddP9TailCoefficient w * factorTwoCenteredP9 x

/-- Canonical first-five-odd-mode part of an arbitrary profile. -/
def fourCellOddOneThreeFiveSevenNineLowPart (w : ℝ → ℝ) : ℝ → ℝ :=
  fourCellOddOneThreeFiveSevenNineLowProfile
    (centeredOddP1Coefficient w) (centeredOddP3Coefficient w)
      (fourCellOddP5TailCoefficient w) (fourCellOddP7TailCoefficient w)
        (fourCellOddP9TailCoefficient w)

theorem fourCellOddOneThreeFiveSevenNineLowPart_add_residual
    (w : ℝ → ℝ) :
    fourCellOddOneThreeFiveSevenNineLowPart w +
        fourCellOddOneThreeFiveSevenNineResidual w = w := by
  have hbase := fourCellOddOneThreeFiveLowPart_add_residual w
  funext x
  have hx := congrFun hbase x
  unfold fourCellOddOneThreeFiveSevenNineLowPart
    fourCellOddOneThreeFiveSevenNineLowProfile
    fourCellOddOneThreeFiveSevenNineResidual
    fourCellOddOneThreeFiveSevenResidual at ⊢
  unfold fourCellOddOneThreeFiveLowPart at hx
  simp only [Pi.add_apply] at hx ⊢
  linarith

theorem contDiff_fourCellOddOneThreeFiveSevenNineResidual
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) :
    ContDiff ℝ 1 (fourCellOddOneThreeFiveSevenNineResidual w) := by
  unfold fourCellOddOneThreeFiveSevenNineResidual
    fourCellOddOneThreeFiveSevenResidual
  exact ((contDiff_fourCellOddOneThreeFiveResidual w hw).sub
    (contDiff_const.mul contDiff_factorTwoCenteredP7_local)).sub
      (contDiff_const.mul contDiff_factorTwoCenteredP9_local)

theorem odd_fourCellOddOneThreeFiveSevenNineResidual
    (w : ℝ → ℝ) (hodd : Function.Odd w) :
    Function.Odd (fourCellOddOneThreeFiveSevenNineResidual w) := by
  intro x
  unfold fourCellOddOneThreeFiveSevenNineResidual
    fourCellOddOneThreeFiveSevenResidual
  rw [odd_fourCellOddOneThreeFiveResidual w hodd,
    odd_factorTwoCenteredP7, odd_factorTwoCenteredP9]
  ring

theorem fourCellOddOneThreeFiveSevenNineResidual_one_of_endpoint_zero
    (w : ℝ → ℝ) (hendpoint : w 1 = 0) :
    fourCellOddOneThreeFiveSevenNineResidual w 1 =
      -(centeredOddP1Coefficient w + centeredOddP3Coefficient w +
        fourCellOddP5TailCoefficient w + fourCellOddP7TailCoefficient w +
          fourCellOddP9TailCoefficient w) := by
  have hreconstruct := congrFun
    (fourCellOddOneThreeFiveSevenNineLowPart_add_residual w) 1
  rw [hendpoint] at hreconstruct
  unfold fourCellOddOneThreeFiveSevenNineLowPart at hreconstruct
  change
    fourCellOddOneThreeFiveSevenNineLowProfile
        (centeredOddP1Coefficient w) (centeredOddP3Coefficient w)
          (fourCellOddP5TailCoefficient w) (fourCellOddP7TailCoefficient w)
            (fourCellOddP9TailCoefficient w) 1 +
      fourCellOddOneThreeFiveSevenNineResidual w 1 = 0 at hreconstruct
  rw [fourCellOddOneThreeFiveSevenNineLowProfile_one] at hreconstruct
  linarith

private theorem centeredOddP1Coefficient_sub_const_mul_local
    (u v : ℝ → ℝ) (a : ℝ) (hu : Continuous u) (hv : Continuous v) :
    centeredOddP1Coefficient (fun x ↦ u x - a * v x) =
      centeredOddP1Coefficient u - a * centeredOddP1Coefficient v := by
  unfold centeredOddP1Coefficient
  rw [intervalIntegral_sub_const_mul_mul u v centeredP1 a (-1) 1
    hu hv (by unfold centeredP1; fun_prop)]
  ring

private theorem centeredOddP3Coefficient_sub_const_mul_local
    (u v : ℝ → ℝ) (a : ℝ) (hu : Continuous u) (hv : Continuous v) :
    centeredOddP3Coefficient (fun x ↦ u x - a * v x) =
      centeredOddP3Coefficient u - a * centeredOddP3Coefficient v := by
  unfold centeredOddP3Coefficient
  rw [intervalIntegral_sub_const_mul_mul u v centeredP3 a (-1) 1
    hu hv (by unfold centeredP3; fun_prop)]
  ring

private theorem centeredOddP5Coefficient_sub_const_mul_local
    (u v : ℝ → ℝ) (a : ℝ) (hu : Continuous u) (hv : Continuous v) :
    centeredOddP5Coefficient (fun x ↦ u x - a * v x) =
      centeredOddP5Coefficient u - a * centeredOddP5Coefficient v := by
  unfold centeredOddP5Coefficient
  rw [intervalIntegral_sub_const_mul_mul u v factorTwoCenteredP5 a (-1) 1
    hu hv continuous_factorTwoCenteredP5]
  ring

private theorem centeredOddP7Coefficient_sub_const_mul_local
    (u v : ℝ → ℝ) (a : ℝ) (hu : Continuous u) (hv : Continuous v) :
    centeredOddP7Coefficient (fun x ↦ u x - a * v x) =
      centeredOddP7Coefficient u - a * centeredOddP7Coefficient v := by
  unfold centeredOddP7Coefficient
  rw [intervalIntegral_sub_const_mul_mul u v factorTwoCenteredP7 a (-1) 1
    hu hv continuous_factorTwoCenteredP7]
  ring

private theorem centeredOddP9Coefficient_sub_const_mul_local
    (u v : ℝ → ℝ) (a : ℝ) (hu : Continuous u) (hv : Continuous v) :
    centeredOddP9Coefficient (fun x ↦ u x - a * v x) =
      centeredOddP9Coefficient u - a * centeredOddP9Coefficient v := by
  unfold centeredOddP9Coefficient
  rw [intervalIntegral_sub_const_mul_mul u v factorTwoCenteredP9 a (-1) 1
    hu hv continuous_factorTwoCenteredP9]
  ring

private theorem centeredOddP7Coefficient_P7_eq_one :
    centeredOddP7Coefficient factorTwoCenteredP7 = 1 := by
  unfold centeredOddP7Coefficient
  rw [show (fun x : ℝ ↦
      factorTwoCenteredP7 x * factorTwoCenteredP7 x) =
      fun x ↦ factorTwoCenteredP7 x ^ 2 by
    funext x
    ring,
    integral_factorTwoCenteredP7_sq]
  norm_num

private theorem centeredOddP9Coefficient_P9_eq_one :
    centeredOddP9Coefficient factorTwoCenteredP9 = 1 := by
  have henergy := factorTwoCenteredP9_energy
  unfold factorTwoIntrinsicEnergy at henergy
  unfold centeredOddP9Coefficient
  rw [show (fun x : ℝ ↦
      factorTwoCenteredP9 x * factorTwoCenteredP9 x) =
      fun x ↦ factorTwoCenteredP9 x ^ 2 by
    funext x
    ring,
    henergy]
  norm_num

private theorem centeredOddP7Coefficient_P9_eq_zero :
    centeredOddP7Coefficient factorTwoCenteredP9 = 0 := by
  have hunit := factorTwoCenteredP9_momentsVanishBelow 7 (by norm_num)
  rw [integral_centeredPullback_mul_shiftedLegendre_eq_neg_half_local
      7 factorTwoCenteredP7 factorTwoCenteredP9
        centeredPullback_factorTwoCenteredP7] at hunit
  have hfull : (∫ x : ℝ in -1..1,
      factorTwoCenteredP9 x * factorTwoCenteredP7 x) = 0 := by
    nlinarith
  unfold centeredOddP7Coefficient
  rw [hfull]
  ring

private theorem continuous_fourCellOddOneThreeFiveResidual_local
    (w : ℝ → ℝ) (hw : Continuous w) :
    Continuous (fourCellOddOneThreeFiveResidual w) := by
  unfold fourCellOddOneThreeFiveResidual centeredOddOneThreeResidual
    centeredP1 centeredP3 factorTwoCenteredP5
  fun_prop

theorem centeredOddLowCoefficients_oneThreeFiveSevenNineResidual_eq_zero
    (w : ℝ → ℝ) (hw : Continuous w) :
    centeredOddP1Coefficient
          (fourCellOddOneThreeFiveSevenNineResidual w) = 0 ∧
      centeredOddP3Coefficient
          (fourCellOddOneThreeFiveSevenNineResidual w) = 0 ∧
        centeredOddP5Coefficient
          (fourCellOddOneThreeFiveSevenNineResidual w) = 0 := by
  let r5 := fourCellOddOneThreeFiveResidual w
  let r7 := fourCellOddOneThreeFiveSevenResidual w
  have hr5 : Continuous r5 := by
    dsimp only [r5]
    exact continuous_fourCellOddOneThreeFiveResidual_local w hw
  have hr7 : Continuous r7 := by
    dsimp only [r7, fourCellOddOneThreeFiveSevenResidual]
    exact hr5.sub (continuous_const.mul continuous_factorTwoCenteredP7)
  rcases centeredOddCoefficients_P7_eq_zero with ⟨h71, h73, h75⟩
  rcases centeredOddCoefficients_P9_eq_zero with ⟨h91, h93, h95⟩
  have h1 := centeredOddP1Coefficient_oneThreeFiveResidual_eq_zero w hw
  have h3 := centeredOddP3Coefficient_oneThreeFiveResidual_eq_zero w hw
  have h5 := centeredOddP5Coefficient_oneThreeFiveResidual_eq_zero w hw
  have hr71 : centeredOddP1Coefficient r7 = 0 := by
    change centeredOddP1Coefficient
      (fun x ↦ r5 x - fourCellOddP7TailCoefficient w *
        factorTwoCenteredP7 x) = 0
    rw [centeredOddP1Coefficient_sub_const_mul_local _ _ _ hr5
      continuous_factorTwoCenteredP7, h1, h71]
    ring
  have hr73 : centeredOddP3Coefficient r7 = 0 := by
    change centeredOddP3Coefficient
      (fun x ↦ r5 x - fourCellOddP7TailCoefficient w *
        factorTwoCenteredP7 x) = 0
    rw [centeredOddP3Coefficient_sub_const_mul_local _ _ _ hr5
      continuous_factorTwoCenteredP7, h3, h73]
    ring
  have hr75 : centeredOddP5Coefficient r7 = 0 := by
    change centeredOddP5Coefficient
      (fun x ↦ r5 x - fourCellOddP7TailCoefficient w *
        factorTwoCenteredP7 x) = 0
    rw [centeredOddP5Coefficient_sub_const_mul_local _ _ _ hr5
      continuous_factorTwoCenteredP7, h5, h75]
    ring
  change
    centeredOddP1Coefficient
          (fun x ↦ r7 x - fourCellOddP9TailCoefficient w *
            factorTwoCenteredP9 x) = 0 ∧
      centeredOddP3Coefficient
          (fun x ↦ r7 x - fourCellOddP9TailCoefficient w *
            factorTwoCenteredP9 x) = 0 ∧
        centeredOddP5Coefficient
          (fun x ↦ r7 x - fourCellOddP9TailCoefficient w *
            factorTwoCenteredP9 x) = 0
  constructor
  · rw [centeredOddP1Coefficient_sub_const_mul_local _ _ _ hr7
      continuous_factorTwoCenteredP9, hr71, h91]
    ring
  constructor
  · rw [centeredOddP3Coefficient_sub_const_mul_local _ _ _ hr7
      continuous_factorTwoCenteredP9, hr73, h93]
    ring
  · rw [centeredOddP5Coefficient_sub_const_mul_local _ _ _ hr7
      continuous_factorTwoCenteredP9, hr75, h95]
    ring

theorem centeredOddP7Coefficient_oneThreeFiveSevenNineResidual_eq_zero
    (w : ℝ → ℝ) (hw : Continuous w) :
    centeredOddP7Coefficient
        (fourCellOddOneThreeFiveSevenNineResidual w) = 0 := by
  let r5 := fourCellOddOneThreeFiveResidual w
  let r7 := fourCellOddOneThreeFiveSevenResidual w
  have hr5 : Continuous r5 := by
    dsimp only [r5]
    exact continuous_fourCellOddOneThreeFiveResidual_local w hw
  have hr7 : Continuous r7 := by
    dsimp only [r7, fourCellOddOneThreeFiveSevenResidual]
    exact hr5.sub (continuous_const.mul continuous_factorTwoCenteredP7)
  have hr77 : centeredOddP7Coefficient r7 = 0 := by
    change centeredOddP7Coefficient
      (fun x ↦ r5 x - fourCellOddP7TailCoefficient w *
        factorTwoCenteredP7 x) = 0
    rw [centeredOddP7Coefficient_sub_const_mul_local _ _ _ hr5
      continuous_factorTwoCenteredP7, centeredOddP7Coefficient_P7_eq_one]
    unfold fourCellOddP7TailCoefficient
    ring
  change centeredOddP7Coefficient
    (fun x ↦ r7 x - fourCellOddP9TailCoefficient w *
      factorTwoCenteredP9 x) = 0
  rw [centeredOddP7Coefficient_sub_const_mul_local _ _ _ hr7
    continuous_factorTwoCenteredP9, hr77,
    centeredOddP7Coefficient_P9_eq_zero]
  ring

theorem centeredOddP9Coefficient_oneThreeFiveSevenNineResidual_eq_zero
    (w : ℝ → ℝ) (hw : Continuous w) :
    centeredOddP9Coefficient
        (fourCellOddOneThreeFiveSevenNineResidual w) = 0 := by
  let r7 := fourCellOddOneThreeFiveSevenResidual w
  have hr7 : Continuous r7 := by
    dsimp only [r7, fourCellOddOneThreeFiveSevenResidual]
    exact (continuous_fourCellOddOneThreeFiveResidual_local w hw).sub
      (continuous_const.mul continuous_factorTwoCenteredP7)
  change centeredOddP9Coefficient
    (fun x ↦ r7 x - fourCellOddP9TailCoefficient w *
      factorTwoCenteredP9 x) = 0
  rw [centeredOddP9Coefficient_sub_const_mul_local _ _ _ hr7
      continuous_factorTwoCenteredP9,
    centeredOddP9Coefficient_P9_eq_one]
  unfold fourCellOddP9TailCoefficient
  dsimp only [r7]
  ring

private theorem add_two_mul_add_nonneg_of_sq_le_mul_fiveMode
    (a b m : ℝ) (ha : 0 ≤ a) (hm : 0 ≤ m)
    (hschur : b ^ 2 ≤ a * m) :
    0 ≤ a + 2 * b + m := by
  by_cases hb : 0 ≤ b
  · linarith
  · have hmb : 0 ≤ -2 * b := by linarith
    have ham : 0 ≤ a + m := add_nonneg ha hm
    have hsquares : (-2 * b) ^ 2 ≤ (a + m) ^ 2 := by
      nlinarith [sq_nonneg (a - m)]
    have hlinear := (sq_le_sq₀ hmb ham).mp hsquares
    linarith

theorem fourCellOddCoreLocal_oneThreeFiveSevenNine_decomposition
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) :
    fourCellOddCoreLocalQuadratic w =
      fourCellOddCoreLocalQuadratic
          (fourCellOddOneThreeFiveSevenNineLowPart w) +
        2 * fourCellOddCoreLocalBilinear
          (fourCellOddOneThreeFiveSevenNineLowPart w)
          (fourCellOddOneThreeFiveSevenNineResidual w) +
        fourCellOddCoreLocalQuadratic
          (fourCellOddOneThreeFiveSevenNineResidual w) := by
  let p := fourCellOddOneThreeFiveSevenNineLowPart w
  let r := fourCellOddOneThreeFiveSevenNineResidual w
  have hp : Continuous p := by
    dsimp only [p, fourCellOddOneThreeFiveSevenNineLowPart]
    exact (contDiff_fourCellOddOneThreeFiveSevenNineLowProfile _ _ _ _ _).continuous
  have hr : Continuous r := by
    dsimp only [r]
    exact (contDiff_fourCellOddOneThreeFiveSevenNineResidual w hw).continuous
  have hadd := fourCellOddCoreLocalQuadratic_add p r hp hr
  have hreconstruct : p + r = w := by
    dsimp only [p, r]
    exact fourCellOddOneThreeFiveSevenNineLowPart_add_residual w
  rw [hreconstruct] at hadd
  exact hadd

/-- Exact endpoint-zero reduction through `P₉`.  Once the finite
five-mode form is nonnegative, universal odd closure is equivalent to the
single `P₁₁+` Riesz premise above; the arbitrary residual diagonal and
the projection identities are discharged here. -/
theorem fourCellOddCoreLocalQuadratic_nonneg_of_endpointZero_fiveMode_formDual
    (hfinite : ∀ c d e f g : ℝ,
      0 ≤ fourCellOddCoreLocalQuadratic
        (fourCellOddOneThreeFiveSevenNineLowProfile c d e f g))
    (hdual : fourCellOddOneThreeFiveSevenNineEndpointFormDualBound)
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w)
    (hendpoint : w (-1) = 0 ∧ w 1 = 0) :
    0 ≤ fourCellOddCoreLocalQuadratic w := by
  let c := centeredOddP1Coefficient w
  let d := centeredOddP3Coefficient w
  let e := fourCellOddP5TailCoefficient w
  let f := fourCellOddP7TailCoefficient w
  let g := fourCellOddP9TailCoefficient w
  let p := fourCellOddOneThreeFiveSevenNineLowPart w
  let r := fourCellOddOneThreeFiveSevenNineResidual w
  have hr : ContDiff ℝ 1 r := by
    dsimp only [r]
    exact contDiff_fourCellOddOneThreeFiveSevenNineResidual w hw
  have hrodd : Function.Odd r := by
    dsimp only [r]
    exact odd_fourCellOddOneThreeFiveSevenNineResidual w hodd
  rcases centeredOddLowCoefficients_oneThreeFiveSevenNineResidual_eq_zero
      w hw.continuous with ⟨hr1, hr3, hr5⟩
  have hr7 : centeredOddP7Coefficient r = 0 := by
    dsimp only [r]
    exact centeredOddP7Coefficient_oneThreeFiveSevenNineResidual_eq_zero
      w hw.continuous
  have hr9 : centeredOddP9Coefficient r = 0 := by
    dsimp only [r]
    exact centeredOddP9Coefficient_oneThreeFiveSevenNineResidual_eq_zero
      w hw.continuous
  have hrone : r 1 = -(c + d + e + f + g) := by
    dsimp only [r, c, d, e, f, g]
    exact fourCellOddOneThreeFiveSevenNineResidual_one_of_endpoint_zero
      w hendpoint.2
  have hp : p = fourCellOddOneThreeFiveSevenNineLowProfile c d e f g := by
    rfl
  have hlow : 0 ≤ fourCellOddCoreLocalQuadratic p := by
    rw [hp]
    exact hfinite c d e f g
  have htail : 0 ≤ fourCellOddCoreLocalQuadratic r :=
    fourCellOddCoreLocalQuadratic_nonneg_of_P11Plus
      r hr hrodd hr1 hr3 hr5 hr7 hr9
  have hschur : fourCellOddCoreLocalBilinear p r ^ 2 ≤
      fourCellOddCoreLocalQuadratic p * fourCellOddCoreLocalQuadratic r := by
    rw [hp]
    exact hdual c d e f g r hr hrodd hr1 hr3 hr5 hr7 hr9 hrone
  have hcompleted : 0 ≤
      fourCellOddCoreLocalQuadratic p +
        2 * fourCellOddCoreLocalBilinear p r +
          fourCellOddCoreLocalQuadratic r :=
    add_two_mul_add_nonneg_of_sq_le_mul_fiveMode
      _ _ _ hlow htail hschur
  have hdecomp :=
    fourCellOddCoreLocal_oneThreeFiveSevenNine_decomposition w hw
  dsimp only [p, r] at hcompleted
  linarith

private theorem centeredRawLogBilinear_symm_local
    (u v : ℝ → ℝ) :
    centeredRawLogBilinear u v = centeredRawLogBilinear v u := by
  unfold centeredRawLogBilinear
  apply intervalIntegral.integral_congr
  intro x _hx
  apply intervalIntegral.integral_congr
  intro y _hy
  ring

private theorem centeredRawLogBilinear_add_left_local
    (u v w : ℝ → ℝ)
    (hu : LocallyLipschitzOn (Icc (-1 : ℝ) 1) u)
    (hv : LocallyLipschitzOn (Icc (-1 : ℝ) 1) v)
    (hw : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w) :
    centeredRawLogBilinear (u + v) w =
      centeredRawLogBilinear u w + centeredRawLogBilinear v w := by
  rw [centeredRawLogBilinear_eq_two_mul_unitCross_local
      (u + v) w (hu.add hv) hw,
    centeredRawLogBilinear_eq_two_mul_unitCross_local u w hu hw,
    centeredRawLogBilinear_eq_two_mul_unitCross_local v w hv hw]
  let fu : unitInterval → ℝ := fun t ↦ centeredPullback u (t : ℝ)
  let fv : unitInterval → ℝ := fun t ↦ centeredPullback v (t : ℝ)
  let fw : unitInterval → ℝ := fun t ↦ centeredPullback w (t : ℝ)
  obtain ⟨C, hfu⟩ := exists_lipschitzWith_centeredPullback u hu
  obtain ⟨D, hfv⟩ := exists_lipschitzWith_centeredPullback v hv
  obtain ⟨E, hfw⟩ := exists_lipschitzWith_centeredPullback w hw
  have huInt := integrable_fourCellUnitIntervalRawLogCrossIntegrand
    fu fw hfu hfw
  have hvInt := integrable_fourCellUnitIntervalRawLogCrossIntegrand
    fv fw hfv hfw
  rw [show (fun z : unitInterval × unitInterval ↦
      fourCellUnitIntervalRawLogCrossIntegrand
        (fun t ↦ centeredPullback (u + v) (t : ℝ)) fw z) =
      fun z ↦ fourCellUnitIntervalRawLogCrossIntegrand fu fw z +
        fourCellUnitIntervalRawLogCrossIntegrand fv fw z by
    funext z
    unfold fourCellUnitIntervalRawLogCrossIntegrand fu fv fw centeredPullback
    simp only [Pi.add_apply]
    ring,
    integral_add huInt hvInt]
  ring

private theorem centeredRawLogBilinear_const_mul_left_local
    (u v : ℝ → ℝ) (a : ℝ) :
    centeredRawLogBilinear (fun x ↦ a * u x) v =
      a * centeredRawLogBilinear u v := by
  rw [centeredRawLogBilinear_symm_local,
    centeredRawLogBilinear_const_mul_right_local,
    centeredRawLogBilinear_symm_local]

private theorem centeredRawLogBilinear_neg_shiftedLegendre_eq_moment_local
    (n : ℕ) (q r : ℝ → ℝ) (hr : Continuous r)
    (hmode : ∀ t : ℝ, centeredPullback q t =
      -(shiftedLegendreReal n).eval t) :
    centeredRawLogBilinear q r =
      4 * (harmonic n : ℝ) * (∫ x : ℝ in -1..1, r x * q x) := by
  let p : ℝ[X] := -(shiftedLegendreReal n)
  have hmode' (t : ℝ) : centeredPullback q t = p.eval t := by
    dsimp only [p]
    rw [Polynomial.eval_neg, hmode]
  have hunit := integral_centeredPullback_mul_shiftedLegendre_eq_neg_half_local
    n q r hmode
  have hpLog : shiftedLogKernel p =
      -(Polynomial.C (2 * (harmonic n : ℝ)) * shiftedLegendreReal n) := by
    dsimp only [p]
    rw [map_neg, shiftedLogKernel_shiftedLegendreReal]
  have hpair : (∫ t : unitInterval,
      centeredPullback r (t : ℝ) *
        (shiftedLogKernel p).eval (t : ℝ)) =
      (harmonic n : ℝ) * (∫ x : ℝ in -1..1, r x * q x) := by
    rw [hpLog]
    simp only [Polynomial.eval_neg, Polynomial.eval_mul, Polynomial.eval_C]
    rw [show (fun t : unitInterval ↦ centeredPullback r (t : ℝ) *
        -(2 * (harmonic n : ℝ) *
          (shiftedLegendreReal n).eval (t : ℝ))) =
      fun t : unitInterval ↦ -(2 * (harmonic n : ℝ)) *
        (centeredPullback r (t : ℝ) *
          (shiftedLegendreReal n).eval (t : ℝ)) by
      funext t
      ring,
      integral_const_mul, hunit]
    ring
  rw [centeredRawLogBilinear_polynomialMode_eq_four_mul_pair
    p q r hr hmode', hpair]
  ring

private theorem centeredRawLogBilinear_P7_tail_eq_zero_local
    (r : ℝ → ℝ) (hr : Continuous r)
    (hseven : centeredOddP7Coefficient r = 0) :
    centeredRawLogBilinear factorTwoCenteredP7 r = 0 := by
  have h := centeredRawLogBilinear_neg_shiftedLegendre_eq_moment_local
    7 factorTwoCenteredP7 r hr centeredPullback_factorTwoCenteredP7
  unfold centeredOddP7Coefficient at hseven
  have hmoment : (∫ x : ℝ in -1..1,
      r x * factorTwoCenteredP7 x) = 0 := by
    nlinarith
  rw [hmoment] at h
  simpa using h

private theorem centeredRawLogBilinear_P9_tail_eq_zero_local
    (r : ℝ → ℝ) (hr : Continuous r)
    (hnine : centeredOddP9Coefficient r = 0) :
    centeredRawLogBilinear factorTwoCenteredP9 r = 0 := by
  have h := centeredRawLogBilinear_neg_shiftedLegendre_eq_moment_local
    9 factorTwoCenteredP9 r hr centeredPullback_factorTwoCenteredP9
  unfold centeredOddP9Coefficient at hnine
  have hmoment : (∫ x : ℝ in -1..1,
      r x * factorTwoCenteredP9 x) = 0 := by
    nlinarith
  rw [hmoment] at h
  simpa using h

/-- The complete global singular raw cross vanishes between the retained
five-mode pivot and a genuine `P₁₁+` residual. -/
theorem centeredRawLogBilinear_oneThreeFiveSevenNine_tail_eq_zero
    (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r)
    (hone : centeredOddP1Coefficient r = 0)
    (hthree : centeredOddP3Coefficient r = 0)
    (hfive : centeredOddP5Coefficient r = 0)
    (hseven : centeredOddP7Coefficient r = 0)
    (hnine : centeredOddP9Coefficient r = 0)
    (c d e f g : ℝ) :
    centeredRawLogBilinear
      (fourCellOddOneThreeFiveSevenNineLowProfile c d e f g) r = 0 := by
  have hp135 :=
    centeredRawLogBilinear_oneThreeFiveLowProfile_tail_eq_zero
      r hr.continuous hone hthree hfive c d e
  have hp7 := centeredRawLogBilinear_P7_tail_eq_zero_local
    r hr.continuous hseven
  have hp9 := centeredRawLogBilinear_P9_tail_eq_zero_local
    r hr.continuous hnine
  have hrLocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) r :=
    hr.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1)
  have hp135Local : LocallyLipschitzOn (Icc (-1 : ℝ) 1)
      (fourCellOddOneThreeFiveLowProfile c d e) :=
    (contDiff_fourCellOddOneThreeFiveLowProfile c d e).contDiffOn
      |>.locallyLipschitzOn (convex_Icc (-1) 1)
  have hp7Local : LocallyLipschitzOn (Icc (-1 : ℝ) 1)
      (fun x ↦ f * factorTwoCenteredP7 x) :=
    (contDiff_const.mul contDiff_factorTwoCenteredP7_local).contDiffOn
      |>.locallyLipschitzOn (convex_Icc (-1) 1)
  have hp9Local : LocallyLipschitzOn (Icc (-1 : ℝ) 1)
      (fun x ↦ g * factorTwoCenteredP9 x) :=
    (contDiff_const.mul contDiff_factorTwoCenteredP9_local).contDiffOn
      |>.locallyLipschitzOn (convex_Icc (-1) 1)
  have hinner := centeredRawLogBilinear_add_left_local
    (fourCellOddOneThreeFiveLowProfile c d e)
      (fun x ↦ f * factorTwoCenteredP7 x) r
        hp135Local hp7Local hrLocal
  have houter := centeredRawLogBilinear_add_left_local
    (fourCellOddOneThreeFiveLowProfile c d e +
      fun x ↦ f * factorTwoCenteredP7 x)
      (fun x ↦ g * factorTwoCenteredP9 x) r
        (hp135Local.add hp7Local) hp9Local hrLocal
  calc
    centeredRawLogBilinear
        (fourCellOddOneThreeFiveSevenNineLowProfile c d e f g) r =
      centeredRawLogBilinear
        ((fourCellOddOneThreeFiveLowProfile c d e +
            fun x ↦ f * factorTwoCenteredP7 x) +
          fun x ↦ g * factorTwoCenteredP9 x) r := by
        congr 1
    _ = centeredRawLogBilinear
          (fourCellOddOneThreeFiveLowProfile c d e +
            fun x ↦ f * factorTwoCenteredP7 x) r +
        centeredRawLogBilinear
          (fun x ↦ g * factorTwoCenteredP9 x) r := houter
    _ = (centeredRawLogBilinear
          (fourCellOddOneThreeFiveLowProfile c d e) r +
        centeredRawLogBilinear
          (fun x ↦ f * factorTwoCenteredP7 x) r) +
        centeredRawLogBilinear
          (fun x ↦ g * factorTwoCenteredP9 x) r := by rw [hinner]
    _ = 0 := by
      rw [centeredRawLogBilinear_const_mul_left_local,
        centeredRawLogBilinear_const_mul_left_local, hp135, hp7, hp9]
      ring

/-- Exact singular normal form of the five-mode/`P₁₁+` mixed row:
the global raw operator is gone, leaving only the adverse endpoint-strip
polarization. -/
theorem fourCellOddRawStripCancellationPolarization_fiveMode_tail_eq
    (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r)
    (hone : centeredOddP1Coefficient r = 0)
    (hthree : centeredOddP3Coefficient r = 0)
    (hfive : centeredOddP5Coefficient r = 0)
    (hseven : centeredOddP7Coefficient r = 0)
    (hnine : centeredOddP9Coefficient r = 0)
    (c d e f g : ℝ) :
    fourCellOddRawStripCancellationPolarization
        (fourCellOddOneThreeFiveSevenNineLowProfile c d e f g) r =
      -(1 / 2 : ℝ) * fourCellOddEndpointStripOddRawPolarization
        (fourCellOddOneThreeFiveSevenNineLowProfile c d e f g) r := by
  rw [fourCellOddRawStripCancellationPolarization_eq_centered_sub_strip
      _ r (contDiff_fourCellOddOneThreeFiveSevenNineLowProfile c d e f g)
        hr (odd_fourCellOddOneThreeFiveSevenNineLowProfile c d e f g) hodd,
    centeredRawLogBilinear_oneThreeFiveSevenNine_tail_eq_zero
      r hr hone hthree hfive hseven hnine c d e f g]
  ring

/-- Final exact normal form of the unresolved `P₁₁+` Riesz row. -/
theorem fourCellOddCoreLocalBilinear_fiveMode_tail_eq_endpointForms
    (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r)
    (hone : centeredOddP1Coefficient r = 0)
    (hthree : centeredOddP3Coefficient r = 0)
    (hfive : centeredOddP5Coefficient r = 0)
    (hseven : centeredOddP7Coefficient r = 0)
    (hnine : centeredOddP9Coefficient r = 0)
    (c d e f g : ℝ) :
    fourCellOddCoreLocalBilinear
        (fourCellOddOneThreeFiveSevenNineLowProfile c d e f g) r =
      -(1 / 2 : ℝ) * fourCellOddEndpointStripOddRawPolarization
          (fourCellOddOneThreeFiveSevenNineLowProfile c d e f g) r +
        fourCellOddStripReducedBilinear
          (fourCellOddOneThreeFiveSevenNineLowProfile c d e f g) r := by
  unfold fourCellOddCoreLocalBilinear
  rw [fourCellOddRawStripCancellationPolarization_fiveMode_tail_eq
    r hr hodd hone hthree hfive hseven hnine c d e f g]

private theorem integral_zero_one_P7_mul_P11Plus_eq_zero
    (r : ℝ → ℝ) (hr : Continuous r) (hodd : Function.Odd r)
    (hseven : centeredOddP7Coefficient r = 0) :
    (∫ x : ℝ in 0..1, factorTwoCenteredP7 x * r x) = 0 := by
  have hfullReverse : (∫ x : ℝ in -1..1,
      r x * factorTwoCenteredP7 x) = 0 := by
    unfold centeredOddP7Coefficient at hseven
    nlinarith
  have hfull : (∫ x : ℝ in -1..1,
      factorTwoCenteredP7 x * r x) = 0 := by
    calc
      _ = ∫ x : ℝ in -1..1, r x * factorTwoCenteredP7 x := by
        apply intervalIntegral.integral_congr
        intro x _hx
        ring
      _ = 0 := hfullReverse
  let F : ℝ → ℝ := fun x ↦ factorTwoCenteredP7 x * r x
  have hF : IntervalIntegrable F volume (-1) 1 :=
    (continuous_factorTwoCenteredP7.mul hr).intervalIntegrable _ _
  have hFeven : Function.Even F := by
    intro x
    dsimp only [F]
    rw [odd_factorTwoCenteredP7, hodd]
    ring
  have hfold := integral_neg_one_one_eq_two_mul_zero_one_of_even F hF hFeven
  dsimp only [F] at hfold
  rw [hfull] at hfold
  linarith

private theorem integral_zero_one_P9_mul_P11Plus_eq_zero
    (r : ℝ → ℝ) (hr : Continuous r) (hodd : Function.Odd r)
    (hnine : centeredOddP9Coefficient r = 0) :
    (∫ x : ℝ in 0..1, factorTwoCenteredP9 x * r x) = 0 := by
  have hfullReverse : (∫ x : ℝ in -1..1,
      r x * factorTwoCenteredP9 x) = 0 := by
    unfold centeredOddP9Coefficient at hnine
    nlinarith
  have hfull : (∫ x : ℝ in -1..1,
      factorTwoCenteredP9 x * r x) = 0 := by
    calc
      _ = ∫ x : ℝ in -1..1, r x * factorTwoCenteredP9 x := by
        apply intervalIntegral.integral_congr
        intro x _hx
        ring
      _ = 0 := hfullReverse
  let F : ℝ → ℝ := fun x ↦ factorTwoCenteredP9 x * r x
  have hF : IntervalIntegrable F volume (-1) 1 :=
    (continuous_factorTwoCenteredP9.mul hr).intervalIntegrable _ _
  have hFeven : Function.Even F := by
    intro x
    dsimp only [F]
    rw [odd_factorTwoCenteredP9, hodd]
    ring
  have hfold := integral_neg_one_one_eq_two_mul_zero_one_of_even F hF hFeven
  dsimp only [F] at hfold
  rw [hfull] at hfold
  linarith

/-- Exact positive-half mass orthogonality of the five-mode pivot and its
`P₁₁+` residual. -/
theorem integral_zero_one_fiveMode_mul_P11Plus_eq_zero
    (r : ℝ → ℝ) (hr : Continuous r) (hodd : Function.Odd r)
    (hone : centeredOddP1Coefficient r = 0)
    (hthree : centeredOddP3Coefficient r = 0)
    (hfive : centeredOddP5Coefficient r = 0)
    (hseven : centeredOddP7Coefficient r = 0)
    (hnine : centeredOddP9Coefficient r = 0)
    (c d e f g : ℝ) :
    (∫ x : ℝ in 0..1,
      fourCellOddOneThreeFiveSevenNineLowProfile c d e f g x * r x) = 0 := by
  have h135 := integral_zero_one_oneThreeFiveLowProfile_mul_tail_eq_zero
    r hr hodd hone hthree hfive c d e
  have h7 := integral_zero_one_P7_mul_P11Plus_eq_zero
    r hr hodd hseven
  have h9 := integral_zero_one_P9_mul_P11Plus_eq_zero
    r hr hodd hnine
  have h135I : IntervalIntegrable (fun x : ℝ ↦
      fourCellOddOneThreeFiveLowProfile c d e x * r x) volume 0 1 :=
    ((contDiff_fourCellOddOneThreeFiveLowProfile c d e).continuous.mul hr)
      |>.intervalIntegrable _ _
  have h7I : IntervalIntegrable (fun x : ℝ ↦
      f * (factorTwoCenteredP7 x * r x)) volume 0 1 :=
    (continuous_const.mul (continuous_factorTwoCenteredP7.mul hr))
      |>.intervalIntegrable _ _
  have h9I : IntervalIntegrable (fun x : ℝ ↦
      g * (factorTwoCenteredP9 x * r x)) volume 0 1 :=
    (continuous_const.mul (continuous_factorTwoCenteredP9.mul hr))
      |>.intervalIntegrable _ _
  unfold fourCellOddOneThreeFiveSevenNineLowProfile
  rw [show (fun x : ℝ ↦
      (fourCellOddOneThreeFiveLowProfile c d e x +
        f * factorTwoCenteredP7 x + g * factorTwoCenteredP9 x) * r x) =
      fun x ↦ fourCellOddOneThreeFiveLowProfile c d e x * r x +
        f * (factorTwoCenteredP7 x * r x) +
          g * (factorTwoCenteredP9 x * r x) by
    funext x
    ring,
    intervalIntegral.integral_add (h135I.add h7I) h9I,
    intervalIntegral.integral_add h135I h7I,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    h135, h7, h9]
  ring

/-- On the five-mode/`P₁₁+` row the signed scalar mass vanishes
exactly; only the wide regular correlation remains. -/
theorem fourCellOddSignedMassRegularBilinear_fiveMode_tail_eq_regular
    (r : ℝ → ℝ) (hr : Continuous r) (hodd : Function.Odd r)
    (hone : centeredOddP1Coefficient r = 0)
    (hthree : centeredOddP3Coefficient r = 0)
    (hfive : centeredOddP5Coefficient r = 0)
    (hseven : centeredOddP7Coefficient r = 0)
    (hnine : centeredOddP9Coefficient r = 0)
    (c d e f g : ℝ) :
    fourCellOddSignedMassRegularBilinear
        (fourCellOddOneThreeFiveSevenNineLowProfile c d e f g) r =
      2 * fourCellOperatorHalfWidth *
        (∫ t : ℝ in 0..2,
          yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
            factorTwoCenteredCorrelationBilinear
              (fourCellOddOneThreeFiveSevenNineLowProfile c d e f g) r t) := by
  unfold fourCellOddSignedMassRegularBilinear
  rw [integral_zero_one_fiveMode_mul_P11Plus_eq_zero
    r hr hodd hone hthree hfive hseven hnine c d e f g]
  ring

/-- Fully reduced exact `P₁₁+` mixed row: both the global raw cross
and scalar mass cross have vanished. -/
theorem fourCellOddCoreLocalBilinear_fiveMode_P11Plus_fullyReduced
    (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r)
    (hone : centeredOddP1Coefficient r = 0)
    (hthree : centeredOddP3Coefficient r = 0)
    (hfive : centeredOddP5Coefficient r = 0)
    (hseven : centeredOddP7Coefficient r = 0)
    (hnine : centeredOddP9Coefficient r = 0)
    (c d e f g : ℝ) :
    fourCellOddCoreLocalBilinear
        (fourCellOddOneThreeFiveSevenNineLowProfile c d e f g) r =
      -(1 / 2 : ℝ) * fourCellOddEndpointStripOddRawPolarization
          (fourCellOddOneThreeFiveSevenNineLowProfile c d e f g) r +
        fourCellOddRetainedPrimePotentialBilinear
          (fourCellOddOneThreeFiveSevenNineLowProfile c d e f g) r -
        2 * fourCellOperatorHalfWidth *
          (∫ t : ℝ in 0..2,
            yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
              factorTwoCenteredCorrelationBilinear
                (fourCellOddOneThreeFiveSevenNineLowProfile c d e f g) r t) := by
  rw [fourCellOddCoreLocalBilinear_eq_retained_sub_signed]
  unfold fourCellOddRetainedEndpointBilinear
  rw [fourCellOddRawStripCancellationPolarization_fiveMode_tail_eq
      r hr hodd hone hthree hfive hseven hnine c d e f g,
    fourCellOddSignedMassRegularBilinear_fiveMode_tail_eq_regular
      r hr.continuous hodd hone hthree hfive hseven hnine c d e f g]

/-- Complete structural Cauchy bound for the surviving wide-regular row
against a `P₁₁+` residual. -/
theorem fourCellOddSignedMassRegularBilinear_fiveMode_tail_sq_le_energy_mul
    (r : ℝ → ℝ) (hr : Continuous r) (hodd : Function.Odd r)
    (hone : centeredOddP1Coefficient r = 0)
    (hthree : centeredOddP3Coefficient r = 0)
    (hfive : centeredOddP5Coefficient r = 0)
    (hseven : centeredOddP7Coefficient r = 0)
    (hnine : centeredOddP9Coefficient r = 0)
    (c d e f g : ℝ) :
    fourCellOddSignedMassRegularBilinear
        (fourCellOddOneThreeFiveSevenNineLowProfile c d e f g) r ^ 2 ≤
      (fourCellOperatorHalfWidth / 10) ^ 2 *
        factorTwoIntrinsicEnergy
          (fourCellOddOneThreeFiveSevenNineLowProfile c d e f g) *
        factorTwoIntrinsicEnergy r := by
  apply fourCellOddSignedMassRegularBilinear_sq_le_energy_mul_of_mass_eq_zero
    (fourCellOddOneThreeFiveSevenNineLowProfile c d e f g) r
      (contDiff_fourCellOddOneThreeFiveSevenNineLowProfile c d e f g).continuous
      hr (odd_fourCellOddOneThreeFiveSevenNineLowProfile c d e f g) hodd
  exact integral_zero_one_fiveMode_mul_P11Plus_eq_zero
    r hr hodd hone hthree hfive hseven hnine c d e f g

/-- The wide-regular row is already absorbed by the proved residual
diagonal, at the explicit finite cost `a²` times the pivot intrinsic energy.
-/
theorem fourCellOddSignedMassRegularBilinear_fiveMode_tail_sq_le_lowEnergy_mul_core
    (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r)
    (hone : centeredOddP1Coefficient r = 0)
    (hthree : centeredOddP3Coefficient r = 0)
    (hfive : centeredOddP5Coefficient r = 0)
    (hseven : centeredOddP7Coefficient r = 0)
    (hnine : centeredOddP9Coefficient r = 0)
    (c d e f g : ℝ) :
    fourCellOddSignedMassRegularBilinear
        (fourCellOddOneThreeFiveSevenNineLowProfile c d e f g) r ^ 2 ≤
      fourCellOperatorHalfWidth ^ 2 *
        factorTwoIntrinsicEnergy
          (fourCellOddOneThreeFiveSevenNineLowProfile c d e f g) *
        fourCellOddCoreLocalQuadratic r := by
  let E := factorTwoIntrinsicEnergy
    (fourCellOddOneThreeFiveSevenNineLowProfile c d e f g)
  have hsigned :=
    fourCellOddSignedMassRegularBilinear_fiveMode_tail_sq_le_energy_mul
      r hr.continuous hodd hone hthree hfive hseven hnine c d e f g
  have htail := one_fiftieth_positiveHalfMass_le_core_add_localWidthDefect_of_P1
    r hr hodd hone
  change (1 / 50 : ℝ) * (∫ x : ℝ in 0..1, r x ^ 2) ≤
    fourCellOddCoreLocalQuadratic r at htail
  have hmass := integral_sq_eq_two_mul_positiveHalf
    r hr.continuous (Or.inr hodd)
  have henergy : factorTwoIntrinsicEnergy r =
      2 * ∫ x : ℝ in 0..1, r x ^ 2 := by
    unfold factorTwoIntrinsicEnergy
    exact hmass
  have henergyLe : factorTwoIntrinsicEnergy r ≤
      100 * fourCellOddCoreLocalQuadratic r := by
    rw [henergy]
    linarith
  have hE0 : 0 ≤ E := by
    dsimp only [E, factorTwoIntrinsicEnergy]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun x _hx ↦ sq_nonneg _)
  have hcoef0 : 0 ≤ (fourCellOperatorHalfWidth / 10) ^ 2 * E :=
    mul_nonneg (sq_nonneg _) hE0
  have hmul := mul_le_mul_of_nonneg_left henergyLe hcoef0
  change fourCellOddSignedMassRegularBilinear
      (fourCellOddOneThreeFiveSevenNineLowProfile c d e f g) r ^ 2 ≤
    (fourCellOperatorHalfWidth / 10) ^ 2 * E *
      factorTwoIntrinsicEnergy r at hsigned
  calc
    fourCellOddSignedMassRegularBilinear
        (fourCellOddOneThreeFiveSevenNineLowProfile c d e f g) r ^ 2 ≤
      (fourCellOperatorHalfWidth / 10) ^ 2 * E *
        factorTwoIntrinsicEnergy r := hsigned
    _ ≤ (fourCellOperatorHalfWidth / 10) ^ 2 * E *
        (100 * fourCellOddCoreLocalQuadratic r) := hmul
    _ = fourCellOperatorHalfWidth ^ 2 * E *
        fourCellOddCoreLocalQuadratic r := by ring
    _ = _ := by rfl

private theorem integral_zero_three_fifths_P7_sq_le :
    (∫ x : ℝ in 0..3 / 5, factorTwoCenteredP7 x ^ 2) ≤
      (1 / 15 : ℝ) := by
  have hlower : IntervalIntegrable
      (fun x : ℝ ↦ factorTwoCenteredP7 x ^ 2) volume 0 (3 / 5) :=
    (continuous_factorTwoCenteredP7.pow 2).intervalIntegrable _ _
  have hupper : IntervalIntegrable
      (fun x : ℝ ↦ factorTwoCenteredP7 x ^ 2) volume (3 / 5) 1 :=
    (continuous_factorTwoCenteredP7.pow 2).intervalIntegrable _ _
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hlower hupper
  have hupper0 : 0 ≤
      ∫ x : ℝ in 3 / 5..1, factorTwoCenteredP7 x ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num)
      (fun x _hx ↦ sq_nonneg (factorTwoCenteredP7 x))
  rw [integral_zero_one_P7_sq] at hsplit
  linarith

private theorem fourCellOddP7GlobalTailWeight_P7_lt_one_hundredth :
    fourCellOddP7GlobalTailWeight factorTwoCenteredP7 < (1 / 100 : ℝ) := by
  have hlower := integral_zero_three_fifths_P7_sq_le
  rw [show fourCellOddP7GlobalTailWeight factorTwoCenteredP7 =
      (27 / 250 : ℝ) *
          (∫ x : ℝ in 0..3 / 5, factorTwoCenteredP7 x ^ 2) +
        (13 / 20000 : ℝ) *
          (∫ x : ℝ in 0..1, factorTwoCenteredP7 x ^ 2) by
    unfold fourCellOddP7GlobalTailWeight fourCellOddP7TailWeight
    rfl]
  rw [integral_zero_one_P7_sq]
  nlinarith

private theorem fourCellOddP7GlobalTailWeight_neg_P7_eq :
    fourCellOddP7GlobalTailWeight (fun x ↦ -factorTwoCenteredP7 x) =
      fourCellOddP7GlobalTailWeight factorTwoCenteredP7 := by
  unfold fourCellOddP7GlobalTailWeight fourCellOddP7TailWeight
  congr 2 <;>
    apply intervalIntegral.integral_congr <;>
    intro x _hx <;>
    ring

private theorem fourCellOddCoreLocalQuadratic_P5_lt_one_fourth :
    fourCellOddCoreLocalQuadratic factorTwoCenteredP5 < (1 / 4 : ℝ) := by
  have hp : fourCellOddOneThreeFiveLowProfile 0 0 1 =
      factorTwoCenteredP5 := by
    funext x
    unfold fourCellOddOneThreeFiveLowProfile
      factorTwoOddStructuralLowProfile centeredP1 centeredP3
    simp
  have hdiag :=
    fourCellOddHalfCoreReserve_add_localWidthDefect_oneThreeFive_eq 0 0 1
  rw [fourCellOddOneThreeFiveCombined_sub_regular_eq_perturbed] at hdiag
  unfold fourCellOddOneThreeFivePerturbedQuadratic at hdiag
  norm_num at hdiag
  have hupper := fourCellOddOneThreeFivePerturbed_entry_bounds
  rcases hupper with
    ⟨_h11lo, _h11hi, _h13lo, _h13hi, _h33lo, _h33hi,
      _h15lo, _h15hi, _h35lo, _h35hi, _h55lo, h55hi⟩
  rw [fourCellOddCoreLocalQuadratic, ← hp]
  linarith

/-- The genuine infinite-dimensional Schur obligation after retaining
`P₁/P₃/P₅`.  Endpoint zero is the exact affine trace condition on the
`P₇+` residual.  The square inequality is a nondegenerate weighted Riesz
dual-norm bound and contains no sampling or numerical enclosure. -/
def fourCellOddOneThreeFiveEndpointGlobalWeightedDualBound : Prop :=
  ∀ (c d e : ℝ) (v : ℝ → ℝ),
    ContDiff ℝ 1 v → Function.Odd v →
    centeredOddP1Coefficient v = 0 →
    centeredOddP3Coefficient v = 0 →
    centeredOddP5Coefficient v = 0 →
    v 1 = -(c + d + e) →
    fourCellOddCoreLocalBilinear
        (fourCellOddOneThreeFiveLowProfile c d e) v ^ 2 ≤
      fourCellOddCoreLocalQuadratic
          (fourCellOddOneThreeFiveLowProfile c d e) *
        fourCellOddP7GlobalTailWeight v

private theorem centeredOddCoefficients_neg_P7_eq_zero :
    centeredOddP1Coefficient (fun x ↦ -factorTwoCenteredP7 x) = 0 ∧
      centeredOddP3Coefficient (fun x ↦ -factorTwoCenteredP7 x) = 0 ∧
        centeredOddP5Coefficient (fun x ↦ -factorTwoCenteredP7 x) = 0 := by
  rcases centeredOddCoefficients_P7_eq_zero with ⟨h1, h3, h5⟩
  unfold centeredOddP1Coefficient at h1 ⊢
  unfold centeredOddP3Coefficient at h3 ⊢
  unfold centeredOddP5Coefficient at h5 ⊢
  have hnegOne : (∫ x : ℝ in -1..1,
      (-factorTwoCenteredP7 x) * centeredP1 x) =
      -∫ x : ℝ in -1..1, factorTwoCenteredP7 x * centeredP1 x := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro x _hx
    ring
  have hnegThree : (∫ x : ℝ in -1..1,
      (-factorTwoCenteredP7 x) * centeredP3 x) =
      -∫ x : ℝ in -1..1, factorTwoCenteredP7 x * centeredP3 x := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro x _hx
    ring
  have hnegFive : (∫ x : ℝ in -1..1,
      (-factorTwoCenteredP7 x) * factorTwoCenteredP5 x) =
      -∫ x : ℝ in -1..1,
        factorTwoCenteredP7 x * factorTwoCenteredP5 x := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro x _hx
    ring
  rw [hnegOne, hnegThree, hnegFive]
  constructor
  · nlinarith
  constructor <;> nlinarith

private theorem fourCellOddCoreLocalBilinear_P5_neg_P7 :
    fourCellOddCoreLocalBilinear factorTwoCenteredP5
        (fun x ↦ -factorTwoCenteredP7 x) =
      -fourCellOddCoreLocalBilinear factorTwoCenteredP5
        factorTwoCenteredP7 := by
  rw [fourCellOddCoreLocalBilinear_eq_retained_sub_signed,
    fourCellOddCoreLocalBilinear_eq_retained_sub_signed]
  have hretained := fourCellOddRetainedEndpointBilinear_const_mul_right
    factorTwoCenteredP5 factorTwoCenteredP7
      (by
        unfold factorTwoCenteredP5
        fun_prop)
      contDiff_factorTwoCenteredP7_local odd_factorTwoCenteredP5
      odd_factorTwoCenteredP7 (-1)
  have hsigned := fourCellOddSignedMassRegularBilinear_const_mul_right
    factorTwoCenteredP5 factorTwoCenteredP7 (-1)
  change fourCellOddRetainedEndpointBilinear factorTwoCenteredP5
      (fun x ↦ (-1 : ℝ) * factorTwoCenteredP7 x) = _ at hretained
  change fourCellOddSignedMassRegularBilinear factorTwoCenteredP5
      (fun x ↦ (-1 : ℝ) * factorTwoCenteredP7 x) = _ at hsigned
  have hfun : (fun x ↦ -factorTwoCenteredP7 x) =
      fun x ↦ (-1 : ℝ) * factorTwoCenteredP7 x := by
    funext x
    ring
  rw [hfun]
  rw [hretained, hsigned]
  ring

private theorem fourCellOddP7GlobalTailWeight_P7_pos :
    0 < fourCellOddP7GlobalTailWeight factorTwoCenteredP7 := by
  have htail := fourCellOddP7TailWeight_nonneg factorTwoCenteredP7
  unfold fourCellOddP7GlobalTailWeight
  rw [integral_zero_one_P7_sq]
  positivity

/-- The scalar global-mass Riesz proposal is false already on the adjacent
structural pair `P₅/P₇`.  This is a finite symbolic obstruction, not a
sampling calculation: the decisive potential cross is exactly `1/26`. -/
theorem not_fourCellOddOneThreeFiveEndpointGlobalWeightedDualBound :
    ¬ fourCellOddOneThreeFiveEndpointGlobalWeightedDualBound := by
  intro hdual
  let v : ℝ → ℝ := fun x ↦ -factorTwoCenteredP7 x
  have hv : ContDiff ℝ 1 v := by
    dsimp only [v]
    exact contDiff_factorTwoCenteredP7_local.neg
  have hvodd : Function.Odd v := by
    intro x
    dsimp only [v]
    rw [odd_factorTwoCenteredP7]
  rcases centeredOddCoefficients_neg_P7_eq_zero with ⟨hv1, hv3, hv5⟩
  have hvendpoint : v 1 = -(0 + 0 + (1 : ℝ)) := by
    dsimp only [v]
    rw [factorTwoCenteredP7_eq]
    norm_num
  have hschur := hdual 0 0 1 v hv hvodd hv1 hv3 hv5 hvendpoint
  have hp : fourCellOddOneThreeFiveLowProfile 0 0 1 =
      factorTwoCenteredP5 := by
    funext x
    unfold fourCellOddOneThreeFiveLowProfile
      factorTwoOddStructuralLowProfile centeredP1 centeredP3
    simp
  dsimp only [v] at hschur
  rw [hp, fourCellOddCoreLocalBilinear_P5_neg_P7,
    fourCellOddP7GlobalTailWeight_neg_P7_eq] at hschur
  have hB := two_twenty_fifths_lt_fourCellOddCoreLocalBilinear_P5_P7
  have hBsq : (4 / 625 : ℝ) <
      fourCellOddCoreLocalBilinear factorTwoCenteredP5
        factorTwoCenteredP7 ^ 2 := by
    nlinarith
  have hQ := fourCellOddCoreLocalQuadratic_P5_lt_one_fourth
  have hW := fourCellOddP7GlobalTailWeight_P7_lt_one_hundredth
  have hWpos := fourCellOddP7GlobalTailWeight_P7_pos
  have hprod :
      fourCellOddCoreLocalQuadratic factorTwoCenteredP5 *
          fourCellOddP7GlobalTailWeight factorTwoCenteredP7 <
        (1 / 400 : ℝ) := by
    calc
      _ < (1 / 4 : ℝ) *
          fourCellOddP7GlobalTailWeight factorTwoCenteredP7 :=
        mul_lt_mul_of_pos_right hQ hWpos
      _ < (1 / 4 : ℝ) * (1 / 100 : ℝ) :=
        mul_lt_mul_of_pos_left hW (by norm_num)
      _ = (1 / 400 : ℝ) := by ring
  nlinarith

/-- Correct form-level Schur obligation.  Unlike the disproved scalar
surrogate, the right-hand side retains the complete singular raw-strip,
prime, potential, scalar, and regular tail quadratic. -/
def fourCellOddOneThreeFiveEndpointFormDualBound : Prop :=
  ∀ (c d e : ℝ) (v : ℝ → ℝ),
    ContDiff ℝ 1 v → Function.Odd v →
    centeredOddP1Coefficient v = 0 →
    centeredOddP3Coefficient v = 0 →
    centeredOddP5Coefficient v = 0 →
    v 1 = -(c + d + e) →
    fourCellOddCoreLocalBilinear
        (fourCellOddOneThreeFiveLowProfile c d e) v ^ 2 ≤
      fourCellOddCoreLocalQuadratic
          (fourCellOddOneThreeFiveLowProfile c d e) *
        fourCellOddCoreLocalQuadratic v

private theorem add_two_mul_add_nonneg_of_sq_le_mul
    (a b m : ℝ) (ha : 0 ≤ a) (hm : 0 ≤ m)
    (hschur : b ^ 2 ≤ a * m) :
    0 ≤ a + 2 * b + m := by
  by_cases hb : 0 ≤ b
  · linarith
  · have hmb : 0 ≤ -2 * b := by linarith
    have ham : 0 ≤ a + m := add_nonneg ha hm
    have hsquares : (-2 * b) ^ 2 ≤ (a + m) ^ 2 := by
      nlinarith [sq_nonneg (a - m)]
    have hlinear := (sq_le_sq₀ hmb ham).mp hsquares
    linarith

/-- Exact endpoint-zero closure after the `P₁/P₃/P₅` split.  The finite
block is stated independently, and the only tail premise is the weighted
Riesz bound above.  The nondegenerate structural tail margin then performs
the Schur completion with no spectral exhaustion. -/
theorem fourCellOddCoreLocalQuadratic_nonneg_of_endpointZero_threeMode_dual
    (hfinite : ∀ c d e : ℝ,
      0 ≤ fourCellOddCoreLocalQuadratic
        (fourCellOddOneThreeFiveLowProfile c d e))
    (hdual : fourCellOddOneThreeFiveEndpointGlobalWeightedDualBound)
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w)
    (hendpoint : w (-1) = 0 ∧ w 1 = 0) :
    0 ≤ fourCellOddCoreLocalQuadratic w := by
  let c := centeredOddP1Coefficient w
  let d := centeredOddP3Coefficient w
  let e := fourCellOddP5TailCoefficient w
  let p := fourCellOddOneThreeFiveLowPart w
  let v := fourCellOddOneThreeFiveResidual w
  have hv : ContDiff ℝ 1 v := by
    dsimp only [v]
    exact contDiff_fourCellOddOneThreeFiveResidual w hw
  have hvodd : Function.Odd v := by
    dsimp only [v]
    exact odd_fourCellOddOneThreeFiveResidual w hodd
  have hvone : centeredOddP1Coefficient v = 0 := by
    dsimp only [v]
    exact centeredOddP1Coefficient_oneThreeFiveResidual_eq_zero w hw.continuous
  have hvthree : centeredOddP3Coefficient v = 0 := by
    dsimp only [v]
    exact centeredOddP3Coefficient_oneThreeFiveResidual_eq_zero w hw.continuous
  have hvfive : centeredOddP5Coefficient v = 0 := by
    dsimp only [v]
    exact centeredOddP5Coefficient_oneThreeFiveResidual_eq_zero w hw.continuous
  have hvendpoint : v 1 = -(c + d + e) := by
    dsimp only [v, c, d, e]
    exact fourCellOddOneThreeFiveResidual_one_of_endpoint_zero w hendpoint.2
  have hp : p = fourCellOddOneThreeFiveLowProfile c d e := by
    rfl
  have hlow : 0 ≤ fourCellOddCoreLocalQuadratic p := by
    rw [hp]
    exact hfinite c d e
  have hmargin : fourCellOddP7GlobalTailWeight v ≤
      fourCellOddCoreLocalQuadratic v := by
    have htail :=
      lowerTailMargin_add_globalMass_le_core_add_localWidthDefect_of_P1
        v hv hvodd hvone
    simpa only [fourCellOddP7GlobalTailWeight, fourCellOddP7TailWeight,
      fourCellOddCoreLocalQuadratic]
      using htail
  have hmargin0 : 0 ≤ fourCellOddP7GlobalTailWeight v :=
    fourCellOddP7GlobalTailWeight_nonneg v
  have hschur : fourCellOddCoreLocalBilinear p v ^ 2 ≤
      fourCellOddCoreLocalQuadratic p * fourCellOddP7GlobalTailWeight v := by
    rw [hp]
    exact hdual c d e v hv hvodd hvone hvthree hvfive hvendpoint
  have hcompleted : 0 ≤
      fourCellOddCoreLocalQuadratic p +
        2 * fourCellOddCoreLocalBilinear p v +
          fourCellOddP7GlobalTailWeight v :=
    add_two_mul_add_nonneg_of_sq_le_mul _ _ _ hlow hmargin0 hschur
  have hdecomp := fourCellOddCoreLocal_oneThreeFive_decomposition w hw.continuous
  linarith

/-- Universal endpoint-zero odd closure is now reduced to exactly one
infinite-dimensional form inequality.  The finite `P₁/P₃/P₅` block and
the complete `P₇+` diagonal are already discharged. -/
theorem fourCellOddCoreLocalQuadratic_nonneg_of_endpointZero_threeMode_formDual
    (hdual : fourCellOddOneThreeFiveEndpointFormDualBound)
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w)
    (hendpoint : w (-1) = 0 ∧ w 1 = 0) :
    0 ≤ fourCellOddCoreLocalQuadratic w := by
  let c := centeredOddP1Coefficient w
  let d := centeredOddP3Coefficient w
  let e := fourCellOddP5TailCoefficient w
  let p := fourCellOddOneThreeFiveLowPart w
  let v := fourCellOddOneThreeFiveResidual w
  have hv : ContDiff ℝ 1 v := by
    dsimp only [v]
    exact contDiff_fourCellOddOneThreeFiveResidual w hw
  have hvodd : Function.Odd v := by
    dsimp only [v]
    exact odd_fourCellOddOneThreeFiveResidual w hodd
  have hvone : centeredOddP1Coefficient v = 0 := by
    dsimp only [v]
    exact centeredOddP1Coefficient_oneThreeFiveResidual_eq_zero w hw.continuous
  have hvthree : centeredOddP3Coefficient v = 0 := by
    dsimp only [v]
    exact centeredOddP3Coefficient_oneThreeFiveResidual_eq_zero w hw.continuous
  have hvfive : centeredOddP5Coefficient v = 0 := by
    dsimp only [v]
    exact centeredOddP5Coefficient_oneThreeFiveResidual_eq_zero w hw.continuous
  have hvendpoint : v 1 = -(c + d + e) := by
    dsimp only [v, c, d, e]
    exact fourCellOddOneThreeFiveResidual_one_of_endpoint_zero w hendpoint.2
  have hp : p = fourCellOddOneThreeFiveLowProfile c d e := by
    rfl
  have hlow : 0 ≤ fourCellOddCoreLocalQuadratic p := by
    rw [hp]
    simpa only [fourCellOddCoreLocalQuadratic] using
      fourCellOddHalfCoreReserve_add_localWidthDefect_oneThreeFive_nonneg
        c d e
  have htailMargin :=
    one_fiftieth_positiveHalfMass_le_core_add_localWidthDefect_of_P1
      v hv hvodd hvone
  have hhalf : 0 ≤ ∫ x : ℝ in 0..1, v x ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num)
      (fun x _hx ↦ sq_nonneg (v x))
  have htail : 0 ≤ fourCellOddCoreLocalQuadratic v := by
    change (1 / 50 : ℝ) * (∫ x : ℝ in 0..1, v x ^ 2) ≤
      fourCellOddCoreLocalQuadratic v at htailMargin
    nlinarith
  have hschur : fourCellOddCoreLocalBilinear p v ^ 2 ≤
      fourCellOddCoreLocalQuadratic p * fourCellOddCoreLocalQuadratic v := by
    rw [hp]
    exact hdual c d e v hv hvodd hvone hvthree hvfive hvendpoint
  have hcompleted : 0 ≤
      fourCellOddCoreLocalQuadratic p +
        2 * fourCellOddCoreLocalBilinear p v +
          fourCellOddCoreLocalQuadratic v :=
    add_two_mul_add_nonneg_of_sq_le_mul _ _ _ hlow htail hschur
  have hdecomp := fourCellOddCoreLocal_oneThreeFive_decomposition w hw.continuous
  linarith

/-! The low block of the retained octic core model. -/

def fourCellOddOcticLowCombined11 : ℝ :=
  rawLowQ11 + fourCellOddLowLocalAlgebraic11

def fourCellOddOcticLowCombined13 : ℝ :=
  rawLowQ13 + fourCellOddLowLocalAlgebraic13

def fourCellOddOcticLowCombined33 : ℝ :=
  rawLowQ33 + fourCellOddLowLocalAlgebraic33

private theorem thirty_nine_two_fiftieths_le_fourCellOddOcticLowCombined11 :
    (39 / 250 : ℝ) ≤ fourCellOddOcticLowCombined11 := by
  have hscalar := fourCellScalar_lt_31577_div_20000
  have hp := sqrt_two_mul_log_two_bounds.1
  have hl := strict_log_two_bounds.1
  rw [show fourCellOddOcticLowCombined11 =
      386959 / 415800 + (7 / 150 : ℝ) * Real.log 2 +
        (94 / 375 : ℝ) * (Real.sqrt 2 * Real.log 2) -
          (2 / 3 : ℝ) *
            (Real.log (2 * fourCellOperatorHalfWidth) +
              Real.eulerMascheroniConstant + Real.log Real.pi) by
    unfold fourCellOddOcticLowCombined11
      fourCellOddLowLocalAlgebraic11 rawLowQ11
    ring]
  nlinarith

private theorem fourCellOddOcticLowCombined13_nonneg :
    0 ≤ fourCellOddOcticLowCombined13 := by
  rw [show fourCellOddOcticLowCombined13 =
      709 / 6500 + (104 / 3125 : ℝ) *
        (Real.sqrt 2 * Real.log 2) by
    unfold fourCellOddOcticLowCombined13
      fourCellOddLowLocalAlgebraic13 rawLowQ13
    ring]
  positivity

private theorem fourCellOddOcticLowCombined13_le_seventy_one_five_hundredths :
    fourCellOddOcticLowCombined13 ≤ (71 / 500 : ℝ) := by
  have hp := sqrt_two_mul_log_two_bounds.2
  rw [show fourCellOddOcticLowCombined13 =
      709 / 6500 + (104 / 3125 : ℝ) *
        (Real.sqrt 2 * Real.log 2) by
    unfold fourCellOddOcticLowCombined13
      fourCellOddLowLocalAlgebraic13 rawLowQ13
    ring]
  nlinarith

private theorem sixty_nine_five_hundredths_le_fourCellOddOcticLowCombined33 :
    (69 / 500 : ℝ) ≤ fourCellOddOcticLowCombined33 := by
  have hscalar := fourCellScalar_lt_31577_div_20000
  have hp := sqrt_two_mul_log_two_bounds.2
  have hl := strict_log_two_bounds.1
  rw [show fourCellOddOcticLowCombined33 =
      701216011 / 1126125000 - (5242 / 109375 : ℝ) *
          (Real.sqrt 2 * Real.log 2) +
        (1 / 50 : ℝ) * Real.log 2 -
          (2 / 7 : ℝ) *
            (Real.log (2 * fourCellOperatorHalfWidth) +
              Real.eulerMascheroniConstant + Real.log Real.pi) by
    unfold fourCellOddOcticLowCombined33
      fourCellOddLowLocalAlgebraic33 rawLowQ33
    ring]
  nlinarith

/-- The low block of the uncompleted octic core already absorbs the full
wide regular budget.  This leaves the entire `53 / 60` tail reserve available
for genuine low--tail and tail--tail terms. -/
theorem fourCellOddLowRegularBudget_le_octicCombined (c d : ℝ) :
    (13 / 2500 : ℝ) * c ^ 2 +
        (91 / 50000 : ℝ) * |c * d| +
          (61 / 100000 : ℝ) * d ^ 2 ≤
      fourCellOddOcticLowCombined11 * c ^ 2 +
        2 * fourCellOddOcticLowCombined13 * c * d +
          fourCellOddOcticLowCombined33 * d ^ 2 := by
  let A : ℝ := fourCellOddOcticLowCombined11
  let B : ℝ := fourCellOddOcticLowCombined13
  let D : ℝ := fourCellOddOcticLowCombined33
  have hA : (39 / 250 : ℝ) ≤ A := by
    simpa only [A] using
      thirty_nine_two_fiftieths_le_fourCellOddOcticLowCombined11
  have hB0 : 0 ≤ B := by
    simpa only [B] using fourCellOddOcticLowCombined13_nonneg
  have hB1 : B ≤ (71 / 500 : ℝ) := by
    simpa only [B] using
      fourCellOddOcticLowCombined13_le_seventy_one_five_hundredths
  have hD : (69 / 500 : ℝ) ≤ D := by
    simpa only [D] using
      sixty_nine_five_hundredths_le_fourCellOddOcticLowCombined33
  have hBabs : |B| ≤ (71 / 500 : ℝ) := by
    apply abs_le.mpr
    constructor <;> linarith
  have hAcross : |2 * B * c * d| ≤ (71 / 250 : ℝ) * |c * d| := by
    calc
      |2 * B * c * d| = 2 * |B| * |c * d| := by
        rw [show 2 * B * c * d = 2 * B * (c * d) by ring,
          abs_mul, abs_mul]
        norm_num
      _ ≤ 2 * (71 / 500 : ℝ) * |c * d| := by gcongr
      _ = (71 / 250 : ℝ) * |c * d| := by ring
  have hcross : -(71 / 250 : ℝ) * |c * d| ≤ 2 * B * c * d := by
    have h := (abs_le.mp hAcross).1
    linarith
  have hAmul : (39 / 250 : ℝ) * c ^ 2 ≤ A * c ^ 2 :=
    mul_le_mul_of_nonneg_right hA (sq_nonneg c)
  have hDmul : (69 / 500 : ℝ) * d ^ 2 ≤ D * d ^ 2 :=
    mul_le_mul_of_nonneg_right hD (sq_nonneg d)
  let A₀ : ℝ := 39 / 250 - 13 / 2500
  let D₀ : ℝ := 69 / 500 - 61 / 100000
  let K₀ : ℝ := 14291 / 50000
  have hreduce :
      A₀ * c ^ 2 + D₀ * d ^ 2 - K₀ * |c * d| ≤
        A * c ^ 2 + 2 * B * c * d + D * d ^ 2 -
          ((13 / 2500 : ℝ) * c ^ 2 +
            (91 / 50000 : ℝ) * |c * d| +
              (61 / 100000 : ℝ) * d ^ 2) := by
    dsimp only [A₀, D₀, K₀]
    linarith
  have hsquare : 0 ≤ (21 * |c| - 20 * |d|) ^ 2 := sq_nonneg _
  have hyoung :
      2 * |c * d| ≤ (21 / 20 : ℝ) * c ^ 2 +
        (20 / 21 : ℝ) * d ^ 2 := by
    rw [abs_mul]
    have hc : |c| ^ 2 = c ^ 2 := sq_abs c
    have hd : |d| ^ 2 = d ^ 2 := sq_abs d
    nlinarith
  have hweighted := mul_le_mul_of_nonneg_left hyoung
    (by norm_num : (0 : ℝ) ≤ 14291 / 100000)
  have hcCoeff :
      (14291 / 100000 : ℝ) * (21 / 20) ≤ A₀ := by
    norm_num [A₀]
  have hdCoeff :
      (14291 / 100000 : ℝ) * (20 / 21) ≤ D₀ := by
    norm_num [D₀]
  have hcMul := mul_le_mul_of_nonneg_right hcCoeff (sq_nonneg c)
  have hdMul := mul_le_mul_of_nonneg_right hdCoeff (sq_nonneg d)
  have hpositive : 0 ≤
      A₀ * c ^ 2 + D₀ * d ^ 2 - K₀ * |c * d| := by
    dsimp only [K₀] at hweighted ⊢
    linarith
  have hfinal := hpositive.trans hreduce
  dsimp only [A, B, D] at hfinal
  linarith

/-- The endpoint-strip parity split cancels every nonlocal raw term outside
the strip from the core defect. -/
theorem fourCellOddStripCorrelationCoreDefect_eq_localWidthDefect
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) :
    fourCellOddStripCorrelationCoreDefect w =
      fourCellOddStripLocalWidthDefect w := by
  have hstrip := fourCellOddEndpointStrip_rawEnergy_eq_even_add_odd w hw
  unfold fourCellOddStripCorrelationCoreDefect
    fourCellOddStripLocalWidthDefect
    fourCellOddStripRetainedPrimeRawCapacity
  rw [hstrip]
  ring

/-- Exact conversion from the completed regular squares/row to the signed
autocorrelation row, valid on the odd form domain. -/
theorem fourCellOddStripCoreDefect_eq_correlation
    (w : ℝ → ℝ) (hw : Continuous w) (hodd : Function.Odd w) :
    fourCellOddStripCoreDefect w =
      fourCellOddStripCorrelationCoreDefect w := by
  have ha0 : 0 ≤ fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  have ha3 : fourCellOperatorHalfWidth ≤ Real.log 3 / 2 := by
    have h := five_mul_log_two_div_four_lt_log_three
    unfold fourCellOperatorHalfWidth
    linarith
  have hregular :=
    neg_two_mul_regularCorrelation_eq_positiveHalfCompletion_odd
      w hw hodd fourCellOperatorHalfWidth ha0 ha3
  unfold fourCellOddStripCoreDefect
    fourCellOddStripCorrelationCoreDefect
  linarith

/-- Exact decomposition of the outstanding base inequality into the known
nonnegative odd core and one genuinely coupled four-cell defect. -/
theorem fourCellOddStripCapacityBase_sub_blended_eq_core_add_defect
    (w : ℝ → ℝ) :
    fourCellOddStripCapacityBase w -
        fourCellOddStripBlendedAllocation w =
      fourCellOddHalfCoreReserve w + fourCellOddStripCoreDefect w := by
  unfold fourCellOddStripCapacityBase
    fourCellOddStripBlendedAllocation fourCellOddHalfCoreReserve
    fourCellOddStripCoreDefect fourCellOddStripRetainedPrimeRawCapacity
  ring

/-- On odd profiles the outstanding base difference is the nonnegative
centered core plus the exact prime/width autocorrelation defect. -/
theorem fourCellOddStripCapacityBase_sub_blended_eq_core_add_correlationDefect
    (w : ℝ → ℝ) (hw : Continuous w) (hodd : Function.Odd w) :
    fourCellOddStripCapacityBase w -
        fourCellOddStripBlendedAllocation w =
      fourCellOddHalfCoreReserve w +
        fourCellOddStripCorrelationCoreDefect w := by
  rw [fourCellOddStripCapacityBase_sub_blended_eq_core_add_defect,
    fourCellOddStripCoreDefect_eq_correlation w hw hodd]

/-- Fully reduced structural form of the remaining odd base inequality. -/
theorem fourCellOddStripCapacityBase_sub_blended_eq_core_add_localWidthDefect
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w) :
    fourCellOddStripCapacityBase w -
        fourCellOddStripBlendedAllocation w =
      fourCellOddHalfCoreReserve w +
        fourCellOddStripLocalWidthDefect w := by
  rw [fourCellOddStripCapacityBase_sub_blended_eq_core_add_correlationDefect
      w hw.continuous hodd,
    fourCellOddStripCorrelationCoreDefect_eq_localWidthDefect w hw]

/-- The exact remaining odd base theorem is a coupled defect absorption:
the sharp centered reserve must dominate the negative part of the four-cell
width/prime defect. -/
theorem fourCellOddStripCapacityBase_ge_blended_of_core_defect
    (w : ℝ → ℝ)
    (hdefect : -fourCellOddStripCoreDefect w ≤
      fourCellOddHalfCoreReserve w) :
    fourCellOddStripBlendedAllocation w ≤
      fourCellOddStripCapacityBase w := by
  rw [← sub_nonneg]
  rw [fourCellOddStripCapacityBase_sub_blended_eq_core_add_defect]
  linarith

/-- Pointwise multiplication weight behind the blended allocation. -/
def fourCellOddStripSchurWeight (x : ℝ) : ℝ :=
  (3 / 200 : ℝ) + (7 / 50 : ℝ) * yoshidaEndpointPotential x

/-- A low-degree rational majorant for the dual Schur density. -/
def fourCellOddStripSchurPolynomial (x : ℝ) : ℝ :=
  (1 / 10 : ℝ) * x + (10 / 3 : ℝ) * x ^ 2 -
    (11 / 2 : ℝ) * x ^ 3 + (249 / 100 : ℝ) * x ^ 4

private def fourCellOddStripSchurQuarticDenominator (x : ℝ) : ℝ :=
  (3 / 200 : ℝ) + (7 / 100 : ℝ) * x ^ 2 +
    (7 / 200 : ℝ) * x ^ 4

private def fourCellOddStripSchurProductGapQuotient (x : ℝ) : ℝ :=
  (167328 * x ^ 7 - 369600 * x ^ 6 + 558656 * x ^ 5 -
      732480 * x ^ 4 + 519712 * x ^ 3 - 144960 * x ^ 2 +
      4125 * x + 2880) / 1920000

private theorem fourCellOddStripSchurProductGapQuotient_nonneg
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ fourCellOddStripSchurProductGapQuotient x := by
  rcases le_total x (1 / 3 : ℝ) with hx | hx
  · let t : ℝ := 3 * x
    have ht0 : 0 ≤ t := by dsimp only [t]; positivity
    have ht1 : t ≤ 1 := by dsimp only [t]; linarith
    have htcomp : 0 ≤ 1 - t := by linarith
    have hbern : fourCellOddStripSchurProductGapQuotient x =
        (3 / 2000 : ℝ) * (1 - t) ^ 7 +
        (4307 / 384000 : ℝ) * t * (1 - t) ^ 6 +
        (15787 / 576000 : ℝ) * t ^ 2 * (1 - t) ^ 5 +
        (1623787 / 51840000 : ℝ) * t ^ 3 * (1 - t) ^ 4 +
        (237497 / 12960000 : ℝ) * t ^ 4 * (1 - t) ^ 3 +
        (2600099 / 466560000 : ℝ) * t ^ 5 * (1 - t) ^ 2 +
        (222727 / 233280000 : ℝ) * t ^ 6 * (1 - t) +
        (54061 / 466560000 : ℝ) * t ^ 7 := by
      unfold fourCellOddStripSchurProductGapQuotient
      dsimp only [t]
      ring
    rw [hbern]
    positivity
  · rcases le_total x (2 / 3 : ℝ) with hx' | hx'
    · let t : ℝ := 3 * x - 1
      have ht0 : 0 ≤ t := by dsimp only [t]; linarith
      have ht1 : t ≤ 1 := by dsimp only [t]; linarith
      have htcomp : 0 ≤ 1 - t := by linarith
      have hbern : fourCellOddStripSchurProductGapQuotient x =
          (54061 / 466560000 : ℝ) * (1 - t) ^ 7 +
          (173 / 259200 : ℝ) * t * (1 - t) ^ 6 +
          (71831 / 18662400 : ℝ) * t ^ 2 * (1 - t) ^ 5 +
          (976823 / 77760000 : ℝ) * t ^ 3 * (1 - t) ^ 4 +
          (9220427 / 466560000 : ℝ) * t ^ 4 * (1 - t) ^ 3 +
          (1781893 / 116640000 : ℝ) * t ^ 5 * (1 - t) ^ 2 +
          (2555657 / 466560000 : ℝ) * t ^ 6 * (1 - t) +
          (172301 / 233280000 : ℝ) * t ^ 7 := by
        unfold fourCellOddStripSchurProductGapQuotient
        dsimp only [t]
        ring
      rw [hbern]
      positivity
    · let t : ℝ := 3 * x - 2
      have ht0 : 0 ≤ t := by dsimp only [t]; linarith
      have ht1 : t ≤ 1 := by dsimp only [t]; linarith
      have htcomp : 0 ≤ 1 - t := by linarith
      have hbern : fourCellOddStripSchurProductGapQuotient x =
          (172301 / 233280000 : ℝ) * (1 - t) ^ 7 +
          (756257 / 155520000 : ℝ) * t * (1 - t) ^ 6 +
          (337891 / 29160000 : ℝ) * t ^ 2 * (1 - t) ^ 5 +
          (1734811 / 155520000 : ℝ) * t ^ 3 * (1 - t) ^ 4 +
          (23563 / 8640000 : ℝ) * t ^ 4 * (1 - t) ^ 3 +
          (18527 / 17280000 : ℝ) * t ^ 5 * (1 - t) ^ 2 +
          (7121 / 1440000 : ℝ) * t ^ 6 * (1 - t) +
          (1887 / 640000 : ℝ) * t ^ 7 := by
        unfold fourCellOddStripSchurProductGapQuotient
        dsimp only [t]
        ring
      rw [hbern]
      positivity

private theorem fourCellOddStripSchur_productGap_nonneg
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ fourCellOddStripSchurPolynomial x *
        fourCellOddStripSchurQuarticDenominator x -
      (49 / 1024 : ℝ) * x ^ 2 := by
  have hq := fourCellOddStripSchurProductGapQuotient_nonneg hx0 hx1
  have hid : fourCellOddStripSchurPolynomial x *
        fourCellOddStripSchurQuarticDenominator x -
      (49 / 1024 : ℝ) * x ^ 2 =
        x * fourCellOddStripSchurProductGapQuotient x := by
    unfold fourCellOddStripSchurPolynomial
      fourCellOddStripSchurQuarticDenominator
      fourCellOddStripSchurProductGapQuotient
    ring
  rw [hid]
  exact mul_nonneg hx0 hq

private theorem fourCellOddStripSchurQuarticDenominator_pos
    (x : ℝ) : 0 < fourCellOddStripSchurQuarticDenominator x := by
  unfold fourCellOddStripSchurQuarticDenominator
  positivity

/-- The rational density forced by the Taylor and quartic envelopes is
bounded pointwise by the explicit Schur polynomial. -/
theorem fourCellOddStripSchur_rationalDensity_le_polynomial
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (49 / 1024 : ℝ) * x ^ 2 /
        fourCellOddStripSchurQuarticDenominator x ≤
      fourCellOddStripSchurPolynomial x := by
  rw [div_le_iff₀ (fourCellOddStripSchurQuarticDenominator_pos x)]
  have hgap := fourCellOddStripSchur_productGap_nonneg hx0 hx1
  linarith

theorem integral_fourCellOddStripSchurPolynomial :
    (∫ x : ℝ in 0..1, fourCellOddStripSchurPolynomial x) =
      2557 / 9000 := by
  unfold fourCellOddStripSchurPolynomial
  have h1 : IntervalIntegrable (fun x : ℝ ↦ (1 / 10 : ℝ) * x)
      volume 0 1 :=
    (by fun_prop : Continuous (fun x : ℝ ↦ (1 / 10 : ℝ) * x))
      |>.intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun x : ℝ ↦ (10 / 3 : ℝ) * x ^ 2)
      volume 0 1 :=
    (by fun_prop : Continuous (fun x : ℝ ↦ (10 / 3 : ℝ) * x ^ 2))
      |>.intervalIntegrable _ _
  have h3 : IntervalIntegrable (fun x : ℝ ↦ (11 / 2 : ℝ) * x ^ 3)
      volume 0 1 :=
    (by fun_prop : Continuous (fun x : ℝ ↦ (11 / 2 : ℝ) * x ^ 3))
      |>.intervalIntegrable _ _
  have h4 : IntervalIntegrable (fun x : ℝ ↦ (249 / 100 : ℝ) * x ^ 4)
      volume 0 1 :=
    (by fun_prop : Continuous (fun x : ℝ ↦ (249 / 100 : ℝ) * x ^ 4))
      |>.intervalIntegrable _ _
  have hi1 : (∫ x : ℝ in 0..1, (1 / 10 : ℝ) * x) = 1 / 20 := by
    rw [show (fun x : ℝ ↦ (1 / 10 : ℝ) * x) =
        fun x ↦ (1 / 10 : ℝ) * x ^ 1 by
      funext x
      ring,
      intervalIntegral.integral_const_mul, integral_pow]
    norm_num
  rw [intervalIntegral.integral_add ((h1.add h2).sub h3) h4,
    intervalIntegral.integral_sub (h1.add h2) h3,
    intervalIntegral.integral_add h1 h2]
  simp only [intervalIntegral.integral_const_mul, integral_pow]
  rw [hi1]
  norm_num

theorem integral_fourCellOddStripSchurPolynomial_lt_two_sevenths :
    (∫ x : ℝ in 0..1, fourCellOddStripSchurPolynomial x) <
      (2 / 7 : ℝ) := by
  rw [integral_fourCellOddStripSchurPolynomial]
  norm_num

private theorem fourCellOddStripSchurQuarticDenominator_le_weight
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    fourCellOddStripSchurQuarticDenominator x ≤
      fourCellOddStripSchurWeight x := by
  have hquartic := quartic_le_endpointPotential
    (show |x| < 1 by
      rw [abs_lt]
      constructor <;> linarith [hx.1, hx.2])
  unfold fourCellOddStripSchurQuarticDenominator
    fourCellOddStripSchurWeight yoshidaEndpointQuartic at *
  nlinarith

private theorem fourCellOddStripSchurWeight_pos_of_mem_Ioo
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    0 < fourCellOddStripSchurWeight x := by
  exact (fourCellOddStripSchurQuarticDenominator_pos x).trans_le
    (fourCellOddStripSchurQuarticDenominator_le_weight hx)

/-- The integral of the pointwise Schur weight against a profile square is
exactly the blended allocation. -/
theorem integral_fourCellOddStripSchurWeight_mul_sq
    (w : ℝ → ℝ) (hw : Continuous w) :
    (∫ x : ℝ in 0..1, fourCellOddStripSchurWeight x * w x ^ 2) =
      fourCellOddStripBlendedAllocation w := by
  have hmass : IntervalIntegrable (fun x : ℝ ↦ w x ^ 2) volume 0 1 :=
    (hw.pow 2).intervalIntegrable _ _
  have hpotentialFull := intervalIntegrable_endpointPotential_mul_sq w hw
  have hpotential : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * w x ^ 2)
      volume 0 1 := hpotentialFull.mono_set (by
    intro x hx
    norm_num at hx ⊢
    constructor <;> linarith : uIcc (0 : ℝ) 1 ⊆ uIcc (-1 : ℝ) 1)
  rw [show (fun x : ℝ ↦ fourCellOddStripSchurWeight x * w x ^ 2) =
      fun x ↦ (3 / 200 : ℝ) * (w x ^ 2) +
        (7 / 50 : ℝ) *
          (yoshidaEndpointPotential x * w x ^ 2) by
    funext x
    unfold fourCellOddStripSchurWeight
    ring]
  rw [intervalIntegral.integral_add
      (hmass.const_mul (3 / 200)) (hpotential.const_mul (7 / 50)),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  rfl

/-- Exact two-obligation Schur closure.  This is stronger than merely
replacing the rank by a multiple of the potential: the scalar and potential
pieces must remain coupled in both hypotheses. -/
theorem fourCellOddStripCapacityLowerOperator_nonneg_of_blendedSchur
    (w : ℝ → ℝ)
    (hbase : fourCellOddStripBlendedAllocation w ≤
      fourCellOddStripCapacityBase w)
    (hrank : 8 * fourCellOperatorHalfWidth *
        fourCellPositiveSinhMoment w
          (fourCellOperatorHalfWidth / 2) ^ 2 ≤
      fourCellOddStripBlendedAllocation w) :
    0 ≤ fourCellOddStripCapacityLowerOperator w := by
  rw [fourCellOddStripCapacityLowerOperator_eq_base_sub_rank]
  linarith

private theorem sinh_le_mul_exp_self {z : ℝ} :
    Real.sinh z ≤ z * Real.exp z := by
  have hbase := Real.add_one_le_exp (-2 * z)
  have hmul := mul_le_mul_of_nonneg_left hbase (Real.exp_pos z).le
  have hprod : Real.exp z * (1 - 2 * z) ≤ Real.exp (-z) := by
    calc
      Real.exp z * (1 - 2 * z) = Real.exp z * (-2 * z + 1) := by ring
      _ ≤ Real.exp z * Real.exp (-2 * z) := hmul
      _ = Real.exp (-z) := by
        rw [← Real.exp_add]
        congr 1
        ring
  rw [Real.sinh_eq]
  nlinarith [Real.exp_pos z]

private theorem fourCellOperatorHalfWidth_lt_seven_sixteenths :
    fourCellOperatorHalfWidth < (7 / 16 : ℝ) := by
  have hlog := strict_log_two_bounds.2
  unfold fourCellOperatorHalfWidth
  norm_num at hlog ⊢
  linarith

/-- Rational pointwise envelope for the production odd representer. -/
theorem fourCell_sinh_weight_le_seven_twenty_fifths
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.sinh (fourCellOperatorHalfWidth * x / 2) ≤ (7 / 25 : ℝ) * x := by
  let z := fourCellOperatorHalfWidth * x / 2
  have ha0 : 0 ≤ fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  have hz0 : 0 ≤ z := by
    dsimp only [z]
    positivity
  have hz : z ≤ (7 / 32 : ℝ) := by
    dsimp only [z]
    nlinarith [fourCellOperatorHalfWidth_lt_seven_sixteenths]
  have hzOne : z < 1 := lt_of_le_of_lt hz (by norm_num)
  have hexp := Real.exp_bound_div_one_sub_of_interval hz0 hzOne
  have hden : 1 / (1 - z) ≤ (32 / 25 : ℝ) := by
    rw [div_le_iff₀ (by linarith : 0 < 1 - z)]
    nlinarith
  have hexpBound : Real.exp z ≤ (32 / 25 : ℝ) := hexp.trans hden
  have hsinh := sinh_le_mul_exp_self (z := z)
  have hzLinear : z ≤ (7 / 32 : ℝ) * x := by
    dsimp only [z]
    nlinarith [fourCellOperatorHalfWidth_lt_seven_sixteenths]
  calc
    Real.sinh z ≤ z * Real.exp z := hsinh
    _ ≤ z * (32 / 25 : ℝ) :=
      mul_le_mul_of_nonneg_left hexpBound hz0
    _ ≤ ((7 / 32 : ℝ) * x) * (32 / 25 : ℝ) :=
      mul_le_mul_of_nonneg_right hzLinear (by norm_num)
    _ = (7 / 25 : ℝ) * x := by ring

/-- Taylor-sharp linear envelope needed by the blended mass--potential
Schur weight.  Unlike the potential-only estimate, its constant is within
one percent of the exact production slope. -/
theorem fourCell_sinh_weight_le_seven_thirty_seconds
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.sinh (fourCellOperatorHalfWidth * x / 2) ≤ (7 / 32 : ℝ) * x := by
  let lambda : ℝ := fourCellOperatorHalfWidth / 2
  let c : ℝ := 1733 / 8000
  let z : ℝ := lambda * x
  have hlog := strict_log_two_bounds.2
  have hlambda : 0 ≤ lambda := by
    dsimp only [lambda]
    unfold fourCellOperatorHalfWidth
    positivity
  have hlambda_lt : lambda < c := by
    dsimp only [lambda, c]
    unfold fourCellOperatorHalfWidth
    norm_num at hlog ⊢
    linarith
  have hc0 : 0 ≤ c := by norm_num [c]
  have hz0 : 0 ≤ z := by
    dsimp only [z]
    positivity
  have hzLinear : z ≤ c * x := by
    dsimp only [z]
    exact mul_le_mul_of_nonneg_right hlambda_lt.le hx0
  have hcx : c * x ≤ c := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hx1 hc0
  have hzc : z ≤ c := hzLinear.trans hcx
  have hzone : z < 1 := hzc.trans_lt (by norm_num [c])
  have hexp := Real.exp_bound_div_one_sub_of_interval hz0 hzone
  have hden : 1 / (1 - z) ≤ (32 / 25 : ℝ) := by
    rw [div_le_iff₀ (by linarith : 0 < 1 - z)]
    dsimp only [c] at hzc
    norm_num at hzc ⊢
    linarith
  have hexpBound : Real.exp z ≤ (32 / 25 : ℝ) := hexp.trans hden
  have hcoshExp : Real.cosh z ≤ Real.exp z := by
    rw [Real.cosh_eq]
    have hneg : Real.exp (-z) ≤ Real.exp z := by
      rw [Real.exp_le_exp]
      linarith
    linarith
  have hcosh : Real.cosh z ≤ (32 / 25 : ℝ) := hcoshExp.trans hexpBound
  have htaylor := abs_sinh_sub_cubic_le z
  have htaylorUpper :
      Real.sinh z ≤ z + z ^ 3 / 6 + Real.cosh z * z ^ 5 / 120 := by
    have hle := (le_abs_self (Real.sinh z - z - z ^ 3 / 6)).trans htaylor
    have hle' : Real.sinh z - z - z ^ 3 / 6 ≤
        Real.cosh z * z ^ 5 / 120 := by
      simpa [abs_of_nonneg hz0] using hle
    linarith
  have hzsq : z ^ 2 ≤ c ^ 2 :=
    (sq_le_sq₀ hz0 hc0).2 hzc
  have hzfour : z ^ 4 ≤ c ^ 4 := by
    nlinarith [sq_nonneg (z ^ 2), sq_nonneg (c ^ 2)]
  have hzthree : z ^ 3 ≤ c ^ 2 * z := by
    nlinarith
  have hzfive : z ^ 5 ≤ c ^ 4 * z := by
    nlinarith
  have hzfactor :
      Real.sinh z ≤ z *
        (1 + c ^ 2 / 6 + (32 / 25 : ℝ) * c ^ 4 / 120) := by
    calc
      Real.sinh z ≤ z + z ^ 3 / 6 + Real.cosh z * z ^ 5 / 120 :=
        htaylorUpper
      _ ≤ z + (c ^ 2 * z) / 6 + (32 / 25 : ℝ) *
          (c ^ 4 * z) / 120 := by
        gcongr
      _ = z *
          (1 + c ^ 2 / 6 + (32 / 25 : ℝ) * c ^ 4 / 120) := by ring
  have hfactor0 : 0 ≤
      1 + c ^ 2 / 6 + (32 / 25 : ℝ) * c ^ 4 / 120 := by positivity
  have hrat : c *
      (1 + c ^ 2 / 6 + (32 / 25 : ℝ) * c ^ 4 / 120) <
        (7 / 32 : ℝ) := by
    norm_num [c]
  rw [show fourCellOperatorHalfWidth * x / 2 = z by
    dsimp only [z, lambda]
    ring]
  calc
    Real.sinh z ≤ z *
        (1 + c ^ 2 / 6 + (32 / 25 : ℝ) * c ^ 4 / 120) := hzfactor
    _ ≤ (c * x) *
        (1 + c ^ 2 / 6 + (32 / 25 : ℝ) * c ^ 4 / 120) :=
      mul_le_mul_of_nonneg_right hzLinear hfactor0
    _ ≤ (7 / 32 : ℝ) * x := by
      nlinarith

/-- Pointwise dual-density domination for the blended Schur weight. -/
theorem fourCellOddStripSchur_sinhDensity_le_polynomial
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    Real.sinh (fourCellOperatorHalfWidth * x / 2) ^ 2 /
        fourCellOddStripSchurWeight x ≤
      fourCellOddStripSchurPolynomial x := by
  have hsinh0 : 0 ≤ Real.sinh (fourCellOperatorHalfWidth * x / 2) := by
    rw [Real.sinh_nonneg_iff]
    have ha0 : 0 ≤ fourCellOperatorHalfWidth := by
      unfold fourCellOperatorHalfWidth
      positivity
    exact div_nonneg (mul_nonneg ha0 hx.1.le) (by norm_num)
  have hsinh := fourCell_sinh_weight_le_seven_thirty_seconds
    hx.1.le hx.2.le
  have hsinhSq :
      Real.sinh (fourCellOperatorHalfWidth * x / 2) ^ 2 ≤
        (49 / 1024 : ℝ) * x ^ 2 := by
    have hsquare :=
      (sq_le_sq₀ hsinh0 (mul_nonneg (by norm_num) hx.1.le)).2 hsinh
    nlinarith
  have hden := fourCellOddStripSchurQuarticDenominator_le_weight hx
  have hden0 := fourCellOddStripSchurQuarticDenominator_pos x
  have hweight0 := fourCellOddStripSchurWeight_pos_of_mem_Ioo hx
  calc
    Real.sinh (fourCellOperatorHalfWidth * x / 2) ^ 2 /
        fourCellOddStripSchurWeight x ≤
      ((49 / 1024 : ℝ) * x ^ 2) /
        fourCellOddStripSchurWeight x :=
      div_le_div_of_nonneg_right hsinhSq hweight0.le
    _ ≤ ((49 / 1024 : ℝ) * x ^ 2) /
        fourCellOddStripSchurQuarticDenominator x := by
      exact div_le_div_of_nonneg_left (by positivity) hden0 hden
    _ ≤ fourCellOddStripSchurPolynomial x :=
      fourCellOddStripSchur_rationalDensity_le_polynomial hx.1.le hx.2.le

/-- The exact dual norm of the sinh representer in the blended weight is
strictly smaller than `2 / 7`. -/
theorem integral_fourCellOddStripSchur_sinhDensity_lt_two_sevenths :
    (∫ x : ℝ in 0..1,
      Real.sinh (fourCellOperatorHalfWidth * x / 2) ^ 2 /
        fourCellOddStripSchurWeight x) < (2 / 7 : ℝ) := by
  let F : ℝ → ℝ := fun x ↦
    Real.sinh (fourCellOperatorHalfWidth * x / 2) ^ 2 /
      fourCellOddStripSchurWeight x
  let P : ℝ → ℝ := fourCellOddStripSchurPolynomial
  have hPint : IntervalIntegrable P volume 0 1 := by
    exact (by
      dsimp only [P]
      unfold fourCellOddStripSchurPolynomial
      fun_prop : Continuous P) |>.intervalIntegrable _ _
  have hFmeas : AEStronglyMeasurable F
      (volume.restrict (Ioc (0 : ℝ) 1)) := by
    apply Measurable.aestronglyMeasurable
    dsimp only [F]
    unfold fourCellOddStripSchurWeight yoshidaEndpointPotential
    fun_prop
  have hPset : IntegrableOn P (Ioc (0 : ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).1 hPint
  have hFset : IntegrableOn F (Ioc (0 : ℝ) 1) := by
    apply hPset.mono' hFmeas
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
        MeasureTheory.Measure.ae_ne
          (volume.restrict (Ioc (0 : ℝ) 1)) (1 : ℝ)] with x hx hx1
    have hxoo : x ∈ Ioo (0 : ℝ) 1 := ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩
    have hle := fourCellOddStripSchur_sinhDensity_le_polynomial hxoo
    have hF0 : 0 ≤ F x := by
      dsimp only [F]
      exact div_nonneg (sq_nonneg _)
        (fourCellOddStripSchurWeight_pos_of_mem_Ioo hxoo).le
    rw [Real.norm_eq_abs, abs_of_nonneg hF0]
    simpa only [F, P] using hle
  have hFint : IntervalIntegrable F volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).2 hFset
  have hmono : (∫ x : ℝ in 0..1, F x) ≤ ∫ x : ℝ in 0..1, P x := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo
      (by norm_num) hFint hPint
    intro x hx
    exact fourCellOddStripSchur_sinhDensity_le_polynomial hx
  dsimp only [F, P] at hmono ⊢
  exact hmono.trans_lt
    integral_fourCellOddStripSchurPolynomial_lt_two_sevenths

private theorem intervalIntegrable_fourCellOddStripSchur_sinhDensity :
    IntervalIntegrable
      (fun x : ℝ ↦
        Real.sinh (fourCellOperatorHalfWidth * x / 2) ^ 2 /
          fourCellOddStripSchurWeight x) volume 0 1 := by
  let F : ℝ → ℝ := fun x ↦
    Real.sinh (fourCellOperatorHalfWidth * x / 2) ^ 2 /
      fourCellOddStripSchurWeight x
  let P : ℝ → ℝ := fourCellOddStripSchurPolynomial
  have hPint : IntervalIntegrable P volume 0 1 := by
    exact (by
      dsimp only [P]
      unfold fourCellOddStripSchurPolynomial
      fun_prop : Continuous P) |>.intervalIntegrable _ _
  have hFmeas : AEStronglyMeasurable F
      (volume.restrict (Ioc (0 : ℝ) 1)) := by
    apply Measurable.aestronglyMeasurable
    dsimp only [F]
    unfold fourCellOddStripSchurWeight yoshidaEndpointPotential
    fun_prop
  have hPset : IntegrableOn P (Ioc (0 : ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).1 hPint
  have hFset : IntegrableOn F (Ioc (0 : ℝ) 1) := by
    apply hPset.mono' hFmeas
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
        MeasureTheory.Measure.ae_ne
          (volume.restrict (Ioc (0 : ℝ) 1)) (1 : ℝ)] with x hx hx1
    have hxoo : x ∈ Ioo (0 : ℝ) 1 := ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩
    have hle := fourCellOddStripSchur_sinhDensity_le_polynomial hxoo
    have hF0 : 0 ≤ F x := by
      dsimp only [F]
      exact div_nonneg (sq_nonneg _)
        (fourCellOddStripSchurWeight_pos_of_mem_Ioo hxoo).le
    rw [Real.norm_eq_abs, abs_of_nonneg hF0]
    simpa only [F, P] using hle
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).2 hFset

private theorem intervalIntegrable_fourCellOddStripSchurWeight_mul_sq
    (w : ℝ → ℝ) (hw : Continuous w) :
    IntervalIntegrable
      (fun x : ℝ ↦ fourCellOddStripSchurWeight x * w x ^ 2)
      volume 0 1 := by
  have hmass : IntervalIntegrable (fun x : ℝ ↦ w x ^ 2) volume 0 1 :=
    (hw.pow 2).intervalIntegrable _ _
  have hpotentialFull := intervalIntegrable_endpointPotential_mul_sq w hw
  have hpotential : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * w x ^ 2)
      volume 0 1 := hpotentialFull.mono_set (by
    intro x hx
    norm_num at hx ⊢
    constructor <;> linarith : uIcc (0 : ℝ) 1 ⊆ uIcc (-1 : ℝ) 1)
  apply (hmass.const_mul (3 / 200)).add
    (hpotential.const_mul (7 / 50)) |>.congr
  intro x _hx
  unfold fourCellOddStripSchurWeight
  ring

/-- Weighted Cauchy--Schwarz with the exact blended diagonal allocation. -/
theorem fourCellPositiveSinhMoment_sq_le_blendedDual_mul_allocation
    (w : ℝ → ℝ) (hw : Continuous w) :
    fourCellPositiveSinhMoment w
        (fourCellOperatorHalfWidth / 2) ^ 2 ≤
      (∫ x : ℝ in 0..1,
        Real.sinh (fourCellOperatorHalfWidth * x / 2) ^ 2 /
          fourCellOddStripSchurWeight x) *
        fourCellOddStripBlendedAllocation w := by
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)
  let W : ℝ → ℝ := fourCellOddStripSchurWeight
  let G : ℝ → ℝ := fun x ↦
    Real.sinh (fourCellOperatorHalfWidth * x / 2)
  have hW : ∀ᵐ x ∂μ, 0 < W x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
        MeasureTheory.Measure.ae_ne μ (1 : ℝ)] with x hx hx1
    exact fourCellOddStripSchurWeight_pos_of_mem_Ioo
      ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩
  have hdualMeas : AEStronglyMeasurable
      (fun x ↦ G x / Real.sqrt (W x)) μ := by
    apply Measurable.aestronglyMeasurable
    dsimp only [G, W, μ]
    unfold fourCellOddStripSchurWeight yoshidaEndpointPotential
    fun_prop
  have hdual : MemLp (fun x ↦ G x / Real.sqrt (W x)) 2 μ := by
    rw [memLp_two_iff_integrable_sq_norm hdualMeas]
    have hset : IntegrableOn
        (fun x : ℝ ↦
          Real.sinh (fourCellOperatorHalfWidth * x / 2) ^ 2 /
            fourCellOddStripSchurWeight x) (Ioc (0 : ℝ) 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).1
        intervalIntegrable_fourCellOddStripSchur_sinhDensity
    have hset' : Integrable
        (fun x : ℝ ↦ G x ^ 2 / W x) μ := by
      simpa only [μ, G, W] using hset
    apply hset'.congr
    filter_upwards [hW] with x hx
    rw [Real.norm_eq_abs, sq_abs, div_pow, Real.sq_sqrt hx.le]
  have hprimalMeas : AEStronglyMeasurable
      (fun x ↦ Real.sqrt (W x) * w x) μ := by
    apply Measurable.aestronglyMeasurable
    dsimp only [W, μ]
    unfold fourCellOddStripSchurWeight yoshidaEndpointPotential
    fun_prop
  have hprimal : MemLp (fun x ↦ Real.sqrt (W x) * w x) 2 μ := by
    rw [memLp_two_iff_integrable_sq_norm hprimalMeas]
    have hset : IntegrableOn
        (fun x : ℝ ↦ fourCellOddStripSchurWeight x * w x ^ 2)
        (Ioc (0 : ℝ) 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).1
        (intervalIntegrable_fourCellOddStripSchurWeight_mul_sq w hw)
    have hset' : Integrable (fun x : ℝ ↦ W x * w x ^ 2) μ := by
      simpa only [μ, W] using hset
    apply hset'.congr
    filter_upwards [hW] with x hx
    rw [Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt hx.le]
  have hcauchy := sq_integral_mul_le_weighted μ W G w
    hW hdual hprimal
  dsimp only [μ] at hcauchy
  repeat rw [← intervalIntegral.integral_of_le (by norm_num)] at hcauchy
  have hmomentEq : (∫ x : ℝ in 0..1, G x * w x) =
      fourCellPositiveSinhMoment w
        (fourCellOperatorHalfWidth / 2) := by
    unfold fourCellPositiveSinhMoment
    apply intervalIntegral.integral_congr
    intro x _hx
    dsimp only [G]
    congr 2
    ring
  have hweightEq : (∫ x : ℝ in 0..1, W x * w x ^ 2) =
      fourCellOddStripBlendedAllocation w := by
    simpa only [W] using integral_fourCellOddStripSchurWeight_mul_sq w hw
  rw [hmomentEq, hweightEq] at hcauchy
  simpa only [G, W] using hcauchy

/-- The complete negative sinh rank is dominated by the blended allocation,
with strict slack in the scalar dual norm. -/
theorem eight_mul_fourCell_sinhMoment_sq_le_blendedAllocation
    (w : ℝ → ℝ) (hw : Continuous w) :
    8 * fourCellOperatorHalfWidth *
        fourCellPositiveSinhMoment w
          (fourCellOperatorHalfWidth / 2) ^ 2 ≤
      fourCellOddStripBlendedAllocation w := by
  let I : ℝ := ∫ x : ℝ in 0..1,
    Real.sinh (fourCellOperatorHalfWidth * x / 2) ^ 2 /
      fourCellOddStripSchurWeight x
  let D : ℝ := fourCellOddStripBlendedAllocation w
  have hmoment :=
    fourCellPositiveSinhMoment_sq_le_blendedDual_mul_allocation w hw
  change fourCellPositiveSinhMoment w
    (fourCellOperatorHalfWidth / 2) ^ 2 ≤ I * D at hmoment
  have hI : I < (2 / 7 : ℝ) := by
    simpa only [I] using
      integral_fourCellOddStripSchur_sinhDensity_lt_two_sevenths
  have ha : 8 * fourCellOperatorHalfWidth < (7 / 2 : ℝ) := by
    nlinarith [fourCellOperatorHalfWidth_lt_seven_sixteenths]
  have hD : 0 ≤ D := by
    dsimp only [D, fourCellOddStripBlendedAllocation]
    have hm : 0 ≤ ∫ x : ℝ in 0..1, w x ^ 2 :=
      intervalIntegral.integral_nonneg (by norm_num)
        (fun x _hx ↦ sq_nonneg (w x))
    have hp : 0 ≤
        ∫ x : ℝ in 0..1, yoshidaEndpointPotential x * w x ^ 2 := by
      apply intervalIntegral.integral_nonneg (by norm_num)
      intro x hx
      by_cases hx1 : x = 1
      · simp [hx1, yoshidaEndpointPotential]
      · have hquartic := quartic_le_endpointPotential
            (show |x| < 1 by
              rw [abs_lt]
              constructor
              · linarith [hx.1]
              · exact lt_of_le_of_ne hx.2 hx1)
        have hV : 0 ≤ yoshidaEndpointPotential x := by
          unfold yoshidaEndpointQuartic at hquartic
          nlinarith [sq_nonneg x, sq_nonneg (x ^ 2)]
        exact mul_nonneg hV (sq_nonneg _)
    positivity
  have hI0 : 0 ≤ I := by
    dsimp only [I]
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro x hx
    by_cases hx0 : x = 0
    · simp [hx0]
    by_cases hx1 : x = 1
    · rw [hx1]
      unfold fourCellOddStripSchurWeight yoshidaEndpointPotential
      norm_num
      exact div_nonneg (sq_nonneg _) (by norm_num)
    · exact div_nonneg (sq_nonneg _)
        (fourCellOddStripSchurWeight_pos_of_mem_Ioo
          ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0), lt_of_le_of_ne hx.2 hx1⟩).le
  have hcoef : 8 * fourCellOperatorHalfWidth * I ≤ 1 := by
    nlinarith
  have ha0 : 0 ≤ 8 * fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  calc
    8 * fourCellOperatorHalfWidth *
        fourCellPositiveSinhMoment w
          (fourCellOperatorHalfWidth / 2) ^ 2 ≤
      8 * fourCellOperatorHalfWidth * (I * D) :=
        mul_le_mul_of_nonneg_left hmoment ha0
    _ = (8 * fourCellOperatorHalfWidth * I) * D := by ring
    _ ≤ 1 * D := mul_le_mul_of_nonneg_right hcoef hD
    _ = D := one_mul D

/-- After the rank is discharged structurally, odd strip positivity has one
remaining obligation: the exact non-rank base must dominate the fixed
blended diagonal allocation. -/
theorem fourCellOddStripCapacityLowerOperator_nonneg_of_base_ge_blended
    (w : ℝ → ℝ) (hw : Continuous w)
    (hbase : fourCellOddStripBlendedAllocation w ≤
      fourCellOddStripCapacityBase w) :
    0 ≤ fourCellOddStripCapacityLowerOperator w := by
  exact fourCellOddStripCapacityLowerOperator_nonneg_of_blendedSchur
    w hbase (eight_mul_fourCell_sinhMoment_sq_le_blendedAllocation w hw)

private theorem fourCell_sinh_sq_le_ninety_eight_six_twenty_fifths_potential
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    Real.sinh (fourCellOperatorHalfWidth * x / 2) ^ 2 ≤
      (98 / 625 : ℝ) * yoshidaEndpointPotential x := by
  have hsinh0 : 0 ≤ Real.sinh (fourCellOperatorHalfWidth * x / 2) := by
    rw [Real.sinh_nonneg_iff]
    have ha0 : 0 ≤ fourCellOperatorHalfWidth := by
      unfold fourCellOperatorHalfWidth
      positivity
    exact div_nonneg (mul_nonneg ha0 hx.1.le) (by norm_num)
  have hsinh := fourCell_sinh_weight_le_seven_twenty_fifths hx.1.le hx.2.le
  have hsinhSq :
      Real.sinh (fourCellOperatorHalfWidth * x / 2) ^ 2 ≤
        ((7 / 25 : ℝ) * x) ^ 2 :=
    (sq_le_sq₀ hsinh0 (mul_nonneg (by norm_num) hx.1.le)).2 hsinh
  have hquartic := quartic_le_endpointPotential
    (show |x| < 1 by rw [abs_lt]; constructor <;> linarith [hx.1, hx.2])
  unfold yoshidaEndpointQuartic at hquartic
  nlinarith [sq_nonneg x, sq_nonneg (x ^ 2)]

private theorem sq_intervalIntegral_zero_one_le_integral_sq
    (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ x : ℝ in 0..1, f x) ^ 2 ≤ ∫ x : ℝ in 0..1, f x ^ 2 := by
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)
  have honeMeas : AEStronglyMeasurable (fun _x : ℝ ↦ (1 : ℝ)) μ := by
    fun_prop
  have hfMeas : AEStronglyMeasurable f μ :=
    hf.aestronglyMeasurable.restrict
  have honeLp : MemLp (fun _x : ℝ ↦ (1 : ℝ)) 2 μ := by
    rw [memLp_two_iff_integrable_sq_norm honeMeas]
    have hcompact : IntegrableOn (fun _x : ℝ ↦ ‖(1 : ℝ)‖ ^ 2)
        (Icc (0 : ℝ) 1) :=
      (by fun_prop : Continuous (fun _x : ℝ ↦ ‖(1 : ℝ)‖ ^ 2))
        |>.continuousOn.integrableOn_compact isCompact_Icc
    exact hcompact.mono_set Ioc_subset_Icc_self
  have hfLp : MemLp f 2 μ := by
    rw [memLp_two_iff_integrable_sq_norm hfMeas]
    have hcompact : IntegrableOn (fun x : ℝ ↦ ‖f x‖ ^ 2)
        (Icc (0 : ℝ) 1) :=
      (hf.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
    exact hcompact.mono_set Ioc_subset_Icc_self
  have h := sq_integral_mul_le_weighted μ
    (fun _x : ℝ ↦ (1 : ℝ)) (fun _x : ℝ ↦ (1 : ℝ)) f
    (by simp) (by simpa using honeLp) (by simpa using hfLp)
  repeat rw [intervalIntegral.integral_of_le (by norm_num)]
  simpa [μ] using h

/-- The squared representer, including the profile, costs at most
`98 / 625` of the endpoint potential. -/
theorem integral_fourCell_sinh_sq_mul_le_ninety_eight_six_twenty_fifths_potential
    (w : ℝ → ℝ) (hw : Continuous w) :
    (∫ x : ℝ in 0..1,
        (Real.sinh (fourCellOperatorHalfWidth * x / 2) * w x) ^ 2) ≤
      (98 / 625 : ℝ) *
        ∫ x : ℝ in 0..1, yoshidaEndpointPotential x * w x ^ 2 := by
  have hleft : IntervalIntegrable
      (fun x : ℝ ↦
        (Real.sinh (fourCellOperatorHalfWidth * x / 2) * w x) ^ 2)
      volume 0 1 := by
    exact (by fun_prop : Continuous (fun x : ℝ ↦
      (Real.sinh (fourCellOperatorHalfWidth * x / 2) * w x) ^ 2))
        |>.intervalIntegrable _ _
  have hpotentialFull := intervalIntegrable_endpointPotential_mul_sq w hw
  have hpotential : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * w x ^ 2)
      volume 0 1 := hpotentialFull.mono_set (by
    intro x hx
    norm_num at hx ⊢
    constructor <;> linarith : uIcc (0 : ℝ) 1 ⊆ uIcc (-1 : ℝ) 1)
  have hright : IntervalIntegrable
      (fun x : ℝ ↦ (98 / 625 : ℝ) *
        (yoshidaEndpointPotential x * w x ^ 2)) volume 0 1 :=
    hpotential.const_mul (98 / 625)
  have hmono :
      (∫ x : ℝ in 0..1,
        (Real.sinh (fourCellOperatorHalfWidth * x / 2) * w x) ^ 2) ≤
      ∫ x : ℝ in 0..1,
        (98 / 625 : ℝ) * (yoshidaEndpointPotential x * w x ^ 2) := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo
      (by norm_num) hleft hright
    intro x hx
    have hweight :=
      fourCell_sinh_sq_le_ninety_eight_six_twenty_fifths_potential hx
    have hmul := mul_le_mul_of_nonneg_right hweight (sq_nonneg (w x))
    calc
      (Real.sinh (fourCellOperatorHalfWidth * x / 2) * w x) ^ 2 =
          Real.sinh (fourCellOperatorHalfWidth * x / 2) ^ 2 * w x ^ 2 := by
            ring
      _ ≤ ((98 / 625 : ℝ) * yoshidaEndpointPotential x) * w x ^ 2 := hmul
      _ = (98 / 625 : ℝ) * (yoshidaEndpointPotential x * w x ^ 2) := by ring
  rw [intervalIntegral.integral_const_mul] at hmono
  exact hmono

/-- Sharp rational structural payment of the complete odd hyperbolic rank.
This retains `907 / 625` of the two positive-half potential copies. -/
theorem eight_mul_fourCell_sinhMoment_sq_le_three_hundred_forty_three_six_twenty_fifths_potential
    (w : ℝ → ℝ) (hw : Continuous w) :
    8 * fourCellOperatorHalfWidth *
        fourCellPositiveSinhMoment w
          (fourCellOperatorHalfWidth / 2) ^ 2 ≤
      (343 / 625 : ℝ) *
        ∫ x : ℝ in 0..1, yoshidaEndpointPotential x * w x ^ 2 := by
  have hcauchy := sq_intervalIntegral_zero_one_le_integral_sq
    (fun x : ℝ ↦
      Real.sinh (fourCellOperatorHalfWidth * x / 2) * w x) (by fun_prop)
  have hweighted :=
    integral_fourCell_sinh_sq_mul_le_ninety_eight_six_twenty_fifths_potential
      w hw
  have ha0 : 0 ≤ fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  have ha : 8 * fourCellOperatorHalfWidth ≤ (7 / 2 : ℝ) := by
    nlinarith [fourCellOperatorHalfWidth_lt_seven_sixteenths]
  unfold fourCellPositiveSinhMoment at hcauchy ⊢
  calc
    8 * fourCellOperatorHalfWidth *
        (∫ x : ℝ in 0..1,
          Real.sinh (fourCellOperatorHalfWidth / 2 * x) * w x) ^ 2 ≤
      8 * fourCellOperatorHalfWidth *
        (∫ x : ℝ in 0..1,
          (Real.sinh (fourCellOperatorHalfWidth * x / 2) * w x) ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            convert hcauchy using 1
            all_goals ring_nf
    _ ≤ 8 * fourCellOperatorHalfWidth *
        ((98 / 625 : ℝ) *
          ∫ x : ℝ in 0..1, yoshidaEndpointPotential x * w x ^ 2) :=
      mul_le_mul_of_nonneg_left hweighted (by positivity)
    _ ≤ (343 / 625 : ℝ) *
        ∫ x : ℝ in 0..1, yoshidaEndpointPotential x * w x ^ 2 := by
      have hpotentialNonneg : 0 ≤
          ∫ x : ℝ in 0..1, yoshidaEndpointPotential x * w x ^ 2 := by
        apply intervalIntegral.integral_nonneg (by norm_num)
        intro x hx
        have hV : 0 ≤ yoshidaEndpointPotential x := by
          by_cases hx1 : x = 1
          · simp [hx1, yoshidaEndpointPotential]
          · have hquartic := quartic_le_endpointPotential
                (show |x| < 1 by
                  rw [abs_lt]
                  constructor
                  · linarith [hx.1]
                  · exact lt_of_le_of_ne hx.2 hx1)
            unfold yoshidaEndpointQuartic at hquartic
            nlinarith [sq_nonneg x, sq_nonneg (x ^ 2)]
        exact mul_nonneg hV (sq_nonneg _)
      nlinarith

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddStripCapacityClosureStructural

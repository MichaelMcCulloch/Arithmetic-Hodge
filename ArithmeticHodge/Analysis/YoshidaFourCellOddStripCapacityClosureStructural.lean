import ArithmeticHodge.Analysis.YoshidaFourCellOddStripCapacityAssemblyStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddPolarPotentialStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicRankResidualBound
import ArithmeticHodge.Analysis.YoshidaEndpointPotentialOddCoercivity
import ArithmeticHodge.Analysis.YoshidaEndpointPullbackLipschitz
import ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedRemainderEnvelopeKernel
import ArithmeticHodge.Analysis.UnitIntervalLogEnergyLipschitz
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddCleanSharp

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddStripCapacityClosureStructural

noncomputable section

open YoshidaEndpointPotentialBound
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
open YoshidaFactorTwoIntegrableLagRepresenterStructural
open YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive
open YoshidaFactorTwoPhaseIntrinsicOddCleanSharp
open YoshidaFactorTwoPhaseIntrinsicOddLowEndpointStructuralPositive
open YoshidaFactorTwoPhaseSymmetricCarleman
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointClean
open YoshidaEndpointOddOneThreeRawPolarization
open YoshidaEndpointOddResidualRegularity
open YoshidaRegularKernelBound
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
  have hKnonneg : ∀ p ∈ A ×ˢ A, 0 ≤ K p := by
    intro p hp
    dsimp only [K, S, J]
    unfold centeredLogDifferenceKernel
    exact add_nonneg (div_nonneg (sq_nonneg _) (abs_nonneg _))
      (div_nonneg (sq_nonneg _) (add_nonneg hp.1.1 hp.2.1))
  have hJnonneg : ∀ p ∈ B ×ˢ B, 0 ≤ J p := by
    intro p hp
    dsimp only [J]
    exact div_nonneg (sq_nonneg _) (add_nonneg
      (by linarith [hp.1.1]) (by linarith [hp.2.1]))
  have hAA0 : 0 ≤
      ∫ p : ℝ × ℝ in A ×ˢ A, K p
        ∂((volume : Measure ℝ).prod volume) := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem (hAmeas.prod hAmeas)] with p hp
    exact hKnonneg p hp
  have hJBB0 : 0 ≤
      ∫ p : ℝ × ℝ in B ×ˢ B, J p
        ∂((volume : Measure ℝ).prod volume) := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem (hBmeas.prod hBmeas)] with p hp
    exact hJnonneg p hp
  have hset :
      2 * (∫ p : ℝ × ℝ in P, K p
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

theorem fourCellOddRawStripCancellationReserve_add
    (u v : ℝ → ℝ) :
    fourCellOddRawStripCancellationReserve (u + v) =
      fourCellOddRawStripCancellationReserve u +
        2 * fourCellOddRawStripCancellationPolarization u v +
          fourCellOddRawStripCancellationReserve v := by
  unfold fourCellOddRawStripCancellationPolarization
  ring

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
            all_goals ring
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

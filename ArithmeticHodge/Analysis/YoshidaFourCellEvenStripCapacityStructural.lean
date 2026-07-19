import ArithmeticHodge.Analysis.YoshidaFourCellOddEndpointStripCoercivityStructural
import ArithmeticHodge.Analysis.YoshidaFourCellCompletedParityOperatorStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellEvenStripCapacityStructural

noncomputable section

open CenteredLogEnergyGap
open UnitIntervalLogEnergyAffine
open UnitIntervalLogEnergyLipschitz
open UnitIntervalLogEnergyProjection
open YoshidaEndpointPullbackLipschitz
open YoshidaFourCellEndpointHalfFoldStructural
open YoshidaFourCellEndpointVarianceStructural
open YoshidaFourCellCompletedParityOperatorStructural
open YoshidaFourCellOddEndpointStripCoercivityStructural
open YoshidaFourCellParityHalfFoldStructural
open YoshidaFourCellParityOperatorStructural
open YoshidaFourCellRawParityFoldStructural
open YoshidaFourCellRegularParityFoldStructural
open YoshidaEndpointPotentialBound
open YoshidaGeneralEndpointPhysicalRealQuadraticStructural

/-!
# Lossless endpoint-strip reduction for the even four-cell channel

Reflection about the midpoint `4/5` diagonalizes the adverse even prime
translation.  The strip-odd component is favorable.  The strip-even
component is adverse only in its constant coordinate: its mean-zero part is
paid by the exact logarithmic spectral gap.  Thus the full endpoint
translation reduces to one scalar strip-mean rank, not a pointwise potential
charge.
-/

/-- Mean of the strip-even trace after pulling `[3/5,1]` back to `[-1,1]`. -/
def fourCellEvenEndpointStripMean (w : ℝ → ℝ) : ℝ :=
  centeredIntervalMean (fourCellOddEndpointStripEven w)

/-- Physical mass of the constant strip-even coordinate. -/
def fourCellEvenEndpointStripMeanMass (w : ℝ → ℝ) : ℝ :=
  (2 / 5 : ℝ) * fourCellEvenEndpointStripMean w ^ 2

/-- Mean-zero part of the strip-even trace. -/
def fourCellEvenEndpointStripResidual (w : ℝ → ℝ) (z : ℝ) : ℝ :=
  fourCellOddEndpointStripEven w z - fourCellEvenEndpointStripMean w

/-- Physical mass of the mean-zero strip-even trace. -/
def fourCellEvenEndpointStripResidualMass (w : ℝ → ℝ) : ℝ :=
  (1 / 5 : ℝ) * ∫ z : ℝ in -1..1,
    fourCellEvenEndpointStripResidual w z ^ 2

/-- Orthogonal mean/residual decomposition of the strip-even mass. -/
theorem fourCellOddEndpointStripEvenMass_eq_mean_add_residual
    (w : ℝ → ℝ) (hw : Continuous w) :
    fourCellOddEndpointStripEvenMass w =
      fourCellEvenEndpointStripMeanMass w +
        fourCellEvenEndpointStripResidualMass w := by
  let e := fourCellOddEndpointStripEven w
  let m := fourCellEvenEndpointStripMean w
  have he : Continuous e :=
    continuous_fourCellOddEndpointStripEven w hw
  have heInt : IntervalIntegrable e volume (-1) 1 :=
    he.intervalIntegrable _ _
  have heSqInt : IntervalIntegrable (fun z : ℝ ↦ e z ^ 2)
      volume (-1) 1 := (he.pow 2).intervalIntegrable _ _
  have hlinInt : IntervalIntegrable (fun z : ℝ ↦ 2 * m * e z)
      volume (-1) 1 := heInt.const_mul (2 * m)
  have hconstInt : IntervalIntegrable (fun _z : ℝ ↦ m ^ 2)
      volume (-1) 1 := intervalIntegrable_const
  have hmean : (∫ z : ℝ in -1..1, e z) = 2 * m := by
    dsimp only [m, e, fourCellEvenEndpointStripMean, centeredIntervalMean]
    ring
  have hresidual :
      (∫ z : ℝ in -1..1, (e z - m) ^ 2) =
        (∫ z : ℝ in -1..1, e z ^ 2) - 2 * m ^ 2 := by
    rw [show (fun z : ℝ ↦ (e z - m) ^ 2) =
        fun z ↦ (e z ^ 2 - 2 * m * e z) + m ^ 2 by
      funext z
      ring,
      intervalIntegral.integral_add (heSqInt.sub hlinInt) hconstInt,
      intervalIntegral.integral_sub heSqInt hlinInt,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const, hmean]
    norm_num
    ring
  unfold fourCellOddEndpointStripEvenMass
    fourCellEvenEndpointStripMeanMass
    fourCellEvenEndpointStripResidualMass
    fourCellEvenEndpointStripResidual
  dsimp only [e, m] at hresidual ⊢
  linarith

/-- Subtracting the strip mean does not change logarithmic difference
energy. -/
theorem centeredRawLogEnergy_evenEndpointStripResidual
    (w : ℝ → ℝ) :
    centeredRawLogEnergy (fourCellEvenEndpointStripResidual w) =
      centeredRawLogEnergy (fourCellOddEndpointStripEven w) := by
  unfold centeredRawLogEnergy fourCellEvenEndpointStripResidual
  apply intervalIntegral.integral_congr
  intro x _hx
  apply intervalIntegral.integral_congr
  intro y _hy
  ring

/-- The strip-even residual has zero centered mean. -/
theorem integral_evenEndpointStripResidual_eq_zero
    (w : ℝ → ℝ) (hw : Continuous w) :
    (∫ z : ℝ in -1..1, fourCellEvenEndpointStripResidual w z) = 0 := by
  let e := fourCellOddEndpointStripEven w
  let m := fourCellEvenEndpointStripMean w
  have he : Continuous e :=
    continuous_fourCellOddEndpointStripEven w hw
  have heInt : IntervalIntegrable e volume (-1) 1 :=
    he.intervalIntegrable _ _
  rw [show (fun z : ℝ ↦ fourCellEvenEndpointStripResidual w z) =
      fun z ↦ e z - m by rfl,
    intervalIntegral.integral_sub heInt intervalIntegrable_const,
    intervalIntegral.integral_const]
  dsimp only [m, e, fourCellEvenEndpointStripMean, centeredIntervalMean]
  norm_num
  ring

/-- The exact logarithmic gap pays four times the physical mass of the
mean-zero strip-even residual. -/
theorem four_mul_evenEndpointStripResidualMass_le_rawEnergy
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) :
    4 * fourCellEvenEndpointStripResidualMass w ≤
      fourCellOddEndpointStripEvenRawEnergy w := by
  let r := fourCellEvenEndpointStripResidual w
  have hrDiff : ContDiff ℝ 1 r := by
    change ContDiff ℝ 1 (fun z : ℝ ↦
      (w (4 / 5 + z / 5) + w (4 / 5 + (-z) / 5)) / 2 -
        fourCellEvenEndpointStripMean w)
    fun_prop
  have hrCont : Continuous r := hrDiff.continuous
  have hrLocal : LocallyLipschitzOn (Icc (-1) 1) r :=
    hrDiff.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1)
  have hmean : (∫ z : ℝ in -1..1, r z) = 0 := by
    simpa only [r] using
      integral_evenEndpointStripResidual_eq_zero w hw.continuous
  obtain ⟨C, hLip⟩ := exists_lipschitzWith_centeredPullback r hrLocal
  let f : unitInterval → ℝ := fun t ↦ centeredPullback r (t : ℝ)
  have hfCont : Continuous f := by
    dsimp only [f, centeredPullback]
    fun_prop
  have hfMem : MemLp f 2 :=
    hfCont.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  have henergy : Integrable (unitIntervalRawLogEnergyIntegrand f) :=
    integrable_unitIntervalRawLogEnergyIntegrand_of_lipschitzWith f
      (by simpa only [f] using hLip)
  have hgap := four_mul_integral_sq_le_centeredRawLogEnergy r
    (by simpa only [f] using hfMem)
    (by simpa only [f] using henergy) hmean
  unfold fourCellEvenEndpointStripResidualMass
    fourCellOddEndpointStripEvenRawEnergy
  rw [← centeredRawLogEnergy_evenEndpointStripResidual w]
  dsimp only [r] at hgap ⊢
  nlinarith

/-- The antimatched endpoint channel is exactly four times the strip-odd
mass. -/
theorem integral_fourCellEndpointHalfAntimatched_sq_eq_four_mul_oddMass
    (w : ℝ → ℝ) :
    (∫ t : ℝ in 0..2 / 5,
      fourCellEndpointHalfAntimatched w t ^ 2) =
      4 * fourCellOddEndpointStripOddMass w := by
  let o := fourCellOddEndpointStripOdd w
  have hsubst := intervalIntegral.integral_comp_mul_add
    (a := (0 : ℝ)) (b := 2 / 5)
    (fun z : ℝ ↦ (2 * o z) ^ 2)
    (by norm_num : (5 : ℝ) ≠ 0) (-1)
  calc
    (∫ t : ℝ in 0..2 / 5,
        fourCellEndpointHalfAntimatched w t ^ 2) =
        ∫ t : ℝ in 0..2 / 5, (2 * o (5 * t - 1)) ^ 2 := by
          apply intervalIntegral.integral_congr
          intro t _ht
          dsimp only [o, fourCellOddEndpointStripOdd,
            fourCellOddEndpointStripPullback]
          unfold fourCellEndpointHalfAntimatched
          congr 2
          all_goals ring_nf
    _ = (1 / 5 : ℝ) * ∫ z : ℝ in -1..1, (2 * o z) ^ 2 := by
      convert hsubst using 1
      all_goals norm_num
    _ = 4 * fourCellOddEndpointStripOddMass w := by
      rw [show (fun z : ℝ ↦ (2 * o z) ^ 2) =
          fun z ↦ 4 * o z ^ 2 by
        funext z
        ring,
        intervalIntegral.integral_const_mul]
      unfold fourCellOddEndpointStripOddMass
      dsimp only [o]
      ring

/-- In the ambient even sector the prime atom is adverse only on the
strip-even component and favorable on the strip-odd component. -/
theorem neg_primePairing_eq_neg_evenMass_add_oddMass_of_even
    (w : ℝ → ℝ) (hw : Continuous w) (heven : Function.Even w) :
    -(Real.sqrt 2 * Real.log 2) * fourCellEndpointPairing w =
      -(Real.sqrt 2 * Real.log 2) *
          fourCellOddEndpointStripEvenMass w +
        Real.sqrt 2 * Real.log 2 *
          fourCellOddEndpointStripOddMass w := by
  calc
    _ = (Real.sqrt 2 * Real.log 2 / 2) *
          (∫ t : ℝ in 0..2 / 5,
            fourCellEndpointHalfAntimatched w t ^ 2) -
        Real.sqrt 2 * Real.log 2 * fourCellEndpointHalfMass w :=
      neg_primePairing_eq_halfAntimatched_sub_mass_of_even w hw heven
    _ = _ := by
      rw [integral_fourCellEndpointHalfAntimatched_sq_eq_four_mul_oddMass w,
        fourCellEndpointHalfMass_eq_evenMass_add_oddMass w hw]
      ring

/-- Lossless structural absorption of the even prime translation.  After
the strip logarithmic gap is used, the only negative endpoint coordinate is
the scalar strip-even mean. -/
theorem fourCellEvenEndpointStrip_retained_prime_coercivity
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (heven : Function.Even w) :
    (2 - Real.sqrt 2 * Real.log 2) *
          fourCellEvenEndpointStripResidualMass w -
        Real.sqrt 2 * Real.log 2 *
          fourCellEvenEndpointStripMeanMass w +
        (1 / 2 : ℝ) * fourCellOddEndpointStripOddRawEnergy w +
        Real.sqrt 2 * Real.log 2 *
          fourCellOddEndpointStripOddMass w ≤
      (1 / 2 : ℝ) * fourCellOddEndpointStripRawEnergy w -
        Real.sqrt 2 * Real.log 2 * fourCellEndpointPairing w := by
  have hraw := fourCellOddEndpointStrip_rawEnergy_eq_even_add_odd w hw
  have hgap := four_mul_evenEndpointStripResidualMass_le_rawEnergy w hw
  have hmass := fourCellOddEndpointStripEvenMass_eq_mean_add_residual
    w hw.continuous
  have hprime := neg_primePairing_eq_neg_evenMass_add_oddMass_of_even
    w hw.continuous heven
  have hform :
      (1 / 2 : ℝ) * fourCellOddEndpointStripRawEnergy w -
          Real.sqrt 2 * Real.log 2 * fourCellEndpointPairing w =
        (1 / 2 : ℝ) * fourCellOddEndpointStripEvenRawEnergy w +
          (1 / 2 : ℝ) * fourCellOddEndpointStripOddRawEnergy w -
          Real.sqrt 2 * Real.log 2 *
            (fourCellEvenEndpointStripMeanMass w +
              fourCellEvenEndpointStripResidualMass w) +
          Real.sqrt 2 * Real.log 2 *
            fourCellOddEndpointStripOddMass w := by
    rw [hraw]
    calc
      (1 / 2 : ℝ) *
            (fourCellOddEndpointStripEvenRawEnergy w +
              fourCellOddEndpointStripOddRawEnergy w) -
          Real.sqrt 2 * Real.log 2 * fourCellEndpointPairing w =
        (1 / 2 : ℝ) * fourCellOddEndpointStripEvenRawEnergy w +
          (1 / 2 : ℝ) * fourCellOddEndpointStripOddRawEnergy w +
          (-(Real.sqrt 2 * Real.log 2) *
            fourCellEndpointPairing w) := by ring
      _ = _ := by rw [hprime, hmass]; ring
  rw [hform]
  nlinarith [hgap]

/-- The exact even operator after the endpoint translation has been reduced
to one adverse scalar strip-mean rank.  All unused raw energy, both regular
completion squares, the exact regular row, endpoint potential, and the
positive cosh rank remain coupled. -/
def fourCellEvenStripCapacityLowerOperator (w : ℝ → ℝ) : ℝ :=
  (2 - Real.sqrt 2 * Real.log 2) *
      fourCellEvenEndpointStripResidualMass w -
    Real.sqrt 2 * Real.log 2 * fourCellEvenEndpointStripMeanMass w +
    (1 / 2 : ℝ) * fourCellOddEndpointStripOddRawEnergy w +
    Real.sqrt 2 * Real.log 2 * fourCellOddEndpointStripOddMass w +
    (1 / 2 : ℝ) *
      (fourCellPositiveHalfRawSameSignEnergy w -
        fourCellOddEndpointStripRawEnergy w) +
    (1 / 2 : ℝ) * fourCellPositiveHalfRawReflectedEnergy w 1 +
    2 * (∫ x : ℝ in 0..1,
      yoshidaEndpointPotential x * w x ^ 2) -
    2 * (Real.log (2 * fourCellOperatorHalfWidth) +
        Real.eulerMascheroniConstant + Real.log Real.pi) *
      (∫ x : ℝ in 0..1, w x ^ 2) +
    fourCellOperatorHalfWidth *
      (fourCellPositiveHalfRegularSameSignSquare w
          fourCellOperatorHalfWidth +
        fourCellPositiveHalfRegularReflectedSquare w
          fourCellOperatorHalfWidth 1) -
    2 * fourCellOperatorHalfWidth *
      fourCellPositiveHalfRegularRowMass w fourCellOperatorHalfWidth +
    8 * fourCellOperatorHalfWidth *
      fourCellPositiveCoshMoment w
        (fourCellOperatorHalfWidth / 2) ^ 2

/-- The strip-mean operator is a genuine lower bound for the exact completed
even operator. -/
theorem fourCellEvenStripCapacityLowerOperator_le_completed
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (heven : Function.Even w) :
    fourCellEvenStripCapacityLowerOperator w ≤
      fourCellEvenCompletedParityOperator w := by
  have hstrip :=
    fourCellEvenEndpointStrip_retained_prime_coercivity w hw heven
  have hprime := neg_primePairing_eq_halfAntimatched_sub_mass_of_even
    w hw.continuous heven
  unfold fourCellEvenStripCapacityLowerOperator
    fourCellEvenCompletedParityOperator
  linear_combination hstrip + hprime

/-- Nonnegativity of the one-rank strip operator suffices for the complete
even four-cell bracket. -/
theorem fourCellBracket_nonnegative_of_evenStripCapacity
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (heven : Function.Even w)
    (hlower : 0 ≤ fourCellEvenStripCapacityLowerOperator w) :
    0 ≤ centeredClippedPhysicalQuadratic fourCellOperatorHalfWidth w -
      Real.sqrt 2 * Real.log 2 * fourCellEndpointPairing w := by
  rw [fourCellBracket_eq_evenCompletedParityOperator w hw.continuous
    (hw.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1)) heven]
  exact hlower.trans
    (fourCellEvenStripCapacityLowerOperator_le_completed w hw heven)

end

end ArithmeticHodge.Analysis.YoshidaFourCellEvenStripCapacityStructural

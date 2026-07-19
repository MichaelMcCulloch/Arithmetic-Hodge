import ArithmeticHodge.Analysis.TwoByTwoSchur
import ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedRemainderEnvelopeKernel
import ArithmeticHodge.Analysis.YoshidaEndpointEvenTailReserve
import ArithmeticHodge.Analysis.YoshidaEndpointPotentialEvenMomentStructural
import ArithmeticHodge.Analysis.YoshidaEndpointTriangleFoldLipschitz
import ArithmeticHodge.Analysis.YoshidaEndpointWeightedCauchy
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseFullProfile
import ArithmeticHodge.Analysis.YoshidaFourCellEvenCapacityClosureStructural
import ArithmeticHodge.Analysis.YoshidaFourCellRegularRowMassBoundStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellEvenPolarSchurStructural

noncomputable section

open TwoByTwoSchur
open CenteredEndpointCorrelation
open UnitIntervalLogEnergyAffine
open UnitIntervalLogEnergyLipschitz
open UnitIntervalLogEnergyProjection
open YoshidaFactorTwoPhaseFullProfile
open YoshidaConstantBounds
open YoshidaEndpointEvenLowPotential
open YoshidaEndpointEvenProjectedRemainderEnvelopeKernel
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointPullbackLipschitz
open YoshidaEndpointPotentialBound
open YoshidaEndpointTriangleFoldLipschitz
open YoshidaFourCellEvenCapacityClosureStructural
open YoshidaFourCellCompletedParityOperatorStructural
open YoshidaFourCellEndpointHalfFoldStructural
open YoshidaFourCellEndpointVarianceStructural
open YoshidaFourCellParityHalfFoldStructural
open YoshidaFourCellParityOperatorStructural
open YoshidaFourCellRawParityFoldStructural
open YoshidaFourCellRegularParityFoldStructural
open YoshidaFourCellRegularRowMassBoundStructural
open YoshidaGeneralEndpointPhysicalRealQuadraticStructural
open YoshidaFourCellWidthPerturbationStructural
open YoshidaEndpointPotentialEvenMomentStructural
open YoshidaEndpointWeightedCauchy
open YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive
open YoshidaFactorTwoIntegrableLagRepresenterStructural
open YoshidaRegularKernelBound

/-!
# Exact polar Schur coordinates for the even four-cell bracket

The two previously proposed even lower operators discard signed pieces and are
false.  This file instead polarizes the complete four-cell bracket and splits
an even profile along its actual positive cosh functional.  No prime, regular,
or strip-gap term is estimated in these identities.
-/

/-- The exact symmetric polarization of the width/prime perturbation. -/
def fourCellWidthPrimePolarization (u v : ℝ → ℝ) : ℝ :=
  (fourCellWidthPrimePerturbation (u + v) -
      fourCellWidthPrimePerturbation u -
      fourCellWidthPrimePerturbation v) / 2

/-- The exact mixed entry of the complete four-cell bracket. -/
def fourCellExactBracketPolarization (u v : ℝ → ℝ) : ℝ :=
  factorTwoCenteredCleanPolarization u v +
    fourCellWidthPrimePolarization u v

/-- Lossless low--mixed--tail expansion of the complete bracket. -/
theorem fourCell_evenBracket_add_eq_low_add_mixed_add_tail
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    centeredClippedPhysicalQuadratic fourCellOperatorHalfWidth (u + v) -
        Real.sqrt 2 * Real.log 2 * fourCellEndpointPairing (u + v) =
      (centeredClippedPhysicalQuadratic fourCellOperatorHalfWidth u -
          Real.sqrt 2 * Real.log 2 * fourCellEndpointPairing u) +
        2 * fourCellExactBracketPolarization u v +
        (centeredClippedPhysicalQuadratic fourCellOperatorHalfWidth v -
          Real.sqrt 2 * Real.log 2 * fourCellEndpointPairing v) := by
  rw [fourCell_evenBracket_eq_clean_add_widthPrime (u + v) (hu.add hv),
    fourCell_evenBracket_eq_clean_add_widthPrime u hu,
    fourCell_evenBracket_eq_clean_add_widthPrime v hv,
    yoshidaEndpointOddCleanQuadratic_add_eq_polarization]
  unfold fourCellExactBracketPolarization fourCellWidthPrimePolarization
  ring

/-- Exact scalar Schur closure for the complete even four-cell bracket.  The
determinant hypothesis retains every cancellation in the mixed entry. -/
theorem fourCell_evenBracket_add_nonnegative_of_exactSchur
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    (hlow : 0 ≤
      centeredClippedPhysicalQuadratic fourCellOperatorHalfWidth u -
        Real.sqrt 2 * Real.log 2 * fourCellEndpointPairing u)
    (htail : 0 ≤
      centeredClippedPhysicalQuadratic fourCellOperatorHalfWidth v -
        Real.sqrt 2 * Real.log 2 * fourCellEndpointPairing v)
    (hdet : fourCellExactBracketPolarization u v ^ 2 ≤
      (centeredClippedPhysicalQuadratic fourCellOperatorHalfWidth u -
          Real.sqrt 2 * Real.log 2 * fourCellEndpointPairing u) *
        (centeredClippedPhysicalQuadratic fourCellOperatorHalfWidth v -
          Real.sqrt 2 * Real.log 2 * fourCellEndpointPairing v)) :
    0 ≤ centeredClippedPhysicalQuadratic fourCellOperatorHalfWidth (u + v) -
      Real.sqrt 2 * Real.log 2 * fourCellEndpointPairing (u + v) := by
  rw [fourCell_evenBracket_add_eq_low_add_mixed_add_tail u v hu hv]
  exact scalar_low_tail_nonneg _ _ _ hlow htail hdet

/-- Remove only the positive wide cosh rank from the exact even operator. -/
def fourCellEvenPolarFreeOperator (w : ℝ → ℝ) : ℝ :=
  fourCellEvenParityOperator w -
    8 * fourCellOperatorHalfWidth *
      fourCellPositiveCoshMoment w
        (fourCellOperatorHalfWidth / 2) ^ 2

/-- The complete even bracket is the polar-free operator plus exactly one
positive rank. -/
theorem fourCell_evenBracket_eq_polarFree_add_coshRank
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w)
    (heven : Function.Even w) :
    centeredClippedPhysicalQuadratic fourCellOperatorHalfWidth w -
        Real.sqrt 2 * Real.log 2 * fourCellEndpointPairing w =
      fourCellEvenPolarFreeOperator w +
        8 * fourCellOperatorHalfWidth *
          fourCellPositiveCoshMoment w
            (fourCellOperatorHalfWidth / 2) ^ 2 := by
  rw [fourCellBracket_eq_evenParityOperator w hw hlocal heven]
  unfold fourCellEvenPolarFreeOperator
  ring

/-- Residual after projecting onto any profile normalized by the wide cosh
functional. -/
def fourCellEvenCoshLow (w p : ℝ → ℝ) : ℝ → ℝ :=
  fun x ↦
    fourCellPositiveCoshMoment w (fourCellOperatorHalfWidth / 2) * p x

def fourCellEvenCoshResidual (w p : ℝ → ℝ) : ℝ → ℝ :=
  fun x ↦ w x - fourCellEvenCoshLow w p x

theorem fourCellEvenCoshResidual_decomposition (w p : ℝ → ℝ) :
    fourCellEvenCoshLow w p + fourCellEvenCoshResidual w p = w := by
  funext x
  simp only [fourCellEvenCoshResidual, fourCellEvenCoshLow, Pi.add_apply]
  ring

theorem fourCellEvenCoshLow_continuous
    (w p : ℝ → ℝ) (hp : Continuous p) :
    Continuous (fourCellEvenCoshLow w p) := by
  unfold fourCellEvenCoshLow
  fun_prop

theorem fourCellEvenCoshResidual_continuous
    (w p : ℝ → ℝ) (hw : Continuous w) (hp : Continuous p) :
    Continuous (fourCellEvenCoshResidual w p) := by
  unfold fourCellEvenCoshResidual
  exact hw.sub (fourCellEvenCoshLow_continuous w p hp)

theorem fourCellEvenCoshLow_even
    (w p : ℝ → ℝ) (hp : Function.Even p) :
    Function.Even (fourCellEvenCoshLow w p) := by
  intro x
  unfold fourCellEvenCoshLow
  rw [hp]

theorem fourCellEvenCoshResidual_even
    (w p : ℝ → ℝ) (hw : Function.Even w) (hp : Function.Even p) :
    Function.Even (fourCellEvenCoshResidual w p) := by
  intro x
  unfold fourCellEvenCoshResidual
  rw [hw, fourCellEvenCoshLow_even w p hp]

/-- A normalized cosh direction leaves a residual in the exact kernel of the
positive rank. -/
theorem fourCellPositiveCoshMoment_residual_eq_zero
    (w p : ℝ → ℝ) (hw : Continuous w) (hp : Continuous p)
    (hpMoment :
      fourCellPositiveCoshMoment p (fourCellOperatorHalfWidth / 2) = 1) :
    fourCellPositiveCoshMoment (fourCellEvenCoshResidual w p)
        (fourCellOperatorHalfWidth / 2) = 0 := by
  let lambda : ℝ := fourCellOperatorHalfWidth / 2
  let h : ℝ := fourCellPositiveCoshMoment w lambda
  have hwInt : IntervalIntegrable
      (fun x : ℝ ↦ Real.cosh (lambda * x) * w x) volume 0 1 :=
    ((Real.continuous_cosh.comp
      (continuous_const.mul continuous_id)).mul hw).intervalIntegrable _ _
  have hpInt : IntervalIntegrable
      (fun x : ℝ ↦ Real.cosh (lambda * x) * p x) volume 0 1 :=
    ((Real.continuous_cosh.comp
      (continuous_const.mul continuous_id)).mul hp).intervalIntegrable _ _
  unfold fourCellPositiveCoshMoment fourCellEvenCoshResidual
    fourCellEvenCoshLow
  change (∫ x : ℝ in 0..1,
      Real.cosh (lambda * x) * (w x - h * p x)) = 0
  rw [show (fun x : ℝ ↦ Real.cosh (lambda * x) * (w x - h * p x)) =
      fun x ↦ Real.cosh (lambda * x) * w x -
        h * (Real.cosh (lambda * x) * p x) by
      funext x
      ring]
  rw [intervalIntegral.integral_sub hwInt (hpInt.const_mul h),
    intervalIntegral.integral_const_mul]
  change fourCellPositiveCoshMoment w lambda -
      h * fourCellPositiveCoshMoment p lambda = 0
  dsimp only [h, lambda]
  rw [hpMoment]
  ring

/-! ## Endpoint-preserving cosh coordinates -/

/-- The lowest even polynomial direction in the actual four-cell production
domain.  Unlike the constant pivot, it vanishes at both endpoint traces. -/
def fourCellEvenEndpointCoshSeed (x : ℝ) : ℝ := 1 - x ^ 2

theorem fourCellEvenEndpointCoshSeed_continuous :
    Continuous fourCellEvenEndpointCoshSeed := by
  unfold fourCellEvenEndpointCoshSeed
  fun_prop

theorem fourCellEvenEndpointCoshSeed_even :
    Function.Even fourCellEvenEndpointCoshSeed := by
  intro x
  unfold fourCellEvenEndpointCoshSeed
  ring

@[simp] theorem fourCellEvenEndpointCoshSeed_neg_one :
    fourCellEvenEndpointCoshSeed (-1) = 0 := by
  norm_num [fourCellEvenEndpointCoshSeed]

@[simp] theorem fourCellEvenEndpointCoshSeed_one :
    fourCellEvenEndpointCoshSeed 1 = 0 := by
  norm_num [fourCellEvenEndpointCoshSeed]

/-- The endpoint-zero seed has strictly positive wide-cosh coordinate. -/
theorem fourCellPositiveCoshMoment_endpointCoshSeed_pos :
    0 < fourCellPositiveCoshMoment fourCellEvenEndpointCoshSeed
      (fourCellOperatorHalfWidth / 2) := by
  unfold fourCellPositiveCoshMoment
  apply intervalIntegral.integral_pos (by norm_num)
  · exact ((Real.continuous_cosh.comp
      (continuous_const.mul continuous_id)).mul
        fourCellEvenEndpointCoshSeed_continuous).continuousOn
  · intro x hx
    have hsq : x ^ 2 ≤ 1 := by
      nlinarith [hx.1, hx.2, sq_nonneg x]
    exact mul_nonneg (Real.cosh_pos _).le (sub_nonneg.mpr hsq)
  · refine ⟨1 / 2, by norm_num, ?_⟩
    unfold fourCellEvenEndpointCoshSeed
    have hcosh : 0 < Real.cosh
        (fourCellOperatorHalfWidth / 2 * (1 / 2 : ℝ)) :=
      Real.cosh_pos _
    nlinarith

/-- Normalize the endpoint-zero seed by its exact wide-cosh coordinate. -/
def fourCellEvenEndpointCoshUnit (x : ℝ) : ℝ :=
  (fourCellPositiveCoshMoment fourCellEvenEndpointCoshSeed
      (fourCellOperatorHalfWidth / 2))⁻¹ *
    fourCellEvenEndpointCoshSeed x

theorem fourCellEvenEndpointCoshUnit_continuous :
    Continuous fourCellEvenEndpointCoshUnit := by
  unfold fourCellEvenEndpointCoshUnit
  exact continuous_const.mul fourCellEvenEndpointCoshSeed_continuous

theorem fourCellEvenEndpointCoshUnit_even :
    Function.Even fourCellEvenEndpointCoshUnit := by
  intro x
  unfold fourCellEvenEndpointCoshUnit
  rw [fourCellEvenEndpointCoshSeed_even]

@[simp] theorem fourCellEvenEndpointCoshUnit_neg_one :
    fourCellEvenEndpointCoshUnit (-1) = 0 := by
  simp [fourCellEvenEndpointCoshUnit]

@[simp] theorem fourCellEvenEndpointCoshUnit_one :
    fourCellEvenEndpointCoshUnit 1 = 0 := by
  simp [fourCellEvenEndpointCoshUnit]

theorem fourCellPositiveCoshMoment_endpointCoshUnit :
    fourCellPositiveCoshMoment fourCellEvenEndpointCoshUnit
        (fourCellOperatorHalfWidth / 2) = 1 := by
  let M : ℝ := fourCellPositiveCoshMoment fourCellEvenEndpointCoshSeed
    (fourCellOperatorHalfWidth / 2)
  have hM : M ≠ 0 := by
    exact fourCellPositiveCoshMoment_endpointCoshSeed_pos.ne'
  unfold fourCellPositiveCoshMoment fourCellEvenEndpointCoshUnit
  rw [show (fun x : ℝ ↦
      Real.cosh (fourCellOperatorHalfWidth / 2 * x) *
        ((fourCellPositiveCoshMoment fourCellEvenEndpointCoshSeed
            (fourCellOperatorHalfWidth / 2))⁻¹ *
          fourCellEvenEndpointCoshSeed x)) =
      fun x ↦ M⁻¹ *
        (Real.cosh (fourCellOperatorHalfWidth / 2 * x) *
          fourCellEvenEndpointCoshSeed x) by
    funext x
    dsimp only [M]
    ring]
  rw [intervalIntegral.integral_const_mul]
  change M⁻¹ * M = 1
  exact inv_mul_cancel₀ hM

/-- For an actual production profile, projection onto the endpoint-zero
cosh direction leaves both endpoint traces zero. -/
theorem fourCellEvenEndpointCoshResidual_endpoints_zero
    (w : ℝ → ℝ) (hw : w (-1) = 0 ∧ w 1 = 0) :
    fourCellEvenCoshResidual w fourCellEvenEndpointCoshUnit (-1) = 0 ∧
      fourCellEvenCoshResidual w fourCellEvenEndpointCoshUnit 1 = 0 := by
  constructor
  · unfold fourCellEvenCoshResidual fourCellEvenCoshLow
    rw [hw.1, fourCellEvenEndpointCoshUnit_neg_one]
    ring
  · unfold fourCellEvenCoshResidual fourCellEvenCoshLow
    rw [hw.2, fourCellEvenEndpointCoshUnit_one]
    ring

/-- The endpoint-adapted projection simultaneously preserves every geometric
constraint available on an even production profile and kills the positive
wide-cosh rank exactly. -/
theorem fourCellEvenEndpointCoshResidual_constraints
    (w : ℝ → ℝ) (hw : Continuous w) (hweven : Function.Even w)
    (hend : w (-1) = 0 ∧ w 1 = 0) :
    Continuous (fourCellEvenCoshResidual w fourCellEvenEndpointCoshUnit) ∧
      Function.Even
        (fourCellEvenCoshResidual w fourCellEvenEndpointCoshUnit) ∧
      (fourCellEvenCoshResidual w fourCellEvenEndpointCoshUnit (-1) = 0 ∧
        fourCellEvenCoshResidual w fourCellEvenEndpointCoshUnit 1 = 0) ∧
      fourCellPositiveCoshMoment
          (fourCellEvenCoshResidual w fourCellEvenEndpointCoshUnit)
          (fourCellOperatorHalfWidth / 2) = 0 := by
  exact ⟨
    fourCellEvenCoshResidual_continuous w fourCellEvenEndpointCoshUnit hw
      fourCellEvenEndpointCoshUnit_continuous,
    fourCellEvenCoshResidual_even w fourCellEvenEndpointCoshUnit hweven
      fourCellEvenEndpointCoshUnit_even,
    fourCellEvenEndpointCoshResidual_endpoints_zero w hend,
    fourCellPositiveCoshMoment_residual_eq_zero
      w fourCellEvenEndpointCoshUnit hw
      fourCellEvenEndpointCoshUnit_continuous
      fourCellPositiveCoshMoment_endpointCoshUnit⟩

/-! ## The zero-cosh hyperplane is quantitatively close to mean zero -/

/-- On the unit interval, `cosh z - 1` is bounded by `z²` throughout the
range needed by the four-cell width. -/
theorem cosh_sub_one_le_sq_of_abs_le_one
    {z : ℝ} (hz : |z| ≤ 1) :
    Real.cosh z - 1 ≤ z ^ 2 := by
  have hzSq0 : 0 ≤ z ^ 2 := sq_nonneg z
  have hzSq : z ^ 2 ≤ 1 := by
    have hpow := pow_le_pow_left₀ (abs_nonneg z) hz 2
    simpa only [sq_abs, one_pow] using hpow
  let u : ℝ := z ^ 2 / 2
  have hu0 : 0 ≤ u := by dsimp only [u]; positivity
  have hu1 : u < 1 := by dsimp only [u]; nlinarith
  have hexp := Real.exp_bound_div_one_sub_of_interval hu0 hu1
  have hfrac : 1 / (1 - u) - 1 ≤ z ^ 2 := by
    have hden : 0 < 1 - u := sub_pos.mpr hu1
    rw [show 1 / (1 - u) - 1 = u / (1 - u) by
      field_simp [hden.ne']
      ring]
    rw [div_le_iff₀ hden]
    dsimp only [u]
    nlinarith
  have hcosh := Real.cosh_le_exp_half_sq z
  change Real.cosh z ≤ Real.exp u at hcosh
  linarith

/-- Vanishing of the positive wide-cosh moment forces the ordinary half-mean
to be tiny compared with the `L²` mass.  This is a genuine codimension-one
estimate: the constant comes from the fourth-order norm of `cosh(λx) - 1`,
not from a modal cutoff. -/
theorem fourCell_halfMean_sq_le_one_div_twoThousand_mass_of_coshMoment_zero
    (w : ℝ → ℝ) (hw : Continuous w)
    (hzero : fourCellPositiveCoshMoment w
      (fourCellOperatorHalfWidth / 2) = 0) :
    (∫ x : ℝ in 0..1, w x) ^ 2 ≤
      (1 / 2000 : ℝ) * (∫ x : ℝ in 0..1, w x ^ 2) := by
  let lambda : ℝ := fourCellOperatorHalfWidth / 2
  let q : ℝ → ℝ := fun x ↦ Real.cosh (lambda * x) - 1
  have hlambda0 : 0 ≤ lambda := by
    dsimp only [lambda]
    unfold fourCellOperatorHalfWidth
    positivity
  have hlambda : lambda < 217 / 1000 := by
    have hlog := strict_log_two_bounds.2
    dsimp only [lambda]
    unfold fourCellOperatorHalfWidth
    nlinarith
  have hlambdaLe : lambda ≤ 1 := hlambda.le.trans (by norm_num)
  have hqcont : Continuous q := by
    dsimp only [q]
    fun_prop
  have hwInt : IntervalIntegrable w volume 0 1 :=
    hw.intervalIntegrable _ _
  have hqwInt : IntervalIntegrable (fun x ↦ q x * w x) volume 0 1 :=
    (hqcont.mul hw).intervalIntegrable _ _
  have hmoment : (∫ x : ℝ in 0..1, w x) =
      -(∫ x : ℝ in 0..1, q x * w x) := by
    have hz : (∫ x : ℝ in 0..1,
        Real.cosh (lambda * x) * w x) = 0 := by
      simpa only [fourCellPositiveCoshMoment, lambda] using hzero
    rw [show (fun x : ℝ ↦ Real.cosh (lambda * x) * w x) =
        fun x ↦ q x * w x + w x by
      funext x
      dsimp only [q]
      ring,
      intervalIntegral.integral_add hqwInt hwInt] at hz
    linarith
  have hcauchy : (∫ x : ℝ in 0..1, q x * w x) ^ 2 ≤
      (∫ x : ℝ in 0..1, q x ^ 2) *
        (∫ x : ℝ in 0..1, w x ^ 2) := by
    let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)
    have hqMeas : AEStronglyMeasurable q μ :=
      hqcont.aestronglyMeasurable.restrict
    have hwMeas : AEStronglyMeasurable w μ :=
      hw.aestronglyMeasurable.restrict
    have hqLp : MemLp q 2 μ := by
      rw [memLp_two_iff_integrable_sq_norm hqMeas]
      have hcompact : IntegrableOn (fun x : ℝ ↦ ‖q x‖ ^ 2)
          (Icc (0 : ℝ) 1) :=
        (hqcont.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
      exact hcompact.mono_set Ioc_subset_Icc_self
    have hwLp : MemLp w 2 μ := by
      rw [memLp_two_iff_integrable_sq_norm hwMeas]
      have hcompact : IntegrableOn (fun x : ℝ ↦ ‖w x‖ ^ 2)
          (Icc (0 : ℝ) 1) :=
        (hw.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
      exact hcompact.mono_set Ioc_subset_Icc_self
    have h := sq_integral_mul_le_weighted μ (fun _ : ℝ ↦ 1) q w
      (by simp) (by simpa using hqLp) (by simpa using hwLp)
    repeat rw [intervalIntegral.integral_of_le (by norm_num)]
    simpa only [μ, div_one, one_mul] using h
  have hqSqInt : IntervalIntegrable (fun x : ℝ ↦ q x ^ 2)
      volume 0 1 := (hqcont.pow 2).intervalIntegrable _ _
  have hpolyInt : IntervalIntegrable
      (fun x : ℝ ↦ lambda ^ 4 * x ^ 4) volume 0 1 :=
    (by fun_prop : Continuous (fun x : ℝ ↦ lambda ^ 4 * x ^ 4))
      |>.intervalIntegrable _ _
  have hqSqPoint {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
      q x ^ 2 ≤ lambda ^ 4 * x ^ 4 := by
    have hxAbs : |x| ≤ 1 := by
      rw [abs_of_nonneg hx.1]
      exact hx.2
    have hzAbs : |lambda * x| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg hlambda0]
      calc
        lambda * |x| ≤ lambda * 1 :=
          mul_le_mul_of_nonneg_left hxAbs hlambda0
        _ ≤ 1 := by simpa only [mul_one] using hlambdaLe
    have hq0 : 0 ≤ q x := by
      dsimp only [q]
      exact sub_nonneg.mpr (Real.one_le_cosh _)
    have hqle : q x ≤ lambda ^ 2 * x ^ 2 := by
      have hcosh := cosh_sub_one_le_sq_of_abs_le_one hzAbs
      dsimp only [q]
      simpa only [mul_pow] using hcosh
    have hrhs0 : 0 ≤ lambda ^ 2 * x ^ 2 :=
      mul_nonneg (sq_nonneg _) (sq_nonneg _)
    have hsq := (sq_le_sq₀ hq0 hrhs0).2 hqle
    nlinarith
  have hqSqBound : (∫ x : ℝ in 0..1, q x ^ 2) ≤
      lambda ^ 4 / 5 := by
    calc
      (∫ x : ℝ in 0..1, q x ^ 2) ≤
          ∫ x : ℝ in 0..1, lambda ^ 4 * x ^ 4 := by
        apply intervalIntegral.integral_mono_on (by norm_num) hqSqInt hpolyInt
        intro x hx
        exact hqSqPoint hx
      _ = lambda ^ 4 / 5 := by
        rw [intervalIntegral.integral_const_mul, integral_pow]
        norm_num
        ring
  have hlambda4 : lambda ^ 4 < (217 / 1000 : ℝ) ^ 4 :=
    pow_lt_pow_left₀ hlambda hlambda0 (by norm_num)
  have hconstant : lambda ^ 4 / 5 < (1 / 2000 : ℝ) := by
    calc
      lambda ^ 4 / 5 < (217 / 1000 : ℝ) ^ 4 / 5 := by
        exact div_lt_div_of_pos_right hlambda4 (by norm_num)
      _ < (1 / 2000 : ℝ) := by norm_num
  have hmass : 0 ≤ ∫ x : ℝ in 0..1, w x ^ 2 := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro x _hx
    exact sq_nonneg _
  rw [hmoment, neg_sq]
  calc
    (∫ x : ℝ in 0..1, q x * w x) ^ 2 ≤
        (∫ x : ℝ in 0..1, q x ^ 2) *
          (∫ x : ℝ in 0..1, w x ^ 2) := hcauchy
    _ ≤ (lambda ^ 4 / 5) * (∫ x : ℝ in 0..1, w x ^ 2) :=
      mul_le_mul_of_nonneg_right hqSqBound hmass
    _ ≤ (1 / 2000 : ℝ) * (∫ x : ℝ in 0..1, w x ^ 2) :=
      mul_le_mul_of_nonneg_right hconstant.le hmass

/-- In centered Legendre coordinates, the same hyperplane estimate says that
the constant coefficient carries at most `1/4000` of the full `L²` mass. -/
theorem centeredEvenP0Coefficient_sq_le_one_div_fourThousand_mass_of_coshMoment_zero
    (w : ℝ → ℝ) (hw : Continuous w) (heven : Function.Even w)
    (hzero : fourCellPositiveCoshMoment w
      (fourCellOperatorHalfWidth / 2) = 0) :
    centeredEvenP0Coefficient w ^ 2 ≤
      (1 / 4000 : ℝ) * (∫ x : ℝ in -1..1, w x ^ 2) := by
  have hmeanFold := integral_neg_one_one_eq_two_mul_zero_one_of_even
    w (hw.intervalIntegrable _ _) heven
  have hmassFold := integral_sq_eq_two_mul_positiveHalf
    w hw (Or.inl heven)
  have hhalf :=
    fourCell_halfMean_sq_le_one_div_twoThousand_mass_of_coshMoment_zero
      w hw hzero
  have hcoeff : centeredEvenP0Coefficient w =
      ∫ x : ℝ in 0..1, w x := by
    unfold centeredEvenP0Coefficient
    rw [hmeanFold]
    ring
  rw [hcoeff, hmassFold]
  convert hhalf using 1
  ring

/-- Removing the tiny constant coordinate forced by the zero-cosh condition
exposes the exact `P₂` gap.  Thus the full singular energy retains almost the
sharp `3/2` mass coefficient, without a finite cutoff. -/
theorem fiveNineNineSeven_div_fourThousand_mass_le_raw_div_four_of_coshMoment_zero
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w)
    (heven : Function.Even w)
    (hzero : fourCellPositiveCoshMoment w
      (fourCellOperatorHalfWidth / 2) = 0) :
    (5997 / 4000 : ℝ) * (∫ x : ℝ in -1..1, w x ^ 2) ≤
      centeredRawLogEnergy w / 4 := by
  let M : ℝ := ∫ x : ℝ in -1..1, w x ^ 2
  let c : ℝ := centeredEvenP0Coefficient w
  let b : ℝ := centeredEvenP2Coefficient w
  let r : ℝ → ℝ := centeredEvenZeroTwoResidual w
  let R : ℝ := ∫ x : ℝ in -1..1, r x ^ 2
  have hM : 0 ≤ M := by
    dsimp only [M]
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro x _hx
    exact sq_nonneg _
  have hR : 0 ≤ R := by
    dsimp only [R]
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro x _hx
    exact sq_nonneg _
  have hc : c ^ 2 ≤ (1 / 4000 : ℝ) * M := by
    simpa only [c, M] using
      centeredEvenP0Coefficient_sq_le_one_div_fourThousand_mass_of_coshMoment_zero
        w hw heven hzero
  have hmassDecomp : M = 2 * c ^ 2 + (2 / 5 : ℝ) * b ^ 2 + R := by
    have hmass := integral_centeredEvenZeroTwoResidual_sq w hw
    dsimp only [M, c, b, r, R]
    linarith
  obtain ⟨C, hLip⟩ :=
    exists_lipschitzWith_centeredPullback w hlocal
  let f : unitInterval → ℝ := fun t ↦ centeredPullback w (t : ℝ)
  have hfcont : Continuous f := by
    dsimp only [f, centeredPullback]
    fun_prop
  have hfmem : MemLp f 2 :=
    hfcont.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  have henergy : Integrable (unitIntervalRawLogEnergyIntegrand f) :=
    integrable_unitIntervalRawLogEnergyIntegrand_of_lipschitzWith f
      (by simpa only [f] using hLip)
  have hspectral :
      (3 / 5 : ℝ) * b ^ 2 + (25 / 12 : ℝ) * R ≤
        centeredRawLogEnergy w / 4 := by
    simpa only [b, R, r, f] using
      centered_even_zero_two_tail_energy_le
        w hw (by simpa only [f] using hfmem)
          (by simpa only [f] using henergy) heven
  have hnonconstant :
      (1999 / 2000 : ℝ) * M ≤ (2 / 5 : ℝ) * b ^ 2 + R := by
    nlinarith
  have hgap :
      (3 / 2 : ℝ) * ((2 / 5 : ℝ) * b ^ 2 + R) ≤
        (3 / 5 : ℝ) * b ^ 2 + (25 / 12 : ℝ) * R := by
    nlinarith
  calc
    (5997 / 4000 : ℝ) * M =
        (3 / 2 : ℝ) * ((1999 / 2000 : ℝ) * M) := by ring
    _ ≤ (3 / 2 : ℝ) * ((2 / 5 : ℝ) * b ^ 2 + R) :=
      mul_le_mul_of_nonneg_left hnonconstant (by norm_num)
    _ ≤ (3 / 5 : ℝ) * b ^ 2 + (25 / 12 : ℝ) * R := hgap
    _ ≤ centeredRawLogEnergy w / 4 := hspectral

/-! ## Canonical normalized constant direction -/

/-- Mass of the wide cosh functional on the constant profile. -/
def fourCellEvenCoshMass : ℝ :=
  fourCellPositiveCoshMoment (fun _ : ℝ ↦ 1)
    (fourCellOperatorHalfWidth / 2)

theorem one_le_fourCellEvenCoshMass : 1 ≤ fourCellEvenCoshMass := by
  have hcosh : IntervalIntegrable
      (fun x : ℝ ↦ Real.cosh ((fourCellOperatorHalfWidth / 2) * x))
      volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h := intervalIntegral.integral_mono_on
    (by norm_num : (0 : ℝ) ≤ 1)
    (Continuous.intervalIntegrable continuous_const 0 1) hcosh
    (fun x _hx ↦ Real.one_le_cosh
      ((fourCellOperatorHalfWidth / 2) * x))
  unfold fourCellEvenCoshMass fourCellPositiveCoshMoment
  simpa using h

theorem fourCellEvenCoshMass_pos : 0 < fourCellEvenCoshMass :=
  lt_of_lt_of_le (by norm_num) one_le_fourCellEvenCoshMass

private theorem one_add_sq_div_two_le_cosh (x : ℝ) :
    1 + x ^ 2 / 2 ≤ Real.cosh x := by
  have hnonneg (y : ℝ) (hy : 0 ≤ y) :
      1 + y ^ 2 / 2 ≤ Real.cosh y := by
    let q : ℝ → ℝ := fun z ↦ Real.cosh z - 1 - z ^ 2 / 2
    have hderiv (z : ℝ) : HasDerivAt q (Real.sinh z - z) z := by
      dsimp only [q]
      convert ((Real.hasDerivAt_cosh z).sub (hasDerivAt_const z 1)).sub
        (((hasDerivAt_id z).pow 2).div_const 2) using 1
      simp only [id_eq, Nat.cast_ofNat]
      ring
    have hcont : Continuous q := by
      dsimp only [q]
      fun_prop
    have hmono : MonotoneOn q (Icc 0 y) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc 0 y) hcont.continuousOn
      · intro z _hz
        exact (hderiv z).differentiableAt.differentiableWithinAt
      · intro z hz
        rw [(hderiv z).deriv]
        exact sub_nonneg.mpr
          (Real.self_le_sinh_iff.mpr (interior_subset hz).1)
    have hq := hmono (show (0 : ℝ) ∈ Icc 0 y by exact ⟨le_rfl, hy⟩)
      (show y ∈ Icc 0 y by exact ⟨hy, le_rfl⟩) hy
    dsimp only [q] at hq
    norm_num at hq
    linarith
  by_cases hx : 0 ≤ x
  · exact hnonneg x hx
  · have h := hnonneg (-x) (by linarith)
    simpa only [Real.cosh_neg, neg_sq] using h

/-- The wide-cosh mass has a quantitative quadratic Taylor reserve.  This
is the extra constant-direction margin needed by the exact Schur pivot. -/
theorem fiveThousandThirtyNine_div_fiveThousand_le_fourCellEvenCoshMass :
    (5039 / 5000 : ℝ) ≤ fourCellEvenCoshMass := by
  let a : ℝ := fourCellOperatorHalfWidth
  have hpoly : IntervalIntegrable
      (fun x : ℝ ↦ 1 + (a * x / 2) ^ 2 / 2) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hcosh : IntervalIntegrable
      (fun x : ℝ ↦ Real.cosh (a * x / 2)) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hle :
      (∫ x : ℝ in 0..1, 1 + (a * x / 2) ^ 2 / 2) ≤
        ∫ x : ℝ in 0..1, Real.cosh (a * x / 2) := by
    apply intervalIntegral.integral_mono_on (by norm_num) hpoly hcosh
    intro x _hx
    exact one_add_sq_div_two_le_cosh (a * x / 2)
  have hpolyExact :
      (∫ x : ℝ in 0..1, 1 + (a * x / 2) ^ 2 / 2) =
        1 + a ^ 2 / 24 := by
    rw [show (fun x : ℝ ↦ 1 + (a * x / 2) ^ 2 / 2) =
        fun x ↦ 1 + (a ^ 2 / 8) * x ^ 2 by
      funext x
      ring,
      intervalIntegral.integral_add
        (Continuous.intervalIntegrable continuous_const 0 1)
        (Continuous.intervalIntegrable (by fun_prop) 0 1),
      intervalIntegral.integral_const_mul, integral_pow]
    norm_num
    ring
  have ha : (34655 / 80000 : ℝ) < a := by
    dsimp only [a]
    unfold fourCellOperatorHalfWidth
    nlinarith [strict_log_two_bounds.1]
  have ha0 : 0 ≤ a := by
    dsimp only [a]
    unfold fourCellOperatorHalfWidth
    positivity
  have hsq : (34655 / 80000 : ℝ) ^ 2 ≤ a ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha.le)
      (add_nonneg ha0 (by norm_num : (0 : ℝ) ≤ 34655 / 80000))]
  have hrational :
      (5039 / 5000 : ℝ) ≤
        1 + (34655 / 80000 : ℝ) ^ 2 / 24 := by
    norm_num
  have hmassEq :
      fourCellEvenCoshMass =
        ∫ x : ℝ in 0..1, Real.cosh (a * x / 2) := by
    unfold fourCellEvenCoshMass fourCellPositiveCoshMoment
    apply intervalIntegral.integral_congr
    intro x _hx
    dsimp only [a]
    ring_nf
  rw [hmassEq]
  dsimp only [a] at hle hpolyExact hsq ⊢
  rw [hpolyExact] at hle
  nlinarith

private theorem centeredEndpointCorrelation_one (t : ℝ) :
    centeredEndpointCorrelation (fun _ : ℝ ↦ 1) t = 2 - t := by
  unfold centeredEndpointCorrelation
  norm_num
  ring

/-- The constant regular row mass is the triangular one-variable kernel
average.  This identity lets kernel envelopes sharpen the constant pivot
without estimating the two square-completion channels separately. -/
theorem fourCellPositiveHalfRegularRowMass_one_eq_triangleIntegral :
    fourCellPositiveHalfRegularRowMass (fun _ : ℝ ↦ 1)
        fourCellOperatorHalfWidth =
      ∫ t : ℝ in 0..2,
        yoshidaRegularKernel (fourCellOperatorHalfWidth * t) * (2 - t) := by
  have ha0 : 0 ≤ fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  have ha3 : fourCellOperatorHalfWidth ≤ Real.log 3 / 2 := by
    have h := five_mul_log_two_div_four_lt_log_three
    unfold fourCellOperatorHalfWidth
    linarith
  have hcomp :=
    neg_two_mul_regularCorrelation_eq_positiveHalfCompletion_even
      (fun _ : ℝ ↦ 1) continuous_const (by intro x; rfl)
      fourCellOperatorHalfWidth ha0 ha3
  have hsame :
      fourCellPositiveHalfRegularSameSignSquare (fun _ : ℝ ↦ 1)
        fourCellOperatorHalfWidth = 0 := by
    unfold fourCellPositiveHalfRegularSameSignSquare
    norm_num
  have hreflected :
      fourCellPositiveHalfRegularReflectedSquare (fun _ : ℝ ↦ 1)
        fourCellOperatorHalfWidth 1 = 0 := by
    unfold fourCellPositiveHalfRegularReflectedSquare
    norm_num
  rw [hsame, hreflected] at hcomp
  simp only [zero_add] at hcomp
  rw [show centeredEndpointCorrelation (fun _ : ℝ ↦ 1) =
      fun t ↦ 2 - t by
    funext t
    exact centeredEndpointCorrelation_one t] at hcomp
  have hapos : 0 < fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  nlinarith

/-- The sixth-order kernel envelope improves the constant regular row from
the generic `1 / 2` bound to `121 / 250`.  The envelope is used only up to
lag `8 / 5`, where the four-cell argument is at most `log 2`; the short
remaining interval uses the universal quarter bound. -/
theorem fourCellPositiveHalfRegularRowMass_one_le_121_div_250 :
    fourCellPositiveHalfRegularRowMass (fun _ : ℝ ↦ 1)
        fourCellOperatorHalfWidth ≤ (121 / 250 : ℝ) := by
  let a : ℝ := fourCellOperatorHalfWidth
  let q : ℝ → ℝ := fun t ↦ yoshidaRegularKernel (a * t)
  let major : ℝ → ℝ := fun t ↦
    (yoshidaRegularKernelPolynomial6 (a * t) + 1 / 500000) * (2 - t)
  have ha0 : 0 ≤ a := by
    dsimp only [a]
    unfold fourCellOperatorHalfWidth
    positivity
  have hqMeas : Measurable q := by
    dsimp only [q]
    exact measurable_yoshidaRegularKernel.comp
      (measurable_const.mul measurable_id)
  have hqBound : ∀ t ∈ Icc (0 : ℝ) 2, |q t| ≤ (1 / 4 : ℝ) := by
    intro t ht
    have harg0 : 0 ≤ a * t := mul_nonneg ha0 ht.1
    have harg4 : a * t ≤ 5 * Real.log 2 / 4 := by
      have hmul := mul_le_mul_of_nonneg_left ht.2 ha0
      dsimp only [a] at hmul ⊢
      unfold fourCellOperatorHalfWidth at hmul ⊢
      nlinarith
    have hk0 := yoshidaRegularKernel_nonneg_fourCellRange harg0 harg4
    rw [abs_of_nonneg hk0]
    exact yoshidaRegularKernel_le_quarter harg0
  have hfull : IntervalIntegrable (fun t ↦ q t * (2 - t)) volume 0 2 :=
    intervalIntegrable_boundedLag_mul_continuous q (fun t ↦ 2 - t)
      hqMeas (by fun_prop) (1 / 4) hqBound
  have hnear : IntervalIntegrable (fun t ↦ q t * (2 - t))
      volume 0 (8 / 5) := by
    apply hfull.mono_set
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 8 / 5),
      uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)]
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hfar : IntervalIntegrable (fun t ↦ q t * (2 - t))
      volume (8 / 5) 2 := by
    apply hfull.mono_set
    rw [uIcc_of_le (by norm_num : (8 / 5 : ℝ) ≤ 2),
      uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)]
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hmajorInt : IntervalIntegrable major volume 0 (8 / 5) := by
    apply Continuous.intervalIntegrable
    dsimp only [major]
    unfold yoshidaRegularKernelPolynomial6
    fun_prop
  have hnearPoint : ∀ t ∈ Icc (0 : ℝ) (8 / 5),
      q t * (2 - t) ≤ major t := by
    intro t ht
    have harg0 : 0 ≤ a * t := mul_nonneg ha0 ht.1
    have hargLog : a * t ≤ Real.log 2 := by
      have hmul := mul_le_mul_of_nonneg_left ht.2 ha0
      dsimp only [a] at hmul ⊢
      unfold fourCellOperatorHalfWidth at hmul ⊢
      nlinarith
    have henv := yoshidaRegularKernelPolynomial6_envelope harg0 hargLog
    have hkernel : q t ≤
        yoshidaRegularKernelPolynomial6 (a * t) + 1 / 500000 := by
      dsimp only [q]
      linarith
    exact mul_le_mul_of_nonneg_right hkernel (by linarith [ht.2])
  have hnearBound :
      (∫ t : ℝ in 0..8 / 5, q t * (2 - t)) ≤
        ∫ t : ℝ in 0..8 / 5, major t := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      hnear hmajorInt hnearPoint
  have hfarMajor : IntervalIntegrable (fun t : ℝ ↦
      (1 / 4 : ℝ) * (2 - t)) volume (8 / 5) 2 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hfarPoint : ∀ t ∈ Icc (8 / 5 : ℝ) 2,
      q t * (2 - t) ≤ (1 / 4 : ℝ) * (2 - t) := by
    intro t ht
    have hqLe : q t ≤ (1 / 4 : ℝ) := by
      exact (le_abs_self (q t)).trans (hqBound t ⟨by linarith [ht.1], ht.2⟩)
    exact mul_le_mul_of_nonneg_right hqLe (by linarith [ht.2])
  have hfarBound :
      (∫ t : ℝ in 8 / 5..2, q t * (2 - t)) ≤
        ∫ t : ℝ in 8 / 5..2, (1 / 4 : ℝ) * (2 - t) := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      hfar hfarMajor hfarPoint
  let A : ℝ → ℝ := fun t ↦
    ((1 / 2 : ℝ) + 1 / 250000) * t +
      (-a / 24 - 1 / 4 - 1 / 500000) * t ^ 2 / 2 +
      (-a ^ 2 / 16 + a / 48) * t ^ 3 / 3 +
      (7 * a ^ 3 / 5760 + a ^ 2 / 32) * t ^ 4 / 4 +
      (5 * a ^ 4 / 768 - 7 * a ^ 3 / 11520) * t ^ 5 / 5 +
      (-31 * a ^ 5 / 967680 - 5 * a ^ 4 / 1536) * t ^ 6 / 6 +
      (-61 * a ^ 6 / 92160 + 31 * a ^ 5 / 1935360) * t ^ 7 / 7 +
      (61 * a ^ 6 / 184320) * t ^ 8 / 8
  have hAderiv (t : ℝ) : HasDerivAt A (major t) t := by
    dsimp only [A, major]
    unfold yoshidaRegularKernelPolynomial6
    have h0 := (hasDerivAt_const t ((1 / 2 : ℝ) + 1 / 250000)).mul
      (hasDerivAt_id t)
    have h1 := ((hasDerivAt_const t
      (-a / 24 - 1 / 4 - 1 / 500000)).mul
        ((hasDerivAt_id t).pow 2)).div_const 2
    have h2 := ((hasDerivAt_const t (-a ^ 2 / 16 + a / 48)).mul
      ((hasDerivAt_id t).pow 3)).div_const 3
    have h3 := ((hasDerivAt_const t
      (7 * a ^ 3 / 5760 + a ^ 2 / 32)).mul
        ((hasDerivAt_id t).pow 4)).div_const 4
    have h4 := ((hasDerivAt_const t
      (5 * a ^ 4 / 768 - 7 * a ^ 3 / 11520)).mul
        ((hasDerivAt_id t).pow 5)).div_const 5
    have h5 := ((hasDerivAt_const t
      (-31 * a ^ 5 / 967680 - 5 * a ^ 4 / 1536)).mul
        ((hasDerivAt_id t).pow 6)).div_const 6
    have h6 := ((hasDerivAt_const t
      (-61 * a ^ 6 / 92160 + 31 * a ^ 5 / 1935360)).mul
        ((hasDerivAt_id t).pow 7)).div_const 7
    have h7 := ((hasDerivAt_const t (61 * a ^ 6 / 184320)).mul
      ((hasDerivAt_id t).pow 8)).div_const 8
    convert (((((((h0.add h1).add h2).add h3).add h4).add h5).add h6).add h7) using 1
    simp only [id_eq, Nat.cast_ofNat]
    ring
  have hmajorExact :
      (∫ t : ℝ in 0..8 / 5, major t) =
        12 / 25 - 28 / 1125 * a - 64 / 1875 * a ^ 2 +
          56 / 78125 * a ^ 3 + 128 / 28125 * a ^ 4 -
          43648 / 1550390625 * a ^ 5 -
          31232 / 41015625 * a ^ 6 + 3 / 781250 := by
    have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ht ↦ hAderiv t) hmajorInt
    rw [hint]
    dsimp only [A]
    ring
  have hfarExact :
      (∫ t : ℝ in 8 / 5..2, (1 / 4 : ℝ) * (2 - t)) = 1 / 50 := by
    let F : ℝ → ℝ := fun t ↦ (1 / 4 : ℝ) * (2 * t - t ^ 2 / 2)
    have hF (t : ℝ) : HasDerivAt F ((1 / 4 : ℝ) * (2 - t)) t := by
      dsimp only [F]
      convert (hasDerivAt_const t (1 / 4 : ℝ)).mul
        ((((hasDerivAt_id t).const_mul 2).sub
          (((hasDerivAt_id t).pow 2).div_const 2))) using 1
      simp only [id_eq, Nat.cast_ofNat]
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ht ↦ hF t) hfarMajor]
    norm_num [F]
  have haLower : (34655 / 80000 : ℝ) ≤ a := by
    dsimp only [a]
    unfold fourCellOperatorHalfWidth
    nlinarith [strict_log_two_bounds.1]
  have haUpper : a ≤ (34660 / 80000 : ℝ) := by
    dsimp only [a]
    unfold fourCellOperatorHalfWidth
    nlinarith [strict_log_two_bounds.2]
  have hlo0 : (0 : ℝ) ≤ 34655 / 80000 := by norm_num
  have hpowLo2 : (34655 / 80000 : ℝ) ^ 2 ≤ a ^ 2 :=
    pow_le_pow_left₀ hlo0 haLower 2
  have hpowLo5 : (34655 / 80000 : ℝ) ^ 5 ≤ a ^ 5 :=
    pow_le_pow_left₀ hlo0 haLower 5
  have hpowLo6 : (34655 / 80000 : ℝ) ^ 6 ≤ a ^ 6 :=
    pow_le_pow_left₀ hlo0 haLower 6
  have hpowHi3 : a ^ 3 ≤ (34660 / 80000 : ℝ) ^ 3 :=
    pow_le_pow_left₀ ha0 haUpper 3
  have hpowHi4 : a ^ 4 ≤ (34660 / 80000 : ℝ) ^ 4 :=
    pow_le_pow_left₀ ha0 haUpper 4
  rw [fourCellPositiveHalfRegularRowMass_one_eq_triangleIntegral]
  change (∫ t : ℝ in 0..2, q t * (2 - t)) ≤ (121 / 250 : ℝ)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hnear hfar
  calc
    (∫ t : ℝ in 0..2, q t * (2 - t)) =
        (∫ t : ℝ in 0..8 / 5, q t * (2 - t)) +
          ∫ t : ℝ in 8 / 5..2, q t * (2 - t) := hsplit.symm
    _ ≤ (∫ t : ℝ in 0..8 / 5, major t) +
          ∫ t : ℝ in 8 / 5..2, (1 / 4 : ℝ) * (2 - t) :=
      add_le_add hnearBound hfarBound
    _ = 12 / 25 - 28 / 1125 * a - 64 / 1875 * a ^ 2 +
          56 / 78125 * a ^ 3 + 128 / 28125 * a ^ 4 -
          43648 / 1550390625 * a ^ 5 -
          31232 / 41015625 * a ^ 6 + 3 / 781250 + 1 / 50 := by
      rw [hmajorExact, hfarExact]
    _ ≤ (121 / 250 : ℝ) := by
      linarith

/-- The canonical constant profile normalized to have wide cosh moment one. -/
def fourCellEvenCoshUnit (_x : ℝ) : ℝ :=
  (fourCellEvenCoshMass)⁻¹

theorem fourCellEvenCoshUnit_continuous : Continuous fourCellEvenCoshUnit := by
  unfold fourCellEvenCoshUnit
  fun_prop

theorem fourCellEvenCoshUnit_even : Function.Even fourCellEvenCoshUnit := by
  intro x
  rfl

theorem fourCellPositiveCoshMoment_unit :
    fourCellPositiveCoshMoment fourCellEvenCoshUnit
      (fourCellOperatorHalfWidth / 2) = 1 := by
  unfold fourCellPositiveCoshMoment fourCellEvenCoshUnit
  rw [show (fun x : ℝ ↦
      Real.cosh ((fourCellOperatorHalfWidth / 2) * x) *
        (fourCellEvenCoshMass)⁻¹) =
      fun x ↦ (fourCellEvenCoshMass)⁻¹ *
        Real.cosh ((fourCellOperatorHalfWidth / 2) * x) by
      funext x
      ring,
    intervalIntegral.integral_const_mul]
  have hmassEq :
      (∫ x : ℝ in 0..1,
        Real.cosh ((fourCellOperatorHalfWidth / 2) * x)) =
        fourCellEvenCoshMass := by
    unfold fourCellEvenCoshMass fourCellPositiveCoshMoment
    simp
  rw [hmassEq]
  exact inv_mul_cancel₀ fourCellEvenCoshMass_pos.ne'

/-- Exact constant-direction normal form.  The singular raw squares, regular
difference squares, and antimatched endpoint square vanish identically; the
only retained regular term is its row mass. -/
theorem fourCellEvenCompletedParityOperator_one_eq :
    fourCellEvenCompletedParityOperator (fun _ : ℝ ↦ 1) =
      2 * (∫ x : ℝ in 0..1, yoshidaEndpointPotential x) -
        2 * (Real.log (2 * fourCellOperatorHalfWidth) +
          Real.eulerMascheroniConstant + Real.log Real.pi) -
        2 * fourCellOperatorHalfWidth *
          fourCellPositiveHalfRegularRowMass (fun _ : ℝ ↦ 1)
            fourCellOperatorHalfWidth +
        8 * fourCellOperatorHalfWidth * fourCellEvenCoshMass ^ 2 -
        (2 / 5 : ℝ) * (Real.sqrt 2 * Real.log 2) := by
  unfold fourCellEvenCompletedParityOperator
    fourCellPositiveHalfRawSameSignEnergy
    fourCellPositiveHalfRawReflectedEnergy
    fourCellPositiveHalfRegularSameSignSquare
    fourCellPositiveHalfRegularReflectedSquare
    fourCellEndpointHalfAntimatched fourCellEndpointHalfMass
    fourCellEvenCoshMass
  norm_num [fourCellPositiveCoshMoment]
  ring

/-- Exact normal form on every constant scalar direction. -/
theorem fourCellEvenCompletedParityOperator_const_eq (c : ℝ) :
    fourCellEvenCompletedParityOperator (fun _ : ℝ ↦ c) =
      2 * c ^ 2 * (∫ x : ℝ in 0..1, yoshidaEndpointPotential x) -
        2 * (Real.log (2 * fourCellOperatorHalfWidth) +
          Real.eulerMascheroniConstant + Real.log Real.pi) * c ^ 2 -
        2 * fourCellOperatorHalfWidth *
          fourCellPositiveHalfRegularRowMass (fun _ : ℝ ↦ c)
            fourCellOperatorHalfWidth +
        8 * fourCellOperatorHalfWidth *
          (c * fourCellEvenCoshMass) ^ 2 -
        (2 / 5 : ℝ) * (Real.sqrt 2 * Real.log 2) * c ^ 2 := by
  unfold fourCellEvenCompletedParityOperator
    fourCellPositiveHalfRawSameSignEnergy
    fourCellPositiveHalfRawReflectedEnergy
    fourCellPositiveHalfRegularSameSignSquare
    fourCellPositiveHalfRegularReflectedSquare
    fourCellEndpointHalfAntimatched fourCellEndpointHalfMass
    fourCellEvenCoshMass fourCellPositiveCoshMoment
  simp only [sub_self, one_mul, mul_one]
  simp_rw [mul_pow]
  rw [show (fun x : ℝ ↦ yoshidaEndpointPotential x * c ^ 2) =
      fun x ↦ c ^ 2 * yoshidaEndpointPotential x by
      funext x
      ring,
    intervalIntegral.integral_const_mul]
  rw [show (fun _x : ℝ ↦ c ^ 2) = fun _x ↦ c ^ 2 * 1 by
      funext x
      ring,
    intervalIntegral.integral_const_mul]
  rw [show (fun x : ℝ ↦
      Real.cosh (fourCellOperatorHalfWidth / 2 * x) * c) =
      fun x ↦ c * Real.cosh (fourCellOperatorHalfWidth / 2 * x) by
      funext x
      ring,
    intervalIntegral.integral_const_mul]
  norm_num
  ring

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

private theorem sqrt_two_mul_log_two_lt_981_div_1000 :
    Real.sqrt 2 * Real.log 2 < (981 / 1000 : ℝ) := by
  have hs := sqrt_two_kernel_bounds.2
  have hl := strict_log_two_bounds.2
  have hs0 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hl0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc
    Real.sqrt 2 * Real.log 2 <
        (70711 / 50000 : ℝ) * Real.log 2 :=
      mul_lt_mul_of_pos_right hs hl0
    _ < (70711 / 50000 : ℝ) * (6932 / 10000 : ℝ) :=
      mul_lt_mul_of_pos_left hl (by norm_num)
    _ < (981 / 1000 : ℝ) := by norm_num

/-- On the zero-cosh hyperplane, the adverse endpoint translation consumes
only a controlled fraction of the raw logarithmic energy.  The small scalar
remainder is the quantitative cost of replacing exact mean zero by the
wide-cosh orthogonality condition. -/
theorem fourCellEndpointPairing_le_raw_add_mass_of_coshMoment_zero
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w)
    (heven : Function.Even w)
    (hzero : fourCellPositiveCoshMoment w
      (fourCellOperatorHalfWidth / 2) = 0) :
    fourCellEndpointPairing w ≤
      (101 / 400 : ℝ) * centeredRawLogEnergy w +
        (101 / 10000 : ℝ) *
          (∫ x : ℝ in -1..1, w x ^ 2) := by
  obtain ⟨C, hC⟩ :=
    hlocal.exists_lipschitzOnWith_of_compact isCompact_Icc
  have henergy :=
    integrableOn_centeredLogDifferenceKernel_prod_of_lipschitzOnWith w hC
  have hpair := fourCellEndpointPairing_le_rawLogEnergy_add_mean
    w hw henergy (ε := (1 / 100 : ℝ)) (by norm_num)
  have hcoeff :=
    centeredEvenP0Coefficient_sq_le_one_div_fourThousand_mass_of_coshMoment_zero
      w hw heven hzero
  have hmean :
      (∫ x : ℝ in -1..1, w x) ^ 2 ≤
        (1 / 1000 : ℝ) * (∫ x : ℝ in -1..1, w x ^ 2) := by
    unfold centeredEvenP0Coefficient at hcoeff
    nlinarith
  have hmeanScaled := mul_le_mul_of_nonneg_left hmean
    (by norm_num : (0 : ℝ) ≤ 101 / 10)
  norm_num at hpair
  nlinarith

/-- Retaining the strict `981/1000` dyadic coefficient leaves a positive
`919/400000` fraction of the raw energy after paying the complete prime
loss. -/
theorem sqrtTwoLogTwo_mul_fourCellEndpointPairing_le_raw_add_mass_of_coshMoment_zero
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w)
    (heven : Function.Even w)
    (hzero : fourCellPositiveCoshMoment w
      (fourCellOperatorHalfWidth / 2) = 0) :
    Real.sqrt 2 * Real.log 2 * fourCellEndpointPairing w ≤
      (99081 / 400000 : ℝ) * centeredRawLogEnergy w +
        (99081 / 10000000 : ℝ) *
          (∫ x : ℝ in -1..1, w x ^ 2) := by
  let P : ℝ := fourCellEndpointPairing w
  let R : ℝ :=
    (101 / 400 : ℝ) * centeredRawLogEnergy w +
      (101 / 10000 : ℝ) * (∫ x : ℝ in -1..1, w x ^ 2)
  let S : ℝ :=
    (99081 / 400000 : ℝ) * centeredRawLogEnergy w +
      (99081 / 10000000 : ℝ) * (∫ x : ℝ in -1..1, w x ^ 2)
  have hpair : P ≤ R := by
    simpa only [P, R] using
      fourCellEndpointPairing_le_raw_add_mass_of_coshMoment_zero
        w hw hlocal heven hzero
  have hraw : 0 ≤ centeredRawLogEnergy w := by
    unfold centeredRawLogEnergy
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro x _hx
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro y _hy
    positivity
  have hmass : 0 ≤ ∫ x : ℝ in -1..1, w x ^ 2 := by
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun _ _ ↦ sq_nonneg _)
  have hR : 0 ≤ R := by
    dsimp only [R]
    positivity
  have hbeta0 : 0 ≤ Real.sqrt 2 * Real.log 2 := by positivity
  have hbeta : Real.sqrt 2 * Real.log 2 ≤ (981 / 1000 : ℝ) :=
    sqrt_two_mul_log_two_lt_981_div_1000.le
  have hscaledR : (981 / 1000 : ℝ) * R = S := by
    dsimp only [R, S]
    ring
  have hS : 0 ≤ S := by
    dsimp only [S]
    positivity
  by_cases hP : 0 ≤ P
  · calc
      Real.sqrt 2 * Real.log 2 * fourCellEndpointPairing w =
          (Real.sqrt 2 * Real.log 2) * P := by rfl
      _ ≤ (981 / 1000 : ℝ) * P :=
        mul_le_mul_of_nonneg_right hbeta hP
      _ ≤ (981 / 1000 : ℝ) * R :=
        mul_le_mul_of_nonneg_left hpair (by norm_num)
      _ = S := hscaledR
      _ = _ := by rfl
  · have hPnonpos : P ≤ 0 := le_of_not_ge hP
    calc
      Real.sqrt 2 * Real.log 2 * fourCellEndpointPairing w =
          (Real.sqrt 2 * Real.log 2) * P := by rfl
      _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hbeta0 hPnonpos
      _ ≤ S := hS
      _ = _ := by rfl

/-- The canonical constant direction has a uniform positive margin in the
complete four-cell bracket.  This is the positive pivot for the exact
codimension-one Schur decomposition. -/
theorem one_twentieth_lt_fourCellEvenCompletedParityOperator_one :
    (1 / 20 : ℝ) <
      fourCellEvenCompletedParityOperator (fun _ : ℝ ↦ 1) := by
  have hpotentialFold := endpointPotential_eq_two_mul_positiveHalf
    (fun _ : ℝ ↦ 1) continuous_const (Or.inl (by intro x; rfl))
  have hpotential :
      2 * (∫ x : ℝ in 0..1, yoshidaEndpointPotential x) =
        2 - 2 * Real.log 2 := by
    calc
      2 * (∫ x : ℝ in 0..1, yoshidaEndpointPotential x) =
          ∫ x : ℝ in -1..1, yoshidaEndpointPotential x := by
        symm
        simpa using hpotentialFold
      _ = 2 - 2 * Real.log 2 := integral_endpointPotential_one
  have hrow := fourCellPositiveHalfRegularRowMass_le_half_mass
    (fun _ : ℝ ↦ 1) continuous_const
  norm_num at hrow
  have ha0 : 0 ≤ fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  have hrowCost :
      2 * fourCellOperatorHalfWidth *
          fourCellPositiveHalfRegularRowMass (fun _ : ℝ ↦ 1)
            fourCellOperatorHalfWidth ≤ fourCellOperatorHalfWidth := by
    nlinarith
  have hcoshSq : 1 ≤ fourCellEvenCoshMass ^ 2 := by
    nlinarith [one_le_fourCellEvenCoshMass]
  have hcoshGain :
      8 * fourCellOperatorHalfWidth ≤
        8 * fourCellOperatorHalfWidth * fourCellEvenCoshMass ^ 2 := by
    simpa only [mul_one] using
      (mul_le_mul_of_nonneg_left hcoshSq
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) ha0))
  have hscalar := fourCellScalar_lt_31577_div_20000
  have hbeta := sqrt_two_mul_log_two_lt_981_div_1000
  have hlogLower := strict_log_two_bounds.1
  have hlogUpper := strict_log_two_bounds.2
  rw [fourCellEvenCompletedParityOperator_one_eq]
  unfold fourCellOperatorHalfWidth at hrowCost hcoshGain hscalar ⊢
  nlinarith

/-- The quadratic Taylor reserve in the wide-cosh mass sharpens the
constant Schur pivot from `1 / 20` to `3 / 20`. -/
theorem three_twentieth_lt_fourCellEvenCompletedParityOperator_one :
    (3 / 20 : ℝ) <
      fourCellEvenCompletedParityOperator (fun _ : ℝ ↦ 1) := by
  have hpotentialFold := endpointPotential_eq_two_mul_positiveHalf
    (fun _ : ℝ ↦ 1) continuous_const (Or.inl (by intro x; rfl))
  have hpotential :
      2 * (∫ x : ℝ in 0..1, yoshidaEndpointPotential x) =
        2 - 2 * Real.log 2 := by
    calc
      2 * (∫ x : ℝ in 0..1, yoshidaEndpointPotential x) =
          ∫ x : ℝ in -1..1, yoshidaEndpointPotential x := by
        symm
        simpa using hpotentialFold
      _ = 2 - 2 * Real.log 2 := integral_endpointPotential_one
  have hrow := fourCellPositiveHalfRegularRowMass_le_half_mass
    (fun _ : ℝ ↦ 1) continuous_const
  norm_num at hrow
  have ha0 : 0 ≤ fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  have hrowCost :
      2 * fourCellOperatorHalfWidth *
          fourCellPositiveHalfRegularRowMass (fun _ : ℝ ↦ 1)
            fourCellOperatorHalfWidth ≤ fourCellOperatorHalfWidth := by
    nlinarith
  have hmass :=
    fiveThousandThirtyNine_div_fiveThousand_le_fourCellEvenCoshMass
  have hmass0 : 0 ≤ fourCellEvenCoshMass :=
    fourCellEvenCoshMass_pos.le
  have hmassSq :
      (5039 / 5000 : ℝ) ^ 2 ≤ fourCellEvenCoshMass ^ 2 := by
    nlinarith [mul_nonneg
      (sub_nonneg.mpr hmass)
      (add_nonneg hmass0 (by norm_num : (0 : ℝ) ≤ 5039 / 5000))]
  have haLower :
      (34655 / 80000 : ℝ) < fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    nlinarith [strict_log_two_bounds.1]
  have hcoshGain :
      8 * (34655 / 80000 : ℝ) * (5039 / 5000 : ℝ) ^ 2 ≤
        8 * fourCellOperatorHalfWidth * fourCellEvenCoshMass ^ 2 := by
    calc
      8 * (34655 / 80000 : ℝ) * (5039 / 5000 : ℝ) ^ 2 ≤
          8 * fourCellOperatorHalfWidth * (5039 / 5000 : ℝ) ^ 2 := by
        nlinarith
      _ ≤ 8 * fourCellOperatorHalfWidth * fourCellEvenCoshMass ^ 2 :=
        mul_le_mul_of_nonneg_left hmassSq
          (mul_nonneg (by norm_num) ha0)
  have hscalar := fourCellScalar_lt_31577_div_20000
  have hbeta := sqrt_two_mul_log_two_lt_981_div_1000
  have hlogLower := strict_log_two_bounds.1
  have hlogUpper := strict_log_two_bounds.2
  rw [fourCellEvenCompletedParityOperator_one_eq, hpotential]
  unfold fourCellOperatorHalfWidth at hrowCost hcoshGain hscalar ⊢
  nlinarith

/-- Combining the Taylor cosh reserve with the sharpened triangular kernel
average raises the normalized constant pivot to `13 / 80`. -/
theorem thirteen_div_eighty_lt_fourCellEvenCompletedParityOperator_one :
    (13 / 80 : ℝ) <
      fourCellEvenCompletedParityOperator (fun _ : ℝ ↦ 1) := by
  have hpotentialFold := endpointPotential_eq_two_mul_positiveHalf
    (fun _ : ℝ ↦ 1) continuous_const (Or.inl (by intro x; rfl))
  have hpotential :
      2 * (∫ x : ℝ in 0..1, yoshidaEndpointPotential x) =
        2 - 2 * Real.log 2 := by
    calc
      2 * (∫ x : ℝ in 0..1, yoshidaEndpointPotential x) =
          ∫ x : ℝ in -1..1, yoshidaEndpointPotential x := by
        symm
        simpa using hpotentialFold
      _ = 2 - 2 * Real.log 2 := integral_endpointPotential_one
  have hrow := fourCellPositiveHalfRegularRowMass_one_le_121_div_250
  have ha0 : 0 ≤ fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  have hrowCost :
      2 * fourCellOperatorHalfWidth *
          fourCellPositiveHalfRegularRowMass (fun _ : ℝ ↦ 1)
            fourCellOperatorHalfWidth ≤
        (121 / 125 : ℝ) * fourCellOperatorHalfWidth := by
    have hscaled := mul_le_mul_of_nonneg_left hrow
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) ha0)
    nlinarith
  have hmass :=
    fiveThousandThirtyNine_div_fiveThousand_le_fourCellEvenCoshMass
  have hmass0 : 0 ≤ fourCellEvenCoshMass :=
    fourCellEvenCoshMass_pos.le
  have hmassSq :
      (5039 / 5000 : ℝ) ^ 2 ≤ fourCellEvenCoshMass ^ 2 := by
    nlinarith [mul_nonneg
      (sub_nonneg.mpr hmass)
      (add_nonneg hmass0 (by norm_num : (0 : ℝ) ≤ 5039 / 5000))]
  have haLower :
      (34655 / 80000 : ℝ) < fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    nlinarith [strict_log_two_bounds.1]
  have hcoshGain :
      8 * (34655 / 80000 : ℝ) * (5039 / 5000 : ℝ) ^ 2 ≤
        8 * fourCellOperatorHalfWidth * fourCellEvenCoshMass ^ 2 := by
    calc
      8 * (34655 / 80000 : ℝ) * (5039 / 5000 : ℝ) ^ 2 ≤
          8 * fourCellOperatorHalfWidth * (5039 / 5000 : ℝ) ^ 2 := by
        nlinarith
      _ ≤ 8 * fourCellOperatorHalfWidth * fourCellEvenCoshMass ^ 2 :=
        mul_le_mul_of_nonneg_left hmassSq
          (mul_nonneg (by norm_num) ha0)
  have hscalar := fourCellScalar_lt_31577_div_20000
  have hbeta := sqrt_two_mul_log_two_lt_981_div_1000
  have hlogLower := strict_log_two_bounds.1
  have hlogUpper := strict_log_two_bounds.2
  rw [fourCellEvenCompletedParityOperator_one_eq, hpotential]
  unfold fourCellOperatorHalfWidth at hrowCost hcoshGain hscalar ⊢
  nlinarith

/-- The positive constant pivot is homogeneous with a uniform quadratic
margin.  The proof keeps the exact regular row and scales its structural row
bound, rather than appealing to an unproved quadratic-form interface. -/
theorem one_twentieth_mul_sq_le_fourCellEvenCompletedParityOperator_const
    (c : ℝ) :
    (1 / 20 : ℝ) * c ^ 2 ≤
      fourCellEvenCompletedParityOperator (fun _ : ℝ ↦ c) := by
  have hpotentialFold := endpointPotential_eq_two_mul_positiveHalf
    (fun _ : ℝ ↦ 1) continuous_const (Or.inl (by intro x; rfl))
  have hpotential :
      2 * (∫ x : ℝ in 0..1, yoshidaEndpointPotential x) =
        2 - 2 * Real.log 2 := by
    calc
      2 * (∫ x : ℝ in 0..1, yoshidaEndpointPotential x) =
          ∫ x : ℝ in -1..1, yoshidaEndpointPotential x := by
        symm
        simpa using hpotentialFold
      _ = 2 - 2 * Real.log 2 := integral_endpointPotential_one
  have hrow := fourCellPositiveHalfRegularRowMass_le_half_mass
    (fun _ : ℝ ↦ c) continuous_const
  norm_num at hrow
  have ha0 : 0 ≤ fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  have hrowCost :
      2 * fourCellOperatorHalfWidth *
          fourCellPositiveHalfRegularRowMass (fun _ : ℝ ↦ c)
            fourCellOperatorHalfWidth ≤
        fourCellOperatorHalfWidth * c ^ 2 := by
    have hscaled := mul_le_mul_of_nonneg_left hrow
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) ha0)
    nlinarith
  have hcoshSq : 1 ≤ fourCellEvenCoshMass ^ 2 := by
    nlinarith [one_le_fourCellEvenCoshMass]
  have hcoshScaled : c ^ 2 ≤ (c * fourCellEvenCoshMass) ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hcoshSq (sq_nonneg c)
    nlinarith
  have hcoshGain :
      8 * fourCellOperatorHalfWidth * c ^ 2 ≤
        8 * fourCellOperatorHalfWidth *
          (c * fourCellEvenCoshMass) ^ 2 := by
    exact mul_le_mul_of_nonneg_left hcoshScaled
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) ha0)
  have hcSq : 0 ≤ c ^ 2 := sq_nonneg c
  have hscalar := fourCellScalar_lt_31577_div_20000
  have hscalarScaled := mul_le_mul_of_nonneg_right hscalar.le hcSq
  have hbeta := sqrt_two_mul_log_two_lt_981_div_1000
  have hbetaScaled := mul_le_mul_of_nonneg_right hbeta.le hcSq
  have hlogLower := strict_log_two_bounds.1
  have hlogLowerScaled := mul_le_mul_of_nonneg_right hlogLower.le hcSq
  have hlogUpper := strict_log_two_bounds.2
  have hlogUpperScaled := mul_le_mul_of_nonneg_right hlogUpper.le hcSq
  rw [fourCellEvenCompletedParityOperator_const_eq]
  unfold fourCellOperatorHalfWidth at hrowCost hcoshGain hscalarScaled ⊢
  nlinarith

/-- Complete bracket form of the homogeneous constant pivot bound. -/
theorem one_twentieth_mul_sq_le_fourCell_evenBracket_const (c : ℝ) :
    (1 / 20 : ℝ) * c ^ 2 ≤
      centeredClippedPhysicalQuadratic fourCellOperatorHalfWidth
          (fun _ : ℝ ↦ c) -
        Real.sqrt 2 * Real.log 2 *
          fourCellEndpointPairing (fun _ : ℝ ↦ c) := by
  rw [fourCellBracket_eq_evenCompletedParityOperator
    (fun _ : ℝ ↦ c) continuous_const
      (contDiff_const.contDiffOn.locallyLipschitzOn
      (convex_Icc (-1 : ℝ) 1)) (by intro x; rfl)]
  exact one_twentieth_mul_sq_le_fourCellEvenCompletedParityOperator_const c

/-- Complete-bracket form of the sharpened normalized constant pivot. -/
theorem three_twentieth_lt_fourCell_evenBracket_one :
    (3 / 20 : ℝ) <
      centeredClippedPhysicalQuadratic fourCellOperatorHalfWidth
          (fun _ : ℝ ↦ 1) -
        Real.sqrt 2 * Real.log 2 *
          fourCellEndpointPairing (fun _ : ℝ ↦ 1) := by
  rw [fourCellBracket_eq_evenCompletedParityOperator
    (fun _ : ℝ ↦ 1) continuous_const
      (contDiff_const.contDiffOn.locallyLipschitzOn
        (convex_Icc (-1 : ℝ) 1)) (by intro x; rfl)]
  exact three_twentieth_lt_fourCellEvenCompletedParityOperator_one

/-- Complete-bracket form of the final sharpened normalized constant pivot. -/
theorem thirteen_div_eighty_lt_fourCell_evenBracket_one :
    (13 / 80 : ℝ) <
      centeredClippedPhysicalQuadratic fourCellOperatorHalfWidth
          (fun _ : ℝ ↦ 1) -
        Real.sqrt 2 * Real.log 2 *
          fourCellEndpointPairing (fun _ : ℝ ↦ 1) := by
  rw [fourCellBracket_eq_evenCompletedParityOperator
    (fun _ : ℝ ↦ 1) continuous_const
      (contDiff_const.contDiffOn.locallyLipschitzOn
        (convex_Icc (-1 : ℝ) 1)) (by intro x; rfl)]
  exact thirteen_div_eighty_lt_fourCellEvenCompletedParityOperator_one

/-- Every canonical cosh-low component therefore has a nonnegative exact
four-cell diagonal. -/
theorem fourCell_evenBracket_coshLow_nonnegative (w : ℝ → ℝ) :
    0 ≤ centeredClippedPhysicalQuadratic fourCellOperatorHalfWidth
          (fourCellEvenCoshLow w fourCellEvenCoshUnit) -
        Real.sqrt 2 * Real.log 2 *
          fourCellEndpointPairing
            (fourCellEvenCoshLow w fourCellEvenCoshUnit) := by
  let c : ℝ :=
    fourCellPositiveCoshMoment w (fourCellOperatorHalfWidth / 2) *
      (fourCellEvenCoshMass)⁻¹
  have hlow : fourCellEvenCoshLow w fourCellEvenCoshUnit =
      (fun _ : ℝ ↦ c) := by
    funext x
    simp only [fourCellEvenCoshLow, fourCellEvenCoshUnit, c]
  rw [hlow]
  exact (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 20) (sq_nonneg c)).trans
    (one_twentieth_mul_sq_le_fourCell_evenBracket_const c)

/-- The polar-free tail and one exact scalar determinant are sufficient for
the complete even bracket.  This is the codimension-one Schur target left by
the positive cosh rank; no lossy lower operator occurs. -/
theorem fourCell_evenBracket_nonnegative_of_normalizedCoshSchur
    (w p : ℝ → ℝ) (hw : Continuous w) (hp : Continuous p)
    (hweven : Function.Even w) (hpeven : Function.Even p)
    (hresLocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1)
      (fourCellEvenCoshResidual w p))
    (hpMoment :
      fourCellPositiveCoshMoment p (fourCellOperatorHalfWidth / 2) = 1)
    (hlow : 0 ≤
      centeredClippedPhysicalQuadratic fourCellOperatorHalfWidth
          (fourCellEvenCoshLow w p) -
        Real.sqrt 2 * Real.log 2 *
          fourCellEndpointPairing (fourCellEvenCoshLow w p))
    (htail : 0 ≤ fourCellEvenPolarFreeOperator
      (fourCellEvenCoshResidual w p))
    (hdet : fourCellExactBracketPolarization
          (fourCellEvenCoshLow w p) (fourCellEvenCoshResidual w p) ^ 2 ≤
      (centeredClippedPhysicalQuadratic fourCellOperatorHalfWidth
            (fourCellEvenCoshLow w p) -
          Real.sqrt 2 * Real.log 2 *
            fourCellEndpointPairing (fourCellEvenCoshLow w p)) *
        fourCellEvenPolarFreeOperator (fourCellEvenCoshResidual w p)) :
    0 ≤ centeredClippedPhysicalQuadratic fourCellOperatorHalfWidth w -
      Real.sqrt 2 * Real.log 2 * fourCellEndpointPairing w := by
  let u := fourCellEvenCoshLow w p
  let v := fourCellEvenCoshResidual w p
  have hu : Continuous u := fourCellEvenCoshLow_continuous w p hp
  have hv : Continuous v := fourCellEvenCoshResidual_continuous w p hw hp
  have hveven : Function.Even v :=
    fourCellEvenCoshResidual_even w p hweven hpeven
  have hvMoment :
      fourCellPositiveCoshMoment v (fourCellOperatorHalfWidth / 2) = 0 :=
    fourCellPositiveCoshMoment_residual_eq_zero w p hw hp hpMoment
  have htailEq :
      centeredClippedPhysicalQuadratic fourCellOperatorHalfWidth v -
          Real.sqrt 2 * Real.log 2 * fourCellEndpointPairing v =
        fourCellEvenPolarFreeOperator v := by
    rw [fourCell_evenBracket_eq_polarFree_add_coshRank
      v hv hresLocal hveven, hvMoment]
    ring
  have hsum := fourCell_evenBracket_add_nonnegative_of_exactSchur
    u v hu hv hlow (by simpa only [v, htailEq] using htail) (by
      simpa only [u, v, htailEq] using hdet)
  rw [fourCellEvenCoshResidual_decomposition w p] at hsum
  exact hsum

/-- Canonical one-dimensional Schur reduction for the universal even
four-cell problem.  The low pivot is now unconditional; precisely two
analytic obligations remain: polar-free coercivity on the zero-cosh residual
and its exact mixed determinant. -/
theorem fourCell_evenBracket_nonnegative_of_canonicalCoshSchur
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hweven : Function.Even w)
    (htail : 0 ≤ fourCellEvenPolarFreeOperator
      (fourCellEvenCoshResidual w fourCellEvenCoshUnit))
    (hdet : fourCellExactBracketPolarization
          (fourCellEvenCoshLow w fourCellEvenCoshUnit)
          (fourCellEvenCoshResidual w fourCellEvenCoshUnit) ^ 2 ≤
      (centeredClippedPhysicalQuadratic fourCellOperatorHalfWidth
            (fourCellEvenCoshLow w fourCellEvenCoshUnit) -
          Real.sqrt 2 * Real.log 2 *
            fourCellEndpointPairing
              (fourCellEvenCoshLow w fourCellEvenCoshUnit)) *
        fourCellEvenPolarFreeOperator
          (fourCellEvenCoshResidual w fourCellEvenCoshUnit)) :
    0 ≤ centeredClippedPhysicalQuadratic fourCellOperatorHalfWidth w -
      Real.sqrt 2 * Real.log 2 * fourCellEndpointPairing w := by
  have hresLocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1)
      (fourCellEvenCoshResidual w fourCellEvenCoshUnit) := by
    have hres : ContDiff ℝ 1
        (fourCellEvenCoshResidual w fourCellEvenCoshUnit) := by
      unfold fourCellEvenCoshResidual fourCellEvenCoshLow
        fourCellEvenCoshUnit
      fun_prop
    exact hres.contDiffOn.locallyLipschitzOn (convex_Icc (-1 : ℝ) 1)
  exact fourCell_evenBracket_nonnegative_of_normalizedCoshSchur
    w fourCellEvenCoshUnit hw.continuous fourCellEvenCoshUnit_continuous
      hweven fourCellEvenCoshUnit_even hresLocal
      fourCellPositiveCoshMoment_unit
      (fourCell_evenBracket_coshLow_nonnegative w) htail hdet

end

end ArithmeticHodge.Analysis.YoshidaFourCellEvenPolarSchurStructural

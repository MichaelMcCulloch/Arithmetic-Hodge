import ArithmeticHodge.Analysis.YoshidaFourCellOddP11UniversalCoreCauchyStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP11CrossSquareExtensionStructural

noncomputable section

open CenteredOddOneThreeEnergy
open YoshidaEndpointOcticPotential
open YoshidaEndpointWeightedCauchy
open YoshidaFourCellOddP11FormDualProbeStructural
open YoshidaFourCellOddP11UniversalCoreCauchyStructural
open YoshidaFourCellOddStripCapacityClosureStructural
open YoshidaFourCellParityHalfFoldStructural

/-!
# The cross-square extension row

The inverse-cube cross square is invariant under adding a multiple of the
Legendre `P₁` profile.  Applying the existing zero-`P₁` estimate to the
canonical Legendre residual therefore controls the deviation of the lower
`P₁` moment from the global `P₁` coefficient without any orthogonality
assumption on the original profile.

Combining this invariant square with the no-`P₁`-assumption global core
margin gives a quantitative extension-row estimate.  In particular, the
complete core controls a strictly positive multiple of the otherwise
uncontrolled Legendre `P₁` coefficient, modulo only lower-strip mass.  The
last theorem specializes this estimate to the actual core-orthogonal Schur
residual plane.
-/

/-- Subtracting the global Legendre `P₁` projection leaves the cross
ground-state square unchanged pointwise. -/
theorem fourCellOddCrossP1Square_p1Residual
    (w : ℝ → ℝ) :
    fourCellOddCrossP1Square (fourCellOddP1Residual w) =
      fourCellOddCrossP1Square w := by
  unfold fourCellOddCrossP1Square
  apply intervalIntegral.integral_congr
  intro x _hx
  apply intervalIntegral.integral_congr
  intro y _hy
  unfold fourCellOddP1Residual centeredP1
  ring

/-- The lower `P₁` moment of the canonical residual is exactly the lower
moment's deviation from the global Legendre coefficient. -/
theorem lowerP1Moment_p1Residual
    (w : ℝ → ℝ) (hw : Continuous w) :
    (∫ x : ℝ in 0..3 / 5, x * fourCellOddP1Residual w x) =
      (∫ x : ℝ in 0..3 / 5, x * w x) -
        (9 / 125 : ℝ) * centeredOddP1Coefficient w := by
  have hfirst : IntervalIntegrable (fun x : ℝ ↦ x * w x)
      volume 0 (3 / 5) := (continuous_id.mul hw).intervalIntegrable _ _
  have hsecond : IntervalIntegrable
      (fun x : ℝ ↦ centeredOddP1Coefficient w * x ^ 2)
      volume 0 (3 / 5) := by
    exact (continuous_const.mul (continuous_id.pow 2)).intervalIntegrable _ _
  rw [show (fun x : ℝ ↦ x * fourCellOddP1Residual w x) =
      fun x ↦ x * w x - centeredOddP1Coefficient w * x ^ 2 by
    funext x
    unfold fourCellOddP1Residual centeredP1
    ring,
    intervalIntegral.integral_sub hfirst hsecond,
    intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  ring

private theorem lowerP1Moment_sq_le_lowerMass
    (w : ℝ → ℝ) (hw : Continuous w) :
    (∫ x : ℝ in 0..3 / 5, x * w x) ^ 2 ≤
      (9 / 125 : ℝ) * (∫ x : ℝ in 0..3 / 5, w x ^ 2) := by
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) (3 / 5))
  have hxMeas : AEStronglyMeasurable (fun x : ℝ ↦ x) μ :=
    continuous_id.aestronglyMeasurable.restrict
  have hwMeas : AEStronglyMeasurable w μ :=
    hw.aestronglyMeasurable.restrict
  have hxLp : MemLp (fun x : ℝ ↦ x) 2 μ := by
    rw [memLp_two_iff_integrable_sq_norm hxMeas]
    have hcompact : IntegrableOn (fun x : ℝ ↦ ‖x‖ ^ 2)
        (Icc (0 : ℝ) (3 / 5)) :=
      (continuous_norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
    exact hcompact.mono_set Ioc_subset_Icc_self
  have hwLp : MemLp w 2 μ := by
    rw [memLp_two_iff_integrable_sq_norm hwMeas]
    have hcompact : IntegrableOn (fun x : ℝ ↦ ‖w x‖ ^ 2)
        (Icc (0 : ℝ) (3 / 5)) :=
      (hw.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
    exact hcompact.mono_set Ioc_subset_Icc_self
  have hcauchy := sq_integral_mul_le_weighted μ (fun _ : ℝ ↦ 1)
    (fun x : ℝ ↦ x) w (by simp) (by simpa using hxLp)
      (by simpa using hwLp)
  have hcauchy' :
      (∫ x : ℝ in 0..3 / 5, x * w x) ^ 2 ≤
        (∫ x : ℝ in 0..3 / 5, x ^ 2) *
          (∫ x : ℝ in 0..3 / 5, w x ^ 2) := by
    repeat rw [intervalIntegral.integral_of_le (by norm_num)]
    simpa only [μ, div_one, one_mul] using hcauchy
  have hx2 : (∫ x : ℝ in 0..3 / 5, x ^ 2) = 9 / 125 := by
    rw [integral_pow]
    norm_num
  rw [hx2] at hcauchy'
  exact hcauchy'

private theorem sq_upperP1Moment_le_invCubeMass_extension
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

/-- Exact weighted-Cauchy constant for the cross-square extension row.  Here
`M` is the complete positive-half `P₁` moment and `A` its lower-strip
part.  No parity or moment hypothesis is needed. -/
theorem exact_globalLowerP1Deviation_sq_le_crossP1Square
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) :
    (3375 / 3724 : ℝ) *
        ((∫ x : ℝ in 0..1, x * w x) -
          (125 / 27 : ℝ) * (∫ x : ℝ in 0..3 / 5, x * w x)) ^ 2 ≤
      fourCellOddCrossP1Square w := by
  let A : ℝ := ∫ x : ℝ in 0..3 / 5, x * w x
  let M : ℝ := ∫ x : ℝ in 0..1, x * w x
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
    have hcauchy := lowerP1Moment_sq_le_lowerMass
      (fun y ↦ y * w x - x * w y) (by fun_prop)
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
    rw [hmoment] at hcauchy
    nlinarith
  have hlowerInt : IntervalIntegrable (fun x : ℝ ↦ x * w x)
      volume 0 (3 / 5) := (by fun_prop : Continuous (fun x : ℝ ↦ x * w x))
        |>.intervalIntegrable _ _
  have hupperInt : IntervalIntegrable (fun x : ℝ ↦ x * w x)
      volume (3 / 5) 1 := (by fun_prop : Continuous (fun x : ℝ ↦ x * w x))
        |>.intervalIntegrable _ _
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    hlowerInt hupperInt
  have hupperMoment :
      (∫ x : ℝ in 3 / 5..1, x * w x) = M - A := by
    dsimp only [M, A]
    linarith
  have hx2 : (∫ x : ℝ in 3 / 5..1, x ^ 2) = 98 / 375 := by
    rw [integral_pow]
    norm_num
  have hhMoment :
      (∫ x : ℝ in 3 / 5..1, x * h x) =
        M - (125 / 27 : ℝ) * A := by
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
  have houter := sq_upperP1Moment_le_invCubeMass_extension h hh
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
    rw [hrightEq, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on_of_le_Ioo
      (by norm_num) hleftInt
    · apply ContinuousOn.intervalIntegrable
      have hinnerContinuous : Continuous (fun x : ℝ ↦
          ∫ y : ℝ in 0..3 / 5, (y * w x - x * w y) ^ 2) := by
        fun_prop
      apply ContinuousOn.mul
      · apply ContinuousOn.div continuousOn_const
          (by fun_prop : Continuous (fun x : ℝ ↦ x ^ 3)).continuousOn
        intro x hx
        rw [uIcc_of_le (by norm_num : (3 / 5 : ℝ) ≤ 1)] at hx
        exact pow_ne_zero 3 (by linarith [hx.1] : x ≠ 0)
      · exact hinnerContinuous.continuousOn
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
  dsimp only [A, M] at houter ⊢
  nlinarith

/-- For an odd profile the global positive-half `P₁` moment is one third
of its normalized Legendre coefficient. -/
theorem positiveHalfP1Moment_eq_one_third_coefficient
    (w : ℝ → ℝ) (hw : Continuous w) (hodd : Function.Odd w) :
    (∫ x : ℝ in 0..1, x * w x) =
      (1 / 3 : ℝ) * centeredOddP1Coefficient w := by
  have heven : Function.Even (fun x : ℝ ↦ w x * centeredP1 x) := by
    intro x
    change w (-x) * centeredP1 (-x) = w x * centeredP1 x
    rw [hodd]
    unfold centeredP1
    ring
  have hfold := integral_neg_one_one_eq_two_mul_zero_one_of_even
    (fun x : ℝ ↦ w x * centeredP1 x)
    ((hw.mul (by unfold centeredP1; fun_prop)).intervalIntegrable _ _)
    heven
  have hfull := integral_mul_centeredP1_eq w
  unfold centeredP1 at hfold hfull
  rw [show (fun x : ℝ ↦ w x * x) = fun x ↦ x * w x by
    funext x
    ring] at hfold hfull
  linarith

/-- Exact deviation version of the cross-square estimate in normalized
Legendre coordinates.  The coefficient is
`(3375/3724)*(125/27)^2 = 1953125/100548`, strictly larger than `19`. -/
theorem exact_lowerP1Deviation_sq_le_crossP1Square
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w) :
    (1953125 / 100548 : ℝ) *
        ((∫ x : ℝ in 0..3 / 5, x * w x) -
          (9 / 125 : ℝ) * centeredOddP1Coefficient w) ^ 2 ≤
      fourCellOddCrossP1Square w := by
  have h := exact_globalLowerP1Deviation_sq_le_crossP1Square w hw
  rw [positiveHalfP1Moment_eq_one_third_coefficient
    w hw.continuous hodd] at h
  convert h using 1
  all_goals ring

/-- The cross square controls the lower/global `P₁` deviation for every
smooth odd profile.  This is the assumption-free extension of
`nineteen_mul_lowerP1Moment_sq_le_crossP1Square`. -/
theorem nineteen_mul_lowerP1Deviation_sq_le_crossP1Square
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w) :
    19 * ((∫ x : ℝ in 0..3 / 5, x * w x) -
        (9 / 125 : ℝ) * centeredOddP1Coefficient w) ^ 2 ≤
      fourCellOddCrossP1Square w := by
  let v := fourCellOddP1Residual w
  have hv : ContDiff ℝ 1 v := by
    dsimp only [v]
    exact contDiff_fourCellOddP1Residual w hw
  have hvodd : Function.Odd v := by
    dsimp only [v]
    exact odd_fourCellOddP1Residual w hodd
  have hvone : centeredOddP1Coefficient v = 0 := by
    dsimp only [v]
    exact centeredOddP1Coefficient_fourCellOddP1Residual_eq_zero
      w hw.continuous
  have hcross := nineteen_mul_lowerP1Moment_sq_le_crossP1Square
    v hv hvodd hvone
  rw [show (∫ x : ℝ in 0..3 / 5, x * v x) =
      (∫ x : ℝ in 0..3 / 5, x * w x) -
        (9 / 125 : ℝ) * centeredOddP1Coefficient w by
    dsimp only [v]
    exact lowerP1Moment_p1Residual w hw.continuous,
    show fourCellOddCrossP1Square v = fourCellOddCrossP1Square w by
      dsimp only [v]
      exact fourCellOddCrossP1Square_p1Residual w] at hcross
  exact hcross

/-- The global no-orthogonality core margin with the invariant cross square
converted into an explicit lower/global `P₁` deviation. -/
theorem lowerP1DeviationRefinedGlobalMargin_le_core
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w) :
    (61 / 150 : ℝ) * (∫ x : ℝ in 0..3 / 5, w x ^ 2) +
        (13 / 20000 : ℝ) * (∫ x : ℝ in 0..1, w x ^ 2) -
        (625 / 27 : ℝ) * (∫ x : ℝ in 0..3 / 5, x * w x) ^ 2 +
        19 * ((∫ x : ℝ in 0..3 / 5, x * w x) -
          (9 / 125 : ℝ) * centeredOddP1Coefficient w) ^ 2 ≤
      fourCellOddCoreLocalQuadratic w := by
  have hrefined := lowerP1RefinedGlobalMargin_le_core_add_localWidthDefect
    w hw hodd
  have hcross := nineteen_mul_lowerP1Deviation_sq_le_crossP1Square
    w hw hodd
  unfold fourCellOddCoreLocalQuadratic
  linarith

/-- Exact-constant form of the preceding global margin. -/
theorem exact_lowerP1DeviationRefinedGlobalMargin_le_core
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w) :
    (61 / 150 : ℝ) * (∫ x : ℝ in 0..3 / 5, w x ^ 2) +
        (13 / 20000 : ℝ) * (∫ x : ℝ in 0..1, w x ^ 2) -
        (625 / 27 : ℝ) * (∫ x : ℝ in 0..3 / 5, x * w x) ^ 2 +
        (1953125 / 100548 : ℝ) *
          ((∫ x : ℝ in 0..3 / 5, x * w x) -
            (9 / 125 : ℝ) * centeredOddP1Coefficient w) ^ 2 ≤
      fourCellOddCoreLocalQuadratic w := by
  have hrefined := lowerP1RefinedGlobalMargin_le_core_add_localWidthDefect
    w hw hodd
  have hcross := exact_lowerP1Deviation_sq_le_crossP1Square w hw hodd
  unfold fourCellOddCoreLocalQuadratic
  linarith

/-- Sharp completion of the exact cross-square coefficient when the
lower-strip debit is fixed at `4/3`.  The coefficient `4125/822214` is the
Schur complement of the two scalar variables `A` and `c₁`; no rounding is
used. -/
theorem sharp_P1Coefficient_sq_sub_four_thirds_lowerMass_le_core
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w) :
    (4125 / 822214 : ℝ) * centeredOddP1Coefficient w ^ 2 -
        (4 / 3 : ℝ) * (∫ x : ℝ in 0..3 / 5, w x ^ 2) ≤
      fourCellOddCoreLocalQuadratic w := by
  let L : ℝ := ∫ x : ℝ in 0..3 / 5, w x ^ 2
  let H : ℝ := ∫ x : ℝ in 0..1, w x ^ 2
  let A : ℝ := ∫ x : ℝ in 0..3 / 5, x * w x
  let c : ℝ := centeredOddP1Coefficient w
  let D : ℝ := A - (9 / 125 : ℝ) * c
  have hrefined := exact_lowerP1DeviationRefinedGlobalMargin_le_core
    w hw hodd
  have hmoment := lowerP1Moment_sq_le_lowerMass w hw.continuous
  have hH : 0 ≤ H := by
    dsimp only [H]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun x _hx ↦ sq_nonneg (w x))
  have halgebra :
      (55 / 54 : ℝ) * A ^ 2 +
          (1953125 / 100548 : ℝ) * D ^ 2 -
            (4125 / 822214 : ℝ) * c ^ 2 =
        (2055535 / 100548 : ℝ) *
          (A - (28125 / 411107 : ℝ) * c) ^ 2 := by
    dsimp only [D]
    ring
  have hquadratic :
      0 ≤ (55 / 54 : ℝ) * A ^ 2 +
          (1953125 / 100548 : ℝ) * D ^ 2 -
            (4125 / 822214 : ℝ) * c ^ 2 := by
    rw [halgebra]
    positivity
  change (61 / 150 : ℝ) * L + (13 / 20000 : ℝ) * H -
      (625 / 27 : ℝ) * A ^ 2 +
        (1953125 / 100548 : ℝ) * D ^ 2 ≤
          fourCellOddCoreLocalQuadratic w at hrefined
  change A ^ 2 ≤ (9 / 125 : ℝ) * L at hmoment
  change (4125 / 822214 : ℝ) * c ^ 2 - (4 / 3 : ℝ) * L ≤
    fourCellOddCoreLocalQuadratic w
  nlinarith

/-- A quantitative extension-row lower bound on the complete odd core.
Unlike the earlier coercivity theorem, this retains a strictly positive
multiple of a nonzero Legendre `P₁` coefficient.  Its only debit is the
physical lower-strip mass. -/
theorem one_two_hundredth_P1Coefficient_sq_sub_four_thirds_lowerMass_le_core
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w) :
    (1 / 200 : ℝ) * centeredOddP1Coefficient w ^ 2 -
        (4 / 3 : ℝ) * (∫ x : ℝ in 0..3 / 5, w x ^ 2) ≤
      fourCellOddCoreLocalQuadratic w := by
  have hsharp := sharp_P1Coefficient_sq_sub_four_thirds_lowerMass_le_core
    w hw hodd
  nlinarith [sq_nonneg (centeredOddP1Coefficient w)]

/-- The cross-square extension estimate closes the coefficient-dominant
region outright.  Thus any still-negative core-orthogonal direction must
carry more lower-strip mass than the displayed threshold. -/
theorem fourCellOddCoreLocalQuadratic_nonneg_of_lowerMass_le_P1Coefficient
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w)
    (hregion :
      (∫ x : ℝ in 0..3 / 5, w x ^ 2) ≤
        (3 / 800 : ℝ) * centeredOddP1Coefficient w ^ 2) :
    0 ≤ fourCellOddCoreLocalQuadratic w := by
  have hbound :=
    one_two_hundredth_P1Coefficient_sq_sub_four_thirds_lowerMass_le_core
      w hw hodd
  nlinarith

/-- Exact coefficient-dominant region obtained from the sharp scalar Schur
completion. -/
theorem fourCellOddCoreLocalQuadratic_nonneg_of_lowerMass_le_sharpP1Coefficient
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w)
    (hregion :
      (∫ x : ℝ in 0..3 / 5, w x ^ 2) ≤
        (12375 / 3288856 : ℝ) * centeredOddP1Coefficient w ^ 2) :
    0 ≤ fourCellOddCoreLocalQuadratic w := by
  have hbound := sharp_P1Coefficient_sq_sub_four_thirds_lowerMass_le_core
    w hw hodd
  nlinarith

/-- Sharp scalar obstruction left by this mechanism: a negative direction
must lie strictly outside the coefficient-dominant region. -/
theorem lowerMass_gt_P1Coefficient_threshold_of_core_negative
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w)
    (hneg : fourCellOddCoreLocalQuadratic w < 0) :
    (3 / 800 : ℝ) * centeredOddP1Coefficient w ^ 2 <
      ∫ x : ℝ in 0..3 / 5, w x ^ 2 := by
  have hbound :=
    one_two_hundredth_P1Coefficient_sq_sub_four_thirds_lowerMass_le_core
      w hw hodd
  nlinarith

/-- Exact complementary obstruction: every negative direction must have
strictly more lower-strip mass than the sharp coefficient threshold. -/
theorem lowerMass_gt_sharpP1Coefficient_threshold_of_core_negative
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w)
    (hneg : fourCellOddCoreLocalQuadratic w < 0) :
    (12375 / 3288856 : ℝ) * centeredOddP1Coefficient w ^ 2 <
      ∫ x : ℝ in 0..3 / 5, w x ^ 2 := by
  have hbound := sharp_P1Coefficient_sq_sub_four_thirds_lowerMass_le_core
    w hw hodd
  nlinarith

/-- The explicit core-orthogonal Schur pencil inherits direct control of
its nonzero Legendre `P₁` extension row.  This is strictly stronger than
the row-zero coercivity line: no cancellation of the displayed row is
assumed. -/
theorem universalCorePencil_extensionRow_control
    (d e f g s t : ℝ) (r : ℝ → ℝ)
    (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r)
    (h1 : centeredOddP1Coefficient r = 0) :
    (4125 / 822214 : ℝ) *
          (s * fourCellOddCoreLocalBilinear centeredP1
              (fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g) +
            t * fourCellOddCoreLocalBilinear centeredP1 r) ^ 2 -
        (4 / 3 : ℝ) *
          (∫ x : ℝ in 0..3 / 5,
            fourCellOddP11UniversalCorePencilProfile
              d e f g s t r x ^ 2) ≤
      fourCellOddCoreLocalQuadratic
        (fourCellOddP11UniversalCorePencilProfile d e f g s t r) := by
  let w := fourCellOddP11UniversalCorePencilProfile d e f g s t r
  have hw : ContDiff ℝ 1 w := by
    dsimp only [w]
    exact contDiff_fourCellOddP11UniversalCorePencilProfile
      d e f g s t r hr
  have hwodd : Function.Odd w := by
    dsimp only [w]
    exact odd_fourCellOddP11UniversalCorePencilProfile
      d e f g s t r hodd
  have hbound :=
    sharp_P1Coefficient_sq_sub_four_thirds_lowerMass_le_core
      w hw hwodd
  have hcoeff := centeredOddP1Coefficient_universalCorePencilProfile
    d e f g s t r hr h1
  dsimp only [w] at hbound hcoeff ⊢
  rw [hcoeff] at hbound
  simpa only [neg_sq] using hbound

/-- Concrete nonnegativity region on the genuine core-orthogonal Schur
residual plane. -/
theorem universalCorePencil_nonnegative_of_lowerMass_le_extensionRow
    (d e f g s t : ℝ) (r : ℝ → ℝ)
    (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r)
    (h1 : centeredOddP1Coefficient r = 0)
    (hregion :
      (∫ x : ℝ in 0..3 / 5,
          fourCellOddP11UniversalCorePencilProfile d e f g s t r x ^ 2) ≤
        (12375 / 3288856 : ℝ) *
          (s * fourCellOddCoreLocalBilinear centeredP1
              (fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g) +
            t * fourCellOddCoreLocalBilinear centeredP1 r) ^ 2) :
    0 ≤ fourCellOddCoreLocalQuadratic
      (fourCellOddP11UniversalCorePencilProfile d e f g s t r) := by
  let w := fourCellOddP11UniversalCorePencilProfile d e f g s t r
  have hw : ContDiff ℝ 1 w := by
    dsimp only [w]
    exact contDiff_fourCellOddP11UniversalCorePencilProfile
      d e f g s t r hr
  have hwodd : Function.Odd w := by
    dsimp only [w]
    exact odd_fourCellOddP11UniversalCorePencilProfile
      d e f g s t r hodd
  have hcoeff := centeredOddP1Coefficient_universalCorePencilProfile
    d e f g s t r hr h1
  apply fourCellOddCoreLocalQuadratic_nonneg_of_lowerMass_le_sharpP1Coefficient
    w hw hwodd
  dsimp only [w] at hcoeff hregion ⊢
  rw [hcoeff]
  simpa only [neg_sq] using hregion

/-- Exact scalar obstruction on the actual core-orthogonal Schur plane.
Any negative pencil direction must violate the preceding coefficient-region
criterion strictly. -/
theorem universalCorePencil_lowerMass_gt_extensionRow_of_negative
    (d e f g s t : ℝ) (r : ℝ → ℝ)
    (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r)
    (h1 : centeredOddP1Coefficient r = 0)
    (hneg : fourCellOddCoreLocalQuadratic
      (fourCellOddP11UniversalCorePencilProfile d e f g s t r) < 0) :
    (12375 / 3288856 : ℝ) *
          (s * fourCellOddCoreLocalBilinear centeredP1
              (fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g) +
            t * fourCellOddCoreLocalBilinear centeredP1 r) ^ 2 <
      ∫ x : ℝ in 0..3 / 5,
        fourCellOddP11UniversalCorePencilProfile d e f g s t r x ^ 2 := by
  let w := fourCellOddP11UniversalCorePencilProfile d e f g s t r
  have hw : ContDiff ℝ 1 w := by
    dsimp only [w]
    exact contDiff_fourCellOddP11UniversalCorePencilProfile
      d e f g s t r hr
  have hwodd : Function.Odd w := by
    dsimp only [w]
    exact odd_fourCellOddP11UniversalCorePencilProfile
      d e f g s t r hodd
  have hcoeff := centeredOddP1Coefficient_universalCorePencilProfile
    d e f g s t r hr h1
  have hobstruction :=
    lowerMass_gt_sharpP1Coefficient_threshold_of_core_negative
      w hw hwodd hneg
  dsimp only [w] at hcoeff hobstruction ⊢
  rw [hcoeff] at hobstruction
  simpa only [neg_sq] using hobstruction

/-- Every direction controlled above is simultaneously orthogonal to `P₁`
for the complete core form. -/
theorem universalCorePencil_coreOrthogonal_and_extensionRow_control
    (d e f g s t : ℝ) (r : ℝ → ℝ)
    (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r)
    (h1 : centeredOddP1Coefficient r = 0) :
    fourCellOddCoreLocalBilinear centeredP1
          (fourCellOddP11UniversalCorePencilProfile d e f g s t r) = 0 ∧
      (4125 / 822214 : ℝ) *
            (s * fourCellOddCoreLocalBilinear centeredP1
                (fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g) +
              t * fourCellOddCoreLocalBilinear centeredP1 r) ^ 2 -
          (4 / 3 : ℝ) *
            (∫ x : ℝ in 0..3 / 5,
              fourCellOddP11UniversalCorePencilProfile
                d e f g s t r x ^ 2) ≤
        fourCellOddCoreLocalQuadratic
          (fourCellOddP11UniversalCorePencilProfile d e f g s t r) := by
  constructor
  · exact
      fourCellOddCoreLocalBilinear_centeredP1_universalCorePencilProfile_eq_zero
        d e f g s t r hr hodd
  · exact universalCorePencil_extensionRow_control
      d e f g s t r hr hodd h1

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP11CrossSquareExtensionStructural

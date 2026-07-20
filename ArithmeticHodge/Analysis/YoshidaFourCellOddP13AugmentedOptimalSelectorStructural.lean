import ArithmeticHodge.Analysis.YoshidaFourCellOddP13AugmentedResidualRepresenterStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddP13AugmentedFiniteSolveStructural

set_option autoImplicit false

open MeasureTheory Polynomial Real Set
open scoped Interval

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP13AugmentedOptimalSelectorStructural

noncomputable section

open CenteredOddOneThreeEnergy
open YoshidaEndpointOcticPotential
open YoshidaEndpointOddResidualRegularity
open YoshidaEndpointPotentialBound
open YoshidaFactorTwoContinuousLagRepresenterStructural
open YoshidaFactorTwoIntegrableLagRepresenterStructural
open YoshidaFourCellOddP11GalerkinResidualDualDirectStructural
open YoshidaFourCellOddP13AugmentedDecompositionStructural
open YoshidaFourCellOddP13AugmentedFiniteSolveStructural
open YoshidaFourCellOddP13AugmentedGalerkinRieszStructural
open YoshidaFourCellOddP13AugmentedResidualRepresenterStructural
open YoshidaFourCellOddStripCapacityClosureStructural
open YoshidaFourCellParityHalfFoldStructural
open YoshidaFourCellParityOperatorStructural
open YoshidaRegularKernelBound

/-!
# Optimal shared six-mode selector for the augmented odd residual

The lower and upper endpoint strips carry two different exact row densities,
but the quotient uses one selector on their union.  This file constructs the
orthogonal projection of that piecewise density onto
`P1/P3/P5/P7/P9/P11`.  Its coefficients are the six exact split moments,
and the residual norm satisfies an exact Pythagorean identity.
-/

/-- Lower-strip row density for fixed augmented Galerkin coefficients. -/
def fourCellOddP13AugmentedLowerRow
    (a3 a5 a7 a9 a11 : ℝ) : ℝ → ℝ :=
  fourCellOddP13SixModeLowerRepresenter
    1 (-a3) (-a5) (-a7) (-a9) (-a11)

/-- Upper-strip row density for fixed augmented Galerkin coefficients. -/
def fourCellOddP13AugmentedUpperRow
    (a3 a5 a7 a9 a11 : ℝ) : ℝ → ℝ :=
  fourCellOddP13SixModeUpperRepresenter
    1 (-a3) (-a5) (-a7) (-a9) (-a11)

/-- Piecewise two-strip pairing with a test function. -/
def fourCellOddP13AugmentedTwoStripPair
    (a3 a5 a7 a9 a11 : ℝ) (q : ℝ → ℝ) : ℝ :=
  (∫ x : ℝ in 0..3 / 5,
      fourCellOddP13AugmentedLowerRow a3 a5 a7 a9 a11 x * q x) +
    ∫ x : ℝ in 3 / 5..1,
      fourCellOddP13AugmentedUpperRow a3 a5 a7 a9 a11 x * q x

/-- Squared two-strip norm of a lower/upper pair. -/
def fourCellOddP13TwoStripNormSq (L U : ℝ → ℝ) : ℝ :=
  (∫ x : ℝ in 0..3 / 5, L x ^ 2) +
    ∫ x : ℝ in 3 / 5..1, U x ^ 2

private theorem continuous_centeredP1_local : Continuous centeredP1 := by
  unfold centeredP1
  fun_prop

private theorem odd_centeredP1_local : Function.Odd centeredP1 := by
  intro x
  unfold centeredP1
  ring

private theorem integral_zero_one_centeredP1_mul_augmentedLow_eq_zero
    (d e f g h : ℝ) :
    (∫ x : ℝ in 0..1,
      centeredP1 x * fourCellOddP11AugmentedLowProfile d e f g h x) = 0 := by
  let u := fourCellOddP11AugmentedLowProfile d e f g h
  have hu : Continuous u :=
    (contDiff_fourCellOddP11AugmentedLowProfile d e f g h).continuous
  have huodd : Function.Odd u :=
    odd_fourCellOddP11AugmentedLowProfile d e f g h
  have hcoefficient :=
    centeredOddP1Coefficient_augmentedLowProfile_eq_zero d e f g h
  have hfull : (∫ x : ℝ in -1..1, centeredP1 x * u x) = 0 := by
    unfold centeredOddP1Coefficient at hcoefficient
    rw [show (fun x : ℝ ↦ centeredP1 x * u x) =
        fun x ↦ u x * centeredP1 x by
      funext x
      ring]
    nlinarith
  have hfold := integral_neg_one_one_eq_two_mul_zero_one_of_even
    (fun x : ℝ ↦ centeredP1 x * u x)
    ((continuous_centeredP1_local.mul hu).intervalIntegrable _ _)
    (by
      intro x
      change centeredP1 (-x) * u (-x) = centeredP1 x * u x
      rw [odd_centeredP1_local, huodd]
      ring)
  rw [hfull] at hfold
  dsimp only [u] at hfold ⊢
  linarith

private theorem integral_zero_one_centeredP1_sq_local :
    (∫ x : ℝ in 0..1, centeredP1 x ^ 2) = 1 / 3 := by
  have hfold := integral_sq_eq_two_mul_positiveHalf
    centeredP1 continuous_centeredP1_local (Or.inr odd_centeredP1_local)
  rw [YoshidaEndpointOcticTwoModeSchurData.integral_centeredP1_sq] at hfold
  linarith

/-- Exact positive-half mass of an arbitrary retained six-mode selector. -/
theorem integral_zero_one_fourCellOddP13SixModeSelector_sq
    (b1 b3 b5 b7 b9 b11 : ℝ) :
    (∫ x : ℝ in 0..1,
      fourCellOddP13SixModeSelector b1 b3 b5 b7 b9 b11 x ^ 2) =
      b1 ^ 2 / 3 + b3 ^ 2 / 7 + b5 ^ 2 / 11 +
        b7 ^ 2 / 15 + b9 ^ 2 / 19 + b11 ^ 2 / 23 := by
  let u := fourCellOddP11AugmentedLowProfile b3 b5 b7 b9 b11
  have hu : Continuous u :=
    (contDiff_fourCellOddP11AugmentedLowProfile b3 b5 b7 b9 b11).continuous
  have h1u := integral_zero_one_centeredP1_mul_augmentedLow_eq_zero
    b3 b5 b7 b9 b11
  have h11 : IntervalIntegrable (fun x : ℝ ↦ centeredP1 x ^ 2)
      volume 0 1 := (continuous_centeredP1_local.pow 2).intervalIntegrable _ _
  have h1uI : IntervalIntegrable (fun x : ℝ ↦ centeredP1 x * u x)
      volume 0 1 := (continuous_centeredP1_local.mul hu).intervalIntegrable _ _
  have huuI : IntervalIntegrable (fun x : ℝ ↦ u x ^ 2)
      volume 0 1 := (hu.pow 2).intervalIntegrable _ _
  rw [show fourCellOddP13SixModeSelector b1 b3 b5 b7 b9 b11 =
      fun x ↦ b1 * centeredP1 x + u x by
    funext x
    dsimp only [u]
    unfold fourCellOddP13SixModeSelector fourCellOddP13SixModeProfile
      fourCellOddP11AugmentedLowProfile
      fourCellOddOneThreeFiveSevenNineLowProfile
      fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
    ring]
  rw [show (fun x : ℝ ↦ (b1 * centeredP1 x + u x) ^ 2) =
      fun x ↦ b1 ^ 2 * centeredP1 x ^ 2 +
        2 * b1 * (centeredP1 x * u x) + u x ^ 2 by
    funext x
    ring,
    intervalIntegral.integral_add
      ((h11.const_mul _).add (h1uI.const_mul _)) huuI,
    intervalIntegral.integral_add (h11.const_mul _) (h1uI.const_mul _),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    integral_zero_one_centeredP1_sq_local, h1u,
    integral_zero_one_fourCellOddP11AugmentedLowProfile_sq]
  ring

/-- Exact positive-half Gram pairing of two retained six-mode selectors. -/
theorem integral_zero_one_fourCellOddP13SixModeSelector_mul
    (b1 b3 b5 b7 b9 b11 c1 c3 c5 c7 c9 c11 : ℝ) :
    (∫ x : ℝ in 0..1,
      fourCellOddP13SixModeSelector b1 b3 b5 b7 b9 b11 x *
        fourCellOddP13SixModeSelector c1 c3 c5 c7 c9 c11 x) =
      b1 * c1 / 3 + b3 * c3 / 7 + b5 * c5 / 11 +
        b7 * c7 / 15 + b9 * c9 / 19 + b11 * c11 / 23 := by
  let p := fourCellOddP13SixModeSelector b1 b3 b5 b7 b9 b11
  let q := fourCellOddP13SixModeSelector c1 c3 c5 c7 c9 c11
  have hp : Continuous p := by
    dsimp only [p, fourCellOddP13SixModeSelector]
    exact (contDiff_fourCellOddP13SixModeProfile _ _ _ _ _ _).continuous
  have hq : Continuous q := by
    dsimp only [q, fourCellOddP13SixModeSelector]
    exact (contDiff_fourCellOddP13SixModeProfile _ _ _ _ _ _).continuous
  rw [show (fun x : ℝ ↦ p x * q x) = fun x ↦
      (1 / 2 : ℝ) * ((p x + q x) ^ 2 - p x ^ 2 - q x ^ 2) by
    funext x
    ring,
    intervalIntegral.integral_const_mul]
  rw [show (fun x : ℝ ↦ (p x + q x) ^ 2 - p x ^ 2 - q x ^ 2) =
      fun x ↦ (p + q) x ^ 2 - p x ^ 2 - q x ^ 2 by
    funext x
    simp only [Pi.add_apply],
    intervalIntegral.integral_sub
      (((hp.add hq).pow 2 |>.intervalIntegrable _ _).sub
        (hp.pow 2 |>.intervalIntegrable _ _))
      (hq.pow 2 |>.intervalIntegrable _ _),
    intervalIntegral.integral_sub
      ((hp.add hq).pow 2 |>.intervalIntegrable _ _)
      (hp.pow 2 |>.intervalIntegrable _ _)]
  have hpq : p + q = fourCellOddP13SixModeSelector
      (b1 + c1) (b3 + c3) (b5 + c5) (b7 + c7) (b9 + c9) (b11 + c11) := by
    funext x
    dsimp only [p, q]
    unfold fourCellOddP13SixModeSelector fourCellOddP13SixModeProfile
      fourCellOddOneThreeFiveSevenNineLowProfile
      fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
    simp only [Pi.add_apply]
    ring
  rw [hpq,
    integral_zero_one_fourCellOddP13SixModeSelector_sq,
    show (∫ x : ℝ in 0..1, p x ^ 2) =
        b1 ^ 2 / 3 + b3 ^ 2 / 7 + b5 ^ 2 / 11 +
          b7 ^ 2 / 15 + b9 ^ 2 / 19 + b11 ^ 2 / 23 by
      dsimp only [p]
      exact integral_zero_one_fourCellOddP13SixModeSelector_sq _ _ _ _ _ _,
    show (∫ x : ℝ in 0..1, q x ^ 2) =
        c1 ^ 2 / 3 + c3 ^ 2 / 7 + c5 ^ 2 / 11 +
          c7 ^ 2 / 15 + c9 ^ 2 / 19 + c11 ^ 2 / 23 by
      dsimp only [q]
      exact integral_zero_one_fourCellOddP13SixModeSelector_sq _ _ _ _ _ _]
  ring

/-! ## Square-integrability of the exact two-strip rows -/

private theorem intervalIntegrable_log_sq_zero_one_local :
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

private theorem intervalIntegrable_log_sq_zero_two_local :
    IntervalIntegrable (fun x : ℝ ↦ Real.log x ^ 2) volume 0 2 := by
  apply intervalIntegrable_log_sq_zero_one_local.trans
  apply ContinuousOn.intervalIntegrable
  exact (Real.continuousOn_log.mono (by
    intro x hx
    rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at hx
    simp only [mem_compl_iff, mem_singleton_iff]
    linarith [hx.1])).pow 2

private theorem intervalIntegrable_endpointPotential_sq_local :
    IntervalIntegrable (fun x : ℝ ↦ yoshidaEndpointPotential x ^ 2)
      volume (-1) 1 := by
  have hlog := intervalIntegrable_log_sq_zero_two_local
  have hminus : IntervalIntegrable
      (fun x : ℝ ↦ Real.log (1 - x) ^ 2) volume (-1) 1 := by
    convert (hlog.comp_sub_left 1).symm using 1 <;> norm_num
  have hplus : IntervalIntegrable
      (fun x : ℝ ↦ Real.log (1 + x) ^ 2) volume (-1) 1 := by
    convert hlog.comp_add_left 1 using 1 <;> norm_num
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
    at hminus hplus ⊢
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

private theorem memLp_two_restrict_of_continuous_local
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

private theorem memLp_endpointPotential_mul_continuous_local
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
      intervalIntegrable_endpointPotential_sq_local.continuousOn_mul
        (hp.pow 2).continuousOn
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)] at hI
  apply hI.congr
  filter_upwards with x
  rw [Real.norm_eq_abs, sq_abs]
  ring

private theorem regularLag_abs_le_quarter_local
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 2) :
    |yoshidaRegularKernel (fourCellOperatorHalfWidth * t)| ≤ 1 / 4 := by
  have ha0 : 0 ≤ fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  have harg0 : 0 ≤ fourCellOperatorHalfWidth * t :=
    mul_nonneg ha0 ht.1
  have harg4 : fourCellOperatorHalfWidth * t ≤
      5 * Real.log 2 / 4 := by
    calc
      fourCellOperatorHalfWidth * t ≤ fourCellOperatorHalfWidth * 2 :=
        mul_le_mul_of_nonneg_left ht.2 ha0
      _ = 5 * Real.log 2 / 4 := by
        unfold fourCellOperatorHalfWidth
        ring
  have hk0 := yoshidaRegularKernel_nonneg_fourCellRange harg0 harg4
  rw [abs_of_nonneg hk0]
  exact yoshidaRegularKernel_le_quarter harg0

/-- The six-mode regular representer is genuinely `L²` on the centered
interval; this supplies the analytic legitimacy fields of the selector
certificate without assuming continuity at the removable lag singularity. -/
theorem memLp_fourCellOddP13SixModeRegularRepresenter_two_restrict
    (c d e f g h : ℝ) :
    MemLp (fourCellOddP13SixModeRegularRepresenter c d e f g h) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
  let k : ℝ → ℝ := fun t ↦
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t)
  let p : ℝ → ℝ := fourCellOddP13SixModeProfile c d e f g h
  have hkMeas : Measurable k := by
    dsimp only [k]
    exact measurable_yoshidaRegularKernel.comp
      (measurable_const.mul measurable_id)
  have hp : Continuous p := by
    dsimp only [p]
    exact (contDiff_fourCellOddP13SixModeProfile c d e f g h).continuous
  have hkBound : ∀ t ∈ Icc (0 : ℝ) 2, |k t| ≤ (1 / 4 : ℝ) := by
    intro t ht
    simpa only [k] using regularLag_abs_le_quarter_local t ht
  have hrightI :=
    intervalIntegrable_mul_factorTwoContinuousLagRightRepresenter_of_bounded
      k p (fun _ : ℝ ↦ 1) hkMeas hp continuous_const (1 / 4) hkBound
  have hleftI :=
    intervalIntegrable_mul_factorTwoContinuousLagLeftRepresenter_of_bounded
      k (fun _ : ℝ ↦ 1) p hkMeas continuous_const hp (1 / 4) hkBound
  have hKI : IntervalIntegrable (factorTwoContinuousLagK k p)
      volume (-1) 1 := by
    apply (hrightI.add hleftI).congr
    intro x _hx
    unfold factorTwoContinuousLagK
    simp only [one_mul]
  obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image hp.norm.continuousOn
  let B : ℝ := max 1 M
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left 1 M)
  have hpB : ∀ x ∈ Icc (-1 : ℝ) 1, ‖p x‖ ≤ B := by
    intro x hx
    exact (hM (Set.mem_image_of_mem _ hx)).trans (le_max_right 1 M)
  have hKBound : ∀ x ∈ Ioc (-1 : ℝ) 1,
      ‖factorTwoContinuousLagK k p x‖ ≤ B := by
    intro x hx
    have hrightPoint : ∀ y ∈ Ι x 1,
        ‖k (y - x) * p y‖ ≤ (1 / 4 : ℝ) * B := by
      intro y hy
      rw [uIoc_of_le hx.2] at hy
      have hyIcc : y ∈ Icc (-1 : ℝ) 1 :=
        ⟨by linarith [hx.1, hy.1], hy.2⟩
      have hlag : y - x ∈ Icc (0 : ℝ) 2 :=
        ⟨by linarith [hy.1], by linarith [hx.1, hy.2]⟩
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul (hkBound (y - x) hlag) (hpB y hyIcc)
        (norm_nonneg _) (by norm_num)
    have hleftPoint : ∀ y ∈ Ι (-1) x,
        ‖k (x - y) * p y‖ ≤ (1 / 4 : ℝ) * B := by
      intro y hy
      rw [uIoc_of_le hx.1.le] at hy
      have hyIcc : y ∈ Icc (-1 : ℝ) 1 :=
        ⟨hy.1.le, by linarith [hy.2, hx.2]⟩
      have hlag : x - y ∈ Icc (0 : ℝ) 2 :=
        ⟨by linarith [hy.2], by linarith [hy.1, hx.2]⟩
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul (hkBound (x - y) hlag) (hpB y hyIcc)
        (norm_nonneg _) (by norm_num)
    have hright :=
      intervalIntegral.norm_integral_le_of_norm_le_const hrightPoint
    have hleft :=
      intervalIntegral.norm_integral_le_of_norm_le_const hleftPoint
    have hright' :
        ‖factorTwoContinuousLagRightRepresenter k p x‖ ≤ B / 2 := by
      change ‖∫ y : ℝ in x..1, k (y - x) * p y‖ ≤ B / 2
      have hlen : |1 - x| ≤ 2 := by
        rw [abs_of_nonneg (by linarith [hx.2])]
        linarith [hx.1]
      nlinarith only [hright, hlen, hBpos]
    have hleft' :
        ‖factorTwoContinuousLagLeftRepresenter k p x‖ ≤ B / 2 := by
      change ‖∫ y : ℝ in -1..x, k (x - y) * p y‖ ≤ B / 2
      have hlen : |x - (-1)| ≤ 2 := by
        rw [abs_of_nonneg (by linarith [hx.1.le])]
        linarith [hx.2]
      nlinarith only [hleft, hlen, hBpos]
    unfold factorTwoContinuousLagK
    exact (norm_add_le _ _).trans (by linarith only [hright', hleft'])
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)] at hKI
  have hmeas : AEStronglyMeasurable (factorTwoContinuousLagK k p)
      (volume.restrict (Ioc (-1 : ℝ) 1)) := hKI.aestronglyMeasurable
  have hLp : MemLp (factorTwoContinuousLagK k p) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
    apply MemLp.of_bound hmeas B
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact hKBound x hx
  simpa only [k, p, fourCellOddP13SixModeRegularRepresenter] using hLp

/-- The exact lower augmented row is `L²` on the centered interval. -/
theorem memLp_fourCellOddP13AugmentedLowerRow_two_restrict
    (a3 a5 a7 a9 a11 : ℝ) :
    MemLp (fourCellOddP13AugmentedLowerRow a3 a5 a7 a9 a11) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
  let p : ℝ → ℝ :=
    fourCellOddP13SixModeProfile 1 (-a3) (-a5) (-a7) (-a9) (-a11)
  have hp : Continuous p := by
    dsimp only [p]
    exact (contDiff_fourCellOddP13SixModeProfile _ _ _ _ _ _).continuous
  have hpotential := memLp_endpointPotential_mul_continuous_local p hp
  have hregular := memLp_fourCellOddP13SixModeRegularRepresenter_two_restrict
    1 (-a3) (-a5) (-a7) (-a9) (-a11)
  unfold fourCellOddP13AugmentedLowerRow
    fourCellOddP13SixModeLowerRepresenter
  dsimp only [p] at hpotential
  simpa only [Pi.sub_apply, mul_assoc] using
    (hpotential.const_mul (93 / 50)).sub
      (hregular.const_mul (2 * fourCellOperatorHalfWidth))

/-- The exact upper augmented row is `L²` on the centered interval. -/
theorem memLp_fourCellOddP13AugmentedUpperRow_two_restrict
    (a3 a5 a7 a9 a11 : ℝ) :
    MemLp (fourCellOddP13AugmentedUpperRow a3 a5 a7 a9 a11) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
  let p : ℝ → ℝ :=
    fourCellOddP13SixModeProfile 1 (-a3) (-a5) (-a7) (-a9) (-a11)
  let reflected : ℝ → ℝ := fun x ↦ p (8 / 5 - x)
  have hp : Continuous p := by
    dsimp only [p]
    exact (contDiff_fourCellOddP13SixModeProfile _ _ _ _ _ _).continuous
  have hreflected : Continuous reflected := by
    dsimp only [reflected]
    fun_prop
  have hbase := memLp_fourCellOddP13AugmentedLowerRow_two_restrict
    a3 a5 a7 a9 a11
  have heven : MemLp (fun x : ℝ ↦ (p x + reflected x) / 2) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) :=
    memLp_two_restrict_of_continuous_local _
      ((hp.add hreflected).div_const 2)
  have hodd : MemLp (fun x : ℝ ↦ (p x - reflected x) / 2) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) :=
    memLp_two_restrict_of_continuous_local _
      ((hp.sub hreflected).div_const 2)
  have hraw : MemLp
      (fourCellOddP13SixModeRawUpperRepresenter
        1 (-a3) (-a5) (-a7) (-a9) (-a11)) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) :=
    memLp_two_restrict_of_continuous_local _
      (continuous_fourCellOddP13SixModeRawUpperRepresenter
        1 (-a3) (-a5) (-a7) (-a9) (-a11))
  unfold fourCellOddP13AugmentedUpperRow
    fourCellOddP13SixModeUpperRepresenter
  dsimp only [p, reflected] at heven hodd
  exact (((hbase.add
      (heven.const_mul (Real.sqrt 2 * Real.log 2))).add
        (hodd.const_mul (2 - Real.sqrt 2 * Real.log 2))).sub
          (hraw.const_mul (1 / 2)))

/-- Every lower selector residual is `L²`. -/
theorem memLp_fourCellOddP13AugmentedResidualLowerSelectorResidual_two_restrict
    (a3 a5 a7 a9 a11 b1 b3 b5 b7 b9 b11 : ℝ) :
    MemLp
      (fourCellOddP13AugmentedResidualLowerSelectorResidual
        a3 a5 a7 a9 a11 b1 b3 b5 b7 b9 b11) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
  have hrow := memLp_fourCellOddP13AugmentedLowerRow_two_restrict
    a3 a5 a7 a9 a11
  have hselector : MemLp
      (fourCellOddP13SixModeSelector b1 b3 b5 b7 b9 b11) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
    apply memLp_two_restrict_of_continuous_local
    unfold fourCellOddP13SixModeSelector
    exact (contDiff_fourCellOddP13SixModeProfile _ _ _ _ _ _).continuous
  simpa only [fourCellOddP13AugmentedLowerRow] using hrow.sub hselector

/-- Every upper selector residual is `L²`. -/
theorem memLp_fourCellOddP13AugmentedResidualUpperSelectorResidual_two_restrict
    (a3 a5 a7 a9 a11 b1 b3 b5 b7 b9 b11 : ℝ) :
    MemLp
      (fourCellOddP13AugmentedResidualUpperSelectorResidual
        a3 a5 a7 a9 a11 b1 b3 b5 b7 b9 b11) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
  have hrow := memLp_fourCellOddP13AugmentedUpperRow_two_restrict
    a3 a5 a7 a9 a11
  have hselector : MemLp
      (fourCellOddP13SixModeSelector b1 b3 b5 b7 b9 b11) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
    apply memLp_two_restrict_of_continuous_local
    unfold fourCellOddP13SixModeSelector
    exact (contDiff_fourCellOddP13SixModeProfile _ _ _ _ _ _).continuous
  simpa only [fourCellOddP13AugmentedUpperRow] using hrow.sub hselector

/-! ## Exact six-moment projection -/

private theorem intervalIntegrable_augmentedLowerRow_mul_sixModeSelector
    (a3 a5 a7 a9 a11 b1 b3 b5 b7 b9 b11 : ℝ) :
    IntervalIntegrable
      (fun x : ℝ ↦ fourCellOddP13AugmentedLowerRow a3 a5 a7 a9 a11 x *
        fourCellOddP13SixModeSelector b1 b3 b5 b7 b9 b11 x)
      volume 0 (3 / 5) := by
  have hrow := memLp_fourCellOddP13AugmentedLowerRow_two_restrict
    a3 a5 a7 a9 a11
  have hselector : MemLp
      (fourCellOddP13SixModeSelector b1 b3 b5 b7 b9 b11) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) :=
    memLp_two_restrict_of_continuous_local _
      ((contDiff_fourCellOddP13SixModeProfile _ _ _ _ _ _).continuous)
  have hprod := hrow.integrable_mul hselector
  have hfull : IntervalIntegrable
      (fun x : ℝ ↦ fourCellOddP13AugmentedLowerRow a3 a5 a7 a9 a11 x *
        fourCellOddP13SixModeSelector b1 b3 b5 b7 b9 b11 x)
      volume (-1) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
    simpa only [Pi.mul_apply] using hprod
  exact hfull.mono_set (by
    intro x hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 3 / 5)] at hx
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    constructor <;> linarith [hx.1, hx.2])

private theorem intervalIntegrable_augmentedUpperRow_mul_sixModeSelector
    (a3 a5 a7 a9 a11 b1 b3 b5 b7 b9 b11 : ℝ) :
    IntervalIntegrable
      (fun x : ℝ ↦ fourCellOddP13AugmentedUpperRow a3 a5 a7 a9 a11 x *
        fourCellOddP13SixModeSelector b1 b3 b5 b7 b9 b11 x)
      volume (3 / 5) 1 := by
  have hrow := memLp_fourCellOddP13AugmentedUpperRow_two_restrict
    a3 a5 a7 a9 a11
  have hselector : MemLp
      (fourCellOddP13SixModeSelector b1 b3 b5 b7 b9 b11) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) :=
    memLp_two_restrict_of_continuous_local _
      ((contDiff_fourCellOddP13SixModeProfile _ _ _ _ _ _).continuous)
  have hprod := hrow.integrable_mul hselector
  have hfull : IntervalIntegrable
      (fun x : ℝ ↦ fourCellOddP13AugmentedUpperRow a3 a5 a7 a9 a11 x *
        fourCellOddP13SixModeSelector b1 b3 b5 b7 b9 b11 x)
      volume (-1) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
    simpa only [Pi.mul_apply] using hprod
  exact hfull.mono_set (by
    intro x hx
    rw [uIcc_of_le (by norm_num : (3 / 5 : ℝ) ≤ 1)] at hx
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    constructor <;> linarith [hx.1, hx.2])

/-- Split `P1` moment of the exact augmented row. -/
def fourCellOddP13AugmentedSelectorMomentOne
    (a3 a5 a7 a9 a11 : ℝ) : ℝ :=
  fourCellOddP13AugmentedTwoStripPair a3 a5 a7 a9 a11
    (fourCellOddP13SixModeSelector 1 0 0 0 0 0)

/-- Split `P3` moment of the exact augmented row. -/
def fourCellOddP13AugmentedSelectorMomentThree
    (a3 a5 a7 a9 a11 : ℝ) : ℝ :=
  fourCellOddP13AugmentedTwoStripPair a3 a5 a7 a9 a11
    (fourCellOddP13SixModeSelector 0 1 0 0 0 0)

/-- Split `P5` moment of the exact augmented row. -/
def fourCellOddP13AugmentedSelectorMomentFive
    (a3 a5 a7 a9 a11 : ℝ) : ℝ :=
  fourCellOddP13AugmentedTwoStripPair a3 a5 a7 a9 a11
    (fourCellOddP13SixModeSelector 0 0 1 0 0 0)

/-- Split `P7` moment of the exact augmented row. -/
def fourCellOddP13AugmentedSelectorMomentSeven
    (a3 a5 a7 a9 a11 : ℝ) : ℝ :=
  fourCellOddP13AugmentedTwoStripPair a3 a5 a7 a9 a11
    (fourCellOddP13SixModeSelector 0 0 0 1 0 0)

/-- Split `P9` moment of the exact augmented row. -/
def fourCellOddP13AugmentedSelectorMomentNine
    (a3 a5 a7 a9 a11 : ℝ) : ℝ :=
  fourCellOddP13AugmentedTwoStripPair a3 a5 a7 a9 a11
    (fourCellOddP13SixModeSelector 0 0 0 0 1 0)

/-- Split `P11` moment of the exact augmented row. -/
def fourCellOddP13AugmentedSelectorMomentEleven
    (a3 a5 a7 a9 a11 : ℝ) : ℝ :=
  fourCellOddP13AugmentedTwoStripPair a3 a5 a7 a9 a11
    (fourCellOddP13SixModeSelector 0 0 0 0 0 1)

/-- The two-strip pairing is exactly the coordinate pairing with its six
Legendre moments. -/
theorem fourCellOddP13AugmentedTwoStripPair_sixModeSelector
    (a3 a5 a7 a9 a11 b1 b3 b5 b7 b9 b11 : ℝ) :
    fourCellOddP13AugmentedTwoStripPair a3 a5 a7 a9 a11
        (fourCellOddP13SixModeSelector b1 b3 b5 b7 b9 b11) =
      b1 * fourCellOddP13AugmentedSelectorMomentOne a3 a5 a7 a9 a11 +
      b3 * fourCellOddP13AugmentedSelectorMomentThree a3 a5 a7 a9 a11 +
      b5 * fourCellOddP13AugmentedSelectorMomentFive a3 a5 a7 a9 a11 +
      b7 * fourCellOddP13AugmentedSelectorMomentSeven a3 a5 a7 a9 a11 +
      b9 * fourCellOddP13AugmentedSelectorMomentNine a3 a5 a7 a9 a11 +
      b11 * fourCellOddP13AugmentedSelectorMomentEleven a3 a5 a7 a9 a11 := by
  have hL1 := intervalIntegrable_augmentedLowerRow_mul_sixModeSelector
    a3 a5 a7 a9 a11 1 0 0 0 0 0
  have hL3 := intervalIntegrable_augmentedLowerRow_mul_sixModeSelector
    a3 a5 a7 a9 a11 0 1 0 0 0 0
  have hL5 := intervalIntegrable_augmentedLowerRow_mul_sixModeSelector
    a3 a5 a7 a9 a11 0 0 1 0 0 0
  have hL7 := intervalIntegrable_augmentedLowerRow_mul_sixModeSelector
    a3 a5 a7 a9 a11 0 0 0 1 0 0
  have hL9 := intervalIntegrable_augmentedLowerRow_mul_sixModeSelector
    a3 a5 a7 a9 a11 0 0 0 0 1 0
  have hL11 := intervalIntegrable_augmentedLowerRow_mul_sixModeSelector
    a3 a5 a7 a9 a11 0 0 0 0 0 1
  have hU1 := intervalIntegrable_augmentedUpperRow_mul_sixModeSelector
    a3 a5 a7 a9 a11 1 0 0 0 0 0
  have hU3 := intervalIntegrable_augmentedUpperRow_mul_sixModeSelector
    a3 a5 a7 a9 a11 0 1 0 0 0 0
  have hU5 := intervalIntegrable_augmentedUpperRow_mul_sixModeSelector
    a3 a5 a7 a9 a11 0 0 1 0 0 0
  have hU7 := intervalIntegrable_augmentedUpperRow_mul_sixModeSelector
    a3 a5 a7 a9 a11 0 0 0 1 0 0
  have hU9 := intervalIntegrable_augmentedUpperRow_mul_sixModeSelector
    a3 a5 a7 a9 a11 0 0 0 0 1 0
  have hU11 := intervalIntegrable_augmentedUpperRow_mul_sixModeSelector
    a3 a5 a7 a9 a11 0 0 0 0 0 1
  have hselector : fourCellOddP13SixModeSelector b1 b3 b5 b7 b9 b11 =
      fun x ↦
        b1 * fourCellOddP13SixModeSelector 1 0 0 0 0 0 x +
        b3 * fourCellOddP13SixModeSelector 0 1 0 0 0 0 x +
        b5 * fourCellOddP13SixModeSelector 0 0 1 0 0 0 x +
        b7 * fourCellOddP13SixModeSelector 0 0 0 1 0 0 x +
        b9 * fourCellOddP13SixModeSelector 0 0 0 0 1 0 x +
        b11 * fourCellOddP13SixModeSelector 0 0 0 0 0 1 x := by
    funext x
    unfold fourCellOddP13SixModeSelector fourCellOddP13SixModeProfile
      fourCellOddOneThreeFiveSevenNineLowProfile
      fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
    ring
  have hLexpand :
      (fun x : ℝ ↦ fourCellOddP13AugmentedLowerRow a3 a5 a7 a9 a11 x *
        fourCellOddP13SixModeSelector b1 b3 b5 b7 b9 b11 x) =
      fun x ↦
        b1 * (fourCellOddP13AugmentedLowerRow a3 a5 a7 a9 a11 x *
          fourCellOddP13SixModeSelector 1 0 0 0 0 0 x) +
        b3 * (fourCellOddP13AugmentedLowerRow a3 a5 a7 a9 a11 x *
          fourCellOddP13SixModeSelector 0 1 0 0 0 0 x) +
        b5 * (fourCellOddP13AugmentedLowerRow a3 a5 a7 a9 a11 x *
          fourCellOddP13SixModeSelector 0 0 1 0 0 0 x) +
        b7 * (fourCellOddP13AugmentedLowerRow a3 a5 a7 a9 a11 x *
          fourCellOddP13SixModeSelector 0 0 0 1 0 0 x) +
        b9 * (fourCellOddP13AugmentedLowerRow a3 a5 a7 a9 a11 x *
          fourCellOddP13SixModeSelector 0 0 0 0 1 0 x) +
        b11 * (fourCellOddP13AugmentedLowerRow a3 a5 a7 a9 a11 x *
          fourCellOddP13SixModeSelector 0 0 0 0 0 1 x) := by
    rw [hselector]
    funext x
    ring
  have hUexpand :
      (fun x : ℝ ↦ fourCellOddP13AugmentedUpperRow a3 a5 a7 a9 a11 x *
        fourCellOddP13SixModeSelector b1 b3 b5 b7 b9 b11 x) =
      fun x ↦
        b1 * (fourCellOddP13AugmentedUpperRow a3 a5 a7 a9 a11 x *
          fourCellOddP13SixModeSelector 1 0 0 0 0 0 x) +
        b3 * (fourCellOddP13AugmentedUpperRow a3 a5 a7 a9 a11 x *
          fourCellOddP13SixModeSelector 0 1 0 0 0 0 x) +
        b5 * (fourCellOddP13AugmentedUpperRow a3 a5 a7 a9 a11 x *
          fourCellOddP13SixModeSelector 0 0 1 0 0 0 x) +
        b7 * (fourCellOddP13AugmentedUpperRow a3 a5 a7 a9 a11 x *
          fourCellOddP13SixModeSelector 0 0 0 1 0 0 x) +
        b9 * (fourCellOddP13AugmentedUpperRow a3 a5 a7 a9 a11 x *
          fourCellOddP13SixModeSelector 0 0 0 0 1 0 x) +
        b11 * (fourCellOddP13AugmentedUpperRow a3 a5 a7 a9 a11 x *
          fourCellOddP13SixModeSelector 0 0 0 0 0 1 x) := by
    rw [hselector]
    funext x
    ring
  unfold fourCellOddP13AugmentedTwoStripPair
    fourCellOddP13AugmentedSelectorMomentOne
    fourCellOddP13AugmentedSelectorMomentThree
    fourCellOddP13AugmentedSelectorMomentFive
    fourCellOddP13AugmentedSelectorMomentSeven
    fourCellOddP13AugmentedSelectorMomentNine
    fourCellOddP13AugmentedSelectorMomentEleven
    fourCellOddP13AugmentedTwoStripPair
  rw [hLexpand, hUexpand]
  rw [intervalIntegral.integral_add
        (((((hL1.const_mul _).add (hL3.const_mul _)).add
          (hL5.const_mul _)).add (hL7.const_mul _)).add (hL9.const_mul _))
        (hL11.const_mul _),
      intervalIntegral.integral_add
        ((((hL1.const_mul _).add (hL3.const_mul _)).add
          (hL5.const_mul _)).add (hL7.const_mul _)) (hL9.const_mul _),
      intervalIntegral.integral_add
        (((hL1.const_mul _).add (hL3.const_mul _)).add
          (hL5.const_mul _)) (hL7.const_mul _),
      intervalIntegral.integral_add
        ((hL1.const_mul _).add (hL3.const_mul _)) (hL5.const_mul _),
      intervalIntegral.integral_add (hL1.const_mul _) (hL3.const_mul _),
      intervalIntegral.integral_add
        (((((hU1.const_mul _).add (hU3.const_mul _)).add
          (hU5.const_mul _)).add (hU7.const_mul _)).add (hU9.const_mul _))
        (hU11.const_mul _),
      intervalIntegral.integral_add
        ((((hU1.const_mul _).add (hU3.const_mul _)).add
          (hU5.const_mul _)).add (hU7.const_mul _)) (hU9.const_mul _),
      intervalIntegral.integral_add
        (((hU1.const_mul _).add (hU3.const_mul _)).add
          (hU5.const_mul _)) (hU7.const_mul _),
      intervalIntegral.integral_add
        ((hU1.const_mul _).add (hU3.const_mul _)) (hU5.const_mul _),
      intervalIntegral.integral_add (hU1.const_mul _) (hU3.const_mul _)]
  repeat' rw [intervalIntegral.integral_const_mul]
  ring

/-- Optimal `P1` coordinate, obtained by inverting its positive-half mass. -/
def fourCellOddP13AugmentedOptimalSelectorCoefficientOne
    (a3 a5 a7 a9 a11 : ℝ) : ℝ :=
  3 * fourCellOddP13AugmentedSelectorMomentOne a3 a5 a7 a9 a11

/-- Optimal `P3` coordinate. -/
def fourCellOddP13AugmentedOptimalSelectorCoefficientThree
    (a3 a5 a7 a9 a11 : ℝ) : ℝ :=
  7 * fourCellOddP13AugmentedSelectorMomentThree a3 a5 a7 a9 a11

/-- Optimal `P5` coordinate. -/
def fourCellOddP13AugmentedOptimalSelectorCoefficientFive
    (a3 a5 a7 a9 a11 : ℝ) : ℝ :=
  11 * fourCellOddP13AugmentedSelectorMomentFive a3 a5 a7 a9 a11

/-- Optimal `P7` coordinate. -/
def fourCellOddP13AugmentedOptimalSelectorCoefficientSeven
    (a3 a5 a7 a9 a11 : ℝ) : ℝ :=
  15 * fourCellOddP13AugmentedSelectorMomentSeven a3 a5 a7 a9 a11

/-- Optimal `P9` coordinate. -/
def fourCellOddP13AugmentedOptimalSelectorCoefficientNine
    (a3 a5 a7 a9 a11 : ℝ) : ℝ :=
  19 * fourCellOddP13AugmentedSelectorMomentNine a3 a5 a7 a9 a11

/-- Optimal `P11` coordinate. -/
def fourCellOddP13AugmentedOptimalSelectorCoefficientEleven
    (a3 a5 a7 a9 a11 : ℝ) : ℝ :=
  23 * fourCellOddP13AugmentedSelectorMomentEleven a3 a5 a7 a9 a11

/-- The canonical shared selector: the orthogonal projection of the
piecewise exact row onto `P1/P3/P5/P7/P9/P11`. -/
def fourCellOddP13AugmentedOptimalSelector
    (a3 a5 a7 a9 a11 : ℝ) : ℝ → ℝ :=
  fourCellOddP13SixModeSelector
    (fourCellOddP13AugmentedOptimalSelectorCoefficientOne a3 a5 a7 a9 a11)
    (fourCellOddP13AugmentedOptimalSelectorCoefficientThree a3 a5 a7 a9 a11)
    (fourCellOddP13AugmentedOptimalSelectorCoefficientFive a3 a5 a7 a9 a11)
    (fourCellOddP13AugmentedOptimalSelectorCoefficientSeven a3 a5 a7 a9 a11)
    (fourCellOddP13AugmentedOptimalSelectorCoefficientNine a3 a5 a7 a9 a11)
    (fourCellOddP13AugmentedOptimalSelectorCoefficientEleven a3 a5 a7 a9 a11)

/-- The exact row and its canonical projection have the same pairing with
every retained six-mode selector. -/
theorem fourCellOddP13AugmentedOptimalSelector_pairing
    (a3 a5 a7 a9 a11 b1 b3 b5 b7 b9 b11 : ℝ) :
    fourCellOddP13AugmentedTwoStripPair a3 a5 a7 a9 a11
        (fourCellOddP13SixModeSelector b1 b3 b5 b7 b9 b11) =
      ∫ x : ℝ in 0..1,
        fourCellOddP13AugmentedOptimalSelector a3 a5 a7 a9 a11 x *
          fourCellOddP13SixModeSelector b1 b3 b5 b7 b9 b11 x := by
  rw [fourCellOddP13AugmentedTwoStripPair_sixModeSelector]
  unfold fourCellOddP13AugmentedOptimalSelector
  rw [integral_zero_one_fourCellOddP13SixModeSelector_mul]
  unfold fourCellOddP13AugmentedOptimalSelectorCoefficientOne
    fourCellOddP13AugmentedOptimalSelectorCoefficientThree
    fourCellOddP13AugmentedOptimalSelectorCoefficientFive
    fourCellOddP13AugmentedOptimalSelectorCoefficientSeven
    fourCellOddP13AugmentedOptimalSelectorCoefficientNine
    fourCellOddP13AugmentedOptimalSelectorCoefficientEleven
  ring

/-- Raw two-strip squared norm before quotienting by a selector. -/
def fourCellOddP13AugmentedRawTwoStripNormSq
    (a3 a5 a7 a9 a11 : ℝ) : ℝ :=
  fourCellOddP13TwoStripNormSq
    (fourCellOddP13AugmentedLowerRow a3 a5 a7 a9 a11)
    (fourCellOddP13AugmentedUpperRow a3 a5 a7 a9 a11)

/-- Two-strip squared norm after subtracting an arbitrary retained selector. -/
def fourCellOddP13AugmentedSelectorResidualTwoStripNormSq
    (a3 a5 a7 a9 a11 b1 b3 b5 b7 b9 b11 : ℝ) : ℝ :=
  fourCellOddP13TwoStripNormSq
    (fourCellOddP13AugmentedResidualLowerSelectorResidual
      a3 a5 a7 a9 a11 b1 b3 b5 b7 b9 b11)
    (fourCellOddP13AugmentedResidualUpperSelectorResidual
      a3 a5 a7 a9 a11 b1 b3 b5 b7 b9 b11)

private theorem intervalIntegrable_sq_of_memLp_two_full_local
    (f : ℝ → ℝ)
    (hf : MemLp f 2 (volume.restrict (Ioc (-1 : ℝ) 1)))
    (a b : ℝ) (hsub : uIcc a b ⊆ uIcc (-1 : ℝ) 1) :
    IntervalIntegrable (fun x : ℝ ↦ f x ^ 2) volume a b := by
  have hfull : IntervalIntegrable (fun x : ℝ ↦ f x ^ 2)
      volume (-1) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
    exact hf.integrable_sq
  exact hfull.mono_set hsub

/-- Exact completion-of-the-square formula before diagonalizing the six
selector coordinates. -/
theorem fourCellOddP13AugmentedSelectorResidualTwoStripNormSq_expansion
    (a3 a5 a7 a9 a11 b1 b3 b5 b7 b9 b11 : ℝ) :
    fourCellOddP13AugmentedSelectorResidualTwoStripNormSq
        a3 a5 a7 a9 a11 b1 b3 b5 b7 b9 b11 =
      fourCellOddP13AugmentedRawTwoStripNormSq a3 a5 a7 a9 a11 -
        2 * fourCellOddP13AugmentedTwoStripPair a3 a5 a7 a9 a11
          (fourCellOddP13SixModeSelector b1 b3 b5 b7 b9 b11) +
        ∫ x : ℝ in 0..1,
          fourCellOddP13SixModeSelector b1 b3 b5 b7 b9 b11 x ^ 2 := by
  let L := fourCellOddP13AugmentedLowerRow a3 a5 a7 a9 a11
  let U := fourCellOddP13AugmentedUpperRow a3 a5 a7 a9 a11
  let S := fourCellOddP13SixModeSelector b1 b3 b5 b7 b9 b11
  have hLsq : IntervalIntegrable (fun x : ℝ ↦ L x ^ 2)
      volume 0 (3 / 5) := by
    apply intervalIntegrable_sq_of_memLp_two_full_local L
      (memLp_fourCellOddP13AugmentedLowerRow_two_restrict
        a3 a5 a7 a9 a11)
    intro x hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 3 / 5)] at hx
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    constructor <;> linarith [hx.1, hx.2]
  have hUsq : IntervalIntegrable (fun x : ℝ ↦ U x ^ 2)
      volume (3 / 5) 1 := by
    apply intervalIntegrable_sq_of_memLp_two_full_local U
      (memLp_fourCellOddP13AugmentedUpperRow_two_restrict
        a3 a5 a7 a9 a11)
    intro x hx
    rw [uIcc_of_le (by norm_num : (3 / 5 : ℝ) ≤ 1)] at hx
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    constructor <;> linarith [hx.1, hx.2]
  have hLS : IntervalIntegrable (fun x : ℝ ↦ L x * S x)
      volume 0 (3 / 5) := by
    simpa only [L, S] using
      intervalIntegrable_augmentedLowerRow_mul_sixModeSelector
        a3 a5 a7 a9 a11 b1 b3 b5 b7 b9 b11
  have hUS : IntervalIntegrable (fun x : ℝ ↦ U x * S x)
      volume (3 / 5) 1 := by
    simpa only [U, S] using
      intervalIntegrable_augmentedUpperRow_mul_sixModeSelector
        a3 a5 a7 a9 a11 b1 b3 b5 b7 b9 b11
  have hS : Continuous S := by
    dsimp only [S, fourCellOddP13SixModeSelector]
    exact (contDiff_fourCellOddP13SixModeProfile _ _ _ _ _ _).continuous
  have hSsqL : IntervalIntegrable (fun x : ℝ ↦ S x ^ 2)
      volume 0 (3 / 5) := (hS.pow 2).intervalIntegrable _ _
  have hSsqU : IntervalIntegrable (fun x : ℝ ↦ S x ^ 2)
      volume (3 / 5) 1 := (hS.pow 2).intervalIntegrable _ _
  have hSsplit := intervalIntegral.integral_add_adjacent_intervals hSsqL hSsqU
  change
    (∫ x : ℝ in 0..3 / 5, (L x - S x) ^ 2) +
      (∫ x : ℝ in 3 / 5..1, (U x - S x) ^ 2) =
    ((∫ x : ℝ in 0..3 / 5, L x ^ 2) +
      ∫ x : ℝ in 3 / 5..1, U x ^ 2) -
      2 * ((∫ x : ℝ in 0..3 / 5, L x * S x) +
        ∫ x : ℝ in 3 / 5..1, U x * S x) +
      ∫ x : ℝ in 0..1, S x ^ 2
  rw [show (fun x : ℝ ↦ (L x - S x) ^ 2) =
      fun x ↦ L x ^ 2 - 2 * (L x * S x) + S x ^ 2 by
        funext x
        ring,
    show (fun x : ℝ ↦ (U x - S x) ^ 2) =
      fun x ↦ U x ^ 2 - 2 * (U x * S x) + S x ^ 2 by
        funext x
        ring,
    intervalIntegral.integral_add (hLsq.sub (hLS.const_mul _)) hSsqL,
    intervalIntegral.integral_sub hLsq (hLS.const_mul _),
    intervalIntegral.integral_add (hUsq.sub (hUS.const_mul _)) hSsqU,
    intervalIntegral.integral_sub hUsq (hUS.const_mul _),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  rw [← hSsplit]
  ring

/-- Diagonal form of the arbitrary-selector residual norm. -/
theorem fourCellOddP13AugmentedSelectorResidualTwoStripNormSq_diagonal
    (a3 a5 a7 a9 a11 b1 b3 b5 b7 b9 b11 : ℝ) :
    fourCellOddP13AugmentedSelectorResidualTwoStripNormSq
        a3 a5 a7 a9 a11 b1 b3 b5 b7 b9 b11 =
      fourCellOddP13AugmentedRawTwoStripNormSq a3 a5 a7 a9 a11 -
        2 * (b1 * fourCellOddP13AugmentedSelectorMomentOne a3 a5 a7 a9 a11 +
          b3 * fourCellOddP13AugmentedSelectorMomentThree a3 a5 a7 a9 a11 +
          b5 * fourCellOddP13AugmentedSelectorMomentFive a3 a5 a7 a9 a11 +
          b7 * fourCellOddP13AugmentedSelectorMomentSeven a3 a5 a7 a9 a11 +
          b9 * fourCellOddP13AugmentedSelectorMomentNine a3 a5 a7 a9 a11 +
          b11 * fourCellOddP13AugmentedSelectorMomentEleven a3 a5 a7 a9 a11) +
        (b1 ^ 2 / 3 + b3 ^ 2 / 7 + b5 ^ 2 / 11 +
          b7 ^ 2 / 15 + b9 ^ 2 / 19 + b11 ^ 2 / 23) := by
  rw [fourCellOddP13AugmentedSelectorResidualTwoStripNormSq_expansion,
    fourCellOddP13AugmentedTwoStripPair_sixModeSelector,
    integral_zero_one_fourCellOddP13SixModeSelector_sq]

/-- Squared norm captured by the six retained Legendre moments. -/
def fourCellOddP13AugmentedSelectorCapturedEnergy
    (a3 a5 a7 a9 a11 : ℝ) : ℝ :=
  3 * fourCellOddP13AugmentedSelectorMomentOne a3 a5 a7 a9 a11 ^ 2 +
  7 * fourCellOddP13AugmentedSelectorMomentThree a3 a5 a7 a9 a11 ^ 2 +
  11 * fourCellOddP13AugmentedSelectorMomentFive a3 a5 a7 a9 a11 ^ 2 +
  15 * fourCellOddP13AugmentedSelectorMomentSeven a3 a5 a7 a9 a11 ^ 2 +
  19 * fourCellOddP13AugmentedSelectorMomentNine a3 a5 a7 a9 a11 ^ 2 +
  23 * fourCellOddP13AugmentedSelectorMomentEleven a3 a5 a7 a9 a11 ^ 2

/-- Squared norm after subtracting the canonical optimal selector. -/
def fourCellOddP13AugmentedOptimalSelectorResidualTwoStripNormSq
    (a3 a5 a7 a9 a11 : ℝ) : ℝ :=
  fourCellOddP13AugmentedSelectorResidualTwoStripNormSq a3 a5 a7 a9 a11
    (fourCellOddP13AugmentedOptimalSelectorCoefficientOne a3 a5 a7 a9 a11)
    (fourCellOddP13AugmentedOptimalSelectorCoefficientThree a3 a5 a7 a9 a11)
    (fourCellOddP13AugmentedOptimalSelectorCoefficientFive a3 a5 a7 a9 a11)
    (fourCellOddP13AugmentedOptimalSelectorCoefficientSeven a3 a5 a7 a9 a11)
    (fourCellOddP13AugmentedOptimalSelectorCoefficientNine a3 a5 a7 a9 a11)
    (fourCellOddP13AugmentedOptimalSelectorCoefficientEleven a3 a5 a7 a9 a11)

/-- The optimal residual is the raw row norm minus the energy of its
orthogonal six-mode projection. -/
theorem fourCellOddP13AugmentedOptimalSelectorResidualTwoStripNormSq_eq
    (a3 a5 a7 a9 a11 : ℝ) :
    fourCellOddP13AugmentedOptimalSelectorResidualTwoStripNormSq
        a3 a5 a7 a9 a11 =
      fourCellOddP13AugmentedRawTwoStripNormSq a3 a5 a7 a9 a11 -
        fourCellOddP13AugmentedSelectorCapturedEnergy a3 a5 a7 a9 a11 := by
  unfold fourCellOddP13AugmentedOptimalSelectorResidualTwoStripNormSq
  rw [fourCellOddP13AugmentedSelectorResidualTwoStripNormSq_diagonal]
  unfold fourCellOddP13AugmentedOptimalSelectorCoefficientOne
    fourCellOddP13AugmentedOptimalSelectorCoefficientThree
    fourCellOddP13AugmentedOptimalSelectorCoefficientFive
    fourCellOddP13AugmentedOptimalSelectorCoefficientSeven
    fourCellOddP13AugmentedOptimalSelectorCoefficientNine
    fourCellOddP13AugmentedOptimalSelectorCoefficientEleven
    fourCellOddP13AugmentedSelectorCapturedEnergy
  ring

/-- Exact Pythagorean identity: every other shared six-mode selector pays
the diagonal squared distance from the canonical projection. -/
theorem fourCellOddP13AugmentedSelectorResidualTwoStripNormSq_pythagorean
    (a3 a5 a7 a9 a11 b1 b3 b5 b7 b9 b11 : ℝ) :
    fourCellOddP13AugmentedSelectorResidualTwoStripNormSq
        a3 a5 a7 a9 a11 b1 b3 b5 b7 b9 b11 =
      fourCellOddP13AugmentedOptimalSelectorResidualTwoStripNormSq
          a3 a5 a7 a9 a11 +
        (b1 - fourCellOddP13AugmentedOptimalSelectorCoefficientOne
          a3 a5 a7 a9 a11) ^ 2 / 3 +
        (b3 - fourCellOddP13AugmentedOptimalSelectorCoefficientThree
          a3 a5 a7 a9 a11) ^ 2 / 7 +
        (b5 - fourCellOddP13AugmentedOptimalSelectorCoefficientFive
          a3 a5 a7 a9 a11) ^ 2 / 11 +
        (b7 - fourCellOddP13AugmentedOptimalSelectorCoefficientSeven
          a3 a5 a7 a9 a11) ^ 2 / 15 +
        (b9 - fourCellOddP13AugmentedOptimalSelectorCoefficientNine
          a3 a5 a7 a9 a11) ^ 2 / 19 +
        (b11 - fourCellOddP13AugmentedOptimalSelectorCoefficientEleven
          a3 a5 a7 a9 a11) ^ 2 / 23 := by
  rw [fourCellOddP13AugmentedSelectorResidualTwoStripNormSq_diagonal,
    fourCellOddP13AugmentedOptimalSelectorResidualTwoStripNormSq_eq]
  unfold fourCellOddP13AugmentedOptimalSelectorCoefficientOne
    fourCellOddP13AugmentedOptimalSelectorCoefficientThree
    fourCellOddP13AugmentedOptimalSelectorCoefficientFive
    fourCellOddP13AugmentedOptimalSelectorCoefficientSeven
    fourCellOddP13AugmentedOptimalSelectorCoefficientNine
    fourCellOddP13AugmentedOptimalSelectorCoefficientEleven
    fourCellOddP13AugmentedSelectorCapturedEnergy
  ring

/-- The canonical selector is globally norm-minimizing among all shared
six-mode selectors. -/
theorem fourCellOddP13AugmentedOptimalSelectorResidualTwoStripNormSq_le
    (a3 a5 a7 a9 a11 b1 b3 b5 b7 b9 b11 : ℝ) :
    fourCellOddP13AugmentedOptimalSelectorResidualTwoStripNormSq
        a3 a5 a7 a9 a11 ≤
      fourCellOddP13AugmentedSelectorResidualTwoStripNormSq
        a3 a5 a7 a9 a11 b1 b3 b5 b7 b9 b11 := by
  rw [fourCellOddP13AugmentedSelectorResidualTwoStripNormSq_pythagorean]
  have h1 : 0 ≤ (b1 - fourCellOddP13AugmentedOptimalSelectorCoefficientOne
      a3 a5 a7 a9 a11) ^ 2 / 3 := by positivity
  have h3 : 0 ≤ (b3 - fourCellOddP13AugmentedOptimalSelectorCoefficientThree
      a3 a5 a7 a9 a11) ^ 2 / 7 := by positivity
  have h5 : 0 ≤ (b5 - fourCellOddP13AugmentedOptimalSelectorCoefficientFive
      a3 a5 a7 a9 a11) ^ 2 / 11 := by positivity
  have h7 : 0 ≤ (b7 - fourCellOddP13AugmentedOptimalSelectorCoefficientSeven
      a3 a5 a7 a9 a11) ^ 2 / 15 := by positivity
  have h9 : 0 ≤ (b9 - fourCellOddP13AugmentedOptimalSelectorCoefficientNine
      a3 a5 a7 a9 a11) ^ 2 / 19 := by positivity
  have h11 : 0 ≤ (b11 - fourCellOddP13AugmentedOptimalSelectorCoefficientEleven
      a3 a5 a7 a9 a11) ^ 2 / 23 := by positivity
  linarith

private theorem memLp_mono_lower_strip_local
    (f : ℝ → ℝ)
    (hf : MemLp f 2 (volume.restrict (Ioc (-1 : ℝ) 1))) :
    MemLp f 2 (volume.restrict (Ioc (0 : ℝ) (3 / 5))) := by
  apply hf.mono_measure
  apply Measure.restrict_mono
  · intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  · exact le_rfl

private theorem memLp_mono_upper_strip_local
    (f : ℝ → ℝ)
    (hf : MemLp f 2 (volume.restrict (Ioc (-1 : ℝ) 1))) :
    MemLp f 2 (volume.restrict (Ioc (3 / 5 : ℝ) 1)) := by
  apply hf.mono_measure
  apply Measure.restrict_mono
  · intro x hx
    exact ⟨by linarith [hx.1], hx.2⟩
  · exact le_rfl

/-- The optimal selector discharges both analytic fields of the production
certificate; only its single scalar norm inequality remains. -/
theorem fourCellOddP13AugmentedResidualSelectorTwoStripNormBound_optimal_iff
    (kappa a3 a5 a7 a9 a11 : ℝ) :
    FourCellOddP13AugmentedResidualSelectorTwoStripNormBound
        kappa a3 a5 a7 a9 a11
        (fourCellOddP13AugmentedOptimalSelectorCoefficientOne
          a3 a5 a7 a9 a11)
        (fourCellOddP13AugmentedOptimalSelectorCoefficientThree
          a3 a5 a7 a9 a11)
        (fourCellOddP13AugmentedOptimalSelectorCoefficientFive
          a3 a5 a7 a9 a11)
        (fourCellOddP13AugmentedOptimalSelectorCoefficientSeven
          a3 a5 a7 a9 a11)
        (fourCellOddP13AugmentedOptimalSelectorCoefficientNine
          a3 a5 a7 a9 a11)
        (fourCellOddP13AugmentedOptimalSelectorCoefficientEleven
          a3 a5 a7 a9 a11) ↔
      fourCellOddP13AugmentedOptimalSelectorResidualTwoStripNormSq
          a3 a5 a7 a9 a11 ≤
        fourCellOddCoreLocalQuadratic
          (fourCellOddP13AugmentedGalerkinResidualProfile
            a3 a5 a7 a9 a11) * kappa := by
  constructor
  · intro h
    exact h.2.2
  · intro hnorm
    refine ⟨?_, ?_, hnorm⟩
    · apply memLp_mono_lower_strip_local
      exact
        memLp_fourCellOddP13AugmentedResidualLowerSelectorResidual_two_restrict
          a3 a5 a7 a9 a11 _ _ _ _ _ _
    · apply memLp_mono_upper_strip_local
      exact
        memLp_fourCellOddP13AugmentedResidualUpperSelectorResidual_two_restrict
          a3 a5 a7 a9 a11 _ _ _ _ _ _

/-- Structural reduction of the quotient certificate to the unique optimal
six-mode scalar norm. -/
theorem fourCellOddP13AugmentedResidualModuloSixModeTwoStripNormBound_of_optimal
    (kappa a3 a5 a7 a9 a11 : ℝ)
    (hnorm : fourCellOddP13AugmentedOptimalSelectorResidualTwoStripNormSq
        a3 a5 a7 a9 a11 ≤
      fourCellOddCoreLocalQuadratic
        (fourCellOddP13AugmentedGalerkinResidualProfile
          a3 a5 a7 a9 a11) * kappa) :
    FourCellOddP13AugmentedResidualModuloSixModeTwoStripNormBound
      kappa a3 a5 a7 a9 a11 := by
  refine ⟨
    fourCellOddP13AugmentedOptimalSelectorCoefficientOne a3 a5 a7 a9 a11,
    fourCellOddP13AugmentedOptimalSelectorCoefficientThree a3 a5 a7 a9 a11,
    fourCellOddP13AugmentedOptimalSelectorCoefficientFive a3 a5 a7 a9 a11,
    fourCellOddP13AugmentedOptimalSelectorCoefficientSeven a3 a5 a7 a9 a11,
    fourCellOddP13AugmentedOptimalSelectorCoefficientNine a3 a5 a7 a9 a11,
    fourCellOddP13AugmentedOptimalSelectorCoefficientEleven a3 a5 a7 a9 a11,
    ?_⟩
  exact
    (fourCellOddP13AugmentedResidualSelectorTwoStripNormBound_optimal_iff
      kappa a3 a5 a7 a9 a11).2 hnorm

/-- The existential selector certificate is equivalent to the one scalar
inequality for the canonical orthogonal projection. -/
theorem fourCellOddP13AugmentedResidualModuloSixModeTwoStripNormBound_iff_optimal
    (kappa a3 a5 a7 a9 a11 : ℝ) :
    FourCellOddP13AugmentedResidualModuloSixModeTwoStripNormBound
        kappa a3 a5 a7 a9 a11 ↔
      fourCellOddP13AugmentedOptimalSelectorResidualTwoStripNormSq
          a3 a5 a7 a9 a11 ≤
        fourCellOddCoreLocalQuadratic
          (fourCellOddP13AugmentedGalerkinResidualProfile
            a3 a5 a7 a9 a11) * kappa := by
  constructor
  · rintro ⟨b1, b3, b5, b7, b9, b11, _hL, _hU, hnorm⟩
    exact
      (fourCellOddP13AugmentedOptimalSelectorResidualTwoStripNormSq_le
        a3 a5 a7 a9 a11 b1 b3 b5 b7 b9 b11).trans hnorm
  · exact
      fourCellOddP13AugmentedResidualModuloSixModeTwoStripNormBound_of_optimal
        kappa a3 a5 a7 a9 a11

theorem one_sub_nineteen_twentieths_sq :
    (1 - (19 / 20 : ℝ) ^ 2) = 39 / 400 := by
  norm_num

/-- At the exact inverse-defined Galerkin solution, the production
`19/20` quotient now has one and only one remaining scalar inequality. -/
theorem fourCellOddP13AugmentedExactSolution_nineteenTwentieths_of_optimalNorm
    (hnorm :
      fourCellOddP13AugmentedOptimalSelectorResidualTwoStripNormSq
          (fourCellOddP13AugmentedRetainedSolution 0)
          (fourCellOddP13AugmentedRetainedSolution 1)
          (fourCellOddP13AugmentedRetainedSolution 2)
          (fourCellOddP13AugmentedRetainedSolution 3)
          (fourCellOddP13AugmentedRetainedSolution 4) ≤
        fourCellOddCoreLocalQuadratic
          (fourCellOddP13AugmentedGalerkinResidualProfile
            (fourCellOddP13AugmentedRetainedSolution 0)
            (fourCellOddP13AugmentedRetainedSolution 1)
            (fourCellOddP13AugmentedRetainedSolution 2)
            (fourCellOddP13AugmentedRetainedSolution 3)
            (fourCellOddP13AugmentedRetainedSolution 4)) *
          (1 - (19 / 20 : ℝ) ^ 2)) :
    FourCellOddP13AugmentedResidualModuloSixModeTwoStripNormBound
      (1 - (19 / 20 : ℝ) ^ 2)
      (fourCellOddP13AugmentedRetainedSolution 0)
      (fourCellOddP13AugmentedRetainedSolution 1)
      (fourCellOddP13AugmentedRetainedSolution 2)
      (fourCellOddP13AugmentedRetainedSolution 3)
      (fourCellOddP13AugmentedRetainedSolution 4) := by
  exact
    fourCellOddP13AugmentedResidualModuloSixModeTwoStripNormBound_of_optimal
      (1 - (19 / 20 : ℝ) ^ 2)
      (fourCellOddP13AugmentedRetainedSolution 0)
      (fourCellOddP13AugmentedRetainedSolution 1)
      (fourCellOddP13AugmentedRetainedSolution 2)
      (fourCellOddP13AugmentedRetainedSolution 3)
      (fourCellOddP13AugmentedRetainedSolution 4) hnorm

/-- Fully normalized statement of the last finite scalar certificate at the
exact inverse-defined solution. -/
theorem fourCellOddP13AugmentedExactSolution_nineteenTwentieths_iff_optimalNorm :
    FourCellOddP13AugmentedResidualModuloSixModeTwoStripNormBound
        (1 - (19 / 20 : ℝ) ^ 2)
        (fourCellOddP13AugmentedRetainedSolution 0)
        (fourCellOddP13AugmentedRetainedSolution 1)
        (fourCellOddP13AugmentedRetainedSolution 2)
        (fourCellOddP13AugmentedRetainedSolution 3)
        (fourCellOddP13AugmentedRetainedSolution 4) ↔
      fourCellOddP13AugmentedOptimalSelectorResidualTwoStripNormSq
          (fourCellOddP13AugmentedRetainedSolution 0)
          (fourCellOddP13AugmentedRetainedSolution 1)
          (fourCellOddP13AugmentedRetainedSolution 2)
          (fourCellOddP13AugmentedRetainedSolution 3)
          (fourCellOddP13AugmentedRetainedSolution 4) ≤
        fourCellOddCoreLocalQuadratic
          (fourCellOddP13AugmentedGalerkinResidualProfile
            (fourCellOddP13AugmentedRetainedSolution 0)
            (fourCellOddP13AugmentedRetainedSolution 1)
            (fourCellOddP13AugmentedRetainedSolution 2)
            (fourCellOddP13AugmentedRetainedSolution 3)
            (fourCellOddP13AugmentedRetainedSolution 4)) * (39 / 400) := by
  rw [fourCellOddP13AugmentedResidualModuloSixModeTwoStripNormBound_iff_optimal,
    one_sub_nineteen_twentieths_sq]

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP13AugmentedOptimalSelectorStructural

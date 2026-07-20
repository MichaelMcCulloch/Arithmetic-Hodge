import ArithmeticHodge.Analysis.YoshidaFourCellOddP11GalerkinRieszStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddP11FiveModeThreeHalvesStructural

set_option autoImplicit false

open MeasureTheory Real Set
open scoped Interval

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP11GalerkinResidualRepresenterStructural

noncomputable section

open CenteredOddOneThreeEnergy
open YoshidaEndpointPotentialBound
open YoshidaFactorTwoContinuousLagRepresenterStructural
open YoshidaFactorTwoIntegrableLagRepresenterStructural
open YoshidaFourCellOddP11EndpointFormDualClosureStructural
open YoshidaFourCellOddP11FiveModeThreeHalvesStructural
open YoshidaFourCellOddP11GalerkinRieszStructural
open YoshidaFourCellOddStripCapacityClosureStructural
open YoshidaFourCellParityOperatorStructural
open YoshidaRegularKernelBound

/-!
# Exact two-strip representer for the Galerkin residual

The Galerkin residual is the five-mode profile with coordinates
`(1,-a₃,-a₅,-a₇,-a₉)`.  This file specializes the exact five-mode
two-strip row to that residual and proves the ordinary, unweighted `L²`
Cauchy reduction.  The only remaining premise is the norm of the exact row
density itself; there is no sampling and no restatement of the target dual
inequality.
-/

/-- Exact lower-strip density of the Galerkin residual row. -/
def fourCellOddP11GalerkinResidualLowerRepresenter
    (a₃ a₅ a₇ a₉ : ℝ) (x : ℝ) : ℝ :=
  fourCellOddFiveModeLowerRepresenter
    1 (-a₃) (-a₅) (-a₇) (-a₉) x

/-- Exact upper-strip density of the Galerkin residual row. -/
def fourCellOddP11GalerkinResidualUpperRepresenter
    (a₃ a₅ a₇ a₉ : ℝ) (x : ℝ) : ℝ :=
  fourCellOddFiveModeUpperRepresenter
    1 (-a₃) (-a₅) (-a₇) (-a₉) x

/-- An arbitrary retained five-mode selector.  Its pairing with every
`P₁₁+` tail vanishes on the whole positive half interval. -/
def fourCellOddP11GalerkinResidualSelector
    (b₁ b₃ b₅ b₇ b₉ : ℝ) : ℝ → ℝ :=
  fourCellOddOneThreeFiveSevenNineLowProfile b₁ b₃ b₅ b₇ b₉

/-- Lower-strip density after subtracting a retained selector. -/
def fourCellOddP11GalerkinResidualLowerSelectorResidual
    (a₃ a₅ a₇ a₉ b₁ b₃ b₅ b₇ b₉ : ℝ) (x : ℝ) : ℝ :=
  fourCellOddP11GalerkinResidualLowerRepresenter a₃ a₅ a₇ a₉ x -
    fourCellOddP11GalerkinResidualSelector b₁ b₃ b₅ b₇ b₉ x

/-- Upper-strip density after subtracting the same retained selector. -/
def fourCellOddP11GalerkinResidualUpperSelectorResidual
    (a₃ a₅ a₇ a₉ b₁ b₃ b₅ b₇ b₉ : ℝ) (x : ℝ) : ℝ :=
  fourCellOddP11GalerkinResidualUpperRepresenter a₃ a₅ a₇ a₉ x -
    fourCellOddP11GalerkinResidualSelector b₁ b₃ b₅ b₇ b₉ x

/-- Exact positive-half two-strip pairing for the Galerkin residual against
a genuine `P₁₁+` profile. -/
theorem fourCellOddCoreLocalBilinear_galerkinResidual_P11Plus_eq_twoStripRepresenter
    (a₃ a₅ a₇ a₉ : ℝ) (r : ℝ → ℝ)
    (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r)
    (h1 : centeredOddP1Coefficient r = 0)
    (h3 : centeredOddP3Coefficient r = 0)
    (h5 : centeredOddP5Coefficient r = 0)
    (h7 : centeredOddP7Coefficient r = 0)
    (h9 : centeredOddP9Coefficient r = 0) :
    fourCellOddCoreLocalBilinear
        (fourCellOddP11GalerkinResidualProfile a₃ a₅ a₇ a₉) r =
      (∫ x : ℝ in 0..3 / 5,
        fourCellOddP11GalerkinResidualLowerRepresenter a₃ a₅ a₇ a₉ x *
          r x) +
      ∫ x : ℝ in 3 / 5..1,
        fourCellOddP11GalerkinResidualUpperRepresenter a₃ a₅ a₇ a₉ x *
          r x := by
  rw [fourCellOddP11GalerkinResidualProfile_eq_fiveMode]
  simpa only [fourCellOddP11GalerkinResidualLowerRepresenter,
    fourCellOddP11GalerkinResidualUpperRepresenter] using
      fourCellOddCoreLocalBilinear_fiveMode_P11Plus_eq_twoStripRepresenter
        r hr hodd h1 h3 h5 h7 h9 1 (-a₃) (-a₅) (-a₇) (-a₉)

/-! ## Square-integrability of the exact densities -/

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

private theorem memLp_two_restrict_of_continuous
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

private theorem regularLag_abs_le_quarter
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

theorem memLp_fourCellOddFiveModeRegularRepresenter_two_restrict
    (c d e f g : ℝ) :
    MemLp (fourCellOddFiveModeRegularRepresenter c d e f g) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
  let k : ℝ → ℝ := fun t ↦
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t)
  let p : ℝ → ℝ :=
    fourCellOddOneThreeFiveSevenNineLowProfile c d e f g
  have hkMeas : Measurable k := by
    dsimp only [k]
    exact measurable_yoshidaRegularKernel.comp
      (measurable_const.mul measurable_id)
  have hp : Continuous p := by
    dsimp only [p]
    exact (contDiff_fourCellOddOneThreeFiveSevenNineLowProfile
      c d e f g).continuous
  have hkBound : ∀ t ∈ Icc (0 : ℝ) 2, |k t| ≤ (1 / 4 : ℝ) := by
    intro t ht
    simpa only [k] using regularLag_abs_le_quarter t ht
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
  simpa only [k, p, fourCellOddFiveModeRegularRepresenter] using hLp

theorem memLp_fourCellOddP11GalerkinResidualLowerRepresenter_two_restrict
    (a₃ a₅ a₇ a₉ : ℝ) :
    MemLp (fourCellOddP11GalerkinResidualLowerRepresenter a₃ a₅ a₇ a₉) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
  let p : ℝ → ℝ := fourCellOddOneThreeFiveSevenNineLowProfile
    1 (-a₃) (-a₅) (-a₇) (-a₉)
  have hp : Continuous p := by
    dsimp only [p]
    exact (contDiff_fourCellOddOneThreeFiveSevenNineLowProfile _ _ _ _ _).continuous
  have hpotential := memLp_endpointPotential_mul_continuous p hp
  have hregular := memLp_fourCellOddFiveModeRegularRepresenter_two_restrict
    1 (-a₃) (-a₅) (-a₇) (-a₉)
  unfold fourCellOddP11GalerkinResidualLowerRepresenter
    fourCellOddFiveModeLowerRepresenter
  dsimp only [p] at hpotential
  simpa only [Pi.sub_apply, mul_assoc] using
    (hpotential.const_mul (93 / 50)).sub
      (hregular.const_mul (2 * fourCellOperatorHalfWidth))

theorem memLp_fourCellOddP11GalerkinResidualUpperRepresenter_two_restrict
    (a₃ a₅ a₇ a₉ : ℝ) :
    MemLp (fourCellOddP11GalerkinResidualUpperRepresenter a₃ a₅ a₇ a₉) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
  let p : ℝ → ℝ := fourCellOddOneThreeFiveSevenNineLowProfile
    1 (-a₃) (-a₅) (-a₇) (-a₉)
  let reflected : ℝ → ℝ := fun x ↦ p (8 / 5 - x)
  have hp : Continuous p := by
    dsimp only [p]
    exact (contDiff_fourCellOddOneThreeFiveSevenNineLowProfile _ _ _ _ _).continuous
  have hreflected : Continuous reflected := by
    dsimp only [reflected]
    fun_prop
  have hbase :=
    memLp_fourCellOddP11GalerkinResidualLowerRepresenter_two_restrict
      a₃ a₅ a₇ a₉
  have heven : MemLp (fun x : ℝ ↦ (p x + reflected x) / 2) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) :=
    memLp_two_restrict_of_continuous _ ((hp.add hreflected).div_const 2)
  have hodd : MemLp (fun x : ℝ ↦ (p x - reflected x) / 2) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) :=
    memLp_two_restrict_of_continuous _ ((hp.sub hreflected).div_const 2)
  have hraw : MemLp
      (fourCellOddFiveModeRawUpperRepresenter
        1 (-a₃) (-a₅) (-a₇) (-a₉)) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) :=
    memLp_two_restrict_of_continuous _
      (continuous_fourCellOddFiveModeRawUpperRepresenter
        1 (-a₃) (-a₅) (-a₇) (-a₉))
  unfold fourCellOddP11GalerkinResidualUpperRepresenter
    fourCellOddFiveModeUpperRepresenter
  dsimp only [p, reflected] at heven hodd
  exact (((hbase.add
      (heven.const_mul (Real.sqrt 2 * Real.log 2))).add
        (hodd.const_mul (2 - Real.sqrt 2 * Real.log 2))).sub
          (hraw.const_mul (1 / 2)))

theorem memLp_fourCellOddP11GalerkinResidualLowerSelectorResidual_two_restrict
    (a₃ a₅ a₇ a₉ b₁ b₃ b₅ b₇ b₉ : ℝ) :
    MemLp
      (fourCellOddP11GalerkinResidualLowerSelectorResidual
        a₃ a₅ a₇ a₉ b₁ b₃ b₅ b₇ b₉) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
  have hrow :=
    memLp_fourCellOddP11GalerkinResidualLowerRepresenter_two_restrict
      a₃ a₅ a₇ a₉
  have hselector : MemLp
      (fourCellOddP11GalerkinResidualSelector b₁ b₃ b₅ b₇ b₉) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
    apply memLp_two_restrict_of_continuous
    unfold fourCellOddP11GalerkinResidualSelector
    exact (contDiff_fourCellOddOneThreeFiveSevenNineLowProfile
      b₁ b₃ b₅ b₇ b₉).continuous
  exact hrow.sub hselector

theorem memLp_fourCellOddP11GalerkinResidualUpperSelectorResidual_two_restrict
    (a₃ a₅ a₇ a₉ b₁ b₃ b₅ b₇ b₉ : ℝ) :
    MemLp
      (fourCellOddP11GalerkinResidualUpperSelectorResidual
        a₃ a₅ a₇ a₉ b₁ b₃ b₅ b₇ b₉) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
  have hrow :=
    memLp_fourCellOddP11GalerkinResidualUpperRepresenter_two_restrict
      a₃ a₅ a₇ a₉
  have hselector : MemLp
      (fourCellOddP11GalerkinResidualSelector b₁ b₃ b₅ b₇ b₉) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
    apply memLp_two_restrict_of_continuous
    unfold fourCellOddP11GalerkinResidualSelector
    exact (contDiff_fourCellOddOneThreeFiveSevenNineLowProfile
      b₁ b₃ b₅ b₇ b₉).continuous
  exact hrow.sub hselector

/-- The retained selector is annihilated by the five tail moments, so the
Galerkin residual row is exactly the pairing with its selector residuals. -/
theorem fourCellOddCoreLocalBilinear_galerkinResidual_P11Plus_eq_selectorResiduals
    (a₃ a₅ a₇ a₉ b₁ b₃ b₅ b₇ b₉ : ℝ) (r : ℝ → ℝ)
    (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r)
    (h1 : centeredOddP1Coefficient r = 0)
    (h3 : centeredOddP3Coefficient r = 0)
    (h5 : centeredOddP5Coefficient r = 0)
    (h7 : centeredOddP7Coefficient r = 0)
    (h9 : centeredOddP9Coefficient r = 0) :
    fourCellOddCoreLocalBilinear
        (fourCellOddP11GalerkinResidualProfile a₃ a₅ a₇ a₉) r =
      (∫ x : ℝ in 0..3 / 5,
        fourCellOddP11GalerkinResidualLowerSelectorResidual
          a₃ a₅ a₇ a₉ b₁ b₃ b₅ b₇ b₉ x * r x) +
      ∫ x : ℝ in 3 / 5..1,
        fourCellOddP11GalerkinResidualUpperSelectorResidual
          a₃ a₅ a₇ a₉ b₁ b₃ b₅ b₇ b₉ x * r x := by
  let S : ℝ → ℝ :=
    fourCellOddP11GalerkinResidualSelector b₁ b₃ b₅ b₇ b₉
  have hSzero : (∫ x : ℝ in 0..1, S x * r x) = 0 := by
    dsimp only [S]
    unfold fourCellOddP11GalerkinResidualSelector
    exact integral_zero_one_fiveMode_mul_P11Plus_eq_zero
      r hr.continuous hodd h1 h3 h5 h7 h9 b₁ b₃ b₅ b₇ b₉
  have hSInt : IntervalIntegrable (fun x : ℝ ↦ S x * r x)
      volume 0 1 := by
    exact (((contDiff_fourCellOddOneThreeFiveSevenNineLowProfile
      b₁ b₃ b₅ b₇ b₉).continuous).mul hr.continuous)
        |>.intervalIntegrable _ _
  have hSL : IntervalIntegrable (fun x : ℝ ↦ S x * r x)
      volume 0 (3 / 5) := by
    apply hSInt.mono_set
    intro x hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 3 / 5)] at hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact ⟨hx.1, by linarith [hx.2]⟩
  have hSU : IntervalIntegrable (fun x : ℝ ↦ S x * r x)
      volume (3 / 5) 1 := by
    apply hSInt.mono_set
    intro x hx
    rw [uIcc_of_le (by norm_num : (3 / 5 : ℝ) ≤ 1)] at hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact ⟨by linarith [hx.1], hx.2⟩
  have hSSplit := intervalIntegral.integral_add_adjacent_intervals hSL hSU
  have hraw :=
    fourCellOddCoreLocalBilinear_galerkinResidual_P11Plus_eq_twoStripRepresenter
      a₃ a₅ a₇ a₉ r hr hodd h1 h3 h5 h7 h9
  have hLfull :=
    memLp_fourCellOddP11GalerkinResidualLowerRepresenter_two_restrict
      a₃ a₅ a₇ a₉
  have hUfull :=
    memLp_fourCellOddP11GalerkinResidualUpperRepresenter_two_restrict
      a₃ a₅ a₇ a₉
  have hrFull := memLp_two_restrict_of_continuous r hr.continuous
  have hLprodFull := hLfull.integrable_mul hrFull
  have hUprodFull := hUfull.integrable_mul hrFull
  have hLprod : IntervalIntegrable
      (fun x : ℝ ↦
        fourCellOddP11GalerkinResidualLowerRepresenter a₃ a₅ a₇ a₉ x * r x)
      volume 0 (3 / 5) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
    exact hLprodFull.mono_measure
      (Measure.restrict_mono (by
        intro x hx
        exact ⟨by linarith [hx.1], by linarith [hx.2]⟩) le_rfl)
  have hUprod : IntervalIntegrable
      (fun x : ℝ ↦
        fourCellOddP11GalerkinResidualUpperRepresenter a₃ a₅ a₇ a₉ x * r x)
      volume (3 / 5) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
    exact hUprodFull.mono_measure
      (Measure.restrict_mono (by
        intro x hx
        exact ⟨by linarith [hx.1], hx.2⟩) le_rfl)
  rw [show (fun x : ℝ ↦
      fourCellOddP11GalerkinResidualLowerSelectorResidual
        a₃ a₅ a₇ a₉ b₁ b₃ b₅ b₇ b₉ x * r x) =
      fun x ↦
        fourCellOddP11GalerkinResidualLowerRepresenter a₃ a₅ a₇ a₉ x * r x -
          S x * r x by
    funext x
    dsimp only [S]
    unfold fourCellOddP11GalerkinResidualLowerSelectorResidual
    ring,
    show (fun x : ℝ ↦
      fourCellOddP11GalerkinResidualUpperSelectorResidual
        a₃ a₅ a₇ a₉ b₁ b₃ b₅ b₇ b₉ x * r x) =
      fun x ↦
        fourCellOddP11GalerkinResidualUpperRepresenter a₃ a₅ a₇ a₉ x * r x -
          S x * r x by
    funext x
    dsimp only [S]
    unfold fourCellOddP11GalerkinResidualUpperSelectorResidual
    ring,
    intervalIntegral.integral_sub hLprod hSL,
    intervalIntegral.integral_sub hUprod hSU]
  rw [hraw]
  linarith only [hSSplit, hSzero]

/-! ## Ordinary two-strip Cauchy -/

private theorem sum_pair_sq_le_sum_norm_mul_sum_mass
    (A B NL NU ML MU : ℝ)
    (hNL : 0 ≤ NL) (hNU : 0 ≤ NU)
    (hML : 0 ≤ ML) (hMU : 0 ≤ MU)
    (hA : A ^ 2 ≤ NL * ML) (hB : B ^ 2 ≤ NU * MU) :
    (A + B) ^ 2 ≤ (NL + NU) * (ML + MU) := by
  have hcross : 2 * A * B ≤ NL * MU + NU * ML := by
    by_cases hab : A * B ≤ 0
    · have hright : 0 ≤ NL * MU + NU * ML :=
        add_nonneg (mul_nonneg hNL hMU) (mul_nonneg hNU hML)
      nlinarith
    · have habpos : 0 < A * B := lt_of_not_ge hab
      have hprod : (A * B) ^ 2 ≤ (NL * ML) * (NU * MU) := by
        rw [mul_pow]
        exact mul_le_mul hA hB (sq_nonneg B) (mul_nonneg hNL hML)
      have hscaled := mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 4)
      have hamgm :
          4 * ((NL * ML) * (NU * MU)) ≤ (NL * MU + NU * ML) ^ 2 := by
        nlinarith only [sq_nonneg (NL * MU - NU * ML)]
      have hsquares : (2 * A * B) ^ 2 ≤
          (NL * MU + NU * ML) ^ 2 := by
        nlinarith only [hscaled, hamgm]
      have hleft : 0 ≤ 2 * A * B := by nlinarith
      have hright : 0 ≤ NL * MU + NU * ML :=
        add_nonneg (mul_nonneg hNL hMU) (mul_nonneg hNU hML)
      exact (sq_le_sq₀ hleft hright).1 hsquares
  nlinarith only [hA, hB, hcross]

/-- Exact two-strip norm bound after subtracting one specified retained
five-mode selector. -/
def FourCellOddP11GalerkinResidualSelectorTwoStripNormBound
    (a₃ a₅ a₇ a₉ b₁ b₃ b₅ b₇ b₉ : ℝ) : Prop :=
  (∫ x : ℝ in 0..3 / 5,
      fourCellOddP11GalerkinResidualLowerSelectorResidual
        a₃ a₅ a₇ a₉ b₁ b₃ b₅ b₇ b₉ x ^ 2) +
    (∫ x : ℝ in 3 / 5..1,
      fourCellOddP11GalerkinResidualUpperSelectorResidual
        a₃ a₅ a₇ a₉ b₁ b₃ b₅ b₇ b₉ x ^ 2) ≤
    fourCellOddCoreLocalQuadratic
      (fourCellOddP11GalerkinResidualProfile a₃ a₅ a₇ a₉) / 50

/-- The useful norm premise is the exact distance of the two-strip row to
the retained five-mode selector space. -/
def FourCellOddP11GalerkinResidualModuloFiveModeTwoStripNormBound
    (a₃ a₅ a₇ a₉ : ℝ) : Prop :=
  ∃ b₁ b₃ b₅ b₇ b₉ : ℝ,
    FourCellOddP11GalerkinResidualSelectorTwoStripNormBound
      a₃ a₅ a₇ a₉ b₁ b₃ b₅ b₇ b₉

/-- Genuine unweighted two-strip `L²` Cauchy for an arbitrary retained
selector.  The selector disappears exactly by the five tail moments. -/
theorem fourCellOddP11GalerkinResidualL2Dual_of_selectorTwoStripNormBound
    (a₃ a₅ a₇ a₉ b₁ b₃ b₅ b₇ b₉ : ℝ)
    (hnorm : FourCellOddP11GalerkinResidualSelectorTwoStripNormBound
      a₃ a₅ a₇ a₉ b₁ b₃ b₅ b₇ b₉) :
    FourCellOddP11GalerkinResidualL2Dual a₃ a₅ a₇ a₉ := by
  intro r hr hodd h1 h3 h5 h7 h9
  let L : ℝ → ℝ :=
    fourCellOddP11GalerkinResidualLowerSelectorResidual
      a₃ a₅ a₇ a₉ b₁ b₃ b₅ b₇ b₉
  let U : ℝ → ℝ :=
    fourCellOddP11GalerkinResidualUpperSelectorResidual
      a₃ a₅ a₇ a₉ b₁ b₃ b₅ b₇ b₉
  let μL : Measure ℝ := volume.restrict (Ioc (0 : ℝ) (3 / 5))
  let μU : Measure ℝ := volume.restrict (Ioc (3 / 5 : ℝ) 1)
  have hLfull :=
    memLp_fourCellOddP11GalerkinResidualLowerSelectorResidual_two_restrict
      a₃ a₅ a₇ a₉ b₁ b₃ b₅ b₇ b₉
  have hUfull :=
    memLp_fourCellOddP11GalerkinResidualUpperSelectorResidual_two_restrict
      a₃ a₅ a₇ a₉ b₁ b₃ b₅ b₇ b₉
  have hL : MemLp L 2 μL := by
    apply hLfull.mono_measure
    dsimp only [μL]
    apply Measure.restrict_mono
    · intro x hx
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    · exact le_rfl
  have hU : MemLp U 2 μU := by
    apply hUfull.mono_measure
    dsimp only [μU]
    apply Measure.restrict_mono
    · intro x hx
      exact ⟨by linarith [hx.1], hx.2⟩
    · exact le_rfl
  have hrFull : MemLp r 2 (volume.restrict (Ioc (-1 : ℝ) 1)) :=
    memLp_two_restrict_of_continuous r hr.continuous
  have hrL : MemLp r 2 μL := by
    apply hrFull.mono_measure
    dsimp only [μL]
    apply Measure.restrict_mono
    · intro x hx
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    · exact le_rfl
  have hrU : MemLp r 2 μU := by
    apply hrFull.mono_measure
    dsimp only [μU]
    apply Measure.restrict_mono
    · intro x hx
      exact ⟨by linarith [hx.1], hx.2⟩
    · exact le_rfl
  have hcauchyL :=
    YoshidaEndpointWeightedCauchy.sq_integral_mul_le_weighted
      μL (fun _ : ℝ ↦ 1) L r (by simp)
        (by simpa only [div_one, Real.sqrt_one] using hL)
        (by simpa only [Real.sqrt_one, one_mul] using hrL)
  have hcauchyU :=
    YoshidaEndpointWeightedCauchy.sq_integral_mul_le_weighted
      μU (fun _ : ℝ ↦ 1) U r (by simp)
        (by simpa only [div_one, Real.sqrt_one] using hU)
        (by simpa only [Real.sqrt_one, one_mul] using hrU)
  have hcauchyL' :
      (∫ x : ℝ in 0..3 / 5, L x * r x) ^ 2 ≤
        (∫ x : ℝ in 0..3 / 5, L x ^ 2) *
          (∫ x : ℝ in 0..3 / 5, r x ^ 2) := by
    repeat rw [intervalIntegral.integral_of_le (by norm_num)]
    simpa only [μL, div_one, one_mul] using hcauchyL
  have hcauchyU' :
      (∫ x : ℝ in 3 / 5..1, U x * r x) ^ 2 ≤
        (∫ x : ℝ in 3 / 5..1, U x ^ 2) *
          (∫ x : ℝ in 3 / 5..1, r x ^ 2) := by
    repeat rw [intervalIntegral.integral_of_le (by norm_num)]
    simpa only [μU, div_one, one_mul] using hcauchyU
  have hNL : 0 ≤ ∫ x : ℝ in 0..3 / 5, L x ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun _ _ ↦ sq_nonneg _)
  have hNU : 0 ≤ ∫ x : ℝ in 3 / 5..1, U x ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun _ _ ↦ sq_nonneg _)
  have hML : 0 ≤ ∫ x : ℝ in 0..3 / 5, r x ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun _ _ ↦ sq_nonneg _)
  have hMU : 0 ≤ ∫ x : ℝ in 3 / 5..1, r x ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun _ _ ↦ sq_nonneg _)
  have htwo := sum_pair_sq_le_sum_norm_mul_sum_mass
    (∫ x : ℝ in 0..3 / 5, L x * r x)
    (∫ x : ℝ in 3 / 5..1, U x * r x)
    (∫ x : ℝ in 0..3 / 5, L x ^ 2)
    (∫ x : ℝ in 3 / 5..1, U x ^ 2)
    (∫ x : ℝ in 0..3 / 5, r x ^ 2)
    (∫ x : ℝ in 3 / 5..1, r x ^ 2)
    hNL hNU hML hMU hcauchyL' hcauchyU'
  have hrLInt : IntervalIntegrable (fun x : ℝ ↦ r x ^ 2)
      volume 0 (3 / 5) := by
    exact (hr.continuous.pow 2).intervalIntegrable _ _
  have hrUInt : IntervalIntegrable (fun x : ℝ ↦ r x ^ 2)
      volume (3 / 5) 1 := by
    exact (hr.continuous.pow 2).intervalIntegrable _ _
  have hmassSplit :=
    intervalIntegral.integral_add_adjacent_intervals hrLInt hrUInt
  have hmass : 0 ≤ ∫ x : ℝ in 0..1, r x ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun _ _ ↦ sq_nonneg _)
  dsimp only [FourCellOddP11GalerkinResidualSelectorTwoStripNormBound] at hnorm
  have hnormScaled := mul_le_mul_of_nonneg_right hnorm hmass
  have hpair :=
    fourCellOddCoreLocalBilinear_galerkinResidual_P11Plus_eq_selectorResiduals
      a₃ a₅ a₇ a₉ b₁ b₃ b₅ b₇ b₉ r hr hodd h1 h3 h5 h7 h9
  dsimp only [L, U] at htwo hpair hnormScaled
  rw [hpair]
  rw [hmassSplit] at htwo
  nlinarith only [htwo, hnormScaled]

/-- Exact quotient formulation: a single norm bound modulo the retained
five-mode span implies the universal Galerkin residual dual estimate. -/
theorem fourCellOddP11GalerkinResidualL2Dual_of_moduloFiveModeTwoStripNormBound
    (a₃ a₅ a₇ a₉ : ℝ)
    (hnorm : FourCellOddP11GalerkinResidualModuloFiveModeTwoStripNormBound
      a₃ a₅ a₇ a₉) :
    FourCellOddP11GalerkinResidualL2Dual a₃ a₅ a₇ a₉ := by
  rcases hnorm with ⟨b₁, b₃, b₅, b₇, b₉, hbound⟩
  exact fourCellOddP11GalerkinResidualL2Dual_of_selectorTwoStripNormBound
    a₃ a₅ a₇ a₉ b₁ b₃ b₅ b₇ b₉ hbound

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP11GalerkinResidualRepresenterStructural

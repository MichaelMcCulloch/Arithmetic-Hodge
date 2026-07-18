import ArithmeticHodge.Analysis.MultiplicativeWeilDirectedCorrelationPhysicalStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilFarGlobalCrossStructural

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace

namespace ArithmeticHodge.Analysis.MultiplicativeWeilFarPhysicalKernelStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilDirectedCorrelationPhysicalStructural
open MultiplicativeWeilFarCauchyMomentStructural
open YoshidaBombieriCrossDistribution
open YoshidaBombieriCrossMoments
open YoshidaRenormalizedGeometricKernel

/-!
# The separated Cauchy tail as one physical kernel

For a strictly separated pair the pole `r * x = 1` lies strictly below the
support of the directed correlation.  The scaled Cauchy moment correction is
therefore an honest geometric series with physical kernel

`1 / (x * ((r * x)^2 - 1))`.
-/

private def farCauchyPhysicalSeriesTerm
    (f g : BombieriTest) (r : ℝ) (k : ℕ) (x : ℝ) : ℂ :=
  (x : ℂ)⁻¹ * (((r * x : ℝ) : ℂ)⁻¹) ^ (2 * k + 2) *
    starRingEnd ℂ (bombieriDirectedCorrelation f g x)

private def farCauchyPhysicalKernel
    (f g : BombieriTest) (r x : ℝ) : ℂ :=
  ((x : ℂ) * ((((r * x : ℝ) : ℂ) ^ 2) - 1))⁻¹ *
    starRingEnd ℂ (bombieriDirectedCorrelation f g x)

private def farCauchyPhysicalSeriesBound
    (f g : BombieriTest) (r : ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  x⁻¹ * (r * x)⁻¹ ^ (2 * k + 2) *
    ‖starRingEnd ℂ (bombieriDirectedCorrelation f g x)‖

private theorem farCauchyPhysicalSeriesTerm_hasSum
    (f g : BombieriTest) {r x : ℝ} (hx : 0 < x) (hrx : 1 < r * x) :
    HasSum (fun k : ℕ ↦ farCauchyPhysicalSeriesTerm f g r k x)
      (farCauchyPhysicalKernel f g r x) := by
  let a : ℂ := (((r * x : ℝ) : ℂ)⁻¹)
  have hrxpos : 0 < r * x := zero_lt_one.trans hrx
  have haNorm : ‖a ^ 2‖ < 1 := by
    rw [norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hrxpos]
    have hainv : (r * x)⁻¹ < 1 :=
      (inv_lt_one₀ hrxpos).2 hrx
    have hainv0 : 0 ≤ (r * x)⁻¹ := (inv_pos.mpr hrxpos).le
    nlinarith [mul_self_lt_mul_self hainv0 hainv]
  have hgeomSummable : Summable (fun k : ℕ ↦ (a ^ 2) ^ k) :=
    summable_geometric_of_norm_lt_one haNorm
  have hgeom := hgeomSummable.hasSum
  rw [tsum_geometric_of_norm_lt_one haNorm] at hgeom
  have hscaled :=
    (hgeom.mul_left ((x : ℂ)⁻¹ * a ^ 2)).mul_right
      (starRingEnd ℂ (bombieriDirectedCorrelation f g x))
  have hlimit :
      ((x : ℂ)⁻¹ * a ^ 2 * (1 - a ^ 2)⁻¹) *
          starRingEnd ℂ (bombieriDirectedCorrelation f g x) =
        farCauchyPhysicalKernel f g r x := by
    unfold farCauchyPhysicalKernel
    dsimp only [a]
    have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
    have hrx0 : (((r * x : ℝ) : ℂ)) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr hrxpos.ne'
    have hden : (((r * x : ℝ) : ℂ) ^ 2 - 1) ≠ 0 := by
      apply sub_ne_zero.mpr
      intro h
      have hreal : (r * x) ^ 2 = 1 := by exact_mod_cast h
      nlinarith [sq_nonneg (r * x - 1)]
    congr 1
    field_simp [hx0, hrx0, hden]
  rw [← hlimit]
  apply hscaled.congr_fun
  intro k
  unfold farCauchyPhysicalSeriesTerm
  dsimp only [a]
  rw [show 2 * k + 2 = 2 + 2 * k by omega, pow_add, pow_mul]
  ring

private theorem norm_farCauchyPhysicalSeriesTerm_eq_bound
    (f g : BombieriTest) {r x : ℝ} (hx : 0 < x) (hrx : 0 < r * x)
    (k : ℕ) :
    ‖farCauchyPhysicalSeriesTerm f g r k x‖ =
      farCauchyPhysicalSeriesBound f g r k x := by
  have hr : 0 < r := by nlinarith
  unfold farCauchyPhysicalSeriesTerm farCauchyPhysicalSeriesBound
  simp only [norm_mul, norm_inv, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hx, abs_of_pos hr]

private theorem tsum_farCauchyPhysicalSeriesBound_eq_norm_kernel
    (f g : BombieriTest) {r x : ℝ} (hx : 0 < x) (hrx : 1 < r * x) :
    ∑' k : ℕ, farCauchyPhysicalSeriesBound f g r k x =
      ‖farCauchyPhysicalKernel f g r x‖ := by
  have hrxpos : 0 < r * x := zero_lt_one.trans hrx
  have hr : 0 < r := by nlinarith
  let q : ℝ := (r * x)⁻¹ ^ 2
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by
    dsimp only [q]
    have hinv : (r * x)⁻¹ < 1 := (inv_lt_one₀ hrxpos).2 hrx
    have hinv0 : 0 ≤ (r * x)⁻¹ := (inv_pos.mpr hrxpos).le
    nlinarith [mul_self_lt_mul_self hinv0 hinv]
  have hgeom := tsum_geometric_of_lt_one hq0 hq1
  calc
    ∑' k : ℕ, farCauchyPhysicalSeriesBound f g r k x =
        ∑' k : ℕ,
          (x⁻¹ * (r * x)⁻¹ ^ 2 * q ^ k) *
            ‖starRingEnd ℂ (bombieriDirectedCorrelation f g x)‖ := by
      apply tsum_congr
      intro k
      unfold farCauchyPhysicalSeriesBound
      dsimp only [q]
      rw [show 2 * k + 2 = 2 + 2 * k by omega, pow_add, pow_mul]
      ring
    _ = (x⁻¹ * (r * x)⁻¹ ^ 2) * (∑' k : ℕ, q ^ k) *
          ‖starRingEnd ℂ (bombieriDirectedCorrelation f g x)‖ := by
      rw [← tsum_mul_left, tsum_mul_right]
    _ = (x * ((r * x) ^ 2 - 1))⁻¹ *
          ‖starRingEnd ℂ (bombieriDirectedCorrelation f g x)‖ := by
      rw [hgeom]
      have hx0 : x ≠ 0 := hx.ne'
      have hrx0 : r * x ≠ 0 := hrxpos.ne'
      have hden : (r * x) ^ 2 - 1 ≠ 0 := by
        nlinarith [sq_nonneg (r * x - 1)]
      dsimp only [q]
      field_simp [hx0, hrx0, hden, hr.ne']
    _ = ‖farCauchyPhysicalKernel f g r x‖ := by
      unfold farCauchyPhysicalKernel
      have hdenpos : 0 < (r * x) ^ 2 - 1 := by
        nlinarith [sq_nonneg (r * x - 1)]
      have hcastden :
          (((r * x : ℝ) : ℂ) ^ 2 - 1) =
            (((r * x) ^ 2 - 1 : ℝ) : ℂ) := by norm_num
      rw [hcastden, norm_mul, norm_inv, norm_mul, Complex.norm_real,
        Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos hx, abs_of_pos hdenpos]

private theorem one_lt_r_mul_supportLower
    {af bg r : ℝ} (haf : 0 < af) (hbg : 0 < bg)
    (hsep : bg / af < r) :
    1 < r * (af / bg) := by
  have hraf : bg < r * af := (div_lt_iff₀ haf).mp hsep
  calc
    (1 : ℝ) = bg / bg := by field_simp [hbg.ne']
    _ < (r * af) / bg := (div_lt_div_iff_of_pos_right hbg).2 hraf
    _ = r * (af / bg) := by ring

private theorem integral_farCauchyPhysicalSeriesTerm_Ioi_eq_supportQuotient
    (f g : BombieriTest) {af bf ag bg r : ℝ}
    (haf : 0 < af) (hag : 0 < ag) (hbg : 0 < bg)
    (hf : tsupport f ⊆ Set.Icc af bf)
    (hg : tsupport g ⊆ Set.Icc ag bg) (k : ℕ) :
    (∫ x : ℝ in Set.Ioi 0, farCauchyPhysicalSeriesTerm f g r k x) =
      ∫ x : ℝ in Set.Icc (af / bg) (bf / ag),
        farCauchyPhysicalSeriesTerm f g r k x := by
  apply setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi
  · intro x hx
    exact (div_pos haf hbg).trans_le hx.1
  · intro x hx
    unfold farCauchyPhysicalSeriesTerm
    rw [star_bombieriDirectedCorrelation_eq_zero_outside_supportQuotient
      f g haf hag hbg hf hg hx.2, mul_zero]

private theorem integral_farCauchyPhysicalKernel_Ioi_eq_supportQuotient
    (f g : BombieriTest) {af bf ag bg r : ℝ}
    (haf : 0 < af) (hag : 0 < ag) (hbg : 0 < bg)
    (hf : tsupport f ⊆ Set.Icc af bf)
    (hg : tsupport g ⊆ Set.Icc ag bg) :
    (∫ x : ℝ in Set.Ioi 0, farCauchyPhysicalKernel f g r x) =
      ∫ x : ℝ in Set.Icc (af / bg) (bf / ag),
        farCauchyPhysicalKernel f g r x := by
  apply setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi
  · intro x hx
    exact (div_pos haf hbg).trans_le hx.1
  · intro x hx
    unfold farCauchyPhysicalKernel
    rw [star_bombieriDirectedCorrelation_eq_zero_outside_supportQuotient
      f g haf hag hbg hf hg hx.2, mul_zero]

/-- Strict support separation puts the geometric pole below the physical
correlation support, so the scaled inverse-odd-power series may be integrated
term by term and resummed into one rational kernel. -/
theorem hasSum_integral_farCauchyPhysicalSeriesTerm
    (f g : BombieriTest) {af bf ag bg r : ℝ}
    (hr : 0 < r) (haf : 0 < af) (hag : 0 < ag) (hbg : 0 < bg)
    (hf : tsupport f ⊆ Set.Icc af bf)
    (hg : tsupport g ⊆ Set.Icc ag bg)
    (hsep : bg / af < r) :
    HasSum (fun k : ℕ ↦ ∫ x : ℝ in Set.Ioi 0,
        farCauchyPhysicalSeriesTerm f g r k x)
      (∫ x : ℝ in Set.Ioi 0, farCauchyPhysicalKernel f g r x) := by
  let K : Set ℝ := Set.Icc (af / bg) (bf / ag)
  let μ : Measure ℝ := volume.restrict K
  have hlower : 0 < af / bg := div_pos haf hbg
  have hrlower : 1 < r * (af / bg) :=
    one_lt_r_mul_supportLower haf hbg hsep
  have hKpos : K ⊆ Set.Ioi 0 := by
    intro x hx
    exact hlower.trans_le hx.1
  have hrx (x : ℝ) (hx : x ∈ K) : 1 < r * x := by
    exact hrlower.trans_le (mul_le_mul_of_nonneg_left hx.1 hr.le)
  have hHInt : IntegrableOn
      (fun x : ℝ ↦ starRingEnd ℂ (bombieriDirectedCorrelation f g x)) K :=
    (star_bombieriDirectedCorrelation_integrableOn_Ioi
      f g haf hag hbg hf hg).mono_set hKpos
  have hscalarTermContinuous (k : ℕ) : ContinuousOn
      (fun x : ℝ ↦
        (x : ℂ)⁻¹ * (((r * x : ℝ) : ℂ)⁻¹) ^ (2 * k + 2)) K := by
    intro x hx
    have hx0 : (x : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (hKpos hx).ne'
    have hrx0 : (((r * x : ℝ) : ℂ)) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (zero_lt_one.trans (hrx x hx)).ne'
    have hxContinuous : ContinuousAt (fun y : ℝ ↦ (y : ℂ)) x :=
      Complex.ofRealCLM.continuous.continuousAt
    have hrxContinuous : ContinuousAt
        (fun y : ℝ ↦ ((r * y : ℝ) : ℂ)) x := by fun_prop
    exact ((hxContinuous.inv₀ hx0).mul
      ((hrxContinuous.inv₀ hrx0).pow (2 * k + 2))).continuousWithinAt
  have htermInt (k : ℕ) : IntegrableOn
      (farCauchyPhysicalSeriesTerm f g r k) K := by
    unfold farCauchyPhysicalSeriesTerm
    exact hHInt.continuousOn_mul (hscalarTermContinuous k) isCompact_Icc
  have hmeas (k : ℕ) :
      AEStronglyMeasurable (farCauchyPhysicalSeriesTerm f g r k) μ := by
    simpa only [μ, IntegrableOn] using (htermInt k).1
  have hbound (k : ℕ) : ∀ᵐ x : ℝ ∂μ,
      ‖farCauchyPhysicalSeriesTerm f g r k x‖ ≤
        farCauchyPhysicalSeriesBound f g r k x := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact (norm_farCauchyPhysicalSeriesTerm_eq_bound
      f g (hKpos hx) (zero_lt_one.trans (hrx x hx)) k).le
  have hboundSummable : ∀ᵐ x : ℝ ∂μ,
      Summable (fun k : ℕ ↦ farCauchyPhysicalSeriesBound f g r k x) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    have hs := (farCauchyPhysicalSeriesTerm_hasSum
      f g (hKpos hx) (hrx x hx)).summable.norm
    exact hs.congr fun k ↦
      norm_farCauchyPhysicalSeriesTerm_eq_bound
        f g (hKpos hx) (zero_lt_one.trans (hrx x hx)) k
  have hscalarKernelContinuous : ContinuousOn
      (fun x : ℝ ↦
        ((x : ℂ) * ((((r * x : ℝ) : ℂ) ^ 2) - 1))⁻¹) K := by
    intro x hx
    have hx0 : (x : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (hKpos hx).ne'
    have hden : ((((r * x : ℝ) : ℂ) ^ 2) - 1) ≠ 0 := by
      apply sub_ne_zero.mpr
      intro h
      have hreal : (r * x) ^ 2 = 1 := by exact_mod_cast h
      nlinarith [sq_nonneg (r * x - 1), hrx x hx]
    have hbase : ContinuousAt
        (fun y : ℝ ↦
          (y : ℂ) * ((((r * y : ℝ) : ℂ) ^ 2) - 1)) x := by fun_prop
    exact (hbase.inv₀ (mul_ne_zero hx0 hden)).continuousWithinAt
  have hkernelInt : IntegrableOn (farCauchyPhysicalKernel f g r) K := by
    unfold farCauchyPhysicalKernel
    exact hHInt.continuousOn_mul hscalarKernelContinuous isCompact_Icc
  have hboundIntegrable : Integrable
      (fun x : ℝ ↦ ∑' k : ℕ,
        farCauchyPhysicalSeriesBound f g r k x) μ := by
    have hnorm : IntegrableOn
        (fun x : ℝ ↦ ‖farCauchyPhysicalKernel f g r x‖) K :=
      hkernelInt.norm
    have hcongr : ∀ x ∈ K,
        (∑' k : ℕ, farCauchyPhysicalSeriesBound f g r k x) =
          ‖farCauchyPhysicalKernel f g r x‖ := by
      intro x hx
      exact tsum_farCauchyPhysicalSeriesBound_eq_norm_kernel
        f g (hKpos hx) (hrx x hx)
    simpa only [μ, IntegrableOn] using
      hnorm.congr_fun (fun x hx ↦ (hcongr x hx).symm) measurableSet_Icc
  have hlim : ∀ᵐ x : ℝ ∂μ,
      HasSum (fun k : ℕ ↦ farCauchyPhysicalSeriesTerm f g r k x)
        (farCauchyPhysicalKernel f g r x) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact farCauchyPhysicalSeriesTerm_hasSum f g (hKpos hx) (hrx x hx)
  have hKsum := MeasureTheory.hasSum_integral_of_dominated_convergence
    (fun k : ℕ ↦ farCauchyPhysicalSeriesBound f g r k) hmeas hbound
      hboundSummable hboundIntegrable hlim
  rw [integral_farCauchyPhysicalKernel_Ioi_eq_supportQuotient
    f g haf hag hbg hf hg]
  simpa only [K, μ,
    integral_farCauchyPhysicalSeriesTerm_Ioi_eq_supportQuotient
      f g haf hag hbg hf hg] using hKsum

private theorem rpow_neg_odd_eq_inv_pow
    (k : ℕ) (x : ℝ) :
    ((x ^ (-(2 * (k : ℝ) + 3)) : ℝ) : ℂ) =
      ((x : ℂ)⁻¹) ^ (2 * k + 3) := by
  rw [show -(2 * (k : ℝ) + 3) = -((2 * k + 3 : ℕ) : ℝ) by
    push_cast
    ring]
  rw [Real.rpow_neg_natCast]
  rw [zpow_neg, inv_pow]
  norm_cast

private theorem sqrt_mul_exp_neg_oddRate_succ_log
    (r : ℝ) (hr : 0 < r) (k : ℕ) :
    Real.sqrt r * Real.exp (-oddRate (k + 1) * Real.log r) =
      r⁻¹ ^ (2 * (k + 1)) := by
  have hsqrt : Real.sqrt r = Real.exp (Real.log r / 2) := by
    rw [← Real.exp_log (Real.sqrt_pos.2 hr), Real.log_sqrt hr.le]
  have hrinv : r⁻¹ = Real.exp (-Real.log r) := by
    rw [Real.exp_neg, Real.exp_log hr]
  rw [hsqrt, hrinv, ← Real.exp_nat_mul, ← Real.exp_add]
  unfold oddRate
  congr 1
  push_cast
  ring

/-- Each scaled rank-one Cauchy moment is exactly the corresponding physical
inverse-power integral. -/
theorem scaled_farCauchyMoment_eq_integral_seriesTerm
    (f g : BombieriTest) (r : ℝ) (hr : 0 < r) (k : ℕ) :
    ((Real.sqrt r : ℝ) : ℂ) *
        (((Real.exp (-oddRate (k + 1) * Real.log r) : ℝ) : ℂ) *
          starRingEnd ℂ
            (bombieriCriticalMoment f (oddRate (k + 1))) *
          bombieriCriticalMoment g (-oddRate (k + 1))) =
      ∫ x : ℝ in Set.Ioi 0,
        farCauchyPhysicalSeriesTerm f g r k x := by
  have hmoment :=
    integral_inverseOddPower_mul_star_bombieriDirectedCorrelation_eq_criticalMoments
      f g k
  have hrate : oddRate (k + 1) = 2 * (k : ℝ) + 5 / 2 := by
    unfold oddRate
    push_cast
    ring
  have hmoment' :
      (∫ x : ℝ in Set.Ioi 0,
        ((x ^ (-(2 * (k : ℝ) + 3)) : ℝ) : ℂ) *
          starRingEnd ℂ (bombieriDirectedCorrelation f g x)) =
        starRingEnd ℂ
            (bombieriCriticalMoment f (oddRate (k + 1))) *
          bombieriCriticalMoment g (-oddRate (k + 1)) := by
    simpa only [hrate] using hmoment
  calc
    ((Real.sqrt r : ℝ) : ℂ) *
          (((Real.exp (-oddRate (k + 1) * Real.log r) : ℝ) : ℂ) *
            starRingEnd ℂ
              (bombieriCriticalMoment f (oddRate (k + 1))) *
            bombieriCriticalMoment g (-oddRate (k + 1))) =
        (((Real.sqrt r : ℝ) : ℂ) *
          ((Real.exp (-oddRate (k + 1) * Real.log r) : ℝ) : ℂ)) *
          (starRingEnd ℂ
              (bombieriCriticalMoment f (oddRate (k + 1))) *
            bombieriCriticalMoment g (-oddRate (k + 1))) := by ring
    _ = (((Real.sqrt r : ℝ) : ℂ) *
          ((Real.exp (-oddRate (k + 1) * Real.log r) : ℝ) : ℂ)) *
        (∫ x : ℝ in Set.Ioi 0,
          ((x ^ (-(2 * (k : ℝ) + 3)) : ℝ) : ℂ) *
            starRingEnd ℂ (bombieriDirectedCorrelation f g x)) := by
      rw [hmoment']
    _ = ((r⁻¹ ^ (2 * (k + 1)) : ℝ) : ℂ) *
        (∫ x : ℝ in Set.Ioi 0,
          ((x ^ (-(2 * (k : ℝ) + 3)) : ℝ) : ℂ) *
            starRingEnd ℂ (bombieriDirectedCorrelation f g x)) := by
      rw [← Complex.ofReal_mul,
        sqrt_mul_exp_neg_oddRate_succ_log r hr k]
    _ = ∫ x : ℝ in Set.Ioi 0,
        ((((r * x : ℝ) : ℂ)⁻¹ ^ 2) ^ (k + 1)) *
          (x : ℂ)⁻¹ *
          starRingEnd ℂ (bombieriDirectedCorrelation f g x) := by
      rw [show ((r⁻¹ ^ (2 * (k + 1)) : ℝ) : ℂ) *
          (∫ x : ℝ in Set.Ioi 0,
            ((x ^ (-(2 * (k : ℝ) + 3)) : ℝ) : ℂ) *
              starRingEnd ℂ (bombieriDirectedCorrelation f g x)) =
          ∫ x : ℝ in Set.Ioi 0,
            ((r⁻¹ ^ (2 * (k + 1)) : ℝ) : ℂ) *
              (((x ^ (-(2 * (k : ℝ) + 3)) : ℝ) : ℂ) *
                starRingEnd ℂ (bombieriDirectedCorrelation f g x)) by
        exact (MeasureTheory.integral_const_mul
          (μ := volume.restrict (Set.Ioi 0)) _ _).symm]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      change ((r⁻¹ ^ (2 * (k + 1)) : ℝ) : ℂ) *
          (((x ^ (-(2 * (k : ℝ) + 3)) : ℝ) : ℂ) *
            starRingEnd ℂ (bombieriDirectedCorrelation f g x)) =
        ((((r * x : ℝ) : ℂ)⁻¹ ^ 2) ^ (k + 1)) *
          (x : ℂ)⁻¹ *
          starRingEnd ℂ (bombieriDirectedCorrelation f g x)
      rw [rpow_neg_odd_eq_inv_pow]
      push_cast
      rw [mul_inv, mul_pow, mul_pow, ← pow_mul, ← pow_mul]
      norm_num [pow_succ]
      ring
    _ = ∫ x : ℝ in Set.Ioi 0,
        farCauchyPhysicalSeriesTerm f g r k x := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      unfold farCauchyPhysicalSeriesTerm
      dsimp only
      rw [← pow_mul]
      rw [show 2 * (k + 1) = 2 * k + 2 by omega]
      ring

/-- The whole scaled Cauchy moment correction resums to the single physical
rational kernel whose pole lies below the separated support. -/
theorem tsum_scaled_farCauchyMomentCorrection_eq_physicalKernel
    (f g : BombieriTest) {af bf ag bg r : ℝ}
    (hr : 0 < r) (haf : 0 < af) (hag : 0 < ag) (hbg : 0 < bg)
    (hf : tsupport f ⊆ Set.Icc af bf)
    (hg : tsupport g ⊆ Set.Icc ag bg)
    (hsep : bg / af < r) :
    (∑' k : ℕ,
      ((Real.sqrt r : ℝ) : ℂ) *
        (((Real.exp (-oddRate (k + 1) * Real.log r) : ℝ) : ℂ) *
          starRingEnd ℂ
            (bombieriCriticalMoment f (oddRate (k + 1))) *
          bombieriCriticalMoment g (-oddRate (k + 1)))) =
      ∫ x : ℝ in Set.Ioi 0,
        starRingEnd ℂ (bombieriDirectedCorrelation f g x) /
          ((x * ((r * x) ^ 2 - 1) : ℝ) : ℂ) := by
  have hsum := hasSum_integral_farCauchyPhysicalSeriesTerm
    f g hr haf hag hbg hf hg hsep
  calc
    (∑' k : ℕ,
        ((Real.sqrt r : ℝ) : ℂ) *
          (((Real.exp (-oddRate (k + 1) * Real.log r) : ℝ) : ℂ) *
            starRingEnd ℂ
              (bombieriCriticalMoment f (oddRate (k + 1))) *
            bombieriCriticalMoment g (-oddRate (k + 1)))) =
        ∑' k : ℕ, ∫ x : ℝ in Set.Ioi 0,
          farCauchyPhysicalSeriesTerm f g r k x := by
      apply tsum_congr
      intro k
      exact scaled_farCauchyMoment_eq_integral_seriesTerm f g r hr k
    _ = ∫ x : ℝ in Set.Ioi 0,
        farCauchyPhysicalKernel f g r x := hsum.tsum_eq
    _ = ∫ x : ℝ in Set.Ioi 0,
        starRingEnd ℂ (bombieriDirectedCorrelation f g x) /
          ((x * ((r * x) ^ 2 - 1) : ℝ) : ℂ) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      unfold farCauchyPhysicalKernel
      push_cast
      rw [div_eq_mul_inv]
      ring

/-- Exact physical form of every strictly separated global cross: the
normalized smoothed Mangoldt discrepancy minus one nonsingular rational
kernel integral. -/
theorem sqrt_mul_bombieriTwoBlockGlobalCrossSymbol_normalizedDilation_eq_physicalDiscrepancy_sub_kernel
    (f g : BombieriTest) {af bf ag bg r : ℝ}
    (hr : 0 < r) (haf : 0 < af) (hag : 0 < ag) (hbg : 0 < bg)
    (hf : tsupport f ⊆ Set.Icc af bf)
    (hg : tsupport g ⊆ Set.Icc ag bg)
    (hsep : bg / af < r) :
    ((Real.sqrt r : ℝ) : ℂ) *
        bombieriTwoBlockGlobalCrossSymbol f (normalizedDilation r hr g) =
      ((r : ℂ) *
          (∫ x : ℝ in Set.Ioi 0,
            starRingEnd ℂ (bombieriDirectedCorrelation f g x)) -
        ∑' n : ℕ, (ArithmeticFunction.vonMangoldt (n + 1) : ℂ) *
          starRingEnd ℂ (bombieriDirectedCorrelation f g
            (r⁻¹ * (n + 1 : ℕ)))) -
      ∫ x : ℝ in Set.Ioi 0,
        starRingEnd ℂ (bombieriDirectedCorrelation f g x) /
          ((x * ((r * x) ^ 2 - 1) : ℝ) : ℂ) := by
  rw [
    sqrt_mul_bombieriTwoBlockGlobalCrossSymbol_normalizedDilation_eq_mangoldtDiscrepancy_sub_momentCorrection
      f g hr haf hag hbg hf hg hsep,
    tsum_scaled_farCauchyMomentCorrection_eq_physicalKernel
      f g hr haf hag hbg hf hg hsep,
    integral_star_bombieriDirectedCorrelation_eq_mellin_endpoints]
  ring

end

end ArithmeticHodge.Analysis.MultiplicativeWeilFarPhysicalKernelStructural

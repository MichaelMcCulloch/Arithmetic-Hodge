import ArithmeticHodge.Analysis.YoshidaFourCellRegularKernelWideEnvelope
import ArithmeticHodge.Analysis.YoshidaFactorTwoEndpointBilinear
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCenteredP9Structural
import ArithmeticHodge.Analysis.YoshidaFourCellParityOperatorStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP3P9RegularCrossStructural

noncomputable section

open CenteredOddOneThreeEnergy
open YoshidaEndpointOcticPotential
open YoshidaConstantBounds
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointParityPencil
open YoshidaFactorTwoPhaseCenteredP9Structural
open YoshidaFourCellParityOperatorStructural
open YoshidaFourCellRegularKernelWideEnvelope
open YoshidaEndpointEvenProjectedRemainderEnvelopeKernel
open YoshidaEndpointWeightedCauchy
open YoshidaRegularKernelBound

/-!
# The four-cell regular-kernel `P₃/P₉` cross

The exact centered correlation has all polynomial moments through degree four
equal to zero.  Thus the sixth-order kernel model leaves only its fifth-order
term, while the range-sensitive analytic remainder is controlled by the exact
correlation `L²` mass.
-/

/-- Exact symmetric centered correlation between the classical odd modes
`P₃` and `P₉`. -/
def fourCellOddP3P9Correlation (t : ℝ) : ℝ :=
  -t + (39 / 2 : ℝ) * t ^ 2 - (245 / 2 : ℝ) * t ^ 3 +
    (715 / 2 : ℝ) * t ^ 4 - (2205 / 4 : ℝ) * t ^ 5 +
      (7293 / 16 : ℝ) * t ^ 6 - (693 / 4 : ℝ) * t ^ 7 +
        (2145 / 128 : ℝ) * t ^ 9 - (429 / 256 : ℝ) * t ^ 11 +
          (85 / 1024 : ℝ) * t ^ 13

private theorem integral_polynomial_twelve
    (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ l r : ℝ) :
    (∫ x : ℝ in l..r,
      a₀ * x ^ 0 + a₁ * x ^ 1 + a₂ * x ^ 2 + a₃ * x ^ 3 +
        a₄ * x ^ 4 + a₅ * x ^ 5 + a₆ * x ^ 6 + a₇ * x ^ 7 +
        a₈ * x ^ 8 + a₉ * x ^ 9 + a₁₀ * x ^ 10 +
        a₁₁ * x ^ 11 + a₁₂ * x ^ 12) =
      a₀ * (r - l) + a₁ * (r ^ 2 - l ^ 2) / 2 +
        a₂ * (r ^ 3 - l ^ 3) / 3 + a₃ * (r ^ 4 - l ^ 4) / 4 +
        a₄ * (r ^ 5 - l ^ 5) / 5 + a₅ * (r ^ 6 - l ^ 6) / 6 +
        a₆ * (r ^ 7 - l ^ 7) / 7 + a₇ * (r ^ 8 - l ^ 8) / 8 +
        a₈ * (r ^ 9 - l ^ 9) / 9 + a₉ * (r ^ 10 - l ^ 10) / 10 +
        a₁₀ * (r ^ 11 - l ^ 11) / 11 +
        a₁₁ * (r ^ 12 - l ^ 12) / 12 +
        a₁₂ * (r ^ 13 - l ^ 13) / 13 := by
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) l r)
    (Continuous.intervalIntegrable (by fun_prop) l r)]
  repeat rw [intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  ring

set_option maxHeartbeats 800000 in
theorem factorTwoCenteredCorrelationBilinear_P3_P9 (t : ℝ) :
    factorTwoCenteredCorrelationBilinear centeredP3 factorTwoCenteredP9 t =
      fourCellOddP3P9Correlation t := by
  unfold factorTwoCenteredCorrelationBilinear
  rw [factorTwoCenteredCrossCorrelation_swap_of_odd_odd
    (by intro x; unfold centeredP3; ring) odd_factorTwoCenteredP9]
  ring_nf
  unfold factorTwoCenteredCrossCorrelation centeredP3
  simp_rw [factorTwoCenteredP9_eq]
  rw [show (fun x : ℝ ↦ ((5 * (t + x) ^ 3 - 3 * (t + x)) / 2) *
      ((12155 * x ^ 9 - 25740 * x ^ 7 + 18018 * x ^ 5 -
        4620 * x ^ 3 + 315 * x) / 128)) =
      fun x ↦
        0 * x ^ 0 +
        ((1575 / 256 : ℝ) * t ^ 3 - (945 / 256 : ℝ) * t) * x ^ 1 +
        ((4725 / 256 : ℝ) * t ^ 2 - (945 / 256 : ℝ)) * x ^ 2 +
        (-(5775 / 64 : ℝ) * t ^ 3 + (18585 / 256 : ℝ) * t) * x ^ 3 +
        (-(17325 / 64 : ℝ) * t ^ 2 + (15435 / 256 : ℝ)) * x ^ 4 +
        ((45045 / 128 : ℝ) * t ^ 3 - (61677 / 128 : ℝ) * t) * x ^ 5 +
        ((135135 / 128 : ℝ) * t ^ 2 - (38577 / 128 : ℝ)) * x ^ 6 +
        (-(32175 / 64 : ℝ) * t ^ 3 + (173745 / 128 : ℝ) * t) * x ^ 7 +
        (-(96525 / 64 : ℝ) * t ^ 2 + (83655 / 128 : ℝ)) * x ^ 8 +
        ((60775 / 256 : ℝ) * t ^ 3 - (422565 / 256 : ℝ) * t) * x ^ 9 +
        ((182325 / 256 : ℝ) * t ^ 2 - (165165 / 256 : ℝ)) * x ^ 10 +
        ((182325 / 256 : ℝ) * t) * x ^ 11 +
        (60775 / 256 : ℝ) * x ^ 12 by
      funext x
      ring,
    integral_polynomial_twelve]
  unfold fourCellOddP3P9Correlation
  ring

set_option maxHeartbeats 800000 in
theorem integral_fourCellOddP3P9Correlation_sq :
    (∫ t : ℝ in 0..2, fourCellOddP3P9Correlation t ^ 2) =
      (625424 / 1003917915 : ℝ) := by
  unfold fourCellOddP3P9Correlation
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [integral_pow]
  norm_num

private theorem sq_intervalIntegral_mul_le_zero_two
    (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    (∫ x : ℝ in 0..2, f x * g x) ^ 2 ≤
      (∫ x : ℝ in 0..2, f x ^ 2) *
        (∫ x : ℝ in 0..2, g x ^ 2) := by
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 2)
  have hfMeas : AEStronglyMeasurable f μ :=
    hf.aestronglyMeasurable.restrict
  have hgMeas : AEStronglyMeasurable g μ :=
    hg.aestronglyMeasurable.restrict
  have hfLp : MemLp f 2 μ := by
    rw [memLp_two_iff_integrable_sq_norm hfMeas]
    have hcompact : IntegrableOn (fun x : ℝ ↦ ‖f x‖ ^ 2)
        (Icc (0 : ℝ) 2) :=
      (hf.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
    exact hcompact.mono_set Ioc_subset_Icc_self
  have hgLp : MemLp g 2 μ := by
    rw [memLp_two_iff_integrable_sq_norm hgMeas]
    have hcompact : IntegrableOn (fun x : ℝ ↦ ‖g x‖ ^ 2)
        (Icc (0 : ℝ) 2) :=
      (hg.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
    exact hcompact.mono_set Ioc_subset_Icc_self
  have h := sq_integral_mul_le_weighted μ (fun _ : ℝ ↦ 1) f g
    (by simp) (by simpa using hfLp) (by simpa using hgLp)
  repeat rw [intervalIntegral.integral_of_le (by norm_num)]
  simpa only [μ, div_one, one_mul] using h

theorem integral_abs_fourCellOddP3P9Correlation_lt :
    (∫ t : ℝ in 0..2, |fourCellOddP3P9Correlation t|) <
      (1 / 25 : ℝ) := by
  have hcs := sq_intervalIntegral_mul_le_zero_two
    (fun _ : ℝ ↦ 1) (fun t ↦ |fourCellOddP3P9Correlation t|)
    continuous_const (by unfold fourCellOddP3P9Correlation; fun_prop)
  simp only [one_mul, one_pow, sq_abs] at hcs
  rw [show (∫ _t : ℝ in 0..2, (1 : ℝ)) = 2 by norm_num,
    integral_fourCellOddP3P9Correlation_sq] at hcs
  have hnonneg : 0 ≤ ∫ t : ℝ in 0..2,
      |fourCellOddP3P9Correlation t| :=
    intervalIntegral.integral_nonneg (by norm_num) (fun _ _ ↦ abs_nonneg _)
  have hrat :
      (2 : ℝ) * (625424 / 1003917915) < (1 / 25 : ℝ) ^ 2 := by
    norm_num
  nlinarith

/-- Signed analytic remainder after replacing the regular kernel by its
sixth-order polynomial on the `P₃/P₉` correlation. -/
def fourCellOddP3P9RegularEnvelopeError : ℝ :=
  ∫ t : ℝ in 0..2,
    (yoshidaRegularKernel (fourCellOperatorHalfWidth * t) -
      yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t)) *
        fourCellOddP3P9Correlation t

private theorem fourCellOddP3P9RegularEnvelope_pointwise
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

private theorem measurable_yoshidaRegularKernel_local :
    Measurable yoshidaRegularKernel := by
  unfold yoshidaRegularKernel
  apply Measurable.ite
  · simpa only [Set.setOf_eq_eq_singleton] using
      measurableSet_singleton (0 : ℝ)
  · exact measurable_const
  · exact ((Real.measurable_exp.comp (measurable_id.div_const 2)).div
      (measurable_const.mul Real.measurable_sinh)).sub
        (measurable_const.div (measurable_const.mul measurable_id))

private theorem intervalIntegrable_fourCellOddP3P9RegularEnvelope :
    IntervalIntegrable
      (fun t ↦
        (yoshidaRegularKernel (fourCellOperatorHalfWidth * t) -
          yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t)) *
            fourCellOddP3P9Correlation t)
      volume 0 2 := by
  let f : ℝ → ℝ := fun t ↦
    (yoshidaRegularKernel (fourCellOperatorHalfWidth * t) -
      yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t)) *
        fourCellOddP3P9Correlation t
  let g : ℝ → ℝ := fun t ↦
    (1 / 80000 : ℝ) * |fourCellOddP3P9Correlation t|
  have hcorr : Continuous fourCellOddP3P9Correlation := by
    unfold fourCellOddP3P9Correlation
    fun_prop
  have hgIcc : IntegrableOn g (Icc (0 : ℝ) 2) volume := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    exact (continuous_const.mul hcorr.abs).continuousOn
  have hg : Integrable g (volume.restrict (Ioc (0 : ℝ) 2)) :=
    hgIcc.mono_set Ioc_subset_Icc_self
  have hfmeas : AEStronglyMeasurable f
      (volume.restrict (Ioc (0 : ℝ) 2)) := by
    apply Measurable.aestronglyMeasurable
    dsimp only [f]
    exact ((measurable_yoshidaRegularKernel_local.comp
      (measurable_const.mul measurable_id)).sub
        (by unfold yoshidaRegularKernelPolynomial6; fun_prop)).mul
          hcorr.measurable
  have hfg : ∀ᵐ t : ℝ ∂(volume.restrict (Ioc (0 : ℝ) 2)),
      ‖f t‖ ≤ g t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have htIcc : t ∈ Icc (0 : ℝ) 2 := ⟨ht.1.le, ht.2⟩
    have henv := fourCellOddP3P9RegularEnvelope_pointwise htIcc
    dsimp only [f, g]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg henv.1]
    exact mul_le_mul_of_nonneg_right henv.2.le
      (abs_nonneg (fourCellOddP3P9Correlation t))
  constructor
  · exact Integrable.mono' hg hfmeas hfg
  · simp

theorem abs_fourCellOddP3P9RegularEnvelopeError_lt :
    |fourCellOddP3P9RegularEnvelopeError| < (1 / 2000000 : ℝ) := by
  let f : ℝ → ℝ := fun t ↦
    (yoshidaRegularKernel (fourCellOperatorHalfWidth * t) -
      yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t)) *
        fourCellOddP3P9Correlation t
  let g : ℝ → ℝ := fun t ↦
    (1 / 80000 : ℝ) * |fourCellOddP3P9Correlation t|
  have hf : IntervalIntegrable f volume 0 2 := by
    dsimp only [f]
    exact intervalIntegrable_fourCellOddP3P9RegularEnvelope
  have hcorr : Continuous fourCellOddP3P9Correlation := by
    unfold fourCellOddP3P9Correlation
    fun_prop
  have hg : IntervalIntegrable g volume 0 2 := by
    dsimp only [g]
    exact (hcorr.abs.const_mul (1 / 80000 : ℝ)).intervalIntegrable 0 2
  have hmono :
      (∫ t : ℝ in 0..2, |f t|) ≤ ∫ t : ℝ in 0..2, g t := by
    apply intervalIntegral.integral_mono_on (by norm_num) hf.abs hg
    intro t ht
    have henv := fourCellOddP3P9RegularEnvelope_pointwise ht
    dsimp only [f, g]
    rw [abs_mul, abs_of_nonneg henv.1]
    exact mul_le_mul_of_nonneg_right henv.2.le
      (abs_nonneg (fourCellOddP3P9Correlation t))
  have habs :
      |fourCellOddP3P9RegularEnvelopeError| ≤
        (1 / 80000 : ℝ) *
          (∫ t : ℝ in 0..2, |fourCellOddP3P9Correlation t|) := by
    calc
      |fourCellOddP3P9RegularEnvelopeError| =
          |∫ t : ℝ in 0..2, f t| := by
        unfold fourCellOddP3P9RegularEnvelopeError
        rfl
      _ ≤ ∫ t : ℝ in 0..2, |f t| :=
        intervalIntegral.abs_integral_le_integral_abs (by norm_num)
      _ ≤ ∫ t : ℝ in 0..2, g t := hmono
      _ = (1 / 80000 : ℝ) *
          (∫ t : ℝ in 0..2, |fourCellOddP3P9Correlation t|) := by
        dsimp only [g]
        rw [intervalIntegral.integral_const_mul]
  have hmass := integral_abs_fourCellOddP3P9Correlation_lt
  nlinarith

/-- Exact sixth-order polynomial contribution to the four-cell `P₃/P₉`
regular cross.  All kernel moments except the fifth-order one cancel. -/
def fourCellOddP3P9RegularPolynomial : ℝ :=
  -(19375 / 2306751533678592 : ℝ) * Real.log 2 ^ 5

set_option maxHeartbeats 800000 in
theorem integral_fourCellRegularPolynomial_mul_P3P9Correlation :
    (∫ t : ℝ in 0..2,
      yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t) *
        fourCellOddP3P9Correlation t) =
      fourCellOddP3P9RegularPolynomial := by
  unfold yoshidaRegularKernelPolynomial6 fourCellOperatorHalfWidth
    fourCellOddP3P9Correlation fourCellOddP3P9RegularPolynomial
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [intervalIntegral.integral_const_mul]
  repeat rw [integral_pow]
  norm_num
  ring

theorem fourCellOddP3P9RegularPolynomial_abs_lt :
    |fourCellOddP3P9RegularPolynomial| < (1 / 1000000000 : ℝ) := by
  have hlogPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogUpper : Real.log 2 < (7 / 10 : ℝ) := by
    have h := strict_log_two_bounds.2
    linarith
  have h5 : Real.log 2 ^ 5 < (7 / 10 : ℝ) ^ 5 :=
    pow_lt_pow_left₀ hlogUpper hlogPos.le (by norm_num)
  have hpowPos : 0 < Real.log 2 ^ 5 := pow_pos hlogPos 5
  unfold fourCellOddP3P9RegularPolynomial
  have hneg :
      -(19375 / 2306751533678592 : ℝ) * Real.log 2 ^ 5 < 0 :=
    mul_neg_of_neg_of_pos (by norm_num) hpowPos
  rw [abs_of_neg hneg]
  calc
    -(-(19375 / 2306751533678592 : ℝ) * Real.log 2 ^ 5) =
        (19375 / 2306751533678592 : ℝ) * Real.log 2 ^ 5 := by ring
    _ < (19375 / 2306751533678592 : ℝ) * (7 / 10 : ℝ) ^ 5 :=
      mul_lt_mul_of_pos_left h5 (by norm_num)
    _ < (1 / 1000000000 : ℝ) := by norm_num

theorem integral_fourCellRegularKernel_mul_P3P9Correlation_eq :
    (∫ t : ℝ in 0..2,
      yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
        fourCellOddP3P9Correlation t) =
      fourCellOddP3P9RegularPolynomial +
        fourCellOddP3P9RegularEnvelopeError := by
  have hpoly : IntervalIntegrable
      (fun t : ℝ ↦
        yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t) *
          fourCellOddP3P9Correlation t) volume 0 2 := by
    exact (by
      unfold yoshidaRegularKernelPolynomial6 fourCellOperatorHalfWidth
        fourCellOddP3P9Correlation
      fun_prop : Continuous (fun t : ℝ ↦
        yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t) *
          fourCellOddP3P9Correlation t)).intervalIntegrable 0 2
  rw [show (fun t : ℝ ↦
      yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
        fourCellOddP3P9Correlation t) = fun t ↦
      yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t) *
          fourCellOddP3P9Correlation t +
        (yoshidaRegularKernel (fourCellOperatorHalfWidth * t) -
          yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t)) *
            fourCellOddP3P9Correlation t by
      funext t
      ring,
    intervalIntegral.integral_add hpoly
      intervalIntegrable_fourCellOddP3P9RegularEnvelope,
    integral_fourCellRegularPolynomial_mul_P3P9Correlation]
  rfl

/-- The regular-kernel `P₃/P₉` cross is structurally negligible at the
four-cell scale.  The proof uses an exact polynomial correlation, exact moment
cancellation, and a range-sensitive analytic envelope; it contains no sampled
or floating-point certificate. -/
theorem abs_integral_fourCellRegularKernel_mul_correlation_P3_P9_lt :
    |∫ t : ℝ in 0..2,
      yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
        factorTwoCenteredCorrelationBilinear
          centeredP3 factorTwoCenteredP9 t| < (1 / 100000 : ℝ) := by
  rw [show (fun t : ℝ ↦
      yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
        factorTwoCenteredCorrelationBilinear
          centeredP3 factorTwoCenteredP9 t) = fun t ↦
      yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
        fourCellOddP3P9Correlation t by
      funext t
      rw [factorTwoCenteredCorrelationBilinear_P3_P9],
    integral_fourCellRegularKernel_mul_P3P9Correlation_eq]
  have hp := fourCellOddP3P9RegularPolynomial_abs_lt
  have he := abs_fourCellOddP3P9RegularEnvelopeError_lt
  calc
    |fourCellOddP3P9RegularPolynomial +
        fourCellOddP3P9RegularEnvelopeError| ≤
      |fourCellOddP3P9RegularPolynomial| +
        |fourCellOddP3P9RegularEnvelopeError| := abs_add_le _ _
    _ < (1 / 1000000000 : ℝ) + 1 / 2000000 := add_lt_add hp he
    _ < (1 / 100000 : ℝ) := by norm_num

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP3P9RegularCrossStructural

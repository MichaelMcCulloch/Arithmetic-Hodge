import ArithmeticHodge.Analysis.YoshidaFourCellRegularKernelWideEnvelope
import ArithmeticHodge.Analysis.YoshidaFactorTwoEndpointBilinear
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
import ArithmeticHodge.Analysis.YoshidaFourCellParityOperatorStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP3P7RegularCrossStructural

noncomputable section

open CenteredOddOneThreeEnergy
open YoshidaEndpointOcticPotential
open YoshidaConstantBounds
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointParityPencil
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
open YoshidaFourCellParityOperatorStructural
open YoshidaFourCellRegularKernelWideEnvelope
open YoshidaEndpointEvenProjectedRemainderEnvelopeKernel
open YoshidaEndpointWeightedCauchy
open YoshidaRegularKernelBound

/-!
# The four-cell regular-kernel `P₃/P₇` cross

The exact centered correlation has its first three polynomial moments equal
to zero.  The sixth-order kernel model therefore leaves only two tiny positive
moments, while the range-sensitive analytic remainder is controlled by the
exact correlation `L²` mass.
-/

/-- Exact symmetric centered correlation between the classical odd modes
`P₃` and `P₇`. -/
def fourCellOddP3P7Correlation (t : ℝ) : ℝ :=
  -t + 11 * t ^ 2 - (75 / 2 : ℝ) * t ^ 3 +
    (429 / 8 : ℝ) * t ^ 4 - (245 / 8 : ℝ) * t ^ 5 +
      (21 / 4 : ℝ) * t ^ 7 - (99 / 128 : ℝ) * t ^ 9 +
        (13 / 256 : ℝ) * t ^ 11

private theorem integral_polynomial_ten
    (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ l r : ℝ) :
    (∫ x : ℝ in l..r,
      a₀ * x ^ 0 + a₁ * x ^ 1 + a₂ * x ^ 2 + a₃ * x ^ 3 +
        a₄ * x ^ 4 + a₅ * x ^ 5 + a₆ * x ^ 6 + a₇ * x ^ 7 +
        a₈ * x ^ 8 + a₉ * x ^ 9 + a₁₀ * x ^ 10) =
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

set_option maxHeartbeats 800000 in
theorem factorTwoCenteredCorrelationBilinear_P3_P7 (t : ℝ) :
    factorTwoCenteredCorrelationBilinear centeredP3 factorTwoCenteredP7 t =
      fourCellOddP3P7Correlation t := by
  unfold factorTwoCenteredCorrelationBilinear
  rw [factorTwoCenteredCrossCorrelation_swap_of_odd_odd
    (by intro x; unfold centeredP3; ring) odd_factorTwoCenteredP7]
  ring_nf
  unfold factorTwoCenteredCrossCorrelation centeredP3
  simp_rw [factorTwoCenteredP7_eq]
  rw [show (fun x : ℝ ↦ ((5 * (t + x) ^ 3 - 3 * (t + x)) / 2) *
      ((429 * x ^ 7 - 693 * x ^ 5 + 315 * x ^ 3 - 35 * x) / 16)) =
      fun x ↦
        0 * x ^ 0 +
        ((-175 / 32 : ℝ) * t ^ 3 + (105 / 32 : ℝ) * t) * x ^ 1 +
        ((-525 / 32 : ℝ) * t ^ 2 + (105 / 32 : ℝ)) * x ^ 2 +
        ((1575 / 32 : ℝ) * t ^ 3 - (735 / 16 : ℝ) * t) * x ^ 3 +
        ((4725 / 32 : ℝ) * t ^ 2 - 35) * x ^ 4 +
        ((-3465 / 32 : ℝ) * t ^ 3 + (1701 / 8 : ℝ) * t) * x ^ 5 +
        ((-10395 / 32 : ℝ) * t ^ 2 + (1827 / 16 : ℝ)) * x ^ 6 +
        ((2145 / 32 : ℝ) * t ^ 3 - (5841 / 16 : ℝ) * t) * x ^ 7 +
        ((6435 / 32 : ℝ) * t ^ 2 - (297 / 2 : ℝ)) * x ^ 8 +
        ((6435 / 32 : ℝ) * t) * x ^ 9 +
        (2145 / 32 : ℝ) * x ^ 10 by
      funext x
      ring,
    integral_polynomial_ten]
  unfold fourCellOddP3P7Correlation
  ring

private theorem integral_polynomial_twentyTwo
    (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅
      a₁₆ a₁₇ a₁₈ a₁₉ a₂₀ a₂₁ a₂₂ l r : ℝ) :
    (∫ x : ℝ in l..r,
      a₀ * x ^ 0 + a₁ * x ^ 1 + a₂ * x ^ 2 + a₃ * x ^ 3 +
        a₄ * x ^ 4 + a₅ * x ^ 5 + a₆ * x ^ 6 + a₇ * x ^ 7 +
        a₈ * x ^ 8 + a₉ * x ^ 9 + a₁₀ * x ^ 10 +
        a₁₁ * x ^ 11 + a₁₂ * x ^ 12 + a₁₃ * x ^ 13 +
        a₁₄ * x ^ 14 + a₁₅ * x ^ 15 + a₁₆ * x ^ 16 +
        a₁₇ * x ^ 17 + a₁₈ * x ^ 18 + a₁₉ * x ^ 19 +
        a₂₀ * x ^ 20 + a₂₁ * x ^ 21 + a₂₂ * x ^ 22) =
      a₀ * (r - l) + a₁ * (r ^ 2 - l ^ 2) / 2 +
        a₂ * (r ^ 3 - l ^ 3) / 3 + a₃ * (r ^ 4 - l ^ 4) / 4 +
        a₄ * (r ^ 5 - l ^ 5) / 5 + a₅ * (r ^ 6 - l ^ 6) / 6 +
        a₆ * (r ^ 7 - l ^ 7) / 7 + a₇ * (r ^ 8 - l ^ 8) / 8 +
        a₈ * (r ^ 9 - l ^ 9) / 9 + a₉ * (r ^ 10 - l ^ 10) / 10 +
        a₁₀ * (r ^ 11 - l ^ 11) / 11 +
        a₁₁ * (r ^ 12 - l ^ 12) / 12 +
        a₁₂ * (r ^ 13 - l ^ 13) / 13 +
        a₁₃ * (r ^ 14 - l ^ 14) / 14 +
        a₁₄ * (r ^ 15 - l ^ 15) / 15 +
        a₁₅ * (r ^ 16 - l ^ 16) / 16 +
        a₁₆ * (r ^ 17 - l ^ 17) / 17 +
        a₁₇ * (r ^ 18 - l ^ 18) / 18 +
        a₁₈ * (r ^ 19 - l ^ 19) / 19 +
        a₁₉ * (r ^ 20 - l ^ 20) / 20 +
        a₂₀ * (r ^ 21 - l ^ 21) / 21 +
        a₂₁ * (r ^ 22 - l ^ 22) / 22 +
        a₂₂ * (r ^ 23 - l ^ 23) / 23 := by
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) l r)
    (Continuous.intervalIntegrable (by fun_prop) l r)]
  repeat rw [intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  ring

theorem integral_fourCellOddP3P7Correlation_sq :
    (∫ t : ℝ in 0..2, fourCellOddP3P7Correlation t ^ 2) =
      (3792 / 2860165 : ℝ) := by
  rw [show (fun t : ℝ ↦ fourCellOddP3P7Correlation t ^ 2) =
      fun t ↦
        0 * t ^ 0 + 0 * t ^ 1 + t ^ 2 - 22 * t ^ 3 + 196 * t ^ 4 -
          (3729 / 4 : ℝ) * t ^ 5 + (10589 / 4 : ℝ) * t ^ 6 -
          (37565 / 8 : ℝ) * t ^ 7 + (330369 / 64 : ℝ) * t ^ 8 -
          (101409 / 32 : ℝ) * t ^ 9 + (8731 / 16 : ℝ) * t ^ 10 +
          (34947 / 64 : ℝ) * t ^ 11 - (8437 / 32 : ℝ) * t ^ 12 -
          (41899 / 512 : ℝ) * t ^ 13 + (36417 / 512 : ℝ) * t ^ 14 +
          (5577 / 1024 : ℝ) * t ^ 15 - (11501 / 1024 : ℝ) * t ^ 16 +
          0 * t ^ 17 + (18537 / 16384 : ℝ) * t ^ 18 + 0 * t ^ 19 -
          (1287 / 16384 : ℝ) * t ^ 20 + 0 * t ^ 21 +
          (169 / 65536 : ℝ) * t ^ 22 by
      funext t
      unfold fourCellOddP3P7Correlation
      ring,
    integral_polynomial_twentyTwo]
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

theorem integral_abs_fourCellOddP3P7Correlation_lt :
    (∫ t : ℝ in 0..2, |fourCellOddP3P7Correlation t|) <
      (3 / 50 : ℝ) := by
  have hcs := sq_intervalIntegral_mul_le_zero_two
    (fun _ : ℝ ↦ 1) (fun t ↦ |fourCellOddP3P7Correlation t|)
    continuous_const (by unfold fourCellOddP3P7Correlation; fun_prop)
  simp only [one_mul, one_pow, sq_abs] at hcs
  rw [show (∫ _t : ℝ in 0..2, (1 : ℝ)) = 2 by norm_num,
    integral_fourCellOddP3P7Correlation_sq] at hcs
  have hnonneg : 0 ≤ ∫ t : ℝ in 0..2,
      |fourCellOddP3P7Correlation t| :=
    intervalIntegral.integral_nonneg (by norm_num) (fun _ _ ↦ abs_nonneg _)
  have hrat :
      (2 : ℝ) * (3792 / 2860165) < (3 / 50 : ℝ) ^ 2 := by
    norm_num
  nlinarith

/-- Signed analytic remainder after replacing the regular kernel by its
sixth-order polynomial on the `P₃/P₇` correlation. -/
def fourCellOddP3P7RegularEnvelopeError : ℝ :=
  ∫ t : ℝ in 0..2,
    (yoshidaRegularKernel (fourCellOperatorHalfWidth * t) -
      yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t)) *
        fourCellOddP3P7Correlation t

private theorem fourCellOddP3P7RegularEnvelope_pointwise
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

private theorem intervalIntegrable_fourCellOddP3P7RegularEnvelope :
    IntervalIntegrable
      (fun t ↦
        (yoshidaRegularKernel (fourCellOperatorHalfWidth * t) -
          yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t)) *
            fourCellOddP3P7Correlation t)
      volume 0 2 := by
  let f : ℝ → ℝ := fun t ↦
    (yoshidaRegularKernel (fourCellOperatorHalfWidth * t) -
      yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t)) *
        fourCellOddP3P7Correlation t
  let g : ℝ → ℝ := fun t ↦
    (1 / 80000 : ℝ) * |fourCellOddP3P7Correlation t|
  have hcorr : Continuous fourCellOddP3P7Correlation := by
    unfold fourCellOddP3P7Correlation
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
    exact ((measurable_yoshidaRegularKernel.comp
      (measurable_const.mul measurable_id)).sub
        (by unfold yoshidaRegularKernelPolynomial6; fun_prop)).mul
          hcorr.measurable
  have hfg : ∀ᵐ t : ℝ ∂(volume.restrict (Ioc (0 : ℝ) 2)),
      ‖f t‖ ≤ g t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have htIcc : t ∈ Icc (0 : ℝ) 2 := ⟨ht.1.le, ht.2⟩
    have henv := fourCellOddP3P7RegularEnvelope_pointwise htIcc
    dsimp only [f, g]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg henv.1]
    exact mul_le_mul_of_nonneg_right henv.2.le
      (abs_nonneg (fourCellOddP3P7Correlation t))
  constructor
  · exact Integrable.mono' hg hfmeas hfg
  · simp

theorem abs_fourCellOddP3P7RegularEnvelopeError_lt :
    |fourCellOddP3P7RegularEnvelopeError| < (3 / 4000000 : ℝ) := by
  let f : ℝ → ℝ := fun t ↦
    (yoshidaRegularKernel (fourCellOperatorHalfWidth * t) -
      yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t)) *
        fourCellOddP3P7Correlation t
  let g : ℝ → ℝ := fun t ↦
    (1 / 80000 : ℝ) * |fourCellOddP3P7Correlation t|
  have hf : IntervalIntegrable f volume 0 2 := by
    dsimp only [f]
    exact intervalIntegrable_fourCellOddP3P7RegularEnvelope
  have hcorr : Continuous fourCellOddP3P7Correlation := by
    unfold fourCellOddP3P7Correlation
    fun_prop
  have hg : IntervalIntegrable g volume 0 2 := by
    dsimp only [g]
    exact (hcorr.abs.const_mul (1 / 80000 : ℝ)).intervalIntegrable 0 2
  have hmono :
      (∫ t : ℝ in 0..2, |f t|) ≤ ∫ t : ℝ in 0..2, g t := by
    apply intervalIntegral.integral_mono_on (by norm_num) hf.abs hg
    intro t ht
    have henv := fourCellOddP3P7RegularEnvelope_pointwise ht
    dsimp only [f, g]
    rw [abs_mul, abs_of_nonneg henv.1]
    exact mul_le_mul_of_nonneg_right henv.2.le
      (abs_nonneg (fourCellOddP3P7Correlation t))
  have habs :
      |fourCellOddP3P7RegularEnvelopeError| ≤
        (1 / 80000 : ℝ) *
          (∫ t : ℝ in 0..2, |fourCellOddP3P7Correlation t|) := by
    calc
      |fourCellOddP3P7RegularEnvelopeError| =
          |∫ t : ℝ in 0..2, f t| := by
        unfold fourCellOddP3P7RegularEnvelopeError
        rfl
      _ ≤ ∫ t : ℝ in 0..2, |f t| :=
        intervalIntegral.abs_integral_le_integral_abs (by norm_num)
      _ ≤ ∫ t : ℝ in 0..2, g t := hmono
      _ = (1 / 80000 : ℝ) *
          (∫ t : ℝ in 0..2, |fourCellOddP3P7Correlation t|) := by
        dsimp only [g]
        rw [intervalIntegral.integral_const_mul]
  have hmass := integral_abs_fourCellOddP3P7Correlation_lt
  nlinarith

/-- Exact sixth-order polynomial contribution to the four-cell `P₃/P₇`
regular cross.  Orthogonality kills the constant, linear, quadratic, quartic,
and sextic kernel moments. -/
def fourCellOddP3P7RegularPolynomial : ℝ :=
  (5 / 379551744 : ℝ) * Real.log 2 ^ 3 +
    (3875 / 20234662576128 : ℝ) * Real.log 2 ^ 5

set_option maxHeartbeats 800000 in
theorem integral_fourCellRegularPolynomial_mul_P3P7Correlation :
    (∫ t : ℝ in 0..2,
      yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t) *
        fourCellOddP3P7Correlation t) =
      fourCellOddP3P7RegularPolynomial := by
  unfold yoshidaRegularKernelPolynomial6 fourCellOperatorHalfWidth
    fourCellOddP3P7Correlation fourCellOddP3P7RegularPolynomial
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [intervalIntegral.integral_const_mul]
  repeat rw [integral_pow]
  norm_num
  ring

theorem fourCellOddP3P7RegularPolynomial_nonneg_lt :
    0 ≤ fourCellOddP3P7RegularPolynomial ∧
      fourCellOddP3P7RegularPolynomial < (1 / 100000000 : ℝ) := by
  have hlogPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogUpper : Real.log 2 < (7 / 10 : ℝ) := by
    have h := strict_log_two_bounds.2
    linarith
  have h3 : Real.log 2 ^ 3 < (7 / 10 : ℝ) ^ 3 :=
    pow_lt_pow_left₀ hlogUpper hlogPos.le (by norm_num)
  have h5 : Real.log 2 ^ 5 < (7 / 10 : ℝ) ^ 5 :=
    pow_lt_pow_left₀ hlogUpper hlogPos.le (by norm_num)
  unfold fourCellOddP3P7RegularPolynomial
  constructor
  · positivity
  · nlinarith

theorem integral_fourCellRegularKernel_mul_P3P7Correlation_eq :
    (∫ t : ℝ in 0..2,
      yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
        fourCellOddP3P7Correlation t) =
      fourCellOddP3P7RegularPolynomial +
        fourCellOddP3P7RegularEnvelopeError := by
  have hpoly : IntervalIntegrable
      (fun t : ℝ ↦
        yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t) *
          fourCellOddP3P7Correlation t) volume 0 2 := by
    exact (by
      unfold yoshidaRegularKernelPolynomial6 fourCellOperatorHalfWidth
        fourCellOddP3P7Correlation
      fun_prop : Continuous (fun t : ℝ ↦
        yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t) *
          fourCellOddP3P7Correlation t)).intervalIntegrable 0 2
  rw [show (fun t : ℝ ↦
      yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
        fourCellOddP3P7Correlation t) = fun t ↦
      yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t) *
          fourCellOddP3P7Correlation t +
        (yoshidaRegularKernel (fourCellOperatorHalfWidth * t) -
          yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t)) *
            fourCellOddP3P7Correlation t by
      funext t
      ring,
    intervalIntegral.integral_add hpoly
      intervalIntegrable_fourCellOddP3P7RegularEnvelope,
    integral_fourCellRegularPolynomial_mul_P3P7Correlation]
  rfl

/-- The regular-kernel `P₃/P₇` cross is structurally negligible at the
four-cell scale.  The proof uses an exact polynomial correlation, exact moment
cancellation, and a range-sensitive analytic envelope; it contains no sampled
or floating-point certificate. -/
theorem abs_integral_fourCellRegularKernel_mul_correlation_P3_P7_lt :
    |∫ t : ℝ in 0..2,
      yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
        factorTwoCenteredCorrelationBilinear
          centeredP3 factorTwoCenteredP7 t| < (1 / 100000 : ℝ) := by
  rw [show (fun t : ℝ ↦
      yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
        factorTwoCenteredCorrelationBilinear
          centeredP3 factorTwoCenteredP7 t) = fun t ↦
      yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
        fourCellOddP3P7Correlation t by
      funext t
      rw [factorTwoCenteredCorrelationBilinear_P3_P7],
    integral_fourCellRegularKernel_mul_P3P7Correlation_eq]
  have hp := fourCellOddP3P7RegularPolynomial_nonneg_lt
  have he := abs_fourCellOddP3P7RegularEnvelopeError_lt
  have htri := abs_add fourCellOddP3P7RegularPolynomial
    fourCellOddP3P7RegularEnvelopeError
  rw [abs_of_nonneg hp.1] at htri
  nlinarith

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP3P7RegularCrossStructural

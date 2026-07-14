import ArithmeticHodge.Analysis.YoshidaEndpointEvenFullPolarization
import ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedRemainderEnvelopeKernel
import ArithmeticHodge.Analysis.YoshidaEndpointRegularCorrelation
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddLowEndpointStructuralPositive

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddCleanSharp

noncomputable section

open CenteredEndpointCorrelation
open CenteredOddOneThreeEnergy
open ShiftedLegendreCenteredLowModeL2
open ShiftedLegendreCenteredLowModeThreeL2
open YoshidaConstantBounds
open YoshidaEndpointEvenFullPolarization
open YoshidaEndpointEvenConstantCross
open YoshidaEndpointEvenProjectedRemainderEnvelopeKernel
open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointOddFullPolarization
open YoshidaEndpointOddLowGramExpansion
open YoshidaEndpointOddOneThreeRawPolarization
open YoshidaEndpointOddResidualRegularity
open YoshidaEndpointOcticPotential
open YoshidaEndpointOcticTwoModeSchurData
open YoshidaEndpointPotentialBound
open YoshidaEndpointRegularCorrelation
open YoshidaFactorTwoPhaseIntrinsicOddLowEndpointStructuralPositive
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoPhaseIntrinsicRemainderBound
open YoshidaFactorTwoPhaseOddLowEndpointPositive
open YoshidaFactorTwoPhaseLowSchur
open YoshidaRegularKernelBound
open YoshidaRegularKernelSchur

/-!
# Sharp structural data for the intrinsic odd clean block

The regular kernel is replaced once, globally on `[0, log 2]`, by its
sixth-order envelope.  Everything left after that replacement is an exact
polynomial moment or an exact Hilbert-space estimate for the odd hyperbolic
moments.
-/

/-- Elementary monomial integration on the correlation interval. -/
private theorem integral_polynomial_zero_two
    (N : ℕ) (a : ℕ → ℝ) :
    (∫ x : ℝ in 0..2, ∑ n ∈ Finset.range N, a n * x ^ n) =
      ∑ n ∈ Finset.range N, a n * (2 : ℝ) ^ (n + 1) / (n + 1) := by
  rw [intervalIntegral.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro n _hn
    rw [intervalIntegral.integral_const_mul, integral_pow]
    norm_num
    ring
  · intro n _hn
    exact ((continuous_id.pow n).const_mul (a n)).intervalIntegrable 0 2

/-- Polynomial regular-kernel entry on the first odd mode. -/
def oddCleanRegularPolynomialGram11 : ℝ :=
  yoshidaEndpointA / 90 + yoshidaEndpointA ^ 2 / 36 -
    yoshidaEndpointA ^ 3 / 1200 - yoshidaEndpointA ^ 4 / 144 +
    31 * yoshidaEndpointA ^ 5 / 571536 +
    61 * yoshidaEndpointA ^ 6 / 33600

/-- Polynomial regular-kernel cross entry. -/
def oddCleanRegularPolynomialGram13 : ℝ :=
  -yoshidaEndpointA / 1260 - yoshidaEndpointA ^ 3 / 16200 -
    yoshidaEndpointA ^ 4 / 1008 + 31 * yoshidaEndpointA ^ 5 / 2794176 +
    61 * yoshidaEndpointA ^ 6 / 129600

/-- Polynomial regular-kernel entry on the third odd mode. -/
def oddCleanRegularPolynomialGram33 : ℝ :=
  yoshidaEndpointA / 1890 + yoshidaEndpointA ^ 3 / 118800 +
    31 * yoshidaEndpointA ^ 5 / 27243216 +
    61 * yoshidaEndpointA ^ 6 / 705600

private def regular11Coeff : ℕ → ℝ
  | 0 => 1 / 6
  | 1 => -1 / 4 - yoshidaEndpointA / 72
  | 2 => yoshidaEndpointA / 48 - yoshidaEndpointA ^ 2 / 48
  | 3 => 1 / 24 + yoshidaEndpointA ^ 2 / 32 +
      7 * yoshidaEndpointA ^ 3 / 17280
  | 4 => -7 * yoshidaEndpointA ^ 3 / 11520 +
      5 * yoshidaEndpointA ^ 4 / 2304 - yoshidaEndpointA / 288
  | 5 => -yoshidaEndpointA ^ 2 / 192 -
      5 * yoshidaEndpointA ^ 4 / 1536 -
      31 * yoshidaEndpointA ^ 5 / 2903040
  | 6 => 7 * yoshidaEndpointA ^ 3 / 69120 +
      31 * yoshidaEndpointA ^ 5 / 1935360 -
      61 * yoshidaEndpointA ^ 6 / 276480
  | 7 => 5 * yoshidaEndpointA ^ 4 / 9216 +
      61 * yoshidaEndpointA ^ 6 / 184320
  | 8 => -31 * yoshidaEndpointA ^ 5 / 11612160
  | 9 => -61 * yoshidaEndpointA ^ 6 / 1105920
  | _ => 0

private theorem integral_regularPolynomial_correlation11 :
    2 * (∫ t : ℝ in 0..2,
      yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t) *
        oddStructuralCorrelation11 t) = oddCleanRegularPolynomialGram11 := by
  rw [show (fun t : ℝ ↦
      yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t) *
        oddStructuralCorrelation11 t) =
      fun t ↦ ∑ n ∈ Finset.range 10, regular11Coeff n * t ^ n by
    funext t
    simp [yoshidaRegularKernelPolynomial6, oddStructuralCorrelation11,
      regular11Coeff, Finset.sum_range_succ]
    ring,
    integral_polynomial_zero_two]
  norm_num [regular11Coeff, oddCleanRegularPolynomialGram11,
    Finset.sum_range_succ]
  ring

private def regular13Coeff : ℕ → ℝ
  | 0 => 0
  | 1 => -1 / 4
  | 2 => 5 / 8 + yoshidaEndpointA / 48
  | 3 => -3 / 8 - 5 * yoshidaEndpointA / 96 +
      yoshidaEndpointA ^ 2 / 32
  | 4 => yoshidaEndpointA / 32 - 5 * yoshidaEndpointA ^ 2 / 64 -
      7 * yoshidaEndpointA ^ 3 / 11520
  | 5 => 1 / 32 + 3 * yoshidaEndpointA ^ 2 / 64 +
      7 * yoshidaEndpointA ^ 3 / 4608 -
      5 * yoshidaEndpointA ^ 4 / 1536
  | 6 => -yoshidaEndpointA / 384 -
      7 * yoshidaEndpointA ^ 3 / 7680 +
      25 * yoshidaEndpointA ^ 4 / 3072 +
      31 * yoshidaEndpointA ^ 5 / 1935360
  | 7 => -yoshidaEndpointA ^ 2 / 256 -
      5 * yoshidaEndpointA ^ 4 / 1024 -
      31 * yoshidaEndpointA ^ 5 / 774144 +
      61 * yoshidaEndpointA ^ 6 / 184320
  | 8 => 7 * yoshidaEndpointA ^ 3 / 92160 +
      31 * yoshidaEndpointA ^ 5 / 1290240 -
      61 * yoshidaEndpointA ^ 6 / 73728
  | 9 => 5 * yoshidaEndpointA ^ 4 / 12288 +
      61 * yoshidaEndpointA ^ 6 / 122880
  | 10 => -31 * yoshidaEndpointA ^ 5 / 15482880
  | 11 => -61 * yoshidaEndpointA ^ 6 / 1474560
  | _ => 0

private theorem integral_regularPolynomial_correlation13 :
    2 * (∫ t : ℝ in 0..2,
      yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t) *
        oddStructuralCorrelation13 t) = oddCleanRegularPolynomialGram13 := by
  rw [show (fun t : ℝ ↦
      yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t) *
        oddStructuralCorrelation13 t) =
      fun t ↦ ∑ n ∈ Finset.range 12, regular13Coeff n * t ^ n by
    funext t
    simp [yoshidaRegularKernelPolynomial6, oddStructuralCorrelation13,
      regular13Coeff, Finset.sum_range_succ]
    ring,
    integral_polynomial_zero_two]
  norm_num [regular13Coeff, oddCleanRegularPolynomialGram13,
    Finset.sum_range_succ]
  ring

private def regular33Coeff : ℕ → ℝ
  | 0 => 1 / 14
  | 1 => -1 / 4 - yoshidaEndpointA / 168
  | 2 => yoshidaEndpointA / 48 - yoshidaEndpointA ^ 2 / 112
  | 3 => 1 / 4 + yoshidaEndpointA ^ 2 / 32 +
      yoshidaEndpointA ^ 3 / 5760
  | 4 => -yoshidaEndpointA / 48 -
      7 * yoshidaEndpointA ^ 3 / 11520 +
      5 * yoshidaEndpointA ^ 4 / 5376
  | 5 => -3 / 32 - yoshidaEndpointA ^ 2 / 32 -
      5 * yoshidaEndpointA ^ 4 / 1536 -
      31 * yoshidaEndpointA ^ 5 / 6773760
  | 6 => yoshidaEndpointA / 128 +
      7 * yoshidaEndpointA ^ 3 / 11520 +
      31 * yoshidaEndpointA ^ 5 / 1935360 -
      61 * yoshidaEndpointA ^ 6 / 645120
  | 7 => 5 / 448 + 3 * yoshidaEndpointA ^ 2 / 256 +
      5 * yoshidaEndpointA ^ 4 / 1536 +
      61 * yoshidaEndpointA ^ 6 / 184320
  | 8 => -5 * yoshidaEndpointA / 5376 -
      7 * yoshidaEndpointA ^ 3 / 30720 -
      31 * yoshidaEndpointA ^ 5 / 1935360
  | 9 => -5 * yoshidaEndpointA ^ 2 / 3584 -
      5 * yoshidaEndpointA ^ 4 / 4096 -
      61 * yoshidaEndpointA ^ 6 / 184320
  | 10 => yoshidaEndpointA ^ 3 / 36864 +
      31 * yoshidaEndpointA ^ 5 / 5160960
  | 11 => 25 * yoshidaEndpointA ^ 4 / 172032 +
      61 * yoshidaEndpointA ^ 6 / 491520
  | 12 => -31 * yoshidaEndpointA ^ 5 / 43352064
  | 13 => -61 * yoshidaEndpointA ^ 6 / 4128768
  | _ => 0

private theorem integral_regularPolynomial_correlation33 :
    2 * (∫ t : ℝ in 0..2,
      yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t) *
        oddStructuralCorrelation33 t) = oddCleanRegularPolynomialGram33 := by
  rw [show (fun t : ℝ ↦
      yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t) *
        oddStructuralCorrelation33 t) =
      fun t ↦ ∑ n ∈ Finset.range 14, regular33Coeff n * t ^ n by
    funext t
    simp [yoshidaRegularKernelPolynomial6, oddStructuralCorrelation33,
      regular33Coeff, Finset.sum_range_succ]
    ring,
    integral_polynomial_zero_two]
  norm_num [regular33Coeff, oddCleanRegularPolynomialGram33,
    Finset.sum_range_succ]
  ring

/-! ## The single global regular-kernel envelope -/

/-- Signed error left by the one global sixth-order kernel replacement. -/
def oddCleanRegularEnvelopeError (C : ℝ → ℝ) : ℝ :=
  2 * ∫ t : ℝ in 0..2,
    (yoshidaRegularKernel (yoshidaEndpointA * t) -
      yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t)) * C t

private theorem measurable_yoshidaRegularKernel :
    Measurable yoshidaRegularKernel := by
  unfold yoshidaRegularKernel
  apply Measurable.ite
  · simpa only [Set.setOf_eq_eq_singleton] using
      measurableSet_singleton (0 : ℝ)
  · exact measurable_const
  · exact ((Real.measurable_exp.comp (measurable_id.div_const 2)).div
      (measurable_const.mul Real.measurable_sinh)).sub
        (measurable_const.div (measurable_const.mul measurable_id))

private theorem regularEnvelope_pointwise
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 2) :
    0 ≤ yoshidaRegularKernel (yoshidaEndpointA * t) -
        yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t) ∧
      yoshidaRegularKernel (yoshidaEndpointA * t) -
        yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t) <
          (1 / 500000 : ℝ) := by
  apply yoshidaRegularKernelPolynomial6_envelope
  · exact mul_nonneg yoshidaEndpointA_pos.le ht.1
  · rw [show Real.log 2 = 2 * yoshidaEndpointA by
      unfold yoshidaEndpointA
      ring]
    simpa [mul_comm] using
      (mul_le_mul_of_nonneg_left ht.2 yoshidaEndpointA_pos.le)

private theorem intervalIntegrable_regularEnvelope_mul
    (C : ℝ → ℝ) (hC : Continuous C) :
    IntervalIntegrable
      (fun t ↦
        (yoshidaRegularKernel (yoshidaEndpointA * t) -
          yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t)) * C t)
      volume 0 2 := by
  let f : ℝ → ℝ := fun t ↦
    (yoshidaRegularKernel (yoshidaEndpointA * t) -
      yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t)) * C t
  let g : ℝ → ℝ := fun t ↦ (1 / 500000 : ℝ) * |C t|
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
        (by unfold yoshidaRegularKernelPolynomial6; fun_prop)).mul hC.measurable
  have hfg : ∀ᵐ t : ℝ ∂(volume.restrict (Ioc (0 : ℝ) 2)),
      ‖f t‖ ≤ g t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have htIcc : t ∈ Icc (0 : ℝ) 2 := ⟨ht.1.le, ht.2⟩
    have henv := regularEnvelope_pointwise htIcc
    dsimp only [f, g]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg henv.1]
    exact mul_le_mul_of_nonneg_right henv.2.le (abs_nonneg (C t))
  constructor
  · exact Integrable.mono' hg hfmeas hfg
  · simp

/-- The sixth-order replacement loses at most its uniform envelope times
the exact correlation `L¹` mass. -/
theorem abs_oddCleanRegularEnvelopeError_le
    (C : ℝ → ℝ) (hC : Continuous C) :
    |oddCleanRegularEnvelopeError C| ≤
      (1 / 250000 : ℝ) * (∫ t : ℝ in 0..2, |C t|) := by
  let f : ℝ → ℝ := fun t ↦
    (yoshidaRegularKernel (yoshidaEndpointA * t) -
      yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t)) * C t
  let g : ℝ → ℝ := fun t ↦ (1 / 500000 : ℝ) * |C t|
  have hf : IntervalIntegrable f volume 0 2 := by
    dsimp only [f]
    exact intervalIntegrable_regularEnvelope_mul C hC
  have hg : IntervalIntegrable g volume 0 2 := by
    dsimp only [g]
    exact (hC.abs.const_mul (1 / 500000 : ℝ)).intervalIntegrable 0 2
  have hmono : (∫ t : ℝ in 0..2, |f t|) ≤ ∫ t : ℝ in 0..2, g t := by
    apply intervalIntegral.integral_mono_on (by norm_num) hf.abs hg
    intro t ht
    have henv := regularEnvelope_pointwise ht
    dsimp only [f, g]
    rw [abs_mul, abs_of_nonneg henv.1]
    exact mul_le_mul_of_nonneg_right henv.2.le (abs_nonneg (C t))
  calc
    |oddCleanRegularEnvelopeError C| = 2 * |∫ t : ℝ in 0..2, f t| := by
      unfold oddCleanRegularEnvelopeError
      dsimp only [f]
      rw [abs_mul]
      norm_num
    _ ≤ 2 * (∫ t : ℝ in 0..2, |f t|) := by
      gcongr
      exact intervalIntegral.abs_integral_le_integral_abs (by norm_num)
    _ ≤ 2 * (∫ t : ℝ in 0..2, g t) := by gcongr
    _ = (1 / 250000 : ℝ) * (∫ t : ℝ in 0..2, |C t|) := by
      dsimp only [g]
      rw [intervalIntegral.integral_const_mul]
      ring

private theorem regularIntegral_eq_polynomial_add_error
    (C : ℝ → ℝ) (hC : Continuous C) :
    2 * (∫ t : ℝ in 0..2,
      yoshidaRegularKernel (yoshidaEndpointA * t) * C t) =
      2 * (∫ t : ℝ in 0..2,
        yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t) * C t) +
        oddCleanRegularEnvelopeError C := by
  have herr := intervalIntegrable_regularEnvelope_mul C hC
  have hpoly : IntervalIntegrable
      (fun t : ℝ ↦ yoshidaRegularKernelPolynomial6
        (yoshidaEndpointA * t) * C t) volume 0 2 := by
    exact (by
      unfold yoshidaRegularKernelPolynomial6
      fun_prop : Continuous (fun t : ℝ ↦
        yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t) * C t))
      |>.intervalIntegrable 0 2
  rw [show (fun t : ℝ ↦
      yoshidaRegularKernel (yoshidaEndpointA * t) * C t) =
      fun t ↦
        (yoshidaRegularKernel (yoshidaEndpointA * t) -
          yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t)) * C t +
        yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t) * C t by
    funext t
    ring,
    intervalIntegral.integral_add herr hpoly]
  unfold oddCleanRegularEnvelopeError
  ring

/-- Sharp diagonal error budget for `P₁`. -/
theorem abs_oddCleanRegularEnvelopeError11_le :
    |oddCleanRegularEnvelopeError oddStructuralCorrelation11| ≤
      (1 / 375000 : ℝ) := by
  have h := abs_oddCleanRegularEnvelopeError_le oddStructuralCorrelation11
    (by unfold oddStructuralCorrelation11; fun_prop)
  have hL1 := integral_abs_oddStructuralCorrelation11_le
  nlinarith

/-- Sharp off-diagonal error budget. -/
theorem abs_oddCleanRegularEnvelopeError13_lt :
    |oddCleanRegularEnvelopeError oddStructuralCorrelation13| <
      (1 / 1500000 : ℝ) := by
  have h := abs_oddCleanRegularEnvelopeError_le oddStructuralCorrelation13
    (by unfold oddStructuralCorrelation13; fun_prop)
  have hL1 := integral_abs_oddStructuralCorrelation13_lt
  nlinarith

/-- Sharp diagonal error budget for `P₃`. -/
theorem abs_oddCleanRegularEnvelopeError33_le :
    |oddCleanRegularEnvelopeError oddStructuralCorrelation33| ≤
      (1 / 875000 : ℝ) := by
  have h := abs_oddCleanRegularEnvelopeError_le oddStructuralCorrelation33
    (by unfold oddStructuralCorrelation33; fun_prop)
  have hL1 := integral_abs_oddStructuralCorrelation33_le
  nlinarith

/-! ## Exact odd hyperbolic moment algebra -/

/-- First odd hyperbolic moment. -/
def oddCleanSinhMoment1 : ℝ := yoshidaEndpointSinhMoment centeredP1

/-- Third odd hyperbolic moment. -/
def oddCleanSinhMoment3 : ℝ := yoshidaEndpointSinhMoment centeredP3

/-- Exact squared mass of the odd hyperbolic weight. -/
def oddCleanSinhEnergy : ℝ :=
  ∫ x : ℝ in -1..1, Real.sinh (yoshidaEndpointA * x / 2) ^ 2

private theorem endpointA_fine_bounds :
    (69314718055 / 200000000000 : ℝ) < yoshidaEndpointA ∧
      yoshidaEndpointA < (69314718057 / 200000000000 : ℝ) := by
  unfold yoshidaEndpointA
  constructor <;> linarith [strict_log_two_fine_bounds.1,
    strict_log_two_fine_bounds.2]

private theorem inv_sqrt_two_fine_bounds :
    (707106781185 / 1000000000000 : ℝ) < 1 / Real.sqrt 2 ∧
      1 / Real.sqrt 2 < (70710678119 / 100000000000 : ℝ) := by
  have hsqrt0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsqrtPos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrtSq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hlo : (141421356237 / 100000000000 : ℝ) < Real.sqrt 2 := by
    have hrat : (141421356237 / 100000000000 : ℝ) ^ 2 < 2 := by
      norm_num
    nlinarith
  have hup : Real.sqrt 2 < (141421356238 / 100000000000 : ℝ) := by
    have hrat : (2 : ℝ) < (141421356238 / 100000000000 : ℝ) ^ 2 := by
      norm_num
    nlinarith
  have hinv : 1 / Real.sqrt 2 = Real.sqrt 2 / 2 := by
    field_simp [hsqrtPos.ne']
    nlinarith
  rw [hinv]
  constructor <;> linarith

/-- Closed form for the total odd hyperbolic mass. -/
theorem oddCleanSinhEnergy_eq :
    oddCleanSinhEnergy =
      (1 / Real.sqrt 2 - Real.log 2) / Real.log 2 := by
  have hAne : yoshidaEndpointA ≠ 0 := yoshidaEndpointA_pos.ne'
  have hlogne : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hexact := two_mul_sinh_yoshidaEndpointA_sub_eq
  unfold oddCleanSinhEnergy
  rw [integral_sinh_scaled_sq hAne]
  apply (div_eq_div_iff hAne hlogne).2
  have hAeq : 2 * yoshidaEndpointA = Real.log 2 := by
    unfold yoshidaEndpointA
    ring
  calc
    (Real.sinh yoshidaEndpointA - yoshidaEndpointA) * Real.log 2 =
        (Real.sinh yoshidaEndpointA - yoshidaEndpointA) *
          (2 * yoshidaEndpointA) := by rw [hAeq]
    _ = (2 * (Real.sinh yoshidaEndpointA - yoshidaEndpointA)) *
        yoshidaEndpointA := by ring
    _ = (1 / Real.sqrt 2 - Real.log 2) * yoshidaEndpointA := by
      rw [hexact]

/-- Fine rational upper bound for the exact total odd hyperbolic mass. -/
theorem oddCleanSinhEnergy_lt :
    oddCleanSinhEnergy < (20139447 / 1000000000 : ℝ) := by
  rw [oddCleanSinhEnergy_eq, div_lt_iff₀ (Real.log_pos (by norm_num))]
  have hsqrt := inv_sqrt_two_fine_bounds.2
  have hlog := strict_log_two_fine_bounds.1
  linarith

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

private theorem add_cube_div_six_le_sinh_of_nonneg
    {u : ℝ} (hu : 0 ≤ u) :
    u + u ^ 3 / 6 ≤ Real.sinh u := by
  let q : ℝ → ℝ := fun z ↦ Real.sinh z - z - z ^ 3 / 6
  have hderiv (z : ℝ) :
      HasDerivAt q (Real.cosh z - 1 - z ^ 2 / 2) z := by
    dsimp only [q]
    convert ((Real.hasDerivAt_sinh z).sub (hasDerivAt_id z)).sub
      (((hasDerivAt_id z).pow 3).div_const 6) using 1
    simp only [id_eq, Nat.cast_ofNat]
    ring
  have hcont : Continuous q := by
    dsimp only [q]
    fun_prop
  have hmono : MonotoneOn q (Icc 0 u) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 u) hcont.continuousOn
    · intro z _hz
      exact (hderiv z).differentiableAt.differentiableWithinAt
    · intro z _hz
      rw [(hderiv z).deriv]
      linarith [one_add_sq_div_two_le_cosh z]
  have hq := hmono (show (0 : ℝ) ∈ Icc 0 u by exact ⟨le_rfl, hu⟩)
    (show u ∈ Icc 0 u by exact ⟨hu, le_rfl⟩) hu
  dsimp only [q] at hq
  norm_num at hq
  linarith

private theorem mul_sinh_sub_cubic_nonneg
    {a : ℝ} (ha : 0 ≤ a) (x : ℝ) :
    0 ≤ (Real.sinh (a * x) - (a * x + (a * x) ^ 3 / 6)) * x := by
  by_cases hx : 0 ≤ x
  · have h := add_cube_div_six_le_sinh_of_nonneg (mul_nonneg ha hx)
    exact mul_nonneg (sub_nonneg.mpr h) hx
  · have hax : 0 ≤ -(a * x) := by
      have hx' : x ≤ 0 := le_of_not_ge hx
      nlinarith
    have h := add_cube_div_six_le_sinh_of_nonneg hax
    have hneg : Real.sinh (a * x) - (a * x + (a * x) ^ 3 / 6) ≤ 0 := by
      rw [show a * x = -(-(a * x)) by ring, Real.sinh_neg]
      nlinarith
    exact mul_nonneg_of_nonpos_of_nonpos hneg (le_of_not_ge hx)

/-- The first odd hyperbolic moment dominates its exact cubic moment. -/
theorem oddCleanSinhMoment1_cubic_lower :
    yoshidaEndpointA / 3 + yoshidaEndpointA ^ 3 / 120 ≤
      oddCleanSinhMoment1 := by
  have hpoly : IntervalIntegrable
      (fun x : ℝ ↦
        (yoshidaEndpointA * x / 2 +
          (yoshidaEndpointA * x / 2) ^ 3 / 6) * x)
      volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hsinh : IntervalIntegrable
      (fun x : ℝ ↦ Real.sinh (yoshidaEndpointA * x / 2) * x)
      volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hmono :
      (∫ x : ℝ in -1..1,
        (yoshidaEndpointA * x / 2 +
          (yoshidaEndpointA * x / 2) ^ 3 / 6) * x) ≤
        ∫ x : ℝ in -1..1,
          Real.sinh (yoshidaEndpointA * x / 2) * x := by
    apply intervalIntegral.integral_mono_on (by norm_num) hpoly hsinh
    intro x _hx
    have h := mul_sinh_sub_cubic_nonneg
      (a := yoshidaEndpointA / 2) (half_pos yoshidaEndpointA_pos).le x
    rw [show (yoshidaEndpointA / 2) * x =
      yoshidaEndpointA * x / 2 by ring] at h
    nlinarith
  have hpolyExact :
      (∫ x : ℝ in -1..1,
        (yoshidaEndpointA * x / 2 +
          (yoshidaEndpointA * x / 2) ^ 3 / 6) * x) =
        yoshidaEndpointA / 3 + yoshidaEndpointA ^ 3 / 120 := by
    rw [show (fun x : ℝ ↦
        (yoshidaEndpointA * x / 2 +
          (yoshidaEndpointA * x / 2) ^ 3 / 6) * x) =
      fun x ↦ (yoshidaEndpointA / 2) * x ^ 2 +
        (yoshidaEndpointA ^ 3 / 48) * x ^ 4 by
      funext x
      ring,
      intervalIntegral.integral_add
        (Continuous.intervalIntegrable (by fun_prop) (-1) 1)
        (Continuous.intervalIntegrable (by fun_prop) (-1) 1),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, integral_pow, integral_pow]
    norm_num
    ring
  rw [hpolyExact] at hmono
  simpa only [oddCleanSinhMoment1, yoshidaEndpointSinhMoment, centeredP1]
    using hmono

/-- Rational form of the cubic first-moment lower bound. -/
theorem oddCleanSinhMoment1_gt :
    (11587142 / 100000000 : ℝ) < oddCleanSinhMoment1 := by
  have hmoment := oddCleanSinhMoment1_cubic_lower
  have hA := endpointA_fine_bounds.1
  have hA3 := pow_lt_pow_left₀ hA (by norm_num) (by norm_num : (3 : ℕ) ≠ 0)
  have hrat :
      (11587142 / 100000000 : ℝ) <
        (69314718055 / 200000000000 : ℝ) / 3 +
          (69314718055 / 200000000000 : ℝ) ^ 3 / 120 := by
    norm_num
  nlinarith

/-- Orthogonal `P₁/P₃` projection of the exact sinh-square mass. -/
theorem oddCleanSinhMoments_bessel :
    (3 / 2 : ℝ) * oddCleanSinhMoment1 ^ 2 +
        (7 / 2 : ℝ) * oddCleanSinhMoment3 ^ 2 ≤
      oddCleanSinhEnergy := by
  let h : ℝ → ℝ := fun x ↦ Real.sinh (yoshidaEndpointA * x / 2)
  have hres := integral_centeredOddOneThreeResidual_sq h
    (by dsimp only [h]; fun_prop)
  have hnonneg : 0 ≤ ∫ x : ℝ in -1..1,
      centeredOddOneThreeResidual h x ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun _x _hx ↦ sq_nonneg _)
  rw [hres] at hnonneg
  have hcoeff1 : centeredOddP1Coefficient h =
      (3 / 2 : ℝ) * oddCleanSinhMoment1 := by
    unfold centeredOddP1Coefficient oddCleanSinhMoment1
      yoshidaEndpointSinhMoment
    dsimp only [h]
  have hcoeff3 : centeredOddP3Coefficient h =
      (7 / 2 : ℝ) * oddCleanSinhMoment3 := by
    unfold centeredOddP3Coefficient oddCleanSinhMoment3
      yoshidaEndpointSinhMoment
    dsimp only [h]
  rw [hcoeff1, hcoeff3] at hnonneg
  change 0 ≤ oddCleanSinhEnergy -
    (2 / 3 : ℝ) * ((3 / 2 : ℝ) * oddCleanSinhMoment1) ^ 2 -
    (2 / 7 : ℝ) * ((7 / 2 : ℝ) * oddCleanSinhMoment3) ^ 2 at hnonneg
  nlinarith

/-- The first squared moment uses only its share of the exact sinh mass. -/
theorem oddCleanSinhMoment1_sq_lt :
    oddCleanSinhMoment1 ^ 2 < (134263 / 10000000 : ℝ) := by
  have hbessel := oddCleanSinhMoments_bessel
  have henergy := oddCleanSinhEnergy_lt
  have hsquare : 0 ≤ oddCleanSinhMoment3 ^ 2 := sq_nonneg _
  nlinarith

/-- Cubic saturation of `P₁` leaves only a tiny possible `P₃` moment. -/
theorem oddCleanSinhMoment3_sq_lt :
    oddCleanSinhMoment3 ^ 2 < (481 / 10000000000 : ℝ) := by
  have hbessel := oddCleanSinhMoments_bessel
  have henergy := oddCleanSinhEnergy_lt
  have hfirst := oddCleanSinhMoment1_gt
  have hfirstSq :
      (11587142 / 100000000 : ℝ) ^ 2 < oddCleanSinhMoment1 ^ 2 := by
    nlinarith [sq_nonneg
      (oddCleanSinhMoment1 - (11587142 / 100000000 : ℝ))]
  nlinarith

/-- The hyperbolic cross moment is structurally tiny. -/
theorem abs_oddCleanSinhMoment1_mul_moment3_lt :
    |oddCleanSinhMoment1 * oddCleanSinhMoment3| < (1 / 39000 : ℝ) := by
  have h1 := oddCleanSinhMoment1_sq_lt
  have h3 := oddCleanSinhMoment3_sq_lt
  have hprod1 :
      oddCleanSinhMoment1 ^ 2 * oddCleanSinhMoment3 ^ 2 ≤
        (134263 / 10000000 : ℝ) * oddCleanSinhMoment3 ^ 2 :=
    mul_le_mul_of_nonneg_right h1.le (sq_nonneg _)
  have hprod2 :
      (134263 / 10000000 : ℝ) * oddCleanSinhMoment3 ^ 2 <
        (134263 / 10000000 : ℝ) * (481 / 10000000000 : ℝ) :=
    mul_lt_mul_of_pos_left h3 (by norm_num)
  have hrat :
      (134263 / 10000000 : ℝ) * (481 / 10000000000 : ℝ) <
        (1 / 39000 : ℝ) ^ 2 := by
    norm_num
  have hsquare :
      |oddCleanSinhMoment1 * oddCleanSinhMoment3| ^ 2 <
        (1 / 39000 : ℝ) ^ 2 := by
    rw [sq_abs, mul_pow]
    exact hprod1.trans_lt (hprod2.trans hrat)
  nlinarith [abs_nonneg (oddCleanSinhMoment1 * oddCleanSinhMoment3)]

/-- Rational loss budget for the first hyperbolic diagonal. -/
theorem oddCleanHyperbolicLoss11_lt :
    2 * yoshidaEndpointA * oddCleanSinhMoment1 ^ 2 <
      (931 / 100000 : ℝ) := by
  have hsq := oddCleanSinhMoment1_sq_lt
  have hA := endpointA_fine_bounds.2
  have hmul1 :
      yoshidaEndpointA * oddCleanSinhMoment1 ^ 2 <
        yoshidaEndpointA * (134263 / 10000000 : ℝ) :=
    mul_lt_mul_of_pos_left hsq yoshidaEndpointA_pos
  have hmul2 :
      yoshidaEndpointA * (134263 / 10000000 : ℝ) <
        (69314718057 / 200000000000 : ℝ) *
          (134263 / 10000000 : ℝ) :=
    mul_lt_mul_of_pos_right hA (by norm_num)
  nlinarith

/-- Rational loss budget for the third hyperbolic diagonal. -/
theorem oddCleanHyperbolicLoss33_lt :
    2 * yoshidaEndpointA * oddCleanSinhMoment3 ^ 2 <
      (1 / 20000000 : ℝ) := by
  have hsq := oddCleanSinhMoment3_sq_lt
  have hA := endpointA_fine_bounds.2
  have hmul1 :
      yoshidaEndpointA * oddCleanSinhMoment3 ^ 2 <
        yoshidaEndpointA * (481 / 10000000000 : ℝ) :=
    mul_lt_mul_of_pos_left hsq yoshidaEndpointA_pos
  have hmul2 :
      yoshidaEndpointA * (481 / 10000000000 : ℝ) <
        (69314718057 / 200000000000 : ℝ) *
          (481 / 10000000000 : ℝ) :=
    mul_lt_mul_of_pos_right hA (by norm_num)
  nlinarith

/-- Rational absolute budget for the hyperbolic cross entry. -/
theorem abs_oddCleanHyperbolicCross_lt :
    |2 * yoshidaEndpointA * oddCleanSinhMoment1 * oddCleanSinhMoment3| <
      (9 / 500000 : ℝ) := by
  have hcross := abs_oddCleanSinhMoment1_mul_moment3_lt
  have hA := endpointA_fine_bounds.2
  have hA0 : 0 ≤ 2 * yoshidaEndpointA :=
    mul_nonneg (by norm_num) yoshidaEndpointA_pos.le
  rw [show 2 * yoshidaEndpointA * oddCleanSinhMoment1 *
      oddCleanSinhMoment3 =
    (2 * yoshidaEndpointA) *
      (oddCleanSinhMoment1 * oddCleanSinhMoment3) by ring,
    abs_mul, abs_of_nonneg hA0]
  have hmul1 :
      (2 * yoshidaEndpointA) *
          |oddCleanSinhMoment1 * oddCleanSinhMoment3| <
        (2 * yoshidaEndpointA) * (1 / 39000 : ℝ) :=
    mul_lt_mul_of_pos_left hcross (mul_pos (by norm_num) yoshidaEndpointA_pos)
  have hmul2 :
      (2 * yoshidaEndpointA) * (1 / 39000 : ℝ) <
        (2 * (69314718057 / 200000000000 : ℝ)) *
          (1 / 39000 : ℝ) := by
    gcongr
  exact hmul1.trans (hmul2.trans (by norm_num))

/-! ## Exact assembly of the clean quadratic -/

private theorem intervalIntegrable_regularKernel_mul
    (C : ℝ → ℝ) (hC : Continuous C) :
    IntervalIntegrable
      (fun t ↦ yoshidaRegularKernel (yoshidaEndpointA * t) * C t)
      volume 0 2 := by
  have herr := intervalIntegrable_regularEnvelope_mul C hC
  have hpoly : IntervalIntegrable
      (fun t : ℝ ↦ yoshidaRegularKernelPolynomial6
        (yoshidaEndpointA * t) * C t) volume 0 2 := by
    exact (by
      unfold yoshidaRegularKernelPolynomial6
      fun_prop : Continuous (fun t : ℝ ↦
        yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t) * C t))
      |>.intervalIntegrable 0 2
  apply (herr.add hpoly).congr
  intro t _ht
  ring

/-- Exact `P₁/P₃` correlation polynomial of the complete low profile. -/
theorem centeredEndpointCorrelation_oddStructuralLow
    (c d t : ℝ) :
    centeredEndpointCorrelation (factorTwoOddStructuralLowProfile c d) t =
      c ^ 2 * oddStructuralCorrelation11 t +
        2 * c * d * oddStructuralCorrelation13 t +
        d ^ 2 * oddStructuralCorrelation33 t := by
  have h1 : Continuous centeredP1 := by
    unfold centeredP1
    fun_prop
  have h3 : Continuous centeredP3 := by
    unfold centeredP3
    fun_prop
  rw [show factorTwoOddStructuralLowProfile c d =
      c • centeredP1 + d • centeredP3 by
    funext x
    unfold factorTwoOddStructuralLowProfile
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul],
    centeredEndpointCorrelation_add (c • centeredP1)
      (d • centeredP3) (h1.const_smul c) (h3.const_smul d)]
  have hself1 :
      centeredEndpointCorrelation (c • centeredP1) t =
        c ^ 2 * factorTwoCenteredCorrelationBilinear
          centeredP1 centeredP1 t := by
    rw [← factorTwoCenteredCorrelationBilinear_self,
      factorTwoCenteredCorrelationBilinear_smul_smul]
    ring
  have hself3 :
      centeredEndpointCorrelation (d • centeredP3) t =
        d ^ 2 * factorTwoCenteredCorrelationBilinear
          centeredP3 centeredP3 t := by
    rw [← factorTwoCenteredCorrelationBilinear_self,
      factorTwoCenteredCorrelationBilinear_smul_smul]
    ring
  rw [hself1, hself3,
    factorTwoCenteredCorrelationBilinear_smul_smul,
    factorTwoCenteredCorrelationBilinear_p1_p1,
    factorTwoCenteredCorrelationBilinear_p1_p3,
    factorTwoCenteredCorrelationBilinear_p3_p3]
  unfold oddStructuralCorrelation11 oddStructuralCorrelation13
    oddStructuralCorrelation33
  ring

/-- The clean regular quadratic is one exact polynomial Gram plus the one
global envelope error. -/
theorem re_regularQuadratic_oddStructuralLow_eq
    (c d : ℝ) :
    (yoshidaEndpointRegularQuadratic
      (fun x ↦ (factorTwoOddStructuralLowProfile c d x : ℂ))).re =
      (oddCleanRegularPolynomialGram11 +
          oddCleanRegularEnvelopeError oddStructuralCorrelation11) * c ^ 2 +
        2 * (oddCleanRegularPolynomialGram13 +
          oddCleanRegularEnvelopeError oddStructuralCorrelation13) * c * d +
        (oddCleanRegularPolynomialGram33 +
          oddCleanRegularEnvelopeError oddStructuralCorrelation33) * d ^ 2 := by
  rw [re_yoshidaEndpointRegularQuadratic_eq_correlation _
    (continuous_factorTwoOddStructuralLowProfile c d)]
  simp_rw [centeredEndpointCorrelation_oddStructuralLow c d]
  have h11 := intervalIntegrable_regularKernel_mul oddStructuralCorrelation11
    (by unfold oddStructuralCorrelation11; fun_prop)
  have h13 := intervalIntegrable_regularKernel_mul oddStructuralCorrelation13
    (by unfold oddStructuralCorrelation13; fun_prop)
  have h33 := intervalIntegrable_regularKernel_mul oddStructuralCorrelation33
    (by unfold oddStructuralCorrelation33; fun_prop)
  rw [show (fun t : ℝ ↦ yoshidaRegularKernel (yoshidaEndpointA * t) *
      (c ^ 2 * oddStructuralCorrelation11 t +
        2 * c * d * oddStructuralCorrelation13 t +
        d ^ 2 * oddStructuralCorrelation33 t)) =
      fun t ↦ c ^ 2 *
          (yoshidaRegularKernel (yoshidaEndpointA * t) *
            oddStructuralCorrelation11 t) +
        (2 * c * d) *
          (yoshidaRegularKernel (yoshidaEndpointA * t) *
            oddStructuralCorrelation13 t) +
        d ^ 2 *
          (yoshidaRegularKernel (yoshidaEndpointA * t) *
            oddStructuralCorrelation33 t) by
    funext t
    ring,
    intervalIntegral.integral_add
      ((h11.const_mul (c ^ 2)).add (h13.const_mul (2 * c * d)))
      (h33.const_mul (d ^ 2)),
    intervalIntegral.integral_add
      (h11.const_mul (c ^ 2)) (h13.const_mul (2 * c * d))]
  repeat rw [intervalIntegral.integral_const_mul]
  have hR11 : 2 * (∫ t : ℝ in 0..2,
      yoshidaRegularKernel (yoshidaEndpointA * t) *
        oddStructuralCorrelation11 t) =
      oddCleanRegularPolynomialGram11 +
        oddCleanRegularEnvelopeError oddStructuralCorrelation11 := by
    rw [regularIntegral_eq_polynomial_add_error _
      (by unfold oddStructuralCorrelation11; fun_prop),
      integral_regularPolynomial_correlation11]
  have hR13 : 2 * (∫ t : ℝ in 0..2,
      yoshidaRegularKernel (yoshidaEndpointA * t) *
        oddStructuralCorrelation13 t) =
      oddCleanRegularPolynomialGram13 +
        oddCleanRegularEnvelopeError oddStructuralCorrelation13 := by
    rw [regularIntegral_eq_polynomial_add_error _
      (by unfold oddStructuralCorrelation13; fun_prop),
      integral_regularPolynomial_correlation13]
  have hR33 : 2 * (∫ t : ℝ in 0..2,
      yoshidaRegularKernel (yoshidaEndpointA * t) *
        oddStructuralCorrelation33 t) =
      oddCleanRegularPolynomialGram33 +
        oddCleanRegularEnvelopeError oddStructuralCorrelation33 := by
    rw [regularIntegral_eq_polynomial_add_error _
      (by unfold oddStructuralCorrelation33; fun_prop),
      integral_regularPolynomial_correlation33]
  calc
    2 * (((c ^ 2 * ∫ t : ℝ in 0..2,
          yoshidaRegularKernel (yoshidaEndpointA * t) *
            oddStructuralCorrelation11 t) +
        2 * c * d * ∫ t : ℝ in 0..2,
          yoshidaRegularKernel (yoshidaEndpointA * t) *
            oddStructuralCorrelation13 t) +
        d ^ 2 * ∫ t : ℝ in 0..2,
          yoshidaRegularKernel (yoshidaEndpointA * t) *
            oddStructuralCorrelation33 t) =
      c ^ 2 * (2 * ∫ t : ℝ in 0..2,
          yoshidaRegularKernel (yoshidaEndpointA * t) *
            oddStructuralCorrelation11 t) +
        2 * c * d * (2 * ∫ t : ℝ in 0..2,
          yoshidaRegularKernel (yoshidaEndpointA * t) *
            oddStructuralCorrelation13 t) +
        d ^ 2 * (2 * ∫ t : ℝ in 0..2,
          yoshidaRegularKernel (yoshidaEndpointA * t) *
            oddStructuralCorrelation33 t) := by ring
    _ = _ := by rw [hR11, hR13, hR33]; ring

/-- Exact intrinsic odd mass. -/
theorem integral_oddStructuralLow_sq (c d : ℝ) :
    (∫ x : ℝ in -1..1,
      factorTwoOddStructuralLowProfile c d x ^ 2) =
      (2 / 3 : ℝ) * c ^ 2 + (2 / 7 : ℝ) * d ^ 2 := by
  have h11 : IntervalIntegrable (fun x : ℝ ↦ centeredP1 x ^ 2)
      volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    unfold centeredP1
    fun_prop
  have h13 : IntervalIntegrable
      (fun x : ℝ ↦ centeredP1 x * centeredP3 x) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    unfold centeredP1 centeredP3
    fun_prop
  have h33 : IntervalIntegrable (fun x : ℝ ↦ centeredP3 x ^ 2)
      volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    unfold centeredP3
    fun_prop
  rw [show (fun x : ℝ ↦ factorTwoOddStructuralLowProfile c d x ^ 2) =
      fun x ↦ c ^ 2 * centeredP1 x ^ 2 +
        (2 * c * d) * (centeredP1 x * centeredP3 x) +
        d ^ 2 * centeredP3 x ^ 2 by
    funext x
    unfold factorTwoOddStructuralLowProfile
    ring,
    intervalIntegral.integral_add
      ((h11.const_mul (c ^ 2)).add (h13.const_mul (2 * c * d)))
      (h33.const_mul (d ^ 2)),
    intervalIntegral.integral_add
      (h11.const_mul (c ^ 2)) (h13.const_mul (2 * c * d))]
  repeat rw [intervalIntegral.integral_const_mul]
  rw [integral_centeredP1_sq, integral_centeredP1_mul_p3,
    integral_centeredP3_sq]
  ring

private theorem coshMoment_oddStructuralLow_eq_zero (c d : ℝ) :
    yoshidaEndpointCoshMoment (factorTwoOddStructuralLowProfile c d) = 0 := by
  unfold yoshidaEndpointCoshMoment
  apply centered_interval_integral_eq_zero_of_odd
  intro x
  change Real.cosh (yoshidaEndpointA * (-x) / 2) *
      factorTwoOddStructuralLowProfile c d (-x) =
    -(Real.cosh (yoshidaEndpointA * x / 2) *
      factorTwoOddStructuralLowProfile c d x)
  rw [show yoshidaEndpointA * -x / 2 =
      -(yoshidaEndpointA * x / 2) by ring,
    Real.cosh_neg, odd_factorTwoOddStructuralLowProfile c d]
  ring

private theorem sinhMoment_oddStructuralLow
    (c d : ℝ) :
    yoshidaEndpointSinhMoment (factorTwoOddStructuralLowProfile c d) =
      c * oddCleanSinhMoment1 + d * oddCleanSinhMoment3 := by
  unfold yoshidaEndpointSinhMoment factorTwoOddStructuralLowProfile
  rw [show (fun x : ℝ ↦ Real.sinh (yoshidaEndpointA * x / 2) *
      (c * centeredP1 x + d * centeredP3 x)) =
      fun x ↦ c *
          (Real.sinh (yoshidaEndpointA * x / 2) * centeredP1 x) +
        d * (Real.sinh (yoshidaEndpointA * x / 2) * centeredP3 x) by
    funext x
    ring,
    intervalIntegral.integral_add
      (Continuous.intervalIntegrable
        (by unfold centeredP1; fun_prop) (-1) 1 |>.const_mul c)
      (Continuous.intervalIntegrable
        (by unfold centeredP3; fun_prop) (-1) 1 |>.const_mul d),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  rfl

/-- Exact structural formula from which all sharp rational data below are
deduced. -/
theorem oddCleanQuadratic_structural_eq (c d : ℝ) :
    yoshidaEndpointOddCleanQuadratic
        (factorTwoOddStructuralLowProfile c d) =
      ((14 / 9 : ℝ) - (2 / 3 : ℝ) *
          (Real.log 2 + yoshidaEndpointScalarMassLoss)) * c ^ 2 +
        2 * (1 / 5 : ℝ) * c * d +
        ((674 / 735 : ℝ) - (2 / 7 : ℝ) *
          (Real.log 2 + yoshidaEndpointScalarMassLoss)) * d ^ 2 -
        yoshidaEndpointA *
          ((oddCleanRegularPolynomialGram11 +
              oddCleanRegularEnvelopeError oddStructuralCorrelation11) * c ^ 2 +
            2 * (oddCleanRegularPolynomialGram13 +
              oddCleanRegularEnvelopeError oddStructuralCorrelation13) * c * d +
            (oddCleanRegularPolynomialGram33 +
              oddCleanRegularEnvelopeError oddStructuralCorrelation33) * d ^ 2) -
        2 * yoshidaEndpointA *
          (c * oddCleanSinhMoment1 + d * oddCleanSinhMoment3) ^ 2 := by
  have hraw := centeredRawLogEnergy_factorTwoOddStructuralLowProfile c d
  have hpotential := integral_endpointPotential_oddStructuralLow c d
  have hmass := integral_oddStructuralLow_sq c d
  have hregular := re_regularQuadratic_oddStructuralLow_eq c d
  have hhyper := yoshidaEndpointHyperbolicQuadratic_ofReal_eq_moments
    (factorTwoOddStructuralLowProfile c d)
  rw [coshMoment_oddStructuralLow_eq_zero,
    sinhMoment_oddStructuralLow] at hhyper
  unfold yoshidaEndpointOddCleanQuadratic
  dsimp only
  rw [hraw, hpotential, hmass, hregular, hhyper]
  ring

/-! ## Rational entry data -/

private theorem endpointA_pow_fine_bounds (n : ℕ) (hn : n ≠ 0) :
    (69314718055 / 200000000000 : ℝ) ^ n < yoshidaEndpointA ^ n ∧
      yoshidaEndpointA ^ n <
        (69314718057 / 200000000000 : ℝ) ^ n := by
  constructor
  · exact pow_lt_pow_left₀ endpointA_fine_bounds.1 (by norm_num) hn
  · exact pow_lt_pow_left₀ endpointA_fine_bounds.2
      yoshidaEndpointA_pos.le hn

private theorem log_two_add_scalarMassLoss_lt :
    Real.log 2 + yoshidaEndpointScalarMassLoss < (20489 / 10000 : ℝ) := by
  have hsplit : Real.log (Real.pi * Real.log 2) =
      Real.log Real.pi + Real.log (Real.log 2) := by
    rw [Real.log_mul Real.pi_pos.ne'
      (Real.log_pos (by norm_num)).ne']
  unfold yoshidaEndpointScalarMassLoss
  rw [hsplit]
  linarith [strict_log_two_fine_bounds.2,
    strict_euler_gamma_bounds.2, strict_log_pi_bounds.2,
    strict_log_log_two_bounds.2]

private theorem regularPolynomialGram11_lt :
    oddCleanRegularPolynomialGram11 < (71 / 10000 : ℝ) := by
  have h1 := endpointA_pow_fine_bounds 1 (by norm_num)
  have h2 := endpointA_pow_fine_bounds 2 (by norm_num)
  have h3 := endpointA_pow_fine_bounds 3 (by norm_num)
  have h4 := endpointA_pow_fine_bounds 4 (by norm_num)
  have h5 := endpointA_pow_fine_bounds 5 (by norm_num)
  have h6 := endpointA_pow_fine_bounds 6 (by norm_num)
  unfold oddCleanRegularPolynomialGram11
  nlinarith [pow_nonneg yoshidaEndpointA_pos.le 3,
    pow_nonneg yoshidaEndpointA_pos.le 4]

private theorem regularPolynomialGram13_bounds :
    (-292 / 1000000 : ℝ) < oddCleanRegularPolynomialGram13 ∧
      oddCleanRegularPolynomialGram13 < (-289 / 1000000 : ℝ) := by
  have h1 := endpointA_pow_fine_bounds 1 (by norm_num)
  have h3 := endpointA_pow_fine_bounds 3 (by norm_num)
  have h4 := endpointA_pow_fine_bounds 4 (by norm_num)
  have h5 := endpointA_pow_fine_bounds 5 (by norm_num)
  have h6 := endpointA_pow_fine_bounds 6 (by norm_num)
  unfold oddCleanRegularPolynomialGram13
  constructor <;> nlinarith [pow_nonneg yoshidaEndpointA_pos.le 5,
    pow_nonneg yoshidaEndpointA_pos.le 6]

private theorem regularPolynomialGram33_lt :
    oddCleanRegularPolynomialGram33 < (185 / 1000000 : ℝ) := by
  have h1 := endpointA_pow_fine_bounds 1 (by norm_num)
  have h3 := endpointA_pow_fine_bounds 3 (by norm_num)
  have h5 := endpointA_pow_fine_bounds 5 (by norm_num)
  have h6 := endpointA_pow_fine_bounds 6 (by norm_num)
  unfold oddCleanRegularPolynomialGram33
  nlinarith

private theorem regularTotal11_lt :
    oddCleanRegularPolynomialGram11 +
        oddCleanRegularEnvelopeError oddStructuralCorrelation11 <
      (711 / 100000 : ℝ) := by
  have hp := regularPolynomialGram11_lt
  have he := abs_oddCleanRegularEnvelopeError11_le
  have hle := le_abs_self
    (oddCleanRegularEnvelopeError oddStructuralCorrelation11)
  nlinarith

private theorem regularTotal13_bounds :
    (-3 / 10000 : ℝ) <
        oddCleanRegularPolynomialGram13 +
          oddCleanRegularEnvelopeError oddStructuralCorrelation13 ∧
      oddCleanRegularPolynomialGram13 +
          oddCleanRegularEnvelopeError oddStructuralCorrelation13 <
        (-7 / 25000 : ℝ) := by
  have hp := regularPolynomialGram13_bounds
  have he := abs_oddCleanRegularEnvelopeError13_lt
  have hlo := neg_abs_le
    (oddCleanRegularEnvelopeError oddStructuralCorrelation13)
  have hup := le_abs_self
    (oddCleanRegularEnvelopeError oddStructuralCorrelation13)
  constructor <;> nlinarith

private theorem regularTotal33_lt :
    oddCleanRegularPolynomialGram33 +
        oddCleanRegularEnvelopeError oddStructuralCorrelation33 <
      (187 / 1000000 : ℝ) := by
  have hp := regularPolynomialGram33_lt
  have he := abs_oddCleanRegularEnvelopeError33_le
  have hle := le_abs_self
    (oddCleanRegularEnvelopeError oddStructuralCorrelation33)
  nlinarith

/-- Exact first diagonal entry after structural assembly. -/
theorem yoshidaEndpointOddLowGram11_structural_eq :
    yoshidaEndpointOddLowGram11 =
      (14 / 9 : ℝ) - (2 / 3 : ℝ) *
          (Real.log 2 + yoshidaEndpointScalarMassLoss) -
        yoshidaEndpointA *
          (oddCleanRegularPolynomialGram11 +
            oddCleanRegularEnvelopeError oddStructuralCorrelation11) -
        2 * yoshidaEndpointA * oddCleanSinhMoment1 ^ 2 := by
  have h := oddCleanQuadratic_structural_eq 1 0
  have hprofile : factorTwoOddStructuralLowProfile 1 0 = centeredP1 := by
    funext x
    unfold factorTwoOddStructuralLowProfile
    ring
  rw [hprofile] at h
  unfold yoshidaEndpointOddLowGram11
  norm_num at h ⊢
  nlinarith

/-- Exact third diagonal entry after structural assembly. -/
theorem yoshidaEndpointOddLowGram33_structural_eq :
    yoshidaEndpointOddLowGram33 =
      (674 / 735 : ℝ) - (2 / 7 : ℝ) *
          (Real.log 2 + yoshidaEndpointScalarMassLoss) -
        yoshidaEndpointA *
          (oddCleanRegularPolynomialGram33 +
            oddCleanRegularEnvelopeError oddStructuralCorrelation33) -
        2 * yoshidaEndpointA * oddCleanSinhMoment3 ^ 2 := by
  have h := oddCleanQuadratic_structural_eq 0 1
  have hprofile : factorTwoOddStructuralLowProfile 0 1 = centeredP3 := by
    funext x
    unfold factorTwoOddStructuralLowProfile
    ring
  rw [hprofile] at h
  unfold yoshidaEndpointOddLowGram33
  norm_num at h ⊢
  nlinarith

/-- Exact off-diagonal entry after structural assembly. -/
theorem yoshidaEndpointOddLowGram13_structural_eq :
    yoshidaEndpointOddLowGram13 =
      (1 / 5 : ℝ) - yoshidaEndpointA *
          (oddCleanRegularPolynomialGram13 +
            oddCleanRegularEnvelopeError oddStructuralCorrelation13) -
        2 * yoshidaEndpointA * oddCleanSinhMoment1 * oddCleanSinhMoment3 := by
  have hstruct := oddCleanQuadratic_structural_eq 1 1
  have hgram := yoshidaEndpointOddLowGram_quadratic 1 1
  rw [hgram] at hstruct
  rw [yoshidaEndpointOddLowGram11_structural_eq,
    yoshidaEndpointOddLowGram33_structural_eq] at hstruct
  norm_num at hstruct ⊢
  nlinarith

/-- Sharp structural lower bound for the first clean diagonal. -/
theorem yoshidaEndpointOddLowGram11_gt_1778_div_10000 :
    (1778 / 10000 : ℝ) < yoshidaEndpointOddLowGram11 := by
  rw [yoshidaEndpointOddLowGram11_structural_eq]
  have hT := log_two_add_scalarMassLoss_lt
  have hR := regularTotal11_lt
  have hA := endpointA_fine_bounds.2
  have hreg1 :
      yoshidaEndpointA *
          (oddCleanRegularPolynomialGram11 +
            oddCleanRegularEnvelopeError oddStructuralCorrelation11) <
        yoshidaEndpointA * (711 / 100000 : ℝ) :=
    mul_lt_mul_of_pos_left hR yoshidaEndpointA_pos
  have hreg2 :
      yoshidaEndpointA * (711 / 100000 : ℝ) <
        (69314718057 / 200000000000 : ℝ) *
          (711 / 100000 : ℝ) :=
    mul_lt_mul_of_pos_right hA (by norm_num)
  have hhyper := oddCleanHyperbolicLoss11_lt
  nlinarith

/-- Sharp structural lower bound for the third clean diagonal. -/
theorem yoshidaEndpointOddLowGram33_gt_3315_div_10000 :
    (3315 / 10000 : ℝ) < yoshidaEndpointOddLowGram33 := by
  rw [yoshidaEndpointOddLowGram33_structural_eq]
  have hT := log_two_add_scalarMassLoss_lt
  have hR := regularTotal33_lt
  have hA := endpointA_fine_bounds.2
  have hreg1 :
      yoshidaEndpointA *
          (oddCleanRegularPolynomialGram33 +
            oddCleanRegularEnvelopeError oddStructuralCorrelation33) <
        yoshidaEndpointA * (187 / 1000000 : ℝ) :=
    mul_lt_mul_of_pos_left hR yoshidaEndpointA_pos
  have hreg2 :
      yoshidaEndpointA * (187 / 1000000 : ℝ) <
        (69314718057 / 200000000000 : ℝ) *
          (187 / 1000000 : ℝ) :=
    mul_lt_mul_of_pos_right hA (by norm_num)
  have hhyper := oddCleanHyperbolicLoss33_lt
  nlinarith

/-- The clean off-diagonal lies in a two-ten-thousandths interval around
`0.2001`. -/
theorem yoshidaEndpointOddLowGram13_bounds :
    (1 / 5 : ℝ) < yoshidaEndpointOddLowGram13 ∧
      yoshidaEndpointOddLowGram13 < (2002 / 10000 : ℝ) := by
  rw [yoshidaEndpointOddLowGram13_structural_eq]
  let R : ℝ := oddCleanRegularPolynomialGram13 +
    oddCleanRegularEnvelopeError oddStructuralCorrelation13
  let H : ℝ :=
    2 * yoshidaEndpointA * oddCleanSinhMoment1 * oddCleanSinhMoment3
  have hR : (-3 / 10000 : ℝ) < R ∧ R < (-7 / 25000 : ℝ) := by
    simpa only [R] using regularTotal13_bounds
  have hH : |H| < (9 / 500000 : ℝ) := by
    simpa only [H] using abs_oddCleanHyperbolicCross_lt
  have hHlo : -(9 / 500000 : ℝ) < H := by
    have := neg_abs_le H
    linarith
  have hHup : H < (9 / 500000 : ℝ) :=
    lt_of_le_of_lt (le_abs_self H) hH
  have hAlo := endpointA_fine_bounds.1
  have hAup := endpointA_fine_bounds.2
  have hnegRlo : (7 / 25000 : ℝ) < -R := by linarith
  have hgain1 :
      yoshidaEndpointA * (7 / 25000 : ℝ) <
        yoshidaEndpointA * (-R) :=
    mul_lt_mul_of_pos_left hnegRlo yoshidaEndpointA_pos
  have hgain0 :
      (9 / 500000 : ℝ) <
        (69314718055 / 200000000000 : ℝ) * (7 / 25000 : ℝ) := by
    norm_num
  have hgainA :
      (69314718055 / 200000000000 : ℝ) * (7 / 25000 : ℝ) <
        yoshidaEndpointA * (7 / 25000 : ℝ) :=
    mul_lt_mul_of_pos_right hAlo (by norm_num)
  have hgain : (9 / 500000 : ℝ) < -yoshidaEndpointA * R := by
    calc
      (9 / 500000 : ℝ) <
          (69314718055 / 200000000000 : ℝ) * (7 / 25000 : ℝ) := hgain0
      _ < yoshidaEndpointA * (7 / 25000 : ℝ) := hgainA
      _ < yoshidaEndpointA * (-R) := hgain1
      _ = -yoshidaEndpointA * R := by ring
  have hnegRup : -R < (3 / 10000 : ℝ) := by linarith
  have hreg1 :
      yoshidaEndpointA * (-R) <
        yoshidaEndpointA * (3 / 10000 : ℝ) :=
    mul_lt_mul_of_pos_left hnegRup yoshidaEndpointA_pos
  have hreg2 :
      yoshidaEndpointA * (3 / 10000 : ℝ) <
        (69314718057 / 200000000000 : ℝ) * (3 / 10000 : ℝ) :=
    mul_lt_mul_of_pos_right hAup (by norm_num)
  change (1 / 5 : ℝ) < 1 / 5 - yoshidaEndpointA * R - H ∧
    1 / 5 - yoshidaEndpointA * R - H < (2002 / 10000 : ℝ)
  constructor
  · nlinarith
  · have hrat :
        (69314718057 / 200000000000 : ℝ) * (3 / 10000 : ℝ) +
            9 / 500000 < 2 / 10000 := by
      norm_num
    nlinarith

/-- Tight centered enclosure of the clean cross entry. -/
theorem abs_yoshidaEndpointOddLowGram13_sub_2001_div_10000_lt :
    |yoshidaEndpointOddLowGram13 - (2001 / 10000 : ℝ)| <
      (1 / 10000 : ℝ) := by
  rw [abs_lt]
  constructor <;> nlinarith [yoshidaEndpointOddLowGram13_bounds.1,
    yoshidaEndpointOddLowGram13_bounds.2]

/-- Coupled rational lower quadratic with the sharp cross orientation kept.
This is the form intended for the intrinsic static-minus gate. -/
theorem oddClean_rationalGram_le (c d : ℝ) :
    (1777 / 10000 : ℝ) * c ^ 2 +
        2 * (2001 / 10000 : ℝ) * c * d +
        (3314 / 10000 : ℝ) * d ^ 2 ≤
      yoshidaEndpointOddCleanQuadratic
        (factorTwoOddStructuralLowProfile c d) := by
  rw [yoshidaEndpointOddLowGram_quadratic]
  have ha := yoshidaEndpointOddLowGram11_gt_1778_div_10000
  have hb := yoshidaEndpointOddLowGram13_bounds
  have he := yoshidaEndpointOddLowGram33_gt_3315_div_10000
  have haScaled :
      (1778 / 10000 : ℝ) * c ^ 2 ≤
        yoshidaEndpointOddLowGram11 * c ^ 2 :=
    mul_le_mul_of_nonneg_right ha.le (sq_nonneg c)
  have heScaled :
      (3315 / 10000 : ℝ) * d ^ 2 ≤
        yoshidaEndpointOddLowGram33 * d ^ 2 :=
    mul_le_mul_of_nonneg_right he.le (sq_nonneg d)
  have hcross :
      2 * (2001 / 10000 : ℝ) * c * d -
          (1 / 10000 : ℝ) * (c ^ 2 + d ^ 2) ≤
        2 * yoshidaEndpointOddLowGram13 * c * d := by
    by_cases hcd : 0 ≤ c * d
    · have hmul := mul_le_mul_of_nonneg_right hb.1.le hcd
      nlinarith [sq_nonneg (c - d)]
    · have hcd' : c * d ≤ 0 := le_of_not_ge hcd
      have hmul := mul_le_mul_of_nonpos_right hb.2.le hcd'
      nlinarith [sq_nonneg (c + d)]
  nlinarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddCleanSharp

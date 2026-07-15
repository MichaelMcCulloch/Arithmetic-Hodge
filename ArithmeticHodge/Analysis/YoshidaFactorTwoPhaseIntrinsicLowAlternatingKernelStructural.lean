import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseOddAffineKernelEstimate
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLow
import ArithmeticHodge.Analysis.YoshidaFactorTwoStructuralConstantBounds

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowAlternatingKernelStructural

noncomputable section

open YoshidaConstantBounds
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOcticPotential
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoPhaseEnvelope
open YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseOddAffineKernelEstimate
open YoshidaFactorTwoStructuralConstantBounds
open YoshidaRegularKernelBound

/-!
# Structural control of the intrinsic alternating kernel

The four low even--odd cross differences have a common endpoint factor
`t * (2 - t)`.  Splitting the antisymmetric Cauchy poles against that factor
leaves a continuous rational kernel.  The only analytic estimate below is
the global regular-kernel estimate imported above.
-/

/-- Exact `P₀/P₁` ordered cross difference. -/
theorem factorTwoCenteredCrossDifference_p0_p1
    (t : ℝ) :
    factorTwoCenteredCrossCorrelation centeredP1 centeredEvenP0 t -
        factorTwoCenteredCrossCorrelation centeredEvenP0 centeredP1 t =
      t * (2 - t) := by
  unfold factorTwoCenteredCrossCorrelation centeredP1 centeredEvenP0
  simp only [mul_one, one_mul]
  rw [show (fun x : ℝ ↦ t + x) = fun x ↦ t + 1 * x by
    funext x; ring]
  rw [intervalIntegral.integral_add
      (Continuous.intervalIntegrable (by fun_prop) (-1) (1 - t))
      (Continuous.intervalIntegrable (by fun_prop) (-1) (1 - t))]
  simp only [intervalIntegral.integral_const, smul_eq_mul, integral_id]
  simp only [one_mul]
  rw [integral_id]
  ring

/-- Exact `P₀/P₃` ordered cross difference. -/
theorem factorTwoCenteredCrossDifference_p0_p3
    (t : ℝ) :
    factorTwoCenteredCrossCorrelation centeredP3 centeredEvenP0 t -
        factorTwoCenteredCrossCorrelation centeredEvenP0 centeredP3 t =
      t * (2 - t) * (1 - (5 / 2 : ℝ) * t + (5 / 4 : ℝ) * t ^ 2) := by
  unfold factorTwoCenteredCrossCorrelation centeredP3 centeredEvenP0
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (-1) (1 - t))
    (Continuous.intervalIntegrable (by fun_prop) (-1) (1 - t))]
  simp only [intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const,
    integral_pow, smul_eq_mul]
  rw [intervalIntegral.integral_const_mul, integral_id]
  ring

/-- Exact `P₂/P₁` ordered cross difference. -/
theorem factorTwoCenteredCrossDifference_p2_p1
    (t : ℝ) :
    factorTwoCenteredCrossCorrelation centeredP1 centeredEvenP2 t -
        factorTwoCenteredCrossCorrelation centeredEvenP2 centeredP1 t =
      t * (2 - t) *
        (-1 + (1 / 2 : ℝ) * t + (1 / 4 : ℝ) * t ^ 2) := by
  unfold factorTwoCenteredCrossCorrelation centeredP1 centeredEvenP2
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (-1) (1 - t))
    (Continuous.intervalIntegrable (by fun_prop) (-1) (1 - t))]
  simp only [intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const,
    integral_pow, smul_eq_mul]
  repeat rw [intervalIntegral.integral_const_mul, integral_id]
  ring

/-- Exact `P₂/P₃` ordered cross difference. -/
theorem factorTwoCenteredCrossDifference_p2_p3
    (t : ℝ) :
    factorTwoCenteredCrossCorrelation centeredP3 centeredEvenP2 t -
        factorTwoCenteredCrossCorrelation centeredEvenP2 centeredP3 t =
      t * (2 - t) *
        (1 - t - (1 / 2 : ℝ) * t ^ 2 + (1 / 4 : ℝ) * t ^ 3 +
          (1 / 8 : ℝ) * t ^ 4) := by
  unfold factorTwoCenteredCrossCorrelation centeredP3 centeredEvenP2
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (-1) (1 - t))
    (Continuous.intervalIntegrable (by fun_prop) (-1) (1 - t))]
  simp only [intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const,
    integral_pow, smul_eq_mul]
  repeat rw [intervalIntegral.integral_const_mul, integral_id]
  rw [show (fun x : ℝ ↦ t * (3 / 4 : ℝ) - t * x ^ 2 * 6) =
      fun x ↦ t * (3 / 4 : ℝ) + (-6 * t) * x ^ 2 by
    funext x; ring,
    intervalIntegral.integral_add
      (Continuous.intervalIntegrable (by fun_prop) (-1) (1 - t))
      (Continuous.intervalIntegrable (by fun_prop) (-1) (1 - t))]
  simp only [intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul, integral_pow, smul_eq_mul]
  ring

/-! ## Exact regular--pole separation -/

/-- The common cross-difference shape attached to a scalar polynomial `q`. -/
def intrinsicAlternatingCorrelation (q : ℝ → ℝ) (t : ℝ) : ℝ :=
  t * (2 - t) * q t

/-- The sole analytic remainder after replacing the pole-free kernel by
its global linear model. -/
def intrinsicAlternatingRegularError (q : ℝ → ℝ) : ℝ :=
  ∫ t : ℝ in 0..2,
    (yoshidaEndpointA * factorTwoCenteredAntisymmetricRegularWeight t -
      t / 10) * intrinsicAlternatingCorrelation q t

/-- The explicit archimedean model left after the two Cauchy poles cancel
against the common endpoint factor. -/
def intrinsicAlternatingArchModel (q : ℝ → ℝ) : ℝ :=
  ∫ t : ℝ in 0..2,
    (t / 10) * intrinsicAlternatingCorrelation q t +
      t ^ 2 * q t / (2 + t)

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

private theorem measurable_factorTwoCenteredAntisymmetricRegularWeight_local :
    Measurable factorTwoCenteredAntisymmetricRegularWeight := by
  unfold factorTwoCenteredAntisymmetricRegularWeight
  exact (((measurable_const.mul
      (Real.measurable_cosh.comp (by fun_prop))).sub
        (measurable_const.mul
          (Real.measurable_cosh.comp (by fun_prop)))).sub
      (measurable_yoshidaRegularKernel_local.comp (by fun_prop))).add
        (measurable_yoshidaRegularKernel_local.comp (by fun_prop))

private theorem intervalIntegrable_intrinsicAlternatingRegularError
    (C : ℝ → ℝ) (hC : Continuous C) :
    IntervalIntegrable
      (fun t ↦
        (yoshidaEndpointA * factorTwoCenteredAntisymmetricRegularWeight t -
          t / 10) * C t) volume 0 2 := by
  let f : ℝ → ℝ := fun t ↦
    (yoshidaEndpointA * factorTwoCenteredAntisymmetricRegularWeight t -
      t / 10) * C t
  let g : ℝ → ℝ := fun t ↦ (1 / 1000 : ℝ) * |C t|
  have hgIcc : IntegrableOn g (Icc (0 : ℝ) 2) volume := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    exact (continuous_const.mul hC.abs).continuousOn
  have hg : Integrable g (volume.restrict (Ioc (0 : ℝ) 2)) :=
    hgIcc.mono_set Ioc_subset_Icc_self
  have hfmeas : AEStronglyMeasurable f
      (volume.restrict (Ioc (0 : ℝ) 2)) := by
    apply Measurable.aestronglyMeasurable
    dsimp only [f]
    exact ((measurable_const.mul
      measurable_factorTwoCenteredAntisymmetricRegularWeight_local).sub
        (measurable_id.div_const 10)).mul hC.measurable
  have hfg : ∀ᵐ t : ℝ ∂(volume.restrict (Ioc (0 : ℝ) 2)),
      ‖f t‖ ≤ g t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hk :=
      abs_yoshidaEndpointA_mul_factorTwoCenteredAntisymmetricRegularWeight_sub_linear_le_one_thousand
        ht.1.le ht.2
    dsimp only [f, g]
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right hk (abs_nonneg (C t))
  constructor
  · exact Integrable.mono' hg hfmeas hfg
  · simp

theorem abs_intrinsicAlternatingRegularError_le
    (q : ℝ → ℝ) (hq : Continuous q) :
    |intrinsicAlternatingRegularError q| ≤
      (1 / 1000 : ℝ) *
        (∫ t : ℝ in 0..2, |intrinsicAlternatingCorrelation q t|) := by
  let C : ℝ → ℝ := intrinsicAlternatingCorrelation q
  let f : ℝ → ℝ := fun t ↦
    (yoshidaEndpointA * factorTwoCenteredAntisymmetricRegularWeight t -
      t / 10) * C t
  let g : ℝ → ℝ := fun t ↦ (1 / 1000 : ℝ) * |C t|
  have hC : Continuous C := by
    dsimp only [C]
    unfold intrinsicAlternatingCorrelation
    fun_prop
  have hf : IntervalIntegrable f volume 0 2 := by
    dsimp only [f]
    exact intervalIntegrable_intrinsicAlternatingRegularError C hC
  have hg : IntervalIntegrable g volume 0 2 := by
    dsimp only [g]
    exact (hC.abs.const_mul (1 / 1000 : ℝ)).intervalIntegrable 0 2
  have hmono : (∫ t : ℝ in 0..2, |f t|) ≤ ∫ t : ℝ in 0..2, g t := by
    apply intervalIntegral.integral_mono_on (by norm_num) hf.abs hg
    intro t ht
    have hk :=
      abs_yoshidaEndpointA_mul_factorTwoCenteredAntisymmetricRegularWeight_sub_linear_le_one_thousand
        ht.1 ht.2
    dsimp only [f, g]
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hk (abs_nonneg (C t))
  calc
    |intrinsicAlternatingRegularError q| = |∫ t : ℝ in 0..2, f t| := by
      rfl
    _ ≤ ∫ t : ℝ in 0..2, |f t| :=
      intervalIntegral.abs_integral_le_integral_abs (by norm_num)
    _ ≤ ∫ t : ℝ in 0..2, g t := hmono
    _ = (1 / 1000 : ℝ) *
        (∫ t : ℝ in 0..2, |intrinsicAlternatingCorrelation q t|) := by
      rw [intervalIntegral.integral_const_mul]

private theorem intervalIntegrable_intrinsicAlternatingArchModel
    (q : ℝ → ℝ) (hq : Continuous q) :
    IntervalIntegrable
      (fun t ↦
        (t / 10) * intrinsicAlternatingCorrelation q t +
          t ^ 2 * q t / (2 + t)) volume 0 2 := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] at ht
  have hden : 2 + t ≠ 0 := by linarith [ht.1]
  apply ContinuousAt.continuousWithinAt
  apply ContinuousAt.add
  · unfold intrinsicAlternatingCorrelation
    fun_prop
  · exact ContinuousAt.div (by fun_prop) (by fun_prop) hden

/-- The regular alternating remainder is linear under profile subtraction. -/
theorem intrinsicAlternatingRegularError_sub
    (q r : ℝ → ℝ) (hq : Continuous q) (hr : Continuous r) :
    intrinsicAlternatingRegularError (q - r) =
      intrinsicAlternatingRegularError q -
        intrinsicAlternatingRegularError r := by
  have hqI := intervalIntegrable_intrinsicAlternatingRegularError
    (intrinsicAlternatingCorrelation q) (by
      unfold intrinsicAlternatingCorrelation
      fun_prop)
  have hrI := intervalIntegrable_intrinsicAlternatingRegularError
    (intrinsicAlternatingCorrelation r) (by
      unfold intrinsicAlternatingCorrelation
      fun_prop)
  have hqI' : IntervalIntegrable
      (fun t ↦
        (yoshidaEndpointA * factorTwoCenteredAntisymmetricRegularWeight t -
          t / 10) * (t * (2 - t) * q t)) volume 0 2 := by
    simpa only [intrinsicAlternatingCorrelation] using hqI
  have hrI' : IntervalIntegrable
      (fun t ↦
        (yoshidaEndpointA * factorTwoCenteredAntisymmetricRegularWeight t -
          t / 10) * (t * (2 - t) * r t)) volume 0 2 := by
    simpa only [intrinsicAlternatingCorrelation] using hrI
  unfold intrinsicAlternatingRegularError intrinsicAlternatingCorrelation
  rw [show (fun t : ℝ ↦
      (yoshidaEndpointA * factorTwoCenteredAntisymmetricRegularWeight t -
        t / 10) * (t * (2 - t) * ((q - r) t))) =
    fun t ↦
      (yoshidaEndpointA * factorTwoCenteredAntisymmetricRegularWeight t -
        t / 10) * (t * (2 - t) * q t) -
      (yoshidaEndpointA * factorTwoCenteredAntisymmetricRegularWeight t -
        t / 10) * (t * (2 - t) * r t) by
    funext t
    simp only [Pi.sub_apply]
    ring,
    intervalIntegral.integral_sub hqI' hrI']

/-- The explicit archimedean alternating model has the same subtraction
linearity as its regular remainder. -/
theorem intrinsicAlternatingArchModel_sub
    (q r : ℝ → ℝ) (hq : Continuous q) (hr : Continuous r) :
    intrinsicAlternatingArchModel (q - r) =
      intrinsicAlternatingArchModel q - intrinsicAlternatingArchModel r := by
  have hqI := intervalIntegrable_intrinsicAlternatingArchModel q hq
  have hrI := intervalIntegrable_intrinsicAlternatingArchModel r hr
  have hqI' : IntervalIntegrable
      (fun t ↦ (t / 10) * (t * (2 - t) * q t) +
        t ^ 2 * q t / (2 + t)) volume 0 2 := by
    simpa only [intrinsicAlternatingCorrelation] using hqI
  have hrI' : IntervalIntegrable
      (fun t ↦ (t / 10) * (t * (2 - t) * r t) +
        t ^ 2 * r t / (2 + t)) volume 0 2 := by
    simpa only [intrinsicAlternatingCorrelation] using hrI
  unfold intrinsicAlternatingArchModel intrinsicAlternatingCorrelation
  rw [show (fun t : ℝ ↦
      (t / 10) * (t * (2 - t) * ((q - r) t)) +
        t ^ 2 * (q - r) t / (2 + t)) =
    fun t ↦
      ((t / 10) * (t * (2 - t) * q t) + t ^ 2 * q t / (2 + t)) -
      ((t / 10) * (t * (2 - t) * r t) + t ^ 2 * r t / (2 + t)) by
    funext t
    simp only [Pi.sub_apply]
    ring,
    intervalIntegral.integral_sub hqI' hrI']

private theorem endpoint_mul_integral_antisymmetricWeight_mul_eq_regular_poles
    (q : ℝ → ℝ) :
    yoshidaEndpointA *
        (∫ t : ℝ in 0..2,
          factorTwoAntisymmetricWeight (yoshidaEndpointA * t) *
            intrinsicAlternatingCorrelation q t) =
      ∫ t : ℝ in 0..2,
        (yoshidaEndpointA *
              factorTwoCenteredAntisymmetricRegularWeight t -
            1 / (2 * (2 + t)) + 1 / (2 * (2 - t))) *
          intrinsicAlternatingCorrelation q t := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_ae_restrict
  filter_upwards [
      (Set.countable_singleton (2 : ℝ)).ae_notMem
        (volume.restrict (Set.uIoc (0 : ℝ) 2)),
      ae_restrict_mem measurableSet_uIoc] with t ht2 ht
  have ht' : t ∈ Set.Ioc (0 : ℝ) 2 := by
    simpa only [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using ht
  have htne : t ≠ 2 := by simpa using ht2
  have htlt : t < 2 := lt_of_le_of_ne ht'.2 htne
  calc
    yoshidaEndpointA *
        (factorTwoAntisymmetricWeight (yoshidaEndpointA * t) *
          intrinsicAlternatingCorrelation q t) =
      (yoshidaEndpointA *
        factorTwoAntisymmetricWeight (yoshidaEndpointA * t)) *
          intrinsicAlternatingCorrelation q t := by ring
    _ = _ := by
      rw [yoshidaEndpointA_mul_factorTwoAntisymmetricWeight_eq_regular_poles
        ht'.1 htlt]

private theorem integral_regular_poles_eq_error_add_archModel
    (q : ℝ → ℝ) (hq : Continuous q) :
    (∫ t : ℝ in 0..2,
        (yoshidaEndpointA *
              factorTwoCenteredAntisymmetricRegularWeight t -
            1 / (2 * (2 + t)) + 1 / (2 * (2 - t))) *
          intrinsicAlternatingCorrelation q t) =
      intrinsicAlternatingRegularError q +
        intrinsicAlternatingArchModel q := by
  let f : ℝ → ℝ := fun t ↦
    (yoshidaEndpointA * factorTwoCenteredAntisymmetricRegularWeight t -
      t / 10) * intrinsicAlternatingCorrelation q t
  let g : ℝ → ℝ := fun t ↦
    (t / 10) * intrinsicAlternatingCorrelation q t +
      t ^ 2 * q t / (2 + t)
  have hC : Continuous (intrinsicAlternatingCorrelation q) := by
    unfold intrinsicAlternatingCorrelation
    fun_prop
  have hf : IntervalIntegrable f volume 0 2 := by
    dsimp only [f]
    exact intervalIntegrable_intrinsicAlternatingRegularError
      (intrinsicAlternatingCorrelation q) hC
  have hg : IntervalIntegrable g volume 0 2 := by
    dsimp only [g]
    exact intervalIntegrable_intrinsicAlternatingArchModel q hq
  calc
    (∫ t : ℝ in 0..2,
        (yoshidaEndpointA *
              factorTwoCenteredAntisymmetricRegularWeight t -
            1 / (2 * (2 + t)) + 1 / (2 * (2 - t))) *
          intrinsicAlternatingCorrelation q t) =
      ∫ t : ℝ in 0..2, f t + g t := by
        apply intervalIntegral.integral_congr_ae_restrict
        filter_upwards [
            (Set.countable_singleton (2 : ℝ)).ae_notMem
              (volume.restrict (Set.uIoc (0 : ℝ) 2)),
            ae_restrict_mem measurableSet_uIoc] with t ht2 ht
        have ht' : t ∈ Set.Ioc (0 : ℝ) 2 := by
          simpa only [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using ht
        have htne : t ≠ 2 := by simpa using ht2
        have hplus : 2 + t ≠ 0 := by linarith [ht'.1]
        have hminus : 2 - t ≠ 0 := sub_ne_zero.mpr htne.symm
        dsimp only [f, g, intrinsicAlternatingCorrelation]
        field_simp [hplus, hminus]
        ring
    _ = intrinsicAlternatingRegularError q +
        intrinsicAlternatingArchModel q := by
      rw [intervalIntegral.integral_add hf hg]
      rfl

/-- Exact structural normal form for an even--odd alternating coupling whose
cross difference has the common endpoint factor. -/
theorem factorTwoCenteredAlternatingCoupling_eq_regularError_add_archModel
    (e o q : ℝ → ℝ) (hq : Continuous q)
    (hcross : ∀ t ∈ Icc (0 : ℝ) 2,
      factorTwoCenteredCrossCorrelation o e t -
          factorTwoCenteredCrossCorrelation e o t =
        intrinsicAlternatingCorrelation q t) :
    factorTwoCenteredAlternatingCoupling e o =
      intrinsicAlternatingRegularError q +
        intrinsicAlternatingArchModel q -
        (Real.log 3 / Real.sqrt 3) *
          intrinsicAlternatingCorrelation q
            (factorTwoPrimeShift / yoshidaEndpointA) := by
  have hint :
      (∫ t : ℝ in 0..2,
        factorTwoAntisymmetricWeight (yoshidaEndpointA * t) *
          (factorTwoCenteredCrossCorrelation o e t -
            factorTwoCenteredCrossCorrelation e o t)) =
        ∫ t : ℝ in 0..2,
          factorTwoAntisymmetricWeight (yoshidaEndpointA * t) *
            intrinsicAlternatingCorrelation q t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] at ht
    change factorTwoAntisymmetricWeight (yoshidaEndpointA * t) *
        (factorTwoCenteredCrossCorrelation o e t -
          factorTwoCenteredCrossCorrelation e o t) =
      factorTwoAntisymmetricWeight (yoshidaEndpointA * t) *
        intrinsicAlternatingCorrelation q t
    rw [hcross t ht]
  have htau := factorTwoPrimeShift_div_endpointA_mem_one_two
  have htauIcc : factorTwoPrimeShift / yoshidaEndpointA ∈ Icc (0 : ℝ) 2 :=
    ⟨by linarith [htau.1], htau.2⟩
  have hprime := hcross (factorTwoPrimeShift / yoshidaEndpointA) htauIcc
  unfold factorTwoCenteredAlternatingCoupling
  rw [hint, hprime,
    endpoint_mul_integral_antisymmetricWeight_mul_eq_regular_poles,
    integral_regular_poles_eq_error_add_archModel q hq]

/-! ## The four coupled intrinsic directions -/

def intrinsicAlternatingQ01Plus21 (t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * t + (1 / 4 : ℝ) * t ^ 2

def intrinsicAlternatingQ01Minus21 (t : ℝ) : ℝ :=
  2 - (1 / 2 : ℝ) * t - (1 / 4 : ℝ) * t ^ 2

def intrinsicAlternatingQ03Plus23 (t : ℝ) : ℝ :=
  2 - (7 / 2 : ℝ) * t + (3 / 4 : ℝ) * t ^ 2 +
    (1 / 4 : ℝ) * t ^ 3 + (1 / 8 : ℝ) * t ^ 4

def intrinsicAlternatingQ03Minus23 (t : ℝ) : ℝ :=
  -(3 / 2 : ℝ) * t + (7 / 4 : ℝ) * t ^ 2 -
    (1 / 4 : ℝ) * t ^ 3 - (1 / 8 : ℝ) * t ^ 4

private def centeredEvenP0PlusP2 : ℝ → ℝ :=
  centeredEvenP0 + centeredEvenP2

private def centeredEvenP0MinusP2 : ℝ → ℝ :=
  centeredEvenP0 + (-1 : ℝ) • centeredEvenP2

private theorem continuous_neg_centeredEvenP2 :
    Continuous ((-1 : ℝ) • centeredEvenP2) := by
  change Continuous (fun x ↦ (-1 : ℝ) * centeredEvenP2 x)
  unfold centeredEvenP2
  fun_prop

private theorem centeredEvenP0PlusP2_crossDifference_p1
    (t : ℝ) (_ht : t ∈ Icc (0 : ℝ) 2) :
    factorTwoCenteredCrossCorrelation centeredP1 centeredEvenP0PlusP2 t -
        factorTwoCenteredCrossCorrelation centeredEvenP0PlusP2 centeredP1 t =
      intrinsicAlternatingCorrelation intrinsicAlternatingQ01Plus21 t := by
  have h0 := factorTwoCenteredCrossDifference_p0_p1 t
  have h2 := factorTwoCenteredCrossDifference_p2_p1 t
  unfold centeredEvenP0PlusP2
  rw [factorTwoCenteredCrossCorrelation_add_right
      centeredP1 centeredEvenP0 centeredEvenP2
      (by unfold centeredP1; fun_prop)
      (by unfold centeredEvenP0; fun_prop)
      (by unfold centeredEvenP2; fun_prop),
    factorTwoCenteredCrossCorrelation_add_left
      centeredEvenP0 centeredEvenP2 centeredP1
      (by unfold centeredEvenP0; fun_prop)
      (by unfold centeredEvenP2; fun_prop)
      (by unfold centeredP1; fun_prop)]
  unfold intrinsicAlternatingCorrelation intrinsicAlternatingQ01Plus21
  linear_combination h0 + h2

private theorem centeredEvenP0MinusP2_crossDifference_p1
    (t : ℝ) (_ht : t ∈ Icc (0 : ℝ) 2) :
    factorTwoCenteredCrossCorrelation centeredP1 centeredEvenP0MinusP2 t -
        factorTwoCenteredCrossCorrelation centeredEvenP0MinusP2 centeredP1 t =
      intrinsicAlternatingCorrelation intrinsicAlternatingQ01Minus21 t := by
  have h0 := factorTwoCenteredCrossDifference_p0_p1 t
  have h2 := factorTwoCenteredCrossDifference_p2_p1 t
  unfold centeredEvenP0MinusP2
  rw [factorTwoCenteredCrossCorrelation_add_right
      centeredP1 centeredEvenP0 ((-1 : ℝ) • centeredEvenP2)
      (by unfold centeredP1; fun_prop)
      (by unfold centeredEvenP0; fun_prop)
      continuous_neg_centeredEvenP2,
    factorTwoCenteredCrossCorrelation_add_left
      centeredEvenP0 ((-1 : ℝ) • centeredEvenP2) centeredP1
      (by unfold centeredEvenP0; fun_prop)
      continuous_neg_centeredEvenP2
      (by unfold centeredP1; fun_prop),
    factorTwoCenteredCrossCorrelation_smul_right,
    factorTwoCenteredCrossCorrelation_smul_left]
  unfold intrinsicAlternatingCorrelation intrinsicAlternatingQ01Minus21
  linear_combination h0 - h2

private theorem centeredEvenP0PlusP2_crossDifference_p3
    (t : ℝ) (_ht : t ∈ Icc (0 : ℝ) 2) :
    factorTwoCenteredCrossCorrelation centeredP3 centeredEvenP0PlusP2 t -
        factorTwoCenteredCrossCorrelation centeredEvenP0PlusP2 centeredP3 t =
      intrinsicAlternatingCorrelation intrinsicAlternatingQ03Plus23 t := by
  have h0 := factorTwoCenteredCrossDifference_p0_p3 t
  have h2 := factorTwoCenteredCrossDifference_p2_p3 t
  unfold centeredEvenP0PlusP2
  rw [factorTwoCenteredCrossCorrelation_add_right
      centeredP3 centeredEvenP0 centeredEvenP2
      (by unfold centeredP3; fun_prop)
      (by unfold centeredEvenP0; fun_prop)
      (by unfold centeredEvenP2; fun_prop),
    factorTwoCenteredCrossCorrelation_add_left
      centeredEvenP0 centeredEvenP2 centeredP3
      (by unfold centeredEvenP0; fun_prop)
      (by unfold centeredEvenP2; fun_prop)
      (by unfold centeredP3; fun_prop)]
  unfold intrinsicAlternatingCorrelation intrinsicAlternatingQ03Plus23
  linear_combination h0 + h2

private theorem centeredEvenP0MinusP2_crossDifference_p3
    (t : ℝ) (_ht : t ∈ Icc (0 : ℝ) 2) :
    factorTwoCenteredCrossCorrelation centeredP3 centeredEvenP0MinusP2 t -
        factorTwoCenteredCrossCorrelation centeredEvenP0MinusP2 centeredP3 t =
      intrinsicAlternatingCorrelation intrinsicAlternatingQ03Minus23 t := by
  have h0 := factorTwoCenteredCrossDifference_p0_p3 t
  have h2 := factorTwoCenteredCrossDifference_p2_p3 t
  unfold centeredEvenP0MinusP2
  rw [factorTwoCenteredCrossCorrelation_add_right
      centeredP3 centeredEvenP0 ((-1 : ℝ) • centeredEvenP2)
      (by unfold centeredP3; fun_prop)
      (by unfold centeredEvenP0; fun_prop)
      continuous_neg_centeredEvenP2,
    factorTwoCenteredCrossCorrelation_add_left
      centeredEvenP0 ((-1 : ℝ) • centeredEvenP2) centeredP3
      (by unfold centeredEvenP0; fun_prop)
      continuous_neg_centeredEvenP2
      (by unfold centeredP3; fun_prop),
    factorTwoCenteredCrossCorrelation_smul_right,
    factorTwoCenteredCrossCorrelation_smul_left]
  unfold intrinsicAlternatingCorrelation intrinsicAlternatingQ03Minus23
  linear_combination h0 - h2

theorem intrinsicAlternating01_add_21_eq_structuralModel :
    factorTwoIntrinsicAlternating01 + factorTwoIntrinsicAlternating21 =
      intrinsicAlternatingRegularError intrinsicAlternatingQ01Plus21 +
        intrinsicAlternatingArchModel intrinsicAlternatingQ01Plus21 -
        (Real.log 3 / Real.sqrt 3) *
          intrinsicAlternatingCorrelation intrinsicAlternatingQ01Plus21
            (factorTwoPrimeShift / yoshidaEndpointA) := by
  calc
    factorTwoIntrinsicAlternating01 + factorTwoIntrinsicAlternating21 =
        factorTwoCenteredAlternatingCoupling centeredEvenP0PlusP2 centeredP1 := by
      unfold factorTwoIntrinsicAlternating01 factorTwoIntrinsicAlternating21
        centeredEvenP0PlusP2
      rw [factorTwoCenteredAlternatingCoupling_add_left
        centeredEvenP0 centeredEvenP2 centeredP1
        (by unfold centeredEvenP0; fun_prop)
        (by unfold centeredEvenP2; fun_prop)
        (by unfold centeredP1; fun_prop)]
    _ = _ := factorTwoCenteredAlternatingCoupling_eq_regularError_add_archModel
      centeredEvenP0PlusP2 centeredP1 intrinsicAlternatingQ01Plus21
      (by unfold intrinsicAlternatingQ01Plus21; fun_prop)
      centeredEvenP0PlusP2_crossDifference_p1

theorem intrinsicAlternating01_sub_21_eq_structuralModel :
    factorTwoIntrinsicAlternating01 - factorTwoIntrinsicAlternating21 =
      intrinsicAlternatingRegularError intrinsicAlternatingQ01Minus21 +
        intrinsicAlternatingArchModel intrinsicAlternatingQ01Minus21 -
        (Real.log 3 / Real.sqrt 3) *
          intrinsicAlternatingCorrelation intrinsicAlternatingQ01Minus21
            (factorTwoPrimeShift / yoshidaEndpointA) := by
  calc
    factorTwoIntrinsicAlternating01 - factorTwoIntrinsicAlternating21 =
        factorTwoCenteredAlternatingCoupling centeredEvenP0MinusP2 centeredP1 := by
      unfold factorTwoIntrinsicAlternating01 factorTwoIntrinsicAlternating21
        centeredEvenP0MinusP2
      rw [factorTwoCenteredAlternatingCoupling_add_left
        centeredEvenP0 ((-1 : ℝ) • centeredEvenP2) centeredP1
        (by unfold centeredEvenP0; fun_prop)
        continuous_neg_centeredEvenP2
        (by unfold centeredP1; fun_prop),
        factorTwoCenteredAlternatingCoupling_smul_left]
      ring
    _ = _ := factorTwoCenteredAlternatingCoupling_eq_regularError_add_archModel
      centeredEvenP0MinusP2 centeredP1 intrinsicAlternatingQ01Minus21
      (by unfold intrinsicAlternatingQ01Minus21; fun_prop)
      centeredEvenP0MinusP2_crossDifference_p1

theorem intrinsicAlternating03_add_23_eq_structuralModel :
    factorTwoIntrinsicAlternating03 + factorTwoIntrinsicAlternating23 =
      intrinsicAlternatingRegularError intrinsicAlternatingQ03Plus23 +
        intrinsicAlternatingArchModel intrinsicAlternatingQ03Plus23 -
        (Real.log 3 / Real.sqrt 3) *
          intrinsicAlternatingCorrelation intrinsicAlternatingQ03Plus23
            (factorTwoPrimeShift / yoshidaEndpointA) := by
  calc
    factorTwoIntrinsicAlternating03 + factorTwoIntrinsicAlternating23 =
        factorTwoCenteredAlternatingCoupling centeredEvenP0PlusP2 centeredP3 := by
      unfold factorTwoIntrinsicAlternating03 factorTwoIntrinsicAlternating23
        centeredEvenP0PlusP2
      rw [factorTwoCenteredAlternatingCoupling_add_left
        centeredEvenP0 centeredEvenP2 centeredP3
        (by unfold centeredEvenP0; fun_prop)
        (by unfold centeredEvenP2; fun_prop)
        (by unfold centeredP3; fun_prop)]
    _ = _ := factorTwoCenteredAlternatingCoupling_eq_regularError_add_archModel
      centeredEvenP0PlusP2 centeredP3 intrinsicAlternatingQ03Plus23
      (by unfold intrinsicAlternatingQ03Plus23; fun_prop)
      centeredEvenP0PlusP2_crossDifference_p3

theorem intrinsicAlternating03_sub_23_eq_structuralModel :
    factorTwoIntrinsicAlternating03 - factorTwoIntrinsicAlternating23 =
      intrinsicAlternatingRegularError intrinsicAlternatingQ03Minus23 +
        intrinsicAlternatingArchModel intrinsicAlternatingQ03Minus23 -
        (Real.log 3 / Real.sqrt 3) *
          intrinsicAlternatingCorrelation intrinsicAlternatingQ03Minus23
            (factorTwoPrimeShift / yoshidaEndpointA) := by
  calc
    factorTwoIntrinsicAlternating03 - factorTwoIntrinsicAlternating23 =
        factorTwoCenteredAlternatingCoupling centeredEvenP0MinusP2 centeredP3 := by
      unfold factorTwoIntrinsicAlternating03 factorTwoIntrinsicAlternating23
        centeredEvenP0MinusP2
      rw [factorTwoCenteredAlternatingCoupling_add_left
        centeredEvenP0 ((-1 : ℝ) • centeredEvenP2) centeredP3
        (by unfold centeredEvenP0; fun_prop)
        continuous_neg_centeredEvenP2
        (by unfold centeredP3; fun_prop),
        factorTwoCenteredAlternatingCoupling_smul_left]
      ring
    _ = _ := factorTwoCenteredAlternatingCoupling_eq_regularError_add_archModel
      centeredEvenP0MinusP2 centeredP3 intrinsicAlternatingQ03Minus23
      (by unfold intrinsicAlternatingQ03Minus23; fun_prop)
      centeredEvenP0MinusP2_crossDifference_p3

/-! ## Exact archimedean moments -/

private theorem integral_septic_local
    (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ l r : ℝ) :
    (∫ x : ℝ in l..r,
      a₀ * x ^ 0 + (a₁ * x ^ 1 + (a₂ * x ^ 2 +
        (a₃ * x ^ 3 + (a₄ * x ^ 4 + (a₅ * x ^ 5 +
          (a₆ * x ^ 6 + a₇ * x ^ 7))))))) =
      a₀ * (r - l) + a₁ * (r ^ 2 - l ^ 2) / 2 +
        a₂ * (r ^ 3 - l ^ 3) / 3 +
        a₃ * (r ^ 4 - l ^ 4) / 4 +
        a₄ * (r ^ 5 - l ^ 5) / 5 +
        a₅ * (r ^ 6 - l ^ 6) / 6 +
        a₆ * (r ^ 7 - l ^ 7) / 7 +
        a₇ * (r ^ 8 - l ^ 8) / 8 := by
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) l r)
    (Continuous.intervalIntegrable (by fun_prop) l r)]
  repeat rw [intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  ring

private theorem integral_inv_two_add_local :
    (∫ t : ℝ in 0..2, 1 / (2 + t)) = Real.log 2 := by
  let F : ℝ → ℝ := fun t ↦ Real.log (2 + t)
  have hderiv (t : ℝ) (ht : 2 + t ≠ 0) :
      HasDerivAt F (1 / (2 + t)) t := by
    have hadd : HasDerivAt (fun x : ℝ ↦ 2 + x) 1 t := by
      simpa using (hasDerivAt_const t 2).add (hasDerivAt_id t)
    simpa only [F, Function.comp_apply, one_div, mul_one] using
      (Real.hasDerivAt_log ht).comp t hadd
  have hcont : ContinuousOn (fun t : ℝ ↦ 1 / (2 + t))
      (uIcc (0 : ℝ) 2) := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 2 := by
      simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using ht
    have hne : 2 + t ≠ 0 := by linarith [ht'.1]
    exact (continuousAt_const.div
      (continuousAt_const.add continuousAt_id) hne).continuousWithinAt
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht ↦ hderiv t (by
      have ht' : t ∈ Icc (0 : ℝ) 2 := by
        simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using ht
      linarith [ht'.1])) hcont.intervalIntegrable
  rw [hint]
  dsimp only [F]
  norm_num
  rw [show Real.log 4 = 2 * Real.log 2 by
    rw [show (4 : ℝ) = 2 * 2 by norm_num,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
        (by norm_num : (2 : ℝ) ≠ 0)]
    ring]
  ring

private theorem intervalIntegrable_inv_two_add_local :
    IntervalIntegrable (fun t : ℝ ↦ 1 / (2 + t)) volume 0 2 := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 2 := by
    simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using ht
  have hne : 2 + t ≠ 0 := by linarith [ht'.1]
  exact (continuousAt_const.div
    (continuousAt_const.add continuousAt_id) hne).continuousWithinAt

theorem intrinsicAlternatingArchModel_q01Plus21 :
    intrinsicAlternatingArchModel intrinsicAlternatingQ01Plus21 =
      (17 / 15 : ℝ) := by
  have hint :
      intrinsicAlternatingArchModel intrinsicAlternatingQ01Plus21 =
        ∫ t : ℝ in 0..2,
          0 * t ^ 0 + (0 * t ^ 1 + (0 * t ^ 2 +
            ((7 / 20 : ℝ) * t ^ 3 + (0 * t ^ 4 +
              ((-1 / 40 : ℝ) * t ^ 5 +
                (0 * t ^ 6 + 0 * t ^ 7)))))) := by
    unfold intrinsicAlternatingArchModel intrinsicAlternatingCorrelation
      intrinsicAlternatingQ01Plus21
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] at ht
    have hden : 2 + t ≠ 0 := by linarith [ht.1]
    field_simp [hden]
    ring
  rw [hint, integral_septic_local]
  norm_num

theorem intrinsicAlternatingArchModel_q01Minus21 :
    intrinsicAlternatingArchModel intrinsicAlternatingQ01Minus21 =
      8 * Real.log 2 - (73 / 15 : ℝ) := by
  let p : ℝ → ℝ := fun t ↦
    (-4 : ℝ) * t ^ 0 + (2 * t ^ 1 + ((2 / 5 : ℝ) * t ^ 2 +
      ((-11 / 20 : ℝ) * t ^ 3 + (0 * t ^ 4 +
        ((1 / 40 : ℝ) * t ^ 5 + (0 * t ^ 6 + 0 * t ^ 7))))))
  have hint :
      intrinsicAlternatingArchModel intrinsicAlternatingQ01Minus21 =
        ∫ t : ℝ in 0..2, p t + 8 * (1 / (2 + t)) := by
    unfold intrinsicAlternatingArchModel intrinsicAlternatingCorrelation
      intrinsicAlternatingQ01Minus21
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] at ht
    have hden : 2 + t ≠ 0 := by linarith [ht.1]
    dsimp only [p]
    field_simp [hden]
    ring
  have hp : IntervalIntegrable p volume 0 2 := by
    exact (by
      dsimp only [p]
      fun_prop : Continuous p).intervalIntegrable 0 2
  rw [hint, intervalIntegral.integral_add hp
      (intervalIntegrable_inv_two_add_local.const_mul 8),
    intervalIntegral.integral_const_mul, integral_inv_two_add_local]
  change
    (∫ t : ℝ in 0..2,
      (-4 : ℝ) * t ^ 0 + (2 * t ^ 1 + ((2 / 5 : ℝ) * t ^ 2 +
        ((-11 / 20 : ℝ) * t ^ 3 + (0 * t ^ 4 +
          ((1 / 40 : ℝ) * t ^ 5 + (0 * t ^ 6 + 0 * t ^ 7))))))) +
        8 * Real.log 2 = 8 * Real.log 2 - 73 / 15
  rw [integral_septic_local]
  norm_num
  ring

theorem intrinsicAlternatingArchModel_q03Plus23 :
    intrinsicAlternatingArchModel intrinsicAlternatingQ03Plus23 =
      48 * Real.log 2 - 33 := by
  let p : ℝ → ℝ := fun t ↦
    (-24 : ℝ) * t ^ 0 + (12 * t ^ 1 + ((-23 / 5 : ℝ) * t ^ 2 +
      ((-3 / 20 : ℝ) * t ^ 3 + ((1 / 2 : ℝ) * t ^ 4 +
        ((1 / 10 : ℝ) * t ^ 5 + (0 * t ^ 6 +
          (-1 / 80 : ℝ) * t ^ 7))))))
  have hint :
      intrinsicAlternatingArchModel intrinsicAlternatingQ03Plus23 =
        ∫ t : ℝ in 0..2, p t + 48 * (1 / (2 + t)) := by
    unfold intrinsicAlternatingArchModel intrinsicAlternatingCorrelation
      intrinsicAlternatingQ03Plus23
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] at ht
    have hden : 2 + t ≠ 0 := by linarith [ht.1]
    dsimp only [p]
    field_simp [hden]
    ring
  have hp : IntervalIntegrable p volume 0 2 := by
    exact (by
      dsimp only [p]
      fun_prop : Continuous p).intervalIntegrable 0 2
  rw [hint, intervalIntegral.integral_add hp
      (intervalIntegrable_inv_two_add_local.const_mul 48),
    intervalIntegral.integral_const_mul, integral_inv_two_add_local]
  change
    (∫ t : ℝ in 0..2,
      (-24 : ℝ) * t ^ 0 + (12 * t ^ 1 + ((-23 / 5 : ℝ) * t ^ 2 +
        ((-3 / 20 : ℝ) * t ^ 3 + ((1 / 2 : ℝ) * t ^ 4 +
          ((1 / 10 : ℝ) * t ^ 5 + (0 * t ^ 6 +
            (-1 / 80 : ℝ) * t ^ 7))))))) +
        48 * Real.log 2 = 48 * Real.log 2 - 33
  rw [integral_septic_local]
  norm_num
  ring

theorem intrinsicAlternatingArchModel_q03Minus23 :
    intrinsicAlternatingArchModel intrinsicAlternatingQ03Minus23 =
      40 * Real.log 2 - (83 / 3 : ℝ) := by
  let p : ℝ → ℝ := fun t ↦
    (-20 : ℝ) * t ^ 0 + (10 * t ^ 1 + ((-5 : ℝ) * t ^ 2 +
      ((29 / 20 : ℝ) * t ^ 3 + ((1 / 2 : ℝ) * t ^ 4 +
        ((-7 / 20 : ℝ) * t ^ 5 + (0 * t ^ 6 +
          (1 / 80 : ℝ) * t ^ 7))))))
  have hint :
      intrinsicAlternatingArchModel intrinsicAlternatingQ03Minus23 =
        ∫ t : ℝ in 0..2, p t + 40 * (1 / (2 + t)) := by
    unfold intrinsicAlternatingArchModel intrinsicAlternatingCorrelation
      intrinsicAlternatingQ03Minus23
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] at ht
    have hden : 2 + t ≠ 0 := by linarith [ht.1]
    dsimp only [p]
    field_simp [hden]
    ring
  have hp : IntervalIntegrable p volume 0 2 := by
    exact (by
      dsimp only [p]
      fun_prop : Continuous p).intervalIntegrable 0 2
  rw [hint, intervalIntegral.integral_add hp
      (intervalIntegrable_inv_two_add_local.const_mul 40),
    intervalIntegral.integral_const_mul, integral_inv_two_add_local]
  change
    (∫ t : ℝ in 0..2,
      (-20 : ℝ) * t ^ 0 + (10 * t ^ 1 + ((-5 : ℝ) * t ^ 2 +
        ((29 / 20 : ℝ) * t ^ 3 + ((1 / 2 : ℝ) * t ^ 4 +
          ((-7 / 20 : ℝ) * t ^ 5 + (0 * t ^ 6 +
            (1 / 80 : ℝ) * t ^ 7))))))) +
        40 * Real.log 2 = 40 * Real.log 2 - 83 / 3
  rw [integral_septic_local]
  norm_num
  ring

/-! ## Coupled global error budgets -/

private theorem intrinsicAlternatingCorrelation_q01Plus21_nonneg
    {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
    0 ≤ intrinsicAlternatingCorrelation intrinsicAlternatingQ01Plus21 t := by
  unfold intrinsicAlternatingCorrelation intrinsicAlternatingQ01Plus21
  have hfour : 0 ≤ 4 - t ^ 2 := by nlinarith [sq_nonneg (2 - t)]
  rw [show t * (2 - t) * ((1 / 2 : ℝ) * t + (1 / 4 : ℝ) * t ^ 2) =
      (1 / 4 : ℝ) * t ^ 2 * (4 - t ^ 2) by ring]
  positivity

private theorem intrinsicAlternatingCorrelation_q01Minus21_nonneg
    {t : ℝ} (ht0 : 0 ≤ t) (_ht2 : t ≤ 2) :
    0 ≤ intrinsicAlternatingCorrelation intrinsicAlternatingQ01Minus21 t := by
  unfold intrinsicAlternatingCorrelation intrinsicAlternatingQ01Minus21
  rw [show t * (2 - t) *
      (2 - (1 / 2 : ℝ) * t - (1 / 4 : ℝ) * t ^ 2) =
        t * (2 - t) ^ 2 * (1 + t / 4) by ring]
  positivity

private theorem integral_abs_intrinsicAlternatingCorrelation_q01Plus21 :
    (∫ t : ℝ in 0..2,
      |intrinsicAlternatingCorrelation intrinsicAlternatingQ01Plus21 t|) =
      (16 / 15 : ℝ) := by
  have hcongr :
      (∫ t : ℝ in 0..2,
        |intrinsicAlternatingCorrelation intrinsicAlternatingQ01Plus21 t|) =
        ∫ t : ℝ in 0..2,
          0 * t ^ 0 + (0 * t ^ 1 + (1 * t ^ 2 +
            (0 * t ^ 3 + ((-1 / 4 : ℝ) * t ^ 4 +
              (0 * t ^ 5 + (0 * t ^ 6 + 0 * t ^ 7)))))) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] at ht
    change |intrinsicAlternatingCorrelation
        intrinsicAlternatingQ01Plus21 t| = _
    rw [abs_of_nonneg
      (intrinsicAlternatingCorrelation_q01Plus21_nonneg ht.1 ht.2)]
    unfold intrinsicAlternatingCorrelation intrinsicAlternatingQ01Plus21
    ring
  rw [hcongr, integral_septic_local]
  norm_num

private theorem integral_abs_intrinsicAlternatingCorrelation_q01Minus21 :
    (∫ t : ℝ in 0..2,
      |intrinsicAlternatingCorrelation intrinsicAlternatingQ01Minus21 t|) =
      (8 / 5 : ℝ) := by
  have hcongr :
      (∫ t : ℝ in 0..2,
        |intrinsicAlternatingCorrelation intrinsicAlternatingQ01Minus21 t|) =
        ∫ t : ℝ in 0..2,
          0 * t ^ 0 + (4 * t ^ 1 + ((-3 : ℝ) * t ^ 2 +
            (0 * t ^ 3 + ((1 / 4 : ℝ) * t ^ 4 +
              (0 * t ^ 5 + (0 * t ^ 6 + 0 * t ^ 7)))))) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] at ht
    change |intrinsicAlternatingCorrelation
        intrinsicAlternatingQ01Minus21 t| = _
    rw [abs_of_nonneg
      (intrinsicAlternatingCorrelation_q01Minus21_nonneg ht.1 ht.2)]
    unfold intrinsicAlternatingCorrelation intrinsicAlternatingQ01Minus21
    ring
  rw [hcongr, integral_septic_local]
  norm_num

private theorem abs_intrinsicAlternatingQ03Plus23_le_two
    {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
    |intrinsicAlternatingQ03Plus23 t| ≤ 2 := by
  let x : ℝ := t / 2
  have hx0 : 0 ≤ x := by dsimp only [x]; linarith
  have hx1 : 0 ≤ 1 - x := by dsimp only [x]; linarith
  have hlower : -2 ≤ intrinsicAlternatingQ03Plus23 t := by
    have hdecomp : intrinsicAlternatingQ03Plus23 t + 2 =
        4 * (1 - x) ^ 4 + 9 * x * (1 - x) ^ 3 +
          6 * x ^ 2 * (1 - x) ^ 2 +
          3 * x ^ 3 * (1 - x) + 4 * x ^ 4 := by
      dsimp only [x]
      unfold intrinsicAlternatingQ03Plus23
      ring
    have hsum : 0 ≤
        4 * (1 - x) ^ 4 + 9 * x * (1 - x) ^ 3 +
          6 * x ^ 2 * (1 - x) ^ 2 +
          3 * x ^ 3 * (1 - x) + 4 * x ^ 4 := by positivity
    linarith [hdecomp]
  have hupper : intrinsicAlternatingQ03Plus23 t ≤ 2 := by
    have hdecomp : 2 - intrinsicAlternatingQ03Plus23 t =
        t * (2 - t) * (t ^ 2 / 8 + t / 2 + 7 / 4) := by
      unfold intrinsicAlternatingQ03Plus23
      ring
    have hthird : 0 ≤ t ^ 2 / 8 + t / 2 + 7 / 4 := by
      nlinarith [sq_nonneg t]
    have hnonneg : 0 ≤
        t * (2 - t) * (t ^ 2 / 8 + t / 2 + 7 / 4) :=
      mul_nonneg (mul_nonneg ht0 (sub_nonneg.mpr ht2)) hthird
    linarith [hdecomp]
  exact (abs_le).2 ⟨hlower, hupper⟩

private theorem abs_intrinsicAlternatingQ03Minus23_le_one
    {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
    |intrinsicAlternatingQ03Minus23 t| ≤ 1 := by
  let x : ℝ := t / 2
  have hx0 : 0 ≤ x := by dsimp only [x]; linarith
  have hx1 : 0 ≤ 1 - x := by dsimp only [x]; linarith
  have hlower : -1 ≤ intrinsicAlternatingQ03Minus23 t := by
    have hdecomp : intrinsicAlternatingQ03Minus23 t + 1 =
        (1 - x) ^ 4 + x * (1 - x) ^ 3 +
          4 * x ^ 2 * (1 - x) ^ 2 +
          7 * x ^ 3 * (1 - x) + x ^ 4 := by
      dsimp only [x]
      unfold intrinsicAlternatingQ03Minus23
      ring
    have hsum : 0 ≤
        (1 - x) ^ 4 + x * (1 - x) ^ 3 +
          4 * x ^ 2 * (1 - x) ^ 2 +
          7 * x ^ 3 * (1 - x) + x ^ 4 := by positivity
    linarith [hdecomp]
  have hupper : intrinsicAlternatingQ03Minus23 t ≤ 1 := by
    have hdecomp : 1 - intrinsicAlternatingQ03Minus23 t =
        (1 - x) ^ 4 + 7 * x * (1 - x) ^ 3 +
          8 * x ^ 2 * (1 - x) ^ 2 +
          x ^ 3 * (1 - x) + x ^ 4 := by
      dsimp only [x]
      unfold intrinsicAlternatingQ03Minus23
      ring
    have hsum : 0 ≤
        (1 - x) ^ 4 + 7 * x * (1 - x) ^ 3 +
          8 * x ^ 2 * (1 - x) ^ 2 +
          x ^ 3 * (1 - x) + x ^ 4 := by positivity
    linarith [hdecomp]
  exact (abs_le).2 ⟨hlower, hupper⟩

private theorem integral_abs_intrinsicAlternatingCorrelation_le_of_abs_q_le
    (q : ℝ → ℝ) (hq : Continuous q) (M : ℝ)
    (hbound : ∀ t, 0 ≤ t → t ≤ 2 → |q t| ≤ M) :
    (∫ t : ℝ in 0..2, |intrinsicAlternatingCorrelation q t|) ≤
      M * (4 / 3 : ℝ) := by
  have hleft : IntervalIntegrable
      (fun t : ℝ ↦ |intrinsicAlternatingCorrelation q t|) volume 0 2 := by
    apply Continuous.intervalIntegrable
    unfold intrinsicAlternatingCorrelation
    fun_prop
  have hright : IntervalIntegrable
      (fun t : ℝ ↦ M * (t * (2 - t))) volume 0 2 := by
    exact (by fun_prop : Continuous
      (fun t : ℝ ↦ M * (t * (2 - t)))).intervalIntegrable 0 2
  have hmono :
      (∫ t : ℝ in 0..2, |intrinsicAlternatingCorrelation q t|) ≤
        ∫ t : ℝ in 0..2, M * (t * (2 - t)) := by
    apply intervalIntegral.integral_mono_on (by norm_num) hleft hright
    intro t ht
    unfold intrinsicAlternatingCorrelation
    rw [abs_mul, abs_mul, abs_of_nonneg ht.1,
      abs_of_nonneg (sub_nonneg.mpr ht.2)]
    have h := mul_le_mul_of_nonneg_left (hbound t ht.1 ht.2)
      (mul_nonneg ht.1 (sub_nonneg.mpr ht.2))
    nlinarith
  calc
    (∫ t : ℝ in 0..2, |intrinsicAlternatingCorrelation q t|) ≤
        ∫ t : ℝ in 0..2, M * (t * (2 - t)) := hmono
    _ = M * (4 / 3 : ℝ) := by
      rw [show (fun t : ℝ ↦ M * (t * (2 - t))) = fun t ↦
          0 * t ^ 0 + ((2 * M) * t ^ 1 + ((-M) * t ^ 2 +
            (0 * t ^ 3 + (0 * t ^ 4 +
              (0 * t ^ 5 + (0 * t ^ 6 + 0 * t ^ 7)))))) by
        funext t; ring,
        integral_septic_local]
      ring

theorem abs_intrinsicAlternatingRegularError_q01Plus21_le :
    |intrinsicAlternatingRegularError intrinsicAlternatingQ01Plus21| ≤
      (2 / 1875 : ℝ) := by
  have h := abs_intrinsicAlternatingRegularError_le
    intrinsicAlternatingQ01Plus21
    (by unfold intrinsicAlternatingQ01Plus21; fun_prop)
  rw [integral_abs_intrinsicAlternatingCorrelation_q01Plus21] at h
  norm_num at h ⊢
  exact h

theorem abs_intrinsicAlternatingRegularError_q01Minus21_le :
    |intrinsicAlternatingRegularError intrinsicAlternatingQ01Minus21| ≤
      (1 / 625 : ℝ) := by
  have h := abs_intrinsicAlternatingRegularError_le
    intrinsicAlternatingQ01Minus21
    (by unfold intrinsicAlternatingQ01Minus21; fun_prop)
  rw [integral_abs_intrinsicAlternatingCorrelation_q01Minus21] at h
  norm_num at h ⊢
  exact h

theorem abs_intrinsicAlternatingRegularError_q03Plus23_le :
    |intrinsicAlternatingRegularError intrinsicAlternatingQ03Plus23| ≤
      (1 / 375 : ℝ) := by
  have hL1 := integral_abs_intrinsicAlternatingCorrelation_le_of_abs_q_le
    intrinsicAlternatingQ03Plus23
    (by unfold intrinsicAlternatingQ03Plus23; fun_prop) 2
    (fun _ ht0 ht2 ↦ abs_intrinsicAlternatingQ03Plus23_le_two ht0 ht2)
  have herr := abs_intrinsicAlternatingRegularError_le
    intrinsicAlternatingQ03Plus23
    (by unfold intrinsicAlternatingQ03Plus23; fun_prop)
  norm_num at hL1 ⊢
  nlinarith

theorem abs_intrinsicAlternatingRegularError_q03Minus23_le :
    |intrinsicAlternatingRegularError intrinsicAlternatingQ03Minus23| ≤
      (1 / 750 : ℝ) := by
  have hL1 := integral_abs_intrinsicAlternatingCorrelation_le_of_abs_q_le
    intrinsicAlternatingQ03Minus23
    (by unfold intrinsicAlternatingQ03Minus23; fun_prop) 1
    (fun _ ht0 ht2 ↦ abs_intrinsicAlternatingQ03Minus23_le_one ht0 ht2)
  have herr := abs_intrinsicAlternatingRegularError_le
    intrinsicAlternatingQ03Minus23
    (by unfold intrinsicAlternatingQ03Minus23; fun_prop)
  norm_num at hL1 ⊢
  nlinarith

/-! ## The retained-prime values -/

theorem intrinsicAlternatingPrimeCorrelation_bounds :
    (9 / 10 : ℝ) <
        intrinsicAlternatingCorrelation intrinsicAlternatingQ01Plus21
          (factorTwoPrimeShift / yoshidaEndpointA) ∧
      intrinsicAlternatingCorrelation intrinsicAlternatingQ01Plus21
          (factorTwoPrimeShift / yoshidaEndpointA) < (901 / 1000 : ℝ) ∧
    (26 / 25 : ℝ) <
        intrinsicAlternatingCorrelation intrinsicAlternatingQ01Minus21
          (factorTwoPrimeShift / yoshidaEndpointA) ∧
      intrinsicAlternatingCorrelation intrinsicAlternatingQ01Minus21
          (factorTwoPrimeShift / yoshidaEndpointA) < (1043 / 1000 : ℝ) ∧
    (-423 / 1000 : ℝ) <
        intrinsicAlternatingCorrelation intrinsicAlternatingQ03Plus23
          (factorTwoPrimeShift / yoshidaEndpointA) ∧
      intrinsicAlternatingCorrelation intrinsicAlternatingQ03Plus23
          (factorTwoPrimeShift / yoshidaEndpointA) < (-21 / 50 : ℝ) ∧
    (1 / 200 : ℝ) <
        intrinsicAlternatingCorrelation intrinsicAlternatingQ03Minus23
          (factorTwoPrimeShift / yoshidaEndpointA) ∧
      intrinsicAlternatingCorrelation intrinsicAlternatingQ03Minus23
          (factorTwoPrimeShift / yoshidaEndpointA) < (3 / 500 : ℝ) := by
  let t : ℝ := factorTwoPrimeShift / yoshidaEndpointA
  let L : ℝ := 11699 / 10000
  let U : ℝ := 117 / 100
  have ht := factorTwoPrimeRatio_kernel_bounds
  have hL : L ≤ t := by dsimp only [L, t]; exact ht.1.le
  have hU : t ≤ U := by dsimp only [U, t]; exact ht.2.le
  have hL0 : 0 ≤ L := by norm_num [L]
  have ht0 : 0 ≤ t := hL0.trans hL
  have hLn (n : ℕ) : L ^ n ≤ t ^ n :=
    pow_le_pow_left₀ hL0 hL n
  have hUn (n : ℕ) : t ^ n ≤ U ^ n :=
    pow_le_pow_left₀ ht0 hU n
  have hp01Lower : (9 / 10 : ℝ) < t ^ 2 - t ^ 4 / 4 := by
    have h2 := hLn 2
    have h4 := hUn 4
    norm_num [L, U] at h2 h4 ⊢
    nlinarith
  have hp01Upper : t ^ 2 - t ^ 4 / 4 < (901 / 1000 : ℝ) := by
    have h2 := hUn 2
    have h4 := hLn 4
    norm_num [L, U] at h2 h4 ⊢
    nlinarith
  have hm01Lower :
      (26 / 25 : ℝ) < 4 * t - 3 * t ^ 2 + t ^ 4 / 4 := by
    have h2 := hUn 2
    have h4 := hLn 4
    norm_num [L, U] at hL h2 h4 ⊢
    nlinarith
  have hm01Upper :
      4 * t - 3 * t ^ 2 + t ^ 4 / 4 < (1043 / 1000 : ℝ) := by
    have h2 := hLn 2
    have h4 := hUn 4
    norm_num [L, U] at hU h2 h4 ⊢
    nlinarith
  have hp03Lower :
      (-423 / 1000 : ℝ) <
        4 * t - 9 * t ^ 2 + 5 * t ^ 3 - t ^ 4 / 4 - t ^ 6 / 8 := by
    have h2 := hUn 2
    have h3 := hLn 3
    have h4 := hUn 4
    have h6 := hUn 6
    norm_num [L, U] at hL h2 h3 h4 h6 ⊢
    nlinarith
  have hp03Upper :
      4 * t - 9 * t ^ 2 + 5 * t ^ 3 - t ^ 4 / 4 - t ^ 6 / 8 <
        (-21 / 50 : ℝ) := by
    have h2 := hLn 2
    have h3 := hUn 3
    have h4 := hLn 4
    have h6 := hLn 6
    norm_num [L, U] at hU h2 h3 h4 h6 ⊢
    nlinarith
  have hm03Lower :
      (1 / 200 : ℝ) <
        -3 * t ^ 2 + 5 * t ^ 3 - (9 / 4 : ℝ) * t ^ 4 + t ^ 6 / 8 := by
    have h2 := hUn 2
    have h3 := hLn 3
    have h4 := hUn 4
    have h6 := hLn 6
    norm_num [L, U] at h2 h3 h4 h6 ⊢
    nlinarith
  have hm03Upper :
      -3 * t ^ 2 + 5 * t ^ 3 - (9 / 4 : ℝ) * t ^ 4 + t ^ 6 / 8 <
        (3 / 500 : ℝ) := by
    have h2 := hLn 2
    have h3 := hUn 3
    have h4 := hLn 4
    have h6 := hUn 6
    norm_num [L, U] at h2 h3 h4 h6 ⊢
    nlinarith
  dsimp only [t] at hp01Lower hp01Upper hm01Lower hm01Upper
  dsimp only [t] at hp03Lower hp03Upper hm03Lower hm03Upper
  unfold intrinsicAlternatingCorrelation intrinsicAlternatingQ01Plus21
    intrinsicAlternatingQ01Minus21 intrinsicAlternatingQ03Plus23
    intrinsicAlternatingQ03Minus23
  constructor
  · (convert hp01Lower using 1; ring)
  constructor
  · (convert hp01Upper using 1; ring)
  constructor
  · (convert hm01Lower using 1; ring)
  constructor
  · (convert hm01Upper using 1; ring)
  constructor
  · (convert hp03Lower using 1; ring)
  constructor
  · (convert hp03Upper using 1; ring)
  constructor
  · (convert hm03Lower using 1; ring)
  · (convert hm03Upper using 1; ring)

theorem intrinsicAlternatingPrimeProduct_bounds :
    (57 / 100 : ℝ) <
        (Real.log 3 / Real.sqrt 3) *
          intrinsicAlternatingCorrelation intrinsicAlternatingQ01Plus21
            (factorTwoPrimeShift / yoshidaEndpointA) ∧
      (Real.log 3 / Real.sqrt 3) *
          intrinsicAlternatingCorrelation intrinsicAlternatingQ01Plus21
            (factorTwoPrimeShift / yoshidaEndpointA) < (143 / 250 : ℝ) ∧
    (659 / 1000 : ℝ) <
        (Real.log 3 / Real.sqrt 3) *
          intrinsicAlternatingCorrelation intrinsicAlternatingQ01Minus21
            (factorTwoPrimeShift / yoshidaEndpointA) ∧
      (Real.log 3 / Real.sqrt 3) *
          intrinsicAlternatingCorrelation intrinsicAlternatingQ01Minus21
            (factorTwoPrimeShift / yoshidaEndpointA) < (331 / 500 : ℝ) ∧
    (-269 / 1000 : ℝ) <
        (Real.log 3 / Real.sqrt 3) *
          intrinsicAlternatingCorrelation intrinsicAlternatingQ03Plus23
            (factorTwoPrimeShift / yoshidaEndpointA) ∧
      (Real.log 3 / Real.sqrt 3) *
          intrinsicAlternatingCorrelation intrinsicAlternatingQ03Plus23
            (factorTwoPrimeShift / yoshidaEndpointA) < (-133 / 500 : ℝ) ∧
    (3 / 1000 : ℝ) <
        (Real.log 3 / Real.sqrt 3) *
          intrinsicAlternatingCorrelation intrinsicAlternatingQ03Minus23
            (factorTwoPrimeShift / yoshidaEndpointA) ∧
      (Real.log 3 / Real.sqrt 3) *
          intrinsicAlternatingCorrelation intrinsicAlternatingQ03Minus23
            (factorTwoPrimeShift / yoshidaEndpointA) < (1 / 250 : ℝ) := by
  let β : ℝ := Real.log 3 / Real.sqrt 3
  let dP01 : ℝ := intrinsicAlternatingCorrelation
    intrinsicAlternatingQ01Plus21 (factorTwoPrimeShift / yoshidaEndpointA)
  let dM01 : ℝ := intrinsicAlternatingCorrelation
    intrinsicAlternatingQ01Minus21 (factorTwoPrimeShift / yoshidaEndpointA)
  let dP03 : ℝ := intrinsicAlternatingCorrelation
    intrinsicAlternatingQ03Plus23 (factorTwoPrimeShift / yoshidaEndpointA)
  let dM03 : ℝ := intrinsicAlternatingCorrelation
    intrinsicAlternatingQ03Minus23 (factorTwoPrimeShift / yoshidaEndpointA)
  have hb := log_three_div_sqrt_three_kernel_bounds
  have hβpos : 0 < β := by dsimp only [β]; positivity
  rcases intrinsicAlternatingPrimeCorrelation_bounds with
    ⟨hdP01L, hdP01U, hdM01L, hdM01U, hdP03L, hdP03U, hdM03L, hdM03U⟩
  have hdP01pos : 0 < dP01 := by dsimp only [dP01]; linarith
  have hdM01pos : 0 < dM01 := by dsimp only [dM01]; linarith
  have hdP03neg : dP03 < 0 := by dsimp only [dP03]; linarith
  have hdM03pos : 0 < dM03 := by dsimp only [dM03]; linarith
  have hp01L : (57 / 100 : ℝ) < β * dP01 := by
    calc
      (57 / 100 : ℝ) < (63427 / 100000 : ℝ) * (9 / 10 : ℝ) := by
        norm_num
      _ < β * (9 / 10 : ℝ) := by
        apply mul_lt_mul_of_pos_right
        · simpa only [β] using hb.1
        · norm_num
      _ < β * dP01 := by
        apply mul_lt_mul_of_pos_left
        · simpa only [dP01] using hdP01L
        · exact hβpos
  have hp01U : β * dP01 < (143 / 250 : ℝ) := by
    calc
      β * dP01 < (6343 / 10000 : ℝ) * dP01 := by
        apply mul_lt_mul_of_pos_right
        · simpa only [β] using hb.2
        · exact hdP01pos
      _ < (6343 / 10000 : ℝ) * (901 / 1000 : ℝ) := by
        apply mul_lt_mul_of_pos_left
        · simpa only [dP01] using hdP01U
        · norm_num
      _ < (143 / 250 : ℝ) := by norm_num
  have hm01L : (659 / 1000 : ℝ) < β * dM01 := by
    calc
      (659 / 1000 : ℝ) < (63427 / 100000 : ℝ) * (26 / 25 : ℝ) := by
        norm_num
      _ < β * (26 / 25 : ℝ) := by
        apply mul_lt_mul_of_pos_right
        · simpa only [β] using hb.1
        · norm_num
      _ < β * dM01 := by
        apply mul_lt_mul_of_pos_left
        · simpa only [dM01] using hdM01L
        · exact hβpos
  have hm01U : β * dM01 < (331 / 500 : ℝ) := by
    calc
      β * dM01 < (6343 / 10000 : ℝ) * dM01 := by
        apply mul_lt_mul_of_pos_right
        · simpa only [β] using hb.2
        · exact hdM01pos
      _ < (6343 / 10000 : ℝ) * (1043 / 1000 : ℝ) := by
        apply mul_lt_mul_of_pos_left
        · simpa only [dM01] using hdM01U
        · norm_num
      _ < (331 / 500 : ℝ) := by norm_num
  have hp03L : (-269 / 1000 : ℝ) < β * dP03 := by
    calc
      (-269 / 1000 : ℝ) <
          (6343 / 10000 : ℝ) * (-423 / 1000 : ℝ) := by norm_num
      _ < β * (-423 / 1000 : ℝ) := by
        apply mul_lt_mul_of_neg_right
        · simpa only [β] using hb.2
        · norm_num
      _ < β * dP03 := by
        apply mul_lt_mul_of_pos_left
        · simpa only [dP03] using hdP03L
        · exact hβpos
  have hp03U : β * dP03 < (-133 / 500 : ℝ) := by
    calc
      β * dP03 < β * (-21 / 50 : ℝ) := by
        apply mul_lt_mul_of_pos_left
        · simpa only [dP03] using hdP03U
        · exact hβpos
      _ < (63427 / 100000 : ℝ) * (-21 / 50 : ℝ) := by
        apply mul_lt_mul_of_neg_right
        · simpa only [β] using hb.1
        · norm_num
      _ < (-133 / 500 : ℝ) := by norm_num
  have hm03L : (3 / 1000 : ℝ) < β * dM03 := by
    calc
      (3 / 1000 : ℝ) < (63427 / 100000 : ℝ) * (1 / 200 : ℝ) := by
        norm_num
      _ < β * (1 / 200 : ℝ) := by
        apply mul_lt_mul_of_pos_right
        · simpa only [β] using hb.1
        · norm_num
      _ < β * dM03 := by
        apply mul_lt_mul_of_pos_left
        · simpa only [dM03] using hdM03L
        · exact hβpos
  have hm03U : β * dM03 < (1 / 250 : ℝ) := by
    calc
      β * dM03 < (6343 / 10000 : ℝ) * dM03 := by
        apply mul_lt_mul_of_pos_right
        · simpa only [β] using hb.2
        · exact hdM03pos
      _ < (6343 / 10000 : ℝ) * (3 / 500 : ℝ) := by
        apply mul_lt_mul_of_pos_left
        · simpa only [dM03] using hdM03U
        · norm_num
      _ < (1 / 250 : ℝ) := by norm_num
  simpa only [β, dP01, dM01, dP03, dM03] using
    ⟨hp01L, hp01U, hm01L, hm01U, hp03L, hp03U, hm03L, hm03U⟩

theorem intrinsicAlternatingArchModel_rational_bounds :
    (6785 / 10000 : ℝ) <
        intrinsicAlternatingArchModel intrinsicAlternatingQ01Minus21 ∧
      intrinsicAlternatingArchModel intrinsicAlternatingQ01Minus21 <
        (3393 / 5000 : ℝ) ∧
    (271 / 1000 : ℝ) <
        intrinsicAlternatingArchModel intrinsicAlternatingQ03Plus23 ∧
      intrinsicAlternatingArchModel intrinsicAlternatingQ03Plus23 <
        (34 / 125 : ℝ) ∧
    (59 / 1000 : ℝ) <
        intrinsicAlternatingArchModel intrinsicAlternatingQ03Minus23 ∧
      intrinsicAlternatingArchModel intrinsicAlternatingQ03Minus23 <
        (3 / 50 : ℝ) := by
  have hlog := strict_log_two_fine_bounds
  rw [intrinsicAlternatingArchModel_q01Minus21,
    intrinsicAlternatingArchModel_q03Plus23,
    intrinsicAlternatingArchModel_q03Minus23]
  constructor
  · nlinarith [hlog.1]
  constructor
  · nlinarith [hlog.2]
  constructor
  · nlinarith [hlog.1]
  constructor
  · nlinarith [hlog.2]
  constructor
  · nlinarith [hlog.1]
  · nlinarith [hlog.2]

/-! ## Coupled rational bounds for the intrinsic alternating block -/

theorem intrinsicAlternating01_add_21_bounds :
    (14 / 25 : ℝ) <
        factorTwoIntrinsicAlternating01 + factorTwoIntrinsicAlternating21 ∧
      factorTwoIntrinsicAlternating01 + factorTwoIntrinsicAlternating21 <
        (113 / 200 : ℝ) := by
  have heq := intrinsicAlternating01_add_21_eq_structuralModel
  rw [intrinsicAlternatingArchModel_q01Plus21] at heq
  have herr := abs_intrinsicAlternatingRegularError_q01Plus21_le
  rw [abs_le] at herr
  rcases intrinsicAlternatingPrimeProduct_bounds with
    ⟨hpL, hpU, _hmL, _hmU, _hp03L, _hp03U, _hm03L, _hm03U⟩
  constructor <;> nlinarith

theorem intrinsicAlternating01_sub_21_bounds :
    (7 / 500 : ℝ) <
        factorTwoIntrinsicAlternating01 - factorTwoIntrinsicAlternating21 ∧
      factorTwoIntrinsicAlternating01 - factorTwoIntrinsicAlternating21 <
        (11 / 500 : ℝ) := by
  have heq := intrinsicAlternating01_sub_21_eq_structuralModel
  have herr := abs_intrinsicAlternatingRegularError_q01Minus21_le
  rw [abs_le] at herr
  rcases intrinsicAlternatingPrimeProduct_bounds with
    ⟨_hpL, _hpU, hmL, hmU, _hp03L, _hp03U, _hm03L, _hm03U⟩
  rcases intrinsicAlternatingArchModel_rational_bounds with
    ⟨haL, haU, _ha03pL, _ha03pU, _ha03mL, _ha03mU⟩
  constructor <;> nlinarith

theorem intrinsicAlternating03_add_23_bounds :
    (267 / 500 : ℝ) <
        factorTwoIntrinsicAlternating03 + factorTwoIntrinsicAlternating23 ∧
      factorTwoIntrinsicAlternating03 + factorTwoIntrinsicAlternating23 <
        (109 / 200 : ℝ) := by
  have heq := intrinsicAlternating03_add_23_eq_structuralModel
  have herr := abs_intrinsicAlternatingRegularError_q03Plus23_le
  rw [abs_le] at herr
  rcases intrinsicAlternatingPrimeProduct_bounds with
    ⟨_hpL, _hpU, _hmL, _hmU, hp03L, hp03U, _hm03L, _hm03U⟩
  rcases intrinsicAlternatingArchModel_rational_bounds with
    ⟨_haL, _haU, ha03pL, ha03pU, _ha03mL, _ha03mU⟩
  constructor <;> nlinarith

theorem intrinsicAlternating03_sub_23_bounds :
    (53 / 1000 : ℝ) <
        factorTwoIntrinsicAlternating03 - factorTwoIntrinsicAlternating23 ∧
      factorTwoIntrinsicAlternating03 - factorTwoIntrinsicAlternating23 <
        (3 / 50 : ℝ) := by
  have heq := intrinsicAlternating03_sub_23_eq_structuralModel
  have herr := abs_intrinsicAlternatingRegularError_q03Minus23_le
  rw [abs_le] at herr
  rcases intrinsicAlternatingPrimeProduct_bounds with
    ⟨_hpL, _hpU, _hmL, _hmU, _hp03L, _hp03U, hm03L, hm03U⟩
  rcases intrinsicAlternatingArchModel_rational_bounds with
    ⟨_haL, _haU, _ha03pL, _ha03pU, ha03mL, ha03mU⟩
  constructor <;> nlinarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowAlternatingKernelStructural

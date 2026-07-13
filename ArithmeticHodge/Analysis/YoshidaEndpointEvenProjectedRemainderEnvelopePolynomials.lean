import ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedRemainderEnvelopeKernel
import ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedRemainderMoments
import ArithmeticHodge.Analysis.YoshidaEndpointEvenLowHyperbolic
import ArithmeticHodge.Analysis.YoshidaEndpointEvenLowRegular

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedRemainderEnvelopePolynomials

open YoshidaEndpointEvenProjectedDualIdentity
open YoshidaEndpointEvenProjectedRemainderEnvelopeKernel
open YoshidaEndpointEvenProjectedRemainderMoments
open YoshidaEndpointEvenConstantCross
open YoshidaEndpointEvenLowHyperbolic
open YoshidaEndpointEvenLowRegular
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointHyperbolicBound
open YoshidaRegularKernelBound
open YoshidaConstantBounds

noncomputable section

/-- Integral-defined degree-six approximation to the regular representer. -/
def yoshidaEndpointEvenRegularRepresenterPolynomial6
    (p : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y : ℝ in -1..1,
    yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * |x - y|) * p y

/-- Smooth part of the projected constant representer after replacing both
analytic factors by their degree-six envelopes. -/
def fixedProjectedSmoothRemainderPolynomial6_0 (x : ℝ) : ℝ :=
  -yoshidaEndpointA *
      yoshidaEndpointEvenRegularRepresenterPolynomial6 centeredEvenP0 x +
    2 * yoshidaEndpointA * yoshidaEndpointCoshMoment centeredEvenP0 *
      yoshidaEndpointCoshPolynomial6 x

/-- Smooth part of the projected degree-two representer after replacement. -/
def fixedProjectedSmoothRemainderPolynomial6_2 (x : ℝ) : ℝ :=
  -yoshidaEndpointA *
      yoshidaEndpointEvenRegularRepresenterPolynomial6 centeredEvenP2 x +
    2 * yoshidaEndpointA * yoshidaEndpointCoshMoment centeredEvenP2 *
      yoshidaEndpointCoshPolynomial6 x

/-- Degree-six model of the shifted constant-basis remainder. -/
def fixedProjectedShiftedRemainderPolynomial6_0 (x : ℝ) : ℝ :=
  fixedProjectedSmoothRemainderPolynomial6_0 x -
    (883 / 480 : ℝ) - (35 / 32 : ℝ) * x ^ 2

/-- Degree-eight-in-`x` model of the shifted degree-two-basis remainder. -/
def fixedProjectedShiftedRemainderPolynomial6_2 (x : ℝ) : ℝ :=
  fixedProjectedSmoothRemainderPolynomial6_2 x +
    (107 / 240 : ℝ) - (71 / 40 : ℝ) * x ^ 2

private theorem intervalIntegrable_regularRepresenterPolynomial6
    (p : ℝ → ℝ) (hp : Continuous p) (x : ℝ) :
    IntervalIntegrable
      (fun y ↦ yoshidaRegularKernelPolynomial6
          (yoshidaEndpointA * |x - y|) * p y) volume (-1) 1 := by
  apply Continuous.intervalIntegrable
  unfold yoshidaRegularKernelPolynomial6
  fun_prop

private theorem intervalIntegrable_regularRepresenter
    (p : ℝ → ℝ) (hp : Continuous p) (x : ℝ)
    (hx : x ∈ Icc (-1) 1) :
    IntervalIntegrable
      (fun y ↦ yoshidaRegularKernel
          (yoshidaEndpointA * |x - y|) * p y) volume (-1) 1 := by
  let I : Set ℝ := Icc (-1) 1
  let μ : Measure ℝ := volume.restrict I
  have hpInt : Integrable p μ :=
    hp.continuousOn.integrableOn_compact isCompact_Icc
  have hdom : Integrable (fun y ↦ (1 / 4 : ℝ) * ‖p y‖) μ :=
    hpInt.norm.const_mul (1 / 4 : ℝ)
  have hregularMeas : Measurable yoshidaRegularKernel := by
    unfold yoshidaRegularKernel
    apply Measurable.ite (measurableSet_singleton 0) <;> fun_prop
  have hmeas : AEStronglyMeasurable
      (fun y ↦ yoshidaRegularKernel
        (yoshidaEndpointA * |x - y|) * p y) μ := by
    apply Measurable.aestronglyMeasurable
    exact (hregularMeas.comp (by fun_prop)).mul hp.measurable
  have hInt : Integrable
      (fun y ↦ yoshidaRegularKernel
        (yoshidaEndpointA * |x - y|) * p y) μ := by
    refine hdom.mono' hmeas ?_
    have hyMem : ∀ᵐ y ∂μ, y ∈ I := by
      dsimp only [μ]
      exact ae_restrict_mem measurableSet_Icc
    filter_upwards [hyMem] with y hy
    have hxy : |x - y| ≤ 2 := by
      rw [abs_le]
      constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
    have harg0 : 0 ≤ yoshidaEndpointA * |x - y| :=
      mul_nonneg yoshidaEndpointA_pos.le (abs_nonneg _)
    have hargLog : yoshidaEndpointA * |x - y| ≤ Real.log 2 := by
      unfold yoshidaEndpointA
      nlinarith [mul_le_mul_of_nonneg_left hxy
        (by positivity : 0 ≤ Real.log 2 / 2)]
    have hK := yoshidaRegularKernel_mem_Icc harg0 hargLog
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hK.1]
    exact mul_le_mul_of_nonneg_right hK.2 (abs_nonneg _)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
  dsimp only [μ, I] at hInt ⊢
  exact hInt.mono_measure
    (Measure.restrict_mono Ioc_subset_Icc_self (le_refl volume))

private theorem regularRepresenterPolynomial6_error_zero
    {x : ℝ} (hx : x ∈ Icc (-1) 1) :
    0 ≤ yoshidaEndpointEvenRegularRepresenter centeredEvenP0 x -
        yoshidaEndpointEvenRegularRepresenterPolynomial6 centeredEvenP0 x ∧
      yoshidaEndpointEvenRegularRepresenter centeredEvenP0 x -
        yoshidaEndpointEvenRegularRepresenterPolynomial6 centeredEvenP0 x ≤
          (1 / 250000 : ℝ) := by
  have hp : Continuous centeredEvenP0 := by
    unfold centeredEvenP0
    fun_prop
  have htrue := intervalIntegrable_regularRepresenter centeredEvenP0 hp x hx
  have hpoly := intervalIntegrable_regularRepresenterPolynomial6
    centeredEvenP0 hp x
  let Δ : ℝ → ℝ := fun y ↦
    yoshidaRegularKernel (yoshidaEndpointA * |x - y|) -
      yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * |x - y|)
  have hEq :
      yoshidaEndpointEvenRegularRepresenter centeredEvenP0 x -
          yoshidaEndpointEvenRegularRepresenterPolynomial6 centeredEvenP0 x =
        ∫ y : ℝ in -1..1, Δ y := by
    unfold yoshidaEndpointEvenRegularRepresenter
      yoshidaEndpointEvenRegularRepresenterPolynomial6
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
      ← intervalIntegral.integral_sub htrue hpoly]
    apply intervalIntegral.integral_congr
    intro y _hy
    dsimp only [Δ]
    unfold centeredEvenP0
    ring
  have hDelta : IntervalIntegrable Δ volume (-1) 1 := by
    apply (htrue.sub hpoly).congr
    intro y _hy
    dsimp only [Δ]
    unfold centeredEvenP0
    ring
  have hpoint (y : ℝ) (hy : y ∈ Icc (-1) 1) :
      0 ≤ Δ y ∧ Δ y < (1 / 500000 : ℝ) := by
    have hxy : |x - y| ≤ 2 := by
      rw [abs_le]
      constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
    have harg0 : 0 ≤ yoshidaEndpointA * |x - y| :=
      mul_nonneg yoshidaEndpointA_pos.le (abs_nonneg _)
    have hargLog : yoshidaEndpointA * |x - y| ≤ Real.log 2 := by
      unfold yoshidaEndpointA
      nlinarith [mul_le_mul_of_nonneg_left hxy
        (by positivity : 0 ≤ Real.log 2 / 2)]
    simpa only [Δ] using
      yoshidaRegularKernelPolynomial6_envelope harg0 hargLog
  have hLower : 0 ≤ ∫ y : ℝ in -1..1, Δ y := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro y hy
    exact (hpoint y (by simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hy)).1
  have hUpper :
      (∫ y : ℝ in -1..1, Δ y) ≤ (1 / 250000 : ℝ) := by
    have hconst : IntervalIntegrable (fun _ : ℝ ↦ (1 / 500000 : ℝ))
        volume (-1) 1 := continuous_const.intervalIntegrable (-1) 1
    have hmono :
        (∫ y : ℝ in -1..1, Δ y) ≤
          ∫ _y : ℝ in -1..1, (1 / 500000 : ℝ) := by
      apply intervalIntegral.integral_mono_on (by norm_num) hDelta hconst
      intro y hy
      exact (hpoint y hy).2.le
    norm_num at hmono ⊢
    exact hmono
  rw [hEq]
  exact ⟨hLower, hUpper⟩

private theorem regularRepresenterPolynomial6_error_two
    {x : ℝ} (hx : x ∈ Icc (-1) 1) :
    |yoshidaEndpointEvenRegularRepresenter centeredEvenP2 x -
        yoshidaEndpointEvenRegularRepresenterPolynomial6 centeredEvenP2 x| <
      (1 / 625000 : ℝ) := by
  have hp : Continuous centeredEvenP2 := by
    unfold centeredEvenP2
    fun_prop
  have htrue := intervalIntegrable_regularRepresenter centeredEvenP2 hp x hx
  have hpoly := intervalIntegrable_regularRepresenterPolynomial6
    centeredEvenP2 hp x
  let Δ : ℝ → ℝ := fun y ↦
    yoshidaRegularKernel (yoshidaEndpointA * |x - y|) -
      yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * |x - y|)
  have hEq :
      yoshidaEndpointEvenRegularRepresenter centeredEvenP2 x -
          yoshidaEndpointEvenRegularRepresenterPolynomial6 centeredEvenP2 x =
        ∫ y : ℝ in -1..1, Δ y * centeredEvenP2 y := by
    unfold yoshidaEndpointEvenRegularRepresenter
      yoshidaEndpointEvenRegularRepresenterPolynomial6
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
      ← intervalIntegral.integral_sub htrue hpoly]
    apply intervalIntegral.integral_congr
    intro y _hy
    dsimp only [Δ]
    ring
  have hDeltaP : IntervalIntegrable (fun y ↦ Δ y * centeredEvenP2 y)
      volume (-1) 1 := by
    apply (htrue.sub hpoly).congr
    intro y _hy
    dsimp only [Δ]
    ring
  have hAbsP : IntervalIntegrable
      (fun y ↦ (1 / 500000 : ℝ) * |centeredEvenP2 y|)
      volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    unfold centeredEvenP2
    fun_prop
  have hmono :
      (∫ y : ℝ in -1..1, |Δ y * centeredEvenP2 y|) ≤
        ∫ y : ℝ in -1..1,
          (1 / 500000 : ℝ) * |centeredEvenP2 y| := by
    apply intervalIntegral.integral_mono_on (by norm_num) hDeltaP.abs hAbsP
    intro y hy
    have hxy : |x - y| ≤ 2 := by
      rw [abs_le]
      constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
    have harg0 : 0 ≤ yoshidaEndpointA * |x - y| :=
      mul_nonneg yoshidaEndpointA_pos.le (abs_nonneg _)
    have hargLog : yoshidaEndpointA * |x - y| ≤ Real.log 2 := by
      unfold yoshidaEndpointA
      nlinarith [mul_le_mul_of_nonneg_left hxy
        (by positivity : 0 ≤ Real.log 2 / 2)]
    have hEnv := yoshidaRegularKernelPolynomial6_envelope harg0 hargLog
    rw [abs_mul, abs_of_nonneg hEnv.1]
    exact mul_le_mul_of_nonneg_right hEnv.2.le (abs_nonneg _)
  have hP2 := integral_abs_centeredEvenP2_lt_four_fifths
  have hbound :
      (∫ y : ℝ in -1..1,
          (1 / 500000 : ℝ) * |centeredEvenP2 y|) <
        (1 / 625000 : ℝ) := by
    rw [intervalIntegral.integral_const_mul]
    nlinarith
  rw [hEq]
  exact (intervalIntegral.abs_integral_le_integral_abs (by norm_num)).trans_lt
    (hmono.trans_lt hbound)

private theorem abs_fixedProjectedShiftedRemainder0_sub_polynomial6_lt_core
    {x : ℝ} (hx : x ∈ Icc (-1) 1) :
    |fixedProjectedShiftedRemainder0 x -
        fixedProjectedShiftedRemainderPolynomial6_0 x| <
      (1 / 720000 : ℝ) := by
  let R : ℝ :=
    yoshidaEndpointEvenRegularRepresenter centeredEvenP0 x -
      yoshidaEndpointEvenRegularRepresenterPolynomial6 centeredEvenP0 x
  let E : ℝ :=
    Real.cosh (yoshidaEndpointA * x / 2) -
      yoshidaEndpointCoshPolynomial6 x
  let C : ℝ := yoshidaEndpointCoshMoment centeredEvenP0
  have hRraw := regularRepresenterPolynomial6_error_zero hx
  have hR : 0 ≤ R ∧ R ≤ (1 / 250000 : ℝ) := hRraw
  have hE : |E| < (1 / 48000000000 : ℝ) := by
    exact abs_cosh_sub_yoshidaEndpointCoshPolynomial6_lt hx
  have hA0 : 0 ≤ yoshidaEndpointA := yoshidaEndpointA_pos.le
  have hA : yoshidaEndpointA < (1733 / 5000 : ℝ) := by
    unfold yoshidaEndpointA
    linarith [strict_log_two_fine_bounds.2]
  have hC0 : 0 < C := by
    have htwo : (2 : ℝ) < C := by
      dsimp only [C]
      unfold yoshidaEndpointCoshMoment centeredEvenP0
      simpa using two_lt_integral_yoshidaEndpoint_cosh
    linarith
  have hC : C < (61 / 30 : ℝ) := by
    dsimp only [C]
    unfold yoshidaEndpointCoshMoment centeredEvenP0
    simpa using integral_yoshidaEndpoint_cosh_lt_sixty_one_div_thirty
  have hEq :
      fixedProjectedShiftedRemainder0 x -
          fixedProjectedShiftedRemainderPolynomial6_0 x =
        -yoshidaEndpointA * R + 2 * yoshidaEndpointA * C * E := by
    dsimp only [R, E, C]
    unfold fixedProjectedShiftedRemainder0 fixedProjectedShiftedRemainder
      fixedProjectedBoundedRemainder fixedProjectionPolynomial
      fixedEvenLowProfile fixedProjectedShiftedRemainderPolynomial6_0
      fixedProjectedSmoothRemainderPolynomial6_0 centeredEvenP0 centeredEvenP2
    ring
  have htriangle :
      |-yoshidaEndpointA * R + 2 * yoshidaEndpointA * C * E| ≤
        yoshidaEndpointA * R + 2 * yoshidaEndpointA * C * |E| := by
    calc
      _ ≤ |-yoshidaEndpointA * R| + |2 * yoshidaEndpointA * C * E| :=
        abs_add_le _ _
      _ = _ := by
        rw [abs_mul, abs_mul, abs_mul, abs_neg,
          abs_of_nonneg hA0, abs_of_nonneg hR.1,
          abs_of_nonneg (mul_nonneg (by norm_num) hA0),
          abs_of_pos hC0]
  have hRegular :
      yoshidaEndpointA * R ≤
        (1733 / 5000 : ℝ) * (1 / 250000 : ℝ) := by
    calc
      yoshidaEndpointA * R ≤
          yoshidaEndpointA * (1 / 250000 : ℝ) :=
        mul_le_mul_of_nonneg_left hR.2 hA0
      _ ≤ (1733 / 5000 : ℝ) * (1 / 250000 : ℝ) := by
        gcongr
  have hCosh :
      2 * yoshidaEndpointA * C * |E| <
        (1733 / 2500 : ℝ) * (61 / 30 : ℝ) *
          (1 / 48000000000 : ℝ) := by
    have htwoA : 2 * yoshidaEndpointA ≤ (1733 / 2500 : ℝ) := by
      linarith
    calc
      2 * yoshidaEndpointA * C * |E| ≤
          (1733 / 2500 : ℝ) * C * |E| := by
        gcongr
      _ ≤ (1733 / 2500 : ℝ) * (61 / 30 : ℝ) * |E| := by
        gcongr
      _ < (1733 / 2500 : ℝ) * (61 / 30 : ℝ) *
          (1 / 48000000000 : ℝ) := by
        gcongr
  have hrat :
      (1733 / 5000 : ℝ) * (1 / 250000 : ℝ) +
          (1733 / 2500 : ℝ) * (61 / 30 : ℝ) *
            (1 / 48000000000 : ℝ) <
        (1 / 720000 : ℝ) := by
    norm_num
  rw [hEq]
  exact htriangle.trans_lt ((add_lt_add_of_le_of_lt hRegular hCosh).trans hrat)

private theorem abs_fixedProjectedShiftedRemainder2_sub_polynomial6_lt_core
    {x : ℝ} (hx : x ∈ Icc (-1) 1) :
    |fixedProjectedShiftedRemainder2 x -
        fixedProjectedShiftedRemainderPolynomial6_2 x| <
      (1 / 1800000 : ℝ) := by
  let R : ℝ :=
    yoshidaEndpointEvenRegularRepresenter centeredEvenP2 x -
      yoshidaEndpointEvenRegularRepresenterPolynomial6 centeredEvenP2 x
  let E : ℝ :=
    Real.cosh (yoshidaEndpointA * x / 2) -
      yoshidaEndpointCoshPolynomial6 x
  let C : ℝ := yoshidaEndpointCoshMoment centeredEvenP2
  have hR : |R| < (1 / 625000 : ℝ) :=
    regularRepresenterPolynomial6_error_two hx
  have hE : |E| < (1 / 48000000000 : ℝ) :=
    abs_cosh_sub_yoshidaEndpointCoshPolynomial6_lt hx
  have hA0 : 0 ≤ yoshidaEndpointA := yoshidaEndpointA_pos.le
  have hA : yoshidaEndpointA < (1733 / 5000 : ℝ) := by
    unfold yoshidaEndpointA
    linarith [strict_log_two_fine_bounds.2]
  have hC0 : 0 < C := by
    dsimp only [C]
    unfold yoshidaEndpointCoshMoment
    simpa using integral_yoshidaEndpoint_cosh_mul_centeredEvenP2_pos
  have hC : C < (1 / 245 : ℝ) := by
    dsimp only [C]
    unfold yoshidaEndpointCoshMoment
    simpa using
      integral_yoshidaEndpoint_cosh_mul_centeredEvenP2_lt_one_div_two_hundred_forty_five
  have hEq :
      fixedProjectedShiftedRemainder2 x -
          fixedProjectedShiftedRemainderPolynomial6_2 x =
        -yoshidaEndpointA * R + 2 * yoshidaEndpointA * C * E := by
    dsimp only [R, E, C]
    unfold fixedProjectedShiftedRemainder2 fixedProjectedShiftedRemainder
      fixedProjectedBoundedRemainder fixedProjectionPolynomial
      fixedEvenLowProfile fixedProjectedShiftedRemainderPolynomial6_2
      fixedProjectedSmoothRemainderPolynomial6_2 centeredEvenP0 centeredEvenP2
    ring
  have htriangle :
      |-yoshidaEndpointA * R + 2 * yoshidaEndpointA * C * E| ≤
        yoshidaEndpointA * |R| + 2 * yoshidaEndpointA * C * |E| := by
    calc
      _ ≤ |-yoshidaEndpointA * R| + |2 * yoshidaEndpointA * C * E| :=
        abs_add_le _ _
      _ = _ := by
        rw [abs_mul, abs_mul, abs_mul, abs_neg,
          abs_of_nonneg hA0,
          abs_of_nonneg (mul_nonneg (by norm_num) hA0),
          abs_of_pos hC0]
  have hRegular :
      yoshidaEndpointA * |R| <
        (1733 / 5000 : ℝ) * (1 / 625000 : ℝ) := by
    calc
      yoshidaEndpointA * |R| <
          yoshidaEndpointA * (1 / 625000 : ℝ) := by
        exact mul_lt_mul_of_pos_left hR yoshidaEndpointA_pos
      _ < (1733 / 5000 : ℝ) * (1 / 625000 : ℝ) := by
        gcongr
  have hCosh :
      2 * yoshidaEndpointA * C * |E| <
        (1733 / 2500 : ℝ) * (1 / 245 : ℝ) *
          (1 / 48000000000 : ℝ) := by
    have htwoA : 2 * yoshidaEndpointA ≤ (1733 / 2500 : ℝ) := by
      linarith
    calc
      2 * yoshidaEndpointA * C * |E| ≤
          (1733 / 2500 : ℝ) * C * |E| := by
        gcongr
      _ ≤ (1733 / 2500 : ℝ) * (1 / 245 : ℝ) * |E| := by
        gcongr
      _ < (1733 / 2500 : ℝ) * (1 / 245 : ℝ) *
          (1 / 48000000000 : ℝ) := by
        gcongr
  have hrat :
      (1733 / 5000 : ℝ) * (1 / 625000 : ℝ) +
          (1733 / 2500 : ℝ) * (1 / 245 : ℝ) *
            (1 / 48000000000 : ℝ) <
        (1 / 1800000 : ℝ) := by
    norm_num
  rw [hEq]
  exact htriangle.trans_lt ((add_lt_add hRegular hCosh).trans hrat)

/-- The shifted constant-basis remainder is uniformly captured by the
degree-six kernel/cosh polynomial model. -/
theorem abs_fixedProjectedShiftedRemainder0_sub_polynomial6_lt
    {x : ℝ} (hx : x ∈ Icc (-1) 1) :
    |fixedProjectedShiftedRemainder0 x -
        fixedProjectedShiftedRemainderPolynomial6_0 x| <
      (1 / 720000 : ℝ) := by
  exact abs_fixedProjectedShiftedRemainder0_sub_polynomial6_lt_core hx

/-- The shifted degree-two-basis remainder has the sharper uniform envelope. -/
theorem abs_fixedProjectedShiftedRemainder2_sub_polynomial6_lt
    {x : ℝ} (hx : x ∈ Icc (-1) 1) :
    |fixedProjectedShiftedRemainder2 x -
        fixedProjectedShiftedRemainderPolynomial6_2 x| <
      (1 / 1800000 : ℝ) := by
  exact abs_fixedProjectedShiftedRemainder2_sub_polynomial6_lt_core hx

end

end ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedRemainderEnvelopePolynomials

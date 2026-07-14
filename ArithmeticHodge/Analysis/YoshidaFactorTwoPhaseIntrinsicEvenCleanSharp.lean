import ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedRemainderEnvelopeClosure
import ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedRemainderEnvelopeCoefficients
import ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedRemainderEnvelopeMoments
import ArithmeticHodge.Analysis.YoshidaEndpointEvenLowProfile
import ArithmeticHodge.Analysis.YoshidaEndpointScalarStructuralUpper

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicEvenCleanSharp

open YoshidaConstantBounds
open YoshidaEndpointEvenConstantCross
open YoshidaEndpointEvenExactLowGramPositive
open YoshidaEndpointEvenLowPotential
open YoshidaEndpointEvenLowProfile
open YoshidaEndpointEvenP2LogEnergy
open YoshidaEndpointEvenProjectedRemainderEnvelopeCoefficients
open YoshidaEndpointEvenProjectedRemainderEnvelopeKernel
open YoshidaEndpointEvenProjectedRemainderEnvelopeMoments
open YoshidaEndpointEvenProjectedRemainderEnvelopePolynomials
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointPotentialBound
open YoshidaEndpointScalarStructuralUpper
open YoshidaRegularKernelBound
open UnitIntervalLogEnergyAffine

noncomputable section

/-!
# Sharp structural clean bounds on the intrinsic even plane

The analytic estimates in this file use one global sixth-order envelope for
the regular kernel and endpoint cosh factor.  There is no interval partition,
sampled certificate, or retained-rank computation.
-/

/-- The exact intrinsic even mass, retained as a quadratic form. -/
theorem integral_intrinsicEvenLowProfile_sq (c d : ℝ) :
    (∫ x : ℝ in -1..1, yoshidaEndpointEvenLowProfile c d x ^ 2) =
      2 * c ^ 2 + (2 / 5 : ℝ) * d ^ 2 := by
  exact integral_yoshidaEndpointEvenLowProfile_sq c d

private def elementaryEvenMoment (n : ℕ) : ℝ :=
  2 / (2 * (n : ℝ) + 1)

private theorem integral_evenPolynomial
    (N : ℕ) (a : ℕ → ℝ) :
    (∫ x : ℝ in -1..1, ∑ n ∈ Finset.range N, a n * x ^ (2 * n)) =
      ∑ n ∈ Finset.range N, a n * elementaryEvenMoment n := by
  rw [intervalIntegral.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro n _hn
    rw [intervalIntegral.integral_const_mul, integral_pow]
    unfold elementaryEvenMoment
    norm_num [pow_mul]
  · intro n _hn
    exact ((continuous_id.pow (2 * n)).const_mul (a n)).intervalIntegrable (-1) 1

private def regularPoly00Coeff : ℕ → ℝ
  | 0 => 1 / 2 - yoshidaEndpointA / 48 - yoshidaEndpointA ^ 2 / 48 +
      7 * yoshidaEndpointA ^ 3 / 23040 + yoshidaEndpointA ^ 4 / 768 -
      31 * yoshidaEndpointA ^ 5 / 5806080 -
      61 * yoshidaEndpointA ^ 6 / 645120
  | 1 => -yoshidaEndpointA / 48 - yoshidaEndpointA ^ 2 / 16 +
      7 * yoshidaEndpointA ^ 3 / 3840 + 5 * yoshidaEndpointA ^ 4 / 384 -
      31 * yoshidaEndpointA ^ 5 / 387072 -
      61 * yoshidaEndpointA ^ 6 / 30720
  | 2 => 7 * yoshidaEndpointA ^ 3 / 23040 +
      5 * yoshidaEndpointA ^ 4 / 768 -
      31 * yoshidaEndpointA ^ 5 / 387072 -
      61 * yoshidaEndpointA ^ 6 / 18432
  | 3 => -31 * yoshidaEndpointA ^ 5 / 5806080 -
      61 * yoshidaEndpointA ^ 6 / 92160
  | _ => 0

private def regularPoly02Coeff : ℕ → ℝ
  | 0 => -yoshidaEndpointA / 192 - yoshidaEndpointA ^ 2 / 120 +
      7 * yoshidaEndpointA ^ 3 / 46080 + yoshidaEndpointA ^ 4 / 1344 -
      31 * yoshidaEndpointA ^ 5 / 9289728 -
      61 * yoshidaEndpointA ^ 6 / 967680
  | 1 => yoshidaEndpointA / 96 + 7 * yoshidaEndpointA ^ 3 / 15360 +
      yoshidaEndpointA ^ 4 / 192 - 31 * yoshidaEndpointA ^ 5 / 774144 -
      61 * yoshidaEndpointA ^ 6 / 53760
  | 2 => -yoshidaEndpointA / 192 - 7 * yoshidaEndpointA ^ 3 / 46080 -
      31 * yoshidaEndpointA ^ 5 / 1548288 -
      61 * yoshidaEndpointA ^ 6 / 46080
  | 3 => 7 * yoshidaEndpointA ^ 3 / 230400 +
      31 * yoshidaEndpointA ^ 5 / 11612160
  | 4 => -31 * yoshidaEndpointA ^ 5 / 108380160
  | _ => 0

private theorem regularRepresenterPolynomial6_0_as_sum (x : ℝ) :
    regularRepresenterPolynomial6_0_explicit x =
      ∑ n ∈ Finset.range 4, regularPoly00Coeff n * x ^ (2 * n) := by
  simp [regularRepresenterPolynomial6_0_explicit, regularPoly00Coeff,
    Finset.sum_range_succ]
  ring

private theorem regularRepresenterPolynomial6_2_as_sum (x : ℝ) :
    regularRepresenterPolynomial6_2_explicit x =
      ∑ n ∈ Finset.range 5, regularPoly02Coeff n * x ^ (2 * n) := by
  simp [regularRepresenterPolynomial6_2_explicit, regularPoly02Coeff,
    Finset.sum_range_succ]
  ring

private theorem integral_regularRepresenterPolynomial6_0_explicit :
    (∫ x : ℝ in -1..1, regularRepresenterPolynomial6_0_explicit x) =
      1 - yoshidaEndpointA / 18 - yoshidaEndpointA ^ 2 / 12 +
        7 * yoshidaEndpointA ^ 3 / 3600 + yoshidaEndpointA ^ 4 / 72 -
        31 * yoshidaEndpointA ^ 5 / 317520 -
        61 * yoshidaEndpointA ^ 6 / 20160 := by
  rw [show (fun x : ℝ ↦ regularRepresenterPolynomial6_0_explicit x) =
      fun x ↦ ∑ n ∈ Finset.range 4,
        regularPoly00Coeff n * x ^ (2 * n) by
    funext x
    exact regularRepresenterPolynomial6_0_as_sum x,
    integral_evenPolynomial]
  norm_num [regularPoly00Coeff, elementaryEvenMoment, Finset.sum_range_succ]
  ring

private theorem integral_regularRepresenterPolynomial6_2_explicit :
    (∫ x : ℝ in -1..1, regularRepresenterPolynomial6_2_explicit x) =
      -yoshidaEndpointA / 180 - yoshidaEndpointA ^ 2 / 60 +
        yoshidaEndpointA ^ 3 / 1800 +
        5 * yoshidaEndpointA ^ 4 / 1008 -
        31 * yoshidaEndpointA ^ 5 / 762048 -
        61 * yoshidaEndpointA ^ 6 / 43200 := by
  rw [show (fun x : ℝ ↦ regularRepresenterPolynomial6_2_explicit x) =
      fun x ↦ ∑ n ∈ Finset.range 5,
        regularPoly02Coeff n * x ^ (2 * n) by
    funext x
    exact regularRepresenterPolynomial6_2_as_sum x,
    integral_evenPolynomial]
  norm_num [regularPoly02Coeff, elementaryEvenMoment, Finset.sum_range_succ]
  ring

private theorem integral_regularRepresenterPolynomial6_0_mul_p2 :
    (∫ x : ℝ in -1..1,
      regularRepresenterPolynomial6_0_explicit x * centeredEvenP2 x) =
      -yoshidaEndpointA / 180 - yoshidaEndpointA ^ 2 / 60 +
        yoshidaEndpointA ^ 3 / 1800 +
        5 * yoshidaEndpointA ^ 4 / 1008 -
        31 * yoshidaEndpointA ^ 5 / 762048 -
        61 * yoshidaEndpointA ^ 6 / 43200 := by
  rw [show (fun x : ℝ ↦
      regularRepresenterPolynomial6_0_explicit x * centeredEvenP2 x) =
      fun x ↦ ∑ n ∈ Finset.range 5,
        (match n with
          | 0 => -regularPoly00Coeff 0 / 2
          | k + 1 => (3 * regularPoly00Coeff k - regularPoly00Coeff (k + 1)) / 2) *
            x ^ (2 * n) by
    funext x
    simp [regularRepresenterPolynomial6_0_explicit, regularPoly00Coeff,
      centeredEvenP2, Finset.sum_range_succ]
    ring,
    integral_evenPolynomial]
  norm_num [regularPoly00Coeff, elementaryEvenMoment, Finset.sum_range_succ]
  ring

private theorem integral_regularRepresenterPolynomial6_2_mul_p2 :
    (∫ x : ℝ in -1..1,
      regularRepresenterPolynomial6_2_explicit x * centeredEvenP2 x) =
      yoshidaEndpointA / 630 + yoshidaEndpointA ^ 3 / 10800 +
        yoshidaEndpointA ^ 4 / 720 -
        31 * yoshidaEndpointA ^ 5 / 2095632 -
        61 * yoshidaEndpointA ^ 6 / 100800 := by
  rw [show (fun x : ℝ ↦
      regularRepresenterPolynomial6_2_explicit x * centeredEvenP2 x) =
      fun x ↦ ∑ n ∈ Finset.range 6,
        (match n with
          | 0 => -regularPoly02Coeff 0 / 2
          | k + 1 => (3 * regularPoly02Coeff k - regularPoly02Coeff (k + 1)) / 2) *
            x ^ (2 * n) by
    funext x
    simp [regularRepresenterPolynomial6_2_explicit, regularPoly02Coeff,
      centeredEvenP2, Finset.sum_range_succ]
    ring,
    integral_evenPolynomial]
  norm_num [regularPoly02Coeff, elementaryEvenMoment, Finset.sum_range_succ]
  ring

private theorem intervalIntegrable_regularRepresenterPolynomial6_local
    (p : ℝ → ℝ) (hp : Continuous p) (x : ℝ) :
    IntervalIntegrable
      (fun y ↦ yoshidaRegularKernelPolynomial6
          (yoshidaEndpointA * |x - y|) * p y) volume (-1) 1 := by
  apply Continuous.intervalIntegrable
  unfold yoshidaRegularKernelPolynomial6
  fun_prop

private theorem intervalIntegrable_regularRepresenter_local
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
  have htrue := intervalIntegrable_regularRepresenter_local centeredEvenP0 hp x hx
  have hpoly := intervalIntegrable_regularRepresenterPolynomial6_local
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
    exact (hpoint y (by
      simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hy)).1
  have hUpper : (∫ y : ℝ in -1..1, Δ y) ≤ (1 / 250000 : ℝ) := by
    have hconst : IntervalIntegrable (fun _ : ℝ ↦ (1 / 500000 : ℝ))
        volume (-1) 1 := continuous_const.intervalIntegrable (-1) 1
    have hmono : (∫ y : ℝ in -1..1, Δ y) ≤
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
  have htrue := intervalIntegrable_regularRepresenter_local centeredEvenP2 hp x hx
  have hpoly := intervalIntegrable_regularRepresenterPolynomial6_local
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
  have hP2 := YoshidaEndpointEvenLowRegular.integral_abs_centeredEvenP2_lt_four_fifths
  have hbound :
      (∫ y : ℝ in -1..1,
          (1 / 500000 : ℝ) * |centeredEvenP2 y|) <
        (1 / 625000 : ℝ) := by
    rw [intervalIntegral.integral_const_mul]
    nlinarith
  rw [hEq]
  exact (intervalIntegral.abs_integral_le_integral_abs (by norm_num)).trans_lt
    (hmono.trans_lt hbound)

private def regularPolynomialGram00 : ℝ :=
  1 - yoshidaEndpointA / 18 - yoshidaEndpointA ^ 2 / 12 +
    7 * yoshidaEndpointA ^ 3 / 3600 + yoshidaEndpointA ^ 4 / 72 -
    31 * yoshidaEndpointA ^ 5 / 317520 -
    61 * yoshidaEndpointA ^ 6 / 20160

private def regularPolynomialGram02 : ℝ :=
  -yoshidaEndpointA / 180 - yoshidaEndpointA ^ 2 / 60 +
    yoshidaEndpointA ^ 3 / 1800 +
    5 * yoshidaEndpointA ^ 4 / 1008 -
    31 * yoshidaEndpointA ^ 5 / 762048 -
    61 * yoshidaEndpointA ^ 6 / 43200

private def regularPolynomialGram22 : ℝ :=
  yoshidaEndpointA / 630 + yoshidaEndpointA ^ 3 / 10800 +
    yoshidaEndpointA ^ 4 / 720 -
    31 * yoshidaEndpointA ^ 5 / 2095632 -
    61 * yoshidaEndpointA ^ 6 / 100800

private theorem integral_regularPolynomial_p0 :
    (∫ x : ℝ in -1..1,
      yoshidaEndpointEvenRegularRepresenterPolynomial6 centeredEvenP0 x) =
      regularPolynomialGram00 := by
  calc
    (∫ x : ℝ in -1..1,
        yoshidaEndpointEvenRegularRepresenterPolynomial6 centeredEvenP0 x) =
        ∫ x : ℝ in -1..1, regularRepresenterPolynomial6_0_explicit x := by
      apply intervalIntegral.integral_congr
      intro x hx
      exact regularRepresenterPolynomial6_p0_eq (by
        simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hx)
    _ = regularPolynomialGram00 := by
      simpa only [regularPolynomialGram00] using
        integral_regularRepresenterPolynomial6_0_explicit

private theorem integral_regularPolynomial_p0_mul_p2 :
    (∫ x : ℝ in -1..1,
      yoshidaEndpointEvenRegularRepresenterPolynomial6 centeredEvenP0 x *
        centeredEvenP2 x) = regularPolynomialGram02 := by
  calc
    (∫ x : ℝ in -1..1,
        yoshidaEndpointEvenRegularRepresenterPolynomial6 centeredEvenP0 x *
          centeredEvenP2 x) =
        ∫ x : ℝ in -1..1,
          regularRepresenterPolynomial6_0_explicit x * centeredEvenP2 x := by
      apply intervalIntegral.integral_congr
      intro x hx
      dsimp only
      rw [regularRepresenterPolynomial6_p0_eq (by
        simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hx)]
    _ = regularPolynomialGram02 := by
      simpa only [regularPolynomialGram02] using
        integral_regularRepresenterPolynomial6_0_mul_p2

private theorem integral_regularPolynomial_p2_mul_p2 :
    (∫ x : ℝ in -1..1,
      yoshidaEndpointEvenRegularRepresenterPolynomial6 centeredEvenP2 x *
        centeredEvenP2 x) = regularPolynomialGram22 := by
  calc
    (∫ x : ℝ in -1..1,
        yoshidaEndpointEvenRegularRepresenterPolynomial6 centeredEvenP2 x *
          centeredEvenP2 x) =
        ∫ x : ℝ in -1..1,
          regularRepresenterPolynomial6_2_explicit x * centeredEvenP2 x := by
      apply intervalIntegral.integral_congr
      intro x hx
      dsimp only
      rw [regularRepresenterPolynomial6_p2_eq (by
        simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hx)]
    _ = regularPolynomialGram22 := by
      simpa only [regularPolynomialGram22] using
        integral_regularRepresenterPolynomial6_2_mul_p2

private theorem intervalIntegrable_regularPolynomial_p0 :
    IntervalIntegrable
      (yoshidaEndpointEvenRegularRepresenterPolynomial6 centeredEvenP0)
      volume (-1) 1 := by
  apply (by
    unfold regularRepresenterPolynomial6_0_explicit
    fun_prop : Continuous regularRepresenterPolynomial6_0_explicit)
    |>.intervalIntegrable (-1) 1 |>.congr
  intro x hx
  have hxIcc : x ∈ Icc (-1 : ℝ) 1 := by
    rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
    exact ⟨hx.1.le, hx.2⟩
  exact (regularRepresenterPolynomial6_p0_eq hxIcc).symm

private theorem intervalIntegrable_regularPolynomial_p0_mul_p2 :
    IntervalIntegrable
      (fun x ↦ yoshidaEndpointEvenRegularRepresenterPolynomial6 centeredEvenP0 x *
        centeredEvenP2 x) volume (-1) 1 := by
  apply (by
    unfold regularRepresenterPolynomial6_0_explicit centeredEvenP2
    fun_prop : Continuous fun x : ℝ ↦
      regularRepresenterPolynomial6_0_explicit x * centeredEvenP2 x)
    |>.intervalIntegrable (-1) 1 |>.congr
  intro x hx
  have hxIcc : x ∈ Icc (-1 : ℝ) 1 := by
    rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
    exact ⟨hx.1.le, hx.2⟩
  dsimp only
  rw [regularRepresenterPolynomial6_p0_eq hxIcc]

private theorem intervalIntegrable_regularPolynomial_p2_mul_p2 :
    IntervalIntegrable
      (fun x ↦ yoshidaEndpointEvenRegularRepresenterPolynomial6 centeredEvenP2 x *
        centeredEvenP2 x) volume (-1) 1 := by
  apply (by
    unfold regularRepresenterPolynomial6_2_explicit centeredEvenP2
    fun_prop : Continuous fun x : ℝ ↦
      regularRepresenterPolynomial6_2_explicit x * centeredEvenP2 x)
    |>.intervalIntegrable (-1) 1 |>.congr
  intro x hx
  have hxIcc : x ∈ Icc (-1 : ℝ) 1 := by
    rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
    exact ⟨hx.1.le, hx.2⟩
  dsimp only
  rw [regularRepresenterPolynomial6_p2_eq hxIcc]

/-- The global kernel envelope controls the constant regular Gram entry. -/
private theorem regularIntegral00_bounds :
    regularPolynomialGram00 ≤
        (∫ x : ℝ in -1..1,
          yoshidaEndpointEvenRegularRepresenter centeredEvenP0 x) ∧
      (∫ x : ℝ in -1..1,
          yoshidaEndpointEvenRegularRepresenter centeredEvenP0 x) ≤
        regularPolynomialGram00 + 1 / 125000 := by
  have htrue : IntervalIntegrable
      (yoshidaEndpointEvenRegularRepresenter centeredEvenP0)
      volume (-1) 1 := by
    simpa only [centeredEvenP0, mul_one] using
      intervalIntegrable_regularRepresenter_mul centeredEvenP0
        (fun _ : ℝ ↦ 1) (by unfold centeredEvenP0; fun_prop) continuous_const
  have hdiff := htrue.sub intervalIntegrable_regularPolynomial_p0
  have hLower : 0 ≤ ∫ x : ℝ in -1..1,
      yoshidaEndpointEvenRegularRepresenter centeredEvenP0 x -
        yoshidaEndpointEvenRegularRepresenterPolynomial6 centeredEvenP0 x := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro x hx
    exact (regularRepresenterPolynomial6_error_zero (by
      simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hx)).1
  have hUpper : (∫ x : ℝ in -1..1,
      yoshidaEndpointEvenRegularRepresenter centeredEvenP0 x -
        yoshidaEndpointEvenRegularRepresenterPolynomial6 centeredEvenP0 x) ≤
      (1 / 125000 : ℝ) := by
    have hc : IntervalIntegrable (fun _ : ℝ ↦ (1 / 250000 : ℝ))
        volume (-1) 1 := continuous_const.intervalIntegrable (-1) 1
    have hm : (∫ x : ℝ in -1..1,
        yoshidaEndpointEvenRegularRepresenter centeredEvenP0 x -
          yoshidaEndpointEvenRegularRepresenterPolynomial6 centeredEvenP0 x) ≤
        ∫ _x : ℝ in -1..1, (1 / 250000 : ℝ) := by
      apply intervalIntegral.integral_mono_on (by norm_num) hdiff hc
      intro x hx
      exact (regularRepresenterPolynomial6_error_zero hx).2
    norm_num at hm ⊢
    exact hm
  rw [intervalIntegral.integral_sub htrue
      intervalIntegrable_regularPolynomial_p0,
    integral_regularPolynomial_p0] at hLower hUpper
  constructor <;> linarith

/-- The mixed regular Gram entry is captured to global-envelope accuracy. -/
private theorem abs_regularIntegral02_sub_polynomial_lt :
    |(∫ x : ℝ in -1..1,
        yoshidaEndpointEvenRegularRepresenter centeredEvenP0 x * centeredEvenP2 x) -
      regularPolynomialGram02| < (1 / 312500 : ℝ) := by
  have htrue := intervalIntegrable_regularRepresenter_mul centeredEvenP0 centeredEvenP2
    (by unfold centeredEvenP0; fun_prop) (by unfold centeredEvenP2; fun_prop)
  have hdiff := htrue.sub intervalIntegrable_regularPolynomial_p0_mul_p2
  rw [← integral_regularPolynomial_p0_mul_p2,
    ← intervalIntegral.integral_sub htrue
      intervalIntegrable_regularPolynomial_p0_mul_p2]
  calc
    |(∫ x : ℝ in -1..1,
        yoshidaEndpointEvenRegularRepresenter centeredEvenP0 x * centeredEvenP2 x -
          yoshidaEndpointEvenRegularRepresenterPolynomial6 centeredEvenP0 x *
            centeredEvenP2 x)| ≤
        ∫ x : ℝ in -1..1,
          |yoshidaEndpointEvenRegularRepresenter centeredEvenP0 x * centeredEvenP2 x -
            yoshidaEndpointEvenRegularRepresenterPolynomial6 centeredEvenP0 x *
              centeredEvenP2 x| :=
      intervalIntegral.abs_integral_le_integral_abs (by norm_num)
    _ ≤ ∫ x : ℝ in -1..1,
        (1 / 250000 : ℝ) * |centeredEvenP2 x| := by
      apply intervalIntegral.integral_mono_on (by norm_num) hdiff.abs
        (by
          apply Continuous.intervalIntegrable
          unfold centeredEvenP2
          fun_prop)
      intro x hx
      rw [show
          yoshidaEndpointEvenRegularRepresenter centeredEvenP0 x * centeredEvenP2 x -
              yoshidaEndpointEvenRegularRepresenterPolynomial6 centeredEvenP0 x *
                centeredEvenP2 x =
            (yoshidaEndpointEvenRegularRepresenter centeredEvenP0 x -
              yoshidaEndpointEvenRegularRepresenterPolynomial6 centeredEvenP0 x) *
                centeredEvenP2 x by ring,
        abs_mul]
      rw [abs_of_nonneg (regularRepresenterPolynomial6_error_zero hx).1]
      exact mul_le_mul_of_nonneg_right
        (regularRepresenterPolynomial6_error_zero hx).2 (abs_nonneg _)
    _ < (1 / 312500 : ℝ) := by
      rw [intervalIntegral.integral_const_mul]
      nlinarith [YoshidaEndpointEvenLowRegular.integral_abs_centeredEvenP2_lt_four_fifths]

/-- The degree-two regular Gram entry is captured to global-envelope accuracy. -/
private theorem abs_regularIntegral22_sub_polynomial_lt :
    |(∫ x : ℝ in -1..1,
        yoshidaEndpointEvenRegularRepresenter centeredEvenP2 x * centeredEvenP2 x) -
      regularPolynomialGram22| < (1 / 781250 : ℝ) := by
  have htrue := intervalIntegrable_regularRepresenter_mul centeredEvenP2 centeredEvenP2
    (by unfold centeredEvenP2; fun_prop) (by unfold centeredEvenP2; fun_prop)
  have hdiff := htrue.sub intervalIntegrable_regularPolynomial_p2_mul_p2
  rw [← integral_regularPolynomial_p2_mul_p2,
    ← intervalIntegral.integral_sub htrue
      intervalIntegrable_regularPolynomial_p2_mul_p2]
  calc
    |(∫ x : ℝ in -1..1,
        yoshidaEndpointEvenRegularRepresenter centeredEvenP2 x * centeredEvenP2 x -
          yoshidaEndpointEvenRegularRepresenterPolynomial6 centeredEvenP2 x *
            centeredEvenP2 x)| ≤
        ∫ x : ℝ in -1..1,
          |yoshidaEndpointEvenRegularRepresenter centeredEvenP2 x * centeredEvenP2 x -
            yoshidaEndpointEvenRegularRepresenterPolynomial6 centeredEvenP2 x *
              centeredEvenP2 x| :=
      intervalIntegral.abs_integral_le_integral_abs (by norm_num)
    _ ≤ ∫ x : ℝ in -1..1,
        (1 / 625000 : ℝ) * |centeredEvenP2 x| := by
      apply intervalIntegral.integral_mono_on (by norm_num) hdiff.abs
        (by
          apply Continuous.intervalIntegrable
          unfold centeredEvenP2
          fun_prop)
      intro x hx
      rw [show
          yoshidaEndpointEvenRegularRepresenter centeredEvenP2 x * centeredEvenP2 x -
              yoshidaEndpointEvenRegularRepresenterPolynomial6 centeredEvenP2 x *
                centeredEvenP2 x =
            (yoshidaEndpointEvenRegularRepresenter centeredEvenP2 x -
              yoshidaEndpointEvenRegularRepresenterPolynomial6 centeredEvenP2 x) *
                centeredEvenP2 x by ring,
        abs_mul]
      exact mul_le_mul_of_nonneg_right
        (regularRepresenterPolynomial6_error_two hx).le (abs_nonneg _)
    _ < (1 / 781250 : ℝ) := by
      rw [intervalIntegral.integral_const_mul]
      nlinarith [YoshidaEndpointEvenLowRegular.integral_abs_centeredEvenP2_lt_four_fifths]

private theorem endpointA_fine_bounds :
    (69314718055 / 200000000000 : ℝ) < yoshidaEndpointA ∧
      yoshidaEndpointA < (69314718057 / 200000000000 : ℝ) := by
  unfold yoshidaEndpointA
  constructor <;> linarith [strict_log_two_fine_bounds.1,
    strict_log_two_fine_bounds.2]

private theorem endpointA_pow_fine_bounds (n : ℕ) (hn : n ≠ 0) :
    (69314718055 / 200000000000 : ℝ) ^ n < yoshidaEndpointA ^ n ∧
      yoshidaEndpointA ^ n <
        (69314718057 / 200000000000 : ℝ) ^ n := by
  constructor
  · exact pow_lt_pow_left₀ endpointA_fine_bounds.1 (by norm_num) hn
  · exact pow_lt_pow_left₀ endpointA_fine_bounds.2 yoshidaEndpointA_pos.le hn

private theorem regularPolynomialGram00_lt :
    regularPolynomialGram00 < (97103 / 100000 : ℝ) := by
  have h1 := endpointA_fine_bounds
  have h2 := endpointA_pow_fine_bounds 2 (by norm_num)
  have h3 := endpointA_pow_fine_bounds 3 (by norm_num)
  have h4 := endpointA_pow_fine_bounds 4 (by norm_num)
  have h5 := endpointA_pow_fine_bounds 5 (by norm_num)
  have h6 := endpointA_pow_fine_bounds 6 (by norm_num)
  unfold regularPolynomialGram00
  norm_num at h1 h2 h3 h4 h5 h6 ⊢
  linarith

private theorem regularPolynomialGram02_bounds :
    (-3837 / 1000000 : ℝ) < regularPolynomialGram02 ∧
      regularPolynomialGram02 < (-3833 / 1000000 : ℝ) := by
  have h1 := endpointA_fine_bounds
  have h2 := endpointA_pow_fine_bounds 2 (by norm_num)
  have h3 := endpointA_pow_fine_bounds 3 (by norm_num)
  have h4 := endpointA_pow_fine_bounds 4 (by norm_num)
  have h5 := endpointA_pow_fine_bounds 5 (by norm_num)
  have h6 := endpointA_pow_fine_bounds 6 (by norm_num)
  unfold regularPolynomialGram02
  constructor <;> norm_num at h1 h2 h3 h4 h5 h6 ⊢ <;> linarith

private theorem regularPolynomialGram22_lt :
    regularPolynomialGram22 < (574 / 1000000 : ℝ) := by
  have h1 := endpointA_fine_bounds
  have h3 := endpointA_pow_fine_bounds 3 (by norm_num)
  have h4 := endpointA_pow_fine_bounds 4 (by norm_num)
  have h5 := endpointA_pow_fine_bounds 5 (by norm_num)
  have h6 := endpointA_pow_fine_bounds 6 (by norm_num)
  unfold regularPolynomialGram22
  norm_num at h1 h3 h4 h5 h6 ⊢
  linarith

/-- Sharp structural upper bound for the constant regular Gram entry. -/
theorem intrinsicEven_regularGram00_lt :
    (∫ x : ℝ in -1..1,
      yoshidaEndpointEvenRegularRepresenter centeredEvenP0 x) <
      (97104 / 100000 : ℝ) := by
  have h := regularIntegral00_bounds.2
  have hp := regularPolynomialGram00_lt
  norm_num at h hp ⊢
  linarith

/-- Sharp structural two-sided bound for the mixed regular Gram entry. -/
theorem intrinsicEven_regularGram02_bounds :
    (-77 / 20000 : ℝ) <
        (∫ x : ℝ in -1..1,
          yoshidaEndpointEvenRegularRepresenter centeredEvenP0 x * centeredEvenP2 x) ∧
      (∫ x : ℝ in -1..1,
          yoshidaEndpointEvenRegularRepresenter centeredEvenP0 x * centeredEvenP2 x) <
        (-191 / 50000 : ℝ) := by
  have he := abs_lt.mp abs_regularIntegral02_sub_polynomial_lt
  have hp := regularPolynomialGram02_bounds
  constructor <;> norm_num at he hp ⊢ <;> linarith

/-- Sharp structural upper bound for the degree-two regular Gram entry. -/
theorem intrinsicEven_regularGram22_lt :
    (∫ x : ℝ in -1..1,
      yoshidaEndpointEvenRegularRepresenter centeredEvenP2 x * centeredEvenP2 x) <
      (58 / 100000 : ℝ) := by
  have he := (abs_lt.mp abs_regularIntegral22_sub_polynomial_lt).2
  have hp := regularPolynomialGram22_lt
  norm_num at he hp ⊢
  linarith

/-! ## Exact clean expansion and sharp rational enclosure -/

/-- Exact constant-coordinate clean expansion. -/
theorem intrinsicEven_cleanGram00_expansion :
    yoshidaEndpointEvenLowGram00 =
      (∫ x : ℝ in -1..1, yoshidaEndpointPotential x) -
        2 * yoshidaEndpointScalarMassLoss -
        yoshidaEndpointA *
          (∫ x : ℝ in -1..1,
            yoshidaEndpointEvenRegularRepresenter centeredEvenP0 x) +
        2 * yoshidaEndpointA *
          yoshidaEndpointCoshMoment centeredEvenP0 ^ 2 := by
  have hreg := yoshidaEndpointRegularRealBilinear_eq_integral_representer
    centeredEvenP0 centeredEvenP0 (by unfold centeredEvenP0; fun_prop)
      (by unfold centeredEvenP0; fun_prop)
  have hsinh := yoshidaEndpointSinhMoment_eq_zero_of_even centeredEvenP0
    (by intro x; rfl)
  unfold yoshidaEndpointEvenLowGram00 yoshidaEndpointEvenCleanBilinear
  rw [centeredRawLogBilinear_centeredEvenP0_eq_zero centeredEvenP0,
    hreg, hsinh]
  unfold centeredEvenP0
  norm_num
  ring

/-- Exact mixed-coordinate clean expansion. -/
theorem intrinsicEven_cleanGram02_expansion :
    yoshidaEndpointEvenLowGram02 =
      (∫ x : ℝ in -1..1,
          yoshidaEndpointPotential x * centeredEvenP2 x) -
        yoshidaEndpointA *
          (∫ x : ℝ in -1..1,
            yoshidaEndpointEvenRegularRepresenter centeredEvenP0 x *
              centeredEvenP2 x) +
        2 * yoshidaEndpointA *
          yoshidaEndpointCoshMoment centeredEvenP0 *
            yoshidaEndpointCoshMoment centeredEvenP2 := by
  have hreg := yoshidaEndpointRegularRealBilinear_eq_integral_representer
    centeredEvenP0 centeredEvenP2 (by unfold centeredEvenP0; fun_prop)
      (by unfold centeredEvenP2; fun_prop)
  have hsinh0 := yoshidaEndpointSinhMoment_eq_zero_of_even centeredEvenP0
    (by intro x; rfl)
  have hsinh2 := yoshidaEndpointSinhMoment_eq_zero_of_even centeredEvenP2
    (by intro x; unfold centeredEvenP2; ring)
  unfold yoshidaEndpointEvenLowGram02 yoshidaEndpointEvenCleanBilinear
  rw [centeredRawLogBilinear_centeredEvenP0_eq_zero centeredEvenP2,
    hreg, hsinh0, hsinh2, integral_centeredEvenP0_mul_p2]
  unfold centeredEvenP0
  norm_num
  ring

/-- Exact degree-two-coordinate clean expansion. -/
theorem intrinsicEven_cleanGram22_expansion :
    yoshidaEndpointEvenLowGram22 =
      (3 / 5 : ℝ) +
        (∫ x : ℝ in -1..1,
          yoshidaEndpointPotential x * centeredEvenP2 x ^ 2) -
        (2 / 5 : ℝ) * yoshidaEndpointScalarMassLoss -
        yoshidaEndpointA *
          (∫ x : ℝ in -1..1,
            yoshidaEndpointEvenRegularRepresenter centeredEvenP2 x *
              centeredEvenP2 x) +
        2 * yoshidaEndpointA *
          yoshidaEndpointCoshMoment centeredEvenP2 ^ 2 := by
  have hreg := yoshidaEndpointRegularRealBilinear_eq_integral_representer
    centeredEvenP2 centeredEvenP2 (by unfold centeredEvenP2; fun_prop)
      (by unfold centeredEvenP2; fun_prop)
  have hsinh := yoshidaEndpointSinhMoment_eq_zero_of_even centeredEvenP2
    (by intro x; unfold centeredEvenP2; ring)
  have hraw : centeredRawLogBilinear centeredEvenP2 centeredEvenP2 =
      centeredRawLogEnergy centeredEvenP2 := by
    unfold centeredRawLogBilinear centeredRawLogEnergy
    apply intervalIntegral.integral_congr
    intro x _hx
    apply intervalIntegral.integral_congr
    intro y _hy
    ring
  unfold yoshidaEndpointEvenLowGram22 yoshidaEndpointEvenCleanBilinear
  rw [hraw, centeredRawLogEnergy_centeredEvenP2, hreg, hsinh]
  rw [show (fun x : ℝ ↦ centeredEvenP2 x * centeredEvenP2 x) =
      fun x ↦ centeredEvenP2 x ^ 2 by
    funext x
    ring,
    integral_centeredEvenP2_sq]
  norm_num
  ring

private theorem intrinsicEven_hyper00_lower :
    2 * (69314718055 / 200000000000 : ℝ) *
        (2010024476 / 1000000000 : ℝ) ^ 2 <
      2 * yoshidaEndpointA *
        yoshidaEndpointCoshMoment centeredEvenP0 ^ 2 := by
  have hA := endpointA_fine_bounds.1
  have hC := coshMoment_p0_bounds.1
  have hC0 : 0 < yoshidaEndpointCoshMoment centeredEvenP0 :=
    (by norm_num : (0 : ℝ) < 2010024476 / 1000000000).trans hC
  have hCsq : (2010024476 / 1000000000 : ℝ) ^ 2 <
      yoshidaEndpointCoshMoment centeredEvenP0 ^ 2 :=
    pow_lt_pow_left₀ hC (by norm_num) (by norm_num)
  have hmul1 :
      (69314718055 / 200000000000 : ℝ) *
          (2010024476 / 1000000000 : ℝ) ^ 2 <
        yoshidaEndpointA * (2010024476 / 1000000000 : ℝ) ^ 2 :=
    mul_lt_mul_of_pos_right hA (by positivity)
  have hmul2 :
      yoshidaEndpointA * (2010024476 / 1000000000 : ℝ) ^ 2 <
        yoshidaEndpointA * yoshidaEndpointCoshMoment centeredEvenP0 ^ 2 :=
    mul_lt_mul_of_pos_left hCsq yoshidaEndpointA_pos
  nlinarith [hmul1.trans hmul2]

private theorem intrinsicEven_hyper02_bounds :
    2 * (69314718055 / 200000000000 : ℝ) *
        (2010024476 / 1000000000 : ℝ) *
          (4012369 / 1000000000 : ℝ) <
      2 * yoshidaEndpointA *
        yoshidaEndpointCoshMoment centeredEvenP0 *
          yoshidaEndpointCoshMoment centeredEvenP2 ∧
    2 * yoshidaEndpointA *
        yoshidaEndpointCoshMoment centeredEvenP0 *
          yoshidaEndpointCoshMoment centeredEvenP2 <
      2 * (69314718057 / 200000000000 : ℝ) *
        (2010024478 / 1000000000 : ℝ) *
          (4012371 / 1000000000 : ℝ) := by
  have hA := endpointA_fine_bounds
  have hC0 := coshMoment_p0_bounds
  have hC2 := coshMoment_p2_bounds
  have hC0pos : 0 < yoshidaEndpointCoshMoment centeredEvenP0 :=
    (by norm_num : (0 : ℝ) < 2010024476 / 1000000000).trans hC0.1
  have hC2pos : 0 < yoshidaEndpointCoshMoment centeredEvenP2 :=
    (by norm_num : (0 : ℝ) < 4012369 / 1000000000).trans hC2.1
  constructor
  · have hp :
        (2010024476 / 1000000000 : ℝ) *
            (4012369 / 1000000000 : ℝ) <
          yoshidaEndpointCoshMoment centeredEvenP0 *
            yoshidaEndpointCoshMoment centeredEvenP2 := by
      have hp1 :
          (2010024476 / 1000000000 : ℝ) *
              (4012369 / 1000000000 : ℝ) <
            yoshidaEndpointCoshMoment centeredEvenP0 *
              (4012369 / 1000000000 : ℝ) :=
        mul_lt_mul_of_pos_right hC0.1 (by norm_num)
      have hp2 :
          yoshidaEndpointCoshMoment centeredEvenP0 *
              (4012369 / 1000000000 : ℝ) <
            yoshidaEndpointCoshMoment centeredEvenP0 *
              yoshidaEndpointCoshMoment centeredEvenP2 :=
        mul_lt_mul_of_pos_left hC2.1 hC0pos
      exact hp1.trans hp2
    have hm1 :
        (69314718055 / 200000000000 : ℝ) *
            ((2010024476 / 1000000000 : ℝ) *
              (4012369 / 1000000000 : ℝ)) <
          yoshidaEndpointA *
            ((2010024476 / 1000000000 : ℝ) *
              (4012369 / 1000000000 : ℝ)) :=
      mul_lt_mul_of_pos_right hA.1 (by positivity)
    have hm2 :
        yoshidaEndpointA *
            ((2010024476 / 1000000000 : ℝ) *
              (4012369 / 1000000000 : ℝ)) <
          yoshidaEndpointA *
            (yoshidaEndpointCoshMoment centeredEvenP0 *
              yoshidaEndpointCoshMoment centeredEvenP2) :=
      mul_lt_mul_of_pos_left hp yoshidaEndpointA_pos
    nlinarith [hm1.trans hm2]
  · have hp :
        yoshidaEndpointCoshMoment centeredEvenP0 *
            yoshidaEndpointCoshMoment centeredEvenP2 <
          (2010024478 / 1000000000 : ℝ) *
            (4012371 / 1000000000 : ℝ) := by
      have hp1 :
          yoshidaEndpointCoshMoment centeredEvenP0 *
              yoshidaEndpointCoshMoment centeredEvenP2 <
            (2010024478 / 1000000000 : ℝ) *
              yoshidaEndpointCoshMoment centeredEvenP2 :=
        mul_lt_mul_of_pos_right hC0.2 hC2pos
      have hp2 :
          (2010024478 / 1000000000 : ℝ) *
              yoshidaEndpointCoshMoment centeredEvenP2 <
            (2010024478 / 1000000000 : ℝ) *
              (4012371 / 1000000000 : ℝ) :=
        mul_lt_mul_of_pos_left hC2.2 (by norm_num)
      exact hp1.trans hp2
    have hm1 :
        yoshidaEndpointA *
            (yoshidaEndpointCoshMoment centeredEvenP0 *
              yoshidaEndpointCoshMoment centeredEvenP2) <
          (69314718057 / 200000000000 : ℝ) *
            (yoshidaEndpointCoshMoment centeredEvenP0 *
              yoshidaEndpointCoshMoment centeredEvenP2) :=
      mul_lt_mul_of_pos_right hA.2 (mul_pos hC0pos hC2pos)
    have hm2 :
        (69314718057 / 200000000000 : ℝ) *
            (yoshidaEndpointCoshMoment centeredEvenP0 *
              yoshidaEndpointCoshMoment centeredEvenP2) <
          (69314718057 / 200000000000 : ℝ) *
            ((2010024478 / 1000000000 : ℝ) *
              (4012371 / 1000000000 : ℝ)) :=
      mul_lt_mul_of_pos_left hp (by norm_num)
    nlinarith [hm1.trans hm2]

private theorem intrinsicEven_hyper22_lower :
    2 * (69314718055 / 200000000000 : ℝ) *
        (4012369 / 1000000000 : ℝ) ^ 2 <
      2 * yoshidaEndpointA *
        yoshidaEndpointCoshMoment centeredEvenP2 ^ 2 := by
  have hA := endpointA_fine_bounds.1
  have hC := coshMoment_p2_bounds.1
  have hCsq : (4012369 / 1000000000 : ℝ) ^ 2 <
      yoshidaEndpointCoshMoment centeredEvenP2 ^ 2 :=
    pow_lt_pow_left₀ hC (by norm_num) (by norm_num)
  have hmul1 :
      (69314718055 / 200000000000 : ℝ) *
          (4012369 / 1000000000 : ℝ) ^ 2 <
        yoshidaEndpointA * (4012369 / 1000000000 : ℝ) ^ 2 :=
    mul_lt_mul_of_pos_right hA (by positivity)
  have hmul2 :
      yoshidaEndpointA * (4012369 / 1000000000 : ℝ) ^ 2 <
        yoshidaEndpointA * yoshidaEndpointCoshMoment centeredEvenP2 ^ 2 :=
    mul_lt_mul_of_pos_left hCsq yoshidaEndpointA_pos
  nlinarith [hmul1.trans hmul2]

private theorem intrinsicEven_regular00_scaled_upper :
    yoshidaEndpointA *
        (∫ x : ℝ in -1..1,
          yoshidaEndpointEvenRegularRepresenter centeredEvenP0 x) <
      (69314718057 / 200000000000 : ℝ) * (97104 / 100000 : ℝ) := by
  have hR := intrinsicEven_regularGram00_lt
  have hfirst := mul_lt_mul_of_pos_left hR yoshidaEndpointA_pos
  have hsecond := mul_lt_mul_of_pos_right endpointA_fine_bounds.2 (by norm_num :
    (0 : ℝ) < 97104 / 100000)
  exact hfirst.trans hsecond

private theorem intrinsicEven_regular02_scaled_bounds :
    (69314718055 / 200000000000 : ℝ) * (191 / 50000 : ℝ) <
      -yoshidaEndpointA *
        (∫ x : ℝ in -1..1,
          yoshidaEndpointEvenRegularRepresenter centeredEvenP0 x * centeredEvenP2 x) ∧
    -yoshidaEndpointA *
        (∫ x : ℝ in -1..1,
          yoshidaEndpointEvenRegularRepresenter centeredEvenP0 x * centeredEvenP2 x) <
      (69314718057 / 200000000000 : ℝ) * (77 / 20000 : ℝ) := by
  have hR := intrinsicEven_regularGram02_bounds
  have hA := endpointA_fine_bounds
  constructor
  · have hneg : (191 / 50000 : ℝ) <
        -(∫ x : ℝ in -1..1,
          yoshidaEndpointEvenRegularRepresenter centeredEvenP0 x * centeredEvenP2 x) := by
      linarith [hR.2]
    have hp1 :
        (69314718055 / 200000000000 : ℝ) * (191 / 50000 : ℝ) <
          yoshidaEndpointA * (191 / 50000 : ℝ) :=
      mul_lt_mul_of_pos_right hA.1 (by norm_num)
    have hp2 :
        yoshidaEndpointA * (191 / 50000 : ℝ) <
          yoshidaEndpointA *
            (-(∫ x : ℝ in -1..1,
              yoshidaEndpointEvenRegularRepresenter centeredEvenP0 x *
                centeredEvenP2 x)) :=
      mul_lt_mul_of_pos_left hneg yoshidaEndpointA_pos
    nlinarith [hp1.trans hp2]
  · have hneg :
        -(∫ x : ℝ in -1..1,
          yoshidaEndpointEvenRegularRepresenter centeredEvenP0 x * centeredEvenP2 x) <
          (77 / 20000 : ℝ) := by
      linarith [hR.1]
    have hp := mul_lt_mul hA.2 hneg.le (by
      have := hR.2
      norm_num at this ⊢
      linarith) (by norm_num)
    nlinarith

private theorem intrinsicEven_regular22_scaled_upper :
    yoshidaEndpointA *
        (∫ x : ℝ in -1..1,
          yoshidaEndpointEvenRegularRepresenter centeredEvenP2 x * centeredEvenP2 x) <
      (69314718057 / 200000000000 : ℝ) * (58 / 100000 : ℝ) := by
  have hR := intrinsicEven_regularGram22_lt
  have hfirst := mul_lt_mul_of_pos_left hR yoshidaEndpointA_pos
  have hsecond := mul_lt_mul_of_pos_right endpointA_fine_bounds.2
    (by norm_num : (0 : ℝ) < 58 / 100000)
  exact hfirst.trans hsecond

/-- Sharp structural lower bound for the constant clean Gram entry. -/
theorem intrinsicEven_cleanGram00_gt :
    (3665 / 10000 : ℝ) < yoshidaEndpointEvenLowGram00 := by
  have hS := yoshidaEndpointScalarMassLoss_lt_338887_div_250000
  have hA := endpointA_fine_bounds.2
  have hR := intrinsicEven_regular00_scaled_upper
  have hH := intrinsicEven_hyper00_lower
  rw [intrinsicEven_cleanGram00_expansion, integral_endpointPotential_one]
  have hlog : Real.log 2 = 2 * yoshidaEndpointA := by
    unfold yoshidaEndpointA
    ring
  rw [hlog]
  norm_num at hS hA hR hH ⊢
  linarith

/-- Sharp structural enclosure for the mixed clean Gram entry. -/
theorem intrinsicEven_cleanGram02_bounds :
    (3402 / 10000 : ℝ) < yoshidaEndpointEvenLowGram02 ∧
      yoshidaEndpointEvenLowGram02 < (3403 / 10000 : ℝ) := by
  have hR := intrinsicEven_regular02_scaled_bounds
  have hH := intrinsicEven_hyper02_bounds
  rw [intrinsicEven_cleanGram02_expansion,
    integral_endpointPotential_mul_centeredEvenP2]
  constructor <;> norm_num at hR hH ⊢ <;> linarith

/-- Sharp structural lower bound for the degree-two clean Gram entry. -/
theorem intrinsicEven_cleanGram22_gt :
    (3269 / 10000 : ℝ) < yoshidaEndpointEvenLowGram22 := by
  have hS := yoshidaEndpointScalarMassLoss_lt_338887_div_250000
  have hA := endpointA_fine_bounds.2
  have hR := intrinsicEven_regular22_scaled_upper
  have hH := intrinsicEven_hyper22_lower
  rw [intrinsicEven_cleanGram22_expansion,
    integral_endpointPotential_mul_centeredEvenP2_sq]
  have hlog : Real.log 2 = 2 * yoshidaEndpointA := by
    unfold yoshidaEndpointA
    ring
  rw [hlog]
  norm_num at hS hA hR hH ⊢
  linarith

/-! ## Cancellation-preserving quadratic lower form -/

/-- The sharp entry enclosure is packaged as one quadratic-form lower bound.
The `1/20000` mixed-entry uncertainty is absorbed by
`2 |c d| ≤ c² + d²`, rather than by choosing a sign for the cross term. -/
theorem intrinsicEven_clean_rationalQuadratic_le (c d : ℝ) :
    (7329 / 20000 : ℝ) * c ^ 2 +
        2 * (1361 / 4000 : ℝ) * c * d +
        (6537 / 20000 : ℝ) * d ^ 2 ≤
      yoshidaEndpointEvenLowGram00 * c ^ 2 +
        2 * yoshidaEndpointEvenLowGram02 * c * d +
        yoshidaEndpointEvenLowGram22 * d ^ 2 := by
  have h00 := intrinsicEven_cleanGram00_gt
  have h02 := intrinsicEven_cleanGram02_bounds
  have h22 := intrinsicEven_cleanGram22_gt
  have herr :
      |yoshidaEndpointEvenLowGram02 - (1361 / 4000 : ℝ)| <
        (1 / 20000 : ℝ) := by
    rw [abs_lt]
    constructor <;> norm_num at h02 ⊢ <;> linarith
  have hcross :
      -(1 / 20000 : ℝ) * (c ^ 2 + d ^ 2) ≤
        2 * (yoshidaEndpointEvenLowGram02 - (1361 / 4000 : ℝ)) * c * d := by
    rcases abs_lt.mp herr with ⟨herrL, herrU⟩
    by_cases hcd : 0 ≤ c * d
    · have hp := mul_le_mul_of_nonneg_right herrL.le hcd
      nlinarith [sq_nonneg (c - d)]
    · have hcd' : c * d ≤ 0 := le_of_not_ge hcd
      have hp := mul_le_mul_of_nonpos_right herrU.le hcd'
      nlinarith [sq_nonneg (c + d)]
  have h00scaled := mul_le_mul_of_nonneg_right h00.le (sq_nonneg c)
  have h22scaled := mul_le_mul_of_nonneg_right h22.le (sq_nonneg d)
  norm_num at h00scaled h22scaled hcross ⊢
  linarith

/-- The rational lower model retains a determinant reserve larger than
`1/250`; this is exact rational arithmetic. -/
theorem intrinsicEven_clean_rationalDet_gt :
    (1 / 250 : ℝ) <
      (7329 / 20000 : ℝ) * (6537 / 20000 : ℝ) -
        (1361 / 4000 : ℝ) ^ 2 := by
  norm_num

/-- Direct sharp clean-form lower bound on the intrinsic `P₀/P₂` profile. -/
theorem intrinsicEven_clean_profile_rationalQuadratic_le (c d : ℝ) :
    (7329 / 20000 : ℝ) * c ^ 2 +
        2 * (1361 / 4000 : ℝ) * c * d +
        (6537 / 20000 : ℝ) * d ^ 2 ≤
      yoshidaEndpointOddCleanQuadratic
        (yoshidaEndpointEvenLowProfile c d) := by
  rw [show yoshidaEndpointEvenLowProfile c d =
      (fun x ↦ c * centeredEvenP0 x + d * centeredEvenP2 x) by
    funext x
    unfold yoshidaEndpointEvenLowProfile centeredEvenP0
    ring]
  rw [yoshidaEndpointEvenLowGram_quadratic_eq_clean]
  exact intrinsicEven_clean_rationalQuadratic_le c d

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicEvenCleanSharp

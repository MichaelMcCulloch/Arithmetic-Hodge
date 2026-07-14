import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicEvenPositiveEndpointLoewnerUltraSharp
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowControlStep01CauchyStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowControlStep23EvenSlopeStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationOneSided
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowControlStep01MidpointReserve
import ArithmeticHodge.Analysis.YoshidaDiagonalFineBase

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowControlStep01Slope23FifthsStructural

noncomputable section

open CenteredEndpointCorrelation
open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointEvenConstantCross
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoEndpointParityPencil
open YoshidaFactorTwoPhaseIntrinsicEvenEndpointStructuralPositive
open YoshidaFactorTwoPhaseIntrinsicEvenCleanSharp
open YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive
open YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationSharp
open YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationOneSided
open YoshidaFactorTwoPhaseIntrinsicEvenPositiveEndpointSharp
open YoshidaFactorTwoPhaseIntrinsicEvenPositiveEndpointLoewnerUltraSharp
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicLowControlStep01CauchyStructural
open YoshidaFactorTwoPhaseIntrinsicLowControlStep01MidpointReserve
open YoshidaFactorTwoPhaseIntrinsicLowControlStep23EvenSlopeStructural
open YoshidaFactorTwoPhaseIntrinsicLowStaticSplitPositive
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoPhaseOddAffineKernelEstimate
open YoshidaConstantBounds
open YoshidaDiagonalFineBase
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointEvenLowPotential
open YoshidaEndpointEvenLowRegular
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointEvenProjectedRemainderEnvelopeKernel
open YoshidaEndpointEvenProjectedRemainderEnvelopeCoefficients
open YoshidaEndpointEvenProjectedRemainderEnvelopeMoments
open YoshidaEndpointEvenProjectedRemainderEnvelopePolynomials
open YoshidaRegularKernelBound

/-!
# The true structural Step01 determinant slope

The proof stays division-free until the positive endpoint determinant is
cancelled.  Its analytic core is one coupled `2 x 2` comparison; no phase or
mode enumeration, interval subdivision, sampling, or certificate replay is
used.
-/

def step01CleanDet : ℝ :=
  yoshidaEndpointEvenLowGram00 * yoshidaEndpointEvenLowGram22 -
    yoshidaEndpointEvenLowGram02 ^ 2

def step01NegativePerturbationDet : ℝ :=
  evenNegativePerturbation00 * evenNegativePerturbation22 -
    evenNegativePerturbation02 ^ 2

def step01CleanNegativeMixedDet : ℝ :=
  yoshidaEndpointEvenLowGram00 * evenNegativePerturbation22 +
    yoshidaEndpointEvenLowGram22 * evenNegativePerturbation00 -
    2 * yoshidaEndpointEvenLowGram02 * evenNegativePerturbation02

/-- Exact cancellation-preserving normal form for the `23/5` slope gap. -/
theorem five_mul_step01DetCoefficient1_sub_23_mul_coefficient0 :
    5 * factorTwoIntrinsicEvenDetCoefficient1 -
        23 * factorTwoIntrinsicEvenDetCoefficient0 =
      -23 * step01CleanDet +
        33 * step01CleanNegativeMixedDet -
        43 * step01NegativePerturbationDet := by
  unfold step01CleanDet step01CleanNegativeMixedDet
    step01NegativePerturbationDet
  unfold factorTwoIntrinsicEvenDetCoefficient0
    factorTwoIntrinsicEvenDetCoefficient1 factorTwoIntrinsicEvenPhaseDet
    factorTwoIntrinsicEvenDirection00 factorTwoIntrinsicEvenDirection02
    factorTwoIntrinsicEvenDirection22 factorTwoStructuralPhaseLow00
    factorTwoStructuralPhaseLow02 factorTwoStructuralPhaseLow22
    evenNegativePerturbation00 evenNegativePerturbation02
    evenNegativePerturbation22
  ring

/-! ## Tight global clean-coordinate upper bounds -/

private theorem step01_log_pi_mul_log_two_gt :
    (778205 / 1000000 : ℝ) < Real.log (Real.pi * Real.log 2) := by
  have hprod : (108879 / 50000 : ℝ) < Real.pi * Real.log 2 := by
    calc
      (108879 / 50000 : ℝ) <
          (3.14159265358979323846 : ℝ) *
            (69314718055 / 100000000000 : ℝ) := by norm_num
      _ < Real.pi * (69314718055 / 100000000000 : ℝ) :=
        mul_lt_mul_of_pos_right Real.pi_gt_d20 (by norm_num)
      _ < Real.pi * Real.log 2 :=
        mul_lt_mul_of_pos_left strict_log_two_fine_bounds.1 Real.pi_pos
  have hseries := Real.sum_range_le_log_div
    (x := (58879 / 158879 : ℝ)) (by norm_num) (by norm_num) 10
  have hrat : (778205 / 1000000 : ℝ) <
      Real.log (108879 / 50000 : ℝ) := by
    norm_num [Finset.sum_range_succ] at hseries ⊢
    linarith
  exact hrat.trans
    (Real.strictMonoOn_log (by norm_num)
      (mul_pos Real.pi_pos (Real.log_pos (by norm_num))) hprod)

private theorem step01_scalarMassLoss_gt :
    (135542 / 100000 : ℝ) < yoshidaEndpointScalarMassLoss := by
  have hgamma := fineGammaInterval_contains
  have hgammaLower : (5772155 / 10000000 : ℝ) ≤
      Real.eulerMascheroniConstant := by
    norm_num [fineGammaInterval, RatInterval.Contains] at hgamma ⊢
    exact hgamma.1
  unfold yoshidaEndpointScalarMassLoss
  linarith [step01_log_pi_mul_log_two_gt, hgammaLower]

private def step01RegularPolynomialGram00 : ℝ :=
  1 - yoshidaEndpointA / 18 - yoshidaEndpointA ^ 2 / 12 +
    7 * yoshidaEndpointA ^ 3 / 3600 + yoshidaEndpointA ^ 4 / 72 -
    31 * yoshidaEndpointA ^ 5 / 317520 -
    61 * yoshidaEndpointA ^ 6 / 20160

private def step01RegularPolynomialGram22 : ℝ :=
  yoshidaEndpointA / 630 + yoshidaEndpointA ^ 3 / 10800 +
    yoshidaEndpointA ^ 4 / 720 -
    31 * yoshidaEndpointA ^ 5 / 2095632 -
    61 * yoshidaEndpointA ^ 6 / 100800

private theorem step01_endpointA_bounds :
    (69314718055 / 200000000000 : ℝ) < yoshidaEndpointA ∧
      yoshidaEndpointA < (69314718057 / 200000000000 : ℝ) := by
  unfold yoshidaEndpointA
  constructor <;> linarith [strict_log_two_fine_bounds.1,
    strict_log_two_fine_bounds.2]

private theorem step01_endpointA_pow_bounds (n : ℕ) (hn : n ≠ 0) :
    (69314718055 / 200000000000 : ℝ) ^ n < yoshidaEndpointA ^ n ∧
      yoshidaEndpointA ^ n <
        (69314718057 / 200000000000 : ℝ) ^ n := by
  constructor
  · exact pow_lt_pow_left₀ step01_endpointA_bounds.1 (by norm_num) hn
  · exact pow_lt_pow_left₀ step01_endpointA_bounds.2
      yoshidaEndpointA_pos.le hn

private theorem step01RegularPolynomialGram00_gt :
    (971 / 1000 : ℝ) < step01RegularPolynomialGram00 := by
  have h1 := step01_endpointA_bounds
  have h2 := step01_endpointA_pow_bounds 2 (by norm_num)
  have h3 := step01_endpointA_pow_bounds 3 (by norm_num)
  have h4 := step01_endpointA_pow_bounds 4 (by norm_num)
  have h5 := step01_endpointA_pow_bounds 5 (by norm_num)
  have h6 := step01_endpointA_pow_bounds 6 (by norm_num)
  unfold step01RegularPolynomialGram00
  norm_num at h1 h2 h3 h4 h5 h6 ⊢
  linarith

private theorem step01RegularPolynomialGram22_gt :
    (572 / 1000000 : ℝ) < step01RegularPolynomialGram22 := by
  have h1 := step01_endpointA_bounds
  have h3 := step01_endpointA_pow_bounds 3 (by norm_num)
  have h4 := step01_endpointA_pow_bounds 4 (by norm_num)
  have h5 := step01_endpointA_pow_bounds 5 (by norm_num)
  have h6 := step01_endpointA_pow_bounds 6 (by norm_num)
  unfold step01RegularPolynomialGram22
  norm_num at h1 h3 h4 h5 h6 ⊢
  linarith

private def step01ElementaryEvenMoment (n : ℕ) : ℝ :=
  2 / (2 * (n : ℝ) + 1)

private theorem step01_integral_evenPolynomial
    (N : ℕ) (a : ℕ → ℝ) :
    (∫ x : ℝ in -1..1, ∑ n ∈ Finset.range N, a n * x ^ (2 * n)) =
      ∑ n ∈ Finset.range N, a n * step01ElementaryEvenMoment n := by
  rw [intervalIntegral.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro n _hn
    rw [intervalIntegral.integral_const_mul, integral_pow]
    unfold step01ElementaryEvenMoment
    norm_num [pow_mul]
  · intro n _hn
    exact ((continuous_id.pow (2 * n)).const_mul (a n)).intervalIntegrable (-1) 1

private def step01RegularPoly00Coeff : ℕ → ℝ
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

private def step01RegularPoly02Coeff : ℕ → ℝ
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

private theorem step01_regularRepresenterPolynomial6_0_as_sum (x : ℝ) :
    regularRepresenterPolynomial6_0_explicit x =
      ∑ n ∈ Finset.range 4, step01RegularPoly00Coeff n * x ^ (2 * n) := by
  simp [regularRepresenterPolynomial6_0_explicit, step01RegularPoly00Coeff,
    Finset.sum_range_succ]
  ring

private theorem step01_integral_regularPolynomial00 :
    (∫ x : ℝ in -1..1, regularRepresenterPolynomial6_0_explicit x) =
      step01RegularPolynomialGram00 := by
  rw [show (fun x : ℝ ↦ regularRepresenterPolynomial6_0_explicit x) =
      fun x ↦ ∑ n ∈ Finset.range 4,
        step01RegularPoly00Coeff n * x ^ (2 * n) by
    funext x
    exact step01_regularRepresenterPolynomial6_0_as_sum x,
    step01_integral_evenPolynomial]
  norm_num [step01RegularPoly00Coeff, step01ElementaryEvenMoment,
    Finset.sum_range_succ]
  unfold step01RegularPolynomialGram00
  ring

private theorem step01_integral_regularPolynomial22 :
    (∫ x : ℝ in -1..1,
      regularRepresenterPolynomial6_2_explicit x * centeredEvenP2 x) =
      step01RegularPolynomialGram22 := by
  rw [show (fun x : ℝ ↦
      regularRepresenterPolynomial6_2_explicit x * centeredEvenP2 x) =
      fun x ↦ ∑ n ∈ Finset.range 6,
        (match n with
          | 0 => -step01RegularPoly02Coeff 0 / 2
          | k + 1 =>
              (3 * step01RegularPoly02Coeff k -
                step01RegularPoly02Coeff (k + 1)) / 2) *
            x ^ (2 * n) by
    funext x
    simp [regularRepresenterPolynomial6_2_explicit, step01RegularPoly02Coeff,
      centeredEvenP2, Finset.sum_range_succ]
    ring,
    step01_integral_evenPolynomial]
  norm_num [step01RegularPoly02Coeff, step01ElementaryEvenMoment,
    Finset.sum_range_succ]
  unfold step01RegularPolynomialGram22
  ring

private theorem step01_intervalIntegrable_regularPolynomial
    (p : ℝ → ℝ) (hp : Continuous p) (x : ℝ) :
    IntervalIntegrable
      (fun y ↦ yoshidaRegularKernelPolynomial6
          (yoshidaEndpointA * |x - y|) * p y) volume (-1) 1 := by
  apply Continuous.intervalIntegrable
  unfold yoshidaRegularKernelPolynomial6
  fun_prop

private theorem step01_intervalIntegrable_regularKernel
    (p : ℝ → ℝ) (hp : Continuous p) (x : ℝ)
    (hx : x ∈ Set.Icc (-1) 1) :
    IntervalIntegrable
      (fun y ↦ yoshidaRegularKernel
          (yoshidaEndpointA * |x - y|) * p y) volume (-1) 1 := by
  let I : Set ℝ := Set.Icc (-1) 1
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

private theorem step01_regularPolynomial_p0_le_true
    {x : ℝ} (hx : x ∈ Set.Icc (-1) 1) :
    yoshidaEndpointEvenRegularRepresenterPolynomial6 centeredEvenP0 x ≤
      yoshidaEndpointEvenRegularRepresenter centeredEvenP0 x := by
  have hp : Continuous centeredEvenP0 := by
    unfold centeredEvenP0
    fun_prop
  have htrue := step01_intervalIntegrable_regularKernel centeredEvenP0 hp x hx
  have hpoly := step01_intervalIntegrable_regularPolynomial centeredEvenP0 hp x
  unfold yoshidaEndpointEvenRegularRepresenter
    yoshidaEndpointEvenRegularRepresenterPolynomial6
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  apply intervalIntegral.integral_mono_on (by norm_num) hpoly htrue
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
  have henv := yoshidaRegularKernelPolynomial6_envelope harg0 hargLog
  unfold centeredEvenP0
  linarith

private theorem step01_regularRepresenterPolynomial6_error_two
    {x : ℝ} (hx : x ∈ Set.Icc (-1) 1) :
    |yoshidaEndpointEvenRegularRepresenter centeredEvenP2 x -
        yoshidaEndpointEvenRegularRepresenterPolynomial6 centeredEvenP2 x| <
      (1 / 625000 : ℝ) := by
  have hp : Continuous centeredEvenP2 := by
    unfold centeredEvenP2
    fun_prop
  have htrue := step01_intervalIntegrable_regularKernel centeredEvenP2 hp x hx
  have hpoly := step01_intervalIntegrable_regularPolynomial centeredEvenP2 hp x
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
  have hbound :
      (∫ y : ℝ in -1..1,
          (1 / 500000 : ℝ) * |centeredEvenP2 y|) <
        (1 / 625000 : ℝ) := by
    rw [intervalIntegral.integral_const_mul]
    nlinarith [integral_abs_centeredEvenP2_lt_four_fifths]
  rw [hEq]
  exact (intervalIntegral.abs_integral_le_integral_abs (by norm_num)).trans_lt
    (hmono.trans_lt hbound)

private theorem step01_regularIntegral00_gt :
    (971 / 1000 : ℝ) <
      ∫ x : ℝ in -1..1,
        yoshidaEndpointEvenRegularRepresenter centeredEvenP0 x := by
  have htrue : IntervalIntegrable
      (yoshidaEndpointEvenRegularRepresenter centeredEvenP0)
      volume (-1) 1 := by
    simpa only [centeredEvenP0, mul_one] using
      intervalIntegrable_regularRepresenter_mul centeredEvenP0
        (fun _ : ℝ ↦ 1) (by unfold centeredEvenP0; fun_prop) continuous_const
  have hpoly : IntervalIntegrable regularRepresenterPolynomial6_0_explicit
      volume (-1) 1 := by
    exact (by
      unfold regularRepresenterPolynomial6_0_explicit
      fun_prop : Continuous regularRepresenterPolynomial6_0_explicit)
        |>.intervalIntegrable (-1) 1
  have hmono :
      (∫ x : ℝ in -1..1, regularRepresenterPolynomial6_0_explicit x) ≤
        ∫ x : ℝ in -1..1,
          yoshidaEndpointEvenRegularRepresenter centeredEvenP0 x := by
    apply intervalIntegral.integral_mono_on (by norm_num) hpoly htrue
    intro x hx
    rw [← regularRepresenterPolynomial6_p0_eq hx]
    exact step01_regularPolynomial_p0_le_true hx
  rw [step01_integral_regularPolynomial00] at hmono
  exact step01RegularPolynomialGram00_gt.trans_le hmono

private theorem step01_abs_regularIntegral22_sub_polynomial_lt :
    |(∫ x : ℝ in -1..1,
        yoshidaEndpointEvenRegularRepresenter centeredEvenP2 x * centeredEvenP2 x) -
      step01RegularPolynomialGram22| < (1 / 781250 : ℝ) := by
  have htrue := intervalIntegrable_regularRepresenter_mul
    centeredEvenP2 centeredEvenP2
    (by unfold centeredEvenP2; fun_prop) (by unfold centeredEvenP2; fun_prop)
  have hpoly : IntervalIntegrable
      (fun x : ℝ ↦
        regularRepresenterPolynomial6_2_explicit x * centeredEvenP2 x)
      volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    unfold regularRepresenterPolynomial6_2_explicit centeredEvenP2
    fun_prop
  have hdiff := htrue.sub hpoly
  rw [← step01_integral_regularPolynomial22,
    ← intervalIntegral.integral_sub htrue hpoly]
  calc
    |(∫ x : ℝ in -1..1,
        yoshidaEndpointEvenRegularRepresenter centeredEvenP2 x * centeredEvenP2 x -
          regularRepresenterPolynomial6_2_explicit x * centeredEvenP2 x)| ≤
        ∫ x : ℝ in -1..1,
          |yoshidaEndpointEvenRegularRepresenter centeredEvenP2 x * centeredEvenP2 x -
            regularRepresenterPolynomial6_2_explicit x * centeredEvenP2 x| :=
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
              regularRepresenterPolynomial6_2_explicit x * centeredEvenP2 x =
            (yoshidaEndpointEvenRegularRepresenter centeredEvenP2 x -
              yoshidaEndpointEvenRegularRepresenterPolynomial6 centeredEvenP2 x) *
                centeredEvenP2 x by
          rw [regularRepresenterPolynomial6_p2_eq hx]
          ring,
        abs_mul]
      exact mul_le_mul_of_nonneg_right
        (step01_regularRepresenterPolynomial6_error_two hx).le (abs_nonneg _)
    _ < (1 / 781250 : ℝ) := by
      rw [intervalIntegral.integral_const_mul]
      nlinarith [integral_abs_centeredEvenP2_lt_four_fifths]

private theorem step01_regularIntegral22_gt :
    (57 / 100000 : ℝ) <
      ∫ x : ℝ in -1..1,
        yoshidaEndpointEvenRegularRepresenter centeredEvenP2 x * centeredEvenP2 x := by
  have herr := step01_abs_regularIntegral22_sub_polynomial_lt
  rw [abs_lt] at herr
  nlinarith [step01RegularPolynomialGram22_gt]

/-- The constant clean coordinate is controlled globally, without splitting
the endpoint interval. -/
theorem intrinsicEven_cleanGram00_lt_step01 :
    yoshidaEndpointEvenLowGram00 < (3668 / 10000 : ℝ) := by
  have hlog := strict_log_two_fine_bounds.1
  have hmass := step01_scalarMassLoss_gt
  have hregular := step01_regularIntegral00_gt
  have hregularScaled :
      (69314718055 / 200000000000 : ℝ) * (971 / 1000) <
        yoshidaEndpointA *
          (∫ x : ℝ in -1..1,
            yoshidaEndpointEvenRegularRepresenter centeredEvenP0 x) := by
    exact mul_lt_mul step01_endpointA_bounds.1 hregular.le
      (by norm_num) yoshidaEndpointA_pos.le
  have hC := coshMoment_p0_bounds.2
  have hCpos : 0 < yoshidaEndpointCoshMoment centeredEvenP0 := by
    linarith [coshMoment_p0_bounds.1]
  have hCsq : yoshidaEndpointCoshMoment centeredEvenP0 ^ 2 <
      (2010024478 / 1000000000 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ hC hCpos.le (by norm_num)
  have hhyper :
      2 * yoshidaEndpointA *
          yoshidaEndpointCoshMoment centeredEvenP0 ^ 2 <
        2 * (69314718057 / 200000000000 : ℝ) *
          (2010024478 / 1000000000 : ℝ) ^ 2 := by
    have hmul1 := mul_lt_mul_of_pos_right step01_endpointA_bounds.2
      (sq_pos_of_pos hCpos)
    have hmul2 := mul_lt_mul_of_pos_left hCsq
      (show (0 : ℝ) < 69314718057 / 200000000000 by norm_num)
    nlinarith [hmul1, hmul2]
  rw [intrinsicEven_cleanGram00_expansion,
    YoshidaEndpointEvenLowPotential.integral_endpointPotential_one]
  norm_num at hlog hmass hregularScaled hhyper ⊢
  linarith

/-- The degree-two clean coordinate has the matching global upper bound. -/
theorem intrinsicEven_cleanGram22_lt_step01 :
    yoshidaEndpointEvenLowGram22 < (3271 / 10000 : ℝ) := by
  have hlog := strict_log_two_fine_bounds.1
  have hmass := step01_scalarMassLoss_gt
  have hregular := step01_regularIntegral22_gt
  have hregularScaled :
      (69314718055 / 200000000000 : ℝ) * (57 / 100000) <
        yoshidaEndpointA *
          (∫ x : ℝ in -1..1,
            yoshidaEndpointEvenRegularRepresenter centeredEvenP2 x *
              centeredEvenP2 x) := by
    exact mul_lt_mul step01_endpointA_bounds.1 hregular.le
      (by norm_num) yoshidaEndpointA_pos.le
  have hC := coshMoment_p2_bounds.2
  have hCpos : 0 < yoshidaEndpointCoshMoment centeredEvenP2 := by
    linarith [coshMoment_p2_bounds.1]
  have hCsq : yoshidaEndpointCoshMoment centeredEvenP2 ^ 2 <
      (4012371 / 1000000000 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ hC hCpos.le (by norm_num)
  have hhyper :
      2 * yoshidaEndpointA *
          yoshidaEndpointCoshMoment centeredEvenP2 ^ 2 <
        2 * (69314718057 / 200000000000 : ℝ) *
          (4012371 / 1000000000 : ℝ) ^ 2 := by
    have hmul1 := mul_lt_mul_of_pos_right step01_endpointA_bounds.2
      (sq_pos_of_pos hCpos)
    have hmul2 := mul_lt_mul_of_pos_left hCsq
      (show (0 : ℝ) < 69314718057 / 200000000000 by norm_num)
    nlinarith [hmul1, hmul2]
  rw [intrinsicEven_cleanGram22_expansion,
    integral_endpointPotential_mul_centeredEvenP2_sq]
  norm_num at hlog hmass hregularScaled hhyper ⊢
  linarith

/-! ## One global Bernstein sign for the coupled analytic defect -/

private def step01DefectKernel (x y z t : ℝ) : ℝ :=
  z + x * (3 * t ^ 4 + 6 * t ^ 3 - 8 * t ^ 2 - 16 * t + 8) / 40 -
    y * t * (t - 1)

/-- A single Bernstein basis proves the correlation pencil has the needed
sign on the whole displacement interval. -/
private theorem step01DefectKernel_nonneg
    {x y z t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 2)
    (hxLower : (46369 / 20000 : ℝ) < x)
    (hxUpper : x < (1165723 / 500000 : ℝ))
    (hyLower : (604577 / 250000 : ℝ) < y)
    (hyUpper : y < (1211621 / 500000 : ℝ))
    (hzLower : (2681039 / 1000000 : ℝ) < z) :
    0 ≤ step01DefectKernel x y z t := by
  let u : ℝ := t / 2
  let k0 : ℝ := z + x / 5
  let k1 : ℝ := z + y / 2
  let k2 : ℝ := z + (y - x) / 3
  let k3 : ℝ := z - (x + y) / 2
  let k4 : ℝ := x - 2 * y + z
  have hu0 : 0 ≤ u := by dsimp only [u]; linarith [ht.1]
  have hu1 : u ≤ 1 := by dsimp only [u]; linarith [ht.2]
  have huOne : 0 ≤ 1 - u := sub_nonneg.mpr hu1
  have hk0 : 0 ≤ k0 := by dsimp only [k0]; norm_num at *; linarith
  have hk1 : 0 ≤ k1 := by dsimp only [k1]; norm_num at *; linarith
  have hk2 : 0 ≤ k2 := by dsimp only [k2]; norm_num at *; linarith
  have hk3 : 0 ≤ k3 := by dsimp only [k3]; norm_num at *; linarith
  have hk4 : 0 ≤ k4 := by dsimp only [k4]; norm_num at *; linarith
  have h0 : 0 ≤ k0 * (1 - u) ^ 4 := mul_nonneg hk0 (by positivity)
  have h1 : 0 ≤ 4 * k1 * u * (1 - u) ^ 3 := by positivity
  have h2 : 0 ≤ 6 * k2 * u ^ 2 * (1 - u) ^ 2 := by positivity
  have h3 : 0 ≤ 4 * k3 * u ^ 3 * (1 - u) := by positivity
  have h4 : 0 ≤ k4 * u ^ 4 := mul_nonneg hk4 (by positivity)
  have hBernstein :
      step01DefectKernel x y z t =
        k0 * (1 - u) ^ 4 + 4 * k1 * u * (1 - u) ^ 3 +
          6 * k2 * u ^ 2 * (1 - u) ^ 2 +
          4 * k3 * u ^ 3 * (1 - u) + k4 * u ^ 4 := by
    unfold step01DefectKernel
    dsimp only [u, k0, k1, k2, k3, k4]
    ring
  rw [hBernstein]
  positivity

def step01AnalyticError00 : ℝ :=
  poleFreeAnalyticError evenStructuralCorrelation00

def step01AnalyticError02 : ℝ :=
  poleFreeAnalyticError evenStructuralCorrelation02

def step01AnalyticError22 : ℝ :=
  poleFreeAnalyticError evenStructuralCorrelation22

/-- The true negative perturbation is the public polynomial midpoint minus
one globally coupled analytic-error Gram. -/
theorem step01_negativePerturbation_eq_midpoint_sub_error :
    evenNegativePerturbation00 = step01Midpoint00 - step01AnalyticError00 ∧
      evenNegativePerturbation02 = step01Midpoint02 - step01AnalyticError02 ∧
      evenNegativePerturbation22 = step01Midpoint22 - step01AnalyticError22 := by
  have hsplit00 := evenStructuralRegularError_eq_analytic_add_polynomial
    evenStructuralCorrelation00
      (by unfold evenStructuralCorrelation00; fun_prop)
  have hsplit02 := evenStructuralRegularError_eq_analytic_add_polynomial
    evenStructuralCorrelation02
      (by unfold evenStructuralCorrelation02; fun_prop)
  have hsplit22 := evenStructuralRegularError_eq_analytic_add_polynomial
    evenStructuralCorrelation22
      (by unfold evenStructuralCorrelation22; fun_prop)
  rw [integral_polynomialDifference_mul_evenCorrelations.1] at hsplit00
  rw [integral_polynomialDifference_mul_evenCorrelations.2.1] at hsplit02
  rw [integral_polynomialDifference_mul_evenCorrelations.2.2] at hsplit22
  have hpert00 :
      factorTwoCenteredSymmetricPerturbation centeredEvenP0 =
        evenStructuralRegularError evenStructuralCorrelation00 +
          evenStructuralKernelBase00 := by
    rw [factorTwoCenteredSymmetricPerturbation_even_structural_eq.1]
    unfold evenStructuralKernelBase00
    ring
  have hpert02 :
      factorTwoCenteredSymmetricPerturbationBilinear
          centeredEvenP0 centeredEvenP2 =
        evenStructuralRegularError evenStructuralCorrelation02 +
          evenStructuralKernelBase02 := by
    rw [factorTwoCenteredSymmetricPerturbation_even_structural_eq.2.1]
    unfold evenStructuralKernelBase02
    ring
  have hpert22 :
      factorTwoCenteredSymmetricPerturbation centeredEvenP2 =
        evenStructuralRegularError evenStructuralCorrelation22 +
          evenStructuralKernelBase22 := by
    rw [factorTwoCenteredSymmetricPerturbation_even_structural_eq.2.2]
    unfold evenStructuralKernelBase22
    ring
  constructor
  · unfold evenNegativePerturbation00 step01AnalyticError00
    rw [hpert00, hsplit00,
      step01Midpoint_eq_kernel_sub_positiveMoment.1]
    ring
  constructor
  · unfold evenNegativePerturbation02 step01AnalyticError02
    rw [hpert02, hsplit02,
      step01Midpoint_eq_kernel_sub_positiveMoment.2.1]
    ring
  · unfold evenNegativePerturbation22 step01AnalyticError22
    rw [hpert22, hsplit22,
      step01Midpoint_eq_kernel_sub_positiveMoment.2.2]
    ring

private theorem step01_abs_analyticError00_le :
    |step01AnalyticError00| ≤ (3 / 4000 : ℝ) := by
  have h := abs_poleFreeAnalyticError_profile_le 1 0
  have hfun : centeredEndpointCorrelation
      (factorTwoEvenStructuralLowProfile 1 0) = evenStructuralCorrelation00 := by
    funext t
    rw [centeredEndpointCorrelation_evenStructuralProfile]
    norm_num
  rw [hfun] at h
  norm_num [step01AnalyticError00] at h ⊢
  exact h

private theorem step01_abs_analyticError22_le :
    |step01AnalyticError22| ≤ (3 / 20000 : ℝ) := by
  have h := abs_poleFreeAnalyticError_profile_le 0 1
  have hfun : centeredEndpointCorrelation
      (factorTwoEvenStructuralLowProfile 0 1) = evenStructuralCorrelation22 := by
    funext t
    rw [centeredEndpointCorrelation_evenStructuralProfile]
    norm_num
  rw [hfun] at h
  norm_num [step01AnalyticError22] at h ⊢
  exact h

private theorem step01_analyticError_det_le :
    step01AnalyticError00 * step01AnalyticError22 -
        step01AnalyticError02 ^ 2 ≤ (9 / 80000000 : ℝ) := by
  have hprod : step01AnalyticError00 * step01AnalyticError22 ≤
      |step01AnalyticError00| * |step01AnalyticError22| := by
    calc
      step01AnalyticError00 * step01AnalyticError22 ≤
          |step01AnalyticError00 * step01AnalyticError22| := le_abs_self _
      _ = |step01AnalyticError00| * |step01AnalyticError22| := abs_mul _ _
  have habsProd : |step01AnalyticError00| * |step01AnalyticError22| ≤
      (3 / 4000 : ℝ) * (3 / 20000 : ℝ) :=
    mul_le_mul step01_abs_analyticError00_le step01_abs_analyticError22_le
      (abs_nonneg _) (by norm_num)
  nlinarith [sq_nonneg step01AnalyticError02]

private def step01AnalyticCorrelationPencil
    (a b d u v w t : ℝ) : ℝ :=
  (43 * u - 33 * a) * evenStructuralCorrelation22 t +
    (43 * w - 33 * d) * evenStructuralCorrelation00 t -
    2 * (43 * v - 33 * b) * evenStructuralCorrelation02 t

private theorem step01AnalyticCorrelationPencil_nonpos
    {a b d u v w t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 2)
    (haLower : (3665 / 10000 : ℝ) < a)
    (haUpper : a < (3668 / 10000 : ℝ))
    (hbLower : (3402 / 10000 : ℝ) < b)
    (hbUpper : b < (3403 / 10000 : ℝ))
    (hdLower : (3269 / 10000 : ℝ) < d)
    (huLower : (227278 / 1000000 : ℝ) < u)
    (huUpper : u < (227350 / 1000000 : ℝ))
    (hvLower : (204806 / 1000000 : ℝ) < v)
    (hvUpper : v < (204844 / 1000000 : ℝ))
    (hwUpper : w < (188527 / 1000000 : ℝ)) :
    step01AnalyticCorrelationPencil a b d u v w t ≤ 0 := by
  let x : ℝ := 33 * a - 43 * u
  let y : ℝ := 33 * b - 43 * v
  let z : ℝ := 33 * d - 43 * w
  have hxLower : (46369 / 20000 : ℝ) < x := by
    dsimp only [x]
    norm_num at *
    linarith
  have hxUpper : x < (1165723 / 500000 : ℝ) := by
    dsimp only [x]
    norm_num at *
    linarith
  have hyLower : (604577 / 250000 : ℝ) < y := by
    dsimp only [y]
    norm_num at *
    linarith
  have hyUpper : y < (1211621 / 500000 : ℝ) := by
    dsimp only [y]
    norm_num at *
    linarith
  have hzLower : (2681039 / 1000000 : ℝ) < z := by
    dsimp only [z]
    norm_num at *
    linarith
  have hK := step01DefectKernel_nonneg ht hxLower hxUpper hyLower hyUpper hzLower
  have hidentity :
      step01AnalyticCorrelationPencil a b d u v w t =
        -(2 - t) * step01DefectKernel x y z t := by
    unfold step01AnalyticCorrelationPencil step01DefectKernel
      evenStructuralCorrelation00 evenStructuralCorrelation02
      evenStructuralCorrelation22
    dsimp only [x, y, z]
    ring
  rw [hidentity]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sub_nonneg.mpr ht.2)) hK

private theorem step01_analyticMixed_nonneg
    {a b d u v w : ℝ}
    (haLower : (3665 / 10000 : ℝ) < a)
    (haUpper : a < (3668 / 10000 : ℝ))
    (hbLower : (3402 / 10000 : ℝ) < b)
    (hbUpper : b < (3403 / 10000 : ℝ))
    (hdLower : (3269 / 10000 : ℝ) < d)
    (huLower : (227278 / 1000000 : ℝ) < u)
    (huUpper : u < (227350 / 1000000 : ℝ))
    (hvLower : (204806 / 1000000 : ℝ) < v)
    (hvUpper : v < (204844 / 1000000 : ℝ))
    (hwUpper : w < (188527 / 1000000 : ℝ)) :
    0 ≤
      (43 * u - 33 * a) * step01AnalyticError22 +
        (43 * w - 33 * d) * step01AnalyticError00 -
        2 * (43 * v - 33 * b) * step01AnalyticError02 := by
  let h : ℝ → ℝ := fun t ↦
    oddLowPoleFreeKernel t - poleFreeKernelPolynomial6 t
  let A00 : ℝ := 43 * u - 33 * a
  let A02 : ℝ := 43 * v - 33 * b
  let A22 : ℝ := 43 * w - 33 * d
  have h00 : IntervalIntegrable
      (fun t ↦ h t * evenStructuralCorrelation00 t) volume 0 2 := by
    dsimp only [h]
    exact intervalIntegrable_poleFreeAnalyticError evenStructuralCorrelation00
      (by unfold evenStructuralCorrelation00; fun_prop)
  have h02 : IntervalIntegrable
      (fun t ↦ h t * evenStructuralCorrelation02 t) volume 0 2 := by
    dsimp only [h]
    exact intervalIntegrable_poleFreeAnalyticError evenStructuralCorrelation02
      (by unfold evenStructuralCorrelation02; fun_prop)
  have h22 : IntervalIntegrable
      (fun t ↦ h t * evenStructuralCorrelation22 t) volume 0 2 := by
    dsimp only [h]
    exact intervalIntegrable_poleFreeAnalyticError evenStructuralCorrelation22
      (by unfold evenStructuralCorrelation22; fun_prop)
  have hEq :
      (43 * u - 33 * a) * step01AnalyticError22 +
          (43 * w - 33 * d) * step01AnalyticError00 -
          2 * (43 * v - 33 * b) * step01AnalyticError02 =
        ∫ t : ℝ in 0..2,
          h t * step01AnalyticCorrelationPencil a b d u v w t := by
    calc
      (43 * u - 33 * a) * step01AnalyticError22 +
          (43 * w - 33 * d) * step01AnalyticError00 -
          2 * (43 * v - 33 * b) * step01AnalyticError02 =
        A00 * (∫ t : ℝ in 0..2, h t * evenStructuralCorrelation22 t) +
          A22 * (∫ t : ℝ in 0..2, h t * evenStructuralCorrelation00 t) -
          (2 * A02) *
            (∫ t : ℝ in 0..2, h t * evenStructuralCorrelation02 t) := by
        unfold step01AnalyticError00 step01AnalyticError02
          step01AnalyticError22 poleFreeAnalyticError
        dsimp only [h, A00, A02, A22]
      _ = ∫ t : ℝ in 0..2,
          (A00 * (h t * evenStructuralCorrelation22 t) +
            A22 * (h t * evenStructuralCorrelation00 t)) -
              (2 * A02) * (h t * evenStructuralCorrelation02 t) := by
        rw [intervalIntegral.integral_sub
          ((h22.const_mul A00).add (h00.const_mul A22))
          (h02.const_mul (2 * A02)),
          intervalIntegral.integral_add (h22.const_mul A00)
            (h00.const_mul A22)]
        repeat rw [intervalIntegral.integral_const_mul]
      _ = ∫ t : ℝ in 0..2,
          h t * step01AnalyticCorrelationPencil a b d u v w t := by
        apply intervalIntegral.integral_congr
        intro t _ht
        unfold step01AnalyticCorrelationPencil
        dsimp only [A00, A02, A22]
        ring
  rw [hEq]
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro t ht
  exact mul_nonneg_of_nonpos_of_nonpos
    (poleFreeKernel_sub_polynomial_nonpos ht)
    (step01AnalyticCorrelationPencil_nonpos ht haLower haUpper hbLower hbUpper
      hdLower huLower huUpper hvLower hvUpper hwUpper)

private theorem step01_target_eq_midpoint_analytic :
    -23 * step01CleanDet +
        33 * step01CleanNegativeMixedDet -
        43 * step01NegativePerturbationDet =
      step01MidpointReserve
          yoshidaEndpointEvenLowGram00 yoshidaEndpointEvenLowGram02
          yoshidaEndpointEvenLowGram22 +
        ((43 * step01Midpoint00 - 33 * yoshidaEndpointEvenLowGram00) *
            step01AnalyticError22 +
          (43 * step01Midpoint22 - 33 * yoshidaEndpointEvenLowGram22) *
            step01AnalyticError00 -
          2 * (43 * step01Midpoint02 - 33 * yoshidaEndpointEvenLowGram02) *
            step01AnalyticError02) -
        43 * (step01AnalyticError00 * step01AnalyticError22 -
          step01AnalyticError02 ^ 2) := by
  unfold step01CleanDet step01CleanNegativeMixedDet
    step01NegativePerturbationDet step01MidpointReserve
  rw [step01_negativePerturbation_eq_midpoint_sub_error.1,
    step01_negativePerturbation_eq_midpoint_sub_error.2.1,
    step01_negativePerturbation_eq_midpoint_sub_error.2.2]
  ring

/-- The cancellation-preserving determinant numerator has a strict global
reserve at the target slope `23/5`. -/
theorem five_mul_step01DetCoefficient1_sub_23_mul_coefficient0_pos :
    0 < 5 * factorTwoIntrinsicEvenDetCoefficient1 -
      23 * factorTwoIntrinsicEvenDetCoefficient0 := by
  have hreserve := one_div_twenty_thousand_lt_step01MidpointReserve
    intrinsicEven_cleanGram00_gt intrinsicEven_cleanGram00_lt_step01
    intrinsicEven_cleanGram02_bounds.1 intrinsicEven_cleanGram22_gt
    intrinsicEven_cleanGram22_lt_step01
  have hmixed := step01_analyticMixed_nonneg
    intrinsicEven_cleanGram00_gt intrinsicEven_cleanGram00_lt_step01
    intrinsicEven_cleanGram02_bounds.1 intrinsicEven_cleanGram02_bounds.2
    intrinsicEven_cleanGram22_gt step01Midpoint00_gt step01Midpoint00_lt
    step01Midpoint02_gt step01Midpoint02_lt step01Midpoint22_lt
  have hdet := step01_analyticError_det_le
  rw [five_mul_step01DetCoefficient1_sub_23_mul_coefficient0,
    step01_target_eq_midpoint_analytic]
  norm_num at hreserve hdet ⊢
  nlinarith

private theorem factorTwoIntrinsicEvenDetCoefficient0_pos_step01 :
    0 < factorTwoIntrinsicEvenDetCoefficient0 := by
  unfold factorTwoIntrinsicEvenDetCoefficient0
  exact factorTwoIntrinsicEven_plus_endpoint_structural_gates.2

/-- Unconditional structural Step01 determinant slope bound. -/
theorem factorTwoIntrinsicStep01Slope_twentyThree_fifths_le :
    (23 / 5 : ℝ) ≤ factorTwoIntrinsicStep01Slope := by
  unfold factorTwoIntrinsicStep01Slope
  rw [le_div_iff₀ factorTwoIntrinsicEvenDetCoefficient0_pos_step01]
  nlinarith [five_mul_step01DetCoefficient1_sub_23_mul_coefficient0_pos]

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowControlStep01Slope23FifthsStructural

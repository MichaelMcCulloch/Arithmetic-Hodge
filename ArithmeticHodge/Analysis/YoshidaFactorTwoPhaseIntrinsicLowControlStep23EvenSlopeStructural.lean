import ArithmeticHodge.Analysis.TwoByTwoRankOneVariance
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowControlStep12Step23Positive

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowControlStep23EvenSlopeStructural

noncomputable section

open YoshidaConstantBounds
open CenteredEndpointCorrelation
open YoshidaEndpointEvenExactLowGramPositive
open YoshidaEndpointEvenConstantCross
open YoshidaEndpointEvenProjectedRemainderEnvelopeKernel
open YoshidaEndpointEvenProjectedRemainderEnvelopeCoefficients
open YoshidaEndpointEvenProjectedRemainderEnvelopeMoments
open YoshidaEndpointEvenProjectedRemainderEnvelopePolynomials
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointPotentialBound
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoEndpointParityPencil
open YoshidaFactorTwoPhaseIntrinsicEvenCleanSharp
open YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicLowControlStep12Step23Positive
open YoshidaFactorTwoPhaseIntrinsicLowControlsPositive
open YoshidaFactorTwoPhaseLowSchur
open YoshidaRegularKernelBound

/-!
# Structural closure of the Step23 even determinant slope

Write the even pencil as `E(x) = (C-Q) + x(2Q)`, where `x = (1-a)/2`,
`C` is the clean midpoint matrix, and `Q` is the negative of the symmetric
perturbation.  The global regular-kernel remainder gives a
single Loewner lower Gram `L ⪯ Q`.  The determinant slope is monotone
under adding the positive-semidefinite defect `Q-L`, so the proof reduces
to one exact mixed-determinant inequality for `C` and `L`.

There is no phase subdivision, sampled certificate, or entrywise Step23
control estimate below.
-/

/-! ## The global-kernel lower Gram for the negative perturbation -/

def evenSlopeKernel00 : ℝ :=
  -evenStructuralKernelBase00 - 1 / 250

def evenSlopeKernel02 : ℝ :=
  -evenStructuralKernelBase02

def evenSlopeKernel22 : ℝ :=
  -evenStructuralKernelBase22 - 1 / 1250

theorem evenSlopeKernel00_lower :
    (5591 / 25000 : ℝ) < evenSlopeKernel00 := by
  have hL := strict_log_two_fine_bounds.1
  have ha := log_two_div_sqrt_two_kernel_lower
  have hb := log_three_div_sqrt_three_kernel_bounds.1
  have hC := primeRatio_evenCorrelation_bounds.1
  have hbeta : 0 < Real.log 3 / Real.sqrt 3 := by positivity
  have hprod :
      (63427 / 100000 : ℝ) * (83 / 100 : ℝ) <
        (Real.log 3 / Real.sqrt 3) *
          evenStructuralCorrelation00
            (factorTwoPrimeShift / yoshidaEndpointA) := by
    calc
      (63427 / 100000 : ℝ) * (83 / 100 : ℝ) <
          (Real.log 3 / Real.sqrt 3) * (83 / 100 : ℝ) :=
        mul_lt_mul_of_pos_right hb (by norm_num)
      _ < (Real.log 3 / Real.sqrt 3) *
          evenStructuralCorrelation00
            (factorTwoPrimeShift / yoshidaEndpointA) :=
        mul_lt_mul_of_pos_left hC hbeta
  unfold evenSlopeKernel00 evenStructuralKernelBase00
  nlinarith

theorem evenSlopeKernel02_bounds :
    0 < evenSlopeKernel02 ∧
      evenSlopeKernel02 < (4097 / 20000 : ℝ) := by
  have hL := strict_log_two_fine_bounds
  have hb := log_three_div_sqrt_three_kernel_bounds
  have hC := primeRatio_evenCorrelation_bounds.2
  have hbeta : 0 < Real.log 3 / Real.sqrt 3 := by positivity
  have hprodPos : 0 < (Real.log 3 / Real.sqrt 3) *
      evenStructuralCorrelation02
        (factorTwoPrimeShift / yoshidaEndpointA) :=
    mul_pos hbeta hC.1
  have hprodUpper :
      (Real.log 3 / Real.sqrt 3) *
          evenStructuralCorrelation02
            (factorTwoPrimeShift / yoshidaEndpointA) <
        (6343 / 10000 : ℝ) * (1651 / 20000 : ℝ) := by
    calc
      (Real.log 3 / Real.sqrt 3) *
          evenStructuralCorrelation02
            (factorTwoPrimeShift / yoshidaEndpointA) <
          (6343 / 10000 : ℝ) *
            evenStructuralCorrelation02
              (factorTwoPrimeShift / yoshidaEndpointA) :=
        mul_lt_mul_of_pos_right hb.2 hC.1
      _ < (6343 / 10000 : ℝ) * (1651 / 20000 : ℝ) :=
        mul_lt_mul_of_pos_left hC.2.1 (by norm_num)
  unfold evenSlopeKernel02 evenStructuralKernelBase02
  constructor <;> nlinarith

private theorem primeRatio_evenCorrelation02_lower :
    (824 / 10000 : ℝ) < evenStructuralCorrelation02
      (factorTwoPrimeShift / yoshidaEndpointA) := by
  let t : ℝ := factorTwoPrimeShift / yoshidaEndpointA
  let a : ℝ := 11699 / 10000
  have ht := factorTwoPrimeRatio_kernel_bounds
  have ha : a < t := by simpa only [a, t] using ht.1
  have hb : (83 / 100 : ℝ) < 2 - t := by
    dsimp only [t]
    linarith [ht.2]
  have hc : (1699 / 10000 : ℝ) < t - 1 := by
    dsimp only [a] at ha
    linarith
  have ht0 : 0 < t := by dsimp only [t]; linarith [ht.1]
  have htwo : 0 < 2 - t := by linarith [hb]
  have hone : 0 < t - 1 := by linarith [hc]
  have hp1 : a * (83 / 100 : ℝ) < t * (2 - t) := by
    calc
      a * (83 / 100 : ℝ) < t * (83 / 100 : ℝ) :=
        mul_lt_mul_of_pos_right ha (by norm_num)
      _ < t * (2 - t) := mul_lt_mul_of_pos_left hb ht0
  have hp1pos : 0 < t * (2 - t) := mul_pos ht0 htwo
  have hp2 :
      a * (83 / 100 : ℝ) * (1699 / 10000 : ℝ) <
        t * (2 - t) * (t - 1) := by
    calc
      a * (83 / 100 : ℝ) * (1699 / 10000 : ℝ) <
          (t * (2 - t)) * (1699 / 10000 : ℝ) :=
        mul_lt_mul_of_pos_right hp1 (by norm_num)
      _ < (t * (2 - t)) * (t - 1) :=
        mul_lt_mul_of_pos_left hc hp1pos
  dsimp only [t] at hp2 ⊢
  unfold evenStructuralCorrelation02
  norm_num at hp2 ⊢
  nlinarith

theorem evenSlopeKernel02_lower :
    (2047 / 10000 : ℝ) < evenSlopeKernel02 := by
  have hL := strict_log_two_fine_bounds.1
  have hb := log_three_div_sqrt_three_kernel_bounds.1
  have hC := primeRatio_evenCorrelation02_lower
  have hbeta : 0 < Real.log 3 / Real.sqrt 3 := by positivity
  have hprod :
      (63427 / 100000 : ℝ) * (824 / 10000 : ℝ) <
        (Real.log 3 / Real.sqrt 3) *
          evenStructuralCorrelation02
            (factorTwoPrimeShift / yoshidaEndpointA) := by
    calc
      (63427 / 100000 : ℝ) * (824 / 10000 : ℝ) <
          (Real.log 3 / Real.sqrt 3) * (824 / 10000 : ℝ) :=
        mul_lt_mul_of_pos_right hb (by norm_num)
      _ < (Real.log 3 / Real.sqrt 3) *
          evenStructuralCorrelation02
            (factorTwoPrimeShift / yoshidaEndpointA) :=
        mul_lt_mul_of_pos_left hC hbeta
  unfold evenSlopeKernel02 evenStructuralKernelBase02
  nlinarith

theorem evenSlopeKernel22_lower :
    (1877 / 10000 : ℝ) < evenSlopeKernel22 := by
  have hL := strict_log_two_fine_bounds.1
  have ha := log_two_div_sqrt_two_kernel_lower
  have hb := log_three_div_sqrt_three_kernel_bounds.2
  have hC := primeRatio_evenCorrelation_bounds.2.2.2
  have hbeta : 0 < Real.log 3 / Real.sqrt 3 := by positivity
  have hCneg : (-1337 / 10000 : ℝ) < 0 := by norm_num
  have hstep1 :
      (Real.log 3 / Real.sqrt 3) * (-1337 / 10000 : ℝ) <
        (Real.log 3 / Real.sqrt 3) *
          evenStructuralCorrelation22
            (factorTwoPrimeShift / yoshidaEndpointA) :=
    mul_lt_mul_of_pos_left hC hbeta
  have hstep2 :
      (6343 / 10000 : ℝ) * (-1337 / 10000 : ℝ) <
        (Real.log 3 / Real.sqrt 3) * (-1337 / 10000 : ℝ) :=
    mul_lt_mul_of_neg_right hb hCneg
  have hprod := hstep2.trans hstep1
  unfold evenSlopeKernel22 evenStructuralKernelBase22
  nlinarith

private theorem primeRatio_evenCorrelation22_upper :
    evenStructuralCorrelation22
        (factorTwoPrimeShift / yoshidaEndpointA) < (-267 / 2000 : ℝ) := by
  let t : ℝ := factorTwoPrimeShift / yoshidaEndpointA
  let s : ℝ := t - 1
  let p : ℝ :=
    3 * t ^ 4 + 6 * t ^ 3 - 8 * t ^ 2 - 16 * t + 8
  have ht := factorTwoPrimeRatio_kernel_bounds
  have hsLower : (1699 / 10000 : ℝ) < s := by
    dsimp only [s, t]
    linarith [ht.1]
  have hsUpper : s < (17 / 100 : ℝ) := by
    dsimp only [s, t]
    linarith [ht.2]
  have hs0 : 0 ≤ s := by linarith [hsLower]
  have hs2 : s ^ 2 < (17 / 100 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ hsUpper hs0 (by norm_num)
  have hs3 : s ^ 3 < (17 / 100 : ℝ) ^ 3 :=
    pow_lt_pow_left₀ hsUpper hs0 (by norm_num)
  have hs4 : s ^ 4 < (17 / 100 : ℝ) ^ 4 :=
    pow_lt_pow_left₀ hsUpper hs0 (by norm_num)
  have hpExpansion :
      p = 3 * s ^ 4 + 18 * s ^ 3 + 28 * s ^ 2 - 2 * s - 7 := by
    dsimp only [p, s]
    ring
  have hp : p < (-6439 / 1000 : ℝ) := by
    rw [hpExpansion]
    nlinarith
  have htwo : (83 / 100 : ℝ) < 2 - t := by
    dsimp only [t]
    linarith [ht.2]
  have hnegp : (6439 / 1000 : ℝ) < -p := by linarith
  have hprod :
      (83 / 100 : ℝ) * (6439 / 1000 : ℝ) <
        (2 - t) * (-p) := by
    calc
      (83 / 100 : ℝ) * (6439 / 1000 : ℝ) <
          (2 - t) * (6439 / 1000 : ℝ) :=
        mul_lt_mul_of_pos_right htwo (by norm_num)
      _ < (2 - t) * (-p) :=
        mul_lt_mul_of_pos_left hnegp (by linarith [htwo])
  have hcorr : evenStructuralCorrelation22 t = -((2 - t) * (-p)) / 40 := by
    unfold evenStructuralCorrelation22
    dsimp only [p]
    ring
  dsimp only [t] at hcorr ⊢
  rw [hcorr]
  norm_num at hprod ⊢
  nlinarith

private theorem log_two_div_sqrt_two_kernel_upper :
    Real.log 2 / Real.sqrt 2 < (49014 / 100000 : ℝ) := by
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  rw [div_lt_iff₀ hspos]
  have hlog := strict_log_two_fine_bounds.2
  have hs := sqrt_two_kernel_bounds.1
  nlinarith

theorem evenSlopeKernel22_upper :
    evenSlopeKernel22 < (188 / 1000 : ℝ) := by
  have hL := strict_log_two_fine_bounds.2
  have ha := log_two_div_sqrt_two_kernel_upper
  have hb := log_three_div_sqrt_three_kernel_bounds.1
  have hC := primeRatio_evenCorrelation22_upper
  have hbeta : 0 < Real.log 3 / Real.sqrt 3 := by positivity
  have hCneg : (-267 / 2000 : ℝ) < 0 := by norm_num
  have hstep1 :
      (Real.log 3 / Real.sqrt 3) *
          evenStructuralCorrelation22
            (factorTwoPrimeShift / yoshidaEndpointA) <
        (Real.log 3 / Real.sqrt 3) * (-267 / 2000 : ℝ) :=
    mul_lt_mul_of_pos_left hC hbeta
  have hstep2 :
      (Real.log 3 / Real.sqrt 3) * (-267 / 2000 : ℝ) <
        (63427 / 100000 : ℝ) * (-267 / 2000 : ℝ) :=
    mul_lt_mul_of_neg_right hb hCneg
  have hprod := hstep1.trans hstep2
  unfold evenSlopeKernel22 evenStructuralKernelBase22
  nlinarith

/-- The exact global kernel envelope leaves a positive-definite lower Gram
inside the negative perturbation. -/
theorem evenSlopeKernel_principal_minors_pos :
    0 < evenSlopeKernel00 ∧
      0 < evenSlopeKernel00 * evenSlopeKernel22 - evenSlopeKernel02 ^ 2 := by
  have h00 := evenSlopeKernel00_lower
  have h02 := evenSlopeKernel02_bounds
  have h22 := evenSlopeKernel22_lower
  have h00pos : 0 < evenSlopeKernel00 :=
    (by norm_num : (0 : ℝ) < 5591 / 25000).trans h00
  have hprod :
      (5591 / 25000 : ℝ) * (1877 / 10000 : ℝ) <
        evenSlopeKernel00 * evenSlopeKernel22 :=
    mul_lt_mul h00 h22.le (by norm_num) h00pos.le
  have hsq : evenSlopeKernel02 ^ 2 < (4097 / 20000 : ℝ) ^ 2 := by
    have hsum : 0 < (4097 / 20000 : ℝ) + evenSlopeKernel02 :=
      add_pos (by norm_num) h02.1
    nlinarith [mul_pos (sub_pos.mpr h02.2) hsum]
  constructor
  · exact h00pos
  · have hrational :
        (4097 / 20000 : ℝ) ^ 2 <
          (5591 / 25000 : ℝ) * (1877 / 10000 : ℝ) := by
      norm_num
    nlinarith

/-- The coupled regular-kernel error is charged once to the full profile,
so the fixed Gram `L` lies below the complete negative perturbation `Q` in
Loewner order. -/
theorem evenSlopeKernel_quadratic_le_negativePerturbation (c d : ℝ) :
    evenSlopeKernel00 * c ^ 2 +
        2 * evenSlopeKernel02 * c * d +
        evenSlopeKernel22 * d ^ 2 ≤
      -factorTwoCenteredSymmetricPerturbation
        (factorTwoEvenStructuralLowProfile c d) := by
  have herr := abs_evenStructuralRegularError_profile_le c d
  have herrUpper :
      evenStructuralRegularError
          (centeredEndpointCorrelation
            (factorTwoEvenStructuralLowProfile c d)) ≤
        (1 / 500 : ℝ) * (2 * c ^ 2 + (2 / 5 : ℝ) * d ^ 2) :=
    (le_abs_self _).trans herr
  rw [factorTwoCenteredSymmetricPerturbation_even_profile_kernel_eq]
  unfold evenSlopeKernel00 evenSlopeKernel02 evenSlopeKernel22
  nlinarith

/-! ## A coarse structural upper bound for the clean constant entry -/

private theorem intervalIntegrable_regularPolynomial_local
    (p : ℝ → ℝ) (hp : Continuous p) (x : ℝ) :
    IntervalIntegrable
      (fun y ↦ yoshidaRegularKernelPolynomial6
          (yoshidaEndpointA * |x - y|) * p y) volume (-1) 1 := by
  apply Continuous.intervalIntegrable
  unfold yoshidaRegularKernelPolynomial6
  fun_prop

private theorem intervalIntegrable_regularKernel_local
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

private theorem regularRepresenterPolynomial6_le_true
    {x : ℝ} (hx : x ∈ Icc (-1) 1) :
    yoshidaEndpointEvenRegularRepresenterPolynomial6 centeredEvenP0 x ≤
      yoshidaEndpointEvenRegularRepresenter centeredEvenP0 x := by
  have hp : Continuous centeredEvenP0 := by
    unfold centeredEvenP0
    fun_prop
  have htrue := intervalIntegrable_regularKernel_local centeredEvenP0 hp x hx
  have hpoly := intervalIntegrable_regularPolynomial_local centeredEvenP0 hp x
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

private def regularPolynomialGram00 : ℝ :=
  1 - yoshidaEndpointA / 18 - yoshidaEndpointA ^ 2 / 12 +
    7 * yoshidaEndpointA ^ 3 / 3600 + yoshidaEndpointA ^ 4 / 72 -
    31 * yoshidaEndpointA ^ 5 / 317520 -
    61 * yoshidaEndpointA ^ 6 / 20160

private theorem integral_regularRepresenterPolynomial6_0_explicit :
    (∫ x : ℝ in -1..1, regularRepresenterPolynomial6_0_explicit x) =
      regularPolynomialGram00 := by
  unfold regularRepresenterPolynomial6_0_explicit regularPolynomialGram00
  norm_num
  ring

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
  · exact pow_lt_pow_left₀ endpointA_fine_bounds.2
      yoshidaEndpointA_pos.le hn

private theorem regularPolynomialGram00_gt :
    (97 / 100 : ℝ) < regularPolynomialGram00 := by
  have h1 := endpointA_fine_bounds
  have h2 := endpointA_pow_fine_bounds 2 (by norm_num)
  have h3 := endpointA_pow_fine_bounds 3 (by norm_num)
  have h4 := endpointA_pow_fine_bounds 4 (by norm_num)
  have h5 := endpointA_pow_fine_bounds 5 (by norm_num)
  have h6 := endpointA_pow_fine_bounds 6 (by norm_num)
  unfold regularPolynomialGram00
  norm_num at h1 h2 h3 h4 h5 h6 ⊢
  linarith

theorem intrinsicEven_regularGram00_gt_ninety_seven_hundredths :
    (97 / 100 : ℝ) <
      ∫ x : ℝ in -1..1,
        yoshidaEndpointEvenRegularRepresenter centeredEvenP0 x := by
  have htrue : IntervalIntegrable
      (yoshidaEndpointEvenRegularRepresenter centeredEvenP0) volume (-1) 1 := by
    simpa only [mul_one] using
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
    exact regularRepresenterPolynomial6_le_true hx
  rw [integral_regularRepresenterPolynomial6_0_explicit] at hmono
  exact regularPolynomialGram00_gt.trans_le hmono

private theorem log_pi_mul_log_two_gt_7776 :
    (7776 / 10000 : ℝ) < Real.log (Real.pi * Real.log 2) := by
  have hlog := strict_log_two_fine_bounds.1
  have hp1 :
      (3.14159265358979323846 : ℝ) *
          (69314718055 / 100000000000 : ℝ) <
        Real.pi * (69314718055 / 100000000000 : ℝ) :=
    mul_lt_mul_of_pos_right Real.pi_gt_d20 (by norm_num)
  have hp2 :
      Real.pi * (69314718055 / 100000000000 : ℝ) <
        Real.pi * Real.log 2 :=
    mul_lt_mul_of_pos_left hlog Real.pi_pos
  have hprod : (2177 / 1000 : ℝ) < Real.pi * Real.log 2 := by
    calc
      (2177 / 1000 : ℝ) <
          (3.14159265358979323846 : ℝ) *
            (69314718055 / 100000000000 : ℝ) := by norm_num
      _ < Real.pi * (69314718055 / 100000000000 : ℝ) := hp1
      _ < Real.pi * Real.log 2 := hp2
  have hseries := Real.sum_range_le_log_div
    (x := (1177 / 3177 : ℝ)) (by norm_num) (by norm_num) 3
  have hrat : (7776 / 10000 : ℝ) < Real.log (2177 / 1000 : ℝ) := by
    norm_num [Finset.sum_range_succ] at hseries ⊢
    linarith
  exact hrat.trans (Real.strictMonoOn_log (by norm_num)
    (mul_pos Real.pi_pos (Real.log_pos (by norm_num))) hprod)

private theorem yoshidaEndpointScalarMassLoss_gt_13547 :
    (13547 / 10000 : ℝ) < yoshidaEndpointScalarMassLoss := by
  unfold yoshidaEndpointScalarMassLoss
  linarith [strict_euler_gamma_bounds.1, log_pi_mul_log_two_gt_7776]

/-- Only a coarse constant-entry upper bound is needed by the exact
mixed-determinant margin.  Its proof uses the global sixth-order kernel
envelope, not a diagonal computation. -/
theorem intrinsicEven_cleanGram00_lt_thirtyseven_hundredths :
    yoshidaEndpointEvenLowGram00 < (37 / 100 : ℝ) := by
  have hpotential :
      (∫ x : ℝ in -1..1, yoshidaEndpointPotential x) <
        (307 / 500 : ℝ) := by
    rw [YoshidaEndpointEvenLowPotential.integral_endpointPotential_one]
    linarith [strict_log_two_fine_bounds.1]
  have hmass := yoshidaEndpointScalarMassLoss_gt_13547
  have hregular := intrinsicEven_regularGram00_gt_ninety_seven_hundredths
  have hregularScaled : (3361 / 10000 : ℝ) <
      yoshidaEndpointA *
        (∫ x : ℝ in -1..1,
          yoshidaEndpointEvenRegularRepresenter centeredEvenP0 x) := by
    have hmul := mul_lt_mul endpointA_fine_bounds.1 hregular.le
      (by norm_num) yoshidaEndpointA_pos.le
    norm_num at hmul ⊢
    nlinarith
  have hC := coshMoment_p0_bounds.2
  have hCpos : 0 < yoshidaEndpointCoshMoment centeredEvenP0 := by
    linarith [coshMoment_p0_bounds.1]
  have hCsq : yoshidaEndpointCoshMoment centeredEvenP0 ^ 2 <
      (2010024478 / 1000000000 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ hC hCpos.le (by norm_num)
  have hhyper :
      2 * yoshidaEndpointA *
          yoshidaEndpointCoshMoment centeredEvenP0 ^ 2 <
        (2801 / 1000 : ℝ) := by
    have hmul :
        yoshidaEndpointA * yoshidaEndpointCoshMoment centeredEvenP0 ^ 2 <
          (69314718057 / 200000000000 : ℝ) *
            (2010024478 / 1000000000 : ℝ) ^ 2 := by
      calc
        yoshidaEndpointA * yoshidaEndpointCoshMoment centeredEvenP0 ^ 2 <
            (69314718057 / 200000000000 : ℝ) *
              yoshidaEndpointCoshMoment centeredEvenP0 ^ 2 :=
          mul_lt_mul_of_pos_right endpointA_fine_bounds.2 (sq_pos_of_pos hCpos)
        _ < (69314718057 / 200000000000 : ℝ) *
            (2010024478 / 1000000000 : ℝ) ^ 2 :=
          mul_lt_mul_of_pos_left hCsq (by norm_num)
    norm_num at hmul ⊢
    nlinarith
  rw [intrinsicEven_cleanGram00_expansion]
  linarith

theorem intrinsicEven_cleanGram00_lt_three_eighths :
    yoshidaEndpointEvenLowGram00 < (3 / 8 : ℝ) :=
  intrinsicEven_cleanGram00_lt_thirtyseven_hundredths.trans (by norm_num)

/-! ## The exact clean/kernel mixed-determinant margin -/

private def determinantSlopeMargin
    (a b d u v w : ℝ) : ℝ :=
  -3 * (a * d - b ^ 2) +
    5 * (a * w + d * u - 2 * b * v) +
    13 * (u * w - v ^ 2)

/-- This is the sole rational margin in the proof.  It is a comparison of
two complete Gram matrices: the exact clean matrix and the global-kernel
lower matrix. -/
theorem intrinsicEven_clean_slopeKernel_margin_pos :
    0 < determinantSlopeMargin
      yoshidaEndpointEvenLowGram00 yoshidaEndpointEvenLowGram02
      yoshidaEndpointEvenLowGram22
      evenSlopeKernel00 evenSlopeKernel02 evenSlopeKernel22 := by
  let a : ℝ := yoshidaEndpointEvenLowGram00
  let b : ℝ := yoshidaEndpointEvenLowGram02
  let d : ℝ := yoshidaEndpointEvenLowGram22
  let u : ℝ := evenSlopeKernel00
  let v : ℝ := evenSlopeKernel02
  let w : ℝ := evenSlopeKernel22
  have ha : a < (37 / 100 : ℝ) := by
    simpa only [a] using intrinsicEven_cleanGram00_lt_thirtyseven_hundredths
  have hb0 : 0 < b := by
    dsimp only [b]
    linarith [intrinsicEven_cleanGram02_bounds.1]
  have hb : b < (3403 / 10000 : ℝ) := by
    simpa only [b] using intrinsicEven_cleanGram02_bounds.2
  have hd : (3269 / 10000 : ℝ) < d := by
    simpa only [d] using intrinsicEven_cleanGram22_gt
  have hu : (5591 / 25000 : ℝ) < u := by
    simpa only [u] using evenSlopeKernel00_lower
  have hv0 : 0 < v := by
    simpa only [v] using evenSlopeKernel02_bounds.1
  have hvLower : (2047 / 10000 : ℝ) < v := by
    simpa only [v] using evenSlopeKernel02_lower
  have hv : v < (4097 / 20000 : ℝ) := by
    simpa only [v] using evenSlopeKernel02_bounds.2
  have hw0 : 0 < w := by
    dsimp only [w]
    linarith [evenSlopeKernel22_lower]
  have hwLower : (1877 / 10000 : ℝ) < w := by
    simpa only [w] using evenSlopeKernel22_lower
  have hw : w < (188 / 1000 : ℝ) := by
    simpa only [w] using evenSlopeKernel22_upper
  have hstepV :
      determinantSlopeMargin
          (37 / 100) (3403 / 10000) (3269 / 10000)
          (5591 / 25000) (4097 / 20000) (1877 / 10000) <
        determinantSlopeMargin
          (37 / 100) (3403 / 10000) (3269 / 10000)
          (5591 / 25000) v (1877 / 10000) := by
    have hfactor : 0 <
        ((4097 / 20000 : ℝ) - v) *
          (10 * (3403 / 10000 : ℝ) +
            13 * (v + (4097 / 20000 : ℝ))) := by
      exact mul_pos (sub_pos.mpr hv) (by positivity)
    unfold determinantSlopeMargin
    nlinarith
  have hstepW :
      determinantSlopeMargin
          (37 / 100) (3403 / 10000) (3269 / 10000)
          (5591 / 25000) v (1877 / 10000) <
        determinantSlopeMargin
          (37 / 100) (3403 / 10000) (3269 / 10000)
          (5591 / 25000) v w := by
    have hfactor : 0 <
        (w - (1877 / 10000 : ℝ)) *
          (5 * (37 / 100 : ℝ) + 13 * (5591 / 25000 : ℝ)) := by
      exact mul_pos (sub_pos.mpr hwLower) (by norm_num)
    unfold determinantSlopeMargin
    nlinarith
  have hstepU :
      determinantSlopeMargin
          (37 / 100) (3403 / 10000) (3269 / 10000)
          (5591 / 25000) v w <
        determinantSlopeMargin
          (37 / 100) (3403 / 10000) (3269 / 10000) u v w := by
    have hfactor : 0 <
        (u - (5591 / 25000 : ℝ)) *
          (5 * (3269 / 10000 : ℝ) + 13 * w) := by
      exact mul_pos (sub_pos.mpr hu) (by positivity)
    unfold determinantSlopeMargin
    nlinarith
  have hstepB :
      determinantSlopeMargin
          (37 / 100) (3403 / 10000) (3269 / 10000) u v w <
        determinantSlopeMargin
          (37 / 100) b (3269 / 10000) u v w := by
    have hslope :
        0 < 10 * v - 3 * ((3403 / 10000 : ℝ) + b) := by
      nlinarith
    have hfactor : 0 <
        ((3403 / 10000 : ℝ) - b) *
          (10 * v - 3 * ((3403 / 10000 : ℝ) + b)) :=
      mul_pos (sub_pos.mpr hb) hslope
    unfold determinantSlopeMargin
    nlinarith
  have hstepD :
      determinantSlopeMargin
          (37 / 100) b (3269 / 10000) u v w <
        determinantSlopeMargin (37 / 100) b d u v w := by
    have hslope : 0 < 5 * u - 3 * (37 / 100 : ℝ) := by
      nlinarith
    have hfactor : 0 <
        (d - (3269 / 10000 : ℝ)) *
          (5 * u - 3 * (37 / 100 : ℝ)) :=
      mul_pos (sub_pos.mpr hd) hslope
    unfold determinantSlopeMargin
    nlinarith
  have hstepA :
      determinantSlopeMargin (37 / 100) b d u v w <
        determinantSlopeMargin a b d u v w := by
    have hslope : 0 < 3 * d - 5 * w := by
      nlinarith
    have hfactor : 0 <
        ((37 / 100 : ℝ) - a) * (3 * d - 5 * w) :=
      mul_pos (sub_pos.mpr ha) hslope
    unfold determinantSlopeMargin
    nlinarith
  have hrational : 0 <
      determinantSlopeMargin
        (37 / 100) (3403 / 10000) (3269 / 10000)
        (5591 / 25000) (4097 / 20000) (1877 / 10000) := by
    norm_num [determinantSlopeMargin]
  dsimp only [a, b, d, u, v, w] at hstepA ⊢
  exact hrational.trans
    (hstepV.trans (hstepW.trans
      (hstepU.trans (hstepB.trans (hstepD.trans hstepA)))))

/-! ## Monotonicity under the positive-semidefinite kernel defect -/

private theorem twoByTwo_coefficients_nonneg_of_quadratic_nonneg
    (q00 q02 q22 : ℝ)
    (hq : ∀ c d : ℝ,
      0 ≤ q00 * c ^ 2 + 2 * q02 * c * d + q22 * d ^ 2) :
    0 ≤ q00 ∧ 0 ≤ q22 ∧ 0 ≤ q00 * q22 - q02 ^ 2 := by
  have h00 : 0 ≤ q00 := by
    have h := hq 1 0
    norm_num at h ⊢
    exact h
  have h22 : 0 ≤ q22 := by
    have h := hq 0 1
    norm_num at h ⊢
    exact h
  refine ⟨h00, h22, ?_⟩
  by_cases hq00 : q00 = 0
  · subst q00
    by_cases hq22 : q22 = 0
    · subst q22
      have hp := hq 1 1
      have hm := hq 1 (-1)
      norm_num at hp hm ⊢
      have hq02 : q02 = 0 := by linarith
      norm_num [hq02]
    · have hq22pos : 0 < q22 := lt_of_le_of_ne h22 (Ne.symm hq22)
      have hspecial := hq q22 (-q02)
      norm_num at hspecial ⊢
      have hq02 : q02 = 0 := by
        by_contra hne
        have hsq : 0 < q02 ^ 2 := sq_pos_of_ne_zero hne
        nlinarith [mul_pos hq22pos hsq]
      norm_num [hq02]
  · have hq00pos : 0 < q00 := lt_of_le_of_ne h00 (Ne.symm hq00)
    have hspecial := hq q02 (-q00)
    have hid :
        q00 * q02 ^ 2 + 2 * q02 * q02 * (-q00) +
            q22 * (-q00) ^ 2 =
          q00 * (q00 * q22 - q02 ^ 2) := by
      ring
    rw [hid] at hspecial
    exact nonneg_of_mul_nonneg_right hspecial hq00pos

private theorem twoByTwo_mixedDet_nonneg_of_quadratics_nonneg
    (a b d u v w : ℝ)
    (hA : ∀ c e : ℝ,
      0 ≤ a * c ^ 2 + 2 * b * c * e + d * e ^ 2)
    (hU : ∀ c e : ℝ,
      0 ≤ u * c ^ 2 + 2 * v * c * e + w * e ^ 2) :
    0 ≤ a * w + d * u - 2 * b * v := by
  have hAc := twoByTwo_coefficients_nonneg_of_quadratic_nonneg a b d hA
  have hUc := twoByTwo_coefficients_nonneg_of_quadratic_nonneg u v w hU
  by_cases hu : u = 0
  · subst u
    have hv : v = 0 := by
      by_cases hw : w = 0
      · subst w
        have hp := hU 1 1
        have hm := hU 1 (-1)
        norm_num at hp hm
        linarith
      · have hwpos : 0 < w := lt_of_le_of_ne hUc.2.1 (Ne.symm hw)
        have hspecial := hU w (-v)
        norm_num at hspecial
        by_contra hne
        have hsq : 0 < v ^ 2 := sq_pos_of_ne_zero hne
        nlinarith [mul_pos hwpos hsq]
    subst v
    norm_num
    exact mul_nonneg hAc.1 hUc.2.1
  · have hupos : 0 < u := lt_of_le_of_ne hUc.1 (Ne.symm hu)
    have hAeval := hA v (-u)
    have hid :
        u * (a * w + d * u - 2 * b * v) =
          a * (u * w - v ^ 2) +
            (a * v ^ 2 + 2 * b * v * (-u) + d * (-u) ^ 2) := by
      ring
    have hscaled : 0 ≤ u * (a * w + d * u - 2 * b * v) := by
      rw [hid]
      exact add_nonneg (mul_nonneg hAc.1 hUc.2.2) hAeval
    exact nonneg_of_mul_nonneg_right hscaled hupos

def evenNegativePerturbation00 : ℝ :=
  -factorTwoCenteredSymmetricPerturbation centeredEvenP0

def evenNegativePerturbation02 : ℝ :=
  -factorTwoCenteredSymmetricPerturbationBilinear
    centeredEvenP0 centeredEvenP2

def evenNegativePerturbation22 : ℝ :=
  -factorTwoCenteredSymmetricPerturbation centeredEvenP2

theorem evenNegativePerturbation_profile_eq (c d : ℝ) :
    evenNegativePerturbation00 * c ^ 2 +
        2 * evenNegativePerturbation02 * c * d +
        evenNegativePerturbation22 * d ^ 2 =
      -factorTwoCenteredSymmetricPerturbation
        (factorTwoEvenStructuralLowProfile c d) := by
  rw [factorTwoCenteredSymmetricPerturbation_structuralLow]
  unfold evenNegativePerturbation00 evenNegativePerturbation02
    evenNegativePerturbation22
  ring

/-- The difference `Q-L` is positive semidefinite as a complete quadratic
form.  No coefficient of the defect is bounded separately. -/
theorem evenNegativePerturbation_sub_slopeKernel_nonneg (c d : ℝ) :
    0 ≤
      (evenNegativePerturbation00 - evenSlopeKernel00) * c ^ 2 +
        2 * (evenNegativePerturbation02 - evenSlopeKernel02) * c * d +
        (evenNegativePerturbation22 - evenSlopeKernel22) * d ^ 2 := by
  have hle := evenSlopeKernel_quadratic_le_negativePerturbation c d
  rw [← evenNegativePerturbation_profile_eq] at hle
  nlinarith

private theorem intrinsicEven_clean_quadratic_nonneg (c d : ℝ) :
    0 ≤ yoshidaEndpointEvenLowGram00 * c ^ 2 +
      2 * yoshidaEndpointEvenLowGram02 * c * d +
      yoshidaEndpointEvenLowGram22 * d ^ 2 := by
  by_cases hne : c ≠ 0 ∨ d ≠ 0
  · exact (real_twoByTwo_quadratic_pos
      yoshidaEndpointEvenLowGram00 yoshidaEndpointEvenLowGram02
      yoshidaEndpointEvenLowGram22 c d
      yoshidaEndpointEvenLowGram00_pos
      yoshidaEndpointEvenLowGram_det_pos hne).le
  · push_neg at hne
    rcases hne with ⟨rfl, rfl⟩
    norm_num

private theorem evenSlopeKernel_quadratic_nonneg (c d : ℝ) :
    0 ≤ evenSlopeKernel00 * c ^ 2 +
      2 * evenSlopeKernel02 * c * d + evenSlopeKernel22 * d ^ 2 := by
  by_cases hne : c ≠ 0 ∨ d ≠ 0
  · exact (real_twoByTwo_quadratic_pos
      evenSlopeKernel00 evenSlopeKernel02 evenSlopeKernel22 c d
      evenSlopeKernel_principal_minors_pos.1
      evenSlopeKernel_principal_minors_pos.2 hne).le
  · push_neg at hne
    rcases hne with ⟨rfl, rfl⟩
    norm_num

/-- Adding the positive-semidefinite defect `Q-L` can only increase the
complete determinant-slope margin. -/
theorem intrinsicEven_clean_negativePerturbation_margin_pos :
    0 < determinantSlopeMargin
      yoshidaEndpointEvenLowGram00 yoshidaEndpointEvenLowGram02
      yoshidaEndpointEvenLowGram22
      evenNegativePerturbation00 evenNegativePerturbation02
      evenNegativePerturbation22 := by
  let m00 : ℝ := evenNegativePerturbation00 - evenSlopeKernel00
  let m02 : ℝ := evenNegativePerturbation02 - evenSlopeKernel02
  let m22 : ℝ := evenNegativePerturbation22 - evenSlopeKernel22
  have hMquad : ∀ c d : ℝ,
      0 ≤ m00 * c ^ 2 + 2 * m02 * c * d + m22 * d ^ 2 := by
    intro c d
    simpa only [m00, m02, m22] using
      evenNegativePerturbation_sub_slopeKernel_nonneg c d
  have hMcoeff := twoByTwo_coefficients_nonneg_of_quadratic_nonneg
    m00 m02 m22 hMquad
  have hCMixed := twoByTwo_mixedDet_nonneg_of_quadratics_nonneg
    yoshidaEndpointEvenLowGram00 yoshidaEndpointEvenLowGram02
    yoshidaEndpointEvenLowGram22 m00 m02 m22
    intrinsicEven_clean_quadratic_nonneg hMquad
  have hLMixed := twoByTwo_mixedDet_nonneg_of_quadratics_nonneg
    evenSlopeKernel00 evenSlopeKernel02 evenSlopeKernel22 m00 m02 m22
    evenSlopeKernel_quadratic_nonneg hMquad
  have hbase := intrinsicEven_clean_slopeKernel_margin_pos
  dsimp only [m00, m02, m22] at hMcoeff hCMixed hLMixed
  unfold determinantSlopeMargin at hbase ⊢
  nlinarith

/-! ## Exact determinant derivative and unconditional Step23 slope -/

/-- The desired endpoint determinant slope differs from zero by exactly one
quarter of the complete clean/negative-perturbation mixed-determinant
margin. -/
theorem evenStep23DeterminantSlope_gap_eq_margin :
    (factorTwoIntrinsicEvenDetCoefficient0 +
          2 * factorTwoIntrinsicEvenDetCoefficient1 +
          3 * factorTwoIntrinsicEvenDetCoefficient2) -
        (7 / 4 : ℝ) * factorTwoIntrinsicEvenPhaseDet (-1) =
      (1 / 4 : ℝ) * determinantSlopeMargin
        yoshidaEndpointEvenLowGram00 yoshidaEndpointEvenLowGram02
        yoshidaEndpointEvenLowGram22
        evenNegativePerturbation00 evenNegativePerturbation02
        evenNegativePerturbation22 := by
  unfold factorTwoIntrinsicEvenDetCoefficient0
    factorTwoIntrinsicEvenDetCoefficient1
    factorTwoIntrinsicEvenDetCoefficient2
    factorTwoIntrinsicEvenPhaseDet
    factorTwoIntrinsicEvenDirection00
    factorTwoIntrinsicEvenDirection02
    factorTwoIntrinsicEvenDirection22
    factorTwoStructuralPhaseLow00
    factorTwoStructuralPhaseLow02
    factorTwoStructuralPhaseLow22
    evenNegativePerturbation00 evenNegativePerturbation02
    evenNegativePerturbation22 determinantSlopeMargin
  ring

/-- Unconditional structural proof of the sole even scalar isolated by the
endpoint Step23 argument. -/
theorem evenStep23DeterminantSlope : EvenStep23DeterminantSlope := by
  have hmargin := intrinsicEven_clean_negativePerturbation_margin_pos
  have hgap := evenStep23DeterminantSlope_gap_eq_margin
  unfold EvenStep23DeterminantSlope
  nlinarith

/-- Consequently the complete final intrinsic Bernstein difference is
nonnegative, with all odd and alternating terms still coupled. -/
theorem factorTwoIntrinsicBoundaryControlStep23_nonneg_structural
    (c d : ℝ) :
    0 ≤ factorTwoIntrinsicBoundaryControlStep23 c d :=
  factorTwoIntrinsicBoundaryControlStep23_nonneg_of_evenSlope
    evenStep23DeterminantSlope c d

theorem factorTwoIntrinsicBoundaryControlStep23_nonneg_structural_all :
    ∀ c d : ℝ, 0 ≤ factorTwoIntrinsicBoundaryControlStep23 c d :=
  factorTwoIntrinsicBoundaryControlStep23_nonneg_structural

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowControlStep23EvenSlopeStructural

import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcretePerturbationMoments
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseRankLimit
import ArithmeticHodge.Analysis.YoshidaMomentSeries

set_option autoImplicit false
set_option maxRecDepth 100000

open Filter MeasureTheory Real Set Topology
open scoped BigOperators Interval

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhasePerturbationMomentSeries

noncomputable section

open ArithmeticHodge.Analysis
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoEndpointParityPencil
open YoshidaFactorTwoPhaseConcreteEvenPerturbationAdaptation
open YoshidaFactorTwoPhaseConcretePerturbationMoments
open YoshidaFactorTwoPhaseRankLimit
open YoshidaFactorTwoPhaseSymmetricCoercivity
open YoshidaEndpointHyperbolicBound
open YoshidaMomentSeries
open YoshidaOddGramPrefix
open YoshidaRenormalizedGeometricKernel

/-!
# Dyadic Cauchy series for the factor-two sine moment

This file evaluates the first primitive perturbation-moment family.  The
singular symmetric weight is approached by its finite hyperbolic-rank
expansion; dominated convergence is performed before the resulting elementary
Laplace integrals are rewritten in dyadic form.
-/

/-- The full factor-two logarithmic length `L = log 2`. -/
def factorTwoMomentLength : ℝ := 2 * yoshidaEndpointA

/-- Dimensionless Fourier frequency `y_n = pi n / L`. -/
def factorTwoMomentY (n : ℕ) : ℝ :=
  factorTwoNaturalFrequency n / factorTwoMomentLength

/-- Half-odd Cauchy abscissae.  The decaying ranks use `j ≥ 1`; `j = 0`
is the growing head rank. -/
def factorTwoCauchyX (j : ℕ) : ℝ := (j : ℝ) + 1 / 4

/-- Exact dyadic endpoint exponential `q_j`. -/
def factorTwoDyadicQ (j : ℕ) : ℝ :=
  (Real.sqrt 2)⁻¹ / (4 : ℝ) ^ j

/-- Exact positive dyadic rank coefficient. -/
def factorTwoDyadicD (j : ℕ) : ℝ :=
  (1 - factorTwoDyadicQ j) ^ 2

/-- The growing-head defect. -/
def factorTwoHeadDefect : ℝ := (Real.sqrt 2 - 1) ^ 2

/-- The `j`th positive Cauchy rank, with the intended use `j ≥ 1`. -/
def factorTwoSymmetricSinDyadicTerm (n j : ℕ) : ℝ :=
  (1 / 2 : ℝ) * factorTwoDyadicD j * factorTwoMomentY n /
    (factorTwoCauchyX j ^ 2 + factorTwoMomentY n ^ 2)

/-- The archimedean sine transform before the retained prime atoms. -/
def factorTwoSymmetricSinArchMoment (n : ℕ) : ℝ :=
  yoshidaEndpointA *
    ∫ t : ℝ in 0..2,
      factorTwoSymmetricWeight (yoshidaEndpointA * t) *
        Real.sin (factorTwoNaturalFrequency n * t)

/-- Its finite hyperbolic-rank approximation. -/
def factorTwoSymmetricSinArchPartial (n N : ℕ) : ℝ :=
  yoshidaEndpointA *
    ∫ t : ℝ in 0..2,
      factorTwoSymmetricRankPartialWeight N t *
        Real.sin (factorTwoNaturalFrequency n * t)

theorem factorTwoMomentLength_eq_yoshidaLength :
    factorTwoMomentLength = yoshidaLength := by
  unfold factorTwoMomentLength yoshidaEndpointA yoshidaLength
  ring

theorem factorTwoMomentLength_pos : 0 < factorTwoMomentLength := by
  unfold factorTwoMomentLength
  exact mul_pos (by norm_num) yoshidaEndpointA_pos

theorem exp_yoshidaEndpointA_eq_sqrt_two :
    Real.exp yoshidaEndpointA = Real.sqrt 2 := by
  have hsqExp : Real.exp yoshidaEndpointA ^ 2 = 2 := by
    rw [pow_two, ← Real.exp_add]
    rw [show yoshidaEndpointA + yoshidaEndpointA = Real.log 2 by
      unfold yoshidaEndpointA
      ring]
    rw [Real.exp_log (by norm_num)]
  have hsqrtSq : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  nlinarith [Real.exp_pos yoshidaEndpointA, Real.sqrt_nonneg 2]

theorem exp_neg_mul_cosh_sub_one (z : ℝ) :
    Real.exp (-z) * (Real.cosh z - 1) =
      (1 - Real.exp (-z)) ^ 2 / 2 := by
  rw [Real.cosh_eq, Real.exp_neg]
  field_simp [Real.exp_ne_zero]
  ring

theorem factorTwoNaturalFrequency_mul_two_sin (n : ℕ) :
    Real.sin (factorTwoNaturalFrequency n * 2) = 0 := by
  rw [show factorTwoNaturalFrequency n * 2 =
      (2 * n : ℕ) * Real.pi by
    unfold factorTwoNaturalFrequency
    push_cast
    ring]
  exact Real.sin_nat_mul_pi (2 * n)

theorem factorTwoNaturalFrequency_mul_two_cos (n : ℕ) :
    Real.cos (factorTwoNaturalFrequency n * 2) = 1 := by
  rw [show factorTwoNaturalFrequency n * 2 =
      (2 * n : ℕ) * Real.pi by
    unfold factorTwoNaturalFrequency
    push_cast
    ring,
    Real.cos_nat_mul_pi, pow_mul]
  norm_num

/-- Elementary complete-period hyperbolic sine transform. -/
theorem integral_cosh_mul_factorTwoSin
    {n : ℕ} (hn : n ≠ 0) (lambda : ℝ) :
    (∫ t : ℝ in 0..2,
      Real.cosh (lambda * t) *
        Real.sin (factorTwoNaturalFrequency n * t)) =
      factorTwoNaturalFrequency n * (1 - Real.cosh (2 * lambda)) /
        (lambda ^ 2 + factorTwoNaturalFrequency n ^ 2) := by
  have hw : factorTwoNaturalFrequency n ≠ 0 := by
    unfold factorTwoNaturalFrequency
    exact mul_ne_zero Real.pi_ne_zero (Nat.cast_ne_zero.mpr hn)
  have hdenPos : lambda ^ 2 + factorTwoNaturalFrequency n ^ 2 ≠ 0 := by
    positivity
  have hpos := integral_exp_neg_mul_sin hdenPos
    (factorTwoNaturalFrequency_mul_two_sin n)
    (factorTwoNaturalFrequency_mul_two_cos n)
    (b := lambda) (L := 2) (κ := factorTwoNaturalFrequency n)
  have hnegDen : (-lambda) ^ 2 + factorTwoNaturalFrequency n ^ 2 ≠ 0 := by
    positivity
  have hneg := integral_exp_neg_mul_sin hnegDen
    (factorTwoNaturalFrequency_mul_two_sin n)
    (factorTwoNaturalFrequency_mul_two_cos n)
    (b := -lambda) (L := 2) (κ := factorTwoNaturalFrequency n)
  rw [show (fun t : ℝ ↦
      Real.cosh (lambda * t) *
        Real.sin (factorTwoNaturalFrequency n * t)) =
      fun t ↦ (1 / 2 : ℝ) *
        (Real.exp (-(-lambda) * t) *
            Real.sin (factorTwoNaturalFrequency n * t) +
          Real.exp (-lambda * t) *
            Real.sin (factorTwoNaturalFrequency n * t)) by
    funext t
    rw [Real.cosh_eq]
    rw [show - -lambda * t = lambda * t by ring,
      show -(lambda * t) = -lambda * t by ring]
    ring,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add
      (Continuous.intervalIntegrable (by fun_prop) 0 2)
      (Continuous.intervalIntegrable (by fun_prop) 0 2),
    hneg, hpos]
  rw [show -(-lambda) * 2 = 2 * lambda by ring,
    show -lambda * 2 = -(2 * lambda) by ring,
    Real.cosh_eq, Real.exp_neg]
  field_simp [hdenPos, hnegDen, Real.exp_ne_zero]
  ring

private theorem factorTwoRankPartialTail_le_tsum
    {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t < 2) (N : ℕ) :
    (∑ m ∈ Finset.range N,
      2 * Real.exp
          (-2 * yoshidaEndpointA * oddRate (m + 1)) *
        Real.cosh
          (yoshidaEndpointA * oddRate (m + 1) * t)) ≤
      ∑' m : ℕ,
        2 * Real.exp
            (-2 * yoshidaEndpointA * oddRate (m + 1)) *
          Real.cosh
            (yoshidaEndpointA * oddRate (m + 1) * t) := by
  have hs := summable_factorTwoSymmetricRankTail ht0 ht2
  apply hs.sum_le_tsum (Finset.range N)
  intro m _hm
  positivity

/-- Dominated passage from the finite hyperbolic ranks to the singular
symmetric sine transform. -/
theorem factorTwoSymmetricSinArchPartial_tendsto
    (n : FactorTwoCanonicalEvenIndex) (hn : n.1 ≠ 0) :
    Tendsto (fun N : ℕ ↦ factorTwoSymmetricSinArchPartial n.1 N)
      atTop (nhds (factorTwoSymmetricSinArchMoment n.1)) := by
  let C : ℝ → ℝ := fun t ↦
    Real.sin (factorTwoNaturalFrequency n.1 * t)
  let H : ℝ → ℝ := fun t ↦
    2 * Real.exp yoshidaEndpointA *
      Real.cosh (yoshidaEndpointA * t / 2)
  let W : ℝ → ℝ := fun t ↦
    factorTwoSymmetricWeight (yoshidaEndpointA * t)
  let F : ℕ → ℝ → ℝ := fun N t ↦
    factorTwoSymmetricRankPartialWeight N t * C t
  let B : ℝ → ℝ := fun t ↦
    2 * |H t * C t| + |W t * C t|
  have hHead : IntervalIntegrable (fun t : ℝ ↦ H t * C t)
      volume 0 2 := by
    apply Continuous.intervalIntegrable
    dsimp only [H, C]
    fun_prop
  have hWeight : IntervalIntegrable (fun t : ℝ ↦ W t * C t)
      volume 0 2 := by
    simpa only [W, C] using
      intervalIntegrable_factorTwoSymmetricSinMoment n hn
  have hB : IntervalIntegrable B volume 0 2 := by
    dsimp only [B]
    exact (hHead.norm.const_mul 2).add hWeight.norm
  have hFmeas : ∀ᶠ N in atTop,
      AEStronglyMeasurable (F N) (volume.restrict (Ι (0 : ℝ) 2)) := by
    filter_upwards [] with N
    apply Continuous.aestronglyMeasurable
    dsimp only [F, C, factorTwoSymmetricRankPartialWeight]
    fun_prop
  have hBound : ∀ᶠ N in atTop, ∀ᵐ t ∂volume,
      t ∈ Ι (0 : ℝ) 2 → ‖F N t‖ ≤ B t := by
    filter_upwards [] with N
    filter_upwards [MeasureTheory.Measure.ae_ne volume (2 : ℝ)] with t ht2
    intro ht
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 2)] at ht
    have ht0 : 0 ≤ t := ht.1.le
    have htlt2 : t < 2 := lt_of_le_of_ne ht.2 ht2
    let S : ℝ := ∑ m ∈ Finset.range N,
      2 * Real.exp
          (-2 * yoshidaEndpointA * oddRate (m + 1)) *
        Real.cosh
          (yoshidaEndpointA * oddRate (m + 1) * t)
    let T : ℝ := ∑' m : ℕ,
      2 * Real.exp
          (-2 * yoshidaEndpointA * oddRate (m + 1)) *
        Real.cosh
          (yoshidaEndpointA * oddRate (m + 1) * t)
    have hS0 : 0 ≤ S := by
      dsimp only [S]
      positivity
    have hST : S ≤ T := by
      simpa only [S, T] using
        factorTwoRankPartialTail_le_tsum ht0 htlt2 N
    have hT0 : 0 ≤ T := hS0.trans hST
    have hSC : |S * C t| ≤ |T * C t| := by
      rw [abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_right
        (by simpa only [abs_of_nonneg hS0, abs_of_nonneg hT0] using hST)
        (abs_nonneg (C t))
    have hseries := factorTwoSymmetricWeight_eq_rankOneSeries ht0 htlt2
    change W t = H t - T at hseries
    have hTC : |T * C t| ≤ |H t * C t| + |W t * C t| := by
      have htri := abs_sub (H t * C t) (W t * C t)
      rw [show H t * C t - W t * C t = T * C t by
        rw [hseries]
        ring] at htri
      exact htri
    dsimp only [F, B, factorTwoSymmetricRankPartialWeight]
    change ‖(H t - S) * C t‖ ≤ 2 * |H t * C t| + |W t * C t|
    rw [Real.norm_eq_abs, sub_mul]
    calc
      |H t * C t - S * C t| ≤
          |H t * C t| + |S * C t| := abs_sub _ _
      _ ≤ |H t * C t| + |T * C t| :=
        add_le_add (le_refl _) hSC
      _ ≤ 2 * |H t * C t| + |W t * C t| := by
        linarith
  have hLim : ∀ᵐ t ∂volume, t ∈ Ι (0 : ℝ) 2 →
      Tendsto (fun N : ℕ ↦ F N t) atTop (nhds (W t * C t)) := by
    filter_upwards [MeasureTheory.Measure.ae_ne volume (2 : ℝ)] with t ht2
    intro ht
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 2)] at ht
    have htlt2 : t < 2 := lt_of_le_of_ne ht.2 ht2
    have hweight := factorTwoSymmetricRankPartialWeight_tendsto ht.1.le htlt2
    exact hweight.mul_const (C t)
  have hIntegral :
      Tendsto (fun N : ℕ ↦ ∫ t : ℝ in 0..2, F N t) atTop
        (nhds (∫ t : ℝ in 0..2, W t * C t)) := by
    exact intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      B hFmeas hBound hB hLim
  have hScaled := hIntegral.const_mul yoshidaEndpointA
  simpa only [factorTwoSymmetricSinArchPartial,
    factorTwoSymmetricSinArchMoment, F, W, C] using hScaled

/-- Raw growing-rank contribution before the dyadic simplification. -/
def factorTwoSymmetricSinHeadRaw (n : ℕ) : ℝ :=
  yoshidaEndpointA * 2 * Real.exp yoshidaEndpointA *
    (factorTwoNaturalFrequency n *
      (1 - Real.cosh yoshidaEndpointA) /
      ((yoshidaEndpointA / 2) ^ 2 +
        factorTwoNaturalFrequency n ^ 2))

/-- Raw positive decaying-rank contribution. -/
def factorTwoSymmetricSinRankRaw (n m : ℕ) : ℝ :=
  yoshidaEndpointA * 2 *
    Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
    (factorTwoNaturalFrequency n *
      (Real.cosh (2 * yoshidaEndpointA * oddRate (m + 1)) - 1) /
      ((yoshidaEndpointA * oddRate (m + 1)) ^ 2 +
        factorTwoNaturalFrequency n ^ 2))

/-- Every finite hyperbolic approximation is already a finite Cauchy sum. -/
theorem factorTwoSymmetricSinArchPartial_eq_raw
    {n : ℕ} (hn : n ≠ 0) (N : ℕ) :
    factorTwoSymmetricSinArchPartial n N =
      factorTwoSymmetricSinHeadRaw n +
        ∑ m ∈ Finset.range N, factorTwoSymmetricSinRankRaw n m := by
  let omega := factorTwoNaturalFrequency n
  have hhead := integral_cosh_mul_factorTwoSin hn (yoshidaEndpointA / 2)
  have htail (m : ℕ) := integral_cosh_mul_factorTwoSin hn
    (yoshidaEndpointA * oddRate (m + 1))
  have hheadInt : IntervalIntegrable
      (fun t : ℝ ↦
        2 * Real.exp yoshidaEndpointA *
          Real.cosh (yoshidaEndpointA * t / 2) *
          Real.sin (factorTwoNaturalFrequency n * t)) volume 0 2 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have htailInt (m : ℕ) : IntervalIntegrable
      (fun t : ℝ ↦
        2 * Real.exp
            (-2 * yoshidaEndpointA * oddRate (m + 1)) *
          Real.cosh
            (yoshidaEndpointA * oddRate (m + 1) * t) *
          Real.sin (factorTwoNaturalFrequency n * t)) volume 0 2 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have htailSumInt : IntervalIntegrable
      (fun t : ℝ ↦ ∑ m ∈ Finset.range N,
        2 * Real.exp
            (-2 * yoshidaEndpointA * oddRate (m + 1)) *
          Real.cosh
            (yoshidaEndpointA * oddRate (m + 1) * t) *
          Real.sin (factorTwoNaturalFrequency n * t)) volume 0 2 := by
    apply Continuous.intervalIntegrable
    fun_prop
  unfold factorTwoSymmetricSinArchPartial
    factorTwoSymmetricRankPartialWeight
  have hpoint : (fun t : ℝ ↦
      (2 * Real.exp yoshidaEndpointA *
          Real.cosh (yoshidaEndpointA * t / 2) -
        ∑ m ∈ Finset.range N,
          2 * Real.exp
              (-2 * yoshidaEndpointA * oddRate (m + 1)) *
            Real.cosh
              (yoshidaEndpointA * oddRate (m + 1) * t)) *
        Real.sin (factorTwoNaturalFrequency n * t)) =
      fun t : ℝ ↦
        2 * Real.exp yoshidaEndpointA *
            Real.cosh (yoshidaEndpointA * t / 2) *
            Real.sin (factorTwoNaturalFrequency n * t) -
          ∑ m ∈ Finset.range N,
            2 * Real.exp
                (-2 * yoshidaEndpointA * oddRate (m + 1)) *
              Real.cosh
                (yoshidaEndpointA * oddRate (m + 1) * t) *
              Real.sin (factorTwoNaturalFrequency n * t) := by
    funext t
    simp only [sub_mul, Finset.sum_mul]
  rw [hpoint]
  rw [intervalIntegral.integral_sub hheadInt htailSumInt,
    intervalIntegral.integral_finset_sum
      (fun m _hm ↦ htailInt m)]
  rw [show (∫ t : ℝ in 0..2,
      2 * Real.exp yoshidaEndpointA *
        Real.cosh (yoshidaEndpointA * t / 2) *
        Real.sin (factorTwoNaturalFrequency n * t)) =
      2 * Real.exp yoshidaEndpointA *
        (∫ t : ℝ in 0..2,
          Real.cosh ((yoshidaEndpointA / 2) * t) *
          Real.sin (factorTwoNaturalFrequency n * t)) by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext t
    ring]
  rw [hhead]
  simp_rw [show ∀ m : ℕ,
      (∫ t : ℝ in 0..2,
        2 * Real.exp
            (-2 * yoshidaEndpointA * oddRate (m + 1)) *
          Real.cosh
            (yoshidaEndpointA * oddRate (m + 1) * t) *
          Real.sin (factorTwoNaturalFrequency n * t)) =
        2 * Real.exp
            (-2 * yoshidaEndpointA * oddRate (m + 1)) *
          (∫ t : ℝ in 0..2,
            Real.cosh
              ((yoshidaEndpointA * oddRate (m + 1)) * t) *
            Real.sin (factorTwoNaturalFrequency n * t)) by
    intro m
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext t
    ring]
  simp_rw [htail]
  unfold factorTwoSymmetricSinHeadRaw factorTwoSymmetricSinRankRaw
  rw [show 2 * (yoshidaEndpointA / 2) = yoshidaEndpointA by ring]
  have hsum :
      (∑ m ∈ Finset.range N,
        yoshidaEndpointA * 2 *
          Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
          (factorTwoNaturalFrequency n *
            (Real.cosh (2 * yoshidaEndpointA * oddRate (m + 1)) - 1) /
            ((yoshidaEndpointA * oddRate (m + 1)) ^ 2 +
              factorTwoNaturalFrequency n ^ 2))) =
        -yoshidaEndpointA *
          ∑ m ∈ Finset.range N,
            2 * Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
              (factorTwoNaturalFrequency n *
                (1 - Real.cosh
                  (2 * (yoshidaEndpointA * oddRate (m + 1)))) /
                ((yoshidaEndpointA * oddRate (m + 1)) ^ 2 +
                  factorTwoNaturalFrequency n ^ 2)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _hm
    ring
  rw [hsum]
  ring

theorem factorTwoSymmetricSinRankRaw_nonneg
    {n : ℕ} (hn : n ≠ 0) (m : ℕ) :
    0 ≤ factorTwoSymmetricSinRankRaw n m := by
  have hw : 0 < factorTwoNaturalFrequency n := by
    unfold factorTwoNaturalFrequency
    positivity
  have hcosh : 1 ≤
      Real.cosh (2 * yoshidaEndpointA * oddRate (m + 1)) :=
    Real.one_le_cosh _
  have hdiff : 0 ≤
      Real.cosh (2 * yoshidaEndpointA * oddRate (m + 1)) - 1 :=
    sub_nonneg.mpr hcosh
  unfold factorTwoSymmetricSinRankRaw
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg yoshidaEndpointA_pos.le (by norm_num))
      (Real.exp_nonneg _))
    (div_nonneg (mul_nonneg hw.le hdiff) (by positivity))

/-- The decaying raw ranks have the sum forced by the dominated integral
limit. -/
theorem hasSum_factorTwoSymmetricSinRankRaw
    (n : FactorTwoCanonicalEvenIndex) (hn : n.1 ≠ 0) :
    HasSum (factorTwoSymmetricSinRankRaw n.1)
      (factorTwoSymmetricSinArchMoment n.1 -
        factorTwoSymmetricSinHeadRaw n.1) := by
  have hlim := factorTwoSymmetricSinArchPartial_tendsto n hn
  have hsub := hlim.sub_const (factorTwoSymmetricSinHeadRaw n.1)
  apply (hasSum_iff_tendsto_nat_of_nonneg
    (factorTwoSymmetricSinRankRaw_nonneg hn) _).2
  convert hsub using 1
  funext N
  rw [factorTwoSymmetricSinArchPartial_eq_raw hn N]
  ring

/-- Honest infinite-series identity before the elementary dyadic
simplification. -/
theorem factorTwoSymmetricSinArchMoment_eq_raw_tsum
    (n : FactorTwoCanonicalEvenIndex) (hn : n.1 ≠ 0) :
    factorTwoSymmetricSinArchMoment n.1 =
      factorTwoSymmetricSinHeadRaw n.1 +
        ∑' m : ℕ, factorTwoSymmetricSinRankRaw n.1 m := by
  rw [(hasSum_factorTwoSymmetricSinRankRaw n hn).tsum_eq]
  ring

/-- The growing rank is the negative `j = 0` Cauchy defect. -/
theorem factorTwoSymmetricSinHeadRaw_eq_dyadic (n : ℕ) :
    factorTwoSymmetricSinHeadRaw n =
      -(factorTwoHeadDefect / 2) * factorTwoMomentY n /
        (factorTwoCauchyX 0 ^ 2 + factorTwoMomentY n ^ 2) := by
  have hsqrtPos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrtSq : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hcoef : Real.sqrt 2 * (1 - Real.cosh yoshidaEndpointA) =
      -((Real.sqrt 2 - 1) ^ 2) / 2 := by
    rw [Real.cosh_eq, Real.exp_neg,
      exp_yoshidaEndpointA_eq_sqrt_two]
    field_simp [hsqrtPos.ne']
    nlinarith
  have hdenRaw : (yoshidaEndpointA / 2) ^ 2 +
      factorTwoNaturalFrequency n ^ 2 ≠ 0 := by
    have hA : 0 < (yoshidaEndpointA / 2) ^ 2 :=
      sq_pos_of_pos (div_pos yoshidaEndpointA_pos (by norm_num))
    positivity
  have hdenScaled : ((0 : ℝ) + 1 / 4) ^ 2 +
      (factorTwoNaturalFrequency n / (2 * yoshidaEndpointA)) ^ 2 ≠ 0 := by
    have hx : 0 < ((0 : ℝ) + 1 / 4) ^ 2 := by norm_num
    positivity
  calc
    factorTwoSymmetricSinHeadRaw n =
        yoshidaEndpointA * 2 *
          (Real.sqrt 2 * (1 - Real.cosh yoshidaEndpointA)) *
          factorTwoNaturalFrequency n /
          ((yoshidaEndpointA / 2) ^ 2 +
            factorTwoNaturalFrequency n ^ 2) := by
      unfold factorTwoSymmetricSinHeadRaw
      rw [exp_yoshidaEndpointA_eq_sqrt_two]
      ring
    _ = yoshidaEndpointA * 2 *
          (-((Real.sqrt 2 - 1) ^ 2) / 2) *
          factorTwoNaturalFrequency n /
          ((yoshidaEndpointA / 2) ^ 2 +
            factorTwoNaturalFrequency n ^ 2) := by rw [hcoef]
    _ = _ := by
      have hD1 : factorTwoNaturalFrequency n ^ 2 * 4 +
          yoshidaEndpointA ^ 2 ≠ 0 := by
        have hA : 0 < yoshidaEndpointA ^ 2 :=
          sq_pos_of_pos yoshidaEndpointA_pos
        positivity
      have hD2 : factorTwoNaturalFrequency n ^ 2 * 16 +
          yoshidaEndpointA ^ 2 * 4 ≠ 0 := by
        have hA : 0 < yoshidaEndpointA ^ 2 * 4 :=
          mul_pos (sq_pos_of_pos yoshidaEndpointA_pos) (by norm_num)
        positivity
      have hE1 : yoshidaEndpointA ^ 2 + 2 ^ 2 *
          factorTwoNaturalFrequency n ^ 2 ≠ 0 := by
        have hA : 0 < yoshidaEndpointA ^ 2 :=
          sq_pos_of_pos yoshidaEndpointA_pos
        positivity
      have hE2 : yoshidaEndpointA ^ 2 * 2 ^ 2 +
          factorTwoNaturalFrequency n ^ 2 * 16 ≠ 0 := by
        have hA : 0 < yoshidaEndpointA ^ 2 * 2 ^ 2 :=
          mul_pos (sq_pos_of_pos yoshidaEndpointA_pos) (by norm_num)
        positivity
      unfold factorTwoHeadDefect factorTwoMomentY factorTwoMomentLength
        factorTwoCauchyX
      norm_num only [Nat.cast_zero, zero_add]
      field_simp [yoshidaEndpointA_pos.ne', hdenRaw, hdenScaled, hD1, hD2]
      field_simp [hE1, hE2]
      ring

/-- Every decaying hyperbolic rank is exactly one positive dyadic Cauchy
term; rank `m` corresponds to Cauchy index `m + 1`. -/
theorem factorTwoSymmetricSinRankRaw_eq_dyadic
    (n m : ℕ) :
    factorTwoSymmetricSinRankRaw n m =
      factorTwoSymmetricSinDyadicTerm n (m + 1) := by
  let r : ℝ := oddRate (m + 1)
  let q : ℝ := Real.exp (-2 * yoshidaEndpointA * r)
  have hL : factorTwoMomentLength = yoshidaLength :=
    factorTwoMomentLength_eq_yoshidaLength
  have hL0 : factorTwoMomentLength ≠ 0 := factorTwoMomentLength_pos.ne'
  have hq : q = factorTwoDyadicQ (m + 1) := by
    dsimp only [q]
    rw [show -2 * yoshidaEndpointA * r =
        -r * yoshidaLength by
      rw [← hL]
      unfold factorTwoMomentLength
      ring]
    dsimp only [r]
    rw [exp_neg_oddRate_mul_length]
    rfl
  have hxr : yoshidaEndpointA * r =
      factorTwoMomentLength * factorTwoCauchyX (m + 1) := by
    dsimp only [r]
    unfold factorTwoMomentLength factorTwoCauchyX oddRate
    push_cast
    ring
  have hwy : factorTwoNaturalFrequency n =
      factorTwoMomentLength * factorTwoMomentY n := by
    unfold factorTwoMomentY
    field_simp [hL0]
  have hpair : q * (Real.cosh (2 * yoshidaEndpointA * r) - 1) =
      factorTwoDyadicD (m + 1) / 2 := by
    rw [show q = Real.exp (-(2 * yoshidaEndpointA * r)) by
      dsimp only [q]
      congr 1
      ring,
      exp_neg_mul_cosh_sub_one]
    unfold factorTwoDyadicD
    rw [← hq]
    rw [show Real.exp (-(2 * yoshidaEndpointA * r)) = q by
      dsimp only [q]
      congr 1
      ring]
  have hx : 0 < factorTwoCauchyX (m + 1) := by
    unfold factorTwoCauchyX
    positivity
  have hdenScaled : factorTwoCauchyX (m + 1) ^ 2 +
      factorTwoMomentY n ^ 2 ≠ 0 := by
    have hxsq : 0 < factorTwoCauchyX (m + 1) ^ 2 :=
      sq_pos_of_pos hx
    positivity
  calc
    factorTwoSymmetricSinRankRaw n m =
        yoshidaEndpointA * 2 *
          (q * (Real.cosh (2 * yoshidaEndpointA * r) - 1)) *
          factorTwoNaturalFrequency n /
          ((yoshidaEndpointA * r) ^ 2 +
            factorTwoNaturalFrequency n ^ 2) := by
      unfold factorTwoSymmetricSinRankRaw
      dsimp only [q, r]
      ring
    _ = yoshidaEndpointA * 2 *
          (factorTwoDyadicD (m + 1) / 2) *
          factorTwoNaturalFrequency n /
          ((yoshidaEndpointA * r) ^ 2 +
            factorTwoNaturalFrequency n ^ 2) := by rw [hpair]
    _ = _ := by
      rw [hxr, hwy]
      unfold factorTwoSymmetricSinDyadicTerm
      have hA : yoshidaEndpointA = factorTwoMomentLength / 2 := by
        unfold factorTwoMomentLength
        ring
      rw [hA]
      field_simp [hL0, hdenScaled]

/-- The archimedean primitive sine moment as one negative head term followed
by the exact positive dyadic Cauchy series. -/
theorem factorTwoSymmetricSinArchMoment_eq_dyadicCauchySeries
    (n : FactorTwoCanonicalEvenIndex) (hn : n.1 ≠ 0) :
    factorTwoSymmetricSinArchMoment n.1 =
      -(factorTwoHeadDefect / 2) * factorTwoMomentY n.1 /
          (factorTwoCauchyX 0 ^ 2 + factorTwoMomentY n.1 ^ 2) +
        ∑' m : ℕ, factorTwoSymmetricSinDyadicTerm n.1 (m + 1) := by
  rw [factorTwoSymmetricSinArchMoment_eq_raw_tsum n hn,
    factorTwoSymmetricSinHeadRaw_eq_dyadic]
  congr 1
  apply tsum_congr
  intro m
  exact factorTwoSymmetricSinRankRaw_eq_dyadic n.1 m

/-- Full symmetric sine perturbation moment, including the exact retained
`p = 3` atom.  The `p = 2` atom vanishes at zero. -/
theorem factorTwoSymmetricSinMoment_eq_dyadicCauchySeries
    (n : FactorTwoCanonicalEvenIndex) (hn : n.1 ≠ 0) :
    factorTwoSymmetricSinMoment n.1 =
      -(factorTwoHeadDefect / 2) * factorTwoMomentY n.1 /
          (factorTwoCauchyX 0 ^ 2 + factorTwoMomentY n.1 ^ 2) +
        ∑' m : ℕ, factorTwoSymmetricSinDyadicTerm n.1 (m + 1) -
        (Real.log 3 / Real.sqrt 3) *
          Real.sin
            (2 * factorTwoMomentY n.1 * factorTwoPrimeShift) := by
  have harg : factorTwoNaturalFrequency n.1 *
        (factorTwoPrimeShift / yoshidaEndpointA) =
      2 * factorTwoMomentY n.1 * factorTwoPrimeShift := by
    unfold factorTwoMomentY factorTwoMomentLength
    field_simp [yoshidaEndpointA_pos.ne']
  unfold factorTwoSymmetricSinMoment
    factorTwoSymmetricPerturbationFunctional
  change factorTwoSymmetricSinArchMoment n.1 -
      (Real.log 2 / Real.sqrt 2) *
        Real.sin (factorTwoNaturalFrequency n.1 * 0) -
      (Real.log 3 / Real.sqrt 3) *
        Real.sin (factorTwoNaturalFrequency n.1 *
          (factorTwoPrimeShift / yoshidaEndpointA)) = _
  rw [factorTwoSymmetricSinArchMoment_eq_dyadicCauchySeries n hn,
    harg]
  simp only [mul_zero, Real.sin_zero]
  ring

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhasePerturbationMomentSeries

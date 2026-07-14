import ArithmeticHodge.Analysis.YoshidaFactorTwoPhasePerturbationMomentSeries

set_option autoImplicit false
set_option maxRecDepth 100000

open Filter MeasureTheory Real Set Topology
open scoped BigOperators Interval

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhasePerturbationAffineCosSeries

noncomputable section

open ArithmeticHodge.Analysis
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoEndpointParityPencil
open YoshidaFactorTwoPhaseConcreteEvenPerturbationAdaptation
open YoshidaFactorTwoPhaseConcretePerturbationMoments
open YoshidaFactorTwoPhasePerturbationMomentSeries
open YoshidaFactorTwoPhaseRankLimit
open YoshidaFactorTwoPhaseSymmetricCoercivity
open YoshidaEndpointHyperbolicBound
open YoshidaMomentSeries
open YoshidaOddGramPrefix
open YoshidaRenormalizedGeometricKernel

/-!
# Dyadic Cauchy series for the factor-two affine cosine moment

The endpoint factor `2 - t` cancels the singular endpoint of the symmetric
weight.  We first pass honestly through finite hyperbolic-rank approximations,
then evaluate every rank by a complete-period affine-cosine transform.  Unlike
the sine series, these ranks change sign, so the final passage to a `tsum` uses
an explicit absolutely summable quadratic majorant.
-/

/-- The signed derivative-type Cauchy kernel. -/
def factorTwoCauchyT (x y : ℝ) : ℝ :=
  (x ^ 2 - y ^ 2) / (x ^ 2 + y ^ 2) ^ 2

/-- A decaying dyadic affine-cosine rank, before its common coefficient. -/
def factorTwoSymmetricAffineCosDyadicKernel (n j : ℕ) : ℝ :=
  factorTwoDyadicD j *
    factorTwoCauchyT (factorTwoCauchyX j) (factorTwoMomentY n)

/-- The archimedean affine-cosine transform before the retained prime atoms. -/
def factorTwoSymmetricAffineCosArchMoment (n : ℕ) : ℝ :=
  yoshidaEndpointA *
    ∫ t : ℝ in 0..2,
      factorTwoSymmetricWeight (yoshidaEndpointA * t) *
        ((2 - t) * Real.cos (factorTwoNaturalFrequency n * t))

/-- Its finite hyperbolic-rank approximation. -/
def factorTwoSymmetricAffineCosArchPartial (n N : ℕ) : ℝ :=
  yoshidaEndpointA *
    ∫ t : ℝ in 0..2,
      factorTwoSymmetricRankPartialWeight N t *
        ((2 - t) * Real.cos (factorTwoNaturalFrequency n * t))

private def affineCosRampPrimitive (b kappa L u : ℝ) : ℝ :=
  (1 - u / L) * Real.exp (b * u) *
      (b * Real.cos (kappa * u) + kappa * Real.sin (kappa * u)) /
        (b ^ 2 + kappa ^ 2) +
    Real.exp (b * u) *
      ((b ^ 2 - kappa ^ 2) * Real.cos (kappa * u) +
        2 * b * kappa * Real.sin (kappa * u)) /
      (L * (b ^ 2 + kappa ^ 2) ^ 2)

private theorem affineCosRampPrimitive_hasDerivAt
    {b kappa L u : ℝ} (hL : L ≠ 0)
    (hden : b ^ 2 + kappa ^ 2 ≠ 0) :
    HasDerivAt (affineCosRampPrimitive b kappa L)
      (Real.exp (b * u) * (1 - u / L) * Real.cos (kappa * u)) u := by
  have hbu : HasDerivAt (fun x : ℝ ↦ b * x) b u := by
    simpa using (hasDerivAt_id u).const_mul b
  have hku : HasDerivAt (fun x : ℝ ↦ kappa * x) kappa u := by
    simpa using (hasDerivAt_id u).const_mul kappa
  have hexp : HasDerivAt (fun x : ℝ ↦ Real.exp (b * x))
      (Real.exp (b * u) * b) u :=
    Real.hasDerivAt_exp (b * u) |>.comp u hbu
  have hsin : HasDerivAt (fun x : ℝ ↦ Real.sin (kappa * x))
      (Real.cos (kappa * u) * kappa) u :=
    Real.hasDerivAt_sin (kappa * u) |>.comp u hku
  have hcos : HasDerivAt (fun x : ℝ ↦ Real.cos (kappa * x))
      (-Real.sin (kappa * u) * kappa) u := by
    simpa only [Function.comp_apply] using
      (Real.hasDerivAt_cos (kappa * u) |>.comp u hku)
  have hramp : HasDerivAt (fun x : ℝ ↦ 1 - x / L) (-(1 / L)) u := by
    simpa only [zero_sub] using
      (hasDerivAt_const u (1 : ℝ)).sub ((hasDerivAt_id u).div_const L)
  have hacos : HasDerivAt
      (fun x : ℝ ↦ b * Real.cos (kappa * x) +
        kappa * Real.sin (kappa * x))
      (b * (-Real.sin (kappa * u) * kappa) +
        kappa * (Real.cos (kappa * u) * kappa)) u :=
    (hcos.const_mul b).add (hsin.const_mul kappa)
  have hg : HasDerivAt
      (fun x : ℝ ↦ (b ^ 2 - kappa ^ 2) * Real.cos (kappa * x) +
        2 * b * kappa * Real.sin (kappa * x))
      ((b ^ 2 - kappa ^ 2) * (-Real.sin (kappa * u) * kappa) +
        2 * b * kappa * (Real.cos (kappa * u) * kappa)) u :=
    (hcos.const_mul (b ^ 2 - kappa ^ 2)).add
      (hsin.const_mul (2 * b * kappa))
  convert ((((hramp.mul hexp).mul hacos).div_const
      (b ^ 2 + kappa ^ 2)).add
    ((hexp.mul hg).div_const (L * (b ^ 2 + kappa ^ 2) ^ 2))) using 1
  simp only [Pi.mul_apply]
  field_simp [hL, hden]
  ring

private theorem integral_exp_mul_affineCosRamp_periodic
    {b kappa L : ℝ} (hL : L ≠ 0)
    (hden : b ^ 2 + kappa ^ 2 ≠ 0)
    (hsin : Real.sin (kappa * L) = 0)
    (hcos : Real.cos (kappa * L) = 1) :
    (∫ u in 0..L,
        Real.exp (b * u) * (1 - u / L) * Real.cos (kappa * u)) =
      ((Real.exp (b * L) - 1 - b * L) * (b ^ 2 - kappa ^ 2) -
          2 * b * kappa ^ 2 * L) /
        (L * (b ^ 2 + kappa ^ 2) ^ 2) := by
  have hderiv : ∀ u ∈ Set.uIcc (0 : ℝ) L,
      HasDerivAt (affineCosRampPrimitive b kappa L)
        (Real.exp (b * u) * (1 - u / L) * Real.cos (kappa * u)) u :=
    fun u _ ↦ affineCosRampPrimitive_hasDerivAt hL hden
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (Continuous.intervalIntegrable (by fun_prop) 0 L)
  rw [h]
  simp only [affineCosRampPrimitive, mul_zero, zero_div, sub_zero,
    Real.exp_zero, Real.sin_zero, Real.cos_zero, hsin, hcos]
  field_simp [hL, hden]
  ring

/-- Complete-period affine-cosine transform.  It includes the zero Fourier
mode; only the hyperbolic rate must be nonzero. -/
theorem integral_cosh_mul_factorTwoAffineCos
    (n : ℕ) {lambda : ℝ} (hlambda : lambda ≠ 0) :
    (∫ t : ℝ in 0..2,
      Real.cosh (lambda * t) *
        ((2 - t) * Real.cos (factorTwoNaturalFrequency n * t))) =
      2 * Real.sinh lambda ^ 2 *
        factorTwoCauchyT lambda (factorTwoNaturalFrequency n) := by
  let omega := factorTwoNaturalFrequency n
  have hden : lambda ^ 2 + omega ^ 2 ≠ 0 := by
    have hlambdaSq : 0 < lambda ^ 2 := sq_pos_of_ne_zero hlambda
    positivity
  have hnegDen : (-lambda) ^ 2 + omega ^ 2 ≠ 0 := by
    have hlambdaSq : 0 < (-lambda) ^ 2 := sq_pos_of_ne_zero (neg_ne_zero.mpr hlambda)
    positivity
  have hpos := integral_exp_mul_affineCosRamp_periodic
    (by norm_num : (2 : ℝ) ≠ 0) hden
    (factorTwoNaturalFrequency_mul_two_sin n)
    (factorTwoNaturalFrequency_mul_two_cos n)
    (b := lambda) (kappa := omega) (L := 2)
  have hneg := integral_exp_mul_affineCosRamp_periodic
    (by norm_num : (2 : ℝ) ≠ 0) hnegDen
    (factorTwoNaturalFrequency_mul_two_sin n)
    (factorTwoNaturalFrequency_mul_two_cos n)
    (b := -lambda) (kappa := omega) (L := 2)
  have hposInt : IntervalIntegrable
      (fun t : ℝ ↦ Real.exp (lambda * t) *
        (1 - t / 2) * Real.cos (omega * t)) volume 0 2 :=
    by
      apply Continuous.intervalIntegrable
      fun_prop
  have hnegInt : IntervalIntegrable
      (fun t : ℝ ↦ Real.exp (-lambda * t) *
        (1 - t / 2) * Real.cos (omega * t)) volume 0 2 :=
    by
      apply Continuous.intervalIntegrable
      fun_prop
  rw [show (fun t : ℝ ↦
      Real.cosh (lambda * t) *
        ((2 - t) * Real.cos (factorTwoNaturalFrequency n * t))) =
      fun t ↦
        Real.exp (lambda * t) * (1 - t / 2) * Real.cos (omega * t) +
        Real.exp (-lambda * t) * (1 - t / 2) * Real.cos (omega * t) by
    funext t
    dsimp only [omega]
    rw [Real.cosh_eq]
    rw [show -(lambda * t) = -lambda * t by ring]
    ring,
    intervalIntegral.integral_add hposInt hnegInt,
    hpos, hneg]
  unfold factorTwoCauchyT
  dsimp only [omega]
  rw [show -lambda * 2 = -(lambda * 2) by ring,
    show (-lambda) ^ 2 = lambda ^ 2 by ring,
    Real.sinh_eq]
  rw [show Real.exp (lambda * 2) = Real.exp lambda ^ 2 by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring,
    show Real.exp (-(lambda * 2)) = Real.exp (-lambda) ^ 2 by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring]
  field_simp [hden, hnegDen, Real.exp_ne_zero]
  have hexpPair : Real.exp lambda * Real.exp (-lambda) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [show (Real.exp lambda - Real.exp (-lambda)) ^ 2 =
      Real.exp lambda ^ 2 + Real.exp (-lambda) ^ 2 - 2 by
    nlinarith]
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

/-- Dominated passage from finite hyperbolic ranks to the singular symmetric
affine-cosine transform.  The endpoint cancellation supplies integrability
also at the zero Fourier mode. -/
theorem factorTwoSymmetricAffineCosArchPartial_tendsto
    (n : FactorTwoCanonicalEvenIndex) :
    Tendsto (fun N : ℕ ↦ factorTwoSymmetricAffineCosArchPartial n.1 N)
      atTop (nhds (factorTwoSymmetricAffineCosArchMoment n.1)) := by
  let C : ℝ → ℝ := fun t ↦
    (2 - t) * Real.cos (factorTwoNaturalFrequency n.1 * t)
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
      intervalIntegrable_factorTwoSymmetricAffineCosMoment n
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
      have hAbsST : |S| ≤ |T| := by
        simpa only [abs_of_nonneg hS0, abs_of_nonneg hT0] using hST
      calc
        |S * C t| = |S| * |C t| := abs_mul _ _
        _ ≤ |T| * |C t| :=
          mul_le_mul_of_nonneg_right hAbsST (abs_nonneg (C t))
        _ = |T * C t| := (abs_mul _ _).symm
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
  simpa only [factorTwoSymmetricAffineCosArchPartial,
    factorTwoSymmetricAffineCosArchMoment, F, W, C] using hScaled

/-- Raw growing-rank affine-cosine contribution. -/
def factorTwoSymmetricAffineCosHeadRaw (n : ℕ) : ℝ :=
  yoshidaEndpointA * 2 * Real.exp yoshidaEndpointA *
    (2 * Real.sinh (yoshidaEndpointA / 2) ^ 2 *
      factorTwoCauchyT (yoshidaEndpointA / 2)
        (factorTwoNaturalFrequency n))

/-- Raw signed decaying-rank affine-cosine contribution. -/
def factorTwoSymmetricAffineCosRankRaw (n m : ℕ) : ℝ :=
  -yoshidaEndpointA * 2 *
    Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
    (2 * Real.sinh (yoshidaEndpointA * oddRate (m + 1)) ^ 2 *
      factorTwoCauchyT (yoshidaEndpointA * oddRate (m + 1))
        (factorTwoNaturalFrequency n))

/-- Every finite hyperbolic approximation is a finite sum of the raw signed
affine-cosine ranks. -/
theorem factorTwoSymmetricAffineCosArchPartial_eq_raw
    (n N : ℕ) :
    factorTwoSymmetricAffineCosArchPartial n N =
      factorTwoSymmetricAffineCosHeadRaw n +
        ∑ m ∈ Finset.range N, factorTwoSymmetricAffineCosRankRaw n m := by
  have hheadRate : yoshidaEndpointA / 2 ≠ 0 := by
    exact div_ne_zero yoshidaEndpointA_pos.ne' (by norm_num)
  have hhead := integral_cosh_mul_factorTwoAffineCos n hheadRate
  have htailRate (m : ℕ) :
      yoshidaEndpointA * oddRate (m + 1) ≠ 0 := by
    exact mul_ne_zero yoshidaEndpointA_pos.ne' (oddRate_pos _).ne'
  have htail (m : ℕ) :=
    integral_cosh_mul_factorTwoAffineCos n (htailRate m)
  have hheadInt : IntervalIntegrable
      (fun t : ℝ ↦
        2 * Real.exp yoshidaEndpointA *
          Real.cosh (yoshidaEndpointA * t / 2) *
          ((2 - t) * Real.cos (factorTwoNaturalFrequency n * t)))
      volume 0 2 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have htailInt (m : ℕ) : IntervalIntegrable
      (fun t : ℝ ↦
        2 * Real.exp
            (-2 * yoshidaEndpointA * oddRate (m + 1)) *
          Real.cosh
            (yoshidaEndpointA * oddRate (m + 1) * t) *
          ((2 - t) * Real.cos (factorTwoNaturalFrequency n * t)))
      volume 0 2 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have htailSumInt : IntervalIntegrable
      (fun t : ℝ ↦ ∑ m ∈ Finset.range N,
        2 * Real.exp
            (-2 * yoshidaEndpointA * oddRate (m + 1)) *
          Real.cosh
            (yoshidaEndpointA * oddRate (m + 1) * t) *
          ((2 - t) * Real.cos (factorTwoNaturalFrequency n * t)))
      volume 0 2 := by
    apply Continuous.intervalIntegrable
    fun_prop
  unfold factorTwoSymmetricAffineCosArchPartial
    factorTwoSymmetricRankPartialWeight
  have hpoint : (fun t : ℝ ↦
      (2 * Real.exp yoshidaEndpointA *
          Real.cosh (yoshidaEndpointA * t / 2) -
        ∑ m ∈ Finset.range N,
          2 * Real.exp
              (-2 * yoshidaEndpointA * oddRate (m + 1)) *
            Real.cosh
              (yoshidaEndpointA * oddRate (m + 1) * t)) *
        ((2 - t) * Real.cos (factorTwoNaturalFrequency n * t))) =
      fun t : ℝ ↦
        2 * Real.exp yoshidaEndpointA *
            Real.cosh (yoshidaEndpointA * t / 2) *
            ((2 - t) * Real.cos (factorTwoNaturalFrequency n * t)) -
          ∑ m ∈ Finset.range N,
            2 * Real.exp
                (-2 * yoshidaEndpointA * oddRate (m + 1)) *
              Real.cosh
                (yoshidaEndpointA * oddRate (m + 1) * t) *
              ((2 - t) * Real.cos (factorTwoNaturalFrequency n * t)) := by
    funext t
    simp only [sub_mul, Finset.sum_mul]
  rw [hpoint]
  rw [intervalIntegral.integral_sub hheadInt htailSumInt,
    intervalIntegral.integral_finset_sum (fun m _hm ↦ htailInt m)]
  rw [show (∫ t : ℝ in 0..2,
      2 * Real.exp yoshidaEndpointA *
        Real.cosh (yoshidaEndpointA * t / 2) *
        ((2 - t) * Real.cos (factorTwoNaturalFrequency n * t))) =
      2 * Real.exp yoshidaEndpointA *
        (∫ t : ℝ in 0..2,
          Real.cosh ((yoshidaEndpointA / 2) * t) *
            ((2 - t) * Real.cos (factorTwoNaturalFrequency n * t))) by
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
          ((2 - t) * Real.cos (factorTwoNaturalFrequency n * t))) =
        2 * Real.exp
            (-2 * yoshidaEndpointA * oddRate (m + 1)) *
          (∫ t : ℝ in 0..2,
            Real.cosh
              ((yoshidaEndpointA * oddRate (m + 1)) * t) *
              ((2 - t) * Real.cos (factorTwoNaturalFrequency n * t))) by
    intro m
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext t
    ring]
  simp_rw [htail]
  unfold factorTwoSymmetricAffineCosHeadRaw
    factorTwoSymmetricAffineCosRankRaw
  have hsum :
      (∑ m ∈ Finset.range N,
        -yoshidaEndpointA * 2 *
          Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
          (2 * Real.sinh
              (yoshidaEndpointA * oddRate (m + 1)) ^ 2 *
            factorTwoCauchyT
              (yoshidaEndpointA * oddRate (m + 1))
              (factorTwoNaturalFrequency n))) =
        -yoshidaEndpointA *
          ∑ m ∈ Finset.range N,
            2 * Real.exp
                (-2 * yoshidaEndpointA * oddRate (m + 1)) *
              (2 * Real.sinh
                  (yoshidaEndpointA * oddRate (m + 1)) ^ 2 *
                factorTwoCauchyT
                  (yoshidaEndpointA * oddRate (m + 1))
                  (factorTwoNaturalFrequency n)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _hm
    ring
  rw [hsum]
  ring

/-- The growing rank is the positive `j = 0` derivative-Cauchy defect. -/
theorem factorTwoSymmetricAffineCosHeadRaw_eq_dyadic (n : ℕ) :
    factorTwoSymmetricAffineCosHeadRaw n =
      factorTwoHeadDefect / (2 * factorTwoMomentLength) *
        factorTwoCauchyT (factorTwoCauchyX 0) (factorTwoMomentY n) := by
  have hsqrtPos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrtSq : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hsinh : 2 * Real.sinh (yoshidaEndpointA / 2) ^ 2 =
      Real.cosh yoshidaEndpointA - 1 := by
    have htwo := Real.cosh_two_mul (yoshidaEndpointA / 2)
    have hdiff := Real.cosh_sq_sub_sinh_sq (yoshidaEndpointA / 2)
    rw [show 2 * (yoshidaEndpointA / 2) = yoshidaEndpointA by ring] at htwo
    nlinarith
  have hcoef :
      4 * Real.exp yoshidaEndpointA *
          Real.sinh (yoshidaEndpointA / 2) ^ 2 =
        factorTwoHeadDefect := by
    rw [show 4 * Real.exp yoshidaEndpointA *
          Real.sinh (yoshidaEndpointA / 2) ^ 2 =
        2 * Real.exp yoshidaEndpointA *
          (2 * Real.sinh (yoshidaEndpointA / 2) ^ 2) by ring,
      hsinh, Real.cosh_eq, Real.exp_neg,
      exp_yoshidaEndpointA_eq_sqrt_two]
    unfold factorTwoHeadDefect
    field_simp [hsqrtPos.ne']
    nlinarith
  have hL0 : factorTwoMomentLength ≠ 0 := factorTwoMomentLength_pos.ne'
  have hxscale : yoshidaEndpointA / 2 =
      factorTwoMomentLength * factorTwoCauchyX 0 := by
    unfold factorTwoMomentLength factorTwoCauchyX
    norm_num
    ring
  have hyscale : factorTwoNaturalFrequency n =
      factorTwoMomentLength * factorTwoMomentY n := by
    unfold factorTwoMomentY
    field_simp [hL0]
  have hx : 0 < factorTwoCauchyX 0 := by
    unfold factorTwoCauchyX
    norm_num
  have hdenScaled : factorTwoCauchyX 0 ^ 2 +
      factorTwoMomentY n ^ 2 ≠ 0 := by
    have hxsq : 0 < factorTwoCauchyX 0 ^ 2 := sq_pos_of_pos hx
    positivity
  calc
    factorTwoSymmetricAffineCosHeadRaw n =
        yoshidaEndpointA * factorTwoHeadDefect *
          factorTwoCauchyT (yoshidaEndpointA / 2)
            (factorTwoNaturalFrequency n) := by
      unfold factorTwoSymmetricAffineCosHeadRaw
      rw [← hcoef]
      ring
    _ = _ := by
      rw [hxscale, hyscale]
      unfold factorTwoCauchyT factorTwoMomentLength
      field_simp [hL0, hdenScaled, yoshidaEndpointA_pos.ne']

/-- Every decaying hyperbolic rank is its signed dyadic derivative-Cauchy
kernel; raw rank `m` corresponds to Cauchy index `m + 1`. -/
theorem factorTwoSymmetricAffineCosRankRaw_eq_dyadic
    (n m : ℕ) :
    factorTwoSymmetricAffineCosRankRaw n m =
      -(1 / (2 * factorTwoMomentLength)) *
        factorTwoSymmetricAffineCosDyadicKernel n (m + 1) := by
  let r : ℝ := oddRate (m + 1)
  let q : ℝ := Real.exp (-2 * yoshidaEndpointA * r)
  have hL : factorTwoMomentLength = yoshidaLength :=
    factorTwoMomentLength_eq_yoshidaLength
  have hL0 : factorTwoMomentLength ≠ 0 := factorTwoMomentLength_pos.ne'
  have hq : q = factorTwoDyadicQ (m + 1) := by
    dsimp only [q]
    rw [show -2 * yoshidaEndpointA * r = -r * yoshidaLength by
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
  have hsinh :
      2 * Real.sinh (yoshidaEndpointA * r) ^ 2 =
        Real.cosh (2 * (yoshidaEndpointA * r)) - 1 := by
    have htwo := Real.cosh_two_mul (yoshidaEndpointA * r)
    have hdiff := Real.cosh_sq_sub_sinh_sq (yoshidaEndpointA * r)
    nlinarith
  have hpair :
      4 * q * Real.sinh (yoshidaEndpointA * r) ^ 2 =
        factorTwoDyadicD (m + 1) := by
    have hbase := exp_neg_mul_cosh_sub_one
      (2 * (yoshidaEndpointA * r))
    have hqexp : Real.exp (-(2 * (yoshidaEndpointA * r))) = q := by
      dsimp only [q]
      congr 1
      ring
    rw [hqexp, ← hsinh] at hbase
    unfold factorTwoDyadicD
    rw [← hq]
    nlinarith
  have hx : 0 < factorTwoCauchyX (m + 1) := by
    unfold factorTwoCauchyX
    positivity
  have hdenScaled : factorTwoCauchyX (m + 1) ^ 2 +
      factorTwoMomentY n ^ 2 ≠ 0 := by
    have hxsq : 0 < factorTwoCauchyX (m + 1) ^ 2 :=
      sq_pos_of_pos hx
    positivity
  calc
    factorTwoSymmetricAffineCosRankRaw n m =
        -yoshidaEndpointA *
          (4 * q * Real.sinh (yoshidaEndpointA * r) ^ 2) *
          factorTwoCauchyT (yoshidaEndpointA * r)
            (factorTwoNaturalFrequency n) := by
      unfold factorTwoSymmetricAffineCosRankRaw
      dsimp only [q, r]
      ring
    _ = -yoshidaEndpointA * factorTwoDyadicD (m + 1) *
          factorTwoCauchyT (yoshidaEndpointA * r)
            (factorTwoNaturalFrequency n) := by rw [hpair]
    _ = _ := by
      rw [hxr, hwy]
      unfold factorTwoSymmetricAffineCosDyadicKernel factorTwoCauchyT
      have hA : yoshidaEndpointA = factorTwoMomentLength / 2 := by
        unfold factorTwoMomentLength
        ring
      rw [hA]
      field_simp [hL0, hdenScaled]

theorem factorTwoDyadicD_succ_mem_unitInterval (m : ℕ) :
    0 ≤ factorTwoDyadicD (m + 1) ∧
      factorTwoDyadicD (m + 1) ≤ 1 := by
  have hsqrtPos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrtSq : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hsqrtOne : 1 ≤ Real.sqrt 2 := by
    nlinarith
  have hinv : (Real.sqrt 2)⁻¹ ≤ 1 :=
    (inv_le_one₀ hsqrtPos).2 hsqrtOne
  have hpow : 1 ≤ (4 : ℝ) ^ (m + 1) :=
    one_le_pow₀ (by norm_num)
  have hpowPos : 0 < (4 : ℝ) ^ (m + 1) := by positivity
  have hq0 : 0 ≤ factorTwoDyadicQ (m + 1) := by
    unfold factorTwoDyadicQ
    positivity
  have hq1 : factorTwoDyadicQ (m + 1) ≤ 1 := by
    unfold factorTwoDyadicQ
    calc
      (Real.sqrt 2)⁻¹ / (4 : ℝ) ^ (m + 1) ≤
          1 / (4 : ℝ) ^ (m + 1) :=
        div_le_div_of_nonneg_right hinv hpowPos.le
      _ ≤ 1 := (div_le_one hpowPos).2 hpow
  constructor
  · unfold factorTwoDyadicD
    positivity
  · unfold factorTwoDyadicD
    have hprod : 0 ≤ factorTwoDyadicQ (m + 1) *
        (1 - factorTwoDyadicQ (m + 1)) :=
      mul_nonneg hq0 (sub_nonneg.mpr hq1)
    nlinarith

theorem factorTwoCauchyT_abs_le_inv_sq
    {x y : ℝ} (hx : 0 < x) :
    |factorTwoCauchyT x y| ≤ 1 / x ^ 2 := by
  have hd : 0 < x ^ 2 + y ^ 2 := by
    nlinarith [sq_pos_of_pos hx, sq_nonneg y]
  have hnum : |x ^ 2 - y ^ 2| ≤ x ^ 2 + y ^ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg x, sq_nonneg y]
  unfold factorTwoCauchyT
  rw [abs_div, abs_pow, abs_of_pos hd]
  calc
    |x ^ 2 - y ^ 2| / (x ^ 2 + y ^ 2) ^ 2 ≤
        (x ^ 2 + y ^ 2) / (x ^ 2 + y ^ 2) ^ 2 :=
      div_le_div_of_nonneg_right hnum (sq_nonneg _)
    _ = 1 / (x ^ 2 + y ^ 2) := by
      field_simp [hd.ne']
    _ ≤ 1 / x ^ 2 := by
      apply one_div_le_one_div_of_le (sq_pos_of_pos hx)
      nlinarith [sq_nonneg y]

theorem factorTwoSymmetricAffineCosDyadicKernel_abs_le
    (n m : ℕ) :
    |factorTwoSymmetricAffineCosDyadicKernel n (m + 1)| ≤
      1 / ((((m + 1 : ℕ) : ℝ) ^ 2)) := by
  let k : ℝ := ((m + 1 : ℕ) : ℝ)
  let x : ℝ := factorTwoCauchyX (m + 1)
  let y : ℝ := factorTwoMomentY n
  have hk : 0 < k := by
    dsimp only [k]
    positivity
  have hx : 0 < x := by
    dsimp only [x]
    unfold factorTwoCauchyX
    positivity
  have hkx : k ^ 2 ≤ x ^ 2 := by
    have hle : k ≤ x := by
      dsimp only [k, x]
      unfold factorTwoCauchyX
      push_cast
      norm_num
    nlinarith
  have hprofile : |factorTwoCauchyT x y| ≤ 1 / k ^ 2 := by
    calc
      |factorTwoCauchyT x y| ≤ 1 / x ^ 2 :=
        factorTwoCauchyT_abs_le_inv_sq hx
      _ ≤ 1 / k ^ 2 :=
        one_div_le_one_div_of_le (sq_pos_of_pos hk) hkx
  have hD := factorTwoDyadicD_succ_mem_unitInterval m
  unfold factorTwoSymmetricAffineCosDyadicKernel
  rw [abs_mul, abs_of_nonneg hD.1]
  change factorTwoDyadicD (m + 1) * |factorTwoCauchyT x y| ≤ _
  calc
    factorTwoDyadicD (m + 1) * |factorTwoCauchyT x y| ≤
        1 * |factorTwoCauchyT x y| :=
      mul_le_mul_of_nonneg_right hD.2 (abs_nonneg _)
    _ ≤ 1 / k ^ 2 := by simpa using hprofile
    _ = _ := by rfl

/-- Absolute summability of the signed dyadic affine-cosine ranks. -/
theorem summable_norm_factorTwoSymmetricAffineCosDyadicKernel (n : ℕ) :
    Summable (fun m : ℕ ↦
      ‖factorTwoSymmetricAffineCosDyadicKernel n (m + 1)‖) := by
  have hmajor : Summable (fun m : ℕ ↦
      1 / ((((m + 1 : ℕ) : ℝ) ^ 2))) := by
    have h := Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).2 h
  apply hmajor.of_nonneg_of_le
  · intro m
    exact norm_nonneg _
  · intro m
    rw [Real.norm_eq_abs]
    exact factorTwoSymmetricAffineCosDyadicKernel_abs_le n m

theorem summable_norm_factorTwoSymmetricAffineCosRankRaw (n : ℕ) :
    Summable (fun m : ℕ ↦ ‖factorTwoSymmetricAffineCosRankRaw n m‖) := by
  let c : ℝ := -(1 / (2 * factorTwoMomentLength))
  have hs :=
    (summable_norm_factorTwoSymmetricAffineCosDyadicKernel n).mul_left ‖c‖
  apply hs.congr
  intro m
  rw [factorTwoSymmetricAffineCosRankRaw_eq_dyadic]
  dsimp only [c]
  rw [norm_mul]

/-- The signed raw ranks have the sum forced by the dominated integral limit. -/
theorem hasSum_factorTwoSymmetricAffineCosRankRaw
    (n : FactorTwoCanonicalEvenIndex) :
    HasSum (factorTwoSymmetricAffineCosRankRaw n.1)
      (factorTwoSymmetricAffineCosArchMoment n.1 -
        factorTwoSymmetricAffineCosHeadRaw n.1) := by
  have hlim := factorTwoSymmetricAffineCosArchPartial_tendsto n
  have hsub := hlim.sub_const (factorTwoSymmetricAffineCosHeadRaw n.1)
  apply (hasSum_iff_tendsto_nat_of_summable_norm
    (summable_norm_factorTwoSymmetricAffineCosRankRaw n.1)).2
  convert hsub using 1
  funext N
  rw [factorTwoSymmetricAffineCosArchPartial_eq_raw]
  ring

/-- Honest infinite-series identity before the dyadic simplification. -/
theorem factorTwoSymmetricAffineCosArchMoment_eq_raw_tsum
    (n : FactorTwoCanonicalEvenIndex) :
    factorTwoSymmetricAffineCosArchMoment n.1 =
      factorTwoSymmetricAffineCosHeadRaw n.1 +
        ∑' m : ℕ, factorTwoSymmetricAffineCosRankRaw n.1 m := by
  rw [(hasSum_factorTwoSymmetricAffineCosRankRaw n).tsum_eq]
  ring

/-- The archimedean affine-cosine moment as the exact growing-head term minus
the absolutely convergent dyadic derivative-Cauchy series. -/
theorem factorTwoSymmetricAffineCosArchMoment_eq_dyadicCauchySeries
    (n : FactorTwoCanonicalEvenIndex) :
    factorTwoSymmetricAffineCosArchMoment n.1 =
      factorTwoHeadDefect / (2 * factorTwoMomentLength) *
          factorTwoCauchyT (factorTwoCauchyX 0) (factorTwoMomentY n.1) -
        (1 / (2 * factorTwoMomentLength)) *
          ∑' m : ℕ,
            factorTwoSymmetricAffineCosDyadicKernel n.1 (m + 1) := by
  rw [factorTwoSymmetricAffineCosArchMoment_eq_raw_tsum n,
    factorTwoSymmetricAffineCosHeadRaw_eq_dyadic]
  rw [show (∑' m : ℕ, factorTwoSymmetricAffineCosRankRaw n.1 m) =
      ∑' m : ℕ,
        -(1 / (2 * factorTwoMomentLength)) *
          factorTwoSymmetricAffineCosDyadicKernel n.1 (m + 1) by
    apply tsum_congr
    intro m
    exact factorTwoSymmetricAffineCosRankRaw_eq_dyadic n.1 m]
  rw [tsum_mul_left]
  ring

/-- Full symmetric affine-cosine perturbation moment, including both retained
prime atoms.  This statement includes the canonical zero mode. -/
theorem factorTwoSymmetricAffineCosMoment_eq_dyadicCauchySeries
    (n : FactorTwoCanonicalEvenIndex) :
    factorTwoSymmetricAffineCosMoment n.1 =
      factorTwoHeadDefect / (2 * factorTwoMomentLength) *
          factorTwoCauchyT (factorTwoCauchyX 0) (factorTwoMomentY n.1) -
        (1 / (2 * factorTwoMomentLength)) *
          ∑' m : ℕ,
            factorTwoSymmetricAffineCosDyadicKernel n.1 (m + 1) -
        2 * factorTwoMomentLength / Real.sqrt 2 -
        (Real.log 3 / Real.sqrt 3) *
          (2 - 2 * factorTwoPrimeShift / factorTwoMomentLength) *
          Real.cos
            (2 * factorTwoMomentY n.1 * factorTwoPrimeShift) := by
  have hlogTwo : Real.log 2 = factorTwoMomentLength := by
    unfold factorTwoMomentLength yoshidaEndpointA
    ring
  have harg : factorTwoNaturalFrequency n.1 *
        (factorTwoPrimeShift / yoshidaEndpointA) =
      2 * factorTwoMomentY n.1 * factorTwoPrimeShift := by
    unfold factorTwoMomentY factorTwoMomentLength
    field_simp [yoshidaEndpointA_pos.ne']
  have hheight :
      2 - factorTwoPrimeShift / yoshidaEndpointA =
        2 - 2 * factorTwoPrimeShift / factorTwoMomentLength := by
    unfold factorTwoMomentLength
    field_simp [yoshidaEndpointA_pos.ne']
  unfold factorTwoSymmetricAffineCosMoment
    factorTwoSymmetricPerturbationFunctional
  change factorTwoSymmetricAffineCosArchMoment n.1 -
      (Real.log 2 / Real.sqrt 2) *
        ((2 - 0) * Real.cos (factorTwoNaturalFrequency n.1 * 0)) -
      (Real.log 3 / Real.sqrt 3) *
        ((2 - factorTwoPrimeShift / yoshidaEndpointA) *
          Real.cos (factorTwoNaturalFrequency n.1 *
            (factorTwoPrimeShift / yoshidaEndpointA))) = _
  rw [factorTwoSymmetricAffineCosArchMoment_eq_dyadicCauchySeries n,
    hlogTwo, hheight, harg]
  simp only [sub_zero, mul_zero, Real.cos_zero, mul_one]
  ring

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhasePerturbationAffineCosSeries

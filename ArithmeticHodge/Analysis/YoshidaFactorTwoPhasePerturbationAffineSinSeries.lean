import ArithmeticHodge.Analysis.YoshidaFactorTwoPhasePerturbationMomentSeries

set_option autoImplicit false
set_option maxRecDepth 100000

open Filter MeasureTheory Real Set Topology
open scoped BigOperators Interval

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhasePerturbationAffineSinSeries

noncomputable section

open ArithmeticHodge.Analysis
open YoshidaFactorTwoAdjacentKernel
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
# Dyadic Cauchy series for the factor-two antisymmetric affine sine moment

The antisymmetric weight has one growing `sinh` rank followed by positive
half-odd decaying ranks.  The endpoint factor `2 - t` supplies the cancellation
needed for dominated convergence.  At positive integer Fourier frequencies,
the negative elementary `sinh` transform combines with the `-2A` normalization
of the alternating functional to give the positive dyadic series below.
-/

/-- The positive off-diagonal derivative-Cauchy kernel. -/
def factorTwoCauchyU (x y : ℝ) : ℝ :=
  2 * x * y / (x ^ 2 + y ^ 2) ^ 2

/-- A positive dyadic affine-sine rank, before its common coefficient. -/
def factorTwoAntisymmetricAffineSinDyadicKernel (n j : ℕ) : ℝ :=
  factorTwoDyadicD j *
    factorTwoCauchyU (factorTwoCauchyX j) (factorTwoMomentY n)

/-- The finite antisymmetric hyperbolic-rank weight. -/
def factorTwoAntisymmetricRankPartialWeight (N : ℕ) (t : ℝ) : ℝ :=
  2 * Real.exp yoshidaEndpointA *
      Real.sinh (yoshidaEndpointA * t / 2) +
    ∑ m ∈ Finset.range N,
      2 * Real.exp
          (-2 * yoshidaEndpointA * oddRate (m + 1)) *
        Real.sinh
          (yoshidaEndpointA * oddRate (m + 1) * t)

/-- The archimedean affine-sine transform before the retained prime atom. -/
def factorTwoAntisymmetricAffineSinArchMoment (n : ℕ) : ℝ :=
  -2 * yoshidaEndpointA *
    ∫ t : ℝ in 0..2,
      factorTwoAntisymmetricWeight (yoshidaEndpointA * t) *
        ((2 - t) * Real.sin (factorTwoNaturalFrequency n * t))

/-- Its finite hyperbolic-rank approximation. -/
def factorTwoAntisymmetricAffineSinArchPartial (n N : ℕ) : ℝ :=
  -2 * yoshidaEndpointA *
    ∫ t : ℝ in 0..2,
      factorTwoAntisymmetricRankPartialWeight N t *
        ((2 - t) * Real.sin (factorTwoNaturalFrequency n * t))

private def affineSinRampPrimitive (b kappa L u : ℝ) : ℝ :=
  (1 - u / L) * Real.exp (b * u) *
      (b * Real.sin (kappa * u) - kappa * Real.cos (kappa * u)) /
        (b ^ 2 + kappa ^ 2) +
    Real.exp (b * u) *
      ((b ^ 2 - kappa ^ 2) * Real.sin (kappa * u) -
        2 * b * kappa * Real.cos (kappa * u)) /
      (L * (b ^ 2 + kappa ^ 2) ^ 2)

private theorem affineSinRampPrimitive_hasDerivAt
    {b kappa L u : ℝ} (hL : L ≠ 0)
    (hden : b ^ 2 + kappa ^ 2 ≠ 0) :
    HasDerivAt (affineSinRampPrimitive b kappa L)
      (Real.exp (b * u) * (1 - u / L) * Real.sin (kappa * u)) u := by
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
  have hasin : HasDerivAt
      (fun x : ℝ ↦ b * Real.sin (kappa * x) -
        kappa * Real.cos (kappa * x))
      (b * (Real.cos (kappa * u) * kappa) -
        kappa * (-Real.sin (kappa * u) * kappa)) u :=
    (hsin.const_mul b).sub (hcos.const_mul kappa)
  have hg : HasDerivAt
      (fun x : ℝ ↦ (b ^ 2 - kappa ^ 2) * Real.sin (kappa * x) -
        2 * b * kappa * Real.cos (kappa * x))
      ((b ^ 2 - kappa ^ 2) * (Real.cos (kappa * u) * kappa) -
        2 * b * kappa * (-Real.sin (kappa * u) * kappa)) u :=
    (hsin.const_mul (b ^ 2 - kappa ^ 2)).sub
      (hcos.const_mul (2 * b * kappa))
  convert ((((hramp.mul hexp).mul hasin).div_const
      (b ^ 2 + kappa ^ 2)).add
    ((hexp.mul hg).div_const (L * (b ^ 2 + kappa ^ 2) ^ 2))) using 1
  simp only [Pi.mul_apply]
  field_simp [hL, hden]
  ring

private theorem integral_exp_mul_affineSinRamp_periodic
    {b kappa L : ℝ} (hL : L ≠ 0)
    (hden : b ^ 2 + kappa ^ 2 ≠ 0)
    (hsin : Real.sin (kappa * L) = 0)
    (hcos : Real.cos (kappa * L) = 1) :
    (∫ u in 0..L,
        Real.exp (b * u) * (1 - u / L) * Real.sin (kappa * u)) =
      kappa *
        (L * (b ^ 2 + kappa ^ 2) -
          2 * b * (Real.exp (b * L) - 1)) /
        (L * (b ^ 2 + kappa ^ 2) ^ 2) := by
  have hderiv : ∀ u ∈ Set.uIcc (0 : ℝ) L,
      HasDerivAt (affineSinRampPrimitive b kappa L)
        (Real.exp (b * u) * (1 - u / L) * Real.sin (kappa * u)) u :=
    fun u _ ↦ affineSinRampPrimitive_hasDerivAt hL hden
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (Continuous.intervalIntegrable (by fun_prop) 0 L)
  rw [h]
  simp only [affineSinRampPrimitive, mul_zero, zero_div, sub_zero,
    Real.exp_zero, Real.sin_zero, Real.cos_zero, hsin, hcos]
  field_simp [hL, hden]
  ring

/-- Complete-period antisymmetric affine-sine transform. -/
theorem integral_sinh_mul_factorTwoAffineSin
    (n : ℕ) {lambda : ℝ} (hlambda : lambda ≠ 0) :
    (∫ t : ℝ in 0..2,
      Real.sinh (lambda * t) *
        ((2 - t) * Real.sin (factorTwoNaturalFrequency n * t))) =
      -2 * lambda * factorTwoNaturalFrequency n *
        (Real.cosh (2 * lambda) - 1) /
        (lambda ^ 2 + factorTwoNaturalFrequency n ^ 2) ^ 2 := by
  let omega := factorTwoNaturalFrequency n
  have hden : lambda ^ 2 + omega ^ 2 ≠ 0 := by
    have hlambdaSq : 0 < lambda ^ 2 := sq_pos_of_ne_zero hlambda
    positivity
  have hnegDen : (-lambda) ^ 2 + omega ^ 2 ≠ 0 := by
    have hlambdaSq : 0 < (-lambda) ^ 2 :=
      sq_pos_of_ne_zero (neg_ne_zero.mpr hlambda)
    positivity
  have hpos := integral_exp_mul_affineSinRamp_periodic
    (by norm_num : (2 : ℝ) ≠ 0) hden
    (factorTwoNaturalFrequency_mul_two_sin n)
    (factorTwoNaturalFrequency_mul_two_cos n)
    (b := lambda) (kappa := omega) (L := 2)
  have hneg := integral_exp_mul_affineSinRamp_periodic
    (by norm_num : (2 : ℝ) ≠ 0) hnegDen
    (factorTwoNaturalFrequency_mul_two_sin n)
    (factorTwoNaturalFrequency_mul_two_cos n)
    (b := -lambda) (kappa := omega) (L := 2)
  have hposInt : IntervalIntegrable
      (fun t : ℝ ↦ Real.exp (lambda * t) *
        (1 - t / 2) * Real.sin (omega * t)) volume 0 2 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hnegInt : IntervalIntegrable
      (fun t : ℝ ↦ Real.exp (-lambda * t) *
        (1 - t / 2) * Real.sin (omega * t)) volume 0 2 := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [show (fun t : ℝ ↦
      Real.sinh (lambda * t) *
        ((2 - t) * Real.sin (factorTwoNaturalFrequency n * t))) =
      fun t ↦
        Real.exp (lambda * t) * (1 - t / 2) * Real.sin (omega * t) -
        Real.exp (-lambda * t) * (1 - t / 2) * Real.sin (omega * t) by
    funext t
    dsimp only [omega]
    rw [Real.sinh_eq]
    rw [show -(lambda * t) = -lambda * t by ring]
    ring,
    intervalIntegral.integral_sub hposInt hnegInt,
    hpos, hneg]
  dsimp only [omega]
  rw [show -lambda * 2 = -(lambda * 2) by ring,
    show (-lambda) ^ 2 = lambda ^ 2 by ring,
    Real.cosh_eq]
  field_simp [hden, hnegDen, Real.exp_ne_zero]
  ring

/-- On the open overlap interval the antisymmetric adjacent weight is one
growing `sinh` rank followed by the exact positive half-odd decaying series. -/
theorem factorTwoAntisymmetricWeight_eq_rankOneSeries
    {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t < 2) :
    factorTwoAntisymmetricWeight (yoshidaEndpointA * t) =
      2 * Real.exp yoshidaEndpointA *
          Real.sinh (yoshidaEndpointA * t / 2) +
        ∑' m : ℕ,
          2 * Real.exp
              (-2 * yoshidaEndpointA * oddRate (m + 1)) *
            Real.sinh
              (yoshidaEndpointA * oddRate (m + 1) * t) := by
  let zp : ℝ := yoshidaEndpointA * (2 + t)
  let zm : ℝ := yoshidaEndpointA * (2 - t)
  have hzp : 0 < zp := by
    dsimp only [zp]
    exact mul_pos yoshidaEndpointA_pos (by linarith)
  have hzm : 0 < zm := by
    dsimp only [zm]
    exact mul_pos yoshidaEndpointA_pos (by linarith)
  have hsummable (z : ℝ) (hz : 0 < z) :
      Summable (fun m : ℕ ↦ Real.exp (-oddRate (m + 1) * z)) := by
    have hfull : Summable
        (fun k : ℕ ↦ Real.exp (-oddRate k * z)) := by
      have hscaled :=
        (hasSum_oddExponentials hz).summable.mul_left (1 / 2 : ℝ)
      convert hscaled using 1
      funext k
      ring
    simpa only [Nat.add_comm] using (summable_nat_add_iff 1).2 hfull
  have hsp := hsummable zp hzp
  have hsm := hsummable zm hzm
  have hhead :
      Real.exp (zp / 2) - Real.exp (zm / 2) =
        2 * Real.exp yoshidaEndpointA *
          Real.sinh (yoshidaEndpointA * t / 2) := by
    rw [Real.sinh_eq]
    dsimp only [zp, zm]
    rw [show yoshidaEndpointA * (2 + t) / 2 =
          yoshidaEndpointA + yoshidaEndpointA * t / 2 by ring,
      show yoshidaEndpointA * (2 - t) / 2 =
          yoshidaEndpointA + -(yoshidaEndpointA * t / 2) by ring,
      Real.exp_add, Real.exp_add]
    ring
  have hterm (m : ℕ) :
      Real.exp (-oddRate (m + 1) * zm) -
          Real.exp (-oddRate (m + 1) * zp) =
        2 * Real.exp
              (-2 * yoshidaEndpointA * oddRate (m + 1)) *
            Real.sinh
              (yoshidaEndpointA * oddRate (m + 1) * t) := by
    rw [Real.sinh_eq]
    dsimp only [zp, zm]
    rw [show -oddRate (m + 1) * (yoshidaEndpointA * (2 - t)) =
          -2 * yoshidaEndpointA * oddRate (m + 1) +
            yoshidaEndpointA * oddRate (m + 1) * t by ring,
      show -oddRate (m + 1) * (yoshidaEndpointA * (2 + t)) =
          -2 * yoshidaEndpointA * oddRate (m + 1) +
            -(yoshidaEndpointA * oddRate (m + 1) * t) by ring,
      Real.exp_add, Real.exp_add]
    ring
  have hsum :
      (∑' m : ℕ, Real.exp (-oddRate (m + 1) * zm)) -
          ∑' m : ℕ, Real.exp (-oddRate (m + 1) * zp) =
        ∑' m : ℕ,
          2 * Real.exp
              (-2 * yoshidaEndpointA * oddRate (m + 1)) *
            Real.sinh
              (yoshidaEndpointA * oddRate (m + 1) * t) := by
    rw [← hsm.tsum_sub hsp]
    apply tsum_congr
    exact hterm
  unfold factorTwoAntisymmetricWeight
  rw [factorTwoLogLength_eq_two_mul_yoshidaEndpointA]
  rw [show 2 * yoshidaEndpointA + yoshidaEndpointA * t = zp by
      dsimp only [zp]
      ring,
    show 2 * yoshidaEndpointA - yoshidaEndpointA * t = zm by
      dsimp only [zm]
      ring,
    factorTwoAdjacentSmoothKernel_eq_exp_sub_tsum hzp,
    factorTwoAdjacentSmoothKernel_eq_exp_sub_tsum hzm]
  linear_combination hhead + hsum

/-- The positive antisymmetric decaying ranks are summable throughout the
open overlap interval. -/
theorem summable_factorTwoAntisymmetricRankTail
    {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t < 2) :
    Summable (fun m : ℕ ↦
      2 * Real.exp
          (-2 * yoshidaEndpointA * oddRate (m + 1)) *
        Real.sinh
          (yoshidaEndpointA * oddRate (m + 1) * t)) := by
  have hmajor := summable_factorTwoSymmetricRankTail ht0 ht2
  apply hmajor.of_nonneg_of_le
  · intro m
    have hz : 0 ≤ yoshidaEndpointA * oddRate (m + 1) * t := by
      exact mul_nonneg
        (mul_nonneg yoshidaEndpointA_pos.le (oddRate_pos _).le) ht0
    exact mul_nonneg (by positivity)
      (Real.sinh_nonneg_iff.mpr hz)
  · intro m
    let z : ℝ := yoshidaEndpointA * oddRate (m + 1) * t
    have hsinhCosh : Real.sinh z ≤ Real.cosh z := by
      rw [Real.sinh_eq, Real.cosh_eq]
      linarith [Real.exp_pos (-z)]
    exact mul_le_mul_of_nonneg_left hsinhCosh (by positivity)

/-- The finite antisymmetric ranks converge pointwise to the complete weight
on the open overlap interval. -/
theorem factorTwoAntisymmetricRankPartialWeight_tendsto
    {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t < 2) :
    Tendsto (fun N : ℕ ↦ factorTwoAntisymmetricRankPartialWeight N t)
      atTop
      (nhds (factorTwoAntisymmetricWeight (yoshidaEndpointA * t))) := by
  let a : ℕ → ℝ := fun m ↦
    2 * Real.exp
        (-2 * yoshidaEndpointA * oddRate (m + 1)) *
      Real.sinh
        (yoshidaEndpointA * oddRate (m + 1) * t)
  have ha : Summable a := by
    simpa only [a] using summable_factorTwoAntisymmetricRankTail ht0 ht2
  have hsum : Tendsto (fun N : ℕ ↦ ∑ m ∈ Finset.range N, a m)
      atTop (nhds (∑' m : ℕ, a m)) := ha.hasSum.tendsto_sum_nat
  have hhead : Tendsto
      (fun _ : ℕ ↦
        2 * Real.exp yoshidaEndpointA *
          Real.sinh (yoshidaEndpointA * t / 2))
      atTop
      (nhds (2 * Real.exp yoshidaEndpointA *
        Real.sinh (yoshidaEndpointA * t / 2))) := tendsto_const_nhds
  have hadd := hhead.add hsum
  rw [factorTwoAntisymmetricWeight_eq_rankOneSeries ht0 ht2]
  simpa only [factorTwoAntisymmetricRankPartialWeight, a] using hadd

private theorem factorTwoAntisymmetricRankPartialTail_le_tsum
    {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t < 2) (N : ℕ) :
    (∑ m ∈ Finset.range N,
      2 * Real.exp
          (-2 * yoshidaEndpointA * oddRate (m + 1)) *
        Real.sinh
          (yoshidaEndpointA * oddRate (m + 1) * t)) ≤
      ∑' m : ℕ,
        2 * Real.exp
            (-2 * yoshidaEndpointA * oddRate (m + 1)) *
          Real.sinh
            (yoshidaEndpointA * oddRate (m + 1) * t) := by
  have hs := summable_factorTwoAntisymmetricRankTail ht0 ht2
  apply hs.sum_le_tsum (Finset.range N)
  intro m _hm
  have hz : 0 ≤ yoshidaEndpointA * oddRate (m + 1) * t := by
    exact mul_nonneg
      (mul_nonneg yoshidaEndpointA_pos.le (oddRate_pos _).le) ht0
  exact mul_nonneg (by positivity) (Real.sinh_nonneg_iff.mpr hz)

/-- Dominated passage from finite antisymmetric ranks to the complete
affine-sine transform. -/
theorem factorTwoAntisymmetricAffineSinArchPartial_tendsto
    (n : FactorTwoCanonicalEvenIndex) (hn : n.1 ≠ 0) :
    Tendsto (fun N : ℕ ↦ factorTwoAntisymmetricAffineSinArchPartial n.1 N)
      atTop (nhds (factorTwoAntisymmetricAffineSinArchMoment n.1)) := by
  let C : ℝ → ℝ := fun t ↦
    (2 - t) * Real.sin (factorTwoNaturalFrequency n.1 * t)
  let G : ℝ → ℝ := fun t ↦
    2 * Real.exp yoshidaEndpointA *
      Real.sinh (yoshidaEndpointA * t / 2)
  let W : ℝ → ℝ := fun t ↦
    factorTwoAntisymmetricWeight (yoshidaEndpointA * t)
  let F : ℕ → ℝ → ℝ := fun N t ↦
    factorTwoAntisymmetricRankPartialWeight N t * C t
  let B : ℝ → ℝ := fun t ↦ |W t * C t|
  have hWeight : IntervalIntegrable (fun t : ℝ ↦ W t * C t)
      volume 0 2 := by
    simpa only [W, C] using
      intervalIntegrable_factorTwoAntisymmetricAffineSinMoment n hn
  have hB : IntervalIntegrable B volume 0 2 := by
    simpa only [B] using hWeight.norm
  have hFmeas : ∀ᶠ N in atTop,
      AEStronglyMeasurable (F N) (volume.restrict (Ι (0 : ℝ) 2)) := by
    filter_upwards [] with N
    apply Continuous.aestronglyMeasurable
    dsimp only [F, C, factorTwoAntisymmetricRankPartialWeight]
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
        Real.sinh
          (yoshidaEndpointA * oddRate (m + 1) * t)
    let T : ℝ := ∑' m : ℕ,
      2 * Real.exp
          (-2 * yoshidaEndpointA * oddRate (m + 1)) *
        Real.sinh
          (yoshidaEndpointA * oddRate (m + 1) * t)
    have hG0 : 0 ≤ G t := by
      dsimp only [G]
      have hz : 0 ≤ yoshidaEndpointA * t / 2 :=
        div_nonneg (mul_nonneg yoshidaEndpointA_pos.le ht0) (by norm_num)
      exact mul_nonneg (by positivity) (Real.sinh_nonneg_iff.mpr hz)
    have hS0 : 0 ≤ S := by
      dsimp only [S]
      apply Finset.sum_nonneg
      intro m _hm
      have hz : 0 ≤ yoshidaEndpointA * oddRate (m + 1) * t := by
        exact mul_nonneg
          (mul_nonneg yoshidaEndpointA_pos.le (oddRate_pos _).le) ht0
      exact mul_nonneg (by positivity) (Real.sinh_nonneg_iff.mpr hz)
    have hST : S ≤ T := by
      simpa only [S, T] using
        factorTwoAntisymmetricRankPartialTail_le_tsum ht0 htlt2 N
    have hT0 : 0 ≤ T := hS0.trans hST
    have hseries := factorTwoAntisymmetricWeight_eq_rankOneSeries ht0 htlt2
    change W t = G t + T at hseries
    have hW0 : 0 ≤ W t := by
      rw [hseries]
      exact add_nonneg hG0 hT0
    have hpartial0 : 0 ≤ G t + S := add_nonneg hG0 hS0
    have hpartialW : G t + S ≤ W t := by
      rw [hseries]
      linarith
    have hWabs : |W t * C t| = W t * |C t| := by
      rw [abs_mul, abs_of_nonneg hW0]
    dsimp only [F, B, factorTwoAntisymmetricRankPartialWeight]
    change ‖(G t + S) * C t‖ ≤ |W t * C t|
    rw [Real.norm_eq_abs]
    calc
      |(G t + S) * C t| = (G t + S) * |C t| := by
        rw [abs_mul, abs_of_nonneg hpartial0]
      _ ≤ W t * |C t| :=
        mul_le_mul_of_nonneg_right hpartialW (abs_nonneg (C t))
      _ = |W t * C t| := hWabs.symm
  have hLim : ∀ᵐ t ∂volume, t ∈ Ι (0 : ℝ) 2 →
      Tendsto (fun N : ℕ ↦ F N t) atTop (nhds (W t * C t)) := by
    filter_upwards [MeasureTheory.Measure.ae_ne volume (2 : ℝ)] with t ht2
    intro ht
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 2)] at ht
    have htlt2 : t < 2 := lt_of_le_of_ne ht.2 ht2
    have hweight :=
      factorTwoAntisymmetricRankPartialWeight_tendsto ht.1.le htlt2
    exact hweight.mul_const (C t)
  have hIntegral :
      Tendsto (fun N : ℕ ↦ ∫ t : ℝ in 0..2, F N t) atTop
        (nhds (∫ t : ℝ in 0..2, W t * C t)) := by
    exact intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      B hFmeas hBound hB hLim
  have hScaled := hIntegral.const_mul (-2 * yoshidaEndpointA)
  simpa only [factorTwoAntisymmetricAffineSinArchPartial,
    factorTwoAntisymmetricAffineSinArchMoment, F, W, C] using hScaled

/-- Raw growing-rank affine-sine contribution after the `-2A` functional
normalization. -/
def factorTwoAntisymmetricAffineSinHeadRaw (n : ℕ) : ℝ :=
  8 * yoshidaEndpointA * Real.exp yoshidaEndpointA *
    (yoshidaEndpointA / 2) * factorTwoNaturalFrequency n *
    (Real.cosh yoshidaEndpointA - 1) /
    (((yoshidaEndpointA / 2) ^ 2 +
      factorTwoNaturalFrequency n ^ 2) ^ 2)

/-- Raw positive decaying-rank affine-sine contribution. -/
def factorTwoAntisymmetricAffineSinRankRaw (n m : ℕ) : ℝ :=
  8 * yoshidaEndpointA *
    Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
    (yoshidaEndpointA * oddRate (m + 1)) *
    factorTwoNaturalFrequency n *
    (Real.cosh (2 * (yoshidaEndpointA * oddRate (m + 1))) - 1) /
    (((yoshidaEndpointA * oddRate (m + 1)) ^ 2 +
      factorTwoNaturalFrequency n ^ 2) ^ 2)

/-- Every finite antisymmetric approximation is a finite sum of the raw
positive affine-sine ranks. -/
theorem factorTwoAntisymmetricAffineSinArchPartial_eq_raw
    (n N : ℕ) :
    factorTwoAntisymmetricAffineSinArchPartial n N =
      factorTwoAntisymmetricAffineSinHeadRaw n +
        ∑ m ∈ Finset.range N,
          factorTwoAntisymmetricAffineSinRankRaw n m := by
  have hheadRate : yoshidaEndpointA / 2 ≠ 0 :=
    div_ne_zero yoshidaEndpointA_pos.ne' (by norm_num)
  have hhead := integral_sinh_mul_factorTwoAffineSin n hheadRate
  have htailRate (m : ℕ) :
      yoshidaEndpointA * oddRate (m + 1) ≠ 0 :=
    mul_ne_zero yoshidaEndpointA_pos.ne' (oddRate_pos _).ne'
  have htail (m : ℕ) :=
    integral_sinh_mul_factorTwoAffineSin n (htailRate m)
  have hheadInt : IntervalIntegrable
      (fun t : ℝ ↦
        2 * Real.exp yoshidaEndpointA *
          Real.sinh (yoshidaEndpointA * t / 2) *
          ((2 - t) * Real.sin (factorTwoNaturalFrequency n * t)))
      volume 0 2 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have htailInt (m : ℕ) : IntervalIntegrable
      (fun t : ℝ ↦
        2 * Real.exp
            (-2 * yoshidaEndpointA * oddRate (m + 1)) *
          Real.sinh
            (yoshidaEndpointA * oddRate (m + 1) * t) *
          ((2 - t) * Real.sin (factorTwoNaturalFrequency n * t)))
      volume 0 2 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have htailSumInt : IntervalIntegrable
      (fun t : ℝ ↦ ∑ m ∈ Finset.range N,
        2 * Real.exp
            (-2 * yoshidaEndpointA * oddRate (m + 1)) *
          Real.sinh
            (yoshidaEndpointA * oddRate (m + 1) * t) *
          ((2 - t) * Real.sin (factorTwoNaturalFrequency n * t)))
      volume 0 2 := by
    apply Continuous.intervalIntegrable
    fun_prop
  unfold factorTwoAntisymmetricAffineSinArchPartial
    factorTwoAntisymmetricRankPartialWeight
  have hpoint : (fun t : ℝ ↦
      (2 * Real.exp yoshidaEndpointA *
          Real.sinh (yoshidaEndpointA * t / 2) +
        ∑ m ∈ Finset.range N,
          2 * Real.exp
              (-2 * yoshidaEndpointA * oddRate (m + 1)) *
            Real.sinh
              (yoshidaEndpointA * oddRate (m + 1) * t)) *
        ((2 - t) * Real.sin (factorTwoNaturalFrequency n * t))) =
      fun t : ℝ ↦
        2 * Real.exp yoshidaEndpointA *
            Real.sinh (yoshidaEndpointA * t / 2) *
            ((2 - t) * Real.sin (factorTwoNaturalFrequency n * t)) +
          ∑ m ∈ Finset.range N,
            2 * Real.exp
                (-2 * yoshidaEndpointA * oddRate (m + 1)) *
              Real.sinh
                (yoshidaEndpointA * oddRate (m + 1) * t) *
              ((2 - t) * Real.sin (factorTwoNaturalFrequency n * t)) := by
    funext t
    simp only [add_mul, Finset.sum_mul]
  rw [hpoint]
  rw [intervalIntegral.integral_add hheadInt htailSumInt,
    intervalIntegral.integral_finset_sum (fun m _hm ↦ htailInt m)]
  rw [show (∫ t : ℝ in 0..2,
      2 * Real.exp yoshidaEndpointA *
        Real.sinh (yoshidaEndpointA * t / 2) *
        ((2 - t) * Real.sin (factorTwoNaturalFrequency n * t))) =
      2 * Real.exp yoshidaEndpointA *
        (∫ t : ℝ in 0..2,
          Real.sinh ((yoshidaEndpointA / 2) * t) *
            ((2 - t) * Real.sin (factorTwoNaturalFrequency n * t))) by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext t
    ring]
  rw [hhead]
  simp_rw [show ∀ m : ℕ,
      (∫ t : ℝ in 0..2,
        2 * Real.exp
            (-2 * yoshidaEndpointA * oddRate (m + 1)) *
          Real.sinh
            (yoshidaEndpointA * oddRate (m + 1) * t) *
          ((2 - t) * Real.sin (factorTwoNaturalFrequency n * t))) =
        2 * Real.exp
            (-2 * yoshidaEndpointA * oddRate (m + 1)) *
          (∫ t : ℝ in 0..2,
            Real.sinh
              ((yoshidaEndpointA * oddRate (m + 1)) * t) *
              ((2 - t) * Real.sin (factorTwoNaturalFrequency n * t))) by
    intro m
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext t
    ring]
  simp_rw [htail]
  unfold factorTwoAntisymmetricAffineSinHeadRaw
    factorTwoAntisymmetricAffineSinRankRaw
  have hsum :
      (∑ m ∈ Finset.range N,
        8 * yoshidaEndpointA *
          Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
          (yoshidaEndpointA * oddRate (m + 1)) *
          factorTwoNaturalFrequency n *
          (Real.cosh
              (2 * (yoshidaEndpointA * oddRate (m + 1))) - 1) /
          (((yoshidaEndpointA * oddRate (m + 1)) ^ 2 +
            factorTwoNaturalFrequency n ^ 2) ^ 2)) =
        -2 * yoshidaEndpointA *
          ∑ m ∈ Finset.range N,
            2 * Real.exp
                (-2 * yoshidaEndpointA * oddRate (m + 1)) *
              (-2 * (yoshidaEndpointA * oddRate (m + 1)) *
                factorTwoNaturalFrequency n *
                (Real.cosh
                    (2 * (yoshidaEndpointA * oddRate (m + 1))) - 1) /
                (((yoshidaEndpointA * oddRate (m + 1)) ^ 2 +
                  factorTwoNaturalFrequency n ^ 2) ^ 2)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _hm
    ring
  rw [hsum]
  ring

theorem factorTwoAntisymmetricAffineSinHeadRaw_nonneg
    {n : ℕ} (hn : n ≠ 0) :
    0 ≤ factorTwoAntisymmetricAffineSinHeadRaw n := by
  have hw : 0 < factorTwoNaturalFrequency n := by
    unfold factorTwoNaturalFrequency
    positivity
  have hdiff : 0 ≤ Real.cosh yoshidaEndpointA - 1 :=
    sub_nonneg.mpr (Real.one_le_cosh _)
  unfold factorTwoAntisymmetricAffineSinHeadRaw
  apply div_nonneg
  · have hpre : 0 ≤ 8 * yoshidaEndpointA * Real.exp yoshidaEndpointA *
        (yoshidaEndpointA / 2) * factorTwoNaturalFrequency n := by
      apply mul_nonneg
      · apply mul_nonneg
        · apply mul_nonneg
          · exact mul_nonneg (by norm_num) yoshidaEndpointA_pos.le
          · exact Real.exp_nonneg _
        · exact div_nonneg yoshidaEndpointA_pos.le (by norm_num)
      · exact hw.le
    exact mul_nonneg hpre hdiff
  · positivity

theorem factorTwoAntisymmetricAffineSinRankRaw_nonneg
    {n : ℕ} (hn : n ≠ 0) (m : ℕ) :
    0 ≤ factorTwoAntisymmetricAffineSinRankRaw n m := by
  have hw : 0 < factorTwoNaturalFrequency n := by
    unfold factorTwoNaturalFrequency
    positivity
  have hdiff : 0 ≤
      Real.cosh (2 * (yoshidaEndpointA * oddRate (m + 1))) - 1 :=
    sub_nonneg.mpr (Real.one_le_cosh _)
  unfold factorTwoAntisymmetricAffineSinRankRaw
  have hr : 0 < oddRate (m + 1) := oddRate_pos _
  have hlambda : 0 ≤ yoshidaEndpointA * oddRate (m + 1) :=
    mul_nonneg yoshidaEndpointA_pos.le hr.le
  apply div_nonneg
  · have hpre : 0 ≤ 8 * yoshidaEndpointA *
        Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
        (yoshidaEndpointA * oddRate (m + 1)) *
        factorTwoNaturalFrequency n := by
      apply mul_nonneg
      · apply mul_nonneg
        · apply mul_nonneg
          · exact mul_nonneg (by norm_num) yoshidaEndpointA_pos.le
          · exact Real.exp_nonneg _
        · exact hlambda
      · exact hw.le
    exact mul_nonneg hpre hdiff
  · positivity

/-- The positive raw ranks have the sum forced by the dominated integral
limit. -/
theorem hasSum_factorTwoAntisymmetricAffineSinRankRaw
    (n : FactorTwoCanonicalEvenIndex) (hn : n.1 ≠ 0) :
    HasSum (factorTwoAntisymmetricAffineSinRankRaw n.1)
      (factorTwoAntisymmetricAffineSinArchMoment n.1 -
        factorTwoAntisymmetricAffineSinHeadRaw n.1) := by
  have hlim := factorTwoAntisymmetricAffineSinArchPartial_tendsto n hn
  have hsub := hlim.sub_const (factorTwoAntisymmetricAffineSinHeadRaw n.1)
  apply (hasSum_iff_tendsto_nat_of_nonneg
    (factorTwoAntisymmetricAffineSinRankRaw_nonneg hn) _).2
  convert hsub using 1
  funext N
  rw [factorTwoAntisymmetricAffineSinArchPartial_eq_raw]
  ring

/-- Honest infinite-series identity before dyadic simplification. -/
theorem factorTwoAntisymmetricAffineSinArchMoment_eq_raw_tsum
    (n : FactorTwoCanonicalEvenIndex) (hn : n.1 ≠ 0) :
    factorTwoAntisymmetricAffineSinArchMoment n.1 =
      factorTwoAntisymmetricAffineSinHeadRaw n.1 +
        ∑' m : ℕ, factorTwoAntisymmetricAffineSinRankRaw n.1 m := by
  rw [(hasSum_factorTwoAntisymmetricAffineSinRankRaw n hn).tsum_eq]
  ring

/-- The growing `sinh` rank is the positive `j = 0` derivative-Cauchy
defect. -/
theorem factorTwoAntisymmetricAffineSinHeadRaw_eq_dyadic (n : ℕ) :
    factorTwoAntisymmetricAffineSinHeadRaw n =
      factorTwoHeadDefect / factorTwoMomentLength *
        factorTwoCauchyU (factorTwoCauchyX 0) (factorTwoMomentY n) := by
  have hsqrtPos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrtSq : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hcoef : Real.exp yoshidaEndpointA *
        (Real.cosh yoshidaEndpointA - 1) =
      factorTwoHeadDefect / 2 := by
    rw [Real.cosh_eq, Real.exp_neg,
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
    factorTwoAntisymmetricAffineSinHeadRaw n =
        4 * yoshidaEndpointA * factorTwoHeadDefect *
          (yoshidaEndpointA / 2) * factorTwoNaturalFrequency n /
          (((yoshidaEndpointA / 2) ^ 2 +
            factorTwoNaturalFrequency n ^ 2) ^ 2) := by
      unfold factorTwoAntisymmetricAffineSinHeadRaw
      rw [show 8 * yoshidaEndpointA * Real.exp yoshidaEndpointA *
            (yoshidaEndpointA / 2) * factorTwoNaturalFrequency n *
            (Real.cosh yoshidaEndpointA - 1) =
          8 * yoshidaEndpointA *
            (Real.exp yoshidaEndpointA *
              (Real.cosh yoshidaEndpointA - 1)) *
            (yoshidaEndpointA / 2) * factorTwoNaturalFrequency n by ring,
        hcoef]
      ring
    _ = _ := by
      rw [hxscale, hyscale]
      unfold factorTwoCauchyU factorTwoMomentLength
      field_simp [hL0, hdenScaled, yoshidaEndpointA_pos.ne']
      ring

/-- Every decaying `sinh` rank is its positive dyadic derivative-Cauchy
kernel; raw rank `m` corresponds to Cauchy index `m + 1`. -/
theorem factorTwoAntisymmetricAffineSinRankRaw_eq_dyadic
    (n m : ℕ) :
    factorTwoAntisymmetricAffineSinRankRaw n m =
      (1 / factorTwoMomentLength) *
        factorTwoAntisymmetricAffineSinDyadicKernel n (m + 1) := by
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
  have hpair : q *
        (Real.cosh (2 * (yoshidaEndpointA * r)) - 1) =
      factorTwoDyadicD (m + 1) / 2 := by
    rw [show q = Real.exp (-(2 * (yoshidaEndpointA * r))) by
      dsimp only [q]
      congr 1
      ring,
      exp_neg_mul_cosh_sub_one]
    unfold factorTwoDyadicD
    rw [← hq]
    rw [show Real.exp (-(2 * (yoshidaEndpointA * r))) = q by
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
    factorTwoAntisymmetricAffineSinRankRaw n m =
        8 * yoshidaEndpointA *
          (q * (Real.cosh (2 * (yoshidaEndpointA * r)) - 1)) *
          (yoshidaEndpointA * r) * factorTwoNaturalFrequency n /
          ((((yoshidaEndpointA * r) ^ 2 +
            factorTwoNaturalFrequency n ^ 2)) ^ 2) := by
      unfold factorTwoAntisymmetricAffineSinRankRaw
      dsimp only [q, r]
      ring
    _ = 8 * yoshidaEndpointA *
          (factorTwoDyadicD (m + 1) / 2) *
          (yoshidaEndpointA * r) * factorTwoNaturalFrequency n /
          ((((yoshidaEndpointA * r) ^ 2 +
            factorTwoNaturalFrequency n ^ 2)) ^ 2) := by rw [hpair]
    _ = _ := by
      rw [hxr, hwy]
      unfold factorTwoAntisymmetricAffineSinDyadicKernel factorTwoCauchyU
      have hA : yoshidaEndpointA = factorTwoMomentLength / 2 := by
        unfold factorTwoMomentLength
        ring
      rw [hA]
      field_simp [hL0, hdenScaled]
      ring

/-- The archimedean affine-sine moment as the exact positive growing-head term
followed by the positive dyadic derivative-Cauchy series. -/
theorem factorTwoAntisymmetricAffineSinArchMoment_eq_dyadicCauchySeries
    (n : FactorTwoCanonicalEvenIndex) (hn : n.1 ≠ 0) :
    factorTwoAntisymmetricAffineSinArchMoment n.1 =
      factorTwoHeadDefect / factorTwoMomentLength *
          factorTwoCauchyU (factorTwoCauchyX 0) (factorTwoMomentY n.1) +
        (1 / factorTwoMomentLength) *
          ∑' m : ℕ,
            factorTwoAntisymmetricAffineSinDyadicKernel n.1 (m + 1) := by
  rw [factorTwoAntisymmetricAffineSinArchMoment_eq_raw_tsum n hn,
    factorTwoAntisymmetricAffineSinHeadRaw_eq_dyadic]
  rw [show (∑' m : ℕ, factorTwoAntisymmetricAffineSinRankRaw n.1 m) =
      ∑' m : ℕ,
        (1 / factorTwoMomentLength) *
          factorTwoAntisymmetricAffineSinDyadicKernel n.1 (m + 1) by
    apply tsum_congr
    intro m
    exact factorTwoAntisymmetricAffineSinRankRaw_eq_dyadic n.1 m]
  rw [tsum_mul_left]

/-- Full antisymmetric affine-sine perturbation moment, including the exact
retained `p = 3` atom. -/
theorem factorTwoAntisymmetricAffineSinMoment_eq_dyadicCauchySeries
    (n : FactorTwoCanonicalEvenIndex) (hn : n.1 ≠ 0) :
    factorTwoAntisymmetricAffineSinMoment n.1 =
      factorTwoHeadDefect / factorTwoMomentLength *
          factorTwoCauchyU (factorTwoCauchyX 0) (factorTwoMomentY n.1) +
        (1 / factorTwoMomentLength) *
          ∑' m : ℕ,
            factorTwoAntisymmetricAffineSinDyadicKernel n.1 (m + 1) +
        2 * (Real.log 3 / Real.sqrt 3) *
          (2 - 2 * factorTwoPrimeShift / factorTwoMomentLength) *
          Real.sin
            (2 * factorTwoMomentY n.1 * factorTwoPrimeShift) := by
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
  unfold factorTwoAntisymmetricAffineSinMoment
    factorTwoAntisymmetricPerturbationFunctional
  change factorTwoAntisymmetricAffineSinArchMoment n.1 +
      2 * (Real.log 3 / Real.sqrt 3) *
        ((2 - factorTwoPrimeShift / yoshidaEndpointA) *
          Real.sin (factorTwoNaturalFrequency n.1 *
            (factorTwoPrimeShift / yoshidaEndpointA))) = _
  rw [factorTwoAntisymmetricAffineSinArchMoment_eq_dyadicCauchySeries n hn,
    hheight, harg]
  ring

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhasePerturbationAffineSinSeries

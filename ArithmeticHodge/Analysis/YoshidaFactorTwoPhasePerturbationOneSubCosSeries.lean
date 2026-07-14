import ArithmeticHodge.Analysis.YoshidaFactorTwoPhasePerturbationMomentSeries

set_option autoImplicit false
set_option maxRecDepth 100000

open Filter MeasureTheory Real Set Topology
open scoped BigOperators Interval

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhasePerturbationOneSubCosSeries

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
# Dyadic Cauchy series for the factor-two one-minus-cosine moment

The antisymmetric adjacent-cell weight is a positive sum of hyperbolic sine
ranks on the open overlap interval.  Its endpoint singularity is cancelled by
`1 - cos`, so finite positive rank sums may be passed through the integral by
dominated convergence.  A complete-period transform then turns every rank
into the asserted positive dyadic Cauchy kernel; the perturbation functional
contributes the overall minus sign.
-/

/-- The positive dyadic Cauchy rank used by the antisymmetric cosine defect. -/
def factorTwoAntisymmetricOneSubCosDyadicTerm (n j : ℕ) : ℝ :=
  factorTwoDyadicD j * factorTwoMomentY n ^ 2 /
    (factorTwoCauchyX j *
      (factorTwoCauchyX j ^ 2 + factorTwoMomentY n ^ 2))

/-- The archimedean part before the retained `p = 3` atom. -/
def factorTwoAntisymmetricOneSubCosArchMoment (n : ℕ) : ℝ :=
  -2 * yoshidaEndpointA *
    ∫ t : ℝ in 0..2,
      factorTwoAntisymmetricWeight (yoshidaEndpointA * t) *
        (1 - Real.cos (factorTwoNaturalFrequency n * t))

/-- The first `N` positive antisymmetric hyperbolic ranks. -/
def factorTwoAntisymmetricRankPartialWeight (N : ℕ) (t : ℝ) : ℝ :=
  2 * Real.exp yoshidaEndpointA *
      Real.sinh (yoshidaEndpointA * t / 2) +
    ∑ m ∈ Finset.range N,
      2 * Real.exp
          (-2 * yoshidaEndpointA * oddRate (m + 1)) *
        Real.sinh
          (yoshidaEndpointA * oddRate (m + 1) * t)

/-- Finite-rank approximation to the antisymmetric archimedean moment. -/
def factorTwoAntisymmetricOneSubCosArchPartial (n N : ℕ) : ℝ :=
  -2 * yoshidaEndpointA *
    ∫ t : ℝ in 0..2,
      factorTwoAntisymmetricRankPartialWeight N t *
        (1 - Real.cos (factorTwoNaturalFrequency n * t))

/-- The complete antisymmetric adjacent-cell weight is one growing sine rank
followed by the positive half-odd decaying-rank series. -/
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
      have hscaled := (hasSum_oddExponentials hz).summable.mul_left (1 / 2 : ℝ)
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
      dsimp only [zp]; ring,
    show 2 * yoshidaEndpointA - yoshidaEndpointA * t = zm by
      dsimp only [zm]; ring,
    factorTwoAdjacentSmoothKernel_eq_exp_sub_tsum hzp,
    factorTwoAdjacentSmoothKernel_eq_exp_sub_tsum hzm]
  linear_combination hhead + hsum

/-- The positive antisymmetric tail is summable at every point before the
singular endpoint. -/
theorem summable_factorTwoAntisymmetricRankTail
    {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t < 2) :
    Summable (fun m : ℕ ↦
      2 * Real.exp
          (-2 * yoshidaEndpointA * oddRate (m + 1)) *
        Real.sinh
          (yoshidaEndpointA * oddRate (m + 1) * t)) := by
  have hs := summable_factorTwoSymmetricRankTail ht0 ht2
  apply hs.of_norm_bounded
  intro m
  have harg : 0 ≤ yoshidaEndpointA * oddRate (m + 1) * t := by
    exact mul_nonneg
      (mul_nonneg yoshidaEndpointA_pos.le (oddRate_pos _).le) ht0
  have hsinh0 : 0 ≤ Real.sinh
      (yoshidaEndpointA * oddRate (m + 1) * t) :=
    Real.sinh_nonneg_iff.mpr harg
  have hsinhCosh : Real.sinh
        (yoshidaEndpointA * oddRate (m + 1) * t) ≤
      Real.cosh (yoshidaEndpointA * oddRate (m + 1) * t) := by
    rw [Real.sinh_eq, Real.cosh_eq]
    linarith [Real.exp_pos
      (-(yoshidaEndpointA * oddRate (m + 1) * t))]
  rw [Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (by positivity) hsinh0)]
  exact mul_le_mul_of_nonneg_left hsinhCosh (by positivity)

/-- Pointwise convergence of finite positive antisymmetric rank sums. -/
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

private def sinhOneSubCosPrimitive (lambda omega u : ℝ) : ℝ :=
  Real.cosh (lambda * u) / lambda -
    (lambda * Real.cosh (lambda * u) * Real.cos (omega * u) +
      omega * Real.sinh (lambda * u) * Real.sin (omega * u)) /
      (lambda ^ 2 + omega ^ 2)

private theorem sinhOneSubCosPrimitive_hasDerivAt
    {lambda omega u : ℝ} (hlambda : lambda ≠ 0)
    (hden : lambda ^ 2 + omega ^ 2 ≠ 0) :
    HasDerivAt (sinhOneSubCosPrimitive lambda omega)
      (Real.sinh (lambda * u) * (1 - Real.cos (omega * u))) u := by
  have hlu : HasDerivAt (fun x : ℝ ↦ lambda * x) lambda u := by
    simpa using (hasDerivAt_id u).const_mul lambda
  have hwu : HasDerivAt (fun x : ℝ ↦ omega * x) omega u := by
    simpa using (hasDerivAt_id u).const_mul omega
  have hcosh : HasDerivAt (fun x : ℝ ↦ Real.cosh (lambda * x))
      (Real.sinh (lambda * u) * lambda) u :=
    Real.hasDerivAt_cosh (lambda * u) |>.comp u hlu
  have hsinh : HasDerivAt (fun x : ℝ ↦ Real.sinh (lambda * x))
      (Real.cosh (lambda * u) * lambda) u :=
    Real.hasDerivAt_sinh (lambda * u) |>.comp u hlu
  have hcos : HasDerivAt (fun x : ℝ ↦ Real.cos (omega * x))
      (-Real.sin (omega * u) * omega) u := by
    simpa only [Function.comp_apply] using
      (Real.hasDerivAt_cos (omega * u) |>.comp u hwu)
  have hsin : HasDerivAt (fun x : ℝ ↦ Real.sin (omega * x))
      (Real.cos (omega * u) * omega) u :=
    Real.hasDerivAt_sin (omega * u) |>.comp u hwu
  have hfirst := hcosh.div_const lambda
  have hsecond :=
    (((hcosh.mul hcos).const_mul lambda).add
      ((hsinh.mul hsin).const_mul omega)).div_const
        (lambda ^ 2 + omega ^ 2)
  unfold sinhOneSubCosPrimitive
  convert hfirst.sub hsecond using 1
  · funext x
    simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply, div_eq_mul_inv]
    ring
  · field_simp [hlambda, hden]
    ring

/-- Complete-period transform of one positive hyperbolic sine rank. -/
theorem integral_sinh_mul_one_sub_factorTwoCos
    {n : ℕ} (hn : n ≠ 0) {lambda : ℝ} (hlambda : lambda ≠ 0) :
    (∫ t : ℝ in 0..2,
      Real.sinh (lambda * t) *
        (1 - Real.cos (factorTwoNaturalFrequency n * t))) =
      factorTwoNaturalFrequency n ^ 2 *
          (Real.cosh (2 * lambda) - 1) /
        (lambda *
          (lambda ^ 2 + factorTwoNaturalFrequency n ^ 2)) := by
  have hw : factorTwoNaturalFrequency n ≠ 0 := by
    unfold factorTwoNaturalFrequency
    exact mul_ne_zero Real.pi_ne_zero (Nat.cast_ne_zero.mpr hn)
  have hden : lambda ^ 2 + factorTwoNaturalFrequency n ^ 2 ≠ 0 := by
    positivity
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 2,
      HasDerivAt
        (sinhOneSubCosPrimitive lambda (factorTwoNaturalFrequency n))
        (Real.sinh (lambda * t) *
          (1 - Real.cos (factorTwoNaturalFrequency n * t))) t :=
    fun t _ ↦ sinhOneSubCosPrimitive_hasDerivAt hlambda hden
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
  rw [h]
  simp only [sinhOneSubCosPrimitive, mul_zero, Real.cosh_zero,
    Real.sinh_zero, Real.cos_zero, Real.sin_zero,
    factorTwoNaturalFrequency_mul_two_sin n,
    factorTwoNaturalFrequency_mul_two_cos n]
  field_simp [hlambda, hden]
  ring

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
  exact mul_nonneg (by positivity)
    (Real.sinh_nonneg_iff.mpr <| mul_nonneg
      (mul_nonneg yoshidaEndpointA_pos.le (oddRate_pos _).le) ht0)

/-- Dominated passage from finite positive hyperbolic ranks to the complete
antisymmetric one-minus-cosine transform. -/
theorem factorTwoAntisymmetricOneSubCosArchPartial_tendsto
    (n : FactorTwoCanonicalEvenIndex) (hn : n.1 ≠ 0) :
    Tendsto
      (fun N : ℕ ↦ factorTwoAntisymmetricOneSubCosArchPartial n.1 N)
      atTop
      (nhds (factorTwoAntisymmetricOneSubCosArchMoment n.1)) := by
  let C : ℝ → ℝ := fun t ↦
    1 - Real.cos (factorTwoNaturalFrequency n.1 * t)
  let H : ℝ → ℝ := fun t ↦
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
      intervalIntegrable_factorTwoAntisymmetricOneSubCosMoment n.1 hn
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
    have hS0 : 0 ≤ S := by
      dsimp only [S]
      apply Finset.sum_nonneg
      intro m _hm
      exact mul_nonneg (by positivity)
        (Real.sinh_nonneg_iff.mpr <| mul_nonneg
          (mul_nonneg yoshidaEndpointA_pos.le (oddRate_pos _).le) ht0)
    have hST : S ≤ T := by
      simpa only [S, T] using
        factorTwoAntisymmetricRankPartialTail_le_tsum ht0 htlt2 N
    have hT0 : 0 ≤ T := hS0.trans hST
    have hH0 : 0 ≤ H t := by
      dsimp only [H]
      exact mul_nonneg (by positivity)
        (Real.sinh_nonneg_iff.mpr <| by
          exact div_nonneg
            (mul_nonneg yoshidaEndpointA_pos.le ht0) (by norm_num))
    have hC0 : 0 ≤ C t := by
      dsimp only [C]
      exact sub_nonneg.mpr (Real.cos_le_one _)
    have hseries := factorTwoAntisymmetricWeight_eq_rankOneSeries ht0 htlt2
    change W t = H t + T at hseries
    have hpartial0 : 0 ≤ (H t + S) * C t :=
      mul_nonneg (add_nonneg hH0 hS0) hC0
    have hcomplete0 : 0 ≤ W t * C t := by
      rw [hseries]
      exact mul_nonneg (add_nonneg hH0 hT0) hC0
    dsimp only [F, B, factorTwoAntisymmetricRankPartialWeight]
    change ‖(H t + S) * C t‖ ≤ |W t * C t|
    rw [Real.norm_eq_abs, abs_of_nonneg hpartial0,
      abs_of_nonneg hcomplete0, hseries]
    exact mul_le_mul_of_nonneg_right (by linarith) hC0
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
  simpa only [factorTwoAntisymmetricOneSubCosArchPartial,
    factorTwoAntisymmetricOneSubCosArchMoment, F, W, C] using hScaled

/-- Raw contribution of the growing antisymmetric rank. -/
def factorTwoAntisymmetricOneSubCosHeadRaw (n : ℕ) : ℝ :=
  -2 * yoshidaEndpointA * 2 * Real.exp yoshidaEndpointA *
    (factorTwoNaturalFrequency n ^ 2 *
        (Real.cosh yoshidaEndpointA - 1) /
      ((yoshidaEndpointA / 2) *
        ((yoshidaEndpointA / 2) ^ 2 +
          factorTwoNaturalFrequency n ^ 2)))

/-- Raw contribution of the `m`th decaying antisymmetric rank. -/
def factorTwoAntisymmetricOneSubCosRankRaw (n m : ℕ) : ℝ :=
  -2 * yoshidaEndpointA * 2 *
    Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
    (factorTwoNaturalFrequency n ^ 2 *
        (Real.cosh (2 * yoshidaEndpointA * oddRate (m + 1)) - 1) /
      ((yoshidaEndpointA * oddRate (m + 1)) *
        ((yoshidaEndpointA * oddRate (m + 1)) ^ 2 +
          factorTwoNaturalFrequency n ^ 2)))

/-- Every finite antisymmetric hyperbolic approximation is the corresponding
finite sum of raw one-minus-cosine ranks. -/
theorem factorTwoAntisymmetricOneSubCosArchPartial_eq_raw
    {n : ℕ} (hn : n ≠ 0) (N : ℕ) :
    factorTwoAntisymmetricOneSubCosArchPartial n N =
      factorTwoAntisymmetricOneSubCosHeadRaw n +
        ∑ m ∈ Finset.range N,
          factorTwoAntisymmetricOneSubCosRankRaw n m := by
  have hheadRate : yoshidaEndpointA / 2 ≠ 0 :=
    div_ne_zero yoshidaEndpointA_pos.ne' (by norm_num)
  have hhead := integral_sinh_mul_one_sub_factorTwoCos hn hheadRate
  have htailRate (m : ℕ) :
      yoshidaEndpointA * oddRate (m + 1) ≠ 0 :=
    mul_ne_zero yoshidaEndpointA_pos.ne' (oddRate_pos _).ne'
  have htail (m : ℕ) :=
    integral_sinh_mul_one_sub_factorTwoCos hn (htailRate m)
  have hheadInt : IntervalIntegrable
      (fun t : ℝ ↦
        2 * Real.exp yoshidaEndpointA *
          Real.sinh (yoshidaEndpointA * t / 2) *
          (1 - Real.cos (factorTwoNaturalFrequency n * t)))
      volume 0 2 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have htailInt (m : ℕ) : IntervalIntegrable
      (fun t : ℝ ↦
        2 * Real.exp
            (-2 * yoshidaEndpointA * oddRate (m + 1)) *
          Real.sinh
            (yoshidaEndpointA * oddRate (m + 1) * t) *
          (1 - Real.cos (factorTwoNaturalFrequency n * t)))
      volume 0 2 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have htailSumInt : IntervalIntegrable
      (fun t : ℝ ↦ ∑ m ∈ Finset.range N,
        2 * Real.exp
            (-2 * yoshidaEndpointA * oddRate (m + 1)) *
          Real.sinh
            (yoshidaEndpointA * oddRate (m + 1) * t) *
          (1 - Real.cos (factorTwoNaturalFrequency n * t)))
      volume 0 2 := by
    apply Continuous.intervalIntegrable
    fun_prop
  unfold factorTwoAntisymmetricOneSubCosArchPartial
    factorTwoAntisymmetricRankPartialWeight
  have hpoint : (fun t : ℝ ↦
      (2 * Real.exp yoshidaEndpointA *
          Real.sinh (yoshidaEndpointA * t / 2) +
        ∑ m ∈ Finset.range N,
          2 * Real.exp
              (-2 * yoshidaEndpointA * oddRate (m + 1)) *
            Real.sinh
              (yoshidaEndpointA * oddRate (m + 1) * t)) *
        (1 - Real.cos (factorTwoNaturalFrequency n * t))) =
      fun t : ℝ ↦
        2 * Real.exp yoshidaEndpointA *
            Real.sinh (yoshidaEndpointA * t / 2) *
            (1 - Real.cos (factorTwoNaturalFrequency n * t)) +
          ∑ m ∈ Finset.range N,
            2 * Real.exp
                (-2 * yoshidaEndpointA * oddRate (m + 1)) *
              Real.sinh
                (yoshidaEndpointA * oddRate (m + 1) * t) *
              (1 - Real.cos (factorTwoNaturalFrequency n * t)) := by
    funext t
    simp only [add_mul, Finset.sum_mul]
  rw [hpoint]
  rw [intervalIntegral.integral_add hheadInt htailSumInt,
    intervalIntegral.integral_finset_sum (fun m _hm ↦ htailInt m)]
  rw [show (∫ t : ℝ in 0..2,
      2 * Real.exp yoshidaEndpointA *
        Real.sinh (yoshidaEndpointA * t / 2) *
        (1 - Real.cos (factorTwoNaturalFrequency n * t))) =
      2 * Real.exp yoshidaEndpointA *
        (∫ t : ℝ in 0..2,
          Real.sinh ((yoshidaEndpointA / 2) * t) *
            (1 - Real.cos (factorTwoNaturalFrequency n * t))) by
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
          (1 - Real.cos (factorTwoNaturalFrequency n * t))) =
        2 * Real.exp
            (-2 * yoshidaEndpointA * oddRate (m + 1)) *
          (∫ t : ℝ in 0..2,
            Real.sinh
              ((yoshidaEndpointA * oddRate (m + 1)) * t) *
              (1 - Real.cos (factorTwoNaturalFrequency n * t))) by
    intro m
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext t
    ring]
  simp_rw [htail]
  unfold factorTwoAntisymmetricOneSubCosHeadRaw
    factorTwoAntisymmetricOneSubCosRankRaw
  rw [show 2 * (yoshidaEndpointA / 2) = yoshidaEndpointA by ring,
    mul_add, Finset.mul_sum]
  ring

/-- The growing hyperbolic sine rank is the negative `j = 0` dyadic defect. -/
theorem factorTwoAntisymmetricOneSubCosHeadRaw_eq_dyadic (n : ℕ) :
    factorTwoAntisymmetricOneSubCosHeadRaw n =
      -factorTwoHeadDefect * factorTwoMomentY n ^ 2 /
        (factorTwoCauchyX 0 *
          (factorTwoCauchyX 0 ^ 2 + factorTwoMomentY n ^ 2)) := by
  have hsqrtPos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrtSq : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hcoef :
      2 * Real.exp yoshidaEndpointA *
          (Real.cosh yoshidaEndpointA - 1) =
        factorTwoHeadDefect := by
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
    factorTwoAntisymmetricOneSubCosHeadRaw n =
        -2 * yoshidaEndpointA *
          (2 * Real.exp yoshidaEndpointA *
            (Real.cosh yoshidaEndpointA - 1)) *
          factorTwoNaturalFrequency n ^ 2 /
          ((yoshidaEndpointA / 2) *
            ((yoshidaEndpointA / 2) ^ 2 +
              factorTwoNaturalFrequency n ^ 2)) := by
      unfold factorTwoAntisymmetricOneSubCosHeadRaw
      ring
    _ = -2 * yoshidaEndpointA * factorTwoHeadDefect *
          factorTwoNaturalFrequency n ^ 2 /
          ((yoshidaEndpointA / 2) *
            ((yoshidaEndpointA / 2) ^ 2 +
              factorTwoNaturalFrequency n ^ 2)) := by rw [hcoef]
    _ = _ := by
      rw [hxscale, hyscale]
      rw [show (-2 : ℝ) * yoshidaEndpointA = -factorTwoMomentLength by
        unfold factorTwoMomentLength
        ring]
      field_simp [hL0, hx.ne', hdenScaled]

/-- Raw decaying rank `m` is minus its positive dyadic Cauchy rank at index
`m + 1`. -/
theorem factorTwoAntisymmetricOneSubCosRankRaw_eq_dyadic
    (n m : ℕ) :
    factorTwoAntisymmetricOneSubCosRankRaw n m =
      -factorTwoAntisymmetricOneSubCosDyadicTerm n (m + 1) := by
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
  have hqexp : Real.exp (-(2 * (yoshidaEndpointA * r))) = q := by
    dsimp only [q]
    congr 1
    ring
  have hpair :
      2 * q * (Real.cosh (2 * yoshidaEndpointA * r) - 1) =
        factorTwoDyadicD (m + 1) := by
    have hbase := exp_neg_mul_cosh_sub_one
      (2 * (yoshidaEndpointA * r))
    rw [hqexp] at hbase
    rw [show 2 * yoshidaEndpointA * r =
      2 * (yoshidaEndpointA * r) by ring]
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
    factorTwoAntisymmetricOneSubCosRankRaw n m =
        -2 * yoshidaEndpointA *
          (2 * q *
            (Real.cosh (2 * yoshidaEndpointA * r) - 1)) *
          factorTwoNaturalFrequency n ^ 2 /
          ((yoshidaEndpointA * r) *
            ((yoshidaEndpointA * r) ^ 2 +
              factorTwoNaturalFrequency n ^ 2)) := by
      unfold factorTwoAntisymmetricOneSubCosRankRaw
      dsimp only [q, r]
      ring
    _ = -2 * yoshidaEndpointA * factorTwoDyadicD (m + 1) *
          factorTwoNaturalFrequency n ^ 2 /
          ((yoshidaEndpointA * r) *
            ((yoshidaEndpointA * r) ^ 2 +
              factorTwoNaturalFrequency n ^ 2)) := by rw [hpair]
    _ = _ := by
      rw [hxr, hwy]
      rw [show (-2 : ℝ) * yoshidaEndpointA = -factorTwoMomentLength by
        unfold factorTwoMomentLength
        ring]
      unfold factorTwoAntisymmetricOneSubCosDyadicTerm
      field_simp [hL0, hx.ne', hdenScaled]

theorem factorTwoAntisymmetricOneSubCosDyadicTerm_nonneg
    (n j : ℕ) :
    0 ≤ factorTwoAntisymmetricOneSubCosDyadicTerm n j := by
  have hx : 0 < factorTwoCauchyX j := by
    unfold factorTwoCauchyX
    positivity
  unfold factorTwoAntisymmetricOneSubCosDyadicTerm
    factorTwoDyadicD
  exact div_nonneg
    (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (mul_nonneg hx.le (by positivity))

theorem factorTwoAntisymmetricOneSubCosRankRaw_nonpos
    (n m : ℕ) :
    factorTwoAntisymmetricOneSubCosRankRaw n m ≤ 0 := by
  rw [factorTwoAntisymmetricOneSubCosRankRaw_eq_dyadic]
  exact neg_nonpos.mpr
    (factorTwoAntisymmetricOneSubCosDyadicTerm_nonneg n (m + 1))

/-- The raw negative ranks have the sum forced by the dominated integral
limit. -/
theorem hasSum_factorTwoAntisymmetricOneSubCosRankRaw
    (n : FactorTwoCanonicalEvenIndex) (hn : n.1 ≠ 0) :
    HasSum (factorTwoAntisymmetricOneSubCosRankRaw n.1)
      (factorTwoAntisymmetricOneSubCosArchMoment n.1 -
        factorTwoAntisymmetricOneSubCosHeadRaw n.1) := by
  have hlim := factorTwoAntisymmetricOneSubCosArchPartial_tendsto n hn
  have hnegLim :=
    (tendsto_const_nhds.sub hlim :
      Tendsto
        (fun N : ℕ ↦ factorTwoAntisymmetricOneSubCosHeadRaw n.1 -
          factorTwoAntisymmetricOneSubCosArchPartial n.1 N)
        atTop
        (nhds (factorTwoAntisymmetricOneSubCosHeadRaw n.1 -
          factorTwoAntisymmetricOneSubCosArchMoment n.1)))
  have hnonneg (m : ℕ) :
      0 ≤ -factorTwoAntisymmetricOneSubCosRankRaw n.1 m :=
    neg_nonneg.mpr
      (factorTwoAntisymmetricOneSubCosRankRaw_nonpos n.1 m)
  have hnegSum :
      HasSum (fun m : ℕ ↦
        -factorTwoAntisymmetricOneSubCosRankRaw n.1 m)
        (factorTwoAntisymmetricOneSubCosHeadRaw n.1 -
          factorTwoAntisymmetricOneSubCosArchMoment n.1) := by
    apply (hasSum_iff_tendsto_nat_of_nonneg hnonneg _).2
    convert hnegLim using 1
    funext N
    rw [factorTwoAntisymmetricOneSubCosArchPartial_eq_raw hn N,
      Finset.sum_neg_distrib]
    ring
  convert hnegSum.neg using 1
  · funext m
    simp only [neg_neg]
  · ring

/-- Honest infinite-series identity before the dyadic normalization. -/
theorem factorTwoAntisymmetricOneSubCosArchMoment_eq_raw_tsum
    (n : FactorTwoCanonicalEvenIndex) (hn : n.1 ≠ 0) :
    factorTwoAntisymmetricOneSubCosArchMoment n.1 =
      factorTwoAntisymmetricOneSubCosHeadRaw n.1 +
        ∑' m : ℕ,
          factorTwoAntisymmetricOneSubCosRankRaw n.1 m := by
  rw [(hasSum_factorTwoAntisymmetricOneSubCosRankRaw n hn).tsum_eq]
  ring

/-- The archimedean one-minus-cosine moment is the negative head Cauchy rank
minus the exact positive dyadic tail. -/
theorem factorTwoAntisymmetricOneSubCosArchMoment_eq_dyadicCauchySeries
    (n : FactorTwoCanonicalEvenIndex) (hn : n.1 ≠ 0) :
    factorTwoAntisymmetricOneSubCosArchMoment n.1 =
      -factorTwoHeadDefect * factorTwoMomentY n.1 ^ 2 /
          (factorTwoCauchyX 0 *
            (factorTwoCauchyX 0 ^ 2 + factorTwoMomentY n.1 ^ 2)) -
        ∑' m : ℕ,
          factorTwoAntisymmetricOneSubCosDyadicTerm n.1 (m + 1) := by
  rw [factorTwoAntisymmetricOneSubCosArchMoment_eq_raw_tsum n hn,
    factorTwoAntisymmetricOneSubCosHeadRaw_eq_dyadic]
  rw [show
      (∑' m : ℕ, factorTwoAntisymmetricOneSubCosRankRaw n.1 m) =
        ∑' m : ℕ,
          -factorTwoAntisymmetricOneSubCosDyadicTerm n.1 (m + 1) by
    apply tsum_congr
    intro m
    exact factorTwoAntisymmetricOneSubCosRankRaw_eq_dyadic n.1 m,
    tsum_neg]
  ring

/-- Full antisymmetric one-minus-cosine perturbation moment for a positive
canonical integer mode, including the retained `p = 3` phase atom. -/
theorem factorTwoAntisymmetricOneSubCosMoment_eq_dyadicCauchySeries
    (n : FactorTwoCanonicalEvenIndex) (hn : n.1 ≠ 0) :
    factorTwoAntisymmetricOneSubCosMoment n.1 =
      -factorTwoHeadDefect * factorTwoMomentY n.1 ^ 2 /
          (factorTwoCauchyX 0 *
            (factorTwoCauchyX 0 ^ 2 + factorTwoMomentY n.1 ^ 2)) -
        (∑' m : ℕ,
          factorTwoDyadicD (m + 1) * factorTwoMomentY n.1 ^ 2 /
            (factorTwoCauchyX (m + 1) *
              (factorTwoCauchyX (m + 1) ^ 2 +
                factorTwoMomentY n.1 ^ 2))) +
        2 * (Real.log 3 / Real.sqrt 3) *
          (1 - Real.cos
            (2 * factorTwoMomentY n.1 * factorTwoPrimeShift)) := by
  have harg : factorTwoNaturalFrequency n.1 *
        (factorTwoPrimeShift / yoshidaEndpointA) =
      2 * factorTwoMomentY n.1 * factorTwoPrimeShift := by
    unfold factorTwoMomentY factorTwoMomentLength
    field_simp [yoshidaEndpointA_pos.ne']
  unfold factorTwoAntisymmetricOneSubCosMoment
    factorTwoAntisymmetricPerturbationFunctional
  change factorTwoAntisymmetricOneSubCosArchMoment n.1 +
      2 * (Real.log 3 / Real.sqrt 3) *
        (1 - Real.cos
          (factorTwoNaturalFrequency n.1 *
            (factorTwoPrimeShift / yoshidaEndpointA))) = _
  rw [factorTwoAntisymmetricOneSubCosArchMoment_eq_dyadicCauchySeries n hn,
    harg]
  simp only [factorTwoAntisymmetricOneSubCosDyadicTerm]

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhasePerturbationOneSubCosSeries

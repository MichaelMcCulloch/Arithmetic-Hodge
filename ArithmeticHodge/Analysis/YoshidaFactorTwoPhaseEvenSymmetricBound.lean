import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseRankLimit
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseSymmetricCarleman

set_option autoImplicit false

open Complex MeasureTheory Real Set
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseEvenSymmetricBound

noncomputable section

open CenteredEndpointCorrelation
open YoshidaEndpointHyperbolicBound
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoAdjacentKernel
open YoshidaFactorTwoCrossDistribution
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoPhaseEnvelope
open YoshidaFactorTwoPhaseRankLimit
open YoshidaFactorTwoPhaseSymmetricCarleman
open YoshidaFactorTwoPhaseSymmetricCoercivity
open YoshidaFactorTwoPhaseTailCoercivity
open YoshidaRenormalizedGeometricKernel

/-!
# The easy side of the even symmetric factor-two bound

The exact even rank expansion is one positive growing square minus a
nonnegative decaying-rank series.  Cauchy--Schwarz controls the growing square
with its exact `cosh` mass.  After subtracting the positive prime block, the
dyadic coefficient cancels and leaves `1 / 2 + beta / 2 < 1`.
-/

/-- Exact squared `cosh` mass on the scaled centered interval. -/
theorem integral_cosh_scaled_sq
    {a : ℝ} (ha : a ≠ 0) :
    (∫ x : ℝ in -1..1, Real.cosh (a * x / 2) ^ 2) =
      (Real.sinh a + a) / a := by
  have hpoint (x : ℝ) :
      Real.cosh (a * x / 2) ^ 2 =
        Real.sinh (a * x / 2) ^ 2 + 1 := by
    nlinarith [Real.cosh_sq_sub_sinh_sq (a * x / 2)]
  rw [show (fun x : ℝ ↦ Real.cosh (a * x / 2) ^ 2) =
      fun x ↦ Real.sinh (a * x / 2) ^ 2 + 1 by
    funext x
    exact hpoint x]
  rw [intervalIntegral.integral_add
    ((by fun_prop : Continuous (fun x : ℝ ↦
      Real.sinh (a * x / 2) ^ 2)).intervalIntegrable _ _)
    (continuous_const.intervalIntegrable _ _),
    integral_sinh_scaled_sq ha]
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  field_simp [ha]
  ring

/-- Cauchy--Schwarz control of the positive endpoint `cosh` moment. -/
theorem normSq_integral_cosh_scaled_le
    {a : ℝ} (ha : 0 < a) (f : ℝ → ℂ) (hf : Continuous f) :
    Complex.normSq
        (∫ x : ℝ in -1..1, (Real.cosh (a * x / 2) : ℂ) * f x) ≤
      ((Real.sinh a + a) / a) *
        (∫ x : ℝ in -1..1, ‖f x‖ ^ 2) := by
  let I : Set ℝ := Set.Ioc (-1) 1
  let μ : Measure ℝ := volume.restrict I
  let c : ℝ → ℂ := fun x ↦ (Real.cosh (a * x / 2) : ℂ)
  have hcMeas : AEStronglyMeasurable c μ := by
    exact (by fun_prop : Continuous c).aestronglyMeasurable.restrict
  have hc : MemLp c 2 μ := by
    rw [memLp_two_iff_integrable_sq_norm hcMeas]
    have hcompact : IntegrableOn (fun x : ℝ ↦ ‖c x‖ ^ 2)
        (Set.Icc (-1) 1) :=
      (by fun_prop : Continuous (fun x : ℝ ↦ ‖c x‖ ^ 2))
        |>.continuousOn.integrableOn_compact isCompact_Icc
    exact hcompact.mono_set Set.Ioc_subset_Icc_self
  have hfMeas : AEStronglyMeasurable f μ :=
    hf.aestronglyMeasurable.restrict
  have hfLp : MemLp f 2 μ := by
    rw [memLp_two_iff_integrable_sq_norm hfMeas]
    have hcompact : IntegrableOn (fun x : ℝ ↦ ‖f x‖ ^ 2)
        (Set.Icc (-1) 1) :=
      (hf.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
    exact hcompact.mono_set Set.Ioc_subset_Icc_self
  have hc' : MemLp c (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using hc
  have hf' : MemLp f (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using hfLp
  have hholder := integral_mul_norm_le_Lp_mul_Lq
    (p := 2) (q := 2) (f := c) (g := f) (μ := μ)
    Real.HolderConjugate.two_two hc' hf'
  have hA0 : 0 ≤ ∫ x : ℝ, ‖c x‖ ^ 2 ∂μ :=
    integral_nonneg fun _ ↦ sq_nonneg _
  have hB0 : 0 ≤ ∫ x : ℝ, ‖f x‖ ^ 2 ∂μ :=
    integral_nonneg fun _ ↦ sq_nonneg _
  have hholder' :
      (∫ x : ℝ, ‖c x‖ * ‖f x‖ ∂μ) ≤
        Real.sqrt (∫ x : ℝ, ‖c x‖ ^ 2 ∂μ) *
          Real.sqrt (∫ x : ℝ, ‖f x‖ ^ 2 ∂μ) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    simpa only [Real.rpow_two] using hholder
  have hnorm :
      ‖∫ x : ℝ in -1..1, c x * f x‖ ≤
        ∫ x : ℝ, ‖c x‖ * ‖f x‖ ∂μ := by
    calc
      ‖∫ x : ℝ in -1..1, c x * f x‖ ≤
          ∫ x : ℝ in -1..1, ‖c x * f x‖ :=
        intervalIntegral.norm_integral_le_integral_norm (by norm_num)
      _ = ∫ x : ℝ in -1..1, ‖c x‖ * ‖f x‖ := by
        apply intervalIntegral.integral_congr
        intro x _
        change ‖c x * f x‖ = ‖c x‖ * ‖f x‖
        rw [norm_mul]
      _ = ∫ x : ℝ, ‖c x‖ * ‖f x‖ ∂μ := by
        rw [intervalIntegral.integral_of_le (by norm_num)]
  have hbound := hnorm.trans hholder'
  have hsq :
      ‖∫ x : ℝ in -1..1, c x * f x‖ ^ 2 ≤
        (∫ x : ℝ, ‖c x‖ ^ 2 ∂μ) *
          (∫ x : ℝ, ‖f x‖ ^ 2 ∂μ) := by
    calc
      ‖∫ x : ℝ in -1..1, c x * f x‖ ^ 2 ≤
          (Real.sqrt (∫ x : ℝ, ‖c x‖ ^ 2 ∂μ) *
            Real.sqrt (∫ x : ℝ, ‖f x‖ ^ 2 ∂μ)) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hbound
      _ = (∫ x : ℝ, ‖c x‖ ^ 2 ∂μ) *
          (∫ x : ℝ, ‖f x‖ ^ 2 ∂μ) := by
        rw [mul_pow, Real.sq_sqrt hA0, Real.sq_sqrt hB0]
  have hweight :
      (∫ x : ℝ, ‖c x‖ ^ 2 ∂μ) = (Real.sinh a + a) / a := by
    change (∫ x : ℝ in I, ‖c x‖ ^ 2) = _
    rw [show (∫ x : ℝ in I, ‖c x‖ ^ 2) =
        ∫ x : ℝ in -1..1, Real.cosh (a * x / 2) ^ 2 by
      rw [intervalIntegral.integral_of_le (by norm_num)]
      apply setIntegral_congr_fun measurableSet_Ioc
      intro x _
      dsimp only [c]
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]]
    exact integral_cosh_scaled_sq ha.ne'
  have henergy :
      (∫ x : ℝ, ‖f x‖ ^ 2 ∂μ) =
        ∫ x : ℝ in -1..1, ‖f x‖ ^ 2 := by
    change (∫ x : ℝ in I, ‖f x‖ ^ 2) = _
    rw [intervalIntegral.integral_of_le (by norm_num)]
  rw [Complex.normSq_eq_norm_sq]
  dsimp only [c] at hsq ⊢
  rw [hweight, henergy] at hsq
  exact hsq

private theorem exp_yoshidaEndpointA_eq_sqrt_two :
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

/-- Exact coefficient of the single positive growing even rank. -/
theorem evenGrowingRank_energyCoefficient :
    yoshidaEndpointA * Real.exp yoshidaEndpointA *
        ((Real.sinh yoshidaEndpointA + yoshidaEndpointA) /
          yoshidaEndpointA) =
      (1 / 2 : ℝ) + Real.log 2 / Real.sqrt 2 := by
  have hsqrtPos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrtSq : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hsinh := two_mul_sinh_yoshidaEndpointA_sub_eq
  rw [exp_yoshidaEndpointA_eq_sqrt_two]
  unfold yoshidaEndpointA at hsinh
  field_simp [hsqrtPos.ne'] at hsinh
  have hsinhScaled :
      2 * Real.sqrt 2 * Real.sinh (Real.log 2 / 2) = 1 := by
    nlinarith
  have hfour :
      4 * Real.sinh (Real.log 2 / 2) = Real.sqrt 2 := by
    calc
      4 * Real.sinh (Real.log 2 / 2) =
          (Real.sqrt 2) ^ 2 *
            (2 * Real.sinh (Real.log 2 / 2)) := by rw [hsqrtSq]; ring
      _ = Real.sqrt 2 *
          (2 * Real.sqrt 2 * Real.sinh (Real.log 2 / 2)) := by ring
      _ = Real.sqrt 2 := by rw [hsinhScaled]; ring
  unfold yoshidaEndpointA
  field_simp [hsqrtPos.ne']
  rw [hsqrtSq]
  nlinarith [hfour]

/-- The dyadic prime weight is strictly below one half. -/
theorem factorTwoDyadicWeight_lt_half :
    Real.log 2 / Real.sqrt 2 < (1 / 2 : ℝ) := by
  have hsqrtPos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrtSq : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hsqrtLower : (7 / 5 : ℝ) < Real.sqrt 2 := by
    nlinarith [Real.sqrt_nonneg 2]
  have hlogUpper : Real.log 2 < (7 / 10 : ℝ) :=
    Real.log_two_lt_d9.trans (by norm_num)
  rw [div_lt_iff₀ hsqrtPos]
  nlinarith

/-- The positive decaying-rank loss in the even archimedean block. -/
def factorTwoEvenDecayingRankTail (w : ℝ → ℝ) : ℝ :=
  yoshidaEndpointA * ∑' m : ℕ,
    Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
      centeredCoshMoment w
        (yoshidaEndpointA * oddRate (m + 1)) ^ 2

private theorem specialized_phaseCorrelation_eq_centered
    (w : ℝ → ℝ) (t : ℝ) :
    factorTwoCenteredPhaseCorrelation w 0 1 0 t =
      centeredEndpointCorrelation w t := by
  simp [factorTwoCenteredPhaseCorrelation, centeredEndpointCorrelation]

private theorem specialized_reflectedDesingularized_eq_regular
    (w : ℝ → ℝ) {t : ℝ} (ht2 : t < 2) :
    factorTwoCenteredReflectedDesingularizedPhaseKernel w 0 1 0 t =
      yoshidaEndpointA * factorTwoCenteredReflectedRegularKernel t *
        centeredEndpointCorrelation w t := by
  have h := endpoint_mul_reflectedPhaseBranch_eq_regular_sub_half_pole
    w 0 1 0 ht2
  unfold factorTwoCenteredReflectedDesingularizedPhaseKernel
  rw [← show factorTwoLogLength - yoshidaEndpointA * t =
      yoshidaEndpointA * (2 - t) by
    rw [factorTwoLogLength_eq_two_mul_yoshidaEndpointA]
    ring]
  rw [h]
  simp only [neg_zero, specialized_phaseCorrelation_eq_centered]
  have hden : 2 - t ≠ 0 := by linarith
  field_simp [hden]
  ring

/-- On an even profile the nonnegative correlation mean absorbs the lower
regular scalar.  Only the exact scalar width acts on the absolute
autocorrelation, whose positive-lag mass is at most one energy. -/
theorem neg_scalarWidth_energy_le_even_regularBlock
    (w : ℝ → ℝ) (hw : Continuous w) (heven : Function.Even w) :
    -((11 / 8 : ℝ) - (11 / 4 : ℝ) * yoshidaEndpointA) *
        (∫ x : ℝ in -1..1, w x ^ 2) ≤
      yoshidaEndpointA *
          (∫ t : ℝ in 0..2,
            factorTwoCenteredForwardPhaseKernel w 0 1 0 t) +
        (∫ t : ℝ in 0..2,
          factorTwoCenteredReflectedDesingularizedPhaseKernel
            w 0 1 0 t) := by
  let E : ℝ := ∫ x : ℝ in -1..1, w x ^ 2
  let C : ℝ → ℝ := centeredEndpointCorrelation w
  let L : ℝ := (11 / 4 : ℝ) * yoshidaEndpointA
  let U : ℝ := (11 / 8 : ℝ)
  let d : ℝ := U - L
  let g : ℝ → ℝ := fun t ↦
    yoshidaEndpointA *
        factorTwoCenteredForwardPhaseKernel w 0 1 0 t +
      factorTwoCenteredReflectedDesingularizedPhaseKernel w 0 1 0 t -
      L * C t
  have hE : 0 ≤ E := by
    dsimp only [E]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun x _ ↦ sq_nonneg (w x))
  have hforward :=
    intervalIntegrable_factorTwoCenteredForwardPhaseKernel
      w 0 hw continuous_zero 1 0
  have hreflected :=
    intervalIntegrable_factorTwoCenteredReflectedDesingularizedPhaseKernel
      w 0 hw continuous_zero 1 0
  have hCcont : Continuous C := by
    dsimp only [C]
    exact continuous_centeredEndpointCorrelation_of_continuous w hw
  have hCint : IntervalIntegrable C volume 0 2 :=
    hCcont.intervalIntegrable 0 2
  have hg : IntervalIntegrable g volume 0 2 := by
    dsimp only [g]
    exact ((hforward.const_mul yoshidaEndpointA).add hreflected).sub
      (hCint.const_mul L)
  have hmeanIdentity :=
    two_mul_integral_cosh_mul_centeredCorrelation_of_even w hw heven 0
  have hmean : 0 ≤ ∫ t : ℝ in 0..2, C t := by
    have hsquare :
        2 * (∫ t : ℝ in 0..2, C t) = centeredCoshMoment w 0 ^ 2 := by
      simpa [C, centeredCoshMoment] using hmeanIdentity
    nlinarith [sq_nonneg (centeredCoshMoment w 0)]
  have hL0 : 0 ≤ L := by
    dsimp only [L]
    exact mul_nonneg (by norm_num) yoshidaEndpointA_pos.le
  have hd0 : 0 ≤ d := by
    have hlogUpper : Real.log 2 < (7 / 10 : ℝ) :=
      Real.log_two_lt_d9.trans (by norm_num)
    dsimp only [L, U, d]
    unfold yoshidaEndpointA
    nlinarith
  have hpoint : ∀ t ∈ Set.Ioo (0 : ℝ) 2,
      |g t| ≤ d * |C t| := by
    intro t ht
    have hb := factorTwo_regular_phase_scalar_bounds ht.1.le ht.2.le
    let F : ℝ := factorTwoAdjacentSmoothKernel
      (yoshidaEndpointA * (2 + t))
    let R : ℝ := factorTwoCenteredReflectedRegularKernel t
    dsimp only at hb
    change (1 : ℝ) ≤ F ∧ F ≤ 2 ∧
      (7 / 4 : ℝ) ≤ R ∧ R ≤ (61 / 32 : ℝ) ∧
      yoshidaEndpointA * (F + R) ≤ (11 / 8 : ℝ) ∧
      yoshidaEndpointA * |F - R| ≤ (203 / 640 : ℝ) at hb
    have hHlower : L ≤ yoshidaEndpointA * (F + R) := by
      rcases hb with ⟨hF, _hF', hR, _⟩
      dsimp only [L]
      have hA := yoshidaEndpointA_pos.le
      nlinarith
    have hHupper : yoshidaEndpointA * (F + R) ≤ U :=
      hb.2.2.2.2.1
    have hdev :
        |yoshidaEndpointA * (F + R) - L| ≤ d := by
      rw [abs_le]
      dsimp only [d]
      constructor <;> nlinarith
    have href := specialized_reflectedDesingularized_eq_regular
      w ht.2
    dsimp only [g, C]
    rw [href]
    unfold factorTwoCenteredForwardPhaseKernel
    rw [specialized_phaseCorrelation_eq_centered]
    change |yoshidaEndpointA *
          (F * centeredEndpointCorrelation w t) +
        yoshidaEndpointA * R * centeredEndpointCorrelation w t -
          L * centeredEndpointCorrelation w t| ≤
      d * |centeredEndpointCorrelation w t|
    rw [show yoshidaEndpointA *
          (F * centeredEndpointCorrelation w t) +
        yoshidaEndpointA * R * centeredEndpointCorrelation w t -
          L * centeredEndpointCorrelation w t =
        (yoshidaEndpointA * (F + R) - L) *
          centeredEndpointCorrelation w t by ring,
      abs_mul]
    exact mul_le_mul_of_nonneg_right hdev (abs_nonneg _)
  have hmajorInt : IntervalIntegrable (fun t : ℝ ↦ d * |C t|)
      volume 0 2 := hCint.abs.const_mul d
  have habsIntegral :
      |(∫ t : ℝ in 0..2, g t)| ≤
        ∫ t : ℝ in 0..2, d * |C t| := by
    calc
      |(∫ t : ℝ in 0..2, g t)| ≤
          ∫ t : ℝ in 0..2, |g t| :=
        intervalIntegral.abs_integral_le_integral_abs (by norm_num)
      _ ≤ ∫ t : ℝ in 0..2, d * |C t| := by
        apply intervalIntegral.integral_mono_on_of_le_Ioo
          (by norm_num) hg.abs hmajorInt
        exact hpoint
  have habsC := integral_abs_centeredEndpointCorrelation_le_energy w hw
  have hscaled := mul_le_mul_of_nonneg_left habsC hd0
  have hcenter :
      yoshidaEndpointA *
            (∫ t : ℝ in 0..2,
              factorTwoCenteredForwardPhaseKernel w 0 1 0 t) +
          (∫ t : ℝ in 0..2,
            factorTwoCenteredReflectedDesingularizedPhaseKernel
              w 0 1 0 t) =
        L * (∫ t : ℝ in 0..2, C t) +
          ∫ t : ℝ in 0..2, g t := by
    dsimp only [g]
    rw [intervalIntegral.integral_sub
          ((hforward.const_mul yoshidaEndpointA).add hreflected)
          (hCint.const_mul L),
      intervalIntegral.integral_add (hforward.const_mul yoshidaEndpointA)
        hreflected,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    ring
  have hgLower : -d * E ≤ ∫ t : ℝ in 0..2, g t := by
    have hcalc :
        (∫ t : ℝ in 0..2, d * |C t|) ≤ d * E := by
      rw [intervalIntegral.integral_const_mul]
      exact hscaled
    nlinarith [neg_abs_le (∫ t : ℝ in 0..2, g t)]
  rw [hcenter]
  change -d * E ≤
    L * (∫ t : ℝ in 0..2, C t) + ∫ t : ℝ in 0..2, g t
  nlinarith [mul_nonneg hL0 hmean]

/-- The regular width, dyadic atom, translated prime, and a `pi / 2`
half-pole budget fit strictly inside three endpoint energies. -/
theorem evenCrudeLossCoefficient_lt_three :
    ((11 / 8 : ℝ) - (11 / 4 : ℝ) * yoshidaEndpointA) +
        Real.pi / 2 + Real.log 2 / Real.sqrt 2 + 1 / 2 < 3 := by
  have hlogLower : (0.6931471803 : ℝ) < Real.log 2 :=
    Real.log_two_gt_d9
  have hpiUpper : Real.pi < (3.1416 : ℝ) := Real.pi_lt_d4
  have halpha : Real.log 2 / Real.sqrt 2 < (1 / 2 : ℝ) :=
    factorTwoDyadicWeight_lt_half
  unfold yoshidaEndpointA
  nlinarith

/-- Once the even endpoint half-pole has its coarse `pi / 2` mass bound, the
directional lower estimate `-3E` follows.  This is exactly the weaker bound
needed by the coupled directional phase budget. -/
theorem neg_three_energy_le_even_symmetricPerturbation_of_halfPole_le
    (w : ℝ → ℝ) (hw : Continuous w) (heven : Function.Even w)
    (hpole :
      (1 / 2 : ℝ) *
          (∫ t : ℝ in 0..2,
            centeredEndpointCorrelation w t / (2 - t)) ≤
        (Real.pi / 2) * (∫ x : ℝ in -1..1, w x ^ 2)) :
    -(3 : ℝ) * (∫ x : ℝ in -1..1, w x ^ 2) ≤
      factorTwoCenteredSymmetricPerturbation w := by
  let E : ℝ := ∫ x : ℝ in -1..1, w x ^ 2
  let regular : ℝ :=
    yoshidaEndpointA *
        (∫ t : ℝ in 0..2,
          factorTwoCenteredForwardPhaseKernel w 0 1 0 t) +
      (∫ t : ℝ in 0..2,
        factorTwoCenteredReflectedDesingularizedPhaseKernel w 0 1 0 t)
  let pole : ℝ := (1 / 2 : ℝ) *
    (∫ t : ℝ in 0..2,
      centeredEndpointCorrelation w t / (2 - t))
  let alpha : ℝ := Real.log 2 / Real.sqrt 2
  let prime : ℝ := (Real.log 3 / Real.sqrt 3) *
    centeredEndpointCorrelation w
      (factorTwoPrimeShift / yoshidaEndpointA)
  have hE : 0 ≤ E := by
    dsimp only [E]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun x _ ↦ sq_nonneg (w x))
  have hregular := neg_scalarWidth_energy_le_even_regularBlock w hw heven
  change -((11 / 8 : ℝ) - (11 / 4 : ℝ) * yoshidaEndpointA) * E ≤
    regular at hregular
  change pole ≤ (Real.pi / 2) * E at hpole
  have hprimeAbs := abs_weighted_primeCorrelation_le_half_energy w hw
  change |prime| ≤ (1 / 2 : ℝ) * E at hprimeAbs
  have hprime : prime ≤ (1 / 2 : ℝ) * E :=
    (le_abs_self prime).trans hprimeAbs
  have hcoeff := evenCrudeLossCoefficient_lt_three
  have hexact := symmetricPerturbation_eq_regular_sub_pole_sub_primes w hw
  simp only [specialized_phaseCorrelation_eq_centered] at hexact
  change factorTwoCenteredSymmetricPerturbation w =
    regular - pole - alpha * E - prime at hexact
  rw [hexact]
  nlinarith

/-- The hard even lower bound reduces exactly to a joint estimate for the
decaying archimedean rank tail and the translated `p = 3` correlation. -/
theorem neg_three_halves_energy_le_even_symmetricPerturbation_of_tail_prime_le
    (w : ℝ → ℝ) (hw : Continuous w) (heven : Function.Even w)
    (hjoint :
      factorTwoEvenDecayingRankTail w +
          (Real.log 3 / Real.sqrt 3) *
            centeredEndpointCorrelation w
              (factorTwoPrimeShift / yoshidaEndpointA) ≤
        ∫ x : ℝ in -1..1, w x ^ 2) :
    -(3 / 2 : ℝ) * (∫ x : ℝ in -1..1, w x ^ 2) ≤
      factorTwoCenteredSymmetricPerturbation w := by
  let E : ℝ := ∫ x : ℝ in -1..1, w x ^ 2
  let alpha : ℝ := Real.log 2 / Real.sqrt 2
  let beta : ℝ := Real.log 3 / Real.sqrt 3
  let C : ℝ := centeredEndpointCorrelation w
    (factorTwoPrimeShift / yoshidaEndpointA)
  let H : ℝ := centeredCoshMoment w (yoshidaEndpointA / 2) ^ 2
  let T : ℝ := ∑' m : ℕ,
    Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
      centeredCoshMoment w
        (yoshidaEndpointA * oddRate (m + 1)) ^ 2
  have hE : 0 ≤ E := by
    dsimp only [E]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun x _ ↦ sq_nonneg (w x))
  have halpha : alpha < (1 / 2 : ℝ) := by
    dsimp only [alpha]
    exact factorTwoDyadicWeight_lt_half
  have harchEq := factorTwoCenteredArchBlock_eq_evenRankSquares
    w hw heven
  change factorTwoCenteredArchBlock w =
    yoshidaEndpointA * (Real.exp yoshidaEndpointA * H - T) at harchEq
  have hhead : 0 ≤
      yoshidaEndpointA * Real.exp yoshidaEndpointA * H := by
    exact mul_nonneg
      (mul_nonneg yoshidaEndpointA_pos.le
        (Real.exp_pos yoshidaEndpointA).le) (sq_nonneg _)
  have harch : -yoshidaEndpointA * T ≤
      factorTwoCenteredArchBlock w := by
    rw [harchEq]
    nlinarith
  change yoshidaEndpointA * T + beta * C ≤ E at hjoint
  rw [symmetricPerturbation_eq_arch_sub_primeBlock]
  unfold factorTwoCenteredPrimeBlock
  change -(3 / 2 : ℝ) * E ≤
    factorTwoCenteredArchBlock w - (alpha * E + beta * C)
  nlinarith

private theorem centeredCoshMoment_half_sq_le_energy
    (w : ℝ → ℝ) (hw : Continuous w) :
    centeredCoshMoment w (yoshidaEndpointA / 2) ^ 2 ≤
      ((Real.sinh yoshidaEndpointA + yoshidaEndpointA) /
        yoshidaEndpointA) *
        (∫ x : ℝ in -1..1, w x ^ 2) := by
  have h := normSq_integral_cosh_scaled_le yoshidaEndpointA_pos
    (fun x : ℝ ↦ (w x : ℂ)) (by fun_prop)
  have hint :
      (∫ x : ℝ in -1..1,
        (Real.cosh (yoshidaEndpointA * x / 2) : ℂ) * (w x : ℂ)) =
        (centeredCoshMoment w (yoshidaEndpointA / 2) : ℂ) := by
    unfold centeredCoshMoment
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro x _
    change (Real.cosh (yoshidaEndpointA * x / 2) : ℂ) * (w x : ℂ) =
      ((Real.cosh ((yoshidaEndpointA / 2) * x) * w x : ℝ) : ℂ)
    rw [show yoshidaEndpointA * x / 2 =
      (yoshidaEndpointA / 2) * x by ring]
    push_cast
    rfl
  rw [hint] at h
  simpa only [Complex.normSq_apply, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, add_zero, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    pow_two, abs_mul_abs_self] using h

/-- Exact generic upper coefficient for the even symmetric perturbation. -/
theorem even_symmetricPerturbation_upper_exact
    (w : ℝ → ℝ) (hw : Continuous w) (heven : Function.Even w) :
    factorTwoCenteredSymmetricPerturbation w ≤
      ((1 / 2 : ℝ) + (Real.log 3 / Real.sqrt 3) / 2) *
        (∫ x : ℝ in -1..1, w x ^ 2) := by
  let E : ℝ := ∫ x : ℝ in -1..1, w x ^ 2
  let C : ℝ := centeredCoshMoment w (yoshidaEndpointA / 2) ^ 2
  let alpha : ℝ := Real.log 2 / Real.sqrt 2
  let beta : ℝ := Real.log 3 / Real.sqrt 3
  let tail : ℝ := ∑' m : ℕ,
    Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
      centeredCoshMoment w
        (yoshidaEndpointA * oddRate (m + 1)) ^ 2
  have hE : 0 ≤ E := by
    dsimp only [E]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun x _ ↦ sq_nonneg (w x))
  have htail : 0 ≤ tail := by
    dsimp only [tail]
    exact tsum_nonneg fun m ↦ mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  have hmoment := centeredCoshMoment_half_sq_le_energy w hw
  change C ≤
    ((Real.sinh yoshidaEndpointA + yoshidaEndpointA) /
      yoshidaEndpointA) * E at hmoment
  have hscaled := mul_le_mul_of_nonneg_left hmoment
    (mul_nonneg yoshidaEndpointA_pos.le
      (Real.exp_pos yoshidaEndpointA).le)
  have hcoeff := evenGrowingRank_energyCoefficient
  change yoshidaEndpointA * Real.exp yoshidaEndpointA *
      ((Real.sinh yoshidaEndpointA + yoshidaEndpointA) /
        yoshidaEndpointA) = (1 / 2 : ℝ) + alpha at hcoeff
  have hhead : yoshidaEndpointA * Real.exp yoshidaEndpointA * C ≤
      ((1 / 2 : ℝ) + alpha) * E := by
    calc
      yoshidaEndpointA * Real.exp yoshidaEndpointA * C =
          (yoshidaEndpointA * Real.exp yoshidaEndpointA) * C := by ring
      _ ≤ (yoshidaEndpointA * Real.exp yoshidaEndpointA) *
          (((Real.sinh yoshidaEndpointA + yoshidaEndpointA) /
            yoshidaEndpointA) * E) := hscaled
      _ = ((1 / 2 : ℝ) + alpha) * E := by
        rw [← mul_assoc, hcoeff]
  have harchEq := factorTwoCenteredArchBlock_eq_evenRankSquares
    w hw heven
  change factorTwoCenteredArchBlock w =
    yoshidaEndpointA * (Real.exp yoshidaEndpointA * C - tail) at harchEq
  have harch : factorTwoCenteredArchBlock w ≤
      ((1 / 2 : ℝ) + alpha) * E := by
    rw [harchEq]
    nlinarith [yoshidaEndpointA_pos]
  have hprime := (primeBlock_mass_bounds w hw).1
  change (alpha - beta / 2) * E ≤
    factorTwoCenteredPrimeBlock w at hprime
  rw [symmetricPerturbation_eq_arch_sub_primeBlock]
  dsimp only [E, C, alpha, beta, tail] at *
  nlinarith

/-- The generic even perturbation has the sharper upper bound `E`. -/
theorem even_symmetricPerturbation_le_energy
    (w : ℝ → ℝ) (hw : Continuous w) (heven : Function.Even w) :
    factorTwoCenteredSymmetricPerturbation w ≤
      ∫ x : ℝ in -1..1, w x ^ 2 := by
  let E : ℝ := ∫ x : ℝ in -1..1, w x ^ 2
  let beta : ℝ := Real.log 3 / Real.sqrt 3
  have hE : 0 ≤ E := by
    dsimp only [E]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun x _ ↦ sq_nonneg (w x))
  have hupper := even_symmetricPerturbation_upper_exact w hw heven
  have hbeta : beta < 1 := by
    dsimp only [beta]
    exact factorTwoPrimeThreeWeight_lt_one
  change factorTwoCenteredSymmetricPerturbation w ≤
    ((1 / 2 : ℝ) + beta / 2) * E at hupper
  change factorTwoCenteredSymmetricPerturbation w ≤ E
  nlinarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseEvenSymmetricBound

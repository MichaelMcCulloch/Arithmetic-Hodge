import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseRankLimit
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseSymmetricCarleman

set_option autoImplicit false

open Complex MeasureTheory Real Set
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseOddSymmetricBound

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
# The easy side of the odd symmetric factor-two bound

The infinite odd rank expansion separates the only negative archimedean
rank from a nonnegative decaying-rank series.  Its loss cancels the dyadic
part of the prime block exactly, leaving the coefficient
`1/2 + (log 3 / sqrt 3)/2`.  Thus the lower half of the desired odd
`3/2` interval actually holds with the sharper constant `1` and requires no
Fourier-tail hypothesis.  The opposite, upper half remains the substantive
tail estimate.
-/

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

/-- Exact coefficient of the single negative growing odd rank. -/
theorem oddGrowingRank_energyCoefficient :
    yoshidaEndpointA * Real.exp yoshidaEndpointA *
        ((Real.sinh yoshidaEndpointA - yoshidaEndpointA) /
          yoshidaEndpointA) =
      (1 / 2 : ℝ) - Real.log 2 / Real.sqrt 2 := by
  have hsqrtPos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrtSq : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hbase := two_mul_sinh_yoshidaEndpointA_sub_eq
  rw [exp_yoshidaEndpointA_eq_sqrt_two]
  field_simp [yoshidaEndpointA_pos.ne', hsqrtPos.ne'] at hbase ⊢
  have hscaled := congrArg (fun z : ℝ ↦ Real.sqrt 2 * z) hbase
  dsimp only at hscaled
  have hsql := congrArg (fun z : ℝ ↦ z * Real.log 2) hsqrtSq
  dsimp only at hsql
  nlinarith

private theorem centeredSinhMoment_half_sq_le_energy
    (w : ℝ → ℝ) (hw : Continuous w) :
    centeredSinhMoment w (yoshidaEndpointA / 2) ^ 2 ≤
      ((Real.sinh yoshidaEndpointA - yoshidaEndpointA) /
        yoshidaEndpointA) *
        (∫ x : ℝ in -1..1, w x ^ 2) := by
  have h := normSq_integral_sinh_scaled_le yoshidaEndpointA_pos
    (fun x : ℝ ↦ (w x : ℂ)) (by fun_prop)
  have hint :
      (∫ x : ℝ in -1..1,
        (Real.sinh (yoshidaEndpointA * x / 2) : ℂ) * (w x : ℂ)) =
        (centeredSinhMoment w (yoshidaEndpointA / 2) : ℂ) := by
    unfold centeredSinhMoment
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro x _hx
    change (Real.sinh (yoshidaEndpointA * x / 2) : ℂ) * (w x : ℂ) =
      ((Real.sinh ((yoshidaEndpointA / 2) * x) * w x : ℝ) : ℂ)
    rw [show yoshidaEndpointA * x / 2 =
      (yoshidaEndpointA / 2) * x by ring]
    push_cast
    rfl
  rw [hint] at h
  simpa only [Complex.normSq_apply, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, add_zero, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    pow_two, abs_mul_abs_self] using h

/-- Exact generic lower coefficient for the odd symmetric perturbation.
The positive infinite rank series is retained, not bounded termwise. -/
theorem odd_symmetricPerturbation_lower_exact
    (w : ℝ → ℝ) (hw : Continuous w) (hodd : Function.Odd w) :
    -((1 / 2 : ℝ) + (Real.log 3 / Real.sqrt 3) / 2) *
        (∫ x : ℝ in -1..1, w x ^ 2) ≤
      factorTwoCenteredSymmetricPerturbation w := by
  let E : ℝ := ∫ x : ℝ in -1..1, w x ^ 2
  let S : ℝ := centeredSinhMoment w (yoshidaEndpointA / 2) ^ 2
  let alpha : ℝ := Real.log 2 / Real.sqrt 2
  let beta : ℝ := Real.log 3 / Real.sqrt 3
  let tail : ℝ := ∑' m : ℕ,
    Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
      centeredSinhMoment w
        (yoshidaEndpointA * oddRate (m + 1)) ^ 2
  have hE : 0 ≤ E := by
    dsimp only [E]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun x _hx ↦ sq_nonneg (w x))
  have htail : 0 ≤ tail := by
    dsimp only [tail]
    exact tsum_nonneg fun m ↦ mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  have hmoment := centeredSinhMoment_half_sq_le_energy w hw
  change S ≤
    ((Real.sinh yoshidaEndpointA - yoshidaEndpointA) /
      yoshidaEndpointA) * E at hmoment
  have hscaled := mul_le_mul_of_nonneg_left hmoment
    (mul_nonneg yoshidaEndpointA_pos.le
      (Real.exp_pos yoshidaEndpointA).le)
  have hcoeff := oddGrowingRank_energyCoefficient
  change yoshidaEndpointA * Real.exp yoshidaEndpointA *
      ((Real.sinh yoshidaEndpointA - yoshidaEndpointA) /
        yoshidaEndpointA) = (1 / 2 : ℝ) - alpha at hcoeff
  have hhead : yoshidaEndpointA * Real.exp yoshidaEndpointA * S ≤
      ((1 / 2 : ℝ) - alpha) * E := by
    calc
      yoshidaEndpointA * Real.exp yoshidaEndpointA * S =
          (yoshidaEndpointA * Real.exp yoshidaEndpointA) * S := by ring
      _ ≤ (yoshidaEndpointA * Real.exp yoshidaEndpointA) *
          (((Real.sinh yoshidaEndpointA - yoshidaEndpointA) /
            yoshidaEndpointA) * E) := hscaled
      _ = ((1 / 2 : ℝ) - alpha) * E := by
        rw [← mul_assoc, hcoeff]
  have harchEq := factorTwoCenteredArchBlock_eq_oddRankSquares
    w hw hodd
  change factorTwoCenteredArchBlock w =
    yoshidaEndpointA *
      (-Real.exp yoshidaEndpointA * S + tail) at harchEq
  have harch : -((1 / 2 : ℝ) - alpha) * E ≤
      factorTwoCenteredArchBlock w := by
    rw [harchEq]
    have hA : 0 ≤ yoshidaEndpointA := yoshidaEndpointA_pos.le
    nlinarith
  have hprime := (primeBlock_mass_bounds w hw).2
  change factorTwoCenteredPrimeBlock w ≤ (alpha + beta / 2) * E at hprime
  rw [symmetricPerturbation_eq_arch_sub_primeBlock]
  dsimp only [E, S, alpha, beta, tail] at *
  nlinarith

/-- The generic odd perturbation has the sharper lower bound `-E`.  This is
the lower half of the requested `|P| ≤ 3E/2` interval, without any tail
assumption. -/
theorem neg_energy_le_odd_symmetricPerturbation
    (w : ℝ → ℝ) (hw : Continuous w) (hodd : Function.Odd w) :
    -(∫ x : ℝ in -1..1, w x ^ 2) ≤
      factorTwoCenteredSymmetricPerturbation w := by
  let E : ℝ := ∫ x : ℝ in -1..1, w x ^ 2
  let beta : ℝ := Real.log 3 / Real.sqrt 3
  have hE : 0 ≤ E := by
    dsimp only [E]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun x _hx ↦ sq_nonneg (w x))
  have hlower := odd_symmetricPerturbation_lower_exact w hw hodd
  have hbeta : beta < 1 := by
    dsimp only [beta]
    exact factorTwoPrimeThreeWeight_lt_one
  change -((1 / 2 : ℝ) + beta / 2) * E ≤
    factorTwoCenteredSymmetricPerturbation w at hlower
  change -E ≤ factorTwoCenteredSymmetricPerturbation w
  nlinarith

/-! ## The generic odd upper bound -/

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

/-- Centering the two nonsingular scalar branches by the zero mean of an odd
autocorrelation costs only their exact scalar width. -/
theorem abs_odd_regularBlock_le_scalarWidth_energy
    (w : ℝ → ℝ) (hw : Continuous w) (hodd : Function.Odd w) :
    |yoshidaEndpointA *
          (∫ t : ℝ in 0..2,
            factorTwoCenteredForwardPhaseKernel w 0 1 0 t) +
        (∫ t : ℝ in 0..2,
          factorTwoCenteredReflectedDesingularizedPhaseKernel
            w 0 1 0 t)| ≤
      ((11 / 8 : ℝ) - (11 / 4 : ℝ) * yoshidaEndpointA) *
        (∫ x : ℝ in -1..1, w x ^ 2) := by
  let C : ℝ → ℝ := centeredEndpointCorrelation w
  let L : ℝ := (11 / 4 : ℝ) * yoshidaEndpointA
  let U : ℝ := (11 / 8 : ℝ)
  let k : ℝ := (L + U) / 2
  let d : ℝ := (U - L) / 2
  let g : ℝ → ℝ := fun t ↦
    yoshidaEndpointA *
        factorTwoCenteredForwardPhaseKernel w 0 1 0 t +
      factorTwoCenteredReflectedDesingularizedPhaseKernel w 0 1 0 t -
      k * C t
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
      (hCint.const_mul k)
  have hzero : (∫ t : ℝ in 0..2, C t) = 0 := by
    dsimp only [C]
    exact integral_centeredEndpointCorrelation_eq_zero_of_odd w hw hodd
  have hcenter :
      yoshidaEndpointA *
            (∫ t : ℝ in 0..2,
              factorTwoCenteredForwardPhaseKernel w 0 1 0 t) +
          (∫ t : ℝ in 0..2,
            factorTwoCenteredReflectedDesingularizedPhaseKernel
              w 0 1 0 t) =
        ∫ t : ℝ in 0..2, g t := by
    dsimp only [g]
    rw [intervalIntegral.integral_sub
          ((hforward.const_mul yoshidaEndpointA).add hreflected)
          (hCint.const_mul k),
      intervalIntegral.integral_add (hforward.const_mul yoshidaEndpointA)
        hreflected,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, hzero]
    ring
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
    have hHupper : yoshidaEndpointA * (F + R) ≤ U := by
      exact hb.2.2.2.2.1
    have hdev :
        |yoshidaEndpointA * (F + R) - k| ≤ d := by
      rw [abs_le]
      dsimp only [k, d]
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
          k * centeredEndpointCorrelation w t| ≤
      d * |centeredEndpointCorrelation w t|
    rw [show yoshidaEndpointA *
          (F * centeredEndpointCorrelation w t) +
        yoshidaEndpointA * R * centeredEndpointCorrelation w t -
          k * centeredEndpointCorrelation w t =
        (yoshidaEndpointA * (F + R) - k) *
          centeredEndpointCorrelation w t by ring]
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hdev (abs_nonneg _)
  have hmajorInt : IntervalIntegrable (fun t : ℝ ↦ d * |C t|)
      volume 0 2 := (hCint.abs.const_mul d)
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
  have habsC :=
    integral_abs_centeredEndpointCorrelation_le_two_mul_energy w hw
  have hscaled := mul_le_mul_of_nonneg_left habsC hd0
  rw [hcenter]
  calc
    |(∫ t : ℝ in 0..2, g t)| ≤
        ∫ t : ℝ in 0..2, d * |C t| := habsIntegral
    _ = d * (∫ t : ℝ in 0..2, |C t|) := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ d * (2 * (∫ x : ℝ in -1..1, w x ^ 2)) := hscaled
    _ = ((11 / 8 : ℝ) - (11 / 4 : ℝ) * yoshidaEndpointA) *
        (∫ x : ℝ in -1..1, w x ^ 2) := by
      dsimp only [d, U, L]
      ring

/-- Every continuous odd profile satisfies the missing upper half of the
factor-two symmetric `3/2` estimate. -/
theorem odd_symmetricPerturbation_le_three_halves_energy
    (w : ℝ → ℝ) (hw : Continuous w) (hodd : Function.Odd w) :
    factorTwoCenteredSymmetricPerturbation w ≤
      (3 / 2 : ℝ) * (∫ x : ℝ in -1..1, w x ^ 2) := by
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
  let beta : ℝ := Real.log 3 / Real.sqrt 3
  have hE : 0 ≤ E := by
    dsimp only [E]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun x _hx ↦ sq_nonneg (w x))
  have hregular := abs_odd_regularBlock_le_scalarWidth_energy w hw hodd
  change |regular| ≤
    ((11 / 8 : ℝ) - (11 / 4 : ℝ) * yoshidaEndpointA) * E at hregular
  have hregularUpper := le_trans (le_abs_self regular) hregular
  have hpole :=
    abs_half_centeredCorrelation_pole_le_pi_quarter_energy_of_odd w hw hodd
  change |pole| ≤ (Real.pi / 4) * E at hpole
  have hnegPole : -pole ≤ (Real.pi / 4) * E :=
    le_trans (neg_le_abs pole) hpole
  have hprime := (primeBlock_mass_bounds w hw).1
  change (alpha - beta / 2) * E ≤ factorTwoCenteredPrimeBlock w at hprime
  have hcoeff :
      ((11 / 8 : ℝ) - (11 / 4 : ℝ) * yoshidaEndpointA) +
          Real.pi / 4 - alpha + beta / 2 < (3 / 2 : ℝ) := by
    have hlogLower : (2 / 3 : ℝ) < Real.log 2 := by
      exact (by norm_num : (2 / 3 : ℝ) < 0.6931471803).trans
        Real.log_two_gt_d9
    have hsqrt2Pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    have hsqrt2Sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hsqrt2Upper : Real.sqrt 2 < (3 / 2 : ℝ) := by nlinarith
    have halphaLower : (4 / 9 : ℝ) < alpha := by
      dsimp only [alpha]
      rw [lt_div_iff₀ hsqrt2Pos]
      nlinarith
    have hbetaUpper : beta < 1 := by
      dsimp only [beta]
      exact factorTwoPrimeThreeWeight_lt_one
    have hpiUpper : Real.pi < (3.1416 : ℝ) := Real.pi_lt_d4
    dsimp only [yoshidaEndpointA]
    nlinarith
  have hexact := symmetricPerturbation_eq_regular_sub_pole_sub_primes w hw
  simp only [specialized_phaseCorrelation_eq_centered] at hexact
  change factorTwoCenteredSymmetricPerturbation w =
    regular - pole - alpha * E - beta *
      centeredEndpointCorrelation w
        (factorTwoPrimeShift / yoshidaEndpointA) at hexact
  have hprimeDef : factorTwoCenteredPrimeBlock w =
      alpha * E + beta * centeredEndpointCorrelation w
        (factorTwoPrimeShift / yoshidaEndpointA) := by
    rfl
  rw [hprimeDef] at hprime
  rw [hexact]
  change regular - pole - alpha * E - beta *
      centeredEndpointCorrelation w
        (factorTwoPrimeShift / yoshidaEndpointA) ≤ (3 / 2 : ℝ) * E
  nlinarith

/-- Unconditional odd symmetric radius bound in the exact form consumed by
the factor-two phase closure. -/
theorem abs_odd_symmetricPerturbation_le_three_halves_energy
    (w : ℝ → ℝ) (hw : Continuous w) (hodd : Function.Odd w) :
    |factorTwoCenteredSymmetricPerturbation w| ≤
      (3 / 2 : ℝ) * (∫ x : ℝ in -1..1, w x ^ 2) := by
  let E : ℝ := ∫ x : ℝ in -1..1, w x ^ 2
  have hE : 0 ≤ E := by
    dsimp only [E]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun x _hx ↦ sq_nonneg (w x))
  have hlower := neg_energy_le_odd_symmetricPerturbation w hw hodd
  have hupper := odd_symmetricPerturbation_le_three_halves_energy w hw hodd
  change -E ≤ factorTwoCenteredSymmetricPerturbation w at hlower
  change factorTwoCenteredSymmetricPerturbation w ≤ (3 / 2 : ℝ) * E at hupper
  rw [abs_le]
  constructor
  · nlinarith
  · exact hupper

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseOddSymmetricBound

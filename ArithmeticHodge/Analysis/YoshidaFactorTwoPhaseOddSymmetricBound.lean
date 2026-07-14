import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseRankLimit

set_option autoImplicit false

open Complex MeasureTheory Real Set
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseOddSymmetricBound

noncomputable section

open CenteredEndpointCorrelation
open YoshidaEndpointHyperbolicBound
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoPhaseRankLimit
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

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseOddSymmetricBound

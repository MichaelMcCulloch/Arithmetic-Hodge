import ArithmeticHodge.Analysis.YoshidaEndpointPotentialExactLowMode
import ArithmeticHodge.Analysis.YoshidaEndpointQuarticObstruction

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointOddLowModePositive

open YoshidaEndpointPotentialExactLowMode
open YoshidaEndpointQuarticObstruction

noncomputable section

/-!
# Positivity of the exact odd endpoint low coefficient

The coarse quartic potential loses on degree one, but the full endpoint
potential reverses that scalar sign.  The proof below uses a classical
positive integral for the structural bound `pi < 22/7`, short logarithm
remainder estimates, and the standard Euler--Mascheroni bounds.  It proves
only the low diagonal margin; low/tail coupling remains a separate Schur
obligation.
-/

/-- The classical positive integrand whose integral is `22/7 - pi`. -/
def archimedesPiWitness (x : ℝ) : ℝ :=
  x ^ 4 * (1 - x) ^ 4 / (1 + x ^ 2)

theorem integral_archimedesPiWitness :
    (∫ x : ℝ in 0..1, archimedesPiWitness x) = 22 / 7 - Real.pi := by
  let p : ℝ → ℝ := fun x ↦
    x ^ 6 - 4 * x ^ 5 + 5 * x ^ 4 - 4 * x ^ 2 + 4
  have hpoint (x : ℝ) :
      archimedesPiWitness x = p x - 4 * (1 + x ^ 2)⁻¹ := by
    unfold archimedesPiWitness
    dsimp only [p]
    have hden : 1 + x ^ 2 ≠ 0 := by nlinarith [sq_nonneg x]
    field_simp [hden]
    ring
  have hp : IntervalIntegrable p volume 0 1 :=
    Continuous.intervalIntegrable (by
      dsimp only [p]
      fun_prop) 0 1
  have hi : IntervalIntegrable (fun x : ℝ ↦ 4 * (1 + x ^ 2)⁻¹)
      volume 0 1 := by
    have hden : Continuous (fun x : ℝ ↦ 1 + x ^ 2) := by fun_prop
    have hinv : Continuous (fun x : ℝ ↦ (1 + x ^ 2)⁻¹) :=
      hden.inv₀ fun x ↦ by nlinarith [sq_nonneg x]
    exact (continuous_const.mul hinv).intervalIntegrable 0 1
  calc
    (∫ x : ℝ in 0..1, archimedesPiWitness x) =
        ∫ x : ℝ in 0..1, p x - 4 * (1 + x ^ 2)⁻¹ := by
      apply intervalIntegral.integral_congr
      intro x _hx
      exact hpoint x
    _ = (∫ x : ℝ in 0..1, p x) -
        ∫ x : ℝ in 0..1, 4 * (1 + x ^ 2)⁻¹ := by
      rw [intervalIntegral.integral_sub hp hi]
    _ = (∫ x : ℝ in 0..1,
        x ^ 6 - 4 * x ^ 5 + 5 * x ^ 4 - 4 * x ^ 2 + 4) -
          4 * ∫ x : ℝ in 0..1, (1 + x ^ 2)⁻¹ := by
      dsimp only [p]
      rw [intervalIntegral.integral_const_mul]
    _ = 22 / 7 - Real.pi := by
      rw [integral_inv_one_add_sq, Real.arctan_one, Real.arctan_zero]
      norm_num [integral_pow, intervalIntegral.integral_add,
        intervalIntegral.integral_sub]
      ring

/-- A structural Archimedean upper bound, proved from a positive integral. -/
theorem pi_lt_twenty_two_div_seven : Real.pi < 22 / 7 := by
  have hpos : 0 < ∫ x : ℝ in 0..1, archimedesPiWitness x := by
    apply intervalIntegral.integral_pos (by norm_num)
    · have hnum : Continuous (fun x : ℝ ↦ x ^ 4 * (1 - x) ^ 4) := by
        fun_prop
      have hden : Continuous (fun x : ℝ ↦ 1 + x ^ 2) := by fun_prop
      exact (hnum.div hden fun x ↦ by
        nlinarith [sq_nonneg x]).continuousOn
    · intro x _hx
      unfold archimedesPiWitness
      positivity
    · refine ⟨1 / 2, by norm_num, ?_⟩
      norm_num [archimedesPiWitness]
  rw [integral_archimedesPiWitness] at hpos
  linarith

/-- A structural upper bound for the endpoint renormalization logarithm. -/
theorem log_pi_mul_log_two_lt_three_hundred_thirteen_div_four_hundred :
    Real.log (Real.pi * Real.log 2) < (313 / 400 : ℝ) := by
  have hprod : Real.pi * Real.log 2 < (1529 / 700 : ℝ) := by
    nlinarith [pi_lt_twenty_two_div_seven,
      log_two_lt_one_hundred_thirty_nine_div_two_hundred,
      Real.pi_pos, Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have hlog : Real.log (1529 / 700 : ℝ) < (313 / 400 : ℝ) := by
    have h := Real.log_div_le_sum_range_add (x := (829 / 2229 : ℝ))
      (by norm_num) (by norm_num) 5
    norm_num [Finset.sum_range_succ] at h ⊢
    linarith
  have hleft : 0 < Real.pi * Real.log 2 := by positivity
  have hright : (0 : ℝ) < 1529 / 700 := by norm_num
  exact (Real.strictMonoOn_log hleft hright hprod).trans hlog

theorem inv_sqrt_two_lt_seventy_one_div_hundred :
    1 / Real.sqrt 2 < (71 / 100 : ℝ) := by
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrtSq : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  rw [div_lt_iff₀ hsqrt]
  nlinarith [Real.sqrt_nonneg 2]

/-- Exact degree-one coefficient supplied by the logarithmic energy and full
potential after subtracting the global odd mass losses. -/
def yoshidaEndpointOddExactLowCoefficient : ℝ :=
  1 + (4 / 3 - Real.log 2) - yoshidaEndpointOddMassLoss

/-- The exact potential leaves a positive low-mode margin of more than
`1/2400`. -/
theorem one_div_two_thousand_four_hundred_lt_yoshidaEndpointOddExactLowCoefficient :
    (1 / 2400 : ℝ) < yoshidaEndpointOddExactLowCoefficient := by
  have hgamma : Real.eulerMascheroniConstant < (2 / 3 : ℝ) :=
    Real.eulerMascheroniConstant_lt_two_thirds
  have hlog :=
    log_pi_mul_log_two_lt_three_hundred_thirteen_div_four_hundred
  have htwo := log_two_lt_one_hundred_thirty_nine_div_two_hundred
  have hsqrt := inv_sqrt_two_lt_seventy_one_div_hundred
  unfold yoshidaEndpointOddExactLowCoefficient yoshidaEndpointOddMassLoss
    yoshidaEndpointEvenMassLoss
  linarith

theorem yoshidaEndpointOddExactLowCoefficient_pos :
    0 < yoshidaEndpointOddExactLowCoefficient :=
  (by norm_num : (0 : ℝ) < 1 / 2400).trans
    one_div_two_thousand_four_hundred_lt_yoshidaEndpointOddExactLowCoefficient

end

end ArithmeticHodge.Analysis.YoshidaEndpointOddLowModePositive

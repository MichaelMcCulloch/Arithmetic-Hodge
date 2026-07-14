import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseTailCoercivity
import ArithmeticHodge.Analysis.YoshidaEndpointScalarStructuralUpper

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseEvenReserve

noncomputable section

open YoshidaEndpointOddCleanPositive
open YoshidaEndpointScalarStructuralUpper

/-!
# Even radius-two reserve

This file records the exact scalar margin in the radius-two
singular-square route.  It also packages the final arithmetic transport:
once the clean, raw, scalar, regular, smooth-regular, and translated-prime
components have their natural lower bounds, their sum leaves more than
`13 / 25` of one endpoint energy.
-/

private theorem dyadic_weight_lt_491_div_1000 :
    Real.log 2 / Real.sqrt 2 < (491 / 1000 : ℝ) := by
  have hsqrtPos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrtSq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrtLower : (707 / 500 : ℝ) < Real.sqrt 2 := by
    nlinarith [Real.sqrt_nonneg 2]
  have hlogUpper := Real.log_two_lt_d9
  rw [div_lt_iff₀ hsqrtPos]
  nlinarith

private theorem prime_three_weight_lt_16_div_25 :
    Real.log 3 / Real.sqrt 3 < (16 / 25 : ℝ) := by
  have hsqrtPos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hsqrtSq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsqrtLower : (173 / 100 : ℝ) < Real.sqrt 3 := by
    nlinarith [Real.sqrt_nonneg 3]
  have hpow : (3 : ℝ) ^ 17 < (2 : ℝ) ^ 27 := by norm_num
  have hlog := Real.strictMonoOn_log (by norm_num) (by norm_num) hpow
  rw [Real.log_pow, Real.log_pow] at hlog
  have hlogUpper := Real.log_two_lt_d9
  rw [div_lt_iff₀ hsqrtPos]
  norm_num at hlog
  nlinarith

/-- The exact scalar reserve left by the radius-two singular-square route.
All transcendental inputs are structural bounds already proved in the
project. -/
theorem even_plus_scalar_reserve_gt_13_div_25 :
    (13 / 25 : ℝ) <
      (51 / 25 : ℝ) + 3 / 4 -
        (1 / 2 : ℝ) *
          (yoshidaEndpointScalarMassLoss + Real.log 2 +
            2 * (Real.log 2 / Real.sqrt 2)) -
        (Real.log 2 / 2) / 64 -
        ((11 / 8 : ℝ) - (11 / 8 : ℝ) * Real.log 2) -
        (Real.log 3 / Real.sqrt 3) / 2 := by
  have hmass := yoshidaEndpointScalarMassLoss_lt_338887_div_250000
  have hlogUpper := Real.log_two_lt_d9
  have hlogLower := Real.log_two_gt_d9
  have halpha := dyadic_weight_lt_491_div_1000
  have hbeta := prime_three_weight_lt_16_div_25
  nlinarith

/-- Arithmetic transport for the even radius-two reserve.  The hypotheses
are precisely the component estimates supplied by half of the clean
coercivity, one eighth of the raw parity gap, and half of the signed
radius-two remainder. -/
theorem thirteen_twenty_fifths_energy_le_of_radiusTwo_component_bounds
    (E clean raw scalar regular smooth prime total : ℝ)
    (hE : 0 ≤ E)
    (hclean : (102 / 25 : ℝ) * E ≤ clean)
    (hraw : 6 * E ≤ raw)
    (hscalar :
      -(1 / 2 : ℝ) *
          (yoshidaEndpointScalarMassLoss + Real.log 2 +
            2 * (Real.log 2 / Real.sqrt 2)) * E ≤ scalar)
    (hregular : -(Real.log 2 / 2) / 64 * E ≤ regular)
    (hsmooth :
      -((11 / 8 : ℝ) - (11 / 8 : ℝ) * Real.log 2) * E ≤ smooth)
    (hprime : -(Real.log 3 / Real.sqrt 3) / 2 * E ≤ prime)
    (hassembly :
      (1 / 2 : ℝ) * clean + raw / 8 + scalar + regular + smooth + prime ≤
        total) :
    (13 / 25 : ℝ) * E ≤ total := by
  have hmargin := even_plus_scalar_reserve_gt_13_div_25
  have hscaled := mul_le_mul_of_nonneg_right (le_of_lt hmargin) hE
  nlinarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseEvenReserve

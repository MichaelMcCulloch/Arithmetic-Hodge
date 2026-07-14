import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseTailCoercivity

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseDirectionalBudget

noncomputable section

open YoshidaFactorTwoEndpointBilinear

/-!
# Directional factor-two phase budget

The symmetric even and odd channels do not need matching absolute bounds.
Their one-sided estimates can be paired with the mixed-channel determinant
bound directly.  The sign of the real phase selects the relevant endpoint of
each one-sided interval; the remaining diagonal budget absorbs the imaginary
phase through the exact real quadratic-pencil criterion.
-/

/-- The asymmetric one-sided channel bounds, together with the sharp mixed
energy estimate, imply positivity in every phase direction in the closed unit
disk.  All constants are exact rationals. -/
theorem phase_uniform_of_directional_tail_bounds
    (Ee Eo Qe Qo Pe Po J a b : ℝ)
    (hEe : 0 ≤ Ee) (hEo : 0 ≤ Eo)
    (hQe : (102 / 25 : ℝ) * Ee ≤ Qe)
    (hQo : (38 / 25 : ℝ) * Eo ≤ Qo)
    (hPeLower : -(3 : ℝ) * Ee ≤ Pe)
    (hPeUpper : Pe ≤ Ee)
    (hPoLower : -Eo ≤ Po)
    (hPoUpper : Po ≤ (3 / 2 : ℝ) * Eo)
    (hJ : J ^ 2 ≤ (625 / 64 : ℝ) * Ee * Eo)
    (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    0 ≤ Qe + Qo + a * (Pe + Po) + b * J := by
  by_cases ha : 0 ≤ a
  · let Re : ℝ := (102 / 25 : ℝ) - 3 * a
    let Ro : ℝ := (38 / 25 : ℝ) - a
    have ha1 : a ≤ 1 := by
      nlinarith [sq_nonneg b]
    have hRe : 0 ≤ Re := by
      dsimp only [Re]
      nlinarith
    have hRo : 0 ≤ Ro := by
      dsimp only [Ro]
      nlinarith
    have hdiagE : Re * Ee ≤ Qe + a * Pe := by
      dsimp only [Re]
      nlinarith
    have hdiagO : Ro * Eo ≤ Qo + a * Po := by
      dsimp only [Ro]
      nlinarith
    have hbudget : (625 / 256 : ℝ) * b ^ 2 ≤ Re * Ro := by
      have hb : b ^ 2 ≤ 1 - a ^ 2 := by
        nlinarith
      have hpoly :
          (625 / 256 : ℝ) * (1 - a ^ 2) ≤ Re * Ro := by
        dsimp only [Re, Ro]
        nlinarith [sq_nonneg (1393 * a - (27648 / 25 : ℝ))]
      exact (mul_le_mul_of_nonneg_left hb (by norm_num)).trans hpoly
    let AE : ℝ := Re * Ee
    let AO : ℝ := Ro * Eo
    let C : ℝ := b * J / 2
    have hAE : 0 ≤ AE := mul_nonneg hRe hEe
    have hAO : 0 ≤ AO := mul_nonneg hRo hEo
    have hC : C ^ 2 ≤ AE * AO := by
      have hJscaled := mul_le_mul_of_nonneg_left hJ (sq_nonneg b)
      have hEprod : 0 ≤ Ee * Eo := mul_nonneg hEe hEo
      have hbudgetScaled :=
        mul_le_mul_of_nonneg_right hbudget hEprod
      dsimp only [C, AE, AO]
      calc
        (b * J / 2) ^ 2 = (b ^ 2 * J ^ 2) / 4 := by ring
        _ ≤ (b ^ 2 * ((625 / 64 : ℝ) * Ee * Eo)) / 4 := by
          nlinarith
        _ = ((625 / 256 : ℝ) * b ^ 2) * (Ee * Eo) := by ring
        _ ≤ (Re * Ro) * (Ee * Eo) := hbudgetScaled
        _ = (Re * Ee) * (Ro * Eo) := by ring
    have hbase : 0 ≤ AE + 2 * C + AO := by
      have hp := (real_quadratic_pencil_nonneg_iff AE AO C).2
        ⟨hAE, hAO, hC⟩ 1 1
      simpa only [one_pow, mul_one] using hp
    dsimp only [AE, AO, C] at hbase
    nlinarith
  · have ha0 : a ≤ 0 := le_of_not_ge ha
    let x : ℝ := -a
    let Re : ℝ := (102 / 25 : ℝ) - x
    let Ro : ℝ := (38 / 25 : ℝ) - (3 / 2 : ℝ) * x
    have hx0 : 0 ≤ x := by
      dsimp only [x]
      linarith
    have hx1 : x ≤ 1 := by
      dsimp only [x]
      nlinarith [sq_nonneg b]
    have hRe : 0 ≤ Re := by
      dsimp only [Re]
      nlinarith
    have hRo : 0 ≤ Ro := by
      dsimp only [Ro]
      nlinarith
    have hdiagE : Re * Ee ≤ Qe + a * Pe := by
      dsimp only [Re, x]
      nlinarith
    have hdiagO : Ro * Eo ≤ Qo + a * Po := by
      dsimp only [Ro, x]
      nlinarith
    have hbudget : (625 / 256 : ℝ) * b ^ 2 ≤ Re * Ro := by
      have hb : b ^ 2 ≤ 1 - x ^ 2 := by
        dsimp only [x]
        nlinarith
      have hpoly :
          (625 / 256 : ℝ) * (1 - x ^ 2) ≤ Re * Ro := by
        dsimp only [Re, Ro]
        nlinarith [sq_nonneg (1009 * x - (24448 / 25 : ℝ))]
      exact (mul_le_mul_of_nonneg_left hb (by norm_num)).trans hpoly
    let AE : ℝ := Re * Ee
    let AO : ℝ := Ro * Eo
    let C : ℝ := b * J / 2
    have hAE : 0 ≤ AE := mul_nonneg hRe hEe
    have hAO : 0 ≤ AO := mul_nonneg hRo hEo
    have hC : C ^ 2 ≤ AE * AO := by
      have hJscaled := mul_le_mul_of_nonneg_left hJ (sq_nonneg b)
      have hEprod : 0 ≤ Ee * Eo := mul_nonneg hEe hEo
      have hbudgetScaled :=
        mul_le_mul_of_nonneg_right hbudget hEprod
      dsimp only [C, AE, AO]
      calc
        (b * J / 2) ^ 2 = (b ^ 2 * J ^ 2) / 4 := by ring
        _ ≤ (b ^ 2 * ((625 / 64 : ℝ) * Ee * Eo)) / 4 := by
          nlinarith
        _ = ((625 / 256 : ℝ) * b ^ 2) * (Ee * Eo) := by ring
        _ ≤ (Re * Ro) * (Ee * Eo) := hbudgetScaled
        _ = (Re * Ee) * (Ro * Eo) := by ring
    have hbase : 0 ≤ AE + 2 * C + AO := by
      have hp := (real_quadratic_pencil_nonneg_iff AE AO C).2
        ⟨hAE, hAO, hC⟩ 1 1
      simpa only [one_pow, mul_one] using hp
    dsimp only [AE, AO, C] at hbase
    nlinarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseDirectionalBudget

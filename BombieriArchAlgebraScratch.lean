import ArithmeticHodge.Analysis.MultiplicativeWeilGammaIntegral
import ArithmeticHodge.Analysis.MultiplicativeWeilHarmonicConstant

set_option autoImplicit false

open Complex Real
open scoped BigOperators

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

private def correctedOddTerm (W : ℕ → ℂ) (z : ℂ) (m : ℕ) : ℂ :=
  W m - (((2 : ℝ) / (2 * (m : ℝ) + 1) : ℝ) : ℂ) * z

private def bombieriHarmonicDelta (n : ℕ) : ℝ :=
  2 / (2 * (((n + 1 : ℕ) : ℝ)) + 1) -
    1 / (((n + 1 : ℕ) : ℝ))

private theorem bombieri_gamma_series_algebra
    (W : ℕ → ℂ) (z : ℂ)
    (hA : Summable (correctedOddTerm W z)) :
    W 0 + ∑' n : ℕ,
        (W (n + 1) - (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ) * z) =
      (∑' m : ℕ, correctedOddTerm W z m) +
        (Real.log 4 : ℂ) * z := by
  have hC : Summable bombieriHarmonicDelta := by
    simpa only [bombieriHarmonicDelta] using
      bombieri_harmonic_series_summable
  have hconst : 2 + ∑' n : ℕ, bombieriHarmonicDelta n = Real.log 4 := by
    simpa only [bombieriHarmonicDelta] using
      bombieri_harmonic_series_eq_log_four
  have hAshift : Summable (fun n : ℕ ↦ correctedOddTerm W z (n + 1)) :=
    hA.comp_injective Nat.succ_injective
  have hCcast : Summable (fun n : ℕ ↦ (bombieriHarmonicDelta n : ℂ)) :=
    Complex.summable_ofReal.mpr hC
  have hCmul : Summable (fun n : ℕ ↦ (bombieriHarmonicDelta n : ℂ) * z) :=
    hCcast.mul_right z
  have hpoint (n : ℕ) :
      W (n + 1) - (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ) * z =
        correctedOddTerm W z (n + 1) +
          (bombieriHarmonicDelta n : ℂ) * z := by
    simp only [correctedOddTerm, bombieriHarmonicDelta]
    push_cast
    ring
  calc
    W 0 + ∑' n : ℕ,
        (W (n + 1) - (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ) * z) =
        correctedOddTerm W z 0 + 2 * z +
          ∑' n : ℕ,
            (correctedOddTerm W z (n + 1) +
              (bombieriHarmonicDelta n : ℂ) * z) := by
      rw [show W 0 = correctedOddTerm W z 0 + 2 * z by
        simp [correctedOddTerm]]
      rw [tsum_congr hpoint]
    _ = correctedOddTerm W z 0 + 2 * z +
          ((∑' n : ℕ, correctedOddTerm W z (n + 1)) +
            ∑' n : ℕ, (bombieriHarmonicDelta n : ℂ) * z) := by
      rw [hAshift.tsum_add hCmul]
    _ = (∑' m : ℕ, correctedOddTerm W z m) +
          (2 + ∑' n : ℕ, (bombieriHarmonicDelta n : ℂ)) * z := by
      rw [hA.tsum_eq_zero_add, hCcast.tsum_mul_right z]
      ring
    _ = (∑' m : ℕ, correctedOddTerm W z m) +
          (Real.log 4 : ℂ) * z := by
      have hconstC :
          (2 : ℂ) + ∑' n : ℕ, (bombieriHarmonicDelta n : ℂ) =
            (Real.log 4 : ℂ) := by
        exact_mod_cast hconst
      rw [hconstC]

#print axioms bombieri_gamma_series_algebra

end

end ArithmeticHodge.Analysis.MultiplicativeWeil

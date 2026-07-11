import BombieriWeightedMellinRealSpaceScratch
import BombieriArchSeriesIntegralScratch
import ArithmeticHodge.Analysis.MultiplicativeWeilHarmonicConstant

set_option autoImplicit false

open Complex MeasureTheory Real Set
open scoped BigOperators

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

private def bombieriWeightedMellinValue
    (f : BombieriTest) (m : ℕ) : ℂ :=
  mellin (bombieriCauchyWeight f (2 * m + 1 / 2)) (1 / 2 : ℝ)

private def bombieriCorrectedWeightedMellinValue
    (f : BombieriTest) (m : ℕ) : ℂ :=
  bombieriWeightedMellinValue f m -
    (((2 : ℝ) / (2 * (m : ℝ) + 1) : ℝ) : ℂ) * f 1

private def bombieriHarmonicDelta (n : ℕ) : ℝ :=
  2 / (2 * (((n + 1 : ℕ) : ℝ)) + 1) -
    1 / (((n + 1 : ℕ) : ℝ))

private theorem hasSum_bombieriCorrectedWeightedMellinValue
    (f : BombieriTest) :
    HasSum (bombieriCorrectedWeightedMellinValue f)
      (∫ x : ℝ in Ioi 1, bombieriArchIntegrand f x) := by
  refine (hasSum_integral_bombieriArchSeriesTerm f).congr_fun (fun m ↦ ?_)
  simpa [bombieriCorrectedWeightedMellinValue,
    bombieriWeightedMellinValue] using
      (bombieriWeightedMellinAtom_sub_eq_realSpace f m)

private theorem bombieri_gamma_series_algebra
    (f : BombieriTest) :
    bombieriWeightedMellinValue f 0 + ∑' n : ℕ,
        (bombieriWeightedMellinValue f (n + 1) -
          (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ) * f 1) =
      (∑' m : ℕ, bombieriCorrectedWeightedMellinValue f m) +
        (Real.log 4 : ℂ) * f 1 := by
  have hA : Summable (bombieriCorrectedWeightedMellinValue f) :=
    (hasSum_bombieriCorrectedWeightedMellinValue f).summable
  have hAshift : Summable
      (fun n : ℕ ↦ bombieriCorrectedWeightedMellinValue f (n + 1)) :=
    hA.comp_injective Nat.succ_injective
  have hC : Summable bombieriHarmonicDelta := by
    simpa only [bombieriHarmonicDelta] using
      bombieri_harmonic_series_summable
  have hCcast : Summable (fun n : ℕ ↦ (bombieriHarmonicDelta n : ℂ)) :=
    Complex.summable_ofReal.mpr hC
  have hCmul : Summable
      (fun n : ℕ ↦ (bombieriHarmonicDelta n : ℂ) * f 1) :=
    hCcast.mul_right (f 1)
  have hpoint (n : ℕ) :
      bombieriWeightedMellinValue f (n + 1) -
          (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ) * f 1 =
        bombieriCorrectedWeightedMellinValue f (n + 1) +
          (bombieriHarmonicDelta n : ℂ) * f 1 := by
    simp only [bombieriCorrectedWeightedMellinValue, bombieriHarmonicDelta]
    push_cast
    ring
  calc
    bombieriWeightedMellinValue f 0 + ∑' n : ℕ,
        (bombieriWeightedMellinValue f (n + 1) -
          (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ) * f 1) =
        bombieriCorrectedWeightedMellinValue f 0 + 2 * f 1 +
          ∑' n : ℕ,
            (bombieriCorrectedWeightedMellinValue f (n + 1) +
              (bombieriHarmonicDelta n : ℂ) * f 1) := by
      rw [show bombieriWeightedMellinValue f 0 =
          bombieriCorrectedWeightedMellinValue f 0 + 2 * f 1 by
        simp [bombieriCorrectedWeightedMellinValue]]
      rw [tsum_congr hpoint]
    _ = bombieriCorrectedWeightedMellinValue f 0 + 2 * f 1 +
          ((∑' n : ℕ, bombieriCorrectedWeightedMellinValue f (n + 1)) +
            ∑' n : ℕ, (bombieriHarmonicDelta n : ℂ) * f 1) := by
      rw [hAshift.tsum_add hCmul]
    _ = (∑' m : ℕ, bombieriCorrectedWeightedMellinValue f m) +
          (2 + ∑' n : ℕ, (bombieriHarmonicDelta n : ℂ)) * f 1 := by
      rw [hA.tsum_eq_zero_add, hCcast.tsum_mul_right (f 1)]
      ring
    _ = (∑' m : ℕ, bombieriCorrectedWeightedMellinValue f m) +
          (Real.log 4 : ℂ) * f 1 := by
      have hconstC :
          (2 : ℂ) + ∑' n : ℕ, (bombieriHarmonicDelta n : ℂ) =
            (Real.log 4 : ℂ) := by
        simp only [bombieriHarmonicDelta]
        exact_mod_cast bombieri_harmonic_series_eq_log_four
      rw [hconstC]

theorem bombieri_digamma_integral_sub_log_pi_eq_archTerm_scratch
    (f : BombieriTest) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ v : ℝ,
          ((Complex.digamma ((1 / 4 : ℝ) + (v / 2) * I)).re : ℂ) *
            mellin (f : ℝ → ℂ) ((1 / 2 : ℝ) + v * I)) -
      (Real.log Real.pi : ℂ) * f 1 =
        bombieriArchTerm f := by
  rw [bombieri_digamma_integral]
  have hseries :
      mellin (bombieriCauchyWeight f (1 / 2)) (1 / 2 : ℝ) +
          ∑' n : ℕ,
            (mellin (bombieriCauchyWeight f (2 * (n + 1) + 1 / 2))
                (1 / 2 : ℝ) -
              (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ) * f 1) =
        (∑' m : ℕ, bombieriCorrectedWeightedMellinValue f m) +
          (Real.log 4 : ℂ) * f 1 := by
    simpa only [bombieriWeightedMellinValue, Nat.cast_zero, mul_zero,
      zero_add, Nat.cast_add, Nat.cast_one] using
        bombieri_gamma_series_algebra f
  let W0 : ℂ :=
    mellin (bombieriCauchyWeight f (1 / 2)) (1 / 2 : ℝ)
  let S : ℂ := ∑' n : ℕ,
    (mellin (bombieriCauchyWeight f (2 * (n + 1) + 1 / 2))
        (1 / 2 : ℝ) -
      (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ) * f 1)
  have hseries' : W0 + S =
      (∑' m : ℕ, bombieriCorrectedWeightedMellinValue f m) +
        (Real.log 4 : ℂ) * f 1 := by
    simpa only [W0, S] using hseries
  change -(W0 + (Real.eulerMascheroniConstant : ℂ) * f 1 + S) -
      (Real.log Real.pi : ℂ) * f 1 = bombieriArchTerm f
  rw [show W0 + (Real.eulerMascheroniConstant : ℂ) * f 1 + S =
      (W0 + S) + (Real.eulerMascheroniConstant : ℂ) * f 1 by ring,
    hseries']
  rw [(hasSum_bombieriCorrectedWeightedMellinValue f).tsum_eq]
  rw [bombieriArchTerm]
  have hlog : Real.log (4 * Real.pi) = Real.log 4 + Real.log Real.pi := by
    exact Real.log_mul (by norm_num) Real.pi_ne_zero
  rw [hlog]
  push_cast
  ring

#print axioms bombieri_digamma_integral_sub_log_pi_eq_archTerm_scratch

end

end ArithmeticHodge.Analysis.MultiplicativeWeil

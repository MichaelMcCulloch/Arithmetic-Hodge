/-
  The zeta logarithmic-derivative realization of Bombieri's prime term.

  Absolute convergence on `Re(s) > 1` identifies the von Mangoldt L-series
  with `-ζ'/ζ`.  Vertical Mellin integration then recovers the finitely
  supported integer samples of a test and its transpose, exactly matching
  the existing `primeSum` normalization.
-/

import ArithmeticHodge.Analysis.MultiplicativeWeilDirichletInterchange
import ArithmeticHodge.Analysis.MultiplicativeWeilPrime

set_option autoImplicit false

open Complex MeasureTheory Real Set
open scoped ArithmeticFunction

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-- On `Re(s) = σ > 1`, the Bombieri Mellin transform times the negative
logarithmic derivative of `ζ` is genuinely integrable. -/
theorem bombieriMellin_mul_negZetaLogDeriv_integrable
    (f : BombieriTest) (σ : ℝ) (hσ : 1 < σ) :
    Integrable (fun t : ℝ ↦
      mellin (f : ℝ → ℂ) (σ + t * I) *
        (-(deriv riemannZeta (σ + t * I) / riemannZeta (σ + t * I)))) := by
  have hsum : LSeriesSummable
      (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ)) σ := by
    simpa using ArithmeticFunction.LSeriesSummable_vonMangoldt
      (show 1 < (σ : ℂ).re by simpa)
  have hL := f.mellin_mul_LSeries_integrable
    (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ)) σ hsum
  refine hL.congr ?_
  filter_upwards [] with t
  have hst : 1 < (σ + t * I).re := by simpa using hσ
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hst]
  ring

/-- The normalized vertical negative-logarithmic-derivative integral equals
the von-Mangoldt-weighted integer samples of the test. -/
theorem bombieriMellin_integral_mul_negZetaLogDeriv
    (f : BombieriTest) (σ : ℝ) (hσ : 1 < σ) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ,
          mellin (f : ℝ → ℂ) (σ + t * I) *
            (-(deriv riemannZeta (σ + t * I) /
              riemannZeta (σ + t * I))) =
      ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * f n := by
  rw [← bombieriMellin_integral_mul_vonMangoldt_LSeries f σ hσ]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  have hst : 1 < (σ + t * I).re := by simpa using hσ
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hst]
  ring

private theorem vonMangoldt_direct_add_transpose_tsum_eq_primeSum
    (f : BombieriTest) :
    (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * f n) +
        (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) *
          transposeLinearMap f n) =
      primeSum f := by
  let D : ℕ → ℂ := fun n ↦
    (ArithmeticFunction.vonMangoldt n : ℂ) * f n
  let T : ℕ → ℂ := fun n ↦
    (ArithmeticFunction.vonMangoldt n : ℂ) * transposeLinearMap f n
  let Q : ℕ → ℂ := fun n ↦
    (ArithmeticFunction.vonMangoldt n : ℂ) *
      (f n + transpose (f : ℝ → ℂ) n)
  have hD : Summable D := by
    simpa only [D] using f.coeffEval_summable
      (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ))
  have hT : Summable T := by
    simpa only [T] using (transposeLinearMap f).coeffEval_summable
      (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ))
  have hQ : Summable Q := by
    refine (hD.add hT).congr ?_
    intro n
    simp only [D, T, Q, transposeLinearMap_apply]
    ring
  calc
    (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * f n) +
        (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) *
          transposeLinearMap f n) =
        ∑' n : ℕ, Q n := by
      rw [show (∑' n : ℕ,
          (ArithmeticFunction.vonMangoldt n : ℂ) * f n) = ∑' n : ℕ, D n by rfl,
        show (∑' n : ℕ,
          (ArithmeticFunction.vonMangoldt n : ℂ) * transposeLinearMap f n) =
            ∑' n : ℕ, T n by rfl,
        ← hD.tsum_add hT]
      apply tsum_congr
      intro n
      simp only [D, T, Q, transposeLinearMap_apply]
      ring
    _ = ∑' k : ℕ, Q (k + 1) := by
      rw [hQ.tsum_eq_zero_add]
      have hQ0 : Q 0 = 0 := by simp [Q]
      rw [hQ0, zero_add]
    _ = primeSum f := by
      unfold primeSum
      apply tsum_congr
      intro k
      rfl

/-- The direct-plus-transpose logarithmic-derivative integrand is genuinely
integrable on every vertical line `σ > 1`. -/
theorem bombieriPrimeSum_integrand_integrable
    (f : BombieriTest) (σ : ℝ) (hσ : 1 < σ) :
    Integrable (fun t : ℝ ↦
      (mellin (f : ℝ → ℂ) (σ + t * I) +
        mellin (transposeLinearMap f : ℝ → ℂ) (σ + t * I)) *
          (-(deriv riemannZeta (σ + t * I) /
            riemannZeta (σ + t * I)))) := by
  have hf := bombieriMellin_mul_negZetaLogDeriv_integrable f σ hσ
  have ht := bombieriMellin_mul_negZetaLogDeriv_integrable
    (transposeLinearMap f) σ hσ
  refine (hf.add ht).congr ?_
  filter_upwards [] with t
  simp only [Pi.add_apply]
  ring

/-- The direct-plus-transpose logarithmic-derivative integral is the existing
finite Bombieri prime sum. -/
theorem bombieriPrimeSum_integral
    (f : BombieriTest) (σ : ℝ) (hσ : 1 < σ) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ,
          (mellin (f : ℝ → ℂ) (σ + t * I) +
            mellin (transposeLinearMap f : ℝ → ℂ) (σ + t * I)) *
              (-(deriv riemannZeta (σ + t * I) /
                riemannZeta (σ + t * I))) =
      primeSum f := by
  let Z : ℝ → ℂ := fun t ↦
    -(deriv riemannZeta (σ + t * I) / riemannZeta (σ + t * I))
  let A : ℝ → ℂ := fun t ↦
    mellin (f : ℝ → ℂ) (σ + t * I) * Z t
  let B : ℝ → ℂ := fun t ↦
    mellin (transposeLinearMap f : ℝ → ℂ) (σ + t * I) * Z t
  have hA : Integrable A := by
    simpa only [A, Z] using
      bombieriMellin_mul_negZetaLogDeriv_integrable f σ hσ
  have hB : Integrable B := by
    simpa only [B, Z] using
      bombieriMellin_mul_negZetaLogDeriv_integrable (transposeLinearMap f) σ hσ
  let c : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  calc
    c * ∫ t : ℝ,
          (mellin (f : ℝ → ℂ) (σ + t * I) +
            mellin (transposeLinearMap f : ℝ → ℂ) (σ + t * I)) * Z t =
        c * ∫ t : ℝ, A t + B t := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with t
      simp only [A, B]
      ring
    _ = c * ((∫ t : ℝ, A t) + ∫ t : ℝ, B t) := by
      rw [MeasureTheory.integral_add hA hB]
    _ = c * (∫ t : ℝ, A t) + c * (∫ t : ℝ, B t) := by ring
    _ = (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * f n) +
        (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) *
          transposeLinearMap f n) := by
      rw [show c * (∫ t : ℝ, A t) =
          ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * f n by
        simpa only [c, A, Z] using
          bombieriMellin_integral_mul_negZetaLogDeriv f σ hσ]
      rw [show c * (∫ t : ℝ, B t) =
          ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) *
            transposeLinearMap f n by
        simpa only [c, B, Z] using
          bombieriMellin_integral_mul_negZetaLogDeriv (transposeLinearMap f) σ hσ]
    _ = primeSum f := vonMangoldt_direct_add_transpose_tsum_eq_primeSum f


end

end ArithmeticHodge.Analysis.MultiplicativeWeil


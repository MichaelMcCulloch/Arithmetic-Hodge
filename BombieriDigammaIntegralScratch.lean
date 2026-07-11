import ArithmeticHodge.Analysis.MultiplicativeWeilArchimedeanKernel
import ArithmeticHodge.Analysis.MultiplicativeWeilDigamma

set_option autoImplicit false

open Complex MeasureTheory Real

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

private theorem bombieriDigammaKernel_eq_cauchy
    (k : ℕ) (v : ℝ) :
    (bombieriDigammaKernel k v : ℂ) =
      (2 * (2 * k + 1 / 2 : ℝ) : ℂ) /
        (((2 * k + 1 / 2 : ℝ) : ℂ) ^ 2 + (v : ℂ) ^ 2) := by
  unfold bombieriDigammaKernel
  push_cast
  congr 1
  ring

private theorem bombieriDigammaKernel_integral
    (f : BombieriTest) (k : ℕ) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ v : ℝ,
          (bombieriDigammaKernel k v : ℂ) *
            mellin (f : ℝ → ℂ) ((1 / 2 : ℝ) + v * I) =
      mellin (bombieriCauchyWeight f (2 * k + 1 / 2)) (1 / 2 : ℝ) := by
  have ha : 0 < (2 * k + 1 / 2 : ℝ) := by positivity
  rw [← bombieriMellin_cauchyKernel_eq_weightedMellin f _ ha]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with v
  rw [bombieriDigammaKernel_eq_cauchy]

private theorem bombieriDigammaKernel_mul_mellin_integrable
    (f : BombieriTest) (k : ℕ) :
    Integrable (fun v : ℝ ↦
      (bombieriDigammaKernel k v : ℂ) *
        mellin (f : ℝ → ℂ) ((1 / 2 : ℝ) + v * I)) := by
  have ha : 0 < (2 * k + 1 / 2 : ℝ) := by positivity
  refine (bombieriMellin_cauchyKernel_integrable f _ ha).congr ?_
  filter_upwards [] with v
  rw [bombieriDigammaKernel_eq_cauchy]

private theorem normalized_integral_mellin_eq_apply_one
    (f : BombieriTest) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ v : ℝ, mellin (f : ℝ → ℂ) ((1 / 2 : ℝ) + v * I) =
      f 1 := by
  have h := bombieriMellin_integral_mul_LSeriesTerm
    f (fun _ : ℕ ↦ (1 : ℂ)) (1 / 2) (n := 1) (by norm_num)
  simpa [LSeries.term] using h

private theorem bombieriDigammaKernel_sub_integral
    (f : BombieriTest) (n : ℕ) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ v : ℝ,
          ((bombieriDigammaKernel (n + 1) v : ℂ) -
              (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ)) *
            mellin (f : ℝ → ℂ) ((1 / 2 : ℝ) + v * I) =
      mellin (bombieriCauchyWeight f (2 * (n + 1) + 1 / 2))
          (1 / 2 : ℝ) -
        (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ) * f 1 := by
  let M : ℝ → ℂ := fun v ↦
    mellin (f : ℝ → ℂ) ((1 / 2 : ℝ) + v * I)
  let r : ℂ := (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ)
  let c : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  have hK : Integrable (fun v : ℝ ↦
      (bombieriDigammaKernel (n + 1) v : ℂ) * M v) := by
    simpa only [M] using
      bombieriDigammaKernel_mul_mellin_integrable f (n + 1)
  have hM : Integrable M := by
    simpa only [M] using f.mellin_verticalIntegrable (1 / 2)
  calc
    c * ∫ v : ℝ,
          ((bombieriDigammaKernel (n + 1) v : ℂ) - r) * M v =
        c * ∫ v : ℝ,
          (bombieriDigammaKernel (n + 1) v : ℂ) * M v - r * M v := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with v
      ring
    _ = c * ((∫ v : ℝ,
          (bombieriDigammaKernel (n + 1) v : ℂ) * M v) -
        ∫ v : ℝ, r * M v) := by
      rw [MeasureTheory.integral_sub hK (hM.const_mul r)]
    _ = (c * ∫ v : ℝ,
          (bombieriDigammaKernel (n + 1) v : ℂ) * M v) -
        r * (c * ∫ v : ℝ, M v) := by
      have hr : (∫ v : ℝ, r * M v) = r * ∫ v : ℝ, M v :=
        MeasureTheory.integral_const_mul (μ := volume) r M
      rw [hr]
      ring
    _ = mellin (bombieriCauchyWeight f (2 * (n + 1) + 1 / 2))
          (1 / 2 : ℝ) - r * f 1 := by
      rw [show c * ∫ v : ℝ,
            (bombieriDigammaKernel (n + 1) v : ℂ) * M v =
          mellin (bombieriCauchyWeight f (2 * (n + 1) + 1 / 2))
            (1 / 2 : ℝ) by
        simpa only [c, M, Nat.cast_add, Nat.cast_one] using
          bombieriDigammaKernel_integral f (n + 1)]
      rw [show c * ∫ v : ℝ, M v = f 1 by
        simpa only [c, M] using normalized_integral_mellin_eq_apply_one f]

#print axioms bombieriDigammaKernel_eq_cauchy
#print axioms bombieriDigammaKernel_integral
#print axioms bombieriDigammaKernel_mul_mellin_integrable
#print axioms normalized_integral_mellin_eq_apply_one
#print axioms bombieriDigammaKernel_sub_integral

end

end ArithmeticHodge.Analysis.MultiplicativeWeil

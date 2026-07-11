import ArithmeticHodge.Analysis.MultiplicativeWeilDigammaSummation

set_option autoImplicit false

open Complex MeasureTheory Real

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

private theorem digamma_quarter_vertical_re_mul_mellin_eq
    (f : BombieriTest) (v : ℝ) :
    ((Complex.digamma ((1 / 4 : ℝ) + (v / 2) * I)).re : ℂ) *
        mellin (f : ℝ → ℂ) ((1 / 2 : ℝ) + v * I) =
      -((bombieriDigammaKernel 0 v : ℂ) *
          mellin (f : ℝ → ℂ) ((1 / 2 : ℝ) + v * I) +
        (Real.eulerMascheroniConstant : ℂ) *
          mellin (f : ℝ → ℂ) ((1 / 2 : ℝ) + v * I) +
        (∑' n : ℕ,
            ((bombieriDigammaKernel (n + 1) v : ℂ) -
              (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ))) *
          mellin (f : ℝ → ℂ) ((1 / 2 : ℝ) + v * I)) := by
  have hc := summable_bombieriDigammaKernel_sub_inv v
  have habs : Summable (fun n : ℕ ↦
      |bombieriDigammaKernel (n + 1) v - ((n + 1 : ℕ) : ℝ)⁻¹|) := by
    simpa only [← Complex.ofReal_inv, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs] using hc.norm
  have hreal : Summable (fun n : ℕ ↦
      bombieriDigammaKernel (n + 1) v - ((n + 1 : ℕ) : ℝ)⁻¹) :=
    habs.of_abs
  have hdig :
      ((Complex.digamma ((1 / 4 : ℝ) + (v / 2) * I)).re : ℂ) =
        -((bombieriDigammaKernel 0 v : ℂ) +
          (Real.eulerMascheroniConstant : ℂ) +
          ∑' n : ℕ,
            ((bombieriDigammaKernel (n + 1) v : ℂ) -
              (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ))) := by
    rw [digamma_quarter_vertical_re_eq]
    push_cast
    rfl
  rw [hdig]
  ring

theorem digamma_quarter_vertical_re_mul_mellin_integrable
    (f : BombieriTest) :
    Integrable (fun v : ℝ ↦
      ((Complex.digamma ((1 / 4 : ℝ) + (v / 2) * I)).re : ℂ) *
        mellin (f : ℝ → ℂ) ((1 / 2 : ℝ) + v * I)) := by
  let M : ℝ → ℂ := fun v ↦
    mellin (f : ℝ → ℂ) ((1 / 2 : ℝ) + v * I)
  let A : ℝ → ℂ := fun v ↦
    (bombieriDigammaKernel 0 v : ℂ) * M v
  let B : ℝ → ℂ := fun v ↦
    (Real.eulerMascheroniConstant : ℂ) * M v
  let C : ℝ → ℂ := fun v ↦
    (∑' n : ℕ,
        ((bombieriDigammaKernel (n + 1) v : ℂ) -
          (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ))) * M v
  have hA : Integrable A := by
    simpa only [A, M] using bombieriDigammaKernel_mul_mellin_integrable f 0
  have hM : Integrable M := by
    simpa only [M] using f.mellin_verticalIntegrable (1 / 2)
  have hB : Integrable B := by
    simpa only [B] using hM.const_mul (Real.eulerMascheroniConstant : ℂ)
  have hC : Integrable C := by
    simpa only [C, M] using bombieriDigammaSeries_integrable f
  refine (((hA.add hB).add hC).neg).congr ?_
  filter_upwards [] with v
  simp only [Pi.add_apply, Pi.neg_apply, A, B, C, M]
  exact (digamma_quarter_vertical_re_mul_mellin_eq f v).symm

theorem bombieri_digamma_integral
    (f : BombieriTest) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ v : ℝ,
          ((Complex.digamma ((1 / 4 : ℝ) + (v / 2) * I)).re : ℂ) *
            mellin (f : ℝ → ℂ) ((1 / 2 : ℝ) + v * I) =
      -(mellin (bombieriCauchyWeight f (1 / 2)) (1 / 2 : ℝ) +
        (Real.eulerMascheroniConstant : ℂ) * f 1 +
        ∑' n : ℕ,
          (mellin (bombieriCauchyWeight f (2 * (n + 1) + 1 / 2))
              (1 / 2 : ℝ) -
            (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ) * f 1)) := by
  let c : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  let M : ℝ → ℂ := fun v ↦
    mellin (f : ℝ → ℂ) ((1 / 2 : ℝ) + v * I)
  let A : ℝ → ℂ := fun v ↦
    (bombieriDigammaKernel 0 v : ℂ) * M v
  let B : ℝ → ℂ := fun v ↦
    (Real.eulerMascheroniConstant : ℂ) * M v
  let C : ℝ → ℂ := fun v ↦
    (∑' n : ℕ,
        ((bombieriDigammaKernel (n + 1) v : ℂ) -
          (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ))) * M v
  have hA : Integrable A := by
    simpa only [A, M] using bombieriDigammaKernel_mul_mellin_integrable f 0
  have hM : Integrable M := by
    simpa only [M] using f.mellin_verticalIntegrable (1 / 2)
  have hB : Integrable B := by
    simpa only [B] using hM.const_mul (Real.eulerMascheroniConstant : ℂ)
  have hC : Integrable C := by
    simpa only [C, M] using bombieriDigammaSeries_integrable f
  calc
    c * ∫ v : ℝ,
          ((Complex.digamma ((1 / 4 : ℝ) + (v / 2) * I)).re : ℂ) * M v =
        c * ∫ v : ℝ, -(A v + B v + C v) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with v
      simpa only [A, B, C, M] using
        digamma_quarter_vertical_re_mul_mellin_eq f v
    _ = -(c * (∫ v : ℝ, A v) + c * (∫ v : ℝ, B v) +
          c * (∫ v : ℝ, C v)) := by
      rw [MeasureTheory.integral_neg]
      have hAB : (∫ v : ℝ, A v + B v) =
          (∫ v : ℝ, A v) + ∫ v : ℝ, B v :=
        MeasureTheory.integral_add hA hB
      have hABC : (∫ v : ℝ, A v + B v + C v) =
          ((∫ v : ℝ, A v) + ∫ v : ℝ, B v) +
            ∫ v : ℝ, C v := by
        calc
          (∫ v : ℝ, A v + B v + C v) =
              (∫ v : ℝ, A v + B v) + ∫ v : ℝ, C v := by
            simpa only [Pi.add_apply] using
              MeasureTheory.integral_add (hA.add hB) hC
          _ = _ := by rw [hAB]
      rw [hABC]
      ring
    _ = -(mellin (bombieriCauchyWeight f (1 / 2)) (1 / 2 : ℝ) +
        (Real.eulerMascheroniConstant : ℂ) * f 1 +
        ∑' n : ℕ,
          (mellin (bombieriCauchyWeight f (2 * (n + 1) + 1 / 2))
              (1 / 2 : ℝ) -
            (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ) * f 1)) := by
      have hAn : c * (∫ v : ℝ, A v) =
          mellin (bombieriCauchyWeight f (1 / 2)) (1 / 2 : ℝ) := by
        simpa only [c, A, M, Nat.cast_zero, mul_zero, zero_add] using
          bombieriDigammaKernel_integral f 0
      have hBn : c * (∫ v : ℝ, B v) =
          (Real.eulerMascheroniConstant : ℂ) * f 1 := by
        rw [show (∫ v : ℝ, B v) =
            (Real.eulerMascheroniConstant : ℂ) * ∫ v : ℝ, M v by
          simpa only [B] using MeasureTheory.integral_const_mul
            (Real.eulerMascheroniConstant : ℂ) M]
        calc
          c * ((Real.eulerMascheroniConstant : ℂ) * ∫ v : ℝ, M v) =
              (Real.eulerMascheroniConstant : ℂ) *
                (c * ∫ v : ℝ, M v) := by ring
          _ = (Real.eulerMascheroniConstant : ℂ) * f 1 := by
            rw [show c * ∫ v : ℝ, M v = f 1 by
              simpa only [c, M] using normalized_integral_mellin_eq_apply_one f]
      have hCn : c * (∫ v : ℝ, C v) =
          ∑' n : ℕ,
            (mellin (bombieriCauchyWeight f (2 * (n + 1) + 1 / 2))
                (1 / 2 : ℝ) -
              (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ) * f 1) := by
        simpa only [c, C, M] using bombieriDigamma_series_integral f
      rw [hAn, hBn, hCn]

#print axioms digamma_quarter_vertical_re_mul_mellin_integrable
#print axioms bombieri_digamma_integral

end

end ArithmeticHodge.Analysis.MultiplicativeWeil

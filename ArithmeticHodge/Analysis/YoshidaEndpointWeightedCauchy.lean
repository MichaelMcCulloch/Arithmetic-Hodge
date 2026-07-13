import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.MeanInequalities

set_option autoImplicit false

open MeasureTheory Real

namespace ArithmeticHodge.Analysis.YoshidaEndpointWeightedCauchy

noncomputable section

/-- Weighted Cauchy--Schwarz in the exact form needed for the even low/tail
Schur complement.  The weight is allowed to have null-set exceptional points. -/
theorem sq_integral_mul_le_weighted
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (W G r : α → ℝ)
    (hW : ∀ᵐ x ∂μ, 0 < W x)
    (hdual : MemLp (fun x ↦ G x / Real.sqrt (W x)) 2 μ)
    (hprimal : MemLp (fun x ↦ Real.sqrt (W x) * r x) 2 μ) :
    (∫ x, G x * r x ∂μ) ^ 2 ≤
      (∫ x, G x ^ 2 / W x ∂μ) *
        (∫ x, W x * r x ^ 2 ∂μ) := by
  let f : α → ℝ := fun x ↦ G x / Real.sqrt (W x)
  let g : α → ℝ := fun x ↦ Real.sqrt (W x) * r x
  have hholder := integral_mul_norm_le_Lp_mul_Lq
    (p := 2) (q := 2) (f := f) (g := g) (μ := μ)
    Real.HolderConjugate.two_two
      (by simpa [f] using hdual) (by simpa [g] using hprimal)
  let A : ℝ := ∫ x, ‖f x‖ ^ 2 ∂μ
  let B : ℝ := ∫ x, ‖g x‖ ^ 2 ∂μ
  have hA0 : 0 ≤ A := by
    dsimp only [A]
    exact integral_nonneg fun _ ↦ sq_nonneg _
  have hB0 : 0 ≤ B := by
    dsimp only [B]
    exact integral_nonneg fun _ ↦ sq_nonneg _
  have hholder' :
      (∫ x, ‖f x‖ * ‖g x‖ ∂μ) ≤ Real.sqrt A * Real.sqrt B := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    simpa only [A, B, Real.rpow_two] using hholder
  have hfg : ∀ᵐ x ∂μ, f x * g x = G x * r x := by
    filter_upwards [hW] with x hx
    dsimp only [f, g]
    have hsqrt : Real.sqrt (W x) ≠ 0 := (Real.sqrt_pos.2 hx).ne'
    field_simp [hsqrt]
  have hnorm :
      ‖∫ x, G x * r x ∂μ‖ ≤ ∫ x, ‖f x‖ * ‖g x‖ ∂μ := by
    calc
      ‖∫ x, G x * r x ∂μ‖ = ‖∫ x, f x * g x ∂μ‖ := by
        congr 1
        apply integral_congr_ae
        filter_upwards [hfg] with x hx
        exact hx.symm
      _ ≤ ∫ x, ‖f x * g x‖ ∂μ := norm_integral_le_integral_norm _
      _ = ∫ x, ‖f x‖ * ‖g x‖ ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with x
        exact norm_mul (f x) (g x)
  have hbound : ‖∫ x, G x * r x ∂μ‖ ≤ Real.sqrt A * Real.sqrt B :=
    hnorm.trans hholder'
  have hsq :
      (∫ x, G x * r x ∂μ) ^ 2 ≤ A * B := by
    have hright : 0 ≤ Real.sqrt A * Real.sqrt B :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    calc
      (∫ x, G x * r x ∂μ) ^ 2 =
          ‖∫ x, G x * r x ∂μ‖ ^ 2 := by
        rw [Real.norm_eq_abs, sq_abs]
      _ ≤ (Real.sqrt A * Real.sqrt B) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) hright).2 hbound
      _ = A * B := by
        rw [mul_pow, Real.sq_sqrt hA0, Real.sq_sqrt hB0]
  have hAeq : A = ∫ x, G x ^ 2 / W x ∂μ := by
    dsimp only [A]
    apply integral_congr_ae
    filter_upwards [hW] with x hx
    dsimp only [f]
    rw [Real.norm_eq_abs, sq_abs, div_pow, Real.sq_sqrt hx.le]
  have hBeq : B = ∫ x, W x * r x ^ 2 ∂μ := by
    dsimp only [B]
    apply integral_congr_ae
    filter_upwards [hW] with x hx
    dsimp only [g]
    rw [Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt hx.le]
  rw [hAeq, hBeq] at hsq
  exact hsq

end


end ArithmeticHodge.Analysis.YoshidaEndpointWeightedCauchy

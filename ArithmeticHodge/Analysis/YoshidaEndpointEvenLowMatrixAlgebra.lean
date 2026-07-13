import Mathlib

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaEndpointEvenLowMatrixAlgebra

noncomputable section

/-- Structural lower-Gram constant entry in terms of `L=log 2`, the complete
even scalar loss, and the constant cosh moment. -/
def evenLow00 (L loss C0 : ℝ) : ℝ :=
  2 - 2 * L - 2 * loss - 15 * L / 32 + L * C0 ^ 2

/-- Structural lower-Gram mixed entry. -/
def evenLow02 (L C0 C2 : ℝ) : ℝ :=
  1 / 3 + L * C0 * C2

/-- Structural lower-Gram degree-two entry. -/
def evenLow22 (L loss C2 : ℝ) : ℝ :=
  86 / 75 - (2 / 5 : ℝ) * (loss + L) + L * C2 ^ 2

/-- The sharp scalar and hyperbolic moment bounds leave a strictly positive
fixed `2 × 2` lower Gram, with explicit rational entry margins. -/
theorem low_matrix_bounds
    (L loss C0 C2 : ℝ)
    (hLlower : (6931 / 10000 : ℝ) < L)
    (hLupper : L < (6932 / 10000 : ℝ))
    (hloss : loss < (854 / 625 : ℝ))
    (hC0lower : (201 / 100 : ℝ) < C0)
    (hC0upper : C0 < (61 / 30 : ℝ))
    (hC2pos : 0 < C2)
    (hC2upper : C2 < (1 / 245 : ℝ)) :
    (3563 / 10000 : ℝ) < evenLow00 L loss C0 ∧
      0 < evenLow02 L C0 C2 ∧
      evenLow02 L C0 C2 < (3391 / 10000 : ℝ) ∧
      (807 / 2500 : ℝ) < evenLow22 L loss C2 ∧
      0 < evenLow00 L loss C0 * evenLow22 L loss C2 -
        evenLow02 L C0 C2 ^ 2 := by
  have hLpos : 0 < L := (by norm_num : (0 : ℝ) < 6931 / 10000).trans hLlower
  have hC0pos : 0 < C0 :=
    (by norm_num : (0 : ℝ) < 201 / 100).trans hC0lower
  let d : ℝ := (201 / 100 : ℝ) ^ 2 - 79 / 32
  have hdpos : 0 < d := by
    dsimp only [d]
    norm_num
  have hC0sq : (201 / 100 : ℝ) ^ 2 < C0 ^ 2 := by
    nlinarith
  have hdelta : d < C0 ^ 2 - 79 / 32 := by
    dsimp only [d]
    linarith
  have hprod00 :
      (6931 / 10000 : ℝ) * d < L * (C0 ^ 2 - 79 / 32) := by
    have hfirst : (6931 / 10000 : ℝ) * d < L * d :=
      mul_lt_mul_of_pos_right hLlower hdpos
    have hsecond : L * d < L * (C0 ^ 2 - 79 / 32) :=
      mul_lt_mul_of_pos_left hdelta hLpos
    exact hfirst.trans hsecond
  have h00 : (3563 / 10000 : ℝ) < evenLow00 L loss C0 := by
    unfold evenLow00
    nlinarith
  have hLC0pos : 0 < L * C0 := mul_pos hLpos hC0pos
  have h02pos : 0 < evenLow02 L C0 C2 := by
    unfold evenLow02
    have := mul_pos hLC0pos hC2pos
    nlinarith
  have hLC0 : L * C0 < (6932 / 10000 : ℝ) * (61 / 30 : ℝ) := by
    exact mul_lt_mul hLupper hC0upper.le hC0pos (by norm_num)
  have hLC0C2 : L * C0 * C2 <
      ((6932 / 10000 : ℝ) * (61 / 30 : ℝ)) * (1 / 245 : ℝ) := by
    exact mul_lt_mul hLC0 hC2upper.le hC2pos (by positivity)
  have h02upper : evenLow02 L C0 C2 < (3391 / 10000 : ℝ) := by
    unfold evenLow02
    nlinarith
  have h22 : (807 / 2500 : ℝ) < evenLow22 L loss C2 := by
    unfold evenLow22
    have hnonneg : 0 ≤ L * C2 ^ 2 :=
      mul_nonneg hLpos.le (sq_nonneg C2)
    nlinarith
  have h22pos : 0 < evenLow22 L loss C2 :=
    (by norm_num : (0 : ℝ) < 807 / 2500).trans h22
  have hprodLower :
      (3563 / 10000 : ℝ) * (807 / 2500 : ℝ) <
        evenLow00 L loss C0 * evenLow22 L loss C2 := by
    have hfirst :
        (3563 / 10000 : ℝ) * (807 / 2500 : ℝ) <
          evenLow00 L loss C0 * (807 / 2500 : ℝ) :=
      mul_lt_mul_of_pos_right h00 (by norm_num)
    have hsecond :
        evenLow00 L loss C0 * (807 / 2500 : ℝ) <
          evenLow00 L loss C0 * evenLow22 L loss C2 :=
      mul_lt_mul_of_pos_left h22
        ((by norm_num : (0 : ℝ) < 3563 / 10000).trans h00)
    exact hfirst.trans hsecond
  have hsqUpper : evenLow02 L C0 C2 ^ 2 < (3391 / 10000 : ℝ) ^ 2 := by
    have hsum : 0 < (3391 / 10000 : ℝ) + evenLow02 L C0 C2 :=
      add_pos (by norm_num) h02pos
    have hdiff : 0 < (3391 / 10000 : ℝ) - evenLow02 L C0 C2 :=
      sub_pos.mpr h02upper
    nlinarith [mul_pos hdiff hsum]
  have hrational :
      (3391 / 10000 : ℝ) ^ 2 <
        (3563 / 10000 : ℝ) * (807 / 2500 : ℝ) := by
    norm_num
  refine ⟨h00, h02pos, h02upper, h22, ?_⟩
  nlinarith

end

end ArithmeticHodge.Analysis.YoshidaEndpointEvenLowMatrixAlgebra

import ArithmeticHodge.Analysis.ComplexStirling

set_option autoImplicit false

open Complex Real

namespace ArithmeticHodge.Analysis

noncomputable section

private def bombieriDigammaKernel (k : ℕ) (v : ℝ) : ℝ :=
  (4 * k + 1 : ℝ) / ((2 * k + 1 / 2 : ℝ) ^ 2 + v ^ 2)

private theorem one_div_quarter_vertical_add_nat_re
    (k : ℕ) (v : ℝ) :
    ((1 : ℂ) /
      ((1 / 4 : ℝ) + (v / 2) * I + k)).re =
        bombieriDigammaKernel k v := by
  let z : ℂ := (1 / 4 : ℝ) + (v / 2) * I + k
  change ((1 : ℂ) / z).re = _
  have hre : z.re = 1 / 4 + k := by simp [z]
  have him : z.im = v / 2 := by simp [z]
  rw [div_re, Complex.normSq_apply, hre, him]
  unfold bombieriDigammaKernel
  simp only [one_re, one_im, zero_mul]
  field_simp
  ring

private theorem digamma_quarter_vertical_re_eq
    (v : ℝ) :
    (Complex.digamma ((1 / 4 : ℝ) + (v / 2) * I)).re =
      -(bombieriDigammaKernel 0 v + Real.eulerMascheroniConstant +
        ∑' n : ℕ,
          (bombieriDigammaKernel (n + 1) v - (n + 1 : ℝ)⁻¹)) := by
  let z : ℂ := (1 / 4 : ℝ) + (v / 2) * I
  have hzre : 0 < z.re := by simp [z]
  have hsumm := summable_digamma_partialFraction_of_nonneg_re z hzre.le
  rw [digamma_eq_tsum_of_pos_re z hzre]
  rw [neg_re, add_re, add_re]
  have hretsum :
      (∑' n : ℕ,
        ((1 : ℂ) / (z + (↑(n + 1 : ℕ) : ℂ)) -
          1 / (↑(n + 1 : ℕ) : ℂ))).re =
        ∑' n : ℕ,
          (((1 : ℂ) / (z + (↑(n + 1 : ℕ) : ℂ)) -
            1 / (↑(n + 1 : ℕ) : ℂ))).re := by
    change Complex.reCLM (∑' n : ℕ,
      ((1 : ℂ) / (z + (↑(n + 1 : ℕ) : ℂ)) -
        1 / (↑(n + 1 : ℕ) : ℂ))) = _
    simpa only [Function.comp_apply] using Complex.reCLM.map_tsum hsumm
  rw [hretsum]
  simp only [ofReal_re]
  change -(((1 / z).re + Real.eulerMascheroniConstant) +
    ∑' n : ℕ,
      ((1 / (z + (n + 1 : ℕ))).re - ((1 : ℂ) / (n + 1 : ℕ)).re)) = _
  have hzero : (1 / z).re = bombieriDigammaKernel 0 v := by
    simpa only [Nat.cast_zero, add_zero, z] using
      one_div_quarter_vertical_add_nat_re 0 v
  rw [hzero]
  congr 2
  apply tsum_congr
  intro n
  rw [show (1 / (z + (n + 1 : ℕ))).re =
      bombieriDigammaKernel (n + 1) v by
    simpa only [z] using one_div_quarter_vertical_add_nat_re (n + 1) v]
  congr 1
  rw [show ((n + 1 : ℕ) : ℂ) = (((n + 1 : ℕ) : ℝ) : ℂ) by norm_cast]
  rw [one_div, ← Complex.ofReal_inv]
  simp
  rw [Complex.normSq_apply]
  norm_num

#print axioms one_div_quarter_vertical_add_nat_re
#print axioms digamma_quarter_vertical_re_eq

end

end ArithmeticHodge.Analysis

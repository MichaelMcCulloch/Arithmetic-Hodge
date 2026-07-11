/-
  A coarse logarithmic lower bound for the critical Bombieri digamma kernel.

  The renormalized partial-fraction summands are nonnegative.  Truncating at
  the natural floor of the vertical parameter exposes a harmonic sum, while
  the discarded rational kernels have a uniform finite-sum bound.
-/

import ArithmeticHodge.Analysis.MultiplicativeWeilDigamma
import Mathlib.NumberTheory.Harmonic.Bounds

set_option autoImplicit false

open Complex Real

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

private theorem bombieriDigammaKernel_nonneg (k : ℕ) (v : ℝ) :
    0 ≤ bombieriDigammaKernel k v := by
  unfold bombieriDigammaKernel
  positivity

private theorem bombieriDigammaKernel_le_div_sq
    (k : ℕ) {v : ℝ} (hv : 1 ≤ |v|) :
    bombieriDigammaKernel k v ≤ (4 * k + 1 : ℝ) / v ^ 2 := by
  have hv0 : v ≠ 0 := by
    intro hvzero
    subst v
    norm_num at hv
  unfold bombieriDigammaKernel
  gcongr
  nlinarith [sq_nonneg (2 * (k : ℝ) + 1 / 2)]

private theorem harmonic_sum_lower_log (N : ℕ) :
    Real.log (N + 1 : ℝ) ≤
      ∑ k ∈ Finset.range N, ((k + 1 : ℕ) : ℝ)⁻¹ := by
  simpa [harmonic] using log_add_one_le_harmonic N

private theorem bombieriDigammaKernel_le_inv_succ
    (n : ℕ) (v : ℝ) :
    bombieriDigammaKernel (n + 1) v ≤ ((n + 1 : ℕ) : ℝ)⁻¹ := by
  simp only [bombieriDigammaKernel, Nat.cast_add, Nat.cast_one]
  let m : ℝ := n + 1
  change (4 * m + 1) / ((2 * m + 1 / 2) ^ 2 + v ^ 2) ≤ m⁻¹
  have hm : 1 ≤ m := by simp [m]
  have hm0 : 0 < m := zero_lt_one.trans_le hm
  have hden : 0 < (2 * m + 1 / 2) ^ 2 + v ^ 2 := by positivity
  rw [div_le_iff₀ hden]
  field_simp
  nlinarith [sq_nonneg v]

private theorem bombieriDigammaKernel_zero_le_four (v : ℝ) :
    bombieriDigammaKernel 0 v ≤ 4 := by
  unfold bombieriDigammaKernel
  norm_num
  have hden : 0 < (1 / 4 : ℝ) + v ^ 2 := by positivity
  rw [inv_eq_one_div, div_le_iff₀ hden]
  nlinarith [sq_nonneg v]

private theorem one_div_quarter_vertical_add_nat_re_lower
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

private theorem summable_bombieriDigammaKernel_sub_inv_real
    (v : ℝ) :
    Summable (fun n : ℕ ↦
      bombieriDigammaKernel (n + 1) v - ((n + 1 : ℕ) : ℝ)⁻¹) := by
  let z : ℂ := (1 / 4 : ℝ) + (v / 2) * I
  have hzre : 0 ≤ z.re := by simp [z]
  have hs := summable_digamma_partialFraction_of_nonneg_re z hzre
  have hre : Summable (fun n : ℕ ↦
      Complex.reCLM ((1 : ℂ) / (z + (n + 1 : ℕ)) - 1 / (n + 1 : ℕ))) := by
    simpa only [Function.comp_apply] using
      hs.map Complex.reCLM Complex.reCLM.continuous
  refine hre.congr ?_
  intro n
  change (((1 : ℂ) / (z + (n + 1 : ℕ)) -
    1 / (n + 1 : ℕ)).re) = _
  rw [sub_re]
  rw [show ((1 : ℂ) / (z + (n + 1 : ℕ))).re =
      bombieriDigammaKernel (n + 1) v by
    simpa only [z] using
      one_div_quarter_vertical_add_nat_re_lower (n + 1) v]
  congr 1
  rw [show ((n + 1 : ℕ) : ℂ) = (((n + 1 : ℕ) : ℝ) : ℂ) by norm_cast]
  rw [one_div, ← Complex.ofReal_inv]
  simp
  rw [Complex.normSq_apply]
  norm_num

private theorem summable_inv_sub_bombieriDigammaKernel_real
    (v : ℝ) :
    Summable (fun n : ℕ ↦
      ((n + 1 : ℕ) : ℝ)⁻¹ - bombieriDigammaKernel (n + 1) v) := by
  simpa only [neg_sub] using
    (summable_bombieriDigammaKernel_sub_inv_real v).neg

private theorem sum_bombieriDigammaKernel_floor_le_five
    {v : ℝ} (hv : 1 ≤ |v|) :
    ∑ k ∈ Finset.range ⌊|v|⌋₊,
      bombieriDigammaKernel (k + 1) v ≤ 5 := by
  let N : ℕ := ⌊|v|⌋₊
  have hv0 : v ≠ 0 := by
    intro hvzero
    subst v
    norm_num at hv
  have hv2 : 0 < v ^ 2 := sq_pos_of_ne_zero hv0
  have hNle : (N : ℝ) ≤ |v| := by
    exact Nat.floor_le (abs_nonneg v)
  have hNone : 1 ≤ N := by
    simpa only [N] using (Nat.one_le_floor_iff |v|).2 hv
  have hNoneR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNone
  have hNsq : (N : ℝ) ^ 2 ≤ v ^ 2 := by
    rw [← sq_abs v]
    exact (sq_le_sq₀ (Nat.cast_nonneg N) (abs_nonneg v)).2 hNle
  have hterm : ∀ k ∈ Finset.range N,
      bombieriDigammaKernel (k + 1) v ≤
        5 * (N : ℝ) / v ^ 2 := by
    intro k hk
    have hkN : k + 1 ≤ N := by
      exact Nat.succ_le_iff.mpr (Finset.mem_range.mp hk)
    have hkNR : ((k + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast hkN
    calc
      bombieriDigammaKernel (k + 1) v ≤
          (4 * ((k + 1 : ℕ) : ℝ) + 1) / v ^ 2 := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          bombieriDigammaKernel_le_div_sq (k + 1) hv
      _ ≤ 5 * (N : ℝ) / v ^ 2 := by
        rw [div_le_div_iff_of_pos_right hv2]
        nlinarith
  change ∑ k ∈ Finset.range N,
      bombieriDigammaKernel (k + 1) v ≤ 5
  calc
    ∑ k ∈ Finset.range N, bombieriDigammaKernel (k + 1) v
        ≤ ∑ _k ∈ Finset.range N, 5 * (N : ℝ) / v ^ 2 := by
          exact Finset.sum_le_sum hterm
    _ = (N : ℝ) * (5 * (N : ℝ) / v ^ 2) := by simp
    _ = 5 * (N : ℝ) ^ 2 / v ^ 2 := by ring
    _ ≤ 5 := by
      rw [div_le_iff₀ hv2]
      nlinarith

private theorem digamma_quarter_vertical_re_eq_nonneg_series
    (v : ℝ) :
    (Complex.digamma ((1 / 4 : ℝ) + (v / 2) * I)).re =
      -bombieriDigammaKernel 0 v - Real.eulerMascheroniConstant +
        ∑' n : ℕ,
          (((n + 1 : ℕ) : ℝ)⁻¹ - bombieriDigammaKernel (n + 1) v) := by
  rw [digamma_quarter_vertical_re_eq]
  have htsum :
      (∑' n : ℕ,
          (((n + 1 : ℕ) : ℝ)⁻¹ - bombieriDigammaKernel (n + 1) v)) =
        -∑' n : ℕ,
          (bombieriDigammaKernel (n + 1) v - ((n + 1 : ℕ) : ℝ)⁻¹) := by
    calc
      (∑' n : ℕ,
          (((n + 1 : ℕ) : ℝ)⁻¹ - bombieriDigammaKernel (n + 1) v)) =
          ∑' n : ℕ,
            -(bombieriDigammaKernel (n + 1) v - ((n + 1 : ℕ) : ℝ)⁻¹) := by
              apply tsum_congr
              intro n
              ring
      _ = -∑' n : ℕ,
          (bombieriDigammaKernel (n + 1) v - ((n + 1 : ℕ) : ℝ)⁻¹) :=
        tsum_neg
  rw [htsum]
  simp only [Nat.cast_add, Nat.cast_one]
  ring

private theorem digamma_quarter_vertical_re_global_lower (v : ℝ) :
    -4 - |Real.eulerMascheroniConstant| ≤
      (Complex.digamma ((1 / 4 : ℝ) + (v / 2) * I)).re := by
  rw [digamma_quarter_vertical_re_eq_nonneg_series]
  have htsum : 0 ≤ ∑' n : ℕ,
      (((n + 1 : ℕ) : ℝ)⁻¹ - bombieriDigammaKernel (n + 1) v) := by
    apply tsum_nonneg
    intro n
    exact sub_nonneg.mpr (bombieriDigammaKernel_le_inv_succ n v)
  nlinarith [bombieriDigammaKernel_zero_le_four v,
    le_abs_self Real.eulerMascheroniConstant]

private theorem digamma_quarter_vertical_re_log_lower
    {v : ℝ} (hv : 1 ≤ |v|) :
    Real.log |v| - (9 + |Real.eulerMascheroniConstant|) ≤
      (Complex.digamma ((1 / 4 : ℝ) + (v / 2) * I)).re := by
  let N : ℕ := ⌊|v|⌋₊
  have hvpos : 0 < |v| := zero_lt_one.trans_le hv
  have hfloor_lt : |v| < (N : ℝ) + 1 := by
    simpa only [N, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one |v|
  have hlog_floor : Real.log |v| ≤ Real.log (N + 1 : ℝ) :=
    Real.log_le_log hvpos hfloor_lt.le
  have hlog_sum : Real.log |v| ≤
      ∑ n ∈ Finset.range N, ((n + 1 : ℕ) : ℝ)⁻¹ :=
    hlog_floor.trans (harmonic_sum_lower_log N)
  have hkernel_sum :
      ∑ n ∈ Finset.range N, bombieriDigammaKernel (n + 1) v ≤ 5 := by
    simpa only [N] using sum_bombieriDigammaKernel_floor_le_five hv
  have hfinite :
      ∑ n ∈ Finset.range N,
          (((n + 1 : ℕ) : ℝ)⁻¹ - bombieriDigammaKernel (n + 1) v) ≤
        ∑' n : ℕ,
          (((n + 1 : ℕ) : ℝ)⁻¹ - bombieriDigammaKernel (n + 1) v) := by
    exact (summable_inv_sub_bombieriDigammaKernel_real v).sum_le_tsum
      (Finset.range N) (fun n _hn ↦
        sub_nonneg.mpr (bombieriDigammaKernel_le_inv_succ n v))
  rw [Finset.sum_sub_distrib] at hfinite
  rw [digamma_quarter_vertical_re_eq_nonneg_series]
  nlinarith [bombieriDigammaKernel_zero_le_four v,
    le_abs_self Real.eulerMascheroniConstant]

theorem exists_bombieriCriticalGammaKernel_log_lower :
    ∃ C : ℝ, 0 < C ∧ ∀ v : ℝ,
      (1 / 2 : ℝ) * Real.log (max 1 |v|) - C ≤
        (Complex.digamma ((1 / 4 : ℝ) + (v / 2) * Complex.I)).re -
          Real.log Real.pi := by
  refine ⟨9 + |Real.eulerMascheroniConstant| + |Real.log Real.pi|, ?_, ?_⟩
  · positivity
  intro v
  by_cases hv : 1 ≤ |v|
  · have hlog_nonneg : 0 ≤ Real.log |v| := Real.log_nonneg hv
    have hlower := digamma_quarter_vertical_re_log_lower hv
    rw [max_eq_right hv]
    nlinarith [le_abs_self (Real.log Real.pi)]
  · have hvle : |v| ≤ 1 := le_of_not_ge hv
    have hlower := digamma_quarter_vertical_re_global_lower v
    rw [max_eq_left hvle, Real.log_one]
    nlinarith [le_abs_self (Real.log Real.pi)]

end


end ArithmeticHodge.Analysis.MultiplicativeWeil

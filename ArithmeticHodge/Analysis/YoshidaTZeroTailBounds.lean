import ArithmeticHodge.Analysis.DigammaTrapezoid
import ArithmeticHodge.Analysis.YoshidaWeightedTailBounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Set

namespace ArithmeticHodge.Analysis.YoshidaTZeroTailBounds

open YoshidaWeightedTailBounds
open DigammaTrapezoid

/-! Yoshida Section 6 defines `t₀` as the positive zero of
`t ↦ Re ψ(1/4 + i t/2)` and reports `t₀ = 2.0320...`.

The rational endpoint `51/25 = 2.04` leaves enough room for exact weighted-tail
certificates. -/

def IsYoshidaTZero (t : ℝ) : Prop :=
  0 < t ∧
    (Complex.digamma ((1 / 4 : ℝ) + (t / 2) * Complex.I)).re = 0

def lowCUpperQ : ℚ := 177 / 250

theorem odd_low_rational_head_tail_certificate :
    finiteWeightedUpperQ lowCUpperQ 11 190 +
      analyticTailUpperQ lowCUpperQ 200 < 77 / 200 := by
  decide +kernel

theorem even_low_rational_head_tail_certificate :
    finiteWeightedUpperQ lowCUpperQ 200 201 +
      analyticTailUpperQ lowCUpperQ 400 < 101 / 5000 := by
  decide +kernel

theorem yoshidaA_mul_51_div_25_le_lowCUpper :
    yoshidaA * (51 / 25 : ℝ) ≤ ((lowCUpperQ : ℚ) : ℝ) := by
  norm_num [yoshidaA, lowCUpperQ] at ⊢
  nlinarith [Real.log_two_lt_d9]

private theorem yoshidaA_pos : 0 < yoshidaA := by
  unfold yoshidaA
  positivity

theorem odd_low_weightedTail_of_mem_Icc
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) (51 / 25 : ℝ)) :
    weightedTail 10 t ≤ (77 / 200 : ℝ) := by
  have hAt0 : 0 ≤ yoshidaA * t :=
    mul_nonneg yoshidaA_pos.le ht.1
  have hAtEndpoint : yoshidaA * t ≤ yoshidaA * (51 / 25 : ℝ) :=
    mul_le_mul_of_nonneg_left ht.2 yoshidaA_pos.le
  have hcc : yoshidaA * t ≤ ((lowCUpperQ : ℚ) : ℝ) :=
    hAtEndpoint.trans yoshidaA_mul_51_div_25_le_lowCUpper
  have h := weightedTail_le_finite_add_analytic
    (N := 10) (count := 190) (t := t)
    (cUpper := ((lowCUpperQ : ℚ) : ℝ))
    (by norm_num) hAt0 (by norm_num [lowCUpperQ]) hcc
    (by norm_num [lowCUpperQ, piLowerR])
  rw [show 10 + 190 = 200 by norm_num] at h
  have hcert :
      ((finiteWeightedUpperQ lowCUpperQ 11 190 : ℚ) : ℝ) +
          ((analyticTailUpperQ lowCUpperQ 200 : ℚ) : ℝ) <
        (77 / 200 : ℝ) := by
    have hr :
        (((finiteWeightedUpperQ lowCUpperQ 11 190 +
            analyticTailUpperQ lowCUpperQ 200 : ℚ)) : ℝ) <
          (((77 / 200 : ℚ)) : ℝ) := by
      exact_mod_cast odd_low_rational_head_tail_certificate
    simpa using hr
  rw [coe_finiteWeightedUpperQ, coe_analyticTailUpperQ] at hcert
  norm_num [lowCUpperQ] at hcert h
  exact h.trans hcert.le

theorem even_low_weightedTail_of_mem_Icc
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) (51 / 25 : ℝ)) :
    weightedTail 199 t ≤ (101 / 5000 : ℝ) := by
  have hAt0 : 0 ≤ yoshidaA * t :=
    mul_nonneg yoshidaA_pos.le ht.1
  have hAtEndpoint : yoshidaA * t ≤ yoshidaA * (51 / 25 : ℝ) :=
    mul_le_mul_of_nonneg_left ht.2 yoshidaA_pos.le
  have hcc : yoshidaA * t ≤ ((lowCUpperQ : ℚ) : ℝ) :=
    hAtEndpoint.trans yoshidaA_mul_51_div_25_le_lowCUpper
  have h := weightedTail_le_finite_add_analytic
    (N := 199) (count := 201) (t := t)
    (cUpper := ((lowCUpperQ : ℚ) : ℝ))
    (by norm_num) hAt0 (by norm_num [lowCUpperQ]) hcc
    (by norm_num [lowCUpperQ, piLowerR])
  rw [show 199 + 201 = 400 by norm_num] at h
  have hcert :
      ((finiteWeightedUpperQ lowCUpperQ 200 201 : ℚ) : ℝ) +
          ((analyticTailUpperQ lowCUpperQ 400 : ℚ) : ℝ) <
        (101 / 5000 : ℝ) := by
    have hr :
        (((finiteWeightedUpperQ lowCUpperQ 200 201 +
            analyticTailUpperQ lowCUpperQ 400 : ℚ)) : ℝ) <
          (((101 / 5000 : ℚ)) : ℝ) := by
      exact_mod_cast even_low_rational_head_tail_certificate
    simpa using hr
  rw [coe_finiteWeightedUpperQ, coe_analyticTailUpperQ] at hcert
  norm_num [lowCUpperQ] at hcert h
  exact h.trans hcert.le

def endpointKernelQ (k : ℕ) : ℚ :=
  ((1 / 4 : ℚ) + k) /
    (((1 / 4 : ℚ) + k) ^ 2 + (51 / 50 : ℚ) ^ 2)

def endpointKernelSumQ : ℚ :=
  ∑ k ∈ Finset.range 257, endpointKernelQ k

theorem endpoint_kernel_sum_certificate :
    endpointKernelSumQ < 8 * (6931471803 / 10000000000 : ℚ) := by
  decide +kernel

theorem coe_endpointKernelQ (k : ℕ) :
    ((endpointKernelQ k : ℚ) : ℝ) =
      shiftedReciprocalRealPart (1 / 4) (51 / 50) k := by
  norm_num [endpointKernelQ, shiftedReciprocalRealPart, reciprocalRealPart]

theorem coe_endpointKernelSumQ :
    ((endpointKernelSumQ : ℚ) : ℝ) =
      ∑ k ∈ Finset.range 257,
        shiftedReciprocalRealPart (1 / 4) (51 / 50) k := by
  simp [endpointKernelSumQ, coe_endpointKernelQ]

private theorem quarterDigammaSeriesTerm_endpoint_nonneg (n : ℕ) :
    0 ≤ quarterDigammaSeriesTerm (51 / 25) n := by
  have hm : 0 < (n : ℝ) + 1 := by positivity
  have hden : 0 < ((1 / 4 : ℝ) + ((n : ℝ) + 1)) ^ 2 +
      (51 / 50 : ℝ) ^ 2 := by
    positivity
  have hcross : ((1 / 4 : ℝ) + ((n : ℝ) + 1)) * ((n : ℝ) + 1) ≤
      ((1 / 4 : ℝ) + ((n : ℝ) + 1)) ^ 2 + (51 / 50 : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((1 / 4 : ℝ) + ((n : ℝ) + 1)),
      sq_nonneg (51 / 50 : ℝ)]
  unfold quarterDigammaSeriesTerm shiftedReciprocalRealPart reciprocalRealPart
  norm_num at hden hcross ⊢
  rw [inv_eq_one_div, div_le_div_iff₀ hden hm]
  simpa using hcross

theorem digamma_quarter_vertical_re_51_div_25_pos :
    0 < (Complex.digamma ((1 / 4 : ℝ) +
      ((51 / 25 : ℝ) / 2) * Complex.I)).re := by
  have hgamma := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 256
  rw [Real.eulerMascheroniSeq', if_neg (by norm_num)] at hgamma
  have hlog :
      8 * (6931471803 / 10000000000 : ℝ) < Real.log (256 : ℝ) := by
    rw [show (256 : ℝ) = (2 : ℝ) ^ 8 by norm_num, Real.log_pow]
    nlinarith [Real.log_two_gt_d9]
  have hkernelQ :
      ((endpointKernelSumQ : ℚ) : ℝ) <
        8 * (6931471803 / 10000000000 : ℝ) := by
    have hr :
        ((endpointKernelSumQ : ℚ) : ℝ) <
          (((8 * (6931471803 / 10000000000 : ℚ)) : ℚ) : ℝ) := by
      exact_mod_cast endpoint_kernel_sum_certificate
    norm_num at hr ⊢
    exact hr
  rw [coe_endpointKernelSumQ] at hkernelQ
  have hlogNat :
      8 * (6931471803 / 10000000000 : ℝ) <
        Real.log (((256 : ℕ) : ℝ)) := by
    simpa using hlog
  have hlogKernel :
      (∑ k ∈ Finset.range 257,
          shiftedReciprocalRealPart (1 / 4) (51 / 50) k) <
        Real.log (((256 : ℕ) : ℝ)) := hkernelQ.trans hlogNat
  have hHarmonic :
      Real.log (((256 : ℕ) : ℝ)) <
        (harmonic 256 : ℝ) - Real.eulerMascheroniConstant := by
    linarith only [hgamma]
  have hpartialPos : 0 < quarterDigammaPartialApprox (51 / 25) 256 := by
    rw [quarterDigammaPartialApprox_eq_harmonic_sub_sum]
    rw [show 256 + 1 = 257 by norm_num,
      show (51 / 25 : ℝ) / 2 = 51 / 50 by norm_num]
    exact sub_pos.mpr (hlogKernel.trans hHarmonic)
  have hfinite :
      ∑ n ∈ Finset.range 256, quarterDigammaSeriesTerm (51 / 25) n ≤
        ∑' n : ℕ, quarterDigammaSeriesTerm (51 / 25) n :=
    (summable_quarterDigammaSeriesTerm (51 / 25)).sum_le_tsum
      (Finset.range 256)
      (fun n _hn ↦ quarterDigammaSeriesTerm_endpoint_nonneg n)
  rw [digamma_quarter_vertical_re_eq_trapezoid_series]
  unfold quarterDigammaPartialApprox at hpartialPos
  norm_num at hpartialPos ⊢
  linarith

theorem shiftedReciprocalRealPart_antitone_abs
    (k : ℕ) {v w : ℝ} (hvw : |v| ≤ |w|) :
    shiftedReciprocalRealPart (1 / 4) (w / 2) k ≤
      shiftedReciprocalRealPart (1 / 4) (v / 2) k := by
  have hsq : (v / 2) ^ 2 ≤ (w / 2) ^ 2 := by
    have habs : |v / 2| ≤ |w / 2| := by
      simpa [abs_div] using (div_le_div_of_nonneg_right hvw (by norm_num : (0 : ℝ) ≤ 2))
    rw [← sq_abs (v / 2), ← sq_abs (w / 2)]
    exact (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).2 habs
  unfold shiftedReciprocalRealPart reciprocalRealPart
  apply div_le_div_of_nonneg_left
  · positivity
  · positivity
  · nlinarith

theorem re_digamma_quarter_vertical_monotoneOn :
    MonotoneOn
      (fun v : ℝ ↦
        (Complex.digamma ((1 / 4 : ℝ) + (v / 2) * Complex.I)).re)
      (Set.Ici 0) := by
  intro v hv w hw hvw
  have hv0 : 0 ≤ v := hv
  have hw0 : 0 ≤ w := hw
  have habs : |v| ≤ |w| := by
    simpa [abs_of_nonneg hv0, abs_of_nonneg hw0] using hvw
  have hzero := shiftedReciprocalRealPart_antitone_abs 0 habs
  have hpoint (n : ℕ) :
      quarterDigammaSeriesTerm v n ≤ quarterDigammaSeriesTerm w n := by
    unfold quarterDigammaSeriesTerm
    simpa only [Nat.cast_add, Nat.cast_one] using
      (sub_le_sub_left
        (shiftedReciprocalRealPart_antitone_abs (n + 1) habs)
        (((n + 1 : ℕ) : ℝ)⁻¹))
  have htsum :
      (∑' n : ℕ, quarterDigammaSeriesTerm v n) ≤
        ∑' n : ℕ, quarterDigammaSeriesTerm w n :=
    (summable_quarterDigammaSeriesTerm v).tsum_le_tsum hpoint
      (summable_quarterDigammaSeriesTerm w)
  change
    (Complex.digamma ((1 / 4 : ℝ) + (v / 2) * Complex.I)).re ≤
      (Complex.digamma ((1 / 4 : ℝ) + (w / 2) * Complex.I)).re
  rw [digamma_quarter_vertical_re_eq_trapezoid_series,
    digamma_quarter_vertical_re_eq_trapezoid_series]
  linarith [hzero, htsum]

theorem yoshidaTZero_le_51_div_25
    {tZero : ℝ} (ht : IsYoshidaTZero tZero) :
    tZero ≤ (51 / 25 : ℝ) := by
  by_contra hnot
  have hlt : (51 / 25 : ℝ) < tZero := lt_of_not_ge hnot
  have hmono := re_digamma_quarter_vertical_monotoneOn
    (show (51 / 25 : ℝ) ∈ Set.Ici 0 by norm_num)
    (show tZero ∈ Set.Ici 0 by exact ht.1.le) hlt.le
  change
    (Complex.digamma ((1 / 4 : ℝ) +
      ((51 / 25 : ℝ) / 2) * Complex.I)).re ≤
      (Complex.digamma ((1 / 4 : ℝ) +
        (tZero / 2) * Complex.I)).re at hmono
  rw [ht.2] at hmono
  linarith [digamma_quarter_vertical_re_51_div_25_pos]

theorem odd_weightedTail_at_yoshidaTZero
    {tZero : ℝ} (ht : IsYoshidaTZero tZero) :
    weightedTail 10 tZero ≤ (77 / 200 : ℝ) := by
  apply odd_low_weightedTail_of_mem_Icc
  exact ⟨ht.1.le, yoshidaTZero_le_51_div_25 ht⟩

theorem even_weightedTail_at_yoshidaTZero
    {tZero : ℝ} (ht : IsYoshidaTZero tZero) :
    weightedTail 199 tZero ≤ (101 / 5000 : ℝ) := by
  apply even_low_weightedTail_of_mem_Icc
  exact ⟨ht.1.le, yoshidaTZero_le_51_div_25 ht⟩

end ArithmeticHodge.Analysis.YoshidaTZeroTailBounds

import ArithmeticHodge.Analysis.DigammaNumericBounds
import ArithmeticHodge.Analysis.YoshidaWeightedTailBounds

noncomputable section

open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaCoercivityNumerics

open ArithmeticHodge.Analysis.DigammaNumericBounds
open ArithmeticHodge.Analysis.YoshidaWeightedTailBounds

/-!
# Yoshida Section 6 numerical substitution

This module packages the rational inequalities surrounding Yoshida's
equations (6.7)--(6.9).  The high-frequency weighted tails and the two
digamma values are discharged by kernel-checked certificates; the remaining
low-interval tail is kept as an explicit input until its source parameter
`tZero` is certified.
-/

def digammaQuarterVerticalRe (t : ℝ) : ℝ :=
  (Complex.digamma ((1 / 4 : ℝ) + (t / 2) * Complex.I)).re

def oscillatoryWindow (t : ℝ) : ℝ :=
  t - Real.sin (2 * yoshidaA * t) / (2 * yoshidaA)

def highFrequencyPenalty (N : ℕ) (t C : ℝ) : ℝ :=
  yoshidaA * C / (2 * Real.pi ^ 3) *
    oscillatoryWindow t * weightedTail N t

def lowIntervalPenalty (N : ℕ) (tZero : ℝ) : ℝ :=
  (2773 / 1000 : ℝ) * yoshidaA / Real.pi ^ 3 * weightedTail N tZero

def section6LowerBound (N : ℕ) (tZero tOne : ℝ) : ℝ :=
  let C := digammaQuarterVerticalRe tOne
  C - Real.log Real.pi - (1 / Real.sqrt 2 - Real.log 2) -
    highFrequencyPenalty N tOne C - lowIntervalPenalty N tZero

theorem log_two_gt_693_div_1000 : (693 / 1000 : ℝ) < Real.log 2 := by
  exact (by norm_num : (693 / 1000 : ℝ) < 0.6931471803).trans Real.log_two_gt_d9

theorem inv_sqrt_two_lt_71_div_100 :
    1 / Real.sqrt 2 < (71 / 100 : ℝ) := by
  have hsqrt_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrt_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hrat : (100 / 71 : ℝ) < Real.sqrt 2 := by
    nlinarith
  rw [div_lt_iff₀ hsqrt_pos]
  nlinarith

theorem inv_sqrt_two_lt_177_div_250 :
    1 / Real.sqrt 2 < (177 / 250 : ℝ) := by
  have hsqrt_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrt_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hrat : (250 / 177 : ℝ) < Real.sqrt 2 := by
    nlinarith
  rw [div_lt_iff₀ hsqrt_pos]
  nlinarith

theorem two_mul_yoshidaA_eq_log_two : 2 * yoshidaA = Real.log 2 := by
  unfold yoshidaA
  ring

theorem yoshidaA_pos : 0 < yoshidaA := by
  unfold yoshidaA
  positivity

theorem yoshidaA_lt_347_div_1000 : yoshidaA < (347 / 1000 : ℝ) := by
  unfold yoshidaA
  nlinarith [Real.log_two_lt_d9]

theorem pi_cube_gt_31415_div_10000_cube :
    (31415 / 10000 : ℝ) ^ 3 < Real.pi ^ 3 := by
  have h := pow_lt_pow_left₀ (n := 3) Real.pi_gt_d4 (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

theorem weightedTail_nonneg (N : ℕ) (t : ℝ) : 0 ≤ weightedTail N t := by
  unfold weightedTail
  exact tsum_nonneg fun k => mul_nonneg (one_div_nonneg.mpr (sq_nonneg _)) (sq_nonneg _)

theorem oscillatoryWindow_upper (t : ℝ) :
    oscillatoryWindow t ≤ t + 1000 / 693 := by
  have hlog : (693 / 1000 : ℝ) < 2 * yoshidaA := by
    rw [two_mul_yoshidaA_eq_log_two]
    exact log_two_gt_693_div_1000
  have hden : 0 < 2 * yoshidaA := by positivity
  have hinv : 1 / (2 * yoshidaA) < (1000 / 693 : ℝ) := by
    rw [div_lt_iff₀ hden]
    nlinarith
  have hsin := Real.neg_one_le_sin (2 * yoshidaA * t)
  unfold oscillatoryWindow
  have hfrac :
      -(Real.sin (2 * yoshidaA * t)) / (2 * yoshidaA) ≤
        1 / (2 * yoshidaA) := by
    exact (div_le_div_iff_of_pos_right hden).2 (by linarith)
  calc
    oscillatoryWindow t =
        t + (-(Real.sin (2 * yoshidaA * t)) / (2 * yoshidaA)) := by
      unfold oscillatoryWindow
      ring
    _ ≤ t + 1 / (2 * yoshidaA) := add_le_add_right hfrac t
    _ ≤ t + 1000 / 693 := add_le_add_right hinv.le t

theorem oscillatoryWindow_50_nonneg : 0 ≤ oscillatoryWindow 50 := by
  have hden : 0 < 2 * yoshidaA := mul_pos (by norm_num) yoshidaA_pos
  have hlog : (693 / 1000 : ℝ) < 2 * yoshidaA := by
    rw [two_mul_yoshidaA_eq_log_two]
    exact log_two_gt_693_div_1000
  have hinv : 1 / (2 * yoshidaA) < (1000 / 693 : ℝ) := by
    rw [div_lt_iff₀ hden]
    nlinarith
  have hsin := Real.sin_le_one (2 * yoshidaA * 50)
  unfold oscillatoryWindow
  have hfrac :
      Real.sin (2 * yoshidaA * 50) / (2 * yoshidaA) ≤
        1 / (2 * yoshidaA) :=
    (div_le_div_iff_of_pos_right hden).2 hsin
  nlinarith

theorem oscillatoryWindow_700_nonneg : 0 ≤ oscillatoryWindow 700 := by
  have hden : 0 < 2 * yoshidaA := mul_pos (by norm_num) yoshidaA_pos
  have hlog : (693 / 1000 : ℝ) < 2 * yoshidaA := by
    rw [two_mul_yoshidaA_eq_log_two]
    exact log_two_gt_693_div_1000
  have hinv : 1 / (2 * yoshidaA) < (1000 / 693 : ℝ) := by
    rw [div_lt_iff₀ hden]
    nlinarith
  have hsin := Real.sin_le_one (2 * yoshidaA * 700)
  unfold oscillatoryWindow
  have hfrac :
      Real.sin (2 * yoshidaA * 700) / (2 * yoshidaA) ≤
        1 / (2 * yoshidaA) :=
    (div_le_div_iff_of_pos_right hden).2 hsin
  nlinarith

theorem highFrequencyPenalty_le_of_rational_components
    {N : ℕ} {t C cUpper windowUpper tailUpper target : ℝ}
    (hC0 : 0 ≤ C) (hC : C ≤ cUpper) (hcUpper0 : 0 ≤ cUpper)
    (hWindow0 : 0 ≤ oscillatoryWindow t)
    (hWindow : oscillatoryWindow t ≤ windowUpper)
    (hWindowUpper0 : 0 ≤ windowUpper)
    (hTail0 : 0 ≤ weightedTail N t)
    (hTail : weightedTail N t ≤ tailUpper)
    (hTarget0 : 0 ≤ target)
    (hRational :
      (347 / 1000 : ℝ) * cUpper * windowUpper * tailUpper ≤
        target * (2 * (31415 / 10000 : ℝ) ^ 3)) :
    highFrequencyPenalty N t C ≤ target := by
  have ha : yoshidaA ≤ (347 / 1000 : ℝ) := yoshidaA_lt_347_div_1000.le
  have hac : yoshidaA * C ≤ (347 / 1000 : ℝ) * cUpper :=
    mul_le_mul ha hC hC0 (by norm_num)
  have hacw : yoshidaA * C * oscillatoryWindow t ≤
      (347 / 1000 : ℝ) * cUpper * windowUpper :=
    mul_le_mul hac hWindow hWindow0
      (mul_nonneg (by norm_num) hcUpper0)
  have hnum : yoshidaA * C * oscillatoryWindow t * weightedTail N t ≤
      (347 / 1000 : ℝ) * cUpper * windowUpper * tailUpper :=
    mul_le_mul hacw hTail hTail0
      (mul_nonneg (mul_nonneg (by norm_num) hcUpper0) hWindowUpper0)
  have hpiCube : (31415 / 10000 : ℝ) ^ 3 ≤ Real.pi ^ 3 :=
    pi_cube_gt_31415_div_10000_cube.le
  have hden : 0 < 2 * Real.pi ^ 3 := by positivity
  rw [show highFrequencyPenalty N t C =
      (yoshidaA * C * oscillatoryWindow t * weightedTail N t) /
        (2 * Real.pi ^ 3) by
    unfold highFrequencyPenalty
    ring]
  apply (div_le_iff₀ hden).2
  calc
    yoshidaA * C * oscillatoryWindow t * weightedTail N t ≤
        (347 / 1000 : ℝ) * cUpper * windowUpper * tailUpper := hnum
    _ ≤ target * (2 * (31415 / 10000 : ℝ) ^ 3) := hRational
    _ ≤ target * (2 * Real.pi ^ 3) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hpiCube (by norm_num)) hTarget0

theorem lowIntervalPenalty_le_of_weightedTail
    {N : ℕ} {tZero tailUpper target : ℝ}
    (hTail : weightedTail N tZero ≤ tailUpper)
    (hTarget0 : 0 ≤ target)
    (hRational :
      (2773 / 1000 : ℝ) * (347 / 1000 : ℝ) * tailUpper ≤
        target * (31415 / 10000 : ℝ) ^ 3) :
    lowIntervalPenalty N tZero ≤ target := by
  have hTail0 : 0 ≤ weightedTail N tZero := weightedTail_nonneg N tZero
  have hconst0 : 0 ≤ (2773 / 1000 : ℝ) := by norm_num
  have hfirst :
      (2773 / 1000 : ℝ) * yoshidaA ≤
        (2773 / 1000 : ℝ) * (347 / 1000 : ℝ) :=
    mul_le_mul_of_nonneg_left yoshidaA_lt_347_div_1000.le hconst0
  have hnum :
      (2773 / 1000 : ℝ) * yoshidaA * weightedTail N tZero ≤
        (2773 / 1000 : ℝ) * (347 / 1000 : ℝ) * tailUpper :=
    mul_le_mul hfirst hTail hTail0
      (mul_nonneg hconst0 (by norm_num))
  have hpiCube : (31415 / 10000 : ℝ) ^ 3 ≤ Real.pi ^ 3 :=
    pi_cube_gt_31415_div_10000_cube.le
  have hden : 0 < Real.pi ^ 3 := by positivity
  rw [show lowIntervalPenalty N tZero =
      ((2773 / 1000 : ℝ) * yoshidaA * weightedTail N tZero) /
        Real.pi ^ 3 by
    unfold lowIntervalPenalty
    ring]
  apply (div_le_iff₀ hden).2
  calc
    (2773 / 1000 : ℝ) * yoshidaA * weightedTail N tZero ≤
        (2773 / 1000 : ℝ) * (347 / 1000 : ℝ) * tailUpper := hnum
    _ ≤ target * (31415 / 10000 : ℝ) ^ 3 := hRational
    _ ≤ target * Real.pi ^ 3 := mul_le_mul_of_nonneg_left hpiCube hTarget0

theorem pi_lt_exp_229_div_200 : Real.pi < Real.exp (229 / 200 : ℝ) := by
  let x : ℝ := 29 / 200
  have hx : 0 ≤ x := by norm_num [x]
  have hpoly :
      1 + x + x ^ 2 / 2 + x ^ 3 / 6 ≤ Real.exp x := by
    have h := Real.sum_le_exp_of_nonneg hx 4
    norm_num [Finset.sum_range_succ] at h ⊢
    nlinarith
  calc
    Real.pi < (3.1416 : ℝ) := Real.pi_lt_d4
    _ < (2.7182818283 : ℝ) *
        (1 + x + x ^ 2 / 2 + x ^ 3 / 6) := by norm_num [x]
    _ ≤ Real.exp 1 * Real.exp x := by
      exact mul_le_mul Real.exp_one_gt_d9.le hpoly
        (by positivity) (Real.exp_nonneg 1)
    _ = Real.exp (229 / 200 : ℝ) := by
      rw [← Real.exp_add]
      congr 1
      norm_num [x]

theorem log_pi_lt_229_div_200 :
    Real.log Real.pi < (229 / 200 : ℝ) := by
  rw [← Real.exp_lt_exp]
  rw [Real.exp_log Real.pi_pos]
  exact pi_lt_exp_229_div_200

theorem odd_highFrequencyPenalty_le
    (hC0 : 0 ≤ digammaQuarterVerticalRe 50)
    (hCUpper : digammaQuarterVerticalRe 50 ≤ (3219 / 1000 : ℝ))
    (hTail : weightedTail 10 50 ≤ (283 / 500 : ℝ)) :
    highFrequencyPenalty 10 50 (digammaQuarterVerticalRe 50) ≤
      (263 / 500 : ℝ) := by
  apply highFrequencyPenalty_le_of_rational_components
      (cUpper := (3219 / 1000 : ℝ))
      (windowUpper := (50 + 1000 / 693 : ℝ))
      (tailUpper := (283 / 500 : ℝ))
  · exact hC0
  · exact hCUpper
  · norm_num
  · exact oscillatoryWindow_50_nonneg
  · exact oscillatoryWindow_upper 50
  · norm_num
  · exact weightedTail_nonneg 10 50
  · exact hTail
  · norm_num
  · norm_num

theorem even_highFrequencyPenalty_le
    (hC0 : 0 ≤ digammaQuarterVerticalRe 700)
    (hCUpper : digammaQuarterVerticalRe 700 ≤ (5858 / 1000 : ℝ))
    (hTail : weightedTail 199 700 ≤ (53 / 2000 : ℝ)) :
    highFrequencyPenalty 199 700 (digammaQuarterVerticalRe 700) ≤
      (61 / 100 : ℝ) := by
  apply highFrequencyPenalty_le_of_rational_components
      (cUpper := (5858 / 1000 : ℝ))
      (windowUpper := (700 + 1000 / 693 : ℝ))
      (tailUpper := (53 / 2000 : ℝ))
  · exact hC0
  · exact hCUpper
  · norm_num
  · exact oscillatoryWindow_700_nonneg
  · exact oscillatoryWindow_upper 700
  · norm_num
  · exact weightedTail_nonneg 199 700
  · exact hTail
  · norm_num
  · norm_num

theorem odd_lowIntervalPenalty_le
    {tZero : ℝ} (hTail : weightedTail 10 tZero ≤ (77 / 200 : ℝ)) :
    lowIntervalPenalty 10 tZero ≤ (3 / 250 : ℝ) := by
  apply lowIntervalPenalty_le_of_weightedTail
      (tailUpper := (77 / 200 : ℝ))
  · exact hTail
  · norm_num
  · norm_num

theorem even_lowIntervalPenalty_le
    {tZero : ℝ} (hTail : weightedTail 199 tZero ≤ (101 / 5000 : ℝ)) :
    lowIntervalPenalty 199 tZero ≤ (1 / 1000 : ℝ) := by
  apply lowIntervalPenalty_le_of_weightedTail
      (tailUpper := (101 / 5000 : ℝ))
  · exact hTail
  · norm_num
  · norm_num

theorem odd_substitution_from_source_aligned_enclosures
    {formValue C highLoss lowLoss : ℝ}
    (h67 : C - Real.log Real.pi - (1 / Real.sqrt 2 - Real.log 2) -
      highLoss - lowLoss ≤ formValue)
    (hC : (1609 / 500 : ℝ) ≤ C)
    (hHigh : highLoss ≤ (263 / 500 : ℝ))
    (hLow : lowLoss ≤ (3 / 250 : ℝ)) :
    (38 / 25 : ℝ) ≤ formValue := by
  nlinarith [log_two_gt_693_div_1000, inv_sqrt_two_lt_177_div_250,
    log_pi_lt_229_div_200]

theorem even_substitution_from_source_aligned_enclosures
    {formValue C highLoss lowLoss : ℝ}
    (h67 : C - Real.log Real.pi - (1 / Real.sqrt 2 - Real.log 2) -
      highLoss - lowLoss ≤ formValue)
    (hC : (5857 / 1000 : ℝ) ≤ C)
    (hHigh : highLoss ≤ (61 / 100 : ℝ))
    (hLow : lowLoss ≤ (1 / 1000 : ℝ)) :
    (102 / 25 : ℝ) ≤ formValue := by
  nlinarith [log_two_gt_693_div_1000, inv_sqrt_two_lt_177_div_250,
    log_pi_lt_229_div_200]

theorem odd_section6_domain_condition :
    yoshidaA * 50 < Real.pi * ((10 + 1 : ℕ) : ℝ) := by
  unfold yoshidaA
  have hlog := Real.log_two_lt_d9
  have hpi := Real.pi_gt_three
  norm_num at hlog ⊢
  nlinarith

theorem even_section6_domain_condition :
    yoshidaA * 700 < Real.pi * ((199 + 1 : ℕ) : ℝ) := by
  unfold yoshidaA
  have hlog := Real.log_two_lt_d9
  have hpi := Real.pi_gt_three
  norm_num at hlog ⊢
  nlinarith

/-- The four numerical certificates still required after equation (6.7)
has been proved analytically, for Yoshida's `(t₁,N)=(50,10)` substitution. -/
structure OddSourceAlignedEnclosures (tZero : ℝ) : Prop where
  digamma_at_50_lower :
    (1609 / 500 : ℝ) ≤ digammaQuarterVerticalRe 50
  digamma_at_50_upper :
    digammaQuarterVerticalRe 50 ≤ (3219 / 1000 : ℝ)
  weighted_tail_50_10_upper :
    weightedTail 10 50 ≤ (283 / 500 : ℝ)
  weighted_tail_tZero_10_upper :
    weightedTail 10 tZero ≤ (77 / 200 : ℝ)

/-- The four numerical certificates still required after equation (6.7)
has been proved analytically, for Yoshida's `(t₁,N)=(700,199)` substitution.

The lower endpoint `5.857` is deliberately weaker than the direct numerical
value `5.857933...`; it does not use the source's discrepant printed
`5.9914...`. -/
structure EvenSourceAlignedEnclosures (tZero : ℝ) : Prop where
  digamma_at_700_lower :
    (5857 / 1000 : ℝ) ≤ digammaQuarterVerticalRe 700
  digamma_at_700_upper :
    digammaQuarterVerticalRe 700 ≤ (5858 / 1000 : ℝ)
  weighted_tail_700_199_upper :
    weightedTail 199 700 ≤ (53 / 2000 : ℝ)
  weighted_tail_tZero_199_upper :
    weightedTail 199 tZero ≤ (101 / 5000 : ℝ)

/-- The odd source-aligned enclosure now needs only the low-interval tail:
the digamma and high-frequency tail fields are certified independently. -/
theorem oddSourceAlignedEnclosures_of_lowTail
    {tZero : ℝ} (hLow : weightedTail 10 tZero ≤ (77 / 200 : ℝ)) :
    OddSourceAlignedEnclosures tZero where
  digamma_at_50_lower := by
    simpa [digammaQuarterVerticalRe] using
      digamma_quarter_vertical_re_fifty_lower
  digamma_at_50_upper := by
    simpa [digammaQuarterVerticalRe] using
      digamma_quarter_vertical_re_fifty_upper
  weighted_tail_50_10_upper := odd_weightedTail_upper
  weighted_tail_tZero_10_upper := hLow

/-- The even source-aligned enclosure now needs only the low-interval tail.
The upper digamma endpoint `2929 / 500` is exactly `5858 / 1000`. -/
theorem evenSourceAlignedEnclosures_of_lowTail
    {tZero : ℝ} (hLow : weightedTail 199 tZero ≤ (101 / 5000 : ℝ)) :
    EvenSourceAlignedEnclosures tZero where
  digamma_at_700_lower := by
    simpa [digammaQuarterVerticalRe] using
      digamma_quarter_vertical_re_sevenHundred_lower
  digamma_at_700_upper := by
    have h := digamma_quarter_vertical_re_sevenHundred_upper
    norm_num [digammaQuarterVerticalRe] at h ⊢
    exact h
  weighted_tail_700_199_upper := even_weightedTail_upper
  weighted_tail_tZero_199_upper := hLow

theorem odd_section6_lowerBound_ge_source
    {tZero : ℝ} (h : OddSourceAlignedEnclosures tZero) :
    (38 / 25 : ℝ) ≤ section6LowerBound 10 tZero 50 := by
  have hC0 : 0 ≤ digammaQuarterVerticalRe 50 :=
    (by norm_num : (0 : ℝ) ≤ 1609 / 500).trans h.digamma_at_50_lower
  have hHigh := odd_highFrequencyPenalty_le
    hC0 h.digamma_at_50_upper h.weighted_tail_50_10_upper
  have hLow := odd_lowIntervalPenalty_le h.weighted_tail_tZero_10_upper
  apply odd_substitution_from_source_aligned_enclosures
      (C := digammaQuarterVerticalRe 50)
      (highLoss := highFrequencyPenalty 10 50 (digammaQuarterVerticalRe 50))
      (lowLoss := lowIntervalPenalty 10 tZero)
  · rfl
  · exact h.digamma_at_50_lower
  · exact hHigh
  · exact hLow

theorem even_section6_lowerBound_ge_source
    {tZero : ℝ} (h : EvenSourceAlignedEnclosures tZero) :
    (102 / 25 : ℝ) ≤ section6LowerBound 199 tZero 700 := by
  have hC0 : 0 ≤ digammaQuarterVerticalRe 700 :=
    (by norm_num : (0 : ℝ) ≤ 5857 / 1000).trans h.digamma_at_700_lower
  have hHigh := even_highFrequencyPenalty_le
    hC0 h.digamma_at_700_upper h.weighted_tail_700_199_upper
  have hLow := even_lowIntervalPenalty_le h.weighted_tail_tZero_199_upper
  apply even_substitution_from_source_aligned_enclosures
      (C := digammaQuarterVerticalRe 700)
      (highLoss := highFrequencyPenalty 199 700 (digammaQuarterVerticalRe 700))
      (lowLoss := lowIntervalPenalty 199 tZero)
  · rfl
  · exact h.digamma_at_700_lower
  · exact hHigh
  · exact hLow

theorem odd_form_value_ge_source_of_equation6_7
    {tZero formValue : ℝ} (h : OddSourceAlignedEnclosures tZero)
    (hequation6_7 : section6LowerBound 10 tZero 50 ≤ formValue) :
    (38 / 25 : ℝ) ≤ formValue :=
  (odd_section6_lowerBound_ge_source h).trans hequation6_7

theorem even_form_value_ge_source_of_equation6_7
    {tZero formValue : ℝ} (h : EvenSourceAlignedEnclosures tZero)
    (hequation6_7 : section6LowerBound 199 tZero 700 ≤ formValue) :
    (102 / 25 : ℝ) ≤ formValue :=
  (even_section6_lowerBound_ge_source h).trans hequation6_7

theorem odd_section6_lowerBound_ge_of_lowTail
    {tZero : ℝ} (hLow : weightedTail 10 tZero ≤ (77 / 200 : ℝ)) :
    (38 / 25 : ℝ) ≤ section6LowerBound 10 tZero 50 :=
  odd_section6_lowerBound_ge_source
    (oddSourceAlignedEnclosures_of_lowTail hLow)

theorem even_section6_lowerBound_ge_of_lowTail
    {tZero : ℝ} (hLow : weightedTail 199 tZero ≤ (101 / 5000 : ℝ)) :
    (102 / 25 : ℝ) ≤ section6LowerBound 199 tZero 700 :=
  even_section6_lowerBound_ge_source
    (evenSourceAlignedEnclosures_of_lowTail hLow)

theorem odd_form_value_ge_of_lowTail_and_equation6_7
    {tZero formValue : ℝ}
    (hLow : weightedTail 10 tZero ≤ (77 / 200 : ℝ))
    (hequation6_7 : section6LowerBound 10 tZero 50 ≤ formValue) :
    (38 / 25 : ℝ) ≤ formValue :=
  (odd_section6_lowerBound_ge_of_lowTail hLow).trans hequation6_7

theorem even_form_value_ge_of_lowTail_and_equation6_7
    {tZero formValue : ℝ}
    (hLow : weightedTail 199 tZero ≤ (101 / 5000 : ℝ))
    (hequation6_7 : section6LowerBound 199 tZero 700 ≤ formValue) :
    (102 / 25 : ℝ) ≤ formValue :=
  (even_section6_lowerBound_ge_of_lowTail hLow).trans hequation6_7

theorem source_printed_even_C_conflicts_with_5858_upper
    {C : ℝ} (hprinted : (59914 / 10000 : ℝ) ≤ C)
    (hcomputedUpper : C ≤ (5858 / 1000 : ℝ)) : False := by
  norm_num at hprinted hcomputedUpper
  linarith

end ArithmeticHodge.Analysis.YoshidaCoercivityNumerics

import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowControlStep01WeightedProfileSharp
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowStaticMinusRationalSchur
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowAlternatingKernelSharp
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicEvenPositiveEndpointLoewnerUltraSharp
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddCleanSharp
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddPerturbationLoewnerSharp

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowControlStep01CoupledResidualPositive

noncomputable section

open YoshidaEndpointOddResidualRegularity
open YoshidaEndpointOddFullPolarization
open YoshidaEndpointOddLowGramExpansion
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoEndpointParityPencil
open YoshidaFactorTwoPhaseIntrinsicEvenLowEndpointPositive
open YoshidaFactorTwoPhaseIntrinsicEvenPositiveEndpointLoewnerUltraSharp
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicLowAlternatingKernelSharp
open YoshidaFactorTwoPhaseIntrinsicLowControlStep01CauchyStructural
open YoshidaFactorTwoPhaseIntrinsicLowControlStep01Positive
open YoshidaFactorTwoPhaseIntrinsicLowControlStep01SharpClosure
open YoshidaFactorTwoPhaseIntrinsicLowControlStep01WeightedProfileSharp
open YoshidaFactorTwoPhaseIntrinsicLowControlMonotonicity
open YoshidaFactorTwoPhaseIntrinsicLowStaticMinusRationalSchur
open YoshidaFactorTwoPhaseIntrinsicLowStaticMinusStructural
open YoshidaFactorTwoPhaseIntrinsicLowStaticSplitPositive
open YoshidaFactorTwoPhaseIntrinsicOddCleanSharp
open YoshidaFactorTwoPhaseIntrinsicOddPerturbationLoewnerSharp
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoPhaseOddStructuralPerturbation

/-!
# Positivity of the intrinsic Step01 coupled residual

The alternating block is kept in its sum/difference coordinates.  The
resulting Schur determinant retains the positive square of the determinant
of the two alternating columns; it is not replaced by three independent
entry budgets.
-/

/-- Rational lower Gram targeted for the positive even endpoint. -/
def step01EvenLower00 : ℝ := 1383 / 10000
def step01EvenLower02 : ℝ := 6769 / 50000
def step01EvenLower22 : ℝ := 1381 / 10000

def step01EvenLower (u v : ℝ) : ℝ :=
  step01EvenLower00 * u ^ 2 +
    2 * step01EvenLower02 * u * v + step01EvenLower22 * v ^ 2

/-- Lower odd budget corresponding to the determinant slope `23 / 5`.
It is the sum of twice the clean lower Gram and `13 / 5` times the
positive-endpoint odd lower Gram. -/
def step01OddBudgetLower11 : ℝ := 8611 / 10000
def step01OddBudgetLower13 : ℝ := 4471 / 5000
def step01OddBudgetLower33 : ℝ := 30389 / 25000

def step01OddBudgetLower (c d : ℝ) : ℝ :=
  step01OddBudgetLower11 * c ^ 2 +
    2 * step01OddBudgetLower13 * c * d +
      step01OddBudgetLower33 * d ^ 2

theorem step01EvenLower_principal_minors_pos :
    0 < step01EvenLower00 ∧
      0 < step01EvenLower00 * step01EvenLower22 -
        step01EvenLower02 ^ 2 := by
  norm_num [step01EvenLower00, step01EvenLower02, step01EvenLower22]

theorem step01OddBudgetLower_principal_minors_pos :
    0 < step01OddBudgetLower11 ∧
      0 < step01OddBudgetLower11 * step01OddBudgetLower33 -
        step01OddBudgetLower13 ^ 2 := by
  norm_num [step01OddBudgetLower11, step01OddBudgetLower13,
    step01OddBudgetLower33]

theorem step01EvenLower_nonneg (u v : ℝ) :
    0 ≤ step01EvenLower u v := by
  by_cases hne : u ≠ 0 ∨ v ≠ 0
  · exact (real_twoByTwo_quadratic_pos
      step01EvenLower00 step01EvenLower02 step01EvenLower22 u v
      step01EvenLower_principal_minors_pos.1
      step01EvenLower_principal_minors_pos.2 hne).le
  · push_neg at hne
    rcases hne with ⟨rfl, rfl⟩
    norm_num [step01EvenLower]

theorem step01OddBudgetLower_nonneg (c d : ℝ) :
    0 ≤ step01OddBudgetLower c d := by
  by_cases hne : c ≠ 0 ∨ d ≠ 0
  · exact (real_twoByTwo_quadratic_pos
      step01OddBudgetLower11 step01OddBudgetLower13
      step01OddBudgetLower33 c d
      step01OddBudgetLower_principal_minors_pos.1
      step01OddBudgetLower_principal_minors_pos.2 hne).le
  · push_neg at hne
    rcases hne with ⟨rfl, rfl⟩
    norm_num [step01OddBudgetLower]

/-- The rational even Gram is a Loewner lower bound for the exact positive
endpoint form. -/
theorem step01EvenLower_le (u v : ℝ) :
    step01EvenLower u v ≤ factorTwoIntrinsicEvenPlusQuadratic u v := by
  simpa [step01EvenLower, step01EvenLower00, step01EvenLower02,
    step01EvenLower22, evenPositiveEndpointUltraSharp00,
    evenPositiveEndpointUltraSharp02, evenPositiveEndpointUltraSharp22,
    factorTwoIntrinsicEvenPlusQuadratic,
    factorTwoIntrinsicStaticEvenQuadratic] using
      (evenPositiveEndpointUltraSharp_quadratic_le u v)

private def step01OddCleanLower (c d : ℝ) : ℝ :=
  (1777 / 10000 : ℝ) * c ^ 2 +
    2 * (2001 / 10000 : ℝ) * c * d +
      (3314 / 10000 : ℝ) * d ^ 2

private def step01OddPlusLower (c d : ℝ) : ℝ :=
  (1945 / 10000 : ℝ) * c ^ 2 +
    2 * (19 / 100 : ℝ) * c * d +
      (1063 / 5000 : ℝ) * d ^ 2

private theorem step01OddPlusLower_nonneg (c d : ℝ) :
    0 ≤ step01OddPlusLower c d := by
  by_cases hne : c ≠ 0 ∨ d ≠ 0
  · exact (real_twoByTwo_quadratic_pos
      (1945 / 10000) (19 / 100) (1063 / 5000) c d
      (by norm_num) (by norm_num) hne).le
  · push_neg at hne
    rcases hne with ⟨rfl, rfl⟩
    norm_num [step01OddPlusLower]

private theorem step01OddCleanLower_le (c d : ℝ) :
    step01OddCleanLower c d ≤
      yoshidaEndpointOddLowGram11 * c ^ 2 +
        2 * yoshidaEndpointOddLowGram13 * c * d +
          yoshidaEndpointOddLowGram33 * d ^ 2 := by
  have h := oddClean_rationalGram_le c d
  rw [yoshidaEndpointOddLowGram_quadratic] at h
  simpa only [step01OddCleanLower] using h

private theorem step01OddPlusLower_le (c d : ℝ) :
    step01OddPlusLower c d ≤
      factorTwoIntrinsicOddPhaseQuadratic 1 c d := by
  have hclean := step01OddCleanLower_le c d
  have hpert := oddPerturbationLoewner_quadratic_le c d
  rw [factorTwoCenteredSymmetricPerturbation_oddStructuralLow] at hpert
  unfold step01OddPlusLower at ⊢
  unfold step01OddCleanLower at hclean
  unfold factorTwoIntrinsicOddPhaseQuadratic factorTwoIntrinsicOddPhaseLow11
    factorTwoIntrinsicOddPhaseLow13 factorTwoIntrinsicOddPhaseLow33
    at ⊢
  unfold oddPerturbationLoewner11 oddPerturbationLoewner13
    oddPerturbationLoewner33 at hpert
  norm_num at hclean hpert ⊢
  linarith

/-- The quantitative determinant slope transports the two global odd
Loewner lower forms to the exact Step01 odd budget. -/
theorem step01OddBudgetLower_le
    (hslope : (23 / 5 : ℝ) ≤ factorTwoIntrinsicStep01Slope)
    (c d : ℝ) :
    step01OddBudgetLower c d ≤
      factorTwoIntrinsicStep01ExactOddBudget c d := by
  let C : ℝ := step01OddCleanLower c d
  let O : ℝ := step01OddPlusLower c d
  let Cexact : ℝ :=
    yoshidaEndpointOddLowGram11 * c ^ 2 +
      2 * yoshidaEndpointOddLowGram13 * c * d +
        yoshidaEndpointOddLowGram33 * d ^ 2
  let Oexact : ℝ := factorTwoIntrinsicOddPhaseQuadratic 1 c d
  have hC : C ≤ Cexact := by
    simpa only [C, Cexact] using step01OddCleanLower_le c d
  have hO : O ≤ Oexact := by
    simpa only [O, Oexact] using step01OddPlusLower_le c d
  have hO0 : 0 ≤ O := by
    simpa only [O] using step01OddPlusLower_nonneg c d
  have hOexact0 : 0 ≤ Oexact := hO0.trans hO
  have hscaledC : 2 * C ≤ 2 * Cexact := by linarith
  have hscaledO : (13 / 5 : ℝ) * O ≤
      (factorTwoIntrinsicStep01Slope - 2) * Oexact := by
    have hfirst : (13 / 5 : ℝ) * O ≤ (13 / 5 : ℝ) * Oexact := by
      exact mul_le_mul_of_nonneg_left hO (by norm_num)
    have hsecond : (13 / 5 : ℝ) * Oexact ≤
        (factorTwoIntrinsicStep01Slope - 2) * Oexact := by
      exact mul_le_mul_of_nonneg_right (by linarith) hOexact0
    exact hfirst.trans hsecond
  have hbudgetIdentity :
      factorTwoIntrinsicStep01ExactOddBudget c d =
        2 * Cexact +
          (factorTwoIntrinsicStep01Slope - 2) * Oexact := by
    dsimp only [Cexact, Oexact]
    unfold factorTwoIntrinsicStep01ExactOddBudget
      factorTwoIntrinsicStep01Slope
      factorTwoIntrinsicOddDirectionQuadratic
      factorTwoIntrinsicOddPhaseQuadratic factorTwoIntrinsicOddPhaseLow11
      factorTwoIntrinsicOddPhaseLow13 factorTwoIntrinsicOddPhaseLow33
    field_simp [ne_of_gt factorTwoIntrinsicEvenDetCoefficient0_pos]
    ring
  rw [hbudgetIdentity]
  have hlowerIdentity : step01OddBudgetLower c d =
      2 * C + (13 / 5 : ℝ) * O := by
    dsimp only [C, O]
    unfold step01OddBudgetLower step01OddBudgetLower11
      step01OddBudgetLower13 step01OddBudgetLower33
      step01OddCleanLower step01OddPlusLower
    ring
  rw [hlowerIdentity]
  linarith

private def step01EvenLowerDet : ℝ :=
  step01EvenLower00 * step01EvenLower22 - step01EvenLower02 ^ 2

private def step01AlternatingAdj11 (s₁ d₁ : ℝ) : ℝ :=
  ((step01EvenLower00 + step01EvenLower22 - 2 * step01EvenLower02) * s₁ ^ 2 +
      (step01EvenLower00 + step01EvenLower22 + 2 * step01EvenLower02) * d₁ ^ 2 +
      2 * (step01EvenLower22 - step01EvenLower00) * s₁ * d₁) / 4

private def step01AlternatingAdj13 (s₁ d₁ s₃ d₃ : ℝ) : ℝ :=
  ((step01EvenLower00 + step01EvenLower22 - 2 * step01EvenLower02) * s₁ * s₃ +
      (step01EvenLower00 + step01EvenLower22 + 2 * step01EvenLower02) * d₁ * d₃ +
      (step01EvenLower22 - step01EvenLower00) *
        (s₁ * d₃ + d₁ * s₃)) / 4

private def step01AlternatingAdj33 (s₃ d₃ : ℝ) : ℝ :=
  ((step01EvenLower00 + step01EvenLower22 - 2 * step01EvenLower02) * s₃ ^ 2 +
      (step01EvenLower00 + step01EvenLower22 + 2 * step01EvenLower02) * d₃ ^ 2 +
      2 * (step01EvenLower22 - step01EvenLower00) * s₃ * d₃) / 4

private def step01RationalResidual11 (s₁ d₁ : ℝ) : ℝ :=
  step01EvenLowerDet * step01OddBudgetLower11 -
    step01AlternatingAdj11 s₁ d₁

private def step01RationalResidual13 (s₁ d₁ s₃ d₃ : ℝ) : ℝ :=
  step01EvenLowerDet * step01OddBudgetLower13 -
    step01AlternatingAdj13 s₁ d₁ s₃ d₃

private def step01RationalResidual33 (s₃ d₃ : ℝ) : ℝ :=
  step01EvenLowerDet * step01OddBudgetLower33 -
    step01AlternatingAdj33 s₃ d₃

private def step01RationalResidualDet (s₁ d₁ s₃ d₃ : ℝ) : ℝ :=
  step01RationalResidual11 s₁ d₁ * step01RationalResidual33 s₃ d₃ -
    step01RationalResidual13 s₁ d₁ s₃ d₃ ^ 2

private theorem step01AlternatingAdj11_eq
    (j01 j21 : ℝ) :
    step01AlternatingAdj11 (j01 + j21) (j01 - j21) =
      step01EvenLower22 * j01 ^ 2 -
        2 * step01EvenLower02 * j01 * j21 +
          step01EvenLower00 * j21 ^ 2 := by
  rw [adjugateQuadratic_eq_sum_difference]
  rfl

private theorem step01AlternatingAdj13_eq
    (j01 j21 j03 j23 : ℝ) :
    step01AlternatingAdj13 (j01 + j21) (j01 - j21)
        (j03 + j23) (j03 - j23) =
      step01EvenLower22 * j01 * j03 -
        step01EvenLower02 * (j01 * j23 + j21 * j03) +
          step01EvenLower00 * j21 * j23 := by
  rw [adjugateBilinear_eq_sum_difference]
  rfl

private theorem step01AlternatingAdj33_eq
    (j03 j23 : ℝ) :
    step01AlternatingAdj33 (j03 + j23) (j03 - j23) =
      step01EvenLower22 * j03 ^ 2 -
        2 * step01EvenLower02 * j03 * j23 +
          step01EvenLower00 * j23 ^ 2 := by
  rw [adjugateQuadratic_eq_sum_difference]
  rfl

private theorem step01RationalResidual_gates_of_sum_difference_bounds
    (s₁ d₁ s₃ d₃ : ℝ)
    (hs₁L : (56168 / 100000 : ℝ) < s₁)
    (hs₁U : s₁ < (56173 / 100000 : ℝ))
    (hd₁L : (1687 / 100000 : ℝ) < d₁)
    (hd₁U : d₁ < (1692 / 100000 : ℝ))
    (hs₃L : (53815 / 100000 : ℝ) < s₃)
    (hs₃U : s₃ < (53836 / 100000 : ℝ))
    (hd₃L : (555 / 10000 : ℝ) < d₃)
    (hd₃U : d₃ < (279 / 5000 : ℝ)) :
    0 ≤ step01RationalResidual11 s₁ d₁ ∧
      0 ≤ step01RationalResidual33 s₃ d₃ ∧
      step01RationalResidual13 s₁ d₁ s₃ d₃ ^ 2 ≤
        step01RationalResidual11 s₁ d₁ *
          step01RationalResidual33 s₃ d₃ := by
  have hs₁pos : 0 < s₁ := (by norm_num : (0 : ℝ) < 56168 / 100000).trans hs₁L
  have hd₁pos : 0 < d₁ := (by norm_num : (0 : ℝ) < 1687 / 100000).trans hd₁L
  have hs₃pos : 0 < s₃ := (by norm_num : (0 : ℝ) < 53815 / 100000).trans hs₃L
  have hd₃pos : 0 < d₃ := (by norm_num : (0 : ℝ) < 555 / 10000).trans hd₃L
  have hs₁sqU : s₁ ^ 2 < (56173 / 100000 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ hs₁U hs₁pos.le (by norm_num)
  have hd₁sqU : d₁ ^ 2 < (1692 / 100000 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ hd₁U hd₁pos.le (by norm_num)
  have hs₃sqU : s₃ ^ 2 < (53836 / 100000 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ hs₃U hs₃pos.le (by norm_num)
  have hd₃sqU : d₃ ^ 2 < (279 / 5000 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ hd₃U hd₃pos.le (by norm_num)
  have hs₁d₁L :
      (56168 / 100000 : ℝ) * (1687 / 100000) < s₁ * d₁ := by
    calc
      (56168 / 100000 : ℝ) * (1687 / 100000) <
          s₁ * (1687 / 100000) := mul_lt_mul_of_pos_right hs₁L (by norm_num)
      _ < s₁ * d₁ := mul_lt_mul_of_pos_left hd₁L hs₁pos
  have hs₃d₃L :
      (53815 / 100000 : ℝ) * (555 / 10000) < s₃ * d₃ := by
    calc
      (53815 / 100000 : ℝ) * (555 / 10000) <
          s₃ * (555 / 10000) := mul_lt_mul_of_pos_right hs₃L (by norm_num)
      _ < s₃ * d₃ := mul_lt_mul_of_pos_left hd₃L hs₃pos
  have hs₁s₃L :
      (56168 / 100000 : ℝ) * (53815 / 100000) < s₁ * s₃ := by
    calc
      (56168 / 100000 : ℝ) * (53815 / 100000) <
          s₁ * (53815 / 100000) := mul_lt_mul_of_pos_right hs₁L (by norm_num)
      _ < s₁ * s₃ := mul_lt_mul_of_pos_left hs₃L hs₁pos
  have hs₁s₃U :
      s₁ * s₃ < (56173 / 100000 : ℝ) * (53836 / 100000) := by
    calc
      s₁ * s₃ < (56173 / 100000 : ℝ) * s₃ :=
        mul_lt_mul_of_pos_right hs₁U hs₃pos
      _ < (56173 / 100000 : ℝ) * (53836 / 100000) :=
        mul_lt_mul_of_pos_left hs₃U (by norm_num)
  have hd₁d₃L :
      (1687 / 100000 : ℝ) * (555 / 10000) < d₁ * d₃ := by
    calc
      (1687 / 100000 : ℝ) * (555 / 10000) <
          d₁ * (555 / 10000) := mul_lt_mul_of_pos_right hd₁L (by norm_num)
      _ < d₁ * d₃ := mul_lt_mul_of_pos_left hd₃L hd₁pos
  have hd₁d₃U :
      d₁ * d₃ < (1692 / 100000 : ℝ) * (279 / 5000) := by
    calc
      d₁ * d₃ < (1692 / 100000 : ℝ) * d₃ :=
        mul_lt_mul_of_pos_right hd₁U hd₃pos
      _ < (1692 / 100000 : ℝ) * (279 / 5000) :=
        mul_lt_mul_of_pos_left hd₃U (by norm_num)
  have hs₁d₃L :
      (56168 / 100000 : ℝ) * (555 / 10000) < s₁ * d₃ := by
    calc
      (56168 / 100000 : ℝ) * (555 / 10000) <
          s₁ * (555 / 10000) := mul_lt_mul_of_pos_right hs₁L (by norm_num)
      _ < s₁ * d₃ := mul_lt_mul_of_pos_left hd₃L hs₁pos
  have hs₁d₃U :
      s₁ * d₃ < (56173 / 100000 : ℝ) * (279 / 5000) := by
    calc
      s₁ * d₃ < (56173 / 100000 : ℝ) * d₃ :=
        mul_lt_mul_of_pos_right hs₁U hd₃pos
      _ < (56173 / 100000 : ℝ) * (279 / 5000) :=
        mul_lt_mul_of_pos_left hd₃U (by norm_num)
  have hd₁s₃L :
      (1687 / 100000 : ℝ) * (53815 / 100000) < d₁ * s₃ := by
    calc
      (1687 / 100000 : ℝ) * (53815 / 100000) <
          d₁ * (53815 / 100000) := mul_lt_mul_of_pos_right hd₁L (by norm_num)
      _ < d₁ * s₃ := mul_lt_mul_of_pos_left hs₃L hd₁pos
  have hd₁s₃U :
      d₁ * s₃ < (1692 / 100000 : ℝ) * (53836 / 100000) := by
    calc
      d₁ * s₃ < (1692 / 100000 : ℝ) * s₃ :=
        mul_lt_mul_of_pos_right hd₁U hs₃pos
      _ < (1692 / 100000 : ℝ) * (53836 / 100000) :=
        mul_lt_mul_of_pos_left hs₃U (by norm_num)
  have hA11U : step01AlternatingAdj11 s₁ d₁ < (484 / 1000000 : ℝ) := by
    unfold step01AlternatingAdj11 step01EvenLower00 step01EvenLower02
      step01EvenLower22
    norm_num at hs₁sqU hd₁sqU hs₁d₁L ⊢
    linarith only [hs₁sqU, hd₁sqU, hs₁d₁L]
  have hA33U : step01AlternatingAdj33 s₃ d₃ < (832 / 1000000 : ℝ) := by
    unfold step01AlternatingAdj33 step01EvenLower00 step01EvenLower02
      step01EvenLower22
    norm_num at hs₃sqU hd₃sqU hs₃d₃L ⊢
    linarith only [hs₃sqU, hd₃sqU, hs₃d₃L]
  have hA13L : (552 / 1000000 : ℝ) <
      step01AlternatingAdj13 s₁ d₁ s₃ d₃ := by
    unfold step01AlternatingAdj13 step01EvenLower00 step01EvenLower02
      step01EvenLower22
    norm_num at hs₁s₃L hd₁d₃L hs₁d₃U hd₁s₃U ⊢
    linarith only [hs₁s₃L, hd₁d₃L, hs₁d₃U, hd₁s₃U]
  have hA13U : step01AlternatingAdj13 s₁ d₁ s₃ d₃ <
      (554 / 1000000 : ℝ) := by
    unfold step01AlternatingAdj13 step01EvenLower00 step01EvenLower02
      step01EvenLower22
    norm_num at hs₁s₃U hd₁d₃U hs₁d₃L hd₁s₃L ⊢
    linarith only [hs₁s₃U, hd₁d₃U, hs₁d₃L, hd₁s₃L]
  have hr11 : (1802 / 10000000 : ℝ) < step01RationalResidual11 s₁ d₁ := by
    unfold step01RationalResidual11 step01EvenLowerDet
      step01EvenLower00 step01EvenLower02 step01EvenLower22
      step01OddBudgetLower11
    norm_num at hA11U ⊢
    linarith only [hA11U]
  have hr33 : (1057 / 10000000 : ℝ) < step01RationalResidual33 s₃ d₃ := by
    unfold step01RationalResidual33 step01EvenLowerDet
      step01EvenLower00 step01EvenLower02 step01EvenLower22
      step01OddBudgetLower33
    norm_num at hA33U ⊢
    linarith only [hA33U]
  have hr13pos : 0 < step01RationalResidual13 s₁ d₁ s₃ d₃ := by
    unfold step01RationalResidual13 step01EvenLowerDet
      step01EvenLower00 step01EvenLower02 step01EvenLower22
      step01OddBudgetLower13
    norm_num at hA13U ⊢
    linarith only [hA13U]
  have hr13U : step01RationalResidual13 s₁ d₁ s₃ d₃ <
      (1379 / 10000000 : ℝ) := by
    unfold step01RationalResidual13 step01EvenLowerDet
      step01EvenLower00 step01EvenLower02 step01EvenLower22
      step01OddBudgetLower13
    norm_num at hA13L ⊢
    linarith only [hA13L]
  have hprod :
      (1802 / 10000000 : ℝ) * (1057 / 10000000) <
        step01RationalResidual11 s₁ d₁ *
          step01RationalResidual33 s₃ d₃ := by
    exact mul_lt_mul hr11 hr33.le (by norm_num) (by linarith [hr11])
  have hrsq : step01RationalResidual13 s₁ d₁ s₃ d₃ ^ 2 <
      (1379 / 10000000 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ hr13U hr13pos.le (by norm_num)
  have hrat : (1379 / 10000000 : ℝ) ^ 2 <
      (1802 / 10000000) * (1057 / 10000000) := by norm_num
  refine ⟨(by linarith [hr11]), (by linarith [hr33]), ?_⟩
  linarith only [hprod, hrsq, hrat]

/-- The four sharp sum/difference intervals imply one rational Cauchy
inequality.  The two alternating columns remain coupled through the full
`2 x 2` Schur residual. -/
theorem step01_rationalCauchy_of_alternatingSharpBounds
    (hJ : FactorTwoIntrinsicAlternatingSharpBounds) :
    ∀ u v c d : ℝ,
      factorTwoIntrinsicAlternatingBilinear u v c d ^ 2 ≤
        step01EvenLower u v * step01OddBudgetLower c d := by
  rcases hJ with ⟨hs₁L, hs₁U, hd₁L, hd₁U,
    hs₃L, hs₃U, hd₃L, hd₃U⟩
  let s₁ : ℝ := factorTwoIntrinsicAlternating01 +
    factorTwoIntrinsicAlternating21
  let d₁ : ℝ := factorTwoIntrinsicAlternating01 -
    factorTwoIntrinsicAlternating21
  let s₃ : ℝ := factorTwoIntrinsicAlternating03 +
    factorTwoIntrinsicAlternating23
  let d₃ : ℝ := factorTwoIntrinsicAlternating03 -
    factorTwoIntrinsicAlternating23
  have hgates := step01RationalResidual_gates_of_sum_difference_bounds
    s₁ d₁ s₃ d₃
    (by simpa only [s₁] using hs₁L) (by simpa only [s₁] using hs₁U)
    (by simpa only [d₁] using hd₁L) (by simpa only [d₁] using hd₁U)
    (by simpa only [s₃] using hs₃L) (by simpa only [s₃] using hs₃U)
    (by simpa only [d₃] using hd₃L) (by simpa only [d₃] using hd₃U)
  have hresidual : ∀ c d : ℝ,
      0 ≤ step01RationalResidual11 s₁ d₁ * c ^ 2 +
        2 * step01RationalResidual13 s₁ d₁ s₃ d₃ * c * d +
          step01RationalResidual33 s₃ d₃ * d ^ 2 :=
    (real_quadratic_pencil_nonneg_iff
      (step01RationalResidual11 s₁ d₁)
      (step01RationalResidual33 s₃ d₃)
      (step01RationalResidual13 s₁ d₁ s₃ d₃)).mpr hgates
  have hschur : ∀ c d : ℝ,
      0 ≤ 4 * step01EvenLowerDet *
          ((step01OddBudgetLower11 / 4) * c ^ 2 +
            2 * (step01OddBudgetLower13 / 4) * c * d +
              (step01OddBudgetLower33 / 4) * d ^ 2) -
        (step01EvenLower22 *
              (factorTwoIntrinsicAlternating01 * c +
                factorTwoIntrinsicAlternating03 * d) ^ 2 -
          2 * step01EvenLower02 *
              (factorTwoIntrinsicAlternating01 * c +
                factorTwoIntrinsicAlternating03 * d) *
              (factorTwoIntrinsicAlternating21 * c +
                factorTwoIntrinsicAlternating23 * d) +
          step01EvenLower00 *
              (factorTwoIntrinsicAlternating21 * c +
                factorTwoIntrinsicAlternating23 * d) ^ 2) := by
    intro c d
    have h := hresidual c d
    have hidentity :
        4 * step01EvenLowerDet *
            ((step01OddBudgetLower11 / 4) * c ^ 2 +
              2 * (step01OddBudgetLower13 / 4) * c * d +
                (step01OddBudgetLower33 / 4) * d ^ 2) -
          (step01EvenLower22 *
                (factorTwoIntrinsicAlternating01 * c +
                  factorTwoIntrinsicAlternating03 * d) ^ 2 -
            2 * step01EvenLower02 *
                (factorTwoIntrinsicAlternating01 * c +
                  factorTwoIntrinsicAlternating03 * d) *
                (factorTwoIntrinsicAlternating21 * c +
                  factorTwoIntrinsicAlternating23 * d) +
            step01EvenLower00 *
                (factorTwoIntrinsicAlternating21 * c +
                  factorTwoIntrinsicAlternating23 * d) ^ 2) =
          step01RationalResidual11 s₁ d₁ * c ^ 2 +
            2 * step01RationalResidual13 s₁ d₁ s₃ d₃ * c * d +
              step01RationalResidual33 s₃ d₃ * d ^ 2 := by
      unfold step01RationalResidual11 step01RationalResidual13
        step01RationalResidual33
      rw [step01AlternatingAdj11_eq,
        step01AlternatingAdj13_eq, step01AlternatingAdj33_eq]
      ring
    rw [hidentity]
    exact h
  have hcauchy := bilinear_sq_le_four_mul_of_schur
    step01EvenLower00 step01EvenLower02 step01EvenLower22
    (step01OddBudgetLower11 / 4) (step01OddBudgetLower13 / 4)
    (step01OddBudgetLower33 / 4)
    factorTwoIntrinsicAlternating01 factorTwoIntrinsicAlternating03
    factorTwoIntrinsicAlternating21 factorTwoIntrinsicAlternating23
    step01EvenLower_principal_minors_pos.1
    (by simpa only [step01EvenLowerDet] using
      step01EvenLower_principal_minors_pos.2)
    (by simpa only [step01EvenLowerDet] using hschur)
  intro u v c d
  have h := hcauchy u v c d
  unfold factorTwoIntrinsicAlternatingBilinear
    factorTwoIntrinsicAlternatingRow0 factorTwoIntrinsicAlternatingRow2
    step01EvenLower step01OddBudgetLower at ⊢
  simpa only [mul_div_assoc] using (by nlinarith [h] :
    (u * (factorTwoIntrinsicAlternating01 * c +
          factorTwoIntrinsicAlternating03 * d) +
        v * (factorTwoIntrinsicAlternating21 * c +
          factorTwoIntrinsicAlternating23 * d)) ^ 2 ≤
      (step01EvenLower00 * u ^ 2 +
        2 * step01EvenLower02 * u * v + step01EvenLower22 * v ^ 2) *
      (step01OddBudgetLower11 * c ^ 2 +
        2 * step01OddBudgetLower13 * c * d +
          step01OddBudgetLower33 * d ^ 2))

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowControlStep01CoupledResidualPositive

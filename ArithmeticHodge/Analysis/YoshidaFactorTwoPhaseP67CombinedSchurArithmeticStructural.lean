import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP67CombinedSchurArithmeticStructural

noncomputable section

/-!
# Square-root-free arithmetic for the combined `P6/P7` border

The analytic and forward-Hankel functionals occupy the same four Cartesian
cells.  This file contains only the reusable algebra needed to combine two
square bounds in one cell and then apply a four-row Schur estimate.  No
profile, mode, or kernel is inspected here.
-/

/-- Young's inequality in the exact form used to combine two functionals
which charge the same low/residual energy cell. -/
theorem sq_add_le_weighted_sq_add_sq
    (u v r : ℝ) (hr : 0 < r) :
    (u + v) ^ 2 ≤
      (1 + r) * u ^ 2 + (1 + 1 / r) * v ^ 2 := by
  rw [← sub_nonneg]
  have hid :
      (1 + r) * u ^ 2 + (1 + 1 / r) * v ^ 2 - (u + v) ^ 2 =
        (r * u - v) ^ 2 / r := by
    field_simp [hr.ne']
    ring
  rw [hid]
  positivity

/-- Two normalized square bounds in one cell combine with an arbitrary
positive Young parameter. -/
theorem sq_add_le_combined_cell
    (u v A F X r : ℝ)
    (hr : 0 < r)
    (hu : u ^ 2 ≤ A * X) (hv : v ^ 2 ≤ F * X) :
    (u + v) ^ 2 ≤
      ((1 + r) * A + (1 + 1 / r) * F) * X := by
  calc
    (u + v) ^ 2 ≤
        (1 + r) * u ^ 2 + (1 + 1 / r) * v ^ 2 :=
      sq_add_le_weighted_sq_add_sq u v r hr
    _ ≤ (1 + r) * (A * X) + (1 + 1 / r) * (F * X) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left hu (by positivity)
      · exact mul_le_mul_of_nonneg_left hv (by
          have : 0 < 1 / r := one_div_pos.mpr hr
          positivity)
    _ = ((1 + r) * A + (1 + 1 / r) * F) * X := by ring

/-- Generic square-root-free four-row Schur lemma which retains an arbitrary
total normalized budget.  In particular, strict slack in the sum of the four
row weights survives the Schur assembly instead of being rounded up to one. -/
theorem four_row_schur_of_normalized_sq_bounds_with_budget
    (B c₀₀ c₀₁ c₁₀ c₁₁ : ℝ)
    (z₀₀ z₀₁ z₁₀ z₁₁ x₀ x₁ y₀ y₁ : ℝ)
    (hc₀₀ : 0 < c₀₀) (hc₀₁ : 0 < c₀₁)
    (hc₁₀ : 0 < c₁₀) (hc₁₁ : 0 < c₁₁)
    (hbudget : c₀₀ + c₀₁ + c₁₀ + c₁₁ ≤ B)
    (hx₀ : 0 ≤ x₀) (hx₁ : 0 ≤ x₁)
    (hy₀ : 0 ≤ y₀) (hy₁ : 0 ≤ y₁)
    (hz₀₀ : z₀₀ ^ 2 ≤ c₀₀ * x₀ * y₀)
    (hz₀₁ : z₀₁ ^ 2 ≤ c₀₁ * x₀ * y₁)
    (hz₁₀ : z₁₀ ^ 2 ≤ c₁₀ * x₁ * y₀)
    (hz₁₁ : z₁₁ ^ 2 ≤ c₁₁ * x₁ * y₁) :
    (z₀₀ + z₀₁ + z₁₀ + z₁₁) ^ 2 ≤
      B * ((x₀ + x₁) * (y₀ + y₁)) := by
  have h₀₀ : z₀₀ ^ 2 / c₀₀ ≤ x₀ * y₀ := by
    apply (div_le_iff₀ hc₀₀).2
    nlinarith
  have h₀₁ : z₀₁ ^ 2 / c₀₁ ≤ x₀ * y₁ := by
    apply (div_le_iff₀ hc₀₁).2
    nlinarith
  have h₁₀ : z₁₀ ^ 2 / c₁₀ ≤ x₁ * y₀ := by
    apply (div_le_iff₀ hc₁₀).2
    nlinarith
  have h₁₁ : z₁₁ ^ 2 / c₁₁ ≤ x₁ * y₁ := by
    apply (div_le_iff₀ hc₁₁).2
    nlinarith
  have hidentity :
      (c₀₀ + c₀₁ + c₁₀ + c₁₁) *
          (z₀₀ ^ 2 / c₀₀ + z₀₁ ^ 2 / c₀₁ +
            z₁₀ ^ 2 / c₁₀ + z₁₁ ^ 2 / c₁₁) -
          (z₀₀ + z₀₁ + z₁₀ + z₁₁) ^ 2 =
        ((c₀₁ * z₀₀ - c₀₀ * z₀₁) ^ 2 / (c₀₀ * c₀₁) +
          ((c₁₀ * z₀₀ - c₀₀ * z₁₀) ^ 2 / (c₀₀ * c₁₀) +
          ((c₁₁ * z₀₀ - c₀₀ * z₁₁) ^ 2 / (c₀₀ * c₁₁) +
          ((c₁₀ * z₀₁ - c₀₁ * z₁₀) ^ 2 / (c₀₁ * c₁₀) +
          ((c₁₁ * z₀₁ - c₀₁ * z₁₁) ^ 2 / (c₀₁ * c₁₁) +
          (c₁₁ * z₁₀ - c₁₀ * z₁₁) ^ 2 / (c₁₀ * c₁₁)))))) := by
    field_simp [hc₀₀.ne', hc₀₁.ne', hc₁₀.ne', hc₁₁.ne']
    ring
  have hweighted :
      (z₀₀ + z₀₁ + z₁₀ + z₁₁) ^ 2 ≤
        (c₀₀ + c₀₁ + c₁₀ + c₁₁) *
          (z₀₀ ^ 2 / c₀₀ + z₀₁ ^ 2 / c₀₁ +
            z₁₀ ^ 2 / c₁₀ + z₁₁ ^ 2 / c₁₁) := by
    rw [← sub_nonneg, hidentity]
    positivity
  have hrows :
      z₀₀ ^ 2 / c₀₀ + z₀₁ ^ 2 / c₀₁ +
          z₁₀ ^ 2 / c₁₀ + z₁₁ ^ 2 / c₁₁ ≤
        x₀ * y₀ + x₀ * y₁ + x₁ * y₀ + x₁ * y₁ := by
    linarith
  have hpairs : 0 ≤ x₀ * y₀ + x₀ * y₁ + x₁ * y₀ + x₁ * y₁ := by
    positivity
  have hweightNonneg :
      0 ≤ c₀₀ + c₀₁ + c₁₀ + c₁₁ := by
    positivity
  calc
    (z₀₀ + z₀₁ + z₁₀ + z₁₁) ^ 2 ≤
        (c₀₀ + c₀₁ + c₁₀ + c₁₁) *
          (z₀₀ ^ 2 / c₀₀ + z₀₁ ^ 2 / c₀₁ +
            z₁₀ ^ 2 / c₁₀ + z₁₁ ^ 2 / c₁₁) := hweighted
    _ ≤ (c₀₀ + c₀₁ + c₁₀ + c₁₁) *
        (x₀ * y₀ + x₀ * y₁ + x₁ * y₀ + x₁ * y₁) :=
      mul_le_mul_of_nonneg_left hrows hweightNonneg
    _ ≤ B * (x₀ * y₀ + x₀ * y₁ + x₁ * y₀ + x₁ * y₁) :=
      mul_le_mul_of_nonneg_right hbudget hpairs
    _ = B * ((x₀ + x₁) * (y₀ + y₁)) := by ring

/-- Compatibility wrapper for the original unit-budget four-row Schur
lemma. -/
theorem four_row_schur_of_normalized_sq_bounds
    (c₀₀ c₀₁ c₁₀ c₁₁ : ℝ)
    (z₀₀ z₀₁ z₁₀ z₁₁ x₀ x₁ y₀ y₁ : ℝ)
    (hc₀₀ : 0 < c₀₀) (hc₀₁ : 0 < c₀₁)
    (hc₁₀ : 0 < c₁₀) (hc₁₁ : 0 < c₁₁)
    (hbudget : c₀₀ + c₀₁ + c₁₀ + c₁₁ ≤ 1)
    (hx₀ : 0 ≤ x₀) (hx₁ : 0 ≤ x₁)
    (hy₀ : 0 ≤ y₀) (hy₁ : 0 ≤ y₁)
    (hz₀₀ : z₀₀ ^ 2 ≤ c₀₀ * x₀ * y₀)
    (hz₀₁ : z₀₁ ^ 2 ≤ c₀₁ * x₀ * y₁)
    (hz₁₀ : z₁₀ ^ 2 ≤ c₁₀ * x₁ * y₀)
    (hz₁₁ : z₁₁ ^ 2 ≤ c₁₁ * x₁ * y₁) :
    (z₀₀ + z₀₁ + z₁₀ + z₁₁) ^ 2 ≤
      (x₀ + x₁) * (y₀ + y₁) := by
  simpa only [one_mul] using
    four_row_schur_of_normalized_sq_bounds_with_budget
      1 c₀₀ c₀₁ c₁₀ c₁₁
      z₀₀ z₀₁ z₁₀ z₁₁ x₀ x₁ y₀ y₁
      hc₀₀ hc₀₁ hc₁₀ hc₁₁ hbudget
      hx₀ hx₁ hy₀ hy₁ hz₀₀ hz₀₁ hz₁₀ hz₁₁

/-! ## Exact combined budget -/

def factorTwoP67AnalyticWeight₀₀ : ℝ := 9 / 2560
def factorTwoP67AnalyticWeight₀₁ : ℝ := 1 / 4
def factorTwoP67AnalyticWeight₁₀ : ℝ := 1 / 40
def factorTwoP67AnalyticWeight₁₁ : ℝ := 9 / 256

def factorTwoP67ForwardWeight₀₀ : ℝ := 8125 / 35831808
def factorTwoP67ForwardWeight₀₁ : ℝ := 40625 / 13716864
def factorTwoP67ForwardWeight₁₀ : ℝ := 1953125 / 146313216
def factorTwoP67ForwardWeight₁₁ : ℝ := 66015625 / 292626432

/-- Exact conversion of the `KP6` derivative envelope to the normalized
`P6`/even-residual cell. -/
theorem factorTwoP67ForwardWeight₀₀_normalization :
    (1 / 16 : ℝ) * (1 / 8778792960000000) * 14000 ^ 2 =
      factorTwoP67ForwardWeight₀₀ * (1 / 100) * (2 / 13) * (1 / 250) := by
  norm_num [factorTwoP67ForwardWeight₀₀]

/-- Exact conversion of the `LP6` derivative envelope to the normalized
`P6`/odd-residual cell. -/
theorem factorTwoP67ForwardWeight₀₁_normalization :
    (1 / 16 : ℝ) * (1 / 8778792960000000) * 16000 ^ 2 =
      factorTwoP67ForwardWeight₀₁ * (1 / 100) * (2 / 13) * (1 / 2500) := by
  norm_num [factorTwoP67ForwardWeight₀₁]

/-- Exact conversion of the `LP7` derivative envelope to the normalized
`P7`/even-residual cell. -/
theorem factorTwoP67ForwardWeight₁₀_normalization :
    (1 / 16 : ℝ) * (1 / 8778792960000000) * 100000 ^ 2 =
      factorTwoP67ForwardWeight₁₀ * (1 / 100) * (2 / 15) * (1 / 250) := by
  norm_num [factorTwoP67ForwardWeight₁₀]

/-- Exact conversion of the `KP7` derivative envelope to the normalized
`P7`/odd-residual cell. -/
theorem factorTwoP67ForwardWeight₁₁_normalization :
    (1 / 16 : ℝ) * (1 / 8778792960000000) * 130000 ^ 2 =
      factorTwoP67ForwardWeight₁₁ * (1 / 100) * (2 / 15) * (1 / 2500) := by
  norm_num [factorTwoP67ForwardWeight₁₁]

def factorTwoP67YoungParameter₀₀ : ℝ := 1 / 4
def factorTwoP67YoungParameter₀₁ : ℝ := 1 / 9
def factorTwoP67YoungParameter₁₀ : ℝ := 3 / 4
def factorTwoP67YoungParameter₁₁ : ℝ := 5 / 2

def factorTwoP67CombinedWeight₀₀ : ℝ := 198089 / 35831808
def factorTwoP67CombinedWeight₀₁ : ℝ := 2108245 / 6858432
def factorTwoP67CombinedWeight₁₀ : ℝ := 23482489 / 313528320
def factorTwoP67CombinedWeight₁₁ : ℝ := 18346949 / 41803776

theorem factorTwoP67CombinedWeight₀₀_eq_young :
    (1 + factorTwoP67YoungParameter₀₀) * factorTwoP67AnalyticWeight₀₀ +
        (1 + 1 / factorTwoP67YoungParameter₀₀) * factorTwoP67ForwardWeight₀₀ =
      factorTwoP67CombinedWeight₀₀ := by
  norm_num [factorTwoP67YoungParameter₀₀, factorTwoP67AnalyticWeight₀₀,
    factorTwoP67ForwardWeight₀₀, factorTwoP67CombinedWeight₀₀]

theorem factorTwoP67CombinedWeight₀₁_eq_young :
    (1 + factorTwoP67YoungParameter₀₁) * factorTwoP67AnalyticWeight₀₁ +
        (1 + 1 / factorTwoP67YoungParameter₀₁) * factorTwoP67ForwardWeight₀₁ =
      factorTwoP67CombinedWeight₀₁ := by
  norm_num [factorTwoP67YoungParameter₀₁, factorTwoP67AnalyticWeight₀₁,
    factorTwoP67ForwardWeight₀₁, factorTwoP67CombinedWeight₀₁]

theorem factorTwoP67CombinedWeight₁₀_eq_young :
    (1 + factorTwoP67YoungParameter₁₀) * factorTwoP67AnalyticWeight₁₀ +
        (1 + 1 / factorTwoP67YoungParameter₁₀) * factorTwoP67ForwardWeight₁₀ =
      factorTwoP67CombinedWeight₁₀ := by
  norm_num [factorTwoP67YoungParameter₁₀, factorTwoP67AnalyticWeight₁₀,
    factorTwoP67ForwardWeight₁₀, factorTwoP67CombinedWeight₁₀]

theorem factorTwoP67CombinedWeight₁₁_eq_young :
    (1 + factorTwoP67YoungParameter₁₁) * factorTwoP67AnalyticWeight₁₁ +
        (1 + 1 / factorTwoP67YoungParameter₁₁) * factorTwoP67ForwardWeight₁₁ =
      factorTwoP67CombinedWeight₁₁ := by
  norm_num [factorTwoP67YoungParameter₁₁, factorTwoP67AnalyticWeight₁₁,
    factorTwoP67ForwardWeight₁₁, factorTwoP67CombinedWeight₁₁]

/-- Exact sum of the four analytic-plus-forward normalized weights. -/
theorem factorTwoP67CombinedWeight_sum :
    factorTwoP67CombinedWeight₀₀ + factorTwoP67CombinedWeight₀₁ +
        factorTwoP67CombinedWeight₁₀ + factorTwoP67CombinedWeight₁₁ =
      (7257454387 / 8778792960 : ℝ) := by
  norm_num [factorTwoP67CombinedWeight₀₀, factorTwoP67CombinedWeight₀₁,
    factorTwoP67CombinedWeight₁₀, factorTwoP67CombinedWeight₁₁]

/-- The combined budget retains a simple strict margin below one. -/
theorem factorTwoP67CombinedWeight_sum_lt_five_six :
    factorTwoP67CombinedWeight₀₀ + factorTwoP67CombinedWeight₀₁ +
        factorTwoP67CombinedWeight₁₀ + factorTwoP67CombinedWeight₁₁ <
      (5 / 6 : ℝ) := by
  rw [factorTwoP67CombinedWeight_sum]
  norm_num

theorem factorTwoP67CombinedWeight_sum_le_one :
    factorTwoP67CombinedWeight₀₀ + factorTwoP67CombinedWeight₀₁ +
        factorTwoP67CombinedWeight₁₀ + factorTwoP67CombinedWeight₁₁ ≤
      (1 : ℝ) :=
  (factorTwoP67CombinedWeight_sum_lt_five_six.trans_le (by norm_num)).le

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP67CombinedSchurArithmeticStructural

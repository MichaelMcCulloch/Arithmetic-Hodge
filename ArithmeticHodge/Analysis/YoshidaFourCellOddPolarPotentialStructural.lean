import ArithmeticHodge.Analysis.YoshidaConstantBounds
import ArithmeticHodge.Analysis.YoshidaEndpointPotentialIntegrable
import ArithmeticHodge.Analysis.YoshidaEndpointWeightedCauchy
import ArithmeticHodge.Analysis.YoshidaFourCellParityOperatorStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddPolarPotentialStructural

noncomputable section

open YoshidaConstantBounds
open YoshidaEndpointPotentialBound
open YoshidaEndpointPotentialIntegrable
open YoshidaEndpointWeightedCauchy
open YoshidaFourCellParityHalfFoldStructural
open YoshidaFourCellParityOperatorStructural

/-!
# Potential absorption of the odd four-cell polar rank

At the four-cell halfwidth the odd `sinh` representer is pointwise smaller
than one third of the centered coordinate.  The endpoint potential controls
the square of that coordinate, so weighted Cauchy charges the complete
negative odd polar rank to less than half of the folded potential term.
-/

theorem fourCellOperatorHalfWidth_lt_one_half :
    fourCellOperatorHalfWidth < (1 / 2 : ℝ) := by
  have hlog := strict_log_two_bounds.2
  unfold fourCellOperatorHalfWidth
  nlinarith

private theorem sinh_le_mul_exp_self {z : ℝ} :
    Real.sinh z ≤ z * Real.exp z := by
  have hbase := Real.add_one_le_exp (-2 * z)
  have hmul := mul_le_mul_of_nonneg_left hbase (Real.exp_pos z).le
  have hprod : Real.exp z * (1 - 2 * z) ≤ Real.exp (-z) := by
    calc
      Real.exp z * (1 - 2 * z) = Real.exp z * (-2 * z + 1) := by ring
      _ ≤ Real.exp z * Real.exp (-2 * z) := hmul
      _ = Real.exp (-z) := by
        rw [← Real.exp_add]
        congr 1
        ring
  rw [Real.sinh_eq]
  nlinarith [Real.exp_pos z]

/-- The positive-half odd hyperbolic representer is bounded by `x / 3`. -/
theorem fourCell_sinh_weight_le_third
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.sinh (fourCellOperatorHalfWidth * x / 2) ≤ x / 3 := by
  let z := fourCellOperatorHalfWidth * x / 2
  have ha0 : 0 ≤ fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  have hz0 : 0 ≤ z := by
    dsimp only [z]
    positivity
  have hzQuarter : z ≤ x / 4 := by
    dsimp only [z]
    nlinarith [fourCellOperatorHalfWidth_lt_one_half]
  have hzOne : z < 1 := lt_of_le_of_lt hzQuarter (by nlinarith)
  have hexp := Real.exp_bound_div_one_sub_of_interval hz0 hzOne
  have hden : 1 / (1 - z) ≤ (4 / 3 : ℝ) := by
    rw [div_le_iff₀ (by linarith : 0 < 1 - z)]
    nlinarith
  have hexpFourThirds : Real.exp z ≤ (4 / 3 : ℝ) := hexp.trans hden
  have hsinh := sinh_le_mul_exp_self (z := z)
  calc
    Real.sinh z ≤ z * Real.exp z := hsinh
    _ ≤ z * (4 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_left hexpFourThirds hz0
    _ ≤ (x / 4) * (4 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_right hzQuarter (by norm_num)
    _ = x / 3 := by ring

private theorem fourCell_sinh_sq_le_two_ninths_endpointPotential
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    Real.sinh (fourCellOperatorHalfWidth * x / 2) ^ 2 ≤
      (2 / 9 : ℝ) * yoshidaEndpointPotential x := by
  have hsinh0 : 0 ≤ Real.sinh (fourCellOperatorHalfWidth * x / 2) := by
    rw [Real.sinh_nonneg_iff]
    have ha0 : 0 ≤ fourCellOperatorHalfWidth := by
      unfold fourCellOperatorHalfWidth
      positivity
    exact div_nonneg (mul_nonneg ha0 hx.1.le) (by norm_num)
  have hsinh := fourCell_sinh_weight_le_third hx.1.le hx.2.le
  have hsinhSq :
      Real.sinh (fourCellOperatorHalfWidth * x / 2) ^ 2 ≤ (x / 3) ^ 2 :=
    (sq_le_sq₀ hsinh0 (div_nonneg hx.1.le (by norm_num))).2 hsinh
  have hquartic := quartic_le_endpointPotential
    (show |x| < 1 by rw [abs_lt]; constructor <;> linarith [hx.1, hx.2])
  unfold yoshidaEndpointQuartic at hquartic
  nlinarith [sq_nonneg x, sq_nonneg (x ^ 2)]

private theorem sq_intervalIntegral_zero_one_le_integral_sq
    (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ x : ℝ in 0..1, f x) ^ 2 ≤ ∫ x : ℝ in 0..1, f x ^ 2 := by
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)
  have honeMeas : AEStronglyMeasurable (fun _x : ℝ ↦ (1 : ℝ)) μ := by
    fun_prop
  have hfMeas : AEStronglyMeasurable f μ :=
    hf.aestronglyMeasurable.restrict
  have honeLp : MemLp (fun _x : ℝ ↦ (1 : ℝ)) 2 μ := by
    rw [memLp_two_iff_integrable_sq_norm honeMeas]
    have hcompact : IntegrableOn (fun _x : ℝ ↦ ‖(1 : ℝ)‖ ^ 2)
        (Icc (0 : ℝ) 1) :=
      (by fun_prop : Continuous (fun _x : ℝ ↦ ‖(1 : ℝ)‖ ^ 2))
        |>.continuousOn.integrableOn_compact isCompact_Icc
    exact hcompact.mono_set Ioc_subset_Icc_self
  have hfLp : MemLp f 2 μ := by
    rw [memLp_two_iff_integrable_sq_norm hfMeas]
    have hcompact : IntegrableOn (fun x : ℝ ↦ ‖f x‖ ^ 2)
        (Icc (0 : ℝ) 1) :=
      (hf.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
    exact hcompact.mono_set Ioc_subset_Icc_self
  have h := sq_integral_mul_le_weighted μ
    (fun _x : ℝ ↦ (1 : ℝ)) (fun _x : ℝ ↦ (1 : ℝ)) f
    (by simp) (by simpa using honeLp) (by simpa using hfLp)
  repeat rw [intervalIntegral.integral_of_le (by norm_num)]
  simpa [μ] using h

/-- Squared odd `sinh` weight, including the profile, is charged pointwise
to `2 / 9` of the positive-half endpoint potential. -/
theorem integral_fourCell_sinh_sq_mul_le_two_ninths_potential
    (w : ℝ → ℝ) (hw : Continuous w) :
    (∫ x : ℝ in 0..1,
        (Real.sinh (fourCellOperatorHalfWidth * x / 2) * w x) ^ 2) ≤
      (2 / 9 : ℝ) *
        ∫ x : ℝ in 0..1, yoshidaEndpointPotential x * w x ^ 2 := by
  have hleft : IntervalIntegrable
      (fun x : ℝ ↦
        (Real.sinh (fourCellOperatorHalfWidth * x / 2) * w x) ^ 2)
      volume 0 1 := by
    exact (by fun_prop : Continuous (fun x : ℝ ↦
      (Real.sinh (fourCellOperatorHalfWidth * x / 2) * w x) ^ 2))
        |>.intervalIntegrable _ _
  have hpotentialFull := intervalIntegrable_endpointPotential_mul_sq w hw
  have hpotential : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * w x ^ 2)
      volume 0 1 := hpotentialFull.mono_set (by
    intro x hx
    norm_num at hx ⊢
    constructor <;> linarith : uIcc (0 : ℝ) 1 ⊆ uIcc (-1 : ℝ) 1)
  have hright : IntervalIntegrable
      (fun x : ℝ ↦ (2 / 9 : ℝ) *
        (yoshidaEndpointPotential x * w x ^ 2)) volume 0 1 :=
    hpotential.const_mul (2 / 9)
  have hmono :
      (∫ x : ℝ in 0..1,
        (Real.sinh (fourCellOperatorHalfWidth * x / 2) * w x) ^ 2) ≤
      ∫ x : ℝ in 0..1,
        (2 / 9 : ℝ) * (yoshidaEndpointPotential x * w x ^ 2) := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo
      (by norm_num) hleft hright
    intro x hx
    have hweight := fourCell_sinh_sq_le_two_ninths_endpointPotential hx
    have hmul := mul_le_mul_of_nonneg_right hweight (sq_nonneg (w x))
    calc
      (Real.sinh (fourCellOperatorHalfWidth * x / 2) * w x) ^ 2 =
          Real.sinh (fourCellOperatorHalfWidth * x / 2) ^ 2 * w x ^ 2 := by
            ring
      _ ≤ ((2 / 9 : ℝ) * yoshidaEndpointPotential x) * w x ^ 2 := hmul
      _ = (2 / 9 : ℝ) * (yoshidaEndpointPotential x * w x ^ 2) := by ring
  rw [intervalIntegral.integral_const_mul] at hmono
  exact hmono

/-- The complete negative odd polar rank costs at most `8 / 9` of one
positive-half endpoint-potential copy. -/
theorem eight_mul_fourCell_sinhMoment_sq_le_eight_ninths_potential
    (w : ℝ → ℝ) (hw : Continuous w) :
    8 * fourCellOperatorHalfWidth *
        fourCellPositiveSinhMoment w
          (fourCellOperatorHalfWidth / 2) ^ 2 ≤
      (8 / 9 : ℝ) *
        ∫ x : ℝ in 0..1, yoshidaEndpointPotential x * w x ^ 2 := by
  have hcauchy := sq_intervalIntegral_zero_one_le_integral_sq
    (fun x : ℝ ↦
      Real.sinh (fourCellOperatorHalfWidth * x / 2) * w x) (by fun_prop)
  have hweighted := integral_fourCell_sinh_sq_mul_le_two_ninths_potential w hw
  have hpotentialNonneg : 0 ≤
      ∫ x : ℝ in 0..1, yoshidaEndpointPotential x * w x ^ 2 := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro x hx
    have hV : 0 ≤ yoshidaEndpointPotential x := by
      by_cases hx1 : x = 1
      · simp [hx1, yoshidaEndpointPotential]
      · have hquartic := quartic_le_endpointPotential
          (show |x| < 1 by
            rw [abs_lt]
            constructor
            · linarith [hx.1]
            · exact lt_of_le_of_ne hx.2 hx1)
        exact (by
          unfold yoshidaEndpointQuartic at hquartic
          nlinarith [sq_nonneg x, sq_nonneg (x ^ 2)])
    exact mul_nonneg hV (sq_nonneg _)
  unfold fourCellPositiveSinhMoment at hcauchy ⊢
  have ha0 : 0 ≤ fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  calc
    8 * fourCellOperatorHalfWidth *
        (∫ x : ℝ in 0..1,
          Real.sinh (fourCellOperatorHalfWidth / 2 * x) * w x) ^ 2 ≤
      8 * fourCellOperatorHalfWidth *
        (∫ x : ℝ in 0..1,
          (Real.sinh (fourCellOperatorHalfWidth * x / 2) * w x) ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            convert hcauchy using 1
            all_goals ring
    _ ≤ 8 * fourCellOperatorHalfWidth *
        ((2 / 9 : ℝ) *
          ∫ x : ℝ in 0..1, yoshidaEndpointPotential x * w x ^ 2) :=
      mul_le_mul_of_nonneg_left hweighted (by positivity)
    _ ≤ (8 / 9 : ℝ) *
        ∫ x : ℝ in 0..1, yoshidaEndpointPotential x * w x ^ 2 := by
      have ha : 8 * fourCellOperatorHalfWidth ≤ 4 := by
        nlinarith [fourCellOperatorHalfWidth_lt_one_half]
      nlinarith

/-- After absorbing the odd polar loss, the two folded potential copies
retain at least `10 / 9` of one positive-half potential energy. -/
theorem ten_ninths_potential_le_odd_potential_sub_polar
    (w : ℝ → ℝ) (hw : Continuous w) :
    (10 / 9 : ℝ) *
        (∫ x : ℝ in 0..1, yoshidaEndpointPotential x * w x ^ 2) ≤
      2 * (∫ x : ℝ in 0..1,
        yoshidaEndpointPotential x * w x ^ 2) -
        8 * fourCellOperatorHalfWidth *
          fourCellPositiveSinhMoment w
            (fourCellOperatorHalfWidth / 2) ^ 2 := by
  have h := eight_mul_fourCell_sinhMoment_sq_le_eight_ninths_potential w hw
  linarith

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddPolarPotentialStructural

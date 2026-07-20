import ArithmeticHodge.Analysis.YoshidaEndpointWeightedCauchy
import ArithmeticHodge.Analysis.YoshidaFourCellOddP51GalerkinRieszStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP51TailBudgetAssemblyStructural

noncomputable section

open YoshidaEndpointWeightedCauchy
open YoshidaFourCellOddP51GalerkinRieszStructural
open YoshidaFourCellOddStripCapacityClosureStructural

/-!
# Two-budget assembly for the `P53+` residual row

The exact `q51` row is split into a finite main representer and a uniformly
small kernel error.  The constants below leave a strict rational reserve:

`17 / 16 * 9 / 10 + 17 * 1 / 1000 = 3893 / 4000 < 1`.

This file is independent of how the two representers are evaluated.  It is
the exact assembly used by the degree-18 kernel replacement.
-/

/-- Weighted two-term square inequality with the constants chosen for the
degree-18 kernel split. -/
theorem add_sq_le_budget_of_main_and_error
    (x y budget : ℝ) (hbudget : 0 ≤ budget)
    (hmain : x ^ 2 ≤ (9 / 10 : ℝ) * budget)
    (herror : y ^ 2 ≤ (1 / 1000 : ℝ) * budget) :
    (x + y) ^ 2 ≤ budget := by
  have hsplit : (x + y) ^ 2 ≤
      (17 / 16 : ℝ) * x ^ 2 + 17 * y ^ 2 := by
    nlinarith [sq_nonneg (x / 4 - 4 * y)]
  calc
    (x + y) ^ 2 ≤ (17 / 16 : ℝ) * x ^ 2 + 17 * y ^ 2 := hsplit
    _ ≤ (17 / 16 : ℝ) * ((9 / 10 : ℝ) * budget) +
        17 * ((1 / 1000 : ℝ) * budget) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hmain (by norm_num))
        (mul_le_mul_of_nonneg_left herror (by norm_num))
    _ = (3893 / 4000 : ℝ) * budget := by ring
    _ ≤ budget := by nlinarith

/-- Exact decomposition of the `q51` row into a main and an error pairing on
every genuine `P53+` tail. -/
def FourCellOddP51TailRowDecomposition
    (main error : ℝ → ℝ) : Prop :=
  ∀ (r : ℝ → ℝ), ContDiff ℝ 1 r → Function.Odd r →
    FourCellOddP53PlusMomentConditions r →
      fourCellOddCoreLocalBilinear fourCellOddQ51 r =
        (∫ x : ℝ in 0..1, main x * r x) +
          ∫ x : ℝ in 0..1, error x * r x

/-- A representer consumes at most the fraction `rho` of the complete P51
Schur budget on every genuine tail. -/
def FourCellOddP51TailPairBudget
    (rho kappa : ℝ) (F : ℝ → ℝ) : Prop :=
  ∀ (r : ℝ → ℝ), ContDiff ℝ 1 r → Function.Odd r →
    FourCellOddP53PlusMomentConditions r →
      (∫ x : ℝ in 0..1, F x * r x) ^ 2 ≤
        rho * (fourCellOddP51GalerkinPivot *
          (kappa * (∫ x : ℝ in 0..1, r x ^ 2)))

/-- The `9/10` main budget and the `1/1000` kernel-error budget close the
complete P51 residual dual. -/
theorem fourCellOddP51GalerkinP53PlusResidualDual_of_tailBudgets
    (kappa : ℝ) (hkappa : 0 ≤ kappa)
    (hpivot : FourCellOddP51GalerkinPivotNonnegative)
    (main error : ℝ → ℝ)
    (hrow : FourCellOddP51TailRowDecomposition main error)
    (hmain : FourCellOddP51TailPairBudget (9 / 10) kappa main)
    (herror : FourCellOddP51TailPairBudget (1 / 1000) kappa error) :
    FourCellOddP51GalerkinP53PlusResidualDual kappa := by
  intro r hr hodd htail
  have hmass : 0 ≤ ∫ x : ℝ in 0..1, r x ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num)
      (fun x _hx ↦ sq_nonneg (r x))
  have hbudget : 0 ≤ fourCellOddP51GalerkinPivot *
      (kappa * (∫ x : ℝ in 0..1, r x ^ 2)) :=
    mul_nonneg hpivot (mul_nonneg hkappa hmass)
  rw [hrow r hr hodd htail]
  exact add_sq_le_budget_of_main_and_error
    (∫ x : ℝ in 0..1, main x * r x)
    (∫ x : ℝ in 0..1, error x * r x)
    (fourCellOddP51GalerkinPivot *
      (kappa * (∫ x : ℝ in 0..1, r x ^ 2)))
    hbudget (hmain r hr hodd htail) (herror r hr hodd htail)

/-! ## Turning an `L²` error estimate into the error pairing budget -/

/-- Unweighted Cauchy--Schwarz on the positive half interval. -/
theorem sq_intervalIntegral_mul_le_zero_one
    (f r : ℝ → ℝ) (hf : Continuous f) (hr : Continuous r) :
    (∫ x : ℝ in 0..1, f x * r x) ^ 2 ≤
      (∫ x : ℝ in 0..1, f x ^ 2) *
        ∫ x : ℝ in 0..1, r x ^ 2 := by
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)
  have hfMeas : AEStronglyMeasurable f μ :=
    hf.aestronglyMeasurable.restrict
  have hrMeas : AEStronglyMeasurable r μ :=
    hr.aestronglyMeasurable.restrict
  have hfLp : MemLp f 2 μ := by
    rw [memLp_two_iff_integrable_sq_norm hfMeas]
    have hcompact : IntegrableOn (fun x : ℝ ↦ ‖f x‖ ^ 2)
        (Icc (0 : ℝ) 1) :=
      (hf.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
    exact hcompact.mono_set Ioc_subset_Icc_self
  have hrLp : MemLp r 2 μ := by
    rw [memLp_two_iff_integrable_sq_norm hrMeas]
    have hcompact : IntegrableOn (fun x : ℝ ↦ ‖r x‖ ^ 2)
        (Icc (0 : ℝ) 1) :=
      (hr.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
    exact hcompact.mono_set Ioc_subset_Icc_self
  have h := sq_integral_mul_le_weighted μ (fun _ : ℝ ↦ 1) f r
    (by simp) (by simpa using hfLp) (by simpa using hrLp)
  repeat rw [intervalIntegral.integral_of_le (by norm_num)]
  simpa only [μ, div_one, one_mul, Real.norm_eq_abs, sq_abs] using h

/-- A positive-half `L²` estimate for a continuous error representer
immediately gives its `1/1000` tail pairing budget. -/
theorem fourCellOddP51TailPairBudget_one_thousandth_of_l2
    (kappa : ℝ) (error : ℝ → ℝ) (herror : Continuous error)
    (hl2 : (∫ x : ℝ in 0..1, error x ^ 2) ≤
      (1 / 1000 : ℝ) *
        (fourCellOddP51GalerkinPivot * kappa)) :
    FourCellOddP51TailPairBudget (1 / 1000) kappa error := by
  intro r hr _hodd _htail
  have hcauchy := sq_intervalIntegral_mul_le_zero_one
    error r herror hr.continuous
  have hmass : 0 ≤ ∫ x : ℝ in 0..1, r x ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num)
      (fun x _hx ↦ sq_nonneg (r x))
  calc
    (∫ x : ℝ in 0..1, error x * r x) ^ 2 ≤
        (∫ x : ℝ in 0..1, error x ^ 2) *
          ∫ x : ℝ in 0..1, r x ^ 2 := hcauchy
    _ ≤ ((1 / 1000 : ℝ) *
        (fourCellOddP51GalerkinPivot * kappa)) *
          ∫ x : ℝ in 0..1, r x ^ 2 :=
      mul_le_mul_of_nonneg_right hl2 hmass
    _ = (1 / 1000 : ℝ) *
        (fourCellOddP51GalerkinPivot *
          (kappa * (∫ x : ℝ in 0..1, r x ^ 2))) := by ring

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP51TailBudgetAssemblyStructural

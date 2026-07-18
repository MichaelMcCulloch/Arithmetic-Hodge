import ArithmeticHodge.Analysis.MatrixPosSemidefTraceDominationStructural
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option autoImplicit false

open Matrix MeasureTheory Set
open scoped BigOperators Interval

namespace ArithmeticHodge.Analysis.FiniteIntervalWeightedGramTraceStructural

noncomputable section

/-- Interval weighted Gram for a finite family of real rows. -/
def finiteIntervalWeightedGram
    {ι : Type*} (a b : ℝ) (W : ℝ → ℝ) (F : ι → ℝ → ℝ) :
    Matrix ι ι ℝ := fun i j ↦
  ∫ x : ℝ in a..b, F i x * F j x / W x

/-- Diagonal row-energy integrand of an interval weighted Gram. -/
def finiteIntervalWeightedRowEnergy
    {ι : Type*} (W : ℝ → ℝ) (F : ι → ℝ → ℝ)
    (i : ι) (x : ℝ) : ℝ :=
  F i x ^ 2 / W x

/-- The trace of an interval weighted Gram is the finite sum of its row
energies. -/
theorem finiteIntervalWeightedGram_trace
    {ι : Type*} [Fintype ι]
    (a b : ℝ) (W : ℝ → ℝ) (F : ι → ℝ → ℝ) :
    (finiteIntervalWeightedGram a b W F).trace =
      ∑ i, ∫ x : ℝ in a..b, finiteIntervalWeightedRowEnergy W F i x := by
  simp [finiteIntervalWeightedGram, finiteIntervalWeightedRowEnergy,
    Matrix.trace, pow_two]

/-- When the individual row energies are integrable, their finite sum may be
moved inside the interval integral. -/
theorem finiteIntervalWeightedGram_trace_eq_integral_sum
    {ι : Type*} [Fintype ι]
    (a b : ℝ) (W : ℝ → ℝ) (F : ι → ℝ → ℝ)
    (hEnergy : ∀ i, IntervalIntegrable
      (finiteIntervalWeightedRowEnergy W F i) volume a b) :
    (finiteIntervalWeightedGram a b W F).trace =
      ∫ x : ℝ in a..b,
        ∑ i, finiteIntervalWeightedRowEnergy W F i x := by
  rw [finiteIntervalWeightedGram_trace]
  symm
  apply intervalIntegral.integral_finset_sum
  intro i _hi
  exact hEnergy i

/-- A single pointwise majorant for the sum of all row energies bounds the
trace, without estimating off-diagonal Gram entries. -/
theorem finiteIntervalWeightedGram_trace_le_integral_majorant
    {ι : Type*} [Fintype ι]
    (a b : ℝ) (hab : a ≤ b) (W : ℝ → ℝ) (F : ι → ℝ → ℝ)
    (majorant : ℝ → ℝ)
    (hEnergy : ∀ i, IntervalIntegrable
      (finiteIntervalWeightedRowEnergy W F i) volume a b)
    (hMajorant : IntervalIntegrable majorant volume a b)
    (hPoint : ∀ x ∈ Icc a b,
      ∑ i, finiteIntervalWeightedRowEnergy W F i x ≤ majorant x) :
    (finiteIntervalWeightedGram a b W F).trace ≤
      ∫ x : ℝ in a..b, majorant x := by
  rw [finiteIntervalWeightedGram_trace_eq_integral_sum a b W F hEnergy]
  apply intervalIntegral.integral_mono_on hab
  · have heq :
        (fun x ↦ ∑ i, finiteIntervalWeightedRowEnergy W F i x) =
          ∑ i, finiteIntervalWeightedRowEnergy W F i := by
          funext x
          rw [Finset.sum_apply]
    rw [heq]
    exact IntervalIntegrable.sum Finset.univ fun i _hi ↦ hEnergy i
  · exact hMajorant
  · exact hPoint

/-- A scalar bound for the majorant integral is a Loewner upper certificate
for the whole weighted Gram, provided the Gram is positive semidefinite. -/
theorem finiteIntervalWeightedGram_scalar_upper_of_majorant
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ℝ) (hab : a ≤ b) (W : ℝ → ℝ) (F : ι → ℝ → ℝ)
    (majorant : ℝ → ℝ) (gamma : ℝ)
    (hGram : (finiteIntervalWeightedGram a b W F).PosSemidef)
    (hEnergy : ∀ i, IntervalIntegrable
      (finiteIntervalWeightedRowEnergy W F i) volume a b)
    (hMajorant : IntervalIntegrable majorant volume a b)
    (hPoint : ∀ x ∈ Icc a b,
      ∑ i, finiteIntervalWeightedRowEnergy W F i x ≤ majorant x)
    (hIntegral : (∫ x : ℝ in a..b, majorant x) ≤ gamma) :
    (gamma • (1 : Matrix ι ι ℝ) -
      finiteIntervalWeightedGram a b W F).PosSemidef := by
  apply Matrix.PosSemidef.scalar_smul_one_sub_of_trace_le hGram
  exact (finiteIntervalWeightedGram_trace_le_integral_majorant
    a b hab W F majorant hEnergy hMajorant hPoint).trans hIntegral

end

end ArithmeticHodge.Analysis.FiniteIntervalWeightedGramTraceStructural

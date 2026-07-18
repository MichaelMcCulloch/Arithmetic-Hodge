import ArithmeticHodge.Analysis.FiniteIntervalWeightedGramTraceStructural

set_option autoImplicit false

open Matrix MeasureTheory Set
open scoped BigOperators

namespace ArithmeticHodge.Analysis.FiniteIntervalWeightedGramTraceInteriorStructural

open FiniteIntervalWeightedGramTraceStructural

noncomputable section

/-!
# Interior-point weighted Gram trace majorants

Endpoint logarithms in Lean use totalized conventions, so the sharp
reciprocal comparison is naturally stated only on the open interval.  Since
Lebesgue volume has no atoms, endpoint values do not affect the interval
integral.
-/

/-- An interior pointwise majorant bounds the trace of an interval weighted
Gram. -/
theorem finiteIntervalWeightedGram_trace_le_integral_majorant_of_le_Ioo
    {iota : Type*} [Fintype iota]
    (a b : Real) (hab : a ≤ b) (W : Real -> Real)
    (F : iota -> Real -> Real) (majorant : Real -> Real)
    (hEnergy : ∀ i, IntervalIntegrable
      (finiteIntervalWeightedRowEnergy W F i) volume a b)
    (hMajorant : IntervalIntegrable majorant volume a b)
    (hPoint : ∀ x ∈ Ioo a b,
      (∑ i, finiteIntervalWeightedRowEnergy W F i x) ≤ majorant x) :
    (finiteIntervalWeightedGram a b W F).trace ≤
      ∫ x : Real in a..b, majorant x := by
  rw [finiteIntervalWeightedGram_trace_eq_integral_sum a b W F hEnergy]
  apply intervalIntegral.integral_mono_on_of_le_Ioo hab
  · have hsum := IntervalIntegrable.sum Finset.univ fun i _hi => hEnergy i
    convert hsum using 1
    funext x
    simp only [Finset.sum_apply]
  · exact hMajorant
  · exact hPoint

/-- An interior scalar majorant gives the corresponding Loewner upper
certificate. -/
theorem finiteIntervalWeightedGram_scalar_upper_of_majorant_of_le_Ioo
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    (a b : Real) (hab : a ≤ b) (W : Real -> Real)
    (F : iota -> Real -> Real) (majorant : Real -> Real) (gamma : Real)
    (hGram : (finiteIntervalWeightedGram a b W F).PosSemidef)
    (hEnergy : ∀ i, IntervalIntegrable
      (finiteIntervalWeightedRowEnergy W F i) volume a b)
    (hMajorant : IntervalIntegrable majorant volume a b)
    (hPoint : ∀ x ∈ Ioo a b,
      (∑ i, finiteIntervalWeightedRowEnergy W F i x) ≤ majorant x)
    (hIntegral : (∫ x : Real in a..b, majorant x) ≤ gamma) :
    (gamma • (1 : Matrix iota iota Real) -
      finiteIntervalWeightedGram a b W F).PosSemidef := by
  apply Matrix.PosSemidef.scalar_smul_one_sub_of_trace_le hGram
  exact (finiteIntervalWeightedGram_trace_le_integral_majorant_of_le_Ioo
    a b hab W F majorant hEnergy hMajorant hPoint).trans hIntegral

end

end ArithmeticHodge.Analysis.FiniteIntervalWeightedGramTraceInteriorStructural

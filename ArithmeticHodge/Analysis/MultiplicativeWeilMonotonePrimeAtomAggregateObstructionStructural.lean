import ArithmeticHodge.Analysis.MultiplicativeWeilMonotonePrimeAtomAggregateStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneCutoffEnergyMonotonicityObstructionStructural

set_option autoImplicit false

open Complex Real

namespace ArithmeticHodge.Analysis.MultiplicativeWeilMonotonePrimeAtomAggregateObstructionStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilMonotoneCutoffEnergyMonotonicityObstructionStructural
open MultiplicativeWeilMonotonePrimeAtomAggregateStructural
open MultiplicativeWeilMonotoneQuarterPartitionStructural
open MultiplicativeWeilRealMonotonePropagationCriterionStructural

/-!
# The missing cross in aggregate prime Schur absorption

Write `H`, `I`, and `T` for the head, inner-suffix, and aggregate-slice
diagonals.  Write `C` for the head--aggregate cross and `D` for the true
head--suffix global cross.  The balance used by aggregate Schur absorption is

`B = H + I + 2 * (D + C)`.

The available inner positivity and ratio-two determinant constrain
`H, I, T, C`, but do not constrain `D`.  The scalar models below show that
neither the sign nor the determinant-scale condition on `B` follows from
those data, even when the other aggregate-Schur condition is retained.

The exact new coordinate for a genuine three-block argument is the real
suffix--aggregate cross `K`.  Pivoting through the aggregate slice then
isolates one residual contraction

`(T * D - C * K)^2 <= (H * T - C^2) * (I * T - K^2)`.
-/

/-- Scalar information supplied by inner-suffix positivity and the
ratio-two head--aggregate determinant. -/
def AggregateSchurBaseData (H I T C : ℝ) : Prop :=
  0 ≤ H ∧ 0 ≤ I ∧ 0 ≤ T ∧ C ^ 2 ≤ H * T

/-- The signed balance appearing in aggregate Schur absorption. -/
def aggregateSchurBalance (H I D C : ℝ) : ℝ :=
  H + I + 2 * (D + C)

/-- The actual outer cutoff value in scalar head--suffix coordinates. -/
def aggregateOuterValue (H I D : ℝ) : ℝ :=
  H + I + 2 * D

/-- The aggregate balance differs from the desired outer value by exactly
twice the already-controlled head--aggregate cross. -/
theorem aggregateSchurBalance_eq_outer_add_two_cross
    (H I D C : ℝ) :
    aggregateSchurBalance H I D C =
      aggregateOuterValue H I D + 2 * C := by
  unfold aggregateSchurBalance aggregateOuterValue
  ring

/-- Inner positivity, the ratio-two determinant, and even the nonnegative
aggregate balance do not imply its determinant-scale lower bound.  The
displayed model still has a strictly negative outer value. -/
theorem aggregateSchurBase_and_mean_allow_scale_failure :
    ∃ H I T C D : ℝ,
      AggregateSchurBaseData H I T C ∧
        0 ≤ aggregateSchurBalance H I D C ∧
        aggregateSchurBalance H I D C ^ 2 < 4 * H * T ∧
        aggregateOuterValue H I D < 0 := by
  refine ⟨1, 1, 1, 1, -(3 / 2), ?_⟩
  unfold AggregateSchurBaseData aggregateSchurBalance aggregateOuterValue
  norm_num

/-- Conversely, the squared determinant-scale condition does not select the
positive square-root branch.  It can hold while the aggregate balance and
the desired outer value are both strictly negative. -/
theorem aggregateSchurBase_and_scale_allow_mean_failure :
    ∃ H I T C D : ℝ,
      AggregateSchurBaseData H I T C ∧
        4 * H * T ≤ aggregateSchurBalance H I D C ^ 2 ∧
        aggregateSchurBalance H I D C < 0 ∧
        aggregateOuterValue H I D < 0 := by
  refine ⟨1, 1, 1, 0, -2, ?_⟩
  unfold AggregateSchurBaseData aggregateSchurBalance aggregateOuterValue
  norm_num

/-- The genuinely three-way residual contraction after pivoting through the
aggregate slice. -/
def AggregateThreeWayResidualContraction
    (H I T C K D : ℝ) : Prop :=
  (T * D - C * K) ^ 2 ≤
    (H * T - C ^ 2) * (I * T - K ^ 2)

/-- Once both aggregate-adjacent minors and the three-way residual
contraction are known, the outer head--suffix value is nonnegative.  This is
the exact additional Schur input; it is not a consequence of the four scalar
coordinates in `AggregateSchurBaseData`. -/
theorem aggregateOuterValue_nonnegative_of_threeWayResidual
    {H I T C K D : ℝ}
    (hT : 0 < T)
    (hheadAggregate : C ^ 2 ≤ H * T)
    (hinnerAggregate : K ^ 2 ≤ I * T)
    (hresidual : AggregateThreeWayResidualContraction H I T C K D) :
    0 ≤ aggregateOuterValue H I D := by
  let alpha : ℝ := H * T - C ^ 2
  let beta : ℝ := I * T - K ^ 2
  let delta : ℝ := T * D - C * K
  have halpha : 0 ≤ alpha := by
    dsimp only [alpha]
    linarith
  have hbeta : 0 ≤ beta := by
    dsimp only [beta]
    linarith
  have hdelta : delta ^ 2 ≤ alpha * beta := by
    simpa only [AggregateThreeWayResidualContraction,
      alpha, beta, delta] using hresidual
  have hschur : 0 ≤ alpha + beta + 2 * delta := by
    nlinarith [sq_nonneg (alpha - beta),
      sq_nonneg (alpha + beta + 2 * delta)]
  have hidentity :
      T * aggregateOuterValue H I D =
        (C + K) ^ 2 + alpha + beta + 2 * delta := by
    unfold aggregateOuterValue
    dsimp only [alpha, beta, delta]
    ring
  have hscaled : 0 ≤ T * aggregateOuterValue H I D := by
    rw [hidentity]
    nlinarith [sq_nonneg (C + K)]
  exact (mul_nonneg_iff_of_pos_left hT).mp hscaled

/-- The absent analytic coordinate: the real global cross between the actual
inner suffix and the coherently aggregated ratio-two slice. -/
def monotonePrimeAtomInnerSuffixAggregateCross
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ) : ℝ :=
  (bombieriTwoBlockGlobalCrossSymbol
    (monotoneQuarterCutoff parent (k + 1))
    (monotonePrimeAtomAggregateSlice parent k S)).re

/-- Actual head--suffix global cross, separated from its archimedean-minus-
prime expansion. -/
def monotonePrimeAtomHeadSuffixGlobalCross
    (parent : BombieriTest) (k : ℤ) : ℝ :=
  (bombieriTwoBlockGlobalCrossSymbol
    (monotoneQuarterCell parent k)
    (monotoneQuarterCutoff parent (k + 1))).re

/-- Concrete form of the three-way criterion.  The known ratio-two
head--aggregate determinant supplies one adjacent minor.  A suffix--aggregate
minor and the residual contraction involving its exact cross `K` then imply
nonnegativity of the outer cutoff. -/
theorem monotoneQuarterCutoff_nonnegative_of_primeAtom_aggregateThreeWayResidual
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ)
    (haggregate :
      0 < monotonePrimeAtomAggregateReserve parent k S)
    (hinnerAggregate :
      monotonePrimeAtomInnerSuffixAggregateCross parent k S ^ 2 ≤
        bombieriRealQuadraticValue
            (monotoneQuarterCutoff parent (k + 1)) *
          monotonePrimeAtomAggregateReserve parent k S)
    (hresidual :
      AggregateThreeWayResidualContraction
        (bombieriRealQuadraticValue (monotoneQuarterCell parent k))
        (bombieriRealQuadraticValue
          (monotoneQuarterCutoff parent (k + 1)))
        (monotonePrimeAtomAggregateReserve parent k S)
        (monotonePrimeAtomAggregateCross parent k S).re
        (monotonePrimeAtomInnerSuffixAggregateCross parent k S)
        (monotonePrimeAtomHeadSuffixGlobalCross parent k)) :
    0 ≤ bombieriRealQuadraticValue
      (monotoneQuarterCutoff parent k) := by
  let H : ℝ := bombieriRealQuadraticValue (monotoneQuarterCell parent k)
  let I : ℝ := bombieriRealQuadraticValue
    (monotoneQuarterCutoff parent (k + 1))
  let T : ℝ := monotonePrimeAtomAggregateReserve parent k S
  let C : ℝ := (monotonePrimeAtomAggregateCross parent k S).re
  let K : ℝ := monotonePrimeAtomInnerSuffixAggregateCross parent k S
  let D : ℝ := monotonePrimeAtomHeadSuffixGlobalCross parent k
  have hheadAggregate : C ^ 2 ≤ H * T := by
    have hdet := monotonePrimeAtom_aggregateCross_determinant parent k S
    have hre : C ^ 2 ≤
        Complex.normSq (monotonePrimeAtomAggregateCross parent k S) := by
      dsimp only [C]
      simp only [Complex.normSq_apply]
      nlinarith [sq_nonneg (monotonePrimeAtomAggregateCross parent k S).im]
    exact hre.trans (by simpa only [H, T] using hdet)
  have houter : 0 ≤ aggregateOuterValue H I D := by
    apply aggregateOuterValue_nonnegative_of_threeWayResidual
      (H := H) (I := I) (T := T) (C := C) (K := K) (D := D)
    · simpa only [T] using haggregate
    · exact hheadAggregate
    · simpa only [I, T, K] using hinnerAggregate
    · simpa only [H, I, T, C, K, D] using hresidual
  rw [monotoneQuarterCutoff_eq_cell_add_next]
  unfold bombieriRealQuadraticValue
  have hexpand := bombieriFunctional_twoBlock_re
    (monotoneQuarterCell parent k)
    (monotoneQuarterCutoff parent (k + 1)) (1 : ℂ)
  simp only [Complex.normSq_one, one_smul, one_mul] at hexpand
  rw [hexpand]
  simpa only [H, I, D, aggregateOuterValue,
    monotonePrimeAtomHeadSuffixGlobalCross] using houter

end

end ArithmeticHodge.Analysis.MultiplicativeWeilMonotonePrimeAtomAggregateObstructionStructural

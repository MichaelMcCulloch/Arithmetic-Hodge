import ArithmeticHodge.Analysis.MultiplicativeWeilMonotonePrimeAtomAggregateStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneCutoffEnergyMonotonicityObstructionStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilFourCellEnergyAbsorptionStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilSeparatedCellCrossStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellLocalCrossSignObstructionStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellCommonParentDeterminantStructural

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped Pointwise

namespace ArithmeticHodge.Analysis.MultiplicativeWeilMonotonePrimeAtomAggregateObstructionStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilFourCellEnergyAbsorptionStructural
open MultiplicativeWeilMinimalNegativeBlockStructural
open MultiplicativeWeilMinimalBlockEndpointEliminationStructural
open MultiplicativeWeilMonotoneCellEnergyFrameStructural
open MultiplicativeWeilMonotoneCutChebyshevFrontierStructural
open MultiplicativeWeilMonotoneCutoffEnergyMonotonicityObstructionStructural
open MultiplicativeWeilMonotoneNullSuffixVariationStructural
open MultiplicativeWeilMonotoneFourCellPrimeGeometryStructural
open MultiplicativeWeilMonotonePrimeAtomAbsorptionStructural
open MultiplicativeWeilMonotonePrimeAtomAggregateStructural
open MultiplicativeWeilMonotoneQuarterPartitionStructural
open MultiplicativeWeilMonotoneRatioTwoBlockPropagationStructural
open MultiplicativeWeilQuarterLogLatticePartitionStructural
open MultiplicativeWeilDirectedCorrelationPhysicalStructural
open MultiplicativeWeilDirectedCorrelationSmoothStructural
open MultiplicativeWeilMangoldtDiscrepancyAbelStructural
open MultiplicativeWeilRealCutPhaseReductionStructural
open MultiplicativeWeilRealLogKernelStructural
open MultiplicativeWeilRealMonotonePropagationCriterionStructural
open MultiplicativeWeilRealMonotonePropagationLogDefectStructural
open MultiplicativeWeilRealMonotoneTailConeCriterionStructural
open MultiplicativeWeilSeparatedCellCrossStructural
open MultiplicativeWeilFourCellMixedSignObstructionStructural
open MultiplicativeWeilFiveCellLocalCrossSignObstructionStructural
open MultiplicativeWeilAllLengthEndpointReserveStructural
open MultiplicativeWeilFiveCellCommonParentDeterminantStructural
open MultiplicativeWeilFiveCellMinimalBlockReserveStructural

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

/-! ## Why the suffix--aggregate pencil is not ratio two -/

/-- Above the aggregate plateau, adding any scalar multiple of the aggregate
slice leaves the entire original inner-suffix tail unchanged. -/
theorem innerSuffix_add_smul_aggregateSlice_apply_of_upper
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ) (c : ℂ)
    {x : ℝ} (hx : quarterLogLatticePoint (k + 3) ≤ x) :
    (monotoneQuarterCutoff parent (k + 1) +
        c • monotonePrimeAtomAggregateSlice parent k S) x =
      parent x := by
  have hinner : monotoneQuarterStep (k + 1) x = 1 := by
    apply monotoneQuarterStep_eq_one_of_le
    exact (quarterLogLatticePoint_mono (by omega)).trans hx
  have hlower : monotoneQuarterStep (k - 1) x = 1 := by
    apply monotoneQuarterStep_eq_one_of_le
    rw [show k - 1 + 1 = k by ring]
    exact (quarterLogLatticePoint_mono (by omega)).trans hx
  have hupper : monotoneQuarterStep (k + 2) x = 1 := by
    apply monotoneQuarterStep_eq_one_of_le
    simpa only [show k + 2 + 1 = k + 3 by ring] using hx
  simp only [TestFunction.coe_add, Pi.add_apply,
    TestFunction.coe_smul, Pi.smul_apply, smul_eq_mul,
    monotoneQuarterCutoff_apply, monotonePrimeAtomAggregateSlice,
    monotoneRatioTwoBlock_apply, monotoneRatioTwoBlockMultiplier]
  rw [hinner, show k - 1 + 3 = k + 2 by ring, hlower, hupper]
  norm_num

/-- In particular, a nonzero parent tail above the plateau prevents the
suffix--aggregate pencil from being the canonical ratio-two block of any
modified parent. -/
theorem innerSuffix_add_smul_aggregateSlice_ne_ratioTwoBlock_of_upper
    (parent modified : BombieriTest) (k : ℤ) (S : Finset ℕ) (c : ℂ)
    {x : ℝ} (hx : quarterLogLatticePoint (k + 3) ≤ x)
    (hparent : parent x ≠ 0) :
    monotoneRatioTwoBlock modified (k - 1) ≠
      monotoneQuarterCutoff parent (k + 1) +
        c • monotonePrimeAtomAggregateSlice parent k S := by
  have hlower : monotoneQuarterStep (k - 1) x = 1 := by
    apply monotoneQuarterStep_eq_one_of_le
    rw [show k - 1 + 1 = k by ring]
    exact (quarterLogLatticePoint_mono (by omega)).trans hx
  have hupper : monotoneQuarterStep (k + 2) x = 1 := by
    apply monotoneQuarterStep_eq_one_of_le
    simpa only [show k + 2 + 1 = k + 3 by ring] using hx
  intro heq
  have hpoint :
      monotoneRatioTwoBlock modified (k - 1) x =
        (monotoneQuarterCutoff parent (k + 1) +
          c • monotonePrimeAtomAggregateSlice parent k S) x :=
    congrArg (fun f : BombieriTest ↦ f x) heq
  rw [innerSuffix_add_smul_aggregateSlice_apply_of_upper
      parent k S c hx] at hpoint
  simp only [monotoneRatioTwoBlock_apply,
    monotoneRatioTwoBlockMultiplier,
    show k - 1 + 3 = k + 2 by ring, hlower, hupper,
    sub_self, Complex.ofReal_zero, zero_mul] at hpoint
  exact hparent hpoint.symm

private theorem not_ratioTwo_of_nonzero_at_factor_gt_two
    (f : BombieriTest) {x y : ℝ}
    (hxy : 2 * x < y)
    (hfx : f x ≠ 0) (hfy : f y ≠ 0) :
    ¬ BombieriRatioTwoCell f := by
  rintro ⟨a, b, ha, _hab, hsupport, hratio⟩
  have hxSupport : x ∈ tsupport f :=
    subset_tsupport f (Function.mem_support.mpr hfx)
  have hySupport : y ∈ tsupport f :=
    subset_tsupport f (Function.mem_support.mpr hfy)
  have hax : a ≤ x := (hsupport hxSupport).1
  have hyb : y ≤ b := (hsupport hySupport).2
  have hba : b ≤ 2 * a := by
    exact (div_le_iff₀ ha).mp hratio
  linarith

/-- More generally, whenever the pencil genuinely retains a lower aggregate
value and a suffix-tail value separated by a factor greater than two, it is
not any ratio-two Bombieri test. -/
theorem innerSuffix_add_smul_aggregateSlice_not_ratioTwo_of_separated_tail
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ) (c : ℂ)
    {x y : ℝ}
    (hxy : 2 * x < y)
    (hy : quarterLogLatticePoint (k + 3) ≤ y)
    (hleft :
      (monotoneQuarterCutoff parent (k + 1) +
        c • monotonePrimeAtomAggregateSlice parent k S) x ≠ 0)
    (htail : parent y ≠ 0) :
    ¬ BombieriRatioTwoCell
      (monotoneQuarterCutoff parent (k + 1) +
        c • monotonePrimeAtomAggregateSlice parent k S) := by
  apply not_ratioTwo_of_nonzero_at_factor_gt_two
    (f := monotoneQuarterCutoff parent (k + 1) +
      c • monotonePrimeAtomAggregateSlice parent k S)
    hxy hleft
  simpa only [innerSuffix_add_smul_aggregateSlice_apply_of_upper
    parent k S c hy] using htail

/-! ## Concrete aggregate-orthogonal residuals -/

/-- The head with its real aggregate component cleared. -/
def monotonePrimeAtomHeadAggregateOrthogonalResidual
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ) : BombieriTest :=
  let T := monotonePrimeAtomAggregateReserve parent k S
  let C := (monotonePrimeAtomAggregateCross parent k S).re
  (T : ℂ) • monotoneQuarterCell parent k +
    ((-C : ℝ) : ℂ) • monotonePrimeAtomAggregateSlice parent k S

/-- The inner suffix with its real aggregate component cleared. -/
def monotonePrimeAtomInnerAggregateOrthogonalResidual
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ) : BombieriTest :=
  let T := monotonePrimeAtomAggregateReserve parent k S
  let K := monotonePrimeAtomInnerSuffixAggregateCross parent k S
  (T : ℂ) • monotoneQuarterCutoff parent (k + 1) +
    ((-K : ℝ) : ℂ) • monotonePrimeAtomAggregateSlice parent k S

private theorem aggregateCross_real_smul_both_re
    (f g : BombieriTest) (a b : ℝ) :
    (bombieriTwoBlockGlobalCrossSymbol
      ((a : ℂ) • f) ((b : ℂ) • g)).re =
      a * b * (bombieriTwoBlockGlobalCrossSymbol f g).re := by
  rw [bombieriTwoBlockGlobalCrossSymbol_smul_left,
    bombieriTwoBlockGlobalCrossSymbol_smul_right]
  rw [show starRingEnd ℂ (a : ℂ) = (a : ℂ) by
    rw [starRingEnd_apply, Complex.star_def, Complex.conj_ofReal]]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  ring

private theorem aggregateCross_real_linearCombination_re
    (f g h i : BombieriTest) (a b c d : ℝ) :
    (bombieriTwoBlockGlobalCrossSymbol
      ((a : ℂ) • f + (b : ℂ) • g)
      ((c : ℂ) • h + (d : ℂ) • i)).re =
      a * c * (bombieriTwoBlockGlobalCrossSymbol f h).re +
        a * d * (bombieriTwoBlockGlobalCrossSymbol f i).re +
        b * c * (bombieriTwoBlockGlobalCrossSymbol g h).re +
        b * d * (bombieriTwoBlockGlobalCrossSymbol g i).re := by
  rw [bombieriTwoBlockGlobalCrossSymbol_add_left,
    bombieriTwoBlockGlobalCrossSymbol_add_right,
    bombieriTwoBlockGlobalCrossSymbol_add_right]
  simp only [Complex.add_re]
  rw [aggregateCross_real_smul_both_re,
    aggregateCross_real_smul_both_re,
    aggregateCross_real_smul_both_re,
    aggregateCross_real_smul_both_re]
  ring

private theorem aggregateQuadratic_real_linearCombination
    (f g : BombieriTest) (a b : ℝ) :
    bombieriRealQuadraticValue ((a : ℂ) • f + (b : ℂ) • g) =
      a ^ 2 * bombieriRealQuadraticValue f +
        b ^ 2 * bombieriRealQuadraticValue g +
        2 * a * b * (bombieriTwoBlockGlobalCrossSymbol f g).re := by
  have hswap := congrArg Complex.re
    (bombieriTwoBlockGlobalCrossSymbol_conj_swap f g)
  simp only [Complex.star_def, Complex.conj_re] at hswap
  unfold bombieriRealQuadraticValue
  rw [← bombieriTwoBlockGlobalCrossSymbol_self]
  rw [aggregateCross_real_linearCombination_re]
  rw [bombieriTwoBlockGlobalCrossSymbol_self,
    bombieriTwoBlockGlobalCrossSymbol_self]
  simp only [pow_two]
  rw [hswap]
  ring

/-- Exact quadratic and mixed coordinates of the two aggregate-orthogonal
residual tests. -/
theorem monotonePrimeAtom_aggregateOrthogonalResidual_coordinates
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ) :
    let H := bombieriRealQuadraticValue (monotoneQuarterCell parent k)
    let I := bombieriRealQuadraticValue
      (monotoneQuarterCutoff parent (k + 1))
    let T := monotonePrimeAtomAggregateReserve parent k S
    let C := (monotonePrimeAtomAggregateCross parent k S).re
    let K := monotonePrimeAtomInnerSuffixAggregateCross parent k S
    let D := monotonePrimeAtomHeadSuffixGlobalCross parent k
    bombieriRealQuadraticValue
        (monotonePrimeAtomHeadAggregateOrthogonalResidual parent k S) =
          T * (H * T - C ^ 2) ∧
      bombieriRealQuadraticValue
          (monotonePrimeAtomInnerAggregateOrthogonalResidual parent k S) =
            T * (I * T - K ^ 2) ∧
      (bombieriTwoBlockGlobalCrossSymbol
        (monotonePrimeAtomHeadAggregateOrthogonalResidual parent k S)
        (monotonePrimeAtomInnerAggregateOrthogonalResidual parent k S)).re =
          T * (T * D - C * K) := by
  dsimp only
  let h : BombieriTest := monotoneQuarterCell parent k
  let i : BombieriTest := monotoneQuarterCutoff parent (k + 1)
  let t : BombieriTest := monotonePrimeAtomAggregateSlice parent k S
  let H : ℝ := bombieriRealQuadraticValue h
  let I : ℝ := bombieriRealQuadraticValue i
  let T : ℝ := bombieriRealQuadraticValue t
  let C : ℝ := (bombieriTwoBlockGlobalCrossSymbol h t).re
  let K : ℝ := (bombieriTwoBlockGlobalCrossSymbol i t).re
  let D : ℝ := (bombieriTwoBlockGlobalCrossSymbol h i).re
  have hhead := aggregateQuadratic_real_linearCombination h t T (-C)
  have hinner := aggregateQuadratic_real_linearCombination i t T (-K)
  have hcross := aggregateCross_real_linearCombination_re
    h t i t T (-C) T (-K)
  have htt : (bombieriTwoBlockGlobalCrossSymbol t t).re = T := by
    rw [bombieriTwoBlockGlobalCrossSymbol_self]
    rfl
  have hti : (bombieriTwoBlockGlobalCrossSymbol t i).re = K := by
    have hswap := congrArg Complex.re
      (bombieriTwoBlockGlobalCrossSymbol_conj_swap i t)
    simpa only [Complex.star_def, Complex.conj_re, K] using hswap
  change
    bombieriRealQuadraticValue ((T : ℂ) • h + ((-C : ℝ) : ℂ) • t) =
        T * (H * T - C ^ 2) ∧
      bombieriRealQuadraticValue ((T : ℂ) • i + ((-K : ℝ) : ℂ) • t) =
        T * (I * T - K ^ 2) ∧
      (bombieriTwoBlockGlobalCrossSymbol
        ((T : ℂ) • h + ((-C : ℝ) : ℂ) • t)
        ((T : ℂ) • i + ((-K : ℝ) : ℂ) • t)).re =
          T * (T * D - C * K)
  constructor
  · rw [hhead]
    dsimp only [H, T, C]
    ring
  constructor
  · rw [hinner]
    dsimp only [I, T, K]
    ring
  · rw [hcross, htt, hti]
    dsimp only [T, C, K, D]
    ring

/-- With a positive aggregate pivot, the missing suffix--aggregate minor is
exactly nonnegativity of the concrete inner aggregate-orthogonal residual.
No support theorem or positivity input is used in this equivalence. -/
theorem monotonePrimeAtom_innerAggregateMinor_iff_residual_nonnegative
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ)
    (hT : 0 < monotonePrimeAtomAggregateReserve parent k S) :
    monotonePrimeAtomInnerSuffixAggregateCross parent k S ^ 2 ≤
        bombieriRealQuadraticValue
            (monotoneQuarterCutoff parent (k + 1)) *
          monotonePrimeAtomAggregateReserve parent k S ↔
      0 ≤ bombieriRealQuadraticValue
        (monotonePrimeAtomInnerAggregateOrthogonalResidual parent k S) := by
  have hcoordinates :=
    monotonePrimeAtom_aggregateOrthogonalResidual_coordinates parent k S
  dsimp only at hcoordinates
  rw [hcoordinates.2.1]
  constructor
  · intro hminor
    exact mul_nonneg hT.le (sub_nonneg.mpr hminor)
  · intro hresidual
    have hgap :
        0 ≤ bombieriRealQuadraticValue
              (monotoneQuarterCutoff parent (k + 1)) *
              monotonePrimeAtomAggregateReserve parent k S -
            monotonePrimeAtomInnerSuffixAggregateCross parent k S ^ 2 :=
      (mul_nonneg_iff_of_pos_left hT).mp hresidual
    linarith

/-- Expanding the residual quadratic identifies the exact analytic theorem
needed for the suffix--aggregate determinant: the complete symmetric
Mangoldt form of the actual inner residual must be dominated by its
archimedean form.  This is equivalent to the minor, rather than merely a
sufficient estimate. -/
theorem monotonePrimeAtom_innerAggregateMinor_iff_residualPrime_le_archimedean
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ)
    (hT : 0 < monotonePrimeAtomAggregateReserve parent k S) :
    monotonePrimeAtomInnerSuffixAggregateCross parent k S ^ 2 ≤
        bombieriRealQuadraticValue
            (monotoneQuarterCutoff parent (k + 1)) *
          monotonePrimeAtomAggregateReserve parent k S ↔
      bombieriRealLogPrimeAtomCross
          (monotonePrimeAtomInnerAggregateOrthogonalResidual parent k S)
          (monotonePrimeAtomInnerAggregateOrthogonalResidual parent k S) ≤
        bombieriRealLogArchimedeanCross
          (monotonePrimeAtomInnerAggregateOrthogonalResidual parent k S)
          (monotonePrimeAtomInnerAggregateOrthogonalResidual parent k S) := by
  rw [monotonePrimeAtom_innerAggregateMinor_iff_residual_nonnegative
    parent k S hT]
  unfold bombieriRealQuadraticValue
  rw [bombieriFunctional_quadratic_re_eq_completeRealLogKernel]
  unfold bombieriCompleteRealLogKernelCross
  exact sub_nonneg

/-- The same criterion with the arithmetic side displayed as the complete
all-lag Mangoldt series.  In particular, no finite selected-atom row remains
after aggregate orthogonalization. -/
theorem monotonePrimeAtom_innerAggregateMinor_iff_fullResidualPrimeRow_le_archimedean
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ)
    (hT : 0 < monotonePrimeAtomAggregateReserve parent k S) :
    monotonePrimeAtomInnerSuffixAggregateCross parent k S ^ 2 ≤
        bombieriRealQuadraticValue
            (monotoneQuarterCutoff parent (k + 1)) *
          monotonePrimeAtomAggregateReserve parent k S ↔
      (∑' n : ℕ, bombieriLogPrimeAtomWeight n *
        (bombieriRealLogCorrelation
            (monotonePrimeAtomInnerAggregateOrthogonalResidual parent k S)
            (monotonePrimeAtomInnerAggregateOrthogonalResidual parent k S)
            (-Real.log (((n + 1 : ℕ) : ℝ))) +
          bombieriRealLogCorrelation
            (monotonePrimeAtomInnerAggregateOrthogonalResidual parent k S)
            (monotonePrimeAtomInnerAggregateOrthogonalResidual parent k S)
            (Real.log (((n + 1 : ℕ) : ℝ))))) ≤
        bombieriRealLogArchimedeanCross
          (monotonePrimeAtomInnerAggregateOrthogonalResidual parent k S)
          (monotonePrimeAtomInnerAggregateOrthogonalResidual parent k S) := by
  rw [monotonePrimeAtom_innerAggregateMinor_iff_residualPrime_le_archimedean
    parent k S hT]
  rfl

/-- A genuine failure of the suffix--aggregate minor is already a negative
Bombieri quadratic for the explicit inner residual test.  Thus constructing
an admissible parent counterexample here would not merely refute a local
estimate: it would produce a witness against global Bombieri nonnegativity. -/
theorem monotonePrimeAtomInnerAggregateOrthogonalResidual_quadratic_negative_of_minor_failure
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ)
    (hT : 0 < monotonePrimeAtomAggregateReserve parent k S)
    (hfailure :
      bombieriRealQuadraticValue
            (monotoneQuarterCutoff parent (k + 1)) *
          monotonePrimeAtomAggregateReserve parent k S <
        monotonePrimeAtomInnerSuffixAggregateCross parent k S ^ 2) :
    bombieriRealQuadraticValue
        (monotonePrimeAtomInnerAggregateOrthogonalResidual parent k S) < 0 := by
  have hcoordinates :=
    monotonePrimeAtom_aggregateOrthogonalResidual_coordinates parent k S
  dsimp only at hcoordinates
  rw [hcoordinates.2.1]
  exact mul_neg_of_pos_of_neg hT (sub_neg.mpr hfailure)

/-- Conversely, global nonnegativity of the actual Bombieri quadratic closes
the suffix--aggregate minor immediately by testing the explicit residual.
This records precisely why a proof using only that input would be circular
for an RH proof. -/
theorem monotonePrimeAtom_innerAggregateMinor_of_global_nonnegative
    (hglobal : ∀ g : BombieriTest, 0 ≤ bombieriRealQuadraticValue g)
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ)
    (hT : 0 < monotonePrimeAtomAggregateReserve parent k S) :
    monotonePrimeAtomInnerSuffixAggregateCross parent k S ^ 2 ≤
      bombieriRealQuadraticValue
          (monotoneQuarterCutoff parent (k + 1)) *
        monotonePrimeAtomAggregateReserve parent k S := by
  exact (monotonePrimeAtom_innerAggregateMinor_iff_residual_nonnegative
    parent k S hT).2
      (hglobal (monotonePrimeAtomInnerAggregateOrthogonalResidual parent k S))

/-- With a positive aggregate pivot, the scalar three-way contraction is
exactly real Cauchy--Schwarz for the two concrete aggregate-orthogonal
residual tests. -/
theorem aggregateThreeWayResidualContraction_iff_residualCross
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ)
    (hT : 0 < monotonePrimeAtomAggregateReserve parent k S) :
    AggregateThreeWayResidualContraction
        (bombieriRealQuadraticValue (monotoneQuarterCell parent k))
        (bombieriRealQuadraticValue
          (monotoneQuarterCutoff parent (k + 1)))
        (monotonePrimeAtomAggregateReserve parent k S)
        (monotonePrimeAtomAggregateCross parent k S).re
        (monotonePrimeAtomInnerSuffixAggregateCross parent k S)
        (monotonePrimeAtomHeadSuffixGlobalCross parent k) ↔
      (bombieriTwoBlockGlobalCrossSymbol
        (monotonePrimeAtomHeadAggregateOrthogonalResidual parent k S)
        (monotonePrimeAtomInnerAggregateOrthogonalResidual parent k S)).re ^ 2 ≤
        bombieriRealQuadraticValue
            (monotonePrimeAtomHeadAggregateOrthogonalResidual parent k S) *
          bombieriRealQuadraticValue
            (monotonePrimeAtomInnerAggregateOrthogonalResidual parent k S) := by
  let H : ℝ := bombieriRealQuadraticValue (monotoneQuarterCell parent k)
  let I : ℝ := bombieriRealQuadraticValue
    (monotoneQuarterCutoff parent (k + 1))
  let T : ℝ := monotonePrimeAtomAggregateReserve parent k S
  let C : ℝ := (monotonePrimeAtomAggregateCross parent k S).re
  let K : ℝ := monotonePrimeAtomInnerSuffixAggregateCross parent k S
  let D : ℝ := monotonePrimeAtomHeadSuffixGlobalCross parent k
  let alpha : ℝ := H * T - C ^ 2
  let beta : ℝ := I * T - K ^ 2
  let delta : ℝ := T * D - C * K
  have hcoordinates :=
    monotonePrimeAtom_aggregateOrthogonalResidual_coordinates parent k S
  change
    bombieriRealQuadraticValue
        (monotonePrimeAtomHeadAggregateOrthogonalResidual parent k S) =
          T * alpha ∧
      bombieriRealQuadraticValue
          (monotonePrimeAtomInnerAggregateOrthogonalResidual parent k S) =
            T * beta ∧
      (bombieriTwoBlockGlobalCrossSymbol
        (monotonePrimeAtomHeadAggregateOrthogonalResidual parent k S)
        (monotonePrimeAtomInnerAggregateOrthogonalResidual parent k S)).re =
          T * delta at hcoordinates
  change delta ^ 2 ≤ alpha * beta ↔
    (bombieriTwoBlockGlobalCrossSymbol
      (monotonePrimeAtomHeadAggregateOrthogonalResidual parent k S)
      (monotonePrimeAtomInnerAggregateOrthogonalResidual parent k S)).re ^ 2 ≤
      bombieriRealQuadraticValue
          (monotonePrimeAtomHeadAggregateOrthogonalResidual parent k S) *
        bombieriRealQuadraticValue
          (monotonePrimeAtomInnerAggregateOrthogonalResidual parent k S)
  rw [hcoordinates.1, hcoordinates.2.1, hcoordinates.2.2]
  constructor
  · intro h
    calc
      (T * delta) ^ 2 = T ^ 2 * delta ^ 2 := by ring
      _ ≤ T ^ 2 * (alpha * beta) :=
        mul_le_mul_of_nonneg_left h (sq_nonneg T)
      _ = (T * alpha) * (T * beta) := by ring
  · intro h
    have hscaled : T ^ 2 * delta ^ 2 ≤ T ^ 2 * (alpha * beta) := by
      calc
        T ^ 2 * delta ^ 2 = (T * delta) ^ 2 := by ring
        _ ≤ (T * alpha) * (T * beta) := h
        _ = T ^ 2 * (alpha * beta) := by ring
    exact le_of_mul_le_mul_left hscaled (sq_pos_of_pos hT)

private theorem ratioTwo_real_smul
    (f : BombieriTest) (c : ℝ) (hf : BombieriRatioTwoCell f) :
    BombieriRatioTwoCell ((c : ℂ) • f) := by
  rcases hf with ⟨a, b, ha, hab, hsupport, hratio⟩
  refine ⟨a, b, ha, hab, ?_, hratio⟩
  exact (tsupport_smul_subset_right (fun _x : ℝ ↦ (c : ℂ))
    (f : ℝ → ℂ)).trans hsupport

/-- The head residual is still an honest ratio-two test because both of its
terms lie in the aggregate plateau. -/
theorem monotonePrimeAtomHeadAggregateOrthogonalResidual_ratioTwo
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ)
    (hT : monotonePrimeAtomAggregateReserve parent k S ≠ 0) :
    BombieriRatioTwoCell
      (monotonePrimeAtomHeadAggregateOrthogonalResidual parent k S) := by
  let T : ℝ := monotonePrimeAtomAggregateReserve parent k S
  let C : ℝ := (monotonePrimeAtomAggregateCross parent k S).re
  have hT' : T ≠ 0 := hT
  have hpencil := monotonePrimeAtom_head_add_smul_aggregateSlice_ratioTwo
    parent k S (((-C / T : ℝ) : ℂ))
  have heq :
      monotonePrimeAtomHeadAggregateOrthogonalResidual parent k S =
        (T : ℂ) • (monotoneQuarterCell parent k +
          (((-C / T : ℝ) : ℂ) •
            monotonePrimeAtomAggregateSlice parent k S)) := by
    apply TestFunction.ext
    intro x
    change
      (T : ℂ) * monotoneQuarterCell parent k x +
          ((-C : ℝ) : ℂ) * monotonePrimeAtomAggregateSlice parent k S x =
        (T : ℂ) * (monotoneQuarterCell parent k x +
          (((-C / T : ℝ) : ℂ) *
            monotonePrimeAtomAggregateSlice parent k S x))
    rw [mul_add, ← mul_assoc]
    congr 2
    push_cast
    field_simp [hT']
  rw [heq]
  exact ratioTwo_real_smul _ T hpencil

/-- The inner residual retains the original suffix tail, scaled only by the
aggregate reserve. -/
theorem monotonePrimeAtomInnerAggregateOrthogonalResidual_apply_of_upper
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ)
    {x : ℝ} (hx : quarterLogLatticePoint (k + 3) ≤ x) :
    monotonePrimeAtomInnerAggregateOrthogonalResidual parent k S x =
      (monotonePrimeAtomAggregateReserve parent k S : ℂ) * parent x := by
  have hinner : monotoneQuarterStep (k + 1) x = 1 := by
    apply monotoneQuarterStep_eq_one_of_le
    exact (quarterLogLatticePoint_mono (by omega)).trans hx
  have hlower : monotoneQuarterStep (k - 1) x = 1 := by
    apply monotoneQuarterStep_eq_one_of_le
    rw [show k - 1 + 1 = k by ring]
    exact (quarterLogLatticePoint_mono (by omega)).trans hx
  have hupper : monotoneQuarterStep (k + 2) x = 1 := by
    apply monotoneQuarterStep_eq_one_of_le
    simpa only [show k + 2 + 1 = k + 3 by ring] using hx
  simp only [monotonePrimeAtomInnerAggregateOrthogonalResidual,
    TestFunction.coe_add, Pi.add_apply,
    TestFunction.coe_smul, Pi.smul_apply, smul_eq_mul,
    monotoneQuarterCutoff_apply, monotonePrimeAtomAggregateSlice,
    monotoneRatioTwoBlock_apply, monotoneRatioTwoBlockMultiplier]
  rw [hinner, show k - 1 + 3 = k + 2 by ring, hlower, hupper]
  norm_num

/-- Pointwise, the concrete inner residual is the original suffix multiplied
by the aggregate pivot, minus the full finite von-Mangoldt dilation operator
multiplied by the suffix--aggregate cross.  This exposes the actual common
parent at both physical scales; no abstract residual coordinate remains. -/
theorem monotonePrimeAtomInnerAggregateOrthogonalResidual_apply
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ) (x : ℝ) :
    monotonePrimeAtomInnerAggregateOrthogonalResidual parent k S x =
      (((monotonePrimeAtomAggregateReserve parent k S *
          monotoneQuarterStep (k + 1) x : ℝ) : ℂ) * parent x) -
        (((monotonePrimeAtomInnerSuffixAggregateCross parent k S *
          monotonePrimeAtomPlateauMultiplier k x : ℝ) : ℂ) *
          ∑ j ∈ S,
            ((ArithmeticFunction.vonMangoldt (j + 1) : ℝ) : ℂ) *
              monotoneQuarterCutoff parent (k + 1)
                (((j + 1 : ℕ) : ℝ) * x)) := by
  simp only [monotonePrimeAtomInnerAggregateOrthogonalResidual,
    TestFunction.coe_add, Pi.add_apply, TestFunction.coe_smul,
    Pi.smul_apply, smul_eq_mul, monotoneQuarterCutoff_apply,
    monotonePrimeAtomAggregateSlice_apply]
  push_cast
  ring

/-- On the diagonal, the same actual parent transfer has exactly the
archimedean-minus-full-Mangoldt form displayed below.  Both arguments retain
the original long suffix and the finite aggregate of its normalized
dilations; there is no ratio-two replacement hidden in this identity. -/
theorem monotonePrimeAtomInnerAggregateOrthogonalResidual_quadratic_eq_parentTransfer_arch_sub_prime
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ) :
    bombieriRealQuadraticValue
        (monotonePrimeAtomInnerAggregateOrthogonalResidual parent k S) =
      bombieriRealLogArchimedeanCross
          (((monotonePrimeAtomAggregateReserve parent k S : ℝ) : ℂ) •
              monotoneQuarterCutoff parent (k + 1) +
            (((-monotonePrimeAtomInnerSuffixAggregateCross parent k S : ℝ) :
                ℂ) • monotonePrimeAtomAggregateSlice parent k S))
          (((monotonePrimeAtomAggregateReserve parent k S : ℝ) : ℂ) •
              monotoneQuarterCutoff parent (k + 1) +
            (((-monotonePrimeAtomInnerSuffixAggregateCross parent k S : ℝ) :
                ℂ) • monotonePrimeAtomAggregateSlice parent k S)) -
        bombieriRealLogPrimeAtomCross
          (((monotonePrimeAtomAggregateReserve parent k S : ℝ) : ℂ) •
              monotoneQuarterCutoff parent (k + 1) +
            (((-monotonePrimeAtomInnerSuffixAggregateCross parent k S : ℝ) :
                ℂ) • monotonePrimeAtomAggregateSlice parent k S))
          (((monotonePrimeAtomAggregateReserve parent k S : ℝ) : ℂ) •
              monotoneQuarterCutoff parent (k + 1) +
            (((-monotonePrimeAtomInnerSuffixAggregateCross parent k S : ℝ) :
                ℂ) • monotonePrimeAtomAggregateSlice parent k S)) := by
  unfold bombieriRealQuadraticValue
  rw [bombieriFunctional_quadratic_re_eq_completeRealLogKernel]
  rfl

private theorem monotonePrimeAtomAggregateSlice_add
    (f g : BombieriTest) (k : ℤ) (S : Finset ℕ) :
    monotonePrimeAtomAggregateSlice (f + g) k S =
      monotonePrimeAtomAggregateSlice f k S +
        monotonePrimeAtomAggregateSlice g k S := by
  apply TestFunction.ext
  intro x
  simp only [monotonePrimeAtomAggregateSlice_apply,
    monotoneQuarterCutoff_apply, TestFunction.coe_add, Pi.add_apply]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  ring

private theorem monotoneQuarterCutoff_add_for_aggregateVariation
    (f g : BombieriTest) (k : ℤ) :
    monotoneQuarterCutoff (f + g) k =
      monotoneQuarterCutoff f k + monotoneQuarterCutoff g k := by
  apply TestFunction.ext
  intro x
  simp only [monotoneQuarterCutoff_apply, TestFunction.coe_add, Pi.add_apply]
  ring

private theorem monotoneQuarterCutoff_real_smul_for_aggregateVariation
    (a : ℝ) (g : BombieriTest) (k : ℤ) :
    monotoneQuarterCutoff ((a : ℂ) • g) k =
      (a : ℂ) • monotoneQuarterCutoff g k := by
  apply TestFunction.ext
  intro x
  simp only [monotoneQuarterCutoff_apply, TestFunction.coe_smul,
    Pi.smul_apply, smul_eq_mul]
  ring

private theorem monotonePrimeAtomAggregateSlice_real_smul
    (a : ℝ) (g : BombieriTest) (k : ℤ) (S : Finset ℕ) :
    monotonePrimeAtomAggregateSlice ((a : ℂ) • g) k S =
      (a : ℂ) • monotonePrimeAtomAggregateSlice g k S := by
  apply TestFunction.ext
  intro x
  simp only [monotonePrimeAtomAggregateSlice_apply,
    monotoneQuarterCutoff_apply, TestFunction.coe_smul,
    Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  push_cast
  ring

/-- A variation invisible to the finite aggregate transfer leaves the
aggregate slice exactly fixed along the whole real parent line. -/
theorem monotonePrimeAtomAggregateSlice_add_real_smul_eq_of_transfer_zero
    (parent variation : BombieriTest) (k : ℤ) (S : Finset ℕ)
    (hzero : monotonePrimeAtomAggregateSlice variation k S = 0)
    (a : ℝ) :
    monotonePrimeAtomAggregateSlice (parent + (a : ℂ) • variation) k S =
      monotonePrimeAtomAggregateSlice parent k S := by
  rw [monotonePrimeAtomAggregateSlice_add,
    monotonePrimeAtomAggregateSlice_real_smul, hzero]
  simp

/-- A sufficiently far-right variation is invisible to the finite aggregate
transfer.  The explicit threshold depends only on the largest selected
dilation and the upper endpoint of the aggregate plateau. -/
theorem monotonePrimeAtomAggregateSlice_eq_zero_of_vanishes_below
    (variation : BombieriTest) (k : ℤ) (S : Finset ℕ)
    (hfar : ∀ y : ℝ,
      y < (((S.sup id + 2 : ℕ) : ℝ) *
        quarterLogLatticePoint (k + 3)) → variation y = 0) :
    monotonePrimeAtomAggregateSlice variation k S = 0 := by
  apply TestFunction.ext
  intro x
  rw [monotonePrimeAtomAggregateSlice_apply]
  by_cases hx : x ≤ quarterLogLatticePoint (k + 3)
  · have hsum :
        (∑ j ∈ S,
          ((ArithmeticFunction.vonMangoldt (j + 1) : ℝ) : ℂ) *
            monotoneQuarterCutoff variation (k + 1)
              (((j + 1 : ℕ) : ℝ) * x)) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hjle : j ≤ S.sup id := Finset.le_sup (f := id) hj
      have hjlt : j + 1 < S.sup id + 2 := by omega
      have hscaled :
          (((j + 1 : ℕ) : ℝ) * x) <
            (((S.sup id + 2 : ℕ) : ℝ) *
              quarterLogLatticePoint (k + 3)) := by
        calc
          (((j + 1 : ℕ) : ℝ) * x) ≤
              ((j + 1 : ℕ) : ℝ) *
                quarterLogLatticePoint (k + 3) :=
            mul_le_mul_of_nonneg_left hx (by positivity)
          _ < (((S.sup id + 2 : ℕ) : ℝ) *
                quarterLogLatticePoint (k + 3)) := by
            apply mul_lt_mul_of_pos_right _
              (quarterLogLatticePoint_pos (k + 3))
            exact_mod_cast hjlt
      rw [monotoneQuarterCutoff_apply, hfar _ hscaled, mul_zero, mul_zero]
    rw [hsum, mul_zero]
    rfl
  · have hxlower : quarterLogLatticePoint (k + 3) ≤ x :=
      (lt_of_not_ge hx).le
    have hlower : monotoneQuarterStep (k - 1) x = 1 := by
      apply monotoneQuarterStep_eq_one_of_le
      rw [show k - 1 + 1 = k by ring]
      exact (quarterLogLatticePoint_mono (by omega)).trans hxlower
    have hupper : monotoneQuarterStep (k + 2) x = 1 := by
      apply monotoneQuarterStep_eq_one_of_le
      simpa only [show k + 2 + 1 = k + 3 by ring] using hxlower
    unfold monotonePrimeAtomPlateauMultiplier
      monotoneRatioTwoBlockMultiplier
    rw [show k - 1 + 3 = k + 2 by ring, hlower, hupper]
    norm_num

/-- Every nonzero Bombieri test can be moved, by a common normalized
dilation that preserves its complete quadratic, into the blind region of the
finite aggregate transfer.  At that location the next monotone cutoff is the
test itself. -/
theorem exists_transferInvisible_normalizedDilation
    (g : BombieriTest) (hg : g ≠ 0) (k : ℤ) (S : Finset ℕ) :
    ∃ variation : BombieriTest,
      monotonePrimeAtomAggregateSlice variation k S = 0 ∧
      monotoneQuarterCutoff variation (k + 1) = variation ∧
      bombieriRealQuadraticValue variation = bombieriRealQuadraticValue g := by
  have hsupportNonempty : (tsupport (g : ℝ → ℂ)).Nonempty := by
    by_contra hempty
    apply hg
    apply TestFunction.ext
    intro x
    by_contra hx
    have hxmem : x ∈ tsupport (g : ℝ → ℂ) :=
      subset_tsupport (g : ℝ → ℂ) (Function.mem_support.mpr hx)
    exact hempty ⟨x, hxmem⟩
  let l : ℝ := sInf (tsupport (g : ℝ → ℂ))
  have hlmem : l ∈ tsupport (g : ℝ → ℂ) :=
    g.hasCompactSupport.isCompact.sInf_mem hsupportNonempty
  have hlpos : 0 < l := by
    simpa only [l, positiveHalfLine, mem_Ioi] using g.tsupport_subset hlmem
  have hleast : ∀ x ∈ tsupport (g : ℝ → ℂ), l ≤ x :=
    (g.hasCompactSupport.isCompact.isGLB_sInf hsupportNonempty).1
  let Y : ℝ := ((S.sup id + 2 : ℕ) : ℝ) *
    quarterLogLatticePoint (k + 3)
  have hYpos : 0 < Y := by
    dsimp only [Y]
    have hfactorpos : (0 : ℝ) < ((S.sup id + 2 : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < S.sup id + 2 by omega)
    exact mul_pos hfactorpos (quarterLogLatticePoint_pos (k + 3))
  let lambda : ℝ := l / (2 * Y)
  have hlambda : 0 < lambda := by
    dsimp only [lambda]
    positivity
  let variation : BombieriTest := normalizedDilation lambda hlambda g
  have hfar : ∀ y : ℝ, y < Y → variation y = 0 := by
    intro y hy
    rw [show variation y =
      ((Real.sqrt lambda : ℝ) : ℂ) * g (lambda * y) by
        rfl]
    have harg : lambda * y < l := by
      calc
        lambda * y < lambda * Y := mul_lt_mul_of_pos_left hy hlambda
        _ = l / 2 := by
          dsimp only [lambda]
          field_simp [hYpos.ne']
        _ < l := by linarith
    have hzero : g (lambda * y) = 0 := by
      by_contra hne
      have hmem : lambda * y ∈ tsupport (g : ℝ → ℂ) :=
        subset_tsupport (g : ℝ → ℂ) (Function.mem_support.mpr hne)
      exact (not_lt_of_ge (hleast _ hmem)) harg
    rw [hzero, mul_zero]
  have htransfer : monotonePrimeAtomAggregateSlice variation k S = 0 := by
    apply monotonePrimeAtomAggregateSlice_eq_zero_of_vanishes_below
    simpa only [Y] using hfar
  have hlambdaLower : l / lambda = 2 * Y := by
    dsimp only [lambda]
    field_simp [hlpos.ne', hYpos.ne']
  have hYlower : quarterLogLatticePoint (k + 2) ≤ Y := by
    have hstep : quarterLogLatticePoint (k + 2) ≤
        quarterLogLatticePoint (k + 3) :=
      quarterLogLatticePoint_mono (by omega)
    have hfactor : (1 : ℝ) ≤ ((S.sup id + 2 : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ S.sup id + 2 by omega)
    dsimp only [Y]
    calc
      quarterLogLatticePoint (k + 2) ≤
          quarterLogLatticePoint (k + 3) := hstep
      _ ≤ ((S.sup id + 2 : ℕ) : ℝ) *
          quarterLogLatticePoint (k + 3) := by
        nlinarith [quarterLogLatticePoint_pos (k + 3)]
  have hcutoff : monotoneQuarterCutoff variation (k + 1) = variation := by
    apply monotoneQuarterCutoff_eq_parent_of_lattice_le_tsupport
    intro x hx
    have hxpre : lambda * x ∈ tsupport (g : ℝ → ℂ) := by
      have hx' := hx
      rw [show tsupport (variation : ℝ → ℂ) =
        (Homeomorph.mulLeft₀ lambda hlambda.ne') ⁻¹'
          tsupport (g : ℝ → ℂ) by
            exact normalizedDilation_tsupport lambda hlambda g] at hx'
      exact hx'
    have hlx : l / lambda ≤ x := by
      rw [div_le_iff₀ hlambda]
      simpa only [mul_comm] using hleast _ hxpre
    rw [hlambdaLower] at hlx
    have hxlower : quarterLogLatticePoint (k + 2) ≤ x :=
      hYlower.trans (by linarith)
    simpa only [show k + 1 + 1 = k + 2 by ring] using hxlower
  refine ⟨variation, htransfer, hcutoff, ?_⟩
  dsimp only [variation]
  unfold bombieriRealQuadraticValue
  rw [bombieriFunctional_quadratic_normalizedDilation]

/-- The direction induced in the inner residual by a transfer-invisible
parent variation: the far variation with its complete projection onto the
fixed aggregate slice removed. -/
def monotonePrimeAtomInnerAggregateVariationDirection
    (parent variation : BombieriTest) (k : ℤ) (S : Finset ℕ) : BombieriTest :=
  let T := monotonePrimeAtomAggregateReserve parent k S
  let L := (bombieriTwoBlockGlobalCrossSymbol
    (monotoneQuarterCutoff variation (k + 1))
    (monotonePrimeAtomAggregateSlice parent k S)).re
  (T : ℂ) • monotoneQuarterCutoff variation (k + 1) +
    ((-L : ℝ) : ℂ) • monotonePrimeAtomAggregateSlice parent k S

/-- Along a transfer-invisible parent line, the actual inner residual varies
affinely in the projected far-tail direction above.  In particular, the
finite aggregate slice and its reserve do not change with the parameter. -/
theorem monotonePrimeAtomInnerAggregateOrthogonalResidual_add_real_smul_eq
    (parent variation : BombieriTest) (k : ℤ) (S : Finset ℕ)
    (hzero : monotonePrimeAtomAggregateSlice variation k S = 0)
    (a : ℝ) :
    monotonePrimeAtomInnerAggregateOrthogonalResidual
        (parent + (a : ℂ) • variation) k S =
      monotonePrimeAtomInnerAggregateOrthogonalResidual parent k S +
        (a : ℂ) • monotonePrimeAtomInnerAggregateVariationDirection
          parent variation k S := by
  have hslice :=
    monotonePrimeAtomAggregateSlice_add_real_smul_eq_of_transfer_zero
      parent variation k S hzero a
  have hcutoff :
      monotoneQuarterCutoff (parent + (a : ℂ) • variation) (k + 1) =
        monotoneQuarterCutoff parent (k + 1) +
          (a : ℂ) • monotoneQuarterCutoff variation (k + 1) := by
    rw [monotoneQuarterCutoff_add_for_aggregateVariation,
      monotoneQuarterCutoff_real_smul_for_aggregateVariation]
  have hreserve :
      monotonePrimeAtomAggregateReserve
          (parent + (a : ℂ) • variation) k S =
        monotonePrimeAtomAggregateReserve parent k S := by
    unfold monotonePrimeAtomAggregateReserve
    rw [hslice]
  let L : ℝ := (bombieriTwoBlockGlobalCrossSymbol
    (monotoneQuarterCutoff variation (k + 1))
    (monotonePrimeAtomAggregateSlice parent k S)).re
  have hcross :
      monotonePrimeAtomInnerSuffixAggregateCross
          (parent + (a : ℂ) • variation) k S =
        monotonePrimeAtomInnerSuffixAggregateCross parent k S + a * L := by
    unfold monotonePrimeAtomInnerSuffixAggregateCross
    rw [hslice, hcutoff,
      bombieriTwoBlockGlobalCrossSymbol_add_left,
      bombieriTwoBlockGlobalCrossSymbol_smul_left, Complex.add_re]
    dsimp only [L]
    rw [starRingEnd_apply, Complex.star_def, Complex.conj_ofReal]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
  apply TestFunction.ext
  intro x
  simp only [monotonePrimeAtomInnerAggregateOrthogonalResidual,
    monotonePrimeAtomInnerAggregateVariationDirection,
    TestFunction.coe_add, Pi.add_apply, TestFunction.coe_smul,
    Pi.smul_apply, smul_eq_mul]
  rw [hreserve, hcross, hslice, hcutoff]
  dsimp only [L]
  simp only [TestFunction.coe_add, Pi.add_apply,
    TestFunction.coe_smul, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

/-- The projected variation direction has the exact Schur-complement
quadratic.  Hence its nonnegativity forces nonnegativity of the original far
variation and even the sharp determinant against the fixed aggregate slice. -/
theorem monotonePrimeAtomInnerAggregateVariationDirection_quadratic
    (parent variation : BombieriTest) (k : ℤ) (S : Finset ℕ) :
    let T := monotonePrimeAtomAggregateReserve parent k S
    let L := (bombieriTwoBlockGlobalCrossSymbol
      (monotoneQuarterCutoff variation (k + 1))
      (monotonePrimeAtomAggregateSlice parent k S)).re
    bombieriRealQuadraticValue
        (monotonePrimeAtomInnerAggregateVariationDirection
          parent variation k S) =
      T * (T * bombieriRealQuadraticValue
        (monotoneQuarterCutoff variation (k + 1)) - L ^ 2) := by
  dsimp only
  let g : BombieriTest := monotoneQuarterCutoff variation (k + 1)
  let t : BombieriTest := monotonePrimeAtomAggregateSlice parent k S
  let T : ℝ := bombieriRealQuadraticValue t
  let L : ℝ := (bombieriTwoBlockGlobalCrossSymbol g t).re
  have hquad := aggregateQuadratic_real_linearCombination g t T (-L)
  have ht : bombieriRealQuadraticValue t = T := rfl
  change bombieriRealQuadraticValue ((T : ℂ) • g + ((-L : ℝ) : ℂ) • t) =
    T * (T * bombieriRealQuadraticValue g - L ^ 2)
  rw [hquad, ht]
  ring

private theorem quadratic_leading_nonnegative_of_forall_nonnegative
    (A B C : ℝ)
    (hall : ∀ a : ℝ, 0 ≤ A + 2 * a * B + a ^ 2 * C) :
    0 ≤ C := by
  by_contra hC
  have hCneg : C < 0 := lt_of_not_ge hC
  let d : ℝ := -C
  have hd : 0 < d := by dsimp only [d]; linarith
  let a : ℝ := (2 * |B| + |A| + d) / d
  have ha : 1 ≤ a := by
    dsimp only [a]
    rw [le_div_iff₀ hd]
    nlinarith [abs_nonneg A, abs_nonneg B]
  have had : a * d = 2 * |B| + |A| + d := by
    dsimp only [a]
    field_simp [hd.ne']
  have hdom : |A| + 2 * a * |B| < a ^ 2 * d := by
    have hnonneg : 0 ≤ (a - 1) * |A| :=
      mul_nonneg (sub_nonneg.mpr ha) (abs_nonneg A)
    have hpos : 0 < a * d := mul_pos (lt_of_lt_of_le zero_lt_one ha) hd
    have hid :
        a ^ 2 * d - (|A| + 2 * a * |B|) =
          (a - 1) * |A| + a * d := by
      calc
        a ^ 2 * d - (|A| + 2 * a * |B|) =
            a * (a * d) - (|A| + 2 * a * |B|) := by ring
        _ = a * (2 * |B| + |A| + d) -
            (|A| + 2 * a * |B|) := by rw [had]
        _ = (a - 1) * |A| + a * d := by ring
    nlinarith
  have hBbound : 2 * a * B ≤ 2 * a * |B| := by
    exact mul_le_mul_of_nonneg_left (le_abs_self B)
      (mul_nonneg (by norm_num) (le_trans (by norm_num) ha))
  have hpoly : A + 2 * a * B + a ^ 2 * C < 0 := by
    have hAabs := le_abs_self A
    dsimp only [d] at hdom
    nlinarith
  exact (not_lt_of_ge (hall a)) hpoly

/-- If the suffix--aggregate minor were valid along every point of a parent
line invisible to the finite transfer, then its leading coefficient forces
the sharp complete determinant between that arbitrary variation and the
fixed aggregate slice.  This is the expressivity step: the local residual
family tests a whole far-tail Bombieri direction, not merely the base
parent. -/
theorem innerAggregateMinor_family_forces_transferInvisibleVariation_determinant
    (parent variation : BombieriTest) (k : ℤ) (S : Finset ℕ)
    (hzero : monotonePrimeAtomAggregateSlice variation k S = 0)
    (hT : 0 < monotonePrimeAtomAggregateReserve parent k S)
    (hminor : ∀ a : ℝ,
      monotonePrimeAtomInnerSuffixAggregateCross
            (parent + (a : ℂ) • variation) k S ^ 2 ≤
        bombieriRealQuadraticValue
            (monotoneQuarterCutoff
              (parent + (a : ℂ) • variation) (k + 1)) *
          monotonePrimeAtomAggregateReserve
            (parent + (a : ℂ) • variation) k S) :
    (bombieriTwoBlockGlobalCrossSymbol
        (monotoneQuarterCutoff variation (k + 1))
        (monotonePrimeAtomAggregateSlice parent k S)).re ^ 2 ≤
      monotonePrimeAtomAggregateReserve parent k S *
        bombieriRealQuadraticValue
          (monotoneQuarterCutoff variation (k + 1)) := by
  let R₀ : BombieriTest :=
    monotonePrimeAtomInnerAggregateOrthogonalResidual parent k S
  let D : BombieriTest :=
    monotonePrimeAtomInnerAggregateVariationDirection parent variation k S
  let A : ℝ := bombieriRealQuadraticValue R₀
  let B : ℝ := (bombieriTwoBlockGlobalCrossSymbol R₀ D).re
  let C : ℝ := bombieriRealQuadraticValue D
  have hall : ∀ a : ℝ, 0 ≤ A + 2 * a * B + a ^ 2 * C := by
    intro a
    have hslice :=
      monotonePrimeAtomAggregateSlice_add_real_smul_eq_of_transfer_zero
        parent variation k S hzero a
    have hreserve :
        monotonePrimeAtomAggregateReserve
            (parent + (a : ℂ) • variation) k S =
          monotonePrimeAtomAggregateReserve parent k S := by
      unfold monotonePrimeAtomAggregateReserve
      rw [hslice]
    have hTa :
        0 < monotonePrimeAtomAggregateReserve
          (parent + (a : ℂ) • variation) k S := by
      rw [hreserve]
      exact hT
    have hresidual :=
      (monotonePrimeAtom_innerAggregateMinor_iff_residual_nonnegative
        (parent + (a : ℂ) • variation) k S hTa).1 (hminor a)
    rw [monotonePrimeAtomInnerAggregateOrthogonalResidual_add_real_smul_eq
      parent variation k S hzero a] at hresidual
    have hquad := aggregateQuadratic_real_linearCombination R₀ D 1 a
    norm_num at hquad
    change bombieriRealQuadraticValue (R₀ + (a : ℂ) • D) =
      A + a ^ 2 * C + 2 * a * B at hquad
    rw [hquad] at hresidual
    nlinarith
  have hC : 0 ≤ C :=
    quadratic_leading_nonnegative_of_forall_nonnegative A B C hall
  have hdirection :=
    monotonePrimeAtomInnerAggregateVariationDirection_quadratic
      parent variation k S
  change C =
    monotonePrimeAtomAggregateReserve parent k S *
      (monotonePrimeAtomAggregateReserve parent k S *
          bombieriRealQuadraticValue
            (monotoneQuarterCutoff variation (k + 1)) -
        (bombieriTwoBlockGlobalCrossSymbol
          (monotoneQuarterCutoff variation (k + 1))
          (monotonePrimeAtomAggregateSlice parent k S)).re ^ 2) at hdirection
  rw [hdirection] at hC
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hT).mp hC)

/-- In particular, validity of the residual minor on every transfer-blind
far-tail variation forces the original variation itself to have nonnegative
complete Bombieri quadratic value. -/
theorem innerAggregateMinor_family_forces_transferInvisibleVariation_nonnegative
    (parent variation : BombieriTest) (k : ℤ) (S : Finset ℕ)
    (hzero : monotonePrimeAtomAggregateSlice variation k S = 0)
    (hT : 0 < monotonePrimeAtomAggregateReserve parent k S)
    (hminor : ∀ a : ℝ,
      monotonePrimeAtomInnerSuffixAggregateCross
            (parent + (a : ℂ) • variation) k S ^ 2 ≤
        bombieriRealQuadraticValue
            (monotoneQuarterCutoff
              (parent + (a : ℂ) • variation) (k + 1)) *
          monotonePrimeAtomAggregateReserve
            (parent + (a : ℂ) • variation) k S) :
    0 ≤ bombieriRealQuadraticValue
      (monotoneQuarterCutoff variation (k + 1)) := by
  have hdet :=
    innerAggregateMinor_family_forces_transferInvisibleVariation_determinant
      parent variation k S hzero hT hminor
  have hsq : 0 ≤
      (bombieriTwoBlockGlobalCrossSymbol
        (monotoneQuarterCutoff variation (k + 1))
        (monotonePrimeAtomAggregateSlice parent k S)).re ^ 2 := sq_nonneg _
  nlinarith

private theorem bombieriRealQuadraticValue_zero_for_aggregateExpressivity :
    bombieriRealQuadraticValue (0 : BombieriTest) = 0 := by
  unfold bombieriRealQuadraticValue
  have h := bombieriFunctional_quadratic_smul
    (0 : ℂ) (0 : BombieriTest)
  simpa only [zero_smul, Complex.normSq_zero, Complex.ofReal_zero,
    zero_mul, Complex.zero_re] using congrArg Complex.re h

/-- A universal proof of the inner suffix--aggregate minor at one fixed
positive aggregate pivot would already prove the complete Bombieri
quadratic nonnegative on every test.  Indeed, normalized dilation moves an
arbitrary nonzero test into the transfer-blind region without changing its
quadratic, and the parent-line leading coefficient recovers that quadratic.

Thus this residual-minor route is globally expressive rather than a
strictly simpler local induction step. -/
theorem innerAggregateMinor_for_all_parents_forces_global_nonnegative
    (base : BombieriTest) (k : ℤ) (S : Finset ℕ)
    (hT : 0 < monotonePrimeAtomAggregateReserve base k S)
    (hminor : ∀ parent : BombieriTest,
      monotonePrimeAtomInnerSuffixAggregateCross parent k S ^ 2 ≤
        bombieriRealQuadraticValue
            (monotoneQuarterCutoff parent (k + 1)) *
          monotonePrimeAtomAggregateReserve parent k S) :
    ∀ g : BombieriTest, 0 ≤ bombieriRealQuadraticValue g := by
  intro g
  by_cases hg : g = 0
  · rw [hg, bombieriRealQuadraticValue_zero_for_aggregateExpressivity]
  · obtain ⟨variation, hzero, hcutoff, hquadratic⟩ :=
      exists_transferInvisible_normalizedDilation g hg k S
    have hvariation :=
      innerAggregateMinor_family_forces_transferInvisibleVariation_nonnegative
        base variation k S hzero hT (fun a => hminor _)
    rw [hcutoff, hquadratic] at hvariation
    exact hvariation

/-- For a nonzero pivot, the inner residual is the positive-pivot scaling of
the actual suffix--aggregate Schur pencil.  Thus proving its nonnegativity is
precisely a production pencil problem, not a new abstract scalar form. -/
theorem monotonePrimeAtomInnerAggregateOrthogonalResidual_eq_smul_pencil
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ)
    (hT : monotonePrimeAtomAggregateReserve parent k S ≠ 0) :
    monotonePrimeAtomInnerAggregateOrthogonalResidual parent k S =
      ((monotonePrimeAtomAggregateReserve parent k S : ℝ) : ℂ) •
        (monotoneQuarterCutoff parent (k + 1) +
          (((-monotonePrimeAtomInnerSuffixAggregateCross parent k S /
              monotonePrimeAtomAggregateReserve parent k S : ℝ) : ℂ) •
            monotonePrimeAtomAggregateSlice parent k S)) := by
  apply TestFunction.ext
  intro x
  simp only [monotonePrimeAtomInnerAggregateOrthogonalResidual,
    TestFunction.coe_add, Pi.add_apply, TestFunction.coe_smul,
    Pi.smul_apply, smul_eq_mul]
  rw [mul_add, ← mul_assoc]
  congr 2
  push_cast
  field_simp [hT]

/-- The production residual generally lies outside the ratio-two cone.  If
it has one nonzero lower value and the parent has a surviving tail value more
than a factor two away, the residual cannot be a ratio-two Bombieri test.
The upper value is forced by the exact tail formula, so this obstruction is
support-theoretic rather than a failure of scalar normalization. -/
theorem monotonePrimeAtomInnerAggregateOrthogonalResidual_not_ratioTwo_of_separated_tail
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ)
    (hT : monotonePrimeAtomAggregateReserve parent k S ≠ 0)
    {x y : ℝ} (hxy : 2 * x < y)
    (hy : quarterLogLatticePoint (k + 3) ≤ y)
    (hleft :
      monotonePrimeAtomInnerAggregateOrthogonalResidual parent k S x ≠ 0)
    (htail : parent y ≠ 0) :
    ¬ BombieriRatioTwoCell
      (monotonePrimeAtomInnerAggregateOrthogonalResidual parent k S) := by
  apply not_ratioTwo_of_nonzero_at_factor_gt_two
    (f := monotonePrimeAtomInnerAggregateOrthogonalResidual parent k S)
    hxy hleft
  rw [monotonePrimeAtomInnerAggregateOrthogonalResidual_apply_of_upper
    parent k S hy]
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hT) htail

/-! ## The surviving Mangoldt row after residualization -/

/-- Archimedean part of the aggregate-pivot residual cross. -/
def monotonePrimeAtomAggregateResidualArchimedeanCross
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ) : ℝ :=
  monotonePrimeAtomAggregateReserve parent k S *
      monotoneQuarterHeadSuffixRealArchimedeanCross parent k -
    (monotonePrimeAtomAggregateCross parent k S).re *
      bombieriRealLogArchimedeanCross
        (monotoneQuarterCutoff parent (k + 1))
        (monotonePrimeAtomAggregateSlice parent k S)

/-- The new full Mangoldt cross between the unchanged inner suffix and the
aggregate slice. -/
def monotonePrimeAtomInnerSuffixAggregatePrimeCross
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ) : ℝ :=
  bombieriRealLogPrimeAtomCross
    (monotoneQuarterCutoff parent (k + 1))
    (monotonePrimeAtomAggregateSlice parent k S)

/-- Prime part of the aggregate-pivot residual cross. -/
def monotonePrimeAtomAggregateResidualPrimeCross
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ) : ℝ :=
  monotonePrimeAtomAggregateReserve parent k S *
      monotoneQuarterHeadSuffixRealPrimeCross parent k -
    (monotonePrimeAtomAggregateCross parent k S).re *
      monotonePrimeAtomInnerSuffixAggregatePrimeCross parent k S

/-- The cross of the two aggregate-orthogonal residuals is exactly the
archimedean residual minus the surviving Mangoldt residual, scaled by the
aggregate pivot. -/
theorem monotonePrimeAtom_aggregateOrthogonalResidual_cross_eq_arch_sub_prime
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ) :
    (bombieriTwoBlockGlobalCrossSymbol
      (monotonePrimeAtomHeadAggregateOrthogonalResidual parent k S)
      (monotonePrimeAtomInnerAggregateOrthogonalResidual parent k S)).re =
        monotonePrimeAtomAggregateReserve parent k S *
          (monotonePrimeAtomAggregateResidualArchimedeanCross parent k S -
            monotonePrimeAtomAggregateResidualPrimeCross parent k S) := by
  have hcoordinates :=
    monotonePrimeAtom_aggregateOrthogonalResidual_coordinates parent k S
  rw [hcoordinates.2.2]
  unfold monotonePrimeAtomHeadSuffixGlobalCross
    monotonePrimeAtomInnerSuffixAggregateCross
    monotonePrimeAtomAggregateResidualArchimedeanCross
    monotonePrimeAtomAggregateResidualPrimeCross
    monotonePrimeAtomInnerSuffixAggregatePrimeCross
  rw [← bombieriCompleteRealLogKernelCross_eq_globalCross_re,
    ← bombieriCompleteRealLogKernelCross_eq_globalCross_re,
    bombieriCompleteRealLogKernelCross,
    bombieriCompleteRealLogKernelCross,
    bombieriRealLogArchimedeanCross_cell_cutoff_eq_explicit,
    bombieriRealLogPrimeAtomCross_cell_cutoff_eq_explicit]
  ring

/-- The new suffix--aggregate prime cross is still the complete symmetric
Mangoldt row.  No atom-count or lag truncation is created by the aggregate
pivot. -/
theorem monotonePrimeAtomInnerSuffixAggregatePrimeCross_eq_tsum
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ) :
    monotonePrimeAtomInnerSuffixAggregatePrimeCross parent k S =
      ∑' j : ℕ, bombieriLogPrimeAtomWeight j *
        (bombieriRealLogCorrelation
            (monotoneQuarterCutoff parent (k + 1))
            (monotonePrimeAtomAggregateSlice parent k S)
            (-Real.log (((j + 1 : ℕ) : ℝ))) +
          bombieriRealLogCorrelation
            (monotoneQuarterCutoff parent (k + 1))
            (monotonePrimeAtomAggregateSlice parent k S)
            (Real.log (((j + 1 : ℕ) : ℝ)))) := by
  rfl

/-- If `S` captures the original head--suffix prime row, residualization
replaces that finite row by the same weighted finite sum minus the new full
suffix--aggregate Mangoldt row. -/
theorem monotonePrimeAtomAggregateResidualPrimeCross_eq_finset_sub_full
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ)
    (hout : ∀ j ∉ S, monotonePrimeAtomValue parent k j = 0) :
    monotonePrimeAtomAggregateResidualPrimeCross parent k S =
      monotonePrimeAtomAggregateReserve parent k S *
          (∑ j ∈ S, monotonePrimeAtomValue parent k j) -
        (monotonePrimeAtomAggregateCross parent k S).re *
          monotonePrimeAtomInnerSuffixAggregatePrimeCross parent k S := by
  unfold monotonePrimeAtomAggregateResidualPrimeCross
  rw [← monotoneQuarterHeadSuffixRealPrimeCross_eq_finset parent k S hout]

/-- Equivalently, after using the aggregate remainder identity, the surviving
prime obstruction is a full suffix--aggregate Mangoldt row plus the exact
translated-kernel remainder.  It does not cancel structurally. -/
theorem monotonePrimeAtomAggregateResidualPrimeCross_eq_survivingRow
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ)
    (hout : ∀ j ∉ S, monotonePrimeAtomValue parent k j = 0) :
    monotonePrimeAtomAggregateResidualPrimeCross parent k S =
      (monotonePrimeAtomAggregateCross parent k S).re *
          (monotonePrimeAtomAggregateReserve parent k S -
            monotonePrimeAtomInnerSuffixAggregatePrimeCross parent k S) -
        monotonePrimeAtomAggregateReserve parent k S *
          monotonePrimeAtomAggregateRemainder parent k S := by
  rw [monotonePrimeAtomAggregateResidualPrimeCross_eq_finset_sub_full
    parent k S hout]
  unfold monotonePrimeAtomAggregateRemainder
  ring

/-! ## A different all-length coordinate: the zero-lag aggregate overlap -/

private theorem aggregateDirectedCorrelation_integrableOn
    (f g : BombieriTest) (x : ℝ) :
    IntegrableOn
      (fun y : ℝ ↦ f (x * y) * starRingEnd ℂ (g y))
      (Set.Ioi 0) := by
  have hcont : Continuous
      (fun y : ℝ ↦ f (x * y) * starRingEnd ℂ (g y)) := by
    fun_prop
  have hgcompact : HasCompactSupport
      (fun y : ℝ ↦ starRingEnd ℂ (g y)) := by
    exact g.hasCompactSupport.comp_left (by simp)
  have hcompact : HasCompactSupport
      (fun y : ℝ ↦ f (x * y) * starRingEnd ℂ (g y)) := by
    simpa only [Pi.mul_apply] using
      hgcompact.mul_left (f := fun y : ℝ ↦ f (x * y))
  exact (hcont.integrable_of_hasCompactSupport hcompact).integrableOn

private theorem aggregateDirectedCorrelation_add_left
    (f g h : BombieriTest) (x : ℝ) :
    bombieriDirectedCorrelation (f + g) h x =
      bombieriDirectedCorrelation f h x +
        bombieriDirectedCorrelation g h x := by
  unfold bombieriDirectedCorrelation
  rw [← integral_add
    (aggregateDirectedCorrelation_integrableOn f h x)
    (aggregateDirectedCorrelation_integrableOn g h x)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y _hy
  simp only [TestFunction.coe_add, Pi.add_apply]
  ring

private theorem aggregateDirectedCorrelation_finset_sum_left
    {J : Type*} [DecidableEq J] (S : Finset J)
    (f : J → BombieriTest) (g : BombieriTest) (x : ℝ) :
    bombieriDirectedCorrelation (∑ j ∈ S, f j) g x =
      ∑ j ∈ S, bombieriDirectedCorrelation (f j) g x := by
  induction S using Finset.induction_on with
  | empty => simp [bombieriDirectedCorrelation]
  | @insert j S hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj,
        aggregateDirectedCorrelation_add_left, ih]

/-- The selected finite Mangoldt row has a representation that does not use
the complete global Bombieri cross at all: it is exactly one zero-lag
physical overlap between the coherently aggregated transplanted slice and
the head.  Thus aggregation removes the translated-kernel remainder at the
level of this coordinate, rather than asking a later Schur complement to
cancel it. -/
theorem monotonePrimeAtom_finset_sum_eq_aggregate_zeroLagOverlap
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ) :
    ∑ j ∈ S, monotonePrimeAtomValue parent k j =
      (bombieriDirectedCorrelation
        (monotonePrimeAtomAggregateSlice parent k S)
        (monotoneQuarterCell parent k) 1).re := by
  rw [monotonePrimeAtomAggregateSlice_eq_sum,
    aggregateDirectedCorrelation_finset_sum_left]
  change
    ∑ j ∈ S, monotonePrimeAtomValue parent k j =
      Complex.reCLM
        (∑ j ∈ S,
          bombieriDirectedCorrelation
            (((bombieriLogPrimeAtomWeight j : ℝ) : ℂ) •
              monotonePrimeAtomTransplantedSlice parent k j)
            (monotoneQuarterCell parent k) 1)
  rw [map_sum Complex.reCLM]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [bombieriDirectedCorrelation_smul_left]
  rcases Nat.eq_zero_or_pos j with rfl | hjpos
  · unfold monotonePrimeAtomValue bombieriLogPrimeAtomCrossSummand
      bombieriLogPrimeAtomWeight
    simp only [Nat.zero_add, ArithmeticFunction.vonMangoldt_apply_one,
      zero_mul, Complex.ofReal_zero, Complex.zero_re,
      Complex.reCLM_apply]
  · rw [monotonePrimeAtomValue_eq_weight_mul_transplantedOverlap
      parent k j hjpos]
    simp only [Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]

/-- Consequently the entire selected prime row costs only one head critical
energy and one aggregate-slice critical energy, independent of the number of
atoms in `S`.  The remaining all-length problem in this coordinate is a norm
transfer estimate for the single aggregate slice. -/
theorem monotonePrimeAtom_finset_sum_sq_le_criticalLogEnergy
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ) :
    (∑ j ∈ S, monotonePrimeAtomValue parent k j) ^ 2 ≤
      bombieriCriticalLogEnergy
          (monotonePrimeAtomAggregateSlice parent k S) *
        bombieriCriticalLogEnergy (monotoneQuarterCell parent k) := by
  rw [monotonePrimeAtom_finset_sum_eq_aggregate_zeroLagOverlap]
  have hre :
      (bombieriDirectedCorrelation
          (monotonePrimeAtomAggregateSlice parent k S)
          (monotoneQuarterCell parent k) 1).re ^ 2 ≤
        Complex.normSq
          (bombieriDirectedCorrelation
            (monotonePrimeAtomAggregateSlice parent k S)
            (monotoneQuarterCell parent k) 1) := by
    simp only [Complex.normSq_apply]
    nlinarith [sq_nonneg
      (bombieriDirectedCorrelation
        (monotonePrimeAtomAggregateSlice parent k S)
        (monotoneQuarterCell parent k) 1).im]
  exact hre.trans
    (normSq_bombieriDirectedCorrelation_one_le_criticalLogEnergy_mul
      (monotonePrimeAtomAggregateSlice parent k S)
      (monotoneQuarterCell parent k))

/-! ## The remaining norm-transfer deficit -/

/-- For a conjugation-fixed parent, the aggregate slice is still
conjugation-fixed.  Thus both tests in the zero-lag representation lie in the
real ratio-two coercivity class. -/
theorem bombieriConjugateTest_monotonePrimeAtomAggregateSlice
    (parent : BombieriTest)
    (hparent : bombieriConjugateTest parent = parent)
    (k : ℤ) (S : Finset ℕ) :
    bombieriConjugateTest
        (monotonePrimeAtomAggregateSlice parent k S) =
      monotonePrimeAtomAggregateSlice parent k S := by
  apply TestFunction.ext
  intro x
  simp only [bombieriConjugateTest_apply]
  rw [monotonePrimeAtomAggregateSlice_apply,
    map_mul, Complex.conj_ofReal,
    map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _hj
  rw [map_mul, Complex.conj_ofReal]
  have hcut := congrArg
    (fun f : BombieriTest ↦ f (((j + 1 : ℕ) : ℝ) * x))
    (bombieriConjugateTest_monotoneQuarterCutoff
      parent hparent (k + 1))
  have hcut' :
      starRingEnd ℂ
          (monotoneQuarterCutoff parent (k + 1)
            (((j + 1 : ℕ) : ℝ) * x)) =
        monotoneQuarterCutoff parent (k + 1)
          (((j + 1 : ℕ) : ℝ) * x) := by
    simpa only [bombieriConjugateTest_apply] using hcut
  rw [hcut']

/-- The concrete inner aggregate-orthogonal residual remains a real
Bombieri test whenever the common parent is real. -/
theorem bombieriConjugateTest_monotonePrimeAtomInnerAggregateOrthogonalResidual
    (parent : BombieriTest)
    (hparent : bombieriConjugateTest parent = parent)
    (k : ℤ) (S : Finset ℕ) :
    bombieriConjugateTest
        (monotonePrimeAtomInnerAggregateOrthogonalResidual parent k S) =
      monotonePrimeAtomInnerAggregateOrthogonalResidual parent k S := by
  have hstar (a : ℝ) : starRingEnd ℂ (a : ℂ) = (a : ℂ) := by
    rw [starRingEnd_apply, Complex.star_def, Complex.conj_ofReal]
  unfold monotonePrimeAtomInnerAggregateOrthogonalResidual
  simp only [bombieriConjugateTest_add,
    bombieriConjugateTest_smul, hstar,
    bombieriConjugateTest_monotoneQuarterCutoff parent hparent (k + 1),
    bombieriConjugateTest_monotonePrimeAtomAggregateSlice parent hparent k S]

/-- Therefore any minor failure for a conjugation-fixed common parent gives
a genuine conjugation-fixed negative Bombieri test, namely the explicitly
constructed inner residual itself. -/
theorem exists_conjugationFixed_negativeBombieriTest_of_innerAggregateMinor_failure
    (parent : BombieriTest)
    (hparent : bombieriConjugateTest parent = parent)
    (k : ℤ) (S : Finset ℕ)
    (hT : 0 < monotonePrimeAtomAggregateReserve parent k S)
    (hfailure :
      bombieriRealQuadraticValue
            (monotoneQuarterCutoff parent (k + 1)) *
          monotonePrimeAtomAggregateReserve parent k S <
        monotonePrimeAtomInnerSuffixAggregateCross parent k S ^ 2) :
    ∃ g : BombieriTest,
      bombieriConjugateTest g = g ∧ bombieriRealQuadraticValue g < 0 := by
  refine ⟨monotonePrimeAtomInnerAggregateOrthogonalResidual parent k S,
    bombieriConjugateTest_monotonePrimeAtomInnerAggregateOrthogonalResidual
      parent hparent k S, ?_⟩
  exact
    monotonePrimeAtomInnerAggregateOrthogonalResidual_quadratic_negative_of_minor_failure
      parent k S hT hfailure

private theorem realRatioTwo_criticalLogEnergy_le_quadraticValue
    (g : BombieriTest)
    (hcell : BombieriRatioTwoCell g)
    (hreal : bombieriConjugateTest g = g) :
    (1 / 12000 : ℝ) * bombieriCriticalLogEnergy g ≤
      bombieriRealQuadraticValue g := by
  have hcoercive :=
    real_ratioTwo_localCriticalForm_re_ge_criticalLogEnergy g hcell hreal
  obtain ⟨a, b, ha, hab, hsupport, hratio⟩ := hcell
  have heq := bombieriFunctional_quadratic_eq_bombieriLocalCriticalForm_le_two
    g ha hab hsupport hratio
  unfold bombieriRealQuadraticValue
  rw [heq]
  exact hcoercive

/-- The presently available separate ratio-two coercivity bounds pay the
head and aggregate critical energies into their complete reserves only with
coefficient `1 / 12000`. -/
theorem monotonePrimeAtom_head_aggregate_criticalLogEnergy_le_reserves
    (parent : BombieriTest)
    (hparent : bombieriConjugateTest parent = parent)
    (k : ℤ) (S : Finset ℕ) :
    (1 / 12000 : ℝ) *
          bombieriCriticalLogEnergy (monotoneQuarterCell parent k) ≤
        bombieriRealQuadraticValue (monotoneQuarterCell parent k) ∧
      (1 / 12000 : ℝ) *
          bombieriCriticalLogEnergy
            (monotonePrimeAtomAggregateSlice parent k S) ≤
        monotonePrimeAtomAggregateReserve parent k S := by
  constructor
  · exact realRatioTwo_criticalLogEnergy_le_quadraticValue
      (monotoneQuarterCell parent k)
      (monotoneQuarterCell_ratioTwo parent k)
      (bombieriConjugateTest_monotoneQuarterCell parent hparent k)
  · unfold monotonePrimeAtomAggregateReserve
    exact realRatioTwo_criticalLogEnergy_le_quadraticValue
      (monotonePrimeAtomAggregateSlice parent k S)
      (monotoneRatioTwoBlock_ratioTwo _ (k - 1))
      (bombieriConjugateTest_monotonePrimeAtomAggregateSlice
        parent hparent k S)

/-- The complete aggregate cross is the new physical zero-lag prime-row
coordinate plus exactly the already-defined translated-kernel remainder. -/
theorem monotonePrimeAtomAggregateCross_re_eq_zeroLagOverlap_add_remainder
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ) :
    (monotonePrimeAtomAggregateCross parent k S).re =
      (bombieriDirectedCorrelation
        (monotonePrimeAtomAggregateSlice parent k S)
        (monotoneQuarterCell parent k) 1).re +
      monotonePrimeAtomAggregateRemainder parent k S := by
  rw [← monotonePrimeAtom_finset_sum_eq_aggregate_zeroLagOverlap]
  unfold monotonePrimeAtomAggregateRemainder
  ring

/-- Exact coefficient-one defect between the physical prime-row coordinate
and the complete cross controlled by the ratio-two determinant.  No norm
inequality is lost here: the whole deficit is the signed remainder-alignment
product on the right. -/
theorem monotonePrimeAtom_zeroLag_sq_sub_aggregateCross_re_sq
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ) :
    (bombieriDirectedCorrelation
        (monotonePrimeAtomAggregateSlice parent k S)
        (monotoneQuarterCell parent k) 1).re ^ 2 -
      (monotonePrimeAtomAggregateCross parent k S).re ^ 2 =
        -monotonePrimeAtomAggregateRemainder parent k S *
          (2 *
              (bombieriDirectedCorrelation
                (monotonePrimeAtomAggregateSlice parent k S)
                (monotoneQuarterCell parent k) 1).re +
            monotonePrimeAtomAggregateRemainder parent k S) := by
  rw [monotonePrimeAtomAggregateCross_re_eq_zeroLagOverlap_add_remainder]
  ring

/-- Alignment is stronger than necessary when the complete determinant has
slack.  The exact weakest coefficient-one condition along the Mangoldt
weight vector is that the signed defect cost fit inside that unused complete
determinant slack.  This statement is an equivalence, with no analytic
inequality discarded. -/
theorem monotonePrimeAtom_finset_sum_sq_le_reserves_iff_remainderCost_le_completeSlack
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ) :
    (∑ j ∈ S, monotonePrimeAtomValue parent k j) ^ 2 ≤
        bombieriRealQuadraticValue (monotoneQuarterCell parent k) *
          monotonePrimeAtomAggregateReserve parent k S ↔
      -monotonePrimeAtomAggregateRemainder parent k S *
          (2 * (∑ j ∈ S, monotonePrimeAtomValue parent k j) +
            monotonePrimeAtomAggregateRemainder parent k S) ≤
        bombieriRealQuadraticValue (monotoneQuarterCell parent k) *
            monotonePrimeAtomAggregateReserve parent k S -
          (monotonePrimeAtomAggregateCross parent k S).re ^ 2 := by
  let P : ℝ := ∑ j ∈ S, monotonePrimeAtomValue parent k j
  let C : ℝ := (monotonePrimeAtomAggregateCross parent k S).re
  let H : ℝ := bombieriRealQuadraticValue (monotoneQuarterCell parent k)
  let T : ℝ := monotonePrimeAtomAggregateReserve parent k S
  change P ^ 2 ≤ H * T ↔
    -(C - P) * (2 * P + (C - P)) ≤ H * T - C ^ 2
  constructor <;> intro h <;> nlinarith

/-- Thus the existing complete ratio-two determinant gives the desired
coefficient-one reserve bound for the whole prime row exactly after a signed
alignment estimate for the translated-kernel remainder. -/
theorem monotonePrimeAtom_finset_sum_sq_le_reserves_of_remainderAlignment
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ)
    (halign :
      0 ≤ monotonePrimeAtomAggregateRemainder parent k S *
        (2 * (∑ j ∈ S, monotonePrimeAtomValue parent k j) +
          monotonePrimeAtomAggregateRemainder parent k S)) :
    (∑ j ∈ S, monotonePrimeAtomValue parent k j) ^ 2 ≤
      bombieriRealQuadraticValue (monotoneQuarterCell parent k) *
        monotonePrimeAtomAggregateReserve parent k S := by
  have hcrossRe :
      (monotonePrimeAtomAggregateCross parent k S).re ^ 2 ≤
        Complex.normSq (monotonePrimeAtomAggregateCross parent k S) := by
    simp only [Complex.normSq_apply]
    nlinarith [sq_nonneg
      (monotonePrimeAtomAggregateCross parent k S).im]
  have hdet := monotonePrimeAtom_aggregateCross_determinant parent k S
  have hcomplete :
      (monotonePrimeAtomAggregateCross parent k S).re ^ 2 ≤
        bombieriRealQuadraticValue (monotoneQuarterCell parent k) *
          monotonePrimeAtomAggregateReserve parent k S :=
    hcrossRe.trans hdet
  have hdefect :
      (∑ j ∈ S, monotonePrimeAtomValue parent k j) ^ 2 -
          (monotonePrimeAtomAggregateCross parent k S).re ^ 2 =
        -monotonePrimeAtomAggregateRemainder parent k S *
          (2 * (∑ j ∈ S, monotonePrimeAtomValue parent k j) +
            monotonePrimeAtomAggregateRemainder parent k S) := by
    rw [monotonePrimeAtom_finset_sum_eq_aggregate_zeroLagOverlap]
    exact monotonePrimeAtom_zeroLag_sq_sub_aggregateCross_re_sq
      parent k S
  nlinarith

/-- The determinant, physical Cauchy bound, exact cross decomposition, and
both currently available `1 / 12000` reserve coercivities do not force the
remainder-alignment sign.  This fixed scalar model also violates the desired
coefficient-one reserve bound, so a proof must control the remainder jointly
or introduce another coordinate; separate energy coercivity cannot close it. -/
theorem aggregate_zeroLag_knownData_allow_remainder_misalignment :
    ∃ H T C P R EH ET : ℝ,
      0 ≤ H ∧ 0 ≤ T ∧ 0 ≤ EH ∧ 0 ≤ ET ∧
      C = P + R ∧
      C ^ 2 ≤ H * T ∧
      P ^ 2 ≤ EH * ET ∧
      (1 / 12000 : ℝ) * EH ≤ H ∧
      (1 / 12000 : ℝ) * ET ≤ T ∧
      R * (2 * P + R) < 0 ∧
      H * T < P ^ 2 := by
  refine ⟨1, 1, 0, 2, -2, 2, 2, ?_⟩
  norm_num

/-! ## Localizing the physical cost to the head window -/

/-- Only the part of the aggregate slice on the physical support window of
the head can contribute to the zero-lag overlap. -/
def monotonePrimeAtomAggregateHeadWindowEnergy
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ) : ℝ :=
  ∫ x : ℝ in Set.Icc (quarterLogLatticePoint k)
      (quarterLogLatticePoint (k + 2)),
    ‖monotonePrimeAtomAggregateSlice parent k S x‖ ^ 2

private theorem aggregateWindow_normSq_integral_star_mul_le
    {α : Type*} [MeasurableSpace α] (mu : Measure α)
    (F G : α → ℂ)
    (hFmeas : AEStronglyMeasurable F mu)
    (hGmeas : AEStronglyMeasurable G mu)
    (hFsq : Integrable (fun x ↦ ‖F x‖ ^ 2) mu)
    (hGsq : Integrable (fun x ↦ ‖G x‖ ^ 2) mu) :
    Complex.normSq (∫ x, starRingEnd ℂ (F x) * G x ∂mu) ≤
      (∫ x, ‖F x‖ ^ 2 ∂mu) * ∫ x, ‖G x‖ ^ 2 ∂mu := by
  have hFLp : MemLp F 2 mu :=
    (memLp_two_iff_integrable_sq_norm hFmeas).2 hFsq
  have hGLp : MemLp G 2 mu :=
    (memLp_two_iff_integrable_sq_norm hGmeas).2 hGsq
  have hholder := integral_mul_norm_le_Lp_mul_Lq
    (p := 2) (q := 2) (f := F) (g := G) (μ := mu)
    Real.HolderConjugate.two_two (by simpa using hFLp) (by simpa using hGLp)
  let A : ℝ := ∫ x, ‖F x‖ ^ 2 ∂mu
  let B : ℝ := ∫ x, ‖G x‖ ^ 2 ∂mu
  have hA0 : 0 ≤ A := integral_nonneg fun _ ↦ sq_nonneg _
  have hB0 : 0 ≤ B := integral_nonneg fun _ ↦ sq_nonneg _
  have hholder' :
      (∫ x, ‖F x‖ * ‖G x‖ ∂mu) ≤ Real.sqrt A * Real.sqrt B := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    simpa only [A, B, Real.rpow_two] using hholder
  have hnorm :
      ‖∫ x, starRingEnd ℂ (F x) * G x ∂mu‖ ≤
        ∫ x, ‖F x‖ * ‖G x‖ ∂mu := by
    calc
      ‖∫ x, starRingEnd ℂ (F x) * G x ∂mu‖ ≤
          ∫ x, ‖starRingEnd ℂ (F x) * G x‖ ∂mu :=
        norm_integral_le_integral_norm _
      _ = ∫ x, ‖F x‖ * ‖G x‖ ∂mu := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [norm_mul, Complex.norm_conj]
  have hbound := hnorm.trans hholder'
  rw [Complex.normSq_eq_norm_sq]
  calc
    ‖∫ x, starRingEnd ℂ (F x) * G x ∂mu‖ ^ 2 ≤
        (Real.sqrt A * Real.sqrt B) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hbound
    _ = A * B := by
      rw [mul_pow, Real.sq_sqrt hA0, Real.sq_sqrt hB0]
    _ = _ := rfl

private theorem monotoneQuarterCell_headWindowEnergy_eq_criticalLogEnergy
    (parent : BombieriTest) (k : ℤ) :
    (∫ x : ℝ in Set.Icc (quarterLogLatticePoint k)
        (quarterLogLatticePoint (k + 2)),
      ‖monotoneQuarterCell parent k x‖ ^ 2) =
      bombieriCriticalLogEnergy (monotoneQuarterCell parent k) := by
  rw [bombieriCriticalLogEnergy_eq_integral_Ioi_norm_sq]
  symm
  apply setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi
  · intro x hx
    exact (quarterLogLatticePoint_pos k).trans_le hx.1
  · intro x hx
    have hzero : monotoneQuarterCell parent k x = 0 := by
      by_contra hne
      exact hx.2 (monotoneQuarterCell_tsupport_subset parent k
        (subset_tsupport _ (Function.mem_support.mpr hne)))
    rw [hzero, norm_zero]
    norm_num

private theorem aggregate_zeroLag_eq_headWindowIntegral
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ) :
    bombieriDirectedCorrelation
        (monotonePrimeAtomAggregateSlice parent k S)
        (monotoneQuarterCell parent k) 1 =
      ∫ x : ℝ in Set.Icc (quarterLogLatticePoint k)
          (quarterLogLatticePoint (k + 2)),
        monotonePrimeAtomAggregateSlice parent k S x *
          starRingEnd ℂ (monotoneQuarterCell parent k x) := by
  unfold bombieriDirectedCorrelation
  simp only [one_mul]
  apply setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi
  · intro x hx
    exact (quarterLogLatticePoint_pos k).trans_le hx.1
  · intro x hx
    have hzero : monotoneQuarterCell parent k x = 0 := by
      by_contra hne
      exact hx.2 (monotoneQuarterCell_tsupport_subset parent k
        (subset_tsupport _ (Function.mem_support.mpr hne)))
    rw [hzero, map_zero, mul_zero]

/-- Sharp localized Cauchy--Schwarz: the whole finite prime row costs the
head critical energy and only the aggregate mass on the head's two-quarter
window.  No aggregate mass outside the interaction window is charged. -/
theorem monotonePrimeAtom_finset_sum_sq_le_headWindowEnergy
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ) :
    (∑ j ∈ S, monotonePrimeAtomValue parent k j) ^ 2 ≤
      monotonePrimeAtomAggregateHeadWindowEnergy parent k S *
        bombieriCriticalLogEnergy (monotoneQuarterCell parent k) := by
  rw [monotonePrimeAtom_finset_sum_eq_aggregate_zeroLagOverlap]
  let A : BombieriTest := monotonePrimeAtomAggregateSlice parent k S
  let H : BombieriTest := monotoneQuarterCell parent k
  let I : Set ℝ := Set.Icc (quarterLogLatticePoint k)
    (quarterLogLatticePoint (k + 2))
  let mu : Measure ℝ := volume.restrict I
  have hAmeas : AEStronglyMeasurable (fun x : ℝ ↦ A x) mu :=
    A.contDiff.continuous.aestronglyMeasurable.restrict
  have hHmeas : AEStronglyMeasurable (fun x : ℝ ↦ H x) mu :=
    H.contDiff.continuous.aestronglyMeasurable.restrict
  have hAsq : Integrable (fun x : ℝ ↦ ‖A x‖ ^ 2) mu :=
    (A.contDiff.continuous.norm.pow 2).continuousOn.integrableOn_compact
      isCompact_Icc
  have hHsq : Integrable (fun x : ℝ ↦ ‖H x‖ ^ 2) mu :=
    (H.contDiff.continuous.norm.pow 2).continuousOn.integrableOn_compact
      isCompact_Icc
  have hcauchy := aggregateWindow_normSq_integral_star_mul_le
    mu (fun x : ℝ ↦ H x) (fun x : ℝ ↦ A x)
    hHmeas hAmeas hHsq hAsq
  have hcommute :
      (∫ x : ℝ in I, A x * starRingEnd ℂ (H x)) =
        ∫ x : ℝ in I, starRingEnd ℂ (H x) * A x := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro x _hx
    ring
  have hnormSq :
      Complex.normSq
          (bombieriDirectedCorrelation A H 1) ≤
        (∫ x : ℝ in I, ‖H x‖ ^ 2) *
          ∫ x : ℝ in I, ‖A x‖ ^ 2 := by
    rw [show bombieriDirectedCorrelation A H 1 =
        ∫ x : ℝ in I, A x * starRingEnd ℂ (H x) by
      simpa only [A, H, I] using
        aggregate_zeroLag_eq_headWindowIntegral parent k S,
      hcommute]
    simpa only [mu] using hcauchy
  have hre :
      (bombieriDirectedCorrelation A H 1).re ^ 2 ≤
        Complex.normSq (bombieriDirectedCorrelation A H 1) := by
    simp only [Complex.normSq_apply]
    nlinarith [sq_nonneg (bombieriDirectedCorrelation A H 1).im]
  have hbound := hre.trans hnormSq
  rw [monotoneQuarterCell_headWindowEnergy_eq_criticalLogEnergy]
    at hbound
  simpa only [A, H, I, monotonePrimeAtomAggregateHeadWindowEnergy,
    mul_comm] using hbound

/-! ## The exact operator on the interaction window -/

/-- The common ratio-two plateau is identically one throughout the physical
support window of the head, not merely after multiplication by the head
weight. -/
theorem monotonePrimeAtomPlateauMultiplier_eq_one_of_mem_headWindow
    (k : ℤ) {x : ℝ}
    (hx : x ∈ Set.Icc (quarterLogLatticePoint k)
      (quarterLogLatticePoint (k + 2))) :
    monotonePrimeAtomPlateauMultiplier k x = 1 := by
  unfold monotonePrimeAtomPlateauMultiplier
    monotoneRatioTwoBlockMultiplier
  rw [show k - 1 + 3 = k + 2 by omega,
    monotoneQuarterStep_eq_one_of_le (k - 1) (by
      simpa only [show k - 1 + 1 = k by omega] using hx.1),
    monotoneQuarterStep_eq_zero_of_le (k + 2) hx.2]
  ring

private theorem monotoneQuarterCutoff_dilate_eq_parent_of_mem_headWindow
    (parent : BombieriTest) (k : ℤ) {x : ℝ}
    (hx : x ∈ Set.Icc (quarterLogLatticePoint k)
      (quarterLogLatticePoint (k + 2)))
    (j : ℕ) (hj : 1 ≤ j) :
    monotoneQuarterCutoff parent (k + 1)
        (((j + 1 : ℕ) : ℝ) * x) =
      parent (((j + 1 : ℕ) : ℝ) * x) := by
  have hxnonneg : 0 ≤ x :=
    (quarterLogLatticePoint_pos k).le.trans hx.1
  have hjcast : (2 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 2 ≤ j + 1 by omega)
  have hscale :
      quarterLogLatticePoint (k + 2) ≤
        ((j + 1 : ℕ) : ℝ) * x := by
    calc
      quarterLogLatticePoint (k + 2) ≤
          quarterLogLatticePoint (k + 4) :=
        quarterLogLatticePoint_mono (by omega)
      _ = 2 * quarterLogLatticePoint k := by
        rw [quarterLogLatticePoint_add_four]
      _ ≤ 2 * x := mul_le_mul_of_nonneg_left hx.1 (by norm_num)
      _ ≤ ((j + 1 : ℕ) : ℝ) * x :=
        mul_le_mul_of_nonneg_right hjcast hxnonneg
  rw [monotoneQuarterCutoff_apply,
    monotoneQuarterStep_eq_one_of_le (k + 1) (by
      simpa only [show k + 1 + 1 = k + 2 by omega] using hscale)]
  simp

/-- On the head interaction window all auxiliary masks disappear.  The
aggregate slice is exactly the finite von-Mangoldt dilation operator applied
to the original parent. -/
theorem monotonePrimeAtomAggregateSlice_apply_of_mem_headWindow
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc (quarterLogLatticePoint k)
      (quarterLogLatticePoint (k + 2))) :
    monotonePrimeAtomAggregateSlice parent k S x =
      ∑ j ∈ S,
        ((ArithmeticFunction.vonMangoldt (j + 1) : ℝ) : ℂ) *
          parent (((j + 1 : ℕ) : ℝ) * x) := by
  rw [monotonePrimeAtomAggregateSlice_apply,
    monotonePrimeAtomPlateauMultiplier_eq_one_of_mem_headWindow k hx]
  simp only [Complex.ofReal_one, one_mul]
  apply Finset.sum_congr rfl
  intro j _hj
  rcases Nat.eq_zero_or_pos j with rfl | hjpos
  · simp only [Nat.zero_add, ArithmeticFunction.vonMangoldt_apply_one,
      Complex.ofReal_zero, zero_mul]
  · rw [monotoneQuarterCutoff_dilate_eq_parent_of_mem_headWindow
      parent k hx j hjpos]

/-- Hence the localized energy is precisely the `L²` mass, on the head
window, of the finite von-Mangoldt dilation operator.  The remaining transfer
problem is an operator/reserve estimate for this expression; no cutoff or
plateau loss remains hidden in it. -/
theorem monotonePrimeAtomAggregateHeadWindowEnergy_eq_vonMangoldtDilates
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ) :
    monotonePrimeAtomAggregateHeadWindowEnergy parent k S =
      ∫ x : ℝ in Set.Icc (quarterLogLatticePoint k)
          (quarterLogLatticePoint (k + 2)),
        ‖∑ j ∈ S,
          ((ArithmeticFunction.vonMangoldt (j + 1) : ℝ) : ℂ) *
            parent (((j + 1 : ℕ) : ℝ) * x)‖ ^ 2 := by
  unfold monotonePrimeAtomAggregateHeadWindowEnergy
  apply setIntegral_congr_fun measurableSet_Icc
  intro x hx
  change ‖monotonePrimeAtomAggregateSlice parent k S x‖ ^ 2 = _
  rw [monotonePrimeAtomAggregateSlice_apply_of_mem_headWindow
    parent k S hx]

/-- Even after recording the smaller head-window energy, the known separate
estimates do not imply coefficient-one absorption.  In this model the window
mass is only `1 / 36000000` of the full aggregate critical energy, local
Cauchy is sharp, both `1 / 12000` coercivities are sharp, and the desired
reserve product still fails.  Thus the missing input must couple the window
operator to the two complete reserves (or control the exact remainder); a
mere comparison with the full aggregate energy cannot close the route. -/
theorem aggregate_headWindow_knownData_allow_coefficientOne_failure :
    ∃ H T C P R EH EA W : ℝ,
      0 ≤ H ∧ 0 ≤ T ∧ 0 ≤ EH ∧ 0 ≤ EA ∧ 0 ≤ W ∧
      C = P + R ∧
      C ^ 2 ≤ H * T ∧
      P ^ 2 ≤ W * EH ∧
      W ≤ EA ∧
      (1 / 12000 : ℝ) * EH ≤ H ∧
      (1 / 12000 : ℝ) * EA ≤ T ∧
      R * (2 * P + R) < 0 ∧
      H * T < P ^ 2 := by
  refine ⟨1, 1, 0, 2, -2, 12000, 12000, 1 / 3000, ?_⟩
  norm_num

/-! ## The rational-dilation Gram matrix -/

/-- The real local Gram entry between the `m`- and `n`-dilates of the parent
on the head window.  The indices here are the actual positive dilation
factors, rather than the zero-based Mangoldt indices. -/
def monotonePrimeAtomLocalDilationGram
    (parent : BombieriTest) (k : ℤ) (m n : ℕ) : ℝ :=
  ∫ x : ℝ in Set.Icc (quarterLogLatticePoint k)
      (quarterLogLatticePoint (k + 2)),
    (starRingEnd ℂ (parent ((m : ℝ) * x)) *
      parent ((n : ℝ) * x)).re

/-- The local dilation Gram matrix is symmetric. -/
theorem monotonePrimeAtomLocalDilationGram_comm
    (parent : BombieriTest) (k : ℤ) (m n : ℕ) :
    monotonePrimeAtomLocalDilationGram parent k m n =
      monotonePrimeAtomLocalDilationGram parent k n m := by
  unfold monotonePrimeAtomLocalDilationGram
  apply setIntegral_congr_fun measurableSet_Icc
  intro x _hx
  change
    (starRingEnd ℂ (parent ((m : ℝ) * x)) *
      parent ((n : ℝ) * x)).re =
    (starRingEnd ℂ (parent ((n : ℝ) * x)) *
      parent ((m : ℝ) * x)).re
  rw [starRingEnd_apply, Complex.star_def,
    starRingEnd_apply, Complex.star_def]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

private theorem norm_sq_finset_realCombination_eq_gram
    (S : Finset ℕ) (c : ℕ → ℝ) (z : ℕ → ℂ) :
    ‖∑ j ∈ S, ((c j : ℝ) : ℂ) * z j‖ ^ 2 =
      ∑ i ∈ S, ∑ j ∈ S,
        c i * c j * (starRingEnd ℂ (z i) * z j).re := by
  let w : ℂ := ∑ j ∈ S, ((c j : ℝ) : ℂ) * z j
  have hcomplex :
      ((Complex.normSq w : ℝ) : ℂ) =
        ∑ i ∈ S, ∑ j ∈ S,
          (((c j * c i : ℝ) : ℂ) *
            (starRingEnd ℂ (z j) * z i)) := by
    rw [Complex.normSq_eq_conj_mul_self]
    dsimp only [w]
    simp only [map_sum, map_mul, Complex.conj_ofReal,
      Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    apply Finset.sum_congr rfl
    intro j _hj
    push_cast
    ring
  have hre := congrArg Complex.reCLM hcomplex
  have hre' :
      Complex.normSq w =
        ∑ i ∈ S, ∑ j ∈ S,
          c j * c i * (starRingEnd ℂ (z j) * z i).re := by
    simpa only [map_sum Complex.reCLM, Complex.reCLM_apply,
      Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      zero_mul, sub_zero] using hre
  rw [Complex.normSq_eq_norm_sq] at hre'
  change ‖w‖ ^ 2 = _
  calc
    ‖w‖ ^ 2 = ∑ i ∈ S, ∑ j ∈ S,
        c j * c i * (starRingEnd ℂ (z j) * z i).re := hre'
    _ = ∑ i ∈ S, ∑ j ∈ S,
        c i * c j * (starRingEnd ℂ (z i) * z j).re := by
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro j _hj
      have hsym :
          (starRingEnd ℂ (z j) * z i).re =
            (starRingEnd ℂ (z i) * z j).re := by
        rw [starRingEnd_apply, Complex.star_def,
          starRingEnd_apply, Complex.star_def]
        simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
        ring
      rw [hsym]
      ring

private theorem monotonePrimeAtomLocalDilationGram_integrable
    (parent : BombieriTest) (k : ℤ) (m n : ℕ) :
    IntegrableOn
      (fun x : ℝ ↦
        (starRingEnd ℂ (parent ((m : ℝ) * x)) *
          parent ((n : ℝ) * x)).re)
      (Set.Icc (quarterLogLatticePoint k)
        (quarterLogLatticePoint (k + 2))) := by
  have hcont : Continuous (fun x : ℝ ↦
      (starRingEnd ℂ (parent ((m : ℝ) * x)) *
        parent ((n : ℝ) * x)).re) := by
    fun_prop
  exact hcont.continuousOn.integrableOn_compact isCompact_Icc

/-- Exact Gram expansion of the localized Mangoldt operator.  All
off-diagonal interactions are retained as rational-dilation overlaps; no
absolute values or atom-count estimate has been introduced. -/
theorem monotonePrimeAtomAggregateHeadWindowEnergy_eq_dilationGram
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ) :
    monotonePrimeAtomAggregateHeadWindowEnergy parent k S =
      ∑ i ∈ S, ∑ j ∈ S,
        (ArithmeticFunction.vonMangoldt (i + 1) : ℝ) *
          (ArithmeticFunction.vonMangoldt (j + 1) : ℝ) *
            monotonePrimeAtomLocalDilationGram parent k (i + 1) (j + 1) := by
  rw [monotonePrimeAtomAggregateHeadWindowEnergy_eq_vonMangoldtDilates]
  let I : Set ℝ := Set.Icc (quarterLogLatticePoint k)
    (quarterLogLatticePoint (k + 2))
  let c : ℕ → ℝ := fun j ↦ ArithmeticFunction.vonMangoldt (j + 1)
  let z : ℕ → ℝ → ℂ := fun j x ↦ parent (((j + 1 : ℕ) : ℝ) * x)
  have hpoint (x : ℝ) :
      ‖∑ j ∈ S, ((c j : ℝ) : ℂ) * z j x‖ ^ 2 =
        ∑ i ∈ S, ∑ j ∈ S,
          c i * c j * (starRingEnd ℂ (z i x) * z j x).re :=
    norm_sq_finset_realCombination_eq_gram S c (fun j ↦ z j x)
  have hbase (i : ℕ) (_hi : i ∈ S) (j : ℕ) (_hj : j ∈ S) :
      IntegrableOn
        (fun x : ℝ ↦ c i * c j *
          (starRingEnd ℂ (z i x) * z j x).re) I := by
    exact (monotonePrimeAtomLocalDilationGram_integrable
      parent k (i + 1) (j + 1)).const_mul (c i * c j)
  calc
    (∫ x : ℝ in I,
        ‖∑ j ∈ S, ((c j : ℝ) : ℂ) * z j x‖ ^ 2) =
        ∫ x : ℝ in I, ∑ i ∈ S, ∑ j ∈ S,
          c i * c j * (starRingEnd ℂ (z i x) * z j x).re := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro x _hx
      exact hpoint x
    _ = ∑ i ∈ S, ∑ j ∈ S,
        ∫ x : ℝ in I, c i * c j *
          (starRingEnd ℂ (z i x) * z j x).re := by
      rw [MeasureTheory.integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro i hi
        rw [MeasureTheory.integral_finset_sum]
        intro j hj
        exact hbase i hi j hj
      · intro i hi
        exact integrable_finset_sum S fun j hj ↦ hbase i hi j hj
    _ = ∑ i ∈ S, ∑ j ∈ S,
        c i * c j * monotonePrimeAtomLocalDilationGram
          parent k (i + 1) (j + 1) := by
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro j _hj
      rw [MeasureTheory.integral_const_mul]
      rfl
    _ = _ := by
      rfl

/-- Every finite real quadratic form of the local dilation Gram is exactly
the squared `L²` norm of the corresponding coherent dilation sum. -/
theorem monotonePrimeAtomLocalDilationGram_quadratic_eq_integral
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ) (c : ℕ → ℝ) :
    (∑ i ∈ S, ∑ j ∈ S,
        c i * c j * monotonePrimeAtomLocalDilationGram parent k i j) =
      ∫ x : ℝ in Set.Icc (quarterLogLatticePoint k)
          (quarterLogLatticePoint (k + 2)),
        ‖∑ j ∈ S, ((c j : ℝ) : ℂ) * parent ((j : ℝ) * x)‖ ^ 2 := by
  let I : Set ℝ := Set.Icc (quarterLogLatticePoint k)
    (quarterLogLatticePoint (k + 2))
  let z : ℕ → ℝ → ℂ := fun j x ↦ parent ((j : ℝ) * x)
  have hpoint (x : ℝ) :
      ‖∑ j ∈ S, ((c j : ℝ) : ℂ) * z j x‖ ^ 2 =
        ∑ i ∈ S, ∑ j ∈ S,
          c i * c j * (starRingEnd ℂ (z i x) * z j x).re :=
    norm_sq_finset_realCombination_eq_gram S c (fun j ↦ z j x)
  have hbase (i : ℕ) (_hi : i ∈ S) (j : ℕ) (_hj : j ∈ S) :
      IntegrableOn
        (fun x : ℝ ↦ c i * c j *
          (starRingEnd ℂ (z i x) * z j x).re) I := by
    exact (monotonePrimeAtomLocalDilationGram_integrable
      parent k i j).const_mul (c i * c j)
  calc
    (∑ i ∈ S, ∑ j ∈ S,
        c i * c j * monotonePrimeAtomLocalDilationGram parent k i j) =
        ∑ i ∈ S, ∑ j ∈ S,
          ∫ x : ℝ in I, c i * c j *
            (starRingEnd ℂ (z i x) * z j x).re := by
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro j _hj
      rw [MeasureTheory.integral_const_mul]
      rfl
    _ = ∫ x : ℝ in I, ∑ i ∈ S, ∑ j ∈ S,
        c i * c j * (starRingEnd ℂ (z i x) * z j x).re := by
      rw [MeasureTheory.integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro i hi
        rw [MeasureTheory.integral_finset_sum]
        intro j hj
        exact hbase i hi j hj
      · intro i hi
        exact integrable_finset_sum S fun j hj ↦ hbase i hi j hj
    _ = ∫ x : ℝ in I,
        ‖∑ j ∈ S, ((c j : ℝ) : ℂ) * z j x‖ ^ 2 := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro x _hx
      exact (hpoint x).symm
    _ = _ := rfl

/-- In particular, every finite principal Gram quadratic is nonnegative. -/
theorem monotonePrimeAtomLocalDilationGram_posSemidefinite
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ) (c : ℕ → ℝ) :
    0 ≤ ∑ i ∈ S, ∑ j ∈ S,
      c i * c j * monotonePrimeAtomLocalDilationGram parent k i j := by
  rw [monotonePrimeAtomLocalDilationGram_quadratic_eq_integral]
  exact integral_nonneg fun _x ↦ sq_nonneg _

/-- A diagonal Gram entry is the local mass of the corresponding dilation. -/
theorem monotonePrimeAtomLocalDilationGram_self
    (parent : BombieriTest) (k : ℤ) (n : ℕ) :
    monotonePrimeAtomLocalDilationGram parent k n n =
      ∫ x : ℝ in Set.Icc (quarterLogLatticePoint k)
          (quarterLogLatticePoint (k + 2)),
        ‖parent ((n : ℝ) * x)‖ ^ 2 := by
  unfold monotonePrimeAtomLocalDilationGram
  apply setIntegral_congr_fun measurableSet_Icc
  intro x _hx
  change (starRingEnd ℂ (parent ((n : ℝ) * x)) *
    parent ((n : ℝ) * x)).re = ‖parent ((n : ℝ) * x)‖ ^ 2
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    starRingEnd_apply, Complex.star_def]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- Primitive overlap after extracting a common positive integer scale `d`
from two dilation indices. -/
def monotonePrimeAtomPrimitiveDilationOverlap
    (parent : BombieriTest) (k : ℤ) (d a b : ℕ) : ℝ :=
  ∫ y : ℝ in Set.Icc
      ((d : ℝ) * quarterLogLatticePoint k)
      ((d : ℝ) * quarterLogLatticePoint (k + 2)),
    (starRingEnd ℂ (parent ((a : ℝ) * y)) *
      parent ((b : ℝ) * y)).re

/-- Exact gcd normalization of every positive-index Gram entry.  Its
off-diagonal direction is the reduced rational pair
`(m / gcd m n, n / gcd m n)`; the common scale contributes only the Jacobian
`1 / gcd m n` and the corresponding dilation of the head window. -/
theorem monotonePrimeAtomLocalDilationGram_eq_gcdPrimitiveOverlap
    (parent : BombieriTest) (k : ℤ) (m n : ℕ)
    (hm : 0 < m) :
    monotonePrimeAtomLocalDilationGram parent k m n =
      (((Nat.gcd m n : ℕ) : ℝ)⁻¹) *
        monotonePrimeAtomPrimitiveDilationOverlap parent k
          (Nat.gcd m n) (m / Nat.gcd m n) (n / Nat.gcd m n) := by
  let d : ℕ := Nat.gcd m n
  let a : ℕ := m / d
  let b : ℕ := n / d
  let I : Set ℝ := Set.Icc (quarterLogLatticePoint k)
    (quarterLogLatticePoint (k + 2))
  let F : ℝ → ℝ := fun y ↦
    (starRingEnd ℂ (parent ((a : ℝ) * y)) *
      parent ((b : ℝ) * y)).re
  have hdNat : 0 < d := by
    exact Nat.gcd_pos_of_pos_left n hm
  have hd : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdNat
  have hdmNat : a * d = m := by
    exact Nat.div_mul_cancel (Nat.gcd_dvd_left m n)
  have hdnNat : b * d = n := by
    exact Nat.div_mul_cancel (Nat.gcd_dvd_right m n)
  have hdm : (a : ℝ) * (d : ℝ) = (m : ℝ) := by
    exact_mod_cast hdmNat
  have hdn : (b : ℝ) * (d : ℝ) = (n : ℝ) := by
    exact_mod_cast hdnNat
  have hscale := Measure.setIntegral_comp_smul_of_pos
    volume F I hd
  have hscale' :
      (∫ x : ℝ in I, F ((d : ℝ) * x)) =
        ((d : ℝ)⁻¹) *
          ∫ y : ℝ in Set.Icc
            ((d : ℝ) * quarterLogLatticePoint k)
            ((d : ℝ) * quarterLogLatticePoint (k + 2)), F y := by
    dsimp only [I] at hscale
    rw [LinearOrderedField.smul_Icc hd] at hscale
    simpa only [smul_eq_mul, Module.finrank_self, pow_one] using hscale
  change
    (∫ x : ℝ in I,
      (starRingEnd ℂ (parent ((m : ℝ) * x)) *
        parent ((n : ℝ) * x)).re) = _
  calc
    (∫ x : ℝ in I,
      (starRingEnd ℂ (parent ((m : ℝ) * x)) *
        parent ((n : ℝ) * x)).re) =
        ∫ x : ℝ in I, F ((d : ℝ) * x) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro x _hx
      dsimp only [F]
      rw [← mul_assoc, hdm, ← mul_assoc, hdn]
    _ = ((d : ℝ)⁻¹) *
        ∫ y : ℝ in Set.Icc
          ((d : ℝ) * quarterLogLatticePoint k)
          ((d : ℝ) * quarterLogLatticePoint (k + 2)), F y := hscale'
    _ = _ := rfl

/-- The two dilation indices left after gcd normalization are coprime. -/
theorem monotonePrimeAtom_gcdReducedDilation_coprime
    (m n : ℕ) (hm : 0 < m) :
    Nat.Coprime (m / Nat.gcd m n) (n / Nat.gcd m n) := by
  exact Nat.coprime_div_gcd_div_gcd
    (Nat.gcd_pos_of_pos_left n hm)

/-- Every two rational-dilation coordinates satisfy the sharp principal
minor inequality of the local Gram matrix. -/
theorem monotonePrimeAtomLocalDilationGram_sq_le_diagonal_mul
    (parent : BombieriTest) (k : ℤ) (m n : ℕ) :
    monotonePrimeAtomLocalDilationGram parent k m n ^ 2 ≤
      monotonePrimeAtomLocalDilationGram parent k m m *
        monotonePrimeAtomLocalDilationGram parent k n n := by
  let I : Set ℝ := Set.Icc (quarterLogLatticePoint k)
    (quarterLogLatticePoint (k + 2))
  let mu : Measure ℝ := volume.restrict I
  let F : ℝ → ℂ := fun x ↦ parent ((m : ℝ) * x)
  let G : ℝ → ℂ := fun x ↦ parent ((n : ℝ) * x)
  have hFcont : Continuous F := by
    dsimp only [F]
    fun_prop
  have hGcont : Continuous G := by
    dsimp only [G]
    fun_prop
  have hFmeas : AEStronglyMeasurable F mu :=
    hFcont.aestronglyMeasurable.restrict
  have hGmeas : AEStronglyMeasurable G mu :=
    hGcont.aestronglyMeasurable.restrict
  have hFsq : Integrable (fun x : ℝ ↦ ‖F x‖ ^ 2) mu :=
    (hFcont.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hGsq : Integrable (fun x : ℝ ↦ ‖G x‖ ^ 2) mu :=
    (hGcont.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hcrossInt :
      Integrable (fun x : ℝ ↦ starRingEnd ℂ (F x) * G x) mu := by
    have hcont : Continuous
        (fun x : ℝ ↦ starRingEnd ℂ (F x) * G x) := by
      fun_prop
    exact hcont.continuousOn.integrableOn_compact isCompact_Icc
  have hcauchy :
      Complex.normSq
          (∫ x : ℝ in I, starRingEnd ℂ (F x) * G x) ≤
        (∫ x : ℝ in I, ‖F x‖ ^ 2) *
          ∫ x : ℝ in I, ‖G x‖ ^ 2 := by
    simpa only [mu] using
      aggregateWindow_normSq_integral_star_mul_le
        mu F G hFmeas hGmeas hFsq hGsq
  have hre :
      (∫ x : ℝ in I,
          (starRingEnd ℂ (F x) * G x).re) =
        (∫ x : ℝ in I, starRingEnd ℂ (F x) * G x).re := by
    simpa only [mu] using integral_re hcrossInt
  have hrealSq :
      (∫ x : ℝ in I,
          (starRingEnd ℂ (F x) * G x).re) ^ 2 ≤
        Complex.normSq
          (∫ x : ℝ in I, starRingEnd ℂ (F x) * G x) := by
    rw [hre]
    simp only [Complex.normSq_apply]
    nlinarith [sq_nonneg
      (∫ x : ℝ in I, starRingEnd ℂ (F x) * G x).im]
  rw [monotonePrimeAtomLocalDilationGram_self,
    monotonePrimeAtomLocalDilationGram_self]
  unfold monotonePrimeAtomLocalDilationGram
  simpa only [I, F, G] using hrealSq.trans hcauchy

/-! ## The complete reserve Gram on the same atom indices -/

/-- Complete Bombieri cross Gram of two transplanted atom slices. -/
def monotonePrimeAtomCompleteSliceGram
    (parent : BombieriTest) (k : ℤ) (i j : ℕ) : ℝ :=
  (bombieriTwoBlockGlobalCrossSymbol
    (monotonePrimeAtomTransplantedSlice parent k i)
    (monotonePrimeAtomTransplantedSlice parent k j)).re

/-- The complete slice Gram is symmetric on real coordinates. -/
theorem monotonePrimeAtomCompleteSliceGram_comm
    (parent : BombieriTest) (k : ℤ) (i j : ℕ) :
    monotonePrimeAtomCompleteSliceGram parent k i j =
      monotonePrimeAtomCompleteSliceGram parent k j i := by
  have hswap := congrArg Complex.re
    (bombieriTwoBlockGlobalCrossSymbol_conj_swap
      (monotonePrimeAtomTransplantedSlice parent k i)
      (monotonePrimeAtomTransplantedSlice parent k j))
  simpa only [monotonePrimeAtomCompleteSliceGram,
    Complex.star_def, Complex.conj_re] using hswap.symm

private theorem completeCross_finset_sum_right_re
    (f : BombieriTest) (S : Finset ℕ)
    (c : ℕ → ℝ) (g : ℕ → BombieriTest) :
    (bombieriTwoBlockGlobalCrossSymbol f
      (∑ j ∈ S, ((c j : ℝ) : ℂ) • g j)).re =
      ∑ j ∈ S, c j *
        (bombieriTwoBlockGlobalCrossSymbol f (g j)).re := by
  induction S using Finset.induction_on with
  | empty =>
      simp [bombieriTwoBlockGlobalCrossSymbol_zero_right]
  | @insert j S hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj,
        bombieriTwoBlockGlobalCrossSymbol_add_right,
        bombieriTwoBlockGlobalCrossSymbol_smul_right,
        Complex.add_re, ih]
      simp only [Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]

private theorem completeCross_finset_sum_both_re
    (S : Finset ℕ) (c : ℕ → ℝ)
    (f : ℕ → BombieriTest) :
    (bombieriTwoBlockGlobalCrossSymbol
      (∑ i ∈ S, ((c i : ℝ) : ℂ) • f i)
      (∑ j ∈ S, ((c j : ℝ) : ℂ) • f j)).re =
      ∑ i ∈ S, ∑ j ∈ S, c i * c j *
        (bombieriTwoBlockGlobalCrossSymbol (f i) (f j)).re := by
  let F : BombieriTest :=
    ∑ i ∈ S, ((c i : ℝ) : ℂ) • f i
  have hswap (i : ℕ) :
      (bombieriTwoBlockGlobalCrossSymbol F (f i)).re =
        (bombieriTwoBlockGlobalCrossSymbol (f i) F).re := by
    have h := congrArg Complex.re
      (bombieriTwoBlockGlobalCrossSymbol_conj_swap (f i) F)
    simpa only [Complex.star_def, Complex.conj_re] using h
  change (bombieriTwoBlockGlobalCrossSymbol F F).re = _
  rw [completeCross_finset_sum_right_re]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [hswap, completeCross_finset_sum_right_re, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  ring

/-- The complete aggregate reserve is exactly the Mangoldt-weighted
quadratic of the complete slice Gram.  This is the second Hermitian form on
the same atom index set as the physical dilation Gram. -/
theorem monotonePrimeAtomAggregateReserve_eq_completeSliceGram
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ) :
    monotonePrimeAtomAggregateReserve parent k S =
      ∑ i ∈ S, ∑ j ∈ S,
        bombieriLogPrimeAtomWeight i * bombieriLogPrimeAtomWeight j *
          monotonePrimeAtomCompleteSliceGram parent k i j := by
  unfold monotonePrimeAtomAggregateReserve bombieriRealQuadraticValue
  rw [← bombieriTwoBlockGlobalCrossSymbol_self,
    monotonePrimeAtomAggregateSlice_eq_sum]
  simpa only [monotonePrimeAtomCompleteSliceGram] using
    completeCross_finset_sum_both_re S bombieriLogPrimeAtomWeight
      (monotonePrimeAtomTransplantedSlice parent k)

/-- Physical head coordinate of one unweighted transplanted slice. -/
def monotonePrimeAtomPhysicalHeadSliceCoordinate
    (parent : BombieriTest) (k : ℤ) (j : ℕ) : ℝ :=
  (bombieriDirectedCorrelation
    (monotonePrimeAtomTransplantedSlice parent k j)
    (monotoneQuarterCell parent k) 1).re

/-- The finite prime row is the Mangoldt-weighted pairing of the physical
head vector with the transplanted-slice family. -/
theorem monotonePrimeAtom_finset_sum_eq_physicalHeadSliceCoordinates
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ) :
    ∑ j ∈ S, monotonePrimeAtomValue parent k j =
      ∑ j ∈ S, bombieriLogPrimeAtomWeight j *
        monotonePrimeAtomPhysicalHeadSliceCoordinate parent k j := by
  rw [monotonePrimeAtom_finset_sum_eq_aggregate_zeroLagOverlap,
    monotonePrimeAtomAggregateSlice_eq_sum,
    aggregateDirectedCorrelation_finset_sum_left]
  change
    Complex.reCLM
        (∑ j ∈ S,
          bombieriDirectedCorrelation
            (((bombieriLogPrimeAtomWeight j : ℝ) : ℂ) •
              monotonePrimeAtomTransplantedSlice parent k j)
            (monotoneQuarterCell parent k) 1) = _
  rw [map_sum Complex.reCLM]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [bombieriDirectedCorrelation_smul_left]
  simp only [Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero,
    monotonePrimeAtomPhysicalHeadSliceCoordinate]

/-- Arbitrary real linear combination of the transplanted slice family. -/
def monotonePrimeAtomCompleteSliceCombination
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ)
    (c : ℕ → ℝ) : BombieriTest :=
  ∑ j ∈ S, ((c j : ℝ) : ℂ) •
    monotonePrimeAtomTransplantedSlice parent k j

private theorem completeSliceCombination_tsupport_subset
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ)
    (c : ℕ → ℝ) :
    tsupport (monotonePrimeAtomCompleteSliceCombination parent k S c) ⊆
      Set.Icc (quarterLogLatticePoint (k - 1))
        (quarterLogLatticePoint (k + 3)) := by
  unfold monotonePrimeAtomCompleteSliceCombination
  induction S using Finset.induction_on with
  | empty => simp
  | @insert j S hj ih =>
      rw [Finset.sum_insert hj]
      apply (tsupport_add _ _).trans
      apply Set.union_subset
      · exact (tsupport_smul_subset_right
          (fun _x : ℝ ↦ ((c j : ℝ) : ℂ))
          (monotonePrimeAtomTransplantedSlice parent k j : ℝ → ℂ)).trans
          (by
            simpa only [monotonePrimeAtomTransplantedSlice,
              show k - 1 + 4 = k + 3 by omega] using
              (monotoneRatioTwoBlock_tsupport_subset
                (normalizedDilation ((j + 1 : ℕ) : ℝ) (by positivity)
                  (monotoneQuarterCutoff parent (k + 1))) (k - 1)))
      · exact ih

/-- Every real atom combination remains in the common ratio-two plateau. -/
theorem monotonePrimeAtomCompleteSliceCombination_ratioTwo
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ)
    (c : ℕ → ℝ) :
    BombieriRatioTwoCell
      (monotonePrimeAtomCompleteSliceCombination parent k S c) := by
  refine ⟨quarterLogLatticePoint (k - 1),
    quarterLogLatticePoint (k + 3),
    quarterLogLatticePoint_pos (k - 1),
    quarterLogLatticePoint_mono (by omega),
    completeSliceCombination_tsupport_subset parent k S c, ?_⟩
  rw [show k + 3 = (k - 1) + 4 by omega,
    quarterLogLatticePoint_add_four]
  exact le_of_eq
    (mul_div_cancel_right₀ 2
      (quarterLogLatticePoint_pos (k - 1)).ne')

/-- The quadratic of the complete slice Gram is exactly the complete
Bombieri reserve of the corresponding atom combination. -/
theorem monotonePrimeAtomCompleteSliceGram_quadratic_eq_reserve
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ)
    (c : ℕ → ℝ) :
    (∑ i ∈ S, ∑ j ∈ S,
      c i * c j * monotonePrimeAtomCompleteSliceGram parent k i j) =
        bombieriRealQuadraticValue
          (monotonePrimeAtomCompleteSliceCombination parent k S c) := by
  unfold monotonePrimeAtomCompleteSliceCombination
    bombieriRealQuadraticValue
  rw [← bombieriTwoBlockGlobalCrossSymbol_self]
  simpa only [monotonePrimeAtomCompleteSliceGram] using
    (completeCross_finset_sum_both_re S c
      (monotonePrimeAtomTransplantedSlice parent k)).symm

/-- Consequently the complete slice Gram is positive semidefinite on every
finite atom set. -/
theorem monotonePrimeAtomCompleteSliceGram_posSemidefinite
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ)
    (c : ℕ → ℝ) :
    0 ≤ ∑ i ∈ S, ∑ j ∈ S,
      c i * c j * monotonePrimeAtomCompleteSliceGram parent k i j := by
  rw [monotonePrimeAtomCompleteSliceGram_quadratic_eq_reserve]
  unfold bombieriRealQuadraticValue
  exact bombieriFunctional_quadratic_re_nonneg_of_ratioTwoCell _
    (monotonePrimeAtomCompleteSliceCombination_ratioTwo parent k S c)

/-- Complete head coordinate of one transplanted slice. -/
def monotonePrimeAtomCompleteHeadSliceCoordinate
    (parent : BombieriTest) (k : ℤ) (j : ℕ) : ℝ :=
  (bombieriTwoBlockGlobalCrossSymbol
    (monotoneQuarterCell parent k)
    (monotonePrimeAtomTransplantedSlice parent k j)).re

/-- The complete head--aggregate cross is the same Mangoldt weight vector
paired with the complete head-coordinate vector. -/
theorem monotonePrimeAtomAggregateCross_re_eq_completeHeadSliceCoordinates
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ) :
    (monotonePrimeAtomAggregateCross parent k S).re =
      ∑ j ∈ S, bombieriLogPrimeAtomWeight j *
        monotonePrimeAtomCompleteHeadSliceCoordinate parent k j := by
  unfold monotonePrimeAtomAggregateCross
  rw [monotonePrimeAtomAggregateSlice_eq_sum]
  simpa only [monotonePrimeAtomCompleteHeadSliceCoordinate] using
    completeCross_finset_sum_right_re
      (monotoneQuarterCell parent k) S bombieriLogPrimeAtomWeight
      (monotonePrimeAtomTransplantedSlice parent k)

/-- Atom-level defect between the complete head cross and the physical
zero-lag head coordinate. -/
def monotonePrimeAtomHeadCoordinateDefect
    (parent : BombieriTest) (k : ℤ) (j : ℕ) : ℝ :=
  monotonePrimeAtomCompleteHeadSliceCoordinate parent k j -
    monotonePrimeAtomPhysicalHeadSliceCoordinate parent k j

/-- The coordinate defect is not an abstract error term: it is exactly the
common-parent archimedean head--slice row, minus the full symmetric Mangoldt
head--slice row, minus the selected physical zero-lag overlap. -/
theorem monotonePrimeAtomHeadCoordinateDefect_eq_arch_sub_prime_sub_zeroLag
    (parent : BombieriTest) (k : ℤ) (j : ℕ) :
    monotonePrimeAtomHeadCoordinateDefect parent k j =
      bombieriRealLogArchimedeanCross
          (monotoneQuarterCell parent k)
          (monotonePrimeAtomTransplantedSlice parent k j) -
        bombieriRealLogPrimeAtomCross
          (monotoneQuarterCell parent k)
          (monotonePrimeAtomTransplantedSlice parent k j) -
        (bombieriDirectedCorrelation
          (monotonePrimeAtomTransplantedSlice parent k j)
          (monotoneQuarterCell parent k) 1).re := by
  unfold monotonePrimeAtomHeadCoordinateDefect
    monotonePrimeAtomCompleteHeadSliceCoordinate
    monotonePrimeAtomPhysicalHeadSliceCoordinate
  rw [← bombieriCompleteRealLogKernelCross_eq_globalCross_re]
  rfl

/-- Expanding the preceding identity exposes the entire translated Mangoldt
row.  Thus the defect coordinate retains every logarithmic lag; it is not a
finite correction supported on the selected atom index. -/
theorem monotonePrimeAtomHeadCoordinateDefect_eq_arch_sub_fullPrimeRow_sub_zeroLag
    (parent : BombieriTest) (k : ℤ) (j : ℕ) :
    monotonePrimeAtomHeadCoordinateDefect parent k j =
      bombieriRealLogArchimedeanCross
          (monotoneQuarterCell parent k)
          (monotonePrimeAtomTransplantedSlice parent k j) -
        (∑' n : ℕ, bombieriLogPrimeAtomWeight n *
          (bombieriRealLogCorrelation
              (monotoneQuarterCell parent k)
              (monotonePrimeAtomTransplantedSlice parent k j)
              (-Real.log (((n + 1 : ℕ) : ℝ))) +
            bombieriRealLogCorrelation
              (monotoneQuarterCell parent k)
              (monotonePrimeAtomTransplantedSlice parent k j)
              (Real.log (((n + 1 : ℕ) : ℝ))))) -
        (bombieriDirectedCorrelation
          (monotonePrimeAtomTransplantedSlice parent k j)
          (monotoneQuarterCell parent k) 1).re := by
  rw [monotonePrimeAtomHeadCoordinateDefect_eq_arch_sub_prime_sub_zeroLag]
  rfl

/-- After multiplication by its Mangoldt weight, the common-parent
coordinate defect is exactly the atom-level translated-kernel remainder.
This includes the zero-weight index, where both sides vanish. -/
theorem monotonePrimeAtom_weight_mul_headCoordinateDefect_eq_transportRemainder
    (parent : BombieriTest) (k : ℤ) (j : ℕ) :
    bombieriLogPrimeAtomWeight j *
        monotonePrimeAtomHeadCoordinateDefect parent k j =
      monotonePrimeAtomTransportRemainder parent k j := by
  unfold monotonePrimeAtomTransportRemainder
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have hw : bombieriLogPrimeAtomWeight 0 = 0 := by
      simp [bombieriLogPrimeAtomWeight,
        ArithmeticFunction.vonMangoldt_apply_one]
    have hatom : monotonePrimeAtomValue parent k 0 = 0 := by
      unfold monotonePrimeAtomValue bombieriLogPrimeAtomCrossSummand
      rw [hw]
      norm_num
    rw [hw, hatom]
    ring
  · rw [monotonePrimeAtomValue_eq_weight_mul_transplantedOverlap
      parent k j hj]
    unfold monotonePrimeAtomHeadCoordinateDefect
      monotonePrimeAtomCompleteHeadSliceCoordinate
      monotonePrimeAtomPhysicalHeadSliceCoordinate
      monotonePrimeAtomTransportedCross
    ring

/-- The aggregate translated-kernel remainder is exactly the Mangoldt
weight vector paired with the atom-level head-coordinate defect. -/
theorem monotonePrimeAtomAggregateRemainder_eq_headCoordinateDefects
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ) :
    monotonePrimeAtomAggregateRemainder parent k S =
      ∑ j ∈ S, bombieriLogPrimeAtomWeight j *
        monotonePrimeAtomHeadCoordinateDefect parent k j := by
  unfold monotonePrimeAtomAggregateRemainder
    monotonePrimeAtomHeadCoordinateDefect
  rw [monotonePrimeAtomAggregateCross_re_eq_completeHeadSliceCoordinates,
    monotonePrimeAtom_finset_sum_eq_physicalHeadSliceCoordinates]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _hj
  ring

/-- Summing the exact common-parent coordinates gives the aggregate defect
as one weighted archimedean row minus one weighted full Mangoldt row minus
the selected finite physical prime row. -/
theorem monotonePrimeAtomAggregateRemainder_eq_arch_sub_prime_sub_physical
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ) :
    monotonePrimeAtomAggregateRemainder parent k S =
      (∑ j ∈ S, bombieriLogPrimeAtomWeight j *
        bombieriRealLogArchimedeanCross
          (monotoneQuarterCell parent k)
          (monotonePrimeAtomTransplantedSlice parent k j)) -
      (∑ j ∈ S, bombieriLogPrimeAtomWeight j *
        bombieriRealLogPrimeAtomCross
          (monotoneQuarterCell parent k)
          (monotonePrimeAtomTransplantedSlice parent k j)) -
      ∑ j ∈ S, monotonePrimeAtomValue parent k j := by
  rw [monotonePrimeAtomAggregateRemainder_eq_headCoordinateDefects]
  simp_rw [monotonePrimeAtomHeadCoordinateDefect_eq_arch_sub_prime_sub_zeroLag]
  rw [monotonePrimeAtom_finset_sum_eq_physicalHeadSliceCoordinates]
  calc
    (∑ j ∈ S, bombieriLogPrimeAtomWeight j *
      (bombieriRealLogArchimedeanCross
          (monotoneQuarterCell parent k)
          (monotonePrimeAtomTransplantedSlice parent k j) -
        bombieriRealLogPrimeAtomCross
          (monotoneQuarterCell parent k)
          (monotonePrimeAtomTransplantedSlice parent k j) -
        (bombieriDirectedCorrelation
          (monotonePrimeAtomTransplantedSlice parent k j)
          (monotoneQuarterCell parent k) 1).re)) =
        ∑ j ∈ S,
          (bombieriLogPrimeAtomWeight j *
              bombieriRealLogArchimedeanCross
                (monotoneQuarterCell parent k)
                (monotonePrimeAtomTransplantedSlice parent k j) -
            bombieriLogPrimeAtomWeight j *
              bombieriRealLogPrimeAtomCross
                (monotoneQuarterCell parent k)
                (monotonePrimeAtomTransplantedSlice parent k j) -
            bombieriLogPrimeAtomWeight j *
              monotonePrimeAtomPhysicalHeadSliceCoordinate parent k j) := by
          apply Finset.sum_congr rfl
          intro j _hj
          unfold monotonePrimeAtomPhysicalHeadSliceCoordinate
          ring
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]

/-- The head adjoined to an arbitrary real complete-slice combination. -/
def monotonePrimeAtomCompleteHeadSliceCombination
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ)
    (a : ℝ) (c : ℕ → ℝ) : BombieriTest :=
  ((a : ℝ) : ℂ) • monotoneQuarterCell parent k +
    monotonePrimeAtomCompleteSliceCombination parent k S c

/-- The complete augmented head/slice family occupies the same ratio-two
plateau for every real coefficient vector. -/
theorem monotonePrimeAtomCompleteHeadSliceCombination_ratioTwo
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ)
    (a : ℝ) (c : ℕ → ℝ) :
    BombieriRatioTwoCell
      (monotonePrimeAtomCompleteHeadSliceCombination parent k S a c) := by
  refine ⟨quarterLogLatticePoint (k - 1),
    quarterLogLatticePoint (k + 3),
    quarterLogLatticePoint_pos (k - 1),
    quarterLogLatticePoint_mono (by omega), ?_, ?_⟩
  · unfold monotonePrimeAtomCompleteHeadSliceCombination
    apply (tsupport_add _ _).trans
    apply Set.union_subset
    · exact (tsupport_smul_subset_right
        (fun _x : ℝ ↦ ((a : ℝ) : ℂ))
        (monotoneQuarterCell parent k : ℝ → ℂ)).trans
        ((monotoneQuarterCell_tsupport_subset parent k).trans
          (Set.Icc_subset_Icc
            (quarterLogLatticePoint_mono (by omega))
            (quarterLogLatticePoint_mono (by omega))))
    · exact completeSliceCombination_tsupport_subset parent k S c
  · rw [show k + 3 = (k - 1) + 4 by omega,
      quarterLogLatticePoint_add_four]
    exact le_of_eq
      (mul_div_cancel_right₀ 2
        (quarterLogLatticePoint_pos (k - 1)).ne')

/-- Exact quadratic coordinates of the unconditionally positive complete
augmented block `[H qᵀ; q Q]`. -/
theorem monotonePrimeAtomCompleteHeadSliceCombination_quadratic
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ)
    (a : ℝ) (c : ℕ → ℝ) :
    bombieriRealQuadraticValue
        (monotonePrimeAtomCompleteHeadSliceCombination parent k S a c) =
      a ^ 2 * bombieriRealQuadraticValue (monotoneQuarterCell parent k) +
        2 * a * (∑ j ∈ S, c j *
          monotonePrimeAtomCompleteHeadSliceCoordinate parent k j) +
        ∑ i ∈ S, ∑ j ∈ S,
          c i * c j * monotonePrimeAtomCompleteSliceGram parent k i j := by
  let V : BombieriTest :=
    monotonePrimeAtomCompleteSliceCombination parent k S c
  have hquad := aggregateQuadratic_real_linearCombination
    (monotoneQuarterCell parent k) V a 1
  have hcross :
      (bombieriTwoBlockGlobalCrossSymbol
        (monotoneQuarterCell parent k) V).re =
        ∑ j ∈ S, c j *
          monotonePrimeAtomCompleteHeadSliceCoordinate parent k j := by
    dsimp only [V, monotonePrimeAtomCompleteSliceCombination]
    simpa only [monotonePrimeAtomCompleteHeadSliceCoordinate] using
      completeCross_finset_sum_right_re
        (monotoneQuarterCell parent k) S c
        (monotonePrimeAtomTransplantedSlice parent k)
  have hreserve :
      bombieriRealQuadraticValue V =
        ∑ i ∈ S, ∑ j ∈ S,
          c i * c j * monotonePrimeAtomCompleteSliceGram parent k i j := by
    exact (monotonePrimeAtomCompleteSliceGram_quadratic_eq_reserve
      parent k S c).symm
  change bombieriRealQuadraticValue
      (((a : ℝ) : ℂ) • monotoneQuarterCell parent k + V) = _
  rw [hreserve, hcross] at hquad
  have hone : (((1 : ℝ) : ℂ) • V) = V := by norm_num
  rw [hone] at hquad
  rw [hquad]
  ring

/-- Therefore the full complete augmented head/slice Gram is positive
semidefinite for every finite atom set. -/
theorem monotonePrimeAtomCompleteAugmentedGram_posSemidefinite
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ)
    (a : ℝ) (c : ℕ → ℝ) :
    0 ≤
      a ^ 2 * bombieriRealQuadraticValue (monotoneQuarterCell parent k) +
        2 * a * (∑ j ∈ S, c j *
          monotonePrimeAtomCompleteHeadSliceCoordinate parent k j) +
        ∑ i ∈ S, ∑ j ∈ S,
          c i * c j * monotonePrimeAtomCompleteSliceGram parent k i j := by
  rw [← monotonePrimeAtomCompleteHeadSliceCombination_quadratic]
  unfold bombieriRealQuadraticValue
  exact bombieriFunctional_quadratic_re_nonneg_of_ratioTwoCell _
    (monotonePrimeAtomCompleteHeadSliceCombination_ratioTwo
      parent k S a c)

/-- The two unconditional PSD structures do not by themselves survive the
sharp mixed mutation `q ↦ p`.  In this one-atom model the complete augmented
pencil `[H q; q Q]` and the physical augmented pencil `[EH p; p L]` are both
positive semidefinite, both available `1 / 12000` diagonal comparisons hold,
and `R = q - p` is exact.  Nevertheless the hybrid `[H p; p Q]` has negative
determinant.  Hence a proof of the mixed Schur bound must use an additional
common-parent relation between the two forms, equivalently a signed control
of the coordinate defect; the currently proved ratio-two and physical Gram
data do not imply it. -/
theorem mixedAtomGram_currentData_allow_sharpMutationFailure :
    ∃ H Q q EH L p R : ℝ,
      0 ≤ H ∧ 0 ≤ Q ∧ 0 ≤ EH ∧ 0 ≤ L ∧
      (∀ a c : ℝ, 0 ≤ H * a ^ 2 + 2 * q * a * c + Q * c ^ 2) ∧
      (∀ a c : ℝ, 0 ≤ EH * a ^ 2 + 2 * p * a * c + L * c ^ 2) ∧
      (1 / 12000 : ℝ) * EH ≤ H ∧
      (1 / 12000 : ℝ) * L ≤ Q ∧
      R = q - p ∧
      R * (2 * p + R) < 0 ∧
      H * Q < p ^ 2 := by
  refine ⟨1, 1, 0, 4, 1, 2, -2,
    by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_,
    by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · intro a c
    nlinarith [sq_nonneg a, sq_nonneg c]
  · intro a c
    nlinarith [sq_nonneg (2 * a + c)]

/-- Even imposing the exact common-parent coordinate decomposition on the
available scalar data does not turn the two forms into the required
alignment sign.  This production-shaped one-atom model uses the actual first
nonzero Mangoldt weight `w₁`, writes the complete
coordinate as an archimedean row minus a full prime row, writes the defect as
`q - p`, and forms every aggregate coordinate with the same weight `w₁`.
Both the complete and physical pencils are positive semidefinite and the two
available diagonal coercivities hold.  Nevertheless the weighted defect is
anti-aligned and the coefficient-one hybrid determinant fails.  Therefore
the coordinate expansion alone cannot close the route: a successful proof
must establish a new analytic coupling between the archimedean/full-prime
row and the physical zero-lag form, or abandon this hybrid mutation. -/
theorem actualMangoldtWeight_productionCoordinateData_allow_alignmentFailure :
    ∃ w H Q q EH L p A M d P C R T : ℝ,
      w = bombieriLogPrimeAtomWeight 1 ∧ 0 < w ∧
      0 ≤ H ∧ 0 ≤ Q ∧ 0 ≤ EH ∧ 0 ≤ L ∧ 0 ≤ A ∧ 0 ≤ M ∧
      q = A - M ∧ d = q - p ∧
      P = w * p ∧ C = w * q ∧ R = w * d ∧ T = w ^ 2 * Q ∧
      C = P + R ∧
      (∀ a c : ℝ, 0 ≤ H * a ^ 2 + 2 * q * a * c + Q * c ^ 2) ∧
      (∀ a c : ℝ, 0 ≤ EH * a ^ 2 + 2 * p * a * c + L * c ^ 2) ∧
      (1 / 12000 : ℝ) * EH ≤ H ∧
      (1 / 12000 : ℝ) * L ≤ Q ∧
      R * (2 * P + R) < 0 ∧
      H * T - C ^ 2 < -R * (2 * P + R) ∧
      H * T < P ^ 2 := by
  let w : ℝ := bombieriLogPrimeAtomWeight 1
  let u : ℝ := w⁻¹
  have hw : 0 < w := by
    dsimp only [w]
    have hneg := neg_bombieriLogPrimeAtomWeight_one_lt_zero
    linarith
  have hu : 0 < u := by
    exact inv_pos.mpr hw
  have hwu : w * u = 1 := by
    dsimp only [u]
    exact mul_inv_cancel₀ hw.ne'
  refine ⟨w, 1, u ^ 2, 0, 4, u ^ 2, 2 * u, u, u, -2 * u,
    2, 0, -2, 1, rfl, hw, by norm_num, sq_nonneg u, by norm_num,
    sq_nonneg u, hu.le, hu.le, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · ring
  · ring
  · nlinarith
  · ring
  · nlinarith
  · calc
      (1 : ℝ) = (w * u) ^ 2 := by rw [hwu]; norm_num
      _ = w ^ 2 * u ^ 2 := by ring
  · norm_num
  · intro a c
    nlinarith [sq_nonneg a, sq_nonneg (u * c)]
  · intro a c
    nlinarith [sq_nonneg (2 * a + u * c)]
  · norm_num
  · nlinarith [sq_nonneg u]
  · norm_num
  · norm_num
  · norm_num

/-! ## Adjacent ratio-two telescope and its remote-row obstruction -/

private theorem bombieriRealQuadraticValue_threeTerm_overlap_for_telescope
    (left middle right : BombieriTest) :
    bombieriRealQuadraticValue ((left + middle) + right) =
      bombieriRealQuadraticValue (left + middle) +
        bombieriRealQuadraticValue (middle + right) -
          bombieriRealQuadraticValue middle +
        2 * (bombieriTwoBlockGlobalCrossSymbol left right).re := by
  rw [bombieriRealQuadraticValue_add,
    bombieriRealQuadraticValue_add middle right,
    bombieriTwoBlockGlobalCrossSymbol_add_left]
  simp only [Complex.add_re]
  ring

/-- Exact one-step attempt to telescope a finite monotone block through its
adjacent three-cell (hence ratio-two) terminal window.  Besides the previous
prefix, the new local terms are the three-cell window minus its two-cell
overlap.  The sole remaining term is the complete global cross between the
entire remote prefix and the new endpoint cell.

Thus adjacent ratio-two positivity does not close under telescoping: every
extension creates a genuinely nonlocal row rather than a positive overlap
correction. -/
theorem bombieriRealQuadraticValue_finiteBlock_succ_three_eq_adjacentWindow_add_remote
    (parent : BombieriTest) (lo : ℤ) (start n : ℕ) :
    bombieriRealQuadraticValue
        (monotoneQuarterFiniteBlock parent lo start (n + 3)) =
      bombieriRealQuadraticValue
          (monotoneQuarterFiniteBlock parent lo start (n + 2)) +
        bombieriRealQuadraticValue
          (monotoneQuarterFiniteBlock parent lo (start + n) 3) -
        bombieriRealQuadraticValue
          (monotoneQuarterFiniteBlock parent lo (start + n) 2) +
        2 * (bombieriTwoBlockGlobalCrossSymbol
          (monotoneQuarterFiniteBlock parent lo start n)
          (monotoneQuarterFiniteBlock parent lo (start + n + 2) 1)).re := by
  let left := monotoneQuarterFiniteBlock parent lo start n
  let middle := monotoneQuarterFiniteBlock parent lo (start + n) 2
  let right := monotoneQuarterFiniteBlock parent lo (start + n + 2) 1
  have hprefix := monotoneQuarterFiniteBlock_eq_prefix_add_suffix
    parent lo start (n + 2) n (by omega)
  have hwhole := monotoneQuarterFiniteBlock_eq_prefix_add_suffix
    parent lo start (n + 3) (n + 2) (by omega)
  have hwindow := monotoneQuarterFiniteBlock_eq_prefix_add_suffix
    parent lo (start + n) 3 2 (by omega)
  have hleftMiddle : left + middle =
      monotoneQuarterFiniteBlock parent lo start (n + 2) := by
    simpa only [left, middle, Nat.add_sub_cancel_left] using hprefix.symm
  have hmiddleRight : middle + right =
      monotoneQuarterFiniteBlock parent lo (start + n) 3 := by
    simpa only [middle, right, Nat.add_assoc] using hwindow.symm
  have hwhole' : monotoneQuarterFiniteBlock parent lo start (n + 3) =
      (left + middle) + right := by
    rw [hwhole, ← hleftMiddle]
    simp only [right, Nat.add_assoc,
      show n + 3 - (n + 2) = 1 by omega]
  rw [hwhole',
    bombieriRealQuadraticValue_threeTerm_overlap_for_telescope,
    hleftMiddle, hmiddleRight]

/-- Consequently, if a support-minimal negative block has length `n + 3`,
the nonlocal cross created at the last adjacent-window extension must strictly
overcome the previous prefix and terminal three-cell reserves relative to
their two-cell overlap.  This is the exact structural obstruction to a
positive adjacent-block telescope. -/
theorem supportMinimalNegativeMonotoneBlock_terminalRemoteRow_deficit
    {parent : BombieriTest} {lo : ℤ} {total start len n : ℕ}
    (hmin : IsSupportMinimalNegativeMonotoneBlock
      parent lo total start len)
    (hlen : len = n + 3) :
    bombieriRealQuadraticValue
          (monotoneQuarterFiniteBlock parent lo start (n + 2)) +
        bombieriRealQuadraticValue
          (monotoneQuarterFiniteBlock parent lo (start + n) 3) +
        2 * (bombieriTwoBlockGlobalCrossSymbol
          (monotoneQuarterFiniteBlock parent lo start n)
          (monotoneQuarterFiniteBlock parent lo (start + n + 2) 1)).re <
      bombieriRealQuadraticValue
        (monotoneQuarterFiniteBlock parent lo (start + n) 2) := by
  have hnegative : bombieriRealQuadraticValue
      (monotoneQuarterFiniteBlock parent lo start (n + 3)) < 0 := by
    simpa only [hlen] using hmin.negative
  rw [bombieriRealQuadraticValue_finiteBlock_succ_three_eq_adjacentWindow_add_remote]
    at hnegative
  linarith

/-! ## Lag polarization is circular beyond the ratio-two range -/

/-- The cross of two endpoint cells at lag `n + 1` is the mixed second
difference of the four contiguous interval quadratics determined by those
endpoints.  This is the strongest exact lag-polarization telescope.

For `n ≤ 1` all four intervals have at most three cells and ratio-two
positivity applies.  At the first genuinely remote lag, `n = 2`, the leading
term is the four-cell quadratic itself.  Hence solving the remote cross by
this identity is circular; further lag expansion only replaces it by still
longer interval quadratics. -/
theorem two_mul_endpointCellCross_eq_intervalQuadratic_mixedDifference
    (parent : BombieriTest) (lo : ℤ) (start n : ℕ) :
    2 * (bombieriTwoBlockGlobalCrossSymbol
          (monotoneQuarterFiniteBlock parent lo start 1)
          (monotoneQuarterFiniteBlock parent lo (start + n + 1) 1)).re =
      bombieriRealQuadraticValue
          (monotoneQuarterFiniteBlock parent lo start (n + 2)) -
        bombieriRealQuadraticValue
          (monotoneQuarterFiniteBlock parent lo start (n + 1)) -
        bombieriRealQuadraticValue
          (monotoneQuarterFiniteBlock parent lo (start + 1) (n + 1)) +
        bombieriRealQuadraticValue
          (monotoneQuarterFiniteBlock parent lo (start + 1) n) := by
  let left := monotoneQuarterFiniteBlock parent lo start 1
  let middle := monotoneQuarterFiniteBlock parent lo (start + 1) n
  let right := monotoneQuarterFiniteBlock parent lo (start + n + 1) 1
  have hleftMiddleSplit := monotoneQuarterFiniteBlock_eq_prefix_add_suffix
    parent lo start (n + 1) 1 (by omega)
  have hmiddleRightSplit := monotoneQuarterFiniteBlock_eq_prefix_add_suffix
    parent lo (start + 1) (n + 1) n (by omega)
  have hwholeSplit := monotoneQuarterFiniteBlock_eq_prefix_add_suffix
    parent lo start (n + 2) (n + 1) (by omega)
  have hleftMiddle : left + middle =
      monotoneQuarterFiniteBlock parent lo start (n + 1) := by
    simpa only [left, middle, show n + 1 - 1 = n by omega]
      using hleftMiddleSplit.symm
  have hmiddleRight : middle + right =
      monotoneQuarterFiniteBlock parent lo (start + 1) (n + 1) := by
    simpa only [middle, right, Nat.add_assoc, Nat.add_comm 1 n,
      show n + 1 - n = 1 by omega]
      using hmiddleRightSplit.symm
  have hwhole : monotoneQuarterFiniteBlock parent lo start (n + 2) =
      (left + middle) + right := by
    rw [hwholeSplit, ← hleftMiddle]
    simp only [right, Nat.add_assoc,
      show n + 2 - (n + 1) = 1 by omega]
  have hoverlap :=
    bombieriRealQuadraticValue_threeTerm_overlap_for_telescope
      left middle right
  rw [← hwhole, hleftMiddle, hmiddleRight] at hoverlap
  dsimp only [left, middle, right] at hoverlap
  linarith

/-- A finite-coordinate quadratic carrying only one remote corner.  The
parameter `X` is completely invisible on each of the two adjacent
three-coordinate subspaces. -/
def remoteCornerFourCoordinateQuadratic
    (X a b c d : ℝ) : ℝ :=
  a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + 2 * X * a * d

theorem remoteCornerFourCoordinateQuadratic_leftTriple
    (X a b c : ℝ) :
    remoteCornerFourCoordinateQuadratic X a b c 0 =
      a ^ 2 + b ^ 2 + c ^ 2 := by
  unfold remoteCornerFourCoordinateQuadratic
  ring

theorem remoteCornerFourCoordinateQuadratic_rightTriple
    (X b c d : ℝ) :
    remoteCornerFourCoordinateQuadratic X 0 b c d =
      b ^ 2 + c ^ 2 + d ^ 2 := by
  unfold remoteCornerFourCoordinateQuadratic
  ring

/-- Adjacent ratio-two PSD, including every overlap diagonal and every
linear combination inside either adjacent triple, does not control the
remote row.  With remote corner `X = -3`, both local `3 x 3` restrictions
are the identity form, while the all-ones four-coordinate vector is strictly
negative.  Therefore no sum of already-local ratio-two quadratics can recover
the remote cross without an additional nonlocal input. -/
theorem adjacentTriplePSD_and_all_overlapData_allow_negative_remoteCorner :
    ∃ X : ℝ,
      (∀ a b c : ℝ,
        0 ≤ remoteCornerFourCoordinateQuadratic X a b c 0) ∧
      (∀ b c d : ℝ,
        0 ≤ remoteCornerFourCoordinateQuadratic X 0 b c d) ∧
      remoteCornerFourCoordinateQuadratic X 1 1 1 1 < 0 := by
  refine ⟨-3, ?_, ?_, ?_⟩
  · intro a b c
    rw [remoteCornerFourCoordinateQuadratic_leftTriple]
    nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
  · intro b c d
    rw [remoteCornerFourCoordinateQuadratic_rightTriple]
    nlinarith [sq_nonneg b, sq_nonneg c, sq_nonneg d]
  · norm_num [remoteCornerFourCoordinateQuadratic]

/-! ## The all-support remote row as a separated physical operator -/

private theorem tsupport_finset_sum_subset_Icc_for_remoteRow
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → BombieriTest) (a b : ℝ)
    (hf : ∀ i ∈ s, tsupport (f i) ⊆ Set.Icc a b) :
    tsupport (((∑ i ∈ s, f i) : BombieriTest) : ℝ → ℂ) ⊆
      Set.Icc a b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (tsupport_add (f i : ℝ → ℂ)
          (∑ j ∈ s, f j : BombieriTest)).trans
        (union_subset (hf i (by simp))
          (ih (fun j hj ↦ hf j (by simp [hj]))))

/-- The exact support interval of the prefix occurring in the adjacent-block
remote row.  Unlike the ratio-two support lemma, its upper endpoint grows
with the entire prefix length. -/
theorem monotoneQuarterFiniteBlock_remotePrefix_tsupport_subset
    (parent : BombieriTest) (lo : ℤ) (start n : ℕ) :
    tsupport (monotoneQuarterFiniteBlock parent lo start n) ⊆
      Set.Icc
        (quarterLogLatticePoint (lo + (start : ℤ)))
        (quarterLogLatticePoint
          (lo + (start : ℤ) + (n : ℤ) + 1)) := by
  unfold monotoneQuarterFiniteBlock
  apply tsupport_finset_sum_subset_Icc_for_remoteRow
  intro i hi
  have hin : i < n := Finset.mem_range.mp hi
  have hcell := monotoneQuarterCell_tsupport_subset parent
    (lo + ((start + i : ℕ) : ℤ))
  apply hcell.trans
  apply Set.Icc_subset_Icc
  · apply quarterLogLatticePoint_mono
    push_cast
    omega
  · apply quarterLogLatticePoint_mono
    push_cast
    omega

/-- The complete remote prefix--endpoint row has an exact nonlocal physical
representation: a Chebyshev-discrepancy pairing minus the nonsingular
archimedean kernel.  This uses the full prefix at once, not a local-window
expansion.  The adjacent one-quarter support gap discharges strict
separation uniformly for every prefix length. -/
theorem remotePrefixEndpointGlobalCross_eq_chebyshevError_sub_archimedeanKernel
    (parent : BombieriTest) (lo : ℤ) (start n : ℕ) :
    let base : ℤ := lo + (start : ℤ)
    let front := monotoneQuarterFiniteBlock parent lo start n
    let endpoint := monotoneQuarterCell parent (base + (n : ℤ) + 2)
    bombieriTwoBlockGlobalCrossSymbol endpoint front =
      separatedChebyshevErrorPairing endpoint front 1 -
        separatedArchimedeanKernel endpoint front 1 := by
  dsimp only
  let base : ℤ := lo + (start : ℤ)
  let front : BombieriTest :=
    monotoneQuarterFiniteBlock parent lo start n
  let endpoint : BombieriTest :=
    monotoneQuarterCell parent (base + (n : ℤ) + 2)
  have hfront : tsupport front ⊆
      Set.Icc (quarterLogLatticePoint base)
        (quarterLogLatticePoint (base + (n : ℤ) + 1)) := by
    simpa only [front, base, add_assoc] using
      monotoneQuarterFiniteBlock_remotePrefix_tsupport_subset
        parent lo start n
  have hendpoint : tsupport endpoint ⊆
      Set.Icc (quarterLogLatticePoint (base + (n : ℤ) + 2))
        (quarterLogLatticePoint (base + (n : ℤ) + 4)) := by
    simpa only [endpoint, add_assoc] using
      monotoneQuarterCell_tsupport_subset parent (base + (n : ℤ) + 2)
  have hsep :
      quarterLogLatticePoint (base + (n : ℤ) + 1) /
          quarterLogLatticePoint (base + (n : ℤ) + 2) < 1 := by
    apply (div_lt_one
      (quarterLogLatticePoint_pos (base + (n : ℤ) + 2))).2
    exact quarterLogLatticePoint_strictMono (by omega)
  have hrepresentation :=
    sqrt_mul_globalCross_eq_chebyshevError_sub_archimedeanKernel
      endpoint front (by norm_num : (0 : ℝ) < 1)
      (quarterLogLatticePoint_pos (base + (n : ℤ) + 2))
      (quarterLogLatticePoint_pos base)
      (quarterLogLatticePoint_pos (base + (n : ℤ) + 1))
      hendpoint hfront hsep
  simpa only [Real.sqrt_one, Complex.ofReal_one, one_mul,
    normalizedDilation_one, endpoint, front] using hrepresentation

private theorem bombieriCriticalLogEnergy_normalizedDilation_for_remoteRow
    (lambda : ℝ) (hlambda : 0 < lambda) (g : BombieriTest) :
    bombieriCriticalLogEnergy (normalizedDilation lambda hlambda g) =
      bombieriCriticalLogEnergy g := by
  unfold bombieriCriticalLogEnergy
  simp_rw [normalizedDilation_logarithmicPullbackSchwartz_critical]
  simpa only [sub_eq_add_neg] using
    MeasureTheory.integral_add_right_eq_self
      (fun u : ℝ ↦ ‖g.logarithmicPullbackSchwartz (1 / 2) u‖ ^ 2)
      (-Real.log lambda)

/-- Multiplicative correlation is a genuine Hilbert operator between the
critical physical energies.  At lag `x`, its squared norm pays the exact
Jacobian `x⁻¹`; this is the diagonal reserve needed to control an entire
separated correlation row rather than individual local windows. -/
theorem normSq_bombieriDirectedCorrelation_le_inv_mul_criticalLogEnergy
    (f g : BombieriTest) {x : ℝ} (hx : 0 < x) :
    Complex.normSq (bombieriDirectedCorrelation f g x) ≤
      x⁻¹ * bombieriCriticalLogEnergy f *
        bombieriCriticalLogEnergy g := by
  have hcorrelation :
      bombieriDirectedCorrelation
          (normalizedDilation x hx f) g 1 =
        ((Real.sqrt x : ℝ) : ℂ) *
          bombieriDirectedCorrelation f g x := by
    unfold bombieriDirectedCorrelation
    calc
      (∫ y : ℝ in Set.Ioi 0,
          normalizedDilation x hx f (1 * y) *
            starRingEnd ℂ (g y)) =
          ∫ y : ℝ in Set.Ioi 0,
            ((Real.sqrt x : ℝ) : ℂ) *
              (f (x * y) * starRingEnd ℂ (g y)) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro y _hy
        change normalizedDilation x hx f (1 * y) *
            starRingEnd ℂ (g y) =
          ((Real.sqrt x : ℝ) : ℂ) *
            (f (x * y) * starRingEnd ℂ (g y))
        rw [one_mul, normalizedDilation_apply]
        ring
      _ = ((Real.sqrt x : ℝ) : ℂ) *
          ∫ y : ℝ in Set.Ioi 0,
            f (x * y) * starRingEnd ℂ (g y) := by
        exact MeasureTheory.integral_const_mul _ _
  have hlagOne :=
    normSq_bombieriDirectedCorrelation_one_le_criticalLogEnergy_mul
      (normalizedDilation x hx f) g
  rw [hcorrelation, Complex.normSq_mul, Complex.normSq_ofReal,
    bombieriCriticalLogEnergy_normalizedDilation_for_remoteRow] at hlagOne
  have hsqrt : Real.sqrt x * Real.sqrt x = x := by
    nlinarith [Real.sq_sqrt hx.le]
  rw [hsqrt] at hlagOne
  rw [show x⁻¹ * bombieriCriticalLogEnergy f *
      bombieriCriticalLogEnergy g =
        (bombieriCriticalLogEnergy f * bombieriCriticalLogEnergy g) / x by
    field_simp [hx.ne']]
  apply (le_div_iff₀ hx).2
  simpa only [mul_comm] using hlagOne

/-- Norm form of the exact multiplicative Hilbert bound. -/
theorem norm_bombieriDirectedCorrelation_le_inv_sqrt_mul_sqrt_energy
    (f g : BombieriTest) {x : ℝ} (hx : 0 < x) :
    ‖bombieriDirectedCorrelation f g x‖ ≤
      (Real.sqrt x)⁻¹ * Real.sqrt
        (bombieriCriticalLogEnergy f * bombieriCriticalLogEnergy g) := by
  let E : ℝ := bombieriCriticalLogEnergy f * bombieriCriticalLogEnergy g
  have hE : 0 ≤ E := mul_nonneg
    (bombieriCriticalLogEnergy_nonnegative f)
    (bombieriCriticalLogEnergy_nonnegative g)
  have hbase : 0 ≤ x⁻¹ * E :=
    mul_nonneg (inv_nonneg.mpr hx.le) hE
  have hsq :=
    normSq_bombieriDirectedCorrelation_le_inv_mul_criticalLogEnergy
      f g hx
  have hnorm : ‖bombieriDirectedCorrelation f g x‖ ≤
      Real.sqrt (x⁻¹ * E) := by
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [← Complex.normSq_eq_norm_sq, Real.sq_sqrt hbase]
    simpa only [E, mul_assoc] using hsq
  rw [Real.sqrt_mul (inv_nonneg.mpr hx.le), Real.sqrt_inv] at hnorm
  exact hnorm

private theorem separatedChebyshevErrorPairing_one_eq_integral_sub_primeRow
    (f g : BombieriTest) :
    separatedChebyshevErrorPairing f g 1 =
      (∫ x : ℝ in Set.Ioi 0,
        starRingEnd ℂ (bombieriDirectedCorrelation f g x)) -
      ∑' n : ℕ,
        ((ArithmeticFunction.vonMangoldt (n + 1) : ℝ) : ℂ) *
          starRingEnd ℂ
            (bombieriDirectedCorrelation f g (n + 1 : ℕ)) := by
  let H : ℝ → ℂ := fun x ↦
    starRingEnd ℂ (bombieriDirectedCorrelation f g x)
  have habel := scaled_integral_sub_tsum_vonMangoldt_eq_integral_chebyshevError
    H (star_bombieriDirectedCorrelation_contDiff_one f g)
      (star_bombieriDirectedCorrelation_hasCompactSupport f g)
      (by norm_num : (0 : ℝ) < 1)
  simpa only [separatedChebyshevErrorPairing, H, Complex.ofReal_one,
    one_mul, inv_one] using habel.symm

/-- Finite operator mass of the Mangoldt sampling row through index `N`. -/
def bombieriLogPrimeAtomPartialMass (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, bombieriLogPrimeAtomWeight k

/-- Compact support truncates the arithmetic row in the Abel identity at
any natural cutoff beyond the upper physical support quotient. -/
theorem separatedPrimeRow_eq_sum_range_of_support
    (f g : BombieriTest) {af bf ag bg : ℝ}
    (haf : 0 < af) (hag : 0 < ag) (hbg : 0 < bg)
    (hfsupport : tsupport f ⊆ Set.Icc af bf)
    (hgsupport : tsupport g ⊆ Set.Icc ag bg)
    (N : ℕ) (hN : bf / ag < (N : ℝ)) :
    (∑' k : ℕ,
        ((ArithmeticFunction.vonMangoldt (k + 1) : ℝ) : ℂ) *
          starRingEnd ℂ
            (bombieriDirectedCorrelation f g (k + 1 : ℕ))) =
      ∑ k ∈ Finset.range N,
        ((ArithmeticFunction.vonMangoldt (k + 1) : ℝ) : ℂ) *
          starRingEnd ℂ
            (bombieriDirectedCorrelation f g (k + 1 : ℕ)) := by
  rw [tsum_eq_sum]
  intro k hk
  rw [Finset.mem_range] at hk
  have hNk : N ≤ k := Nat.le_of_not_gt hk
  have hcast : (N : ℝ) < (k + 1 : ℕ) := by
    exact_mod_cast hNk.trans_lt (Nat.lt_succ_self k)
  have hupper : bf / ag < (k + 1 : ℕ) := hN.trans hcast
  have hout : ((k + 1 : ℕ) : ℝ) ∉
      Set.Icc (af / bg) (bf / ag) := by
    intro hmem
    exact (not_lt_of_ge hmem.2) hupper
  rw [star_bombieriDirectedCorrelation_eq_zero_outside_supportQuotient
    f g haf hag hbg hfsupport hgsupport hout, mul_zero]

/-- The finite Mangoldt sampling operator has an exact diagonal `L²`
reserve.  Each sample pays its sharp multiplicative Jacobian, producing the
classical half-weight `Λ(m) / sqrt(m)` and no support-length loss. -/
theorem norm_separatedPrimeRow_sum_range_le_partialMass_mul_sqrtEnergy
    (f g : BombieriTest) (N : ℕ) :
    ‖∑ k ∈ Finset.range N,
        ((ArithmeticFunction.vonMangoldt (k + 1) : ℝ) : ℂ) *
          starRingEnd ℂ
            (bombieriDirectedCorrelation f g (k + 1 : ℕ))‖ ≤
      bombieriLogPrimeAtomPartialMass N *
        Real.sqrt
          (bombieriCriticalLogEnergy f * bombieriCriticalLogEnergy g) := by
  calc
    ‖∑ k ∈ Finset.range N,
        ((ArithmeticFunction.vonMangoldt (k + 1) : ℝ) : ℂ) *
          starRingEnd ℂ
            (bombieriDirectedCorrelation f g (k + 1 : ℕ))‖ ≤
      ∑ k ∈ Finset.range N,
        ‖((ArithmeticFunction.vonMangoldt (k + 1) : ℝ) : ℂ) *
          starRingEnd ℂ
            (bombieriDirectedCorrelation f g (k + 1 : ℕ))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range N,
        bombieriLogPrimeAtomWeight k *
          Real.sqrt
            (bombieriCriticalLogEnergy f *
              bombieriCriticalLogEnergy g) := by
      apply Finset.sum_le_sum
      intro k _hk
      have hcorr :=
        norm_bombieriDirectedCorrelation_le_inv_sqrt_mul_sqrt_energy
          f g (show (0 : ℝ) < (k + 1 : ℕ) by positivity)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        starRingEnd_apply, Complex.star_def, Complex.norm_conj,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      calc
        ArithmeticFunction.vonMangoldt (k + 1) *
            ‖bombieriDirectedCorrelation f g (k + 1 : ℕ)‖ ≤
          ArithmeticFunction.vonMangoldt (k + 1) *
            ((Real.sqrt (((k + 1 : ℕ) : ℝ)))⁻¹ *
              Real.sqrt
                (bombieriCriticalLogEnergy f *
                  bombieriCriticalLogEnergy g)) :=
          mul_le_mul_of_nonneg_left hcorr
            ArithmeticFunction.vonMangoldt_nonneg
        _ = bombieriLogPrimeAtomWeight k *
            Real.sqrt
              (bombieriCriticalLogEnergy f *
                bombieriCriticalLogEnergy g) := by
          unfold bombieriLogPrimeAtomWeight
          ring
    _ = bombieriLogPrimeAtomPartialMass N *
        Real.sqrt
          (bombieriCriticalLogEnergy f * bombieriCriticalLogEnergy g) := by
      unfold bombieriLogPrimeAtomPartialMass
      rw [Finset.sum_mul]

/-- Integrating the preceding pointwise Hilbert bound over the exact support
quotient gives a finite all-row reserve.  The coefficient depends only on
the two physical support intervals; the diagonal terms are the actual full
critical energies of `f` and `g`. -/
theorem separatedCorrelationNormMass_le_supportGeometryEnergy
    (f g : BombieriTest) {af bf ag bg : ℝ}
    (haf : 0 < af) (hafbf : af ≤ bf)
    (hag : 0 < ag) (hagbg : ag ≤ bg) (hbg : 0 < bg)
    (hfsupport : tsupport f ⊆ Set.Icc af bf)
    (hgsupport : tsupport g ⊆ Set.Icc ag bg) :
    separatedCorrelationNormMass f g ≤
      (bf / ag - af / bg) *
        Real.sqrt ((af / bg)⁻¹ *
          bombieriCriticalLogEnergy f * bombieriCriticalLogEnergy g) := by
  let L : ℝ := af / bg
  let U : ℝ := bf / ag
  let E : ℝ := (af / bg)⁻¹ *
    bombieriCriticalLogEnergy f * bombieriCriticalLogEnergy g
  have hbf : 0 < bf := haf.trans_le hafbf
  have hL : 0 < L := by
    dsimp only [L]
    exact div_pos haf hbg
  have hU : 0 < U := by
    dsimp only [U]
    exact div_pos hbf hag
  have hLU : L ≤ U := by
    dsimp only [L, U]
    apply (div_le_div_iff₀ hbg hag).2
    calc
      af * ag ≤ bf * ag := mul_le_mul_of_nonneg_right hafbf hag.le
      _ ≤ bf * bg := mul_le_mul_of_nonneg_left hagbg hbf.le
  have hEf : 0 ≤ bombieriCriticalLogEnergy f :=
    bombieriCriticalLogEnergy_nonnegative f
  have hEg : 0 ≤ bombieriCriticalLogEnergy g :=
    bombieriCriticalLogEnergy_nonnegative g
  have hE : 0 ≤ E := by
    dsimp only [E]
    exact mul_nonneg
      (mul_nonneg (inv_nonneg.mpr (div_nonneg haf.le hbg.le)) hEf) hEg
  have hKpos : Set.Icc L U ⊆ Set.Ioi (0 : ℝ) := by
    intro x hx
    exact hL.trans_le hx.1
  have hcorrInt : IntegrableOn
      (fun x : ℝ ↦
        ‖starRingEnd ℂ (bombieriDirectedCorrelation f g x)‖)
      (Set.Ioi 0) :=
    (star_bombieriDirectedCorrelation_integrableOn_Ioi
      f g haf hag hbg hfsupport hgsupport).norm
  have hrestrict : separatedCorrelationNormMass f g =
      ∫ x : ℝ in Set.Icc L U,
        ‖starRingEnd ℂ (bombieriDirectedCorrelation f g x)‖ := by
    unfold separatedCorrelationNormMass
    apply setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi
    · exact hKpos
    · intro x hx
      rw [star_bombieriDirectedCorrelation_eq_zero_outside_supportQuotient
        f g haf hag hbg hfsupport hgsupport hx.2, norm_zero]
  have hpoint (x : ℝ) (hx : x ∈ Set.Icc L U) :
      ‖starRingEnd ℂ (bombieriDirectedCorrelation f g x)‖ ≤
        Real.sqrt E := by
    have hxpos : 0 < x := hL.trans_le hx.1
    have hcorr :=
      normSq_bombieriDirectedCorrelation_le_inv_mul_criticalLogEnergy
        f g hxpos
    have hinv : x⁻¹ ≤ L⁻¹ :=
      (inv_le_inv₀ hxpos hL).2 hx.1
    have henergy :
        x⁻¹ * bombieriCriticalLogEnergy f *
            bombieriCriticalLogEnergy g ≤ E := by
      dsimp only [E, L]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hinv hEf) hEg
    have hsq :
        Complex.normSq (bombieriDirectedCorrelation f g x) ≤ E :=
      hcorr.trans henergy
    rw [starRingEnd_apply, Complex.star_def, Complex.norm_conj]
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg E)).mp
    rw [← Complex.normSq_eq_norm_sq, Real.sq_sqrt hE]
    exact hsq
  have hleftInt : IntegrableOn
      (fun x : ℝ ↦
        ‖starRingEnd ℂ (bombieriDirectedCorrelation f g x)‖)
      (Set.Icc L U) := hcorrInt.mono_set hKpos
  have hrightInt : IntegrableOn (fun _x : ℝ ↦ Real.sqrt E)
      (Set.Icc L U) := integrableOn_const measure_Icc_lt_top.ne
  rw [hrestrict]
  calc
    (∫ x : ℝ in Set.Icc L U,
        ‖starRingEnd ℂ (bombieriDirectedCorrelation f g x)‖) ≤
        ∫ _x : ℝ in Set.Icc L U, Real.sqrt E := by
      apply integral_mono_ae hleftInt hrightInt
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      exact hpoint x hx
    _ = (U - L) * Real.sqrt E := by
      rw [setIntegral_const, Real.volume_real_Icc_of_le hLU]
      simp only [smul_eq_mul]
    _ = (bf / ag - af / bg) *
        Real.sqrt ((af / bg)⁻¹ *
          bombieriCriticalLogEnergy f * bombieriCriticalLogEnergy g) := by
      rfl

/-- Full unconditional all-support bound for the Chebyshev-discrepancy
pairing.  Its continuous part is paid by support geometry, while its exact
finite arithmetic sampling row is paid by the partial half-weight mass
`sum Λ(m) / sqrt(m)`.  Both use the genuine full diagonal energies. -/
theorem norm_separatedChebyshevErrorPairing_one_le_energyReserve
    (f g : BombieriTest) {af bf ag bg : ℝ}
    (haf : 0 < af) (hafbf : af ≤ bf)
    (hag : 0 < ag) (hagbg : ag ≤ bg) (hbg : 0 < bg)
    (hfsupport : tsupport f ⊆ Set.Icc af bf)
    (hgsupport : tsupport g ⊆ Set.Icc ag bg)
    (N : ℕ) (hN : bf / ag < (N : ℝ)) :
    ‖separatedChebyshevErrorPairing f g 1‖ ≤
      (bf / ag - af / bg) *
          Real.sqrt ((af / bg)⁻¹ *
            bombieriCriticalLogEnergy f * bombieriCriticalLogEnergy g) +
        bombieriLogPrimeAtomPartialMass N *
          Real.sqrt
            (bombieriCriticalLogEnergy f *
              bombieriCriticalLogEnergy g) := by
  have hidentity :=
    separatedChebyshevErrorPairing_one_eq_integral_sub_primeRow f g
  have hfinite := separatedPrimeRow_eq_sum_range_of_support
    f g haf hag hbg hfsupport hgsupport N hN
  rw [hfinite] at hidentity
  have hintegral :
      ‖∫ x : ℝ in Set.Ioi 0,
          starRingEnd ℂ (bombieriDirectedCorrelation f g x)‖ ≤
        separatedCorrelationNormMass f g := by
    exact norm_integral_le_integral_norm _
  have hmass := separatedCorrelationNormMass_le_supportGeometryEnergy
    f g haf hafbf hag hagbg hbg hfsupport hgsupport
  have hprime :=
    norm_separatedPrimeRow_sum_range_le_partialMass_mul_sqrtEnergy
      f g N
  rw [hidentity]
  exact (norm_sub_le _ _).trans
    ((add_le_add hintegral hprime).trans
      (add_le_add hmass le_rfl))

/-- The arithmetic coefficient in the unconditional triangle estimate is
already much larger than the available `1 / 12000` local coercivity budget
as soon as the factor-two atom is present.  Thus the Hilbert bound is a true
diagonal reserve, but coefficient-only absorption cannot close the proof;
one must retain cancellation between the continuous and Mangoldt rows. -/
theorem one_over_twelve_thousand_lt_bombieriLogPrimeAtomPartialMass
    (N : ℕ) (hN : 2 ≤ N) :
    (1 / 12000 : ℝ) < bombieriLogPrimeAtomPartialMass N := by
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrtLt : Real.sqrt 2 < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hweight : (1 / 12000 : ℝ) < bombieriLogPrimeAtomWeight 1 := by
    rw [bombieriLogPrimeAtomWeight_one]
    apply (lt_div_iff₀ hsqrt).2
    nlinarith [Real.log_two_gt_d9]
  have honeMem : 1 ∈ Finset.range N := Finset.mem_range.mpr (by omega)
  have honeLe : bombieriLogPrimeAtomWeight 1 ≤
      bombieriLogPrimeAtomPartialMass N := by
    unfold bombieriLogPrimeAtomPartialMass
    exact Finset.single_le_sum
      (fun k _hk ↦ bombieriLogPrimeAtomWeight_nonneg k) honeMem
  exact hweight.trans_le honeLe

/-- The nonsingular part of every strictly separated complete cross has a
true diagonal Hilbert reserve.  Combining the exact kernel denominator with
the all-row correlation estimate bounds it solely by the two full critical
energies and explicit support geometry. -/
theorem norm_separatedArchimedeanKernel_one_le_supportGeometryEnergy
    (f g : BombieriTest) {af bf ag bg : ℝ}
    (haf : 0 < af) (hafbf : af ≤ bf)
    (hag : 0 < ag) (hagbg : ag ≤ bg) (hbg : 0 < bg)
    (hfsupport : tsupport f ⊆ Set.Icc af bf)
    (hgsupport : tsupport g ⊆ Set.Icc ag bg)
    (hsep : bg / af < 1) :
    ‖separatedArchimedeanKernel f g 1‖ ≤
      (af / bg * ((af / bg) ^ 2 - 1))⁻¹ *
        ((bf / ag - af / bg) *
          Real.sqrt ((af / bg)⁻¹ *
            bombieriCriticalLogEnergy f * bombieriCriticalLogEnergy g)) := by
  have hkernel := norm_separatedArchimedeanKernel_le
    f g (by norm_num : (0 : ℝ) < 1) haf hag hbg
      hfsupport hgsupport hsep
  have hmass := separatedCorrelationNormMass_le_supportGeometryEnergy
    f g haf hafbf hag hagbg hbg hfsupport hgsupport
  have hbgaf : bg < af := by
    simpa using (div_lt_iff₀ haf).mp hsep
  have hratio : 1 < af / bg := by
    exact (lt_div_iff₀ hbg).2 (by simpa using hbgaf)
  have hden : 0 < af / bg * ((af / bg) ^ 2 - 1) := by
    exact mul_pos (zero_lt_one.trans hratio)
      (by nlinarith [sq_nonneg (af / bg - 1)])
  have hcoefficient :
      0 ≤ (af / bg * ((af / bg) ^ 2 - 1))⁻¹ :=
    (inv_pos.mpr hden).le
  calc
    ‖separatedArchimedeanKernel f g 1‖ ≤
        (af / bg * ((af / bg) ^ 2 - 1))⁻¹ *
          separatedCorrelationNormMass f g := by
      simpa only [one_mul] using hkernel
    _ ≤ (af / bg * ((af / bg) ^ 2 - 1))⁻¹ *
        ((bf / ag - af / bg) *
          Real.sqrt ((af / bg)⁻¹ *
            bombieriCriticalLogEnergy f *
              bombieriCriticalLogEnergy g)) :=
      mul_le_mul_of_nonneg_left hmass hcoefficient

/-! ## Signed Chebyshev cancellation cannot supply a universal gap -/

/-- The first genuinely remote prefix in the adjacent-block telescope: two
cells at the lower end and the cell four quarter-steps from the base. -/
def remoteTwoPrefix (parent : BombieriTest) (k : ℤ) : BombieriTest :=
  monotoneQuarterFiniteBlock parent k 0 2

/-- The endpoint paired with `remoteTwoPrefix` in the first remote row. -/
def remoteTwoEndpoint (parent : BombieriTest) (k : ℤ) : BombieriTest :=
  monotoneQuarterCell parent (k + 4)

/-- A proposed one-sided diagonal gap extracted from the exact signed
continuous-minus-Mangoldt row. -/
def RemoteTwoPrefixChebyshevEnergyGap
    (c : ℝ) (parent : BombieriTest) (k : ℤ) : Prop :=
  c * (bombieriCriticalLogEnergy (remoteTwoPrefix parent k) +
      bombieriCriticalLogEnergy (remoteTwoEndpoint parent k)) ≤
    (separatedChebyshevErrorPairing
      (remoteTwoEndpoint parent k) (remoteTwoPrefix parent k) 1).re

private theorem separatedChebyshevErrorPairing_one_neg_left
    (f g : BombieriTest) :
    separatedChebyshevErrorPairing (-f) g 1 =
      -separatedChebyshevErrorPairing f g 1 := by
  rw [separatedChebyshevErrorPairing_one_eq_integral_sub_primeRow,
    separatedChebyshevErrorPairing_one_eq_integral_sub_primeRow]
  have hcorr (x : ℝ) :
      starRingEnd ℂ (bombieriDirectedCorrelation (-f) g x) =
        -starRingEnd ℂ (bombieriDirectedCorrelation f g x) := by
    have h := bombieriDirectedCorrelation_smul_left (-1 : ℂ) f g x
    simpa only [neg_smul, one_smul, neg_mul, one_mul, map_neg] using
      congrArg (starRingEnd ℂ) h
  simp_rw [hcorr, mul_neg]
  rw [MeasureTheory.integral_neg, tsum_neg]
  ring

private theorem criticalLogEnergy_neg_for_remoteGap (g : BombieriTest) :
    bombieriCriticalLogEnergy (-g) = bombieriCriticalLogEnergy g := by
  rw [bombieriCriticalLogEnergy_eq_integral_Ioi_norm_sq,
    bombieriCriticalLogEnergy_eq_integral_Ioi_norm_sq]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x _hx
  simp

private theorem monotoneQuarterFiniteBlock_add_for_remoteGap
    (f g : BombieriTest) (lo : ℤ) (start len : ℕ) :
    monotoneQuarterFiniteBlock (f + g) lo start len =
      monotoneQuarterFiniteBlock f lo start len +
        monotoneQuarterFiniteBlock g lo start len := by
  classical
  unfold monotoneQuarterFiniteBlock
  simp_rw [monotoneQuarterCell_add]
  exact Finset.sum_add_distrib

private theorem monotoneQuarterFiniteBlock_neg_for_remoteGap
    (f : BombieriTest) (lo : ℤ) (start len : ℕ) :
    monotoneQuarterFiniteBlock (-f) lo start len =
      -monotoneQuarterFiniteBlock f lo start len := by
  classical
  unfold monotoneQuarterFiniteBlock
  simp_rw [show monotoneQuarterCell (-f) =
      fun j ↦ -monotoneQuarterCell f j by
    funext j
    simpa only [neg_smul, one_smul] using
      monotoneQuarterCell_smul (-1 : ℂ) f j]
  rw [Finset.sum_neg_distrib]

private theorem remoteTwoPrefix_add
    (f g : BombieriTest) (k : ℤ) :
    remoteTwoPrefix (f + g) k =
      remoteTwoPrefix f k + remoteTwoPrefix g k := by
  exact monotoneQuarterFiniteBlock_add_for_remoteGap f g k 0 2

private theorem remoteTwoPrefix_neg
    (f : BombieriTest) (k : ℤ) :
    remoteTwoPrefix (-f) k = -remoteTwoPrefix f k := by
  exact monotoneQuarterFiniteBlock_neg_for_remoteGap f k 0 2

private theorem remoteTwoPrefix_eq_cells
    (parent : BombieriTest) (k : ℤ) :
    remoteTwoPrefix parent k =
      monotoneQuarterCell parent k + monotoneQuarterCell parent (k + 1) := by
  classical
  unfold remoteTwoPrefix monotoneQuarterFiniteBlock
  norm_num [Finset.sum_range_succ]

private theorem remoteGapCell_eq_zero_of_tsupport_le
    (parent : BombieriTest) (j : ℤ)
    (hupper : ∀ x ∈ tsupport parent, x ≤ quarterLogLatticePoint j) :
    monotoneQuarterCell parent j = 0 := by
  apply TestFunction.ext
  intro x
  by_cases hx : x ∈ tsupport parent
  · rw [monotoneQuarterCell_apply,
      monotoneQuarterWeight_eq_zero_of_le j (hupper x hx)]
    simp
  · have hpx : parent x = 0 := by
      by_contra hp
      exact hx (subset_tsupport parent (Function.mem_support.mpr hp))
    change (monotoneQuarterWeight j x : ℂ) * parent x = 0
    rw [hpx, mul_zero]

private theorem remoteGapCell_eq_zero_of_lattice_le_tsupport
    (parent : BombieriTest) (j : ℤ)
    (hlower : ∀ x ∈ tsupport parent,
      quarterLogLatticePoint (j + 2) ≤ x) :
    monotoneQuarterCell parent j = 0 := by
  apply TestFunction.ext
  intro x
  by_cases hx : x ∈ tsupport parent
  · rw [monotoneQuarterCell_apply,
      monotoneQuarterWeight_eq_zero_of_le_left j (hlower x hx)]
    simp
  · have hpx : parent x = 0 := by
      by_contra hp
      exact hx (subset_tsupport parent (Function.mem_support.mpr hp))
    change (monotoneQuarterWeight j x : ℂ) * parent x = 0
    rw [hpx, mul_zero]

private theorem remoteGapWeight_pos_on_first_interval
    (j : ℤ) {x : ℝ}
    (hx : x ∈ Set.Ioo (quarterLogLatticePoint j)
      (quarterLogLatticePoint (j + 1))) :
    0 < monotoneQuarterWeight j x := by
  unfold monotoneQuarterWeight
  rw [monotoneQuarterStep_eq_zero_of_le (j + 1) hx.2.le]
  simpa only [sub_zero] using
    monotoneQuarterStep_pos_of_lattice_lt j hx.1

private theorem remoteGapCell_ne_zero_of_first_interval
    (parent : BombieriTest) (j : ℤ) (hne : parent ≠ 0)
    (hsupport : tsupport parent ⊆ Set.Ioo
      (quarterLogLatticePoint j) (quarterLogLatticePoint (j + 1))) :
    monotoneQuarterCell parent j ≠ 0 := by
  intro hzero
  obtain ⟨x, hx⟩ : ∃ x : ℝ, parent x ≠ 0 := by
    by_contra h
    push_neg at h
    apply hne
    ext y
    simpa using h y
  have hxt : x ∈ tsupport parent :=
    subset_tsupport parent (Function.mem_support.mpr hx)
  have hweight := remoteGapWeight_pos_on_first_interval j (hsupport hxt)
  have happly := congrArg (fun f : BombieriTest ↦ f x) hzero
  simp only [monotoneQuarterCell_apply, TestFunction.coe_zero,
    Pi.zero_apply] at happly
  exact hx (mul_eq_zero.mp happly |>.resolve_left
    (Complex.ofReal_ne_zero.mpr hweight.ne'))

private theorem conjugate_fixed_add_for_remoteGap
    {f g : BombieriTest}
    (hf : bombieriConjugateTest f = f)
    (hg : bombieriConjugateTest g = g) :
    bombieriConjugateTest (f + g) = f + g := by
  rw [bombieriConjugateTest_add, hf, hg]

private theorem conjugate_fixed_sub_for_remoteGap
    {f g : BombieriTest}
    (hf : bombieriConjugateTest f = f)
    (hg : bombieriConjugateTest g = g) :
    bombieriConjugateTest (f - g) = f - g := by
  apply TestFunction.ext
  intro x
  have hfx := congrArg (fun q : BombieriTest ↦ q x) hf
  have hgx := congrArg (fun q : BombieriTest ↦ q x) hg
  simp only [bombieriConjugateTest_apply, TestFunction.coe_sub,
    Pi.sub_apply, map_sub] at hfx hgx ⊢
  rw [hfx, hgx]

/-- No positive portion of the diagonal energy can be supplied uniformly by
the exact signed continuous-minus-Mangoldt row.  The witness consists of two
nonzero smooth, conjugation-fixed endpoint bumps placed in one common parent.
Changing only the remote bump's sign preserves both diagonal energies and
negates the entire Chebyshev-error pairing, before either row is estimated
separately. -/
theorem not_universal_real_remoteTwoPrefixChebyshevEnergyGap
    (c : ℝ) (hc : 0 < c) :
    ¬ (∀ parent : BombieriTest,
      bombieriConjugateTest parent = parent → ∀ k : ℤ,
        RemoteTwoPrefixChebyshevEnergyGap c parent k) := by
  intro hall
  let k : ℤ := 0
  obtain ⟨lower, upper, hlowerNe, hupperNe,
      hlowerFixed, hupperFixed, hlowerSupport, hupperSupport, _hsep⟩ :=
    exists_nonzero_endpoint_localized_halfSeparated_pair k
  let f : BombieriTest := monotoneQuarterCell lower k
  let g : BombieriTest := monotoneQuarterCell upper (k + 4)
  have hfNe : f ≠ 0 :=
    remoteGapCell_ne_zero_of_first_interval lower k hlowerNe hlowerSupport
  have hgNe : g ≠ 0 :=
    remoteGapCell_ne_zero_of_first_interval upper (k + 4) hupperNe
      hupperSupport
  have hlowerNext : monotoneQuarterCell lower (k + 1) = 0 := by
    apply remoteGapCell_eq_zero_of_tsupport_le lower (k + 1)
    intro x hx
    exact (hlowerSupport hx).2.le
  have hlowerEndpoint : remoteTwoEndpoint lower k = 0 := by
    unfold remoteTwoEndpoint
    apply remoteGapCell_eq_zero_of_tsupport_le lower (k + 4)
    intro x hx
    exact (hlowerSupport hx).2.le.trans
      (quarterLogLatticePoint_mono (by omega))
  have hupperCellZero (j : ℤ) (hj : j + 2 ≤ k + 4) :
      monotoneQuarterCell upper j = 0 := by
    apply remoteGapCell_eq_zero_of_lattice_le_tsupport upper j
    intro x hx
    exact (quarterLogLatticePoint_mono hj).trans
      (hupperSupport hx).1.le
  have hlowerPrefix : remoteTwoPrefix lower k = f := by
    rw [remoteTwoPrefix_eq_cells, hlowerNext, add_zero]
  have hupperPrefix : remoteTwoPrefix upper k = 0 := by
    rw [remoteTwoPrefix_eq_cells, hupperCellZero k (by omega),
      hupperCellZero (k + 1) (by omega), add_zero]
  have hupperEndpoint : remoteTwoEndpoint upper k = g := by
    rfl
  have hplusPrefix : remoteTwoPrefix (lower + upper) k = f := by
    rw [remoteTwoPrefix_add, hlowerPrefix, hupperPrefix, add_zero]
  have hplusEndpoint : remoteTwoEndpoint (lower + upper) k = g := by
    unfold remoteTwoEndpoint
    rw [monotoneQuarterCell_add]
    change monotoneQuarterCell lower (k + 4) + g = g
    rw [show monotoneQuarterCell lower (k + 4) = 0 by
      simpa only [remoteTwoEndpoint] using hlowerEndpoint, zero_add]
  have hminusPrefix : remoteTwoPrefix (lower - upper) k = f := by
    rw [sub_eq_add_neg, remoteTwoPrefix_add, remoteTwoPrefix_neg,
      hlowerPrefix, hupperPrefix, neg_zero, add_zero]
  have hminusEndpoint : remoteTwoEndpoint (lower - upper) k = -g := by
    unfold remoteTwoEndpoint
    have hneg : monotoneQuarterCell (-upper) (k + 4) =
        -monotoneQuarterCell upper (k + 4) := by
      simpa only [neg_smul, one_smul] using
        monotoneQuarterCell_smul (-1 : ℂ) upper (k + 4)
    rw [sub_eq_add_neg, monotoneQuarterCell_add, hneg]
    change monotoneQuarterCell lower (k + 4) + -g = -g
    rw [show monotoneQuarterCell lower (k + 4) = 0 by
      simpa only [remoteTwoEndpoint] using hlowerEndpoint, zero_add]
  have hEf : 0 < bombieriCriticalLogEnergy f :=
    bombieriCriticalLogEnergy_pos_of_ne_zero f hfNe
  have hEg : 0 < bombieriCriticalLogEnergy g :=
    bombieriCriticalLogEnergy_pos_of_ne_zero g hgNe
  have hcost : 0 < c *
      (bombieriCriticalLogEnergy f + bombieriCriticalLogEnergy g) :=
    mul_pos hc (add_pos hEf hEg)
  have hplus := hall (lower + upper)
    (conjugate_fixed_add_for_remoteGap hlowerFixed hupperFixed) k
  have hminus := hall (lower - upper)
    (conjugate_fixed_sub_for_remoteGap hlowerFixed hupperFixed) k
  unfold RemoteTwoPrefixChebyshevEnergyGap at hplus hminus
  rw [hplusPrefix, hplusEndpoint] at hplus
  rw [hminusPrefix, hminusEndpoint,
    criticalLogEnergy_neg_for_remoteGap,
    separatedChebyshevErrorPairing_one_neg_left] at hminus
  simp only [Complex.neg_re] at hminus
  linarith

/-! ## What support minimality actually forces -/

/-- Complete interval-and-cut package attached to a support-minimal negative
monotone block.  The quantified interval clause contains every proper
prefix, every proper suffix, and every proper adjacent subblock.  The cut
clause records, simultaneously at every internal cut, the two nonnegative
diagonals together with the strict arithmetic-mean and determinant
reversals of their complete cross.

This is the full direct scalar information supplied by support minimality;
no endpoint propagation or global positivity statement is assumed. -/
theorem supportMinimalNegativeMonotoneBlock_completeIntervalCutConstraints
    {parent : BombieriTest} {lo : ℤ} {N start len : ℕ}
    (hmin : IsSupportMinimalNegativeMonotoneBlock
      parent lo N start len) :
    4 ≤ len ∧
      bombieriRealQuadraticValue
          (monotoneQuarterFiniteBlock parent lo start len) < 0 ∧
      (∀ offset sublen : ℕ,
        offset + sublen ≤ len → sublen < len →
          0 ≤ bombieriRealQuadraticValue
            (monotoneQuarterFiniteBlock parent lo
              (start + offset) sublen)) ∧
      ∀ cut : ℕ, 0 < cut → cut < len →
        let leftBlock := monotoneQuarterFiniteBlock parent lo start cut
        let rightBlock := monotoneQuarterFiniteBlock parent lo
          (start + cut) (len - cut)
        0 ≤ bombieriRealQuadraticValue leftBlock ∧
          0 ≤ bombieriRealQuadraticValue rightBlock ∧
          (bombieriTwoBlockGlobalCrossSymbol leftBlock rightBlock).re <
            -(bombieriRealQuadraticValue leftBlock +
                bombieriRealQuadraticValue rightBlock) / 2 ∧
          bombieriRealQuadraticValue leftBlock *
              bombieriRealQuadraticValue rightBlock <
            (bombieriTwoBlockGlobalCrossSymbol leftBlock rightBlock).re ^ 2 := by
  refine ⟨four_le_length_of_supportMinimalNegativeMonotoneBlock hmin,
    hmin.negative, ?_, ?_⟩
  · intro offset sublen hinside hproper
    exact supportMinimalNegativeMonotoneBlock_properSubblock_nonnegative
      hmin offset sublen hinside hproper
  · intro cut hcutPos hcutLt
    let leftBlock := monotoneQuarterFiniteBlock parent lo start cut
    let rightBlock := monotoneQuarterFiniteBlock parent lo
      (start + cut) (len - cut)
    have hcut := supportMinimalNegativeMonotoneBlock_internalCut_constraints
      hmin cut hcutPos hcutLt
    exact ⟨hcut.left_nonnegative, hcut.right_nonnegative,
      hcut.cross_strictly_below_arithmeticMean,
      hcut.determinant_strictly_reversed⟩

/-- At the right-endpoint cut, support minimality forces the strict negation
of both candidate endpoint absorptions.  The endpoint cross is below the
negative arithmetic mean, and its square is strictly larger than the
prefix--endpoint diagonal product.  Thus the minimal-block hypothesis does
not furnish the missing Schur estimate: conditional on a minimal negative
block, it reverses that estimate. -/
theorem supportMinimalNegativeMonotoneBlock_rightEndpoint_absorption_strictly_fails
    {parent : BombieriTest} {lo : ℤ} {N start len : ℕ}
    (hmin : IsSupportMinimalNegativeMonotoneBlock
      parent lo N start len) :
    let front := monotoneQuarterFiniteBlock parent lo start (len - 1)
    let endpoint := monotoneQuarterFiniteBlock parent lo
      (start + (len - 1)) 1
    0 ≤ bombieriRealQuadraticValue front ∧
      0 ≤ bombieriRealQuadraticValue endpoint ∧
      ¬ (-(bombieriRealQuadraticValue front +
            bombieriRealQuadraticValue endpoint) / 2 ≤
          (bombieriTwoBlockGlobalCrossSymbol front endpoint).re) ∧
      ¬ ((bombieriTwoBlockGlobalCrossSymbol front endpoint).re ^ 2 ≤
          bombieriRealQuadraticValue front *
            bombieriRealQuadraticValue endpoint) := by
  dsimp only
  have hright :=
    supportMinimalNegativeMonotoneBlock_rightEndpoint_constraints hmin
  exact ⟨hright.left_nonnegative, hright.right_nonnegative,
    not_le_of_gt hright.cross_strictly_below_arithmeticMean,
    not_le_of_gt hright.determinant_strictly_reversed⟩

/-- Scalar coordinates of the terminal remote-row split
`left + middle + right`.  Here `X`, `Y`, and `Z` are respectively the
left--middle, middle--right, and genuinely remote left--right real crosses.
The five nonnegative quantities are precisely the three pieces and the two
proper adjacent unions; the last field is the full-block negativity. -/
structure MinimalNegativeTerminalRemoteScalarConstraints
    (A B C X Y Z : ℝ) : Prop where
  left_nonnegative : 0 ≤ A
  middle_nonnegative : 0 ≤ B
  right_nonnegative : 0 ≤ C
  leftMiddle_nonnegative : 0 ≤ A + B + 2 * X
  middleRight_nonnegative : 0 ≤ B + C + 2 * Y
  full_negative : A + B + C + 2 * (X + Y + Z) < 0

/-- The terminal three-piece coordinates of every support-minimal negative
block satisfy the exact scalar remote-row constraints.  This is the
endpoint-telescope specialization of the complete interval package, with no
estimate applied to any cross. -/
theorem supportMinimalNegativeMonotoneBlock_terminalRemoteScalarConstraints
    {parent : BombieriTest} {lo : ℤ} {N start len n : ℕ}
    (hmin : IsSupportMinimalNegativeMonotoneBlock
      parent lo N start len)
    (hlen : len = n + 3) :
    let leftBlock := monotoneQuarterFiniteBlock parent lo start n
    let middleBlock := monotoneQuarterFiniteBlock parent lo (start + n) 2
    let rightBlock := monotoneQuarterFiniteBlock parent lo
      (start + n + 2) 1
    MinimalNegativeTerminalRemoteScalarConstraints
      (bombieriRealQuadraticValue leftBlock)
      (bombieriRealQuadraticValue middleBlock)
      (bombieriRealQuadraticValue rightBlock)
      (bombieriTwoBlockGlobalCrossSymbol leftBlock middleBlock).re
      (bombieriTwoBlockGlobalCrossSymbol middleBlock rightBlock).re
      (bombieriTwoBlockGlobalCrossSymbol leftBlock rightBlock).re := by
  dsimp only
  let leftBlock := monotoneQuarterFiniteBlock parent lo start n
  let middleBlock := monotoneQuarterFiniteBlock parent lo (start + n) 2
  let rightBlock := monotoneQuarterFiniteBlock parent lo
    (start + n + 2) 1
  have hlenFour := four_le_length_of_supportMinimalNegativeMonotoneBlock hmin
  have hn : 1 ≤ n := by omega
  have hleft : 0 ≤ bombieriRealQuadraticValue leftBlock := by
    dsimp only [leftBlock]
    apply supportMinimalNegativeMonotoneBlock_properSubblock_nonnegative
      hmin 0 n <;> omega
  have hmiddle : 0 ≤ bombieriRealQuadraticValue middleBlock := by
    dsimp only [middleBlock]
    apply supportMinimalNegativeMonotoneBlock_properSubblock_nonnegative
      hmin n 2 <;> omega
  have hright : 0 ≤ bombieriRealQuadraticValue rightBlock := by
    dsimp only [rightBlock]
    apply supportMinimalNegativeMonotoneBlock_properSubblock_nonnegative
      hmin (n + 2) 1 <;> omega
  have hleftMiddleSplit := monotoneQuarterFiniteBlock_eq_prefix_add_suffix
    parent lo start (n + 2) n (by omega)
  have hleftMiddle : leftBlock + middleBlock =
      monotoneQuarterFiniteBlock parent lo start (n + 2) := by
    simpa only [leftBlock, middleBlock, Nat.add_sub_cancel_left] using
      hleftMiddleSplit.symm
  have hmiddleRightSplit := monotoneQuarterFiniteBlock_eq_prefix_add_suffix
    parent lo (start + n) 3 2 (by omega)
  have hmiddleRight : middleBlock + rightBlock =
      monotoneQuarterFiniteBlock parent lo (start + n) 3 := by
    simpa only [middleBlock, rightBlock, Nat.add_assoc,
      show 3 - 2 = 1 by omega] using hmiddleRightSplit.symm
  have hleftMiddleNonnegative :
      0 ≤ bombieriRealQuadraticValue leftBlock +
          bombieriRealQuadraticValue middleBlock +
        2 * (bombieriTwoBlockGlobalCrossSymbol leftBlock middleBlock).re := by
    rw [← bombieriRealQuadraticValue_add, hleftMiddle]
    apply supportMinimalNegativeMonotoneBlock_properSubblock_nonnegative
      hmin 0 (n + 2) <;> omega
  have hmiddleRightNonnegative :
      0 ≤ bombieriRealQuadraticValue middleBlock +
          bombieriRealQuadraticValue rightBlock +
        2 * (bombieriTwoBlockGlobalCrossSymbol middleBlock rightBlock).re := by
    rw [← bombieriRealQuadraticValue_add, hmiddleRight]
    apply supportMinimalNegativeMonotoneBlock_properSubblock_nonnegative
      hmin n 3 <;> omega
  have hwholeSplit := monotoneQuarterFiniteBlock_eq_prefix_add_suffix
    parent lo start (n + 3) (n + 2) (by omega)
  have hwholeN : monotoneQuarterFiniteBlock parent lo start (n + 3) =
      (leftBlock + middleBlock) + rightBlock := by
    rw [hwholeSplit, ← hleftMiddle]
    simp only [rightBlock, Nat.add_assoc,
      show n + 3 - (n + 2) = 1 by omega]
  have hwhole : monotoneQuarterFiniteBlock parent lo start len =
      (leftBlock + middleBlock) + rightBlock := by
    rw [hlen]
    exact hwholeN
  have hfull : bombieriRealQuadraticValue
      ((leftBlock + middleBlock) + rightBlock) < 0 := by
    rw [← hwhole]
    exact hmin.negative
  refine ⟨hleft, hmiddle, hright, hleftMiddleNonnegative,
    hmiddleRightNonnegative, ?_⟩
  rw [bombieriRealQuadraticValue_add,
    bombieriRealQuadraticValue_add,
    bombieriTwoBlockGlobalCrossSymbol_add_left] at hfull
  simp only [Complex.add_re] at hfull
  linarith

/-- The terminal scalar system itself forces the endpoint-versus-prefix
arithmetic-mean and Schur inequalities in the wrong direction.  In
particular, retaining every adjacent nonnegativity constraint does not absorb
the remote row `Z`; it only says that `Y + Z` must defeat the full preceding
prefix. -/
theorem minimalNegativeTerminalRemoteScalarConstraints_endpointAbsorption_reversed
    {A B C X Y Z : ℝ}
    (h : MinimalNegativeTerminalRemoteScalarConstraints A B C X Y Z) :
    Y + Z < -(A + B + 2 * X + C) / 2 ∧
      (A + B + 2 * X) * C < (Y + Z) ^ 2 := by
  have hnegative :
      (A + B + 2 * X) + C + 2 * (Y + Z) < 0 := by
    linarith [h.full_negative]
  constructor
  · linarith
  · nlinarith [h.leftMiddle_nonnegative, h.right_nonnegative,
      sq_nonneg ((A + B + 2 * X) - C),
      sq_nonneg ((A + B + 2 * X) + C + 2 * (Y + Z))]

/-- The terminal scalar constraints are algebraically consistent.  The
values `A = C = 1`, `B = 2`, `X = Y = 0`, and `Z = -3` make each piece and
both adjacent unions nonnegative while the full remote row is negative. -/
theorem minimalNegativeTerminalRemoteScalarConstraints_realizable :
    ∃ A B C X Y Z : ℝ,
      MinimalNegativeTerminalRemoteScalarConstraints A B C X Y Z := by
  refine ⟨1, 2, 1, 0, 0, -3, ?_⟩
  constructor <;> norm_num

/-- A stronger constrained model: every quadratic vector supported in
either proper adjacent three-coordinate interval is nonnegative, yet the
four-cell all-ones vector is negative and all three internal cuts have the
strict arithmetic-mean and Schur reversals forced by support minimality.

Thus even upgrading the proper-interval scalar inequalities to positive
semidefiniteness on every proper contiguous coordinate subspace does not
produce endpoint absorption.  An additional analytic constraint coupling
the remote corner to the adjacent blocks is indispensable. -/
theorem allProperContiguousSubspacesPSD_allow_allInternalCutReversals :
    ∃ X : ℝ,
      (∀ a b c : ℝ,
        0 ≤ remoteCornerFourCoordinateQuadratic X a b c 0) ∧
      (∀ b c d : ℝ,
        0 ≤ remoteCornerFourCoordinateQuadratic X 0 b c d) ∧
      remoteCornerFourCoordinateQuadratic X 1 1 1 1 < 0 ∧
      X < -(remoteCornerFourCoordinateQuadratic X 1 0 0 0 +
            remoteCornerFourCoordinateQuadratic X 0 1 1 1) / 2 ∧
      remoteCornerFourCoordinateQuadratic X 1 0 0 0 *
          remoteCornerFourCoordinateQuadratic X 0 1 1 1 < X ^ 2 ∧
      X < -(remoteCornerFourCoordinateQuadratic X 1 1 0 0 +
            remoteCornerFourCoordinateQuadratic X 0 0 1 1) / 2 ∧
      remoteCornerFourCoordinateQuadratic X 1 1 0 0 *
          remoteCornerFourCoordinateQuadratic X 0 0 1 1 < X ^ 2 ∧
      X < -(remoteCornerFourCoordinateQuadratic X 1 1 1 0 +
            remoteCornerFourCoordinateQuadratic X 0 0 0 1) / 2 ∧
      remoteCornerFourCoordinateQuadratic X 1 1 1 0 *
          remoteCornerFourCoordinateQuadratic X 0 0 0 1 < X ^ 2 := by
  refine ⟨-3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b c
    rw [remoteCornerFourCoordinateQuadratic_leftTriple]
    nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
  · intro b c d
    rw [remoteCornerFourCoordinateQuadratic_rightTriple]
    nlinarith [sq_nonneg b, sq_nonneg c, sq_nonneg d]
  all_goals norm_num [remoteCornerFourCoordinateQuadratic]

/-! ## First common-parent constraint absent from the scalar model -/

/-- In the actual five-cell monotone geometry, a vanishing middle-three
block does not leave a free remote corner.  Exact support collapse annihilates
the endpoint prime atom, while the shortened endpoint supports give a local
critical determinant.  Consequently the sparse endpoint pair is
nonnegative.

This conclusion genuinely uses the common parent and its monotone weights;
it is false for the unconstrained scalar remote-corner model above. -/
theorem bombieriRealQuadraticValue_fiveCellSparseEndpointPair_nonnegative_of_middle_zero
    (parent : BombieriTest) (k : ℤ)
    (hparent : bombieriConjugateTest parent = parent)
    (hmiddle : fiveCellMiddleThree parent k = 0) :
    0 ≤ bombieriRealQuadraticValue
      (monotoneQuarterCell parent k +
        monotoneQuarterCell parent (k + 4)) := by
  let a : BombieriTest := monotoneQuarterCell parent k
  let e : BombieriTest := monotoneQuarterCell parent (k + 4)
  let A : ℝ := (bombieriLocalCriticalForm a a).re
  let E : ℝ := (bombieriLocalCriticalForm e e).re
  let X : ℂ := bombieriLocalCriticalForm a e
  have hdiag :=
    fiveCell_endpointLocalCritical_diagonal_coercivity_of_middle_zero
      parent k hparent hmiddle
  have hdet :=
    fiveCell_remoteEndpointLocalCritical_determinant_of_middle_zero
      parent k hparent hmiddle
  have hEa0 : 0 ≤ bombieriCriticalLogEnergy a :=
    bombieriCriticalLogEnergy_nonnegative a
  have hEe0 : 0 ≤ bombieriCriticalLogEnergy e :=
    bombieriCriticalLogEnergy_nonnegative e
  have hc0 : 0 ≤ (27 / 100 : ℝ) := by norm_num
  have hA0 : 0 ≤ A := by
    dsimp only [A, a]
    exact (mul_nonneg hc0 hEa0).trans hdiag.1
  have hE0 : 0 ≤ E := by
    dsimp only [E, e]
    exact (mul_nonneg hc0 hEe0).trans hdiag.2
  have hReSq : X.re ^ 2 ≤ Complex.normSq X := by
    rw [Complex.normSq_apply]
    nlinarith [sq_nonneg X.im]
  have hSchur : X.re ^ 2 ≤ A * E := by
    exact hReSq.trans (by simpa only [X, A, E, a, e] using hdet)
  have hsum : 0 ≤ A + E + 2 * X.re := by
    nlinarith [sq_nonneg (A - E), sq_nonneg (A + E + 2 * X.re)]
  unfold bombieriRealQuadraticValue
  rw [bombieriFunctional_remoteEndpointPair_re_eq_local_of_middle_zero
    parent k hmiddle]
  simpa only [A, E, X, a, e] using hsum

private theorem monotoneQuarterFiniteBlock_five_eq_fiveBlock
    (parent : BombieriTest) (lo : ℤ) (start : ℕ) :
    monotoneQuarterFiniteBlock parent lo start 5 =
      monotoneQuarterFiveBlock parent (lo + (start : ℤ)) := by
  classical
  unfold monotoneQuarterFiveBlock monotoneQuarterFiniteBlock
  apply Finset.sum_congr rfl
  intro i _hi
  congr 1
  push_cast
  ring

private theorem monotoneQuarterFiveBlock_eq_endpoint_middle_endpoint
    (parent : BombieriTest) (k : ℤ) :
    monotoneQuarterFiveBlock parent k =
      (monotoneQuarterCell parent k + fiveCellMiddleThree parent k) +
        monotoneQuarterCell parent (k + 4) := by
  classical
  simp [monotoneQuarterFiveBlock, monotoneQuarterFiniteBlock,
    fiveCellMiddleThree, Finset.sum_range_succ]
  module

/-- Therefore a support-minimal negative five-cell block has a nonzero
middle-three block.  The degenerate branch of the three-block determinant is
not an actual minimal counterexample: exact common-parent support geometry
excludes it before any four-cell positivity assumption is used. -/
theorem supportMinimalNegativeMonotoneBlock_length_five_middle_ne_zero
    {parent : BombieriTest} {lo : ℤ} {N start len : ℕ}
    (hparent : bombieriConjugateTest parent = parent)
    (hmin : IsSupportMinimalNegativeMonotoneBlock
      parent lo N start len)
    (hlen : len = 5) :
    fiveCellMiddleThree parent (lo + (start : ℤ)) ≠ 0 := by
  intro hmiddle
  let k : ℤ := lo + (start : ℤ)
  have hpair :=
    bombieriRealQuadraticValue_fiveCellSparseEndpointPair_nonnegative_of_middle_zero
      parent k hparent hmiddle
  have hnegative : bombieriRealQuadraticValue
      (monotoneQuarterFiveBlock parent k) < 0 := by
    rw [← monotoneQuarterFiniteBlock_five_eq_fiveBlock]
    simpa only [hlen] using hmin.negative
  rw [monotoneQuarterFiveBlock_eq_endpoint_middle_endpoint,
    hmiddle, add_zero] at hnegative
  exact (not_lt_of_ge hpair) hnegative

/-- Combining the common-parent exclusion of the zero-middle branch with
the adjacent four-cell principal minors leaves one—and only one—length-five
obstruction.  Every support-minimal negative five-cell block must strictly
reverse the nondegenerate middle-pivot contraction coupling the remote
endpoint balance `X` to the two adjacent rows `U` and `V`.

Thus proving this single actual common-parent residual inequality would rule
out minimal negative blocks of length five once production four-cell
positivity is available. -/
theorem supportMinimalNegativeMonotoneBlock_length_five_forces_middlePivotResidual_reversal
    (hfour : RealFourCellProductionNonnegative)
    {parent : BombieriTest} {lo : ℤ} {N start len : ℕ}
    (hparent : bombieriConjugateTest parent = parent)
    (hmin : IsSupportMinimalNegativeMonotoneBlock
      parent lo N start len) (hlen : len = 5) :
    let k := monotoneQuarterFiniteBlockBase lo start
    let a := monotoneQuarterCell parent k
    let m := fiveCellMiddleThree parent k
    let e := monotoneQuarterCell parent (k + 4)
    let A := bombieriRealQuadraticValue a
    let M := bombieriRealQuadraticValue m
    let E := bombieriRealQuadraticValue e
    let U := (bombieriTwoBlockGlobalCrossSymbol a m).re
    let V := (bombieriTwoBlockGlobalCrossSymbol m e).re
    let X := fiveCellRemoteEndpointBalance parent k
    (A * M - U ^ 2) * (M * E - V ^ 2) <
      (M * X - U * V) ^ 2 := by
  have hmiddle : fiveCellMiddleThree parent
      (monotoneQuarterFiniteBlockBase lo start) ≠ 0 := by
    simpa only [monotoneQuarterFiniteBlockBase] using
      supportMinimalNegativeMonotoneBlock_length_five_middle_ne_zero
        hparent hmin hlen
  exact
    supportMinimalNegativeMonotoneBlock_length_five_middlePivotResidual_reversed
      hfour hparent hmin hlen hmiddle

/-! ## The forced sign of the nondegenerate five-cell residual -/

/-- The negative all-ones direction selects the negative branch of the
middle-pivot residual.  Once the adjacent principal minors are nonnegative,
the exact pivot identity gives the stronger quantitative bound

`M X - U V < -((M+U+V)^2 + (A M-U^2) + (M E-V^2))/2`.

Thus the residual reversal above is not merely an absolute-value
obstruction: its conditional remote corner has a forced sign. -/
theorem FiveCellCoupledEndpointSchurConstraints.middlePivotResidual_negativeBranch
    {A M E U V X : ℝ}
    (h : FiveCellCoupledEndpointSchurConstraints A M E U V X)
    (hMpos : 0 < M)
    (hAM : U ^ 2 ≤ A * M)
    (hME : V ^ 2 ≤ M * E) :
    M * X - U * V <
      -((M + U + V) ^ 2 + (A * M - U ^ 2) +
          (M * E - V ^ 2)) / 2 := by
  rcases h with
    ⟨_hA, _hM, _hE, _hL, _hR, _hleftMean, _hleftDet,
      _hrightMean, _hrightDet, hwhole⟩
  have halpha : 0 ≤ A * M - U ^ 2 := by linarith
  have hbeta : 0 ≤ M * E - V ^ 2 := by linarith
  have hscaled :
      M * (A + M + E + 2 * (U + V + X)) < 0 :=
    mul_neg_of_pos_of_neg hMpos hwhole
  have hidentity :
      M * (A + M + E + 2 * (U + V + X)) =
        (M + U + V) ^ 2 + (A * M - U ^ 2) +
          (M * E - V ^ 2) + 2 * (M * X - U * V) := by
    ring
  rw [hidentity] at hscaled
  nlinarith [sq_nonneg (M + U + V)]

/-- Production form of the forced negative branch.  For an actual
support-minimal negative five-cell block, universal four-cell positivity and
the common-parent exclusion of the zero-middle case imply a strict signed
coupling between the remote endpoint balance `X` and the two adjacent rows:

`M X < U V`,

with the displayed quantitative deficit.  Any common-parent argument that
forces the opposite conditional-correlation sign therefore excludes the
length-five obstruction outright. -/
theorem supportMinimalNegativeMonotoneBlock_length_five_forces_middlePivotResidual_negativeBranch
    (hfour : RealFourCellProductionNonnegative)
    {parent : BombieriTest} {lo : ℤ} {N start len : ℕ}
    (hparent : bombieriConjugateTest parent = parent)
    (hmin : IsSupportMinimalNegativeMonotoneBlock
      parent lo N start len) (hlen : len = 5) :
    let k := monotoneQuarterFiniteBlockBase lo start
    let a := monotoneQuarterCell parent k
    let m := fiveCellMiddleThree parent k
    let e := monotoneQuarterCell parent (k + 4)
    let A := bombieriRealQuadraticValue a
    let M := bombieriRealQuadraticValue m
    let E := bombieriRealQuadraticValue e
    let U := (bombieriTwoBlockGlobalCrossSymbol a m).re
    let V := (bombieriTwoBlockGlobalCrossSymbol m e).re
    let X := fiveCellRemoteEndpointBalance parent k
    M * X - U * V <
      -((M + U + V) ^ 2 + (A * M - U ^ 2) +
          (M * E - V ^ 2)) / 2 := by
  dsimp only
  let k : ℤ := monotoneQuarterFiniteBlockBase lo start
  let a : BombieriTest := monotoneQuarterCell parent k
  let m : BombieriTest := fiveCellMiddleThree parent k
  let e : BombieriTest := monotoneQuarterCell parent (k + 4)
  let A : ℝ := bombieriRealQuadraticValue a
  let M : ℝ := bombieriRealQuadraticValue m
  let E : ℝ := bombieriRealQuadraticValue e
  let U : ℝ := (bombieriTwoBlockGlobalCrossSymbol a m).re
  let V : ℝ := (bombieriTwoBlockGlobalCrossSymbol m e).re
  let X : ℝ := fiveCellRemoteEndpointBalance parent k
  have hmiddle : m ≠ 0 := by
    dsimp only [m, k]
    simpa only [monotoneQuarterFiniteBlockBase] using
      supportMinimalNegativeMonotoneBlock_length_five_middle_ne_zero
        hparent hmin hlen
  have hconstraints :=
    supportMinimalNegativeMonotoneBlock_length_five_coupledEndpointSchur
      hmin hlen
  dsimp only at hconstraints
  have hmiddleEq :
      monotoneQuarterFiniteBlock parent lo (start + 1) 3 = m := by
    classical
    dsimp only [m, k]
    simp [monotoneQuarterFiniteBlock,
      monotoneQuarterFiniteBlockBase, fiveCellMiddleThree,
      Finset.sum_range_succ]
    congr 1 <;> ring
  rw [hmiddleEq] at hconstraints
  change FiveCellCoupledEndpointSchurConstraints A M E U V X at hconstraints
  have hadj := fiveCell_adjacentPrincipalMinors_of_fourCellProduction
    hfour parent hparent k
  change U ^ 2 ≤ A * M ∧ V ^ 2 ≤ M * E at hadj
  have hMpos : 0 < M := by
    dsimp only [M, m]
    exact fiveCellMiddleThree_quadratic_pos_of_ne_zero
      parent hparent k hmiddle
  exact
    FiveCellCoupledEndpointSchurConstraints.middlePivotResidual_negativeBranch
      hconstraints hMpos hadj.1 hadj.2

/-- In particular, the conditional remote cross itself is strictly
negative.  This is the sign-only interface of the quantitative branch
theorem and is often the more convenient contradiction target. -/
theorem supportMinimalNegativeMonotoneBlock_length_five_forces_middlePivotConditionalCross_neg
    (hfour : RealFourCellProductionNonnegative)
    {parent : BombieriTest} {lo : ℤ} {N start len : ℕ}
    (hparent : bombieriConjugateTest parent = parent)
    (hmin : IsSupportMinimalNegativeMonotoneBlock
      parent lo N start len) (hlen : len = 5) :
    let k := monotoneQuarterFiniteBlockBase lo start
    let a := monotoneQuarterCell parent k
    let m := fiveCellMiddleThree parent k
    let e := monotoneQuarterCell parent (k + 4)
    let M := bombieriRealQuadraticValue m
    let U := (bombieriTwoBlockGlobalCrossSymbol a m).re
    let V := (bombieriTwoBlockGlobalCrossSymbol m e).re
    let X := fiveCellRemoteEndpointBalance parent k
    M * X - U * V < 0 := by
  dsimp only
  let k : ℤ := monotoneQuarterFiniteBlockBase lo start
  let a : BombieriTest := monotoneQuarterCell parent k
  let m : BombieriTest := fiveCellMiddleThree parent k
  let e : BombieriTest := monotoneQuarterCell parent (k + 4)
  let A : ℝ := bombieriRealQuadraticValue a
  let M : ℝ := bombieriRealQuadraticValue m
  let E : ℝ := bombieriRealQuadraticValue e
  let U : ℝ := (bombieriTwoBlockGlobalCrossSymbol a m).re
  let V : ℝ := (bombieriTwoBlockGlobalCrossSymbol m e).re
  let X : ℝ := fiveCellRemoteEndpointBalance parent k
  have hbranch :=
    supportMinimalNegativeMonotoneBlock_length_five_forces_middlePivotResidual_negativeBranch
      hfour hparent hmin hlen
  change M * X - U * V <
    -((M + U + V) ^ 2 + (A * M - U ^ 2) +
        (M * E - V ^ 2)) / 2 at hbranch
  have hadj := fiveCell_adjacentPrincipalMinors_of_fourCellProduction
    hfour parent hparent k
  change U ^ 2 ≤ A * M ∧ V ^ 2 ≤ M * E at hadj
  change M * X - U * V < 0
  nlinarith [sq_nonneg (M + U + V)]

/-- Concrete residual-test form of the forced branch.  The two actual
middle-orthogonal tests cut from the same parent cannot have zero or positive
real global cross in a remaining support-minimal negative five-cell block;
their cross is strictly negative. -/
theorem supportMinimalNegativeMonotoneBlock_length_five_forces_middleOrthogonalResidualCross_neg
    (hfour : RealFourCellProductionNonnegative)
    {parent : BombieriTest} {lo : ℤ} {N start len : ℕ}
    (hparent : bombieriConjugateTest parent = parent)
    (hmin : IsSupportMinimalNegativeMonotoneBlock
      parent lo N start len) (hlen : len = 5) :
    let k := monotoneQuarterFiniteBlockBase lo start
    (bombieriTwoBlockGlobalCrossSymbol
      (fiveCellLeftMiddleOrthogonalResidual parent k)
      (fiveCellRightMiddleOrthogonalResidual parent k)).re < 0 := by
  dsimp only
  let k : ℤ := monotoneQuarterFiniteBlockBase lo start
  let a : BombieriTest := monotoneQuarterCell parent k
  let m : BombieriTest := fiveCellMiddleThree parent k
  let e : BombieriTest := monotoneQuarterCell parent (k + 4)
  let M : ℝ := bombieriRealQuadraticValue m
  let U : ℝ := (bombieriTwoBlockGlobalCrossSymbol a m).re
  let V : ℝ := (bombieriTwoBlockGlobalCrossSymbol m e).re
  let X : ℝ := fiveCellRemoteEndpointBalance parent k
  have hdelta :=
    supportMinimalNegativeMonotoneBlock_length_five_forces_middlePivotConditionalCross_neg
      hfour hparent hmin hlen
  change M * X - U * V < 0 at hdelta
  have hmiddle : m ≠ 0 := by
    dsimp only [m, k]
    simpa only [monotoneQuarterFiniteBlockBase] using
      supportMinimalNegativeMonotoneBlock_length_five_middle_ne_zero
        hparent hmin hlen
  have hMpos : 0 < M := by
    dsimp only [M, m]
    exact fiveCellMiddleThree_quadratic_pos_of_ne_zero
      parent hparent k hmiddle
  have hcoordinates := fiveCell_middleOrthogonalResidual_coordinates parent k
  have hcross := hcoordinates.2.2
  change
    (bombieriTwoBlockGlobalCrossSymbol
      (fiveCellLeftMiddleOrthogonalResidual parent k)
      (fiveCellRightMiddleOrthogonalResidual parent k)).re =
        M * (M * X - U * V) at hcross
  rw [hcross]
  exact mul_neg_of_pos_of_neg hMpos hdelta

/-! ## Exact common-parent remote-row closure at five cells -/

/-- The remaining analytic sign condition written entirely in the exact
common-parent remote-row coordinates.  The two adjacent rows consist of
their near entries plus the lag-three corrected-Chebyshev entries, while the
remote corner is the lag-four corrected-Chebyshev entry.

This is strictly weaker than the full middle-pivot Cauchy--Schwarz
contraction: it asks only that the conditional remote cross have the
nonnegative sign. -/
def RealFiveCellRemoteRowConditionalNonnegative : Prop :=
  ∀ parent : BombieriTest,
    bombieriConjugateTest parent = parent →
      ∀ k : ℤ,
        (fiveCellLeftNearCross parent k +
            monotoneQuarterFarChebyshevContribution parent k 3) *
          (monotoneQuarterFarChebyshevContribution parent (k + 1) 3 +
            fiveCellRightNearCross parent k) ≤
          bombieriRealQuadraticValue (fiveCellMiddleThree parent k) *
            monotoneQuarterFarChebyshevContribution parent k 4

/-- The expanded remote-row condition is exactly nonnegativity of
`M X - U V` in the endpoint--middle--endpoint coordinates. -/
theorem middlePivotConditionalCross_nonnegative_of_realFiveCellRemoteRow
    (hrow : RealFiveCellRemoteRowConditionalNonnegative)
    (parent : BombieriTest)
    (hparent : bombieriConjugateTest parent = parent) (k : ℤ) :
    let a := monotoneQuarterCell parent k
    let m := fiveCellMiddleThree parent k
    let e := monotoneQuarterCell parent (k + 4)
    let M := bombieriRealQuadraticValue m
    let U := (bombieriTwoBlockGlobalCrossSymbol a m).re
    let V := (bombieriTwoBlockGlobalCrossSymbol m e).re
    let X := fiveCellRemoteEndpointBalance parent k
    0 ≤ M * X - U * V := by
  dsimp only
  have h := hrow parent hparent k
  rw [← fiveCell_leftEndpointMiddleCross_re_eq_near_add_chebyshev,
    ← fiveCell_middleRightEndpointCross_re_eq_chebyshev_add_near,
    ← fiveCellRemoteEndpointBalance_eq_farChebyshevContribution] at h
  linarith

/-- The exact remote-row sign condition directly excludes a
support-minimal negative five-cell block.  This is the sharp current
five-cell interface: four-cell production positivity supplies the adjacent
principal minors, and only the signed conditional remote-row inequality is
new. -/
theorem not_supportMinimalNegativeMonotoneBlock_length_five_of_realFiveCellRemoteRow
    (hfour : RealFourCellProductionNonnegative)
    (hrow : RealFiveCellRemoteRowConditionalNonnegative)
    {parent : BombieriTest} {lo : ℤ} {N start len : ℕ}
    (hparent : bombieriConjugateTest parent = parent)
    (hmin : IsSupportMinimalNegativeMonotoneBlock
      parent lo N start len) (hlen : len = 5) : False := by
  let k : ℤ := monotoneQuarterFiniteBlockBase lo start
  let a : BombieriTest := monotoneQuarterCell parent k
  let m : BombieriTest := fiveCellMiddleThree parent k
  let e : BombieriTest := monotoneQuarterCell parent (k + 4)
  let M : ℝ := bombieriRealQuadraticValue m
  let U : ℝ := (bombieriTwoBlockGlobalCrossSymbol a m).re
  let V : ℝ := (bombieriTwoBlockGlobalCrossSymbol m e).re
  let X : ℝ := fiveCellRemoteEndpointBalance parent k
  have hnegative :=
    supportMinimalNegativeMonotoneBlock_length_five_forces_middlePivotConditionalCross_neg
      hfour hparent hmin hlen
  change M * X - U * V < 0 at hnegative
  have hnonnegative :=
    middlePivotConditionalCross_nonnegative_of_realFiveCellRemoteRow
      hrow parent hparent k
  change 0 ≤ M * X - U * V at hnonnegative
  exact (not_lt_of_ge hnonnegative) hnegative

private theorem monotoneQuarterFiniteBlock_four_eq_fourBlock
    (parent : BombieriTest) (lo : ℤ) (start : ℕ) :
    monotoneQuarterFiniteBlock parent lo start 4 =
      monotoneQuarterFourBlock parent (lo + (start : ℤ)) := by
  classical
  unfold monotoneQuarterFourBlock monotoneQuarterFiniteBlock
  apply Finset.sum_congr rfl
  intro i _hi
  congr 1
  push_cast
  ring

/-- Five-cell production positivity now has a sharply isolated sufficient
interface.  Four-cell production positivity excludes a shortest negative
subblock of length four; the exact conditional remote-row sign excludes the
only other possible length, five. -/
theorem bombieriRealQuadraticValue_monotoneQuarterFiveBlock_nonnegative_of_fourCell_and_remoteRow
    (hfour : RealFourCellProductionNonnegative)
    (hrow : RealFiveCellRemoteRowConditionalNonnegative)
    (parent : BombieriTest)
    (hparent : bombieriConjugateTest parent = parent) (k : ℤ) :
    0 ≤ bombieriRealQuadraticValue (monotoneQuarterFiveBlock parent k) := by
  by_contra hnot
  have hnegative : bombieriRealQuadraticValue
      (monotoneQuarterFiniteBlock parent k 0 5) < 0 := by
    change bombieriRealQuadraticValue
      (monotoneQuarterFiveBlock parent k) < 0
    exact lt_of_not_ge hnot
  obtain ⟨start, len, hmin⟩ :=
    exists_supportMinimalNegativeMonotoneBlock parent k 5 hnegative
  have hlenLower : 4 ≤ len :=
    four_le_length_of_supportMinimalNegativeMonotoneBlock hmin
  have hwithin := hmin.within
  have hlenUpper : len ≤ 5 := by omega
  rcases (show len = 4 ∨ len = 5 by omega) with hlen | hlen
  · have hnegativeFour := hmin.negative
    rw [hlen, monotoneQuarterFiniteBlock_four_eq_fourBlock] at hnegativeFour
    have hnonnegativeFour := hfour parent hparent (k + (start : ℤ))
    exact (not_lt_of_ge hnonnegativeFour) hnegativeFour
  · exact
      not_supportMinimalNegativeMonotoneBlock_length_five_of_realFiveCellRemoteRow
        hfour hrow hparent hmin hlen

/-! ## All-length common-parent middle-pivot induction -/

/-- Production nonnegativity for all real common parents at one exact block
length. -/
def RealFiniteBlockProductionNonnegativeAtLength (n : ℕ) : Prop :=
  ∀ parent : BombieriTest,
    bombieriConjugateTest parent = parent →
      ∀ k : ℤ,
        0 ≤ bombieriRealQuadraticValue
          (monotoneQuarterFiniteBlock parent k 0 n)

/-- Production nonnegativity through a prescribed finite block length. -/
def RealFiniteBlockProductionNonnegativeUpTo (n : ℕ) : Prop :=
  ∀ m : ℕ, m ≤ n → RealFiniteBlockProductionNonnegativeAtLength m

/-- The interior obtained by deleting both endpoint cells from an
`n`-cell block. -/
def monotoneQuarterFiniteBlockInterior
    (parent : BombieriTest) (k : ℤ) (n : ℕ) : BombieriTest :=
  monotoneQuarterFiniteBlock parent k 1 (n - 2)

private theorem monotoneQuarterFiniteBlock_zero_apply_allLength
    (parent : BombieriTest) (k : ℤ) (n : ℕ) (x : ℝ) :
    monotoneQuarterFiniteBlock parent k 0 n x =
      (((monotoneQuarterStep k x -
        monotoneQuarterStep (k + (n : ℤ)) x : ℝ) : ℂ) * parent x) := by
  unfold monotoneQuarterFiniteBlock
  simp only [Nat.zero_add]
  rw [sum_range_monotoneQuarterCell_eq_cutoff_sub]
  simp only [TestFunction.coe_sub, Pi.sub_apply,
    monotoneQuarterCutoff_apply]
  push_cast
  ring

private theorem monotoneQuarterFiniteBlock_add_allLength
    (f g : BombieriTest) (k : ℤ) (n : ℕ) :
    monotoneQuarterFiniteBlock (f + g) k 0 n =
      monotoneQuarterFiniteBlock f k 0 n +
        monotoneQuarterFiniteBlock g k 0 n := by
  classical
  unfold monotoneQuarterFiniteBlock
  simp_rw [monotoneQuarterCell_add]
  exact Finset.sum_add_distrib

private theorem monotoneQuarterFiniteBlock_smul_allLength
    (c : ℂ) (f : BombieriTest) (k : ℤ) (n : ℕ) :
    monotoneQuarterFiniteBlock (c • f) k 0 n =
      c • monotoneQuarterFiniteBlock f k 0 n := by
  classical
  unfold monotoneQuarterFiniteBlock
  simp_rw [monotoneQuarterCell_smul]
  exact Finset.smul_sum.symm

private theorem monotoneQuarterFiniteBlock_eq_endpoint_add_tail
    (parent : BombieriTest) (k : ℤ) (n : ℕ) (hn : 1 ≤ n) :
    monotoneQuarterFiniteBlock parent k 0 n =
      monotoneQuarterCell parent k +
        monotoneQuarterFiniteBlock parent k 1 (n - 1) := by
  have hsplit := monotoneQuarterFiniteBlock_eq_prefix_add_suffix
    parent k 0 n 1 hn
  simpa only [monotoneQuarterFiniteBlock_one,
    monotoneQuarterFiniteBlockBase, Int.ofNat_zero, add_zero,
    Nat.zero_add] using hsplit

private theorem monotoneQuarterFiniteBlock_eq_head_add_endpoint
    (parent : BombieriTest) (k : ℤ) (n : ℕ) (hn : 1 ≤ n) :
    monotoneQuarterFiniteBlock parent k 1 n =
      monotoneQuarterFiniteBlock parent k 1 (n - 1) +
        monotoneQuarterCell parent (k + (n : ℤ)) := by
  have hsplit := monotoneQuarterFiniteBlock_eq_prefix_add_suffix
    parent k 1 n (n - 1) (by omega)
  have hsub : n - (n - 1) = 1 := by omega
  rw [hsub, monotoneQuarterFiniteBlock_one] at hsplit
  have hindex : 1 + (n - 1) = n := by omega
  simpa only [monotoneQuarterFiniteBlockBase, hindex] using hsplit

private theorem monotoneQuarterFiniteBlock_shift_start_one
    (parent : BombieriTest) (k : ℤ) (n : ℕ) :
    monotoneQuarterFiniteBlock parent (k + 1) 0 n =
      monotoneQuarterFiniteBlock parent k 1 n := by
  classical
  unfold monotoneQuarterFiniteBlock
  apply Finset.sum_congr rfl
  intro i _hi
  congr 1
  push_cast
  ring

/-- Pointwise telescope for the interior obtained by deleting both endpoint
cells.  Its only multiplier is the difference of the two boundary cutoff
steps. -/
theorem monotoneQuarterFiniteBlockInterior_apply
    (parent : BombieriTest) (k : ℤ) (n : ℕ) (hn : 2 ≤ n) (x : ℝ) :
    monotoneQuarterFiniteBlockInterior parent k n x =
      (((monotoneQuarterStep (k + 1) x -
        monotoneQuarterStep
          (k + ((n - 1 : ℕ) : ℤ)) x : ℝ) : ℂ) * parent x) := by
  rw [monotoneQuarterFiniteBlockInterior,
    ← monotoneQuarterFiniteBlock_shift_start_one,
    monotoneQuarterFiniteBlock_zero_apply_allLength]
  have hsub : n - 2 + 1 = n - 1 := by omega
  have hindex : k + 1 + ((n - 2 : ℕ) : ℤ) =
      k + ((n - 1 : ℕ) : ℤ) := by
    calc
      k + 1 + ((n - 2 : ℕ) : ℤ) =
          k + (((n - 2) + 1 : ℕ) : ℤ) := by push_cast; ring
      _ = k + ((n - 1 : ℕ) : ℤ) := by rw [hsub]
  rw [hindex]

private theorem monotoneQuarterStep_lt_one_of_lt_next
    (j : ℤ) {x : ℝ}
    (hx : x < quarterLogLatticePoint (j + 1)) :
    monotoneQuarterStep j x < 1 := by
  unfold monotoneQuarterStep
  apply Real.smoothTransition.lt_one_of_lt_one
  rw [div_lt_one (quarterLogLatticePoint_gap_pos j)]
  linarith

private theorem finiteBlock_parent_eq_zero_of_interior_zero_of_leftTransition
    (parent : BombieriTest) (k : ℤ) (n : ℕ) (hn : 4 ≤ n)
    (hmiddle : monotoneQuarterFiniteBlockInterior parent k n = 0)
    {x : ℝ}
    (hxleft : quarterLogLatticePoint (k + 1) < x)
    (hxright : x < quarterLogLatticePoint (k + 2)) :
    parent x = 0 := by
  have hpoint := congrArg (fun g : BombieriTest ↦ g x) hmiddle
  have hpoint' :
      monotoneQuarterFiniteBlockInterior parent k n x = 0 := by
    simpa only [TestFunction.coe_zero, Pi.zero_apply] using hpoint
  rw [monotoneQuarterFiniteBlockInterior_apply parent k n (by omega)] at hpoint'
  have hstepPos : 0 < monotoneQuarterStep (k + 1) x :=
    monotoneQuarterStep_pos_of_lattice_lt (k + 1) hxleft
  have hstepZero :
      monotoneQuarterStep (k + ((n - 1 : ℕ) : ℤ)) x = 0 := by
    apply monotoneQuarterStep_eq_zero_of_le
    exact hxright.le.trans (quarterLogLatticePoint_mono (by omega))
  rw [hstepZero, sub_zero] at hpoint'
  exact (mul_eq_zero.mp hpoint').resolve_left
    (Complex.ofReal_ne_zero.mpr hstepPos.ne')

private theorem finiteBlock_parent_eq_zero_of_interior_zero_of_rightTransition
    (parent : BombieriTest) (k : ℤ) (n : ℕ) (hn : 4 ≤ n)
    (hmiddle : monotoneQuarterFiniteBlockInterior parent k n = 0)
    {x : ℝ}
    (hxleft :
      quarterLogLatticePoint (k + ((n - 1 : ℕ) : ℤ)) < x)
    (hxright :
      x < quarterLogLatticePoint (k + ((n - 1 : ℕ) : ℤ) + 1)) :
    parent x = 0 := by
  have hpoint := congrArg (fun g : BombieriTest ↦ g x) hmiddle
  have hpoint' :
      monotoneQuarterFiniteBlockInterior parent k n x = 0 := by
    simpa only [TestFunction.coe_zero, Pi.zero_apply] using hpoint
  rw [monotoneQuarterFiniteBlockInterior_apply parent k n (by omega)] at hpoint'
  have hstepOne : monotoneQuarterStep (k + 1) x = 1 := by
    apply monotoneQuarterStep_eq_one_of_le
    exact (quarterLogLatticePoint_mono (by omega)).trans hxleft.le
  have hstepLt :
      monotoneQuarterStep (k + ((n - 1 : ℕ) : ℤ)) x < 1 :=
    monotoneQuarterStep_lt_one_of_lt_next
      (k + ((n - 1 : ℕ) : ℤ)) hxright
  rw [hstepOne] at hpoint'
  exact (mul_eq_zero.mp hpoint').resolve_left
    (Complex.ofReal_ne_zero.mpr (sub_pos.mpr hstepLt).ne')

/-- If an arbitrary-length interior test itself vanishes, both endpoint
cells collapse from their two-step supports to the two outward transition
intervals.  This is the all-length support geometry hidden in the singular
middle-pivot branch. -/
theorem finiteBlock_endpoint_tsupports_collapse_of_interior_zero
    (parent : BombieriTest) (k : ℤ) (n : ℕ) (hn : 4 ≤ n)
    (hmiddle : monotoneQuarterFiniteBlockInterior parent k n = 0) :
    tsupport (monotoneQuarterCell parent k : ℝ → ℂ) ⊆
        Set.Icc (quarterLogLatticePoint k)
          (quarterLogLatticePoint (k + 1)) ∧
      tsupport
          (monotoneQuarterCell parent
            (k + ((n - 1 : ℕ) : ℤ)) : ℝ → ℂ) ⊆
        Set.Icc
          (quarterLogLatticePoint
            (k + ((n - 1 : ℕ) : ℤ) + 1))
          (quarterLogLatticePoint
            (k + ((n - 1 : ℕ) : ℤ) + 2)) := by
  constructor
  · rw [tsupport]
    apply closure_minimal _ isClosed_Icc
    intro x hx
    have hxne : monotoneQuarterCell parent k x ≠ 0 :=
      Function.mem_support.mp hx
    have hwide := monotoneQuarterCell_tsupport_subset parent k
      (subset_tsupport _ hx)
    refine ⟨hwide.1, ?_⟩
    by_contra hnot
    have hxleft : quarterLogLatticePoint (k + 1) < x :=
      lt_of_not_ge hnot
    by_cases hxright : quarterLogLatticePoint (k + 2) ≤ x
    · apply hxne
      rw [monotoneQuarterCell_apply,
        monotoneQuarterWeight_eq_zero_of_le_left k hxright]
      simp
    · have hparent : parent x = 0 :=
        finiteBlock_parent_eq_zero_of_interior_zero_of_leftTransition
          parent k n hn hmiddle hxleft (lt_of_not_ge hxright)
      apply hxne
      rw [monotoneQuarterCell_apply, hparent, mul_zero]
  · rw [tsupport]
    apply closure_minimal _ isClosed_Icc
    intro x hx
    have hxne :
        monotoneQuarterCell parent
          (k + ((n - 1 : ℕ) : ℤ)) x ≠ 0 :=
      Function.mem_support.mp hx
    have hwide := monotoneQuarterCell_tsupport_subset parent
      (k + ((n - 1 : ℕ) : ℤ)) (subset_tsupport _ hx)
    refine ⟨?_, hwide.2⟩
    by_contra hnot
    have hxright :
        x < quarterLogLatticePoint
          (k + ((n - 1 : ℕ) : ℤ) + 1) :=
      lt_of_not_ge hnot
    by_cases hxleft :
        x ≤ quarterLogLatticePoint (k + ((n - 1 : ℕ) : ℤ))
    · apply hxne
      rw [monotoneQuarterCell_apply,
        monotoneQuarterWeight_eq_zero_of_le
          (k + ((n - 1 : ℕ) : ℤ)) hxleft]
      simp
    · have hparent : parent x = 0 :=
        finiteBlock_parent_eq_zero_of_interior_zero_of_rightTransition
          parent k n hn hmiddle (lt_of_not_ge hxleft) hxright
      apply hxne
      rw [monotoneQuarterCell_apply, hparent, mul_zero]

/-- Every nonzero conjugation-fixed ratio-two test has strictly positive
complete Bombieri quadratic value.  This packages local coercivity and the
exact absence of prime terms at support ratio at most two. -/
theorem bombieriRealQuadraticValue_pos_of_ratioTwoCell_of_real_of_ne_zero
    (m : BombieriTest) (hcell : BombieriRatioTwoCell m)
    (hmreal : bombieriConjugateTest m = m) (hm : m ≠ 0) :
    0 < bombieriRealQuadraticValue m := by
  have hcoercive := real_ratioTwo_localCriticalForm_re_ge_criticalLogEnergy
    m hcell hmreal
  have henergy : 0 < bombieriCriticalLogEnergy m :=
    bombieriCriticalLogEnergy_pos_of_ne_zero m hm
  have hlocal : 0 < (bombieriLocalCriticalForm m m).re := by
    have hcoeff : 0 < (1 / 12000 : ℝ) := by norm_num
    exact lt_of_lt_of_le (mul_pos hcoeff henergy) hcoercive
  obtain ⟨a, b, ha, hab, hsupport, hratio⟩ := hcell
  have heq := bombieriFunctional_quadratic_eq_bombieriLocalCriticalForm_le_two
    m ha hab hsupport hratio
  unfold bombieriRealQuadraticValue
  rw [heq]
  exact hlocal

/-- A nonzero real production block of at most three consecutive cells has
strictly positive complete Bombieri quadratic value.  The ratio-two local
coercivity therefore has no quadratic null vectors on these short blocks. -/
theorem bombieriRealQuadraticValue_monotoneQuarterFiniteBlock_pos_of_le_three_of_ne_zero
    (parent : BombieriTest)
    (hparent : bombieriConjugateTest parent = parent)
    (lo : ℤ) (start len : ℕ) (hlen : len ≤ 3)
    (hblock : monotoneQuarterFiniteBlock parent lo start len ≠ 0) :
    0 < bombieriRealQuadraticValue
      (monotoneQuarterFiniteBlock parent lo start len) := by
  apply bombieriRealQuadraticValue_pos_of_ratioTwoCell_of_real_of_ne_zero
  · exact monotoneQuarterFiniteBlock_ratioTwo_of_le_three
      parent lo start len hlen
  · exact bombieriConjugateTest_monotoneQuarterFiniteBlock
      parent hparent lo start len
  · exact hblock

/-- Through length five, a zero interior diagonal is already a zero interior
test: deleting the two endpoints leaves at most three ratio-two cells. -/
theorem monotoneQuarterFiniteBlockInterior_eq_zero_of_quadratic_eq_zero_of_le_five
    (parent : BombieriTest)
    (hparent : bombieriConjugateTest parent = parent)
    (k : ℤ) (n : ℕ) (hnLower : 4 ≤ n) (hnUpper : n ≤ 5)
    (hzero : bombieriRealQuadraticValue
      (monotoneQuarterFiniteBlockInterior parent k n) = 0) :
    monotoneQuarterFiniteBlockInterior parent k n = 0 := by
  by_contra hne
  have hpositive :=
    bombieriRealQuadraticValue_monotoneQuarterFiniteBlock_pos_of_le_three_of_ne_zero
      parent hparent k 1 (n - 2) (by omega) (by
        simpa only [monotoneQuarterFiniteBlockInterior] using hne)
  have hzero' : bombieriRealQuadraticValue
      (monotoneQuarterFiniteBlock parent k 1 (n - 2)) = 0 := by
    simpa only [monotoneQuarterFiniteBlockInterior] using hzero
  rw [hzero'] at hpositive
  exact (lt_irrefl 0) hpositive

/-- Hence at lengths four and five the singular quadratic branch already
inherits the exact outward endpoint-support collapse.  Length six is the
first place where quadratic-null coercivity becomes a genuinely new issue. -/
theorem finiteBlock_endpoint_tsupports_collapse_of_interior_quadratic_zero_of_le_five
    (parent : BombieriTest)
    (hparent : bombieriConjugateTest parent = parent)
    (k : ℤ) (n : ℕ) (hnLower : 4 ≤ n) (hnUpper : n ≤ 5)
    (hzero : bombieriRealQuadraticValue
      (monotoneQuarterFiniteBlockInterior parent k n) = 0) :
    tsupport (monotoneQuarterCell parent k : ℝ → ℂ) ⊆
        Set.Icc (quarterLogLatticePoint k)
          (quarterLogLatticePoint (k + 1)) ∧
      tsupport
          (monotoneQuarterCell parent
            (k + ((n - 1 : ℕ) : ℤ)) : ℝ → ℂ) ⊆
        Set.Icc
          (quarterLogLatticePoint
            (k + ((n - 1 : ℕ) : ℤ) + 1))
          (quarterLogLatticePoint
            (k + ((n - 1 : ℕ) : ℤ) + 2)) := by
  apply finiteBlock_endpoint_tsupports_collapse_of_interior_zero
    parent k n hnLower
  exact
    monotoneQuarterFiniteBlockInterior_eq_zero_of_quadratic_eq_zero_of_le_five
      parent hparent k n hnLower hnUpper hzero

/-- At the first singular length, the collapsed right endpoint interval is
exactly twice the collapsed left interval.  Thus the length-four singular
branch is a pure factor-two endpoint problem, with no residual wider support
or additional prime window. -/
theorem fourCell_endpoint_tsupports_factorTwo_collapse_of_interior_quadratic_zero
    (parent : BombieriTest)
    (hparent : bombieriConjugateTest parent = parent)
    (k : ℤ)
    (hzero : bombieriRealQuadraticValue
      (monotoneQuarterFiniteBlockInterior parent k 4) = 0) :
    tsupport (monotoneQuarterCell parent k : ℝ → ℂ) ⊆
        Set.Icc (quarterLogLatticePoint k)
          (quarterLogLatticePoint (k + 1)) ∧
      tsupport (monotoneQuarterCell parent (k + 3) : ℝ → ℂ) ⊆
        Set.Icc (2 * quarterLogLatticePoint k)
          (2 * quarterLogLatticePoint (k + 1)) := by
  have hcollapse :=
    finiteBlock_endpoint_tsupports_collapse_of_interior_quadratic_zero_of_le_five
      parent hparent k 4 (by omega) (by omega) hzero
  constructor
  · exact hcollapse.1
  · simpa only [Nat.reduceSubDiff, Nat.cast_ofNat,
      show k + 3 + 1 = k + 4 by ring,
      show k + 3 + 2 = (k + 1) + 4 by ring,
      quarterLogLatticePoint_add_four] using hcollapse.2

private theorem finiteBlock_parent_sub_nextCutoff_eq_leftEndpoint_allLength
    (parent : BombieriTest) (k : ℤ) (n : ℕ) (hn : 2 ≤ n) :
    monotoneQuarterFiniteBlock
        (parent - monotoneQuarterCutoff parent (k + 1)) k 0 n =
      monotoneQuarterCell parent k := by
  apply TestFunction.ext
  intro x
  rw [monotoneQuarterFiniteBlock_zero_apply_allLength,
    monotoneQuarterCell_apply]
  simp only [TestFunction.coe_sub, Pi.sub_apply,
    monotoneQuarterCutoff_apply]
  have hk1 := monotoneQuarterStep_mul_later
    (k := k) (j := k + 1) (by omega) x
  have h1n := monotoneQuarterStep_mul_later
    (k := k + 1) (j := k + (n : ℤ)) (by omega) x
  have hmask :
      (monotoneQuarterStep k x -
          monotoneQuarterStep (k + (n : ℤ)) x) *
        (1 - monotoneQuarterStep (k + 1) x) =
      monotoneQuarterWeight k x := by
    unfold monotoneQuarterWeight
    calc
      (monotoneQuarterStep k x -
            monotoneQuarterStep (k + (n : ℤ)) x) *
          (1 - monotoneQuarterStep (k + 1) x) =
        monotoneQuarterStep k x -
          monotoneQuarterStep k x * monotoneQuarterStep (k + 1) x -
          monotoneQuarterStep (k + (n : ℤ)) x +
          monotoneQuarterStep (k + 1) x *
            monotoneQuarterStep (k + (n : ℤ)) x := by ring
      _ = monotoneQuarterStep k x -
          monotoneQuarterStep (k + 1) x := by
        rw [hk1, h1n]
        ring
  change
    (↑(monotoneQuarterStep k x -
        monotoneQuarterStep (k + (n : ℤ)) x) : ℂ) *
        (parent x - ↑(monotoneQuarterStep (k + 1) x) * parent x) =
      (monotoneQuarterWeight k x : ℂ) * parent x
  calc
    (↑(monotoneQuarterStep k x -
          monotoneQuarterStep (k + (n : ℤ)) x) : ℂ) *
          (parent x - ↑(monotoneQuarterStep (k + 1) x) * parent x) =
        (↑((monotoneQuarterStep k x -
            monotoneQuarterStep (k + (n : ℤ)) x) *
              (1 - monotoneQuarterStep (k + 1) x)) : ℂ) * parent x := by
      push_cast
      ring
    _ = (monotoneQuarterWeight k x : ℂ) * parent x := by rw [hmask]

private theorem finiteBlock_rightCutoff_eq_rightEndpoint_allLength
    (parent : BombieriTest) (k : ℤ) (n : ℕ) (hn : 2 ≤ n) :
    monotoneQuarterFiniteBlock
        (monotoneQuarterCutoff parent (k + (n : ℤ))) (k + 1) 0 n =
      monotoneQuarterCell parent (k + (n : ℤ)) := by
  apply TestFunction.ext
  intro x
  rw [monotoneQuarterFiniteBlock_zero_apply_allLength,
    monotoneQuarterCell_apply]
  simp only [monotoneQuarterCutoff_apply]
  have h1n := monotoneQuarterStep_mul_later
    (k := k + 1) (j := k + (n : ℤ)) (by omega) x
  have hnnext := monotoneQuarterStep_mul_later
    (k := k + (n : ℤ)) (j := (k + 1) + (n : ℤ)) (by omega) x
  have hindex : (k + 1) + (n : ℤ) = k + (n : ℤ) + 1 := by ring
  rw [hindex] at hnnext
  have hmask :
      (monotoneQuarterStep (k + 1) x -
          monotoneQuarterStep ((k + 1) + (n : ℤ)) x) *
        monotoneQuarterStep (k + (n : ℤ)) x =
      monotoneQuarterWeight (k + (n : ℤ)) x := by
    unfold monotoneQuarterWeight
    rw [hindex]
    calc
      (monotoneQuarterStep (k + 1) x -
            monotoneQuarterStep (k + (n : ℤ) + 1) x) *
          monotoneQuarterStep (k + (n : ℤ)) x =
        monotoneQuarterStep (k + 1) x *
            monotoneQuarterStep (k + (n : ℤ)) x -
          monotoneQuarterStep (k + (n : ℤ)) x *
            monotoneQuarterStep (k + (n : ℤ) + 1) x := by ring
      _ = monotoneQuarterStep (k + (n : ℤ)) x -
          monotoneQuarterStep (k + (n : ℤ) + 1) x := by
        rw [h1n, hnnext]
  change
    (↑(monotoneQuarterStep (k + 1) x -
        monotoneQuarterStep ((k + 1) + (n : ℤ)) x) : ℂ) *
        (↑(monotoneQuarterStep (k + (n : ℤ)) x) * parent x) =
      (monotoneQuarterWeight (k + (n : ℤ)) x : ℂ) * parent x
  calc
    (↑(monotoneQuarterStep (k + 1) x -
          monotoneQuarterStep ((k + 1) + (n : ℤ)) x) : ℂ) *
          (↑(monotoneQuarterStep (k + (n : ℤ)) x) * parent x) =
        (↑((monotoneQuarterStep (k + 1) x -
            monotoneQuarterStep ((k + 1) + (n : ℤ)) x) *
              monotoneQuarterStep (k + (n : ℤ)) x) : ℂ) * parent x := by
      push_cast
      ring
    _ = (monotoneQuarterWeight (k + (n : ℤ)) x : ℂ) * parent x := by
      rw [hmask]

private theorem conjugate_fixed_real_smul_allLength
    {f : BombieriTest} (hf : bombieriConjugateTest f = f) (c : ℝ) :
    bombieriConjugateTest ((c : ℂ) • f) = (c : ℂ) • f := by
  rw [bombieriConjugateTest_smul, Complex.conj_ofReal, hf]

private theorem exists_realParent_finiteBlock_eq_leftEndpoint_add_smul_middle
    (parent : BombieriTest)
    (hparent : bombieriConjugateTest parent = parent)
    (k : ℤ) (n : ℕ) (hn : 2 ≤ n) (t : ℝ) :
    ∃ modified : BombieriTest,
      bombieriConjugateTest modified = modified ∧
        monotoneQuarterFiniteBlock modified k 0 n =
          monotoneQuarterCell parent k +
            (t : ℂ) • monotoneQuarterFiniteBlock parent k 1 (n - 1) := by
  let endpointParent : BombieriTest :=
    parent - monotoneQuarterCutoff parent (k + 1)
  let modified : BombieriTest :=
    (t : ℂ) • parent + ((1 - t : ℝ) : ℂ) • endpointParent
  have hendpoint : bombieriConjugateTest endpointParent = endpointParent := by
    dsimp only [endpointParent]
    exact conjugate_fixed_sub_for_remoteGap hparent
      (bombieriConjugateTest_monotoneQuarterCutoff parent hparent (k + 1))
  refine ⟨modified, ?_, ?_⟩
  · dsimp only [modified]
    rw [bombieriConjugateTest_add,
      conjugate_fixed_real_smul_allLength hparent t,
      conjugate_fixed_real_smul_allLength hendpoint (1 - t)]
  · dsimp only [modified]
    rw [monotoneQuarterFiniteBlock_add_allLength,
      monotoneQuarterFiniteBlock_smul_allLength,
      monotoneQuarterFiniteBlock_smul_allLength,
      monotoneQuarterFiniteBlock_eq_endpoint_add_tail parent k n (by omega),
      show monotoneQuarterFiniteBlock endpointParent k 0 n =
          monotoneQuarterCell parent k by
        exact finiteBlock_parent_sub_nextCutoff_eq_leftEndpoint_allLength
          parent k n hn]
    module

private theorem exists_realParent_finiteBlock_eq_middle_add_smul_rightEndpoint
    (parent : BombieriTest)
    (hparent : bombieriConjugateTest parent = parent)
    (k : ℤ) (n : ℕ) (hn : 2 ≤ n) (t : ℝ) :
    ∃ modified : BombieriTest,
      bombieriConjugateTest modified = modified ∧
        monotoneQuarterFiniteBlock modified (k + 1) 0 n =
          monotoneQuarterFiniteBlock parent k 1 (n - 1) +
            (t : ℂ) • monotoneQuarterCell parent (k + (n : ℤ)) := by
  let endpointParent : BombieriTest :=
    monotoneQuarterCutoff parent (k + (n : ℤ))
  let modified : BombieriTest :=
    parent + ((t - 1 : ℝ) : ℂ) • endpointParent
  have hendpoint : bombieriConjugateTest endpointParent = endpointParent := by
    dsimp only [endpointParent]
    exact bombieriConjugateTest_monotoneQuarterCutoff
      parent hparent (k + (n : ℤ))
  refine ⟨modified, ?_, ?_⟩
  · dsimp only [modified]
    rw [bombieriConjugateTest_add, hparent,
      conjugate_fixed_real_smul_allLength hendpoint (t - 1)]
  · dsimp only [modified]
    rw [monotoneQuarterFiniteBlock_add_allLength,
      monotoneQuarterFiniteBlock_smul_allLength,
      monotoneQuarterFiniteBlock_shift_start_one,
      monotoneQuarterFiniteBlock_eq_head_add_endpoint parent k n (by omega),
      show monotoneQuarterFiniteBlock endpointParent (k + 1) 0 n =
          monotoneQuarterCell parent (k + (n : ℤ)) by
        exact finiteBlock_rightCutoff_eq_rightEndpoint_allLength
          parent k n hn]
    module

private theorem monotoneQuarterFiniteBlockInterior_add
    (f g : BombieriTest) (k : ℤ) (n : ℕ) :
    monotoneQuarterFiniteBlockInterior (f + g) k n =
      monotoneQuarterFiniteBlockInterior f k n +
        monotoneQuarterFiniteBlockInterior g k n := by
  unfold monotoneQuarterFiniteBlockInterior
  rw [← monotoneQuarterFiniteBlock_shift_start_one (f + g),
    ← monotoneQuarterFiniteBlock_shift_start_one f,
    ← monotoneQuarterFiniteBlock_shift_start_one g,
    monotoneQuarterFiniteBlock_add_allLength]

private theorem monotoneQuarterFiniteBlockInterior_smul
    (c : ℂ) (f : BombieriTest) (k : ℤ) (n : ℕ) :
    monotoneQuarterFiniteBlockInterior (c • f) k n =
      c • monotoneQuarterFiniteBlockInterior f k n := by
  unfold monotoneQuarterFiniteBlockInterior
  rw [← monotoneQuarterFiniteBlock_shift_start_one (c • f),
    ← monotoneQuarterFiniteBlock_shift_start_one f,
    monotoneQuarterFiniteBlock_smul_allLength]

private theorem bombieriRealQuadraticValue_add_real_smul_allLength
    (f g : BombieriTest) (t : ℝ) :
    bombieriRealQuadraticValue (f + (t : ℂ) • g) =
      bombieriRealQuadraticValue f +
        t ^ 2 * bombieriRealQuadraticValue g +
          2 * t * (bombieriTwoBlockGlobalCrossSymbol f g).re := by
  unfold bombieriRealQuadraticValue
  have h := bombieriFunctional_twoBlock_re f g (t : ℂ)
  simpa only [Complex.normSq_apply, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, add_zero, Complex.mul_re,
    zero_mul, sub_zero, pow_two, mul_assoc] using h

private theorem real_two_by_two_determinant_of_all_nonnegative_allLength
    {A B U : ℝ} (hB : 0 ≤ B)
    (hall : ∀ t : ℝ, 0 ≤ A + t ^ 2 * B + 2 * t * U) :
    U ^ 2 ≤ A * B := by
  by_cases hBzero : B = 0
  · have hU : U = 0 := by
      by_contra hUne
      let t : ℝ := -(A + 1) / (2 * U)
      have h := hall t
      have hid : A + t ^ 2 * B + 2 * t * U = -1 := by
        dsimp only [t]
        rw [hBzero, mul_zero, add_zero]
        field_simp [hUne]
        ring
      rw [hid] at h
      linarith
    rw [hBzero, hU]
    norm_num
  · have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hBzero)
    have h := hall (-U / B)
    have hid : A + (-U / B) ^ 2 * B + 2 * (-U / B) * U =
        (A * B - U ^ 2) / B := by
      field_simp [hBzero]
      ring
    rw [hid] at h
    rcases (div_nonneg_iff.mp h) with hpos | hneg
    · exact sub_nonneg.mp hpos.1
    · exact (not_le_of_gt hBpos hneg.2).elim

/-- Under positivity at the shorter interior length, a zero interior
diagonal is a radical vector for every real common-parent variation of that
same interior block.  This is the exact structural information available in
the long singular branch even when zero quadratic value does not force the
test itself to vanish. -/
theorem finiteBlockInterior_globalCross_eq_zero_of_previousLengths_and_quadratic_zero
    (n : ℕ) (hn : 4 ≤ n)
    (hprev : RealFiniteBlockProductionNonnegativeUpTo (n - 1))
    (parent : BombieriTest)
    (hparent : bombieriConjugateTest parent = parent)
    (k : ℤ)
    (hzero : bombieriRealQuadraticValue
      (monotoneQuarterFiniteBlockInterior parent k n) = 0)
    (variation : BombieriTest)
    (hvariation : bombieriConjugateTest variation = variation) :
    (bombieriTwoBlockGlobalCrossSymbol
      (monotoneQuarterFiniteBlockInterior parent k n)
      (monotoneQuarterFiniteBlockInterior variation k n)).re = 0 := by
  let m : BombieriTest :=
    monotoneQuarterFiniteBlockInterior parent k n
  let g : BombieriTest :=
    monotoneQuarterFiniteBlockInterior variation k n
  let B : ℝ := bombieriRealQuadraticValue g
  let U : ℝ := (bombieriTwoBlockGlobalCrossSymbol m g).re
  have hgShift :
      monotoneQuarterFiniteBlock variation (k + 1) 0 (n - 2) = g := by
    dsimp only [g, monotoneQuarterFiniteBlockInterior]
    exact monotoneQuarterFiniteBlock_shift_start_one variation k (n - 2)
  have hB : 0 ≤ B := by
    have hnonnegative :=
      hprev (n - 2) (by omega) variation hvariation (k + 1)
    rw [hgShift] at hnonnegative
    exact hnonnegative
  have hdet : U ^ 2 ≤ bombieriRealQuadraticValue m * B := by
    apply real_two_by_two_determinant_of_all_nonnegative_allLength hB
    intro t
    let modified : BombieriTest := parent + (t : ℂ) • variation
    have hmodified : bombieriConjugateTest modified = modified := by
      dsimp only [modified]
      rw [bombieriConjugateTest_add, hparent,
        conjugate_fixed_real_smul_allLength hvariation t]
    have hnonnegative :=
      hprev (n - 2) (by omega) modified hmodified (k + 1)
    have hmodifiedShift :
        monotoneQuarterFiniteBlock modified (k + 1) 0 (n - 2) =
          monotoneQuarterFiniteBlockInterior modified k n := by
      exact monotoneQuarterFiniteBlock_shift_start_one modified k (n - 2)
    rw [hmodifiedShift,
      show monotoneQuarterFiniteBlockInterior modified k n =
          m + (t : ℂ) • g by
        dsimp only [modified, m, g]
        rw [monotoneQuarterFiniteBlockInterior_add,
          monotoneQuarterFiniteBlockInterior_smul],
      bombieriRealQuadraticValue_add_real_smul_allLength] at hnonnegative
    exact hnonnegative
  have hmzero : bombieriRealQuadraticValue m = 0 := by
    simpa only [m] using hzero
  rw [hmzero, zero_mul] at hdet
  have hU : U = 0 := by nlinarith [sq_nonneg U]
  exact hU

/-- Positivity through length `n-1` supplies both adjacent principal minors
of the endpoint--interior--endpoint matrix for an arbitrary `n`-cell common
parent block.  The proof uses the all-length modified-parent pencils above,
so no independence of the three blocks is assumed. -/
theorem finiteBlock_adjacentPrincipalMinors_of_previousLengths
    (n : ℕ) (hn : 4 ≤ n)
    (hprev : RealFiniteBlockProductionNonnegativeUpTo (n - 1))
    (parent : BombieriTest)
    (hparent : bombieriConjugateTest parent = parent) (k : ℤ) :
    let a := monotoneQuarterCell parent k
    let m := monotoneQuarterFiniteBlockInterior parent k n
    let e := monotoneQuarterCell parent (k + ((n - 1 : ℕ) : ℤ))
    let A := bombieriRealQuadraticValue a
    let M := bombieriRealQuadraticValue m
    let E := bombieriRealQuadraticValue e
    let U := (bombieriTwoBlockGlobalCrossSymbol a m).re
    let V := (bombieriTwoBlockGlobalCrossSymbol m e).re
    U ^ 2 ≤ A * M ∧ V ^ 2 ≤ M * E := by
  dsimp only
  let p : ℕ := n - 1
  let a : BombieriTest := monotoneQuarterCell parent k
  let m : BombieriTest := monotoneQuarterFiniteBlockInterior parent k n
  let e : BombieriTest :=
    monotoneQuarterCell parent (k + ((n - 1 : ℕ) : ℤ))
  let A : ℝ := bombieriRealQuadraticValue a
  let M : ℝ := bombieriRealQuadraticValue m
  let E : ℝ := bombieriRealQuadraticValue e
  let U : ℝ := (bombieriTwoBlockGlobalCrossSymbol a m).re
  let V : ℝ := (bombieriTwoBlockGlobalCrossSymbol m e).re
  have hp : 2 ≤ p := by dsimp only [p]; omega
  have hmLength : p - 1 = n - 2 := by dsimp only [p]; omega
  have hmShift :
      monotoneQuarterFiniteBlock parent (k + 1) 0 (n - 2) = m := by
    dsimp only [m, monotoneQuarterFiniteBlockInterior]
    exact monotoneQuarterFiniteBlock_shift_start_one parent k (n - 2)
  have hM : 0 ≤ M := by
    have hmiddle := hprev (n - 2) (by omega) parent hparent (k + 1)
    rw [hmShift] at hmiddle
    exact hmiddle
  have hE : 0 ≤ E := by
    dsimp only [E, e]
    exact bombieriFunctional_quadratic_re_nonneg_of_ratioTwoCell _
      (monotoneQuarterCell_ratioTwo parent
        (k + ((n - 1 : ℕ) : ℤ)))
  constructor
  · apply real_two_by_two_determinant_of_all_nonnegative_allLength hM
    intro t
    obtain ⟨modified, hmodified, hblock⟩ :=
      exists_realParent_finiteBlock_eq_leftEndpoint_add_smul_middle
        parent hparent k p hp t
    rw [hmLength] at hblock
    change monotoneQuarterFiniteBlock modified k 0 p =
      a + (t : ℂ) • m at hblock
    rw [← bombieriRealQuadraticValue_add_real_smul_allLength]
    rw [← hblock]
    exact hprev p (by dsimp only [p]; omega) modified hmodified k
  · apply real_two_by_two_determinant_of_all_nonnegative_allLength hE
    intro t
    obtain ⟨modified, hmodified, hblock⟩ :=
      exists_realParent_finiteBlock_eq_middle_add_smul_rightEndpoint
        parent hparent k p hp t
    rw [hmLength] at hblock
    change monotoneQuarterFiniteBlock modified (k + 1) 0 p =
      m + (t : ℂ) • e at hblock
    rw [← bombieriRealQuadraticValue_add_real_smul_allLength]
    rw [← hblock]
    exact hprev p (by dsimp only [p]; omega) modified hmodified (k + 1)

private theorem monotoneQuarterFiniteBlock_eq_endpoint_interior_endpoint
    (parent : BombieriTest) (k : ℤ) (n : ℕ) (hn : 3 ≤ n) :
    monotoneQuarterFiniteBlock parent k 0 n =
      (monotoneQuarterCell parent k +
        monotoneQuarterFiniteBlockInterior parent k n) +
        monotoneQuarterCell parent (k + ((n - 1 : ℕ) : ℤ)) := by
  rw [monotoneQuarterFiniteBlock_eq_endpoint_add_tail parent k n (by omega)]
  have htail := monotoneQuarterFiniteBlock_eq_head_add_endpoint
    parent k (n - 1) (by omega)
  have hlen : (n - 1) - 1 = n - 2 := by omega
  rw [hlen] at htail
  rw [htail]
  unfold monotoneQuarterFiniteBlockInterior
  module

/-- Lossless endpoint--interior--endpoint expansion at arbitrary length. -/
theorem bombieriRealQuadraticValue_finiteBlock_eq_threeBlock_allLength
    (parent : BombieriTest) (k : ℤ) (n : ℕ) (hn : 3 ≤ n) :
    let a := monotoneQuarterCell parent k
    let m := monotoneQuarterFiniteBlockInterior parent k n
    let e := monotoneQuarterCell parent (k + ((n - 1 : ℕ) : ℤ))
    let A := bombieriRealQuadraticValue a
    let M := bombieriRealQuadraticValue m
    let E := bombieriRealQuadraticValue e
    let U := (bombieriTwoBlockGlobalCrossSymbol a m).re
    let V := (bombieriTwoBlockGlobalCrossSymbol m e).re
    let X := (bombieriTwoBlockGlobalCrossSymbol a e).re
    bombieriRealQuadraticValue
        (monotoneQuarterFiniteBlock parent k 0 n) =
      A + M + E + 2 * (U + V + X) := by
  dsimp only
  rw [monotoneQuarterFiniteBlock_eq_endpoint_interior_endpoint
      parent k n hn,
    bombieriRealQuadraticValue_add, bombieriRealQuadraticValue_add,
    bombieriTwoBlockGlobalCrossSymbol_add_left, Complex.add_re]
  ring

/-- The positive-middle analytic input at one arbitrary length.  It asks
only for the sign of the exact conditional endpoint cross after pivoting
through the actual interior cut from the same common parent. -/
def RealFiniteBlockMiddlePivotConditionalCrossNonnegativeAtLength
    (n : ℕ) : Prop :=
  ∀ parent : BombieriTest,
    bombieriConjugateTest parent = parent →
      ∀ k : ℤ,
        let a := monotoneQuarterCell parent k
        let m := monotoneQuarterFiniteBlockInterior parent k n
        let e := monotoneQuarterCell parent
          (k + ((n - 1 : ℕ) : ℤ))
        let M := bombieriRealQuadraticValue m
        let U := (bombieriTwoBlockGlobalCrossSymbol a m).re
        let V := (bombieriTwoBlockGlobalCrossSymbol m e).re
        let X := (bombieriTwoBlockGlobalCrossSymbol a e).re
        0 < M → 0 ≤ M * X - U * V

/-- The left middle-orthogonal residual test for an arbitrary finite block. -/
def finiteBlockLeftMiddleOrthogonalResidual
    (parent : BombieriTest) (k : ℤ) (n : ℕ) : BombieriTest :=
  let a := monotoneQuarterCell parent k
  let m := monotoneQuarterFiniteBlockInterior parent k n
  let M := bombieriRealQuadraticValue m
  let U := (bombieriTwoBlockGlobalCrossSymbol a m).re
  (M : ℂ) • a + ((-U : ℝ) : ℂ) • m

/-- The right middle-orthogonal residual test for an arbitrary finite block. -/
def finiteBlockRightMiddleOrthogonalResidual
    (parent : BombieriTest) (k : ℤ) (n : ℕ) : BombieriTest :=
  let m := monotoneQuarterFiniteBlockInterior parent k n
  let e := monotoneQuarterCell parent (k + ((n - 1 : ℕ) : ℤ))
  let M := bombieriRealQuadraticValue m
  let V := (bombieriTwoBlockGlobalCrossSymbol m e).re
  (M : ℂ) • e + ((-V : ℝ) : ℂ) • m

/-- The actual common-parent residual-cross sign statement at one length. -/
def RealFiniteBlockMiddleOrthogonalResidualCrossNonnegativeAtLength
    (n : ℕ) : Prop :=
  ∀ parent : BombieriTest,
    bombieriConjugateTest parent = parent →
      ∀ k : ℤ,
        0 < bombieriRealQuadraticValue
            (monotoneQuarterFiniteBlockInterior parent k n) →
          0 ≤ (bombieriTwoBlockGlobalCrossSymbol
            (finiteBlockLeftMiddleOrthogonalResidual parent k n)
            (finiteBlockRightMiddleOrthogonalResidual parent k n)).re

private theorem bombieriTwoBlockGlobalCrossSymbol_real_smul_both_re_allLength
    (f g : BombieriTest) (a b : ℝ) :
    (bombieriTwoBlockGlobalCrossSymbol
      ((a : ℂ) • f) ((b : ℂ) • g)).re =
      a * b * (bombieriTwoBlockGlobalCrossSymbol f g).re := by
  rw [bombieriTwoBlockGlobalCrossSymbol_smul_left,
    bombieriTwoBlockGlobalCrossSymbol_smul_right]
  rw [show starRingEnd ℂ (a : ℂ) = (a : ℂ) by
    rw [starRingEnd_apply, Complex.star_def, Complex.conj_ofReal]]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  ring

private theorem bombieriTwoBlockGlobalCrossSymbol_real_linearCombination_re_allLength
    (f g h i : BombieriTest) (a b c d : ℝ) :
    (bombieriTwoBlockGlobalCrossSymbol
      ((a : ℂ) • f + (b : ℂ) • g)
      ((c : ℂ) • h + (d : ℂ) • i)).re =
      a * c * (bombieriTwoBlockGlobalCrossSymbol f h).re +
        a * d * (bombieriTwoBlockGlobalCrossSymbol f i).re +
        b * c * (bombieriTwoBlockGlobalCrossSymbol g h).re +
        b * d * (bombieriTwoBlockGlobalCrossSymbol g i).re := by
  rw [bombieriTwoBlockGlobalCrossSymbol_add_left,
    bombieriTwoBlockGlobalCrossSymbol_add_right,
    bombieriTwoBlockGlobalCrossSymbol_add_right]
  simp only [Complex.add_re]
  rw [bombieriTwoBlockGlobalCrossSymbol_real_smul_both_re_allLength,
    bombieriTwoBlockGlobalCrossSymbol_real_smul_both_re_allLength,
    bombieriTwoBlockGlobalCrossSymbol_real_smul_both_re_allLength,
    bombieriTwoBlockGlobalCrossSymbol_real_smul_both_re_allLength]
  ring

/-- Exact coordinate of the real cross between the two arbitrary-length
middle-orthogonal residual tests. -/
theorem finiteBlock_middleOrthogonalResidualCross_coordinate
    (parent : BombieriTest) (k : ℤ) (n : ℕ) :
    let a := monotoneQuarterCell parent k
    let m := monotoneQuarterFiniteBlockInterior parent k n
    let e := monotoneQuarterCell parent (k + ((n - 1 : ℕ) : ℤ))
    let M := bombieriRealQuadraticValue m
    let U := (bombieriTwoBlockGlobalCrossSymbol a m).re
    let V := (bombieriTwoBlockGlobalCrossSymbol m e).re
    let X := (bombieriTwoBlockGlobalCrossSymbol a e).re
    (bombieriTwoBlockGlobalCrossSymbol
      (finiteBlockLeftMiddleOrthogonalResidual parent k n)
      (finiteBlockRightMiddleOrthogonalResidual parent k n)).re =
        M * (M * X - U * V) := by
  dsimp only
  let a : BombieriTest := monotoneQuarterCell parent k
  let m : BombieriTest := monotoneQuarterFiniteBlockInterior parent k n
  let e : BombieriTest :=
    monotoneQuarterCell parent (k + ((n - 1 : ℕ) : ℤ))
  let M : ℝ := bombieriRealQuadraticValue m
  let U : ℝ := (bombieriTwoBlockGlobalCrossSymbol a m).re
  let V : ℝ := (bombieriTwoBlockGlobalCrossSymbol m e).re
  let X : ℝ := (bombieriTwoBlockGlobalCrossSymbol a e).re
  have hmm : (bombieriTwoBlockGlobalCrossSymbol m m).re = M := by
    rw [bombieriTwoBlockGlobalCrossSymbol_self]
    rfl
  change
    (bombieriTwoBlockGlobalCrossSymbol
      ((M : ℂ) • a + ((-U : ℝ) : ℂ) • m)
      ((M : ℂ) • e + ((-V : ℝ) : ℂ) • m)).re =
        M * (M * X - U * V)
  rw [bombieriTwoBlockGlobalCrossSymbol_real_linearCombination_re_allLength,
    hmm]
  dsimp only [U, V, X]
  ring

/-- For a positive interior pivot, nonnegativity of the concrete residual
cross is exactly the conditional numerator sign used by the induction. -/
theorem realFiniteBlockMiddlePivotConditionalCrossNonnegative_of_residualCross
    (n : ℕ)
    (hresidual :
      RealFiniteBlockMiddleOrthogonalResidualCrossNonnegativeAtLength n) :
    RealFiniteBlockMiddlePivotConditionalCrossNonnegativeAtLength n := by
  intro parent hparent k
  dsimp only
  let a : BombieriTest := monotoneQuarterCell parent k
  let m : BombieriTest := monotoneQuarterFiniteBlockInterior parent k n
  let e : BombieriTest :=
    monotoneQuarterCell parent (k + ((n - 1 : ℕ) : ℤ))
  let M : ℝ := bombieriRealQuadraticValue m
  let U : ℝ := (bombieriTwoBlockGlobalCrossSymbol a m).re
  let V : ℝ := (bombieriTwoBlockGlobalCrossSymbol m e).re
  let X : ℝ := (bombieriTwoBlockGlobalCrossSymbol a e).re
  intro hMpos
  have hcross := hresidual parent hparent k hMpos
  have hcoordinate := finiteBlock_middleOrthogonalResidualCross_coordinate
    parent k n
  change
    (bombieriTwoBlockGlobalCrossSymbol
      (finiteBlockLeftMiddleOrthogonalResidual parent k n)
      (finiteBlockRightMiddleOrthogonalResidual parent k n)).re =
        M * (M * X - U * V) at hcoordinate
  rw [hcoordinate] at hcross
  exact (mul_nonneg_iff_of_pos_left hMpos).mp hcross

/-- Conversely the conditional numerator sign gives the concrete residual
cross sign, so the two positive-pivot formulations are equivalent. -/
theorem realFiniteBlockMiddleOrthogonalResidualCrossNonnegative_of_conditionalCross
    (n : ℕ)
    (hconditional :
      RealFiniteBlockMiddlePivotConditionalCrossNonnegativeAtLength n) :
    RealFiniteBlockMiddleOrthogonalResidualCrossNonnegativeAtLength n := by
  intro parent hparent k hMpos
  have hdelta := hconditional parent hparent k hMpos
  have hcoordinate := finiteBlock_middleOrthogonalResidualCross_coordinate
    parent k n
  rw [hcoordinate]
  exact mul_nonneg hMpos.le hdelta

theorem realFiniteBlockMiddleOrthogonalResidualCrossNonnegative_iff_conditionalCross
    (n : ℕ) :
    RealFiniteBlockMiddleOrthogonalResidualCrossNonnegativeAtLength n ↔
      RealFiniteBlockMiddlePivotConditionalCrossNonnegativeAtLength n := by
  exact ⟨
    realFiniteBlockMiddlePivotConditionalCrossNonnegative_of_residualCross n,
    realFiniteBlockMiddleOrthogonalResidualCrossNonnegative_of_conditionalCross n⟩

/-- The exact singular-pivot obligation at one arbitrary length.  When the
interior diagonal vanishes, the induction needs only the sparse pair of the
two endpoint cells. -/
def RealFiniteBlockZeroInteriorSparseEndpointNonnegativeAtLength
    (n : ℕ) : Prop :=
  ∀ parent : BombieriTest,
    bombieriConjugateTest parent = parent →
      ∀ k : ℤ,
        let a := monotoneQuarterCell parent k
        let m := monotoneQuarterFiniteBlockInterior parent k n
        let e := monotoneQuarterCell parent
          (k + ((n - 1 : ℕ) : ℤ))
        bombieriRealQuadraticValue m = 0 →
          0 ≤ bombieriRealQuadraticValue (a + e)

/-- Test-level form of the singular four-cell endpoint obligation.  The
support theorem above shows that these two surviving endpoint cells occupy
intervals related by the exact dilation factor two. -/
def RealFourCellZeroInteriorFactorTwoEndpointNonnegative : Prop :=
  ∀ parent : BombieriTest,
    bombieriConjugateTest parent = parent →
      ∀ k : ℤ,
        monotoneQuarterFiniteBlockInterior parent k 4 = 0 →
          0 ≤ bombieriRealQuadraticValue
            (monotoneQuarterCell parent k +
              monotoneQuarterCell parent (k + 3))

/-- The abstract zero-diagonal clause at the first inductive length is
exactly the concrete collapsed factor-two endpoint problem.  Short-block
coercivity removes any distinction between a zero quadratic value and a
zero interior test. -/
theorem realFiniteBlockZeroInteriorSparseEndpointNonnegativeAtLength_four_iff_factorTwo
    : RealFiniteBlockZeroInteriorSparseEndpointNonnegativeAtLength 4 ↔
      RealFourCellZeroInteriorFactorTwoEndpointNonnegative := by
  constructor
  · intro hsparse parent hparent k hmiddle
    have hzero : bombieriRealQuadraticValue
        (monotoneQuarterFiniteBlockInterior parent k 4) = 0 := by
      rw [hmiddle, bombieriRealQuadraticValue_zero_for_aggregateExpressivity]
    have hpair := hsparse parent hparent k hzero
    simpa only [Nat.reduceSubDiff, Nat.cast_ofNat] using hpair
  · intro hfactor parent hparent k
    dsimp only
    intro hzero
    have hmiddle : monotoneQuarterFiniteBlockInterior parent k 4 = 0 :=
      monotoneQuarterFiniteBlockInterior_eq_zero_of_quadratic_eq_zero_of_le_five
        parent hparent k 4 (by omega) (by omega) hzero
    simpa only [Nat.reduceSubDiff, Nat.cast_ofNat] using
      hfactor parent hparent k hmiddle

/-- Chebyshev-row form of the singular-pivot obligation. -/
def RealFiniteBlockZeroInteriorFarChebyshevBoundAtLength
    (n : ℕ) : Prop :=
  ∀ parent : BombieriTest,
    bombieriConjugateTest parent = parent →
      ∀ k : ℤ,
        let a := monotoneQuarterCell parent k
        let m := monotoneQuarterFiniteBlockInterior parent k n
        let e := monotoneQuarterCell parent
          (k + ((n - 1 : ℕ) : ℤ))
        bombieriRealQuadraticValue m = 0 →
          -(bombieriRealQuadraticValue a +
              bombieriRealQuadraticValue e) / 2 ≤
            monotoneQuarterFarChebyshevContribution parent k
              ((n - 1 : ℕ) : ℤ)

/-- Once the interior diagonal vanishes, sparse endpoint positivity is
exactly one lower bound on the lag-`n-1` corrected-Chebyshev entry. -/
theorem realFiniteBlockZeroInteriorSparseEndpointNonnegative_iff_farChebyshevBound
    (n : ℕ) (hn : 4 ≤ n) :
    RealFiniteBlockZeroInteriorSparseEndpointNonnegativeAtLength n ↔
      RealFiniteBlockZeroInteriorFarChebyshevBoundAtLength n := by
  constructor
  · intro hsparse parent hparent k
    dsimp only
    intro hMzero
    have hpair := hsparse parent hparent k hMzero
    rw [bombieriRealQuadraticValue_add] at hpair
    have hfar := monotoneQuarterCell_far_globalCross_re_eq_contribution
      parent k ((n - 1 : ℕ) : ℤ) (by omega)
    rw [hfar] at hpair
    linarith
  · intro hfarBound parent hparent k
    dsimp only
    intro hMzero
    have hbound := hfarBound parent hparent k hMzero
    rw [bombieriRealQuadraticValue_add]
    have hfar := monotoneQuarterCell_far_globalCross_re_eq_contribution
      parent k ((n - 1 : ℕ) : ℤ) (by omega)
    rw [hfar]
    linarith

private theorem monotoneQuarterFiniteBlockInterior_five_eq_middleThree
    (parent : BombieriTest) (k : ℤ) :
    monotoneQuarterFiniteBlockInterior parent k 5 =
      fiveCellMiddleThree parent k := by
  classical
  simp [monotoneQuarterFiniteBlockInterior,
    monotoneQuarterFiniteBlock, fiveCellMiddleThree,
    Finset.sum_range_succ]

/-- The singular branch is already discharged at length five.  The
ratio-two coercivity of the middle three-cell block turns a zero diagonal
into the zero test, after which the exact common-parent support-collapse
theorem proves sparse endpoint positivity. -/
theorem realFiniteBlockZeroInteriorSparseEndpointNonnegativeAtLength_five :
    RealFiniteBlockZeroInteriorSparseEndpointNonnegativeAtLength 5 := by
  intro parent hparent k
  dsimp only
  have hinterior :=
    monotoneQuarterFiniteBlockInterior_five_eq_middleThree parent k
  rw [hinterior]
  intro hMzero
  have hmiddle : fiveCellMiddleThree parent k = 0 := by
    by_contra hmiddleNe
    have hpositive := fiveCellMiddleThree_quadratic_pos_of_ne_zero
      parent hparent k hmiddleNe
    rw [hMzero] at hpositive
    linarith
  simpa only [Nat.reduceSubDiff, Nat.cast_ofNat] using
    bombieriRealQuadraticValue_fiveCellSparseEndpointPair_nonnegative_of_middle_zero
      parent k hparent hmiddle

private theorem threeBlockQuadratic_nonnegative_of_conditionalCross
    {A M E U V X : ℝ}
    (hMpos : 0 < M)
    (hAM : U ^ 2 ≤ A * M)
    (hME : V ^ 2 ≤ M * E)
    (hdelta : 0 ≤ M * X - U * V) :
    0 ≤ A + M + E + 2 * (U + V + X) := by
  have halpha : 0 ≤ A * M - U ^ 2 := by linarith
  have hbeta : 0 ≤ M * E - V ^ 2 := by linarith
  have hidentity :
      M * (A + M + E + 2 * (U + V + X)) =
        (M + U + V) ^ 2 + (A * M - U ^ 2) +
          (M * E - V ^ 2) + 2 * (M * X - U * V) := by
    ring
  have hscaled :
      0 ≤ M * (A + M + E + 2 * (U + V + X)) := by
    rw [hidentity]
    positivity
  exact (mul_nonneg_iff_of_pos_left hMpos).mp hscaled

/-- The arbitrary-length induction step.  Positivity at every shorter
length supplies the two adjacent principal minors by actual modified-parent
pencils.  A nonnegative conditional residual cross closes the positive
interior branch; the sparse endpoint hypothesis closes the zero-interior
branch. -/
theorem realFiniteBlockProductionNonnegativeAtLength_of_previousLengths_and_middlePivot
    (n : ℕ) (hn : 4 ≤ n)
    (hprev : RealFiniteBlockProductionNonnegativeUpTo (n - 1))
    (hcross :
      RealFiniteBlockMiddlePivotConditionalCrossNonnegativeAtLength n)
    (hzero :
      RealFiniteBlockZeroInteriorSparseEndpointNonnegativeAtLength n) :
    RealFiniteBlockProductionNonnegativeAtLength n := by
  intro parent hparent k
  let a : BombieriTest := monotoneQuarterCell parent k
  let m : BombieriTest := monotoneQuarterFiniteBlockInterior parent k n
  let e : BombieriTest :=
    monotoneQuarterCell parent (k + ((n - 1 : ℕ) : ℤ))
  let A : ℝ := bombieriRealQuadraticValue a
  let M : ℝ := bombieriRealQuadraticValue m
  let E : ℝ := bombieriRealQuadraticValue e
  let U : ℝ := (bombieriTwoBlockGlobalCrossSymbol a m).re
  let V : ℝ := (bombieriTwoBlockGlobalCrossSymbol m e).re
  let X : ℝ := (bombieriTwoBlockGlobalCrossSymbol a e).re
  have hadj := finiteBlock_adjacentPrincipalMinors_of_previousLengths
    n hn hprev parent hparent k
  change U ^ 2 ≤ A * M ∧ V ^ 2 ≤ M * E at hadj
  have hmShift :
      monotoneQuarterFiniteBlock parent (k + 1) 0 (n - 2) = m := by
    dsimp only [m, monotoneQuarterFiniteBlockInterior]
    exact monotoneQuarterFiniteBlock_shift_start_one parent k (n - 2)
  have hM : 0 ≤ M := by
    have hmiddle := hprev (n - 2) (by omega) parent hparent (k + 1)
    rw [hmShift] at hmiddle
    exact hmiddle
  have hvalue := bombieriRealQuadraticValue_finiteBlock_eq_threeBlock_allLength
    parent k n (by omega)
  change bombieriRealQuadraticValue
      (monotoneQuarterFiniteBlock parent k 0 n) =
    A + M + E + 2 * (U + V + X) at hvalue
  rw [hvalue]
  by_cases hMzero : M = 0
  · have hU : U = 0 := by
      have h := hadj.1
      rw [hMzero, mul_zero] at h
      nlinarith [sq_nonneg U]
    have hV : V = 0 := by
      have h := hadj.2
      rw [hMzero, zero_mul] at h
      nlinarith [sq_nonneg V]
    have hpair := hzero parent hparent k
    change M = 0 →
      0 ≤ bombieriRealQuadraticValue (a + e) at hpair
    have hpair0 := hpair hMzero
    rw [bombieriRealQuadraticValue_add] at hpair0
    change 0 ≤ A + E + 2 * X at hpair0
    rw [hMzero, hU, hV]
    linarith
  · have hMpos : 0 < M := lt_of_le_of_ne hM (Ne.symm hMzero)
    have hdelta := hcross parent hparent k
    change 0 < M → 0 ≤ M * X - U * V at hdelta
    exact threeBlockQuadratic_nonnegative_of_conditionalCross
      hMpos hadj.1 hadj.2 (hdelta hMpos)

private theorem monotoneQuarterFiniteBlock_eq_shiftedZero_allLength
    (parent : BombieriTest) (lo : ℤ) (start n : ℕ) :
    monotoneQuarterFiniteBlock parent lo start n =
      monotoneQuarterFiniteBlock parent
        (monotoneQuarterFiniteBlockBase lo start) 0 n := by
  classical
  unfold monotoneQuarterFiniteBlock monotoneQuarterFiniteBlockBase
  apply Finset.sum_congr rfl
  intro i _hi
  congr 1
  push_cast
  ring

/-- Arbitrary-length obstruction form for a support-minimal negative block.
Assuming all shorter production lengths, there are exactly two branches:

* the interior diagonal vanishes and the sparse endpoint pair is negative;
* the interior diagonal is positive and the two concrete middle-orthogonal
  residual tests have strictly negative real global cross.

Thus nonnegativity of the actual residual cross rules out the entire
nondegenerate branch at every length, not only at five cells. -/
theorem supportMinimalNegativeMonotoneBlock_length_n_forces_zeroInteriorEndpoint_or_residualCross_neg
    (n : ℕ) (hn : 4 ≤ n)
    (hprev : RealFiniteBlockProductionNonnegativeUpTo (n - 1))
    {parent : BombieriTest} {lo : ℤ} {N start len : ℕ}
    (hparent : bombieriConjugateTest parent = parent)
    (hmin : IsSupportMinimalNegativeMonotoneBlock
      parent lo N start len) (hlen : len = n) :
    let k := monotoneQuarterFiniteBlockBase lo start
    let a := monotoneQuarterCell parent k
    let m := monotoneQuarterFiniteBlockInterior parent k n
    let e := monotoneQuarterCell parent (k + ((n - 1 : ℕ) : ℤ))
    let M := bombieriRealQuadraticValue m
    (M = 0 ∧ bombieriRealQuadraticValue (a + e) < 0) ∨
      (bombieriTwoBlockGlobalCrossSymbol
        (finiteBlockLeftMiddleOrthogonalResidual parent k n)
        (finiteBlockRightMiddleOrthogonalResidual parent k n)).re < 0 := by
  dsimp only
  let k : ℤ := monotoneQuarterFiniteBlockBase lo start
  let a : BombieriTest := monotoneQuarterCell parent k
  let m : BombieriTest := monotoneQuarterFiniteBlockInterior parent k n
  let e : BombieriTest :=
    monotoneQuarterCell parent (k + ((n - 1 : ℕ) : ℤ))
  let A : ℝ := bombieriRealQuadraticValue a
  let M : ℝ := bombieriRealQuadraticValue m
  let E : ℝ := bombieriRealQuadraticValue e
  let U : ℝ := (bombieriTwoBlockGlobalCrossSymbol a m).re
  let V : ℝ := (bombieriTwoBlockGlobalCrossSymbol m e).re
  let X : ℝ := (bombieriTwoBlockGlobalCrossSymbol a e).re
  have hnegative : bombieriRealQuadraticValue
      (monotoneQuarterFiniteBlock parent k 0 n) < 0 := by
    rw [← monotoneQuarterFiniteBlock_eq_shiftedZero_allLength
      parent lo start n]
    simpa only [hlen] using hmin.negative
  have hadj := finiteBlock_adjacentPrincipalMinors_of_previousLengths
    n hn hprev parent hparent k
  change U ^ 2 ≤ A * M ∧ V ^ 2 ≤ M * E at hadj
  have hmShift :
      monotoneQuarterFiniteBlock parent (k + 1) 0 (n - 2) = m := by
    dsimp only [m, monotoneQuarterFiniteBlockInterior]
    exact monotoneQuarterFiniteBlock_shift_start_one parent k (n - 2)
  have hM : 0 ≤ M := by
    have hmiddle := hprev (n - 2) (by omega) parent hparent (k + 1)
    rw [hmShift] at hmiddle
    exact hmiddle
  have hvalue := bombieriRealQuadraticValue_finiteBlock_eq_threeBlock_allLength
    parent k n (by omega)
  change bombieriRealQuadraticValue
      (monotoneQuarterFiniteBlock parent k 0 n) =
    A + M + E + 2 * (U + V + X) at hvalue
  have hwhole : A + M + E + 2 * (U + V + X) < 0 := by
    rw [← hvalue]
    exact hnegative
  by_cases hMzero : M = 0
  · left
    refine ⟨hMzero, ?_⟩
    have hU : U = 0 := by
      have h := hadj.1
      rw [hMzero, mul_zero] at h
      nlinarith [sq_nonneg U]
    have hV : V = 0 := by
      have h := hadj.2
      rw [hMzero, zero_mul] at h
      nlinarith [sq_nonneg V]
    rw [bombieriRealQuadraticValue_add]
    change A + E + 2 * X < 0
    rw [hMzero, hU, hV] at hwhole
    linarith
  · right
    have hMpos : 0 < M := lt_of_le_of_ne hM (Ne.symm hMzero)
    have halpha : 0 ≤ A * M - U ^ 2 := by linarith [hadj.1]
    have hbeta : 0 ≤ M * E - V ^ 2 := by linarith [hadj.2]
    have hidentity :
        M * (A + M + E + 2 * (U + V + X)) =
          (M + U + V) ^ 2 + (A * M - U ^ 2) +
            (M * E - V ^ 2) + 2 * (M * X - U * V) := by
      ring
    have hscaled :
        M * (A + M + E + 2 * (U + V + X)) < 0 :=
      mul_neg_of_pos_of_neg hMpos hwhole
    rw [hidentity] at hscaled
    have hdelta : M * X - U * V < 0 := by
      nlinarith [sq_nonneg (M + U + V)]
    have hcoordinate := finiteBlock_middleOrthogonalResidualCross_coordinate
      parent k n
    change
      (bombieriTwoBlockGlobalCrossSymbol
        (finiteBlockLeftMiddleOrthogonalResidual parent k n)
        (finiteBlockRightMiddleOrthogonalResidual parent k n)).re =
          M * (M * X - U * V) at hcoordinate
    rw [hcoordinate]
    exact mul_neg_of_pos_of_neg hMpos hdelta

/-- The unconditional ratio-two theorem initializes the induction through
length three. -/
theorem realFiniteBlockProductionNonnegativeUpTo_three :
    RealFiniteBlockProductionNonnegativeUpTo 3 := by
  intro n hn parent _hparent k
  exact
    bombieriRealQuadraticValue_monotoneQuarterFiniteBlock_nonnegative_of_le_three
      parent k 0 n hn

/-- One successor step for the cumulative production predicate. -/
theorem realFiniteBlockProductionNonnegativeUpTo_succ_of_middlePivot
    (n : ℕ) (hn : 3 ≤ n)
    (hprev : RealFiniteBlockProductionNonnegativeUpTo n)
    (hcross :
      RealFiniteBlockMiddlePivotConditionalCrossNonnegativeAtLength (n + 1))
    (hzero :
      RealFiniteBlockZeroInteriorSparseEndpointNonnegativeAtLength (n + 1)) :
    RealFiniteBlockProductionNonnegativeUpTo (n + 1) := by
  intro m hm
  by_cases hmn : m ≤ n
  · exact hprev m hmn
  · have hmeq : m = n + 1 := by omega
    subst m
    apply
      realFiniteBlockProductionNonnegativeAtLength_of_previousLengths_and_middlePivot
        (n + 1) (by omega)
    · simpa only [Nat.add_sub_cancel] using hprev
    · exact hcross
    · exact hzero

/-- The exact all-length local analytic interface.  At each length at least
four it retains only two genuinely new common-parent obligations:

* for a positive interior pivot, `0 ≤ M X - U V`;
* for a zero interior pivot, nonnegativity of the sparse endpoint pair.

Everything else in the induction is supplied by shorter production blocks. -/
def RealFiniteBlockAllLengthMiddlePivotClosure : Prop :=
  ∀ n : ℕ, 4 ≤ n →
    RealFiniteBlockMiddlePivotConditionalCrossNonnegativeAtLength n ∧
      RealFiniteBlockZeroInteriorSparseEndpointNonnegativeAtLength n

/-- Equivalent all-length interface written directly as nonnegativity of the
two concrete middle-orthogonal residual tests, plus the unavoidable singular
pivot clause. -/
def RealFiniteBlockAllLengthResidualCrossClosure : Prop :=
  ∀ n : ℕ, 4 ≤ n →
    RealFiniteBlockMiddleOrthogonalResidualCrossNonnegativeAtLength n ∧
      RealFiniteBlockZeroInteriorSparseEndpointNonnegativeAtLength n

/-- Weakest staged form of the middle-pivot interface exposed by the
induction: the two new length-`n` obligations may use the already established
production positivity through length `n-1`. -/
def RealFiniteBlockInductiveMiddlePivotClosure : Prop :=
  ∀ n : ℕ, 4 ≤ n →
    RealFiniteBlockProductionNonnegativeUpTo (n - 1) →
      RealFiniteBlockMiddlePivotConditionalCrossNonnegativeAtLength n ∧
        RealFiniteBlockZeroInteriorSparseEndpointNonnegativeAtLength n

/-- Residual-test version of the staged all-length interface. -/
def RealFiniteBlockInductiveResidualCrossClosure : Prop :=
  ∀ n : ℕ, 4 ≤ n →
    RealFiniteBlockProductionNonnegativeUpTo (n - 1) →
      RealFiniteBlockMiddleOrthogonalResidualCrossNonnegativeAtLength n ∧
        RealFiniteBlockZeroInteriorSparseEndpointNonnegativeAtLength n

theorem realFiniteBlockInductiveMiddlePivotClosure_of_residualCross
    (hclosure : RealFiniteBlockInductiveResidualCrossClosure) :
    RealFiniteBlockInductiveMiddlePivotClosure := by
  intro n hn hprev
  have h := hclosure n hn hprev
  exact ⟨
    realFiniteBlockMiddlePivotConditionalCrossNonnegative_of_residualCross
      n h.1,
    h.2⟩

theorem realFiniteBlockAllLengthMiddlePivotClosure_of_residualCross
    (hclosure : RealFiniteBlockAllLengthResidualCrossClosure) :
    RealFiniteBlockAllLengthMiddlePivotClosure := by
  intro n hn
  have h := hclosure n hn
  exact ⟨
    realFiniteBlockMiddlePivotConditionalCrossNonnegative_of_residualCross
      n h.1,
    h.2⟩

/-- The all-length middle-pivot interface propagates production positivity
through every finite block length. -/
theorem realFiniteBlockProductionNonnegativeUpTo_all
    (hclosure : RealFiniteBlockAllLengthMiddlePivotClosure) :
    ∀ n : ℕ, RealFiniteBlockProductionNonnegativeUpTo n := by
  intro n
  induction n with
  | zero =>
      intro m hm
      exact realFiniteBlockProductionNonnegativeUpTo_three m (by omega)
  | succ n ih =>
      by_cases hsmall : n + 1 ≤ 3
      · intro m hm
        exact realFiniteBlockProductionNonnegativeUpTo_three m
          (hm.trans hsmall)
      · have hn4 : 4 ≤ n + 1 := by omega
        have hnew := hclosure (n + 1) hn4
        exact
          realFiniteBlockProductionNonnegativeUpTo_succ_of_middlePivot
            n (by omega) ih hnew.1 hnew.2

/-- Finite induction from the staged interface.  At the `n`-th step the
closure hypothesis receives exactly the shorter-length production theorem
that has just been established. -/
theorem realFiniteBlockProductionNonnegativeUpTo_all_of_inductiveMiddlePivot
    (hclosure : RealFiniteBlockInductiveMiddlePivotClosure) :
    ∀ n : ℕ, RealFiniteBlockProductionNonnegativeUpTo n := by
  intro n
  induction n with
  | zero =>
      intro m hm
      exact realFiniteBlockProductionNonnegativeUpTo_three m (by omega)
  | succ n ih =>
      by_cases hsmall : n + 1 ≤ 3
      · intro m hm
        exact realFiniteBlockProductionNonnegativeUpTo_three m
          (hm.trans hsmall)
      · have hn4 : 4 ≤ n + 1 := by omega
        have hprev :
            RealFiniteBlockProductionNonnegativeUpTo ((n + 1) - 1) := by
          simpa only [Nat.add_sub_cancel] using ih
        have hnew := hclosure (n + 1) hn4 hprev
        exact
          realFiniteBlockProductionNonnegativeUpTo_succ_of_middlePivot
            n (by omega) ih hnew.1 hnew.2

theorem realFiniteBlockAllLengthMiddlePivotClosure_of_inductive
    (hclosure : RealFiniteBlockInductiveMiddlePivotClosure) :
    RealFiniteBlockAllLengthMiddlePivotClosure := by
  intro n hn
  exact hclosure n hn
    (realFiniteBlockProductionNonnegativeUpTo_all_of_inductiveMiddlePivot
      hclosure (n - 1))

/-- In particular every exact finite production length is nonnegative. -/
theorem realFiniteBlockProductionNonnegativeAtLength_all
    (hclosure : RealFiniteBlockAllLengthMiddlePivotClosure) :
    ∀ n : ℕ, RealFiniteBlockProductionNonnegativeAtLength n := by
  intro n
  exact realFiniteBlockProductionNonnegativeUpTo_all hclosure n n le_rfl

/-- The all-length common-parent middle-pivot interface implies the complete
real Bombieri quadratic criterion.  Compact support supplies a finite
monotone decomposition, and the exact-length theorem applies to its full
block. -/
theorem bombieriRealQuadraticNonnegativity_of_allLengthMiddlePivotClosure
    (hclosure : RealFiniteBlockAllLengthMiddlePivotClosure) :
    BombieriRealQuadraticNonnegativity := by
  intro parent hparent
  obtain ⟨lo, n, _hleft, _hright, hsum, _hratio, _hsuffix⟩ :=
    exists_monotoneQuarterCell_decomposition parent
  have hproduction :=
    realFiniteBlockProductionNonnegativeAtLength_all hclosure n
      parent hparent lo
  have hblock : monotoneQuarterFiniteBlock parent lo 0 n = parent := by
    simpa only [monotoneQuarterFiniteBlock, zero_add] using hsum
  rw [hblock] at hproduction
  exact hproduction

/-- Conditional local-to-global closure: the two all-length common-parent
middle-pivot obligations imply the Riemann Hypothesis through the already
verified Bombieri criterion. -/
theorem riemannHypothesis_of_allLengthMiddlePivotClosure
    (zeros : ZetaZeroEnumeration)
    (hclosure : RealFiniteBlockAllLengthMiddlePivotClosure) :
    RiemannHypothesis := by
  exact
    (riemannHypothesis_iff_bombieriRealQuadraticNonnegativity zeros).2
      (bombieriRealQuadraticNonnegativity_of_allLengthMiddlePivotClosure
        hclosure)

/-- Residual-cross form of the compiled all-length local-to-global theorem. -/
theorem riemannHypothesis_of_allLengthResidualCrossClosure
    (zeros : ZetaZeroEnumeration)
    (hclosure : RealFiniteBlockAllLengthResidualCrossClosure) :
    RiemannHypothesis := by
  exact riemannHypothesis_of_allLengthMiddlePivotClosure zeros
    (realFiniteBlockAllLengthMiddlePivotClosure_of_residualCross hclosure)

/-- Sharp staged local-to-global theorem: it is enough to prove the concrete
residual-cross and singular-pivot clauses one length at a time, using all
shorter production positivity at the next step. -/
theorem riemannHypothesis_of_inductiveResidualCrossClosure
    (zeros : ZetaZeroEnumeration)
    (hclosure : RealFiniteBlockInductiveResidualCrossClosure) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_allLengthMiddlePivotClosure zeros
  exact realFiniteBlockAllLengthMiddlePivotClosure_of_inductive
    (realFiniteBlockInductiveMiddlePivotClosure_of_residualCross hclosure)

end

end ArithmeticHodge.Analysis.MultiplicativeWeilMonotonePrimeAtomAggregateObstructionStructural

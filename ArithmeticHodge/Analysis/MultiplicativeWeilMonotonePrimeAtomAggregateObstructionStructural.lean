import ArithmeticHodge.Analysis.MultiplicativeWeilMonotonePrimeAtomAggregateStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneCutoffEnergyMonotonicityObstructionStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilFourCellEnergyAbsorptionStructural

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped Pointwise

namespace ArithmeticHodge.Analysis.MultiplicativeWeilMonotonePrimeAtomAggregateObstructionStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilFourCellEnergyAbsorptionStructural
open MultiplicativeWeilMonotoneCellEnergyFrameStructural
open MultiplicativeWeilMonotoneCutoffEnergyMonotonicityObstructionStructural
open MultiplicativeWeilMonotonePrimeAtomAbsorptionStructural
open MultiplicativeWeilMonotonePrimeAtomAggregateStructural
open MultiplicativeWeilMonotoneQuarterPartitionStructural
open MultiplicativeWeilMonotoneRatioTwoBlockPropagationStructural
open MultiplicativeWeilQuarterLogLatticePartitionStructural
open MultiplicativeWeilRealCutPhaseReductionStructural
open MultiplicativeWeilRealLogKernelStructural
open MultiplicativeWeilRealMonotonePropagationCriterionStructural
open MultiplicativeWeilRealMonotonePropagationLogDefectStructural

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

end

end ArithmeticHodge.Analysis.MultiplicativeWeilMonotonePrimeAtomAggregateObstructionStructural

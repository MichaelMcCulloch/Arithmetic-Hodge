import ArithmeticHodge.Analysis.MultiplicativeWeilMonotonePrimeAtomAggregateStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneCutoffEnergyMonotonicityObstructionStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilFourCellEnergyAbsorptionStructural

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace

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

end

end ArithmeticHodge.Analysis.MultiplicativeWeilMonotonePrimeAtomAggregateObstructionStructural

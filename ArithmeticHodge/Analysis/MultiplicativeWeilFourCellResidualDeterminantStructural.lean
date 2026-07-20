import ArithmeticHodge.Analysis.MultiplicativeWeilMonotonePrimeAtomAggregateObstructionStructural

set_option autoImplicit false

open Complex Real Set

namespace ArithmeticHodge.Analysis.MultiplicativeWeilFourCellResidualDeterminantStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilMinimalNegativeBlockStructural
open MultiplicativeWeilMonotoneNullSuffixVariationStructural
open MultiplicativeWeilMonotoneQuarterPartitionStructural
open MultiplicativeWeilRealCutPhaseReductionStructural
open MultiplicativeWeilRealMonotonePropagationCriterionStructural
open MultiplicativeWeilRealMonotoneTailConeCriterionStructural
open MultiplicativeWeilMonotonePrimeAtomAggregateObstructionStructural

/-!
# The first residual determinant is the full four-cell problem

At four cells the two endpoint cells and the two-cell interior can be scaled
independently by replacing a real common parent with a real linear combination
of that parent and its cutoffs at the two inner boundaries.  Consequently the
positive-pivot residual determinant is not a new local consequence of the
three-cell theorem: together with the zero-pivot endpoint clause, it is exactly
four-cell production positivity.
-/

private theorem monotoneQuarterFiniteBlock_add
    (f g : BombieriTest) (k : ℤ) (start len : ℕ) :
    monotoneQuarterFiniteBlock (f + g) k start len =
      monotoneQuarterFiniteBlock f k start len +
        monotoneQuarterFiniteBlock g k start len := by
  classical
  unfold monotoneQuarterFiniteBlock
  simp_rw [monotoneQuarterCell_add]
  exact Finset.sum_add_distrib

private theorem monotoneQuarterFiniteBlock_smul
    (c : ℂ) (f : BombieriTest) (k : ℤ) (start len : ℕ) :
    monotoneQuarterFiniteBlock (c • f) k start len =
      c • monotoneQuarterFiniteBlock f k start len := by
  classical
  unfold monotoneQuarterFiniteBlock
  simp_rw [monotoneQuarterCell_smul]
  exact Finset.smul_sum.symm

private theorem conjugate_fixed_real_smul
    {f : BombieriTest} (hf : bombieriConjugateTest f = f) (c : ℝ) :
    bombieriConjugateTest ((c : ℂ) • f) = (c : ℂ) • f := by
  rw [bombieriConjugateTest_smul, Complex.conj_ofReal, hf]

private theorem monotoneQuarterFiniteBlock_eq_cutoff_sub
    (parent : BombieriTest) (k : ℤ) (start len : ℕ) :
    monotoneQuarterFiniteBlock parent k start len =
      monotoneQuarterCutoff parent (k + (start : ℤ)) -
        monotoneQuarterCutoff parent (k + ((start + len : ℕ) : ℤ)) := by
  classical
  unfold monotoneQuarterFiniteBlock
  convert sum_range_monotoneQuarterCell_eq_cutoff_sub
    parent (k + (start : ℤ)) len using 1 <;> push_cast <;> ring_nf

private theorem monotoneQuarterCutoff_cutoff_eq_later_left
    (parent : BombieriTest) {k j : ℤ} (hkj : k < j) :
    monotoneQuarterCutoff (monotoneQuarterCutoff parent j) k =
      monotoneQuarterCutoff parent j := by
  apply TestFunction.ext
  intro x
  simp only [monotoneQuarterCutoff_apply]
  calc
    (monotoneQuarterStep k x : ℂ) *
        ((monotoneQuarterStep j x : ℂ) * parent x) =
      ((monotoneQuarterStep k x * monotoneQuarterStep j x : ℝ) : ℂ) *
        parent x := by push_cast; ring
    _ = (monotoneQuarterStep j x : ℂ) * parent x := by
      rw [monotoneQuarterStep_mul_later hkj]

private theorem fourBlock_cutoff_one_eq_suffix
    (parent : BombieriTest) (k : ℤ) :
    monotoneQuarterFiniteBlock
        (monotoneQuarterCutoff parent (k + 1)) k 0 4 =
      monotoneQuarterFiniteBlock parent k 1 3 := by
  rw [monotoneQuarterFiniteBlock_eq_cutoff_sub,
    monotoneQuarterFiniteBlock_eq_cutoff_sub]
  norm_num
  rw [monotoneQuarterCutoff_cutoff_eq_later_left parent (by omega),
    monotoneQuarterCutoff_cutoff_eq_later parent (by omega)]

private theorem fourBlock_cutoff_three_eq_rightEndpoint
    (parent : BombieriTest) (k : ℤ) :
    monotoneQuarterFiniteBlock
        (monotoneQuarterCutoff parent (k + 3)) k 0 4 =
      monotoneQuarterFiniteBlock parent k 3 1 := by
  rw [monotoneQuarterFiniteBlock_eq_cutoff_sub,
    monotoneQuarterFiniteBlock_eq_cutoff_sub]
  norm_num
  rw [monotoneQuarterCutoff_cutoff_eq_later_left parent (by omega),
    monotoneQuarterCutoff_cutoff_eq_later parent (by omega)]

private theorem fourBlock_eq_endpoint_interior_endpoint
    (parent : BombieriTest) (k : ℤ) :
    monotoneQuarterFiniteBlock parent k 0 4 =
      monotoneQuarterCell parent k +
        monotoneQuarterFiniteBlockInterior parent k 4 +
          monotoneQuarterCell parent (k + 3) := by
  classical
  simp [monotoneQuarterFiniteBlock,
    monotoneQuarterFiniteBlockInterior, Finset.sum_range_succ]
  abel

private theorem fourBlock_suffix_one_eq_interior_add_endpoint
    (parent : BombieriTest) (k : ℤ) :
    monotoneQuarterFiniteBlock parent k 1 3 =
      monotoneQuarterFiniteBlockInterior parent k 4 +
        monotoneQuarterCell parent (k + 3) := by
  classical
  simp [monotoneQuarterFiniteBlock,
    monotoneQuarterFiniteBlockInterior, Finset.sum_range_succ]

private theorem fourBlock_suffix_three_eq_endpoint
    (parent : BombieriTest) (k : ℤ) :
    monotoneQuarterFiniteBlock parent k 3 1 =
      monotoneQuarterCell parent (k + 3) := by
  classical
  simp [monotoneQuarterFiniteBlock]

/-- The common parent remasked so that its left endpoint, two-cell interior,
and right endpoint acquire the independent real coefficients `x`, `y`, and
`z`. -/
def fourCellThreeRegionRescaledParent
    (parent : BombieriTest) (k : ℤ) (x y z : ℝ) : BombieriTest :=
  (x : ℂ) • parent +
    ((y - x : ℝ) : ℂ) • monotoneQuarterCutoff parent (k + 1) +
      ((z - y : ℝ) : ℂ) • monotoneQuarterCutoff parent (k + 3)

theorem fourCellThreeRegionRescaledParent_conjugate_fixed
    (parent : BombieriTest)
    (hparent : bombieriConjugateTest parent = parent)
    (k : ℤ) (x y z : ℝ) :
    bombieriConjugateTest
        (fourCellThreeRegionRescaledParent parent k x y z) =
      fourCellThreeRegionRescaledParent parent k x y z := by
  unfold fourCellThreeRegionRescaledParent
  rw [bombieriConjugateTest_add, bombieriConjugateTest_add,
    conjugate_fixed_real_smul hparent x,
    conjugate_fixed_real_smul
      (bombieriConjugateTest_monotoneQuarterCutoff parent hparent (k + 1))
      (y - x),
    conjugate_fixed_real_smul
      (bombieriConjugateTest_monotoneQuarterCutoff parent hparent (k + 3))
      (z - y)]

/-- Exact independent three-region realization inside the same four-cell
window. -/
theorem fourBlock_threeRegionRescaledParent_eq
    (parent : BombieriTest) (k : ℤ) (x y z : ℝ) :
    monotoneQuarterFiniteBlock
        (fourCellThreeRegionRescaledParent parent k x y z) k 0 4 =
      (x : ℂ) • monotoneQuarterCell parent k +
        (y : ℂ) • monotoneQuarterFiniteBlockInterior parent k 4 +
          (z : ℂ) • monotoneQuarterCell parent (k + 3) := by
  unfold fourCellThreeRegionRescaledParent
  rw [monotoneQuarterFiniteBlock_add,
    monotoneQuarterFiniteBlock_add,
    monotoneQuarterFiniteBlock_smul,
    monotoneQuarterFiniteBlock_smul,
    monotoneQuarterFiniteBlock_smul,
    fourBlock_cutoff_one_eq_suffix,
    fourBlock_cutoff_three_eq_rightEndpoint,
    fourBlock_eq_endpoint_interior_endpoint,
    fourBlock_suffix_one_eq_interior_add_endpoint,
    fourBlock_suffix_three_eq_endpoint]
  module

private theorem bombieriRealQuadraticValue_add_real_smul
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

private theorem real_two_by_two_determinant_of_all_nonnegative
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

/-- Four-cell production positivity already forces the positive-pivot
residual determinant.  The proof uses only independent real remasking of the
three regions of the same common parent. -/
theorem fourCell_residualDeterminant_of_production
    (hproduction : RealFiniteBlockProductionNonnegativeAtLength 4) :
    RealFiniteBlockMiddleOrthogonalResidualDeterminantAtLength 4 := by
  intro parent hparent k _hMpos
  let a : BombieriTest := monotoneQuarterCell parent k
  let m : BombieriTest := monotoneQuarterFiniteBlockInterior parent k 4
  let e : BombieriTest := monotoneQuarterCell parent (k + 3)
  let M : ℝ := bombieriRealQuadraticValue m
  let U : ℝ := (bombieriTwoBlockGlobalCrossSymbol a m).re
  let V : ℝ := (bombieriTwoBlockGlobalCrossSymbol m e).re
  let l : BombieriTest := finiteBlockLeftMiddleOrthogonalResidual parent k 4
  let r : BombieriTest := finiteBlockRightMiddleOrthogonalResidual parent k 4
  have hl : l = (M : ℂ) • a + ((-U : ℝ) : ℂ) • m := by rfl
  have hr : r = (M : ℂ) • e + ((-V : ℝ) : ℂ) • m := by rfl
  have hrealize : ∀ x y z : ℝ,
      ∃ modified : BombieriTest,
        bombieriConjugateTest modified = modified ∧
          monotoneQuarterFiniteBlock modified k 0 4 =
            (x : ℂ) • a + (y : ℂ) • m + (z : ℂ) • e := by
    intro x y z
    exact ⟨fourCellThreeRegionRescaledParent parent k x y z,
      fourCellThreeRegionRescaledParent_conjugate_fixed
        parent hparent k x y z,
      fourBlock_threeRegionRescaledParent_eq parent k x y z⟩
  have hrNonnegative : 0 ≤ bombieriRealQuadraticValue r := by
    obtain ⟨modified, hmodified, hblock⟩ := hrealize 0 (-V) M
    have h := hproduction modified hmodified k
    have hblock' : monotoneQuarterFiniteBlock modified k 0 4 = r := by
      rw [hblock, hr]
      module
    rw [hblock'] at h
    exact h
  apply real_two_by_two_determinant_of_all_nonnegative hrNonnegative
  intro t
  rw [← bombieriRealQuadraticValue_add_real_smul]
  obtain ⟨modified, hmodified, hblock⟩ :=
    hrealize M (-U - t * V) (t * M)
  have h := hproduction modified hmodified k
  have hblock' :
      monotoneQuarterFiniteBlock modified k 0 4 = l + (t : ℂ) • r := by
    rw [hblock, hl, hr]
    push_cast
    module
  rw [hblock'] at h
  exact h

/-- Four-cell production positivity also forces the singular sparse-endpoint
clause by setting the independently rescaled interior coefficient to zero. -/
theorem fourCell_zeroInteriorSparseEndpointNonnegative_of_production
    (hproduction : RealFiniteBlockProductionNonnegativeAtLength 4) :
    RealFiniteBlockZeroInteriorSparseEndpointNonnegativeAtLength 4 := by
  intro parent hparent k
  dsimp only
  intro _hzero
  let modified := fourCellThreeRegionRescaledParent parent k 1 0 1
  have hmodified : bombieriConjugateTest modified = modified :=
    fourCellThreeRegionRescaledParent_conjugate_fixed
      parent hparent k 1 0 1
  have h := hproduction modified hmodified k
  have hblock := fourBlock_threeRegionRescaledParent_eq parent k 1 0 1
  change monotoneQuarterFiniteBlock modified k 0 4 = _ at hblock
  rw [hblock] at h
  simpa using h

/-- At the first inductive length, the residual determinant plus the singular
endpoint clause are exactly four-cell production positivity. -/
theorem fourCell_productionNonnegative_iff_residualDeterminant_and_zeroInterior :
    RealFiniteBlockProductionNonnegativeAtLength 4 ↔
      RealFiniteBlockMiddleOrthogonalResidualDeterminantAtLength 4 ∧
        RealFiniteBlockZeroInteriorSparseEndpointNonnegativeAtLength 4 := by
  constructor
  · intro hproduction
    exact ⟨fourCell_residualDeterminant_of_production hproduction,
      fourCell_zeroInteriorSparseEndpointNonnegative_of_production hproduction⟩
  · rintro ⟨hresidual, hzero⟩
    exact
      realFiniteBlockProductionNonnegativeAtLength_of_previousLengths_and_residualDeterminant
        4 (by omega) realFiniteBlockProductionNonnegativeUpTo_three
        hresidual hzero

/-- Using short-block coercivity, the same exact characterization exposes the
singular clause as the collapsed factor-two endpoint problem. -/
theorem fourCell_productionNonnegative_iff_residualDeterminant_and_factorTwoEndpoint :
    RealFiniteBlockProductionNonnegativeAtLength 4 ↔
      RealFiniteBlockMiddleOrthogonalResidualDeterminantAtLength 4 ∧
        RealFourCellZeroInteriorFactorTwoEndpointNonnegative := by
  rw [fourCell_productionNonnegative_iff_residualDeterminant_and_zeroInterior,
    realFiniteBlockZeroInteriorSparseEndpointNonnegativeAtLength_four_iff_factorTwo]

end

end ArithmeticHodge.Analysis.MultiplicativeWeilFourCellResidualDeterminantStructural

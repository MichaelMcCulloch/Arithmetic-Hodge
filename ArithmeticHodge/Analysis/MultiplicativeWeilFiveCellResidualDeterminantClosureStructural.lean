import ArithmeticHodge.Analysis.MultiplicativeWeilAllLengthResidualDeterminantSingularClosureStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellCommonParentDeterminantStructural

set_option autoImplicit false

open Complex Real Set

namespace ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellResidualDeterminantClosureStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilAllLengthEndpointReserveStructural
open MultiplicativeWeilAllLengthResidualDeterminantSingularClosureStructural
open MultiplicativeWeilFiveCellCommonParentDeterminantStructural
open MultiplicativeWeilFiveCellMinimalBlockReserveStructural
open MultiplicativeWeilMinimalNegativeBlockStructural
open MultiplicativeWeilMonotonePrimeAtomAggregateObstructionStructural
open MultiplicativeWeilMonotoneQuarterPartitionStructural
open MultiplicativeWeilRealMonotonePropagationCriterionStructural

/-!
# The first genuine residual determinant is exactly five-cell production

Every real pencil on the two middle-orthogonal residuals is an honest
five-cell block of a remasked common parent.  Consequently universal
five-cell production positivity forces the residual Cauchy--Schwarz
inequality.  Conversely, after the already-established shorter-length
positivity, the all-length pivot theorem turns that determinant back into
five-cell production positivity.

Thus the first residual determinant is not a consequence obtainable merely
by repackaging the four-cell theorem: under the four-cell induction
hypothesis it is exactly the entire new five-cell production statement.
-/

private theorem finiteBlockInterior_five_eq_middleThree
    (parent : BombieriTest) (k : ℤ) :
    monotoneQuarterFiniteBlockInterior parent k 5 =
      fiveCellMiddleThree parent k := by
  classical
  simp [monotoneQuarterFiniteBlockInterior,
    monotoneQuarterFiniteBlock, fiveCellMiddleThree,
    Finset.sum_range_succ]

private theorem finiteBlockLeftResidual_five_eq
    (parent : BombieriTest) (k : ℤ) :
    finiteBlockLeftMiddleOrthogonalResidual parent k 5 =
      fiveCellLeftMiddleOrthogonalResidual parent k := by
  unfold finiteBlockLeftMiddleOrthogonalResidual
    fiveCellLeftMiddleOrthogonalResidual
  rw [finiteBlockInterior_five_eq_middleThree]

private theorem finiteBlockRightResidual_five_eq
    (parent : BombieriTest) (k : ℤ) :
    finiteBlockRightMiddleOrthogonalResidual parent k 5 =
      fiveCellRightMiddleOrthogonalResidual parent k := by
  unfold finiteBlockRightMiddleOrthogonalResidual
    fiveCellRightMiddleOrthogonalResidual
  norm_num
  rw [finiteBlockInterior_five_eq_middleThree]

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

/-- Universal five-cell production positivity forces the genuine length-five
middle-orthogonal residual determinant.  The proof uses the exact
common-parent remasking theorem, not an assumed global Cauchy--Schwarz
principle. -/
theorem fiveCell_residualDeterminant_of_production
    (hproduction : RealFiniteBlockProductionNonnegativeAtLength 5) :
    RealFiniteBlockMiddleOrthogonalResidualDeterminantAtLength 5 := by
  intro parent hparent k _hMpos
  let l : BombieriTest :=
    finiteBlockLeftMiddleOrthogonalResidual parent k 5
  let r : BombieriTest :=
    finiteBlockRightMiddleOrthogonalResidual parent k 5
  have hl : l = fiveCellLeftMiddleOrthogonalResidual parent k := by
    exact finiteBlockLeftResidual_five_eq parent k
  have hr : r = fiveCellRightMiddleOrthogonalResidual parent k := by
    exact finiteBlockRightResidual_five_eq parent k
  have hrNonnegative : 0 ≤ bombieriRealQuadraticValue r := by
    let m : BombieriTest := fiveCellMiddleThree parent k
    let e : BombieriTest := monotoneQuarterCell parent (k + 4)
    let M : ℝ := bombieriRealQuadraticValue m
    let V : ℝ := (bombieriTwoBlockGlobalCrossSymbol m e).re
    obtain ⟨modified, hmodified, hblock⟩ :=
      exists_realParent_fiveBlock_eq_threeBlockCombination
        parent hparent k 0 (-V) M
    have h := hproduction modified hmodified k
    change 0 ≤ bombieriRealQuadraticValue
      (monotoneQuarterFiveBlock modified k) at h
    have hblock' : monotoneQuarterFiveBlock modified k = r := by
      rw [hblock, hr]
      unfold fiveCellRightMiddleOrthogonalResidual
      dsimp only [m, e, M, V]
      module
    rw [hblock'] at h
    exact h
  apply real_two_by_two_determinant_of_all_nonnegative hrNonnegative
  intro t
  rw [← bombieriRealQuadraticValue_add_real_smul]
  obtain ⟨modified, hmodified, hblock⟩ :=
    exists_realParent_fiveBlock_eq_middleOrthogonalResidualPencil
      parent hparent k t
  have h := hproduction modified hmodified k
  change 0 ≤ bombieriRealQuadraticValue
    (monotoneQuarterFiveBlock modified k) at h
  rw [hblock, ← hl, ← hr] at h
  exact h

/-- The concrete common-parent form of the first residual determinant.  Its
remote entry is the exact local-minus-prime endpoint balance from the
five-cell API. -/
def RealFiveCellCommonParentMiddlePivotResidualContraction : Prop :=
  ∀ parent : BombieriTest,
    bombieriConjugateTest parent = parent →
      ∀ k : ℤ,
        FiveCellCommonParentMiddlePivotResidualContraction parent k

/-- At length five the all-length residual-test statement is losslessly the
concrete common-parent scalar contraction.  The zero-middle branch is
automatic; the nonzero branch has a positive pivot by three-cell coercivity. -/
theorem residualDeterminantAtLength_five_iff_commonParentContraction :
    RealFiniteBlockMiddleOrthogonalResidualDeterminantAtLength 5 ↔
      RealFiveCellCommonParentMiddlePivotResidualContraction := by
  constructor
  · intro hdeterminant parent hparent k
    by_cases hmiddle : fiveCellMiddleThree parent k = 0
    · exact middlePivotResidualContraction_of_middle_zero parent k hmiddle
    · have hMpos : 0 < bombieriRealQuadraticValue
          (fiveCellMiddleThree parent k) :=
        fiveCellMiddleThree_quadratic_pos_of_ne_zero
          parent hparent k hmiddle
      have hactual := hdeterminant parent hparent k
      have hMpos' : 0 < bombieriRealQuadraticValue
          (monotoneQuarterFiniteBlockInterior parent k 5) := by
        rw [finiteBlockInterior_five_eq_middleThree]
        exact hMpos
      have hcross := hactual hMpos'
      rw [finiteBlockLeftResidual_five_eq,
        finiteBlockRightResidual_five_eq] at hcross
      exact
        (fiveCellCommonParentMiddlePivotResidualContraction_iff_residualCross
          parent k hMpos).2 hcross
  · intro hcontraction parent hparent k hMpos
    have hMpos' : 0 < bombieriRealQuadraticValue
        (fiveCellMiddleThree parent k) := by
      rw [← finiteBlockInterior_five_eq_middleThree]
      exact hMpos
    have hcross :=
      (fiveCellCommonParentMiddlePivotResidualContraction_iff_residualCross
        parent k hMpos').1 (hcontraction parent hparent k)
    rwa [finiteBlockLeftResidual_five_eq,
      finiteBlockRightResidual_five_eq]

/-- Under production positivity through length four, the first residual
determinant is equivalent to universal production positivity at length five.
This is the sharp structural boundary: proving the determinant closes the
new length, while proving the new length necessarily proves the determinant. -/
theorem fiveCell_productionNonnegative_iff_residualDeterminant
    (hprev : RealFiniteBlockProductionNonnegativeUpTo 4) :
    RealFiniteBlockProductionNonnegativeAtLength 5 ↔
      RealFiniteBlockMiddleOrthogonalResidualDeterminantAtLength 5 := by
  constructor
  · exact fiveCell_residualDeterminant_of_production
  · intro hdeterminant
    exact
      realFiniteBlockProductionNonnegativeAtLength_of_previousLengths_and_residualDeterminant_only
        5 (by omega) (by simpa using hprev) hdeterminant

/-- Final sharp five-cell target: once lengths at most four are available,
universal five-cell production is equivalent to the single exact
local-minus-prime common-parent middle-pivot contraction. -/
theorem fiveCell_productionNonnegative_iff_commonParentContraction
    (hprev : RealFiniteBlockProductionNonnegativeUpTo 4) :
    RealFiniteBlockProductionNonnegativeAtLength 5 ↔
      RealFiveCellCommonParentMiddlePivotResidualContraction := by
  exact (fiveCell_productionNonnegative_iff_residualDeterminant hprev).trans
    residualDeterminantAtLength_five_iff_commonParentContraction

end

end ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellResidualDeterminantClosureStructural

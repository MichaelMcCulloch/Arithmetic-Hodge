import ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellLocalCrossSignObstructionStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilDirectedCorrelationSmoothStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilFarPhysicalKernelStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilGlobalCrossSesquilinearStructural

set_option autoImplicit false

open Complex Filter MeasureTheory Real Set TopologicalSpace
open scoped ContDiff Topology

namespace ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellCommonParentDeterminantStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilAllLengthEndpointReserveStructural
open ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellLocalCrossSignObstructionStructural
open ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural
open MultiplicativeWeilBelowThreePrimeReductionStructural
open MultiplicativeWeilFourCellEnergyAbsorptionStructural
open MultiplicativeWeilDirectedCorrelationPhysicalStructural
open MultiplicativeWeilDirectedCorrelationSmoothStructural
open MultiplicativeWeilFarCauchyMomentStructural
open MultiplicativeWeilFarPhysicalKernelStructural
open MultiplicativeWeilFarSupportSeparationStructural
open MultiplicativeWeilMinimalBlockEndpointEliminationStructural
open MultiplicativeWeilMinimalNegativeBlockStructural
open MultiplicativeWeilMonotoneFourCellPrimeGeometryStructural
open MultiplicativeWeilMonotoneCellEnergyFrameStructural
open MultiplicativeWeilMonotoneQuarterPartitionStructural
open MultiplicativeWeilMonotoneNullSuffixVariationStructural
open MultiplicativeWeilQuarterLogLatticePartitionStructural
open MultiplicativeWeilRealMonotonePropagationCriterionStructural
open MultiplicativeWeilRealMonotoneTailConeCriterionStructural
open YoshidaBombieriCrossDistribution

/-!
# The sharp common-parent determinant at five cells

The three-by-three Bombieri matrix on the left endpoint, the middle three
cells, and the right endpoint is not automatically a positive Gram matrix.
Pivoting through the middle block shows exactly what is new at length five:

`(M * X - U * V)^2 <= (A * M - U^2) * (M * E - V^2)`.

Both factors on the right are already four-cell questions.  We prove this
without treating the three blocks as independent: every real scalar pencil
on either adjacent pair is itself an honest four-cell block cut from a
modified common parent.  Consequently universal production four-cell
positivity supplies both adjacent principal minors.

For a nonzero middle block, a support-minimal negative five-cell block then
strictly reverses the displayed residual contraction.  If the middle block
vanishes, the remaining obstruction is instead the sparse pair of remote
endpoint cells; a full determinant cannot see that degenerate case.
-/

/-- Universal nonnegativity of the actual real four-cell production family. -/
def RealFourCellProductionNonnegative : Prop :=
  ∀ parent : BombieriTest,
    bombieriConjugateTest parent = parent →
      ∀ k : ℤ,
        0 ≤ bombieriRealQuadraticValue (monotoneQuarterFourBlock parent k)

private theorem monotoneQuarterFourBlock_add
    (f g : BombieriTest) (k : ℤ) :
    monotoneQuarterFourBlock (f + g) k =
      monotoneQuarterFourBlock f k + monotoneQuarterFourBlock g k := by
  classical
  unfold monotoneQuarterFourBlock monotoneQuarterFiniteBlock
  simp_rw [monotoneQuarterCell_add]
  exact Finset.sum_add_distrib

private theorem monotoneQuarterFourBlock_smul
    (c : ℂ) (f : BombieriTest) (k : ℤ) :
    monotoneQuarterFourBlock (c • f) k =
      c • monotoneQuarterFourBlock f k := by
  classical
  unfold monotoneQuarterFourBlock monotoneQuarterFiniteBlock
  simp_rw [monotoneQuarterCell_smul]
  exact Finset.smul_sum.symm

private theorem conjugate_fixed_sub
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

private theorem conjugate_fixed_monotoneQuarterCutoff
    {parent : BombieriTest}
    (hparent : bombieriConjugateTest parent = parent) (j : ℤ) :
    bombieriConjugateTest (monotoneQuarterCutoff parent j) =
      monotoneQuarterCutoff parent j := by
  apply TestFunction.ext
  intro x
  have hx := congrArg (fun q : BombieriTest ↦ q x) hparent
  simp only [bombieriConjugateTest_apply, monotoneQuarterCutoff_apply] at hx ⊢
  rw [map_mul, Complex.conj_ofReal, hx]

private theorem conjugate_fixed_real_smul
    {f : BombieriTest} (hf : bombieriConjugateTest f = f) (c : ℝ) :
    bombieriConjugateTest ((c : ℂ) • f) = (c : ℂ) • f := by
  rw [bombieriConjugateTest_smul, Complex.conj_ofReal, hf]

private theorem fiveCellMiddleThree_eq_finiteBlock
    (parent : BombieriTest) (k : ℤ) :
    _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellMiddleThree parent k =
      monotoneQuarterFiniteBlock parent k 1 3 := by
  classical
  simp [_root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellMiddleThree, monotoneQuarterFiniteBlock,
    Finset.sum_range_succ]

private theorem fiveCell_leftFourBlock_eq_endpoint_add_middle
    (parent : BombieriTest) (k : ℤ) :
    monotoneQuarterFourBlock parent k =
      monotoneQuarterCell parent k +
        _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellMiddleThree parent k := by
  classical
  simp [monotoneQuarterFourBlock, monotoneQuarterFiniteBlock,
    _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellMiddleThree, Finset.sum_range_succ]
  module

private theorem fiveCell_rightFourBlock_eq_middle_add_endpoint
    (parent : BombieriTest) (k : ℤ) :
    monotoneQuarterFourBlock parent (k + 1) =
      _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellMiddleThree parent k + monotoneQuarterCell parent (k + 4) := by
  classical
  simp [monotoneQuarterFourBlock, monotoneQuarterFiniteBlock,
    _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellMiddleThree, Finset.sum_range_succ]
  rw [show k + 1 + 1 = k + 2 by ring,
    show k + 1 + 2 = k + 3 by ring,
    show k + 1 + 3 = k + 4 by ring]

/-- Removing the next cutoff from the parent makes its four-cell block equal
to the single left endpoint cell. -/
theorem fourBlock_parent_sub_nextCutoff_eq_leftEndpoint
    (parent : BombieriTest) (k : ℤ) :
    monotoneQuarterFourBlock
        (parent - monotoneQuarterCutoff parent (k + 1)) k =
      monotoneQuarterCell parent k := by
  apply TestFunction.ext
  intro x
  rw [monotoneQuarterFourBlock_apply, monotoneQuarterCell_apply]
  simp only [TestFunction.coe_sub, Pi.sub_apply,
    monotoneQuarterCutoff_apply]
  have hk1 := monotoneQuarterStep_mul_later
    (k := k) (j := k + 1) (by omega) x
  have h14 := monotoneQuarterStep_mul_later
    (k := k + 1) (j := k + 4) (by omega) x
  have hmask :
      (monotoneQuarterStep k x - monotoneQuarterStep (k + 4) x) *
          (1 - monotoneQuarterStep (k + 1) x) =
        monotoneQuarterWeight k x := by
    unfold monotoneQuarterWeight
    nlinarith [hk1, h14]
  change
    (↑(monotoneQuarterStep k x - monotoneQuarterStep (k + 4) x) : ℂ) *
        (parent x - ↑(monotoneQuarterStep (k + 1) x) * parent x) =
      (monotoneQuarterWeight k x : ℂ) * parent x
  calc
    (↑(monotoneQuarterStep k x - monotoneQuarterStep (k + 4) x) : ℂ) *
          (parent x - ↑(monotoneQuarterStep (k + 1) x) * parent x) =
        (↑((monotoneQuarterStep k x - monotoneQuarterStep (k + 4) x) *
          (1 - monotoneQuarterStep (k + 1) x)) : ℂ) * parent x := by
      push_cast
      ring
    _ = (monotoneQuarterWeight k x : ℂ) * parent x := by rw [hmask]

/-- Cutting the parent at the right endpoint makes the shifted four-cell
block equal to that single endpoint cell. -/
theorem fourBlock_rightCutoff_eq_rightEndpoint
    (parent : BombieriTest) (k : ℤ) :
    monotoneQuarterFourBlock
        (monotoneQuarterCutoff parent (k + 4)) (k + 1) =
      monotoneQuarterCell parent (k + 4) := by
  apply TestFunction.ext
  intro x
  rw [monotoneQuarterFourBlock_apply, monotoneQuarterCell_apply]
  simp only [monotoneQuarterCutoff_apply]
  have h14 := monotoneQuarterStep_mul_later
    (k := k + 1) (j := k + 4) (by omega) x
  have h45 := monotoneQuarterStep_mul_later
    (k := k + 4) (j := k + 5) (by omega) x
  have hindex : k + 1 + 4 = k + 5 := by ring
  have hmask :
      (monotoneQuarterStep (k + 1) x - monotoneQuarterStep (k + 5) x) *
          monotoneQuarterStep (k + 4) x =
        monotoneQuarterWeight (k + 4) x := by
    unfold monotoneQuarterWeight
    rw [show k + 4 + 1 = k + 5 by ring]
    nlinarith [h14, h45]
  rw [hindex]
  change
    (↑(monotoneQuarterStep (k + 1) x - monotoneQuarterStep (k + 5) x) : ℂ) *
        (↑(monotoneQuarterStep (k + 4) x) * parent x) =
      (monotoneQuarterWeight (k + 4) x : ℂ) * parent x
  calc
    (↑(monotoneQuarterStep (k + 1) x - monotoneQuarterStep (k + 5) x) : ℂ) *
          (↑(monotoneQuarterStep (k + 4) x) * parent x) =
        (↑((monotoneQuarterStep (k + 1) x - monotoneQuarterStep (k + 5) x) *
          monotoneQuarterStep (k + 4) x) : ℂ) * parent x := by
      push_cast
      ring
    _ = (monotoneQuarterWeight (k + 4) x : ℂ) * parent x := by rw [hmask]

/-- Every real scalar pencil on the left endpoint and middle block is an
actual four-cell production block for a modified common parent. -/
theorem exists_realParent_fourBlock_eq_leftEndpoint_add_smul_middle
    (parent : BombieriTest)
    (hparent : bombieriConjugateTest parent = parent)
    (k : ℤ) (t : ℝ) :
    ∃ modified : BombieriTest,
      bombieriConjugateTest modified = modified ∧
        monotoneQuarterFourBlock modified k =
          monotoneQuarterCell parent k +
            (t : ℂ) • _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellMiddleThree parent k := by
  let endpointParent : BombieriTest :=
    parent - monotoneQuarterCutoff parent (k + 1)
  let modified : BombieriTest :=
    (t : ℂ) • parent + ((1 - t : ℝ) : ℂ) • endpointParent
  have hcut := conjugate_fixed_monotoneQuarterCutoff hparent (k + 1)
  have hendpoint : bombieriConjugateTest endpointParent = endpointParent := by
    dsimp only [endpointParent]
    exact conjugate_fixed_sub hparent hcut
  refine ⟨modified, ?_, ?_⟩
  · dsimp only [modified]
    rw [bombieriConjugateTest_add,
      conjugate_fixed_real_smul hparent t,
      conjugate_fixed_real_smul hendpoint (1 - t)]
  · dsimp only [modified]
    rw [monotoneQuarterFourBlock_add,
      monotoneQuarterFourBlock_smul,
      monotoneQuarterFourBlock_smul,
      fiveCell_leftFourBlock_eq_endpoint_add_middle,
      show monotoneQuarterFourBlock endpointParent k =
          monotoneQuarterCell parent k by
        exact fourBlock_parent_sub_nextCutoff_eq_leftEndpoint parent k]
    module

/-- Every real scalar pencil on the middle and right endpoint block is an
actual shifted four-cell production block for a modified common parent. -/
theorem exists_realParent_fourBlock_eq_middle_add_smul_rightEndpoint
    (parent : BombieriTest)
    (hparent : bombieriConjugateTest parent = parent)
    (k : ℤ) (t : ℝ) :
    ∃ modified : BombieriTest,
      bombieriConjugateTest modified = modified ∧
        monotoneQuarterFourBlock modified (k + 1) =
          _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellMiddleThree parent k +
            (t : ℂ) • monotoneQuarterCell parent (k + 4) := by
  let endpointParent : BombieriTest :=
    monotoneQuarterCutoff parent (k + 4)
  let modified : BombieriTest :=
    parent + ((t - 1 : ℝ) : ℂ) • endpointParent
  have hendpoint : bombieriConjugateTest endpointParent = endpointParent := by
    dsimp only [endpointParent]
    exact conjugate_fixed_monotoneQuarterCutoff hparent (k + 4)
  refine ⟨modified, ?_, ?_⟩
  · dsimp only [modified]
    rw [bombieriConjugateTest_add, hparent,
      conjugate_fixed_real_smul hendpoint (t - 1)]
  · dsimp only [modified]
    rw [monotoneQuarterFourBlock_add,
      monotoneQuarterFourBlock_smul,
      fiveCell_rightFourBlock_eq_middle_add_endpoint,
      show monotoneQuarterFourBlock endpointParent (k + 1) =
          monotoneQuarterCell parent (k + 4) by
        exact fourBlock_rightCutoff_eq_rightEndpoint parent k]
    module

private theorem monotoneQuarterFiveBlock_add
    (f g : BombieriTest) (k : ℤ) :
    monotoneQuarterFiveBlock (f + g) k =
      monotoneQuarterFiveBlock f k + monotoneQuarterFiveBlock g k := by
  apply TestFunction.ext
  intro x
  simp only [monotoneQuarterFiveBlock_apply, TestFunction.coe_add,
    Pi.add_apply]
  ring

private theorem monotoneQuarterFiveBlock_smul
    (c : ℂ) (f : BombieriTest) (k : ℤ) :
    monotoneQuarterFiveBlock (c • f) k =
      c • monotoneQuarterFiveBlock f k := by
  apply TestFunction.ext
  intro x
  simp only [monotoneQuarterFiveBlock_apply, TestFunction.coe_smul,
    Pi.smul_apply, smul_eq_mul]
  ring

private theorem fiveCell_fiveBlock_eq_threeBlocks
    (parent : BombieriTest) (k : ℤ) :
    monotoneQuarterFiveBlock parent k =
      (monotoneQuarterCell parent k +
        _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellMiddleThree
          parent k) +
        monotoneQuarterCell parent (k + 4) := by
  classical
  simp [monotoneQuarterFiveBlock, monotoneQuarterFiniteBlock,
    _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellMiddleThree,
    Finset.sum_range_succ]
  module

private theorem fiveBlock_parent_sub_nextCutoff_eq_leftEndpoint
    (parent : BombieriTest) (k : ℤ) :
    monotoneQuarterFiveBlock
        (parent - monotoneQuarterCutoff parent (k + 1)) k =
      monotoneQuarterCell parent k := by
  apply TestFunction.ext
  intro x
  rw [monotoneQuarterFiveBlock_apply, monotoneQuarterCell_apply]
  simp only [TestFunction.coe_sub, Pi.sub_apply,
    monotoneQuarterCutoff_apply]
  have hk1 := monotoneQuarterStep_mul_later
    (k := k) (j := k + 1) (by omega) x
  have h15 := monotoneQuarterStep_mul_later
    (k := k + 1) (j := k + 5) (by omega) x
  have hmask :
      (monotoneQuarterStep k x - monotoneQuarterStep (k + 5) x) *
          (1 - monotoneQuarterStep (k + 1) x) =
        monotoneQuarterWeight k x := by
    unfold monotoneQuarterWeight
    nlinarith [hk1, h15]
  change
    (↑(monotoneQuarterStep k x - monotoneQuarterStep (k + 5) x) : ℂ) *
        (parent x - ↑(monotoneQuarterStep (k + 1) x) * parent x) =
      (monotoneQuarterWeight k x : ℂ) * parent x
  calc
    (↑(monotoneQuarterStep k x - monotoneQuarterStep (k + 5) x) : ℂ) *
          (parent x - ↑(monotoneQuarterStep (k + 1) x) * parent x) =
        (↑((monotoneQuarterStep k x - monotoneQuarterStep (k + 5) x) *
          (1 - monotoneQuarterStep (k + 1) x)) : ℂ) * parent x := by
      push_cast
      ring
    _ = (monotoneQuarterWeight k x : ℂ) * parent x := by rw [hmask]

private theorem fiveBlock_rightCutoff_eq_rightEndpoint
    (parent : BombieriTest) (k : ℤ) :
    monotoneQuarterFiveBlock
        (monotoneQuarterCutoff parent (k + 4)) k =
      monotoneQuarterCell parent (k + 4) := by
  apply TestFunction.ext
  intro x
  rw [monotoneQuarterFiveBlock_apply, monotoneQuarterCell_apply]
  simp only [monotoneQuarterCutoff_apply]
  have h04 := monotoneQuarterStep_mul_later
    (k := k) (j := k + 4) (by omega) x
  have h45 := monotoneQuarterStep_mul_later
    (k := k + 4) (j := k + 5) (by omega) x
  have hmask :
      (monotoneQuarterStep k x - monotoneQuarterStep (k + 5) x) *
          monotoneQuarterStep (k + 4) x =
        monotoneQuarterWeight (k + 4) x := by
    unfold monotoneQuarterWeight
    rw [show k + 4 + 1 = k + 5 by ring]
    nlinarith [h04, h45]
  change
    (↑(monotoneQuarterStep k x - monotoneQuarterStep (k + 5) x) : ℂ) *
        (↑(monotoneQuarterStep (k + 4) x) * parent x) =
      (monotoneQuarterWeight (k + 4) x : ℂ) * parent x
  calc
    (↑(monotoneQuarterStep k x - monotoneQuarterStep (k + 5) x) : ℂ) *
          (↑(monotoneQuarterStep (k + 4) x) * parent x) =
        (↑((monotoneQuarterStep k x - monotoneQuarterStep (k + 5) x) *
          monotoneQuarterStep (k + 4) x) : ℂ) * parent x := by
      push_cast
      ring
    _ = (monotoneQuarterWeight (k + 4) x : ℂ) * parent x := by
      rw [hmask]

/-- Every real scalar combination of the left endpoint, middle three cells,
and right endpoint is an honest five-cell production block of a modified
real common parent. -/
theorem exists_realParent_fiveBlock_eq_threeBlockCombination
    (parent : BombieriTest)
    (hparent : bombieriConjugateTest parent = parent)
    (k : ℤ) (alpha beta gamma : ℝ) :
    ∃ modified : BombieriTest,
      bombieriConjugateTest modified = modified ∧
        monotoneQuarterFiveBlock modified k =
          (alpha : ℂ) • monotoneQuarterCell parent k +
            (beta : ℂ) •
              _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellMiddleThree
                parent k +
            (gamma : ℂ) • monotoneQuarterCell parent (k + 4) := by
  let leftParent : BombieriTest :=
    parent - monotoneQuarterCutoff parent (k + 1)
  let rightParent : BombieriTest :=
    monotoneQuarterCutoff parent (k + 4)
  let modified : BombieriTest :=
    (beta : ℂ) • parent +
      ((alpha - beta : ℝ) : ℂ) • leftParent +
      ((gamma - beta : ℝ) : ℂ) • rightParent
  have hleft : bombieriConjugateTest leftParent = leftParent := by
    dsimp only [leftParent]
    exact conjugate_fixed_sub hparent
      (conjugate_fixed_monotoneQuarterCutoff hparent (k + 1))
  have hright : bombieriConjugateTest rightParent = rightParent := by
    dsimp only [rightParent]
    exact conjugate_fixed_monotoneQuarterCutoff hparent (k + 4)
  refine ⟨modified, ?_, ?_⟩
  · dsimp only [modified]
    rw [bombieriConjugateTest_add, bombieriConjugateTest_add,
      conjugate_fixed_real_smul hparent beta,
      conjugate_fixed_real_smul hleft (alpha - beta),
      conjugate_fixed_real_smul hright (gamma - beta)]
  · dsimp only [modified]
    rw [monotoneQuarterFiveBlock_add,
      monotoneQuarterFiveBlock_add,
      monotoneQuarterFiveBlock_smul,
      monotoneQuarterFiveBlock_smul,
      monotoneQuarterFiveBlock_smul,
      fiveCell_fiveBlock_eq_threeBlocks,
      show monotoneQuarterFiveBlock leftParent k =
          monotoneQuarterCell parent k by
        exact fiveBlock_parent_sub_nextCutoff_eq_leftEndpoint parent k,
      show monotoneQuarterFiveBlock rightParent k =
          monotoneQuarterCell parent (k + 4) by
        exact fiveBlock_rightCutoff_eq_rightEndpoint parent k]
    module

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

private theorem bombieriTwoBlockGlobalCrossSymbol_real_smul_both_re
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

private theorem bombieriTwoBlockGlobalCrossSymbol_real_linearCombination_re
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
  rw [bombieriTwoBlockGlobalCrossSymbol_real_smul_both_re,
    bombieriTwoBlockGlobalCrossSymbol_real_smul_both_re,
    bombieriTwoBlockGlobalCrossSymbol_real_smul_both_re,
    bombieriTwoBlockGlobalCrossSymbol_real_smul_both_re]
  ring

private theorem bombieriRealQuadraticValue_real_linearCombination
    (f g : BombieriTest) (a b : ℝ) :
    bombieriRealQuadraticValue ((a : ℂ) • f + (b : ℂ) • g) =
      a ^ 2 * bombieriRealQuadraticValue f +
        b ^ 2 * bombieriRealQuadraticValue g +
        2 * a * b * (bombieriTwoBlockGlobalCrossSymbol f g).re := by
  have hswap := congrArg Complex.re
    (_root_.ArithmeticHodge.Analysis.MultiplicativeWeil.bombieriTwoBlockGlobalCrossSymbol_conj_swap
      f g)
  simp only [Complex.star_def, Complex.conj_re] at hswap
  unfold bombieriRealQuadraticValue
  rw [← bombieriTwoBlockGlobalCrossSymbol_self]
  rw [bombieriTwoBlockGlobalCrossSymbol_real_linearCombination_re]
  rw [bombieriTwoBlockGlobalCrossSymbol_self,
    bombieriTwoBlockGlobalCrossSymbol_self]
  simp only [pow_two]
  rw [hswap]
  ring

/-- Universal production four-cell positivity supplies both adjacent
principal minors of the genuine five-cell common-parent matrix. -/
theorem fiveCell_adjacentPrincipalMinors_of_fourCellProduction
    (hfour : RealFourCellProductionNonnegative)
    (parent : BombieriTest)
    (hparent : bombieriConjugateTest parent = parent) (k : ℤ) :
    let a := monotoneQuarterCell parent k
    let m := _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellMiddleThree parent k
    let e := monotoneQuarterCell parent (k + 4)
    let A := bombieriRealQuadraticValue a
    let M := bombieriRealQuadraticValue m
    let E := bombieriRealQuadraticValue e
    let U := (bombieriTwoBlockGlobalCrossSymbol a m).re
    let V := (bombieriTwoBlockGlobalCrossSymbol m e).re
    U ^ 2 ≤ A * M ∧ V ^ 2 ≤ M * E := by
  dsimp only
  let a : BombieriTest := monotoneQuarterCell parent k
  let m : BombieriTest := _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellMiddleThree parent k
  let e : BombieriTest := monotoneQuarterCell parent (k + 4)
  have hM : 0 ≤ bombieriRealQuadraticValue m := by
    rw [show m = monotoneQuarterFiniteBlock parent k 1 3 by
      exact fiveCellMiddleThree_eq_finiteBlock parent k]
    exact bombieriRealQuadraticValue_monotoneQuarterFiniteBlock_nonnegative_of_le_three
      parent k 1 3 (by omega)
  have hE : 0 ≤ bombieriRealQuadraticValue e := by
    exact bombieriFunctional_quadratic_re_nonneg_of_ratioTwoCell e
      (monotoneQuarterCell_ratioTwo parent (k + 4))
  constructor
  · apply real_two_by_two_determinant_of_all_nonnegative hM
    intro t
    obtain ⟨modified, hmodified, hblock⟩ :=
      exists_realParent_fourBlock_eq_leftEndpoint_add_smul_middle
        parent hparent k t
    rw [← bombieriRealQuadraticValue_add_real_smul]
    rw [← hblock]
    exact hfour modified hmodified k
  · apply real_two_by_two_determinant_of_all_nonnegative hE
    intro t
    obtain ⟨modified, hmodified, hblock⟩ :=
      exists_realParent_fourBlock_eq_middle_add_smul_rightEndpoint
        parent hparent k t
    rw [← bombieriRealQuadraticValue_add_real_smul]
    rw [← hblock]
    exact hfour modified hmodified (k + 1)

/-- The middle-pivot residual determinant.  Its nonnegativity is equivalent
to the full determinant when the middle diagonal is positive. -/
def fiveCellMiddlePivotResidualDeterminant
    (A M E U V X : ℝ) : ℝ :=
  (A * M - U ^ 2) * (M * E - V ^ 2) - (M * X - U * V) ^ 2

theorem fiveCellMiddlePivotResidualDeterminant_eq_mul_threeBlockDeterminant
    (A M E U V X : ℝ) :
    fiveCellMiddlePivotResidualDeterminant A M E U V X =
      M * _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellThreeBlockDeterminant A M E U V X := by
  unfold fiveCellMiddlePivotResidualDeterminant
    _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellThreeBlockDeterminant
  ring

/-- The pivot identity also handles a zero middle diagonal: adjacent
principal minors force both adjacent crosses to vanish, so the full
determinant is then exactly zero. -/
theorem threeBlockDeterminant_nonnegative_of_middlePivotResidual
    {A M E U V X : ℝ}
    (hM : 0 ≤ M)
    (hAM : U ^ 2 ≤ A * M)
    (hME : V ^ 2 ≤ M * E)
    (hresidual :
      (M * X - U * V) ^ 2 ≤
        (A * M - U ^ 2) * (M * E - V ^ 2)) :
    0 ≤ _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellThreeBlockDeterminant
      A M E U V X := by
  by_cases hMzero : M = 0
  · have hU : U = 0 := by
      rw [hMzero, mul_zero] at hAM
      nlinarith [sq_nonneg U]
    have hV : V = 0 := by
      rw [hMzero, zero_mul] at hME
      nlinarith [sq_nonneg V]
    rw [hMzero, hU, hV]
    simp [_root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellThreeBlockDeterminant]
  · have hMpos : 0 < M := lt_of_le_of_ne hM (Ne.symm hMzero)
    have hscaled :
        0 ≤ fiveCellMiddlePivotResidualDeterminant A M E U V X := by
      unfold fiveCellMiddlePivotResidualDeterminant
      linarith
    rw [fiveCellMiddlePivotResidualDeterminant_eq_mul_threeBlockDeterminant]
      at hscaled
    exact (mul_nonneg_iff_of_pos_left hMpos).mp hscaled

/-- The left middle-orthogonal residual of the actual five-cell common-parent
triple. -/
def fiveCellLeftMiddleOrthogonalResidual
    (parent : BombieriTest) (k : ℤ) : BombieriTest :=
  let a := monotoneQuarterCell parent k
  let m :=
    _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellMiddleThree
      parent k
  let M := bombieriRealQuadraticValue m
  let U := (bombieriTwoBlockGlobalCrossSymbol a m).re
  (M : ℂ) • a + ((-U : ℝ) : ℂ) • m

/-- The right middle-orthogonal residual of the actual five-cell common-parent
triple. -/
def fiveCellRightMiddleOrthogonalResidual
    (parent : BombieriTest) (k : ℤ) : BombieriTest :=
  let m :=
    _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellMiddleThree
      parent k
  let e := monotoneQuarterCell parent (k + 4)
  let M := bombieriRealQuadraticValue m
  let V := (bombieriTwoBlockGlobalCrossSymbol m e).re
  (M : ℂ) • e + ((-V : ℝ) : ℂ) • m

/-- Exact coordinates of the two middle-orthogonal residual tests.  Their
diagonals are the adjacent Schur complements, while their real cross is the
new five-cell middle-pivot numerator. -/
theorem fiveCell_middleOrthogonalResidual_coordinates
    (parent : BombieriTest) (k : ℤ) :
    let a := monotoneQuarterCell parent k
    let m :=
      _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellMiddleThree
        parent k
    let e := monotoneQuarterCell parent (k + 4)
    let A := bombieriRealQuadraticValue a
    let M := bombieriRealQuadraticValue m
    let E := bombieriRealQuadraticValue e
    let U := (bombieriTwoBlockGlobalCrossSymbol a m).re
    let V := (bombieriTwoBlockGlobalCrossSymbol m e).re
    let X :=
      _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellRemoteEndpointBalance
        parent k
    bombieriRealQuadraticValue
        (fiveCellLeftMiddleOrthogonalResidual parent k) =
          M * (A * M - U ^ 2) ∧
      bombieriRealQuadraticValue
        (fiveCellRightMiddleOrthogonalResidual parent k) =
          M * (M * E - V ^ 2) ∧
      (bombieriTwoBlockGlobalCrossSymbol
        (fiveCellLeftMiddleOrthogonalResidual parent k)
        (fiveCellRightMiddleOrthogonalResidual parent k)).re =
          M * (M * X - U * V) := by
  dsimp only
  let a : BombieriTest := monotoneQuarterCell parent k
  let m : BombieriTest :=
    _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellMiddleThree
      parent k
  let e : BombieriTest := monotoneQuarterCell parent (k + 4)
  let A : ℝ := bombieriRealQuadraticValue a
  let M : ℝ := bombieriRealQuadraticValue m
  let E : ℝ := bombieriRealQuadraticValue e
  let U : ℝ := (bombieriTwoBlockGlobalCrossSymbol a m).re
  let V : ℝ := (bombieriTwoBlockGlobalCrossSymbol m e).re
  let X : ℝ :=
    _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellRemoteEndpointBalance
      parent k
  have hleft :=
    bombieriRealQuadraticValue_real_linearCombination a m M (-U)
  have hright :=
    bombieriRealQuadraticValue_real_linearCombination e m M (-V)
  have hcross :=
    bombieriTwoBlockGlobalCrossSymbol_real_linearCombination_re
      a m e m M (-U) M (-V)
  have hem : (bombieriTwoBlockGlobalCrossSymbol e m).re = V := by
    have hswap := congrArg Complex.re
      (_root_.ArithmeticHodge.Analysis.MultiplicativeWeil.bombieriTwoBlockGlobalCrossSymbol_conj_swap
        m e)
    simpa only [Complex.star_def, Complex.conj_re, V] using hswap
  have hmm : (bombieriTwoBlockGlobalCrossSymbol m m).re = M := by
    rw [bombieriTwoBlockGlobalCrossSymbol_self]
    rfl
  have hae : (bombieriTwoBlockGlobalCrossSymbol a e).re = X := by
    dsimp only [a, e, X]
    exact
      _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCell_remoteEndpointGlobalCross_re_eq_balance
        parent k
  change
    bombieriRealQuadraticValue ((M : ℂ) • a + ((-U : ℝ) : ℂ) • m) =
        M * (A * M - U ^ 2) ∧
      bombieriRealQuadraticValue ((M : ℂ) • e + ((-V : ℝ) : ℂ) • m) =
        M * (M * E - V ^ 2) ∧
      (bombieriTwoBlockGlobalCrossSymbol
        ((M : ℂ) • a + ((-U : ℝ) : ℂ) • m)
        ((M : ℂ) • e + ((-V : ℝ) : ℂ) • m)).re =
          M * (M * X - U * V)
  constructor
  · rw [hleft]
    dsimp only [A, M, U]
    ring
  constructor
  · rw [hright, hem]
    dsimp only [M, E, V]
    ring
  · rw [hcross, hae, hmm]
    dsimp only [M, U, V]
    ring

/-- Every real pencil on the two middle-orthogonal residuals is itself an
actual five-cell production block of a modified real common parent. -/
theorem exists_realParent_fiveBlock_eq_middleOrthogonalResidualPencil
    (parent : BombieriTest)
    (hparent : bombieriConjugateTest parent = parent)
    (k : ℤ) (t : ℝ) :
    ∃ modified : BombieriTest,
      bombieriConjugateTest modified = modified ∧
        monotoneQuarterFiveBlock modified k =
          fiveCellLeftMiddleOrthogonalResidual parent k +
            (t : ℂ) • fiveCellRightMiddleOrthogonalResidual parent k := by
  let a : BombieriTest := monotoneQuarterCell parent k
  let m : BombieriTest :=
    _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellMiddleThree
      parent k
  let e : BombieriTest := monotoneQuarterCell parent (k + 4)
  let M : ℝ := bombieriRealQuadraticValue m
  let U : ℝ := (bombieriTwoBlockGlobalCrossSymbol a m).re
  let V : ℝ := (bombieriTwoBlockGlobalCrossSymbol m e).re
  obtain ⟨modified, hmodified, hblock⟩ :=
    exists_realParent_fiveBlock_eq_threeBlockCombination
      parent hparent k M (-(U + t * V)) (t * M)
  refine ⟨modified, hmodified, ?_⟩
  rw [hblock]
  change
    (M : ℂ) • a + ((-(U + t * V) : ℝ) : ℂ) • m +
        ((t * M : ℝ) : ℂ) • e =
      ((M : ℂ) • a + ((-U : ℝ) : ℂ) • m) +
        (t : ℂ) • ((M : ℂ) • e + ((-V : ℝ) : ℂ) • m)
  module

/-- The one genuinely new common-parent inequality after four-cell closure.
The remote entry is written in its exact local-minus-prime form. -/
def FiveCellCommonParentMiddlePivotResidualContraction
    (parent : BombieriTest) (k : ℤ) : Prop :=
  let a := monotoneQuarterCell parent k
  let m := _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellMiddleThree
    parent k
  let e := monotoneQuarterCell parent (k + 4)
  let A := bombieriRealQuadraticValue a
  let M := bombieriRealQuadraticValue m
  let E := bombieriRealQuadraticValue e
  let U := (bombieriTwoBlockGlobalCrossSymbol a m).re
  let V := (bombieriTwoBlockGlobalCrossSymbol m e).re
  let X := _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellRemoteEndpointBalance
    parent k
  (M * X - U * V) ^ 2 ≤
    (A * M - U ^ 2) * (M * E - V ^ 2)

/-- For a positive middle pivot, the common-parent residual contraction is
exactly real Cauchy--Schwarz for the two concrete middle-orthogonal residual
tests. -/
theorem fiveCellCommonParentMiddlePivotResidualContraction_iff_residualCross
    (parent : BombieriTest) (k : ℤ)
    (hMpos : 0 < bombieriRealQuadraticValue
      (_root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellMiddleThree
        parent k)) :
    FiveCellCommonParentMiddlePivotResidualContraction parent k ↔
      (bombieriTwoBlockGlobalCrossSymbol
        (fiveCellLeftMiddleOrthogonalResidual parent k)
        (fiveCellRightMiddleOrthogonalResidual parent k)).re ^ 2 ≤
        bombieriRealQuadraticValue
            (fiveCellLeftMiddleOrthogonalResidual parent k) *
          bombieriRealQuadraticValue
            (fiveCellRightMiddleOrthogonalResidual parent k) := by
  let a : BombieriTest := monotoneQuarterCell parent k
  let m : BombieriTest :=
    _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellMiddleThree
      parent k
  let e : BombieriTest := monotoneQuarterCell parent (k + 4)
  let A : ℝ := bombieriRealQuadraticValue a
  let M : ℝ := bombieriRealQuadraticValue m
  let E : ℝ := bombieriRealQuadraticValue e
  let U : ℝ := (bombieriTwoBlockGlobalCrossSymbol a m).re
  let V : ℝ := (bombieriTwoBlockGlobalCrossSymbol m e).re
  let X : ℝ :=
    _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellRemoteEndpointBalance
      parent k
  let alpha : ℝ := A * M - U ^ 2
  let beta : ℝ := M * E - V ^ 2
  let delta : ℝ := M * X - U * V
  change 0 < M at hMpos
  have hcoordinates := fiveCell_middleOrthogonalResidual_coordinates parent k
  change
    bombieriRealQuadraticValue
        (fiveCellLeftMiddleOrthogonalResidual parent k) = M * alpha ∧
      bombieriRealQuadraticValue
          (fiveCellRightMiddleOrthogonalResidual parent k) = M * beta ∧
      (bombieriTwoBlockGlobalCrossSymbol
        (fiveCellLeftMiddleOrthogonalResidual parent k)
        (fiveCellRightMiddleOrthogonalResidual parent k)).re =
          M * delta at hcoordinates
  change delta ^ 2 ≤ alpha * beta ↔
    (bombieriTwoBlockGlobalCrossSymbol
      (fiveCellLeftMiddleOrthogonalResidual parent k)
      (fiveCellRightMiddleOrthogonalResidual parent k)).re ^ 2 ≤
      bombieriRealQuadraticValue
          (fiveCellLeftMiddleOrthogonalResidual parent k) *
        bombieriRealQuadraticValue
          (fiveCellRightMiddleOrthogonalResidual parent k)
  rw [hcoordinates.1, hcoordinates.2.1, hcoordinates.2.2]
  constructor
  · intro h
    calc
      (M * delta) ^ 2 = M ^ 2 * delta ^ 2 := by ring
      _ ≤ M ^ 2 * (alpha * beta) :=
        mul_le_mul_of_nonneg_left h (sq_nonneg M)
      _ = (M * alpha) * (M * beta) := by ring
  · intro h
    have hscaled : M ^ 2 * delta ^ 2 ≤ M ^ 2 * (alpha * beta) := by
      calc
        M ^ 2 * delta ^ 2 = (M * delta) ^ 2 := by ring
        _ ≤ (M * alpha) * (M * beta) := h
        _ = M ^ 2 * (alpha * beta) := by ring
    exact le_of_mul_le_mul_left hscaled (sq_pos_of_pos hMpos)

/-- Sharp production reduction for the actual common-parent determinant.
Universal four-cell positivity supplies the adjacent factors; the displayed
middle-pivot residual contraction is the only additional analytic input. -/
theorem fiveCellCommonParentThreeBlockDeterminant_nonnegative_of_middlePivot
    (hfour : RealFourCellProductionNonnegative)
    (parent : BombieriTest)
    (hparent : bombieriConjugateTest parent = parent) (k : ℤ)
    (hresidual : FiveCellCommonParentMiddlePivotResidualContraction parent k) :
    0 ≤ _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellCommonParentThreeBlockDeterminant
      parent k := by
  let a : BombieriTest := monotoneQuarterCell parent k
  let m : BombieriTest :=
    _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellMiddleThree
      parent k
  let e : BombieriTest := monotoneQuarterCell parent (k + 4)
  let A : ℝ := bombieriRealQuadraticValue a
  let M : ℝ := bombieriRealQuadraticValue m
  let E : ℝ := bombieriRealQuadraticValue e
  let U : ℝ := (bombieriTwoBlockGlobalCrossSymbol a m).re
  let V : ℝ := (bombieriTwoBlockGlobalCrossSymbol m e).re
  let X : ℝ :=
    _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellRemoteEndpointBalance
      parent k
  have hadj := fiveCell_adjacentPrincipalMinors_of_fourCellProduction
    hfour parent hparent k
  change U ^ 2 ≤ A * M ∧ V ^ 2 ≤ M * E at hadj
  have hM : 0 ≤ M := by
    dsimp only [M, m]
    rw [fiveCellMiddleThree_eq_finiteBlock]
    exact bombieriRealQuadraticValue_monotoneQuarterFiniteBlock_nonnegative_of_le_three
      parent k 1 3 (by omega)
  have hres :
      (M * X - U * V) ^ 2 ≤
        (A * M - U ^ 2) * (M * E - V ^ 2) := by
    simpa only [FiveCellCommonParentMiddlePivotResidualContraction,
      a, m, e, A, M, E, U, V, X] using hresidual
  have hdet := threeBlockDeterminant_nonnegative_of_middlePivotResidual
    hM hadj.1 hadj.2 hres
  unfold _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellCommonParentThreeBlockDeterminant
  change 0 ≤
    _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellThreeBlockDeterminant
      A M E U V
        ((bombieriTwoBlockGlobalCrossSymbol a e).re)
  have hX : (bombieriTwoBlockGlobalCrossSymbol a e).re = X := by
    dsimp only [a, e, X]
    exact _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCell_remoteEndpointGlobalCross_re_eq_balance
      parent k
  rw [hX]
  exact hdet

/-- A nonzero real middle-three block has strictly positive Bombieri
diagonal.  This removes the only singular pivot in the nondegenerate
five-cell case. -/
theorem fiveCellMiddleThree_quadratic_pos_of_ne_zero
    (parent : BombieriTest)
    (hparent : bombieriConjugateTest parent = parent) (k : ℤ)
    (hmiddle :
      _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellMiddleThree
        parent k ≠ 0) :
    0 < bombieriRealQuadraticValue
      (_root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellMiddleThree
        parent k) := by
  let m : BombieriTest :=
    _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellMiddleThree
      parent k
  have hcell : BombieriRatioTwoCell m := by
    rw [show m = monotoneQuarterFiniteBlock parent k 1 3 by
      exact fiveCellMiddleThree_eq_finiteBlock parent k]
    exact monotoneQuarterFiniteBlock_ratioTwo_of_le_three
      parent k 1 3 (by omega)
  have hmreal : bombieriConjugateTest m = m := by
    rw [show m = monotoneQuarterFiniteBlock parent k 1 3 by
      exact fiveCellMiddleThree_eq_finiteBlock parent k]
    exact bombieriConjugateTest_monotoneQuarterFiniteBlock
      parent hparent k 1 3
  have hcoercive := real_ratioTwo_localCriticalForm_re_ge_criticalLogEnergy
    m hcell hmreal
  have henergy : 0 < bombieriCriticalLogEnergy m :=
    bombieriCriticalLogEnergy_pos_of_ne_zero m hmiddle
  have hlocal : 0 < (bombieriLocalCriticalForm m m).re := by
    have hcoeff : 0 < (1 / 12000 : ℝ) := by norm_num
    exact lt_of_lt_of_le (mul_pos hcoeff henergy) hcoercive
  obtain ⟨a, b, ha, hab, hsupport, hratio⟩ := hcell
  have heq := bombieriFunctional_quadratic_eq_bombieriLocalCriticalForm_le_two
    m ha hab hsupport hratio
  unfold bombieriRealQuadraticValue
  rw [heq]
  exact hlocal

private theorem middlePivotResidual_reversed_of_constraints
    {A M E U V X : ℝ}
    (h : _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.FiveCellCoupledEndpointSchurConstraints A M E U V X)
    (hMpos : 0 < M)
    (hAM : U ^ 2 ≤ A * M)
    (hME : V ^ 2 ≤ M * E) :
    (A * M - U ^ 2) * (M * E - V ^ 2) <
      (M * X - U * V) ^ 2 := by
  rcases h with
    ⟨_hA, _hM, _hE, _hL, _hR, _hleftMean, _hleftDet,
      _hrightMean, _hrightDet, hwhole⟩
  let alpha : ℝ := A * M - U ^ 2
  let beta : ℝ := M * E - V ^ 2
  let delta : ℝ := M * X - U * V
  have halpha : 0 ≤ alpha := by
    dsimp only [alpha]
    linarith
  have hbeta : 0 ≤ beta := by
    dsimp only [beta]
    linarith
  by_contra hnot
  have hdelta : delta ^ 2 ≤ alpha * beta := le_of_not_gt hnot
  have hschur : 0 ≤ alpha + beta + 2 * delta := by
    nlinarith [sq_nonneg (alpha - beta),
      sq_nonneg (alpha + beta + 2 * delta)]
  have hidentity :
      M * (A + M + E + 2 * (U + V + X)) =
        (M + U + V) ^ 2 + alpha + beta + 2 * delta := by
    dsimp only [alpha, beta, delta]
    ring
  have hscaled : 0 ≤ M * (A + M + E + 2 * (U + V + X)) := by
    rw [hidentity]
    nlinarith [sq_nonneg (M + U + V)]
  have hnonnegative : 0 ≤ A + M + E + 2 * (U + V + X) :=
    (mul_nonneg_iff_of_pos_left hMpos).mp hscaled
  exact (not_lt_of_ge hnonnegative) hwhole

private theorem finiteBlock_middleThree_eq_fiveCellMiddleThree
    (parent : BombieriTest) (lo : ℤ) (start : ℕ) :
    monotoneQuarterFiniteBlock parent lo (start + 1) 3 =
      _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellMiddleThree
        parent (monotoneQuarterFiniteBlockBase lo start) := by
  classical
  simp [monotoneQuarterFiniteBlock,
    monotoneQuarterFiniteBlockBase,
    _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellMiddleThree,
    Finset.sum_range_succ]
  congr 1 <;> ring

/-- Production form of the sharp residual obstruction.  Once four-cell
positivity is available, every nondegenerate support-minimal negative
five-cell block strictly reverses the one remaining middle-pivot
common-parent contraction. -/
theorem supportMinimalNegativeMonotoneBlock_length_five_middlePivotResidual_reversed
    (hfour : RealFourCellProductionNonnegative)
    {parent : BombieriTest} {lo : ℤ} {N start len : ℕ}
    (hparent : bombieriConjugateTest parent = parent)
    (hmin : IsSupportMinimalNegativeMonotoneBlock
      parent lo N start len) (hlen : len = 5)
    (hmiddle :
      _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellMiddleThree
        parent (monotoneQuarterFiniteBlockBase lo start) ≠ 0) :
    let k := monotoneQuarterFiniteBlockBase lo start
    let a := monotoneQuarterCell parent k
    let m := _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellMiddleThree
      parent k
    let e := monotoneQuarterCell parent (k + 4)
    let A := bombieriRealQuadraticValue a
    let M := bombieriRealQuadraticValue m
    let E := bombieriRealQuadraticValue e
    let U := (bombieriTwoBlockGlobalCrossSymbol a m).re
    let V := (bombieriTwoBlockGlobalCrossSymbol m e).re
    let X := _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellRemoteEndpointBalance
      parent k
    (A * M - U ^ 2) * (M * E - V ^ 2) <
      (M * X - U * V) ^ 2 := by
  dsimp only
  let k : ℤ := monotoneQuarterFiniteBlockBase lo start
  let a : BombieriTest := monotoneQuarterCell parent k
  let m : BombieriTest :=
    _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellMiddleThree
      parent k
  let e : BombieriTest := monotoneQuarterCell parent (k + 4)
  let A : ℝ := bombieriRealQuadraticValue a
  let M : ℝ := bombieriRealQuadraticValue m
  let E : ℝ := bombieriRealQuadraticValue e
  let U : ℝ := (bombieriTwoBlockGlobalCrossSymbol a m).re
  let V : ℝ := (bombieriTwoBlockGlobalCrossSymbol m e).re
  let X : ℝ :=
    _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellRemoteEndpointBalance
      parent k
  have hconstraints :=
    _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.supportMinimalNegativeMonotoneBlock_length_five_coupledEndpointSchur
      hmin hlen
  dsimp only at hconstraints
  have hmiddleEq :
      monotoneQuarterFiniteBlock parent lo (start + 1) 3 = m := by
    dsimp only [m, k]
    exact finiteBlock_middleThree_eq_fiveCellMiddleThree parent lo start
  rw [hmiddleEq] at hconstraints
  have hadj := fiveCell_adjacentPrincipalMinors_of_fourCellProduction
    hfour parent hparent k
  change U ^ 2 ≤ A * M ∧ V ^ 2 ≤ M * E at hadj
  have hMpos : 0 < M := by
    dsimp only [M, m, k]
    exact fiveCellMiddleThree_quadratic_pos_of_ne_zero
      parent hparent (monotoneQuarterFiniteBlockBase lo start) hmiddle
  exact middlePivotResidual_reversed_of_constraints
    hconstraints hMpos hadj.1 hadj.2

private theorem bombieriRealQuadraticValue_zero :
    bombieriRealQuadraticValue (0 : BombieriTest) = 0 := by
  unfold bombieriRealQuadraticValue
  have h := bombieriFunctional_quadratic_smul
    (0 : ℂ) (0 : BombieriTest)
  simpa using congrArg Complex.re h

private theorem bombieriTwoBlockGlobalCrossSymbol_zero_left
    (g : BombieriTest) :
    bombieriTwoBlockGlobalCrossSymbol 0 g = 0 := by
  calc
    bombieriTwoBlockGlobalCrossSymbol 0 g =
        starRingEnd ℂ (bombieriTwoBlockGlobalCrossSymbol g 0) :=
      (_root_.ArithmeticHodge.Analysis.MultiplicativeWeil.bombieriTwoBlockGlobalCrossSymbol_conj_swap
        0 g).symm
    _ = 0 := by
      rw [bombieriTwoBlockGlobalCrossSymbol_zero_right]
      exact map_zero (starRingEnd ℂ)

/-- Exact obstruction to using the full determinant as the entire
five-cell closure: if the middle three-cell block vanishes, the common-parent
determinant is identically zero, independently of the remote endpoint
corner. -/
theorem fiveCellCommonParentThreeBlockDeterminant_eq_zero_of_middle_zero
    (parent : BombieriTest) (k : ℤ)
    (hmiddle :
      _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellMiddleThree
        parent k = 0) :
    _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellCommonParentThreeBlockDeterminant
      parent k = 0 := by
  unfold _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellCommonParentThreeBlockDeterminant
  rw [hmiddle, bombieriRealQuadraticValue_zero,
    bombieriTwoBlockGlobalCrossSymbol_zero_right,
    bombieriTwoBlockGlobalCrossSymbol_zero_left]
  simp [_root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellThreeBlockDeterminant]

/-- The sharp middle-pivot contraction is likewise vacuous in the zero-middle
case.  A separate sparse-endpoint argument is mathematically unavoidable. -/
theorem middlePivotResidualContraction_of_middle_zero
    (parent : BombieriTest) (k : ℤ)
    (hmiddle :
      _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellMiddleThree
        parent k = 0) :
    FiveCellCommonParentMiddlePivotResidualContraction parent k := by
  unfold FiveCellCommonParentMiddlePivotResidualContraction
  rw [hmiddle]
  dsimp only
  rw [bombieriRealQuadraticValue_zero,
    bombieriTwoBlockGlobalCrossSymbol_zero_right,
    bombieriTwoBlockGlobalCrossSymbol_zero_left]
  norm_num

private theorem fiveCellMiddleThree_apply
    (parent : BombieriTest) (k : ℤ) (x : ℝ) :
    _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellMiddleThree
        parent k x =
      ((monotoneQuarterStep (k + 1) x -
          monotoneQuarterStep (k + 4) x : ℝ) : ℂ) * parent x := by
  rw [_root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellMiddleThree]
  simp only [TestFunction.coe_add, Pi.add_apply, monotoneQuarterCell_apply]
  unfold monotoneQuarterWeight
  push_cast
  ring

private theorem monotoneQuarterStep_lt_one_of_lt_succ
    (j : ℤ) {x : ℝ}
    (hx : x < quarterLogLatticePoint (j + 1)) :
    monotoneQuarterStep j x < 1 := by
  unfold monotoneQuarterStep
  apply Real.smoothTransition.lt_one_of_lt_one
  rw [div_lt_one (quarterLogLatticePoint_gap_pos j)]
  linarith

private theorem parent_two_mul_eq_zero_of_middle_zero_of_left
    (parent : BombieriTest) (k : ℤ)
    (hmiddle :
      _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellMiddleThree
        parent k = 0)
    {x : ℝ}
    (hxleft : quarterLogLatticePoint k < x)
    (hxright : x < quarterLogLatticePoint (k + 1)) :
    parent (2 * x) = 0 := by
  have hpoint := congrArg (fun g : BombieriTest ↦ g (2 * x)) hmiddle
  have hpoint' :
      _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellMiddleThree
          parent k (2 * x) = 0 := by
    simpa only [TestFunction.coe_zero, Pi.zero_apply] using hpoint
  rw [fiveCellMiddleThree_apply] at hpoint'
  have hstepOne : monotoneQuarterStep (k + 1) (2 * x) = 1 := by
    apply monotoneQuarterStep_eq_one_of_le
    calc
      quarterLogLatticePoint (k + 1 + 1) ≤
          quarterLogLatticePoint (k + 4) :=
        quarterLogLatticePoint_mono (by omega)
      _ = 2 * quarterLogLatticePoint k := by
        rw [quarterLogLatticePoint_add_four]
      _ ≤ 2 * x := (mul_lt_mul_of_pos_left hxleft (by norm_num)).le
  have htransport :
      monotoneQuarterStep (k + 4) (2 * x) =
        monotoneQuarterStep k x :=
    monotoneQuarterStep_add_four_two_mul k x
  have hstepLt : monotoneQuarterStep k x < 1 :=
    monotoneQuarterStep_lt_one_of_lt_succ k hxright
  rw [hstepOne, htransport] at hpoint'
  exact (mul_eq_zero.mp hpoint').resolve_left
    (Complex.ofReal_ne_zero.mpr (sub_pos.mpr hstepLt).ne')

private theorem parent_eq_zero_of_middle_zero_of_right
    (parent : BombieriTest) (k : ℤ)
    (hmiddle :
      _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellMiddleThree
        parent k = 0)
    {x : ℝ}
    (hxleft : quarterLogLatticePoint (k + 1) < x)
    (hxright : x < quarterLogLatticePoint (k + 2)) :
    parent x = 0 := by
  have hpoint := congrArg (fun g : BombieriTest ↦ g x) hmiddle
  have hpoint' :
      _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellMiddleThree
          parent k x = 0 := by
    simpa only [TestFunction.coe_zero, Pi.zero_apply] using hpoint
  rw [fiveCellMiddleThree_apply] at hpoint'
  have hstepPos : 0 < monotoneQuarterStep (k + 1) x :=
    monotoneQuarterStep_pos_of_lattice_lt (k + 1) hxleft
  have hstepZero : monotoneQuarterStep (k + 4) x = 0 := by
    apply monotoneQuarterStep_eq_zero_of_le
    exact hxright.le.trans (quarterLogLatticePoint_mono (by omega))
  rw [hstepZero, sub_zero] at hpoint'
  exact (mul_eq_zero.mp hpoint').resolve_left
    (Complex.ofReal_ne_zero.mpr hstepPos.ne')

private theorem parent_eq_zero_of_middle_zero_of_upper_transition
    (parent : BombieriTest) (k : ℤ)
    (hmiddle :
      _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellMiddleThree
        parent k = 0)
    {x : ℝ}
    (hxleft : quarterLogLatticePoint (k + 4) < x)
    (hxright : x < quarterLogLatticePoint (k + 5)) :
    parent x = 0 := by
  have hpoint := congrArg (fun g : BombieriTest ↦ g x) hmiddle
  have hpoint' :
      _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellMiddleThree
          parent k x = 0 := by
    simpa only [TestFunction.coe_zero, Pi.zero_apply] using hpoint
  rw [fiveCellMiddleThree_apply] at hpoint'
  have hstepOne : monotoneQuarterStep (k + 1) x = 1 := by
    apply monotoneQuarterStep_eq_one_of_le
    simpa only [show k + 1 + 1 = k + 2 by ring] using
      (quarterLogLatticePoint_mono (m := k + 2) (n := k + 4)
        (by omega)).trans hxleft.le
  have hstepLt : monotoneQuarterStep (k + 4) x < 1 :=
    monotoneQuarterStep_lt_one_of_lt_succ (k + 4) (by
      simpa only [show k + 4 + 1 = k + 5 by ring] using hxright)
  rw [hstepOne] at hpoint'
  exact (mul_eq_zero.mp hpoint').resolve_left
    (Complex.ofReal_ne_zero.mpr (sub_pos.mpr hstepLt).ne')

/-- If the middle three-cell block vanishes, the two surviving endpoint
cells collapse to the outer quarter-step transitions.  Their closed supports
are separated by an exact factor-two gap. -/
theorem fiveCell_endpoint_tsupports_collapse_of_middle_zero
    (parent : BombieriTest) (k : ℤ)
    (hmiddle :
      _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellMiddleThree
        parent k = 0) :
    tsupport (monotoneQuarterCell parent k : ℝ → ℂ) ⊆
        Set.Icc (quarterLogLatticePoint k)
          (quarterLogLatticePoint (k + 1)) ∧
      tsupport (monotoneQuarterCell parent (k + 4) : ℝ → ℂ) ⊆
        Set.Icc (quarterLogLatticePoint (k + 5))
          (quarterLogLatticePoint (k + 6)) := by
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
        parent_eq_zero_of_middle_zero_of_right parent k hmiddle
          hxleft (lt_of_not_ge hxright)
      apply hxne
      rw [monotoneQuarterCell_apply, hparent, mul_zero]
  · rw [tsupport]
    apply closure_minimal _ isClosed_Icc
    intro x hx
    have hxne : monotoneQuarterCell parent (k + 4) x ≠ 0 :=
      Function.mem_support.mp hx
    have hwide := monotoneQuarterCell_tsupport_subset parent (k + 4)
      (subset_tsupport _ hx)
    refine ⟨?_, by
      simpa only [show k + 4 + 2 = k + 6 by ring] using hwide.2⟩
    by_contra hnot
    have hxright : x < quarterLogLatticePoint (k + 5) :=
      lt_of_not_ge hnot
    by_cases hxleft : x ≤ quarterLogLatticePoint (k + 4)
    · apply hxne
      rw [monotoneQuarterCell_apply,
        monotoneQuarterWeight_eq_zero_of_le (k + 4) hxleft]
      simp
    · have hparent : parent x = 0 :=
        parent_eq_zero_of_middle_zero_of_upper_transition parent k hmiddle
          (lt_of_not_ge hxleft) hxright
      apply hxne
      rw [monotoneQuarterCell_apply, hparent, mul_zero]

/-- For two strictly separated physical supports at unit dilation, the local
critical cross is the continuous endpoint term minus one nonsingular physical
Cauchy kernel.  This is the exact real-space formula used below on the two
collapsed five-cell endpoint rectangles. -/
private theorem bombieriLocalCriticalForm_eq_separatedPhysicalKernel_one
    (f g : BombieriTest) {af bf ag bg : ℝ}
    (haf : 0 < af) (hag : 0 < ag) (hbg : 0 < bg)
    (hfsupport : tsupport f ⊆ Set.Icc af bf)
    (hgsupport : tsupport g ⊆ Set.Icc ag bg)
    (hsep : bg / af < 1) :
    bombieriLocalCriticalForm f g =
      (∫ x : ℝ in Set.Ioi 0,
          starRingEnd ℂ (bombieriDirectedCorrelation f g x)) -
        ∫ x : ℝ in Set.Ioi 0,
          starRingEnd ℂ (bombieriDirectedCorrelation f g x) /
            ((x * (x ^ 2 - 1) : ℝ) : ℂ) := by
  have hsepWeak : bg ≤ (1 : ℝ) * af := by
    have hlt : bg < af := by
      simpa using (div_lt_iff₀ haf).mp hsep
    simpa using hlt.le
  have hlocal :=
    bombieriLocalCriticalForm_dilation_eq_endpoint_sub_cauchyTail_of_support
      f g haf hag hbg (by norm_num : (0 : ℝ) < 1)
      hfsupport hgsupport hsepWeak
  have hbridge :=
    tsum_bombieriCauchyCrossValue_normalizedDilation_tail_eq_moments
      f g haf hag hbg (by norm_num : (0 : ℝ) < 1)
      hfsupport hgsupport hsepWeak
  have hphysical :=
    tsum_scaled_farCauchyMomentCorrection_eq_physicalKernel
      f g (by norm_num : (0 : ℝ) < 1) haf hag hbg
      hfsupport hgsupport hsep
  rw [normalizedDilation_one] at hlocal hbridge
  have htail :
      (∑' k : ℕ, bombieriCauchyCrossValue f g (k + 1)) =
        ∫ x : ℝ in Set.Ioi 0,
          starRingEnd ℂ (bombieriDirectedCorrelation f g x) /
            ((x * (x ^ 2 - 1) : ℝ) : ℂ) := by
    rw [hbridge]
    simpa only [Real.sqrt_one, Complex.ofReal_one, one_mul,
      Real.log_one, mul_zero, neg_zero, Real.exp_zero] using hphysical
  rw [hlocal, htail,
    integral_star_bombieriDirectedCorrelation_eq_mellin_endpoints]
  norm_num

/-- The scalar kernel left after the polar endpoint term and the separated
Cauchy tail are put over the same physical correlation. -/
def fiveCellSeparatedLocalKernelWeight (x : ℝ) : ℝ :=
  1 - (x * (x ^ 2 - 1))⁻¹

/-- On the collapsed five-cell endpoint quotient, which starts at two, the
entire separated local-critical kernel has a strict positive sign. -/
theorem fiveCellSeparatedLocalKernelWeight_pos
    {x : ℝ} (hx : 2 ≤ x) :
    0 < fiveCellSeparatedLocalKernelWeight x := by
  have hxpos : 0 < x := (by norm_num : (0 : ℝ) < 2).trans_le hx
  have hsq : (4 : ℝ) ≤ x ^ 2 := by nlinarith [sq_nonneg (x - 2)]
  have hthree : (3 : ℝ) ≤ x ^ 2 - 1 := by linarith
  have hden : 0 < x * (x ^ 2 - 1) :=
    mul_pos hxpos (by linarith)
  have hsix : (6 : ℝ) ≤ x * (x ^ 2 - 1) := by
    have hprod : 0 ≤ (x - 2) * (x ^ 2 - 4) :=
      mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hsq)
    nlinarith
  have hinv : (x * (x ^ 2 - 1))⁻¹ ≤ (6 : ℝ)⁻¹ :=
    (inv_le_inv₀ hden (by norm_num)).2 hsix
  unfold fiveCellSeparatedLocalKernelWeight
  norm_num at hinv ⊢
  linarith

/-- The preceding difference of physical integrals is one integral against
the strict positive scalar kernel. -/
private theorem bombieriLocalCriticalForm_eq_separatedPositiveKernel_one
    (f g : BombieriTest) {af bf ag bg : ℝ}
    (haf : 0 < af) (hag : 0 < ag) (hbg : 0 < bg)
    (hfsupport : tsupport f ⊆ Set.Icc af bf)
    (hgsupport : tsupport g ⊆ Set.Icc ag bg)
    (hsep : bg / af < 1) :
    bombieriLocalCriticalForm f g =
      ∫ x : ℝ in Set.Icc (af / bg) (bf / ag),
        starRingEnd ℂ (bombieriDirectedCorrelation f g x) *
          (fiveCellSeparatedLocalKernelWeight x : ℂ) := by
  let K : Set ℝ := Set.Icc (af / bg) (bf / ag)
  let H : ℝ → ℂ := fun x ↦
    starRingEnd ℂ (bombieriDirectedCorrelation f g x)
  have hLpos : 0 < af / bg := div_pos haf hbg
  have hKpos : K ⊆ Set.Ioi 0 := by
    intro x hx
    exact hLpos.trans_le hx.1
  have hHIntIoi : IntegrableOn H (Set.Ioi 0) := by
    simpa only [H] using
      (star_bombieriDirectedCorrelation_integrableOn_Ioi
        f g haf hag hbg hfsupport hgsupport)
  have hHIntK : IntegrableOn H K := hHIntIoi.mono_set hKpos
  have hone : 1 < af / bg := by
    have hlt : bg < af := by
      simpa using (div_lt_iff₀ haf).mp hsep
    exact (lt_div_iff₀ hbg).2 (by simpa [mul_comm] using hlt)
  have hdenPos (x : ℝ) (hx : x ∈ K) :
      0 < x * (x ^ 2 - 1) := by
    have hxone : 1 < x := hone.trans_le hx.1
    exact mul_pos (zero_lt_one.trans hxone)
      (by nlinarith [sq_nonneg (x - 1)])
  have hscalarContinuous : ContinuousOn
      (fun x : ℝ ↦ (((x * (x ^ 2 - 1) : ℝ) : ℂ))⁻¹) K := by
    intro x hx
    have hbase : ContinuousAt
        (fun y : ℝ ↦ (((y * (y ^ 2 - 1) : ℝ) : ℂ))) x := by fun_prop
    exact (hbase.inv₀ (Complex.ofReal_ne_zero.mpr
      (hdenPos x hx).ne')).continuousWithinAt
  have htailIntK : IntegrableOn
      (fun x : ℝ ↦ H x /
        ((x * (x ^ 2 - 1) : ℝ) : ℂ)) K := by
    simpa only [div_eq_mul_inv, mul_comm] using
      hHIntK.continuousOn_mul hscalarContinuous isCompact_Icc
  have hHrestrict :
      (∫ x : ℝ in Set.Ioi 0, H x) = ∫ x : ℝ in K, H x := by
    apply setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi
    · exact hKpos
    · intro x hx
      exact star_bombieriDirectedCorrelation_eq_zero_outside_supportQuotient
        f g haf hag hbg hfsupport hgsupport hx.2
  have htailRestrict :
      (∫ x : ℝ in Set.Ioi 0,
          H x / ((x * (x ^ 2 - 1) : ℝ) : ℂ)) =
        ∫ x : ℝ in K,
          H x / ((x * (x ^ 2 - 1) : ℝ) : ℂ) := by
    apply setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi
    · exact hKpos
    · intro x hx
      rw [show H x = 0 by
        exact star_bombieriDirectedCorrelation_eq_zero_outside_supportQuotient
          f g haf hag hbg hfsupport hgsupport hx.2]
      simp
  rw [bombieriLocalCriticalForm_eq_separatedPhysicalKernel_one
      f g haf hag hbg hfsupport hgsupport hsep]
  change (∫ x : ℝ in Set.Ioi 0, H x) -
      (∫ x : ℝ in Set.Ioi 0,
        H x / ((x * (x ^ 2 - 1) : ℝ) : ℂ)) = _
  rw [hHrestrict, htailRestrict,
    ← integral_sub hHIntK htailIntK]
  apply setIntegral_congr_fun measurableSet_Icc
  intro x hx
  change H x - H x / ((x * (x ^ 2 - 1) : ℝ) : ℂ) =
    H x * (fiveCellSeparatedLocalKernelWeight x : ℂ)
  have hden : (x * (x ^ 2 - 1) : ℝ) ≠ 0 := (hdenPos x hx).ne'
  unfold fiveCellSeparatedLocalKernelWeight
  push_cast
  field_simp [hden]

/-- In the zero-middle five-cell geometry, the oriented remote local cross is
exactly the positive separated kernel on the physical quotient rectangle.
Its lower quotient endpoint simplifies to two. -/
theorem fiveCell_remoteEndpointLocalCriticalCross_eq_positiveKernel_of_middle_zero
    (parent : BombieriTest) (k : ℤ)
    (hmiddle :
      _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellMiddleThree
        parent k = 0) :
    bombieriLocalCriticalForm
        (monotoneQuarterCell parent (k + 4))
        (monotoneQuarterCell parent k) =
      ∫ x : ℝ in Set.Icc 2
          (quarterLogLatticePoint (k + 6) /
            quarterLogLatticePoint k),
        starRingEnd ℂ (bombieriDirectedCorrelation
          (monotoneQuarterCell parent (k + 4))
          (monotoneQuarterCell parent k) x) *
            (fiveCellSeparatedLocalKernelWeight x : ℂ) := by
  have hcollapse :=
    fiveCell_endpoint_tsupports_collapse_of_middle_zero parent k hmiddle
  have hsep :
      quarterLogLatticePoint (k + 1) /
          quarterLogLatticePoint (k + 5) < 1 := by
    apply (div_lt_iff₀ (quarterLogLatticePoint_pos (k + 5))).2
    rw [show k + 5 = (k + 1) + 4 by ring,
      quarterLogLatticePoint_add_four]
    linarith [quarterLogLatticePoint_pos (k + 1)]
  have hkernel :=
    bombieriLocalCriticalForm_eq_separatedPositiveKernel_one
      (monotoneQuarterCell parent (k + 4))
      (monotoneQuarterCell parent k)
      (quarterLogLatticePoint_pos (k + 5))
      (quarterLogLatticePoint_pos k)
      (quarterLogLatticePoint_pos (k + 1))
      hcollapse.2 hcollapse.1 hsep
  have hlower :
      quarterLogLatticePoint (k + 5) /
          quarterLogLatticePoint (k + 1) = 2 := by
    rw [show k + 5 = (k + 1) + 4 by ring,
      quarterLogLatticePoint_add_four]
    field_simp [(quarterLogLatticePoint_pos (k + 1)).ne']
  simpa only [hlower] using hkernel

/-- A pair of nonnegative real endpoint tests has a strictly positive
oriented local-critical cross as soon as their separated quotient rectangle
starts at two and contains one matching positive pair of physical points. -/
private theorem bombieriLocalCriticalForm_re_pos_of_nonnegative_factorTwoSeparated
    (f g : BombieriTest) {af bf ag bg cf cg : ℝ}
    (haf : 0 < af) (hag : 0 < ag) (hbg : 0 < bg) (hcg : 0 < cg)
    (hfsupport : tsupport f ⊆ Set.Icc af bf)
    (hgsupport : tsupport g ⊆ Set.Icc ag bg)
    (hquot : 2 ≤ af / bg)
    (hx0 : cf / cg ∈ Set.Ioo (af / bg) (bf / ag))
    (hfnonneg : ∀ x, 0 ≤ (f x).re ∧ (f x).im = 0)
    (hgnonneg : ∀ x, 0 ≤ (g x).re ∧ (g x).im = 0)
    (hfc : 0 < (f cf).re) (hgc : 0 < (g cg).re) :
    0 < (bombieriLocalCriticalForm f g).re := by
  let x₀ : ℝ := cf / cg
  let K : Set ℝ := Set.Icc (af / bg) (bf / ag)
  let H : ℝ → ℂ := fun x ↦
    starRingEnd ℂ (bombieriDirectedCorrelation f g x)
  let F : ℝ → ℝ := fun x ↦
    (H x).re * fiveCellSeparatedLocalKernelWeight x
  have hafbg : bg < af := by
    have htwo : 2 * bg ≤ af := by
      exact (le_div_iff₀ hbg).mp (by simpa [mul_comm] using hquot)
    nlinarith
  have hsep : bg / af < 1 := (div_lt_one haf).2 hafbg
  have hinnerInt (x : ℝ) : IntegrableOn
      (fun y : ℝ ↦ f (x * y) * starRingEnd ℂ (g y))
      (Set.Ioi 0) := by
    have hcont : Continuous
        (fun y : ℝ ↦ f (x * y) * starRingEnd ℂ (g y)) := by fun_prop
    have hgcompact : HasCompactSupport
        (fun y : ℝ ↦ starRingEnd ℂ (g y)) :=
      g.hasCompactSupport.comp_left (by simp)
    have hcompact : HasCompactSupport
        (fun y : ℝ ↦ f (x * y) * starRingEnd ℂ (g y)) := by
      simpa only [Pi.mul_apply] using
        hgcompact.mul_left (f := fun y : ℝ ↦ f (x * y))
    exact (hcont.integrable_of_hasCompactSupport hcompact).integrableOn
  have hHnonneg (x : ℝ) : 0 ≤ (H x).re := by
    dsimp only [H]
    rw [starRingEnd_apply, Complex.star_def, Complex.conj_re]
    unfold bombieriDirectedCorrelation
    calc
      0 ≤ ∫ y : ℝ in Set.Ioi 0,
          (f (x * y) * starRingEnd ℂ (g y)).re := by
        apply integral_nonneg
        intro y
        have hfy := hfnonneg (x * y)
        have hgy := hgnonneg y
        change 0 ≤ (f (x * y) * starRingEnd ℂ (g y)).re
        rw [Complex.mul_re, starRingEnd_apply, Complex.star_def,
          Complex.conj_re, Complex.conj_im, hfy.2, hgy.2]
        simp only [neg_zero, mul_zero, sub_zero]
        exact mul_nonneg hfy.1 hgy.1
      _ = (∫ y : ℝ in Set.Ioi 0,
          f (x * y) * starRingEnd ℂ (g y)).re :=
        integral_re (hinnerInt x)
  have hHpos : 0 < (H x₀).re := by
    let J : ℝ → ℝ := fun y ↦
      (f (x₀ * y) * starRingEnd ℂ (g y)).re
    have hJcont : Continuous J := by
      dsimp only [J]
      fun_prop
    have hgcompact : HasCompactSupport
        (fun y : ℝ ↦ starRingEnd ℂ (g y)) :=
      g.hasCompactSupport.comp_left (by simp)
    have hcomplexCompact : HasCompactSupport
        (fun y : ℝ ↦ f (x₀ * y) * starRingEnd ℂ (g y)) := by
      simpa only [Pi.mul_apply] using
        hgcompact.mul_left (f := fun y : ℝ ↦ f (x₀ * y))
    have hJcompact : HasCompactSupport J := by
      exact hcomplexCompact.comp_left (by simp)
    have hJnonneg : 0 ≤ J := by
      intro y
      have hfy := hfnonneg (x₀ * y)
      have hgy := hgnonneg y
      dsimp only [J]
      rw [Complex.mul_re, starRingEnd_apply, Complex.star_def,
        Complex.conj_re, Complex.conj_im, hfy.2, hgy.2]
      simp only [neg_zero, mul_zero, sub_zero]
      exact mul_nonneg hfy.1 hgy.1
    have hxmul : x₀ * cg = cf := by
      dsimp only [x₀]
      field_simp [hcg.ne']
    have hJcg : J cg ≠ 0 := by
      have hgy := hgnonneg cg
      dsimp only [J]
      rw [hxmul, Complex.mul_re, starRingEnd_apply, Complex.star_def,
        Complex.conj_re, Complex.conj_im,
        (hfnonneg cf).2, hgy.2]
      simp only [neg_zero, mul_zero, sub_zero]
      exact (mul_pos hfc hgc).ne'
    have hwhole : 0 < ∫ y : ℝ, J y :=
      hJcont.integral_pos_of_hasCompactSupport_nonneg_nonzero
        hJcompact hJnonneg hJcg
    have hrestrict : (∫ y : ℝ in Set.Ioi 0, J y) = ∫ y : ℝ, J y := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro y hy
      have hynpos : ¬ 0 < y := by simpa using hy
      have hgyzero : g y = 0 := g.apply_eq_zero_of_nonpos hynpos
      dsimp only [J]
      simp only [hgyzero, map_zero, mul_zero, zero_re]
    dsimp only [H]
    rw [starRingEnd_apply, Complex.star_def, Complex.conj_re]
    unfold bombieriDirectedCorrelation
    calc
      0 < ∫ y : ℝ in Set.Ioi 0, J y := by
        rw [hrestrict]
        exact hwhole
      _ = (∫ y : ℝ in Set.Ioi 0,
          f (x₀ * y) * starRingEnd ℂ (g y)).re :=
        integral_re (hinnerInt x₀)
  have hHIntK : IntegrableOn H K := by
    apply (star_bombieriDirectedCorrelation_integrableOn_Ioi
      f g haf hag hbg hfsupport hgsupport).mono_set
    intro x hx
    exact (div_pos haf hbg).trans_le hx.1
  have hweightContinuous : ContinuousOn
      fiveCellSeparatedLocalKernelWeight K := by
    intro x hx
    have hxge : 2 ≤ x := hquot.trans hx.1
    have hden : x * (x ^ 2 - 1) ≠ 0 := by
      have hxpos : 0 < x := (by norm_num : (0 : ℝ) < 2).trans_le hxge
      exact (mul_pos hxpos (by nlinarith [sq_nonneg (x - 2)])).ne'
    unfold fiveCellSeparatedLocalKernelWeight
    have hbase : ContinuousAt (fun y : ℝ ↦ y * (y ^ 2 - 1)) x := by
      fun_prop
    exact continuousWithinAt_const.sub
      ((hbase.inv₀ hden).continuousWithinAt)
  have hcomplexIntK : IntegrableOn
      (fun x : ℝ ↦ H x *
        (fiveCellSeparatedLocalKernelWeight x : ℂ)) K := by
    have hcastContinuous : ContinuousOn
        (fun x : ℝ ↦ (fiveCellSeparatedLocalKernelWeight x : ℂ)) K :=
      Complex.continuous_ofReal.comp_continuousOn hweightContinuous
    simpa only [mul_comm] using
      hHIntK.continuousOn_mul hcastContinuous isCompact_Icc
  have hpointRe (x : ℝ) :
      (H x * (fiveCellSeparatedLocalKernelWeight x : ℂ)).re = F x := by
    dsimp only [F]
    rw [Complex.mul_re]
    norm_num
  have hFIntK : IntegrableOn F K := by
    apply hcomplexIntK.re.congr
    filter_upwards [] with x
    exact hpointRe x
  have hFrewrite :
      (bombieriLocalCriticalForm f g).re = ∫ x : ℝ in K, F x := by
    have hkernel :=
      bombieriLocalCriticalForm_eq_separatedPositiveKernel_one
        f g haf hag hbg hfsupport hgsupport hsep
    rw [hkernel]
    change (∫ x : ℝ in K,
      H x * (fiveCellSeparatedLocalKernelWeight x : ℂ)).re = _
    calc
      (∫ x : ℝ in K,
          H x * (fiveCellSeparatedLocalKernelWeight x : ℂ)).re =
          ∫ x : ℝ in K,
            (H x * (fiveCellSeparatedLocalKernelWeight x : ℂ)).re :=
        (integral_re hcomplexIntK).symm
      _ = ∫ x : ℝ in K, F x := by
        apply integral_congr_ae
        filter_upwards [] with x
        exact hpointRe x
  have hFnonneg : ∀ x ∈ K, 0 ≤ F x := by
    intro x hx
    exact mul_nonneg (hHnonneg x)
      (fiveCellSeparatedLocalKernelWeight_pos (hquot.trans hx.1)).le
  have hHreCont : Continuous (fun x : ℝ ↦ (H x).re) := by
    exact Complex.continuous_re.comp
      (star_bombieriDirectedCorrelation_contDiff f g).continuous
  let O : Set ℝ := Function.support (fun x : ℝ ↦ (H x).re) ∩
    Set.Ioo (af / bg) (bf / ag)
  have hOopen : IsOpen O :=
    hHreCont.isOpen_support.inter isOpen_Ioo
  have hx₀O : x₀ ∈ O := by
    exact ⟨Function.mem_support.mpr hHpos.ne', by simpa only [x₀] using hx0⟩
  have hOmeasure : 0 < volume O := hOopen.measure_pos volume ⟨x₀, hx₀O⟩
  have hOsubset : O ⊆ Function.support F ∩ K := by
    intro x hx
    have hHxPos : 0 < (H x).re :=
      lt_of_le_of_ne (hHnonneg x) (Ne.symm (Function.mem_support.mp hx.1))
    have hxK : x ∈ K := Set.Ioo_subset_Icc_self hx.2
    have hwPos := fiveCellSeparatedLocalKernelWeight_pos
      (hquot.trans hxK.1)
    constructor
    · exact Function.mem_support.mpr (mul_pos hHxPos hwPos).ne'
    · exact hxK
  have hsupportMeasure : 0 < volume (Function.support F ∩ K) :=
    hOmeasure.trans_le (measure_mono hOsubset)
  have hFnonnegAE : ∀ᵐ x : ℝ ∂volume.restrict K, 0 ≤ F x := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact hFnonneg x hx
  have hFpos : 0 < ∫ x : ℝ in K, F x := by
    apply (setIntegral_pos_iff_support_of_nonneg_ae
      hFnonnegAE hFIntK).2
    exact hsupportMeasure
  rw [hFrewrite]
  exact hFpos

private theorem exists_nonnegative_bombieri_bump_at
    (c : ℝ) (U : Set ℝ) (hU : U ∈ 𝓝 c) (hUpos : U ⊆ Ioi 0) :
    ∃ eta : BombieriTest,
      eta c = 1 ∧ tsupport (eta : ℝ → ℂ) ⊆ U ∧
        bombieriConjugateTest eta = eta ∧
        ∀ x, 0 ≤ (eta x).re ∧ (eta x).im = 0 := by
  obtain ⟨phi, hphiSupport, hphiCompact, hphiSmooth, hphiRange, hphiOne⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) hU
  have hsmooth : ContDiff ℝ ∞ (fun x : ℝ ↦ (phi x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hphiSmooth
  have hcompact : HasCompactSupport (fun x : ℝ ↦ (phi x : ℂ)) := by
    change HasCompactSupport (Complex.ofRealCLM ∘ phi)
    exact hphiCompact.comp_left rfl
  have htsupport : tsupport (fun x : ℝ ↦ (phi x : ℂ)) = tsupport phi := by
    have hsupport : Function.support (fun x : ℝ ↦ (phi x : ℂ)) =
        Function.support phi := by
      ext x
      simp only [Function.mem_support, ne_eq, Complex.ofReal_eq_zero]
    unfold tsupport
    rw [hsupport]
  let eta : BombieriTest := TestFunction.mk
    (fun x : ℝ ↦ (phi x : ℂ)) hsmooth hcompact (by
      rw [htsupport]
      simpa only [positiveHalfLine] using hphiSupport.trans hUpos)
  refine ⟨eta, ?_, ?_, ?_, ?_⟩
  · change (phi c : ℂ) = 1
    rw [hphiOne]
    norm_num
  · change tsupport (fun x : ℝ ↦ (phi x : ℂ)) ⊆ U
    rw [htsupport]
    exact hphiSupport
  · apply TestFunction.ext
    intro x
    simp only [bombieriConjugateTest_apply]
    change starRingEnd ℂ (phi x : ℂ) = (phi x : ℂ)
    simp
  · intro x
    have hx := hphiRange (Set.mem_range_self x)
    change 0 ≤ (phi x : ℂ).re ∧ (phi x : ℂ).im = 0
    exact ⟨by simpa using hx.1, by simp⟩

private theorem monotoneQuarterWeight_pos_on_first_transition
    (j : ℤ) {x : ℝ}
    (hx : x ∈ Set.Ioo (quarterLogLatticePoint j)
      (quarterLogLatticePoint (j + 1))) :
    0 < monotoneQuarterWeight j x := by
  unfold monotoneQuarterWeight
  rw [monotoneQuarterStep_eq_zero_of_le (j + 1) hx.2.le]
  simpa only [sub_zero] using
    monotoneQuarterStep_pos_of_lattice_lt j hx.1

private theorem monotoneQuarterWeight_pos_on_second_transition
    (j : ℤ) {x : ℝ}
    (hx : x ∈ Set.Ioo (quarterLogLatticePoint (j + 1))
      (quarterLogLatticePoint (j + 2))) :
    0 < monotoneQuarterWeight j x := by
  unfold monotoneQuarterWeight
  rw [monotoneQuarterStep_eq_one_of_le j hx.1.le]
  exact sub_pos.mpr (monotoneQuarterStep_lt_one_of_lt_succ (j + 1) (by
    simpa only [show j + 1 + 1 = j + 2 by ring] using hx.2))

private theorem monotoneQuarterCell_nonnegative_of_parent_nonnegative
    (parent : BombieriTest) (j : ℤ)
    (hparent : ∀ x, 0 ≤ (parent x).re ∧ (parent x).im = 0) :
    ∀ x, 0 ≤ (monotoneQuarterCell parent j x).re ∧
      (monotoneQuarterCell parent j x).im = 0 := by
  intro x
  rw [monotoneQuarterCell_apply]
  have hp := hparent x
  constructor
  · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    exact mul_nonneg (monotoneQuarterWeight_nonnegative j x) hp.1
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, zero_add, hp.2, mul_zero]

private theorem monotoneQuarterCell_re_pos_at_first_transition
    (parent : BombieriTest) (j : ℤ) {x : ℝ}
    (hx : x ∈ Set.Ioo (quarterLogLatticePoint j)
      (quarterLogLatticePoint (j + 1)))
    (hparent : parent x = 1) :
    0 < (monotoneQuarterCell parent j x).re := by
  rw [monotoneQuarterCell_apply, hparent]
  simpa only [mul_one, Complex.ofReal_re] using
    monotoneQuarterWeight_pos_on_first_transition j hx

private theorem fiveCell_cell_eq_zero_of_tsupport_below
    (parent : BombieriTest) (j : ℤ)
    (hupper : tsupport parent ⊆ Set.Iic (quarterLogLatticePoint j)) :
    monotoneQuarterCell parent j = 0 := by
  apply TestFunction.ext
  intro x
  by_cases hx : parent x = 0
  · simp [monotoneQuarterCell_apply, hx]
  · have hxt : x ∈ tsupport parent :=
      subset_tsupport parent (Function.mem_support.mpr hx)
    rw [monotoneQuarterCell_apply,
      monotoneQuarterWeight_eq_zero_of_le j (hupper hxt),
      Complex.ofReal_zero, zero_mul]
    rfl

private theorem fiveCell_cell_eq_zero_of_tsupport_above
    (parent : BombieriTest) (j : ℤ)
    (hlower : tsupport parent ⊆
      Set.Ici (quarterLogLatticePoint (j + 2))) :
    monotoneQuarterCell parent j = 0 := by
  apply TestFunction.ext
  intro x
  by_cases hx : parent x = 0
  · simp [monotoneQuarterCell_apply, hx]
  · have hxt : x ∈ tsupport parent :=
      subset_tsupport parent (Function.mem_support.mpr hx)
    rw [monotoneQuarterCell_apply,
      monotoneQuarterWeight_eq_zero_of_le_left j (hlower hxt),
      Complex.ofReal_zero, zero_mul]
    rfl

private theorem fiveCellMiddleThree_eq_zero_of_tsupport_below
    (parent : BombieriTest) (k : ℤ)
    (hupper : tsupport parent ⊆
      Set.Iic (quarterLogLatticePoint (k + 1))) :
    _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellMiddleThree
      parent k = 0 := by
  apply TestFunction.ext
  intro x
  rw [fiveCellMiddleThree_apply]
  by_cases hx : parent x = 0
  · simp [hx]
  · have hxt : x ∈ tsupport parent :=
      subset_tsupport parent (Function.mem_support.mpr hx)
    rw [monotoneQuarterStep_eq_zero_of_le (k + 1) (hupper hxt),
      monotoneQuarterStep_eq_zero_of_le (k + 4)
        ((hupper hxt).trans (quarterLogLatticePoint_mono (by omega)))]
    simp

private theorem fiveCellMiddleThree_eq_zero_of_tsupport_above
    (parent : BombieriTest) (k : ℤ)
    (hlower : tsupport parent ⊆
      Set.Ici (quarterLogLatticePoint (k + 5))) :
    _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellMiddleThree
      parent k = 0 := by
  apply TestFunction.ext
  intro x
  rw [fiveCellMiddleThree_apply]
  by_cases hx : parent x = 0
  · simp [hx]
  · have hxt : x ∈ tsupport parent :=
      subset_tsupport parent (Function.mem_support.mpr hx)
    rw [monotoneQuarterStep_eq_one_of_le (k + 1) (by
        simpa only [show k + 1 + 1 = k + 2 by ring] using
          ((quarterLogLatticePoint_mono (m := k + 2) (n := k + 5)
            (by omega)).trans (hlower hxt))),
      monotoneQuarterStep_eq_one_of_le (k + 4) (by
        simpa only [show k + 4 + 1 = k + 5 by ring] using hlower hxt)]
    simp

private theorem fiveCellMiddleThree_add
    (f g : BombieriTest) (k : ℤ) :
    _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellMiddleThree
        (f + g) k =
      _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellMiddleThree
          f k +
        _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellMiddleThree
          g k := by
  apply TestFunction.ext
  intro x
  simp only [fiveCellMiddleThree_apply, TestFunction.coe_add, Pi.add_apply]
  ring

private theorem fiveCellMiddleThree_neg
    (f : BombieriTest) (k : ℤ) :
    _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellMiddleThree
        (-f) k =
      -_root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellMiddleThree
        f k := by
  apply TestFunction.ext
  intro x
  simp only [fiveCellMiddleThree_apply, TestFunction.coe_neg, Pi.neg_apply]
  ring

/-- The strict-positive scalar kernel does not give the mixed local cross a
universal sign, even in the exact zero-middle geometry.  Two nonnegative
endpoint bumps give a positive cross; reversing only the upper bump gives a
real common parent with zero middle block and a strictly negative cross. -/
theorem exists_real_middleZero_fiveCell_negative_remoteLocalCross
    (k : ℤ) :
    ∃ parent : BombieriTest,
      bombieriConjugateTest parent = parent ∧
        _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellMiddleThree
          parent k = 0 ∧
        (bombieriLocalCriticalForm
          (monotoneQuarterCell parent k)
          (monotoneQuarterCell parent (k + 4))).re < 0 := by
  let a₀ : ℝ := quarterLogLatticePoint k
  let b₀ : ℝ := quarterLogLatticePoint (k + 1)
  let c₀ : ℝ := (a₀ + b₀) / 2
  let a₁ : ℝ := quarterLogLatticePoint (k + 5)
  let b₁ : ℝ := quarterLogLatticePoint (k + 6)
  let c₁ : ℝ := (a₁ + b₁) / 2
  have ha₀ : 0 < a₀ := quarterLogLatticePoint_pos k
  have hb₀ : 0 < b₀ := quarterLogLatticePoint_pos (k + 1)
  have ha₁ : 0 < a₁ := quarterLogLatticePoint_pos (k + 5)
  have hb₁ : 0 < b₁ := quarterLogLatticePoint_pos (k + 6)
  have hab₀ : a₀ < b₀ := quarterLogLatticePoint_strictMono (by omega)
  have hab₁ : a₁ < b₁ := quarterLogLatticePoint_strictMono (by omega)
  have hac₀ : a₀ < c₀ := by dsimp only [c₀]; linarith
  have hcb₀ : c₀ < b₀ := by dsimp only [c₀]; linarith
  have hac₁ : a₁ < c₁ := by dsimp only [c₁]; linarith
  have hcb₁ : c₁ < b₁ := by dsimp only [c₁]; linarith
  have hc₀ : 0 < c₀ := ha₀.trans hac₀
  have hU₀pos : Set.Ioo a₀ b₀ ⊆ Set.Ioi 0 := by
    intro x hx
    exact ha₀.trans hx.1
  have hU₁pos : Set.Ioo a₁ b₁ ⊆ Set.Ioi 0 := by
    intro x hx
    exact ha₁.trans hx.1
  obtain ⟨lower, hlowerOne, hlowerSupport, hlowerFixed, hlowerNonneg⟩ :=
    exists_nonnegative_bombieri_bump_at c₀ (Set.Ioo a₀ b₀)
      (Ioo_mem_nhds hac₀ hcb₀) hU₀pos
  obtain ⟨upper, hupperOne, hupperSupport, hupperFixed, hupperNonneg⟩ :=
    exists_nonnegative_bombieri_bump_at c₁ (Set.Ioo a₁ b₁)
      (Ioo_mem_nhds hac₁ hcb₁) hU₁pos
  let f : BombieriTest := monotoneQuarterCell lower k
  let g : BombieriTest := monotoneQuarterCell upper (k + 4)
  have hfSupport : tsupport f ⊆ Set.Icc a₀ b₀ := by
    change tsupport (fun x : ℝ ↦
      ((monotoneQuarterWeight k x : ℝ) : ℂ) * lower x) ⊆ _
    exact tsupport_mul_subset_right.trans
      (hlowerSupport.trans Set.Ioo_subset_Icc_self)
  have hgSupport : tsupport g ⊆ Set.Icc a₁ b₁ := by
    change tsupport (fun x : ℝ ↦
      ((monotoneQuarterWeight (k + 4) x : ℝ) : ℂ) * upper x) ⊆ _
    exact tsupport_mul_subset_right.trans
      (hupperSupport.trans Set.Ioo_subset_Icc_self)
  have hfNonneg : ∀ x, 0 ≤ (f x).re ∧ (f x).im = 0 :=
    monotoneQuarterCell_nonnegative_of_parent_nonnegative
      lower k hlowerNonneg
  have hgNonneg : ∀ x, 0 ≤ (g x).re ∧ (g x).im = 0 :=
    monotoneQuarterCell_nonnegative_of_parent_nonnegative
      upper (k + 4) hupperNonneg
  have hfc : 0 < (f c₀).re := by
    dsimp only [f]
    exact monotoneQuarterCell_re_pos_at_first_transition
      lower k (by simpa only [a₀, b₀] using ⟨hac₀, hcb₀⟩) hlowerOne
  have hgc : 0 < (g c₁).re := by
    dsimp only [g]
    rw [monotoneQuarterCell_apply, hupperOne]
    simpa only [mul_one, Complex.ofReal_re] using
      monotoneQuarterWeight_pos_on_second_transition (k + 4) (by
        simpa only [a₁, b₁,
          show k + 4 + 1 = k + 5 by ring,
          show k + 4 + 2 = k + 6 by ring] using ⟨hac₁, hcb₁⟩)
  have ha₁_div_b₀ : a₁ / b₀ = 2 := by
    dsimp only [a₁, b₀]
    rw [show k + 5 = (k + 1) + 4 by ring,
      quarterLogLatticePoint_add_four]
    field_simp [(quarterLogLatticePoint_pos (k + 1)).ne']
  have hxLower : a₁ / b₀ < c₁ / c₀ := by
    rw [ha₁_div_b₀]
    apply (lt_div_iff₀ hc₀).2
    have hc₀b : 2 * c₀ < 2 * b₀ :=
      mul_lt_mul_of_pos_left hcb₀ (by norm_num)
    have hscale : 2 * b₀ = a₁ := by
      dsimp only [a₁, b₀]
      rw [show k + 5 = (k + 1) + 4 by ring,
        quarterLogLatticePoint_add_four]
    linarith
  have hxUpper : c₁ / c₀ < b₁ / a₀ := by
    apply (div_lt_div_iff₀ hc₀ ha₀).2
    have hleft : c₁ * a₀ < b₁ * a₀ :=
      mul_lt_mul_of_pos_right hcb₁ ha₀
    have hright : b₁ * a₀ < b₁ * c₀ :=
      mul_lt_mul_of_pos_left hac₀ hb₁
    linarith
  have hpositive : 0 < (bombieriLocalCriticalForm g f).re := by
    apply bombieriLocalCriticalForm_re_pos_of_nonnegative_factorTwoSeparated
      g f (af := a₁) (bf := b₁) (ag := a₀) (bg := b₀)
      (cf := c₁) (cg := c₀) ha₁ ha₀ hb₀ hc₀ hgSupport hfSupport
    · rw [ha₁_div_b₀]
    · exact ⟨hxLower, hxUpper⟩
    · exact hgNonneg
    · exact hfNonneg
    · exact hgc
    · exact hfc
  have hpositiveSwap : 0 < (bombieriLocalCriticalForm f g).re := by
    have hswap := congrArg Complex.re
      (bombieriLocalCriticalForm_conj_apply g f)
    simp only [Complex.star_def, Complex.conj_re] at hswap
    rw [hswap]
    exact hpositive
  have hupperLeft : monotoneQuarterCell upper k = 0 := by
    apply fiveCell_cell_eq_zero_of_tsupport_above upper k
    intro x hx
    exact (quarterLogLatticePoint_mono (m := k + 2) (n := k + 5)
      (by omega)).trans (hupperSupport hx).1.le
  have hlowerRight : monotoneQuarterCell lower (k + 4) = 0 := by
    apply fiveCell_cell_eq_zero_of_tsupport_below lower (k + 4)
    intro x hx
    exact (hlowerSupport hx).2.le.trans
      (quarterLogLatticePoint_mono (by omega))
  have hmiddleLower :=
    fiveCellMiddleThree_eq_zero_of_tsupport_below lower k (by
      intro x hx
      exact (hlowerSupport hx).2.le)
  have hmiddleUpper :=
    fiveCellMiddleThree_eq_zero_of_tsupport_above upper k (by
      intro x hx
      exact (hupperSupport hx).1.le)
  let parent : BombieriTest := lower - upper
  have hparentFixed : bombieriConjugateTest parent = parent := by
    dsimp only [parent]
    exact conjugate_fixed_sub hlowerFixed hupperFixed
  have hmiddle :
      _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellMiddleThree
        parent k = 0 := by
    dsimp only [parent]
    rw [sub_eq_add_neg, fiveCellMiddleThree_add,
      fiveCellMiddleThree_neg, hmiddleLower, hmiddleUpper]
    simp
  have hnegCell (j : ℤ) :
      monotoneQuarterCell (-upper) j = -monotoneQuarterCell upper j := by
    simpa only [neg_smul, one_smul] using
      monotoneQuarterCell_smul (-1 : ℂ) upper j
  have hparentLeft : monotoneQuarterCell parent k = f := by
    dsimp only [parent]
    rw [sub_eq_add_neg, monotoneQuarterCell_add, hnegCell,
      hupperLeft, neg_zero, add_zero]
  have hparentRight : monotoneQuarterCell parent (k + 4) = -g := by
    dsimp only [parent]
    rw [sub_eq_add_neg, monotoneQuarterCell_add, hnegCell,
      hlowerRight, zero_add]
  refine ⟨parent, hparentFixed, hmiddle, ?_⟩
  rw [hparentLeft, hparentRight, map_neg]
  simp only [Complex.neg_re]
  linarith

/-- A zero middle-three block annihilates the only factor-two prime atom of
the sparse endpoint pair.  The possible common-parent value at the shared
lattice boundary is a singleton and therefore does not contribute to the
integral. -/
theorem fiveCell_remoteEndpointCross_eq_zero_of_middle_zero
    (parent : BombieriTest) (k : ℤ)
    (hmiddle :
      _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellMiddleThree
        parent k = 0) :
    bombieriQuadraticCrossTest
        (monotoneQuarterCell parent k)
        (monotoneQuarterCell parent (k + 4)) 2 = 0 := by
  rw [fiveCell_remoteEndpointCross_eq_squareMaskIntegral]
  have hzero :
      ∀ᵐ x : ℝ ∂volume.restrict (Set.Ioi 0),
        ((monotoneQuarterWeight k x ^ 2 : ℝ) : ℂ) *
            parent (2 * x) * starRingEnd ℂ (parent x) = 0 := by
    filter_upwards [
        (show ∀ᵐ x : ℝ ∂volume,
            x ≠ quarterLogLatticePoint (k + 1) by
          simp [ae_iff, measure_singleton]).filter_mono
            (ae_mono Measure.restrict_le_self)] with x hxne
    by_cases hxBoundary : x < quarterLogLatticePoint (k + 1)
    · by_cases hxSupport : x ≤ quarterLogLatticePoint k
      · rw [monotoneQuarterWeight_eq_zero_of_le k hxSupport]
        simp
      · have hparentTwo : parent (2 * x) = 0 :=
          parent_two_mul_eq_zero_of_middle_zero_of_left
            parent k hmiddle (lt_of_not_ge hxSupport) hxBoundary
        rw [hparentTwo]
        ring
    · have hxBoundary' : quarterLogLatticePoint (k + 1) < x :=
        lt_of_le_of_ne (le_of_not_gt hxBoundary) (Ne.symm hxne)
      by_cases hxSupport : quarterLogLatticePoint (k + 2) ≤ x
      · rw [monotoneQuarterWeight_eq_zero_of_le_left k hxSupport]
        simp
      · have hparent : parent x = 0 :=
          parent_eq_zero_of_middle_zero_of_right
            parent k hmiddle hxBoundary' (lt_of_not_ge hxSupport)
        rw [hparent]
        simp
  simpa only [integral_zero] using (integral_congr_ae hzero)

/-- Consequently the sparse endpoint pair has no arithmetic prime cost at
all; its exact Bombieri value is the purely local critical quadratic. -/
theorem bombieriFunctional_remoteEndpointPair_re_eq_local_of_middle_zero
    (parent : BombieriTest) (k : ℤ)
    (hmiddle :
      _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellMiddleThree
        parent k = 0) :
    (bombieriFunctional (bombieriQuadraticTest
      (monotoneQuarterCell parent k +
        monotoneQuarterCell parent (k + 4)))).re =
      (bombieriLocalCriticalForm
        (monotoneQuarterCell parent k)
        (monotoneQuarterCell parent k)).re +
      (bombieriLocalCriticalForm
        (monotoneQuarterCell parent (k + 4))
        (monotoneQuarterCell parent (k + 4))).re +
      2 * (bombieriLocalCriticalForm
        (monotoneQuarterCell parent k)
        (monotoneQuarterCell parent (k + 4))).re := by
  rw [bombieriFunctional_remoteEndpointPair_re_eq_localEnergyBalance,
    fiveCell_remoteEndpointCross_eq_zero_of_middle_zero parent k hmiddle]
  simp

/-- With a zero middle block, the sparse endpoint production value is exactly
the diagonal of the local critical form on the endpoint sum.  This identity
does not replace that signed local form by the physical logarithmic energy;
any nonnegativity argument must still provide the corresponding local
coercivity. -/
theorem bombieriFunctional_remoteEndpointPair_re_eq_localCriticalForm_self_of_middle_zero
    (parent : BombieriTest) (k : ℤ)
    (hmiddle :
      _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.fiveCellMiddleThree
        parent k = 0) :
    (bombieriFunctional (bombieriQuadraticTest
      (monotoneQuarterCell parent k +
        monotoneQuarterCell parent (k + 4)))).re =
      (bombieriLocalCriticalForm
        (monotoneQuarterCell parent k +
          monotoneQuarterCell parent (k + 4))
        (monotoneQuarterCell parent k +
          monotoneQuarterCell parent (k + 4))).re := by
  rw [bombieriFunctional_remoteEndpointPair_re_eq_local_of_middle_zero
      parent k hmiddle,
    bombieriLocalCriticalForm_add_self_re]

/-- Exact scalar form of the new common-parent obstruction.  Once the two
adjacent minors are nonnegative and the middle diagonal is positive, a
minimal negative configuration must strictly reverse the residual
middle-pivot contraction. -/
theorem _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.FiveCellCoupledEndpointSchurConstraints.middlePivotResidual_reversed
    {A M E U V X : ℝ}
    (h : _root_.ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural.FiveCellCoupledEndpointSchurConstraints A M E U V X)
    (hMpos : 0 < M)
    (hAM : U ^ 2 ≤ A * M)
    (hME : V ^ 2 ≤ M * E) :
    (A * M - U ^ 2) * (M * E - V ^ 2) <
      (M * X - U * V) ^ 2 := by
  exact middlePivotResidual_reversed_of_constraints h hMpos hAM hME

end

end ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellCommonParentDeterminantStructural

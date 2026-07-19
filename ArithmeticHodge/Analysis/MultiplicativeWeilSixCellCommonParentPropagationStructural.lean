import ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellCommonParentDeterminantStructural

set_option autoImplicit false

open Complex Real

namespace ArithmeticHodge.Analysis.MultiplicativeWeilSixCellCommonParentPropagationStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilAllLengthEndpointReserveStructural
open MultiplicativeWeilFiveCellCommonParentDeterminantStructural
open MultiplicativeWeilFiveCellMinimalBlockReserveStructural
open MultiplicativeWeilMinimalBlockEndpointEliminationStructural
open MultiplicativeWeilMinimalNegativeBlockStructural
open MultiplicativeWeilMonotoneCutChebyshevFrontierStructural
open MultiplicativeWeilMonotoneFourCellPrimeGeometryStructural
open MultiplicativeWeilMonotoneQuarterPartitionStructural
open MultiplicativeWeilQuarterLogLatticePartitionStructural
open MultiplicativeWeilRealMonotonePropagationCriterionStructural
open MultiplicativeWeilRealMonotoneTailConeCriterionStructural

/-!
# The first six-cell common-parent propagation reduction

Write six consecutive cells as a left endpoint `a`, the middle four-cell
block `m`, and a right endpoint `e`.  Universal five-cell positivity controls
every real pencil on `(a,m)` and `(m,e)`: each pencil is itself an honest
five-cell block of a modified common parent.  Hence the two adjacent
principal minors are not new at length six.

If the middle diagonal is positive, negativity of the six-cell block must
therefore strictly reverse the single middle-pivot contraction

`(M X - U V)^2 <= (A M - U^2) (M E - V^2)`.

If the middle diagonal vanishes, both adjacent crosses vanish and the only
remaining obstruction is the sparse endpoint pair.  Thus this file gives a
lossless local reduction after four- and five-cell positivity; it assumes no
all-length contraction and assigns no unjustified sign to the lag-five
corrected-Chebyshev corner `X`.
-/

/-- Six consecutive cells of one common monotone parent. -/
def monotoneQuarterSixBlock
    (parent : BombieriTest) (k : ℤ) : BombieriTest :=
  monotoneQuarterFiniteBlock parent k 0 6

/-- The four cells between the endpoints of a six-cell block. -/
def sixCellMiddleFour
    (parent : BombieriTest) (k : ℤ) : BombieriTest :=
  monotoneQuarterFourBlock parent (k + 1)

/-- Universal nonnegativity of the actual real five-cell production family. -/
def RealFiveCellProductionNonnegative : Prop :=
  ∀ parent : BombieriTest,
    bombieriConjugateTest parent = parent →
      ∀ k : ℤ,
        0 ≤ bombieriRealQuadraticValue (monotoneQuarterFiveBlock parent k)

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

private theorem sixCell_leftFiveBlock_eq_endpoint_add_middle
    (parent : BombieriTest) (k : ℤ) :
    monotoneQuarterFiveBlock parent k =
      monotoneQuarterCell parent k + sixCellMiddleFour parent k := by
  classical
  simp [monotoneQuarterFiveBlock, sixCellMiddleFour,
    monotoneQuarterFourBlock, monotoneQuarterFiniteBlock,
    Finset.sum_range_succ]
  rw [show k + 1 + 1 = k + 2 by ring,
    show k + 1 + 2 = k + 3 by ring,
    show k + 1 + 3 = k + 4 by ring]
  module

private theorem sixCell_rightFiveBlock_eq_middle_add_endpoint
    (parent : BombieriTest) (k : ℤ) :
    monotoneQuarterFiveBlock parent (k + 1) =
      sixCellMiddleFour parent k + monotoneQuarterCell parent (k + 5) := by
  classical
  simp [monotoneQuarterFiveBlock, sixCellMiddleFour,
    monotoneQuarterFourBlock, monotoneQuarterFiniteBlock,
    Finset.sum_range_succ]
  congr 1
  ring

/-- Removing the next cutoff makes a five-cell block equal to its left
endpoint cell. -/
theorem fiveBlock_parent_sub_nextCutoff_eq_leftEndpoint
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

/-- Cutting at the right endpoint makes the shifted five-cell block equal to
that endpoint cell. -/
theorem fiveBlock_rightCutoff_eq_rightEndpoint
    (parent : BombieriTest) (k : ℤ) :
    monotoneQuarterFiveBlock
        (monotoneQuarterCutoff parent (k + 5)) (k + 1) =
      monotoneQuarterCell parent (k + 5) := by
  apply TestFunction.ext
  intro x
  rw [monotoneQuarterFiveBlock_apply, monotoneQuarterCell_apply]
  simp only [monotoneQuarterCutoff_apply]
  have h15 := monotoneQuarterStep_mul_later
    (k := k + 1) (j := k + 5) (by omega) x
  have h56 := monotoneQuarterStep_mul_later
    (k := k + 5) (j := k + 6) (by omega) x
  have hindex : k + 1 + 5 = k + 6 := by ring
  have hmask :
      (monotoneQuarterStep (k + 1) x - monotoneQuarterStep (k + 6) x) *
          monotoneQuarterStep (k + 5) x =
        monotoneQuarterWeight (k + 5) x := by
    unfold monotoneQuarterWeight
    rw [show k + 5 + 1 = k + 6 by ring]
    nlinarith [h15, h56]
  rw [hindex]
  change
    (↑(monotoneQuarterStep (k + 1) x - monotoneQuarterStep (k + 6) x) : ℂ) *
        (↑(monotoneQuarterStep (k + 5) x) * parent x) =
      (monotoneQuarterWeight (k + 5) x : ℂ) * parent x
  calc
    (↑(monotoneQuarterStep (k + 1) x - monotoneQuarterStep (k + 6) x) : ℂ) *
          (↑(monotoneQuarterStep (k + 5) x) * parent x) =
        (↑((monotoneQuarterStep (k + 1) x -
          monotoneQuarterStep (k + 6) x) *
            monotoneQuarterStep (k + 5) x) : ℂ) * parent x := by
      push_cast
      ring
    _ = (monotoneQuarterWeight (k + 5) x : ℂ) * parent x := by rw [hmask]

/-- Every real pencil on the left endpoint and middle four cells is an
actual five-cell production block of a modified common parent. -/
theorem exists_realParent_fiveBlock_eq_leftEndpoint_add_smul_middle
    (parent : BombieriTest)
    (hparent : bombieriConjugateTest parent = parent)
    (k : ℤ) (t : ℝ) :
    ∃ modified : BombieriTest,
      bombieriConjugateTest modified = modified ∧
        monotoneQuarterFiveBlock modified k =
          monotoneQuarterCell parent k +
            (t : ℂ) • sixCellMiddleFour parent k := by
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
    rw [monotoneQuarterFiveBlock_add,
      monotoneQuarterFiveBlock_smul,
      monotoneQuarterFiveBlock_smul,
      sixCell_leftFiveBlock_eq_endpoint_add_middle,
      show monotoneQuarterFiveBlock endpointParent k =
          monotoneQuarterCell parent k by
        exact fiveBlock_parent_sub_nextCutoff_eq_leftEndpoint parent k]
    module

/-- Every real pencil on the middle four cells and right endpoint is an
actual shifted five-cell production block of a modified common parent. -/
theorem exists_realParent_fiveBlock_eq_middle_add_smul_rightEndpoint
    (parent : BombieriTest)
    (hparent : bombieriConjugateTest parent = parent)
    (k : ℤ) (t : ℝ) :
    ∃ modified : BombieriTest,
      bombieriConjugateTest modified = modified ∧
        monotoneQuarterFiveBlock modified (k + 1) =
          sixCellMiddleFour parent k +
            (t : ℂ) • monotoneQuarterCell parent (k + 5) := by
  let endpointParent : BombieriTest :=
    monotoneQuarterCutoff parent (k + 5)
  let modified : BombieriTest :=
    parent + ((t - 1 : ℝ) : ℂ) • endpointParent
  have hendpoint : bombieriConjugateTest endpointParent = endpointParent := by
    dsimp only [endpointParent]
    exact conjugate_fixed_monotoneQuarterCutoff hparent (k + 5)
  refine ⟨modified, ?_, ?_⟩
  · dsimp only [modified]
    rw [bombieriConjugateTest_add, hparent,
      conjugate_fixed_real_smul hendpoint (t - 1)]
  · dsimp only [modified]
    rw [monotoneQuarterFiveBlock_add,
      monotoneQuarterFiveBlock_smul,
      sixCell_rightFiveBlock_eq_middle_add_endpoint,
      show monotoneQuarterFiveBlock endpointParent (k + 1) =
          monotoneQuarterCell parent (k + 5) by
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

/-- Universal five-cell positivity supplies both adjacent principal minors
of the actual six-cell common-parent matrix. -/
theorem sixCell_adjacentPrincipalMinors_of_fiveCellProduction
    (hfour : RealFourCellProductionNonnegative)
    (hfive : RealFiveCellProductionNonnegative)
    (parent : BombieriTest)
    (hparent : bombieriConjugateTest parent = parent) (k : ℤ) :
    let a := monotoneQuarterCell parent k
    let m := sixCellMiddleFour parent k
    let e := monotoneQuarterCell parent (k + 5)
    let A := bombieriRealQuadraticValue a
    let M := bombieriRealQuadraticValue m
    let E := bombieriRealQuadraticValue e
    let U := (bombieriTwoBlockGlobalCrossSymbol a m).re
    let V := (bombieriTwoBlockGlobalCrossSymbol m e).re
    U ^ 2 ≤ A * M ∧ V ^ 2 ≤ M * E := by
  dsimp only
  let a : BombieriTest := monotoneQuarterCell parent k
  let m : BombieriTest := sixCellMiddleFour parent k
  let e : BombieriTest := monotoneQuarterCell parent (k + 5)
  have hM : 0 ≤ bombieriRealQuadraticValue m := by
    dsimp only [m, sixCellMiddleFour]
    exact hfour parent hparent (k + 1)
  have hE : 0 ≤ bombieriRealQuadraticValue e :=
    bombieriFunctional_quadratic_re_nonneg_of_ratioTwoCell e
      (monotoneQuarterCell_ratioTwo parent (k + 5))
  constructor
  · apply real_two_by_two_determinant_of_all_nonnegative hM
    intro t
    obtain ⟨modified, hmodified, hblock⟩ :=
      exists_realParent_fiveBlock_eq_leftEndpoint_add_smul_middle
        parent hparent k t
    rw [← bombieriRealQuadraticValue_add_real_smul, ← hblock]
    exact hfive modified hmodified k
  · apply real_two_by_two_determinant_of_all_nonnegative hE
    intro t
    obtain ⟨modified, hmodified, hblock⟩ :=
      exists_realParent_fiveBlock_eq_middle_add_smul_rightEndpoint
        parent hparent k t
    rw [← bombieriRealQuadraticValue_add_real_smul, ← hblock]
    exact hfive modified hmodified (k + 1)

/-- The remote endpoint corner at length six is exactly the lag-five
corrected-Chebyshev contribution. -/
theorem sixCell_remoteEndpointCross_re_eq_farChebyshev
    (parent : BombieriTest) (k : ℤ) :
    (bombieriTwoBlockGlobalCrossSymbol
        (monotoneQuarterCell parent k)
        (monotoneQuarterCell parent (k + 5))).re =
      monotoneQuarterFarChebyshevContribution parent k 5 := by
  exact monotoneQuarterCell_far_globalCross_re_eq_contribution
    parent k 5 (by omega)

/-- The exact three-block determinant on endpoint, middle four cells, and
endpoint. -/
def sixCellCommonParentThreeBlockDeterminant
    (parent : BombieriTest) (k : ℤ) : ℝ :=
  let a := monotoneQuarterCell parent k
  let m := sixCellMiddleFour parent k
  let e := monotoneQuarterCell parent (k + 5)
  fiveCellThreeBlockDeterminant
    (bombieriRealQuadraticValue a)
    (bombieriRealQuadraticValue m)
    (bombieriRealQuadraticValue e)
    ((bombieriTwoBlockGlobalCrossSymbol a m).re)
    ((bombieriTwoBlockGlobalCrossSymbol m e).re)
    ((bombieriTwoBlockGlobalCrossSymbol a e).re)

/-- The one nondegenerate length-six contraction left after five-cell
positivity has supplied the adjacent principal minors. -/
def SixCellCommonParentMiddlePivotResidualContraction
    (parent : BombieriTest) (k : ℤ) : Prop :=
  let a := monotoneQuarterCell parent k
  let m := sixCellMiddleFour parent k
  let e := monotoneQuarterCell parent (k + 5)
  let A := bombieriRealQuadraticValue a
  let M := bombieriRealQuadraticValue m
  let E := bombieriRealQuadraticValue e
  let U := (bombieriTwoBlockGlobalCrossSymbol a m).re
  let V := (bombieriTwoBlockGlobalCrossSymbol m e).re
  let X := monotoneQuarterFarChebyshevContribution parent k 5
  (M * X - U * V) ^ 2 ≤
    (A * M - U ^ 2) * (M * E - V ^ 2)

private theorem monotoneQuarterSixBlock_eq_threeBlocks
    (parent : BombieriTest) (k : ℤ) :
    monotoneQuarterSixBlock parent k =
      (monotoneQuarterCell parent k + sixCellMiddleFour parent k) +
        monotoneQuarterCell parent (k + 5) := by
  classical
  simp [monotoneQuarterSixBlock, sixCellMiddleFour,
    monotoneQuarterFourBlock, monotoneQuarterFiniteBlock,
    Finset.sum_range_succ]
  rw [show k + 1 + 1 = k + 2 by ring,
    show k + 1 + 2 = k + 3 by ring,
    show k + 1 + 3 = k + 4 by ring]
  module

/-- Lossless scalar expansion of the complete six-cell quadratic. -/
theorem bombieriRealQuadraticValue_sixBlock_eq_threeBlock
    (parent : BombieriTest) (k : ℤ) :
    let a := monotoneQuarterCell parent k
    let m := sixCellMiddleFour parent k
    let e := monotoneQuarterCell parent (k + 5)
    let A := bombieriRealQuadraticValue a
    let M := bombieriRealQuadraticValue m
    let E := bombieriRealQuadraticValue e
    let U := (bombieriTwoBlockGlobalCrossSymbol a m).re
    let V := (bombieriTwoBlockGlobalCrossSymbol m e).re
    let X := monotoneQuarterFarChebyshevContribution parent k 5
    bombieriRealQuadraticValue (monotoneQuarterSixBlock parent k) =
      A + M + E + 2 * (U + V + X) := by
  dsimp only
  rw [monotoneQuarterSixBlock_eq_threeBlocks,
    bombieriRealQuadraticValue_add, bombieriRealQuadraticValue_add,
    bombieriTwoBlockGlobalCrossSymbol_add_left, Complex.add_re,
    sixCell_remoteEndpointCross_re_eq_farChebyshev]
  ring

private theorem threeBlockQuadratic_nonnegative_of_middlePivot
    {A M E U V X : ℝ}
    (hMpos : 0 < M)
    (hAM : U ^ 2 ≤ A * M)
    (hME : V ^ 2 ≤ M * E)
    (hresidual :
      (M * X - U * V) ^ 2 ≤
        (A * M - U ^ 2) * (M * E - V ^ 2)) :
    0 ≤ A + M + E + 2 * (U + V + X) := by
  let alpha : ℝ := A * M - U ^ 2
  let beta : ℝ := M * E - V ^ 2
  let delta : ℝ := M * X - U * V
  have halpha : 0 ≤ alpha := by
    dsimp only [alpha]
    linarith
  have hbeta : 0 ≤ beta := by
    dsimp only [beta]
    linarith
  have hdelta : delta ^ 2 ≤ alpha * beta := by
    simpa only [alpha, beta, delta] using hresidual
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
  exact (mul_nonneg_iff_of_pos_left hMpos).mp hscaled

/-- Exact six-cell propagation after four- and five-cell positivity.  In the
nondegenerate case the middle-pivot contraction is sufficient.  The sole
degenerate obligation is nonnegativity of the sparse endpoint pair. -/
theorem bombieriRealQuadraticValue_sixBlock_nonnegative_of_middlePivot
    (hfour : RealFourCellProductionNonnegative)
    (hfive : RealFiveCellProductionNonnegative)
    (parent : BombieriTest)
    (hparent : bombieriConjugateTest parent = parent) (k : ℤ)
    (hdegenerate :
      bombieriRealQuadraticValue (sixCellMiddleFour parent k) = 0 →
        0 ≤ bombieriRealQuadraticValue
          (monotoneQuarterCell parent k +
            monotoneQuarterCell parent (k + 5)))
    (hresidual : SixCellCommonParentMiddlePivotResidualContraction parent k) :
    0 ≤ bombieriRealQuadraticValue (monotoneQuarterSixBlock parent k) := by
  let a : BombieriTest := monotoneQuarterCell parent k
  let m : BombieriTest := sixCellMiddleFour parent k
  let e : BombieriTest := monotoneQuarterCell parent (k + 5)
  let A : ℝ := bombieriRealQuadraticValue a
  let M : ℝ := bombieriRealQuadraticValue m
  let E : ℝ := bombieriRealQuadraticValue e
  let U : ℝ := (bombieriTwoBlockGlobalCrossSymbol a m).re
  let V : ℝ := (bombieriTwoBlockGlobalCrossSymbol m e).re
  let X : ℝ := monotoneQuarterFarChebyshevContribution parent k 5
  have hadj := sixCell_adjacentPrincipalMinors_of_fiveCellProduction
    hfour hfive parent hparent k
  change U ^ 2 ≤ A * M ∧ V ^ 2 ≤ M * E at hadj
  have hM : 0 ≤ M := by
    dsimp only [M, m, sixCellMiddleFour]
    exact hfour parent hparent (k + 1)
  have hvalue := bombieriRealQuadraticValue_sixBlock_eq_threeBlock parent k
  change bombieriRealQuadraticValue (monotoneQuarterSixBlock parent k) =
    A + M + E + 2 * (U + V + X) at hvalue
  rw [hvalue]
  by_cases hMzero : M = 0
  · have hU : U = 0 := by
      rw [hMzero, mul_zero] at hadj
      nlinarith [sq_nonneg U]
    have hV : V = 0 := by
      rw [hMzero, zero_mul] at hadj
      nlinarith [sq_nonneg V]
    have hpair := hdegenerate (by simpa only [M, m] using hMzero)
    rw [bombieriRealQuadraticValue_add] at hpair
    have hXcross : (bombieriTwoBlockGlobalCrossSymbol a e).re = X := by
      dsimp only [a, e, X]
      exact sixCell_remoteEndpointCross_re_eq_farChebyshev parent k
    rw [hXcross] at hpair
    rw [hMzero, hU, hV]
    linarith
  · have hMpos : 0 < M := lt_of_le_of_ne hM (Ne.symm hMzero)
    have hres :
        (M * X - U * V) ^ 2 ≤
          (A * M - U ^ 2) * (M * E - V ^ 2) := by
      simpa only [SixCellCommonParentMiddlePivotResidualContraction,
        a, m, e, A, M, E, U, V, X] using hresidual
    exact threeBlockQuadratic_nonnegative_of_middlePivot
      hMpos hadj.1 hadj.2 hres

/-- Sharp obstruction form: after four- and five-cell positivity, every
negative six-cell common-parent block either has a zero middle diagonal and a
negative sparse endpoint pair, or strictly reverses the one residual
middle-pivot contraction. -/
theorem negative_sixBlock_forces_degenerateEndpoint_or_middlePivotReversal
    (hfour : RealFourCellProductionNonnegative)
    (hfive : RealFiveCellProductionNonnegative)
    (parent : BombieriTest)
    (hparent : bombieriConjugateTest parent = parent) (k : ℤ)
    (hnegative :
      bombieriRealQuadraticValue (monotoneQuarterSixBlock parent k) < 0) :
    let a := monotoneQuarterCell parent k
    let m := sixCellMiddleFour parent k
    let e := monotoneQuarterCell parent (k + 5)
    let A := bombieriRealQuadraticValue a
    let M := bombieriRealQuadraticValue m
    let E := bombieriRealQuadraticValue e
    let U := (bombieriTwoBlockGlobalCrossSymbol a m).re
    let V := (bombieriTwoBlockGlobalCrossSymbol m e).re
    let X := monotoneQuarterFarChebyshevContribution parent k 5
    (M = 0 ∧ bombieriRealQuadraticValue (a + e) < 0) ∨
      (A * M - U ^ 2) * (M * E - V ^ 2) <
        (M * X - U * V) ^ 2 := by
  dsimp only
  let a : BombieriTest := monotoneQuarterCell parent k
  let m : BombieriTest := sixCellMiddleFour parent k
  let e : BombieriTest := monotoneQuarterCell parent (k + 5)
  let A : ℝ := bombieriRealQuadraticValue a
  let M : ℝ := bombieriRealQuadraticValue m
  let E : ℝ := bombieriRealQuadraticValue e
  let U : ℝ := (bombieriTwoBlockGlobalCrossSymbol a m).re
  let V : ℝ := (bombieriTwoBlockGlobalCrossSymbol m e).re
  let X : ℝ := monotoneQuarterFarChebyshevContribution parent k 5
  have hadj := sixCell_adjacentPrincipalMinors_of_fiveCellProduction
    hfour hfive parent hparent k
  change U ^ 2 ≤ A * M ∧ V ^ 2 ≤ M * E at hadj
  have hM : 0 ≤ M := by
    dsimp only [M, m, sixCellMiddleFour]
    exact hfour parent hparent (k + 1)
  have hvalue := bombieriRealQuadraticValue_sixBlock_eq_threeBlock parent k
  change bombieriRealQuadraticValue (monotoneQuarterSixBlock parent k) =
    A + M + E + 2 * (U + V + X) at hvalue
  have hwhole : A + M + E + 2 * (U + V + X) < 0 := by
    rw [← hvalue]
    exact hnegative
  by_cases hMzero : M = 0
  · left
    refine ⟨hMzero, ?_⟩
    have hU : U = 0 := by
      rw [hMzero, mul_zero] at hadj
      nlinarith [sq_nonneg U]
    have hV : V = 0 := by
      rw [hMzero, zero_mul] at hadj
      nlinarith [sq_nonneg V]
    rw [bombieriRealQuadraticValue_add]
    have hXcross : (bombieriTwoBlockGlobalCrossSymbol a e).re = X := by
      dsimp only [a, e, X]
      exact sixCell_remoteEndpointCross_re_eq_farChebyshev parent k
    rw [hXcross]
    rw [hMzero, hU, hV] at hwhole
    linarith
  · right
    have hMpos : 0 < M := lt_of_le_of_ne hM (Ne.symm hMzero)
    by_contra hnot
    have hres :
        (M * X - U * V) ^ 2 ≤
          (A * M - U ^ 2) * (M * E - V ^ 2) := le_of_not_gt hnot
    have hnonnegative := threeBlockQuadratic_nonnegative_of_middlePivot
      hMpos hadj.1 hadj.2 hres
    exact (not_lt_of_ge hnonnegative) hwhole

private theorem monotoneQuarterFiniteBlock_length_six_eq_sixBlock
    (parent : BombieriTest) (lo : ℤ) (start : ℕ) :
    monotoneQuarterFiniteBlock parent lo start 6 =
      monotoneQuarterSixBlock parent
        (monotoneQuarterFiniteBlockBase lo start) := by
  classical
  unfold monotoneQuarterSixBlock monotoneQuarterFiniteBlock
    monotoneQuarterFiniteBlockBase
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  push_cast
  ring

/-- A support-minimal negative block of length six exhibits exactly the same
local dichotomy.  Thus, once lengths four and five are closed, excluding
minimal length six requires the lag-five middle-pivot contraction together
with its zero-middle sparse-endpoint case; overlap nonnegativity alone does
not propagate. -/
theorem supportMinimalNegativeMonotoneBlock_length_six_forces_obstruction
    (hfour : RealFourCellProductionNonnegative)
    (hfive : RealFiveCellProductionNonnegative)
    {parent : BombieriTest} {lo : ℤ} {N start len : ℕ}
    (hparent : bombieriConjugateTest parent = parent)
    (hmin : IsSupportMinimalNegativeMonotoneBlock
      parent lo N start len) (hlen : len = 6) :
    let k := monotoneQuarterFiniteBlockBase lo start
    let a := monotoneQuarterCell parent k
    let m := sixCellMiddleFour parent k
    let e := monotoneQuarterCell parent (k + 5)
    let A := bombieriRealQuadraticValue a
    let M := bombieriRealQuadraticValue m
    let E := bombieriRealQuadraticValue e
    let U := (bombieriTwoBlockGlobalCrossSymbol a m).re
    let V := (bombieriTwoBlockGlobalCrossSymbol m e).re
    let X := monotoneQuarterFarChebyshevContribution parent k 5
    (M = 0 ∧ bombieriRealQuadraticValue (a + e) < 0) ∨
      (A * M - U ^ 2) * (M * E - V ^ 2) <
        (M * X - U * V) ^ 2 := by
  dsimp only
  let k : ℤ := monotoneQuarterFiniteBlockBase lo start
  have hnegative :
      bombieriRealQuadraticValue (monotoneQuarterSixBlock parent k) < 0 := by
    rw [← monotoneQuarterFiniteBlock_length_six_eq_sixBlock]
    simpa only [hlen] using hmin.negative
  exact negative_sixBlock_forces_degenerateEndpoint_or_middlePivotReversal
    hfour hfive parent hparent k hnegative

end

end ArithmeticHodge.Analysis.MultiplicativeWeilSixCellCommonParentPropagationStructural

import ArithmeticHodge.Analysis.MultiplicativeWeilAllLengthResidualPropagationClosureStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilAllLengthNegativeResidualStructural

set_option autoImplicit false

open Complex Real

namespace ArithmeticHodge.Analysis.MultiplicativeWeilAllLengthCommonParentResidualStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilAllLengthNegativeResidualStructural
open MultiplicativeWeilAllLengthResidualDeterminantSingularClosureStructural
open MultiplicativeWeilFiveCellResidualDeterminantClosureStructural
open MultiplicativeWeilFourCellResidualDeterminantStructural
open MultiplicativeWeilMinimalNegativeBlockStructural
open MultiplicativeWeilMonotoneNullSuffixVariationStructural
open MultiplicativeWeilMonotonePrimeAtomAggregateObstructionStructural
open MultiplicativeWeilMonotoneQuarterPartitionStructural
open MultiplicativeWeilRealCutPhaseReductionStructural
open MultiplicativeWeilRealMonotonePropagationCriterionStructural
open MultiplicativeWeilRealMonotoneTailConeCriterionStructural

/-!
# The actual common-parent residual pencil at every length

The abstract overlap countermodel does not remember that the endpoint and
interior tests are three masks of one Bombieri parent.  This file keeps that
structure.  It proves that the full pencil of the two middle-orthogonal
residuals is exactly one production block of a conjugation-fixed parent whose
mask is constant on the left endpoint, the whole interior, and the right
endpoint.

Consequently the all-length residual determinant is equivalent, under the
already available shorter-length production positivity, to nonnegativity of
this sharply specified one-parameter family.  This is the genuine
common-parent tail certificate; it cannot be replaced by positivity of the
two adjacent shorter windows alone.
-/

private theorem finiteBlock_add
    (f g : BombieriTest) (k : ℤ) (start len : ℕ) :
    monotoneQuarterFiniteBlock (f + g) k start len =
      monotoneQuarterFiniteBlock f k start len +
        monotoneQuarterFiniteBlock g k start len := by
  classical
  unfold monotoneQuarterFiniteBlock
  simp_rw [monotoneQuarterCell_add]
  exact Finset.sum_add_distrib

private theorem finiteBlock_smul
    (c : ℂ) (f : BombieriTest) (k : ℤ) (start len : ℕ) :
    monotoneQuarterFiniteBlock (c • f) k start len =
      c • monotoneQuarterFiniteBlock f k start len := by
  classical
  unfold monotoneQuarterFiniteBlock
  simp_rw [monotoneQuarterCell_smul]
  exact Finset.smul_sum.symm

private theorem finiteBlock_eq_cutoff_sub
    (parent : BombieriTest) (k : ℤ) (start len : ℕ) :
    monotoneQuarterFiniteBlock parent k start len =
      monotoneQuarterCutoff parent (k + (start : ℤ)) -
        monotoneQuarterCutoff parent (k + ((start + len : ℕ) : ℤ)) := by
  classical
  unfold monotoneQuarterFiniteBlock
  convert sum_range_monotoneQuarterCell_eq_cutoff_sub
    parent (k + (start : ℤ)) len using 1 <;> push_cast <;> ring_nf

private theorem cutoff_cutoff_eq_later_left
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

private theorem fullBlock_cutoff_leftBoundary_eq_suffix
    (parent : BombieriTest) (k : ℤ) (n : ℕ) (hn : 2 ≤ n) :
    monotoneQuarterFiniteBlock
        (monotoneQuarterCutoff parent (k + 1)) k 0 n =
      monotoneQuarterFiniteBlock parent k 1 (n - 1) := by
  rw [finiteBlock_eq_cutoff_sub, finiteBlock_eq_cutoff_sub]
  norm_num
  have hright : k + 1 < k + (n : ℤ) := by omega
  rw [cutoff_cutoff_eq_later_left parent (by omega),
    monotoneQuarterCutoff_cutoff_eq_later parent hright]
  congr 2
  omega

private theorem fullBlock_cutoff_rightBoundary_eq_endpoint
    (parent : BombieriTest) (k : ℤ) (n : ℕ) (hn : 2 ≤ n) :
    monotoneQuarterFiniteBlock
        (monotoneQuarterCutoff parent (k + ((n - 1 : ℕ) : ℤ))) k 0 n =
      monotoneQuarterCell parent (k + ((n - 1 : ℕ) : ℤ)) := by
  rw [finiteBlock_eq_cutoff_sub,
    monotoneQuarterCell_eq_cutoff_sub]
  norm_num
  have hleft : k < k + ((n - 1 : ℕ) : ℤ) := by omega
  have hright : k + ((n - 1 : ℕ) : ℤ) < k + (n : ℤ) := by omega
  rw [cutoff_cutoff_eq_later_left parent hleft,
    monotoneQuarterCutoff_cutoff_eq_later parent hright]
  congr 2
  omega

private theorem fullBlock_eq_threeRegions
    (parent : BombieriTest) (k : ℤ) (n : ℕ) (hn : 3 ≤ n) :
    monotoneQuarterFiniteBlock parent k 0 n =
      monotoneQuarterCell parent k +
        monotoneQuarterFiniteBlockInterior parent k n +
          monotoneQuarterCell parent (k + ((n - 1 : ℕ) : ℤ)) := by
  have hhead := monotoneQuarterFiniteBlock_eq_prefix_add_suffix
    parent k 0 n 1 (by omega)
  have htail := monotoneQuarterFiniteBlock_eq_prefix_add_suffix
    parent k 1 (n - 1) (n - 2) (by omega)
  have hsub : n - 1 - (n - 2) = 1 := by omega
  have hindex : 1 + (n - 2) = n - 1 := by omega
  rw [hsub, hindex] at htail
  rw [hhead, htail]
  unfold monotoneQuarterFiniteBlockInterior monotoneQuarterFiniteBlock
  simp
  abel

/-- The same parent with independent real coefficients on the left endpoint,
the complete interior, and the right endpoint of an `n`-cell block. -/
def finiteBlockThreeRegionRescaledParent
    (parent : BombieriTest) (k : ℤ) (n : ℕ)
    (x y z : ℝ) : BombieriTest :=
  (x : ℂ) • parent +
    ((y - x : ℝ) : ℂ) • monotoneQuarterCutoff parent (k + 1) +
      ((z - y : ℝ) : ℂ) •
        monotoneQuarterCutoff parent (k + ((n - 1 : ℕ) : ℤ))

private theorem conjugate_fixed_real_smul
    {f : BombieriTest} (hf : bombieriConjugateTest f = f) (c : ℝ) :
    bombieriConjugateTest ((c : ℂ) • f) = (c : ℂ) • f := by
  rw [bombieriConjugateTest_smul, Complex.conj_ofReal, hf]

theorem finiteBlockThreeRegionRescaledParent_conjugate_fixed
    (parent : BombieriTest)
    (hparent : bombieriConjugateTest parent = parent)
    (k : ℤ) (n : ℕ) (x y z : ℝ) :
    bombieriConjugateTest
        (finiteBlockThreeRegionRescaledParent parent k n x y z) =
      finiteBlockThreeRegionRescaledParent parent k n x y z := by
  unfold finiteBlockThreeRegionRescaledParent
  rw [bombieriConjugateTest_add, bombieriConjugateTest_add,
    conjugate_fixed_real_smul hparent x,
    conjugate_fixed_real_smul
      (bombieriConjugateTest_monotoneQuarterCutoff
        parent hparent (k + 1)) (y - x),
    conjugate_fixed_real_smul
      (bombieriConjugateTest_monotoneQuarterCutoff
        parent hparent (k + ((n - 1 : ℕ) : ℤ))) (z - y)]

/-- Exact all-length three-region realization.  This is where the genuine
common-parent constraint enters: the three tests are not arbitrary vectors,
but nested cutoff masks of one parent. -/
theorem finiteBlock_threeRegionRescaledParent_eq
    (parent : BombieriTest) (k : ℤ) (n : ℕ) (hn : 3 ≤ n)
    (x y z : ℝ) :
    monotoneQuarterFiniteBlock
        (finiteBlockThreeRegionRescaledParent parent k n x y z) k 0 n =
      (x : ℂ) • monotoneQuarterCell parent k +
        (y : ℂ) • monotoneQuarterFiniteBlockInterior parent k n +
          (z : ℂ) •
            monotoneQuarterCell parent (k + ((n - 1 : ℕ) : ℤ)) := by
  unfold finiteBlockThreeRegionRescaledParent
  rw [finiteBlock_add, finiteBlock_add,
    finiteBlock_smul, finiteBlock_smul, finiteBlock_smul,
    fullBlock_cutoff_leftBoundary_eq_suffix parent k n (by omega),
    fullBlock_cutoff_rightBoundary_eq_endpoint parent k n (by omega),
    fullBlock_eq_threeRegions parent k n hn]
  have hsuffix :
      monotoneQuarterFiniteBlock parent k 1 (n - 1) =
        monotoneQuarterFiniteBlockInterior parent k n +
          monotoneQuarterCell parent (k + ((n - 1 : ℕ) : ℤ)) := by
    have htail := monotoneQuarterFiniteBlock_eq_prefix_add_suffix
      parent k 1 (n - 1) (n - 2) (by omega)
    have hsub : n - 1 - (n - 2) = 1 := by omega
    have hindex : 1 + (n - 2) = n - 1 := by omega
    rw [hsub, hindex] at htail
    rw [htail]
    unfold monotoneQuarterFiniteBlockInterior monotoneQuarterFiniteBlock
    simp
  rw [hsuffix]
  module

/-- The modified parent whose production block is the pencil `left + t right`
of the two actual middle-orthogonal residuals. -/
def finiteBlockMiddleOrthogonalResidualPencilParent
    (parent : BombieriTest) (k : ℤ) (n : ℕ) (t : ℝ) : BombieriTest :=
  let a := monotoneQuarterCell parent k
  let m := monotoneQuarterFiniteBlockInterior parent k n
  let e := monotoneQuarterCell parent (k + ((n - 1 : ℕ) : ℤ))
  let M := bombieriRealQuadraticValue m
  let U := (bombieriTwoBlockGlobalCrossSymbol a m).re
  let V := (bombieriTwoBlockGlobalCrossSymbol m e).re
  finiteBlockThreeRegionRescaledParent parent k n M (-U - t * V) (t * M)

theorem finiteBlockMiddleOrthogonalResidualPencilParent_conjugate_fixed
    (parent : BombieriTest)
    (hparent : bombieriConjugateTest parent = parent)
    (k : ℤ) (n : ℕ) (t : ℝ) :
    bombieriConjugateTest
        (finiteBlockMiddleOrthogonalResidualPencilParent parent k n t) =
      finiteBlockMiddleOrthogonalResidualPencilParent parent k n t := by
  unfold finiteBlockMiddleOrthogonalResidualPencilParent
  exact finiteBlockThreeRegionRescaledParent_conjugate_fixed
    parent hparent k n _ _ _

/-- The residual pencil is not merely supported in the same long window: it
is exactly its production block for an explicit modified common parent. -/
theorem finiteBlock_residualPencil_eq
    (parent : BombieriTest) (k : ℤ) (n : ℕ) (hn : 3 ≤ n) (t : ℝ) :
    monotoneQuarterFiniteBlock
        (finiteBlockMiddleOrthogonalResidualPencilParent parent k n t)
        k 0 n =
      finiteBlockLeftMiddleOrthogonalResidual parent k n +
        (t : ℂ) • finiteBlockRightMiddleOrthogonalResidual parent k n := by
  unfold finiteBlockMiddleOrthogonalResidualPencilParent
  rw [finiteBlock_threeRegionRescaledParent_eq parent k n hn]
  unfold finiteBlockLeftMiddleOrthogonalResidual
    finiteBlockRightMiddleOrthogonalResidual
  push_cast
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

private theorem real_pencil_nonnegative_of_two_by_two_determinant
    {A B U : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hdet : U ^ 2 ≤ A * B) (t : ℝ) :
    0 ≤ A + t ^ 2 * B + 2 * t * U := by
  by_cases hBzero : B = 0
  · have hU : U = 0 := by
      rw [hBzero, mul_zero] at hdet
      nlinarith [sq_nonneg U]
    rw [hBzero, hU]
    simpa using hA
  · have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hBzero)
    have hidentity :
        B * (A + t ^ 2 * B + 2 * t * U) =
          (t * B + U) ^ 2 + (A * B - U ^ 2) := by ring
    have hscaled : 0 ≤ B * (A + t ^ 2 * B + 2 * t * U) := by
      rw [hidentity]
      nlinarith [sq_nonneg (t * B + U)]
    exact (mul_nonneg_iff_of_pos_left hBpos).mp hscaled

/-- The sharply delimited actual-kernel certificate left at one length.  It
asks for positivity only on the explicit residual pencil of one common
parent, not on arbitrary pairs of tests and not on arbitrary overlap data. -/
def RealFiniteBlockCommonParentResidualPencilNonnegativeAtLength
    (n : ℕ) : Prop :=
  ∀ parent : BombieriTest,
    bombieriConjugateTest parent = parent →
      ∀ k : ℤ,
        0 < bombieriRealQuadraticValue
            (monotoneQuarterFiniteBlockInterior parent k n) →
          ∀ t : ℝ,
            0 ≤ bombieriRealQuadraticValue
              (monotoneQuarterFiniteBlock
                (finiteBlockMiddleOrthogonalResidualPencilParent
                  parent k n t) k 0 n)

/-- At an induction stage, where all shorter production blocks are already
nonnegative, the original residual determinant is exactly the explicit
common-parent residual-pencil certificate.  Thus the genuine `n ≥ 6`
problem has been reduced without importing the false abstract overlap
principle. -/
theorem realFiniteBlockMiddleOrthogonalResidualDeterminant_iff_commonParentPencil
    (n : ℕ) (hn : 4 ≤ n)
    (hprev : RealFiniteBlockProductionNonnegativeUpTo (n - 1)) :
    RealFiniteBlockMiddleOrthogonalResidualDeterminantAtLength n ↔
      RealFiniteBlockCommonParentResidualPencilNonnegativeAtLength n := by
  constructor
  · intro hdet parent hparent k hMpos t
    let l : BombieriTest :=
      finiteBlockLeftMiddleOrthogonalResidual parent k n
    let r : BombieriTest :=
      finiteBlockRightMiddleOrthogonalResidual parent k n
    let M : ℝ := bombieriRealQuadraticValue
      (monotoneQuarterFiniteBlockInterior parent k n)
    have hadj := finiteBlock_adjacentPrincipalMinors_of_previousLengths
      n hn hprev parent hparent k
    have hdiagonal :=
      finiteBlock_middleOrthogonalResidualQuadratic_coordinates parent k n
    have hM : M = bombieriRealQuadraticValue
        (monotoneQuarterFiniteBlockInterior parent k n) := rfl
    have hMnonnegative : 0 ≤ M := by rw [hM]; exact hMpos.le
    have hlNonnegative : 0 ≤ bombieriRealQuadraticValue l := by
      change 0 ≤ bombieriRealQuadraticValue
        (finiteBlockLeftMiddleOrthogonalResidual parent k n)
      rw [hdiagonal.1]
      exact mul_nonneg hMnonnegative (sub_nonneg.mpr hadj.1)
    have hrNonnegative : 0 ≤ bombieriRealQuadraticValue r := by
      change 0 ≤ bombieriRealQuadraticValue
        (finiteBlockRightMiddleOrthogonalResidual parent k n)
      rw [hdiagonal.2]
      exact mul_nonneg hMnonnegative (sub_nonneg.mpr hadj.2)
    have hresidual :
        (bombieriTwoBlockGlobalCrossSymbol l r).re ^ 2 ≤
          bombieriRealQuadraticValue l * bombieriRealQuadraticValue r := by
      exact hdet parent hparent k hMpos
    rw [finiteBlock_residualPencil_eq parent k n (by omega),
      bombieriRealQuadraticValue_add_real_smul]
    exact real_pencil_nonnegative_of_two_by_two_determinant
      hlNonnegative hrNonnegative hresidual t
  · intro hpencil parent hparent k hMpos
    let l : BombieriTest :=
      finiteBlockLeftMiddleOrthogonalResidual parent k n
    let r : BombieriTest :=
      finiteBlockRightMiddleOrthogonalResidual parent k n
    let M : ℝ := bombieriRealQuadraticValue
      (monotoneQuarterFiniteBlockInterior parent k n)
    have hadj := finiteBlock_adjacentPrincipalMinors_of_previousLengths
      n hn hprev parent hparent k
    have hdiagonal :=
      finiteBlock_middleOrthogonalResidualQuadratic_coordinates parent k n
    have hM : M = bombieriRealQuadraticValue
        (monotoneQuarterFiniteBlockInterior parent k n) := rfl
    have hMnonnegative : 0 ≤ M := by rw [hM]; exact hMpos.le
    have hrNonnegative : 0 ≤ bombieriRealQuadraticValue r := by
      change 0 ≤ bombieriRealQuadraticValue
        (finiteBlockRightMiddleOrthogonalResidual parent k n)
      rw [hdiagonal.2]
      exact mul_nonneg hMnonnegative (sub_nonneg.mpr hadj.2)
    apply real_two_by_two_determinant_of_all_nonnegative hrNonnegative
    intro t
    have h := hpencil parent hparent k hMpos t
    rw [finiteBlock_residualPencil_eq parent k n (by omega),
      bombieriRealQuadraticValue_add_real_smul] at h
    exact h

private theorem real_two_by_two_determinant_of_nonnegative_positiveRay
    {A B U : ℝ}
    (hB : 0 ≤ B) (hU : U < 0)
    (hall : ∀ t : ℝ, 0 ≤ t → 0 ≤ A + t ^ 2 * B + 2 * t * U) :
    U ^ 2 ≤ A * B := by
  have hA : 0 ≤ A := by
    simpa using hall 0 le_rfl
  by_cases hBzero : B = 0
  · let t : ℝ := -(A + 1) / (2 * U)
    have ht : 0 ≤ t := by
      have hnum : 0 < A + 1 := by linarith
      have hden : 2 * U < 0 := by nlinarith
      dsimp only [t]
      exact (div_pos_of_neg_of_neg (neg_lt_zero.mpr hnum) hden).le
    have h := hall t ht
    have hid : A + t ^ 2 * B + 2 * t * U = -1 := by
      dsimp only [t]
      rw [hBzero, mul_zero, add_zero]
      field_simp [ne_of_lt hU]
      ring
    rw [hid] at h
    linarith
  · have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hBzero)
    have ht : 0 ≤ -U / B :=
      div_nonneg (by linarith) hBpos.le
    have h := hall (-U / B) ht
    have hid : A + (-U / B) ^ 2 * B + 2 * (-U / B) * U =
        (A * B - U ^ 2) / B := by
      field_simp [hBzero]
      ring
    rw [hid] at h
    rcases (div_nonneg_iff.mp h) with hpos | hneg
    · exact sub_nonneg.mp hpos.1
    · exact (not_le_of_gt hBpos hneg.2).elim

/-- The actual common-parent residual pencil restricted to the positive
parameter ray.  This is strictly less data than the full real pencil: positive
residual cross is automatically harmless, and only negative cross can attain
its minimum at a positive parameter. -/
def RealFiniteBlockCommonParentResidualPositiveRayNonnegativeAtLength
    (n : ℕ) : Prop :=
  ∀ parent : BombieriTest,
    bombieriConjugateTest parent = parent →
      ∀ k : ℤ,
        0 < bombieriRealQuadraticValue
            (monotoneQuarterFiniteBlockInterior parent k n) →
          ∀ t : ℝ, 0 ≤ t →
            0 ≤ bombieriRealQuadraticValue
              (monotoneQuarterFiniteBlock
                (finiteBlockMiddleOrthogonalResidualPencilParent
                  parent k n t) k 0 n)

/-- Under the already-proved shorter blocks, the genuinely one-sided Schur
condition is exactly positivity of the explicit common-parent residual pencil
on `t ≥ 0`.  No negative parameter and no arbitrary pair of tests is needed. -/
theorem realFiniteBlockMiddlePivotNegativeSchur_iff_commonParentPositiveRay
    (n : ℕ) (hn : 4 ≤ n)
    (hprev : RealFiniteBlockProductionNonnegativeUpTo (n - 1)) :
    RealFiniteBlockMiddlePivotNegativeSchurAtLength n ↔
      RealFiniteBlockCommonParentResidualPositiveRayNonnegativeAtLength n := by
  constructor
  · intro hnegative parent hparent k hMpos t ht
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
    let l : BombieriTest :=
      finiteBlockLeftMiddleOrthogonalResidual parent k n
    let r : BombieriTest :=
      finiteBlockRightMiddleOrthogonalResidual parent k n
    have hadj := finiteBlock_adjacentPrincipalMinors_of_previousLengths
      n hn hprev parent hparent k
    change U ^ 2 ≤ A * M ∧ V ^ 2 ≤ M * E at hadj
    have hdiagonal :=
      finiteBlock_middleOrthogonalResidualQuadratic_coordinates parent k n
    change bombieriRealQuadraticValue l = M * (A * M - U ^ 2) ∧
      bombieriRealQuadraticValue r = M * (M * E - V ^ 2) at hdiagonal
    have hcross := finiteBlock_middleOrthogonalResidualCross_coordinate
      parent k n
    change (bombieriTwoBlockGlobalCrossSymbol l r).re =
      M * (M * X - U * V) at hcross
    have hlNonnegative : 0 ≤ bombieriRealQuadraticValue l := by
      rw [hdiagonal.1]
      exact mul_nonneg hMpos.le (sub_nonneg.mpr hadj.1)
    have hrNonnegative : 0 ≤ bombieriRealQuadraticValue r := by
      rw [hdiagonal.2]
      exact mul_nonneg hMpos.le (sub_nonneg.mpr hadj.2)
    rw [finiteBlock_residualPencil_eq parent k n (by omega),
      bombieriRealQuadraticValue_add_real_smul]
    change 0 ≤ bombieriRealQuadraticValue l +
      t ^ 2 * bombieriRealQuadraticValue r +
        2 * t * (bombieriTwoBlockGlobalCrossSymbol l r).re
    by_cases hdelta : M * X - U * V < 0
    · have hmiddle := hnegative parent hparent k hMpos hdelta
      have hactual :
          (bombieriTwoBlockGlobalCrossSymbol l r).re ^ 2 ≤
            bombieriRealQuadraticValue l * bombieriRealQuadraticValue r := by
        rw [hcross, hdiagonal.1, hdiagonal.2]
        calc
          (M * (M * X - U * V)) ^ 2 =
              M ^ 2 * (M * X - U * V) ^ 2 := by ring
          _ ≤ M ^ 2 *
              ((A * M - U ^ 2) * (M * E - V ^ 2)) :=
            mul_le_mul_of_nonneg_left hmiddle (sq_nonneg M)
          _ = (M * (A * M - U ^ 2)) *
              (M * (M * E - V ^ 2)) := by ring
      exact real_pencil_nonnegative_of_two_by_two_determinant
        hlNonnegative hrNonnegative hactual t
    · have hcrossNonnegative :
          0 ≤ (bombieriTwoBlockGlobalCrossSymbol l r).re := by
        rw [hcross]
        exact mul_nonneg hMpos.le (le_of_not_gt hdelta)
      positivity
  · intro hray parent hparent k
    dsimp only
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
    let l : BombieriTest :=
      finiteBlockLeftMiddleOrthogonalResidual parent k n
    let r : BombieriTest :=
      finiteBlockRightMiddleOrthogonalResidual parent k n
    intro hMpos hdelta
    have hadj := finiteBlock_adjacentPrincipalMinors_of_previousLengths
      n hn hprev parent hparent k
    change U ^ 2 ≤ A * M ∧ V ^ 2 ≤ M * E at hadj
    have hdiagonal :=
      finiteBlock_middleOrthogonalResidualQuadratic_coordinates parent k n
    change bombieriRealQuadraticValue l = M * (A * M - U ^ 2) ∧
      bombieriRealQuadraticValue r = M * (M * E - V ^ 2) at hdiagonal
    have hcross := finiteBlock_middleOrthogonalResidualCross_coordinate
      parent k n
    change (bombieriTwoBlockGlobalCrossSymbol l r).re =
      M * (M * X - U * V) at hcross
    have hrNonnegative : 0 ≤ bombieriRealQuadraticValue r := by
      rw [hdiagonal.2]
      exact mul_nonneg hMpos.le (sub_nonneg.mpr hadj.2)
    have hcrossNegative :
        (bombieriTwoBlockGlobalCrossSymbol l r).re < 0 := by
      rw [hcross]
      exact mul_neg_of_pos_of_neg hMpos hdelta
    have hall : ∀ t : ℝ, 0 ≤ t →
        0 ≤ bombieriRealQuadraticValue l +
          t ^ 2 * bombieriRealQuadraticValue r +
            2 * t * (bombieriTwoBlockGlobalCrossSymbol l r).re := by
      intro t ht
      have h := hray parent hparent k hMpos t ht
      rw [finiteBlock_residualPencil_eq parent k n (by omega),
        bombieriRealQuadraticValue_add_real_smul] at h
      exact h
    have hactual := real_two_by_two_determinant_of_nonnegative_positiveRay
      hrNonnegative hcrossNegative hall
    rw [hcross, hdiagonal.1, hdiagonal.2] at hactual
    have hscaled :
        M ^ 2 * (M * X - U * V) ^ 2 ≤
          M ^ 2 * ((A * M - U ^ 2) * (M * E - V ^ 2)) := by
      calc
        M ^ 2 * (M * X - U * V) ^ 2 =
            (M * (M * X - U * V)) ^ 2 := by ring
        _ ≤ (M * (A * M - U ^ 2)) *
              (M * (M * E - V ^ 2)) := hactual
        _ = M ^ 2 *
              ((A * M - U ^ 2) * (M * E - V ^ 2)) := by ring
    exact le_of_mul_le_mul_left hscaled (sq_pos_of_pos hMpos)

/-- Lengths four and five followed by the positive common-parent residual ray
at every tail length supply the complete one-sided induction. -/
theorem inductiveNegativeSchurOnlyClosure_of_four_five_and_tailPositiveRay
    (hfour : RealFiniteBlockProductionNonnegativeAtLength 4)
    (hfive : RealFiniteBlockProductionNonnegativeAtLength 5)
    (htail : ∀ n : ℕ, 6 ≤ n →
      RealFiniteBlockCommonParentResidualPositiveRayNonnegativeAtLength n) :
    RealFiniteBlockInductiveNegativeSchurOnlyClosure := by
  intro n hn hprev
  by_cases hn4 : n = 4
  · subst n
    exact middlePivotNegativeSchur_of_residualDeterminant 4
      (fourCell_residualDeterminant_of_production hfour)
  by_cases hn5 : n = 5
  · subst n
    exact middlePivotNegativeSchur_of_residualDeterminant 5
      (fiveCell_residualDeterminant_of_production hfive)
  exact
    (realFiniteBlockMiddlePivotNegativeSchur_iff_commonParentPositiveRay
      n hn hprev).2 (htail n (by omega))

/-- The two low production theorems and the positive-ray tail imply complete
real Bombieri positivity. -/
theorem bombieriRealQuadraticNonnegativity_of_four_five_and_tailPositiveRay
    (hfour : RealFiniteBlockProductionNonnegativeAtLength 4)
    (hfive : RealFiniteBlockProductionNonnegativeAtLength 5)
    (htail : ∀ n : ℕ, 6 ≤ n →
      RealFiniteBlockCommonParentResidualPositiveRayNonnegativeAtLength n) :
    BombieriRealQuadraticNonnegativity := by
  exact bombieriRealQuadraticNonnegativity_of_inductiveNegativeSchurOnlyClosure
    (inductiveNegativeSchurOnlyClosure_of_four_five_and_tailPositiveRay
      hfour hfive htail)

/-- Terminal RH bridge with the weakest current all-length common-parent
certificate. -/
theorem riemannHypothesis_of_four_five_and_tailPositiveRay
    (zeros : ZetaZeroEnumeration)
    (hfour : RealFiniteBlockProductionNonnegativeAtLength 4)
    (hfive : RealFiniteBlockProductionNonnegativeAtLength 5)
    (htail : ∀ n : ℕ, 6 ≤ n →
      RealFiniteBlockCommonParentResidualPositiveRayNonnegativeAtLength n) :
    RiemannHypothesis := by
  exact (riemannHypothesis_iff_bombieriRealQuadraticNonnegativity zeros).2
    (bombieriRealQuadraticNonnegativity_of_four_five_and_tailPositiveRay
      hfour hfive htail)

/-- RH supplies every positive common-parent residual ray directly from global
Bombieri positivity. -/
theorem tailPositiveRay_of_riemannHypothesis
    (zeros : ZetaZeroEnumeration) (hRH : RiemannHypothesis) :
    ∀ n : ℕ, 6 ≤ n →
      RealFiniteBlockCommonParentResidualPositiveRayNonnegativeAtLength n := by
  have hglobal : BombieriRealQuadraticNonnegativity :=
    (riemannHypothesis_iff_bombieriRealQuadraticNonnegativity zeros).1 hRH
  intro n _hn parent hparent k _hMpos t _ht
  apply hglobal
  exact bombieriConjugateTest_monotoneQuarterFiniteBlock
    (finiteBlockMiddleOrthogonalResidualPencilParent parent k n t)
    (finiteBlockMiddleOrthogonalResidualPencilParent_conjugate_fixed
      parent hparent k n t) k 0 n

/-- Conditional only on the two active low-length production problems, the
positive common-parent tail ray is exactly RH. -/
theorem riemannHypothesis_iff_tailPositiveRay_of_four_five
    (zeros : ZetaZeroEnumeration)
    (hfour : RealFiniteBlockProductionNonnegativeAtLength 4)
    (hfive : RealFiniteBlockProductionNonnegativeAtLength 5) :
    RiemannHypothesis ↔
      ∀ n : ℕ, 6 ≤ n →
        RealFiniteBlockCommonParentResidualPositiveRayNonnegativeAtLength n := by
  exact ⟨tailPositiveRay_of_riemannHypothesis zeros,
    riemannHypothesis_of_four_five_and_tailPositiveRay
      zeros hfour hfive⟩

end

end ArithmeticHodge.Analysis.MultiplicativeWeilAllLengthCommonParentResidualStructural

import ArithmeticHodge.Analysis.MultiplicativeWeilAllLengthResidualPropagationClosureStructural

set_option autoImplicit false

open Complex Real

namespace ArithmeticHodge.Analysis.MultiplicativeWeilAllLengthCommonParentResidualStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilAllLengthResidualDeterminantSingularClosureStructural
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

end

end ArithmeticHodge.Analysis.MultiplicativeWeilAllLengthCommonParentResidualStructural

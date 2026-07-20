import ArithmeticHodge.Analysis.MultiplicativeWeilFourCellResidualDeterminantStructural

set_option autoImplicit false

open Complex Real Set

namespace ArithmeticHodge.Analysis.MultiplicativeWeilAllLengthResidualDeterminantSingularClosureStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilMinimalNegativeBlockStructural
open MultiplicativeWeilMonotoneNullSuffixVariationStructural
open MultiplicativeWeilMonotoneQuarterPartitionStructural
open MultiplicativeWeilMonotonePrimeAtomAggregateObstructionStructural
open MultiplicativeWeilPositiveResidualKernelObstructionStructural
open MultiplicativeWeilQuarterLogLatticePartitionStructural
open MultiplicativeWeilRealMonotonePropagationCriterionStructural
open MultiplicativeWeilRealMonotoneTailConeCriterionStructural

/-!
# Positive residual pivots recover every singular induction branch

At an arbitrary induction length, insert one strictly positive real bump in a
fixed interior quarter-cell.  Shorter-length positivity makes a zero interior
vector radical against this bump, so the modified interior pivot is strictly
positive while both endpoint cells remain unchanged.  The residual determinant
for the modified parent then forces the missing sparse-endpoint inequality.
-/

private theorem endpointPair_nonnegative_of_residualDeterminant
    {A M E U V X : ℝ}
    (hMpos : 0 < M)
    (hAM : U ^ 2 ≤ A * M)
    (hME : V ^ 2 ≤ M * E)
    (hresidual :
      (M * X - U * V) ^ 2 ≤
        (A * M - U ^ 2) * (M * E - V ^ 2)) :
    0 ≤ A + E + 2 * X := by
  let alpha : ℝ := A * M - U ^ 2
  let beta : ℝ := M * E - V ^ 2
  let delta : ℝ := M * X - U * V
  have halpha : 0 ≤ alpha := by dsimp only [alpha]; linarith
  have hbeta : 0 ≤ beta := by dsimp only [beta]; linarith
  have hresidual' : delta ^ 2 ≤ alpha * beta := by
    simpa only [alpha, beta, delta] using hresidual
  have hschur : 0 ≤ alpha + beta + 2 * delta := by
    by_contra hnot
    have hnegative : alpha + beta + 2 * delta < 0 :=
      lt_of_not_ge hnot
    have hsumNonnegative : 0 ≤ alpha + beta := add_nonneg halpha hbeta
    have hminusDeltaPositive : 0 < -2 * delta := by linarith
    have hsquare :
        (alpha + beta) ^ 2 < (-2 * delta) ^ 2 :=
      (sq_lt_sq₀ hsumNonnegative hminusDeltaPositive.le).2 (by linarith)
    nlinarith [sq_nonneg (alpha - beta)]
  have hidentity :
      M * (A + E + 2 * X) =
        (U + V) ^ 2 + alpha + beta + 2 * delta := by
    dsimp only [alpha, beta, delta]
    ring
  have hscaled : 0 ≤ M * (A + E + 2 * X) := by
    rw [hidentity]
    nlinarith [sq_nonneg (U + V)]
  exact (mul_nonneg_iff_of_pos_left hMpos).mp hscaled

private theorem monotoneQuarterCell_eq_zero_of_innerSupport_left
    (f : BombieriTest) (k : ℤ)
    (hsupport : tsupport (f : ℝ → ℂ) ⊆
      Icc (quarterLogLatticePoint (k + 2))
        (quarterLogLatticePoint (k + 3))) :
    monotoneQuarterCell f k = 0 := by
  apply TestFunction.ext
  intro x
  by_cases hx : f x = 0
  · simp [monotoneQuarterCell_apply, hx]
  · have hxt := hsupport
      (subset_tsupport (f : ℝ → ℂ) (Function.mem_support.mpr hx))
    rw [monotoneQuarterCell_apply,
      monotoneQuarterWeight_eq_zero_of_le_left k hxt.1]
    simp

private theorem monotoneQuarterCell_eq_zero_of_innerSupport_right
    (f : BombieriTest) (k : ℤ) (n : ℕ) (hn : 4 ≤ n)
    (hsupport : tsupport (f : ℝ → ℂ) ⊆
      Icc (quarterLogLatticePoint (k + 2))
        (quarterLogLatticePoint (k + 3))) :
    monotoneQuarterCell f (k + ((n - 1 : ℕ) : ℤ)) = 0 := by
  apply TestFunction.ext
  intro x
  by_cases hx : f x = 0
  · simp [monotoneQuarterCell_apply, hx]
  · have hxt := hsupport
      (subset_tsupport (f : ℝ → ℂ) (Function.mem_support.mpr hx))
    have hindex : k + 3 ≤ k + ((n - 1 : ℕ) : ℤ) := by
      omega
    have hq := quarterLogLatticePoint_mono hindex
    rw [monotoneQuarterCell_apply,
      monotoneQuarterWeight_eq_zero_of_le
        (k + ((n - 1 : ℕ) : ℤ)) (hxt.2.trans hq)]
    simp

private theorem finiteBlockInterior_eq_self_of_innerSupport
    (f : BombieriTest) (k : ℤ) (n : ℕ) (hn : 4 ≤ n)
    (hsupport : tsupport (f : ℝ → ℂ) ⊆
      Icc (quarterLogLatticePoint (k + 2))
        (quarterLogLatticePoint (k + 3))) :
    monotoneQuarterFiniteBlockInterior f k n = f := by
  apply TestFunction.ext
  intro x
  rw [monotoneQuarterFiniteBlockInterior_apply f k n (by omega)]
  by_cases hx : f x = 0
  · simp [hx]
  · have hxt := hsupport
      (subset_tsupport (f : ℝ → ℂ) (Function.mem_support.mpr hx))
    have hindex : k + 3 ≤ k + ((n - 1 : ℕ) : ℤ) := by
      omega
    have hq := quarterLogLatticePoint_mono hindex
    rw [monotoneQuarterStep_eq_one_of_le (k + 1) (by
        simpa only [show k + 1 + 1 = k + 2 by ring] using hxt.1),
      monotoneQuarterStep_eq_zero_of_le
        (k + ((n - 1 : ℕ) : ℤ)) (hxt.2.trans hq)]
    norm_num

private theorem finiteBlockInterior_add
    (f g : BombieriTest) (k : ℤ) (n : ℕ) :
    monotoneQuarterFiniteBlockInterior (f + g) k n =
      monotoneQuarterFiniteBlockInterior f k n +
        monotoneQuarterFiniteBlockInterior g k n := by
  classical
  unfold monotoneQuarterFiniteBlockInterior monotoneQuarterFiniteBlock
  simp_rw [monotoneQuarterCell_add]
  exact Finset.sum_add_distrib

/-- At every induction length, the positive-pivot residual determinant already
contains the apparently missing singular-pivot endpoint clause.  A real bump
supported in one strictly interior cell leaves both endpoints fixed.  Shorter
block positivity makes the original zero interior radical against that bump,
so the modified interior has a strictly positive pivot and the determinant
applies. -/
theorem realFiniteBlockZeroInteriorSparseEndpointNonnegativeAtLength_of_previousLengths_and_residualDeterminant
    (n : ℕ) (hn : 4 ≤ n)
    (hprev : RealFiniteBlockProductionNonnegativeUpTo (n - 1))
    (hdeterminant :
      RealFiniteBlockMiddleOrthogonalResidualDeterminantAtLength n) :
    RealFiniteBlockZeroInteriorSparseEndpointNonnegativeAtLength n := by
  intro parent hparent k
  dsimp only
  intro hMzero
  let qa : ℝ := quarterLogLatticePoint (k + 2)
  let qb : ℝ := quarterLogLatticePoint (k + 3)
  have hqa : 0 < qa := quarterLogLatticePoint_pos (k + 2)
  have hqaqb : qa < qb := quarterLogLatticePoint_strictMono (by omega)
  obtain ⟨middle, center, hmiddleReal, hmiddleSupport, hpoint⟩ :=
    exists_three_pointSeparated_real_bombieri_bumps qa qb hqa hqaqb
  let g : BombieriTest := middle 0
  have hgReal : bombieriConjugateTest g = g := hmiddleReal 0
  have hgSupport : tsupport (g : ℝ → ℂ) ⊆ Icc qa qb :=
    (hmiddleSupport 0).trans Ioo_subset_Icc_self
  have hgOne : g (center 0) = 1 := by
    simpa only [g, if_pos] using hpoint 0 0
  have hgNe : g ≠ 0 := by
    intro hgzero
    have h := congrArg (fun f : BombieriTest ↦ f (center 0)) hgzero
    change g (center 0) = 0 at h
    rw [hgOne] at h
    norm_num at h
  have hratio : qb / qa ≤ 2 := by
    apply (div_le_iff₀ hqa).2
    dsimp only [qa, qb]
    calc
      quarterLogLatticePoint (k + 3) ≤
          quarterLogLatticePoint ((k + 2) + 4) :=
        quarterLogLatticePoint_mono (by omega)
      _ = 2 * quarterLogLatticePoint (k + 2) :=
        quarterLogLatticePoint_add_four (k + 2)
  have hgPositive : 0 < bombieriRealQuadraticValue g :=
    bombieriRealQuadraticValue_pos_of_ratioTwoCell_of_real_of_ne_zero
      g ⟨qa, qb, hqa, hqaqb.le, hgSupport, hratio⟩ hgReal hgNe
  have hgSupport' : tsupport (g : ℝ → ℂ) ⊆
      Icc (quarterLogLatticePoint (k + 2))
        (quarterLogLatticePoint (k + 3)) := by
    simpa only [qa, qb] using hgSupport
  have hcrossZero :=
    finiteBlockInterior_globalCross_eq_zero_of_previousLengths_and_quadratic_zero
      n hn hprev parent hparent k hMzero g hgReal
  rw [finiteBlockInterior_eq_self_of_innerSupport g k n hn hgSupport'] at hcrossZero
  let modified : BombieriTest := parent + g
  have hmodified : bombieriConjugateTest modified = modified := by
    dsimp only [modified]
    rw [bombieriConjugateTest_add, hparent, hgReal]
  have ha : monotoneQuarterCell modified k =
      monotoneQuarterCell parent k := by
    dsimp only [modified]
    rw [monotoneQuarterCell_add,
      monotoneQuarterCell_eq_zero_of_innerSupport_left g k hgSupport',
      add_zero]
  have he :
      monotoneQuarterCell modified (k + ((n - 1 : ℕ) : ℤ)) =
        monotoneQuarterCell parent (k + ((n - 1 : ℕ) : ℤ)) := by
    dsimp only [modified]
    rw [monotoneQuarterCell_add,
      monotoneQuarterCell_eq_zero_of_innerSupport_right
        g k n hn hgSupport', add_zero]
  have hm : monotoneQuarterFiniteBlockInterior modified k n =
      monotoneQuarterFiniteBlockInterior parent k n + g := by
    dsimp only [modified]
    rw [finiteBlockInterior_add,
      finiteBlockInterior_eq_self_of_innerSupport g k n hn hgSupport']
  have hmPositive :
      0 < bombieriRealQuadraticValue
        (monotoneQuarterFiniteBlockInterior modified k n) := by
    rw [hm, bombieriRealQuadraticValue_add, hMzero, hcrossZero]
    linarith
  let a : BombieriTest := monotoneQuarterCell parent k
  let m : BombieriTest := monotoneQuarterFiniteBlockInterior modified k n
  let e : BombieriTest :=
    monotoneQuarterCell parent (k + ((n - 1 : ℕ) : ℤ))
  let A : ℝ := bombieriRealQuadraticValue a
  let M : ℝ := bombieriRealQuadraticValue m
  let E : ℝ := bombieriRealQuadraticValue e
  let U : ℝ := (bombieriTwoBlockGlobalCrossSymbol a m).re
  let V : ℝ := (bombieriTwoBlockGlobalCrossSymbol m e).re
  let X : ℝ := (bombieriTwoBlockGlobalCrossSymbol a e).re
  have hadj := finiteBlock_adjacentPrincipalMinors_of_previousLengths
    n hn hprev modified hmodified k
  rw [ha, he] at hadj
  change U ^ 2 ≤ A * M ∧ V ^ 2 ≤ M * E at hadj
  have hpivot :=
    (realFiniteBlockMiddleOrthogonalResidualDeterminant_iff_middlePivot n).1
      hdeterminant
  have hresidual := hpivot modified hmodified k
  dsimp only at hresidual
  rw [ha, he] at hresidual
  change 0 < M →
    (M * X - U * V) ^ 2 ≤
      (A * M - U ^ 2) * (M * E - V ^ 2) at hresidual
  have hendpoint := endpointPair_nonnegative_of_residualDeterminant
    hmPositive hadj.1 hadj.2 (hresidual hmPositive)
  rw [bombieriRealQuadraticValue_add]
  change 0 ≤ A + E + 2 * X
  exact hendpoint

/-- Consequently the residual determinant is the only new hypothesis needed
at one induction stage; its singular branch follows by perturbation. -/
theorem realFiniteBlockProductionNonnegativeAtLength_of_previousLengths_and_residualDeterminant_only
    (n : ℕ) (hn : 4 ≤ n)
    (hprev : RealFiniteBlockProductionNonnegativeUpTo (n - 1))
    (hdeterminant :
      RealFiniteBlockMiddleOrthogonalResidualDeterminantAtLength n) :
    RealFiniteBlockProductionNonnegativeAtLength n := by
  exact
    realFiniteBlockProductionNonnegativeAtLength_of_previousLengths_and_residualDeterminant
      n hn hprev hdeterminant
        (realFiniteBlockZeroInteriorSparseEndpointNonnegativeAtLength_of_previousLengths_and_residualDeterminant
          n hn hprev hdeterminant)

/-- Minimal staged determinant interface: at each new length, assuming the
already-proved shorter blocks, only the concrete middle-orthogonal residual
Cauchy--Schwarz inequality remains. -/
def RealFiniteBlockInductiveResidualDeterminantOnlyClosure : Prop :=
  ∀ n : ℕ, 4 ≤ n →
    RealFiniteBlockProductionNonnegativeUpTo (n - 1) →
      RealFiniteBlockMiddleOrthogonalResidualDeterminantAtLength n

/-- Removing the separately stated singular clause loses no information. -/
theorem inductiveResidualDeterminantOnlyClosure_iff_existingClosure :
    RealFiniteBlockInductiveResidualDeterminantOnlyClosure ↔
      RealFiniteBlockInductiveResidualDeterminantClosure := by
  constructor
  · intro hclosure n hn hprev
    have hdeterminant := hclosure n hn hprev
    exact ⟨hdeterminant,
      realFiniteBlockZeroInteriorSparseEndpointNonnegativeAtLength_of_previousLengths_and_residualDeterminant
        n hn hprev hdeterminant⟩
  · intro hclosure n hn hprev
    exact (hclosure n hn hprev).1

/-- The sharpened determinant-only induction interface implies RH through the
existing exact Bombieri criterion. -/
theorem riemannHypothesis_of_inductiveResidualDeterminantOnlyClosure
    (zeros : ZetaZeroEnumeration)
    (hclosure : RealFiniteBlockInductiveResidualDeterminantOnlyClosure) :
    RiemannHypothesis := by
  exact riemannHypothesis_of_inductiveResidualDeterminantClosure zeros
    (inductiveResidualDeterminantOnlyClosure_iff_existingClosure.mp hclosure)

/-- Exact RH characterization by one sign-free residual determinant at every
induction length. -/
theorem riemannHypothesis_iff_inductiveResidualDeterminantOnlyClosure
    (zeros : ZetaZeroEnumeration) :
    RiemannHypothesis ↔
      RealFiniteBlockInductiveResidualDeterminantOnlyClosure := by
  rw [riemannHypothesis_iff_inductiveResidualDeterminantClosure zeros]
  exact inductiveResidualDeterminantOnlyClosure_iff_existingClosure.symm

end

end ArithmeticHodge.Analysis.MultiplicativeWeilAllLengthResidualDeterminantSingularClosureStructural

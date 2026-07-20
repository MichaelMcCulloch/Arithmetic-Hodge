import ArithmeticHodge.Analysis.MultiplicativeWeilAllLengthResidualDeterminantSingularClosureStructural

set_option autoImplicit false

open Complex Real Set

namespace ArithmeticHodge.Analysis.MultiplicativeWeilAllLengthNegativeResidualStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilAllLengthResidualDeterminantSingularClosureStructural
open MultiplicativeWeilMinimalNegativeBlockStructural
open MultiplicativeWeilMonotoneNullSuffixVariationStructural
open MultiplicativeWeilMonotonePrimeAtomAggregateObstructionStructural
open MultiplicativeWeilMonotoneQuarterPartitionStructural
open MultiplicativeWeilPositiveResidualKernelObstructionStructural
open MultiplicativeWeilQuarterLogLatticePartitionStructural
open MultiplicativeWeilRealCutPhaseReductionStructural
open MultiplicativeWeilRealMonotonePropagationCriterionStructural
open MultiplicativeWeilRealMonotoneTailConeCriterionStructural

/-!
# The genuinely one-sided all-length residual condition

For production, a nonnegative middle-pivot residual cross helps the full
three-block quadratic.  Only a negative residual cross needs a Schur bound.
This module exposes that weaker condition at every length before addressing
the singular interior-pivot branch.
-/

/-- At one length, require residual Cauchy--Schwarz only when the actual
middle-pivot conditional cross is negative. -/
def RealFiniteBlockMiddlePivotNegativeSchurAtLength (n : ℕ) : Prop :=
  ∀ parent : BombieriTest,
    bombieriConjugateTest parent = parent →
      ∀ k : ℤ,
        let a := monotoneQuarterCell parent k
        let m := monotoneQuarterFiniteBlockInterior parent k n
        let e := monotoneQuarterCell parent
          (k + ((n - 1 : ℕ) : ℤ))
        let A := bombieriRealQuadraticValue a
        let M := bombieriRealQuadraticValue m
        let E := bombieriRealQuadraticValue e
        let U := (bombieriTwoBlockGlobalCrossSymbol a m).re
        let V := (bombieriTwoBlockGlobalCrossSymbol m e).re
        let X := (bombieriTwoBlockGlobalCrossSymbol a e).re
        0 < M → M * X - U * V < 0 →
          (M * X - U * V) ^ 2 ≤
            (A * M - U ^ 2) * (M * E - V ^ 2)

/-- The sign-free residual determinant implies the one-sided condition. -/
theorem middlePivotNegativeSchur_of_residualDeterminant
    (n : ℕ)
    (hdet : RealFiniteBlockMiddleOrthogonalResidualDeterminantAtLength n) :
    RealFiniteBlockMiddlePivotNegativeSchurAtLength n := by
  intro parent hparent k
  dsimp only
  intro hMpos _hnegative
  exact (realFiniteBlockMiddleOrthogonalResidualDeterminant_iff_middlePivot n).1
    hdet parent hparent k hMpos

private theorem threeBlock_nonnegative_of_nonnegativeConditionalCross
    {A M E U V X : ℝ}
    (hMpos : 0 < M)
    (hAM : U ^ 2 ≤ A * M)
    (hME : V ^ 2 ≤ M * E)
    (hdelta : 0 ≤ M * X - U * V) :
    0 ≤ A + M + E + 2 * (U + V + X) := by
  have hidentity :
      M * (A + M + E + 2 * (U + V + X)) =
        (M + U + V) ^ 2 + (A * M - U ^ 2) +
          (M * E - V ^ 2) + 2 * (M * X - U * V) := by
    ring
  have hscaled : 0 ≤
      M * (A + M + E + 2 * (U + V + X)) := by
    rw [hidentity]
    nlinarith [sq_nonneg (M + U + V)]
  exact (mul_nonneg_iff_of_pos_left hMpos).mp hscaled

private theorem monotoneQuarterFiniteBlock_shift_start_one_local
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

private theorem threeBlock_nonnegative_of_negativeSchur
    {A M E U V X : ℝ}
    (hMpos : 0 < M)
    (hAM : U ^ 2 ≤ A * M)
    (hME : V ^ 2 ≤ M * E)
    (hdelta : M * X - U * V < 0)
    (hschur : (M * X - U * V) ^ 2 ≤
      (A * M - U ^ 2) * (M * E - V ^ 2)) :
    0 ≤ A + M + E + 2 * (U + V + X) := by
  let alpha := A * M - U ^ 2
  let beta := M * E - V ^ 2
  let delta := M * X - U * V
  have halpha : 0 ≤ alpha := by dsimp only [alpha]; linarith
  have hbeta : 0 ≤ beta := by dsimp only [beta]; linarith
  have hsum : 0 ≤ alpha + beta + 2 * delta := by
    by_contra hnot
    have hneg : alpha + beta + 2 * delta < 0 := lt_of_not_ge hnot
    have hab : 0 ≤ alpha + beta := add_nonneg halpha hbeta
    have hminus : 0 < -2 * delta := by
      dsimp only [delta]
      linarith
    have hsquares : (alpha + beta) ^ 2 < (-2 * delta) ^ 2 :=
      (sq_lt_sq₀ hab hminus.le).2 (by linarith)
    nlinarith [sq_nonneg (alpha - beta)]
  have hidentity :
      M * (A + M + E + 2 * (U + V + X)) =
        (M + U + V) ^ 2 + alpha + beta + 2 * delta := by
    dsimp only [alpha, beta, delta]
    ring
  have hscaled : 0 ≤
      M * (A + M + E + 2 * (U + V + X)) := by
    rw [hidentity]
    nlinarith [sq_nonneg (M + U + V)]
  exact (mul_nonneg_iff_of_pos_left hMpos).mp hscaled

private theorem endpointPair_nonnegative_of_negativeSchur
    {A M E U V X : ℝ}
    (hMpos : 0 < M)
    (hAM : U ^ 2 ≤ A * M)
    (hME : V ^ 2 ≤ M * E)
    (hnegative : M * X - U * V < 0 →
      (M * X - U * V) ^ 2 ≤
        (A * M - U ^ 2) * (M * E - V ^ 2)) :
    0 ≤ A + E + 2 * X := by
  let alpha : ℝ := A * M - U ^ 2
  let beta : ℝ := M * E - V ^ 2
  let delta : ℝ := M * X - U * V
  have halpha : 0 ≤ alpha := by dsimp only [alpha]; linarith
  have hbeta : 0 ≤ beta := by dsimp only [beta]; linarith
  have hschur : 0 ≤ alpha + beta + 2 * delta := by
    by_cases hdelta : delta < 0
    · have hresidual : delta ^ 2 ≤ alpha * beta := by
        apply hnegative
        simpa only [delta] using hdelta
      by_contra hnot
      have hsumNegative : alpha + beta + 2 * delta < 0 :=
        lt_of_not_ge hnot
      have hsumNonnegative : 0 ≤ alpha + beta := add_nonneg halpha hbeta
      have hminusDeltaPositive : 0 < -2 * delta := by linarith
      have hsquare : (alpha + beta) ^ 2 < (-2 * delta) ^ 2 :=
        (sq_lt_sq₀ hsumNonnegative hminusDeltaPositive.le).2 (by linarith)
      nlinarith [sq_nonneg (alpha - beta)]
    · have hdeltaNonnegative : 0 ≤ delta := le_of_not_gt hdelta
      linarith
  have hidentity :
      M * (A + E + 2 * X) =
        (U + V) ^ 2 + alpha + beta + 2 * delta := by
    dsimp only [alpha, beta, delta]
    ring
  have hscaled : 0 ≤ M * (A + E + 2 * X) := by
    rw [hidentity]
    nlinarith [sq_nonneg (U + V)]
  exact (mul_nonneg_iff_of_pos_left hMpos).mp hscaled

/-- At an arbitrary induction length, the one-sided negative Schur condition
closes the positive-interior branch; the usual sparse endpoint condition
closes the singular branch. -/
theorem realFiniteBlockProductionNonnegativeAtLength_of_negativeSchur_and_zeroInterior
    (n : ℕ) (hn : 4 ≤ n)
    (hprev : RealFiniteBlockProductionNonnegativeUpTo (n - 1))
    (hnegative : RealFiniteBlockMiddlePivotNegativeSchurAtLength n)
    (hzero : RealFiniteBlockZeroInteriorSparseEndpointNonnegativeAtLength n) :
    RealFiniteBlockProductionNonnegativeAtLength n := by
  intro parent hparent k
  let a : BombieriTest := monotoneQuarterCell parent k
  let m : BombieriTest := monotoneQuarterFiniteBlockInterior parent k n
  let e : BombieriTest :=
    monotoneQuarterCell parent (k + ((n - 1 : ℕ) : ℤ))
  let A := bombieriRealQuadraticValue a
  let M := bombieriRealQuadraticValue m
  let E := bombieriRealQuadraticValue e
  let U := (bombieriTwoBlockGlobalCrossSymbol a m).re
  let V := (bombieriTwoBlockGlobalCrossSymbol m e).re
  let X := (bombieriTwoBlockGlobalCrossSymbol a e).re
  have hadj := finiteBlock_adjacentPrincipalMinors_of_previousLengths
    n hn hprev parent hparent k
  change U ^ 2 ≤ A * M ∧ V ^ 2 ≤ M * E at hadj
  have hmShift :
      monotoneQuarterFiniteBlock parent (k + 1) 0 (n - 2) = m := by
    dsimp only [m, monotoneQuarterFiniteBlockInterior]
    exact monotoneQuarterFiniteBlock_shift_start_one_local parent k (n - 2)
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
    change M = 0 → 0 ≤ bombieriRealQuadraticValue (a + e) at hpair
    have hpair0 := hpair hMzero
    rw [bombieriRealQuadraticValue_add] at hpair0
    change 0 ≤ A + E + 2 * X at hpair0
    rw [hMzero, hU, hV]
    linarith
  · have hMpos : 0 < M := lt_of_le_of_ne hM (Ne.symm hMzero)
    by_cases hdelta : M * X - U * V < 0
    · exact threeBlock_nonnegative_of_negativeSchur hMpos hadj.1 hadj.2
        hdelta (hnegative parent hparent k hMpos hdelta)
    · exact threeBlock_nonnegative_of_nonnegativeConditionalCross
        hMpos hadj.1 hadj.2 (le_of_not_gt hdelta)

/-- The one-sided condition also recovers the singular middle-pivot branch.
Insert a strictly positive bump in an interior quarter-cell.  It leaves the
endpoints fixed, while shorter-length positivity makes the original zero
interior radical against the bump.  The modified pivot is therefore positive,
and the endpoint identity needs a Schur bound only if its conditional cross is
negative. -/
theorem realFiniteBlockZeroInteriorSparseEndpointNonnegativeAtLength_of_previousLengths_and_negativeSchur
    (n : ℕ) (hn : 4 ≤ n)
    (hprev : RealFiniteBlockProductionNonnegativeUpTo (n - 1))
    (hnegative : RealFiniteBlockMiddlePivotNegativeSchurAtLength n) :
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
  have hresidual := hnegative modified hmodified k
  dsimp only at hresidual
  rw [ha, he] at hresidual
  change 0 < M → M * X - U * V < 0 →
    (M * X - U * V) ^ 2 ≤
      (A * M - U ^ 2) * (M * E - V ^ 2) at hresidual
  have hendpoint := endpointPair_nonnegative_of_negativeSchur
    hmPositive hadj.1 hadj.2 (hresidual hmPositive)
  rw [bombieriRealQuadraticValue_add]
  change 0 ≤ A + E + 2 * X
  exact hendpoint

/-- Thus the negative-branch Schur inequality is the only new hypothesis at
one induction stage; the positive-cross and singular-pivot branches are both
automatic. -/
theorem realFiniteBlockProductionNonnegativeAtLength_of_previousLengths_and_negativeSchur_only
    (n : ℕ) (hn : 4 ≤ n)
    (hprev : RealFiniteBlockProductionNonnegativeUpTo (n - 1))
    (hnegative : RealFiniteBlockMiddlePivotNegativeSchurAtLength n) :
    RealFiniteBlockProductionNonnegativeAtLength n := by
  exact
    realFiniteBlockProductionNonnegativeAtLength_of_negativeSchur_and_zeroInterior
      n hn hprev hnegative
        (realFiniteBlockZeroInteriorSparseEndpointNonnegativeAtLength_of_previousLengths_and_negativeSchur
          n hn hprev hnegative)

/-- Minimal staged interface: at each new length, require the residual Schur
bound only on actual common-parent data with negative conditional cross. -/
def RealFiniteBlockInductiveNegativeSchurOnlyClosure : Prop :=
  ∀ n : ℕ, 4 ≤ n →
    RealFiniteBlockProductionNonnegativeUpTo (n - 1) →
      RealFiniteBlockMiddlePivotNegativeSchurAtLength n

/-- Finite induction from the genuinely one-sided interface. -/
theorem realFiniteBlockProductionNonnegativeUpTo_all_of_inductiveNegativeSchurOnly
    (hclosure : RealFiniteBlockInductiveNegativeSchurOnlyClosure) :
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
        have hnew :=
          realFiniteBlockProductionNonnegativeAtLength_of_previousLengths_and_negativeSchur_only
            (n + 1) hn4 hprev (hclosure (n + 1) hn4 hprev)
        intro m hm
        by_cases hmn : m ≤ n
        · exact ih m hmn
        · have hmeq : m = n + 1 := by omega
          subst m
          exact hnew

/-- The one-sided staged interface already implies the complete real Bombieri
quadratic criterion. -/
theorem bombieriRealQuadraticNonnegativity_of_inductiveNegativeSchurOnlyClosure
    (hclosure : RealFiniteBlockInductiveNegativeSchurOnlyClosure) :
    BombieriRealQuadraticNonnegativity := by
  intro parent hparent
  obtain ⟨lo, n, _hleft, _hright, hsum, _hratio, _hsuffix⟩ :=
    exists_monotoneQuarterCell_decomposition parent
  have hproduction :=
    realFiniteBlockProductionNonnegativeUpTo_all_of_inductiveNegativeSchurOnly
      hclosure n n le_rfl parent hparent lo
  have hblock : monotoneQuarterFiniteBlock parent lo 0 n = parent := by
    simpa only [monotoneQuarterFiniteBlock, zero_add] using hsum
  rw [hblock] at hproduction
  exact hproduction

/-- Conversely, global real Bombieri positivity supplies the one-sided Schur
condition through ordinary residual Cauchy--Schwarz. -/
theorem inductiveNegativeSchurOnlyClosure_of_bombieriRealQuadraticNonnegativity
    (hglobal : BombieriRealQuadraticNonnegativity) :
    RealFiniteBlockInductiveNegativeSchurOnlyClosure := by
  intro n hn hprev
  have hdeterminant :=
    (realFiniteBlockInductiveResidualDeterminantClosure_of_bombieriRealQuadraticNonnegativity
      hglobal n hn hprev).1
  exact middlePivotNegativeSchur_of_residualDeterminant n hdeterminant

/-- Exact characterization of complete real Bombieri positivity by the
negative branch of the actual common-parent residual pencil alone. -/
theorem bombieriRealQuadraticNonnegativity_iff_inductiveNegativeSchurOnlyClosure :
    BombieriRealQuadraticNonnegativity ↔
      RealFiniteBlockInductiveNegativeSchurOnlyClosure := by
  exact ⟨inductiveNegativeSchurOnlyClosure_of_bombieriRealQuadraticNonnegativity,
    bombieriRealQuadraticNonnegativity_of_inductiveNegativeSchurOnlyClosure⟩

/-- The one-sided closure is a lossless sharpening of the previous sign-free
determinant closure. -/
theorem inductiveNegativeSchurOnlyClosure_iff_existingClosure :
    RealFiniteBlockInductiveNegativeSchurOnlyClosure ↔
      RealFiniteBlockInductiveResidualDeterminantClosure := by
  rw [← bombieriRealQuadraticNonnegativity_iff_inductiveResidualDeterminantClosure]
  exact
    bombieriRealQuadraticNonnegativity_iff_inductiveNegativeSchurOnlyClosure.symm

/-- Terminal implication through the exact Bombieri criterion. -/
theorem riemannHypothesis_of_inductiveNegativeSchurOnlyClosure
    (zeros : ZetaZeroEnumeration)
    (hclosure : RealFiniteBlockInductiveNegativeSchurOnlyClosure) :
    RiemannHypothesis := by
  exact (riemannHypothesis_iff_bombieriRealQuadraticNonnegativity zeros).2
    (bombieriRealQuadraticNonnegativity_of_inductiveNegativeSchurOnlyClosure
      hclosure)

/-- RH is exactly the staged negative-cross Schur family. -/
theorem riemannHypothesis_iff_inductiveNegativeSchurOnlyClosure
    (zeros : ZetaZeroEnumeration) :
    RiemannHypothesis ↔
      RealFiniteBlockInductiveNegativeSchurOnlyClosure := by
  rw [riemannHypothesis_iff_bombieriRealQuadraticNonnegativity zeros]
  exact bombieriRealQuadraticNonnegativity_iff_inductiveNegativeSchurOnlyClosure

end

end ArithmeticHodge.Analysis.MultiplicativeWeilAllLengthNegativeResidualStructural

import ArithmeticHodge.Analysis.MultiplicativeWeilAllLengthPositiveRayKernelStructural

set_option autoImplicit false

open Complex Real Set

namespace ArithmeticHodge.Analysis.MultiplicativeWeilAllLengthResidualParentLocalizationStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilAllLengthCommonParentResidualStructural
open MultiplicativeWeilAllLengthPositiveRayKernelStructural
open MultiplicativeWeilMinimalNegativeBlockStructural
open MultiplicativeWeilMonotonePrimeAtomAggregateObstructionStructural
open MultiplicativeWeilMonotoneQuarterPartitionStructural
open MultiplicativeWeilQuarterLogLatticePartitionStructural
open MultiplicativeWeilRealMonotonePropagationCriterionStructural

/-!
# Localizing the all-length residual parent

Only the `n` physical cells from `k` through `k+n-1` enter the common-parent
residual pencil.  The parent may therefore be replaced, exactly, by the
smooth plateau between the two surrounding quarter-lattice cutoffs.  This
removes all irrelevant remote support before the remaining positive-ray
inequality is attacked.
-/

/-- The common parent cropped by a smooth plateau which is identically one
on every cell used by the `n`-cell residual pencil. -/
def finiteBlockResidualParentPlateau
    (parent : BombieriTest) (k : ℤ) (n : ℕ) : BombieriTest :=
  monotoneQuarterCutoff parent (k - 1) -
    monotoneQuarterCutoff parent (k + (n : ℤ) + 1)

theorem finiteBlockResidualParentPlateau_eq_finiteBlock
    (parent : BombieriTest) (k : ℤ) (n : ℕ) :
    finiteBlockResidualParentPlateau parent k n =
      monotoneQuarterFiniteBlock parent (k - 1) 0 (n + 2) := by
  unfold finiteBlockResidualParentPlateau monotoneQuarterFiniteBlock
  simp only [Nat.zero_add]
  symm
  convert sum_range_monotoneQuarterCell_eq_cutoff_sub
    parent (k - 1) (n + 2) using 1
  all_goals push_cast
  all_goals ring

/-- The localized parent has one fixed finite support window, independent of
the remote support of the original parent. -/
theorem finiteBlockResidualParentPlateau_tsupport_subset
    (parent : BombieriTest) (k : ℤ) (n : ℕ) :
    tsupport (finiteBlockResidualParentPlateau parent k n : ℝ → ℂ) ⊆
      Set.Icc (quarterLogLatticePoint (k - 1))
        (quarterLogLatticePoint (k + (n : ℤ) + 2)) := by
  rw [finiteBlockResidualParentPlateau_eq_finiteBlock]
  convert monotoneQuarterFiniteBlock_remotePrefix_tsupport_subset
      parent (k - 1) 0 (n + 2) using 1
  all_goals push_cast
  all_goals ring

theorem finiteBlockResidualParentPlateau_conjugate_fixed
    (parent : BombieriTest)
    (hparent : bombieriConjugateTest parent = parent)
    (k : ℤ) (n : ℕ) :
    bombieriConjugateTest (finiteBlockResidualParentPlateau parent k n) =
      finiteBlockResidualParentPlateau parent k n := by
  rw [finiteBlockResidualParentPlateau_eq_finiteBlock]
  exact bombieriConjugateTest_monotoneQuarterFiniteBlock
    parent hparent (k - 1) 0 (n + 2)

/-- On the complete lattice window touched by the production block, the
plateau parent is literally the original parent. -/
theorem finiteBlockResidualParentPlateau_apply_eq
    (parent : BombieriTest) (k : ℤ) (n : ℕ) (x : ℝ)
    (hx : x ∈ Set.Icc (quarterLogLatticePoint k)
      (quarterLogLatticePoint (k + (n : ℤ) + 1))) :
    finiteBlockResidualParentPlateau parent k n x = parent x := by
  simp only [finiteBlockResidualParentPlateau, TestFunction.coe_sub,
    Pi.sub_apply, monotoneQuarterCutoff_apply]
  rw [monotoneQuarterStep_eq_one_of_le (k - 1),
    monotoneQuarterStep_eq_zero_of_le (k + (n : ℤ) + 1)]
  · simp
  · exact hx.2
  · simpa only [sub_add_cancel] using hx.1

/-- Every individual cell used by the residual pencil is unchanged by the
plateau localization. -/
theorem monotoneQuarterCell_residualParentPlateau_eq
    (parent : BombieriTest) (k : ℤ) (n i : ℕ) (hi : i < n) :
    monotoneQuarterCell (finiteBlockResidualParentPlateau parent k n)
        (k + (i : ℤ)) =
      monotoneQuarterCell parent (k + (i : ℤ)) := by
  apply TestFunction.ext
  intro x
  simp only [monotoneQuarterCell_apply]
  by_cases hlo : quarterLogLatticePoint (k + (i : ℤ)) ≤ x
  · by_cases hhi : x ≤ quarterLogLatticePoint (k + (i : ℤ) + 2)
    · rw [finiteBlockResidualParentPlateau_apply_eq parent k n x]
      constructor
      · exact (quarterLogLatticePoint_mono (by omega)).trans hlo
      · exact hhi.trans (quarterLogLatticePoint_mono (by
          omega))
    · rw [monotoneQuarterWeight_eq_zero_of_le_left
        (k + (i : ℤ)) (le_of_not_ge hhi)]
      simp
  · rw [monotoneQuarterWeight_eq_zero_of_le
      (k + (i : ℤ)) (le_of_not_ge hlo)]
    simp

/-- Consequently every consecutive subblock contained in the `n` active
cells is exactly unchanged. -/
theorem monotoneQuarterFiniteBlock_residualParentPlateau_eq
    (parent : BombieriTest) (k : ℤ) (n start len : ℕ)
    (hsub : start + len ≤ n) :
    monotoneQuarterFiniteBlock
        (finiteBlockResidualParentPlateau parent k n) k start len =
      monotoneQuarterFiniteBlock parent k start len := by
  classical
  unfold monotoneQuarterFiniteBlock
  apply Finset.sum_congr rfl
  intro i hi
  have hil : i < len := Finset.mem_range.mp hi
  rw [monotoneQuarterCell_residualParentPlateau_eq]
  omega

/-- The actual residual pencil production block is invariant under the
plateau localization of its parent. -/
theorem finiteBlock_residualPencil_parentPlateau_eq
    (parent : BombieriTest) (k : ℤ) (n : ℕ) (hn : 3 ≤ n) (t : ℝ) :
    monotoneQuarterFiniteBlock
        (finiteBlockMiddleOrthogonalResidualPencilParent
          (finiteBlockResidualParentPlateau parent k n) k n t)
        k 0 n =
      monotoneQuarterFiniteBlock
        (finiteBlockMiddleOrthogonalResidualPencilParent parent k n t)
        k 0 n := by
  rw [finiteBlock_residualPencil_eq _ k n hn t,
    finiteBlock_residualPencil_eq parent k n hn t]
  have ha :
      monotoneQuarterCell (finiteBlockResidualParentPlateau parent k n) k =
        monotoneQuarterCell parent k := by
    simpa only [Nat.cast_zero, add_zero] using
      monotoneQuarterCell_residualParentPlateau_eq
        parent k n 0 (by omega)
  have hm := monotoneQuarterFiniteBlock_residualParentPlateau_eq
    parent k n 1 (n - 2) (by omega)
  have he := monotoneQuarterCell_residualParentPlateau_eq
    parent k n (n - 1) (by omega)
  simp only [finiteBlockLeftMiddleOrthogonalResidual,
    finiteBlockRightMiddleOrthogonalResidual,
    monotoneQuarterFiniteBlockInterior]
  rw [ha, hm, he]

/-! ## A canonical finite prime shell depending only on the block length -/

/-- The first natural cutoff above the multiplicative width of an `n`-cell
production block. -/
def finiteBlockResidualPrimeCutoff (n : ℕ) : ℕ :=
  Nat.ceil (quarterLogLatticePoint ((n : ℤ) + 1))

theorem finiteBlockResidual_latticeWindow_ratio
    (k : ℤ) (n : ℕ) :
    quarterLogLatticePoint (k + (n : ℤ) + 1) /
        quarterLogLatticePoint k =
      quarterLogLatticePoint ((n : ℤ) + 1) := by
  rw [show k + (n : ℤ) + 1 = k + ((n : ℤ) + 1) by ring,
    quarterLogLatticePoint_add]
  exact mul_div_cancel_right₀ _ (quarterLogLatticePoint_pos k).ne'

theorem finiteBlockResidual_latticeWindow_ratio_lt_cutoff
    (k : ℤ) (n : ℕ) :
    quarterLogLatticePoint (k + (n : ℤ) + 1) /
        quarterLogLatticePoint k <
      (((finiteBlockResidualPrimeCutoff n + 1 : ℕ) : ℝ)) := by
  rw [finiteBlockResidual_latticeWindow_ratio]
  calc
    quarterLogLatticePoint ((n : ℤ) + 1) ≤
        ((finiteBlockResidualPrimeCutoff n : ℕ) : ℝ) := by
      exact Nat.le_ceil _
    _ < (((finiteBlockResidualPrimeCutoff n + 1 : ℕ) : ℝ)) := by
      exact_mod_cast Nat.lt_succ_self (finiteBlockResidualPrimeCutoff n)

/-- The prime term of every `n`-cell residual pencil is the same canonical
finite shell length, uniformly in its lattice position and parent. -/
theorem primeSum_residualPencil_eq_canonicalFiniteShell
    (parent : BombieriTest) (k : ℤ) (n : ℕ) (t : ℝ) :
    let g := monotoneQuarterFiniteBlock
      (finiteBlockMiddleOrthogonalResidualPencilParent parent k n t)
      k 0 n
    primeSum (bombieriQuadraticTest g) =
      ∑ j ∈ Finset.range (finiteBlockResidualPrimeCutoff n),
        vonMangoldtPrimeSummand (bombieriQuadraticTest g) j := by
  exact primeSum_residualPencil_eq_finiteShell parent k n
    (finiteBlockResidualPrimeCutoff n) t
    (finiteBlockResidual_latticeWindow_ratio_lt_cutoff k n)

/-- Thus every remaining positive-ray fiber is exactly one finite-shell
domination inequality with a cutoff depending only on `n`. -/
theorem bombieriRealQuadraticValue_residualPencil_nonnegative_iff_canonicalFiniteShell
    (parent : BombieriTest) (k : ℤ) (n : ℕ) (t : ℝ) :
    let g := monotoneQuarterFiniteBlock
      (finiteBlockMiddleOrthogonalResidualPencilParent parent k n t)
      k 0 n
    0 ≤ bombieriRealQuadraticValue g ↔
      (∑ j ∈ Finset.range (finiteBlockResidualPrimeCutoff n),
          vonMangoldtPrimeSummand (bombieriQuadraticTest g) j).re ≤
        (bombieriLocalCriticalForm g g).re := by
  exact bombieriRealQuadraticValue_residualPencil_nonnegative_iff_finiteShell
    parent k n (finiteBlockResidualPrimeCutoff n) t
    (finiteBlockResidual_latticeWindow_ratio_lt_cutoff k n)

/-! ## Exact localization of the remaining positive-ray quantifiers -/

/-- The genuinely unresolved ray after deleting both irrelevant remote
support and the already-positive ratio-two cone. -/
def RealFiniteBlockCommonParentResidualPositiveRayNonnegativeLocalizedOutsideRatioTwoAtLength
    (n : ℕ) : Prop :=
  ∀ parent : BombieriTest,
    bombieriConjugateTest parent = parent →
      ∀ k : ℤ,
        tsupport (parent : ℝ → ℂ) ⊆
            Set.Icc (quarterLogLatticePoint (k - 1))
              (quarterLogLatticePoint (k + (n : ℤ) + 2)) →
          ¬ BombieriRatioTwoCell parent →
            0 < bombieriRealQuadraticValue
                (monotoneQuarterFiniteBlockInterior parent k n) →
              ∀ t : ℝ, 0 ≤ t →
                0 ≤ bombieriRealQuadraticValue
                  (monotoneQuarterFiniteBlock
                    (finiteBlockMiddleOrthogonalResidualPencilParent
                      parent k n t) k 0 n)

/-- The outside-ratio-two ray is equivalent to checking only parents in the
explicit surrounding plateau window.  If localization happens to shrink a
wide parent into the ratio-two cone, that fiber is discharged by the
unconditional ratio-two theorem. -/
theorem realFiniteBlockCommonParentResidualPositiveRayNonnegativeOutsideRatioTwo_iff_localized
    (n : ℕ) (hn : 3 ≤ n) :
    RealFiniteBlockCommonParentResidualPositiveRayNonnegativeOutsideRatioTwoAtLength n ↔
      RealFiniteBlockCommonParentResidualPositiveRayNonnegativeLocalizedOutsideRatioTwoAtLength
        n := by
  constructor
  · intro hall parent hparent k _hsupport hwide hMpos t ht
    exact hall parent hparent hwide k hMpos t ht
  · intro hlocal parent hparent _hwide k hMpos t ht
    let cropped : BombieriTest :=
      finiteBlockResidualParentPlateau parent k n
    have hcroppedFixed : bombieriConjugateTest cropped = cropped := by
      dsimp only [cropped]
      exact finiteBlockResidualParentPlateau_conjugate_fixed
        parent hparent k n
    have hcroppedSupport :
        tsupport (cropped : ℝ → ℂ) ⊆
          Set.Icc (quarterLogLatticePoint (k - 1))
            (quarterLogLatticePoint (k + (n : ℤ) + 2)) := by
      dsimp only [cropped]
      exact finiteBlockResidualParentPlateau_tsupport_subset parent k n
    have hinterior :
        monotoneQuarterFiniteBlockInterior cropped k n =
          monotoneQuarterFiniteBlockInterior parent k n := by
      unfold monotoneQuarterFiniteBlockInterior
      dsimp only [cropped]
      exact monotoneQuarterFiniteBlock_residualParentPlateau_eq
        parent k n 1 (n - 2) (by omega)
    have hMposCropped :
        0 < bombieriRealQuadraticValue
          (monotoneQuarterFiniteBlockInterior cropped k n) := by
      rw [hinterior]
      exact hMpos
    have hpencil :
        monotoneQuarterFiniteBlock
            (finiteBlockMiddleOrthogonalResidualPencilParent
              cropped k n t) k 0 n =
          monotoneQuarterFiniteBlock
            (finiteBlockMiddleOrthogonalResidualPencilParent
              parent k n t) k 0 n := by
      dsimp only [cropped]
      exact finiteBlock_residualPencil_parentPlateau_eq
        parent k n hn t
    by_cases hratio : BombieriRatioTwoCell cropped
    · have hnonnegative :=
        bombieriRealQuadraticValue_residualPencil_nonnegative_of_parent_ratioTwo
          cropped hratio k n hn t
      rw [hpencil] at hnonnegative
      exact hnonnegative
    · have hnonnegative := hlocal cropped hcroppedFixed k
        hcroppedSupport hratio hMposCropped t ht
      rw [hpencil] at hnonnegative
      exact hnonnegative

/-- Final quantifier shape: the full common-parent positive ray is exactly
the compact localized non-ratio-two ray above. -/
theorem realFiniteBlockCommonParentResidualPositiveRayNonnegative_iff_localizedOutsideRatioTwo
    (n : ℕ) (hn : 3 ≤ n) :
    RealFiniteBlockCommonParentResidualPositiveRayNonnegativeAtLength n ↔
      RealFiniteBlockCommonParentResidualPositiveRayNonnegativeLocalizedOutsideRatioTwoAtLength
        n := by
  exact
    (realFiniteBlockCommonParentResidualPositiveRayNonnegative_iff_outsideRatioTwo
      n hn).trans
      (realFiniteBlockCommonParentResidualPositiveRayNonnegativeOutsideRatioTwo_iff_localized
        n hn)

end

end ArithmeticHodge.Analysis.MultiplicativeWeilAllLengthResidualParentLocalizationStructural

import ArithmeticHodge.Analysis.MultiplicativeWeilAllLengthCommonParentResidualStructural

set_option autoImplicit false

open Complex Real Set
open scoped BigOperators

namespace ArithmeticHodge.Analysis.MultiplicativeWeilAllLengthPositiveRayKernelStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilAllLengthCommonParentResidualStructural
open MultiplicativeWeilMinimalNegativeBlockStructural
open MultiplicativeWeilMonotoneQuarterPartitionStructural
open MultiplicativeWeilMonotonePrimeAtomAggregateObstructionStructural
open MultiplicativeWeilQuarterLogLatticePartitionStructural
open MultiplicativeWeilRealMonotonePropagationCriterionStructural

/-!
# An unconditional support cone for the all-length positive residual ray

The common-parent residual pencil has three exact real mask coefficients

`[M, -U - t V, t M]`

on the left endpoint, complete interior, and right endpoint.  Those
coefficients may change sign, so pointwise positivity of the mask is not
available.  What *is* preserved for every real `t` is the support of the
common parent: neither the nested cutoffs nor the three-region rescaling can
create support outside the parent.

Consequently the complete residual pencil is unconditionally Bombieri
nonnegative whenever its parent already lies in a ratio-two support window.
This closes the entire real pencil on that genuine common-parent subcone,
not only its positive ray.  Any remaining all-length obstruction must
therefore use parents whose support spans multiplicative width greater than
two; it cannot be produced by the coefficient signs alone.
-/

/-- The positive-ray parent has the advertised three exact coefficients on
the actual endpoint--interior--endpoint decomposition. -/
theorem finiteBlock_residualPencil_threeRegion_coordinates
    (parent : BombieriTest) (k : ℤ) (n : ℕ) (hn : 3 ≤ n) (t : ℝ) :
    let a := monotoneQuarterCell parent k
    let m := monotoneQuarterFiniteBlockInterior parent k n
    let e := monotoneQuarterCell parent
      (k + ((n - 1 : ℕ) : ℤ))
    let M := bombieriRealQuadraticValue m
    let U := (bombieriTwoBlockGlobalCrossSymbol a m).re
    let V := (bombieriTwoBlockGlobalCrossSymbol m e).re
    monotoneQuarterFiniteBlock
        (finiteBlockMiddleOrthogonalResidualPencilParent parent k n t)
        k 0 n =
      (M : ℂ) • a + ((-U - t * V : ℝ) : ℂ) • m +
        ((t * M : ℝ) : ℂ) • e := by
  dsimp only
  unfold finiteBlockMiddleOrthogonalResidualPencilParent
  rw [finiteBlock_threeRegionRescaledParent_eq parent k n hn]

private theorem monotoneQuarterCell_tsupport_subset_parent
    (parent : BombieriTest) (k : ℤ) :
    tsupport (monotoneQuarterCell parent k : ℝ → ℂ) ⊆
      tsupport (parent : ℝ → ℂ) := by
  exact tsupport_mul_subset_right

private theorem monotoneQuarterFiniteBlock_tsupport_subset_parent
    (parent : BombieriTest) (k : ℤ) (start len : ℕ) :
    tsupport (monotoneQuarterFiniteBlock parent k start len : ℝ → ℂ) ⊆
      tsupport (parent : ℝ → ℂ) := by
  classical
  unfold monotoneQuarterFiniteBlock
  induction Finset.range len using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (tsupport_add
        (monotoneQuarterCell parent (k + ((start + i : ℕ) : ℤ)) : ℝ → ℂ)
        ((∑ j ∈ s,
          monotoneQuarterCell parent
            (k + ((start + j : ℕ) : ℤ))) : BombieriTest)).trans
        (union_subset
          (monotoneQuarterCell_tsupport_subset_parent parent _)
          ih)

private theorem tsupport_real_smul_subset
    (c : ℝ) (f : BombieriTest) :
    tsupport (((c : ℝ) : ℂ) • f : ℝ → ℂ) ⊆
      tsupport (f : ℝ → ℂ) := by
  exact tsupport_smul_subset_right
    (fun _x : ℝ ↦ (((c : ℝ) : ℂ))) (f : ℝ → ℂ)

/-- The exact `[M, -U - tV, tM]` mask never enlarges the support of its
common parent, independently of the signs of the coefficients and of the
ray parameter. -/
theorem finiteBlock_residualPencil_tsupport_subset_parent
    (parent : BombieriTest) (k : ℤ) (n : ℕ) (hn : 3 ≤ n) (t : ℝ) :
    tsupport
        (monotoneQuarterFiniteBlock
          (finiteBlockMiddleOrthogonalResidualPencilParent parent k n t)
          k 0 n : ℝ → ℂ) ⊆
      tsupport (parent : ℝ → ℂ) := by
  let a : BombieriTest := monotoneQuarterCell parent k
  let m : BombieriTest := monotoneQuarterFiniteBlockInterior parent k n
  let e : BombieriTest := monotoneQuarterCell parent
    (k + ((n - 1 : ℕ) : ℤ))
  let M : ℝ := bombieriRealQuadraticValue m
  let U : ℝ := (bombieriTwoBlockGlobalCrossSymbol a m).re
  let V : ℝ := (bombieriTwoBlockGlobalCrossSymbol m e).re
  rw [finiteBlock_residualPencil_threeRegion_coordinates
    parent k n hn t]
  change tsupport
      ((((M : ℝ) : ℂ) • a +
          (((-U - t * V : ℝ) : ℂ) • m) +
        (((t * M : ℝ) : ℂ) • e) : BombieriTest) : ℝ → ℂ) ⊆
    tsupport (parent : ℝ → ℂ)
  refine (tsupport_add _ _).trans ?_
  apply union_subset
  · refine (tsupport_add _ _).trans ?_
    apply union_subset
    · exact (tsupport_real_smul_subset M a).trans
        (monotoneQuarterCell_tsupport_subset_parent parent k)
    · exact (tsupport_real_smul_subset (-U - t * V) m).trans
        (monotoneQuarterFiniteBlock_tsupport_subset_parent
          parent k 1 (n - 2))
  · exact (tsupport_real_smul_subset (t * M) e).trans
      (monotoneQuarterCell_tsupport_subset_parent parent _)

/-- Independently of the support of the parent, the `n`-cell residual pencil
is confined to the canonical quarter-lattice window occupied by those
cells. -/
theorem finiteBlock_residualPencil_tsupport_subset_latticeWindow
    (parent : BombieriTest) (k : ℤ) (n : ℕ) (t : ℝ) :
    tsupport
        (monotoneQuarterFiniteBlock
          (finiteBlockMiddleOrthogonalResidualPencilParent parent k n t)
          k 0 n : ℝ → ℂ) ⊆
      Set.Icc (quarterLogLatticePoint k)
        (quarterLogLatticePoint (k + (n : ℤ) + 1)) := by
  simpa only [Nat.cast_zero, add_zero] using
    monotoneQuarterFiniteBlock_remotePrefix_tsupport_subset
      (finiteBlockMiddleOrthogonalResidualPencilParent parent k n t)
      k 0 n

private theorem bombieriQuadraticTest_apply_eq_zero_above_supportRatio
    (g : BombieriTest) {a b x : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a < x) :
    bombieriQuadraticTest g x = 0 := by
  by_contra hne
  have hmem := bombieriQuadraticTest_tsupport_subset_Icc
    g ha hab hsupport
    (subset_tsupport (bombieriQuadraticTest g)
      (Function.mem_support.mpr hne))
  exact (not_lt_of_ge hmem.2) hratio

private theorem vonMangoldtPrimeSummand_residualPencil_eq_zero_of_cutoff_le
    (parent : BombieriTest) (k : ℤ) (n N j : ℕ) (t : ℝ)
    (hratio :
      quarterLogLatticePoint (k + (n : ℤ) + 1) /
          quarterLogLatticePoint k < (((N + 1 : ℕ) : ℝ)))
    (hNj : N ≤ j) :
    vonMangoldtPrimeSummand
        (bombieriQuadraticTest
          (monotoneQuarterFiniteBlock
            (finiteBlockMiddleOrthogonalResidualPencilParent parent k n t)
            k 0 n)) j = 0 := by
  let g : BombieriTest :=
    monotoneQuarterFiniteBlock
      (finiteBlockMiddleOrthogonalResidualPencilParent parent k n t)
      k 0 n
  have hj : (((N + 1 : ℕ) : ℝ)) ≤ (((j + 1 : ℕ) : ℝ)) := by
    exact_mod_cast (show N + 1 ≤ j + 1 by omega)
  have hzero : bombieriQuadraticTest g (((j + 1 : ℕ) : ℝ)) = 0 := by
    apply bombieriQuadraticTest_apply_eq_zero_above_supportRatio
      g (a := quarterLogLatticePoint k)
        (b := quarterLogLatticePoint (k + (n : ℤ) + 1))
    · exact quarterLogLatticePoint_pos k
    · exact quarterLogLatticePoint_mono (by omega)
    · exact finiteBlock_residualPencil_tsupport_subset_latticeWindow
        parent k n t
    · exact hratio.trans_le hj
  unfold vonMangoldtPrimeSummand
  rw [primeKernel_bombieriQuadraticTest_eq_two_re, hzero]
  norm_num

/-- At every fixed length, the residual pencil has an *exact finite* prime
shell.  Any natural cutoff above the canonical lattice-window ratio removes
all later von-Mangoldt summands; no infinite arithmetic tail remains. -/
theorem primeSum_residualPencil_eq_finiteShell
    (parent : BombieriTest) (k : ℤ) (n N : ℕ) (t : ℝ)
    (hratio :
      quarterLogLatticePoint (k + (n : ℤ) + 1) /
          quarterLogLatticePoint k < (((N + 1 : ℕ) : ℝ))) :
    let g := monotoneQuarterFiniteBlock
      (finiteBlockMiddleOrthogonalResidualPencilParent parent k n t)
      k 0 n
    primeSum (bombieriQuadraticTest g) =
      ∑ j ∈ Finset.range N,
        vonMangoldtPrimeSummand (bombieriQuadraticTest g) j := by
  dsimp only
  rw [primeSum, tsum_eq_sum (s := Finset.range N)]
  intro j hj
  have hNj : N ≤ j := by
    simpa only [Finset.mem_range, not_lt] using hj
  exact vonMangoldtPrimeSummand_residualPencil_eq_zero_of_cutoff_le
    parent k n N j t hratio hNj

/-- The wide-support part of the positive-ray problem is exactly a finite
arithmetic domination problem: the local critical energy must dominate the
real part of the finite von-Mangoldt shell selected by the lattice window. -/
theorem bombieriRealQuadraticValue_residualPencil_nonnegative_iff_finiteShell
    (parent : BombieriTest) (k : ℤ) (n N : ℕ) (t : ℝ)
    (hratio :
      quarterLogLatticePoint (k + (n : ℤ) + 1) /
          quarterLogLatticePoint k < (((N + 1 : ℕ) : ℝ))) :
    let g := monotoneQuarterFiniteBlock
      (finiteBlockMiddleOrthogonalResidualPencilParent parent k n t)
      k 0 n
    0 ≤ bombieriRealQuadraticValue g ↔
      (∑ j ∈ Finset.range N,
          vonMangoldtPrimeSummand (bombieriQuadraticTest g) j).re ≤
        (bombieriLocalCriticalForm g g).re := by
  dsimp only
  let g : BombieriTest := monotoneQuarterFiniteBlock
    (finiteBlockMiddleOrthogonalResidualPencilParent parent k n t)
    k 0 n
  have hdecomposition := bombieriFunctional_quadratic_eq_localCritical_sub_prime g
  have hprime := primeSum_residualPencil_eq_finiteShell
    parent k n N t hratio
  change 0 ≤ (bombieriFunctional (bombieriQuadraticTest g)).re ↔ _
  rw [hdecomposition, hprime]
  simp only [Complex.sub_re]
  exact sub_nonneg

/-- Every real residual-pencil parameter is unconditionally nonnegative on
the ratio-two common-parent support cone.  The conclusion is stronger than
the positive-ray obligation: neither `0 ≤ t` nor positivity of the interior
pivot is needed. -/
theorem bombieriRealQuadraticValue_residualPencil_nonnegative_of_parent_ratioTwo
    (parent : BombieriTest) (hparentCell : BombieriRatioTwoCell parent)
    (k : ℤ) (n : ℕ) (hn : 3 ≤ n) (t : ℝ) :
    0 ≤ bombieriRealQuadraticValue
      (monotoneQuarterFiniteBlock
        (finiteBlockMiddleOrthogonalResidualPencilParent parent k n t)
        k 0 n) := by
  obtain ⟨a, b, ha, hab, hsupport, hratio⟩ := hparentCell
  unfold bombieriRealQuadraticValue
  apply bombieriFunctional_quadratic_re_nonneg_of_ratioTwoCell
  exact ⟨a, b, ha, hab,
    (finiteBlock_residualPencil_tsupport_subset_parent
      parent k n hn t).trans hsupport,
    hratio⟩

/-- Quantifier shape matching one fiber of the all-length positive-ray
certificate.  It isolates exactly what is already unconditional: every
ratio-two parent supplies the required inequality for all positive ray
parameters (indeed for every real parameter). -/
theorem commonParentPositiveRay_nonnegative_of_parent_ratioTwo
    (n : ℕ) (hn : 3 ≤ n)
    (parent : BombieriTest) (hparentCell : BombieriRatioTwoCell parent)
    (k : ℤ)
    (_hMpos : 0 < bombieriRealQuadraticValue
      (monotoneQuarterFiniteBlockInterior parent k n))
    (t : ℝ) (_ht : 0 ≤ t) :
    0 ≤ bombieriRealQuadraticValue
      (monotoneQuarterFiniteBlock
        (finiteBlockMiddleOrthogonalResidualPencilParent parent k n t)
        k 0 n) :=
  bombieriRealQuadraticValue_residualPencil_nonnegative_of_parent_ratioTwo
    parent hparentCell k n hn t

/-- The genuinely nonlocal remainder of the positive-ray certificate at one
length: the same production quantifiers, restricted only by the assertion
that the common parent is not supported in any ratio-two interval. -/
def RealFiniteBlockCommonParentResidualPositiveRayNonnegativeOutsideRatioTwoAtLength
    (n : ℕ) : Prop :=
  ∀ parent : BombieriTest,
    bombieriConjugateTest parent = parent →
      ¬ BombieriRatioTwoCell parent →
        ∀ k : ℤ,
          0 < bombieriRealQuadraticValue
              (monotoneQuarterFiniteBlockInterior parent k n) →
            ∀ t : ℝ, 0 ≤ t →
              0 ≤ bombieriRealQuadraticValue
                (monotoneQuarterFiniteBlock
                  (finiteBlockMiddleOrthogonalResidualPencilParent
                    parent k n t) k 0 n)

/-- Exact quantifier-level localization of the all-length ray.  Ratio-two
parents are already unconditional by the actual common-parent support mask,
so the full certificate is equivalent to checking only genuinely nonlocal
parents. -/
theorem realFiniteBlockCommonParentResidualPositiveRayNonnegative_iff_outsideRatioTwo
    (n : ℕ) (hn : 3 ≤ n) :
    RealFiniteBlockCommonParentResidualPositiveRayNonnegativeAtLength n ↔
      RealFiniteBlockCommonParentResidualPositiveRayNonnegativeOutsideRatioTwoAtLength
        n := by
  constructor
  · intro hall parent hparent _hwide k hMpos t ht
    exact hall parent hparent k hMpos t ht
  · intro hwide parent hparent k hMpos t ht
    by_cases hparentCell : BombieriRatioTwoCell parent
    · exact commonParentPositiveRay_nonnegative_of_parent_ratioTwo
        n hn parent hparentCell k hMpos t ht
    · exact hwide parent hparent hparentCell k hMpos t ht

/-- Sharp support obstruction to any counterexample on the positive ray (or
on the full real pencil): a negative value forces the common parent to lie
outside every ratio-two support interval.  Thus the unresolved tail is
genuinely nonlocal in multiplicative support. -/
theorem negative_residualPencil_forces_parent_not_ratioTwo
    (parent : BombieriTest) (k : ℤ) (n : ℕ) (hn : 3 ≤ n) (t : ℝ)
    (hnegative : bombieriRealQuadraticValue
      (monotoneQuarterFiniteBlock
        (finiteBlockMiddleOrthogonalResidualPencilParent parent k n t)
        k 0 n) < 0) :
    ¬ BombieriRatioTwoCell parent := by
  intro hparentCell
  have hnonnegative :=
    bombieriRealQuadraticValue_residualPencil_nonnegative_of_parent_ratioTwo
      parent hparentCell k n hn t
  exact (not_lt_of_ge hnonnegative) hnegative

end

end ArithmeticHodge.Analysis.MultiplicativeWeilAllLengthPositiveRayKernelStructural

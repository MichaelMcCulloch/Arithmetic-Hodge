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

import ArithmeticHodge.Analysis.MultiplicativeWeilMinimalFourCellBlockStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneFourCellPrimeGeometryStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneNullSuffixVariationStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilTwoSeedFactorTwo

set_option autoImplicit false

open Complex Filter Real Set TopologicalSpace
open scoped BigOperators ContDiff Distributions Topology

namespace ArithmeticHodge.Analysis.MultiplicativeWeilFourCellMixedSignObstructionStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilMinimalNegativeBlockStructural
open MultiplicativeWeilMonotoneNullSuffixVariationStructural
open MultiplicativeWeilMonotoneQuarterPartitionStructural
open MultiplicativeWeilQuarterLogLatticePartitionStructural

/-!
# The mixed four-cell inequality is odd under an endpoint sign flip

The proposed mixed closure estimate for a four-cell common-parent block is

`log 2 * Re halfCross(2) <= Re localHalfCross`.

It cannot follow merely from the fact that the two halves were cut from one
parent.  A perturbation supported at the upper endpoint is invisible to the
lower half, and its sign can therefore be reversed without changing the
lower half.  Both mixed terms are odd under that reversal.  Consequently a
universal nonnegative mixed margin would force the margin to vanish on every
such separated endpoint pair; whenever one such margin is nonzero, one of
the two parent signs is a genuine strict counterexample.
-/

/-- The first two cells of a four-cell block beginning at `k`. -/
def fourCellLowHalf (parent : BombieriTest) (k : ℤ) : BombieriTest :=
  monotoneQuarterFiniteBlock parent k 0 2

/-- The last two cells of a four-cell block beginning at `k`. -/
def fourCellHighHalf (parent : BombieriTest) (k : ℤ) : BombieriTest :=
  monotoneQuarterFiniteBlock parent k 2 2

/-- Local-minus-prime margin in the proposed mixed half-block inequality. -/
def fourCellMixedMargin (parent : BombieriTest) (k : ℤ) : ℝ :=
  (bombieriLocalCriticalForm
      (fourCellLowHalf parent k) (fourCellHighHalf parent k)).re -
    Real.log 2 *
      (bombieriQuadraticCrossTest
        (fourCellLowHalf parent k) (fourCellHighHalf parent k) 2).re

/-- The proposed mixed inequality is exactly nonnegativity of its margin. -/
theorem fourCellMixedMargin_nonnegative_iff
    (parent : BombieriTest) (k : ℤ) :
    0 <= fourCellMixedMargin parent k ↔
      Real.log 2 *
          (bombieriQuadraticCrossTest
            (fourCellLowHalf parent k) (fourCellHighHalf parent k) 2).re <=
        (bombieriLocalCriticalForm
          (fourCellLowHalf parent k) (fourCellHighHalf parent k)).re := by
  unfold fourCellMixedMargin
  exact sub_nonneg

private theorem monotoneQuarterFiniteBlock_add
    (f g : BombieriTest) (lo : ℤ) (start len : ℕ) :
    monotoneQuarterFiniteBlock (f + g) lo start len =
      monotoneQuarterFiniteBlock f lo start len +
        monotoneQuarterFiniteBlock g lo start len := by
  classical
  unfold monotoneQuarterFiniteBlock
  simp_rw [monotoneQuarterCell_add]
  exact Finset.sum_add_distrib

private theorem monotoneQuarterFiniteBlock_smul
    (c : ℂ) (f : BombieriTest) (lo : ℤ) (start len : ℕ) :
    monotoneQuarterFiniteBlock (c • f) lo start len =
      c • monotoneQuarterFiniteBlock f lo start len := by
  classical
  unfold monotoneQuarterFiniteBlock
  simp_rw [monotoneQuarterCell_smul]
  rw [Finset.smul_sum]

private theorem fourCellLowHalf_add
    (f g : BombieriTest) (k : ℤ) :
    fourCellLowHalf (f + g) k =
      fourCellLowHalf f k + fourCellLowHalf g k := by
  exact monotoneQuarterFiniteBlock_add f g k 0 2

private theorem fourCellHighHalf_add
    (f g : BombieriTest) (k : ℤ) :
    fourCellHighHalf (f + g) k =
      fourCellHighHalf f k + fourCellHighHalf g k := by
  exact monotoneQuarterFiniteBlock_add f g k 2 2

private theorem fourCellLowHalf_neg
    (f : BombieriTest) (k : ℤ) :
    fourCellLowHalf (-f) k = -fourCellLowHalf f k := by
  simpa only [neg_smul, one_smul] using
    monotoneQuarterFiniteBlock_smul (-1 : ℂ) f k 0 2

private theorem fourCellHighHalf_neg
    (f : BombieriTest) (k : ℤ) :
    fourCellHighHalf (-f) k = -fourCellHighHalf f k := by
  simpa only [neg_smul, one_smul] using
    monotoneQuarterFiniteBlock_smul (-1 : ℂ) f k 2 2

private theorem fourCellLowHalf_eq_cells
    (parent : BombieriTest) (k : ℤ) :
    fourCellLowHalf parent k =
      monotoneQuarterCell parent k +
        monotoneQuarterCell parent (k + 1) := by
  unfold fourCellLowHalf monotoneQuarterFiniteBlock
  norm_num [Finset.sum_range_succ]

private theorem fourCellHighHalf_eq_cells
    (parent : BombieriTest) (k : ℤ) :
    fourCellHighHalf parent k =
      monotoneQuarterCell parent (k + 2) +
        monotoneQuarterCell parent (k + 3) := by
  unfold fourCellHighHalf monotoneQuarterFiniteBlock
  norm_num [Finset.sum_range_succ]

private theorem monotoneQuarterCell_eq_zero_of_tsupport_le_lattice
    (parent : BombieriTest) (j : ℤ)
    (hupper : ∀ x ∈ tsupport parent, x <= quarterLogLatticePoint j) :
    monotoneQuarterCell parent j = 0 := by
  apply TestFunction.ext
  intro x
  by_cases hx : x ∈ tsupport parent
  · rw [monotoneQuarterCell_apply,
      monotoneQuarterWeight_eq_zero_of_le j (hupper x hx)]
    simp
  · have hpx : parent x = 0 := by
      by_contra hp
      exact hx (subset_tsupport parent (Function.mem_support.mpr hp))
    simp only [monotoneQuarterCell_apply, hpx, mul_zero,
      TestFunction.coe_zero, Pi.zero_apply]

private theorem monotoneQuarterCell_eq_zero_of_lattice_le_tsupport
    (parent : BombieriTest) (j : ℤ)
    (hlower : ∀ x ∈ tsupport parent,
      quarterLogLatticePoint (j + 2) <= x) :
    monotoneQuarterCell parent j = 0 := by
  apply TestFunction.ext
  intro x
  by_cases hx : x ∈ tsupport parent
  · rw [monotoneQuarterCell_apply,
      monotoneQuarterWeight_eq_zero_of_le_left j (hlower x hx)]
    simp
  · have hpx : parent x = 0 := by
      by_contra hp
      exact hx (subset_tsupport parent (Function.mem_support.mpr hp))
    simp only [monotoneQuarterCell_apply, hpx, mul_zero,
      TestFunction.coe_zero, Pi.zero_apply]

/-- A pair of parent pieces is half-separated when the lower piece is
invisible to the high half and the upper piece is invisible to the low half.
No equality between a piece and its visible masked half is required. -/
structure IsFourCellHalfSeparated
    (lower upper : BombieriTest) (k : ℤ) : Prop where
  high_lower_eq_zero : fourCellHighHalf lower k = 0
  low_upper_eq_zero : fourCellLowHalf upper k = 0

/-- One empty quarter-lattice gap between the two parent supports is enough
to make their visible halves independent. -/
theorem isFourCellHalfSeparated_of_support_gap
    (lower upper : BombieriTest) (k : ℤ)
    (hlower : tsupport lower ⊆
      Set.Iic (quarterLogLatticePoint (k + 2)))
    (hupper : tsupport upper ⊆
      Set.Ici (quarterLogLatticePoint (k + 3))) :
    IsFourCellHalfSeparated lower upper k := by
  constructor
  · rw [fourCellHighHalf_eq_cells]
    have htwo : monotoneQuarterCell lower (k + 2) = 0 :=
      monotoneQuarterCell_eq_zero_of_tsupport_le_lattice lower (k + 2)
        (fun x hx ↦ hlower hx)
    have hthree : monotoneQuarterCell lower (k + 3) = 0 :=
      monotoneQuarterCell_eq_zero_of_tsupport_le_lattice lower (k + 3)
        (fun x hx ↦ (hlower hx).trans
          (quarterLogLatticePoint_mono (by omega)))
    rw [htwo, hthree, add_zero]
  · rw [fourCellLowHalf_eq_cells]
    have hzero : monotoneQuarterCell upper k = 0 :=
      monotoneQuarterCell_eq_zero_of_lattice_le_tsupport upper k
        (fun x hx ↦
          (quarterLogLatticePoint_mono (m := k + 2) (n := k + 3)
            (by omega)).trans (hupper hx))
    have hone : monotoneQuarterCell upper (k + 1) = 0 :=
      monotoneQuarterCell_eq_zero_of_lattice_le_tsupport upper (k + 1)
        (fun x hx ↦ by simpa only [add_assoc] using hupper hx)
    rw [hzero, hone, add_zero]

/-- In particular, localization in the first and last transition regions of
the four-cell band gives an independently sign-flippable parent pair. -/
theorem isFourCellHalfSeparated_of_endpoint_localization
    (lower upper : BombieriTest) (k : ℤ)
    (hlower : tsupport lower ⊆ Set.Icc
      (quarterLogLatticePoint k) (quarterLogLatticePoint (k + 1)))
    (hupper : tsupport upper ⊆ Set.Icc
      (quarterLogLatticePoint (k + 4))
      (quarterLogLatticePoint (k + 5))) :
    IsFourCellHalfSeparated lower upper k := by
  apply isFourCellHalfSeparated_of_support_gap lower upper k
  · intro x hx
    exact (hlower hx).2.trans (quarterLogLatticePoint_mono (by omega))
  · intro x hx
    exact (quarterLogLatticePoint_mono (by omega)).trans (hupper hx).1

private theorem exists_bombieri_bump_at
    (c : ℝ) (U : Set ℝ) (hU : U ∈ 𝓝 c) (hUpos : U ⊆ Ioi 0) :
    ∃ eta : BombieriTest,
      eta c = 1 ∧ tsupport (eta : ℝ → ℂ) ⊆ U ∧
        bombieriConjugateTest eta = eta := by
  obtain ⟨phi, hphiSupport, hphiCompact, hphiSmooth, _hphiRange, hphiOne⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) hU
  have hsmooth : ContDiff ℝ ∞ (fun x : ℝ ↦ (phi x : ℂ)) := by
    exact Complex.ofRealCLM.contDiff.comp hphiSmooth
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
  refine ⟨eta, ?_, ?_, ?_⟩
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

/-- The separated endpoint geometry is genuinely realizable by two nonzero
smooth Bombieri parents, not merely a formal kernel hypothesis. -/
theorem exists_nonzero_endpoint_localized_halfSeparated_pair (k : ℤ) :
    ∃ lower upper : BombieriTest,
      lower ≠ 0 ∧ upper ≠ 0 ∧
      bombieriConjugateTest lower = lower ∧
      bombieriConjugateTest upper = upper ∧
      tsupport lower ⊆ Set.Ioo
        (quarterLogLatticePoint k) (quarterLogLatticePoint (k + 1)) ∧
      tsupport upper ⊆ Set.Ioo
        (quarterLogLatticePoint (k + 4))
        (quarterLogLatticePoint (k + 5)) ∧
      IsFourCellHalfSeparated lower upper k := by
  let a₀ := quarterLogLatticePoint k
  let b₀ := quarterLogLatticePoint (k + 1)
  let c₀ := (a₀ + b₀) / 2
  have hab₀ : a₀ < b₀ := quarterLogLatticePoint_strictMono (by omega)
  have hac₀ : a₀ < c₀ := by dsimp only [c₀]; linarith
  have hcb₀ : c₀ < b₀ := by dsimp only [c₀]; linarith
  have hpos₀ : Set.Ioo a₀ b₀ ⊆ Ioi 0 := by
    intro x hx
    exact (quarterLogLatticePoint_pos k).trans hx.1
  obtain ⟨lower, hlowerOne, hlowerSupport, hlowerFixed⟩ :=
    exists_bombieri_bump_at
    c₀ (Set.Ioo a₀ b₀) (Ioo_mem_nhds hac₀ hcb₀) hpos₀
  let a₁ := quarterLogLatticePoint (k + 4)
  let b₁ := quarterLogLatticePoint (k + 5)
  let c₁ := (a₁ + b₁) / 2
  have hab₁ : a₁ < b₁ := quarterLogLatticePoint_strictMono (by omega)
  have hac₁ : a₁ < c₁ := by dsimp only [c₁]; linarith
  have hcb₁ : c₁ < b₁ := by dsimp only [c₁]; linarith
  have hpos₁ : Set.Ioo a₁ b₁ ⊆ Ioi 0 := by
    intro x hx
    exact (quarterLogLatticePoint_pos (k + 4)).trans hx.1
  obtain ⟨upper, hupperOne, hupperSupport, hupperFixed⟩ :=
    exists_bombieri_bump_at
    c₁ (Set.Ioo a₁ b₁) (Ioo_mem_nhds hac₁ hcb₁) hpos₁
  have hlowerNe : lower ≠ 0 := by
    intro hzero
    have happly := congrArg (fun f : BombieriTest ↦ f c₀) hzero
    have : lower c₀ = 0 := by simpa using happly
    rw [hlowerOne] at this
    norm_num at this
  have hupperNe : upper ≠ 0 := by
    intro hzero
    have happly := congrArg (fun f : BombieriTest ↦ f c₁) hzero
    have : upper c₁ = 0 := by simpa using happly
    rw [hupperOne] at this
    norm_num at this
  refine ⟨lower, upper, hlowerNe, hupperNe, hlowerFixed, hupperFixed,
    hlowerSupport, hupperSupport, ?_⟩
  apply isFourCellHalfSeparated_of_endpoint_localization lower upper k
  · exact hlowerSupport.trans Set.Ioo_subset_Icc_self
  · exact hupperSupport.trans Set.Ioo_subset_Icc_self

private theorem lowHalf_add_of_halfSeparated
    {lower upper : BombieriTest} {k : ℤ}
    (hsep : IsFourCellHalfSeparated lower upper k) :
    fourCellLowHalf (lower + upper) k = fourCellLowHalf lower k := by
  rw [fourCellLowHalf_add, hsep.low_upper_eq_zero, add_zero]

private theorem highHalf_add_of_halfSeparated
    {lower upper : BombieriTest} {k : ℤ}
    (hsep : IsFourCellHalfSeparated lower upper k) :
    fourCellHighHalf (lower + upper) k = fourCellHighHalf upper k := by
  rw [fourCellHighHalf_add, hsep.high_lower_eq_zero, zero_add]

private theorem lowHalf_sub_of_halfSeparated
    {lower upper : BombieriTest} {k : ℤ}
    (hsep : IsFourCellHalfSeparated lower upper k) :
    fourCellLowHalf (lower - upper) k = fourCellLowHalf lower k := by
  rw [sub_eq_add_neg, fourCellLowHalf_add, fourCellLowHalf_neg,
    hsep.low_upper_eq_zero, neg_zero, add_zero]

private theorem highHalf_sub_of_halfSeparated
    {lower upper : BombieriTest} {k : ℤ}
    (hsep : IsFourCellHalfSeparated lower upper k) :
    fourCellHighHalf (lower - upper) k = -fourCellHighHalf upper k := by
  rw [sub_eq_add_neg, fourCellHighHalf_add, fourCellHighHalf_neg,
    hsep.high_lower_eq_zero, zero_add]

private theorem bombieriQuadraticCrossTest_neg_right
    (f g : BombieriTest) :
    bombieriQuadraticCrossTest f (-g) =
      -bombieriQuadraticCrossTest f g := by
  have h := bombieriQuadraticCrossTest_smul_eq_re_im_polarization
    f g (-1 : ℂ)
  norm_num at h
  simpa using h

/-- The local half-cross itself reverses under the upper endpoint sign flip. -/
theorem localHalfCross_sub_eq_neg_add
    {lower upper : BombieriTest} {k : ℤ}
    (hsep : IsFourCellHalfSeparated lower upper k) :
    (bombieriLocalCriticalForm
        (fourCellLowHalf (lower - upper) k)
        (fourCellHighHalf (lower - upper) k)).re =
      -(bombieriLocalCriticalForm
        (fourCellLowHalf (lower + upper) k)
        (fourCellHighHalf (lower + upper) k)).re := by
  rw [lowHalf_sub_of_halfSeparated hsep,
    highHalf_sub_of_halfSeparated hsep,
    lowHalf_add_of_halfSeparated hsep,
    highHalf_add_of_halfSeparated hsep, map_neg]
  exact Complex.neg_re _

/-- The surviving factor-two half-cross reverses under the same endpoint
sign flip. -/
theorem primeHalfCross_sub_eq_neg_add
    {lower upper : BombieriTest} {k : ℤ}
    (hsep : IsFourCellHalfSeparated lower upper k) :
    (bombieriQuadraticCrossTest
        (fourCellLowHalf (lower - upper) k)
        (fourCellHighHalf (lower - upper) k) 2).re =
      -(bombieriQuadraticCrossTest
        (fourCellLowHalf (lower + upper) k)
        (fourCellHighHalf (lower + upper) k) 2).re := by
  rw [lowHalf_sub_of_halfSeparated hsep,
    highHalf_sub_of_halfSeparated hsep,
    lowHalf_add_of_halfSeparated hsep,
    highHalf_add_of_halfSeparated hsep,
    bombieriQuadraticCrossTest_neg_right]
  simp only [TestFunction.coe_neg, Pi.neg_apply, Complex.neg_re]

/-- In contrast, both local diagonal reserves are unchanged by the endpoint
sign flip. -/
theorem halfLocalDiagonals_sub_eq_add
    {lower upper : BombieriTest} {k : ℤ}
    (hsep : IsFourCellHalfSeparated lower upper k) :
    (bombieriLocalCriticalForm
        (fourCellLowHalf (lower - upper) k)
        (fourCellLowHalf (lower - upper) k)).re =
      (bombieriLocalCriticalForm
        (fourCellLowHalf (lower + upper) k)
        (fourCellLowHalf (lower + upper) k)).re ∧
    (bombieriLocalCriticalForm
        (fourCellHighHalf (lower - upper) k)
        (fourCellHighHalf (lower - upper) k)).re =
      (bombieriLocalCriticalForm
        (fourCellHighHalf (lower + upper) k)
        (fourCellHighHalf (lower + upper) k)).re := by
  constructor
  · rw [lowHalf_sub_of_halfSeparated hsep,
      lowHalf_add_of_halfSeparated hsep]
  · rw [highHalf_sub_of_halfSeparated hsep,
      highHalf_add_of_halfSeparated hsep]
    simp only [map_neg, LinearMap.neg_apply, neg_neg]

/-- Exact oddness: independently flipping the upper endpoint reverses the
entire mixed local-minus-prime margin. -/
theorem fourCellMixedMargin_sub_eq_neg_add
    {lower upper : BombieriTest} {k : ℤ}
    (hsep : IsFourCellHalfSeparated lower upper k) :
    fourCellMixedMargin (lower - upper) k =
      -fourCellMixedMargin (lower + upper) k := by
  rw [fourCellMixedMargin, fourCellMixedMargin,
    lowHalf_sub_of_halfSeparated hsep,
    highHalf_sub_of_halfSeparated hsep,
    lowHalf_add_of_halfSeparated hsep,
    highHalf_add_of_halfSeparated hsep,
    map_neg, bombieriQuadraticCrossTest_neg_right]
  simp only [TestFunction.coe_neg, Pi.neg_apply, Complex.neg_re]
  ring

private theorem conjugate_fixed_add
    {f g : BombieriTest}
    (hf : bombieriConjugateTest f = f)
    (hg : bombieriConjugateTest g = g) :
    bombieriConjugateTest (f + g) = f + g := by
  rw [bombieriConjugateTest_add, hf, hg]

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

/-- If the separated mixed margin is nonzero, one of the two honest
common-parent sign choices strictly violates the proposed mixed inequality. -/
theorem one_endpoint_sign_strictly_violates_mixed_inequality
    {lower upper : BombieriTest} {k : ℤ}
    (hsep : IsFourCellHalfSeparated lower upper k)
    (hne : fourCellMixedMargin (lower + upper) k ≠ 0) :
    ¬ (Real.log 2 *
          (bombieriQuadraticCrossTest
            (fourCellLowHalf (lower + upper) k)
            (fourCellHighHalf (lower + upper) k) 2).re <=
        (bombieriLocalCriticalForm
          (fourCellLowHalf (lower + upper) k)
          (fourCellHighHalf (lower + upper) k)).re) ∨
      ¬ (Real.log 2 *
          (bombieriQuadraticCrossTest
            (fourCellLowHalf (lower - upper) k)
            (fourCellHighHalf (lower - upper) k) 2).re <=
        (bombieriLocalCriticalForm
          (fourCellLowHalf (lower - upper) k)
          (fourCellHighHalf (lower - upper) k)).re) := by
  rw [← fourCellMixedMargin_nonnegative_iff,
    ← fourCellMixedMargin_nonnegative_iff]
  rw [fourCellMixedMargin_sub_eq_neg_add hsep]
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · exact Or.inl (not_le_of_gt hneg)
  · exact Or.inr (not_le_of_gt (neg_lt_zero.mpr hpos))

/-- The same obstruction stays entirely inside the conjugation-fixed class
which suffices for the real RH reduction. -/
theorem one_real_endpoint_sign_strictly_violates_mixed_inequality
    {lower upper : BombieriTest} {k : ℤ}
    (hlowerFixed : bombieriConjugateTest lower = lower)
    (hupperFixed : bombieriConjugateTest upper = upper)
    (hsep : IsFourCellHalfSeparated lower upper k)
    (hne : fourCellMixedMargin (lower + upper) k ≠ 0) :
    (bombieriConjugateTest (lower + upper) = lower + upper ∧
      ¬ (Real.log 2 *
          (bombieriQuadraticCrossTest
            (fourCellLowHalf (lower + upper) k)
            (fourCellHighHalf (lower + upper) k) 2).re <=
        (bombieriLocalCriticalForm
          (fourCellLowHalf (lower + upper) k)
          (fourCellHighHalf (lower + upper) k)).re)) ∨
    (bombieriConjugateTest (lower - upper) = lower - upper ∧
      ¬ (Real.log 2 *
          (bombieriQuadraticCrossTest
            (fourCellLowHalf (lower - upper) k)
            (fourCellHighHalf (lower - upper) k) 2).re <=
        (bombieriLocalCriticalForm
          (fourCellLowHalf (lower - upper) k)
          (fourCellHighHalf (lower - upper) k)).re)) := by
  have hfailure := one_endpoint_sign_strictly_violates_mixed_inequality
    hsep hne
  rcases hfailure with hplus | hminus
  · exact Or.inl ⟨conjugate_fixed_add hlowerFixed hupperFixed, hplus⟩
  · exact Or.inr ⟨conjugate_fixed_sub hlowerFixed hupperFixed, hminus⟩

/-- Thus a universal mixed inequality would force exact zero, rather than a
positive margin, on every independently sign-flippable endpoint pair. -/
theorem universal_mixed_inequality_forces_separated_margin_zero
    (hall : ∀ parent : BombieriTest, ∀ k : ℤ,
      Real.log 2 *
          (bombieriQuadraticCrossTest
            (fourCellLowHalf parent k) (fourCellHighHalf parent k) 2).re <=
        (bombieriLocalCriticalForm
          (fourCellLowHalf parent k) (fourCellHighHalf parent k)).re)
    {lower upper : BombieriTest} {k : ℤ}
    (hsep : IsFourCellHalfSeparated lower upper k) :
    fourCellMixedMargin (lower + upper) k = 0 := by
  have hplus : 0 <= fourCellMixedMargin (lower + upper) k :=
    (fourCellMixedMargin_nonnegative_iff (lower + upper) k).2
      (hall (lower + upper) k)
  have hminus : 0 <= fourCellMixedMargin (lower - upper) k :=
    (fourCellMixedMargin_nonnegative_iff (lower - upper) k).2
      (hall (lower - upper) k)
  rw [fourCellMixedMargin_sub_eq_neg_add hsep] at hminus
  linarith

/-- Even if the proposed universal estimate is restricted to real-valued
parents, it still forces exact vanishing on every real separated pair. -/
theorem universal_real_mixed_inequality_forces_separated_margin_zero
    (hall : ∀ parent : BombieriTest,
      bombieriConjugateTest parent = parent → ∀ k : ℤ,
        Real.log 2 *
            (bombieriQuadraticCrossTest
              (fourCellLowHalf parent k) (fourCellHighHalf parent k) 2).re <=
          (bombieriLocalCriticalForm
            (fourCellLowHalf parent k) (fourCellHighHalf parent k)).re)
    {lower upper : BombieriTest} {k : ℤ}
    (hlowerFixed : bombieriConjugateTest lower = lower)
    (hupperFixed : bombieriConjugateTest upper = upper)
    (hsep : IsFourCellHalfSeparated lower upper k) :
    fourCellMixedMargin (lower + upper) k = 0 := by
  have hplusFixed : bombieriConjugateTest (lower + upper) = lower + upper :=
    conjugate_fixed_add hlowerFixed hupperFixed
  have hminusFixed : bombieriConjugateTest (lower - upper) = lower - upper :=
    conjugate_fixed_sub hlowerFixed hupperFixed
  have hplus : 0 <= fourCellMixedMargin (lower + upper) k :=
    (fourCellMixedMargin_nonnegative_iff (lower + upper) k).2
      (hall (lower + upper) hplusFixed k)
  have hminus : 0 <= fourCellMixedMargin (lower - upper) k :=
    (fourCellMixedMargin_nonnegative_iff (lower - upper) k).2
      (hall (lower - upper) hminusFixed k)
  rw [fourCellMixedMargin_sub_eq_neg_add hsep] at hminus
  linarith

end


end ArithmeticHodge.Analysis.MultiplicativeWeilFourCellMixedSignObstructionStructural

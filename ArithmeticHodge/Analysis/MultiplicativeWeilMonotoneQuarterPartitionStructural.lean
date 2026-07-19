import ArithmeticHodge.Analysis.MultiplicativeWeilQuarterLogLatticeCoherentAggregationStructural
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

set_option autoImplicit false

open Complex Real Set
open scoped BigOperators ContDiff

namespace ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneQuarterPartitionStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilQuarterLogLatticePartitionStructural
open MultiplicativeWeilQuarterLogLatticeCoherentAggregationStructural

/-!
# An explicit monotone quarter-lattice partition

The abstract smooth partition of unity used by the existing coherent
decomposition need not make its cumulative suffix weights monotone.  Here the
weights are instead differences of consecutive smooth steps.  They are
nonnegative, supported on exactly two quarter-lattice intervals, and every
finite consecutive sum telescopes to the difference of its two boundary
steps.  In particular, once the outer steps lie beyond the parent support,
every whole suffix is a single monotone cutoff.
-/

theorem quarterLogLatticePoint_strictMono {m n : ℤ} (hmn : m < n) :
    quarterLogLatticePoint m < quarterLogLatticePoint n := by
  unfold quarterLogLatticePoint
  apply Real.exp_lt_exp.mpr
  apply mul_lt_mul_of_pos_right
  · exact_mod_cast hmn
  · positivity

theorem quarterLogLatticePoint_gap_pos (k : ℤ) :
    0 < quarterLogLatticePoint (k + 1) - quarterLogLatticePoint k := by
  exact sub_pos.mpr (quarterLogLatticePoint_strictMono (by omega))

/-- A smooth increasing step across one quarter-lattice interval. -/
def monotoneQuarterStep (k : ℤ) (x : ℝ) : ℝ :=
  Real.smoothTransition
    ((x - quarterLogLatticePoint k) /
      (quarterLogLatticePoint (k + 1) - quarterLogLatticePoint k))

theorem monotoneQuarterStep_contDiff (k : ℤ) :
    ContDiff ℝ ∞ (monotoneQuarterStep k) := by
  unfold monotoneQuarterStep
  apply Real.smoothTransition.contDiff.comp
  fun_prop

theorem monotoneQuarterStep_monotone (k : ℤ) :
    Monotone (monotoneQuarterStep k) := by
  intro x y hxy
  apply Real.smoothTransition.monotone
  apply div_le_div_of_nonneg_right
  · exact sub_le_sub_right hxy _
  · exact (quarterLogLatticePoint_gap_pos k).le

theorem monotoneQuarterStep_nonneg (k : ℤ) (x : ℝ) :
    0 ≤ monotoneQuarterStep k x :=
  Real.smoothTransition.nonneg _

theorem monotoneQuarterStep_le_one (k : ℤ) (x : ℝ) :
    monotoneQuarterStep k x ≤ 1 :=
  Real.smoothTransition.le_one _

theorem monotoneQuarterStep_eq_zero_of_le
    (k : ℤ) {x : ℝ} (hx : x ≤ quarterLogLatticePoint k) :
    monotoneQuarterStep k x = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx)
    (quarterLogLatticePoint_gap_pos k).le

theorem monotoneQuarterStep_eq_one_of_le
    (k : ℤ) {x : ℝ} (hx : quarterLogLatticePoint (k + 1) ≤ x) :
    monotoneQuarterStep k x = 1 := by
  apply Real.smoothTransition.one_of_one_le
  rw [le_div_iff₀ (quarterLogLatticePoint_gap_pos k)]
  linarith

/-- The canonical cell weight is the difference of two consecutive steps. -/
def monotoneQuarterWeight (k : ℤ) (x : ℝ) : ℝ :=
  monotoneQuarterStep k x - monotoneQuarterStep (k + 1) x

theorem monotoneQuarterWeight_contDiff (k : ℤ) :
    ContDiff ℝ ∞ (monotoneQuarterWeight k) := by
  exact (monotoneQuarterStep_contDiff k).sub
    (monotoneQuarterStep_contDiff (k + 1))

theorem monotoneQuarterWeight_nonnegative (k : ℤ) (x : ℝ) :
    0 ≤ monotoneQuarterWeight k x := by
  unfold monotoneQuarterWeight
  by_cases hx : x ≤ quarterLogLatticePoint (k + 1)
  · rw [monotoneQuarterStep_eq_zero_of_le (k + 1) hx]
    simpa only [sub_zero] using monotoneQuarterStep_nonneg k x
  · have hx' : quarterLogLatticePoint (k + 1) ≤ x := le_of_not_ge hx
    rw [monotoneQuarterStep_eq_one_of_le k hx']
    exact sub_nonneg.mpr (monotoneQuarterStep_le_one (k + 1) x)

/-- Consecutive boundary steps are nested pointwise. -/
theorem monotoneQuarterStep_succ_le (k : ℤ) (x : ℝ) :
    monotoneQuarterStep (k + 1) x ≤ monotoneQuarterStep k x := by
  exact sub_nonneg.mp (monotoneQuarterWeight_nonnegative k x)

theorem monotoneQuarterWeight_eq_zero_of_le
    (k : ℤ) {x : ℝ} (hx : x ≤ quarterLogLatticePoint k) :
    monotoneQuarterWeight k x = 0 := by
  unfold monotoneQuarterWeight
  rw [monotoneQuarterStep_eq_zero_of_le k hx,
    monotoneQuarterStep_eq_zero_of_le (k + 1)
      (hx.trans (quarterLogLatticePoint_mono (by omega)))]
  ring

theorem monotoneQuarterWeight_eq_zero_of_le_left
    (k : ℤ) {x : ℝ} (hx : quarterLogLatticePoint (k + 2) ≤ x) :
    monotoneQuarterWeight k x = 0 := by
  unfold monotoneQuarterWeight
  rw [monotoneQuarterStep_eq_one_of_le k
      ((quarterLogLatticePoint_mono (by omega)).trans hx),
    monotoneQuarterStep_eq_one_of_le (k + 1) (by simpa only [add_assoc] using hx)]
  ring

theorem monotoneQuarterWeight_tsupport_subset (k : ℤ) :
    tsupport (monotoneQuarterWeight k) ⊆
      Set.Icc (quarterLogLatticePoint k) (quarterLogLatticePoint (k + 2)) := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  by_cases hlo : quarterLogLatticePoint k ≤ x
  · refine ⟨hlo, ?_⟩
    by_contra hhi
    exact hx (monotoneQuarterWeight_eq_zero_of_le_left k (le_of_not_ge hhi))
  · exact (hx (monotoneQuarterWeight_eq_zero_of_le k (le_of_not_ge hlo))).elim

/-- Consecutive canonical weights telescope exactly to two boundary steps. -/
theorem sum_range_monotoneQuarterWeight
    (lo : ℤ) (n : ℕ) (x : ℝ) :
    (∑ i ∈ Finset.range n,
        monotoneQuarterWeight (lo + (i : ℤ)) x) =
      monotoneQuarterStep lo x -
        monotoneQuarterStep (lo + (n : ℤ)) x := by
  simpa [monotoneQuarterWeight, add_assoc] using
    (Finset.sum_range_sub'
      (fun i : ℕ ↦ monotoneQuarterStep (lo + (i : ℤ)) x) n)

/-- The canonical physical cell cut from a common parent. -/
def monotoneQuarterCell (parent : BombieriTest) (k : ℤ) : BombieriTest :=
  TestFunction.mk
    (fun x : ℝ ↦ ((monotoneQuarterWeight k x : ℝ) : ℂ) * parent x)
    ((Complex.ofRealCLM.contDiff.comp (monotoneQuarterWeight_contDiff k)).mul
      parent.contDiff)
    parent.hasCompactSupport.mul_left
    ((tsupport_mul_subset_right :
      tsupport (fun x : ℝ ↦ ((monotoneQuarterWeight k x : ℝ) : ℂ) * parent x) ⊆
        tsupport parent).trans parent.tsupport_subset)

@[simp] theorem monotoneQuarterCell_apply
    (parent : BombieriTest) (k : ℤ) (x : ℝ) :
    monotoneQuarterCell parent k x =
      (monotoneQuarterWeight k x : ℂ) * parent x := rfl

/-- The common parent multiplied by one monotone boundary step. -/
def monotoneQuarterCutoff (parent : BombieriTest) (k : ℤ) : BombieriTest :=
  TestFunction.mk
    (fun x : ℝ ↦ ((monotoneQuarterStep k x : ℝ) : ℂ) * parent x)
    ((Complex.ofRealCLM.contDiff.comp (monotoneQuarterStep_contDiff k)).mul
      parent.contDiff)
    parent.hasCompactSupport.mul_left
    ((tsupport_mul_subset_right :
      tsupport (fun x : ℝ ↦ ((monotoneQuarterStep k x : ℝ) : ℂ) * parent x) ⊆
        tsupport parent).trans parent.tsupport_subset)

@[simp] theorem monotoneQuarterCutoff_apply
    (parent : BombieriTest) (k : ℤ) (x : ℝ) :
    monotoneQuarterCutoff parent k x =
      (monotoneQuarterStep k x : ℂ) * parent x := rfl

theorem monotoneQuarterCutoff_eq_zero_of_tsupport_le
    (parent : BombieriTest) (k : ℤ)
    (hupper : ∀ x ∈ tsupport parent, x ≤ quarterLogLatticePoint k) :
    monotoneQuarterCutoff parent k = 0 := by
  apply TestFunction.ext
  intro x
  by_cases hx : x ∈ tsupport parent
  · rw [monotoneQuarterCutoff_apply,
      monotoneQuarterStep_eq_zero_of_le k (hupper x hx)]
    simp
  · have hpx : parent x = 0 := by
      by_contra hp
      exact hx (subset_tsupport parent (Function.mem_support.mpr hp))
    change (monotoneQuarterStep k x : ℂ) * parent x = 0
    rw [hpx, mul_zero]

theorem monotoneQuarterCutoff_eq_parent_of_lattice_le_tsupport
    (parent : BombieriTest) (k : ℤ)
    (hlower : ∀ x ∈ tsupport parent,
      quarterLogLatticePoint (k + 1) ≤ x) :
    monotoneQuarterCutoff parent k = parent := by
  apply TestFunction.ext
  intro x
  by_cases hx : x ∈ tsupport parent
  · rw [monotoneQuarterCutoff_apply,
      monotoneQuarterStep_eq_one_of_le k (hlower x hx)]
    simp
  · have hpx : parent x = 0 := by
      by_contra hp
      exact hx (subset_tsupport parent (Function.mem_support.mpr hp))
    simp only [monotoneQuarterCutoff_apply, hpx, mul_zero]

/-- The physical cells telescope at the level of bundled Bombieri tests. -/
theorem sum_range_monotoneQuarterCell_eq_cutoff_sub
    (parent : BombieriTest) (lo : ℤ) (n : ℕ) :
    (∑ i ∈ Finset.range n,
        monotoneQuarterCell parent (lo + (i : ℤ))) =
      monotoneQuarterCutoff parent lo -
        monotoneQuarterCutoff parent (lo + (n : ℤ)) := by
  apply TestFunction.ext
  intro x
  let ev : BombieriTest →+ ℂ :=
    { toFun := fun f ↦ f x
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  change ev (∑ i ∈ Finset.range n,
      monotoneQuarterCell parent (lo + (i : ℤ))) =
    ev (monotoneQuarterCutoff parent lo -
      monotoneQuarterCutoff parent (lo + (n : ℤ)))
  rw [map_sum]
  change (∑ i ∈ Finset.range n,
      (monotoneQuarterWeight (lo + (i : ℤ)) x : ℂ) * parent x) =
    (monotoneQuarterStep lo x : ℂ) * parent x -
      (monotoneQuarterStep (lo + (n : ℤ)) x : ℂ) * parent x
  rw [← Finset.sum_mul, ← Complex.ofReal_sum,
    sum_range_monotoneQuarterWeight]
  push_cast
  ring

/-- One cell is exactly the difference of its two nested boundary cutoffs. -/
theorem monotoneQuarterCell_eq_cutoff_sub
    (parent : BombieriTest) (k : ℤ) :
    monotoneQuarterCell parent k =
      monotoneQuarterCutoff parent k -
        monotoneQuarterCutoff parent (k + 1) := by
  simpa using sum_range_monotoneQuarterCell_eq_cutoff_sub parent k 1

/-- A head plus a scalar multiple of its whole monotone suffix is a pencil in
two nested cutoffs of the same parent. -/
theorem monotoneQuarterCell_add_smul_cutoff_eq_nestedCutoffs
    (parent : BombieriTest) (k : ℤ) (c : ℂ) :
    monotoneQuarterCell parent k +
        c • monotoneQuarterCutoff parent (k + 1) =
      monotoneQuarterCutoff parent k +
        (c - 1) • monotoneQuarterCutoff parent (k + 1) := by
  rw [monotoneQuarterCell_eq_cutoff_sub]
  apply TestFunction.ext
  intro x
  simp only [TestFunction.coe_add, Pi.add_apply, TestFunction.coe_sub,
    Pi.sub_apply, TestFunction.coe_smul, Pi.smul_apply, smul_eq_mul]
  ring

/-- Starting at an internal cut and summing through the right endpoint gives
the difference of the internal and terminal monotone cutoffs. -/
theorem monotoneQuarterCell_suffix_eq_cutoff_sub
    (parent : BombieriTest) (lo : ℤ) {j n : ℕ} (hjn : j ≤ n) :
    (∑ i ∈ Finset.range (n - j),
        monotoneQuarterCell parent (lo + (j : ℤ) + (i : ℤ))) =
      monotoneQuarterCutoff parent (lo + (j : ℤ)) -
        monotoneQuarterCutoff parent (lo + (n : ℤ)) := by
  have h := sum_range_monotoneQuarterCell_eq_cutoff_sub
    parent (lo + (j : ℤ)) (n - j)
  have hindex :
      (lo + (j : ℤ)) + ((n - j : ℕ) : ℤ) = lo + (n : ℤ) := by
    rw [Nat.cast_sub hjn]
    omega
  simpa only [hindex] using h

/-- At every internal cut of a finite monotone decomposition, the selected
head--whole-suffix pencil is exactly a two-nested-cutoff pencil. -/
theorem monotoneQuarterCutPencil_eq_nestedCutoffs
    (parent : BombieriTest) (lo : ℤ) (n j : ℕ) (hj : j < n)
    (hright : monotoneQuarterCutoff parent (lo + (n : ℤ)) = 0)
    (c : ℂ) :
    monotoneQuarterCell parent (lo + (j : ℤ)) +
        c • (∑ i ∈ Finset.range (n - (j + 1)),
          monotoneQuarterCell parent
            (lo + ((j + 1 : ℕ) : ℤ) + (i : ℤ))) =
      monotoneQuarterCutoff parent (lo + (j : ℤ)) +
        (c - 1) • monotoneQuarterCutoff parent
          (lo + ((j + 1 : ℕ) : ℤ)) := by
  have hsucc : j + 1 ≤ n := by omega
  rw [monotoneQuarterCell_suffix_eq_cutoff_sub parent lo hsucc,
    hright, sub_zero]
  have hindex : lo + ((j + 1 : ℕ) : ℤ) = lo + (j : ℤ) + 1 := by
    norm_num
    ring
  rw [hindex]
  exact monotoneQuarterCell_add_smul_cutoff_eq_nestedCutoffs
    parent (lo + (j : ℤ)) c

theorem monotoneQuarterCell_tsupport_subset
    (parent : BombieriTest) (k : ℤ) :
    tsupport (monotoneQuarterCell parent k) ⊆
      Set.Icc (quarterLogLatticePoint k) (quarterLogLatticePoint (k + 2)) := by
  have hcoe :
      tsupport (fun x : ℝ ↦ ((monotoneQuarterWeight k x : ℝ) : ℂ)) =
        tsupport (monotoneQuarterWeight k) := by
    unfold tsupport
    congr 1
    ext x
    simp only [Function.mem_support, ne_eq, Complex.ofReal_eq_zero]
  exact (tsupport_mul_subset_left :
    tsupport (fun x : ℝ ↦
      ((monotoneQuarterWeight k x : ℝ) : ℂ) * parent x) ⊆
        tsupport (fun x : ℝ ↦ ((monotoneQuarterWeight k x : ℝ) : ℂ))).trans
    (hcoe ▸ monotoneQuarterWeight_tsupport_subset k)

theorem monotoneQuarterCell_ratioTwo
    (parent : BombieriTest) (k : ℤ) :
    BombieriRatioTwoCell (monotoneQuarterCell parent k) := by
  refine ⟨quarterLogLatticePoint k, quarterLogLatticePoint (k + 2),
    quarterLogLatticePoint_pos k, quarterLogLatticePoint_mono (by omega),
    monotoneQuarterCell_tsupport_subset parent k, ?_⟩
  rw [quarterLogLatticePoint_add_two,
    mul_div_cancel_right₀ _ (quarterLogLatticePoint_pos k).ne']
  calc
    quarterLogLatticePoint 2 ≤ quarterLogLatticePoint 4 :=
      quarterLogLatticePoint_mono (by omega)
    _ = 2 := quarterLogLatticePoint_four

private theorem tsupport_finset_sum_subset_Icc
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → BombieriTest) (a b : ℝ)
    (hf : ∀ i ∈ s, tsupport (f i) ⊆ Set.Icc a b) :
    tsupport (((∑ i ∈ s, f i) : BombieriTest) : ℝ → ℂ) ⊆ Set.Icc a b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (tsupport_add (f i : ℝ → ℂ) (∑ j ∈ s, f j : BombieriTest)).trans
        (union_subset (hf i (by simp))
          (ih (fun j hj ↦ hf j (by simp [hj]))))

theorem sum_range_monotoneQuarterCell_eq_parent
    (parent : BombieriTest) (lo : ℤ) (n : ℕ)
    (hleft : ∀ x ∈ tsupport parent, monotoneQuarterStep lo x = 1)
    (hright : ∀ x ∈ tsupport parent,
      monotoneQuarterStep (lo + (n : ℤ)) x = 0) :
    (∑ i ∈ Finset.range n,
        monotoneQuarterCell parent (lo + (i : ℤ))) = parent := by
  apply TestFunction.ext
  intro x
  let ev : BombieriTest →+ ℂ :=
    { toFun := fun f ↦ f x
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  change ev (∑ i ∈ Finset.range n,
      monotoneQuarterCell parent (lo + (i : ℤ))) = ev parent
  rw [map_sum]
  change (∑ i ∈ Finset.range n,
      (monotoneQuarterWeight (lo + (i : ℤ)) x : ℂ) * parent x) = parent x
  rw [← Finset.sum_mul]
  rw [← Complex.ofReal_sum, sum_range_monotoneQuarterWeight]
  by_cases hx : x ∈ tsupport parent
  · rw [hleft x hx, hright x hx]
    simp
  · have hpx : parent x = 0 := by
      by_contra hp
      exact hx (subset_tsupport parent (Function.mem_support.mpr hp))
    simp only [hpx, mul_zero]

/-- Every Bombieri test admits a finite consecutive decomposition by the
explicit monotone weights.  Unlike an arbitrary subordinate partition, all
of its cumulative suffixes telescope to monotone smooth steps. -/
theorem exists_monotoneQuarterCell_decomposition (parent : BombieriTest) :
    ∃ (lo : ℤ) (n : ℕ),
      monotoneQuarterCutoff parent lo = parent ∧
        monotoneQuarterCutoff parent (lo + (n : ℤ)) = 0 ∧
        (∑ i ∈ Finset.range n,
            monotoneQuarterCell parent (lo + (i : ℤ))) = parent ∧
        (∀ i ∈ Finset.range n,
          BombieriRatioTwoCell
            (monotoneQuarterCell parent (lo + (i : ℤ)))) ∧
        ∀ j : ℕ, j ≤ n →
          (∑ i ∈ Finset.range (n - j),
              monotoneQuarterCell parent
                (lo + (j : ℤ) + (i : ℤ))) =
            monotoneQuarterCutoff parent (lo + (j : ℤ)) := by
  obtain ⟨lo₀, hi₀, A, _eta, hlohi, _houtside, hsum, hsupport,
      _hcommon, _hsmooth, _hnonneg, _hsumOne, _hdisjoint⟩ :=
    exists_consecutive_coherent_quarterLogLattice_decomposition parent
  have hcommonSupport : ∀ k ∈ Finset.Icc lo₀ hi₀,
      tsupport (A k) ⊆
        Set.Icc (quarterLogLatticePoint lo₀)
          (quarterLogLatticePoint (hi₀ + 2)) := by
    intro k hk
    have hk' := Finset.mem_Icc.mp hk
    exact (hsupport k).trans fun x hx ↦
      ⟨(quarterLogLatticePoint_mono hk'.1).trans hx.1,
        hx.2.trans (quarterLogLatticePoint_mono (by omega))⟩
  have hparentSupport : tsupport parent ⊆
      Set.Icc (quarterLogLatticePoint lo₀)
        (quarterLogLatticePoint (hi₀ + 2)) := by
    rw [← hsum]
    exact tsupport_finset_sum_subset_Icc
      (Finset.Icc lo₀ hi₀) A _ _ hcommonSupport
  let lo := lo₀ - 1
  let n := Int.toNat (hi₀ - lo₀ + 3)
  have hdiff : 0 ≤ hi₀ - lo₀ + 3 := by omega
  have hn : (n : ℤ) = hi₀ - lo₀ + 3 := by
    exact Int.toNat_of_nonneg hdiff
  have hrightIndex : lo + (n : ℤ) = hi₀ + 2 := by
    dsimp only [lo]
    rw [hn]
    ring
  have hleft : monotoneQuarterCutoff parent lo = parent := by
    apply monotoneQuarterCutoff_eq_parent_of_lattice_le_tsupport
    intro x hx
    dsimp only [lo]
    simpa only [sub_add_cancel] using (hparentSupport hx).1
  have hright : monotoneQuarterCutoff parent (lo + (n : ℤ)) = 0 := by
    apply monotoneQuarterCutoff_eq_zero_of_tsupport_le
    intro x hx
    rw [hrightIndex]
    exact (hparentSupport hx).2
  refine ⟨lo, n, hleft, hright, ?_, ?_, ?_⟩
  · rw [sum_range_monotoneQuarterCell_eq_cutoff_sub, hleft, hright, sub_zero]
  · intro i hi
    exact monotoneQuarterCell_ratioTwo parent _
  · intro j hj
    rw [monotoneQuarterCell_suffix_eq_cutoff_sub parent lo hj, hright, sub_zero]

end

end ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneQuarterPartitionStructural

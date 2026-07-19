import ArithmeticHodge.Analysis.MultiplicativeWeilQuarterLogLatticePartitionCoherenceStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilQuarterLogLatticeAggregationStructural

set_option autoImplicit false

open Complex Real Set
open scoped BigOperators

namespace ArithmeticHodge.Analysis.MultiplicativeWeilQuarterLogLatticeCoherentAggregationStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilQuarterLogLatticePartitionStructural
open MultiplicativeWeilQuarterLogLatticePartitionCoherenceStructural
open MultiplicativeWeilQuarterLogLatticeAggregationStructural

def indexedPhysical (cells : List CoherentQuarterCell) :
    List (ℤ × BombieriTest) :=
  cells.map fun p ↦ (p.index, p.physical)

def aggregatedPhysical (cells : List CoherentQuarterCell) (k : ℤ) :
    BombieriTest :=
  groupedSeed (indexedPhysical cells) k

def aggregatedWeight
    (cells : List CoherentQuarterCell) (k : ℤ) (x : ℝ) : ℝ :=
  (cells.map fun p ↦ if p.index = k then p.weight x else 0).sum

theorem aggregatedPhysical_apply_eq
    (g : BombieriTest) (cells : List CoherentQuarterCell)
    (hcommon : ∀ p ∈ cells, ∀ x : ℝ,
      p.physical x = (p.weight x : ℂ) * g x)
    (k : ℤ) (x : ℝ) :
    aggregatedPhysical cells k x =
      (aggregatedWeight cells k x : ℂ) * g x := by
  induction cells with
  | nil => simp [aggregatedPhysical, aggregatedWeight, indexedPhysical, groupedSeed]
  | cons p cells ih =>
      simp only [aggregatedPhysical, aggregatedWeight, indexedPhysical,
        groupedSeed, List.map_cons, List.sum_cons]
      change (if p.index = k then p.physical else 0) x +
          aggregatedPhysical cells k x =
        (((if p.index = k then p.weight x else 0) +
          aggregatedWeight cells k x : ℝ) : ℂ) * g x
      rw [ih (fun q hq y ↦ hcommon q (List.mem_cons_of_mem p hq) y)]
      by_cases hp : p.index = k
      · rw [if_pos hp, if_pos hp, hcommon p List.mem_cons_self x]
        push_cast
        ring
      · rw [if_neg hp, if_neg hp]
        simp

theorem aggregatedWeight_nonnegative
    (cells : List CoherentQuarterCell)
    (hnonneg : ∀ p ∈ cells, ∀ x : ℝ, 0 ≤ p.weight x)
    (k : ℤ) (x : ℝ) :
    0 ≤ aggregatedWeight cells k x := by
  induction cells with
  | nil => simp [aggregatedWeight]
  | cons p cells ih =>
      simp only [aggregatedWeight, List.map_cons, List.sum_cons]
      apply add_nonneg
      · by_cases hp : p.index = k
        · rw [if_pos hp]
          exact hnonneg p List.mem_cons_self x
        · rw [if_neg hp]
      · exact ih fun q hq y ↦ hnonneg q (List.mem_cons_of_mem p hq) y

theorem aggregatedPhysical_tsupport_subset
    (cells : List CoherentQuarterCell)
    (hsupport : ∀ p ∈ cells,
      tsupport p.seed ⊆ Set.Icc 1 (quarterLogLatticePoint 2))
    (k : ℤ) :
    tsupport (aggregatedPhysical cells k) ⊆ Set.Icc
      (quarterLogLatticePoint k) (quarterLogLatticePoint (k + 2)) := by
  induction cells with
  | nil => simp [aggregatedPhysical, indexedPhysical, groupedSeed]
  | cons p cells ih =>
      simp only [aggregatedPhysical, indexedPhysical, groupedSeed,
        List.map_cons, List.sum_cons]
      by_cases hp : p.index = k
      · rw [if_pos hp]
        apply (tsupport_add (p.physical : ℝ → ℂ)
          (aggregatedPhysical cells k)).trans
        apply union_subset
        · simpa only [CoherentQuarterCell.physical, hp] using
            quarterLogLatticeRescale_tsupport_subset p.index p.seed
              (hsupport p List.mem_cons_self)
        · exact ih fun q hq ↦ hsupport q (List.mem_cons_of_mem p hq)
      · rw [if_neg hp, zero_add]
        exact ih fun q hq ↦ hsupport q (List.mem_cons_of_mem p hq)

theorem sum_Icc_aggregatedWeight
    (cells : List CoherentQuarterCell) (lo hi : ℤ)
    (hlo : ∀ p ∈ cells, lo ≤ p.index)
    (hhi : ∀ p ∈ cells, p.index ≤ hi)
    (x : ℝ) :
    (∑ k ∈ Finset.Icc lo hi, aggregatedWeight cells k x) =
      (cells.map fun p ↦ p.weight x).sum := by
  induction cells with
  | nil => simp [aggregatedWeight]
  | cons p cells ih =>
      simp only [aggregatedWeight, List.map_cons, List.sum_cons]
      rw [Finset.sum_add_distrib]
      have hpIcc : p.index ∈ Finset.Icc lo hi := by
        exact Finset.mem_Icc.mpr
          ⟨hlo p List.mem_cons_self, hhi p List.mem_cons_self⟩
      have hpSingle :
          (∑ k ∈ Finset.Icc lo hi,
            if p.index = k then p.weight x else 0) = p.weight x := by
        calc
          (∑ k ∈ Finset.Icc lo hi,
              if p.index = k then p.weight x else 0) =
              (if p.index = p.index then p.weight x else 0) := by
                apply Finset.sum_eq_single p.index
                · intro b hb hbp
                  have hne : p.index ≠ b := Ne.symm hbp
                  simp [hne]
                · exact fun hpnot ↦ (hpnot hpIcc).elim
          _ = p.weight x := by simp
      rw [hpSingle]
      congr 1
      change (∑ k ∈ Finset.Icc lo hi, aggregatedWeight cells k x) = _
      exact ih
        (fun q hq ↦ hlo q (List.mem_cons_of_mem p hq))
        (fun q hq ↦ hhi q (List.mem_cons_of_mem p hq))

theorem mul_list_sum_eq_zero
    (a : ℝ) (bs : List ℝ)
    (hzero : ∀ b ∈ bs, a * b = 0) :
    a * bs.sum = 0 := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
      rw [List.sum_cons, mul_add, hzero b List.mem_cons_self]
      rw [ih (fun c hc ↦ hzero c (List.mem_cons_of_mem b hc))]
      simp

theorem list_sum_mul_sum_eq_zero_of_pairwise
    (as bs : List ℝ)
    (hzero : ∀ a ∈ as, ∀ b ∈ bs, a * b = 0) :
    as.sum * bs.sum = 0 := by
  induction as with
  | nil => simp
  | cons a as ih =>
      rw [List.sum_cons, add_mul]
      have ha : a * bs.sum = 0 :=
        mul_list_sum_eq_zero a bs fun b hb ↦
          hzero a List.mem_cons_self b hb
      rw [ha, ih (fun c hc b hb ↦
        hzero c (List.mem_cons_of_mem a hc) b hb), zero_add]

theorem aggregatedWeight_mul_eq_zero_of_separated
    (cells : List CoherentQuarterCell)
    (hdisjoint : ∀ p ∈ cells, ∀ q ∈ cells,
      p.index + 2 ≤ q.index ∨ q.index + 2 ≤ p.index →
        ∀ x : ℝ, p.weight x * q.weight x = 0)
    (k l : ℤ)
    (hkl : k + 2 ≤ l ∨ l + 2 ≤ k)
    (x : ℝ) :
    aggregatedWeight cells k x * aggregatedWeight cells l x = 0 := by
  apply list_sum_mul_sum_eq_zero_of_pairwise
  intro a ha b hb
  rcases List.mem_map.mp ha with ⟨p, hp, rfl⟩
  rcases List.mem_map.mp hb with ⟨q, hq, rfl⟩
  by_cases hpk : p.index = k
  · by_cases hql : q.index = l
    · rw [if_pos hpk, if_pos hql]
      apply hdisjoint p hp q hq
      simpa only [hpk, hql] using hkl
    · rw [if_neg hql, mul_zero]
  · rw [if_neg hpk, zero_mul]

/-- Coherent partition cells can be aggregated into one finite consecutive
integer family without losing their common-parent or nearest-neighbor
overlap structure. -/
theorem exists_consecutive_coherent_quarterLogLattice_decomposition
    (g : BombieriTest) :
    ∃ (lo hi : ℤ) (A : ℤ → BombieriTest)
        (eta : ℤ → ℝ → ℝ),
      lo ≤ hi ∧
      (∀ k : ℤ, k ∉ Finset.Icc lo hi →
        A k = 0 ∧ ∀ x : ℝ, eta k x = 0) ∧
      (∑ k ∈ Finset.Icc lo hi, A k) = g ∧
      (∀ k : ℤ, tsupport (A k) ⊆ Set.Icc
        (quarterLogLatticePoint k) (quarterLogLatticePoint (k + 2))) ∧
      (∀ k : ℤ, ∀ x : ℝ,
        A k x = (eta k x : ℂ) * g x) ∧
      (∀ k : ℤ, ∀ x : ℝ, 0 ≤ eta k x) ∧
      (∀ x ∈ tsupport g,
        (∑ k ∈ Finset.Icc lo hi, eta k x) = 1) ∧
      (∀ k l : ℤ,
        k + 2 ≤ l ∨ l + 2 ≤ k →
          ∀ x : ℝ, eta k x * eta l x = 0) := by
  obtain ⟨cells, hsum, hsupport, hcommon, hnonneg, hetaSum, hdisjoint⟩ :=
    exists_coherent_quarterLogLattice_decomposition g
  let pairs := indexedPhysical cells
  let lo := lowerIndex pairs
  let hi := upperIndex pairs
  let A : ℤ → BombieriTest := aggregatedPhysical cells
  let eta : ℤ → ℝ → ℝ := aggregatedWeight cells
  have hpairs_mem (p : CoherentQuarterCell) (hp : p ∈ cells) :
      (p.index, p.physical) ∈ pairs := by
    exact List.mem_map.mpr ⟨p, hp, rfl⟩
  have hlo (p : CoherentQuarterCell) (hp : p ∈ cells) :
      lo ≤ p.index :=
    lowerIndex_le_of_mem (hpairs_mem p hp)
  have hhi (p : CoherentQuarterCell) (hp : p ∈ cells) :
      p.index ≤ hi :=
    le_upperIndex_of_mem (hpairs_mem p hp)
  have houtside (k : ℤ) (hk : k ∉ Finset.Icc lo hi) :
      A k = 0 ∧ ∀ x : ℝ, eta k x = 0 := by
    have hne (p : CoherentQuarterCell) (hp : p ∈ cells) :
        p.index ≠ k := by
      intro hpk
      apply hk
      rw [← hpk]
      exact Finset.mem_Icc.mpr ⟨hlo p hp, hhi p hp⟩
    constructor
    · simp only [A, aggregatedPhysical, groupedSeed, indexedPhysical,
        List.map_map, Function.comp_def]
      apply List.sum_eq_zero
      intro f hf
      rcases List.mem_map.mp hf with ⟨p, hp, rfl⟩
      rw [if_neg (hne p hp)]
    · intro x
      simp only [eta, aggregatedWeight]
      apply List.sum_eq_zero
      intro r hr
      rcases List.mem_map.mp hr with ⟨p, hp, rfl⟩
      rw [if_neg (hne p hp)]
  refine ⟨lo, hi, A, eta, lowerIndex_le_upperIndex pairs,
    houtside, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hgroup := sum_Icc_indicator_fibers lo hi pairs
      (fun p : ℤ × BombieriTest ↦ p.2)
      (fun p hp ↦ lowerIndex_le_of_mem hp)
      (fun p hp ↦ le_upperIndex_of_mem hp)
    rw [show (∑ k ∈ Finset.Icc lo hi, A k) =
        (pairs.map fun p ↦ p.2).sum by
          simpa only [A, aggregatedPhysical, groupedSeed] using hgroup]
    simpa only [pairs, indexedPhysical, List.map_map, Function.comp_apply]
      using hsum
  · intro k
    exact aggregatedPhysical_tsupport_subset cells hsupport k
  · intro k x
    exact aggregatedPhysical_apply_eq g cells hcommon k x
  · intro k x
    exact aggregatedWeight_nonnegative cells hnonneg k x
  · intro x hx
    rw [sum_Icc_aggregatedWeight cells lo hi hlo hhi x]
    exact hetaSum x hx
  · intro k l hkl x
    exact aggregatedWeight_mul_eq_zero_of_separated
      cells hdisjoint k l hkl x

end

end ArithmeticHodge.Analysis.MultiplicativeWeilQuarterLogLatticeCoherentAggregationStructural

import ArithmeticHodge.Analysis.MultiplicativeWeilQuarterLogLatticePartitionStructural

set_option autoImplicit false

open Complex Real Set
open scoped BigOperators

namespace ArithmeticHodge.Analysis.MultiplicativeWeilQuarterLogLatticeAggregationStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilQuarterLogLatticePartitionStructural

/-!
# Consecutive aggregation of a quarter-lattice decomposition

The partition theorem initially returns an unordered list which may contain
duplicate lattice indices and gaps.  Here duplicate seeds are added at their
common index and every missing index is represented by the zero seed.  The
result is one finite consecutive integer interval, with the exact physical
sum and the common normalized support bound preserved.
-/

/-- A lower bound for every index in a finite cell list.  Including zero makes
the empty case and the eventual interval uniformly nonempty. -/
def lowerIndex : List (ℤ × BombieriTest) → ℤ
  | [] => 0
  | p :: cells => min p.1 (lowerIndex cells)

/-- An upper bound for every index in a finite cell list. -/
def upperIndex : List (ℤ × BombieriTest) → ℤ
  | [] => 0
  | p :: cells => max p.1 (upperIndex cells)

theorem lowerIndex_le_of_mem
    {cells : List (ℤ × BombieriTest)} {p : ℤ × BombieriTest}
    (hp : p ∈ cells) :
    lowerIndex cells ≤ p.1 := by
  induction cells with
  | nil => simp at hp
  | cons q cells ih =>
      simp only [lowerIndex]
      rcases List.mem_cons.mp hp with rfl | hp
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (ih hp)

theorem le_upperIndex_of_mem
    {cells : List (ℤ × BombieriTest)} {p : ℤ × BombieriTest}
    (hp : p ∈ cells) :
    p.1 ≤ upperIndex cells := by
  induction cells with
  | nil => simp at hp
  | cons q cells ih =>
      simp only [upperIndex]
      rcases List.mem_cons.mp hp with rfl | hp
      · exact le_max_left _ _
      · exact (ih hp).trans (le_max_right _ _)

theorem lowerIndex_le_zero (cells : List (ℤ × BombieriTest)) :
    lowerIndex cells ≤ 0 := by
  induction cells with
  | nil => simp [lowerIndex]
  | cons p cells ih =>
      exact (min_le_right p.1 (lowerIndex cells)).trans ih

theorem zero_le_upperIndex (cells : List (ℤ × BombieriTest)) :
    0 ≤ upperIndex cells := by
  induction cells with
  | nil => simp [upperIndex]
  | cons p cells ih =>
      exact ih.trans (le_max_right p.1 (upperIndex cells))

theorem lowerIndex_le_upperIndex (cells : List (ℤ × BombieriTest)) :
    lowerIndex cells ≤ upperIndex cells :=
  (lowerIndex_le_zero cells).trans (zero_le_upperIndex cells)

/-- Sum every normalized seed carrying the same lattice index. -/
def groupedSeed (cells : List (ℤ × BombieriTest)) (n : ℤ) :
    BombieriTest :=
  (cells.map fun p ↦ if p.1 = n then p.2 else 0).sum

@[simp]
theorem quarterLogLatticeRescale_zero (n : ℤ) :
    quarterLogLatticeRescale n 0 = 0 := by
  ext x
  simp [quarterLogLatticeRescale, normalizedDilation_apply]

theorem quarterLogLatticeRescale_add
    (n : ℤ) (f g : BombieriTest) :
    quarterLogLatticeRescale n (f + g) =
      quarterLogLatticeRescale n f + quarterLogLatticeRescale n g := by
  exact normalizedDilation_add _ _ f g

theorem quarterLogLatticeRescale_groupedSeed
    (cells : List (ℤ × BombieriTest)) (n : ℤ) :
    quarterLogLatticeRescale n (groupedSeed cells n) =
      (cells.map fun p ↦
        if p.1 = n then quarterLogLatticeRescale p.1 p.2 else 0).sum := by
  induction cells with
  | nil => simp [groupedSeed]
  | cons p cells ih =>
      simp only [groupedSeed, List.map_cons, List.sum_cons]
      rw [quarterLogLatticeRescale_add]
      change quarterLogLatticeRescale n (if p.1 = n then p.2 else 0) +
          quarterLogLatticeRescale n (groupedSeed cells n) = _
      rw [ih]
      by_cases hp : p.1 = n
      · subst n
        simp
      · simp [hp]

/-- Grouping preserves the common normalized support interval. -/
theorem tsupport_groupedSeed_subset
    (cells : List (ℤ × BombieriTest)) (n : ℤ)
    (hcells : ∀ p ∈ cells,
      tsupport p.2 ⊆ Set.Icc 1 (quarterLogLatticePoint 2)) :
    tsupport (groupedSeed cells n) ⊆
      Set.Icc 1 (quarterLogLatticePoint 2) := by
  induction cells with
  | nil => simp [groupedSeed]
  | cons p cells ih =>
      simp only [groupedSeed, List.map_cons, List.sum_cons]
      by_cases hp : p.1 = n
      · rw [if_pos hp]
        exact (tsupport_add (p.2 : ℝ → ℂ) (groupedSeed cells n)).trans
          (union_subset
            (hcells p List.mem_cons_self)
            (ih fun q hq ↦ hcells q (List.mem_cons_of_mem p hq)))
      · rw [if_neg hp, zero_add]
        exact ih fun q hq ↦ hcells q (List.mem_cons_of_mem p hq)

theorem sum_Icc_indicator_fibers
    (lo hi : ℤ) (cells : List (ℤ × BombieriTest))
    (F : ℤ × BombieriTest → BombieriTest)
    (hlo : ∀ p ∈ cells, lo ≤ p.1)
    (hhi : ∀ p ∈ cells, p.1 ≤ hi) :
    (∑ n ∈ Finset.Icc lo hi,
      (cells.map fun p ↦ if p.1 = n then F p else 0).sum) =
        (cells.map F).sum := by
  induction cells with
  | nil => simp
  | cons p cells ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [Finset.sum_add_distrib]
      have hpIcc : p.1 ∈ Finset.Icc lo hi := by
        simp only [Finset.mem_Icc]
        exact ⟨hlo p List.mem_cons_self, hhi p List.mem_cons_self⟩
      have hpSingle :
          (∑ n ∈ Finset.Icc lo hi,
            if p.1 = n then F p else 0) = F p := by
        calc
          (∑ n ∈ Finset.Icc lo hi,
              if p.1 = n then F p else 0) =
              (if p.1 = p.1 then F p else 0) := by
                apply Finset.sum_eq_single p.1
                · intro b hb hbp
                  have hne : p.1 ≠ b := Ne.symm hbp
                  simp [hne]
                · exact fun hpnot ↦ (hpnot hpIcc).elim
          _ = F p := by simp
      rw [hpSingle]
      rw [ih
        (fun q hq ↦ hlo q (List.mem_cons_of_mem p hq))
        (fun q hq ↦ hhi q (List.mem_cons_of_mem p hq))]

/-- The consecutive interval of grouped seeds has exactly the original
physical sum. -/
theorem sum_Icc_grouped_rescales
    (cells : List (ℤ × BombieriTest)) :
    ∑ n ∈ Finset.Icc (lowerIndex cells) (upperIndex cells),
        quarterLogLatticeRescale n (groupedSeed cells n) =
      (cells.map fun p ↦ quarterLogLatticeRescale p.1 p.2).sum := by
  calc
    (∑ n ∈ Finset.Icc (lowerIndex cells) (upperIndex cells),
        quarterLogLatticeRescale n (groupedSeed cells n)) =
      ∑ n ∈ Finset.Icc (lowerIndex cells) (upperIndex cells),
        (cells.map fun p ↦
          if p.1 = n then quarterLogLatticeRescale p.1 p.2 else 0).sum := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [quarterLogLatticeRescale_groupedSeed]
    _ = (cells.map fun p ↦ quarterLogLatticeRescale p.1 p.2).sum := by
      exact sum_Icc_indicator_fibers _ _ cells _
        (fun p hp ↦ lowerIndex_le_of_mem hp)
        (fun p hp ↦ le_upperIndex_of_mem hp)

/-- Every Bombieri test is an exact consecutive finite quarter-lattice sum.
Duplicate indices are coalesced, and gaps are literally zero seeds. -/
theorem exists_consecutive_quarterLogLattice_decomposition
    (g : BombieriTest) :
    ∃ lo hi : ℤ, ∃ seed : ℤ → BombieriTest,
      lo ≤ hi ∧
      (∑ n ∈ Finset.Icc lo hi,
        quarterLogLatticeRescale n (seed n)) = g ∧
      ∀ n ∈ Finset.Icc lo hi,
        tsupport (seed n) ⊆ Set.Icc 1 (quarterLogLatticePoint 2) := by
  obtain ⟨cells, hsum, hsupport⟩ := exists_quarterLogLattice_decomposition g
  refine ⟨lowerIndex cells, upperIndex cells, groupedSeed cells,
    lowerIndex_le_upperIndex cells, ?_, ?_⟩
  · rw [sum_Icc_grouped_rescales, hsum]
  · intro n hn
    exact tsupport_groupedSeed_subset cells n hsupport

end

end ArithmeticHodge.Analysis.MultiplicativeWeilQuarterLogLatticeAggregationStructural

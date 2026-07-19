import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Rotate
import ArithmeticHodge.Analysis.MultiplicativeWeilQuarterLogLatticeAggregationStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilFejerLocalizationStructural

set_option autoImplicit false

open Finset Real Set

namespace ArithmeticHodge.Analysis.MultiplicativeWeilQuarterLogLatticeFejerAssemblyStructural

/-!
# Cyclic Fejer assembly of a consecutive quarter-lattice block

Two leading zero slots turn a finite line into a cyclic family without
creating wraparound interactions in any three-term forward window.  Every
cyclic window is then a genuine window of three consecutive integer lattice
positions, possibly containing exterior zeros.  The quarter-lattice support
geometry makes every such window a ratio-two Bombieri cell, so the complete
cyclic Fejer taper is nonnegative.
-/

section Padding

variable {M : Type*} [AddCommMonoid M]

/-- Add two zero slots before a finite line. -/
def frontPadTwo {n : ℕ} (a : Fin n → M) : Fin (n + 2) → M :=
  Fin.cons 0 (Fin.cons 0 a)

@[simp]
theorem frontPadTwo_zero {n : ℕ} (a : Fin n → M) :
    frontPadTwo a 0 = 0 := rfl

@[simp]
theorem frontPadTwo_one {n : ℕ} (a : Fin n → M) :
    frontPadTwo a 1 = 0 := rfl

@[simp]
theorem frontPadTwo_succ_succ {n : ℕ} (a : Fin n → M) (i : Fin n) :
    frontPadTwo a i.succ.succ = a i := rfl

@[simp]
theorem sum_frontPadTwo {n : ℕ} (a : Fin n → M) :
    (∑ i, frontPadTwo a i) = ∑ i, a i := by
  simp [frontPadTwo]

/-- Read a consecutive integer block as a `Fin`-indexed line. -/
def integerBlock (A : ℤ → M) (lo : ℤ) (n : ℕ) : Fin n → M :=
  fun i ↦ A (lo + (i : ℕ))

/-- Two-zero cyclic padding of a consecutive integer block. -/
def paddedIntegerBlock (A : ℤ → M) (lo : ℤ) (n : ℕ) :
    Fin (n + 2) → M :=
  frontPadTwo (integerBlock A lo n)

@[simp]
theorem sum_paddedIntegerBlock (A : ℤ → M) (lo : ℤ) (n : ℕ) :
    (∑ i, paddedIntegerBlock A lo n i) =
      ∑ i : Fin n, A (lo + (i : ℕ)) := by
  simp [paddedIntegerBlock, integerBlock]

private theorem padded_window_zero
    (A : ℤ → M) (lo : ℤ) (n : ℕ) (hn : 2 ≤ n) :
    let b := paddedIntegerBlock A lo n
    let σ := finRotate (n + 2)
    b 0 + b (σ 0) + b (σ (σ 0)) = A lo := by
  dsimp only
  have hσ0 : finRotate (n + 2) (0 : Fin (n + 2)) = 1 := by simp
  have hσ1 : finRotate (n + 2) (1 : Fin (n + 2)) = 2 := by
    rw [finRotate_succ_apply]
    apply Fin.ext
    simp [Fin.add_def]
  rw [hσ0, hσ1]
  let i0 : Fin n := ⟨0, by omega⟩
  have htwo : (2 : Fin (n + 2)) = i0.succ.succ := by
    apply Fin.ext
    simp [i0]
    omega
  have hb2 : paddedIntegerBlock A lo n (2 : Fin (n + 2)) = A lo := by
    change frontPadTwo (integerBlock A lo n) (2 : Fin (n + 2)) = A lo
    rw [htwo, frontPadTwo_succ_succ]
    simp [integerBlock, i0]
  rw [hb2]
  change 0 + 0 + A lo = A lo
  simp

private theorem padded_window_one
    (A : ℤ → M) (lo : ℤ) (n : ℕ) (hn : 2 ≤ n) :
    let b := paddedIntegerBlock A lo n
    let σ := finRotate (n + 2)
    b 1 + b (σ 1) + b (σ (σ 1)) = A lo + A (lo + 1) := by
  dsimp only
  have hσ1 : finRotate (n + 2) (1 : Fin (n + 2)) = 2 := by
    rw [finRotate_succ_apply]
    apply Fin.ext
    simp [Fin.add_def]
  have hσ2 : finRotate (n + 2) (2 : Fin (n + 2)) = 3 := by
    rw [finRotate_succ_apply]
    apply Fin.ext
    simp [Fin.add_def]
  rw [hσ1, hσ2]
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  have htwo : (2 : Fin (n + 2)) = i0.succ.succ := by
    apply Fin.ext
    simp [i0]
    omega
  have hthree : (3 : Fin (n + 2)) = i1.succ.succ := by
    apply Fin.ext
    simp [i1]
    omega
  have hb2 : paddedIntegerBlock A lo n (2 : Fin (n + 2)) = A lo := by
    change frontPadTwo (integerBlock A lo n) (2 : Fin (n + 2)) = A lo
    rw [htwo, frontPadTwo_succ_succ]
    simp [integerBlock, i0]
  have hb3 : paddedIntegerBlock A lo n (3 : Fin (n + 2)) = A (lo + 1) := by
    change frontPadTwo (integerBlock A lo n) (3 : Fin (n + 2)) = A (lo + 1)
    rw [hthree, frontPadTwo_succ_succ]
    simp [integerBlock, i1]
  rw [hb2, hb3]
  change 0 + A lo + A (lo + 1) = A lo + A (lo + 1)
  simp

/-- An interior cyclic window is the literal three-term window of the line. -/
theorem frontPadTwo_window_internal
    {n : ℕ} (a : Fin n → M) (j : Fin n)
    (hj : j.val + 2 < n) :
    let b := frontPadTwo a
    let σ := finRotate (n + 2)
    let i : Fin (n + 2) := ⟨j.val + 2, by omega⟩
    b i + b (σ i) + b (σ (σ i)) =
      a j + a ⟨j.val + 1, by omega⟩ + a ⟨j.val + 2, hj⟩ := by
  dsimp only
  let j1 : Fin n := ⟨j.val + 1, by omega⟩
  let j2 : Fin n := ⟨j.val + 2, hj⟩
  let i : Fin (n + 2) := ⟨j.val + 2, by omega⟩
  have hi : i = j.succ.succ := by
    apply Fin.ext
    rfl
  have hσi : finRotate (n + 2) i = j1.succ.succ := by
    rw [finRotate_succ_apply]
    apply Fin.ext
    simp [Fin.add_def, i, j1]
    omega
  have hσσi : finRotate (n + 2) (finRotate (n + 2) i) =
      j2.succ.succ := by
    rw [hσi, finRotate_succ_apply]
    apply Fin.ext
    simp [Fin.add_def, j1, j2]
    omega
  change frontPadTwo a i + frontPadTwo a (finRotate (n + 2) i) +
      frontPadTwo a (finRotate (n + 2) (finRotate (n + 2) i)) =
    a j + a j1 + a j2
  rw [hσσi, hσi, hi]
  simp only [frontPadTwo_succ_succ]

/-- The penultimate cyclic slot sees the final two entries and one zero. -/
theorem frontPadTwo_window_penultimate
    {n : ℕ} (a : Fin n → M) (hn : 2 ≤ n) :
    let b := frontPadTwo a
    let σ := finRotate (n + 2)
    let i : Fin (n + 2) := ⟨n, by omega⟩
    b i + b (σ i) + b (σ (σ i)) =
      a ⟨n - 2, by omega⟩ + a ⟨n - 1, by omega⟩ := by
  dsimp only
  let j0 : Fin n := ⟨n - 2, by omega⟩
  let j1 : Fin n := ⟨n - 1, by omega⟩
  let i : Fin (n + 2) := ⟨n, by omega⟩
  have hi : i = j0.succ.succ := by
    apply Fin.ext
    simp [i, j0]
    omega
  have hσi : finRotate (n + 2) i = j1.succ.succ := by
    rw [finRotate_succ_apply]
    apply Fin.ext
    simp [Fin.add_def, i, j1]
    omega
  have hj1last : j1.succ.succ = Fin.last (n + 1) := by
    apply Fin.ext
    simp [j1]
    omega
  have hσσi : finRotate (n + 2) (finRotate (n + 2) i) = 0 := by
    rw [hσi, hj1last, finRotate_last]
  change frontPadTwo a i + frontPadTwo a (finRotate (n + 2) i) +
      frontPadTwo a (finRotate (n + 2) (finRotate (n + 2) i)) =
    a j0 + a j1
  rw [hσσi, hσi, hi]
  simp only [frontPadTwo_succ_succ, frontPadTwo_zero, add_zero]

/-- The final cyclic slot sees only the final entry and two zeros. -/
theorem frontPadTwo_window_last
    {n : ℕ} (a : Fin n → M) (hn : 2 ≤ n) :
    let b := frontPadTwo a
    let σ := finRotate (n + 2)
    b (Fin.last (n + 1)) + b (σ (Fin.last (n + 1))) +
        b (σ (σ (Fin.last (n + 1)))) =
      a ⟨n - 1, by omega⟩ := by
  dsimp only
  let j : Fin n := ⟨n - 1, by omega⟩
  have hlast : Fin.last (n + 1) = j.succ.succ := by
    apply Fin.ext
    simp [j]
    omega
  have hσlast : finRotate (n + 2) (Fin.last (n + 1)) = 0 :=
    finRotate_last
  have hσzero : finRotate (n + 2) (0 : Fin (n + 2)) = 1 := by simp
  rw [hσlast, hσzero, hlast]
  simp only [frontPadTwo_succ_succ, frontPadTwo_zero, frontPadTwo_one,
    add_zero]
  congr 1

/-- Every cyclic window of a padded consecutive block is a genuine
three-consecutive-index window of the zero-extended integer family. -/
theorem paddedIntegerBlock_window_eq_consecutive
    (A : ℤ → M) (lo : ℤ) (n : ℕ) (hn : 2 ≤ n)
    (hleft : ∀ k : ℤ, k < lo → A k = 0)
    (hright : ∀ k : ℤ, lo + (n : ℤ) ≤ k → A k = 0)
    (i : Fin (n + 2)) :
    ∃ k : ℤ,
      paddedIntegerBlock A lo n i +
          paddedIntegerBlock A lo n (finRotate (n + 2) i) +
          paddedIntegerBlock A lo n
            (finRotate (n + 2) (finRotate (n + 2) i)) =
        A k + A (k + 1) + A (k + 2) := by
  by_cases hi0 : i.val = 0
  · have hi : i = (0 : Fin (n + 2)) := Fin.ext hi0
    subst i
    refine ⟨lo - 2, ?_⟩
    rw [padded_window_zero A lo n hn]
    have hm2 : A (lo - 2) = 0 := hleft _ (by omega)
    have hm1 : A (lo - 2 + 1) = 0 := hleft _ (by omega)
    rw [hm2, hm1]
    simp
  · by_cases hi1 : i.val = 1
    · have hi : i = (1 : Fin (n + 2)) := Fin.ext hi1
      subst i
      refine ⟨lo - 1, ?_⟩
      rw [padded_window_one A lo n hn]
      have hm1 : A (lo - 1) = 0 := hleft _ (by omega)
      rw [hm1]
      have heq : lo - 1 + 2 = lo + 1 := by omega
      rw [heq]
      simp
    · by_cases hin : i.val < n
      · let j : Fin n := ⟨i.val - 2, by omega⟩
        have hj : j.val + 2 < n := by
          simp only [j]
          omega
        let ii : Fin (n + 2) := ⟨j.val + 2, by omega⟩
        have hii : i = ii := by
          apply Fin.ext
          simp [ii, j]
          omega
        refine ⟨lo + (j.val : ℤ), ?_⟩
        rw [hii]
        have hwindow := frontPadTwo_window_internal
          (integerBlock A lo n) j hj
        change
          paddedIntegerBlock A lo n ii +
              paddedIntegerBlock A lo n (finRotate (n + 2) ii) +
              paddedIntegerBlock A lo n
                (finRotate (n + 2) (finRotate (n + 2) ii)) = _
        have hw :
            paddedIntegerBlock A lo n ii +
                  paddedIntegerBlock A lo n (finRotate (n + 2) ii) +
                  paddedIntegerBlock A lo n
                    (finRotate (n + 2) (finRotate (n + 2) ii)) =
              A (lo + (j.val : ℤ)) +
                A (lo + ((j.val + 1 : ℕ) : ℤ)) +
                A (lo + ((j.val + 2 : ℕ) : ℤ)) := by
          simpa only [paddedIntegerBlock, integerBlock, ii] using hwindow
        rw [hw]
        have hj1 : ((j.val + 1 : ℕ) : ℤ) = (j.val : ℤ) + 1 := by omega
        have hj2 : ((j.val + 2 : ℕ) : ℤ) = (j.val : ℤ) + 2 := by omega
        rw [hj1, hj2]
        have heq1 : lo + ((j.val : ℤ) + 1) = lo + (j.val : ℤ) + 1 := by omega
        have heq2 : lo + ((j.val : ℤ) + 2) = lo + (j.val : ℤ) + 2 := by omega
        rw [heq1, heq2]
      · have hinle : n ≤ i.val := Nat.le_of_not_gt hin
        have hilast : i.val = n ∨ i.val = n + 1 := by omega
        rcases hilast with hinval | hilastval
        · let ii : Fin (n + 2) := ⟨n, by omega⟩
          have hii : i = ii := Fin.ext hinval
          refine ⟨lo + (n : ℤ) - 2, ?_⟩
          rw [hii]
          have hwindow := frontPadTwo_window_penultimate
            (integerBlock A lo n) hn
          have hz : A (lo + (n : ℤ)) = 0 := hright _ (by omega)
          have hw :
              paddedIntegerBlock A lo n ii +
                    paddedIntegerBlock A lo n (finRotate (n + 2) ii) +
                    paddedIntegerBlock A lo n
                      (finRotate (n + 2) (finRotate (n + 2) ii)) =
                A (lo + ((n - 2 : ℕ) : ℤ)) +
                  A (lo + ((n - 1 : ℕ) : ℤ)) := by
            simpa only [paddedIntegerBlock, integerBlock, ii] using hwindow
          have hn2 : ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 := by omega
          have hn1 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
          rw [hw, hn2, hn1]
          have heq0 : lo + ((n : ℤ) - 2) = lo + (n : ℤ) - 2 := by omega
          have heq1 : lo + ((n : ℤ) - 1) = lo + (n : ℤ) - 2 + 1 := by omega
          have heq2 : lo + (n : ℤ) - 2 + 2 = lo + (n : ℤ) := by omega
          rw [heq0, heq1, heq2, hz]
          simp
        · have hii : i = Fin.last (n + 1) := by
            apply Fin.ext
            simpa using hilastval
          refine ⟨lo + (n : ℤ) - 1, ?_⟩
          rw [hii]
          have hwindow := frontPadTwo_window_last
            (integerBlock A lo n) hn
          have hz0 : A (lo + (n : ℤ)) = 0 := hright _ (by omega)
          have hz1 : A (lo + (n : ℤ) + 1) = 0 := hright _ (by omega)
          have hw :
              paddedIntegerBlock A lo n (Fin.last (n + 1)) +
                    paddedIntegerBlock A lo n
                      (finRotate (n + 2) (Fin.last (n + 1))) +
                    paddedIntegerBlock A lo n
                      (finRotate (n + 2)
                        (finRotate (n + 2) (Fin.last (n + 1)))) =
                A (lo + ((n - 1 : ℕ) : ℤ)) := by
            simpa only [paddedIntegerBlock, integerBlock] using hwindow
          have hn1 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
          rw [hw, hn1]
          have heq0 : lo + ((n : ℤ) - 1) = lo + (n : ℤ) - 1 := by omega
          have heq1 : lo + (n : ℤ) - 1 + 1 = lo + (n : ℤ) := by omega
          have heq2 : lo + (n : ℤ) - 1 + 2 = lo + (n : ℤ) + 1 := by omega
          rw [heq0, heq1, heq2, hz0, hz1]
          simp

end Padding

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilFejerLocalizationStructural
open MultiplicativeWeilQuarterLogLatticePartitionStructural

/-- Three consecutive physical quarter-lattice cells form a ratio-two cell. -/
theorem quarterLogLattice_threeWindow_ratioTwo
    (A : ℤ → BombieriTest) (k : ℤ)
    (hsupport : ∀ j : ℤ,
      tsupport (A j) ⊆ Set.Icc
        (quarterLogLatticePoint j) (quarterLogLatticePoint (j + 2))) :
    BombieriRatioTwoCell (A k + A (k + 1) + A (k + 2)) := by
  have h0 : tsupport (A k) ⊆
      Set.Icc (quarterLogLatticePoint k) (quarterLogLatticePoint (k + 4)) :=
    (hsupport k).trans (Set.Icc_subset_Icc le_rfl
      (quarterLogLatticePoint_mono (by omega)))
  have h1 : tsupport (A (k + 1)) ⊆
      Set.Icc (quarterLogLatticePoint k) (quarterLogLatticePoint (k + 4)) :=
    (hsupport (k + 1)).trans
      (Set.Icc_subset_Icc
        (quarterLogLatticePoint_mono (by omega))
        (quarterLogLatticePoint_mono (by omega)))
  have h2 : tsupport (A (k + 2)) ⊆
      Set.Icc (quarterLogLatticePoint k) (quarterLogLatticePoint (k + 4)) :=
    (hsupport (k + 2)).trans
      (Set.Icc_subset_Icc
        (quarterLogLatticePoint_mono (by omega)) (by
          apply le_of_eq
          congr 1
          omega))
  have h01 : tsupport (A k + A (k + 1)) ⊆
      Set.Icc (quarterLogLatticePoint k) (quarterLogLatticePoint (k + 4)) :=
    (tsupport_add (A k : ℝ → ℂ) (A (k + 1) : ℝ → ℂ)).trans
      (Set.union_subset h0 h1)
  have hall : tsupport (A k + A (k + 1) + A (k + 2)) ⊆
      Set.Icc (quarterLogLatticePoint k) (quarterLogLatticePoint (k + 4)) :=
    (tsupport_add (A k + A (k + 1) : ℝ → ℂ)
      (A (k + 2) : ℝ → ℂ)).trans
      (Set.union_subset h01 h2)
  refine ⟨quarterLogLatticePoint k, quarterLogLatticePoint (k + 4),
    quarterLogLatticePoint_pos k,
    quarterLogLatticePoint_mono (by omega), hall, ?_⟩
  rw [quarterLogLatticePoint_add_four]
  field_simp [(quarterLogLatticePoint_pos k).ne']
  exact le_rfl

/-- Every cyclic three-window of a padded physical quarter-lattice block is
a ratio-two Bombieri cell. -/
theorem paddedQuarterLogLattice_all_windows_ratioTwo
    (A : ℤ → BombieriTest) (lo : ℤ) (n : ℕ) (hn : 2 ≤ n)
    (hleft : ∀ k : ℤ, k < lo → A k = 0)
    (hright : ∀ k : ℤ, lo + (n : ℤ) ≤ k → A k = 0)
    (hsupport : ∀ k : ℤ,
      tsupport (A k) ⊆ Set.Icc
        (quarterLogLatticePoint k) (quarterLogLatticePoint (k + 2)))
    (i : Fin (n + 2)) :
    BombieriRatioTwoCell
      (paddedIntegerBlock A lo n i +
        paddedIntegerBlock A lo n (finRotate (n + 2) i) +
        paddedIntegerBlock A lo n
          (finRotate (n + 2) (finRotate (n + 2) i))) := by
  obtain ⟨k, hk⟩ := paddedIntegerBlock_window_eq_consecutive
    A lo n hn hleft hright i
  rw [hk]
  exact quarterLogLattice_threeWindow_ratioTwo A k hsupport

/-- The complete cyclic Fejer taper of any padded physical quarter-lattice
block is nonnegative. -/
theorem bombieriCyclicFejerThree_paddedQuarterLogLattice_nonnegative
    (A : ℤ → BombieriTest) (lo : ℤ) (n : ℕ) (hn : 2 ≤ n)
    (hleft : ∀ k : ℤ, k < lo → A k = 0)
    (hright : ∀ k : ℤ, lo + (n : ℤ) ≤ k → A k = 0)
    (hsupport : ∀ k : ℤ,
      tsupport (A k) ⊆ Set.Icc
        (quarterLogLatticePoint k) (quarterLogLatticePoint (k + 2))) :
    0 ≤ bombieriCyclicFejerThree (finRotate (n + 2))
      (paddedIntegerBlock A lo n) := by
  apply bombieriCyclicFejerThree_nonnegative_of_ratioTwo_windows
  intro i
  exact paddedQuarterLogLattice_all_windows_ratioTwo
    A lo n hn hleft hright hsupport i

/-- Padding simultaneously preserves the sum and supplies every local
ratio-two window. -/
theorem paddedQuarterLogLattice_sum_and_windows
    (A : ℤ → BombieriTest) (lo : ℤ) (n : ℕ) (hn : 2 ≤ n)
    (hleft : ∀ k : ℤ, k < lo → A k = 0)
    (hright : ∀ k : ℤ, lo + (n : ℤ) ≤ k → A k = 0)
    (hsupport : ∀ k : ℤ,
      tsupport (A k) ⊆ Set.Icc
        (quarterLogLatticePoint k) (quarterLogLatticePoint (k + 2))) :
    ((∑ i, paddedIntegerBlock A lo n i) =
        ∑ i : Fin n, A (lo + (i : ℕ))) ∧
      ∀ i : Fin (n + 2),
        BombieriRatioTwoCell
          (paddedIntegerBlock A lo n i +
            paddedIntegerBlock A lo n (finRotate (n + 2) i) +
            paddedIntegerBlock A lo n
              (finRotate (n + 2) (finRotate (n + 2) i))) := by
  exact ⟨sum_paddedIntegerBlock A lo n,
    paddedQuarterLogLattice_all_windows_ratioTwo
      A lo n hn hleft hright hsupport⟩

end

end ArithmeticHodge.Analysis.MultiplicativeWeilQuarterLogLatticeFejerAssemblyStructural

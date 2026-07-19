import ArithmeticHodge.Analysis.MultiplicativeWeilQuarterLogLatticeAggregationStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilQuarterLogLatticeFejerAssemblyStructural

set_option autoImplicit false

open Complex Finset Real Set
open scoped BigOperators

namespace ArithmeticHodge.Analysis.MultiplicativeWeilQuarterLogLatticeFejerDecompositionStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilFejerLocalizationStructural
open MultiplicativeWeilQuarterLogLatticePartitionStructural
open MultiplicativeWeilQuarterLogLatticeAggregationStructural
open MultiplicativeWeilQuarterLogLatticeFejerAssemblyStructural

/-- Every Bombieri test admits a finite cyclic presentation whose sum is the
test and whose order-three cyclic windows are all ratio-two cells. -/
theorem exists_paddedQuarterLogLattice_fejer_decomposition
    (g : BombieriTest) :
    ∃ (A : ℤ → BombieriTest) (lo : ℤ) (n : ℕ)
        (b : Fin (n + 2) → BombieriTest),
      2 ≤ n ∧
      b = paddedIntegerBlock A lo n ∧
      (∀ k : ℤ, k < lo → A k = 0) ∧
      (∀ k : ℤ, lo + (n : ℤ) ≤ k → A k = 0) ∧
      (∀ k : ℤ, tsupport (A k) ⊆ Set.Icc
        (quarterLogLatticePoint k) (quarterLogLatticePoint (k + 2))) ∧
      (∑ i, b i) = g ∧
      (∀ i : Fin (n + 2),
        BombieriRatioTwoCell
          (b i + b (finRotate (n + 2) i) +
            b (finRotate (n + 2) (finRotate (n + 2) i)))) ∧
      0 ≤ bombieriCyclicFejerThree (finRotate (n + 2)) b := by
  obtain ⟨lo, hi, seed, hlohi, hsum, hseed⟩ :=
    exists_consecutive_quarterLogLattice_decomposition g
  let span : ℕ := (hi + 1 - lo).toNat
  let n : ℕ := span + 2
  let S : ℤ → BombieriTest := fun k ↦
    if k ∈ Finset.Icc lo hi then seed k else 0
  let A : ℤ → BombieriTest := fun k ↦
    quarterLogLatticeRescale k (S k)
  let b : Fin (n + 2) → BombieriTest :=
    paddedIntegerBlock A lo n
  have hdiff : 0 ≤ hi + 1 - lo := by omega
  have hspan_cast : (span : ℤ) = hi + 1 - lo := by
    simp only [span, Int.toNat_of_nonneg hdiff]
  have hn : 2 ≤ n := by
    simp only [n]
    omega
  have hSsupport (k : ℤ) :
      tsupport (S k) ⊆ Set.Icc 1 (quarterLogLatticePoint 2) := by
    dsimp only [S]
    by_cases hk : k ∈ Finset.Icc lo hi
    · rw [if_pos hk]
      exact hseed k hk
    · rw [if_neg hk]
      simp
  have hAsupport (k : ℤ) :
      tsupport (A k) ⊆ Set.Icc
        (quarterLogLatticePoint k) (quarterLogLatticePoint (k + 2)) := by
    simpa only [A] using
      quarterLogLatticeRescale_tsupport_subset k (S k) (hSsupport k)
  have hAleft (k : ℤ) (hk : k < lo) : A k = 0 := by
    have hnot : k ∉ Finset.Icc lo hi := by
      simp only [Finset.mem_Icc, not_and_or]
      exact Or.inl (not_le.mpr hk)
    change quarterLogLatticeRescale k
      (if k ∈ Finset.Icc lo hi then seed k else 0) = 0
    rw [if_neg hnot, quarterLogLatticeRescale_zero]
  have hArightHi (k : ℤ) (hk : hi < k) : A k = 0 := by
    have hnot : k ∉ Finset.Icc lo hi := by
      simp only [Finset.mem_Icc, not_and_or]
      exact Or.inr (not_le.mpr hk)
    change quarterLogLatticeRescale k
      (if k ∈ Finset.Icc lo hi then seed k else 0) = 0
    rw [if_neg hnot, quarterLogLatticeRescale_zero]
  have hAright (k : ℤ) (hk : lo + (n : ℤ) ≤ k) : A k = 0 := by
    apply hArightHi k
    have hn_cast : (n : ℤ) = (span : ℤ) + 2 := by
      simp [n]
    rw [hn_cast, hspan_cast] at hk
    omega
  have hAIcc :
      (∑ k ∈ Finset.Icc lo hi, A k) = g := by
    calc
      (∑ k ∈ Finset.Icc lo hi, A k) =
          ∑ k ∈ Finset.Icc lo hi,
            quarterLogLatticeRescale k (seed k) := by
              apply Finset.sum_congr rfl
              intro k hk
              simp only [A, S, hk, if_pos]
      _ = g := hsum
  have hmain :
      (∑ i ∈ Finset.range span, A (lo + (i : ℕ))) = g := by
    have h := hAIcc
    rw [Int.Icc_eq_finset_map, Finset.sum_map] at h
    simpa only [span, Function.Embedding.trans_apply,
      Nat.castEmbedding_apply, addLeftEmbedding_apply] using h
  have htail :
      (∑ i ∈ Finset.range 2, A (lo + ((span + i : ℕ) : ℤ))) = 0 := by
    apply Finset.sum_eq_zero
    intro i hiRange
    apply hArightHi
    have hi_lt : i < 2 := Finset.mem_range.mp hiRange
    rw [Nat.cast_add, hspan_cast]
    omega
  have hFinSum :
      (∑ i : Fin n, A (lo + (i : ℕ))) = g := by
    calc
      (∑ i : Fin n, A (lo + (i : ℕ))) =
          ∑ i ∈ Finset.range n, A (lo + (i : ℕ)) :=
        Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ A (lo + (i : ℤ))) n
      _ = (∑ i ∈ Finset.range span, A (lo + (i : ℕ))) +
          ∑ i ∈ Finset.range 2,
            A (lo + ((span + i : ℕ) : ℤ)) := by
              simpa only [n, Nat.cast_add] using
                Finset.sum_range_add (fun i : ℕ ↦ A (lo + (i : ℤ))) span 2
      _ = g := by rw [hmain, htail, add_zero]
  have hbsum : (∑ i, b i) = g := by
    rw [show b = paddedIntegerBlock A lo n by rfl,
      sum_paddedIntegerBlock, hFinSum]
  have hwindows : ∀ i : Fin (n + 2),
      BombieriRatioTwoCell
        (b i + b (finRotate (n + 2) i) +
          b (finRotate (n + 2) (finRotate (n + 2) i))) := by
    intro i
    simpa only [b] using paddedQuarterLogLattice_all_windows_ratioTwo
      A lo n hn hAleft hAright hAsupport i
  have hfejer :
      0 ≤ bombieriCyclicFejerThree (finRotate (n + 2)) b := by
    simpa only [b] using
      bombieriCyclicFejerThree_paddedQuarterLogLattice_nonnegative
        A lo n hn hAleft hAright hAsupport
  exact ⟨A, lo, n, b, hn, rfl, hAleft, hAright, hAsupport,
    hbsum, hwindows, hfejer⟩

end

end ArithmeticHodge.Analysis.MultiplicativeWeilQuarterLogLatticeFejerDecompositionStructural

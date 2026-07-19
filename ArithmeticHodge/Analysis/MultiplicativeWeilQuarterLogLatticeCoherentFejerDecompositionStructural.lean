import ArithmeticHodge.Analysis.MultiplicativeWeilQuarterLogLatticeCoherentAggregationStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilQuarterLogLatticeFejerDecompositionStructural

set_option autoImplicit false

open Complex Finset Real Set
open scoped BigOperators ContDiff

namespace ArithmeticHodge.Analysis.MultiplicativeWeilQuarterLogLatticeCoherentFejerDecompositionStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilFejerLocalizationStructural
open MultiplicativeWeilQuarterLogLatticePartitionStructural
open MultiplicativeWeilQuarterLogLatticeFejerAssemblyStructural
open MultiplicativeWeilQuarterLogLatticeFejerDecompositionStructural
open MultiplicativeWeilQuarterLogLatticeCoherentAggregationStructural
open MultiplicativeWeilFejerLinearResidualStructural

/-- A coherent quarter-log-lattice partition admits a padded cyclic
presentation preserving its smooth common-parent weights and exact Fejer
residual. -/
theorem exists_padded_coherent_quarterLogLattice_fejer_decomposition
    (g : BombieriTest) :
    ∃ (A : ℤ → BombieriTest) (eta : ℤ → ℝ → ℝ)
        (lo : ℤ) (n : ℕ) (b : Fin (n + 2) → BombieriTest),
      3 ≤ n ∧
      b = paddedIntegerBlock A lo n ∧
      (∀ k : ℤ, k ∉ Finset.Icc lo (lo + (n : ℤ) - 3) →
        A k = 0 ∧ ∀ x : ℝ, eta k x = 0) ∧
      (∀ k : ℤ, tsupport (A k) ⊆ Set.Icc
        (quarterLogLatticePoint k) (quarterLogLatticePoint (k + 2))) ∧
      (∀ k : ℤ, ∀ x : ℝ,
        A k x = (eta k x : ℂ) * g x) ∧
      (∀ k : ℤ, ContDiff ℝ ∞ (eta k)) ∧
      (∀ k : ℤ, ∀ x : ℝ, 0 ≤ eta k x) ∧
      (∀ x ∈ tsupport g,
        (∑ k ∈ Finset.Icc lo (lo + (n : ℤ) - 3), eta k x) = 1) ∧
      (∀ k l : ℤ,
        k + 2 ≤ l ∨ l + 2 ≤ k →
          ∀ x : ℝ, eta k x * eta l x = 0) ∧
      (∑ i, b i) = g ∧
      (∀ i : Fin (n + 2),
        BombieriRatioTwoCell
          (b i + b (finRotate (n + 2) i) +
            b (finRotate (n + 2) (finRotate (n + 2) i)))) ∧
      0 ≤ bombieriCyclicFejerThree (finRotate (n + 2)) b ∧
      bombieriQuadraticRealValue g =
        bombieriCyclicFejerThree (finRotate (n + 2)) b +
          bombieriWeightedLinearLagCross
            bombieriFejerThreeResidualLagWeight
            (List.ofFn (integerBlock A lo n)) := by
  obtain ⟨lo, hi, A, eta, hlohi, houtside, hAIcc, hAsupport,
      hcommon, hsmooth, hnonneg, hetaSum, hdisjoint⟩ :=
    exists_consecutive_coherent_quarterLogLattice_decomposition g
  let span : ℕ := (hi + 1 - lo).toNat
  let n : ℕ := span + 2
  let b : Fin (n + 2) → BombieriTest :=
    paddedIntegerBlock A lo n
  have hdiff : 0 ≤ hi + 1 - lo := by omega
  have hspan_cast : (span : ℤ) = hi + 1 - lo := by
    simp only [span, Int.toNat_of_nonneg hdiff]
  have hn : 3 ≤ n := by
    simp only [n]
    have hspan : 1 ≤ span := by
      have hint : (1 : ℤ) ≤ (span : ℤ) := by
        rw [hspan_cast]
        omega
      exact_mod_cast hint
    omega
  have hn_cast : (n : ℤ) = (span : ℤ) + 2 := by
    simp [n]
  have hendpoint : lo + (n : ℤ) - 3 = hi := by
    rw [hn_cast, hspan_cast]
    omega
  have houtsideEndpoint (k : ℤ)
      (hk : k ∉ Finset.Icc lo (lo + (n : ℤ) - 3)) :
      A k = 0 ∧ ∀ x : ℝ, eta k x = 0 := by
    apply houtside k
    simpa only [hendpoint] using hk
  have hAleft (k : ℤ) (hk : k < lo) : A k = 0 := by
    apply (houtside k ?_).1
    simp only [Finset.mem_Icc, not_and_or]
    exact Or.inl (not_le.mpr hk)
  have hArightHi (k : ℤ) (hk : hi < k) : A k = 0 := by
    apply (houtside k ?_).1
    simp only [Finset.mem_Icc, not_and_or]
    exact Or.inr (not_le.mpr hk)
  have hAright (k : ℤ) (hk : lo + (n : ℤ) ≤ k) : A k = 0 := by
    apply hArightHi k
    rw [hn_cast, hspan_cast] at hk
    omega
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
                Finset.sum_range_add
                  (fun i : ℕ ↦ A (lo + (i : ℤ))) span 2
      _ = g := by rw [hmain, htail, add_zero]
  have hbsum : (∑ i, b i) = g := by
    rw [show b = paddedIntegerBlock A lo n by rfl,
      sum_paddedIntegerBlock, hFinSum]
  have hetaSumEndpoint : ∀ x ∈ tsupport g,
      (∑ k ∈ Finset.Icc lo (lo + (n : ℤ) - 3), eta k x) = 1 := by
    intro x hx
    simpa only [hendpoint] using hetaSum x hx
  have hwindows : ∀ i : Fin (n + 2),
      BombieriRatioTwoCell
        (b i + b (finRotate (n + 2) i) +
          b (finRotate (n + 2) (finRotate (n + 2) i))) := by
    intro i
    simpa only [b] using paddedQuarterLogLattice_all_windows_ratioTwo
      A lo n (by omega : 2 ≤ n) hAleft hAright hAsupport i
  have hfejer :
      0 ≤ bombieriCyclicFejerThree (finRotate (n + 2)) b := by
    simpa only [b] using
      bombieriCyclicFejerThree_paddedQuarterLogLattice_nonnegative
        A lo n (by omega : 2 ≤ n) hAleft hAright hAsupport
  have hexact :
      bombieriQuadraticRealValue g =
        bombieriCyclicFejerThree (finRotate (n + 2)) b +
          bombieriWeightedLinearLagCross
            bombieriFejerThreeResidualLagWeight
            (List.ofFn (integerBlock A lo n)) := by
    rw [← hbsum]
    simpa only [b] using
      bombieriQuadraticRealValue_paddedIntegerBlock_sum_eq_fejer_add_linear_lags
        A lo n
  exact ⟨A, eta, lo, n, b, hn, rfl, houtsideEndpoint, hAsupport,
    hcommon, hsmooth, hnonneg, hetaSumEndpoint, hdisjoint, hbsum, hwindows,
    hfejer, hexact⟩

end

end ArithmeticHodge.Analysis.MultiplicativeWeilQuarterLogLatticeCoherentFejerDecompositionStructural

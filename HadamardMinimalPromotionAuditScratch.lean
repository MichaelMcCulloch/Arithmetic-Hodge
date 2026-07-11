import XiHadamardClosureScratch

set_option autoImplicit false

open Complex Filter Topology ArithmeticHodge.Analysis.EntireFunction

/-!
## Minimal production promotion map

The compiled scratch chain can be consolidated without changing an existing
public structure or theorem statement:

* Add `EntireFunction/CanonicalGrowth.lean`.  It imports the current
  `GrowthBound` and `MinimumModulus` modules and consolidates the generic
  content of `CanonicalFactorizationScratch`, `ProductLogScratch`,
  `SequenceCountScratch`, `MinimumModulusScratch`,
  `CanonicalProductLowerScratch`, `GrowthBoundSoundScratch`, and the first two
  theorems of `XiHadamardClosureScratch`.  Only four declarations need be
  exported: the canonical factorization, multiplicity-aware summability
  transfer, sound canonical growth bound, and affine-from-growth theorem; all
  transitive lower-bound helpers can remain private.
* Change `EntireFunction/Hadamard.lean` to import `CanonicalGrowth` in place of
  `GrowthBound`.  Since `CanonicalGrowth` itself imports `GrowthBound`, the
  existing Hadamard implementation retains its legacy dependency.
* In `ZetaProduct.lean`, replace the existing `xi_hadamard_product` proof with
  the body below.  The already-production `xi_hadamard_product_reindex_bridge`
  supplies the padding-free sequence.

The legacy factorization statement is too weak by itself: it erases the
construction's chosen genus and the analytic multiplicities of the enumerated
zeros.  The new canonical factorization theorem is therefore a necessary
additive interface rather than a convenience wrapper around the old result.

The lower-bound consolidation can omit the unused scratch declarations
`finite_sum_far_ratio_pow_le`, `log_norm_finset_prod`, and
`sum_le_log_norm_finset_prod`; it can also use the existing production theorem
`finite_nonzero_indices_norm_le` in place of the duplicate scratch theorem
`finite_nonzero_indices_norm_le_of_summable`.
-/

namespace ArithmeticHodge.Analysis.HadamardMinimalPromotionAudit

/-- The production `xi_hadamard_product` statement, copied verbatim as a
promotion-boundary test. -/
theorem exact_public_shape_prototype :
    ∃ (m : ℕ) (A B : ℂ) (zeros : ℕ → ℂ),
      (∀ n, zeros n ≠ 0) ∧
      (∀ n, xiFunction (zeros n) = 0) ∧
      Summable (fun n => (‖zeros n‖⁻¹) ^ (2 : ℝ)) ∧
      ∀ s, xiFunction s =
        s ^ m * Complex.exp (A + B * s) *
        ∏' n, EntireFunction.weierstraßElementary 1 (s / zeros n) := by
  have hfin : HasFiniteOrder xiFunction := by
    show entireOrder xiFunction < ⊤
    rw [xiFunction_order]
    exact EReal.coe_lt_top 1
  obtain ⟨m, g, a, p, hg, hzeros, hconv, hfact, hp, _hcover, horders⟩ :=
    weierstraß_factorization_canonical_scratch xiFunction differentiable_xiFunction
      xiFunction_ne_const_zero hfin
  have hp1 : p = 1 := by
    rw [xiFunction_order] at hp
    simpa using hp
  rw [hp1] at hconv hfact horders
  have hsumm_beta : Summable (fun n ↦ ‖a n‖⁻¹ ^ (3 / 2 : ℝ)) :=
    canonical_sequence_summable_of_order_lt_scratch
      xiFunction differentiable_xiFunction xiFunction_ne_const_zero a 1
      hzeros hconv horders (3 / 2 : ℝ) (by norm_num) (by
        rw [xiFunction_order]
        exact EReal.coe_lt_coe_iff.mpr (by norm_num))
  obtain ⟨C, hC, hgrowth⟩ := canonical_factorization_growth
    xiFunction differentiable_xiFunction m g a 1 hg hfact
      (3 / 2 : ℝ) (7 / 4 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) hsumm_beta (by
        rw [xiFunction_order]
        exact EReal.coe_lt_coe_iff.mpr (by norm_num))
  obtain ⟨A, B, hg_affine⟩ := affine_of_growth_lt_two_scratch
    g hg C (7 / 4 : ℝ) hC (by norm_num) (by norm_num) hgrowth
  have hm : m = 0 := by
    by_contra hm
    have h0 := hfact 0
    rw [xiFunction_zero_val] at h0
    simp [zero_pow hm] at h0
  have hconv2 : Summable (fun n ↦ (‖a n‖⁻¹) ^ (2 : ℝ)) := by
    simpa only [Nat.cast_one, one_add_one_eq_two] using hconv
  have hfactorization : ∀ z, xiFunction z = Complex.exp (A + B * z) *
      ∏' n, weierstraßElementary 1 (z / a n) := by
    intro z
    simpa [hm, hg_affine z] using hfact z
  exact xi_hadamard_product_reindex_bridge A B a hzeros hconv2 hfactorization

#print axioms exact_public_shape_prototype

end ArithmeticHodge.Analysis.HadamardMinimalPromotionAudit

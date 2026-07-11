import ArithmeticHodge.Analysis.EntireFunction.MinimumModulus
import Mathlib.Analysis.PSeries

open Complex Filter Topology Real Set

namespace ArithmeticHodge.Analysis.EntireFunction

set_option autoImplicit false

private theorem finite_nonzero_indices_norm_le_of_summable_scratch
    (a : ℕ → ℂ) (beta : ℝ) (hbeta : 0 < beta)
    (hsumm : Summable (fun n => ‖a n‖⁻¹ ^ beta))
    (R : ℝ) (hR : 0 < R) :
    Set.Finite {n : ℕ | a n ≠ 0 ∧ ‖a n‖ ≤ R} := by
  let c : ℝ := R⁻¹ ^ beta
  have hc : 0 < c := Real.rpow_pos_of_pos (inv_pos.mpr hR) beta
  have hev : ∀ᶠ n in Filter.cofinite, ‖a n‖⁻¹ ^ beta < c :=
    hsumm.tendsto_cofinite_zero.eventually_lt_const hc
  have hfinite : Set.Finite {n : ℕ | c ≤ ‖a n‖⁻¹ ^ beta} := by
    simpa only [Filter.eventually_cofinite, Set.mem_setOf_eq, not_lt] using hev
  apply hfinite.subset
  intro n hn
  have han_pos : 0 < ‖a n‖ := norm_pos_iff.mpr hn.1
  have hinv : R⁻¹ ≤ ‖a n‖⁻¹ :=
    (inv_le_inv₀ hR han_pos).2 hn.2
  exact Real.rpow_le_rpow (inv_nonneg.mpr hR.le) hinv hbeta.le

/-- If every nonzero sequence entry is a zero of `f`, inverse-power
summability and finiteness of the nonzero zero set force only finitely many
nonzero entries.  This turns a padded canonical product into a finite product
under a hypothetical finite-zero assumption. -/
theorem finite_nonzero_support_of_finite_zero_set
    (f : ℂ → ℂ) (a : ℕ → ℂ) (beta : ℝ) (hbeta : 0 < beta)
    (hzeros : ∀ n, a n ≠ 0 → f (a n) = 0)
    (hsumm : Summable (fun n => ‖a n‖⁻¹ ^ beta))
    (hfinite : Set.Finite {z : ℂ | f z = 0 ∧ z ≠ 0}) :
    Set.Finite {n : ℕ | a n ≠ 0} := by
  let Z : Set ℂ := {z : ℂ | f z = 0 ∧ z ≠ 0}
  have hZfinite : Z.Finite := hfinite
  have hnormfinite : (norm '' Z).Finite := hZfinite.image norm
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ r ∈ norm '' Z, r ≤ M := hnormfinite.bddAbove
  let R : ℝ := max 1 M
  have hR : 0 < R := zero_lt_one.trans_le (le_max_left 1 M)
  have hsupport_bound : {n : ℕ | a n ≠ 0} ⊆
      {n : ℕ | a n ≠ 0 ∧ ‖a n‖ ≤ R} := by
    intro n hn
    refine ⟨hn, ?_⟩
    have haZ : a n ∈ Z := ⟨hzeros n hn, hn⟩
    exact (hM ‖a n‖ ⟨a n, haZ, rfl⟩).trans (le_max_right 1 M)
  exact (finite_nonzero_indices_norm_le_of_summable_scratch a beta hbeta hsumm R hR).subset
    hsupport_bound

end ArithmeticHodge.Analysis.EntireFunction

#print axioms ArithmeticHodge.Analysis.EntireFunction.finite_nonzero_support_of_finite_zero_set

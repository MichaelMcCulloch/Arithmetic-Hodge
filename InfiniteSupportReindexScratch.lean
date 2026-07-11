import ArithmeticHodge.Analysis.EntireFunction.WeierstraßProduct
import Mathlib.SetTheory.Cardinal.Basic

open Complex Filter Topology Real Set

namespace ArithmeticHodge.Analysis.EntireFunction

set_option autoImplicit false

/-- An infinitely supported padded zero sequence can be reindexed by `ℕ`
without padding.  Summability and every canonical product are preserved. -/
theorem exists_nonzero_reindex_of_infinite_support
    (a : ℕ → ℂ) (beta : ℝ)
    (hsumm : Summable (fun n => ‖a n‖⁻¹ ^ beta))
    (hinf : Set.Infinite {n : ℕ | a n ≠ 0}) :
    ∃ b : ℕ → ℂ,
      (∀ n, b n ≠ 0) ∧
      Summable (fun n => ‖b n‖⁻¹ ^ beta) ∧
      ∀ (p : ℕ) (z : ℂ),
        ∏' n, weierstraßElementary p (z / b n) =
          ∏' n, weierstraßElementary p (z / a n) := by
  let S : Set ℕ := {n : ℕ | a n ≠ 0}
  letI : Infinite S := hinf.to_subtype
  letI : Denumerable S := Classical.choice (nonempty_denumerable S)
  let e : ℕ ≃ S := (Denumerable.eqv S).symm
  let b : ℕ → ℂ := fun n => a (e n)
  refine ⟨b, ?_, ?_, ?_⟩
  · intro n
    exact (e n).property
  · have hsub : Summable (fun i : S => ‖a i‖⁻¹ ^ beta) := hsumm.subtype S
    exact e.summable_iff.mpr hsub
  · intro p z
    have hsupport : Function.mulSupport (fun n => weierstraßElementary p (z / a n)) ⊆ S := by
      intro n hn
      change a n ≠ 0
      intro han
      apply hn
      simp [han, weierstraßElementary_zero]
    calc
      ∏' n, weierstraßElementary p (z / b n) =
          ∏' i : S, weierstraßElementary p (z / a i) := by
            exact e.tprod_eq (fun i : S => weierstraßElementary p (z / a i))
      _ = ∏' n, weierstraßElementary p (z / a n) :=
        tprod_subtype_eq_of_mulSupport_subset hsupport

end ArithmeticHodge.Analysis.EntireFunction

#print axioms ArithmeticHodge.Analysis.EntireFunction.exists_nonzero_reindex_of_infinite_support

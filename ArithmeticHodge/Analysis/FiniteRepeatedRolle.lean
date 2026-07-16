import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Data.Finset.Sort

set_option autoImplicit false

open Set

namespace ArithmeticHodge.Analysis.FiniteRepeatedRolle

noncomputable section

/-!
# Repeated Rolle theorem for a finite ordered family of zeros

A `C^n` real function with `n + 1` strictly ordered zeros has a zero of its
`n`th derivative between the first and last nodes.  The proof is structural:
one Rolle zero is chosen in every adjacent interval, those zeros remain
strictly ordered, and the argument recurses on the derivative.
-/

/-- A `C^n` function with `n + 1` strictly ordered zeros has a zero of its
`n`th iterated derivative in the closed interval spanned by the nodes. -/
theorem exists_iteratedDeriv_eq_zero_of_strictMono_zeros
    (n : ℕ) (f : ℝ → ℝ) (hf : ContDiff ℝ n f)
    (x : Fin (n + 1) → ℝ) (hx : StrictMono x)
    (hzero : ∀ i, f (x i) = 0) :
    ∃ c ∈ Icc (x 0) (x (Fin.last n)), iteratedDeriv n f c = 0 := by
  induction n generalizing f with
  | zero =>
      exact ⟨x 0, ⟨le_rfl, le_rfl⟩, by simpa using hzero 0⟩
  | succ n ih =>
      have hrolle (i : Fin (n + 1)) :
          ∃ c ∈ Ioo (x i.castSucc) (x i.succ), deriv f c = 0 := by
        apply exists_deriv_eq_zero
        · exact hx i.castSucc_lt_succ
        · exact hf.continuous.continuousOn
        · rw [hzero, hzero]
      let y : Fin (n + 1) → ℝ := fun i ↦ Classical.choose (hrolle i)
      have hy_mem (i : Fin (n + 1)) :
          y i ∈ Ioo (x i.castSucc) (x i.succ) :=
        (Classical.choose_spec (hrolle i)).1
      have hy_zero (i : Fin (n + 1)) : deriv f (y i) = 0 :=
        (Classical.choose_spec (hrolle i)).2
      have hy_mono : StrictMono y := by
        rw [Fin.strictMono_iff_lt_succ]
        intro i
        exact (hy_mem i.castSucc).2.trans (by
          simpa using (hy_mem i.succ).1)
      obtain ⟨c, hc_mem, hc_zero⟩ := ih (deriv f) hf.deriv' y hy_mono hy_zero
      refine ⟨c, ⟨?_, ?_⟩, ?_⟩
      · exact (hy_mem 0).1.le.trans hc_mem.1
      · exact hc_mem.2.trans (by
          simpa using (hy_mem (Fin.last n)).2.le)
      · rw [iteratedDeriv_succ']
        exact hc_zero

/-- Finset form of repeated Rolle.  Sorting is used only to expose the
adjacent intervals; the hypothesis and conclusion remain invariant under the
original ordering of the zeros. -/
theorem exists_iteratedDeriv_eq_zero_of_finset_zeros
    (n : ℕ) (f : ℝ → ℝ) (hf : ContDiff ℝ n f)
    (s : Finset ℝ) (hs : s.card = n + 1)
    {a b : ℝ} (hsIcc : ∀ x ∈ s, x ∈ Icc a b)
    (hzero : ∀ x ∈ s, f x = 0) :
    ∃ c ∈ Icc a b, iteratedDeriv n f c = 0 := by
  let x : Fin (n + 1) → ℝ := s.orderEmbOfFin hs
  have hx : StrictMono x := (s.orderEmbOfFin hs).strictMono
  have hxmem (i : Fin (n + 1)) : x i ∈ s := by
    exact Finset.orderEmbOfFin_mem s hs i
  obtain ⟨c, hc, hczero⟩ :=
    exists_iteratedDeriv_eq_zero_of_strictMono_zeros
      n f hf x hx (fun i ↦ hzero (x i) (hxmem i))
  have hfirst := hsIcc (x 0) (hxmem 0)
  have hlast := hsIcc (x (Fin.last n)) (hxmem (Fin.last n))
  exact ⟨c, ⟨hfirst.1.trans hc.1, hc.2.trans hlast.2⟩, hczero⟩

end

end ArithmeticHodge.Analysis.FiniteRepeatedRolle

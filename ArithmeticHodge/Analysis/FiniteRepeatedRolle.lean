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

/-! ## Local interval form -/

/-- Local form of repeated Rolle.  If a function is `C^n` only on `[a,b]`,
then `n + 1` strictly ordered zeros in that interval still force a zero of
the `n`th derivative-within on `[a,b]`. -/
theorem exists_iteratedDerivWithin_eq_zero_of_strictMono_zeros
    {a b : ℝ} (hab : a < b)
    (n : ℕ) (f : ℝ → ℝ) (hf : ContDiffOn ℝ n f (Icc a b))
    (x : Fin (n + 1) → ℝ) (hx : StrictMono x)
    (hx_mem : ∀ i, x i ∈ Icc a b)
    (hzero : ∀ i, f (x i) = 0) :
    ∃ c ∈ Icc a b,
      iteratedDerivWithin n f (Icc a b) c = 0 := by
  induction n generalizing f with
  | zero =>
      exact ⟨x 0, hx_mem 0, by simpa using hzero 0⟩
  | succ n ih =>
      have hrolle (i : Fin (n + 1)) :
          ∃ c ∈ Ioo (x i.castSucc) (x i.succ),
            derivWithin f (Icc a b) c = 0 := by
        apply exists_hasDerivAt_eq_zero
        · exact hx i.castSucc_lt_succ
        · exact hf.continuousOn.mono (by
            intro z hz
            exact ⟨(hx_mem i.castSucc).1.trans hz.1,
              hz.2.trans (hx_mem i.succ).2⟩)
        · rw [hzero, hzero]
        · intro z hz
          have hzIoo : z ∈ Ioo a b := ⟨
            (hx_mem i.castSucc).1.trans_lt hz.1,
            hz.2.trans_le (hx_mem i.succ).2⟩
          exact ((hf.differentiableOn (by simp)) z
              (Ioo_subset_Icc_self hzIoo)).hasDerivWithinAt
            |>.hasDerivAt (Icc_mem_nhds hzIoo.1 hzIoo.2)
      let y : Fin (n + 1) → ℝ := fun i ↦ Classical.choose (hrolle i)
      have hy_mem (i : Fin (n + 1)) :
          y i ∈ Ioo (x i.castSucc) (x i.succ) :=
        (Classical.choose_spec (hrolle i)).1
      have hy_Icc (i : Fin (n + 1)) : y i ∈ Icc a b := ⟨
        (hx_mem i.castSucc).1.trans (hy_mem i).1.le,
        (hy_mem i).2.le.trans (hx_mem i.succ).2⟩
      have hy_zero (i : Fin (n + 1)) :
          derivWithin f (Icc a b) (y i) = 0 :=
        (Classical.choose_spec (hrolle i)).2
      have hy_mono : StrictMono y := by
        rw [Fin.strictMono_iff_lt_succ]
        intro i
        exact (hy_mem i.castSucc).2.trans (by
          simpa using (hy_mem i.succ).1)
      have hderiv : ContDiffOn ℝ n (derivWithin f (Icc a b)) (Icc a b) :=
        hf.derivWithin (uniqueDiffOn_Icc hab) (by simp)
      obtain ⟨c, hc_mem, hc_zero⟩ :=
        ih (derivWithin f (Icc a b)) hderiv y hy_mono hy_Icc hy_zero
      refine ⟨c, hc_mem, ?_⟩
      rw [iteratedDerivWithin_succ']
      exact hc_zero

/-- Finset form of local repeated Rolle.  A finset of `n + 1` zeros inside
`[a,b]` is sorted structurally and fed to the strictly monotone theorem. -/
theorem exists_iteratedDerivWithin_eq_zero_of_finset_zeros
    {a b : ℝ} (hab : a < b)
    (n : ℕ) (f : ℝ → ℝ) (hf : ContDiffOn ℝ n f (Icc a b))
    (s : Finset ℝ) (hs : s.card = n + 1)
    (hsIcc : ∀ z ∈ s, z ∈ Icc a b)
    (hzero : ∀ z ∈ s, f z = 0) :
    ∃ c ∈ Icc a b,
      iteratedDerivWithin n f (Icc a b) c = 0 := by
  let x : Fin (n + 1) → ℝ := s.orderEmbOfFin hs
  apply exists_iteratedDerivWithin_eq_zero_of_strictMono_zeros
    hab n f hf x (s.orderEmbOfFin hs).strictMono
  · intro i
    exact hsIcc _ (s.orderEmbOfFin_mem hs i)
  · intro i
    exact hzero _ (s.orderEmbOfFin_mem hs i)

end

end ArithmeticHodge.Analysis.FiniteRepeatedRolle

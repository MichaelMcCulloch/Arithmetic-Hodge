/-
  Minimum-modulus infrastructure for canonical products.

  The first step in the good-circle argument is purely measure theoretic:
  a sufficiently long interval of radii cannot be covered by countably many
  exceptional annuli whose radial widths are summable.
-/

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

open Filter Set MeasureTheory
open scoped ENNReal Topology

namespace ArithmeticHodge.Analysis.EntireFunction

/-- A real interval longer than the total diameter of countably many
    summably thin closed intervals contains a point outside all of them. -/
theorem exists_radius_avoiding_summable_intervals
    (center radius : ℕ → ℝ)
    (hradius : ∀ n, 0 ≤ radius n)
    (hsumm : Summable radius)
    (L U : ℝ) (hwidth : 2 * ∑' n, radius n < U - L) :
    ∃ R ∈ Icc L U, ∀ n, radius n < |R - center n| := by
  let bad : ℕ → Set ℝ := fun n => Icc (center n - radius n) (center n + radius n)
  have hbad_volume (n : ℕ) : volume (bad n) = ENNReal.ofReal (2 * radius n) := by
    rw [show bad n = Icc (center n - radius n) (center n + radius n) from rfl,
      Real.volume_Icc]
    congr 1
    ring
  have hsum2 : Summable (fun n => 2 * radius n) := hsumm.mul_left 2
  have hunion_volume : volume (⋃ n, bad n) ≤ ENNReal.ofReal (2 * ∑' n, radius n) := by
    calc
      volume (⋃ n, bad n) ≤ ∑' n, volume (bad n) := measure_iUnion_le _
      _ = ∑' n, ENNReal.ofReal (2 * radius n) := by simp_rw [hbad_volume]
      _ = ENNReal.ofReal (∑' n, 2 * radius n) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg (by norm_num) (hradius n))
          hsum2).symm
      _ = ENNReal.ofReal (2 * ∑' n, radius n) := by rw [tsum_mul_left]
  by_contra h
  push_neg at h
  have hsubset : Icc L U ⊆ ⋃ n, bad n := by
    intro R hR
    obtain ⟨n, hn⟩ := h R hR
    have hbounds := abs_le.mp hn
    exact mem_iUnion.mpr ⟨n, by
      change center n - radius n ≤ R ∧ R ≤ center n + radius n
      constructor <;> linarith⟩
  have hmeasure := measure_mono (μ := volume) hsubset
  rw [Real.volume_Icc] at hmeasure
  have hwidth_pos : 0 < U - L := lt_of_le_of_lt
    (mul_nonneg (by norm_num) (tsum_nonneg fun n => hradius n)) hwidth
  have hstrict : ENNReal.ofReal (2 * ∑' n, radius n) < ENNReal.ofReal (U - L) :=
    (ENNReal.ofReal_lt_ofReal_iff hwidth_pos).mpr hwidth
  exact (not_lt_of_ge (hmeasure.trans hunion_volume)) hstrict

end ArithmeticHodge.Analysis.EntireFunction

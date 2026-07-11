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

/-- For a zero sequence with summable exceptional radii, every sufficiently
    large dyadic annulus `[2r, 4r]` contains a sphere separated from every
    zero modulus by more than its exceptional radius. -/
theorem canonicalProduct_exists_good_radius
    (zeros : ℕ → ℂ) (α : ℝ)
    (hsumm : Summable (fun n => ‖zeros n‖⁻¹ ^ α)) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ r ≥ R₀, ∃ R : ℝ,
      2 * r ≤ R ∧ R ≤ 4 * r ∧
      ∀ n, ‖zeros n‖⁻¹ ^ α < |R - ‖zeros n‖| := by
  let radius : ℕ → ℝ := fun n => ‖zeros n‖⁻¹ ^ α
  let S : ℝ := ∑' n, radius n
  refine ⟨max 1 (S + 1), lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun r hr => ?_⟩
  have hS_lt_r : S < r := by
    have hSr : S + 1 ≤ r := (le_max_right 1 (S + 1)).trans hr
    linarith
  have hwidth : 2 * ∑' n, radius n < 4 * r - 2 * r := by
    change 2 * S < 4 * r - 2 * r
    linarith
  obtain ⟨R, hR, hsep⟩ := exists_radius_avoiding_summable_intervals
    (fun n => ‖zeros n‖) radius
    (fun n => Real.rpow_nonneg (inv_nonneg.mpr (norm_nonneg _)) _)
    hsumm (2 * r) (4 * r) hwidth
  exact ⟨R, hR.1, hR.2, hsep⟩

/-- The selected radius gives uniform geometric separation on the whole
    sphere, by the reverse triangle inequality. -/
theorem canonicalProduct_exists_good_sphere
    (zeros : ℕ → ℂ) (α : ℝ)
    (hsumm : Summable (fun n => ‖zeros n‖⁻¹ ^ α)) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ r ≥ R₀, ∃ R : ℝ,
      2 * r ≤ R ∧ R ≤ 4 * r ∧
      ∀ z : ℂ, ‖z‖ = R → ∀ n, ‖zeros n‖⁻¹ ^ α < ‖z - zeros n‖ := by
  obtain ⟨R₀, hR₀, hgood⟩ := canonicalProduct_exists_good_radius zeros α hsumm
  refine ⟨R₀, hR₀, fun r hr => ?_⟩
  obtain ⟨R, hR_lower, hR_upper, hsep⟩ := hgood r hr
  refine ⟨R, hR_lower, hR_upper, fun z hz n => (hsep n).trans_le ?_⟩
  simpa [hz] using abs_norm_sub_norm_le z (zeros n)

end ArithmeticHodge.Analysis.EntireFunction

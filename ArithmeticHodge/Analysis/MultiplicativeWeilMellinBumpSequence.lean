import ArithmeticHodge.Analysis.MultiplicativeWeilMellinApproximateIdentity

/-!
# A shrinking sequence of smooth multiplicative bumps

This module chooses unit-mass Bombieri bumps with logarithmic radii
`1 / (n + 1)` and proves that their Mellin transforms converge to one at
every fixed complex argument.
-/

set_option autoImplicit false

open Complex Filter MeasureTheory Metric Real Set Topology
open scoped ContDiff Distributions

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-- The logarithmic radius of the `n`th bump. -/
def mellinBumpRadius (n : ℕ) : ℝ :=
  1 / ((n : ℝ) + 1)

theorem mellinBumpRadius_pos (n : ℕ) : 0 < mellinBumpRadius n := by
  simp only [mellinBumpRadius]
  positivity

theorem mellinBumpRadius_tendsto_zero :
    Tendsto mellinBumpRadius atTop (𝓝 0) := by
  simpa only [mellinBumpRadius] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- A chosen sequence of real, nonnegative, unit-mass Bombieri bumps whose
logarithmic supports shrink to the multiplicative identity. -/
def mellinBumpSequence (n : ℕ) : BombieriTest :=
  Classical.choose
    (exists_bombieri_bump_unit_mass
      (mellinBumpRadius n) (mellinBumpRadius_pos n))

theorem mellinBumpSequence_support (n : ℕ) :
    tsupport (mellinBumpSequence n : ℝ → ℂ) ⊆
      Ioo (Real.exp (-mellinBumpRadius n))
        (Real.exp (mellinBumpRadius n)) :=
  (Classical.choose_spec
    (exists_bombieri_bump_unit_mass
      (mellinBumpRadius n) (mellinBumpRadius_pos n))).1

theorem mellinBumpSequence_real_nonnegative (n : ℕ) :
    ∀ x, 0 ≤ (mellinBumpSequence n x).re ∧
      (mellinBumpSequence n x).im = 0 :=
  (Classical.choose_spec
    (exists_bombieri_bump_unit_mass
      (mellinBumpRadius n) (mellinBumpRadius_pos n))).2.1

theorem mellinBumpSequence_unit_mass (n : ℕ) :
    (∫ x : ℝ, (mellinBumpSequence n x).re) = 1 :=
  (Classical.choose_spec
    (exists_bombieri_bump_unit_mass
      (mellinBumpRadius n) (mellinBumpRadius_pos n))).2.2

/-- The support statement with the radius expanded as `1 / (n + 1)`. -/
theorem mellinBumpSequence_support_one_div_add_one (n : ℕ) :
    tsupport (mellinBumpSequence n : ℝ → ℂ) ⊆
      Ioo (Real.exp (-(1 / ((n : ℝ) + 1))))
        (Real.exp (1 / ((n : ℝ) + 1))) := by
  simpa only [mellinBumpRadius] using mellinBumpSequence_support n

/-- At every fixed complex argument, the Mellin transforms of the shrinking
bumps converge to one. -/
theorem mellin_mellinBumpSequence_tendsto_one (s : ℂ) :
    Tendsto (fun n : ℕ => mellin (mellinBumpSequence n : ℝ → ℂ) s)
      atTop (𝓝 1) := by
  have hradius := mellinBumpRadius_tendsto_zero
  have hsmallLimit : Tendsto
      (fun n : ℕ => ‖s - 1‖ * mellinBumpRadius n) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds (x := ‖s - 1‖)).mul hradius
  have hsmall : ∀ᶠ n : ℕ in atTop,
      ‖s - 1‖ * mellinBumpRadius n ≤ 1 :=
    hsmallLimit.eventually_le_const zero_lt_one
  have hbound : ∀ᶠ n : ℕ in atTop,
      ‖mellin (mellinBumpSequence n : ℝ → ℂ) s - 1‖ ≤
        2 * ‖s - 1‖ * mellinBumpRadius n := by
    filter_upwards [hsmall] with n hn
    exact norm_mellin_sub_one_le_of_unit_mass_log_support
      (mellinBumpSequence n) (mellinBumpRadius n)
      (mellinBumpRadius_pos n) (mellinBumpSequence_support n)
      (mellinBumpSequence_real_nonnegative n)
      (mellinBumpSequence_unit_mass n) s hn
  have hboundLimit : Tendsto
      (fun n : ℕ => 2 * ‖s - 1‖ * mellinBumpRadius n)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds (x := 2 * ‖s - 1‖)).mul hradius
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero' (Eventually.of_forall fun n =>
    norm_nonneg (mellin (mellinBumpSequence n : ℝ → ℂ) s - 1))
    hbound hboundLimit

/-- Convergence is uniform over every fixed finite set of complex arguments,
in the elementary eventual sense. -/
theorem mellin_mellinBumpSequence_tendsto_one_uniformOn_finset
    (S : Finset ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ s ∈ S,
      ‖mellin (mellinBumpSequence n : ℝ → ℂ) s - 1‖ < δ := by
  rw [S.eventually_all]
  intro s _hs
  have hs := mellin_mellinBumpSequence_tendsto_one s
  have hevent := hs.eventually (ball_mem_nhds (1 : ℂ) hδ)
  simpa only [mem_ball, dist_eq_norm] using hevent

end

end ArithmeticHodge.Analysis.MultiplicativeWeil

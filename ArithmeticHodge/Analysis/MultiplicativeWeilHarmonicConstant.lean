/-
  The harmonic-series constant in Bombieri's equation (2.8).

  The paired odd and ordinary harmonic terms form a convergent series whose
  exact value supplies the `log 4` term in the multiplicative Weil formula.
-/

import Mathlib.NumberTheory.Harmonic.EulerMascheroni

set_option autoImplicit false

open Filter Topology
open scoped BigOperators

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

private def bombieriPositiveTerm (m : ℕ) : ℝ :=
  1 / (((m + 1 : ℕ) : ℝ)) -
    2 / (2 * (((m + 1 : ℕ) : ℝ)) + 1)

private lemma bombieriPositiveTerm_nonneg (m : ℕ) :
    0 ≤ bombieriPositiveTerm m := by
  rw [bombieriPositiveTerm]
  have hk : 0 < (((m + 1 : ℕ) : ℝ)) := by positivity
  have hd : 0 < 2 * (((m + 1 : ℕ) : ℝ)) + 1 := by positivity
  rw [sub_nonneg, div_le_div_iff₀ hd hk]
  linarith

private lemma sum_range_bombieriPositiveTerm (n : ℕ) :
    ∑ m ∈ Finset.range n, bombieriPositiveTerm m =
      2 - 2 * (harmonic (2 * n + 1) : ℝ) + 2 * (harmonic n : ℝ) := by
  induction n with
  | zero => norm_num [harmonic_succ]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      rw [show 2 * (n + 1) + 1 = (2 * n + 2) + 1 by omega,
        harmonic_succ (2 * n + 2)]
      rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega,
        harmonic_succ (2 * n + 1), harmonic_succ n]
      rw [bombieriPositiveTerm]
      push_cast
      field_simp
      ring

private lemma tendsto_harmonic_two_mul_add_one_sub :
    Tendsto
      (fun n : ℕ => (harmonic (2 * n + 1) : ℝ) - (harmonic n : ℝ))
      atTop (nhds (Real.log 2)) := by
  have hindex : Tendsto (fun n : ℕ => 2 * n + 1) atTop atTop :=
    tendsto_atTop_mono (fun n : ℕ => by simp only [id_eq]; omega)
      (tendsto_id : Tendsto (fun n : ℕ => n) atTop atTop)
  have hlarge := Real.tendsto_harmonic_sub_log_add_one.comp hindex
  have hsmall := Real.tendsto_harmonic_sub_log_add_one
  have hzero := hlarge.sub hsmall
  have hshift := hzero.add (tendsto_const_nhds :
    Tendsto (fun _ : ℕ => Real.log 2) atTop (nhds (Real.log 2)))
  simpa only [sub_self, zero_add] using hshift.congr' (Eventually.of_forall (fun n => by
    simp only [Function.comp_apply]
    have hn : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    have hcast : (((2 * n + 1 : ℕ) : ℝ) + 1) =
        2 * (((n + 1 : ℕ) : ℝ)) := by
      push_cast
      ring
    rw [hcast, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hn]
    push_cast
    ring))

private lemma hasSum_bombieriPositiveTerm :
    HasSum bombieriPositiveTerm (2 - Real.log 4) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg bombieriPositiveTerm_nonneg]
  simp_rw [sum_range_bombieriPositiveTerm]
  have hlim := (tendsto_const_nhds :
    Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (nhds 2)).sub
    (tendsto_harmonic_two_mul_add_one_sub.const_mul 2)
  convert hlim using 1
  · funext n
    ring
  · rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num

/-- The exact real correction series from Bombieri's equation (2.8) sums to
`Real.log 4 - 2`. -/
theorem bombieri_harmonic_series_hasSum :
    HasSum
      (fun m : ℕ =>
        2 / (2 * (((m + 1 : ℕ) : ℝ)) + 1) -
          1 / (((m + 1 : ℕ) : ℝ)))
      (Real.log 4 - 2) := by
  have hneg : HasSum (fun m => -bombieriPositiveTerm m) (Real.log 4 - 2) := by
    convert hasSum_bombieriPositiveTerm.neg using 1
    ring
  refine HasSum.congr_fun hneg (fun m => ?_)
  rw [bombieriPositiveTerm]
  ring

/-- The real correction sequence from Bombieri's equation (2.8) is summable. -/
theorem bombieri_harmonic_series_summable :
    Summable
      (fun m : ℕ =>
        2 / (2 * (((m + 1 : ℕ) : ℝ)) + 1) -
          1 / (((m + 1 : ℕ) : ℝ))) :=
  bombieri_harmonic_series_hasSum.summable

/-- The paired harmonic series in Bombieri's equation (2.8) contributes
exactly the constant `Real.log 4`. -/
theorem bombieri_harmonic_series_eq_log_four :
    2 + ∑' m : ℕ,
      (2 / (2 * (((m + 1 : ℕ) : ℝ)) + 1) -
        1 / (((m + 1 : ℕ) : ℝ))) = Real.log 4 := by
  rw [bombieri_harmonic_series_hasSum.tsum_eq]
  ring

end

end ArithmeticHodge.Analysis.MultiplicativeWeil

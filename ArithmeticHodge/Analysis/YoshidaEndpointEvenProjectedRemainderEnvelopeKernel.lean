import ArithmeticHodge.Analysis.YoshidaEndpointEvenTailRepresenter
import ArithmeticHodge.Analysis.YoshidaConstantBounds
import Mathlib.Analysis.Calculus.Taylor

set_option autoImplicit false

open Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedRemainderEnvelopeKernel

open YoshidaEndpointHyperbolicBound
open YoshidaConstantBounds

noncomputable section

/-- Sixth-order Taylor envelope for the regular Yoshida kernel on
`[0, log 2]`.  The odd powers come from the regularized cosecant term. -/
def yoshidaRegularKernelPolynomial6 (t : ℝ) : ℝ :=
  (1 / 4 : ℝ) - t / 48 - t ^ 2 / 32 + 7 * t ^ 3 / 11520 +
    5 * t ^ 4 / 1536 - 31 * t ^ 5 / 1935360 -
      61 * t ^ 6 / 184320

/-- Even Taylor polynomial used for the fixed endpoint cosh factor. -/
def yoshidaEndpointCoshPolynomial6 (x : ℝ) : ℝ :=
  1 + yoshidaEndpointA ^ 2 * x ^ 2 / 8 +
    yoshidaEndpointA ^ 4 * x ^ 4 / 384 +
      yoshidaEndpointA ^ 6 * x ^ 6 / 46080

/-- The degree-six regular-kernel envelope is normalized at the removable
singularity. -/
theorem yoshidaRegularKernelPolynomial6_zero :
    yoshidaRegularKernelPolynomial6 0 = (1 / 4 : ℝ) := by
  norm_num [yoshidaRegularKernelPolynomial6]

private theorem abs_cosh_sub_evenTaylor6_lt
    {z : ℝ} (hz0 : 0 ≤ z) (hz : z < (1733 / 10000 : ℝ)) :
    |Real.cosh z - (1 + z ^ 2 / 2 + z ^ 4 / 24 + z ^ 6 / 720)| <
      (1 / 48000000000 : ℝ) := by
  rcases eq_or_lt_of_le hz0 with rfl | hzpos
  · norm_num
  · rcases taylor_mean_remainder_lagrange_iteratedDeriv
        (f := Real.cosh) (x₀ := 0) (x := z) (n := 7) hzpos
        Real.contDiff_cosh.contDiffOn with ⟨w, hw, hTaylor⟩
    have hTaylorEval :
        taylorWithinEval Real.cosh 7 (Icc 0 z) 0 z =
          1 + z ^ 2 / 2 + z ^ 4 / 24 + z ^ 6 / 720 := by
      have hder (n : ℕ) :
          iteratedDerivWithin n Real.cosh (Icc 0 z) 0 =
            iteratedDeriv n Real.cosh 0 :=
        Real.iteratedDerivWithin_cosh_Icc n hzpos ⟨le_rfl, hz0⟩
      rw [taylor_within_apply]
      simp [hder, Finset.sum_range_succ]
      ring
    rw [hTaylorEval] at hTaylor
    norm_num [Real.iteratedDeriv_even_cosh] at hTaylor
    have hw0 : 0 ≤ w := hw.1.le
    have hwUpper : w < (1733 / 10000 : ℝ) := hw.2.trans hz
    have hu0 : 0 ≤ w ^ 2 / 2 := by positivity
    have hu61 : w ^ 2 / 2 < (1 / 61 : ℝ) := by
      have hwSq : w ^ 2 < (1733 / 10000 : ℝ) ^ 2 :=
        pow_lt_pow_left₀ hwUpper hw0 (by norm_num)
      norm_num at hwSq ⊢
      nlinarith
    have hu1 : w ^ 2 / 2 < (1 : ℝ) := hu61.trans (by norm_num)
    have hExp : Real.exp (w ^ 2 / 2) ≤ 1 / (1 - w ^ 2 / 2) :=
      Real.exp_bound_div_one_sub_of_interval hu0 hu1
    have hFrac : 1 / (1 - w ^ 2 / 2) < (61 / 60 : ℝ) := by
      rw [div_lt_iff₀ (sub_pos.mpr hu1)]
      nlinarith
    have hCosh : Real.cosh w < (61 / 60 : ℝ) :=
      (Real.cosh_le_exp_half_sq w).trans_lt (hExp.trans_lt hFrac)
    have hzPow : z ^ 8 < (1733 / 10000 : ℝ) ^ 8 :=
      pow_lt_pow_left₀ hz hz0 (by norm_num)
    have hrem0 : 0 ≤ Real.cosh w * z ^ 8 / 40320 := by positivity
    have hremUpper :
        Real.cosh w * z ^ 8 / 40320 <
          (61 / 60 : ℝ) * (1733 / 10000 : ℝ) ^ 8 / 40320 := by
      gcongr
    have hrat :
        (61 / 60 : ℝ) * (1733 / 10000 : ℝ) ^ 8 / 40320 <
          (1 / 48000000000 : ℝ) := by
      norm_num
    rw [hTaylor, abs_of_nonneg hrem0]
    exact hremUpper.trans hrat

private theorem abs_cosh_sub_yoshidaEndpointCoshPolynomial6_lt_core
    {x : ℝ} (hx : x ∈ Icc (-1) 1) :
    |Real.cosh (yoshidaEndpointA * x / 2) -
        yoshidaEndpointCoshPolynomial6 x| <
      (1 / 48000000000 : ℝ) := by
  let z : ℝ := |yoshidaEndpointA * x / 2|
  have hxAbs : |x| ≤ 1 := abs_le.mpr hx
  have hz0 : 0 ≤ z := abs_nonneg _
  have ha : yoshidaEndpointA < (1733 / 5000 : ℝ) := by
    unfold yoshidaEndpointA
    linarith [strict_log_two_fine_bounds.2]
  have hz : z < (1733 / 10000 : ℝ) := by
    dsimp only [z]
    rw [abs_div, abs_mul, abs_of_nonneg yoshidaEndpointA_pos.le]
    norm_num
    have hmul := mul_le_mul_of_nonneg_left hxAbs yoshidaEndpointA_pos.le
    nlinarith
  have hpoly :
      1 + z ^ 2 / 2 + z ^ 4 / 24 + z ^ 6 / 720 =
        yoshidaEndpointCoshPolynomial6 x := by
    have hzSq : z ^ 2 = (yoshidaEndpointA * x / 2) ^ 2 := by
      dsimp only [z]
      exact sq_abs _
    rw [show z ^ 4 = (z ^ 2) ^ 2 by ring,
      show z ^ 6 = (z ^ 2) ^ 3 by ring, hzSq]
    unfold yoshidaEndpointCoshPolynomial6
    ring
  have hcosh : Real.cosh z = Real.cosh (yoshidaEndpointA * x / 2) := by
    dsimp only [z]
    exact Real.cosh_abs _
  rw [← hcosh, ← hpoly]
  exact abs_cosh_sub_evenTaylor6_lt hz0 hz

/-- The fixed endpoint cosh factor is uniformly captured by its even
degree-six Taylor polynomial. -/
theorem abs_cosh_sub_yoshidaEndpointCoshPolynomial6_lt
    {x : ℝ} (hx : x ∈ Icc (-1) 1) :
    |Real.cosh (yoshidaEndpointA * x / 2) -
        yoshidaEndpointCoshPolynomial6 x| <
      (1 / 48000000000 : ℝ) := by
  exact abs_cosh_sub_yoshidaEndpointCoshPolynomial6_lt_core hx

end

end ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedRemainderEnvelopeKernel

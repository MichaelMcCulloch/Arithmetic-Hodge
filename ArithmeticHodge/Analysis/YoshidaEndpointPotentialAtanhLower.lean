import ArithmeticHodge.Analysis.YoshidaEndpointPotentialBound

set_option autoImplicit false

open Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointPotentialAtanhLower

open YoshidaEndpointPotentialBound

noncomputable section

/-!
# A transformed two-term lower bound for the endpoint potential

Writing `z=x²` and `t=z/(2-z)` turns the endpoint logarithm into the
hyperbolic-arctangent series.  Keeping only `t+t³/3` is much sharper near the
endpoints than keeping the first two powers of `z`, while remaining a fixed
structural inequality.
-/

/-- The first two positive terms after the change of variable
`t = x² / (2-x²)`. -/
def yoshidaEndpointPotentialAtanhTwoTerm (x : ℝ) : ℝ :=
  let t := x ^ 2 / (2 - x ^ 2)
  t + t ^ 3 / 3

private def atanhTwoTermRemainder (t : ℝ) : ℝ :=
  (Real.log (1 + t) - Real.log (1 - t)) / 2 - t - t ^ 3 / 3

private theorem atanhTwoTermRemainder_hasDerivAt
    {t : ℝ} (ht : |t| < 1) :
    HasDerivAt atanhTwoTermRemainder (t ^ 4 / (1 - t ^ 2)) t := by
  have hplus : 1 + t ≠ 0 := by
    have := (abs_lt.mp ht).1
    linarith
  have hminus : 1 - t ≠ 0 := by
    have := (abs_lt.mp ht).2
    linarith
  have hsq : 1 - t ^ 2 ≠ 0 := by
    have htSq : t ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one t).2 ht
    linarith
  have hp : HasDerivAt (fun u : ℝ ↦ 1 + u) 1 t := by
    convert (hasDerivAt_const t 1).add (hasDerivAt_id t) using 1
    all_goals simp
  have hm : HasDerivAt (fun u : ℝ ↦ 1 - u) (-1) t := by
    convert (hasDerivAt_const t 1).sub (hasDerivAt_id t) using 1
    all_goals simp
  have hlp := (Real.hasDerivAt_log hplus).comp t hp
  have hlm := (Real.hasDerivAt_log hminus).comp t hm
  unfold atanhTwoTermRemainder
  convert (((hlp.sub hlm).div_const 2).sub (hasDerivAt_id t)).sub
      (((hasDerivAt_id t).pow 3).div_const 3) using 1
  simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, mul_one]
  field_simp [hplus, hminus, hsq]
  ring

private theorem atanhTwoTermRemainder_nonneg
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    0 ≤ atanhTwoTermRemainder t := by
  have hcont : ContinuousOn atanhTwoTermRemainder (Icc 0 t) := by
    intro u hu
    have huAbs : |u| < 1 := by
      rw [abs_lt]
      constructor <;> linarith [hu.1, hu.2]
    exact (atanhTwoTermRemainder_hasDerivAt huAbs).continuousAt.continuousWithinAt
  have hmono : MonotoneOn atanhTwoTermRemainder (Icc 0 t) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 t) hcont ?_ ?_
    · intro u hu
      have huIcc := interior_subset hu
      have huAbs : |u| < 1 := by
        rw [abs_lt]
        constructor <;> linarith [huIcc.1, huIcc.2]
      exact (atanhTwoTermRemainder_hasDerivAt huAbs).differentiableAt
        |>.differentiableWithinAt
    · intro u hu
      have huIcc := interior_subset hu
      have huAbs : |u| < 1 := by
        rw [abs_lt]
        constructor <;> linarith [huIcc.1, huIcc.2]
      rw [(atanhTwoTermRemainder_hasDerivAt huAbs).deriv]
      exact div_nonneg (by positivity) (by
        have huSq : u ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one u).2 huAbs
        linarith)
  have hvalue := hmono (by exact ⟨le_rfl, ht0⟩)
    (by exact ⟨ht0, le_rfl⟩) ht0
  simpa [atanhTwoTermRemainder] using hvalue

/-- Structural transformed-series lower bound on the open endpoint interval. -/
theorem atanhTwoTerm_le_yoshidaEndpointPotential
    {x : ℝ} (hx : |x| < 1) :
    yoshidaEndpointPotentialAtanhTwoTerm x ≤
      yoshidaEndpointPotential x := by
  let z : ℝ := x ^ 2
  let t : ℝ := z / (2 - z)
  have hz0 : 0 ≤ z := by
    dsimp only [z]
    positivity
  have hz1 : z < 1 := by
    dsimp only [z]
    exact (sq_lt_one_iff_abs_lt_one x).2 hx
  have hden : 0 < 2 - z := by linarith
  have ht0 : 0 ≤ t := by
    dsimp only [t]
    exact div_nonneg hz0 hden.le
  have ht1 : t < 1 := by
    dsimp only [t]
    rw [div_lt_one hden]
    linarith
  have hrem := atanhTwoTermRemainder_nonneg ht0 ht1
  have hplus : 0 < 1 + t := by linarith
  have hminus : 0 < 1 - t := by linarith
  have hratio : (1 - t) / (1 + t) = 1 - z := by
    dsimp only [t]
    field_simp [ne_of_gt hden]
    ring
  have hlog : Real.log (1 - z) =
      Real.log (1 - t) - Real.log (1 + t) := by
    calc
      Real.log (1 - z) = Real.log ((1 - t) / (1 + t)) := by
        rw [hratio]
      _ = Real.log (1 - t) - Real.log (1 + t) :=
        Real.log_div (ne_of_gt hminus) (ne_of_gt hplus)
  unfold atanhTwoTermRemainder at hrem
  unfold yoshidaEndpointPotentialAtanhTwoTerm yoshidaEndpointPotential
  dsimp only [z, t] at hrem hlog ⊢
  rw [hlog]
  linarith

end

end ArithmeticHodge.Analysis.YoshidaEndpointPotentialAtanhLower

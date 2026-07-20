import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Extend

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.QuadraticOneSidedCutoffStructural

noncomputable section

open scoped Topology

/-!
# A `C¹` one-sided quadratic cutoff

Multiplication by a squared boundary distance permits a smooth first-order
extension by zero.  This packages the gluing step needed by endpoint-supported
polynomial test profiles without imposing any support-specific coordinates.
-/

/-- Extend `(x - a) ^ 2 * p x` by zero to the left of `a`. -/
def quadraticRightCutoff (a : ℝ) (p : ℝ → ℝ) (x : ℝ) : ℝ :=
  if a ≤ x then (x - a) ^ 2 * p x else 0

/-- The continuous derivative candidate for `quadraticRightCutoff`. -/
def quadraticRightCutoffDeriv (a : ℝ) (p : ℝ → ℝ) (x : ℝ) : ℝ :=
  if a ≤ x then
    2 * (x - a) * p x + (x - a) ^ 2 * deriv p x
  else 0

theorem continuous_quadraticRightCutoff
    (a : ℝ) (p : ℝ → ℝ) (hp : Continuous p) :
    Continuous (quadraticRightCutoff a p) := by
  unfold quadraticRightCutoff
  apply Continuous.if_le (by fun_prop) continuous_const continuous_const
    continuous_id
  intro x hx
  simp only [id_eq] at hx
  rw [hx]
  ring

theorem continuous_quadraticRightCutoffDeriv
    (a : ℝ) (p : ℝ → ℝ) (hp : ContDiff ℝ 1 p) :
    Continuous (quadraticRightCutoffDeriv a p) := by
  have hp' : Continuous (deriv p) := hp.continuous_deriv (by norm_num)
  unfold quadraticRightCutoffDeriv
  apply Continuous.if_le (by fun_prop) continuous_const continuous_const
    continuous_id
  intro x hx
  simp only [id_eq] at hx
  rw [hx]
  ring

theorem hasDerivAt_quadraticRightCutoff
    (a : ℝ) (p : ℝ → ℝ) (hp : ContDiff ℝ 1 p) (x : ℝ) :
    HasDerivAt (quadraticRightCutoff a p)
      (quadraticRightCutoffDeriv a p x) x := by
  let f := quadraticRightCutoff a p
  let f' := quadraticRightCutoffDeriv a p
  have hbranch : ∀ y : ℝ,
      HasDerivAt (fun z : ℝ ↦ (z - a) ^ 2 * p z)
        (2 * (y - a) * p y + (y - a) ^ 2 * deriv p y) y := by
    intro y
    convert (((hasDerivAt_id y).sub_const a).pow 2).mul
      hp.differentiable_one.differentiableAt.hasDerivAt using 1
    simp [id_eq, pow_two]
  have hoff : ∀ y ≠ a, HasDerivAt f (f' y) y := by
    intro y hya
    rcases lt_or_gt_of_ne hya with hya | hay
    · have heq : f =ᶠ[nhds y] fun _ : ℝ ↦ 0 := by
        filter_upwards [eventually_lt_nhds hya] with z hz
        simp [f, quadraticRightCutoff, not_le.mpr hz]
      have hf' : f' y = 0 := by
        simp [f', quadraticRightCutoffDeriv, not_le.mpr hya]
      rw [hf']
      exact (hasDerivAt_const y (0 : ℝ)).congr_of_eventuallyEq heq
    · have heq : f =ᶠ[nhds y] fun z : ℝ ↦ (z - a) ^ 2 * p z := by
        filter_upwards [eventually_gt_nhds hay] with z hz
        simp [f, quadraticRightCutoff, hz.le]
      have hf' : f' y =
          2 * (y - a) * p y + (y - a) ^ 2 * deriv p y := by
        simp [f', quadraticRightCutoffDeriv, hay.le]
      rw [hf']
      exact (hbranch y).congr_of_eventuallyEq heq
  have hf : Continuous f :=
    continuous_quadraticRightCutoff a p hp.continuous
  have hf' : Continuous f' :=
    continuous_quadraticRightCutoffDeriv a p hp
  exact hasDerivAt_of_hasDerivAt_of_ne' hoff hf.continuousAt hf'.continuousAt x

/-- A squared one-sided cutoff of a `C¹` profile is globally `C¹`. -/
theorem contDiff_one_quadraticRightCutoff
    (a : ℝ) (p : ℝ → ℝ) (hp : ContDiff ℝ 1 p) :
    ContDiff ℝ 1 (quadraticRightCutoff a p) := by
  rw [contDiff_one_iff_deriv]
  constructor
  · intro x
    exact (hasDerivAt_quadraticRightCutoff a p hp x).differentiableAt
  · rw [show deriv (quadraticRightCutoff a p) =
        quadraticRightCutoffDeriv a p by
      funext x
      exact (hasDerivAt_quadraticRightCutoff a p hp x).deriv]
    exact continuous_quadraticRightCutoffDeriv a p hp

/-- Antisymmetrize a right cutoff.  For a positive boundary this is the
natural odd extension of an endpoint-supported profile. -/
def oddQuadraticEndpointCutoff (a : ℝ) (p : ℝ → ℝ) (x : ℝ) : ℝ :=
  quadraticRightCutoff a p x - quadraticRightCutoff a p (-x)

theorem odd_oddQuadraticEndpointCutoff (a : ℝ) (p : ℝ → ℝ) :
    Function.Odd (oddQuadraticEndpointCutoff a p) := by
  intro x
  unfold oddQuadraticEndpointCutoff
  rw [neg_neg]
  ring

theorem contDiff_one_oddQuadraticEndpointCutoff
    (a : ℝ) (p : ℝ → ℝ) (hp : ContDiff ℝ 1 p) :
    ContDiff ℝ 1 (oddQuadraticEndpointCutoff a p) := by
  unfold oddQuadraticEndpointCutoff
  exact (contDiff_one_quadraticRightCutoff a p hp).sub
    ((contDiff_one_quadraticRightCutoff a p hp).comp (by fun_prop))

theorem oddQuadraticEndpointCutoff_eq_right_of_nonneg
    {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) (p : ℝ → ℝ) :
    oddQuadraticEndpointCutoff a p x = quadraticRightCutoff a p x := by
  have hneg : ¬ a ≤ -x := by linarith
  unfold oddQuadraticEndpointCutoff
  rw [show quadraticRightCutoff a p (-x) = 0 by
    simp [quadraticRightCutoff, hneg]]
  ring

end

end ArithmeticHodge.Analysis.QuadraticOneSidedCutoffStructural

/-
  Residue Theorem for Meromorphic Functions

  Builds the residue theorem from Mathlib's Cauchy integral formula
  and Cauchy-Goursat theorem for rectangles. Key results:

  1. `circleIntegral_eq_zero_of_diffContOnCl` — ∮ f = 0 for analytic f
  2. `residue` — residue of f at c, defined via circle integral
  3. `residue_eq_of_simple_pole` — for f = g/(z−c), Res(f,c) = g(c)
  4. `circleIntegral_simple_pole` — residue theorem for one simple pole
  5. `circleIntegral_eq_two_pi_I_sum_residues` — multi-pole circle residue theorem
  6. Rectangle Cauchy-Goursat wrappers and contour deformation
-/

import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Meromorphic.Order

open Complex MeasureTheory Set Filter Topology Metric
open scoped Real

namespace ArithmeticHodge.Analysis

/-! ## Circle integrals of analytic functions vanish -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The circle integral of an analytic function vanishes.
    Write `f(z) = (z−c)⁻¹ • ((z−c) • f(z))` on the circle and apply the
    Cauchy integral formula to `g(z) = (z−c) • f(z)` at `w = c`. -/
theorem circleIntegral_eq_zero_of_diffContOnCl {f : ℂ → E} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DiffContOnCl ℂ f (ball c R)) :
    ∮ z in C(c, R), f z = 0 := by
  set g : ℂ → E := fun z => (z - c) • f z
  have hg : DiffContOnCl ℂ g (ball c R) :=
    (DiffContOnCl.sub_const diffContOnCl_id c).smul hf
  have step1 : (∮ z in C(c, R), (z - c)⁻¹ • g z) = (2 * ↑π * I) • g c :=
    hg.circleIntegral_sub_inv_smul (mem_ball_self hR)
  have step2 : g c = 0 := by simp [g, sub_self, zero_smul]
  have step3 : ∮ z in C(c, R), f z = ∮ z in C(c, R), (z - c)⁻¹ • g z := by
    refine circleIntegral.integral_congr hR.le fun z hz => ?_
    simp only [g, inv_smul_smul₀ (sub_ne_zero.mpr (ne_of_mem_sphere hz hR.ne'))]
  rw [step3, step1, step2, smul_zero]

/-! ## Residue definition and basic properties -/

/-- The residue of `f : ℂ → ℂ` at `c`, defined as `(2πi)⁻¹ ∮_{|z−c|=1} f(z) dz`. -/
noncomputable def residue (f : ℂ → ℂ) (c : ℂ) : ℂ :=
  (2 * ↑Real.pi * I)⁻¹ * (∮ z in C(c, 1), f z)

/-- The residue equals `(2πi)⁻¹` times the circle integral at any positive radius,
    provided `f` is continuous on the closed annulus and differentiable on its interior
    (between the unit circle and the circle of radius `R`). -/
theorem residue_eq_inv_two_pi_I_circleIntegral {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hc : ContinuousOn f (closedBall c (max 1 R) \ ball c (min 1 R)))
    (hd : ∀ z ∈ ball c (max 1 R) \ closedBall c (min 1 R),
      DifferentiableAt ℂ f z) :
    residue f c = (2 * ↑Real.pi * I)⁻¹ * (∮ z in C(c, R), f z) := by
  unfold residue
  congr 1
  rcases le_or_lt R 1 with hR1 | hR1
  · -- R ≤ 1: deform from radius 1 down to R
    have hmin : min 1 R = R := min_eq_right hR1
    have hmax : max 1 R = 1 := max_eq_left hR1
    rw [hmin, hmax] at hc hd
    exact (Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable hR hR1
      countable_empty (by rwa [diff_empty]) (fun z hz => hd z (by rwa [diff_empty] at hz))).symm
  · -- R > 1: deform from radius 1 up to R
    have hmin : min 1 R = 1 := min_eq_left hR1.le
    have hmax : max 1 R = R := max_eq_right hR1.le
    rw [hmin, hmax] at hc hd
    exact Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable one_pos hR1.le
      countable_empty (by rwa [diff_empty]) (fun z hz => hd z (by rwa [diff_empty] at hz))

/-- For a simple pole `f(z) = (z−c)⁻¹ · g(z)` with `g` analytic on `closedBall c 1`,
    the residue is `g(c)`. -/
theorem residue_eq_of_simple_pole {g : ℂ → ℂ} {c : ℂ}
    (hg : DiffContOnCl ℂ g (ball c 1)) :
    residue (fun z => (z - c)⁻¹ * g z) c = g c := by
  unfold residue
  have key : (∮ z in C(c, 1), (z - c)⁻¹ * g z) = 2 * ↑Real.pi * I * g c := by
    have h1 : (∮ z in C(c, 1), (z - c)⁻¹ • g z) = (2 * ↑Real.pi * I) • g c :=
      hg.circleIntegral_sub_inv_smul (mem_ball_self one_pos)
    simpa [smul_eq_mul] using h1
  rw [key, ← mul_assoc, inv_mul_cancel₀, one_mul]
  simp [Real.pi_ne_zero, I_ne_zero]

/-! ## Residue theorem for circle contours -/

/-- **Residue theorem** (single simple pole, circle contour):
    `∮_{|z−c|=R} g(z)/(z−c) dz = 2πi · g(c)`. -/
theorem circleIntegral_simple_pole {g : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hg : DiffContOnCl ℂ g (ball c R)) :
    (∮ z in C(c, R), (z - c)⁻¹ * g z) = 2 * ↑Real.pi * I * g c := by
  have : (∮ z in C(c, R), (z - c)⁻¹ • g z) = (2 * ↑Real.pi * I) • g c :=
    hg.circleIntegral_sub_inv_smul (mem_ball_self hR)
  simpa [smul_eq_mul] using this

/-- **Residue theorem** (simple pole at `w ≠ c`, circle contour):
    `∮_{|z−c|=R} g(z)/(z−w) dz = 2πi · g(w)` for `w ∈ ball c R`. -/
theorem circleIntegral_simple_pole_off_center {g : ℂ → ℂ} {c w : ℂ} {R : ℝ}
    (hw : w ∈ ball c R)
    (hg : DiffContOnCl ℂ g (ball c R)) :
    (∮ z in C(c, R), (z - w)⁻¹ * g z) = 2 * ↑Real.pi * I * g w := by
  have : (∮ z in C(c, R), (z - w)⁻¹ • g z) = (2 * ↑Real.pi * I) • g w :=
    hg.circleIntegral_sub_inv_smul hw
  simpa [smul_eq_mul] using this

/-- `∮_{|z−c|=R} (z−w)⁻¹ dz = 2πi` for `w` inside the circle. -/
theorem circleIntegral_sub_inv_eq_two_pi_I {c w : ℂ} {R : ℝ} (hw : w ∈ ball c R) :
    (∮ z in C(c, R), (z - w)⁻¹) = 2 * ↑Real.pi * I :=
  circleIntegral.integral_sub_inv_of_mem_ball hw

/-! ## Multi-pole residue theorem for circles -/

/-- **Residue theorem** (finitely many simple poles, circle contour):
    If `f` agrees with `h + Σ aₖ·(z−wₖ)⁻¹` on the circle, where `h` is analytic
    on the closed disk and each `wₖ` is strictly inside, then
    `∮ f = 2πi · Σ aₖ`. The `aₖ` are the residues. -/
theorem circleIntegral_eq_two_pi_I_sum_residues
    {c : ℂ} {R : ℝ} (hR : 0 < R)
    {n : ℕ} {w : Fin n → ℂ} {a : Fin n → ℂ}
    {h : ℂ → ℂ}
    (hw : ∀ k, w k ∈ ball c R)
    (hh : DiffContOnCl ℂ h (ball c R))
    {f : ℂ → ℂ}
    (hf : ∀ z ∈ sphere c R,
      f z = h z + ∑ k : Fin n, a k * (z - w k)⁻¹) :
    (∮ z in C(c, R), f z) = 2 * ↑Real.pi * I * ∑ k : Fin n, a k := by
  -- Rewrite integral using the decomposition on the sphere
  rw [circleIntegral.integral_congr hR.le hf]
  -- Split: ∮ (h + Σ aₖ/(z-wₖ)) = ∮ h + ∮ Σ aₖ/(z-wₖ)
  have hint_pole : ∀ k : Fin n,
      ContinuousOn (fun z => a k * (z - w k)⁻¹) (sphere c R) := by
    intro k
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const)
    intro z hz
    exact sub_ne_zero.mpr (ne_of_mem_of_not_mem hz (not_mem_sphere_of_lt (hw k)))
  have hint_sum : CircleIntegrable (fun z => ∑ k : Fin n, a k * (z - w k)⁻¹) c R :=
    CircleIntegrable.fun_sum _ (fun k _ =>
      (hint_pole k).circleIntegrable hR.le)
  have hint_h : CircleIntegrable h c R :=
    hh.continuousOn_ball.circleIntegrable hR.le
  rw [circleIntegral.integral_add hint_h hint_sum]
  -- ∮ h = 0 by Cauchy-Goursat
  rw [circleIntegral_eq_zero_of_diffContOnCl hR hh, zero_add]
  -- ∮ Σ aₖ/(z-wₖ) = Σ aₖ · 2πi
  rw [circleIntegral.integral_fun_sum (fun k _ => (hint_pole k).circleIntegrable hR.le)]
  simp_rw [circleIntegral.integral_const_mul,
    circleIntegral_sub_inv_eq_two_pi_I (hw ·)]
  ring

/-! ## Rectangle contour infrastructure -/

/-- Rectangle boundary integral with corners `z` and `w`:
    `∫ bottom − ∫ top + I·∫ right − I·∫ left`. -/
noncomputable def rectIntegral (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (∫ x : ℝ in z.re..w.re, f (↑x + ↑z.im * I)) -
  (∫ x : ℝ in z.re..w.re, f (↑x + ↑w.im * I)) +
  I * (∫ y : ℝ in z.im..w.im, f (↑w.re + ↑y * I)) -
  I * (∫ y : ℝ in z.im..w.im, f (↑z.re + ↑y * I))

/-- **Cauchy-Goursat for rectangles** (off-countable version). -/
theorem rectIntegral_eq_zero {f : ℂ → ℂ} {z w : ℂ} {s : Set ℂ}
    (hs : s.Countable)
    (hc : ContinuousOn f ([[z.re, w.re]] ×ℂ [[z.im, w.im]]))
    (hd : ∀ x ∈ Ioo (min z.re w.re) (max z.re w.re) ×ℂ
            Ioo (min z.im w.im) (max z.im w.im) \ s,
      DifferentiableAt ℂ f x) :
    rectIntegral f z w = 0 := by
  have := Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable
    f z w s hs hc hd
  simp only [rectIntegral]
  linarith

/-- **Cauchy-Goursat for rectangles** (differentiable-on version). -/
theorem rectIntegral_eq_zero_of_differentiableOn {f : ℂ → ℂ} {z w : ℂ}
    (hd : DifferentiableOn ℂ f ([[z.re, w.re]] ×ℂ [[z.im, w.im]])) :
    rectIntegral f z w = 0 :=
  rectIntegral_eq_zero countable_empty hd.continuousOn (fun x hx =>
    (hd.differentiableAt ((isOpen_Ioo.reProdIm isOpen_Ioo).mem_nhds hx.1)).differentiableWithinAt
    |>.differentiableAt ((isOpen_Ioo.reProdIm isOpen_Ioo).mem_nhds hx.1))

end ArithmeticHodge.Analysis

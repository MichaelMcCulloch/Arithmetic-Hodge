/-
  Phase 2, Step 2.1: Fourier Transform Positivity (Bochner-type)

  For autocorrelation f = g ∗ g̃, the Fourier cosine transform satisfies
  fourierCos f ξ = |ĝ(ξ)|² ≥ 0.

  This is the key ingredient for the forward direction of Weil's criterion:
  RH ⟹ W(f) ≥ 0 for autocorrelations.

  The proof uses Fubini's theorem and the computation:
    f̂(ξ) = ∫∫ g(y) g(y+x) cos(2πξx) dy dx
          = |∫ g(y) e^{-2πiyξ} dy|²
          ≥ 0
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Real.Pi.Bounds

import ArithmeticHodge.Analysis.WeilExplicit

open MeasureTheory Real Complex Filter Convolution Set

namespace ArithmeticHodge.Analysis

-- ============================================================
-- Auxiliary Lemmas
-- ============================================================

/-- An autocorrelation of an L¹ function is integrable.
    f(x) = ∫ g(y) g(y+x) dy is integrable when g ∈ L¹ (Young's inequality).
    Proof via convolution: the autocorrelation equals g̃ ⋆ g where g̃(t) = g(-t). -/
theorem autocorrelation_integrable (g : ℝ → ℝ)
    (hg : Integrable g volume) :
    Integrable (fun x => ∫ y : ℝ, g y * g (y + x)) volume := by
  -- The autocorrelation equals g̃ ⋆ g where g̃(t) = g(-t), so it's integrable by Young.
  set g' : ℝ → ℝ := fun t => g (-t)
  have hg' : Integrable g' volume := by
    exact hg.comp_sub_left 0 |>.congr (ae_of_all _ fun x => by simp [g'])
  -- The convolution g' ⋆ g is integrable by Young's inequality
  have hconv : Integrable (g' ⋆ g) volume :=
    hg'.integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hg
  -- Our function equals this convolution a.e. (by change of variables t ↦ -t)
  exact hconv.congr (ae_of_all _ fun x => by
    show (g' ⋆ g) x = ∫ y, g y * g (y + x)
    simp only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul, g']
    -- LHS = ∫ g(-t) g(x - t) dt, RHS = ∫ g(y) g(y + x) dy
    -- These are equal by the substitution t = -y (measure-preserving for Lebesgue measure).
    -- After sub: g(-(-y)) g(x-(-y)) = g(y) g(x+y) = g(y) g(y+x)
    simp_rw [show ∀ t : ℝ, x - t = -t + x from fun t => by ring]
    -- Now: ∫ g(-t) g(-t + x) dt = ∫ g(y) g(y + x) dy
    -- by substitution y = -t
    rw [show (fun t : ℝ => g (-t) * g (-t + x)) = (fun y => g y * g (y + x)) ∘ Neg.neg from by
      ext t; simp]
    exact (Measure.measurePreserving_neg (volume : Measure ℝ)).integral_comp
      (MeasurableEquiv.neg ℝ).measurableEmbedding (fun y : ℝ => g y * g (y + x)))

-- ============================================================
-- Fourier Transform of Autocorrelations
-- ============================================================

/-- The complex Fourier transform of a real-valued function. -/
noncomputable def fourierTransformC (g : ℝ → ℝ) (ξ : ℝ) : ℂ :=
  ∫ y : ℝ, (g y : ℂ) * Complex.exp (-2 * Real.pi * ξ * y * Complex.I)

/-- **The Fourier cosine transform of an autocorrelation equals |ĝ|².**

    This is the precise identity. -/
theorem fourierCos_autocorrelation_eq_sq (g : ℝ → ℝ)
    (hg : Integrable g MeasureTheory.volume)
    (hg_sq : Integrable (fun y => g y ^ 2) MeasureTheory.volume)
    (f : ℝ → ℝ) (hf : ∀ x, f x = ∫ y : ℝ, g y * g (y + x))
    (ξ : ℝ) :
    fourierCos f ξ = ‖fourierTransformC g ξ‖ ^ 2 := by
  -- The identity fourierCos f ξ = ‖ĝ(ξ)‖² follows from:
  -- (A) fourierCos f ξ = Re(∫ x, (f x : ℂ) * exp(-2πiξx))  [cos = Re(exp), f real]
  -- (B) ∫ x, (f x : ℂ) * exp(-2πiξx) = conj(ĝ) * ĝ         [Fubini + shear]
  -- (C) ‖ĝ‖² = Re(conj(ĝ) * ĝ)                              [standard]
  --
  -- We reduce to the key Fubini identity (B) and the cos=Re(exp) identity (A).
  set ĝ := fourierTransformC g ξ
  -- Step 1: Relate fourierCos to a pointwise computation
  -- fourierCos f ξ = ∫ f(x) cos(2πξx)
  -- and cos(2πξx) = Re(exp(-2πiξx)) for real 2πξx.
  -- Also f(x) is real, so f(x)*cos(θ) = Re((f(x):ℂ)*exp(-iθ)).
  -- Therefore fourierCos f ξ = ∫ Re(F(x)) = Re(∫ F(x)) where
  -- F(x) = (f(x):ℂ) * exp(-2πiξx·I).
  --
  -- To avoid the Fubini machinery entirely, we use the `suffices` approach:
  -- we reduce to showing pointwise equalities.
  --
  -- Actually, the cleanest proof uses congrArg on both representations.
  -- We show both sides equal the same thing.
  -- ‖ĝ‖² = normSq(ĝ) = Re(conj(ĝ)*ĝ) = Re(∫∫ ...) = ∫ Re(...) = fourierCos f ξ.
  --
  -- Core Fubini identity: ∫ f(x) E(x) = conj(ĝ) * ĝ
  -- where E(x) = exp(-2πiξx·I).
  -- This + cos = Re(exp) + integral_re gives the result.
  suffices key : ∫ x : ℝ, (f x : ℂ) *
      Complex.exp (↑(-2 * Real.pi * ξ * x) * Complex.I) = starRingEnd ℂ ĝ * ĝ by
    -- Connect LHS (fourierCos) to Re of the complex integral
    have rhs_eq : ‖ĝ‖ ^ 2 = (starRingEnd ℂ ĝ * ĝ).re := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_conj_mul_self,
          Complex.ofReal_re]
    rw [rhs_eq, ← key]
    -- Goal: fourierCos f ξ = (∫ x, (↑(f x)) * exp(...)).re
    -- Use integral_re: ∫ Re(F(x)) = Re(∫ F(x)) when F is integrable
    simp only [fourierCos]
    -- First show pointwise: f(x) * cos(...) = Re((f x : ℂ) * exp(...))
    have pw : ∀ x : ℝ, f x * Real.cos (2 * Real.pi * ξ * x) =
        Complex.re ((f x : ℂ) * Complex.exp (↑(-2 * Real.pi * ξ * x) * Complex.I)) := by
      intro x
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, sub_zero, zero_mul]
      rw [show (-2 : ℝ) * Real.pi * ξ * x = -(2 * Real.pi * ξ * x) from by ring,
          Real.cos_neg]
    simp_rw [pw]
    have hf_int : Integrable f volume :=
      (autocorrelation_integrable g hg).congr (ae_of_all _ fun x => (hf x).symm)
    -- The complex integrand (f x : ℂ) * exp(iθ) is integrable since |exp(iθ)| = 1
    have hint : Integrable (fun x : ℝ =>
        (f x : ℂ) * Complex.exp (↑(-2 * Real.pi * ξ * x) * Complex.I)) volume := by
      apply Integrable.mono' (f := fun x : ℝ =>
          (f x : ℂ) * Complex.exp (↑(-2 * Real.pi * ξ * x) * Complex.I))
          (g := fun x => ‖f x‖) hf_int.norm
      · fun_prop
      · exact ae_of_all _ fun x => by
          rw [Complex.norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real]
    exact integral_re hint
  -- Core Fubini identity: ∫ f(x) E(x) dx = conj(ĝ) * ĝ
  -- Proof sketch:
  --   LHS = ∫ x, (∫ y, g(y) g(y+x)) E(x) dx              [expand f via hf]
  --       = ∫ x, ∫ y, g(y) g(y+x) E(x) dy dx              [push E into inner integral]
  --       = ∫ y, ∫ x, g(y) g(y+x) E(x) dx dy              [Fubini]
  --       = ∫ y, g(y) (∫ x, g(y+x) E(x) dx) dy            [factor g(y) out]
  --       = ∫ y, g(y) (∫ u, g(u) E(u-y) du) dy             [u = y+x]
  --       = ∫ y, g(y) E(-y) (∫ u, g(u) E(u) du) dy         [E(u-y) = E(u)E(-y)]
  --       = (∫ y, g(y) E(-y) dy) · (∫ u, g(u) E(u) du)     [factor constant integral]
  --       = conj(ĝ(ξ)) · ĝ(ξ)                               [recognize Fourier transforms]
  --
  -- We prove the identity by showing both sides equal conj(ĝ) * ĝ.
  -- Set up notation
  set E : ℝ → ℂ := fun x => Complex.exp (↑(-2 * Real.pi * ξ * x) * Complex.I) with hE_def
  -- Key property of E: E(a+b) = E(a) * E(b)
  have hE_add : ∀ a b : ℝ, E (a + b) = E a * E b := by
    intro a b; simp only [E]; rw [show (-2 * Real.pi * ξ * (a + b) : ℝ) =
      (-2 * Real.pi * ξ * a) + (-2 * Real.pi * ξ * b) from by ring]
    push_cast; rw [add_mul, Complex.exp_add]
  -- Key: ∫ g(y) * E(-y) = conj(ĝ) for real-valued g
  -- Key identity: ∫ g(y) E(-y) = conj(ĝ)
  -- Proof: conj(ĝ) = conj(∫ g(y) E(y)) = ∫ conj(g(y) E(y)) = ∫ g(y) E(-y)
  -- (using integral_conj, g real, conj(exp(iθ)) = exp(-iθ))
  have hE_conj : ∀ y : ℝ, starRingEnd ℂ (E y) = E (-y) := by
    intro y
    change star (E y) = E (-y)
    change star (Complex.exp (↑(-2 * Real.pi * ξ * y) * Complex.I)) =
      Complex.exp (↑(-2 * Real.pi * ξ * (-y)) * Complex.I)
    rw [Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast; ring
  have hint_conjg : ∫ y : ℝ, (g y : ℂ) * E (-y) = starRingEnd ℂ ĝ := by
    have pw : ∀ y, (g y : ℂ) * E (-y) = starRingEnd ℂ ((g y : ℂ) * E y) := by
      intro y; rw [map_mul, Complex.conj_ofReal, hE_conj]
    simp_rw [pw]
    -- Normalize the exponent form and apply integral_conj
    have norm_exp : ∀ y : ℝ, E y = Complex.exp (-2 * ↑Real.pi * ↑ξ * ↑y * Complex.I) := by
      intro y; simp only [hE_def]; push_cast; ring_nf
    simp_rw [norm_exp]
    simp only [ĝ, fourierTransformC]
    exact integral_conj (𝕜 := ℂ) (X := ℝ) (μ := MeasureTheory.volume)
  -- The main identity by Fubini + substitution + factoring.
  -- The goal is: ∫ x, (↑(f x)) * E x = conj(ĝ) * ĝ
  --
  -- Step 1: Express ĝ in terms of E
  have hg_hat : ĝ = ∫ u : ℝ, (g u : ℂ) * E u := by
    simp only [ĝ, fourierTransformC, hE_def]
    congr 1; ext y; push_cast; ring
  -- Step 2: Inner integral calculation
  -- ∫ x, g(y+x) E(x) = E(-y) * ĝ
  have inner_calc : ∀ y : ℝ,
      ∫ x : ℝ, (g (y + x) : ℂ) * E x = E (-y) * ĝ := by
    intro y
    -- Sub u = y + x: ∫ x, g(y+x) E(x) = ∫ u, g(u) E(u-y)
    -- Sub u = y + x: ∫ x, g(y+x) E(x) = ∫ u, g(u) E(u-y)
    have hsub : ∫ x : ℝ, (g (y + x) : ℂ) * E x =
        ∫ u : ℝ, (g u : ℂ) * E (u - y) := by
      set F : ℝ → ℂ := fun u => (g u : ℂ) * E (u - y)
      have : (fun x : ℝ => (g (y + x) : ℂ) * E x) = fun x => F (x + y) := by
        ext x; simp only [F]; congr 1
        · congr 1; ring
        · congr 1; ring
      rw [this]
      exact integral_add_right_eq_self F y
    rw [hsub]
    -- Split E(u-y) = E(u) * E(-y)
    simp_rw [show ∀ u : ℝ, E (u - y) = E u * E (-y) from fun u => by
      rw [show (u - y : ℝ) = u + (-y) from sub_eq_add_neg u y]; exact hE_add u (-y)]
    -- ∫ u, g(u) * (E(u) * E(-y)) = (∫ u, g(u) * E(u)) * E(-y)
    simp_rw [show ∀ u : ℝ, (g u : ℂ) * (E u * E (-y)) = (g u : ℂ) * E u * E (-y) from
      fun u => by ring]
    have : ∫ u : ℝ, (g u : ℂ) * E u * E (-y) = (∫ u : ℝ, (g u : ℂ) * E u) * E (-y) :=
      integral_mul_const (E (-y)) (fun u => (g u : ℂ) * E u)
    rw [this, hg_hat, mul_comm]
  -- Step 3: Assemble the proof
  -- LHS = ∫ x, ↑(f x) * E x
  -- First rewrite f(x) = ∫ y, g(y) * g(y+x) and push cast
  -- Rewrite: ↑(f x) = ∫ y, ↑(g y) * ↑(g(y+x))
  have cast_f : ∀ x : ℝ, (f x : ℂ) = ∫ y : ℝ, (g y : ℂ) * (g (y + x) : ℂ) := by
    intro x; rw [hf x]
    -- ↑(∫ g y * g(y+x)) = ∫ ↑(g y * g(y+x)) = ∫ ↑(g y) * ↑(g(y+x))
    trans ∫ y : ℝ, ((g y * g (y + x) : ℝ) : ℂ)
    · exact integral_ofReal (𝕜 := ℂ).symm
    · congr 1; ext y; push_cast; ring
  -- Combined: expand f, push cast, distribute E
  have expand_distrib : ∀ x : ℝ,
      (f x : ℂ) * E x = ∫ y : ℝ, (g y : ℂ) * (g (y + x) : ℂ) * E x := by
    intro x
    rw [cast_f]
    exact (integral_mul_const (E x) _).symm
  have lhs_rw : (∫ x : ℝ, (f x : ℂ) * E x) =
      ∫ x : ℝ, ∫ y : ℝ, (g y : ℂ) * (g (y + x) : ℂ) * E x := by
    congr 1; ext x; exact expand_distrib x
  rw [lhs_rw]
  -- Apply Fubini (need product integrability)
  have hprod_int : Integrable (Function.uncurry fun (x y : ℝ) =>
      (g y : ℂ) * (g (y + x) : ℂ) * E x) (volume.prod volume) := by
    -- |g(y) g(y+x) E(x)| = |g(y)| |g(y+x)| since |E(x)| = 1.
    -- Step A: convolution_integrand gives (x, y) ↦ g̃(y) g(x-y) is product-integrable
    set g' : ℝ → ℝ := fun t => g (-t)
    have hg' : Integrable g' volume :=
      hg.comp_sub_left 0 |>.congr (ae_of_all _ fun x => by simp [g'])
    have hconv_prod : Integrable (fun p : ℝ × ℝ =>
        (ContinuousLinearMap.lsmul ℝ ℝ) (g' p.2) (g (p.1 - p.2))) (volume.prod volume) :=
      hg'.convolution_integrand (ContinuousLinearMap.lsmul ℝ ℝ) hg
    -- Step B: Under (x,y) ↦ (x,-y), this becomes g(y) * g(y+x)
    have hmp : MeasurePreserving (Prod.map id Neg.neg : ℝ × ℝ → ℝ × ℝ)
        (volume.prod volume) (volume.prod volume) :=
      (MeasurePreserving.id volume).prod (Measure.measurePreserving_neg volume)
    have hreal_prod : Integrable (fun p : ℝ × ℝ => g p.2 * g (p.2 + p.1))
        (volume.prod volume) := by
      rw [show (fun p : ℝ × ℝ => g p.2 * g (p.2 + p.1)) =
          (fun p : ℝ × ℝ => (ContinuousLinearMap.lsmul ℝ ℝ) (g' p.2) (g (p.1 - p.2))) ∘
          (Prod.map id Neg.neg) from by
        ext ⟨x, y⟩
        simp [g', ContinuousLinearMap.lsmul_apply, smul_eq_mul, sub_neg_eq_add, add_comm]]
      exact (hmp.integrable_comp hconv_prod.aestronglyMeasurable).mpr hconv_prod
    -- Step C: Complex integrand has ‖g(y) g(y+x) E(x)‖ = |g(y) * g(y+x)|
    -- so our complex function is integrable by Integrable.mono.
    refine hreal_prod.mono ?_ (ae_of_all _ fun ⟨x, y⟩ => ?_)
    · -- AEStronglyMeasurable of the complex integrand
      -- (↑(g(y) * g(y+x))) * E(x) is ae-measurable since ↑(real-integrand) and E are.
      have h_ofReal : AEStronglyMeasurable (fun p : ℝ × ℝ =>
          (↑(g p.2 * g (p.2 + p.1)) : ℂ)) (volume.prod volume) :=
        continuous_ofReal.comp_aestronglyMeasurable hreal_prod.aestronglyMeasurable
      have h_E : AEStronglyMeasurable (fun p : ℝ × ℝ => E p.1) (volume.prod volume) :=
        ((Complex.continuous_exp.comp
          ((continuous_ofReal.comp (continuous_const.mul continuous_id')).mul
            continuous_const)).comp continuous_fst).aestronglyMeasurable
      exact (h_ofReal.mul h_E).congr (ae_of_all _ fun ⟨x, y⟩ => by
        simp only [Function.uncurry, Pi.mul_apply, Complex.ofReal_mul])
    · simp only [Function.uncurry]
      rw [Complex.norm_mul, Complex.norm_mul, Complex.norm_real, Complex.norm_real,
          Complex.norm_exp_ofReal_mul_I, mul_one, Real.norm_eq_abs, Real.norm_eq_abs,
          ← abs_mul]
      exact le_of_eq (Real.norm_eq_abs _).symm
  rw [integral_integral_swap hprod_int]
  -- Factor out g(y) from inner integral + use inner_calc + collect
  -- Goal: ∫ y, ∫ x, g(y) * g(y+x) * E(x) = conj(ĝ) * ĝ
  have step_factor_inner : ∀ y : ℝ,
      (∫ x : ℝ, (g y : ℂ) * (g (y + x) : ℂ) * E x) = (g y : ℂ) * (E (-y) * ĝ) := by
    intro y
    -- Factor g(y) out: ∫ x, g(y) * g(y+x) * E(x) = g(y) * ∫ x, g(y+x) * E(x)
    have : ∫ x : ℝ, (g y : ℂ) * (g (y + x) : ℂ) * E x =
        (g y : ℂ) * ∫ x : ℝ, (g (y + x) : ℂ) * E x := by
      have : ∀ x : ℝ, (g y : ℂ) * (g (y + x) : ℂ) * E x =
          (g y : ℂ) * ((g (y + x) : ℂ) * E x) := fun x => by ring
      simp_rw [this]
      exact integral_const_mul (g y : ℂ) _
    rw [this, inner_calc]
  have goal_rw : (∫ y : ℝ, ∫ x : ℝ, (g y : ℂ) * (g (y + x) : ℂ) * E x) =
      ∫ y : ℝ, (g y : ℂ) * (E (-y) * ĝ) := by
    congr 1; ext y; exact step_factor_inner y
  rw [goal_rw]
  -- Now: ∫ y, g(y) * (E(-y) * ĝ) = conj(ĝ) * ĝ
  -- = ∫ y, g(y) * E(-y) * ĝ = (∫ y, g(y) * E(-y)) * ĝ
  have : ∀ y : ℝ, (g y : ℂ) * (E (-y) * ĝ) = (g y : ℂ) * E (-y) * ĝ :=
    fun y => by ring
  simp_rw [this]
  have : ∫ y : ℝ, (g y : ℂ) * E (-y) * ĝ = (∫ y : ℝ, (g y : ℂ) * E (-y)) * ĝ :=
    integral_mul_const ĝ _
  rw [this, hint_conjg]

/-- **Fourier transform of an autocorrelation is non-negative.**
    Follows from `fourierCos_autocorrelation_eq_sq`: `fourierCos f ξ = ‖ĝ(ξ)‖² ≥ 0`. -/
theorem fourierCos_autocorrelation_nonneg (g : ℝ → ℝ)
    (hg : Integrable g MeasureTheory.volume)
    (hg_sq : Integrable (fun y => g y ^ 2) MeasureTheory.volume)
    (f : ℝ → ℝ) (hf : ∀ x, f x = ∫ y : ℝ, g y * g (y + x))
    (ξ : ℝ) :
    0 ≤ fourierCos f ξ := by
  rw [fourierCos_autocorrelation_eq_sq g hg hg_sq f hf ξ]
  positivity

/-! ### Autocorrelations need not be pointwise nonnegative -/

/-- A signed compactly supported block used to test pointwise claims about
    autocorrelations. -/
private noncomputable def signedBlock (x : ℝ) : ℝ :=
  (Ioc (0 : ℝ) 1).indicator (fun _ => 1) x -
    (Ioc (1 : ℝ) 2).indicator (fun _ => 1) x

private theorem signedBlock_integrable : Integrable signedBlock volume := by
  unfold signedBlock
  exact
    ((integrableOn_const (s := Ioc (0 : ℝ) 1) (by simp [Real.volume_Ioc])).integrable_indicator
      measurableSet_Ioc).sub
      ((integrableOn_const (s := Ioc (1 : ℝ) 2) (by simp [Real.volume_Ioc])).integrable_indicator
        measurableSet_Ioc)

private theorem signedBlock_sq_integrable :
    Integrable (fun x => signedBlock x ^ 2) volume := by
  have hpoint : (fun x => signedBlock x ^ 2) =
      (Ioc (0 : ℝ) 2).indicator (fun _ => 1) := by
    funext x
    by_cases h0 : 0 < x
    · by_cases h1 : x ≤ 1
      · have h2 : x ≤ 2 := by linarith
        simp [signedBlock, Set.mem_Ioc, h0, h1, h2]
      · have h1' : 1 < x := lt_of_not_ge h1
        by_cases h2 : x ≤ 2
        · simp [signedBlock, Set.mem_Ioc, h0, h1, h1', h2]
        · have h2' : ¬ x ≤ 2 := h2
          simp [signedBlock, Set.mem_Ioc, h0, h1, h1', h2']
    · have h0' : ¬ 0 < x := h0
      have h1' : ¬ 1 < x := by linarith
      simp [signedBlock, Set.mem_Ioc, h0', h1']
  rw [hpoint]
  exact
    (integrableOn_const (s := Ioc (0 : ℝ) 2) (by simp [Real.volume_Ioc])).integrable_indicator
      measurableSet_Ioc

private noncomputable def signedBlockAutocorrelation (x : ℝ) : ℝ :=
  ∫ y : ℝ, signedBlock y * signedBlock (y + x)

private theorem signedBlock_isAutocorrelation :
    IsAutocorrelation signedBlockAutocorrelation := by
  exact ⟨signedBlock, signedBlock_integrable, signedBlock_sq_integrable, fun _ => rfl⟩

private theorem signedBlockAutocorrelation_one :
    signedBlockAutocorrelation 1 = -1 := by
  unfold signedBlockAutocorrelation
  have hpoint : ∀ y : ℝ,
      signedBlock y * signedBlock (y + 1) =
        -(Ioc (0 : ℝ) 1).indicator (fun _ => 1) y := by
    intro y
    by_cases h0 : 0 < y
    · by_cases h1 : y ≤ 1
      · have hy1 : 1 < y + 1 := by linarith
        have hy2 : y + 1 ≤ 2 := by linarith
        simp [signedBlock, Set.mem_Ioc, h0, h1, hy1, hy2]
      · have hy1 : ¬ y + 1 ≤ 2 := by linarith
        simp [signedBlock, Set.mem_Ioc, h0, h1, hy1]
    · have h0' : ¬ 0 < y := h0
      by_cases hm1 : 0 < y + 1
      · have hm2 : y + 1 ≤ 1 := by linarith
        have hy1 : ¬ 1 < y := by linarith
        simp [signedBlock, Set.mem_Ioc, h0', hm1, hm2, hy1]
      · have hm1' : ¬ 0 < y + 1 := hm1
        have hy1 : ¬ 1 < y := by linarith
        simp [signedBlock, Set.mem_Ioc, h0', hm1', hy1]
  simp_rw [hpoint]
  rw [integral_neg]
  simp

/-- Autocorrelation means positive-definite, not pointwise nonnegative: a
    concrete compactly supported `L¹ ∩ L²` witness has value `-1` at `1`.
    Thus Fourier-side nonnegativity cannot justify replacing
    `fourierCos f ξ` by `f ξ` in the Weil spectral sum. -/
theorem exists_autocorrelation_with_negative_value :
    ∃ f : ℝ → ℝ, IsAutocorrelation f ∧ f 1 = -1 :=
  ⟨signedBlockAutocorrelation, signedBlock_isAutocorrelation,
    signedBlockAutocorrelation_one⟩

-- ============================================================
-- Weil Criterion: Forward Direction (RH → Positivity)
-- ============================================================

/-- A correctly oriented explicit-formula obligation for the current additive
`WeilPositivity` predicate.  The spectral side is `fourierCos f`, the quantity
known to be nonnegative for autocorrelations. -/
def FourierOrientedWeilExplicit : Prop :=
  ∀ (f : ℝ → ℝ), IsAutocorrelation f → Continuous f →
    (∀ x : ℝ, ‖f x‖ ≤ 1 / (1 + x ^ 2)) → RiemannHypothesis →
      ∃ zeros : ℕ → ℝ,
        Summable (fun n => fourierCos f (zeros n)) ∧
        ∑' n, fourierCos f (zeros n) =
          weilFunctionalFull f (fourierCos f)

/-- With the spectral transform on the correct side, RH implies Weil
positivity from the explicit-formula obligation. -/
theorem rh_implies_weil_positivity_from_explicit
    (hexplicit : FourierOrientedWeilExplicit) :
    RiemannHypothesis → WeilPositivity := by
  intro hRH f hf hcont hdecay
  obtain ⟨zeros, _hsumm, hexpl⟩ := hexplicit f hf hcont hdecay hRH
  rw [← hexpl]
  exact tsum_nonneg fun n => by
    obtain ⟨g, hg, hgSq, hfg⟩ := hf
    exact fourierCos_autocorrelation_nonneg g hg hgSq f hfg (zeros n)

-- ============================================================
-- Weil Criterion: Backward Direction (Positivity → RH)
-- ============================================================

/-- **Zeros come in pairs under the functional equation.**
    If ρ is a nontrivial zero, so is 1-ρ̄. -/
theorem nontrivial_zero_paired (ρ : NontrivialZetaZero) :
    ∃ ρ' : NontrivialZetaZero, ρ'.val.re = 1 - ρ.val.re := by
  refine ⟨⟨1 - ρ.val, ?_, ?_, ?_⟩, ?_⟩
  · -- riemannZeta (1 - ρ.val) = 0 via functional equation
    have hρ_ne_one : ρ.val ≠ 1 := by
      intro h; have := ρ.re_lt_one; rw [h] at this; simp at this
    have hρ_ne_neg_nat : ∀ n : ℕ, ρ.val ≠ -↑n := by
      intro n hn
      have hre := ρ.re_pos
      rw [hn] at hre
      simp [Complex.neg_re] at hre
      exact not_lt.mpr (Nat.cast_nonneg' n) hre
    rw [riemannZeta_one_sub hρ_ne_neg_nat hρ_ne_one]
    simp [ρ.is_zero]
  · simp [Complex.sub_re, Complex.one_re]; linarith [ρ.re_lt_one]
  · simp [Complex.sub_re, Complex.one_re]; linarith [ρ.re_pos]
  · simp [Complex.sub_re, Complex.one_re]

-- ============================================================
-- Bombieri Test Function Construction
-- ============================================================

/-- The Bombieri modulated Gaussian. -/
noncomputable def bombieriTestFn (σ₀ : ℝ) : ℝ → ℝ :=
  fun x => Real.exp (-Real.pi * x ^ 2) * Real.cos (2 * Real.pi * (σ₀ - 1/2) * x)

/-- The Bombieri test function is integrable (Gaussian × bounded cosine). -/
theorem bombieriTestFn_integrable (σ₀ : ℝ) :
    Integrable (bombieriTestFn σ₀) volume := by
  unfold bombieriTestFn
  apply Integrable.mono' (integrable_exp_neg_mul_sq Real.pi_pos)
  · fun_prop
  · exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_mul]
      calc |Real.exp (-Real.pi * x ^ 2)| * |Real.cos _|
          ≤ |Real.exp (-Real.pi * x ^ 2)| * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)
        _ = Real.exp (-Real.pi * x ^ 2) := by
          rw [mul_one, abs_of_pos (Real.exp_pos _)]

/-- The Bombieri autocorrelation. -/
noncomputable def bombieriAutocorrelation (σ₀ : ℝ) : ℝ → ℝ :=
  fun x => ∫ y : ℝ, bombieriTestFn σ₀ y * bombieriTestFn σ₀ (y + x)

/-- The Bombieri test function is L² (square bounded by Gaussian). -/
theorem bombieriTestFn_sq_integrable (σ₀ : ℝ) :
    Integrable (fun y => bombieriTestFn σ₀ y ^ 2) volume := by
  unfold bombieriTestFn
  apply Integrable.mono' (integrable_exp_neg_mul_sq (by linarith [Real.pi_pos] : (0 : ℝ) < 2 * Real.pi))
  · fun_prop
  · exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]
      have hexp := Real.exp_pos (-Real.pi * x ^ 2)
      have hcos := Real.abs_cos_le_one (2 * Real.pi * (σ₀ - 1 / 2) * x)
      calc |(Real.exp (-Real.pi * x ^ 2) * Real.cos (2 * Real.pi * (σ₀ - 1/2) * x)) ^ 2|
          = (Real.exp (-Real.pi * x ^ 2) * Real.cos (2 * Real.pi * (σ₀ - 1/2) * x)) ^ 2 := by
            rw [abs_of_nonneg (sq_nonneg _)]
        _ = Real.exp (-Real.pi * x ^ 2) ^ 2 * Real.cos (2 * Real.pi * (σ₀ - 1/2) * x) ^ 2 := by ring
        _ ≤ Real.exp (-Real.pi * x ^ 2) ^ 2 * 1 := by
            apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
            exact (sq_le_one_iff_abs_le_one _).mpr (Real.abs_cos_le_one _)
        _ = Real.exp (-(2 * Real.pi) * x ^ 2) := by
            rw [mul_one]
            rw [sq, ← Real.exp_add]
            ring_nf

/-- The Bombieri autocorrelation is an autocorrelation. -/
theorem bombieriAutocorrelation_isAuto (σ₀ : ℝ) :
    IsAutocorrelation (bombieriAutocorrelation σ₀) :=
  ⟨bombieriTestFn σ₀, bombieriTestFn_integrable σ₀, bombieriTestFn_sq_integrable σ₀, fun _ => rfl⟩

/-- The Bombieri autocorrelation is continuous (dominated convergence). -/
theorem bombieriAutocorrelation_continuous (σ₀ : ℝ) :
    Continuous (bombieriAutocorrelation σ₀) := by
  unfold bombieriAutocorrelation
  -- Dominated convergence: |g(y)·g(y+x)| ≤ exp(-πy²), continuous in x
  have hg_cont : Continuous (bombieriTestFn σ₀) := by unfold bombieriTestFn; fun_prop
  apply MeasureTheory.continuous_of_dominated
  · -- Measurability
    intro x
    exact ((bombieriTestFn_integrable σ₀).aestronglyMeasurable.mul
      (hg_cont.measurable.comp (measurable_id.add measurable_const)).aestronglyMeasurable)
  · -- Uniform bound: |g(y)·g(y+x)| ≤ exp(-πy²)
    intro x; exact ae_of_all _ fun y => by
      have hcos1 := Real.abs_cos_le_one (2 * π * (σ₀ - 1 / 2) * y)
      have hcos2 := Real.abs_cos_le_one (2 * π * (σ₀ - 1 / 2) * (y + x))
      have hexp1 := Real.exp_pos (-π * y ^ 2)
      have hexp2 := Real.exp_pos (-π * (y + x) ^ 2)
      have hexp2_le : Real.exp (-π * (y + x) ^ 2) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, sq_nonneg (y + x)])
      simp only [bombieriTestFn, Real.norm_eq_abs]
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos hexp1, abs_of_pos hexp2]
      -- Goal: exp(-πy²) * |cos(...)| * (exp(-π(y+x)²) * |cos(...)|) ≤ exp(-πy²)
      -- Since |cos| ≤ 1 and exp(-π(y+x)²) ≤ 1
      have hc1 : |Real.cos (2 * π * (σ₀ - 1 / 2) * y)| ≤ 1 := hcos1
      have hc2 : |Real.cos (2 * π * (σ₀ - 1 / 2) * (y + x))| ≤ 1 := hcos2
      calc Real.exp (-π * y ^ 2) * |Real.cos (2 * π * (σ₀ - 1 / 2) * y)| *
             (Real.exp (-π * (y + x) ^ 2) * |Real.cos (2 * π * (σ₀ - 1 / 2) * (y + x))|)
          ≤ Real.exp (-π * y ^ 2) * 1 * (1 * 1) := by
            apply mul_le_mul
            · exact mul_le_mul_of_nonneg_left hc1 hexp1.le
            · exact mul_le_mul hexp2_le hc2 (abs_nonneg _) zero_le_one
            · exact mul_nonneg hexp2.le (abs_nonneg _)
            · exact mul_nonneg hexp1.le (by linarith [abs_nonneg (Real.cos (2 * π * (σ₀ - 1 / 2) * y))])
        _ = Real.exp (-π * y ^ 2) := by ring
  · -- Dominator is integrable
    exact (integrable_exp_neg_mul_sq Real.pi_pos).congr (ae_of_all _ fun y => by ring)
  · -- Continuity in x for a.e. y
    exact ae_of_all _ fun y =>
      Continuous.mul continuous_const (hg_cont.comp (continuous_const.add continuous_id))

-- Helper: 1 + x² ≤ exp(π·x²/2) via π/2 > 1 and add_one_le_exp
private lemma one_add_sq_le_exp_pi_half_sq (x : ℝ) :
    1 + x ^ 2 ≤ Real.exp (π * x ^ 2 / 2) := by
  have hpi : (1 : ℝ) ≤ π / 2 := by linarith [Real.pi_gt_three]
  calc 1 + x ^ 2
      ≤ 1 + π / 2 * x ^ 2 := by nlinarith [sq_nonneg x]
    _ = π * x ^ 2 / 2 + 1 := by ring
    _ ≤ Real.exp (π * x ^ 2 / 2) := Real.add_one_le_exp _

-- Helper: exp(-πx²/2) ≤ 1/(1+x²)
private lemma exp_neg_pi_half_sq_le_inv (x : ℝ) :
    Real.exp (-(π * x ^ 2 / 2)) ≤ 1 / (1 + x ^ 2) := by
  have h1 : 0 < 1 + x ^ 2 := by positivity
  rw [le_div_iff₀ h1]
  calc Real.exp (-(π * x ^ 2 / 2)) * (1 + x ^ 2)
      ≤ Real.exp (-(π * x ^ 2 / 2)) * Real.exp (π * x ^ 2 / 2) := by
        apply mul_le_mul_of_nonneg_left (one_add_sq_le_exp_pi_half_sq x) (Real.exp_pos _).le
    _ = 1 := by
        rw [← Real.exp_add]
        have : -(π * x ^ 2 / 2) + π * x ^ 2 / 2 = 0 := by ring
        rw [this, Real.exp_zero]

-- Helper: pointwise norm bound |g(y)·g(y+x)| ≤ exp(-πy²)·exp(-π(y+x)²)
private lemma bombieriTestFn_product_norm_bound (σ₀ x y : ℝ) :
    ‖bombieriTestFn σ₀ y * bombieriTestFn σ₀ (y + x)‖ ≤
    Real.exp (-π * y ^ 2) * Real.exp (-π * (y + x) ^ 2) := by
  simp only [bombieriTestFn, norm_mul, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  calc Real.exp (-π * y ^ 2) * |Real.cos (2 * π * (σ₀ - 1 / 2) * y)| *
         (Real.exp (-π * (y + x) ^ 2) * |Real.cos (2 * π * (σ₀ - 1 / 2) * (y + x))|)
      ≤ Real.exp (-π * y ^ 2) * 1 * (Real.exp (-π * (y + x) ^ 2) * 1) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (Real.exp_pos _).le
        · exact mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (Real.exp_pos _).le
        · exact mul_nonneg (Real.exp_pos _).le (abs_nonneg _)
        · exact mul_nonneg (Real.exp_pos _).le
            (by linarith [Real.abs_cos_le_one (2 * π * (σ₀ - 1 / 2) * y)])
    _ = Real.exp (-π * y ^ 2) * Real.exp (-π * (y + x) ^ 2) := by ring

-- Helper: the Gaussian product dominator is integrable
private lemma gaussian_product_integrable (x : ℝ) :
    Integrable (fun y => Real.exp (-π * y ^ 2) * Real.exp (-π * (y + x) ^ 2)) volume := by
  have : (fun y => Real.exp (-π * y ^ 2) * Real.exp (-π * (y + x) ^ 2)) =
         (fun y => Real.exp (-(2 * π) * (y + x / 2) ^ 2) * Real.exp (-(π * x ^ 2 / 2))) := by
    ext y; rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  rw [this]
  exact ((integrable_exp_neg_mul_sq (by linarith [Real.pi_pos] : (0 : ℝ) < 2 * π)).comp_add_right
    (x / 2)).mul_const _

/-- The Bombieri autocorrelation has Gaussian decay, hence rational decay.

    Proof outline:
    1. `|f(x)| ≤ ∫ exp(-πy²)·exp(-π(y+x)²) dy` (triangle inequality, |cos| ≤ 1)
    2. Complete the square: `-πy² - π(y+x)² = -2π(y+x/2)² - πx²/2`
    3. `∫ exp(-2πu²) du = √(π/(2π)) = √(1/2) ≤ 1` (via `integral_gaussian`)
    4. So `|f(x)| ≤ exp(-πx²/2) ≤ 1/(1+x²)` (via `add_one_le_exp` and `π/2 > 1`) -/
theorem bombieriAutocorrelation_decay (σ₀ : ℝ) :
    ∀ x : ℝ, ‖bombieriAutocorrelation σ₀ x‖ ≤ 1 / (1 + x ^ 2) := by
  intro x
  unfold bombieriAutocorrelation
  -- Step 1: Triangle inequality + pointwise bound
  calc ‖∫ y, bombieriTestFn σ₀ y * bombieriTestFn σ₀ (y + x)‖
      ≤ ∫ y, ‖bombieriTestFn σ₀ y * bombieriTestFn σ₀ (y + x)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ y, Real.exp (-π * y ^ 2) * Real.exp (-π * (y + x) ^ 2) := by
        apply integral_mono_of_nonneg
        · exact ae_of_all _ fun y => norm_nonneg _
        · exact gaussian_product_integrable x
        · exact ae_of_all _ fun y => bombieriTestFn_product_norm_bound σ₀ x y
    -- Step 2: Complete the square, factor out exp(-πx²/2)
    _ = ∫ y, Real.exp (-(2 * π) * (y + x / 2) ^ 2 + -(π * x ^ 2 / 2)) := by
        congr 1; ext y; rw [← Real.exp_add]; congr 1; ring
    _ = ∫ y, Real.exp (-(2 * π) * (y + x / 2) ^ 2) * Real.exp (-(π * x ^ 2 / 2)) := by
        congr 1; ext y; rw [Real.exp_add]
    _ = (∫ y, Real.exp (-(2 * π) * (y + x / 2) ^ 2)) * Real.exp (-(π * x ^ 2 / 2)) := by
        rw [MeasureTheory.integral_mul_const]
    -- Step 3: Shift variable (translation invariance), evaluate Gaussian integral
    _ = (∫ u, Real.exp (-(2 * π) * u ^ 2)) * Real.exp (-(π * x ^ 2 / 2)) := by
        congr 1
        exact integral_add_right_eq_self (fun u => Real.exp (-(2 * π) * u ^ 2)) (x / 2)
    _ = √(π / (2 * π)) * Real.exp (-(π * x ^ 2 / 2)) := by
        rw [integral_gaussian (2 * π)]
    -- Step 4: √(π/(2π)) = √(1/2) ≤ 1
    _ ≤ 1 * Real.exp (-(π * x ^ 2 / 2)) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        rw [show π / (2 * π) = 1 / 2 from by field_simp]
        rw [Real.sqrt_le_one]; norm_num
    _ = Real.exp (-(π * x ^ 2 / 2)) := one_mul _
    -- Step 5: exp(-πx²/2) ≤ 1/(1+x²) via 1+x² ≤ exp(πx²/2)
    _ ≤ 1 / (1 + x ^ 2) := exp_neg_pi_half_sq_le_inv x

/-- Reflecting the parameter across the critical line does not change the
modulated Gaussian. -/
theorem bombieriTestFn_one_sub (σ : ℝ) :
    bombieriTestFn (1 - σ) = bombieriTestFn σ := by
  funext x
  unfold bombieriTestFn
  congr 1
  rw [show 2 * Real.pi * (1 - σ - 1 / 2) * x =
      -(2 * Real.pi * (σ - 1 / 2) * x) by ring]
  exact Real.cos_neg _

/-- The Gaussian autocorrelation likewise sees only unsigned distance from
the critical line. -/
theorem bombieriAutocorrelation_one_sub (σ : ℝ) :
    bombieriAutocorrelation (1 - σ) = bombieriAutocorrelation σ := by
  unfold bombieriAutocorrelation
  rw [bombieriTestFn_one_sub]

/-- The exact scalar inequality needed to make the Gaussian candidate
negative.  An off-line zeta zero by itself supplies none of these component
estimates. -/
theorem bombieriAutocorrelation_weil_neg_of_component_inequality
    (σ : ℝ)
    (hcomponents :
      weilPolar
          (fourierCos (bombieriAutocorrelation σ) 0)
          (fourierCos (bombieriAutocorrelation σ) 1) +
          weilArchimedean (fourierCos (bombieriAutocorrelation σ)) <
        -weilPrimeTerm (bombieriAutocorrelation σ)) :
    weilFunctionalFull (bombieriAutocorrelation σ)
        (fourierCos (bombieriAutocorrelation σ)) < 0 := by
  unfold weilFunctionalFull
  linarith

/-- The genuine missing converse obligation: every off-critical zero must
produce some admissible autocorrelation on which the Weil functional is
negative.  This does not assert that the single Gaussian family is such a
witness. -/
def OffCriticalWeilWitness : Prop :=
  ∀ (ρ : NontrivialZetaZero), ρ.val.re ≠ 1 / 2 →
    ∃ f : ℝ → ℝ,
      IsAutocorrelation f ∧ Continuous f ∧
      (∀ x : ℝ, ‖f x‖ ≤ 1 / (1 + x ^ 2)) ∧
      weilFunctionalFull f (fourierCos f) < 0

/-- Extract the negative test function once the converse obligation is
supplied. -/
theorem exists_negative_weil_autocorrelation
    (hwitness : OffCriticalWeilWitness)
    (ρ₀ : NontrivialZetaZero) (hσ : ρ₀.val.re ≠ 1 / 2) :
    ∃ f : ℝ → ℝ,
      IsAutocorrelation f ∧ Continuous f ∧
      (∀ x : ℝ, ‖f x‖ ≤ 1 / (1 + x ^ 2)) ∧
      weilFunctionalFull f (fourierCos f) < 0 :=
  hwitness ρ₀ hσ

/-- **Nontrivial zeros lie in the critical strip.** -/
theorem nontrivial_zero_in_critical_strip (s : ℂ)
    (hs_zero : riemannZeta s = 0)
    (hs_not_trivial : ¬∃ n : ℕ, s = -2 * (↑n + 1))
    (hs_ne_one : s ≠ 1) :
    0 < s.re ∧ s.re < 1 :=
  nontrivial_zeta_zero_re s hs_zero hs_not_trivial hs_ne_one

/-- **Weil positivity implies RH, proved by contrapositive.** -/
theorem weil_positivity_implies_rh_from_explicit
    (hwitness : OffCriticalWeilWitness) :
    WeilPositivity → RiemannHypothesis := by
  intro hWP s hs_zero hs_not_trivial hs_ne_one
  by_contra hσ
  obtain ⟨hs_re_pos, hs_re_lt⟩ :=
    nontrivial_zero_in_critical_strip s hs_zero hs_not_trivial hs_ne_one
  let ρ₀ : NontrivialZetaZero := ⟨s, hs_zero, hs_re_pos, hs_re_lt⟩
  obtain ⟨f, hf_auto, hf_cont, hf_decay, hf_neg⟩ :=
    exists_negative_weil_autocorrelation hwitness ρ₀ hσ
  have hf_pos : 0 ≤ weilFunctionalFull f (fourierCos f) :=
    hWP f hf_auto hf_cont hf_decay
  linarith

-- ============================================================
-- Weil Criterion Equivalence (combining both directions)
-- ============================================================

/-- **Conditional Weil-criterion wrapper.**

    RH ⟺ W(f) ≥ 0 for all autocorrelation test functions f.

    The forward and backward analytic inputs are explicit hypotheses, so the
    wrapper adds no hidden mathematical assumption. -/
theorem weil_criterion_equiv_proved
    (hforward : FourierOrientedWeilExplicit)
    (hbackward : OffCriticalWeilWitness) :
    RiemannHypothesis ↔ WeilPositivity :=
  ⟨rh_implies_weil_positivity_from_explicit hforward,
    weil_positivity_implies_rh_from_explicit hbackward⟩

end ArithmeticHodge.Analysis

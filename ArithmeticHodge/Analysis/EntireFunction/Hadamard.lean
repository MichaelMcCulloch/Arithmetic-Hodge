/-
  Step 1.3: Hadamard Factorization Theorem

  State and prove Hadamard's theorem: an entire function of finite order ρ
  can be written as z^m · exp(P(z)) · ∏_n E_p(z/a_n) where P is a polynomial
  of degree ≤ ρ and p = ⌊ρ⌋.

  The proof uses:
  1. Weierstraß product over the zeros (Step 1.1)
  2. The quotient f / (product) is entire and zero-free
  3. Write it as exp(g) where g is entire
  4. Growth estimates (Step 1.2) force g to be a polynomial of degree ≤ order
-/

import ArithmeticHodge.Analysis.EntireFunction.WeierstraßProduct
import ArithmeticHodge.Analysis.EntireFunction.Order
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.AbsMax

set_option autoImplicit false

open Complex Filter Topology Metric Set

namespace ArithmeticHodge.Analysis.EntireFunction

-- ============================================================
-- Hadamard Factorization Theorem
-- ============================================================

/-- **Hadamard Factorization Theorem.**

    Let f be an entire function of finite order ρ. Then:
      f(z) = z^m · e^{P(z)} · ∏_n E_p(z/a_n)
    where:
    - m = ord_0(f) is the order of vanishing at 0
    - P is a polynomial of degree ≤ ⌊ρ⌋
    - {a_n} are the nonzero zeros of f (|a₁| ≤ |a₂| ≤ ⋯)
    - p = ⌊ρ⌋ (the genus)
    - E_p is the Weierstraß elementary factor

    The product converges absolutely and uniformly on compact sets.

    The proof has four main steps:
    1. By the exponent of convergence theorem, Σ|a_n|^{-(p+1)} < ∞
       so the Weierstraß product P(z) = ∏ E_p(z/a_n) converges.
    2. The quotient h(z) = f(z)/(z^m · P(z)) is entire and zero-free.
    3. Since h is zero-free and entire, h = exp(g) for some entire g.
    4. Growth: |g(z)| = log|h(z)| ≤ log|f(z)| + log|1/P(z)|.
       By the order bounds, this gives |g(z)| = O(r^{ρ+ε}).
       By the Borel-Carathéodory theorem, g is a polynomial of degree ≤ ⌊ρ⌋. -/
theorem hadamard_factorization (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hord : HasFiniteOrder f) :
    ∃ (m : ℕ) (P : Polynomial ℂ) (zeros : ℕ → ℂ) (p : ℕ),
      (p = Nat.floor (entireOrder f).toReal) ∧
      (P.natDegree ≤ p) ∧
      (∀ n, zeros n ≠ 0 → f (zeros n) = 0) ∧
      Summable (fun n => (‖zeros n‖⁻¹) ^ ((p : ℝ) + 1)) ∧
      ∀ z, f z = z ^ m * Complex.exp (Polynomial.aeval z P) *
        ∏' n, weierstraßElementary p (z / zeros n) := by
  sorry -- SCAFFOLD: Four-step argument above

/-- **Hadamard factorization specialized to order 1.**

    When ρ = 1 (the case relevant for ξ(s)):
      f(z) = z^m · e^{a+bz} · ∏_n (1 - z/a_n) · exp(z/a_n)

    Here P(z) = a + bz (degree ≤ 1) and E₁(w) = (1-w)exp(w). -/
theorem hadamard_factorization_order_one (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hord : entireOrder f = 1) :
    ∃ (m : ℕ) (a b : ℂ) (zeros : ℕ → ℂ),
      (∀ n, zeros n ≠ 0 → f (zeros n) = 0) ∧
      Summable (fun n => (‖zeros n‖⁻¹) ^ (2 : ℝ)) ∧
      ∀ z, f z = z ^ m * Complex.exp (a + b * z) *
        ∏' n, weierstraßElementary 1 (z / zeros n) := by
  sorry -- SCAFFOLD: specialization of hadamard_factorization

-- ============================================================
-- Logarithmic Derivative of Hadamard Products
-- ============================================================

/-- The logarithmic derivative of E₁(z) = (1-z)exp(z):
    E₁'(z)/E₁(z) = 1/(z-1) + 1 = z/(z-1)

    This is the key identity for computing ζ'/ζ from the Hadamard product. -/
theorem weierstraßElementary_one_logDeriv (z : ℂ) (hz : z ≠ 1) :
    deriv (weierstraßElementary 1) z / weierstraßElementary 1 z = z / (z - 1) := by
  -- E₁(z) = (1 - z) * exp(z), so we compute:
  -- E₁'(z) = -exp(z) + (1-z)*exp(z) = -z * exp(z)
  -- E₁'(z)/E₁(z) = -z*exp(z) / ((1-z)*exp(z)) = -z/(1-z) = z/(z-1)
  have h1z : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  have hexp : Complex.exp z ≠ 0 := Complex.exp_ne_zero z
  -- Simplify the function value
  have hval : weierstraßElementary 1 z = (1 - z) * Complex.exp z := by
    simp [weierstraßElementary]
  -- Compute the derivative
  have hderiv : deriv (weierstraßElementary 1) z = -z * Complex.exp z := by
    have hfun : weierstraßElementary 1 = fun z => (1 - z) * Complex.exp z := by
      ext w; simp [weierstraßElementary]
    rw [hfun]
    have h1 : HasDerivAt (fun z : ℂ => 1 - z) (-1) z := by
      have := ((hasDerivAt_const z (1 : ℂ)).sub (hasDerivAt_id z))
      simp at this
      exact this
    have h2 : HasDerivAt Complex.exp (Complex.exp z) z :=
      Complex.hasDerivAt_exp z
    have h3 := h1.mul h2
    have h4 : HasDerivAt (fun z => (1 - z) * Complex.exp z) (-1 * Complex.exp z + (1 - z) * Complex.exp z) z := h3
    have h5 : -1 * Complex.exp z + (1 - z) * Complex.exp z = -z * Complex.exp z := by ring
    rw [h5] at h4
    exact h4.deriv
  rw [hderiv, hval]
  rw [mul_div_mul_right _ _ hexp]
  rw [neg_div]
  rw [show (1 : ℂ) - z = -(z - 1) from by ring]
  rw [div_neg, neg_neg]

/-- **Logarithmic derivative of a Hadamard product.**

    If f(z) = z^m · e^{a+bz} · ∏_n E₁(z/a_n), then
    f'(z)/f(z) = m/z + b + Σ_n [1/(z-a_n) + 1/a_n]

    This partial fraction expansion is the bridge from Hadamard
    to the explicit formula. The sum converges absolutely for
    z ∉ {0, a₁, a₂, ...}. -/
theorem hadamard_logDeriv (m : ℕ) (a b : ℂ) (zeros : ℕ → ℂ)
    (hconv : Summable (fun n => (‖zeros n‖⁻¹) ^ (2 : ℝ)))
    (z : ℂ) (hz : z ≠ 0) (hzn : ∀ n, z ≠ zeros n) :
    let f := fun z => z ^ m * Complex.exp (a + b * z) *
      ∏' n, weierstraßElementary 1 (z / zeros n)
    deriv f z / f z = (m : ℂ) / z + b +
      ∑' n, (1 / (z - zeros n) + 1 / zeros n) := by
  intro f
  -- We decompose f = f₁ * f₂ * f₃ where:
  --   f₁(z) = z^m,  f₂(z) = exp(a + bz),  f₃(z) = ∏' n, E₁(z/aₙ)
  set f₁ : ℂ → ℂ := fun z => z ^ m with hf₁_def
  set f₂ : ℂ → ℂ := fun z => Complex.exp (a + b * z) with hf₂_def
  set f₃ : ℂ → ℂ := fun z => ∏' n, weierstraßElementary 1 (z / zeros n) with hf₃_def
  -- Key nonvanishing conditions
  have hf₁_ne : f₁ z ≠ 0 := pow_ne_zero m hz
  have hf₂_ne : f₂ z ≠ 0 := Complex.exp_ne_zero _
  have hf₃_ne : f₃ z ≠ 0 := by
    sorry -- SCAFFOLD: tprod of nonzero factors is nonzero
  have hf_eq : f = fun z => f₁ z * f₂ z * f₃ z := by ext; rfl
  -- Log derivative of f₁: d/dz log(z^m) = m/z
  have hlogderiv₁ : deriv f₁ z / f₁ z = (m : ℂ) / z := by
    simp only [hf₁_def]
    rcases m with _ | m
    · simp
    · have hd : HasDerivAt (fun z : ℂ => z ^ (m + 1))
          ((↑(m + 1) : ℂ) * z ^ m) z := hasDerivAt_pow (m + 1) z
      rw [hd.deriv]
      rw [Nat.cast_succ]
      field_simp
      ring
  -- Log derivative of f₂: d/dz(a + bz) = b, so d/dz exp(a+bz)/exp(a+bz) = b
  have hlogderiv₂ : deriv f₂ z / f₂ z = b := by
    have h_lin : HasDerivAt (fun z => a + b * z) b z := by
      have := (hasDerivAt_const z a).add ((hasDerivAt_const z b).mul (hasDerivAt_id z))
      simp at this
      exact this
    have hd : HasDerivAt f₂ (Complex.exp (a + b * z) * b) z :=
      h_lin.cexp
    rw [hd.deriv]
    simp only [hf₂_def]
    have hne : Complex.exp (a + b * z) ≠ 0 := Complex.exp_ne_zero _
    field_simp
  -- Log derivative of f₃: ∑' n, (1/(z - aₙ) + 1/aₙ)
  have hlogderiv₃ : deriv f₃ z / f₃ z =
      ∑' n, (1 / (z - zeros n) + 1 / zeros n) := by
    sorry -- SCAFFOLD: HasDerivAt for tprod + term-by-term log differentiation
  -- Combine: log derivative of a product f₁·f₂·f₃ is sum of log derivatives
  have hf₁_diff : DifferentiableAt ℂ f₁ z :=
    (differentiable_pow m).differentiableAt
  have hf₂_diff : DifferentiableAt ℂ f₂ z := by
    apply DifferentiableAt.cexp
    exact (differentiableAt_const a).add ((differentiableAt_const b).mul differentiableAt_id)
  have hf₃_diff : DifferentiableAt ℂ f₃ z := by
    sorry -- SCAFFOLD: differentiability of tprod
  rw [hf_eq]
  set g₁₂ : ℂ → ℂ := fun z => f₁ z * f₂ z with hg₁₂_def
  have hg₁₂_diff : DifferentiableAt ℂ g₁₂ z := hf₁_diff.mul hf₂_diff
  have hg₁₂_ne : g₁₂ z ≠ 0 := mul_ne_zero hf₁_ne hf₂_ne
  have hf_eq2 : f = fun z => g₁₂ z * f₃ z := by ext w; simp [hf_eq, g₁₂, f₁, f₂, f₃]
  have hf_val : f z = g₁₂ z * f₃ z := by rw [hf_eq2]
  have hf_ne : f z ≠ 0 := by rw [hf_val]; exact mul_ne_zero hg₁₂_ne hf₃_ne
  have hf_deriv : deriv f z = deriv g₁₂ z * f₃ z + g₁₂ z * deriv f₃ z := by
    rw [hf_eq2]; exact deriv_mul hg₁₂_diff hf₃_diff
  have hg₁₂_deriv : deriv g₁₂ z = deriv f₁ z * f₂ z + f₁ z * deriv f₂ z := by
    exact deriv_mul hf₁_diff hf₂_diff
  have key : deriv f z / f z = deriv f₁ z / f₁ z + deriv f₂ z / f₂ z + deriv f₃ z / f₃ z := by
    rw [hf_deriv, hf_val, hg₁₂_deriv, hg₁₂_def]
    field_simp
  rw [key, hlogderiv₁, hlogderiv₂, hlogderiv₃]

-- ============================================================
-- Borel-Carathéodory Lemma
-- ============================================================

/-- **Borel-Carathéodory theorem.**
    If f is analytic on |z| ≤ R with Re(f) ≤ A on |z| = R, then
    |f(z)| ≤ 2r/(R-r) · A + (R+r)/(R-r) · |f(0)| for |z| ≤ r < R.

    This is the key tool for promoting real-part bounds on entire functions
    to full bounds, which is used in Step 4 of the Hadamard proof to show
    that g = log(f/product) is a polynomial. -/
theorem borel_caratheodory (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (R r : ℝ) (hR : 0 < R) (hr : 0 < r) (hrR : r < R)
    (A : ℝ) (hA : ∀ z : ℂ, ‖z‖ = R → (f z).re ≤ A) :
    ∀ z : ℂ, ‖z‖ ≤ r →
      ‖f z‖ ≤ 2 * r / (R - r) * A + (R + r) / (R - r) * ‖f 0‖ := by
  have hRr : 0 < R - r := sub_pos.mpr hrR
  -- Step 1: Extend Re(f) ≤ A from the sphere to the open ball via the maximum
  -- modulus principle applied to exp ∘ f (since ‖exp(f z)‖ = exp(Re(f z))).
  have hA_ball : ∀ (w : ℂ), ‖w‖ < R → (f w).re ≤ A := by
    intro w hwR
    have hw_ball : w ∈ ball (0 : ℂ) R := mem_ball_zero_iff.mpr hwR
    have hef_bound : ‖(Complex.exp ∘ f) w‖ ≤ Real.exp A := by
      apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
        ((Complex.differentiable_exp.comp hf).diffContOnCl)
      · intro z hz
        rw [frontier_ball (0 : ℂ) hR.ne'] at hz
        simp only [mem_sphere, dist_zero_right] at hz
        simp only [Function.comp_apply, Complex.norm_exp]
        exact Real.exp_le_exp_of_le (hA z hz)
      · exact subset_closure hw_ball
    simp only [Function.comp_apply, Complex.norm_exp] at hef_bound
    exact Real.exp_le_exp.mp hef_bound
  -- Step 2: Derive ‖f 0‖ ≥ -A (needed for monotonicity).
  have hf0_re : (f 0).re ≤ A := hA_ball 0 (by simp [hR])
  have hf0_norm_ge_neg_A : -A ≤ ‖f 0‖ :=
    calc -A ≤ -(f 0).re := by linarith
      _ ≤ |(f 0).re| := neg_le_abs _
      _ ≤ ‖f 0‖ := Complex.abs_re_le_norm (f 0)
  -- Step 3: Define g = f - f(0), set M = A + ‖f 0‖ ≥ 0.
  set g : ℂ → ℂ := fun w => f w - f 0 with hg_def
  have hg_diff : DifferentiableOn ℂ g (ball 0 R) :=
    hf.differentiableOn.sub (differentiableOn_const _)
  have hg_zero : g 0 = 0 := by simp [g]
  have hM_nonneg : 0 ≤ A + ‖f 0‖ := by linarith
  -- Step 4: Re(g w) ≤ A + ‖f 0‖ for all w in ball.
  have hg_re_le : ∀ (w : ℂ), w ∈ ball (0 : ℂ) R → (g w).re ≤ A + ‖f 0‖ := by
    intro w hw
    simp only [g, Complex.sub_re]
    have hw_re : (f w).re ≤ A := hA_ball w (mem_ball_zero_iff.mp hw)
    linarith [neg_le_abs (f 0).re, Complex.abs_re_le_norm (f 0)]
  -- Step 5: Show ‖g z‖ ≤ 2*(A + ‖f 0‖)*‖z‖/(R - ‖z‖) for z in ball.
  -- When A + ‖f 0‖ > 0, use borelCaratheodory_zero directly.
  -- When A + ‖f 0‖ = 0, show g ≡ 0 by applying borelCaratheodory_zero with any ε > 0.
  intro z hz
  have hzR : ‖z‖ < R := lt_of_le_of_lt hz hrR
  have hz_ball : z ∈ ball (0 : ℂ) R := mem_ball_zero_iff.mpr hzR
  have hRz : 0 < R - ‖z‖ := sub_pos.mpr hzR
  have hg_bound : ‖g z‖ ≤ 2 * (A + ‖f 0‖) * ‖z‖ / (R - ‖z‖) := by
    by_cases hM_pos : 0 < A + ‖f 0‖
    · -- A + ‖f 0‖ > 0: apply borelCaratheodory_zero directly
      exact Complex.borelCaratheodory_zero hM_pos hg_diff
        (fun w hw => hg_re_le w hw) hR hz_ball hg_zero
    · -- A + ‖f 0‖ = 0: for any ε > 0, ‖g z‖ ≤ 2*ε*‖z‖/(R-‖z‖), so ‖g z‖ = 0.
      have hM_eq : A + ‖f 0‖ = 0 := le_antisymm (not_lt.mp hM_pos) hM_nonneg
      simp only [hM_eq, mul_zero, zero_mul, zero_div]
      -- Show ‖g z‖ ≤ 0 by applying BC_zero with arbitrarily small M.
      by_cases hz_zero : z = 0
      · simp [hz_zero, hg_zero]
      · -- For z ≠ 0, use: for any ε > 0, ‖g z‖ ≤ 2*ε*‖z‖/(R-‖z‖).
        -- Choose ε small enough to get contradiction if ‖g z‖ > 0.
        have hznorm_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz_zero
        suffices h : ∀ (ε : ℝ), 0 < ε → ‖g z‖ ≤ 2 * ε * ‖z‖ / (R - ‖z‖) by
          by_contra habs
          push_neg at habs
          have h1 := h (‖g z‖ * (R - ‖z‖) / (4 * ‖z‖)) (by positivity)
          have : 2 * (‖g z‖ * (R - ‖z‖) / (4 * ‖z‖)) * ‖z‖ / (R - ‖z‖) =
              ‖g z‖ / 2 := by field_simp; ring
          linarith
        intro ε hε
        have hg_mapsTo_ε : MapsTo g (ball (0 : ℂ) R) {z | z.re ≤ ε} := by
          intro w hw
          simp only [mem_setOf_eq]
          have := hg_re_le w hw
          linarith [hM_eq]
        exact Complex.borelCaratheodory_zero hε hg_diff hg_mapsTo_ε hR hz_ball hg_zero
  -- Step 6: From ‖g z‖ bound, derive the BC bound with ‖z‖.
  -- ‖f z‖ ≤ ‖g z‖ + ‖f 0‖
  --        ≤ 2*(A+‖f 0‖)*‖z‖/(R-‖z‖) + ‖f 0‖
  --        = 2*A*‖z‖/(R-‖z‖) + ‖f 0‖*(R+‖z‖)/(R-‖z‖)   (by algebra)
  have step1 : ‖f z‖ ≤ 2 * A * ‖z‖ / (R - ‖z‖) + ‖f 0‖ * (R + ‖z‖) / (R - ‖z‖) := by
    have h1 : ‖f z‖ ≤ ‖g z‖ + ‖f 0‖ := by
      calc ‖f z‖ = ‖g z + f 0‖ := by simp [g]
        _ ≤ ‖g z‖ + ‖f 0‖ := norm_add_le _ _
    calc ‖f z‖ ≤ ‖g z‖ + ‖f 0‖ := h1
      _ ≤ 2 * (A + ‖f 0‖) * ‖z‖ / (R - ‖z‖) + ‖f 0‖ := by linarith
      _ = 2 * A * ‖z‖ / (R - ‖z‖) + ‖f 0‖ * (R + ‖z‖) / (R - ‖z‖) := by
          field_simp; ring
  -- Step 7: Monotonicity — replace ‖z‖ by r.
  -- The function t ↦ 2*A*t/(R-t) + ‖f 0‖*(R+t)/(R-t) has derivative
  -- 2*R*(A+‖f 0‖)/(R-t)² ≥ 0, so it is increasing on [0,R).
  calc ‖f z‖
      ≤ 2 * A * ‖z‖ / (R - ‖z‖) + ‖f 0‖ * (R + ‖z‖) / (R - ‖z‖) := step1
    _ ≤ 2 * r / (R - r) * A + (R + r) / (R - r) * ‖f 0‖ := by
        -- Suffices to show the numerators satisfy the right inequality after
        -- clearing the common denominator structure.
        -- LHS = (2*A*‖z‖ + ‖f 0‖*(R+‖z‖)) / (R-‖z‖)
        -- RHS = (2*r*A + (R+r)*‖f 0‖) / (R-r)
        -- Cross-multiply: LHS*(R-r) ≤ RHS*(R-‖z‖) iff
        --   (2*A*‖z‖ + ‖f 0‖*(R+‖z‖))*(R-r) ≤ (2*r*A + (R+r)*‖f 0‖)*(R-‖z‖)
        -- Expand: 2*A*‖z‖*R - 2*A*‖z‖*r + ‖f 0‖*R² + ‖f 0‖*R*‖z‖ - ‖f 0‖*R*r - ‖f 0‖*‖z‖*r
        --       ≤ 2*r*A*R - 2*r*A*‖z‖ + R²*‖f 0‖ + r*R*‖f 0‖ - R*‖z‖*‖f 0‖ - r*‖z‖*‖f 0‖ ? hmm
        -- Simplify: LHS-RHS = 2*A*R*(‖z‖-r) + 2*‖f 0‖*R*(‖z‖-r)
        --                   = 2*R*(A+‖f 0‖)*(‖z‖-r) ≤ 0 since ‖z‖ ≤ r and A+‖f 0‖ ≥ 0.
        suffices h : (2 * A * ‖z‖ + ‖f 0‖ * (R + ‖z‖)) * (R - r) ≤
            (2 * r * A + (R + r) * ‖f 0‖) * (R - ‖z‖) by
          have lhs_eq : 2 * A * ‖z‖ / (R - ‖z‖) + ‖f 0‖ * (R + ‖z‖) / (R - ‖z‖) =
              (2 * A * ‖z‖ + ‖f 0‖ * (R + ‖z‖)) / (R - ‖z‖) := by ring
          have rhs_eq : 2 * r / (R - r) * A + (R + r) / (R - r) * ‖f 0‖ =
              (2 * r * A + (R + r) * ‖f 0‖) / (R - r) := by ring
          rw [lhs_eq, rhs_eq, div_le_div_iff₀ hRz hRr]
          exact h
        -- Difference = 2*R*(A+‖f 0‖)*(‖z‖-r) ≤ 0
        have hdiff : (2 * A * ‖z‖ + ‖f 0‖ * (R + ‖z‖)) * (R - r) -
            (2 * r * A + (R + r) * ‖f 0‖) * (R - ‖z‖) =
            2 * R * (A + ‖f 0‖) * (‖z‖ - r) := by ring
        have hle : 2 * R * (A + ‖f 0‖) * (‖z‖ - r) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
        linarith

end ArithmeticHodge.Analysis.EntireFunction

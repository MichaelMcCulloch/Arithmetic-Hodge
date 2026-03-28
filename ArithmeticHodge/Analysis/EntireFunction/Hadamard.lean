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

import ArithmeticHodge.Analysis.EntireFunction.GrowthBound
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.Deriv.Polynomial

set_option autoImplicit false

open Complex Filter Topology Metric Set Polynomial

namespace ArithmeticHodge.Analysis.EntireFunction

-- ============================================================
-- Helper Lemmas for Hadamard Factorization
-- ============================================================

/-- An entire function whose (n+1)-th iterated derivative vanishes everywhere
    is a polynomial of degree at most n.  Proof by induction on n:
    - Base: deriv g ≡ 0 ⟹ g is constant (by `is_const_of_deriv_eq_zero`).
    - Step: deriv g is polynomial by IH; g is its antiderivative plus a constant.  -/
private theorem polynomial_of_vanishing_iteratedDeriv (g : ℂ → ℂ) (hg : Differentiable ℂ g)
    (n : ℕ) (hvan : ∀ c : ℂ, iteratedDeriv (n + 1) g c = 0) :
    ∃ P : ℂ[X], P.natDegree ≤ n ∧ ∀ z, g z = aeval z P := by
  induction n generalizing g with
  | zero =>
    -- iteratedDeriv 1 g = deriv g ≡ 0 ⟹ g is constant
    have hd : ∀ z, deriv g z = 0 := fun z => by
      have := hvan z; rwa [iteratedDeriv_succ, iteratedDeriv_zero] at this
    have hconst : ∀ z, g z = g 0 :=
      fun z => is_const_of_deriv_eq_zero hg hd z 0
    exact ⟨C (g 0), (natDegree_C _).le, fun z => by rw [hconst z]; simp⟩
  | succ n ih =>
    -- deriv g is entire with vanishing (n+1)-th iterated derivative
    have hg' : Differentiable ℂ (deriv g) := hg.contDiff.differentiable_deriv_two
    have hvan' : ∀ c, iteratedDeriv (n + 1) (deriv g) c = 0 := fun c => by
      have := hvan c; rwa [iteratedDeriv_succ'] at this
    obtain ⟨Q, hQ_deg, hQ_eq⟩ := ih (deriv g) hg' hvan'
    -- Build antiderivative R: derivative R = Q, aeval 0 R = 0
    set R : ℂ[X] := ∑ k ∈ Finset.range (n + 1),
      C (Q.coeff k / (↑(k + 1) : ℂ)) * X ^ (k + 1) with hR_def
    have hR_deriv : derivative R = Q := by
      ext j
      simp only [hR_def, map_sum, derivative_C_mul_X_pow, Nat.add_sub_cancel]
      -- Each coeff simplifies: Q.coeff k / (k+1) * (k+1) = Q.coeff k
      have cancel : ∀ k, Q.coeff k / (↑(k + 1) : ℂ) * ↑(k + 1) = Q.coeff k :=
        fun k => div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k))
      simp_rw [cancel]
      -- Now ∑ k in range(n+1), C(Q.coeff k) * X^k = Q since deg Q ≤ n
      conv_rhs => rw [Q.as_sum_range_C_mul_X_pow' (by omega : Q.natDegree < n + 1)]
    have hR_eval_zero : aeval (0 : ℂ) R = 0 := by
      simp only [hR_def, map_sum, map_mul, aeval_C, aeval_X_pow,
        zero_pow (Nat.succ_ne_zero _), mul_zero, Finset.sum_const_zero]
    have hR_diff : Differentiable ℂ (fun z => aeval z R) := R.differentiable_aeval
    have hconst_diff : Differentiable ℂ (fun z => g z - aeval z R) := hg.sub hR_diff
    have hconst_deriv : ∀ z, deriv (fun w => g w - aeval w R) z = 0 := fun z => by
      have : deriv (fun w => g w - aeval w R) z =
          deriv g z - deriv (fun w => aeval w R) z :=
        deriv_sub hg.differentiableAt hR_diff.differentiableAt
      rw [this, R.deriv_aeval, hR_deriv, hQ_eq z, sub_self]
    have hconst : ∀ z, g z = g 0 + aeval z R := fun z => by
      have h := is_const_of_deriv_eq_zero hconst_diff hconst_deriv z 0
      simp only [hR_eval_zero, sub_zero] at h
      exact eq_add_of_sub_eq h
    refine ⟨C (g 0) + R, ?_, fun z => ?_⟩
    · calc (C (g 0) + R).natDegree
          ≤ max (C (g 0)).natDegree R.natDegree := natDegree_add_le _ _
        _ ≤ max 0 (n + 1) := max_le_max ((natDegree_C _).le) (by
            exact natDegree_sum_le_of_forall_le _ _ fun k hk =>
              (natDegree_C_mul_X_pow_le _ _).trans (by
                simp only [Finset.mem_range] at hk; omega))
        _ = n + 1 := by omega
    · rw [hconst z, map_add, aeval_C]; simp

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
       Cauchy estimates: ‖g⁽ⁿ⁾(c)‖ ≤ n! · M(g,R)/R^n → 0 for n > ρ as R → ∞.
       So g is a polynomial of degree ≤ ⌊ρ⌋. -/
theorem hadamard_factorization (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hf_ne : ¬ f = 0) (hord : HasFiniteOrder f) :
    ∃ (m : ℕ) (P : Polynomial ℂ) (zeros : ℕ → ℂ) (p : ℕ),
      (P.natDegree ≤ Nat.floor (entireOrder f).toReal) ∧
      (∀ n, zeros n ≠ 0 → f (zeros n) = 0) ∧
      Summable (fun n => (‖zeros n‖⁻¹) ^ ((p : ℝ) + 1)) ∧
      ∀ z, f z = z ^ m * Complex.exp (Polynomial.aeval z P) *
        ∏' n, weierstraßElementary p (z / zeros n) := by
  -- [SORRY'd: proof depends on weierstraß_quotient_growth which transitively
  --  depends on sorry'd re_bound_of_factorization in GrowthBound.lean.
  --  The sorry propagates through hg₁_bound causing type mismatches.
  --  Original proof preserved in git history.]
  exact sorry
  /-
  set p := Nat.floor (entireOrder f).toReal with hp_def
  -- ============================================================
  -- Step 2: Growth bound + Cauchy estimates ⟹ g₁ is polynomial.
  -- ============================================================
  -- g₁ is entire with |g₁(z)| = O(r^{ρ+ε}) for all ε > 0.
  -- Cauchy: ‖iteratedDeriv (p+1) g₁ c‖ ≤ (p+1)! · C·r^{ρ+ε} / R^{p+1} → 0
  -- since ρ + ε < p + 1 for small ε. So iteratedDeriv (p+1) g₁ ≡ 0.
  have hvan : ∀ c : ℂ, iteratedDeriv (p + 1) g₁ c = 0 := by
    -- Cauchy estimate: for any center c and radius R > 0,
    -- ‖iteratedDeriv (p+1) g₁ c‖ ≤ (p+1)! · (sphere bound) / R^{p+1}
    have cauchy : ∀ (c : ℂ) (R : ℝ), 0 < R →
        ‖iteratedDeriv (p + 1) g₁ c‖ ≤
        ↑(p + 1).factorial * (C_g * (1 + ‖c‖ + R) ^ α_g) / R ^ (p + 1) :=
      fun c R hR => norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le _ hR
        hg₁_diff.diffContOnCl fun z hz => by
          rw [mem_sphere_iff_norm] at hz
          exact (hg₁_bound z).trans (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (by positivity) (by linarith [norm_le_insert' z c]) hα_nn)
            hC_pos.le)
    -- Step A: iteratedDeriv (p+1) g₁ is bounded.
    -- Choose R = ‖c‖ + 1 in the Cauchy estimate. Then 1+‖c‖+R = 2(‖c‖+1),
    -- and (‖c‖+1)^α / (‖c‖+1)^(p+1) ≤ 1 since ‖c‖+1 ≥ 1 and α ≤ p+1.
    set Bd := ↑(p + 1).factorial * C_g * (2 : ℝ) ^ α_g with hBd_def
    have hBd_pos : 0 < Bd := by positivity
    have hbdd : ∀ c : ℂ, ‖iteratedDeriv (p + 1) g₁ c‖ ≤ Bd := by
      intro c
      have hR : (0 : ℝ) < ‖c‖ + 1 := by positivity
      have h1 := cauchy c (‖c‖ + 1) hR
      have h2 : 1 + ‖c‖ + (‖c‖ + 1) = 2 * (‖c‖ + 1) := by ring
      rw [h2] at h1
      have h3 : (2 * (‖c‖ + 1)) ^ α_g = 2 ^ α_g * (‖c‖ + 1) ^ α_g :=
        Real.mul_rpow (by positivity : (0 : ℝ) ≤ 2) (by positivity : (0 : ℝ) ≤ ‖c‖ + 1)
      have h4 : (‖c‖ + 1) ^ α_g ≤ (‖c‖ + 1) ^ ((p + 1 : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg c] : 1 ≤ ‖c‖ + 1)
          (by push_cast; linarith [hα_lt])
      have h5 : (‖c‖ + 1) ^ ((p + 1 : ℕ) : ℝ) = (‖c‖ + 1) ^ (p + 1) :=
        Real.rpow_natCast (‖c‖ + 1) (p + 1)
      calc ‖iteratedDeriv (p + 1) g₁ c‖
          ≤ ↑(p + 1).factorial * (C_g * (2 * (‖c‖ + 1)) ^ α_g) / (‖c‖ + 1) ^ (p + 1) := h1
        _ = ↑(p + 1).factorial * (C_g * (2 ^ α_g * (‖c‖ + 1) ^ α_g)) /
            (‖c‖ + 1) ^ (p + 1) := by rw [h3]
        _ ≤ ↑(p + 1).factorial * (C_g * (2 ^ α_g * (‖c‖ + 1) ^ (p + 1))) /
            (‖c‖ + 1) ^ (p + 1) := by
          gcongr
          exact h4.trans (h5 ▸ le_refl _)
        _ = Bd := by
          rw [hBd_def]
          field_simp
    -- Step B: By Liouville, iteratedDeriv (p+1) g₁ is constant.
    have hg₂_diff : Differentiable ℂ (iteratedDeriv (p + 1) g₁) :=
      hg₁_diff.contDiff.differentiable_iteratedDeriv (p + 1) (WithTop.coe_lt_top _)
    have hg₂_bdd : Bornology.IsBounded (Set.range (iteratedDeriv (p + 1) g₁)) :=
      (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := Bd)).subset
        (Set.range_subset_iff.mpr fun c => mem_closedBall_zero_iff.mpr (hbdd c))
    have hconst : ∀ c : ℂ, iteratedDeriv (p + 1) g₁ c = iteratedDeriv (p + 1) g₁ 0 :=
      fun c => hg₂_diff.apply_eq_apply_of_bounded hg₂_bdd c 0
    -- Step C: The constant value is 0.
    suffices h0 : iteratedDeriv (p + 1) g₁ 0 = 0 by
      intro c; rw [hconst c, h0]
    -- By contradiction: if nonzero, Cauchy bound at c = 0 with R → ∞ gives contradiction
    by_contra hne
    rw [← ne_eq, ← norm_pos_iff] at hne
    set δ := ‖iteratedDeriv (p + 1) g₁ 0‖
    -- Choose R large enough that the Cauchy bound at 0 is < δ
    -- Bound: (p+1)! * C_g * (1+R)^α / R^(p+1)
    -- For R ≥ 1: ≤ (p+1)! * C_g * (2R)^α / R^(p+1) = Bd * R^α / R^(p+1)
    -- Need: Bd * R^(α-(p+1)) < δ, i.e., R^((p+1)-α) > Bd/δ
    set β := (↑(p + 1) : ℝ) - α_g with hβ_def
    have hβ_pos : 0 < β := by simp [hβ_def]; linarith
    -- Use Archimedean property to find n : ℕ large enough
    obtain ⟨n, hn⟩ := exists_nat_gt (max 1 ((Bd / δ) ^ β⁻¹))
    have hn_pos : (0 : ℝ) < n := by linarith [le_max_left 1 ((Bd / δ) ^ β⁻¹)]
    -- n > (Bd/δ)^(1/β), so n^β > Bd/δ
    have hn_large : (Bd / δ) ^ β⁻¹ < (n : ℝ) := by
      linarith [le_max_right 1 ((Bd / δ) ^ β⁻¹)]
    have hn_rpow : (n : ℝ) ^ β > Bd / δ := by
      have h0 : (0 : ℝ) ≤ (Bd / δ) ^ β⁻¹ := by positivity
      calc (n : ℝ) ^ β
          > ((Bd / δ) ^ β⁻¹) ^ β := Real.rpow_lt_rpow h0 hn_large hβ_pos
        _ = Bd / δ := by
          rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ Bd / δ),
            inv_mul_cancel₀ hβ_pos.ne', Real.rpow_one]
    -- Cauchy estimate at c = 0 with R = n
    have h_cauchy := cauchy 0 n hn_pos
    simp only [norm_zero, add_zero] at h_cauchy
    -- Simplify: 1 + n ≤ 2n (since n ≥ 1)
    have h_1n : (1 : ℝ) + ↑n ≤ 2 * ↑n := by linarith [le_max_left 1 ((Bd / δ) ^ β⁻¹)]
    -- (1+n)^α ≤ (2n)^α
    have h_sphere : (1 + (n : ℝ)) ^ α_g ≤ (2 * (n : ℝ)) ^ α_g :=
      Real.rpow_le_rpow (by positivity) h_1n hα_nn
    -- (2n)^α = 2^α * n^α
    have h_split : (2 * (n : ℝ)) ^ α_g = 2 ^ α_g * (n : ℝ) ^ α_g :=
      Real.mul_rpow (by positivity : (0 : ℝ) ≤ 2) hn_pos.le
    -- n^α / n^(p+1) = n^(α-(p+1)) = n^(-β) = 1/n^β
    have h_rpow_div : (n : ℝ) ^ α_g / (n : ℝ) ^ (p + 1) = (n : ℝ) ^ (-β) := by
      rw [hβ_def, neg_sub, Real.rpow_sub hn_pos, Real.rpow_natCast]
    have h_rpow_neg : (n : ℝ) ^ (-β) = ((n : ℝ) ^ β)⁻¹ :=
      Real.rpow_neg hn_pos.le β
    -- Chain the inequalities
    have h_upper : δ ≤ Bd * ((n : ℝ) ^ β)⁻¹ := by
      calc δ ≤ ↑(p + 1).factorial * (C_g * (1 + ↑n) ^ α_g) / (↑n) ^ (p + 1) := h_cauchy
        _ ≤ ↑(p + 1).factorial * (C_g * (2 ^ α_g * (↑n) ^ α_g)) / (↑n) ^ (p + 1) := by
          gcongr
          calc (1 + (↑n : ℝ)) ^ α_g ≤ (2 * ↑n) ^ α_g := h_sphere
            _ = 2 ^ α_g * (↑n) ^ α_g := h_split
        _ = Bd * ((n : ℝ) ^ α_g / (n : ℝ) ^ (p + 1)) := by
          rw [hBd_def]; field_simp
        _ = Bd * (n : ℝ) ^ (-β) := by rw [h_rpow_div]
        _ = Bd * ((n : ℝ) ^ β)⁻¹ := by rw [h_rpow_neg]
    -- But Bd / n^β < δ (from hn_rpow)
    have h_lower : Bd * ((n : ℝ) ^ β)⁻¹ < δ := by
      rw [← div_eq_mul_inv, div_lt_iff₀ (by positivity : 0 < (n : ℝ) ^ β), mul_comm]
      exact (div_lt_iff₀ hne).mp hn_rpow
    linarith
  -- ============================================================
  -- Step 3: Apply polynomial_of_vanishing_iteratedDeriv.
  -- ============================================================
  obtain ⟨P, hP_deg, hP_eq⟩ := polynomial_of_vanishing_iteratedDeriv g₁ hg₁_diff p hvan
  exact ⟨m, P, zeros, p₀, hP_deg, hzeros_cond, hsumm,
    fun z => by rw [hg₁_eq z, hP_eq z]⟩
  -/

/-- **Hadamard factorization specialized to order 1.**

    When ρ = 1 (the case relevant for ξ(s)):
      f(z) = z^m · e^{P(z)} · ∏_n E_p(z/a_n)

    Here P has degree ≤ 1 and the product converges. -/
theorem hadamard_factorization_order_one (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hf_ne : ¬ f = 0) (hord : entireOrder f = 1) :
    ∃ (m : ℕ) (P : Polynomial ℂ) (zeros : ℕ → ℂ) (p : ℕ),
      (P.natDegree ≤ 1) ∧
      (∀ n, zeros n ≠ 0 → f (zeros n) = 0) ∧
      Summable (fun n => (‖zeros n‖⁻¹) ^ ((p : ℝ) + 1)) ∧
      ∀ z, f z = z ^ m * Complex.exp (Polynomial.aeval z P) *
        ∏' n, weierstraßElementary p (z / zeros n) := by
  have hfin : HasFiniteOrder f := by
    show entireOrder f < ⊤; rw [hord]; exact EReal.coe_lt_top 1
  obtain ⟨m, P, zeros, p, hP_deg, hzeros, hsum, hfact⟩ :=
    hadamard_factorization f hf hf_ne hfin
  refine ⟨m, P, zeros, p, ?_, hzeros, hsum, hfact⟩
  calc P.natDegree ≤ Nat.floor (entireOrder f).toReal := hP_deg
    _ = 1 := by
        rw [hord]
        have : (1 : EReal) = ((1 : ℝ) : EReal) := rfl
        rw [this, EReal.toReal_coe, Nat.floor_one]

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
    (hne_zero : ∀ n, zeros n ≠ 0)
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
    simp only [hf₃_def]
    have hconv' : Summable (fun n => (‖zeros n‖⁻¹) ^ ((1 : ℕ) + 1 : ℝ)) := by
      convert hconv using 2; norm_num
    apply tprod_weierstraßElementary_ne_zero zeros 1 hconv' z
    intro n
    by_cases h0 : zeros n = 0
    · simp [h0]
    · exact fun heq => absurd (div_eq_one_iff_eq h0 |>.mp heq) (hzn n)
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
    -- Use logDeriv_tprod_eq_tsum from Mathlib
    have hconv' : Summable (fun n => (‖zeros n‖⁻¹) ^ ((1 : ℕ) + 1 : ℝ)) := by
      convert hconv using 2; norm_num
    -- Set up the factors
    set fac : ℕ → ℂ → ℂ := fun n w => weierstraßElementary 1 (w / zeros n)
    have hf₃_eq : f₃ = fun w => ∏' n, fac n w := by ext w; rfl
    set s := ball (0 : ℂ) (‖z‖ + 1)
    have hs_open : IsOpen s := isOpen_ball
    have hz_s : z ∈ s := mem_ball_zero_iff.mpr (by linarith)
    -- Each factor is nonzero at z
    have hfne : ∀ n, fac n z ≠ 0 := fun n =>
      weierstraßElementary_ne_zero 1 _ (by
        intro heq; exact hzn n (div_eq_one_iff_eq (hne_zero n) |>.mp heq))
    -- Each factor is differentiable on s
    have hfd : ∀ n, DifferentiableOn ℂ (fac n) s := fun n =>
      ((weierstraßElementary_differentiable 1).comp (differentiable_id.div_const _)).differentiableOn
    -- MultipliableLocallyUniformlyOn
    have hmlu : MultipliableLocallyUniformlyOn fac s :=
      multipliableLocallyUniformlyOn_weierstraß zeros 1 hconv' s hs_open
    -- Product nonzero
    have hprod_ne : ∏' n, fac n z ≠ 0 := hf₃_ne
    -- Per-term logDeriv computation
    have hper_term : ∀ n, logDeriv (fac n) z = 1 / (z - zeros n) + 1 / zeros n := by
      intro n
      have ha := hne_zero n
      have hza : z / zeros n ≠ 1 := by
        intro heq; exact hzn n (div_eq_one_iff_eq ha |>.mp heq)
      have hza_ne : z - zeros n ≠ 0 := sub_ne_zero.mpr (hzn n)
      have hE_ne := weierstraßElementary_ne_zero 1 (z / zeros n) hza
      -- Compute deriv via chain rule
      have h_div : HasDerivAt (fun w => w / zeros n) ((zeros n)⁻¹) z := by
        simpa using (hasDerivAt_id z).div_const (zeros n)
      have hcomp : HasDerivAt (fac n)
          (deriv (weierstraßElementary 1) (z / zeros n) * (zeros n)⁻¹) z :=
        (weierstraßElementary_differentiable 1).differentiableAt.hasDerivAt.comp z h_div
      simp only [logDeriv, Pi.div_apply, fac]
      rw [hcomp.deriv]
      -- Eliminate deriv using logDeriv identity: deriv E₁ w / E₁ w = w/(w-1)
      have hld := weierstraßElementary_one_logDeriv (z / zeros n) hza
      -- Rewrite deriv E₁ (z/a) = (z/a)/(z/a - 1) * E₁(z/a)
      have hderiv_eq : deriv (weierstraßElementary 1) (z / zeros n) =
          (z / zeros n) / (z / zeros n - 1) * weierstraßElementary 1 (z / zeros n) :=
        (div_eq_iff hE_ne).mp hld
      rw [hderiv_eq]
      have hza_sub : z / zeros n - 1 ≠ 0 := sub_ne_zero.mpr hza
      field_simp [hE_ne, ha, hza_ne, hza_sub]
      ring
    -- Summability of logDerivs
    have hm_summ : Summable fun n => logDeriv (fac n) z := by
      simp_rw [hper_term]
      -- 1/(z - zeros n) + 1/zeros n = z / (zeros n * (z - zeros n))
      -- For large n, this is O(‖zeros n‖⁻²), summable from hconv
      have hconv_pow : Summable (fun n => ‖zeros n‖⁻¹ ^ 2) := by
        have : (fun n => (‖zeros n‖⁻¹) ^ (2 : ℝ)) = fun n => ‖zeros n‖⁻¹ ^ 2 := by
          ext n; rw [← Real.rpow_natCast]; norm_cast
        rwa [this] at hconv
      apply (hconv_pow.mul_left (2 * ‖z‖)).of_norm_bounded_eventually
      rw [Nat.cofinite_eq_atTop]
      have htend := (Nat.cofinite_eq_atTop ▸ hconv_pow.tendsto_atTop_zero :
        Tendsto (fun n => ‖zeros n‖⁻¹ ^ 2) atTop (nhds 0))
      set c := 1 / (2 * ‖z‖ + 1)
      apply (htend.eventually (Iio_mem_nhds (show (0 : ℝ) < c ^ 2 by positivity))).mono
      intro n hn
      have hinv_lt : ‖zeros n‖⁻¹ < c := lt_of_pow_lt_pow_left₀ 2 (by positivity) hn
      have ha := hne_zero n
      have hzn_ne : z - zeros n ≠ 0 := sub_ne_zero.mpr (hzn n)
      -- ‖zeros n‖ > 2‖z‖ + 1 > 0
      have ha_pos : (0 : ℝ) < ‖zeros n‖ := norm_pos_iff.mpr ha
      have hzn_large : 2 * ‖z‖ + 1 < ‖zeros n‖ := by
        have hc_eq : c = (2 * ‖z‖ + 1)⁻¹ := by simp [c, one_div]
        rw [hc_eq] at hinv_lt
        exact (inv_lt_inv₀ ha_pos (by positivity)).mp hinv_lt
      -- Reverse triangle: ‖z - zeros n‖ ≥ ‖zeros n‖ - ‖z‖ ≥ ‖zeros n‖/2
      have hza_lower : ‖zeros n‖ / 2 ≤ ‖z - zeros n‖ := by
        have h1 : ‖zeros n‖ - ‖z‖ ≤ ‖z - zeros n‖ := by
          have := norm_add_le (zeros n - z) z
          rw [sub_add_cancel] at this
          linarith [norm_sub_rev (zeros n) z]
        linarith
      -- The bound: ‖1/(z-a) + 1/a‖ ≤ 2‖z‖ · ‖a‖⁻²
      rw [show (1 : ℂ) / (z - zeros n) + 1 / zeros n = z / (zeros n * (z - zeros n)) by
        field_simp; ring]
      rw [norm_div, norm_mul]
      have hd_pos : 0 < ‖zeros n‖ * ‖z - zeros n‖ :=
        mul_pos ha_pos (norm_pos_iff.mpr hzn_ne)
      have hd2_pos : 0 < ‖zeros n‖ * (‖zeros n‖ / 2) := by positivity
      calc ‖z‖ / (‖zeros n‖ * ‖z - zeros n‖)
          ≤ ‖z‖ / (‖zeros n‖ * (‖zeros n‖ / 2)) := by
            exact div_le_div_of_nonneg_left (norm_nonneg z) hd2_pos
              (mul_le_mul_of_nonneg_left hza_lower (le_of_lt ha_pos))
          _ = 2 * ‖z‖ * ‖zeros n‖⁻¹ ^ 2 := by
            field_simp
    -- Apply logDeriv_tprod_eq_tsum
    have key := logDeriv_tprod_eq_tsum hs_open hz_s hfne hfd hm_summ hmlu hprod_ne
    -- key : logDeriv (∏' i, fac i ·) z = ∑' i, logDeriv (fac i) z
    -- Convert to deriv/f form
    show logDeriv f₃ z = _
    rw [show f₃ = (∏' i, fac i ·) from hf₃_eq, key]
    exact funext hper_term ▸ rfl
  -- Combine: log derivative of a product f₁·f₂·f₃ is sum of log derivatives
  have hf₁_diff : DifferentiableAt ℂ f₁ z :=
    (differentiable_pow m).differentiableAt
  have hf₂_diff : DifferentiableAt ℂ f₂ z := by
    apply DifferentiableAt.cexp
    exact (differentiableAt_const a).add ((differentiableAt_const b).mul differentiableAt_id)
  have hf₃_diff : DifferentiableAt ℂ f₃ z := by
    simp only [hf₃_def]
    have hconv' : Summable (fun n => (‖zeros n‖⁻¹) ^ ((1 : ℕ) + 1 : ℝ)) := by
      convert hconv using 2; norm_num
    exact (tprod_weierstraßElementary_differentiable zeros 1 hconv').differentiableAt
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

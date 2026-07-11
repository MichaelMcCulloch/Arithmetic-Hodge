import ArithmeticHodge.Analysis.EntireFunction.CanonicalGrowth
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.Deriv.Polynomial

set_option autoImplicit false

open Complex Filter Topology Metric Set Polynomial

namespace ArithmeticHodge.Analysis.EntireFunction.GenericHadamardRepairScratch

/-!
## Production dependency repair

`CanonicalGrowth.lean` does not use any declaration from `GrowthBound.lean`.
Its first import can be replaced by the two actual dependencies

```lean
import ArithmeticHodge.Analysis.EntireFunction.WeierstraßProduct
import ArithmeticHodge.Analysis.BorelCaratheodory
```

while retaining `MinimumModulus` and its existing Mathlib imports.  Then
`Hadamard.lean` can import `CanonicalGrowth` rather than `GrowthBound`, and its
generic theorem body can be replaced verbatim by the proof below.

The old `weierstraß_quotient_growth` statement must not remain as a theorem:
its arbitrary factorization permits an exponential factor to be shifted
between `g` and the product, so the claimed bound is false.  After migrating
the sole in-repository caller, make `GrowthBound.lean` a compatibility import
of `CanonicalGrowth` (without the old declaration), or remove the module.  Do
not deprecate by retaining an axiom/sorry-backed alias.  The sound replacement
is `canonical_factorization_growth`, whose `beta`, canonical genus, and
inverse-`beta` summability hypotheses prevent that counterexample.
-/

/-- An entire function with globally vanishing `(n+1)`st derivative is a
polynomial of degree at most `n`. -/
private theorem polynomial_of_vanishing_iteratedDeriv (g : ℂ → ℂ)
    (hg : Differentiable ℂ g) (n : ℕ)
    (hvan : ∀ c : ℂ, iteratedDeriv (n + 1) g c = 0) :
    ∃ P : ℂ[X], P.natDegree ≤ n ∧ ∀ z, g z = aeval z P := by
  induction n generalizing g with
  | zero =>
    have hd : ∀ z, deriv g z = 0 := fun z => by
      have h := hvan z
      rwa [iteratedDeriv_succ, iteratedDeriv_zero] at h
    have hconst : ∀ z, g z = g 0 :=
      fun z => is_const_of_deriv_eq_zero hg hd z 0
    exact ⟨C (g 0), (natDegree_C _).le, fun z => by rw [hconst z]; simp⟩
  | succ n ih =>
    have hg' : Differentiable ℂ (deriv g) := hg.contDiff.differentiable_deriv_two
    have hvan' : ∀ c, iteratedDeriv (n + 1) (deriv g) c = 0 := fun c => by
      have h := hvan c
      rwa [iteratedDeriv_succ'] at h
    obtain ⟨Q, hQ_deg, hQ_eq⟩ := ih (deriv g) hg' hvan'
    let R : ℂ[X] := ∑ k ∈ Finset.range (n + 1),
      C (Q.coeff k / (↑(k + 1) : ℂ)) * X ^ (k + 1)
    have hR_deriv : derivative R = Q := by
      ext j
      simp only [R, map_sum, derivative_C_mul_X_pow, Nat.add_sub_cancel]
      have cancel : ∀ k, Q.coeff k / (↑(k + 1) : ℂ) * ↑(k + 1) = Q.coeff k :=
        fun k => div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k))
      simp_rw [cancel]
      conv_rhs => rw [Q.as_sum_range_C_mul_X_pow' (by omega : Q.natDegree < n + 1)]
    have hR_eval_zero : aeval (0 : ℂ) R = 0 := by
      simp only [R, map_sum, map_mul, aeval_C, aeval_X_pow,
        zero_pow (Nat.succ_ne_zero _), mul_zero, Finset.sum_const_zero]
    have hR_diff : Differentiable ℂ (fun z => aeval z R) := R.differentiable_aeval
    have hconst_diff : Differentiable ℂ (fun z => g z - aeval z R) := hg.sub hR_diff
    have hconst_deriv : ∀ z, deriv (fun w => g w - aeval w R) z = 0 := fun z => by
      have h : deriv (fun w => g w - aeval w R) z =
          deriv g z - deriv (fun w => aeval w R) z :=
        deriv_sub hg.differentiableAt hR_diff.differentiableAt
      rw [h, R.deriv_aeval, hR_deriv, hQ_eq z, sub_self]
    have hconst : ∀ z, g z = g 0 + aeval z R := fun z => by
      have h := is_const_of_deriv_eq_zero hconst_diff hconst_deriv z 0
      simp only [hR_eval_zero, sub_zero] at h
      exact eq_add_of_sub_eq h
    refine ⟨C (g 0) + R, ?_, fun z => ?_⟩
    · calc
        (C (g 0) + R).natDegree
            ≤ max (C (g 0)).natDegree R.natDegree := natDegree_add_le _ _
        _ ≤ max 0 (n + 1) := max_le_max ((natDegree_C _).le) (by
            exact natDegree_sum_le_of_forall_le _ _ fun k hk =>
              (natDegree_C_mul_X_pow_le _ _).trans (by
                simp only [Finset.mem_range] at hk
                omega))
        _ = n + 1 := by omega
    · rw [hconst z, map_add, aeval_C]
      simp

/-- Verbatim target shape of the generic production Hadamard theorem. -/
theorem hadamard_factorization_repaired (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hf_ne : ¬ f = 0) (hord : HasFiniteOrder f) :
    ∃ (m : ℕ) (P : Polynomial ℂ) (zeros : ℕ → ℂ) (p : ℕ),
      (P.natDegree ≤ Nat.floor (entireOrder f).toReal) ∧
      (∀ n, zeros n ≠ 0 → f (zeros n) = 0) ∧
      Summable (fun n => (‖zeros n‖⁻¹) ^ ((p : ℝ) + 1)) ∧
      ∀ z, f z = z ^ m * Complex.exp (Polynomial.aeval z P) *
        ∏' n, weierstraßElementary p (z / zeros n) := by
  obtain ⟨m, g, zeros, p, hg, hzeros, hconv, hfact, hp, _hcover, horders⟩ :=
    weierstraß_factorization_canonical f hf hf_ne hord
  let rho : ℝ := (entireOrder f).toReal
  have hord_ne_top : entireOrder f ≠ ⊤ := ne_of_lt hord
  have hord_ne_bot : entireOrder f ≠ ⊥ :=
    ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (entireOrder_nonneg f hf hf_ne))
  have hrho_coe : (rho : EReal) = entireOrder f :=
    EReal.coe_toReal hord_ne_top hord_ne_bot
  have hrho_nonneg : 0 ≤ rho :=
    EReal.toReal_nonneg (entireOrder_nonneg f hf hf_ne)
  have hp_le_rho : (p : ℝ) ≤ rho := by
    rw [hp]
    exact Nat.floor_le hrho_nonneg
  have hrho_lt_p1 : rho < (p : ℝ) + 1 := by
    rw [hp]
    exact_mod_cast Nat.lt_floor_add_one rho
  let beta : ℝ := (rho + ((p : ℝ) + 1)) / 2
  let alpha : ℝ := (beta + ((p : ℝ) + 1)) / 2
  have hp_beta : (p : ℝ) < beta := by
    simp only [beta]
    linarith
  have hrho_beta : rho < beta := by
    simp only [beta]
    linarith
  have hbeta_p1 : beta < (p : ℝ) + 1 := by
    simp only [beta]
    linarith
  have hbeta_alpha : beta < alpha := by
    simp only [alpha]
    linarith
  have halpha_p1 : alpha < (p : ℝ) + 1 := by
    simp only [alpha]
    linarith
  have hbeta_pos : 0 < beta :=
    lt_of_le_of_lt (Nat.cast_nonneg p) hp_beta
  have halpha_nonneg : 0 ≤ alpha :=
    (hbeta_pos.trans hbeta_alpha).le
  have horder_beta : entireOrder f < (beta : EReal) := by
    rw [← hrho_coe]
    exact EReal.coe_lt_coe_iff.mpr hrho_beta
  have horder_alpha : entireOrder f < (alpha : EReal) := by
    rw [← hrho_coe]
    exact EReal.coe_lt_coe_iff.mpr (hrho_beta.trans hbeta_alpha)
  have hsumm_beta : Summable (fun n ↦ ‖zeros n‖⁻¹ ^ beta) :=
    canonical_sequence_summable_of_order_lt f hf hf_ne zeros p hzeros hconv horders
      beta hbeta_pos horder_beta
  obtain ⟨C_g, hC_pos, hg_bound⟩ := canonical_factorization_growth
    f hf m g zeros p hg hfact beta alpha hp_beta hbeta_alpha hbeta_p1
      hsumm_beta horder_alpha
  have hvan : ∀ c : ℂ, iteratedDeriv (p + 1) g c = 0 := by
    have cauchy : ∀ (c : ℂ) (R : ℝ), 0 < R →
        ‖iteratedDeriv (p + 1) g c‖ ≤
        ↑(p + 1).factorial * (C_g * (1 + ‖c‖ + R) ^ alpha) / R ^ (p + 1) :=
      fun c R hR => norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le _ hR
        hg.diffContOnCl fun z hz => by
          rw [mem_sphere_iff_norm] at hz
          exact (hg_bound z).trans (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (by positivity)
              (by linarith [norm_le_insert' z c]) halpha_nonneg)
            hC_pos.le)
    let Bd : ℝ := ↑(p + 1).factorial * C_g * (2 : ℝ) ^ alpha
    have hBd_pos : 0 < Bd := by positivity
    have hbdd : ∀ c : ℂ, ‖iteratedDeriv (p + 1) g c‖ ≤ Bd := by
      intro c
      have hR : (0 : ℝ) < ‖c‖ + 1 := by positivity
      have h1 := cauchy c (‖c‖ + 1) hR
      have h2 : 1 + ‖c‖ + (‖c‖ + 1) = 2 * (‖c‖ + 1) := by ring
      rw [h2] at h1
      have h3 : (2 * (‖c‖ + 1)) ^ alpha =
          2 ^ alpha * (‖c‖ + 1) ^ alpha :=
        Real.mul_rpow (by positivity : (0 : ℝ) ≤ 2)
          (by positivity : (0 : ℝ) ≤ ‖c‖ + 1)
      have h4 : (‖c‖ + 1) ^ alpha ≤ (‖c‖ + 1) ^ ((p + 1 : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le
          (by linarith [norm_nonneg c] : 1 ≤ ‖c‖ + 1) (by
            simpa only [Nat.cast_add, Nat.cast_one] using halpha_p1.le)
      have h5 : (‖c‖ + 1) ^ ((p + 1 : ℕ) : ℝ) =
          (‖c‖ + 1) ^ (p + 1) := Real.rpow_natCast (‖c‖ + 1) (p + 1)
      calc
        ‖iteratedDeriv (p + 1) g c‖
            ≤ ↑(p + 1).factorial * (C_g * (2 * (‖c‖ + 1)) ^ alpha) /
                (‖c‖ + 1) ^ (p + 1) := h1
        _ = ↑(p + 1).factorial *
              (C_g * (2 ^ alpha * (‖c‖ + 1) ^ alpha)) /
                (‖c‖ + 1) ^ (p + 1) := by rw [h3]
        _ ≤ ↑(p + 1).factorial *
              (C_g * (2 ^ alpha * (‖c‖ + 1) ^ (p + 1))) /
                (‖c‖ + 1) ^ (p + 1) := by
          gcongr
          exact h4.trans (h5 ▸ le_refl _)
        _ = Bd := by
          simp only [Bd]
          field_simp
    have hg_deriv_diff : Differentiable ℂ (iteratedDeriv (p + 1) g) :=
      hg.contDiff.differentiable_iteratedDeriv (p + 1) (WithTop.coe_lt_top _)
    have hg_deriv_bdd : Bornology.IsBounded (Set.range (iteratedDeriv (p + 1) g)) :=
      (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := Bd)).subset
        (Set.range_subset_iff.mpr fun c => mem_closedBall_zero_iff.mpr (hbdd c))
    have hconst : ∀ c : ℂ,
        iteratedDeriv (p + 1) g c = iteratedDeriv (p + 1) g 0 :=
      fun c => hg_deriv_diff.apply_eq_apply_of_bounded hg_deriv_bdd c 0
    suffices h0 : iteratedDeriv (p + 1) g 0 = 0 by
      intro c
      rw [hconst c, h0]
    by_contra hne
    rw [← ne_eq, ← norm_pos_iff] at hne
    let delta : ℝ := ‖iteratedDeriv (p + 1) g 0‖
    let gamma : ℝ := (↑(p + 1) : ℝ) - alpha
    have hgamma_pos : 0 < gamma := by
      dsimp only [gamma]
      have h := halpha_p1
      norm_num only [Nat.cast_add, Nat.cast_one] at h ⊢
      linarith
    obtain ⟨n, hn⟩ := exists_nat_gt (max 1 ((Bd / delta) ^ gamma⁻¹))
    have hn_pos : (0 : ℝ) < n := by
      linarith [le_max_left 1 ((Bd / delta) ^ gamma⁻¹)]
    have hn_large : (Bd / delta) ^ gamma⁻¹ < (n : ℝ) := by
      linarith [le_max_right 1 ((Bd / delta) ^ gamma⁻¹)]
    have hn_rpow : (n : ℝ) ^ gamma > Bd / delta := by
      have h0 : (0 : ℝ) ≤ (Bd / delta) ^ gamma⁻¹ := by positivity
      calc
        (n : ℝ) ^ gamma > ((Bd / delta) ^ gamma⁻¹) ^ gamma :=
          Real.rpow_lt_rpow h0 hn_large hgamma_pos
        _ = Bd / delta := by
          rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ Bd / delta),
            inv_mul_cancel₀ hgamma_pos.ne', Real.rpow_one]
    have h_cauchy := cauchy 0 n hn_pos
    simp only [norm_zero, add_zero] at h_cauchy
    have h_1n : (1 : ℝ) + ↑n ≤ 2 * ↑n := by
      linarith [le_max_left 1 ((Bd / delta) ^ gamma⁻¹)]
    have h_sphere : (1 + (n : ℝ)) ^ alpha ≤ (2 * (n : ℝ)) ^ alpha :=
      Real.rpow_le_rpow (by positivity) h_1n halpha_nonneg
    have h_split : (2 * (n : ℝ)) ^ alpha = 2 ^ alpha * (n : ℝ) ^ alpha :=
      Real.mul_rpow (by positivity : (0 : ℝ) ≤ 2) hn_pos.le
    have h_rpow_div : (n : ℝ) ^ alpha / (n : ℝ) ^ (p + 1) =
        (n : ℝ) ^ (-gamma) := by
      dsimp only [gamma]
      rw [neg_sub, Real.rpow_sub hn_pos, Real.rpow_natCast]
    have h_rpow_neg : (n : ℝ) ^ (-gamma) = ((n : ℝ) ^ gamma)⁻¹ :=
      Real.rpow_neg hn_pos.le gamma
    have h_upper : delta ≤ Bd * ((n : ℝ) ^ gamma)⁻¹ := by
      calc
        delta ≤ ↑(p + 1).factorial * (C_g * (1 + ↑n) ^ alpha) /
            (↑n) ^ (p + 1) := h_cauchy
        _ ≤ ↑(p + 1).factorial * (C_g * (2 ^ alpha * (↑n) ^ alpha)) /
            (↑n) ^ (p + 1) := by
          gcongr
          calc
            (1 + (↑n : ℝ)) ^ alpha ≤ (2 * ↑n) ^ alpha := h_sphere
            _ = 2 ^ alpha * (↑n) ^ alpha := h_split
        _ = Bd * ((n : ℝ) ^ alpha / (n : ℝ) ^ (p + 1)) := by
          simp only [Bd]
          field_simp
        _ = Bd * (n : ℝ) ^ (-gamma) := by rw [h_rpow_div]
        _ = Bd * ((n : ℝ) ^ gamma)⁻¹ := by rw [h_rpow_neg]
    have h_lower : Bd * ((n : ℝ) ^ gamma)⁻¹ < delta := by
      rw [← div_eq_mul_inv, div_lt_iff₀ (by positivity : 0 < (n : ℝ) ^ gamma),
        mul_comm]
      exact (div_lt_iff₀ hne).mp hn_rpow
    linarith
  obtain ⟨P, hP_deg, hP_eq⟩ := polynomial_of_vanishing_iteratedDeriv g hg p hvan
  refine ⟨m, P, zeros, p, ?_, hzeros, hconv, ?_⟩
  · simpa only [hp] using hP_deg
  · intro z
    rw [hfact z, hP_eq z]

#print axioms hadamard_factorization_repaired

end ArithmeticHodge.Analysis.EntireFunction.GenericHadamardRepairScratch

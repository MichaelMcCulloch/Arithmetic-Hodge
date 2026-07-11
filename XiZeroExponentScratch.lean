import XiHadamardClosureScratch
import ZeroExponentScratch

set_option autoImplicit false

open Complex Filter Topology Real Set

namespace ArithmeticHodge.Analysis.EntireFunction

private theorem norm_exp_affine_xi_scratch (A B z : ℂ) :
    ‖Complex.exp (A + B * z)‖ ≤ Real.exp (‖A‖ + ‖B‖ * ‖z‖) := by
  rw [norm_exp]
  apply Real.exp_le_exp.mpr
  calc
    (A + B * z).re ≤ ‖A + B * z‖ := Complex.re_le_norm _
    _ ≤ ‖A‖ + ‖B * z‖ := norm_add_le _ _
    _ = ‖A‖ + ‖B‖ * ‖z‖ := by rw [norm_mul]

private theorem exists_geometric_lt_factorial_xi_scratch (K c : ℝ) :
    ∃ n : ℕ, K * c ^ (n + 1) < (n.factorial : ℝ) := by
  have ht : Tendsto (fun n : ℕ ↦ (K * c) * c ^ n / (n.factorial : ℝ))
      atTop (nhds 0) := by
    simpa using
      (FloorSemiring.tendsto_mul_pow_div_factorial_sub_atTop (K * c) c 0 :
        Tendsto (fun n : ℕ ↦ (K * c) * c ^ n / ((n - 0).factorial : ℝ))
          atTop (nhds 0))
  have heventually : ∀ᶠ n : ℕ in atTop,
      (K * c) * c ^ n / (n.factorial : ℝ) < 1 :=
    ht.eventually (Iio_mem_nhds zero_lt_one)
  obtain ⟨N, hN⟩ := eventually_atTop.1 heventually
  refine ⟨N, ?_⟩
  have h := hN N le_rfl
  rw [div_lt_one (by positivity : (0 : ℝ) < N.factorial)] at h
  calc
    K * c ^ (N + 1) = (K * c) * c ^ N := by rw [pow_succ]; ring
    _ < (N.factorial : ℝ) := h

/-- Xi's factorial growth rules out an affine genus-zero product whose inverse
zero norms are summable. -/
theorem xi_no_genus_zero_affine_factorization_scratch :
    ¬ ∃ (A B : ℂ) (a : ℕ → ℂ),
      Summable (fun n ↦ ‖a n‖⁻¹) ∧
      ∀ z, xiFunction z = Complex.exp (A + B * z) *
        ∏' n, weierstraßElementary 0 (z / a n) := by
  rintro ⟨A, B, a, hsumm, hfactorization⟩
  let S : ℝ := ∑' n, ‖a n‖⁻¹
  let D : ℝ := ‖B‖ + S
  have hS : 0 ≤ S := tsum_nonneg (fun n ↦ inv_nonneg.mpr (norm_nonneg _))
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hxi_bound : ∀ z : ℂ,
      ‖xiFunction z‖ ≤ Real.exp (‖A‖ + D * ‖z‖) := by
    intro z
    rw [hfactorization z, norm_mul]
    have haffine := norm_exp_affine_xi_scratch A B z
    have hproduct := norm_tprod_weierstrass_genus_zero_le_exp a hsumm z
    calc
      ‖Complex.exp (A + B * z)‖ *
          ‖∏' n, weierstraßElementary 0 (z / a n)‖ ≤
          Real.exp (‖A‖ + ‖B‖ * ‖z‖) * Real.exp (‖z‖ * S) := by
        gcongr
      _ = Real.exp (‖A‖ + D * ‖z‖) := by
        rw [← Real.exp_add]
        dsimp [D]
        congr 1
        ring
  let K : ℝ := Real.exp ‖A‖
  let c : ℝ := Real.pi * Real.exp (2 * D)
  obtain ⟨n, hn⟩ := exists_geometric_lt_factorial_xi_scratch K c
  let N : ℕ := n + 1
  let z : ℂ := ((2 * N : ℕ) : ℂ)
  have hz_norm : ‖z‖ = 2 * (N : ℝ) := by
    dsimp [z]
    rw [Complex.norm_natCast]
    push_cast
    rfl
  have hlower := xi_even_factorial_re_lower n
  have hupper : ‖xiFunction z‖ ≤ Real.exp (‖A‖ + D * (2 * N)) := by
    simpa only [hz_norm] using hxi_bound z
  have hfac_le : (n.factorial : ℝ) ≤ K * c ^ (n + 1) := by
    have hlower' : (n.factorial : ℝ) / Real.pi ^ N ≤ (xiFunction z).re := by
      simpa only [N, z, Nat.cast_mul, Nat.cast_ofNat] using hlower
    have hquot : (n.factorial : ℝ) / Real.pi ^ N ≤
        Real.exp (‖A‖ + D * (2 * N)) :=
      hlower'.trans ((Complex.re_le_norm _).trans hupper)
    have hden : 0 < Real.pi ^ N := pow_pos Real.pi_pos _
    have hfac₀ : (n.factorial : ℝ) ≤
        Real.exp (‖A‖ + D * (2 * N)) * Real.pi ^ N :=
      (div_le_iff₀ hden).mp hquot
    calc
      (n.factorial : ℝ) ≤
          Real.exp (‖A‖ + D * (2 * N)) * Real.pi ^ N := hfac₀
      _ = Real.exp ‖A‖ * Real.pi ^ N * Real.exp (2 * D * N) := by
        rw [Real.exp_add]
        have hexp : Real.exp (D * (2 * (N : ℝ))) =
            Real.exp (2 * D * N) := by congr 1 <;> ring
        rw [hexp]
        ring
      _ = Real.exp ‖A‖ * (Real.pi * Real.exp (2 * D)) ^ N := by
        rw [mul_pow, ← Real.exp_nat_mul]
        ring
      _ = K * c ^ N := by rfl
      _ = K * c ^ (n + 1) := by rfl
  exact (not_le_of_gt hn) hfac_le

private theorem weierstrass_one_eq_zero_mul_exp_xi_scratch (w : ℂ) :
    weierstraßElementary 1 w =
      weierstraßElementary 0 w * Complex.exp w := by
  simp [weierstraßElementary]

/-- Absolute inverse-norm convergence would let the genus-one corrections be
absorbed into the affine exponential, contradicting xi's factorial growth. -/
theorem xi_no_genus_one_affine_with_inv_sum_scratch :
    ¬ ∃ (A B : ℂ) (a : ℕ → ℂ),
      Summable (fun n ↦ ‖a n‖⁻¹) ∧
      ∀ z, xiFunction z = Complex.exp (A + B * z) *
        ∏' n, weierstraßElementary 1 (z / a n) := by
  rintro ⟨A, B, a, hsumm, hfactorization⟩
  have hsumm_inv_norm : Summable (fun n ↦ ‖(a n)⁻¹‖) := by
    simpa only [norm_inv] using hsumm
  have hsumm_inv : Summable (fun n ↦ (a n)⁻¹) := hsumm_inv_norm.of_norm
  let T : ℂ := ∑' n, (a n)⁻¹
  apply xi_no_genus_zero_affine_factorization_scratch
  refine ⟨A, B + T, a, hsumm, fun z ↦ ?_⟩
  have hzero_rpow : Summable (fun n ↦ ‖a n‖⁻¹ ^ (1 : ℝ)) := by
    simpa using hsumm
  have hmult_zero : Multipliable (fun n ↦ weierstraßElementary 0 (z / a n)) :=
    multipliable_weierstraßElementary_raw a 0 (by simpa using hzero_rpow) z
  have hzsum : HasSum (fun n ↦ z / a n) (z * T) := by
    simpa only [T, div_eq_mul_inv] using hsumm_inv.hasSum.mul_left z
  have hexp_prod : HasProd (fun n ↦ Complex.exp (z / a n)) (Complex.exp (z * T)) :=
    hzsum.cexp
  have hproduct :
      (∏' n, weierstraßElementary 1 (z / a n)) =
        (∏' n, weierstraßElementary 0 (z / a n)) * Complex.exp (z * T) := by
    calc
      (∏' n, weierstraßElementary 1 (z / a n)) =
          ∏' n, (weierstraßElementary 0 (z / a n) * Complex.exp (z / a n)) := by
        apply tprod_congr
        intro n
        exact weierstrass_one_eq_zero_mul_exp_xi_scratch _
      _ = (∏' n, weierstraßElementary 0 (z / a n)) *
          ∏' n, Complex.exp (z / a n) :=
        hmult_zero.tprod_mul hexp_prod.multipliable
      _ = (∏' n, weierstraßElementary 0 (z / a n)) * Complex.exp (z * T) := by
        rw [hexp_prod.tprod_eq]
  rw [hfactorization z, hproduct]
  rw [show Complex.exp (A + (B + T) * z) =
      Complex.exp (A + B * z) * Complex.exp (z * T) by
    rw [← Complex.exp_add]
    congr 1
    ring]
  ring

private theorem summable_inv_norm_of_summable_rpow_lt_one_xi_scratch
    (a : ℕ → ℂ) (s : ℝ) (hs₀ : 0 < s) (hs₁ : s < 1)
    (hsumm : Summable (fun n ↦ ‖a n‖⁻¹ ^ s)) :
    Summable (fun n ↦ ‖a n‖⁻¹) := by
  have hfinite : Set.Finite {n : ℕ | a n ≠ 0 ∧ ‖a n‖ ≤ 1} :=
    finite_nonzero_indices_norm_le a s hs₀ hsumm 1 zero_lt_one
  apply hsumm.of_norm_bounded_eventually
  rw [Filter.eventually_cofinite]
  apply hfinite.subset
  intro n hn
  simp only [Set.mem_setOf_eq] at hn ⊢
  have han : a n ≠ 0 := by
    intro han
    apply hn
    simp [han, Real.zero_rpow hs₀.ne']
  refine ⟨han, ?_⟩
  by_contra hnorm
  have hnorm' : 1 < ‖a n‖ := lt_of_not_ge hnorm
  have hinv_pos : 0 < ‖a n‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr han)
  have hinv_one : ‖a n‖⁻¹ ≤ 1 :=
    (inv_le_one₀ (norm_pos_iff.mpr han)).mpr hnorm'.le
  apply hn
  rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  simpa only [Real.rpow_one] using
    (Real.rpow_le_rpow_of_exponent_ge hinv_pos hinv_one hs₁.le)

/-- There is a multiplicity-repeated xi zero sequence with convergence
exponent exactly one: every power above one is summable, and every power below
one diverges. -/
theorem exists_xi_zero_sequence_exponent_one_scratch :
    ∃ zeros : ℕ → ℂ,
      (∀ n, zeros n ≠ 0) ∧
      (∀ n, xiFunction (zeros n) = 0) ∧
      Summable (fun n ↦ ‖zeros n‖⁻¹ ^ (2 : ℝ)) ∧
      ∀ s : ℝ, 0 < s → s < 1 →
        ¬ Summable (fun n ↦ ‖zeros n‖⁻¹ ^ s) := by
  obtain ⟨m, A, B, zeros, hne, hzero, hsumm2, hfactorization⟩ :=
    xi_hadamard_product_closed_scratch
  have hm : m = 0 := by
    by_contra hm
    have h0 := hfactorization 0
    rw [xiFunction_zero_val] at h0
    simp [zero_pow hm] at h0
  refine ⟨zeros, hne, hzero, hsumm2, fun s hs₀ hs₁ hsumm ↦ ?_⟩
  apply xi_no_genus_one_affine_with_inv_sum_scratch
  refine ⟨A, B, zeros,
    summable_inv_norm_of_summable_rpow_lt_one_xi_scratch zeros s hs₀ hs₁ hsumm,
    fun z ↦ ?_⟩
  simpa [hm] using hfactorization z

#print axioms xi_no_genus_zero_affine_factorization_scratch
#print axioms xi_no_genus_one_affine_with_inv_sum_scratch
#print axioms exists_xi_zero_sequence_exponent_one_scratch

end ArithmeticHodge.Analysis.EntireFunction

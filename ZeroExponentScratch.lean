import ArithmeticHodge.Analysis.ZetaProduct
import ArithmeticHodge.Analysis.EntireFunction.WeierstraßProduct
import Mathlib.Analysis.SpecialFunctions.Log.Summable

set_option autoImplicit false

open Complex Filter Topology Real Set

namespace ArithmeticHodge.Analysis.EntireFunction

/-- The zero set at issue is the `1/2`-point set of xi, not the xi/zeta zero
set controlled by the new vertical-strip regularization. -/
theorem completedZeta_zero_implies_xi_eq_half_scratch {s : ℂ}
    (hs : completedRiemannZeta₀ s = 0) :
    xiFunction s = 1 / 2 := by
  simp [xiFunction, hs]

private theorem log_norm_tprod_weierstrass_scratch
    (zeros : ℕ → ℂ) (p : ℕ)
    (hconv : Summable (fun n ↦ (‖zeros n‖⁻¹) ^ ((p : ℝ) + 1)))
    (z : ℂ) (hne : ∀ n, z / zeros n ≠ 1) :
    Real.log ‖∏' n, weierstraßElementary p (z / zeros n)‖ =
      ∑' n, Real.log ‖weierstraßElementary p (z / zeros n)‖ := by
  let u : ℕ → ℂ := fun n ↦ weierstraßElementary p (z / zeros n) - 1
  have hu : Summable (fun n ↦ ‖u n‖) := by
    simpa only [u] using perturbation_summable' zeros p hconv z
  have hlog : Summable (fun n ↦ Real.log ‖1 + u n‖) :=
    hu.summable_log_norm_one_add
  have hpos : ∀ n, 0 < ‖1 + u n‖ := by
    intro n
    apply norm_pos_iff.mpr
    simpa only [u, add_sub_cancel] using
      weierstraßElementary_ne_zero p (z / zeros n) (hne n)
  have hmult : Multipliable (fun n ↦ weierstraßElementary p (z / zeros n)) :=
    multipliable_weierstraßElementary_raw zeros p hconv z
  have hexp : Real.exp (∑' n, Real.log ‖1 + u n‖) = ∏' n, ‖1 + u n‖ :=
    Real.rexp_tsum_eq_tprod hpos hlog
  calc
    Real.log ‖∏' n, weierstraßElementary p (z / zeros n)‖ =
        Real.log (∏' n, ‖weierstraßElementary p (z / zeros n)‖) := by
      rw [hmult.norm_tprod]
    _ = Real.log (Real.exp (∑' n, Real.log ‖1 + u n‖)) := by
      rw [hexp]
      congr 2
      ext n
      simp only [u, add_sub_cancel]
    _ = ∑' n, Real.log ‖1 + u n‖ := Real.log_exp _
    _ = ∑' n, Real.log ‖weierstraßElementary p (z / zeros n)‖ := by
      congr 1
      ext n
      simp only [u, add_sub_cancel]

/-- A convergent genus-zero canonical product is of finite exponential type. -/
theorem norm_tprod_weierstrass_genus_zero_le_exp
    (a : ℕ → ℂ)
    (hsumm : Summable (fun n ↦ ‖a n‖⁻¹))
    (z : ℂ) :
    ‖∏' n, weierstraßElementary 0 (z / a n)‖ ≤
      Real.exp (‖z‖ * ∑' n, ‖a n‖⁻¹) := by
  have hsumm_rpow : Summable (fun n ↦ ‖a n‖⁻¹ ^ (1 : ℝ)) := by
    simpa using hsumm
  have hmult : Multipliable (fun n ↦ weierstraßElementary 0 (z / a n)) :=
    multipliable_weierstraßElementary_raw a 0 (by simpa using hsumm_rpow) z
  let w : ℕ → ℝ := fun n ↦ ‖z‖ * ‖a n‖⁻¹
  have hw : Summable w := hsumm.mul_left ‖z‖
  have hfactor : ∀ n,
      ‖weierstraßElementary 0 (z / a n)‖ ≤ Real.exp (w n) := by
    intro n
    rw [weierstraßElementary_genus_zero]
    calc
      ‖1 - z / a n‖ ≤ 1 + ‖z / a n‖ := by
        simpa only [norm_one] using norm_sub_le (1 : ℂ) (z / a n)
      _ = 1 + w n := by
        simp only [w, div_eq_mul_inv, norm_mul, norm_inv]
      _ ≤ Real.exp (w n) := by
        simpa only [add_comm] using Real.add_one_le_exp (w n)
  by_cases hzero : ∃ n, z / a n = 1
  · have hprod_zero :
        (∏' n, weierstraßElementary 0 (z / a n)) = 0 := by
      apply tprod_of_exists_eq_zero
      obtain ⟨n, hn⟩ := hzero
      refine ⟨n, ?_⟩
      rw [hn, weierstraßElementary_genus_zero]
      ring
    rw [hprod_zero, norm_zero]
    positivity
  · push_neg at hzero
    have hprod_ne : (∏' n, weierstraßElementary 0 (z / a n)) ≠ 0 :=
      tprod_weierstraßElementary_ne_zero a 0 (by simpa using hsumm_rpow) z hzero
    have hlog_summable :
        Summable (fun n ↦ Real.log ‖weierstraßElementary 0 (z / a n)‖) := by
      let u : ℕ → ℂ := fun n ↦ weierstraßElementary 0 (z / a n) - 1
      have hu : Summable (fun n ↦ ‖u n‖) := by
        simpa only [u] using
          perturbation_summable' a 0 (by simpa using hsumm_rpow) z
      simpa only [u, add_sub_cancel] using hu.summable_log_norm_one_add
    have hlog_factor : ∀ n,
        Real.log ‖weierstraßElementary 0 (z / a n)‖ ≤ w n := by
      intro n
      exact (Real.log_le_iff_le_exp
        (norm_pos_iff.mpr (weierstraßElementary_ne_zero 0 _ (hzero n)))).mpr (hfactor n)
    have hlog_product :
        Real.log ‖∏' n, weierstraßElementary 0 (z / a n)‖ ≤ ∑' n, w n := by
      rw [log_norm_tprod_weierstrass_scratch a 0 (by simpa using hsumm_rpow) z hzero]
      exact hlog_summable.tsum_le_tsum hlog_factor hw
    calc
      ‖∏' n, weierstraßElementary 0 (z / a n)‖ =
          Real.exp (Real.log ‖∏' n, weierstraßElementary 0 (z / a n)‖) :=
        (Real.exp_log (norm_pos_iff.mpr hprod_ne)).symm
      _ ≤ Real.exp (∑' n, w n) := Real.exp_le_exp.mpr hlog_product
      _ = Real.exp (‖z‖ * ∑' n, ‖a n‖⁻¹) := by
        rw [tsum_mul_left]

private theorem norm_exp_affine_scratch (A B z : ℂ) :
    ‖Complex.exp (A + B * z)‖ ≤ Real.exp (‖A‖ + ‖B‖ * ‖z‖) := by
  rw [norm_exp]
  apply Real.exp_le_exp.mpr
  calc
    (A + B * z).re ≤ ‖A + B * z‖ := Complex.re_le_norm _
    _ ≤ ‖A‖ + ‖B * z‖ := norm_add_le _ _
    _ = ‖A‖ + ‖B‖ * ‖z‖ := by rw [norm_mul]

private theorem exists_geometric_lt_factorial_scratch (K c : ℝ) :
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

/-- The analytic endpoint of the proposed zero-exponent argument: the
completed zeta cannot have a genus-zero product with only an affine
exponential factor. -/
theorem completedZeta_no_genus_zero_affine_factorization_scratch :
    ¬ ∃ (m : ℕ) (A B : ℂ) (a : ℕ → ℂ),
      Summable (fun n ↦ ‖a n‖⁻¹) ∧
      ∀ z, completedRiemannZeta₀ z = z ^ m * Complex.exp (A + B * z) *
        ∏' n, weierstraßElementary 0 (z / a n) := by
  rintro ⟨m, A, B, a, hsumm, hfactorization⟩
  let S : ℝ := ∑' n, ‖a n‖⁻¹
  let D : ℝ := ‖B‖ + S
  have hS : 0 ≤ S := tsum_nonneg (fun n ↦ inv_nonneg.mpr (norm_nonneg _))
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hcompleted_bound : ∀ z : ℂ,
      ‖completedRiemannZeta₀ z‖ ≤
        ‖z‖ ^ m * Real.exp (‖A‖ + D * ‖z‖) := by
    intro z
    rw [hfactorization z, norm_mul, norm_mul]
    have haffine := norm_exp_affine_scratch A B z
    have hproduct := norm_tprod_weierstrass_genus_zero_le_exp a hsumm z
    calc
      ‖z ^ m‖ * ‖Complex.exp (A + B * z)‖ *
          ‖∏' n, weierstraßElementary 0 (z / a n)‖ ≤
          ‖z‖ ^ m * Real.exp (‖A‖ + ‖B‖ * ‖z‖) *
            Real.exp (‖z‖ * S) := by
        rw [norm_pow]
        gcongr
      _ = ‖z‖ ^ m * Real.exp (‖A‖ + D * ‖z‖) := by
        rw [mul_assoc, ← Real.exp_add]
        dsimp [D]
        congr 2
        ring
  let E : ℝ := 2 * D + (m : ℝ) + 2
  let K : ℝ := 2 ^ (m + 3) * Real.exp ‖A‖
  let c : ℝ := Real.pi * Real.exp E
  obtain ⟨n, hn⟩ := exists_geometric_lt_factorial_scratch K c
  let N : ℕ := n + 1
  let z : ℂ := ((2 * N : ℕ) : ℂ)
  have hN_pos : (0 : ℝ) < N := by positivity
  have hN_one : (1 : ℝ) ≤ N := by
    dsimp [N]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hz_norm : ‖z‖ = 2 * (N : ℝ) := by
    dsimp [z]
    rw [Complex.norm_natCast]
    push_cast
    rfl
  have hN_pow_exp : (N : ℝ) ^ (m + 2) ≤ Real.exp (((m : ℝ) + 2) * N) := by
    rw [show (N : ℝ) ^ (m + 2) = (N : ℝ) ^ ((m + 2 : ℕ) : ℝ) by
      rw [Real.rpow_natCast]]
    rw [Real.rpow_def_of_pos hN_pos]
    apply Real.exp_le_exp.mpr
    calc
      Real.log (N : ℝ) * ((m + 2 : ℕ) : ℝ) ≤
          (N : ℝ) * ((m + 2 : ℕ) : ℝ) := by
        gcongr
        exact Real.log_le_self hN_pos.le
      _ = ((m : ℝ) + 2) * N := by push_cast; ring
  have hxi_upper : ‖xiFunction z‖ ≤
      2 ^ (m + 3) * Real.exp ‖A‖ * Real.exp (E * N) := by
    have hLambda := hcompleted_bound z
    have hz_sub : ‖z - 1‖ ≤ 2 * (N : ℝ) := by
      have hz_sub_eq : z - 1 = ((2 * (N : ℝ) - 1 : ℝ) : ℂ) := by
        dsimp [z]
        push_cast
        ring
      rw [hz_sub_eq]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
      · linarith
      · linarith
    rw [xiFunction]
    calc
      ‖(1 / 2 : ℂ) * z * (z - 1) * completedRiemannZeta₀ z + 1 / 2‖ ≤
          (1 / 2 : ℝ) * ‖z‖ * ‖z - 1‖ * ‖completedRiemannZeta₀ z‖ + 1 / 2 := by
        simpa only [norm_mul, norm_div, norm_one, Complex.norm_ofNat] using
          norm_add_le ((1 / 2 : ℂ) * z * (z - 1) * completedRiemannZeta₀ z) (1 / 2)
      _ ≤ (1 / 2 : ℝ) * (2 * N) * (4 * N) *
          ((2 * N) ^ m * Real.exp (‖A‖ + D * (2 * N))) + 1 / 2 := by
        have hLambda' : ‖completedRiemannZeta₀ z‖ ≤
            (2 * (N : ℝ)) ^ m * Real.exp (‖A‖ + D * (2 * N)) := by
          simpa only [hz_norm] using hLambda
        rw [hz_norm]
        gcongr
        exact hz_sub.trans (by linarith)
      _ = 2 ^ (m + 2) * (N : ℝ) ^ (m + 2) *
          Real.exp (‖A‖ + 2 * D * N) + 1 / 2 := by
        rw [mul_pow]
        ring_nf
      _ ≤ 2 ^ (m + 2) * Real.exp (((m : ℝ) + 2) * N) *
          Real.exp (‖A‖ + 2 * D * N) + 1 / 2 := by gcongr
      _ ≤ 2 ^ (m + 3) * Real.exp ‖A‖ * Real.exp (E * N) := by
        let Q : ℝ := 2 ^ (m + 2) * Real.exp ‖A‖ * Real.exp (E * N)
        have hleft : 2 ^ (m + 2) * Real.exp (((m : ℝ) + 2) * N) *
            Real.exp (‖A‖ + 2 * D * N) = Q := by
          dsimp [Q]
          calc
            2 ^ (m + 2) * Real.exp (((m : ℝ) + 2) * N) *
                Real.exp (‖A‖ + 2 * D * N) =
                2 ^ (m + 2) * Real.exp
                  (((m : ℝ) + 2) * N + (‖A‖ + 2 * D * N)) := by
              rw [mul_assoc, ← Real.exp_add]
            _ = 2 ^ (m + 2) * Real.exp (‖A‖ + E * N) := by
              congr 2
              dsimp [E]
              ring
            _ = 2 ^ (m + 2) * Real.exp ‖A‖ * Real.exp (E * N) := by
              rw [Real.exp_add]
              ring
        have hright :
            2 ^ (m + 3) * Real.exp ‖A‖ * Real.exp (E * N) = 2 * Q := by
          dsimp [Q]
          rw [show m + 3 = (m + 2) + 1 by omega, pow_succ]
          ring
        have hE : 0 ≤ E := by
          dsimp [E]
          positivity
        have hQ_one : 1 ≤ Q := by
          dsimp [Q]
          have hpow : (1 : ℝ) ≤ 2 ^ (m + 2) := one_le_pow₀ (by norm_num)
          have hAexp : (1 : ℝ) ≤ Real.exp ‖A‖ := Real.one_le_exp (norm_nonneg A)
          have hEexp : (1 : ℝ) ≤ Real.exp (E * N) :=
            Real.one_le_exp (mul_nonneg hE hN_pos.le)
          have hfirst : (1 : ℝ) ≤ 2 ^ (m + 2) * Real.exp ‖A‖ := by
            nlinarith [mul_le_mul hpow hAexp zero_le_one (by positivity)]
          nlinarith [mul_le_mul hfirst hEexp zero_le_one (by positivity)]
        rw [hleft, hright]
        linarith
  have hlower := xi_even_factorial_re_lower n
  have hfac_le : (n.factorial : ℝ) ≤ K * c ^ (n + 1) := by
    have hlower' : (n.factorial : ℝ) / Real.pi ^ N ≤
        (xiFunction z).re := by
      simpa only [N, z, Nat.cast_mul, Nat.cast_ofNat] using hlower
    have hquot : (n.factorial : ℝ) / Real.pi ^ N ≤
        2 ^ (m + 3) * Real.exp ‖A‖ * Real.exp (E * N) :=
      hlower'.trans ((Complex.re_le_norm _).trans hxi_upper)
    have hden : 0 < Real.pi ^ N := pow_pos Real.pi_pos _
    have hfac₀ : (n.factorial : ℝ) ≤
        (2 ^ (m + 3) * Real.exp ‖A‖ * Real.exp (E * N)) * Real.pi ^ N :=
      (div_le_iff₀ hden).mp hquot
    calc
      (n.factorial : ℝ) ≤
          (2 ^ (m + 3) * Real.exp ‖A‖ * Real.exp (E * N)) * Real.pi ^ N := hfac₀
      _ = K * c ^ N := by
        dsimp [K, c]
        rw [mul_pow, ← Real.exp_nat_mul]
        ring_nf
      _ = K * c ^ (n + 1) := by rfl
  exact (not_le_of_gt hn) hfac_le

private theorem weierstrass_one_eq_zero_mul_exp_scratch (w : ℂ) :
    weierstraßElementary 1 w = weierstraßElementary 0 w * Complex.exp w := by
  simp [weierstraßElementary]

/-- Absolute convergence of the first inverse powers also rules out an
affine genus-one factorization: the exponential corrections can be summed
and absorbed into the linear coefficient. -/
theorem completedZeta_no_genus_one_affine_with_inv_sum_scratch :
    ¬ ∃ (m : ℕ) (A B : ℂ) (a : ℕ → ℂ),
      Summable (fun n ↦ ‖a n‖⁻¹) ∧
      ∀ z, completedRiemannZeta₀ z = z ^ m * Complex.exp (A + B * z) *
        ∏' n, weierstraßElementary 1 (z / a n) := by
  rintro ⟨m, A, B, a, hsumm, hfactorization⟩
  have hsumm_inv_norm : Summable (fun n ↦ ‖(a n)⁻¹‖) := by
    simpa only [norm_inv] using hsumm
  have hsumm_inv : Summable (fun n ↦ (a n)⁻¹) := hsumm_inv_norm.of_norm
  let T : ℂ := ∑' n, (a n)⁻¹
  apply completedZeta_no_genus_zero_affine_factorization_scratch
  refine ⟨m, A, B + T, a, hsumm, fun z ↦ ?_⟩
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
        exact weierstrass_one_eq_zero_mul_exp_scratch _
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

private theorem summable_inv_norm_of_summable_rpow_lt_one_scratch
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

/-- Conditional form matching the intended infinite-type argument. It is
fully sufficient once the sequence is the multiplicity-repeated Hadamard
zero sequence. -/
theorem completedZeta_no_genus_one_affine_with_inv_rpow_lt_one_scratch
    (s : ℝ) (hs₀ : 0 < s) (hs₁ : s < 1) :
    ¬ ∃ (m : ℕ) (A B : ℂ) (a : ℕ → ℂ),
      Summable (fun n ↦ ‖a n‖⁻¹ ^ s) ∧
      ∀ z, completedRiemannZeta₀ z = z ^ m * Complex.exp (A + B * z) *
        ∏' n, weierstraßElementary 1 (z / a n) := by
  rintro ⟨m, A, B, a, hsumm, hfactorization⟩
  exact completedZeta_no_genus_one_affine_with_inv_sum_scratch
    ⟨m, A, B, a,
      summable_inv_norm_of_summable_rpow_lt_one_scratch a s hs₀ hs₁ hsumm,
      hfactorization⟩

#print axioms norm_tprod_weierstrass_genus_zero_le_exp
#print axioms completedZeta_zero_implies_xi_eq_half_scratch
#print axioms completedZeta_no_genus_zero_affine_factorization_scratch
#print axioms completedZeta_no_genus_one_affine_with_inv_sum_scratch
#print axioms completedZeta_no_genus_one_affine_with_inv_rpow_lt_one_scratch

end ArithmeticHodge.Analysis.EntireFunction

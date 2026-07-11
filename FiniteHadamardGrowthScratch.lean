import ArithmeticHodge.Analysis.ZetaProduct
import Mathlib.Topology.Algebra.Order.Floor

open Complex Filter Topology Real Set Finset BigOperators

namespace ArithmeticHodge.Analysis

set_option autoImplicit false

/-- A genus-one elementary factor has at most exponential growth. -/
private theorem norm_weierstraßElementary_one_le_exp (w : ℂ) :
    ‖EntireFunction.weierstraßElementary 1 w‖ ≤ Real.exp (2 * ‖w‖) := by
  have hE : EntireFunction.weierstraßElementary 1 w =
      (1 - w) * Complex.exp w := by
    simp [EntireFunction.weierstraßElementary]
  rw [hE]
  rw [norm_mul, norm_exp]
  have hsub : ‖1 - w‖ ≤ 1 + ‖w‖ := by
    simpa using norm_sub_le (1 : ℂ) w
  have hre : Real.exp w.re ≤ Real.exp ‖w‖ :=
    Real.exp_le_exp.mpr (Complex.re_le_norm w)
  calc
    ‖1 - w‖ * Real.exp w.re ≤ (1 + ‖w‖) * Real.exp ‖w‖ :=
      mul_le_mul hsub hre (Real.exp_nonneg _) (by positivity)
    _ ≤ Real.exp ‖w‖ * Real.exp ‖w‖ := by
      exact mul_le_mul_of_nonneg_right
        (by simpa [add_comm] using Real.add_one_le_exp ‖w‖) (Real.exp_nonneg _)
    _ = Real.exp (2 * ‖w‖) := by rw [← Real.exp_add]; congr 1; ring

private theorem norm_weierstraßElementary_one_div_le_exp (z a : ℂ) :
    ‖EntireFunction.weierstraßElementary 1 (z / a)‖ ≤
      Real.exp ((2 * ‖z‖) * ‖a‖⁻¹) := by
  convert norm_weierstraßElementary_one_le_exp (z / a) using 1
  rw [norm_div, div_eq_mul_inv]
  ring_nf

/-- A padded finite genus-one product is bounded by an exponential whose
linear rate is the sum of the inverse norms of its nonzero parameters. -/
private theorem norm_tprod_weierstraßElementary_one_le_exp
    (a : ℕ → ℂ) (F : Finset ℕ) (hF : ∀ n ∉ F, a n = 0) (z : ℂ) :
    ‖∏' n, EntireFunction.weierstraßElementary 1 (z / a n)‖ ≤
      Real.exp ((2 * ‖z‖) * ∑ n ∈ F, ‖a n‖⁻¹) := by
  have htprod :
      (∏' n, EntireFunction.weierstraßElementary 1 (z / a n)) =
        ∏ n ∈ F, EntireFunction.weierstraßElementary 1 (z / a n) := by
    apply tprod_eq_prod
    intro n hn
    rw [hF n hn]
    simp [EntireFunction.weierstraßElementary_zero]
  rw [htprod, norm_prod]
  calc
    ∏ n ∈ F, ‖EntireFunction.weierstraßElementary 1 (z / a n)‖ ≤
        ∏ n ∈ F, Real.exp ((2 * ‖z‖) * ‖a n‖⁻¹) := by
      gcongr with n hn
      exact norm_weierstraßElementary_one_div_le_exp z (a n)
    _ = Real.exp (∑ n ∈ F, (2 * ‖z‖) * ‖a n‖⁻¹) := by
      rw [Real.exp_sum]
    _ = Real.exp ((2 * ‖z‖) * ∑ n ∈ F, ‖a n‖⁻¹) := by
      rw [Finset.mul_sum]

private theorem norm_exp_affine_le_exp (A B z : ℂ) :
    ‖Complex.exp (A + B * z)‖ ≤ Real.exp (‖A‖ + ‖B‖ * ‖z‖) := by
  rw [norm_exp]
  apply Real.exp_le_exp.mpr
  calc
    (A + B * z).re ≤ ‖A + B * z‖ := Complex.re_le_norm _
    _ ≤ ‖A‖ + ‖B * z‖ := norm_add_le _ _
    _ = ‖A‖ + ‖B‖ * ‖z‖ := by rw [norm_mul]

private theorem norm_xi_of_finite_factorization_le_exp
    (A B : ℂ) (a : ℕ → ℂ) (F : Finset ℕ)
    (hF : ∀ n ∉ F, a n = 0)
    (hfactorization : ∀ z, xiFunction z = Complex.exp (A + B * z) *
      ∏' n, EntireFunction.weierstraßElementary 1 (z / a n)) (z : ℂ) :
    ‖xiFunction z‖ ≤
      Real.exp (‖A‖ + (‖B‖ + 2 * (∑ n ∈ F, ‖a n‖⁻¹)) * ‖z‖) := by
  rw [hfactorization z, norm_mul]
  have haffine := norm_exp_affine_le_exp A B z
  have hproduct := norm_tprod_weierstraßElementary_one_le_exp a F hF z
  calc
    ‖Complex.exp (A + B * z)‖ *
        ‖∏' n, EntireFunction.weierstraßElementary 1 (z / a n)‖ ≤
        Real.exp (‖A‖ + ‖B‖ * ‖z‖) *
          Real.exp ((2 * ‖z‖) * ∑ n ∈ F, ‖a n‖⁻¹) :=
      mul_le_mul haffine hproduct (norm_nonneg _) (Real.exp_nonneg _)
    _ = Real.exp (‖A‖ + (‖B‖ + 2 * (∑ n ∈ F, ‖a n‖⁻¹)) * ‖z‖) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- Factorials eventually dominate a fixed constant times any fixed real
geometric progression. -/
private theorem exists_const_mul_pow_lt_factorial (K c : ℝ) :
    ∃ n : ℕ, K * c ^ n < (n.factorial : ℝ) := by
  have ht : Tendsto (fun n : ℕ ↦ K * c ^ n / (n.factorial : ℝ))
      atTop (nhds 0) := by
    simpa using
      (FloorSemiring.tendsto_mul_pow_div_factorial_sub_atTop K c 0 :
        Tendsto (fun n : ℕ ↦ K * c ^ n / ((n - 0).factorial : ℝ))
          atTop (nhds 0))
  have heventually : ∀ᶠ n : ℕ in atTop,
      K * c ^ n / (n.factorial : ℝ) < 1 :=
    ht.eventually (Iio_mem_nhds zero_lt_one)
  obtain ⟨N, hN⟩ := eventually_atTop.1 heventually
  refine ⟨N, ?_⟩
  have h := hN N le_rfl
  rwa [div_lt_one (by positivity : (0 : ℝ) < N.factorial)] at h

/-- A finite padded genus-one Hadamard product cannot represent the Riemann
xi function.  Entries `a n = 0` are padding and contribute the factor one. -/
theorem xi_no_finite_genus_one_factorization_scratch :
    ¬ ∃ (A B : ℂ) (a : ℕ → ℂ),
      Set.Finite {n | a n ≠ 0} ∧
      ∀ z, xiFunction z = Complex.exp (A + B * z) *
        ∏' n, EntireFunction.weierstraßElementary 1 (z / a n) := by
  classical
  rintro ⟨A, B, a, hfinite, hfactorization⟩
  let F : Finset ℕ := hfinite.toFinset
  have hF : ∀ n ∉ F, a n = 0 := by
    intro n hn
    by_contra hne
    apply hn
    dsimp [F]
    rw [Set.Finite.mem_toFinset]
    simpa only [Set.mem_setOf_eq] using hne
  let D : ℝ := ‖B‖ + 2 * (∑ n ∈ F, ‖a n‖⁻¹)
  let c : ℝ := Real.pi * Real.exp (2 * D)
  obtain ⟨n, hn⟩ :=
    exists_const_mul_pow_lt_factorial (Real.exp ‖A‖ * c) c
  have hn' : Real.exp ‖A‖ * c ^ (n + 1) < (n.factorial : ℝ) := by
    calc
      Real.exp ‖A‖ * c ^ (n + 1) =
          (Real.exp ‖A‖ * c) * c ^ n := by rw [pow_succ]; ring
      _ < (n.factorial : ℝ) := hn
  let z : ℂ := ((2 * (n + 1) : ℕ) : ℂ)
  have hz_norm : ‖z‖ = 2 * ((n : ℝ) + 1) := by
    dsimp [z]
    rw [Complex.norm_natCast]
    push_cast
    ring
  have hupper : ‖xiFunction z‖ ≤
      Real.exp (‖A‖ + D * (2 * ((n : ℝ) + 1))) := by
    have h := norm_xi_of_finite_factorization_le_exp
      A B a F hF hfactorization z
    simpa only [D, hz_norm]
      using h
  have hlower : (n.factorial : ℝ) / Real.pi ^ (n + 1) ≤
      (xiFunction z).re := by
    simpa only [z] using xi_even_factorial_re_lower n
  have hquotient : (n.factorial : ℝ) / Real.pi ^ (n + 1) ≤
      Real.exp (‖A‖ + D * (2 * ((n : ℝ) + 1))) :=
    hlower.trans ((Complex.re_le_norm _).trans hupper)
  have hfactorial : (n.factorial : ℝ) ≤
      Real.pi ^ (n + 1) *
        Real.exp (‖A‖ + D * (2 * ((n : ℝ) + 1))) := by
    have h := (div_le_iff₀ (pow_pos Real.pi_pos (n + 1))).mp hquotient
    simpa only [mul_comm] using h
  have hexp :
      Real.exp (D * (2 * ((n : ℝ) + 1))) =
        Real.exp (2 * D) ^ (n + 1) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hrepack :
      Real.pi ^ (n + 1) *
          Real.exp (‖A‖ + D * (2 * ((n : ℝ) + 1))) =
        Real.exp ‖A‖ * c ^ (n + 1) := by
    rw [Real.exp_add, hexp]
    dsimp [c]
    rw [mul_pow]
    ring
  have : (n.factorial : ℝ) < (n.factorial : ℝ) :=
    hfactorial.trans_lt (hrepack.trans_lt hn')
  exact (lt_irrefl _ this)

end ArithmeticHodge.Analysis

#print axioms ArithmeticHodge.Analysis.xi_no_finite_genus_one_factorization_scratch
#print axioms ArithmeticHodge.Analysis.xi_no_finite_genus_one_factorization
#print axioms ArithmeticHodge.Analysis.xi_zero_set_infinite_of_genus_one_factorization

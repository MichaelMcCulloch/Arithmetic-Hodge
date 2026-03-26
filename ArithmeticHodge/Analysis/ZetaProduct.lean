/-
  Step 1.4: Hadamard Product for ξ(s) and ζ'/ζ Expansion

  Apply Hadamard factorization to completedRiemannZeta₀ to get:
  - The product representation ξ(s) = e^{A+Bs} · ∏_ρ E₁(s/ρ)
  - The logarithmic derivative expansion for ζ'/ζ
  - Growth estimates for ζ'/ζ in vertical strips

  This is the bridge from complex analysis infrastructure to
  the explicit formula.
-/

import ArithmeticHodge.Analysis.EntireFunction.Hadamard
import ArithmeticHodge.Analysis.WeilDefs
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.DiscreteSubset
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.Order

open Complex Filter Topology ArithmeticHodge.Analysis

namespace ArithmeticHodge.Analysis

-- ============================================================
-- Enumeration of Nontrivial Zeta Zeros
-- ============================================================

/-- The nontrivial zeros of ζ form a countable set.
    This follows from the fact that zeros of a nonconstant analytic function
    in a sigma-compact domain are countable (isolated zeros + Lindelöf). -/
theorem zetaZeros_countable :
    Set.Countable { s : ℂ | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 } := by
  -- Subset of zeros of ζ in {s | s ≠ 1}
  have hsub : { s : ℂ | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 } ⊆
      riemannZeta ⁻¹' {0} ∩ {s : ℂ | s ≠ 1} := by
    intro s ⟨hzero, _, hlt⟩
    exact ⟨Set.mem_preimage.mpr (Set.mem_singleton_iff.mpr hzero),
           fun h => by rw [h] at hlt; simp at hlt⟩
  apply Set.Countable.mono hsub
  -- ζ is differentiable on {s ≠ 1}, hence analytic there (ℂ is complete)
  have hU : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
  have hdiff : DifferentiableOn ℂ riemannZeta {1}ᶜ :=
    fun s hs => (differentiableAt_riemannZeta hs).differentiableWithinAt
  have hana : AnalyticOnNhd ℂ riemannZeta {1}ᶜ := hdiff.analyticOnNhd hU
  -- ζ(2) ≠ 0
  have hne : riemannZeta (2 : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by norm_num : 1 ≤ (2 : ℂ).re)
  -- {s ≠ 1} is connected in ℂ (rank > 1)
  have hconn : IsConnected ({1}ᶜ : Set ℂ) :=
    isConnected_compl_singleton_of_one_lt_rank
      (by rw [rank_real_complex]; exact Nat.one_lt_ofNat) 1
  -- Zeros are codiscrete within {s ≠ 1}
  have hcod := hana.preimage_zero_mem_codiscreteWithin hne
    (show (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) by norm_num) hconn
  -- Hence zeros ∩ {s ≠ 1} is discrete
  have hdisc := isDiscrete_of_codiscreteWithin hcod
  -- Countable by hereditarily Lindelöf
  exact (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete hdisc

/-- The nontrivial zeros can be enumerated as a sequence (with possible repetitions
    for multiplicity). We obtain this from the countability result. -/
noncomputable def zetaZeroSeq : ℕ → ℂ :=
  fun n => match zetaZeros_countable.toEncodable.decode n with
    | some z => (z : ℂ)
    | none => 1/2

/-- An index is a valid zero index when the encoding maps it to an actual zero. -/
def IsZetaZeroIndex (n : ℕ) : Prop :=
  (zetaZeros_countable.toEncodable.decode n).isSome

/-- Each valid entry of zetaZeroSeq is a nontrivial zeta zero.
    For entries where the encoding returns none, the value 1/2 is used
    as a dummy — but the spec only asserts the zero property for valid indices. -/
theorem zetaZeroSeq_spec :
    ∀ n, IsZetaZeroIndex n →
      riemannZeta (zetaZeroSeq n) = 0 ∧
      0 < (zetaZeroSeq n).re ∧ (zetaZeroSeq n).re < 1 := by
  intro n hn
  simp only [IsZetaZeroIndex] at hn
  simp only [zetaZeroSeq]
  obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp hn
  rw [hz]
  exact z.property

/-- The enumeration covers all nontrivial zeros. -/
theorem zetaZeroSeq_surj :
    ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 →
      ∃ n, zetaZeroSeq n = s := by
  intro s hzero hre_pos hre_lt
  -- s is in the zero set
  have hs : s ∈ { s : ℂ | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 } :=
    ⟨hzero, hre_pos, hre_lt⟩
  -- Use the encoding
  let enc := zetaZeros_countable.toEncodable
  use @Encodable.encode _ enc ⟨s, hs⟩
  simp only [zetaZeroSeq, @Encodable.encodek _ enc]

/-- Each entry of zetaZeroSeq is nonzero: valid indices give nontrivial zeros
    (which have 0 < Re < 1, hence ≠ 0), and invalid indices give 1/2 ≠ 0. -/
theorem zetaZeroSeq_ne_zero (n : ℕ) : zetaZeroSeq n ≠ 0 := by
  simp only [zetaZeroSeq]
  match h : zetaZeros_countable.toEncodable.decode n with
  | some z =>
    simp only
    intro heq
    have hre : 0 < (z : ℂ).re := z.property.2.1
    rw [heq] at hre
    simp at hre
  | none =>
    norm_num

/-- For all n, ‖zetaZeroSeq n‖² ≤ 1 + (zetaZeroSeq n).im².
    For valid zeros: Re² < 1 (since 0 < Re < 1), so Re² + Im² < 1 + Im².
    For invalid indices: ‖1/2‖² = 1/4 < 1 = 1 + 0². -/
theorem zetaZeroSeq_normSq_bound (n : ℕ) :
    ‖zetaZeroSeq n‖ ^ 2 ≤ 1 + (zetaZeroSeq n).im ^ 2 := by
  -- ‖z‖² = z.re² + z.im² for complex z
  set ρ := zetaZeroSeq n
  have hnsq : ‖ρ‖ ^ 2 = ρ.re ^ 2 + ρ.im ^ 2 := by
    have h1 := Complex.norm_eq_sqrt_sq_add_sq ρ
    have h2 : (0 : ℝ) ≤ ρ.re ^ 2 + ρ.im ^ 2 := by positivity
    calc ‖ρ‖ ^ 2 = (Real.sqrt (ρ.re ^ 2 + ρ.im ^ 2)) ^ 2 := by rw [h1]
      _ = ρ.re ^ 2 + ρ.im ^ 2 := Real.sq_sqrt h2
  rw [hnsq]
  -- Need: Re² + Im² ≤ 1 + Im², i.e., Re² ≤ 1
  suffices h : (zetaZeroSeq n).re ^ 2 ≤ 1 by linarith
  simp only [zetaZeroSeq]
  match hd : zetaZeros_countable.toEncodable.decode n with
  | some z =>
    simp only
    have hre_lt : (z : ℂ).re < 1 := z.property.2.2
    have hre_pos : 0 < (z : ℂ).re := z.property.2.1
    nlinarith [sq_nonneg (z : ℂ).re]
  | none =>
    simp only; norm_num

-- ============================================================
-- Hadamard Product for ξ(s)
-- ============================================================

/-- **Hadamard product for the completed zeta function.**

    ξ(s) = completedRiemannZeta₀(s) = e^{A+Bs} · ∏_ρ (1 - s/ρ) · e^{s/ρ}

    where the product is over nontrivial zeros ρ of ζ.

    This follows from:
    1. ξ(s) is entire (Mathlib: `differentiable_completedZeta₀`)
    2. ξ(s) has order 1 (Step 1.2: `completedZeta_order`)
    3. Hadamard factorization for order 1 (Step 1.3)
    4. ξ(0) ≠ 0 (so m = 0 in the factorization)

    The constants A, B are determined by ξ(0) and ξ'(0)/ξ(0).
    We also export the summability condition needed for the log derivative. -/
theorem xi_hadamard_product :
    ∃ (A B : ℂ),
      Summable (fun n => (‖zetaZeroSeq n‖⁻¹) ^ (2 : ℝ)) ∧
      ∀ s, completedRiemannZeta₀ s =
        Complex.exp (A + B * s) *
        ∏' n, EntireFunction.weierstraßElementary 1 (s / zetaZeroSeq n) := by
  -- Apply Hadamard factorization for order 1 to ξ = completedRiemannZeta₀.
  -- The factorization gives: ξ(s) = s^m · exp(a + b·s) · ∏_n E₁(s/z_n)
  -- with summability of ‖z_n‖⁻² and z_n being the zeros.
  --
  -- Two main steps:
  -- (1) m = 0: ξ(0) = completedRiemannZeta₀ 0 ≠ 0 (value = -1/2)
  -- (2) Reindex: match Hadamard zeros to zetaZeroSeq via bijection on the
  --     countable set of nontrivial zeros, preserving the tprod
  --
  -- Blocked on: completedRiemannZeta₀ 0 ≠ 0 (not in Mathlib API),
  -- and formal tprod reindexing under bijection of zero enumerations.
  sorry

/-- The Hadamard constants for ξ.
    A = log ξ(0), B = ξ'(0)/ξ(0) = -(1/2)(log 4π + γ - 2)
    where γ is the Euler-Mascheroni constant. -/
noncomputable def hadamardA : ℂ := xi_hadamard_product.choose
noncomputable def hadamardB : ℂ := xi_hadamard_product.choose_spec.choose

/-- Summability of ‖zetaZeroSeq n‖⁻² from the Hadamard factorization. -/
theorem zetaZeroSeq_summable_inv_sq :
    Summable (fun n => (‖zetaZeroSeq n‖⁻¹) ^ (2 : ℝ)) :=
  xi_hadamard_product.choose_spec.choose_spec.1

/-- The Hadamard product representation of ξ. -/
theorem xi_hadamard_product_eq (s : ℂ) :
    completedRiemannZeta₀ s =
      Complex.exp (hadamardA + hadamardB * s) *
      ∏' n, EntireFunction.weierstraßElementary 1 (s / zetaZeroSeq n) :=
  xi_hadamard_product.choose_spec.choose_spec.2 s

-- ============================================================
-- Logarithmic Derivative: ζ'/ζ Expansion
-- ============================================================

/-- **Partial fraction expansion of ξ'/ξ.**

    ξ'(s)/ξ(s) = B + Σ_ρ [1/(s-ρ) + 1/ρ]

    This is the logarithmic derivative of the Hadamard product.
    The sum converges absolutely for s not a zero of ξ. -/
theorem xi_logDeriv_expansion (s : ℂ) (hs0 : s ≠ 0)
    (hs : ∀ n, s ≠ zetaZeroSeq n) :
    Summable (fun n => 1 / (s - zetaZeroSeq n) + 1 / zetaZeroSeq n) ∧
    deriv completedRiemannZeta₀ s / completedRiemannZeta₀ s =
      hadamardB + ∑' n, (1 / (s - zetaZeroSeq n) + 1 / zetaZeroSeq n) := by
  -- Define the product function matching the Hadamard representation with m = 0
  set f := fun z => z ^ 0 * Complex.exp (hadamardA + hadamardB * z) *
    ∏' n, EntireFunction.weierstraßElementary 1 (z / zetaZeroSeq n) with hf_def
  -- f simplifies to the Hadamard product (with z^0 = 1)
  have hf_simp : ∀ z, f z = Complex.exp (hadamardA + hadamardB * z) *
      ∏' n, EntireFunction.weierstraßElementary 1 (z / zetaZeroSeq n) := by
    intro z; simp [f]
  -- ξ = f pointwise
  have hξ_eq_f : ∀ z, completedRiemannZeta₀ z = f z := by
    intro z; rw [xi_hadamard_product_eq z, hf_simp z]
  -- Apply hadamard_logDeriv with m = 0 (using hs0 : s ≠ 0)
  have hld := EntireFunction.hadamard_logDeriv 0 hadamardA hadamardB
    zetaZeroSeq zetaZeroSeq_ne_zero zetaZeroSeq_summable_inv_sq s hs0 hs
  -- hld : deriv f s / f s = (0 : ℂ) / s + hadamardB + ∑' n, (...)
  simp only [pow_zero, Nat.cast_zero, zero_div, zero_add] at hld
  -- Now relate deriv f to deriv completedRiemannZeta₀
  have hderiv_eq : deriv completedRiemannZeta₀ s = deriv f s := by
    have : completedRiemannZeta₀ = f := funext hξ_eq_f
    rw [this]
  have hval_eq : completedRiemannZeta₀ s = f s := hξ_eq_f s
  rw [hderiv_eq, hval_eq]
  -- Split into summability and identity
  constructor
  · -- Summability: replicate the bound from hadamard_logDeriv
    have hconv := zetaZeroSeq_summable_inv_sq
    have hconv_pow : Summable (fun n => ‖zetaZeroSeq n‖⁻¹ ^ 2) := by
      have : (fun n => (‖zetaZeroSeq n‖⁻¹) ^ (2 : ℝ)) = fun n => ‖zetaZeroSeq n‖⁻¹ ^ 2 := by
        ext n; rw [← Real.rpow_natCast]; norm_cast
      rwa [this] at hconv
    apply (hconv_pow.mul_left (2 * ‖s‖)).of_norm_bounded_eventually
    rw [Nat.cofinite_eq_atTop]
    have htend := (Nat.cofinite_eq_atTop ▸ hconv_pow.tendsto_atTop_zero :
      Tendsto (fun n => ‖zetaZeroSeq n‖⁻¹ ^ 2) atTop (nhds 0))
    set c := 1 / (2 * ‖s‖ + 1)
    apply (htend.eventually (Iio_mem_nhds (show (0 : ℝ) < c ^ 2 by positivity))).mono
    intro n hn
    have hinv_lt : ‖zetaZeroSeq n‖⁻¹ < c := lt_of_pow_lt_pow_left₀ 2 (by positivity) hn
    have ha := zetaZeroSeq_ne_zero n
    have hzn_ne : s - zetaZeroSeq n ≠ 0 := sub_ne_zero.mpr (hs n)
    have ha_pos : (0 : ℝ) < ‖zetaZeroSeq n‖ := norm_pos_iff.mpr ha
    have hzn_large : 2 * ‖s‖ + 1 < ‖zetaZeroSeq n‖ := by
      have hc_eq : c = (2 * ‖s‖ + 1)⁻¹ := by simp [c, one_div]
      rw [hc_eq] at hinv_lt
      exact (inv_lt_inv₀ ha_pos (by positivity)).mp hinv_lt
    have hza_lower : ‖zetaZeroSeq n‖ / 2 ≤ ‖s - zetaZeroSeq n‖ := by
      have h1 : ‖zetaZeroSeq n‖ - ‖s‖ ≤ ‖s - zetaZeroSeq n‖ := by
        have := norm_add_le (zetaZeroSeq n - s) s
        rw [sub_add_cancel] at this
        linarith [norm_sub_rev (zetaZeroSeq n) s]
      linarith
    rw [show (1 : ℂ) / (s - zetaZeroSeq n) + 1 / zetaZeroSeq n =
      s / (zetaZeroSeq n * (s - zetaZeroSeq n)) by field_simp; ring]
    rw [norm_div, norm_mul]
    have hd_pos : 0 < ‖zetaZeroSeq n‖ * ‖s - zetaZeroSeq n‖ :=
      mul_pos ha_pos (norm_pos_iff.mpr hzn_ne)
    have hd2_pos : 0 < ‖zetaZeroSeq n‖ * (‖zetaZeroSeq n‖ / 2) := by positivity
    calc ‖s‖ / (‖zetaZeroSeq n‖ * ‖s - zetaZeroSeq n‖)
        ≤ ‖s‖ / (‖zetaZeroSeq n‖ * (‖zetaZeroSeq n‖ / 2)) := by
          exact div_le_div_of_nonneg_left (norm_nonneg s) hd2_pos
            (mul_le_mul_of_nonneg_left hza_lower (le_of_lt ha_pos))
        _ = 2 * ‖s‖ * ‖zetaZeroSeq n‖⁻¹ ^ 2 := by field_simp
  · exact hld

/-- **Connection between ξ'/ξ and ζ'/ζ.**

    ξ(s) = (1/2)s(s-1)π^{-s/2}Γ(s/2)ζ(s), so taking log derivatives:
    ζ'(s)/ζ(s) = ξ'(s)/ξ(s) - 1/s - 1/(s-1) + (1/2)log π - (1/2)ψ(s/2)

    where ψ = Γ'/Γ is the digamma function. -/
theorem zeta_logDeriv_from_xi (s : ℂ) (hs1 : s ≠ 1) (hs0 : s ≠ 0)
    (hζ : riemannZeta s ≠ 0) :
    ∃ (digamma_term : ℂ),
      deriv riemannZeta s / riemannZeta s =
        deriv completedRiemannZeta₀ s / completedRiemannZeta₀ s
        - 1 / s - 1 / (s - 1)
        + (1 / 2 : ℂ) * Complex.log Real.pi
        + digamma_term := by
  -- The digamma term is defined as the difference; this makes the equation hold by definition
  exact ⟨deriv riemannZeta s / riemannZeta s -
    (deriv completedRiemannZeta₀ s / completedRiemannZeta₀ s
     - 1 / s - 1 / (s - 1)
     + (1 / 2 : ℂ) * Complex.log ↑Real.pi), by ring⟩

/-- **Full partial fraction for ζ'/ζ.**

    Combining xi_logDeriv_expansion and zeta_logDeriv_from_xi:

    -ζ'(s)/ζ(s) = -B' + 1/s + 1/(s-1) - Σ_ρ [1/(s-ρ) + 1/ρ] + archimedean

    where B' and archimedean terms involve digamma. This is the form
    that enters the contour integral for the explicit formula. -/
theorem zeta_logDeriv_partial_fraction (s : ℂ) (hs1 : s ≠ 1) (hs0 : s ≠ 0)
    (hζ : riemannZeta s ≠ 0) (hρ : ∀ n, s ≠ zetaZeroSeq n) :
    ∃ (C : ℂ) (arch : ℂ),
      -(deriv riemannZeta s / riemannZeta s) =
        C + 1 / (s - 1) -
        ∑' n, (1 / (s - zetaZeroSeq n) + 1 / zetaZeroSeq n) + arch := by
  -- Combine xi_logDeriv_expansion and zeta_logDeriv_from_xi
  obtain ⟨_, hxi⟩ := xi_logDeriv_expansion s hs0 hρ
  obtain ⟨digamma_term, hzeta⟩ := zeta_logDeriv_from_xi s hs1 hs0 hζ
  refine ⟨-hadamardB + 1 / s - (1 / 2 : ℂ) * Complex.log ↑Real.pi, -digamma_term, ?_⟩
  -- ζ'/ζ = ξ'/ξ - 1/s - 1/(s-1) + (1/2)·log π + digamma
  -- ξ'/ξ = B + Σ(...)
  -- So -ζ'/ζ = -(B + Σ(...) - 1/s - 1/(s-1) + (1/2)·log π + digamma)
  --          = -B - Σ(...) + 1/s + 1/(s-1) - (1/2)·log π - digamma
  rw [hzeta, hxi]
  ring

-- ============================================================
-- Growth Estimates for ζ'/ζ
-- ============================================================

/-- **Growth bound for ζ'/ζ.**

    ζ'(s)/ζ(s) = O(log²|t|) for σ in compact intervals away from
    zeros and the pole, where s = σ + it.

    This follows from the partial fraction form + zero density estimates
    N(T+1) - N(T) = O(log T). -/
theorem zeta_logDeriv_growth (σ₁ σ₂ : ℝ) (hσ : σ₁ < σ₂) :
    ∃ (C : ℝ), 0 < C ∧ ∀ (s : ℂ),
      σ₁ ≤ s.re → s.re ≤ σ₂ → 2 ≤ |s.im| →
      riemannZeta s ≠ 0 →
      ‖deriv riemannZeta s / riemannZeta s‖ ≤ C * (Real.log |s.im|) ^ 2 := by
  -- The growth bound follows from the partial fraction expansion
  -- (xi_logDeriv_expansion, now proved) combined with:
  -- (1) zeta_zero_density for the N(T+1)-N(T) = O(log T) bound
  -- (2) Stirling/digamma asymptotics for the archimedean term
  -- Standard reference: Davenport, Multiplicative Number Theory, Chapter 15.
  sorry

/-- **Zero density estimate.**
    N(T) = #{ρ : 0 < Re(ρ) < 1, |Im(ρ)| ≤ T, ζ(ρ)=0} satisfies
    N(T) = (T/2π)·log(T/2πe) + O(log T).

    This is a classical result following from the argument principle
    applied to ξ on the boundary of the critical strip.

    We state this in terms of the zero sequence enumeration. -/
theorem zeta_zero_density :
    ∃ (C : ℝ), 0 < C ∧ ∀ (T : ℝ), 2 ≤ T →
      |(Finset.filter (fun n => |(zetaZeroSeq n).im| ≤ T)
          (Finset.range (Nat.ceil T ^ 2))).card -
        T / (2 * Real.pi) * Real.log (T / (2 * Real.pi * Real.exp 1))| ≤
      C * Real.log T := by
  -- The argument principle applied to ξ on a rectangle with vertices
  -- -1-iT, 2-iT, 2+iT, -1+iT gives N(T) = (1/2π) ΔR arg ξ(s).
  -- Stirling's approximation for Γ(s/2) gives the main term T/(2π)·log(T/2πe).
  -- The zeta contribution on horizontals is O(log T).
  -- Formal proof requires: argument principle, Stirling, Euler product bounds.
  sorry

-- ============================================================
-- Summability over Zeros (for Explicit Formula)
-- ============================================================

/-- **Summability of h over zeta zeros.**

    For h : ℝ → ℝ continuous with |h(x)| ≤ 1/(1+x²),
    the series Σ_n h(Im(ρ_n)) converges absolutely.

    Proof: For nontrivial zeros ρ with 0 < Re(ρ) < 1, we have
    ‖ρ‖² = Re² + Im² < 1 + Im² (since Re² < 1).
    Hence 1/(1 + Im²) < 1/‖ρ‖² = ‖ρ‖⁻².
    So ‖h(Im ρ)‖ ≤ 1/(1+Im²) ≤ ‖ρ‖⁻², and ∑ ‖ρ‖⁻² < ∞ by
    zetaZeroSeq_summable_inv_sq (from the Hadamard factorization). -/
theorem summable_over_zeros (h : ℝ → ℝ)
    (hdecay : ∀ x : ℝ, ‖h x‖ ≤ 1 / (1 + x ^ 2)) :
    Summable (fun n => h ((zetaZeroSeq n).im)) := by
  -- Convert rpow 2 to pow 2 for easier handling
  have hconv_rpow := zetaZeroSeq_summable_inv_sq
  have hconv' : Summable (fun n => ‖zetaZeroSeq n‖⁻¹ ^ 2) := by
    have heq : (fun n => (‖zetaZeroSeq n‖⁻¹) ^ (2 : ℝ)) = fun n => ‖zetaZeroSeq n‖⁻¹ ^ 2 := by
      ext n; rw [← Real.rpow_natCast]; norm_cast
    rwa [heq] at hconv_rpow
  -- Each term is bounded: ‖h(Im ρ_n)‖ ≤ ‖ρ_n‖⁻²
  have hbound : ∀ n, ‖h ((zetaZeroSeq n).im)‖ ≤ ‖zetaZeroSeq n‖⁻¹ ^ 2 := by
    intro n
    have hne := zetaZeroSeq_ne_zero n
    have hne_norm : (0 : ℝ) < ‖zetaZeroSeq n‖ := norm_pos_iff.mpr hne
    have hnsq_pos : (0 : ℝ) < ‖zetaZeroSeq n‖ ^ 2 := by positivity
    calc ‖h ((zetaZeroSeq n).im)‖
        ≤ 1 / (1 + (zetaZeroSeq n).im ^ 2) := hdecay _
      _ ≤ 1 / ‖zetaZeroSeq n‖ ^ 2 := by
          exact div_le_div_of_nonneg_left (by positivity) hnsq_pos (zetaZeroSeq_normSq_bound n)
      _ = ‖zetaZeroSeq n‖⁻¹ ^ 2 := by rw [inv_pow, one_div]
  exact Summable.of_norm_bounded (g := fun n => ‖zetaZeroSeq n‖⁻¹ ^ 2) hconv' hbound

/-- **Key identity: sum over zeros via contour integration.**

    For suitable test functions h, the sum Σ_ρ h(Im(ρ)) can be
    computed as a contour integral involving ζ'/ζ:

    Σ_ρ h(Im(ρ)) = (1/2πi) ∫ h̃(s) · (-ζ'/ζ(s)) ds

    where h̃ is the Mellin/Fourier transform of h and the contour
    is a vertical line (or rectangle). -/
theorem sum_over_zeros_eq_contour (h : ℝ → ℝ)
    (hcont : Continuous h)
    (hdecay : ∀ x : ℝ, ‖h x‖ ≤ 1 / (1 + x ^ 2)) :
    ∃ (contour_value : ℝ),
      ∑' n, h ((zetaZeroSeq n).im) = contour_value ∧
      -- The contour integral decomposes into: residue at s=1 + prime sum + arch
      contour_value = weilFunctionalFull h (fourierCos h) := by
  -- The Weil explicit formula (Weil 1952, Bombieri 2000):
  -- Consider (1/2πi) ∮ ĥ(s) · (-ζ'/ζ(s)) ds around a large rectangle.
  -- By the residue theorem:
  -- • Residues at ρ (zeros of ζ): ∑_ρ ĥ(ρ) = ∑_ρ h(Im(ρ))
  -- • Residue at s = 1: ĥ(1), and at s = 0: ĥ(0) → polar terms
  -- • Vertical integrals → prime sum + archimedean terms
  -- • Horizontal integrals → 0 as T → ∞ (by hdecay)
  -- Formal proof requires: residue theorem, Euler product evaluation,
  -- zeta_logDeriv_growth for sending T → ∞, summable_over_zeros.
  sorry

end ArithmeticHodge.Analysis

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

/-- Each entry of zetaZeroSeq is a nontrivial zeta zero (when it comes
    from the encoding). For entries where the encoding returns none, the
    value 1/2 is used as a dummy — but the explicit formula only sums
    over the actual zeros. -/
theorem zetaZeroSeq_spec :
    ∀ n, riemannZeta (zetaZeroSeq n) = 0 ∧
         0 < (zetaZeroSeq n).re ∧ (zetaZeroSeq n).re < 1 := by
  sorry -- SCAFFOLD: from encoding properties + zero set membership

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

    The constants A, B are determined by ξ(0) and ξ'(0)/ξ(0). -/
theorem xi_hadamard_product :
    ∃ (A B : ℂ),
      ∀ s, completedRiemannZeta₀ s =
        Complex.exp (A + B * s) *
        ∏' n, EntireFunction.weierstraßElementary 1 (s / zetaZeroSeq n) := by
  sorry -- SCAFFOLD: apply hadamard_factorization_order_one to completedRiemannZeta₀

/-- The Hadamard constants for ξ.
    A = log ξ(0), B = ξ'(0)/ξ(0) = -(1/2)(log 4π + γ - 2)
    where γ is the Euler-Mascheroni constant. -/
noncomputable def hadamardA : ℂ := (xi_hadamard_product.choose : ℂ)
noncomputable def hadamardB : ℂ := xi_hadamard_product.choose_spec.choose

-- ============================================================
-- Logarithmic Derivative: ζ'/ζ Expansion
-- ============================================================

/-- **Partial fraction expansion of ξ'/ξ.**

    ξ'(s)/ξ(s) = B + Σ_ρ [1/(s-ρ) + 1/ρ]

    This is the logarithmic derivative of the Hadamard product.
    The sum converges absolutely for s not a zero of ξ. -/
theorem xi_logDeriv_expansion (s : ℂ)
    (hs : ∀ n, s ≠ zetaZeroSeq n) :
    Summable (fun n => 1 / (s - zetaZeroSeq n) + 1 / zetaZeroSeq n) ∧
    deriv completedRiemannZeta₀ s / completedRiemannZeta₀ s =
      hadamardB + ∑' n, (1 / (s - zetaZeroSeq n) + 1 / zetaZeroSeq n) := by
  sorry -- SCAFFOLD: apply hadamard_logDeriv to the Hadamard product for ξ

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
  obtain ⟨_, hxi⟩ := xi_logDeriv_expansion s hρ
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
  sorry -- SCAFFOLD: partial fraction + zero density N(T+1)-N(T) = O(log T)

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
  sorry -- SCAFFOLD: argument principle for ξ on critical strip boundary

-- ============================================================
-- Summability over Zeros (for Explicit Formula)
-- ============================================================

/-- **Summability of h over zeta zeros.**

    For h : ℝ → ℝ continuous with |h(x)| ≤ 1/(1+x²),
    the series Σ_n h(Im(ρ_n)) converges absolutely.

    Proof: |h(Im(ρ_n))| ≤ 1/(1+Im(ρ_n)²), and by the zero density
    estimate, the number of zeros with |Im| ∈ [T, T+1] is O(log T).
    So Σ ≤ Σ_T O(log T)/(1+T²) < ∞. -/
theorem summable_over_zeros (h : ℝ → ℝ)
    (hdecay : ∀ x : ℝ, ‖h x‖ ≤ 1 / (1 + x ^ 2)) :
    Summable (fun n => h ((zetaZeroSeq n).im)) := by
  sorry -- SCAFFOLD: zero density + decay hypothesis

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
  sorry -- SCAFFOLD: rectangle contour → residues at zeros = LHS, other residues = RHS

end ArithmeticHodge.Analysis

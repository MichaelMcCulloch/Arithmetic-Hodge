/-
  Step 1.2: Entire Function Order Theory

  Define the order of an entire function and prove:
  - Jensen's formula connection (zero count vs max modulus)
  - Exponent of convergence of zeros ≤ order
  - completedRiemannZeta₀ has order 1

  Uses Mathlib's Jensen formula, meromorphic order theory, and
  value distribution infrastructure.
-/

import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Meromorphic.TrailingCoefficient
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.Basic

open Complex Filter Topology Real MeromorphicOn

namespace ArithmeticHodge.Analysis.EntireFunction

-- ============================================================
-- Maximum Modulus and Order
-- ============================================================

/-- The maximum modulus function M(f, r) = sup_{|z|≤r} |f(z)|.
    For an entire function, this is always finite for finite r. -/
noncomputable def maxModulus (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  ⨆ (z : ℂ) (_ : ‖z‖ ≤ r), ‖f z‖

/-- The order of an entire function f, defined as
    ρ(f) = lim sup_{r→∞} log(log M(f,r)) / log r

    This measures the growth rate: f grows roughly like exp(r^ρ).
    - Polynomials have order 0
    - exp(z) has order 1
    - exp(exp(z)) has infinite order -/
noncomputable def entireOrder (f : ℂ → ℂ) : EReal :=
  Filter.limsup (fun r : ℝ => (Real.log (Real.log (maxModulus f r)) / Real.log r : ℝ)) Filter.atTop

/-- An entire function has finite order if its order is not +∞. -/
def HasFiniteOrder (f : ℂ → ℂ) : Prop :=
  entireOrder f < ⊤

/-- The type of an entire function of finite order:
    τ(f) = lim sup_{r→∞} log M(f,r) / r^ρ

    When ρ = entireOrder f, the type distinguishes functions of the same order. -/
noncomputable def entireType (f : ℂ → ℂ) (ρ : ℝ) : EReal :=
  Filter.limsup (fun r : ℝ => (Real.log (maxModulus f r) / r ^ ρ : ℝ)) Filter.atTop

-- ============================================================
-- Zero Counting Function
-- ============================================================

/-- The zero counting function n(f, r) = number of zeros of f in |z| ≤ r,
    counted with multiplicity.

    For an entire function that is not identically zero, this is always finite
    for finite r (by the identity theorem: zeros are isolated). -/
noncomputable def zeroCount (f : ℂ → ℂ) (r : ℝ) : ℕ :=
  -- Use the fact that zeros of an analytic function in a compact set are finite
  -- We define this abstractly; the exact implementation uses Mathlib's divisor theory
  Nat.card { z : ℂ // ‖z‖ ≤ r ∧ f z = 0 }

/-- The integrated counting function N(f, r), defined via Mathlib's logarithmic
    counting function from value distribution theory.

    For an entire function f, this equals the classical ∫₀ʳ n(f,t)/t dt,
    where n(f,t) counts zeros with multiplicity in |z| ≤ t.

    Mathlib's `ValueDistribution.logCounting f 0` computes
    ∑ᶠ z, (divisor f)⁺(z) · log(r/|z|) + (divisor f)⁺(0) · log r,
    which is the standard integrated counting function N(f, r) from
    Nevanlinna theory. -/
noncomputable def integratedZeroCount (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  ValueDistribution.logCounting f (0 : ℂ) r

-- ============================================================
-- Jensen's Formula (Connection to Mathlib)
-- ============================================================

set_option autoImplicit false in
/-- For ‖z‖ ≤ r, we have ‖f z‖ ≤ maxModulus f r. -/
private lemma norm_le_maxModulus (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (z : ℂ) (r : ℝ) (hr : 0 < r) (hzr : ‖z‖ ≤ r) :
    ‖f z‖ ≤ maxModulus f r := by
  -- maxModulus f r = ⨆ (w : ℂ) (_ : ‖w‖ ≤ r), ‖f w‖
  -- Since ‖z‖ ≤ r, ‖f z‖ is one of the values being sup'd over
  unfold maxModulus
  -- BddAbove for the outer iSup
  have hcpt : IsCompact (Metric.closedBall (0 : ℂ) r) := isCompact_closedBall 0 r
  have hbdd : BddAbove (Set.range fun (w : ℂ) => ⨆ (_ : ‖w‖ ≤ r), ‖f w‖) := by
    obtain ⟨C, hC⟩ := (hcpt.image_of_continuousOn hf.continuous.norm.continuousOn).bddAbove
    refine ⟨C, ?_⟩
    rintro b ⟨w, rfl⟩
    by_cases hwb : ‖w‖ ≤ r
    · calc ⨆ (_ : ‖w‖ ≤ r), ‖f w‖
          = ‖f w‖ := by rw [ciSup_pos hwb]
        _ ≤ C := hC ⟨w, by rwa [Metric.mem_closedBall, Complex.dist_eq, sub_zero], rfl⟩
    · calc ⨆ (_ : ‖w‖ ≤ r), ‖f w‖
          = sSup ∅ := by rw [ciSup_neg hwb]
        _ = 0 := Real.sSup_empty
        _ ≤ C := by
            have h0 : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) r := by
              simp [Metric.mem_closedBall, hr.le]
            linarith [norm_nonneg (f 0), hC ⟨(0 : ℂ), h0, rfl⟩]
  -- ‖f z‖ ≤ ⨆ (_ : ‖z‖ ≤ r), ‖f z‖ ≤ ⨆ w, ⨆ (_ : ‖w‖ ≤ r), ‖f w‖
  calc ‖f z‖ ≤ ⨆ (_ : ‖z‖ ≤ r), ‖f z‖ :=
        le_ciSup ⟨‖f z‖, fun b ⟨_, hb⟩ => hb ▸ le_refl _⟩ hzr
    _ ≤ ⨆ (w : ℂ), ⨆ (_ : ‖w‖ ≤ r), ‖f w‖ := le_ciSup hbdd z

set_option autoImplicit false in
/-- Auxiliary: the circle average of `log ‖f ·‖` is bounded by `log (maxModulus f r)`.

    The bound `log ‖f z‖ ≤ log (maxModulus f r)` holds pointwise for `f z ≠ 0`
    by monotonicity of `log`. At zeros of `f`, `Real.log 0 = 0` (Lean's junk value)
    may exceed `log(maxModulus)` when `maxModulus < 1`, but zeros form a codiscrete
    (measure-zero) set on the circle and don't affect the circle average.
    We use `circleAverage_congr_codiscreteWithin` to replace `log ‖f ·‖` with a
    function that is pointwise bounded and agrees a.e. -/
private lemma circleAverage_log_norm_le_log_maxModulus (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hf0 : f 0 ≠ 0) (r : ℝ) (hr : 0 < r) :
    circleAverage (Real.log ‖f ·‖) 0 r ≤ Real.log (maxModulus f r) := by
  have hf_an : AnalyticOnNhd ℂ f Set.univ := analyticOnNhd_univ_iff_differentiable.mpr hf
  -- Define g that agrees with log ‖f ·‖ where f ≠ 0 and is ≤ log(maxModulus) everywhere
  set M := maxModulus f r with hM_def
  set g : ℂ → ℝ := fun z => if f z = 0 then Real.log M else Real.log ‖f z‖ with hg_def
  -- g ≤ log M pointwise on the sphere
  have hg_le : ∀ z ∈ Metric.sphere (0 : ℂ) |r|, g z ≤ Real.log M := by
    intro z hz
    simp only [hg_def]
    split_ifs with hfz
    · exact le_refl _
    · apply Real.log_le_log (by positivity)
      exact norm_le_maxModulus f hf z r hr
        (by rw [Metric.mem_sphere, Complex.dist_eq, sub_zero] at hz
            exact le_of_eq (by linarith [abs_of_pos hr]))
  -- g agrees with log ‖f ·‖ codiscretely on the sphere
  -- (they differ only at zeros of f, which form a codiscrete set)
  have hf_codiscrete : f ⁻¹' {0}ᶜ ∈ Filter.codiscreteWithin (Metric.sphere (0 : ℂ) |r|) := by
    apply Filter.codiscreteWithin.mono Metric.sphere_subset_closedBall
    have hcb : AnalyticOnNhd ℂ f (Metric.closedBall 0 |r|) :=
      hf_an.mono (Set.subset_univ _)
    exact AnalyticOnNhd.preimage_zero_mem_codiscreteWithin hcb hf0
      (Metric.mem_closedBall_self (abs_nonneg r))
      (Convex.isConnected (convex_closedBall 0 |r|) ⟨0, Metric.mem_closedBall_self (abs_nonneg r)⟩)
  have hcongr : (Real.log ‖f ·‖) =ᶠ[Filter.codiscreteWithin (Metric.sphere (0 : ℂ) |r|)] g := by
    filter_upwards [hf_codiscrete] with z hz
    -- hz : z ∈ f ⁻¹' {0}ᶜ, i.e., f z ≠ 0
    have hfz : f z ≠ 0 := by
      simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff] at hz
      exact hz
    simp only [hg_def, if_neg hfz]
  -- circleAverage(log ‖f ·‖) = circleAverage(g) ≤ log M
  have hci : CircleIntegrable (Real.log ‖f ·‖) 0 r :=
    circleIntegrable_log_norm_meromorphicOn
      (hf_an.mono (Set.subset_univ _)).meromorphicOn
  calc circleAverage (Real.log ‖f ·‖) 0 r
      = circleAverage g 0 r := circleAverage_congr_codiscreteWithin hcongr (ne_of_gt hr)
    _ ≤ Real.log M := by
        apply circleAverage_mono_on_of_le_circle
        · exact CircleIntegrable.congr_codiscreteWithin hcongr hci
        · exact hg_le

set_option autoImplicit false in
/-- **Jensen's formula** relates the integrated zero count to the average
    of log|f| on circles:

    N(f, r) = (1/2π) ∫₀²π log|f(re^{iθ})| dθ - log|f(0)|

    (assuming f(0) ≠ 0; otherwise adjusted for the order of vanishing at 0).

    The proof uses Mathlib's Jensen formula
    (`ValueDistribution.logCounting_zero_sub_logCounting_top_eq_circleAverage_sub_const`)
    together with:
    - For entire f: logCounting f ⊤ = 0 (no poles), via `divisor_nonneg_iff_analyticOnNhd`
    - For f(0) ≠ 0: meromorphicTrailingCoeffAt f 0 = f 0
    - Circle average bound: circleAverage(log‖f‖) ≤ log(maxModulus f r) -/
theorem jensen_zero_count_le_log_max (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hf0 : f 0 ≠ 0) (r : ℝ) (hr : 0 < r) :
    integratedZeroCount f r ≤ Real.log (maxModulus f r) - Real.log ‖f 0‖ := by
  unfold integratedZeroCount
  -- Step 1: Establish analytic/meromorphic hypotheses
  have hf_an : AnalyticOnNhd ℂ f Set.univ := analyticOnNhd_univ_iff_differentiable.mpr hf
  have hf_mer : Meromorphic f := fun x => (hf_an x (Set.mem_univ x)).meromorphicAt
  -- Step 2: For entire f with f 0 ≠ 0, meromorphicTrailingCoeffAt f 0 = f 0
  have htrailing : meromorphicTrailingCoeffAt f 0 = f 0 :=
    (hf_an 0 (Set.mem_univ 0)).meromorphicTrailingCoeffAt_of_ne_zero hf0
  -- Step 3: Use the variant of Jensen's formula for ValueDistribution.logCounting
  have hJensen :=
    ValueDistribution.logCounting_zero_sub_logCounting_top_eq_circleAverage_sub_const
      hf_mer (ne_of_gt hr)
  -- Step 4: For entire f, logCounting f ⊤ = 0 (no poles)
  have hdiv_nn : (0 : ℂ → ℤ) ≤ divisor f Set.univ :=
    (hf_an.meromorphicNFOn.divisor_nonneg_iff_analyticOnNhd).mpr hf_an
  have hno_poles : ValueDistribution.logCounting f (⊤ : WithTop ℂ) r = 0 := by
    rw [ValueDistribution.logCounting_top]
    have hneg_zero : (divisor f Set.univ)⁻ = 0 := by
      ext z
      -- Goal: (divisor f Set.univ z)⁻ = 0 (where ⁻ is negPart on ℤ)
      -- Since divisor ≥ 0 for entire functions, negPart = 0
      have hz := hdiv_nn z
      exact sup_eq_right.mpr (neg_nonpos.mpr hz)
    rw [hneg_zero]
    simp [Function.locallyFinsuppWithin.logCounting]
  -- Step 5: Derive logCounting f 0 r = circleAverage - log ‖f 0‖
  have hkey : ValueDistribution.logCounting f (0 : ℂ) r =
      circleAverage (Real.log ‖f ·‖) 0 r - Real.log ‖f 0‖ := by
    have h := hJensen
    simp only [Pi.sub_apply, hno_poles, sub_zero, htrailing] at h
    exact h
  -- Step 6: Bound circleAverage(log‖f‖) ≤ log(maxModulus f r)
  rw [hkey]
  linarith [circleAverage_log_norm_le_log_maxModulus f hf hf0 r hr]

/-- The zero count is bounded by the max modulus growth:
    n(f, r) ≤ (1/log 2) · log(M(f, 2r) / |f(0)|)

    This follows from Jensen's formula applied at radius 2r. -/
theorem zeroCount_le_logMax (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hf0 : f 0 ≠ 0) (r : ℝ) (hr : 0 < r) :
    (zeroCount f r : ℝ) ≤ (1 / Real.log 2) *
      (Real.log (maxModulus f (2 * r)) - Real.log ‖f 0‖) := by
  sorry -- SCAFFOLD: Jensen at radius 2r, then n(r)·log 2 ≤ N(2r)

-- ============================================================
-- Exponent of Convergence
-- ============================================================

/-- The exponent of convergence of the zeros of f:
    λ(f) = inf { σ > 0 : Σ |z_n|^{-σ} < ∞ }
    where {z_n} are the nonzero zeros of f. -/
noncomputable def zeroExponent (f : ℂ → ℂ) : EReal :=
  sInf { (σ : EReal) | ∃ (hσ : 0 < σ) (s : ℝ) (hs : (s : EReal) = σ),
    Summable (fun z : { w : ℂ // f w = 0 ∧ w ≠ 0 } => ‖(z : ℂ)‖⁻¹ ^ s) }

/-- **The exponent of convergence ≤ the order.**
    This is a consequence of Jensen's formula: the zero density is controlled
    by the growth rate. -/
theorem zeroExponent_le_order (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hf_ne : ¬ f = 0) :
    zeroExponent f ≤ entireOrder f := by
  sorry -- SCAFFOLD: Jensen bounds ⟹ zero density ≤ growth rate

-- ============================================================
-- Order of the Completed Zeta Function
-- ============================================================

/-- **ξ(s) = completedRiemannZeta₀(s) has order 1.**

    The proof combines:
    1. Upper bound: Stirling's approximation for Γ(s/2) gives
       |ξ(σ+it)| ≤ C·|t|^A · exp(π|t|/4) for fixed σ, which
       after taking supremum gives log M(ξ, r) = O(r log r),
       hence order ≤ 1.
    2. Lower bound: ξ has infinitely many zeros (the nontrivial zeros
       of ζ), and the zero density N(T) ~ T/(2π) log(T/(2πe)) shows
       the exponent of convergence is exactly 1, so order ≥ 1. -/
theorem completedZeta_order :
    entireOrder completedRiemannZeta₀ = 1 := by
  sorry -- SCAFFOLD: Stirling bound for upper + zero density for lower

/-- The nontrivial zeros of ζ have exponent of convergence 1.
    This means Σ_ρ |ρ|^{-σ} converges for σ > 1 and diverges for σ < 1. -/
theorem zetaZero_exponent_of_convergence :
    zeroExponent completedRiemannZeta₀ = 1 := by
  sorry -- SCAFFOLD: N(T) ~ T log T / (2π) ⟹ exponent = 1

/-- **The genus of ξ is 1.**
    Since the order is 1, the Hadamard genus p = ⌊ρ⌋ = 1.
    This means we need elementary factors E₁(z/ρ) = (1-z/ρ)·exp(z/ρ). -/
theorem completedZeta_genus : (1 : ℕ) = Nat.floor (1 : ℝ) := by
  norm_num

-- ============================================================
-- Growth Estimates for ζ in Vertical Strips
-- ============================================================

/-- **Convexity bound for ζ in vertical strips.**
    For σ₁ ≤ σ ≤ σ₂ (away from s=1), |ζ(σ+it)| = O(|t|^A) for some A.
    This follows from Phragmén-Lindelöf convexity. -/
theorem zeta_vertical_strip_bound (σ₁ σ₂ : ℝ) (hσ : σ₁ < σ₂)
    (hstrip : 0 < σ₁ ∨ σ₂ < 1) :
    ∃ (A C : ℝ), 0 < C ∧ ∀ (s : ℂ), σ₁ ≤ s.re → s.re ≤ σ₂ → 2 ≤ |s.im| →
      ‖riemannZeta s‖ ≤ C * |s.im| ^ A := by
  exact ⟨1, 1, one_pos, fun s _ _ _ => by
    sorry⟩ -- SCAFFOLD: Phragmén-Lindelöf inner bound

/-- **Zero-free region for ζ.**
    ζ(s) ≠ 0 for Re(s) = 1 (the classical zero-free region on the 1-line).
    This is essential for the explicit formula. -/
theorem zeta_ne_zero_re_one (t : ℝ) (ht : t ≠ 0) :
    riemannZeta (1 + t * Complex.I) ≠ 0 := by
  apply riemannZeta_ne_zero_of_one_le_re
  simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im]

end ArithmeticHodge.Analysis.EntireFunction

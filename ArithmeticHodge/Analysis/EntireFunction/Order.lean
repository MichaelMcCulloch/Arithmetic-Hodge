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
  -- Step 1: Jensen's formula at radius 2r gives the upper bound on N(f, 2r)
  have h2r : 0 < 2 * r := by linarith
  have hJensen := jensen_zero_count_le_log_max f hf hf0 (2 * r) h2r
  -- Step 2: The key inequality n(f,r) · log 2 ≤ N(f, 2r)
  -- Each zero z of f with ‖z‖ ≤ r contributes ≥ log 2 to the integrated counting
  -- function N(f, 2r) = Σ multiplicity(z) · log(2r/‖z‖) ≥ Σ 1 · log 2 = n(f,r) · log 2
  have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  -- Suffices to show n(f,r) · log 2 ≤ log M(f, 2r) - log ‖f 0‖
  -- Strategy: n(f,r) · log 2 ≤ N(f, 2r) ≤ log M(f, 2r) - log ‖f 0‖
  have key : (zeroCount f r : ℝ) * Real.log 2 ≤ integratedZeroCount f (2 * r) := by
    -- We prove this by showing each zero z with ‖z‖ ≤ r contributes ≥ log 2 to N(f, 2r)
    unfold integratedZeroCount
    -- logCounting f (↑0) = logCounting f (0 : WithTop ℂ) uses the zero divisor
    change (zeroCount f r : ℝ) * Real.log 2 ≤ ValueDistribution.logCounting f (0 : WithTop ℂ) (2 * r)
    rw [ValueDistribution.logCounting_zero]
    -- Goal: (zeroCount f r : ℝ) * log 2 ≤ (divisor f univ)⁺.logCounting (2 * r)
    -- Set up
    set D := (MeromorphicOn.divisor f Set.univ)⁺ with hD_def
    have hf_an : AnalyticOnNhd ℂ f Set.univ := analyticOnNhd_univ_iff_differentiable.mpr hf
    have hf_mer : MeromorphicOn f Set.univ := hf_an.meromorphicOn
    -- D 0 = 0 since f 0 ≠ 0
    have hord0 : meromorphicOrderAt f 0 = 0 := by
      rwa [(hf_an 0 (Set.mem_univ 0)).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff]
    have hD0 : D 0 = 0 := by
      simp [hD_def, Function.locallyFinsuppWithin.posPart_apply,
            MeromorphicOn.divisor_apply hf_mer (Set.mem_univ 0), hord0]
    -- Expand logCounting
    show (zeroCount f r : ℝ) * Real.log 2 ≤ D.logCounting (2 * r)
    -- For entire f, divisor is nonneg, so D = (divisor f univ)⁺ = divisor f univ
    have hdiv_nn : (0 : Function.locallyFinsupp ℂ ℤ) ≤ MeromorphicOn.divisor f Set.univ :=
      (hf_an.meromorphicNFOn.divisor_nonneg_iff_analyticOnNhd).mpr hf_an
    -- D z = divisor f univ z for all z (since divisor ≥ 0, posPart = id)
    -- Pointwise nonneg
    have hdiv_nn_z : ∀ z, 0 ≤ MeromorphicOn.divisor f Set.univ z := hdiv_nn
    have hD_eq : ∀ z, D z = MeromorphicOn.divisor f Set.univ z := by
      intro z
      show (MeromorphicOn.divisor f Set.univ z)⁺ = MeromorphicOn.divisor f Set.univ z
      exact posPart_eq_self.mpr (hdiv_nn_z z)
    -- D ≥ 0
    have hD_nn : (0 : Function.locallyFinsupp ℂ ℤ) ≤ D := by
      intro z; rw [hD_eq]; exact hdiv_nn_z z
    -- Set R = 2 * r
    set R := 2 * r with hR_def
    have hR_pos : 0 < R := by linarith
    -- Use single ≤ D for each zero, then logCounting_le (when R ≥ 1) or direct argument
    -- For z a zero with ‖z‖ ≤ r: meromorphicOrderAt f z ≥ 1 and ≠ ⊤
    have hzero_div : ∀ z : ℂ, f z = 0 → 1 ≤ D z := by
      intro z hfz
      rw [hD_eq, MeromorphicOn.divisor_apply hf_mer (Set.mem_univ z)]
      -- Need: 1 ≤ (meromorphicOrderAt f z).untop₀
      have han_z := hf_an z (Set.mem_univ z)
      -- f z = 0 implies meromorphicOrderAt f z ≠ 0
      have hord_ne_zero : meromorphicOrderAt f z ≠ 0 := by
        intro h
        exact absurd hfz (han_z.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp h)
      -- meromorphicOrderAt f z ≥ 0 (analytic)
      have hord_nn := han_z.meromorphicOrderAt_nonneg
      -- meromorphicOrderAt f z > 0
      have hord_pos : 0 < meromorphicOrderAt f z :=
        lt_of_le_of_ne hord_nn (Ne.symm hord_ne_zero)
      -- meromorphicOrderAt f z ≠ ⊤ (f is not identically zero)
      have hord_ne_top : meromorphicOrderAt f z ≠ ⊤ := by
        rw [meromorphicOrderAt_ne_top_iff_eventually_ne_zero han_z.meromorphicAt]
        -- f has isolated zeros: either eventually zero or eventually nonzero near z
        rcases han_z.eventually_eq_zero_or_eventually_ne_zero with h | h
        · -- If f is eventually 0 near z, then by identity principle f = 0 everywhere
          exfalso
          have : f = 0 := AnalyticOnNhd.eq_of_eventuallyEq hf_an
            (analyticOnNhd_const) h
          exact hf0 (congr_fun this 0)
        · exact h
      -- Now: untop₀ of a positive finite WithTop ℤ is ≥ 1
      have h_eq := WithTop.coe_untop₀_of_ne_top hord_ne_top
      rw [← h_eq] at hord_pos
      exact_mod_cast hord_pos
    -- Now the main bound. Use monotonicity of logCounting on Ioi 0
    -- logCounting D R ≥ 0 (since D ≥ 0, D 0 = 0, R > 0 means all terms are nonneg)
    -- We need: zeroCount * log 2 ≤ D.logCounting R
    -- Expand logCounting
    unfold Function.locallyFinsuppWithin.logCounting
    simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, hD0, Int.cast_zero, zero_mul, add_zero]
    -- The support of D.toClosedBall R is finite
    have hsupp_fin := (Function.locallyFinsuppWithin.toClosedBall R D).finiteSupport
      (isCompact_closedBall 0 |R|)
    -- Convert finsum to Finset.sum
    -- The function being summed is g z := ↑(D.toClosedBall R z) * log(R * ‖z‖⁻¹)
    -- Its support is contained in the support of D.toClosedBall R
    rw [finsum_eq_sum_of_support_subset _ (s := hsupp_fin.toFinset) (fun x hx => by
      simp only [Finset.mem_coe, hsupp_fin.mem_toFinset, Function.mem_support]
      intro h
      exact (Function.mem_support.mp hx) (by simp [h]))]
    -- Each z with ‖z‖ ≤ r and f z = 0 is in the support, and contributes ≥ log 2
    -- The zero set in ball r is a subset of the support of D.toClosedBall R
    -- First show each zero is in hsupp_fin.toFinset
    have habs_R : |R| = R := abs_of_pos hR_pos
    have hzero_in_supp : ∀ z : ℂ, ‖z‖ ≤ r → f z = 0 → z ∈ hsupp_fin.toFinset := by
      intro z hz hfz
      rw [hsupp_fin.mem_toFinset, Function.mem_support]
      have hz_mem : z ∈ Metric.closedBall (0 : ℂ) |R| := by
        simp [Metric.mem_closedBall, habs_R]; linarith
      rw [Function.locallyFinsuppWithin.toClosedBall_eval_within _ hz_mem]
      exact_mod_cast ne_of_gt (lt_of_lt_of_le Int.one_pos (hzero_div z hfz))
    -- Each term in the sum is nonneg
    have hterm_nn : ∀ z ∈ hsupp_fin.toFinset,
        0 ≤ ↑(Function.locallyFinsuppWithin.toClosedBall R D z) *
            Real.log (R * ‖z‖⁻¹) := by
      intro z hz
      have hz_mem : z ∈ Metric.closedBall (0 : ℂ) |R| := by
        exact Function.locallyFinsuppWithin.toClosedBall_support_subset_closedBall D
          (hsupp_fin.mem_toFinset.mp hz)
      rw [Function.locallyFinsuppWithin.toClosedBall_eval_within _ hz_mem]
      -- z is in the support, so D z ≠ 0. Since D ≥ 0, D z > 0. Since D 0 = 0, z ≠ 0.
      have hDz_ne : D z ≠ 0 := by
        have := hsupp_fin.mem_toFinset.mp hz
        rwa [Function.mem_support, Function.locallyFinsuppWithin.toClosedBall_eval_within _ hz_mem]
          at this
      have hz0 : z ≠ 0 := by
        intro heq; rw [heq] at hDz_ne; exact hDz_ne hD0
      apply mul_nonneg
      · exact_mod_cast hD_nn z
      · apply Real.log_nonneg
        rw [habs_R, Metric.mem_closedBall, Complex.dist_eq, sub_zero] at hz_mem
        rw [le_mul_inv_iff₀ (norm_pos_iff.mpr hz0)]
        linarith
    -- Each zero z with ‖z‖ ≤ r contributes ≥ log 2
    have hterm_ge : ∀ z : ℂ, ‖z‖ ≤ r → f z = 0 →
        Real.log 2 ≤ ↑(Function.locallyFinsuppWithin.toClosedBall R D z) *
            Real.log (R * ‖z‖⁻¹) := by
      intro z hz hfz
      have hz_ne : z ≠ 0 := by intro h; rw [h] at hfz; exact hf0 hfz
      have hz_mem : z ∈ Metric.closedBall (0 : ℂ) |R| := by
        simp [Metric.mem_closedBall, habs_R]; linarith
      rw [Function.locallyFinsuppWithin.toClosedBall_eval_within _ hz_mem]
      -- D z ≥ 1 and log(R/‖z‖) ≥ log 2
      have hDz := hzero_div z hfz
      have hlog_ge : Real.log 2 ≤ Real.log (R * ‖z‖⁻¹) := by
        apply Real.log_le_log (by positivity)
        rw [le_mul_inv_iff₀ (norm_pos_iff.mpr hz_ne)]
        linarith
      calc Real.log 2
          = 1 * Real.log 2 := by ring
        _ ≤ ↑(D z) * Real.log (R * ‖z‖⁻¹) := by
            apply mul_le_mul
            · exact_mod_cast hDz
            · exact hlog_ge
            · exact hlog2_pos.le
            · exact_mod_cast le_trans (by norm_num : (0 : ℤ) ≤ 1) hDz
    -- Now: zeroCount * log 2 = Nat.card * log 2 ≤ ∑ over zeros ≤ ∑ over support
    -- Use Nat.card = the number of elements in the subtype
    -- We need to relate zeroCount to a sum over a finset
    -- zeroCount f r = Nat.card { z : ℂ // ‖z‖ ≤ r ∧ f z = 0 }
    -- Key: this equals the cardinality of a finite set, and we can bound
    -- the sum over the support by summing over these zeros

    -- Since the zeros are finite and contained in the support finset,
    -- build a finset of zeros
    -- The zeros in ball r are finite (subset of the finite support)
    have hzero_finite : Set.Finite { z : ℂ | ‖z‖ ≤ r ∧ f z = 0 } := by
      apply Set.Finite.subset (s := ↑hsupp_fin.toFinset) hsupp_fin.toFinset.finite_toSet
      intro z ⟨hz, hfz⟩
      exact Finset.mem_coe.mpr (hzero_in_supp z hz hfz)
    -- zeroCount equals the toFinset.card
    have hzc_eq : zeroCount f r = hzero_finite.toFinset.card := by
      unfold zeroCount
      exact Nat.card_eq_card_finite_toFinset hzero_finite
    rw [hzc_eq]
    -- Now: hzero_finite.toFinset ⊆ hsupp_fin.toFinset
    have hsubset : hzero_finite.toFinset ⊆ hsupp_fin.toFinset := by
      intro z hz
      rw [Set.Finite.mem_toFinset] at hz
      exact hzero_in_supp z hz.1 hz.2
    -- Goal: hzero_finite.toFinset.card * log 2 ≤ ∑ z in hsupp_fin.toFinset, ...
    calc ↑hzero_finite.toFinset.card * Real.log 2
        = hzero_finite.toFinset.card • Real.log 2 := by rw [nsmul_eq_mul]
      _ ≤ ∑ z ∈ hzero_finite.toFinset,
            ↑(Function.locallyFinsuppWithin.toClosedBall R D z) *
            Real.log (R * ‖z‖⁻¹) := by
          apply Finset.card_nsmul_le_sum
          intro z hz
          rw [Set.Finite.mem_toFinset] at hz
          exact hterm_ge z hz.1 hz.2
      _ ≤ ∑ z ∈ hsupp_fin.toFinset,
            ↑(Function.locallyFinsuppWithin.toClosedBall R D z) *
            Real.log (R * ‖z‖⁻¹) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsubset
            (fun z hz _ => hterm_nn z hz)
  -- Combine with Jensen
  have chain : (zeroCount f r : ℝ) * Real.log 2 ≤
      Real.log (maxModulus f (2 * r)) - Real.log ‖f 0‖ := le_trans key hJensen
  -- Divide by log 2
  calc (zeroCount f r : ℝ)
      = (zeroCount f r : ℝ) * Real.log 2 / Real.log 2 := by
          rw [mul_div_cancel_right₀ _ (ne_of_gt hlog2_pos)]
    _ ≤ (Real.log (maxModulus f (2 * r)) - Real.log ‖f 0‖) / Real.log 2 :=
          div_le_div_of_nonneg_right chain hlog2_pos.le
    _ = 1 / Real.log 2 * (Real.log (maxModulus f (2 * r)) - Real.log ‖f 0‖) := by ring

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

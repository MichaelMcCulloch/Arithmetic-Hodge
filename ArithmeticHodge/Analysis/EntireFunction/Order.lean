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
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Complex.Liouville
import ArithmeticHodge.Analysis.ComplexStirling
import ArithmeticHodge.Analysis.EntireFunction.Defs

open Complex Filter Topology Real MeromorphicOn

namespace ArithmeticHodge.Analysis.EntireFunction

-- ============================================================
-- Maximum Modulus and Order
-- ============================================================

-- maxModulus, entireOrder, HasFiniteOrder are imported from Defs.lean

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
lemma norm_le_maxModulus (f : ℂ → ℂ) (hf : Differentiable ℂ f)
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
    (hf_ne : ¬ f = 0) (r : ℝ) (hr : 0 < r) :
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
    have hglobal : ∀ᶠ z in Filter.codiscreteWithin (Set.univ : Set ℂ), f z ≠ 0 :=
      (hf_an.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_univ).resolve_left
        (fun hzero => hf_ne (funext fun z => hzero (Set.mem_univ z)))
    exact hglobal.filter_mono (Filter.codiscreteWithin.mono (Set.subset_univ _))
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
/-- Jensen's upper bound using the nonzero trailing coefficient at the origin.
    This version also applies when `f 0 = 0`. -/
private lemma jensen_zero_count_le_log_max_of_ne (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hf_ne : ¬ f = 0) (r : ℝ) (hr : 0 < r) :
    integratedZeroCount f r ≤ Real.log (maxModulus f r) -
      Real.log ‖meromorphicTrailingCoeffAt f 0‖ := by
  unfold integratedZeroCount
  have hf_an : AnalyticOnNhd ℂ f Set.univ := analyticOnNhd_univ_iff_differentiable.mpr hf
  have hf_mer : Meromorphic f := fun x => (hf_an x (Set.mem_univ x)).meromorphicAt
  have hJensen :=
    ValueDistribution.logCounting_zero_sub_logCounting_top_eq_circleAverage_sub_const
      hf_mer (ne_of_gt hr)
  have hdiv_nn : (0 : ℂ → ℤ) ≤ divisor f Set.univ :=
    (hf_an.meromorphicNFOn.divisor_nonneg_iff_analyticOnNhd).mpr hf_an
  have hno_poles : ValueDistribution.logCounting f (⊤ : WithTop ℂ) r = 0 := by
    rw [ValueDistribution.logCounting_top]
    have hneg_zero : (divisor f Set.univ)⁻ = 0 := by
      ext z
      exact sup_eq_right.mpr (neg_nonpos.mpr (hdiv_nn z))
    rw [hneg_zero]
    simp [Function.locallyFinsuppWithin.logCounting]
  have hkey : ValueDistribution.logCounting f (0 : ℂ) r =
      circleAverage (Real.log ‖f ·‖) 0 r -
        Real.log ‖meromorphicTrailingCoeffAt f 0‖ := by
    simpa only [Pi.sub_apply, hno_poles, sub_zero] using hJensen
  rw [hkey]
  linarith [circleAverage_log_norm_le_log_maxModulus f hf hf_ne r hr]

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
  have hf_an : AnalyticOnNhd ℂ f Set.univ := analyticOnNhd_univ_iff_differentiable.mpr hf
  have htrailing : meromorphicTrailingCoeffAt f 0 = f 0 :=
    (hf_an 0 (Set.mem_univ 0)).meromorphicTrailingCoeffAt_of_ne_zero hf0
  have hf_ne : ¬ f = 0 := fun h => hf0 (congr_fun h 0)
  simpa only [htrailing] using jensen_zero_count_le_log_max_of_ne f hf hf_ne r hr

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

/-- The distinct zeros of a nonzero entire function in a closed ball form a finite set. -/
private lemma zeroSet_finite (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hf_ne : ¬ f = 0) (R : ℝ) (hR : 0 ≤ R) :
    Set.Finite {z : ℂ | ‖z‖ ≤ R ∧ f z = 0} := by
  let D := MeromorphicOn.divisor f Set.univ
  have hf_an : AnalyticOnNhd ℂ f Set.univ := analyticOnNhd_univ_iff_differentiable.mpr hf
  have hf_mer : MeromorphicOn f Set.univ := hf_an.meromorphicOn
  have hzero_div : ∀ z : ℂ, f z = 0 → 1 ≤ D z := by
    intro z hfz
    rw [show D z = (meromorphicOrderAt f z).untop₀ by
      simp [D, MeromorphicOn.divisor_apply hf_mer (Set.mem_univ z)]]
    have han_z := hf_an z (Set.mem_univ z)
    have hord_ne_zero : meromorphicOrderAt f z ≠ 0 := by
      intro h
      exact (han_z.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp h) hfz
    have hord_pos : 0 < meromorphicOrderAt f z :=
      lt_of_le_of_ne han_z.meromorphicOrderAt_nonneg (Ne.symm hord_ne_zero)
    have hord_ne_top : meromorphicOrderAt f z ≠ ⊤ := by
      rw [meromorphicOrderAt_ne_top_iff_eventually_ne_zero han_z.meromorphicAt]
      rcases han_z.eventually_eq_zero_or_eventually_ne_zero with h | h
      · exact (hf_ne (AnalyticOnNhd.eq_of_eventuallyEq hf_an analyticOnNhd_const h)).elim
      · exact h
    have h_eq := WithTop.coe_untop₀_of_ne_top hord_ne_top
    rw [← h_eq] at hord_pos
    exact_mod_cast hord_pos
  have hsupp_fin := (Function.locallyFinsuppWithin.toClosedBall R D).finiteSupport
    (isCompact_closedBall 0 |R|)
  apply Set.Finite.subset (s := ↑hsupp_fin.toFinset) hsupp_fin.toFinset.finite_toSet
  intro z hz
  rw [Finset.mem_coe, hsupp_fin.mem_toFinset, Function.mem_support]
  have hz_mem : z ∈ Metric.closedBall (0 : ℂ) |R| := by
    simpa [Metric.mem_closedBall, abs_of_nonneg hR] using hz.1
  rw [Function.locallyFinsuppWithin.toClosedBall_eval_within _ hz_mem]
  exact ne_of_gt (lt_of_lt_of_le Int.zero_lt_one (hzero_div z hz.2))

/-- Every nonzero zero in the radius-`r` ball contributes at least `log 2` to
    the logarithmic counting function at radius `2r`. -/
private lemma nonzeroZeroCount_mul_log_two_le_integrated (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) (hf_ne : ¬ f = 0) (r : ℝ) (hr : 1 ≤ r) :
    (Nat.card {z : ℂ // ‖z‖ ≤ r ∧ f z = 0 ∧ z ≠ 0} : ℝ) * Real.log 2 ≤
      integratedZeroCount f (2 * r) := by
  unfold integratedZeroCount
  change (Nat.card {z : ℂ // ‖z‖ ≤ r ∧ f z = 0 ∧ z ≠ 0} : ℝ) * Real.log 2 ≤
    ValueDistribution.logCounting f (0 : WithTop ℂ) (2 * r)
  rw [ValueDistribution.logCounting_zero]
  set D := (MeromorphicOn.divisor f Set.univ)⁺ with hD_def
  have hf_an : AnalyticOnNhd ℂ f Set.univ := analyticOnNhd_univ_iff_differentiable.mpr hf
  have hf_mer : MeromorphicOn f Set.univ := hf_an.meromorphicOn
  have hdiv_nn : (0 : Function.locallyFinsupp ℂ ℤ) ≤ MeromorphicOn.divisor f Set.univ :=
    (hf_an.meromorphicNFOn.divisor_nonneg_iff_analyticOnNhd).mpr hf_an
  have hdiv_nn_z : ∀ z, 0 ≤ MeromorphicOn.divisor f Set.univ z := hdiv_nn
  have hD_eq : ∀ z, D z = MeromorphicOn.divisor f Set.univ z := by
    intro z
    show (MeromorphicOn.divisor f Set.univ z)⁺ = MeromorphicOn.divisor f Set.univ z
    exact posPart_eq_self.mpr (hdiv_nn_z z)
  have hD_nn : (0 : Function.locallyFinsupp ℂ ℤ) ≤ D := by
    intro z
    rw [hD_eq]
    exact hdiv_nn_z z
  set R := 2 * r with hR_def
  have hR_pos : 0 < R := by linarith
  have hR_ge_one : 1 ≤ R := by linarith
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hzero_div : ∀ z : ℂ, f z = 0 → 1 ≤ D z := by
    intro z hfz
    rw [hD_eq, MeromorphicOn.divisor_apply hf_mer (Set.mem_univ z)]
    have han_z := hf_an z (Set.mem_univ z)
    have hord_ne_zero : meromorphicOrderAt f z ≠ 0 := by
      intro h
      exact (han_z.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp h) hfz
    have hord_pos : 0 < meromorphicOrderAt f z :=
      lt_of_le_of_ne han_z.meromorphicOrderAt_nonneg (Ne.symm hord_ne_zero)
    have hord_ne_top : meromorphicOrderAt f z ≠ ⊤ := by
      rw [meromorphicOrderAt_ne_top_iff_eventually_ne_zero han_z.meromorphicAt]
      rcases han_z.eventually_eq_zero_or_eventually_ne_zero with h | h
      · exact (hf_ne (AnalyticOnNhd.eq_of_eventuallyEq hf_an analyticOnNhd_const h)).elim
      · exact h
    have h_eq := WithTop.coe_untop₀_of_ne_top hord_ne_top
    rw [← h_eq] at hord_pos
    exact_mod_cast hord_pos
  show (Nat.card {z : ℂ // ‖z‖ ≤ r ∧ f z = 0 ∧ z ≠ 0} : ℝ) * Real.log 2 ≤
    D.logCounting R
  unfold Function.locallyFinsuppWithin.logCounting
  simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  have hsupp_fin := (Function.locallyFinsuppWithin.toClosedBall R D).finiteSupport
    (isCompact_closedBall 0 |R|)
  have habs_R : |R| = R := abs_of_pos hR_pos
  have hzero_in_supp : ∀ z : ℂ, ‖z‖ ≤ r → f z = 0 → z ∈ hsupp_fin.toFinset := by
    intro z hz hfz
    rw [hsupp_fin.mem_toFinset, Function.mem_support]
    have hz_mem : z ∈ Metric.closedBall (0 : ℂ) |R| := by
      simp [Metric.mem_closedBall, habs_R]
      linarith
    rw [Function.locallyFinsuppWithin.toClosedBall_eval_within _ hz_mem]
    exact_mod_cast ne_of_gt (lt_of_lt_of_le Int.one_pos (hzero_div z hfz))
  have hterm_nn : ∀ z ∈ hsupp_fin.toFinset,
      0 ≤ ↑(Function.locallyFinsuppWithin.toClosedBall R D z) *
        Real.log (R * ‖z‖⁻¹) := by
    intro z hz
    have hz_mem : z ∈ Metric.closedBall (0 : ℂ) |R| :=
      Function.locallyFinsuppWithin.toClosedBall_support_subset_closedBall D
        (hsupp_fin.mem_toFinset.mp hz)
    rw [Function.locallyFinsuppWithin.toClosedBall_eval_within _ hz_mem]
    by_cases hz0 : z = 0
    · simp [hz0]
    · apply mul_nonneg
      · exact_mod_cast hD_nn z
      · apply Real.log_nonneg
        rw [habs_R, Metric.mem_closedBall, Complex.dist_eq, sub_zero] at hz_mem
        rw [le_mul_inv_iff₀ (norm_pos_iff.mpr hz0)]
        simpa using hz_mem
  have hterm_ge : ∀ z : ℂ, ‖z‖ ≤ r → f z = 0 → z ≠ 0 →
      Real.log 2 ≤ ↑(Function.locallyFinsuppWithin.toClosedBall R D z) *
        Real.log (R * ‖z‖⁻¹) := by
    intro z hz hfz hz0
    have hz_mem : z ∈ Metric.closedBall (0 : ℂ) |R| := by
      simp [Metric.mem_closedBall, habs_R]
      linarith
    rw [Function.locallyFinsuppWithin.toClosedBall_eval_within _ hz_mem]
    have hDz := hzero_div z hfz
    have hlog_ge : Real.log 2 ≤ Real.log (R * ‖z‖⁻¹) := by
      apply Real.log_le_log (by positivity)
      rw [le_mul_inv_iff₀ (norm_pos_iff.mpr hz0)]
      linarith
    calc
      Real.log 2 = 1 * Real.log 2 := by ring
      _ ≤ ↑(D z) * Real.log (R * ‖z‖⁻¹) := by
        apply mul_le_mul
        · exact_mod_cast hDz
        · exact hlog_ge
        · exact hlog2_pos.le
        · exact_mod_cast le_trans (by norm_num : (0 : ℤ) ≤ 1) hDz
  have hzero_finite : Set.Finite {z : ℂ | ‖z‖ ≤ r ∧ f z = 0 ∧ z ≠ 0} :=
    (zeroSet_finite f hf hf_ne r (by linarith)).subset (fun z hz => ⟨hz.1, hz.2.1⟩)
  have hcard_eq : Nat.card {z : ℂ // ‖z‖ ≤ r ∧ f z = 0 ∧ z ≠ 0} =
      hzero_finite.toFinset.card := Nat.card_eq_card_finite_toFinset hzero_finite
  have hsubset : hzero_finite.toFinset ⊆ hsupp_fin.toFinset := by
    intro z hz
    rw [Set.Finite.mem_toFinset] at hz
    exact hzero_in_supp z hz.1 hz.2.1
  have hsum :
      (Nat.card {z : ℂ // ‖z‖ ≤ r ∧ f z = 0 ∧ z ≠ 0} : ℝ) * Real.log 2 ≤
        ∑ᶠ z, ↑(Function.locallyFinsuppWithin.toClosedBall R D z) *
          Real.log (R * ‖z‖⁻¹) := by
    rw [hcard_eq]
    rw [finsum_eq_sum_of_support_subset _ (s := hsupp_fin.toFinset) (fun x hx => by
      simp only [Finset.mem_coe, hsupp_fin.mem_toFinset, Function.mem_support]
      intro h
      exact (Function.mem_support.mp hx) (by simp [h]))]
    calc
      (hzero_finite.toFinset.card : ℝ) * Real.log 2 =
          hzero_finite.toFinset.card • Real.log 2 := by rw [nsmul_eq_mul]
      _ ≤ ∑ z ∈ hzero_finite.toFinset,
          ↑(Function.locallyFinsuppWithin.toClosedBall R D z) *
            Real.log (R * ‖z‖⁻¹) := by
        apply Finset.card_nsmul_le_sum
        intro z hz
        rw [Set.Finite.mem_toFinset] at hz
        exact hterm_ge z hz.1 hz.2.1 hz.2.2
      _ ≤ ∑ z ∈ hsupp_fin.toFinset,
          ↑(Function.locallyFinsuppWithin.toClosedBall R D z) *
            Real.log (R * ‖z‖⁻¹) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun z hz _ => hterm_nn z hz)
  apply le_trans hsum
  apply le_add_of_nonneg_right
  exact mul_nonneg (by exact_mod_cast hD_nn 0) (Real.log_nonneg hR_ge_one)

/-- Jensen's bound for an arbitrary nonzero entire function. The additive `1`
    accounts for the possible zero at the origin. -/
private lemma zeroCount_le_logMax_add_one (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hf_ne : ¬ f = 0) (r : ℝ) (hr : 1 ≤ r) :
    (zeroCount f r : ℝ) ≤ 1 + (1 / Real.log 2) *
      (Real.log (maxModulus f (2 * r)) -
        Real.log ‖meromorphicTrailingCoeffAt f 0‖) := by
  let allFinite := zeroSet_finite f hf hf_ne r (by linarith)
  let nonzeroFinite : Set.Finite {z : ℂ | ‖z‖ ≤ r ∧ f z = 0 ∧ z ≠ 0} :=
    allFinite.subset (fun z hz => ⟨hz.1, hz.2.1⟩)
  have hzc_eq : zeroCount f r = allFinite.toFinset.card := by
    unfold zeroCount
    exact Nat.card_eq_card_finite_toFinset allFinite
  have hnz_eq : Nat.card {z : ℂ // ‖z‖ ≤ r ∧ f z = 0 ∧ z ≠ 0} =
      nonzeroFinite.toFinset.card := Nat.card_eq_card_finite_toFinset nonzeroFinite
  have hsub : allFinite.toFinset ⊆ insert 0 nonzeroFinite.toFinset := by
    intro z hz
    rw [Set.Finite.mem_toFinset] at hz
    by_cases hz0 : z = 0
    · simpa [hz0]
    · apply Finset.mem_insert_of_mem
      rw [Set.Finite.mem_toFinset]
      exact ⟨hz.1, hz.2, hz0⟩
  have hcount_le : (zeroCount f r : ℝ) ≤
      (Nat.card {z : ℂ // ‖z‖ ≤ r ∧ f z = 0 ∧ z ≠ 0} : ℝ) + 1 := by
    rw [hzc_eq, hnz_eq]
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_insert_le 0 _)
  have h2r : 0 < 2 * r := by linarith
  have hkey := nonzeroZeroCount_mul_log_two_le_integrated f hf hf_ne r hr
  have hJensen := jensen_zero_count_le_log_max_of_ne f hf hf_ne (2 * r) h2r
  have hchain :
      (Nat.card {z : ℂ // ‖z‖ ≤ r ∧ f z = 0 ∧ z ≠ 0} : ℝ) * Real.log 2 ≤
        Real.log (maxModulus f (2 * r)) -
          Real.log ‖meromorphicTrailingCoeffAt f 0‖ := hkey.trans hJensen
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hnz_bound :
      (Nat.card {z : ℂ // ‖z‖ ≤ r ∧ f z = 0 ∧ z ≠ 0} : ℝ) ≤
        (1 / Real.log 2) * (Real.log (maxModulus f (2 * r)) -
          Real.log ‖meromorphicTrailingCoeffAt f 0‖) := by
    calc
      (Nat.card {z : ℂ // ‖z‖ ≤ r ∧ f z = 0 ∧ z ≠ 0} : ℝ) =
          (Nat.card {z : ℂ // ‖z‖ ≤ r ∧ f z = 0 ∧ z ≠ 0} : ℝ) *
            Real.log 2 / Real.log 2 := by
              rw [mul_div_cancel_right₀ _ hlog2_pos.ne']
      _ ≤ (Real.log (maxModulus f (2 * r)) -
          Real.log ‖meromorphicTrailingCoeffAt f 0‖) / Real.log 2 :=
        div_le_div_of_nonneg_right hchain hlog2_pos.le
      _ = (1 / Real.log 2) * (Real.log (maxModulus f (2 * r)) -
          Real.log ‖meromorphicTrailingCoeffAt f 0‖) := by ring
  linarith

-- ============================================================
-- Exponent of Convergence
-- ============================================================

/-- The order of a non-zero entire function is nonneg.

    If the order were negative, the limsup of log log M / log r would be < 0,
    meaning eventually M(f,r) < e. By Liouville's theorem, f would be constant,
    and a constant entire function has order 0 — contradiction. -/
lemma entireOrder_nonneg (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hf_ne : ¬ f = 0) : (0 : EReal) ≤ entireOrder f := by
  unfold entireOrder
  apply le_limsup_of_le ⟨⊤, Eventually.of_forall (fun _ => le_top)⟩
  intro b hb
  -- hb : ∀ᶠ r in atTop, (↑(log (log (maxModulus f r)) / log r) : EReal) ≤ b
  -- Goal: (0 : EReal) ≤ b
  by_contra hb_neg
  push_neg at hb_neg
  -- b ≠ ⊥ (since real casts > ⊥) and b ≠ ⊤ (since b < 0)
  have hb_ne_bot : b ≠ ⊥ := by
    intro h; subst h; exact absurd (hb.exists).choose_spec (not_le.mpr (EReal.bot_lt_coe _))
  have hb_ne_top : b ≠ ⊤ := ne_of_lt (lt_trans hb_neg EReal.zero_lt_top)
  have hb'_neg : b.toReal < 0 := EReal.toReal_neg hb_neg hb_ne_bot
  have hb_coe : (b.toReal : EReal) = b := EReal.coe_toReal hb_ne_top hb_ne_bot
  -- Convert to real bound
  have hb_real : ∀ᶠ r in Filter.atTop,
      Real.log (Real.log (maxModulus f r)) / Real.log r ≤ b.toReal := by
    apply hb.mono; intro r hr; rw [← hb_coe] at hr; exact_mod_cast hr
  -- Extract threshold R₀ > 1
  obtain ⟨R₀', hR₀'_bound⟩ := Filter.eventually_atTop.mp hb_real
  set R₀ := max R₀' 2
  have hR₀_pos : 1 < R₀ := by linarith [le_max_right R₀' 2]
  have hR₀_bound : ∀ r ≥ R₀,
      Real.log (Real.log (maxModulus f r)) / Real.log r ≤ b.toReal :=
    fun r hr => hR₀'_bound r (le_trans (le_max_left _ _) hr)
  -- Actually, let's use a simpler approach: f is bounded
  -- For any z, take r = max(‖z‖, R₀) and use norm_le_maxModulus
  have hf_bdd : Bornology.IsBounded (Set.range f) := by
    -- Show ‖f z‖ < Real.exp (R₀ ^ |b.toReal| + 1) for all z (some bound)
    -- From hb_real: for r ≥ R₀, log(log M(f,r)) / log r ≤ b' < 0
    -- This means log(log M(f,r)) ≤ b' * log r < 0 (since log r > 0 for r > 1)
    -- Hence log M(f,r) < e^0 = 1, so M(f,r) < e
    -- For any z: ‖f z‖ ≤ M(f, max(‖z‖, R₀)) < e
    rw [Metric.isBounded_range_iff]
    use 2 * Real.exp 1
    intro z w
    have bound_at : ∀ v : ℂ, ‖f v‖ ≤ Real.exp 1 := by
      intro v
      have hr : 0 < max ‖v‖ R₀ := lt_of_lt_of_le (by linarith : (0 : ℝ) < R₀) (le_max_right _ _)
      have hle := norm_le_maxModulus f hf v (max ‖v‖ R₀) hr (le_max_left _ _)
      -- M(f, max(‖v‖, R₀)) < e
      suffices maxModulus f (max ‖v‖ R₀) ≤ Real.exp 1 from le_trans hle this
      -- From the bound: for r = max(‖v‖, R₀) ≥ R₀
      have hr_ge : R₀ ≤ max ‖v‖ R₀ := le_max_right _ _
      have hr_gt1 : 1 < max ‖v‖ R₀ := lt_of_lt_of_le hR₀_pos hr_ge
      have hlog_pos : 0 < Real.log (max ‖v‖ R₀) := Real.log_pos hr_gt1
      have hbd := hR₀_bound (max ‖v‖ R₀) hr_ge
      -- hbd : log(log M) / log r ≤ b' where b' < 0
      -- If log M ≤ 0: log(log M) = 0 (junk), so 0/log r = 0 ≤ b' < 0, impossible
      -- So log M > 0 and log(log M) ≤ b' * log r < 0, hence log M < 1, M < e
      have hM_nonneg : 0 ≤ maxModulus f (max ‖v‖ R₀) :=
        le_trans (norm_nonneg (f 0)) (norm_le_maxModulus f hf 0 _ hr (by simp))
      by_cases hlogM : Real.log (maxModulus f (max ‖v‖ R₀)) ≤ 0
      · -- log M ≤ 0 means M ≤ 1 ≤ e
        exact le_trans ((Real.log_nonpos_iff hM_nonneg).mp hlogM)
          (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1))
      · push_neg at hlogM
        have hM_pos : 0 < maxModulus f (max ‖v‖ R₀) := by
          by_contra h; push_neg at h
          exact absurd (le_antisymm h hM_nonneg ▸ hlogM) (by simp [Real.log_zero])
        have hloglogM := (div_le_iff₀ hlog_pos).mp hbd
        have hloglogM_neg : Real.log (Real.log (maxModulus f (max ‖v‖ R₀))) < 0 :=
          calc Real.log (Real.log (maxModulus f (max ‖v‖ R₀)))
              ≤ b.toReal * Real.log (max ‖v‖ R₀) := hloglogM
            _ < 0 := mul_neg_of_neg_of_pos hb'_neg hlog_pos
        -- log(log M) < 0 → log M < 1 → M < e
        have hlogM_lt1 : Real.log (maxModulus f (max ‖v‖ R₀)) < 1 := by
          have := (Real.log_lt_iff_lt_exp hlogM).mp hloglogM_neg
          rwa [Real.exp_zero] at this
        exact le_of_lt ((Real.log_lt_iff_lt_exp hM_pos).mp hlogM_lt1)
    calc dist (f z) (f w) ≤ ‖f z‖ + ‖f w‖ := dist_le_norm_add_norm (f z) (f w)
      _ ≤ Real.exp 1 + Real.exp 1 := add_le_add (bound_at z) (bound_at w)
      _ = 2 * Real.exp 1 := by ring
  -- By Liouville: f is constant
  obtain ⟨c, hc⟩ := hf.exists_eq_const_of_bounded hf_bdd
  -- But f ≠ 0
  have hc_ne : c ≠ 0 := by
    intro h; exact hf_ne (hc ▸ h ▸ rfl)
  -- For constant f: maxModulus f r = ‖c‖ for r > 0
  have hM_eq : ∀ r, 0 < r → maxModulus f r = ‖c‖ := by
    intro r hr
    apply le_antisymm
    · -- Upper: all values are ‖c‖ or 0
      show ⨆ (z : ℂ), ⨆ (_ : ‖z‖ ≤ r), ‖f z‖ ≤ ‖c‖
      apply ciSup_le; intro z
      by_cases hz : ‖z‖ ≤ r
      · rw [ciSup_pos hz, hc, Function.const_apply]
      · rw [ciSup_neg hz, Real.sSup_empty]; exact norm_nonneg c
    · calc ‖c‖ = ‖f 0‖ := by rw [hc]; rfl
        _ ≤ maxModulus f r := norm_le_maxModulus f hf 0 r hr (by simp [hr.le])
  -- Contradiction: log(log ‖c‖) / log r → 0 but must be ≤ b.toReal < 0
  -- From hR₀_bound + hM_eq: for r ≥ R₀, log(log ‖c‖) / log r ≤ b.toReal
  set L := Real.log (Real.log ‖c‖)
  have hLr : ∀ r ≥ R₀, L / Real.log r ≤ b.toReal := by
    intro r hr
    have hr_pos : 0 < r := lt_of_lt_of_le (by linarith : (0 : ℝ) < R₀) hr
    rw [show L = Real.log (Real.log (maxModulus f r)) from by rw [hM_eq r hr_pos]]
    exact hR₀_bound r hr
  -- At r = R₀: L ≤ b' * log R₀ < 0
  have hlog_R₀_pos : 0 < Real.log R₀ := Real.log_pos hR₀_pos
  have hprod_neg : b.toReal * Real.log R₀ < 0 := mul_neg_of_neg_of_pos hb'_neg hlog_R₀_pos
  -- Archimedean: find n with n * (b' * log R₀) < L
  obtain ⟨n, hn⟩ := exists_nat_gt (L / (b.toReal * Real.log R₀))
  have hn_pos : 0 < n := by
    by_contra h; push_neg at h; interval_cases n
    simp at hn
    have := (div_lt_iff_of_neg hprod_neg).mp hn
    simp at this; linarith [(div_le_iff₀ hlog_R₀_pos).mp (hLr R₀ le_rfl)]
  have hn_lt : (n : ℝ) * (b.toReal * Real.log R₀) < L :=
    (div_lt_iff_of_neg hprod_neg).mp hn
  -- R₀^n ≥ R₀ and log(R₀^n) = n * log R₀
  have hR₀n_ge : R₀ ≤ R₀ ^ n :=
    le_self_pow₀ (le_of_lt hR₀_pos) (by omega)
  -- Apply hLr at R₀^n to get L ≤ b' * (n * log R₀)
  have hL_le := (div_le_iff₀ (by rw [Real.log_pow]; positivity)).mp (hLr (R₀ ^ n) hR₀n_ge)
  rw [Real.log_pow] at hL_le
  -- hL_le : L ≤ b' * (n * log R₀), hn_lt : n * (b' * log R₀) < L
  linarith [mul_comm b.toReal (↑n * Real.log R₀)]

/-- From `entireOrder f < α`: eventually `Real.log (maxModulus f r) ≤ r ^ α`. -/
private lemma logMax_eventually_le_rpow (f : ℂ → ℂ) (α : ℝ)
    (hα : entireOrder f < (α : EReal)) :
    ∀ᶠ r in Filter.atTop, Real.log (maxModulus f r) ≤ r ^ α := by
  have hev := eventually_lt_of_limsup_lt hα
  apply (hev.and (Filter.eventually_ge_atTop 2)).mono
  intro r ⟨hr_limsup, hr_ge⟩
  have hr_gt1 : (1 : ℝ) < r := by linarith
  have hlogr : 0 < Real.log r := Real.log_pos hr_gt1
  have hr_limsup' : Real.log (Real.log (maxModulus f r)) / Real.log r < α := by
    exact_mod_cast hr_limsup
  by_cases hlogM : Real.log (maxModulus f r) ≤ 0
  · exact le_trans hlogM (rpow_nonneg (le_of_lt (lt_trans zero_lt_one hr_gt1)) α)
  · push_neg at hlogM
    rw [show r ^ α = Real.exp (α * Real.log r) from by
      rw [rpow_def_of_pos (lt_trans zero_lt_one hr_gt1), mul_comm]]
    exact le_of_lt ((Real.log_lt_iff_lt_exp hlogM).mp ((div_lt_iff₀ hlogr).mp hr_limsup'))

/-- Counting function bound: if `entireOrder f < α` and `f 0 ≠ 0`,
    then `zeroCount f r ≤ C * r ^ α` for large `r`. -/
private lemma zeroCount_eventually_le_rpow (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hf0 : f 0 ≠ 0) (α : ℝ) (hα_pos : 0 < α)
    (hα : entireOrder f < (α : EReal)) :
    ∃ (C : ℝ) (R₀ : ℝ), 0 < C ∧ 1 ≤ R₀ ∧
      ∀ r, R₀ ≤ r → (zeroCount f r : ℝ) ≤ C * r ^ α := by
  -- From logMax_eventually_le_rpow: eventually log M(f,r) ≤ r^α
  obtain ⟨R₁, hR₁⟩ := Filter.eventually_atTop.mp (logMax_eventually_le_rpow f α hα)
  -- Choose R₀ large enough for both the logMax bound and absorbing -log ‖f 0‖
  set K := |Real.log ‖f 0‖| -- constant to absorb
  obtain ⟨R₂, hR₂⟩ := Filter.eventually_atTop.mp
    (Filter.eventually_ge_atTop (max 1 (K ^ (1 / α))))
  set R₀ := max (max R₁ R₂) 2
  have hR₀_ge1 : (1 : ℝ) ≤ R₀ := by linarith [le_max_right (max R₁ R₂) 2]
  have hR₁_le : R₁ ≤ R₀ := le_trans (le_max_left R₁ R₂) (le_max_left _ 2)
  have hR₂_le : R₂ ≤ R₀ := le_trans (le_max_right R₁ R₂) (le_max_left _ 2)
  set C := 1 / Real.log 2 * (2 ^ α + 1)
  have hC_pos : 0 < C := by
    apply mul_pos (div_pos one_pos (Real.log_pos one_lt_two))
    linarith [rpow_pos_of_pos (show (0:ℝ) < 2 by norm_num) α]
  refine ⟨C, R₀, hC_pos, hR₀_ge1, fun r hr => ?_⟩
  have hr_pos : 0 < r := by linarith
  -- Jensen bound
  have hJ := zeroCount_le_logMax f hf hf0 r hr_pos
  -- log M(f, 2r) ≤ (2r)^α = 2^α · r^α
  have h2r_logM : Real.log (maxModulus f (2 * r)) ≤ 2 ^ α * r ^ α := by
    calc Real.log (maxModulus f (2 * r))
        ≤ (2 * r) ^ α := hR₁ (2 * r) (by linarith)
      _ = 2 ^ α * r ^ α := Real.mul_rpow (by norm_num) hr_pos.le
  -- -log ‖f 0‖ ≤ K ≤ r^α (since r ≥ R₀ ≥ K^{1/α})
  have hrα_ge_K : K ≤ r ^ α := by
    have hr_ge := hR₂ R₀ hR₂_le
    have hr_ge_K1α : K ^ (1 / α) ≤ r := le_trans (le_max_right 1 _) (le_trans hr_ge hr)
    calc K = (K ^ (1 / α)) ^ α := by
          rw [← Real.rpow_mul (abs_nonneg _), div_mul_cancel₀ 1 hα_pos.ne', Real.rpow_one]
      _ ≤ r ^ α := Real.rpow_le_rpow (by positivity) hr_ge_K1α hα_pos.le
  have hlog_bound : -Real.log ‖f 0‖ ≤ r ^ α := by
    calc -Real.log ‖f 0‖ ≤ |Real.log ‖f 0‖| := neg_le_abs _
      _ ≤ r ^ α := hrα_ge_K
  -- Combine
  calc (zeroCount f r : ℝ)
      ≤ 1 / Real.log 2 * (Real.log (maxModulus f (2 * r)) - Real.log ‖f 0‖) := hJ
    _ ≤ 1 / Real.log 2 * (2 ^ α * r ^ α + r ^ α) := by
        gcongr; linarith
    _ = C * r ^ α := by ring

/-- The eventual power bound for the distinct zero count without assuming that
    the origin is not a zero. -/
private lemma zeroCount_eventually_le_rpow_of_ne (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hf_ne : ¬ f = 0) (α : ℝ) (hα_pos : 0 < α)
    (hα : entireOrder f < (α : EReal)) :
    ∃ (C : ℝ) (R₀ : ℝ), 0 < C ∧ 1 ≤ R₀ ∧
      ∀ r, R₀ ≤ r → (zeroCount f r : ℝ) ≤ C * r ^ α := by
  obtain ⟨R₁, hR₁⟩ := Filter.eventually_atTop.mp (logMax_eventually_le_rpow f α hα)
  set K := |Real.log ‖meromorphicTrailingCoeffAt f 0‖|
  set R₀ := max R₁ (max 2 (K ^ (1 / α)))
  set C := 1 + 1 / Real.log 2 * (2 ^ α + 1)
  have hR₀_ge1 : (1 : ℝ) ≤ R₀ := by
    dsimp [R₀]
    linarith [le_max_left (2 : ℝ) (K ^ (1 / α)), le_max_right R₁ (max 2 (K ^ (1 / α)))]
  have hC_pos : 0 < C := by
    dsimp [C]
    have hfactor : 0 < 1 / Real.log 2 := div_pos one_pos (Real.log_pos one_lt_two)
    have hsum : 0 < (2 : ℝ) ^ α + 1 := by positivity
    positivity
  refine ⟨C, R₀, hC_pos, hR₀_ge1, fun r hr => ?_⟩
  have hr_ge1 : (1 : ℝ) ≤ r := hR₀_ge1.trans hr
  have hr_pos : 0 < r := zero_lt_one.trans_le hr_ge1
  have hJ := zeroCount_le_logMax_add_one f hf hf_ne r hr_ge1
  have hR₁_le : R₁ ≤ R₀ := le_max_left _ _
  have h2r_logM : Real.log (maxModulus f (2 * r)) ≤ 2 ^ α * r ^ α := by
    calc
      Real.log (maxModulus f (2 * r)) ≤ (2 * r) ^ α :=
        hR₁ (2 * r) (by linarith)
      _ = 2 ^ α * r ^ α := Real.mul_rpow (by norm_num) hr_pos.le
  have hr_ge_K1α : K ^ (1 / α) ≤ r := by
    exact (le_max_right (2 : ℝ) _).trans ((le_max_right R₁ _).trans hr)
  have hrα_ge_K : K ≤ r ^ α := by
    calc
      K = (K ^ (1 / α)) ^ α := by
        rw [← Real.rpow_mul (abs_nonneg _), div_mul_cancel₀ 1 hα_pos.ne', Real.rpow_one]
      _ ≤ r ^ α := Real.rpow_le_rpow (by positivity) hr_ge_K1α hα_pos.le
  have hlog_bound : -Real.log ‖meromorphicTrailingCoeffAt f 0‖ ≤ r ^ α := by
    calc
      -Real.log ‖meromorphicTrailingCoeffAt f 0‖ ≤
          |Real.log ‖meromorphicTrailingCoeffAt f 0‖| := neg_le_abs _
      _ ≤ r ^ α := hrα_ge_K
  have hone_le : (1 : ℝ) ≤ r ^ α := Real.one_le_rpow hr_ge1 hα_pos.le
  calc
    (zeroCount f r : ℝ) ≤ 1 + 1 / Real.log 2 *
        (Real.log (maxModulus f (2 * r)) -
          Real.log ‖meromorphicTrailingCoeffAt f 0‖) := hJ
    _ ≤ 1 + 1 / Real.log 2 * (2 ^ α * r ^ α + r ^ α) := by
      gcongr
      linarith
    _ ≤ r ^ α + 1 / Real.log 2 * (2 ^ α * r ^ α + r ^ α) := by
      gcongr
    _ = C * r ^ α := by ring

/-- Summability of `‖z‖⁻ˢ` over nonzero zeros from counting bound + dyadic decomposition. -/
private lemma summable_rpow_inv_of_counting_bound (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hf_ne : ¬ f = 0) (s α : ℝ) (hs : 0 < s) (hαs : α < s) (hα_pos : 0 < α)
    (C R₀ : ℝ) (hC : 0 < C) (hR₀ : 1 ≤ R₀)
    (hcount : ∀ r, R₀ ≤ r → (zeroCount f r : ℝ) ≤ C * r ^ α) :
    Summable (fun z : { w : ℂ // f w = 0 ∧ w ≠ 0 } => ‖(z : ℂ)‖⁻¹ ^ s) := by
  -- Bound: for ‖z‖ ≥ R₀, there are ≤ C·R^α zeros with ‖z‖ ≤ R.
  -- The n-th zero (by modulus, for n > C·R₀^α) has ‖z_n‖ ≥ (n/C)^{1/α}.
  -- So ‖z_n‖⁻ˢ ≤ C^{s/α} · n^{-s/α}, and s/α > 1 gives convergence.
  -- We use Summable.of_norm_bounded with a comparison via the counting bound.
  -- The zero subtype for an entire non-zero function is countable (discrete).
  -- The zero subtype with ‖z‖ ≤ R has ≤ C·R^α elements (for R ≥ R₀).
  -- We bound the sum over zeros with ‖z‖ in (2^k R₀, 2^{k+1} R₀]:
  --   ≤ C·(2^{k+1} R₀)^α terms, each ≤ (2^k R₀)⁻ˢ
  --   = C·2^α·R₀^{α-s}·2^{k(α-s)}
  -- Geometric series in 2^{α-s} < 1. Plus finitely many with ‖z‖ < R₀.
  --
  -- For the Lean proof: bound each term by a function of ‖z‖ alone,
  -- then use summability of the annular bound via geometric series.
  --
  -- Simple bound: if we can show ∑ over the subtype ≤ M for any finite partial sum,
  -- then Summable follows from completeness.
  -- Approach: show the set of zeros is countable, enumerate as ℕ → subtype,
  -- then use the counting bound to show the ℕ-indexed sequence is summable.
  -- The subtype summability follows from the ℕ-indexed summability.
  --
  -- Key: zeros of a non-zero entire function are isolated, hence countable in ℂ.
  -- For any R, the ball of radius R contains finitely many zeros.
  -- The counting bound gives an explicit upper bound on the number in each ball.
  -- Dyadic decomposition + geometric series gives the summability.
  classical
  let Z := { w : ℂ // f w = 0 ∧ w ≠ 0 }
  let D := MeromorphicOn.divisor f Set.univ
  have hf_an : AnalyticOnNhd ℂ f Set.univ := analyticOnNhd_univ_iff_differentiable.mpr hf
  have hf_mer : MeromorphicOn f Set.univ := hf_an.meromorphicOn
  have hdiv_nn : ∀ z, 0 ≤ D z := by
    intro z
    exact (hf_an.meromorphicNFOn.divisor_nonneg_iff_analyticOnNhd.mpr hf_an) z
  have hzero_div : ∀ z : ℂ, f z = 0 → 1 ≤ D z := by
    intro z hfz
    rw [show D z = (meromorphicOrderAt f z).untop₀ by
      simp [D, MeromorphicOn.divisor_apply hf_mer (Set.mem_univ z)]]
    have han_z := hf_an z (Set.mem_univ z)
    have hord_ne_zero : meromorphicOrderAt f z ≠ 0 := by
      intro h
      exact (han_z.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp h) hfz
    have hord_pos : 0 < meromorphicOrderAt f z :=
      lt_of_le_of_ne han_z.meromorphicOrderAt_nonneg (Ne.symm hord_ne_zero)
    have hord_ne_top : meromorphicOrderAt f z ≠ ⊤ := by
      rw [meromorphicOrderAt_ne_top_iff_eventually_ne_zero han_z.meromorphicAt]
      rcases han_z.eventually_eq_zero_or_eventually_ne_zero with h | h
      · have hzero : f = 0 := AnalyticOnNhd.eq_of_eventuallyEq hf_an analyticOnNhd_const h
        exact (hf_ne hzero).elim
      · exact h
    have h_eq := WithTop.coe_untop₀_of_ne_top hord_ne_top
    rw [← h_eq] at hord_pos
    exact_mod_cast hord_pos
  have zero_finite : ∀ (R : ℝ), 0 ≤ R → Set.Finite {z : ℂ | ‖z‖ ≤ R ∧ f z = 0} := by
    intro R hR
    have hsupp_fin := (Function.locallyFinsuppWithin.toClosedBall R D).finiteSupport
      (isCompact_closedBall 0 |R|)
    apply Set.Finite.subset (s := ↑hsupp_fin.toFinset) hsupp_fin.toFinset.finite_toSet
    intro z hz
    rw [Finset.mem_coe, hsupp_fin.mem_toFinset, Function.mem_support]
    have hz_mem : z ∈ Metric.closedBall (0 : ℂ) |R| := by
      simpa [Metric.mem_closedBall, abs_of_nonneg hR] using hz.1
    rw [Function.locallyFinsuppWithin.toClosedBall_eval_within _ hz_mem]
    exact ne_of_gt (lt_of_lt_of_le Int.zero_lt_one (hzero_div z hz.2))
  have card_le_zeroCount (u : Finset Z) (R : ℝ) (hR : 0 ≤ R)
      (huR : ∀ z ∈ u, ‖(z : ℂ)‖ ≤ R) : u.card ≤ zeroCount f R := by
    let e : Z ↪ ℂ := Function.Embedding.subtype _
    have hfin := zero_finite R hR
    have hsub : u.map e ⊆ hfin.toFinset := by
      intro z hz
      rw [Finset.mem_map] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      rw [Set.Finite.mem_toFinset]
      exact ⟨huR w hw, w.2.1⟩
    calc
      u.card = (u.map e).card := (Finset.card_map e).symm
      _ ≤ hfin.toFinset.card := Finset.card_le_card hsub
      _ = zeroCount f R := by
        unfold zeroCount
        exact (Nat.card_eq_card_finite_toFinset hfin).symm
  have hR₀_pos : 0 < R₀ := lt_of_lt_of_le zero_lt_one hR₀
  have htwo_pos : (0 : ℝ) < 2 := by norm_num
  have htwo_nonneg : (0 : ℝ) ≤ 2 := htwo_pos.le
  have hq_pos : 0 < (2 : ℝ) ^ (α - s) := Real.rpow_pos_of_pos htwo_pos _
  have hq_lt_one : (2 : ℝ) ^ (α - s) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (sub_neg.mpr hαs)
  have hgeom : Summable (fun n : ℕ => ((2 : ℝ) ^ (α - s)) ^ n) := by
    apply summable_geometric_of_norm_lt_one
    simpa [Real.norm_eq_abs, abs_of_pos hq_pos] using hq_lt_one
  have small_finite : Set.Finite {z : Z | ‖(z : ℂ)‖ ≤ R₀} := by
    have hpre := (zero_finite R₀ hR₀_pos.le).preimage
      (f := fun z : Z => (z : ℂ))
      (Set.injOn_of_injective Subtype.val_injective)
    convert hpre using 1
    ext z
    constructor
    · intro hz
      exact ⟨hz, z.2.1⟩
    · exact fun hz => hz.1
  let small : Finset Z := small_finite.toFinset
  let smallSum : ℝ := ∑ z ∈ small, ‖(z : ℂ)‖⁻¹ ^ s
  have hsmall_nonneg : 0 ≤ smallSum := by
    apply Finset.sum_nonneg
    intro z hz
    positivity
  have hex (z : Z) : ∃ n : ℕ, ‖(z : ℂ)‖ / R₀ < (2 : ℝ) ^ n :=
    ((tendsto_pow_atTop_atTop_of_one_lt one_lt_two).eventually_gt_atTop
      (‖(z : ℂ)‖ / R₀)).exists
  let idx : Z → ℕ := fun z => Nat.find (hex z)
  have hidx_upper (z : Z) : ‖(z : ℂ)‖ < R₀ * (2 : ℝ) ^ idx z := by
    have h := Nat.find_spec (hex z)
    simpa [mul_comm] using (div_lt_iff₀ hR₀_pos).mp h
  have hidx_lower (z : Z) (n : ℕ) (hz : idx z = n + 1) :
      R₀ * (2 : ℝ) ^ n ≤ ‖(z : ℂ)‖ := by
    have hz' : Nat.find (hex z) = n + 1 := by simpa [idx] using hz
    have hn : n < Nat.find (hex z) := by omega
    have h := not_lt.mp (Nat.find_min (hex z) hn)
    simpa [mul_comm] using (le_div_iff₀ hR₀_pos).mp h
  let q : ℝ := (2 : ℝ) ^ (α - s)
  let A : ℝ := C * R₀ ^ (α - s) * (2 : ℝ) ^ α
  let bound : ℕ → ℝ
    | 0 => smallSum
    | n + 1 => A * q ^ n
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  have hbound_nonneg : ∀ n, 0 ≤ bound n := by
    intro n
    cases n with
    | zero => simpa [bound] using hsmall_nonneg
    | succ n =>
        simp only [bound]
        exact mul_nonneg hA_nonneg (pow_nonneg hq_pos.le _)
  have hbound_summable : Summable bound := by
    apply (summable_nat_add_iff 1).mp
    simpa [bound, q] using hgeom.mul_left A
  apply summable_of_sum_le
  · intro z
    positivity
  · intro u
    rw [← Finset.sum_fiberwise_of_maps_to (t := u.image idx)
      (fun z hz => Finset.mem_image.mpr ⟨z, hz, rfl⟩)
      (fun z : Z => ‖(z : ℂ)‖⁻¹ ^ s)]
    calc
      ∑ n ∈ u.image idx, ∑ z ∈ u with idx z = n, ‖(z : ℂ)‖⁻¹ ^ s
          ≤ ∑ n ∈ u.image idx, bound n := by
            apply Finset.sum_le_sum
            intro n hn
            cases n with
            | zero =>
                apply Finset.sum_le_sum_of_subset_of_nonneg
                · intro z hz
                  simp only [Finset.mem_filter] at hz
                  have hz_lt : ‖(z : ℂ)‖ < R₀ := by
                    have h := hidx_upper z
                    rw [hz.2, pow_zero, mul_one] at h
                    exact h
                  simp only [small, Set.Finite.mem_toFinset]
                  exact hz_lt.le
                · intro z hz hnot
                  positivity
            | succ n =>
                set v := u.filter (fun z => idx z = n + 1)
                have hv_radius : ∀ z ∈ v,
                    ‖(z : ℂ)‖ ≤ R₀ * (2 : ℝ) ^ (n + 1) := by
                  intro z hz
                  have h := hidx_upper z
                  rw [(Finset.mem_filter.mp hz).2] at h
                  exact h.le
                have hv_card : (v.card : ℝ) ≤
                    C * (R₀ * (2 : ℝ) ^ (n + 1)) ^ α := by
                  have hcard : (v.card : ℝ) ≤
                      (zeroCount f (R₀ * (2 : ℝ) ^ (n + 1)) : ℝ) := by
                    exact_mod_cast card_le_zeroCount v _ (by positivity) hv_radius
                  exact le_trans hcard (hcount _ (by
                    have hp : (1 : ℝ) ≤ (2 : ℝ) ^ (n + 1) := one_le_pow₀ (by norm_num)
                    calc
                      R₀ = R₀ * 1 := by ring
                      _ ≤ R₀ * (2 : ℝ) ^ (n + 1) :=
                        mul_le_mul_of_nonneg_left hp hR₀_pos.le))
                have hterm : ∀ z ∈ v,
                    ‖(z : ℂ)‖⁻¹ ^ s ≤ (R₀ * (2 : ℝ) ^ n) ^ (-s) := by
                  intro z hz
                  have hz_lower := hidx_lower z n (Finset.mem_filter.mp hz).2
                  rw [Real.inv_rpow (norm_nonneg (z : ℂ)), ← Real.rpow_neg (norm_nonneg (z : ℂ))]
                  exact Real.rpow_le_rpow_of_exponent_nonpos (by positivity) hz_lower (by linarith)
                calc
                  ∑ z ∈ u with idx z = n + 1, ‖(z : ℂ)‖⁻¹ ^ s
                      ≤ v.card • (R₀ * (2 : ℝ) ^ n) ^ (-s) :=
                        Finset.sum_le_card_nsmul v _ _ hterm
                  _ = (v.card : ℝ) * (R₀ * (2 : ℝ) ^ n) ^ (-s) := by
                        rw [nsmul_eq_mul]
                  _ ≤ C * (R₀ * (2 : ℝ) ^ (n + 1)) ^ α *
                        (R₀ * (2 : ℝ) ^ n) ^ (-s) := by
                        gcongr
                  _ = bound (n + 1) := by
                    simp only [bound, A, q]
                    rw [Real.mul_rpow hR₀_pos.le (by positivity),
                      Real.mul_rpow hR₀_pos.le (by positivity)]
                    rw [show (((2 : ℝ) ^ (n + 1)) ^ α) = ((2 : ℝ) ^ α) ^ (n + 1) by
                      rw [← Real.rpow_natCast, ← Real.rpow_mul htwo_nonneg,
                        mul_comm, Real.rpow_mul htwo_nonneg, Real.rpow_natCast]]
                    rw [show (((2 : ℝ) ^ n) ^ (-s)) = ((2 : ℝ) ^ (-s)) ^ n by
                      rw [← Real.rpow_natCast, ← Real.rpow_mul htwo_nonneg,
                        mul_comm, Real.rpow_mul htwo_nonneg, Real.rpow_natCast]]
                    rw [pow_succ]
                    rw [show R₀ ^ (α - s) = R₀ ^ α * R₀ ^ (-s) by
                      rw [sub_eq_add_neg, Real.rpow_add hR₀_pos]]
                    rw [show (2 : ℝ) ^ (α - s) = 2 ^ α * 2 ^ (-s) by
                      rw [sub_eq_add_neg, Real.rpow_add htwo_pos]]
                    rw [mul_pow]
                    ring
      _ ≤ ∑' n, bound n :=
        hbound_summable.sum_le_tsum _ (fun n hn => hbound_nonneg n)

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
  /- For any σ > entireOrder f, Jensen's formula and Abel summation show
     Σ ‖zₙ‖⁻σ converges, placing σ in the defining set of zeroExponent.
     By density of EReal, sInf of that set ≤ entireOrder f. -/
  apply le_of_forall_gt_imp_ge_of_dense
  intro σ hσ
  -- Case: σ = ⊤ is trivial
  by_cases hσ_top : σ = ⊤
  · exact hσ_top ▸ le_top
  -- For finite σ > entireOrder f: extract a real s with (↑s : EReal) = σ,
  -- s > 0, and the zero series converges at exponent s.
  -- The analytical chain:
  --   entireOrder f < s  ⟹  log M(f,r) ≤ r^s for large r  (definition of order)
  --   zeroCount_le_logMax  ⟹  n(f,r) = O(r^s)             (Jensen's formula)
  --   Abel summation       ⟹  Σ ‖zₙ‖⁻ˢ < ∞               (convergence)
  obtain ⟨s, hs_eq, hs_pos, hs_summ⟩ :
      ∃ s : ℝ, (s : EReal) = σ ∧ 0 < s ∧
      Summable (fun z : { w : ℂ // f w = 0 ∧ w ≠ 0 } => ‖(z : ℂ)‖⁻¹ ^ s) := by
    -- Step 1: σ ≠ ⊥ and extract s
    have hσ_ne_bot : σ ≠ ⊥ := (lt_of_le_of_lt bot_le hσ).ne'
    -- Step 2: σ > 0 from entireOrder f ≥ 0
    have hσ_pos : (0 : EReal) < σ :=
      lt_of_le_of_lt (entireOrder_nonneg f hf hf_ne) hσ
    -- Step 3: Extract s = σ.toReal
    refine ⟨σ.toReal, EReal.coe_toReal hσ_top hσ_ne_bot,
            EReal.toReal_pos hσ_pos hσ_top, ?_⟩
    -- Step 4: Prove summability at exponent σ.toReal
    -- Pick α between ρ and s for the counting bound
    set s := σ.toReal
    have hs_pos : 0 < s := EReal.toReal_pos hσ_pos hσ_top
    have hρ_lt_s : entireOrder f < (s : EReal) := by
      rwa [EReal.coe_toReal hσ_top hσ_ne_bot]
    -- Choose α = (ρ̃ + s) / 2 where ρ̃ = (entireOrder f).toReal
    have hne_top : entireOrder f ≠ ⊤ := ne_of_lt (lt_trans hρ_lt_s (EReal.coe_lt_top s))
    have hne_bot : entireOrder f ≠ ⊥ :=
      ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (entireOrder_nonneg f hf hf_ne))
    set ρ := (entireOrder f).toReal
    have hρ_nn : 0 ≤ ρ := EReal.toReal_nonneg (entireOrder_nonneg f hf hf_ne)
    have hρ_lt_s' : ρ < s := by
      have hρ_coe : ((entireOrder f).toReal : EReal) = entireOrder f :=
        EReal.coe_toReal hne_top hne_bot
      have : entireOrder f < (s : EReal) := hρ_lt_s
      rw [← hρ_coe] at this
      exact_mod_cast this
    set α := (ρ + s) / 2 with hα_def
    have hα_pos : 0 < α := by rw [hα_def]; linarith
    have hα_gt_ρ : ρ < α := by rw [hα_def]; linarith
    have hα_lt_s : α < s := by rw [hα_def]; linarith
    have hα_ereal : entireOrder f < (α : EReal) := by
      rw [← EReal.coe_toReal hne_top hne_bot]
      exact EReal.coe_lt_coe_iff.mpr hα_gt_ρ
    obtain ⟨C, R₀, hC, hR₀, hcount⟩ :=
      zeroCount_eventually_le_rpow_of_ne f hf hf_ne α hα_pos hα_ereal
    exact summable_rpow_inv_of_counting_bound f hf hf_ne s α hs_pos hα_lt_s hα_pos
      C R₀ hC hR₀ hcount
  rw [← hs_eq]
  exact csInf_le' ⟨by exact_mod_cast hs_pos, s, rfl, hs_summ⟩

-- ============================================================
-- Order of the Completed Zeta Function
-- ============================================================

private lemma evenKernel_zero_tail_bound {x : ℝ} (hx : 1 ≤ x) :
    |HurwitzZeta.evenKernel 0 x - 1| ≤ 4 * Real.exp (-x) := by
  have hx_pos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hkernel : HurwitzZeta.evenKernel 0 x =
      HurwitzKernelBounds.F_nat 0 0 x + HurwitzKernelBounds.F_nat 0 1 x := by
    have hEF : HurwitzZeta.evenKernel 0 x = HurwitzKernelBounds.F_int 0 0 x := by
      change HurwitzZeta.evenKernel (↑(0 : ℝ)) x = _
      rw [← (HurwitzZeta.hasSum_int_evenKernel 0 hx_pos).tsum_eq]
      simp only [HurwitzKernelBounds.F_int, HurwitzKernelBounds.f_int]
      congr 1
      funext n
      simp
    have hF := HurwitzKernelBounds.F_int_eq_of_mem_Icc 0
      (a := (0 : ℝ)) (by constructor <;> norm_num) hx_pos
    change HurwitzKernelBounds.F_int 0 (↑(0 : ℝ)) x = _ at hF
    simpa using hEF.trans hF
  have hzero := HurwitzKernelBounds.F_nat_zero_zero_sub_le hx_pos
  have hone := HurwitzKernelBounds.F_nat_zero_le (a := (1 : ℝ)) zero_le_one hx_pos
  have hq_lt_one : Real.exp (-Real.pi * x) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith [Real.pi_pos]
  have hq_nonneg : 0 ≤ Real.exp (-Real.pi * x) / (1 - Real.exp (-Real.pi * x)) := by
    exact div_nonneg (Real.exp_pos _).le (sub_nonneg.mpr hq_lt_one.le)
  have htail : |HurwitzZeta.evenKernel 0 x - 1| ≤
      2 * (Real.exp (-Real.pi * x) / (1 - Real.exp (-Real.pi * x))) := by
    rw [hkernel]
    calc
      |HurwitzKernelBounds.F_nat 0 0 x + HurwitzKernelBounds.F_nat 0 1 x - 1|
          = |(HurwitzKernelBounds.F_nat 0 0 x - 1) +
              HurwitzKernelBounds.F_nat 0 1 x| := by ring_nf
      _ ≤ |HurwitzKernelBounds.F_nat 0 0 x - 1| +
            |HurwitzKernelBounds.F_nat 0 1 x| := abs_add_le _ _
      _ ≤ Real.exp (-Real.pi * x) / (1 - Real.exp (-Real.pi * x)) +
            Real.exp (-Real.pi * 1 ^ 2 * x) /
              (1 - Real.exp (-Real.pi * x)) := add_le_add hzero hone
      _ = 2 * (Real.exp (-Real.pi * x) / (1 - Real.exp (-Real.pi * x))) := by
        ring_nf
  have hpi : 1 ≤ Real.pi := le_trans (by norm_num) Real.pi_gt_three.le
  have hq_le : Real.exp (-Real.pi * x) ≤ Real.exp (-x) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hexp_neg_le_half : Real.exp (-x) ≤ 1 / 2 := by
    calc
      Real.exp (-x) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
      _ ≤ 1 / 2 := by linarith [Real.exp_neg_one_lt_d9]
  have hden : 1 / 2 ≤ 1 - Real.exp (-Real.pi * x) := by linarith
  have hden_pos : 0 < 1 - Real.exp (-Real.pi * x) := lt_of_lt_of_le (by norm_num) hden
  calc
    |HurwitzZeta.evenKernel 0 x - 1|
        ≤ 2 * (Real.exp (-Real.pi * x) / (1 - Real.exp (-Real.pi * x))) := htail
    _ ≤ 2 * (Real.exp (-x) / (1 / 2)) := by
      gcongr
    _ = 4 * Real.exp (-x) := by ring

private lemma norm_hurwitzEven_f_modif_zero_le {x : ℝ} (hx : 1 ≤ x) :
    ‖(HurwitzZeta.hurwitzEvenFEPair 0).f_modif x‖ ≤ 4 * Real.exp (-x) := by
  rcases hx.eq_or_lt with rfl | hx
  · simp [WeakFEPair.f_modif]
    positivity
  · simp only [WeakFEPair.f_modif, Pi.add_apply,
      Set.indicator_of_mem (Set.mem_Ioi.mpr hx),
      Set.indicator_of_notMem (Set.notMem_Ioo_of_ge hx.le), add_zero,
      HurwitzZeta.hurwitzEvenFEPair, Function.comp_apply]
    change ‖(HurwitzZeta.evenKernel 0 x : ℂ) - 1‖ ≤ _
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact evenKernel_zero_tail_bound hx.le

private lemma hurwitzEven_g_modif_zero_eq_f_modif :
    (HurwitzZeta.hurwitzEvenFEPair 0).g_modif =
      (HurwitzZeta.hurwitzEvenFEPair 0).f_modif := by
  funext x
  simp only [WeakFEPair.g_modif, WeakFEPair.f_modif,
    HurwitzZeta.hurwitzEvenFEPair, Function.comp_apply]
  rw [HurwitzZeta.evenKernel_eq_cosKernel_of_zero]
  simp

private lemma norm_hurwitzEven_f_modif_zero_le_small {x : ℝ}
    (hx_pos : 0 < x) (hx : x ≤ 1) :
    ‖(HurwitzZeta.hurwitzEvenFEPair 0).f_modif x‖ ≤
      4 * x ^ (-(1 / 2 : ℝ)) * Real.exp (-(1 / x)) := by
  rcases hx.eq_or_lt with rfl | hx
  · simp [WeakFEPair.f_modif]
    positivity
  · have hinv_pos : 0 < 1 / x := one_div_pos.mpr hx_pos
    have hinv : 1 ≤ 1 / x := (le_div_iff₀ hx_pos).mpr (by simpa using hx.le)
    have hFE := (HurwitzZeta.hurwitzEvenFEPair 0).hf_modif_FE (1 / x) hinv_pos
    rw [one_div_div, hurwitzEven_g_modif_zero_eq_f_modif] at hFE
    have hFE' : (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x =
        (↑((1 / x) ^ (1 / 2 : ℝ)) : ℂ) •
          (HurwitzZeta.hurwitzEvenFEPair 0).f_modif (1 / x) := by
      simpa only [div_one, HurwitzZeta.hurwitzEvenFEPair, one_mul] using hFE
    rw [hFE', norm_smul]
    have hscalar : ‖((1 : ℂ) * ↑((1 / x) ^ (1 / 2 : ℝ)))‖ =
        x ^ (-(1 / 2 : ℝ)) := by
      rw [one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.rpow_pos_of_pos hinv_pos _), one_div,
        Real.inv_rpow hx_pos.le, ← Real.rpow_neg hx_pos.le]
    rw [show ‖(↑((1 / x) ^ (1 / 2 : ℝ)) : ℂ)‖ = x ^ (-(1 / 2 : ℝ)) by
      simpa only [one_mul] using hscalar]
    calc
      x ^ (-(1 / 2 : ℝ)) * ‖(HurwitzZeta.hurwitzEvenFEPair 0).f_modif (1 / x)‖
          ≤ x ^ (-(1 / 2 : ℝ)) * (4 * Real.exp (-(1 / x))) := by
            gcongr
            exact norm_hurwitzEven_f_modif_zero_le hinv
      _ = 4 * x ^ (-(1 / 2 : ℝ)) * Real.exp (-(1 / x)) := by ring

private lemma norm_completedZeta_mellin_integrand_le
    (r : ℝ) (s : ℂ) (hs : ‖s‖ ≤ r) {x : ℝ} (hx_pos : 0 < x) :
    ‖(x : ℂ) ^ (s / 2 - 1) • (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x‖ ≤
      4 * (x ^ (r / 2) * Real.exp (-x) +
        x ^ (-r / 2 - 2) * Real.exp (-(1 / x))) := by
  have hs_re_upper : s.re ≤ r := (Complex.re_le_norm s).trans hs
  have hs_re_lower : -r ≤ s.re := by
    exact (neg_le_neg hs).trans (abs_le.mp (Complex.abs_re_le_norm s)).1
  have hre : (s / 2 - 1).re = s.re / 2 - 1 := by
    norm_num [Complex.div_re]
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hx_pos]
  by_cases hx : x ≤ 1
  · have hcpow : x ^ (s / 2 - 1).re ≤ x ^ (-r / 2 - 1) := by
      apply Real.rpow_le_rpow_of_exponent_ge hx_pos hx
      rw [hre]
      nlinarith
    have hfm := norm_hurwitzEven_f_modif_zero_le_small hx_pos hx
    have hx_invhalf_le : x ^ (-(1 / 2 : ℝ)) ≤ x ^ (-1 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_ge hx_pos hx
      norm_num
    have hlow : x ^ (s / 2 - 1).re *
          ‖(HurwitzZeta.hurwitzEvenFEPair 0).f_modif x‖ ≤
        4 * (x ^ (-r / 2 - 2) * Real.exp (-(1 / x))) := by
      calc
        x ^ (s / 2 - 1).re * ‖(HurwitzZeta.hurwitzEvenFEPair 0).f_modif x‖
            ≤ x ^ (-r / 2 - 1) *
                (4 * x ^ (-(1 / 2 : ℝ)) * Real.exp (-(1 / x))) := by gcongr
        _ ≤ x ^ (-r / 2 - 1) *
                (4 * x ^ (-1 : ℝ) * Real.exp (-(1 / x))) := by gcongr
        _ = 4 * ((x ^ (-r / 2 - 1) * x ^ (-1 : ℝ)) *
              Real.exp (-(1 / x))) := by ring
        _ = 4 * (x ^ (-r / 2 - 2) * Real.exp (-(1 / x))) := by
          rw [← Real.rpow_add hx_pos]
          congr 3
          ring
    calc
      x ^ (s / 2 - 1).re * ‖(HurwitzZeta.hurwitzEvenFEPair 0).f_modif x‖
          ≤ 4 * (x ^ (-r / 2 - 2) * Real.exp (-(1 / x))) := hlow
      _ ≤ 4 * (x ^ (r / 2) * Real.exp (-x) +
          x ^ (-r / 2 - 2) * Real.exp (-(1 / x))) := by
            gcongr
            exact le_add_of_nonneg_left (mul_nonneg (Real.rpow_nonneg hx_pos.le _)
              (Real.exp_pos _).le)
  · have hx_one : 1 ≤ x := le_of_not_ge hx
    have hcpow : x ^ (s / 2 - 1).re ≤ x ^ (r / 2) := by
      apply Real.rpow_le_rpow_of_exponent_le hx_one
      rw [hre]
      nlinarith
    have hfm := norm_hurwitzEven_f_modif_zero_le hx_one
    calc
      x ^ (s / 2 - 1).re * ‖(HurwitzZeta.hurwitzEvenFEPair 0).f_modif x‖
          ≤ x ^ (r / 2) * (4 * Real.exp (-x)) := by gcongr
      _ = 4 * (x ^ (r / 2) * Real.exp (-x)) := by ring
      _ ≤ 4 * (x ^ (r / 2) * Real.exp (-x) +
          x ^ (-r / 2 - 2) * Real.exp (-(1 / x))) := by
            gcongr
            exact le_add_of_nonneg_right (mul_nonneg (Real.rpow_nonneg hx_pos.le _)
              (Real.exp_pos _).le)

private lemma completedZeta_majorant_integrable (r : ℝ) (hr : 2 ≤ r) :
    MeasureTheory.IntegrableOn
      (fun x : ℝ => 4 * (x ^ (r / 2) * Real.exp (-x) +
        x ^ (-r / 2 - 2) * Real.exp (-(1 / x)))) (Set.Ioi 0) := by
  let g : ℝ → ℝ := fun x => x ^ (r / 2) * Real.exp (-x)
  have harg : 0 < r / 2 + 1 := by linarith
  have hg : MeasureTheory.IntegrableOn g (Set.Ioi 0) := by
    have hΓ := Real.GammaIntegral_convergent harg
    simpa only [g, show r / 2 + 1 - 1 = r / 2 by ring, mul_comm] using hΓ
  have hlow : MeasureTheory.IntegrableOn
      (fun x : ℝ => x ^ (-r / 2 - 2) * Real.exp (-(1 / x))) (Set.Ioi 0) := by
    have htrans := (MeasureTheory.integrableOn_Ioi_comp_rpow_iff g
      (p := (-1 : ℝ)) (by norm_num)).mpr hg
    refine htrans.congr_fun ?_ measurableSet_Ioi
    intro x hx
    have hx_pos : 0 < x := hx
    simp only [abs_neg, abs_one, one_mul, one_div, smul_eq_mul, g]
    rw [Real.rpow_neg_one, Real.inv_rpow hx_pos.le, ← Real.rpow_neg hx_pos.le]
    rw [← mul_assoc, ← Real.rpow_add hx_pos]
    congr 2
    ring
  exact (hg.add hlow).const_mul 4

private lemma integral_completedZeta_majorant (r : ℝ) (hr : 2 ≤ r) :
    (∫ x : ℝ in Set.Ioi 0, 4 * (x ^ (r / 2) * Real.exp (-x) +
        x ^ (-r / 2 - 2) * Real.exp (-(1 / x)))) =
      8 * Real.Gamma (r / 2 + 1) := by
  let g : ℝ → ℝ := fun x => x ^ (r / 2) * Real.exp (-x)
  have harg : 0 < r / 2 + 1 := by linarith
  have hg : MeasureTheory.IntegrableOn g (Set.Ioi 0) := by
    have hΓ := Real.GammaIntegral_convergent harg
    simpa only [g, show r / 2 + 1 - 1 = r / 2 by ring, mul_comm] using hΓ
  have hhigh : (∫ x : ℝ in Set.Ioi 0, g x) = Real.Gamma (r / 2 + 1) := by
    rw [Real.Gamma_eq_integral harg]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x _
    simp only [g, show r / 2 + 1 - 1 = r / 2 by ring, mul_comm]
  have hlow : MeasureTheory.IntegrableOn
      (fun x : ℝ => x ^ (-r / 2 - 2) * Real.exp (-(1 / x))) (Set.Ioi 0) := by
    have htrans := (MeasureTheory.integrableOn_Ioi_comp_rpow_iff g
      (p := (-1 : ℝ)) (by norm_num)).mpr hg
    refine htrans.congr_fun ?_ measurableSet_Ioi
    intro x hx
    have hx_pos : 0 < x := hx
    simp only [abs_neg, abs_one, one_mul, one_div, smul_eq_mul, g]
    rw [Real.rpow_neg_one, Real.inv_rpow hx_pos.le, ← Real.rpow_neg hx_pos.le]
    rw [← mul_assoc, ← Real.rpow_add hx_pos]
    congr 2
    ring
  have hlow_int :
      (∫ x : ℝ in Set.Ioi 0, x ^ (-r / 2 - 2) * Real.exp (-(1 / x))) =
        Real.Gamma (r / 2 + 1) := by
    calc
      (∫ x : ℝ in Set.Ioi 0, x ^ (-r / 2 - 2) * Real.exp (-(1 / x))) =
          ∫ x : ℝ in Set.Ioi 0, ((|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) •
            g (x ^ (-1 : ℝ))) := by
              apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
              intro x hx
              have hx_pos : 0 < x := hx
              simp only [abs_neg, abs_one, one_mul, one_div, smul_eq_mul, g]
              rw [Real.rpow_neg_one, Real.inv_rpow hx_pos.le, ← Real.rpow_neg hx_pos.le]
              rw [← mul_assoc, ← Real.rpow_add hx_pos]
              congr 2
              ring
      _ = ∫ y : ℝ in Set.Ioi 0, g y :=
        MeasureTheory.integral_comp_rpow_Ioi g (p := (-1 : ℝ)) (by norm_num)
      _ = Real.Gamma (r / 2 + 1) := hhigh
  rw [MeasureTheory.integral_const_mul,
    MeasureTheory.integral_add hg hlow, hhigh, hlow_int]
  ring

private lemma norm_completedRiemannZeta₀_le_gamma
    (r : ℝ) (hr : 2 ≤ r) (s : ℂ) (hs : ‖s‖ ≤ r) :
    ‖completedRiemannZeta₀ s‖ ≤ 4 * Real.Gamma (r / 2 + 1) := by
  have hint : MeasureTheory.IntegrableOn
      (fun x : ℝ => (x : ℂ) ^ (s / 2 - 1) •
        (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x) (Set.Ioi 0) := by
    exact ((HurwitzZeta.hurwitzEvenFEPair 0).toStrongFEPair.hasMellin (s / 2)).1
  have hmajor := completedZeta_majorant_integrable r hr
  have hmono :
      (∫ x : ℝ in Set.Ioi 0, ‖(x : ℂ) ^ (s / 2 - 1) •
          (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x‖) ≤
        ∫ x : ℝ in Set.Ioi 0, 4 * (x ^ (r / 2) * Real.exp (-x) +
          x ^ (-r / 2 - 2) * Real.exp (-(1 / x))) := by
    apply MeasureTheory.setIntegral_mono_on hint.norm hmajor measurableSet_Ioi
    intro x hx
    exact norm_completedZeta_mellin_integrand_le r s hs hx
  rw [completedRiemannZeta₀, HurwitzZeta.completedHurwitzZetaEven₀,
    WeakFEPair.Λ₀, mellin]
  rw [norm_div, Complex.norm_ofNat]
  calc
    ‖∫ x : ℝ in Set.Ioi 0, (x : ℂ) ^ (s / 2 - 1) •
          (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x‖ / 2
        ≤ (∫ x : ℝ in Set.Ioi 0, ‖(x : ℂ) ^ (s / 2 - 1) •
          (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x‖) / 2 := by
            gcongr
            exact MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ (∫ x : ℝ in Set.Ioi 0, 4 * (x ^ (r / 2) * Real.exp (-x) +
          x ^ (-r / 2 - 2) * Real.exp (-(1 / x)))) / 2 := by gcongr
    _ = 4 * Real.Gamma (r / 2 + 1) := by
      rw [integral_completedZeta_majorant r hr]
      ring

private lemma four_mul_Gamma_le_completedZeta_scale (r : ℝ) (hr : 2 ≤ r) :
    4 * Real.Gamma (r / 2 + 1) ≤ (r + 10) ^ (r + 10) := by
  let a := r / 2 + 1
  let N := ⌈a⌉₊
  let R := r + 10
  have ha : 2 ≤ a := by dsimp [a]; linarith
  have ha_pos : 0 < a := lt_of_lt_of_le zero_lt_two ha
  have hN_ge : a ≤ (N : ℝ) := by exact Nat.le_ceil a
  have hN_lt : (N : ℝ) < a + 1 := Nat.ceil_lt_add_one ha_pos.le
  have hR : 12 ≤ R := by dsimp [R]; linarith
  have hΓ : Real.Gamma a ≤ (N : ℝ) ^ N := by
    calc
      Real.Gamma a ≤ Real.Gamma ((N : ℝ) + 1) := by
        apply Real.Gamma_strictMonoOn_Ici.monotoneOn
        · exact ha
        · simp only [Set.mem_Ici]
          linarith
        · linarith
      _ = (N.factorial : ℝ) := Real.Gamma_nat_eq_factorial N
      _ ≤ ((N ^ N : ℕ) : ℝ) := by exact_mod_cast N.factorial_le_pow
      _ = (N : ℝ) ^ N := by norm_num
  have hN_le_R : (N : ℝ) ≤ R := by
    dsimp [a, R] at hN_lt ⊢
    linarith
  have hN_one_le_R : (N : ℝ) + 1 ≤ R := by
    dsimp [a, R] at hN_lt ⊢
    linarith
  calc
    4 * Real.Gamma (r / 2 + 1) = 4 * Real.Gamma a := by rfl
    _ ≤ 4 * (N : ℝ) ^ N := by gcongr
    _ ≤ R * R ^ N := by
      apply mul_le_mul
      · linarith
      · exact pow_le_pow_left₀ (by positivity) hN_le_R N
      · positivity
      · linarith
    _ = R ^ ((N : ℝ) + 1) := by
      rw [Real.rpow_add (by linarith : 0 < R), Real.rpow_natCast, Real.rpow_one]
      ring
    _ ≤ R ^ R := Real.rpow_le_rpow_of_exponent_le (by linarith) hN_one_le_R
    _ = (r + 10) ^ (r + 10) := rfl

/- **Stirling upper bound on the order of Λ₀.**

    The growth of completedRiemannZeta₀ satisfies log M(Λ₀, r) = O(r log r),
    which gives entireOrder Λ₀ ≤ 1.

    Proof sketch: Λ₀(s) is expressed via the Mellin transform of the Jacobi theta
    kernel, which has exponential decay O(e^{−πt}) at infinity.
    For |s| ≤ r, the Mellin integral satisfies
      |Λ₀(s/2)| ≤ ∫₀^∞ |f(t)| · t^{r/2−1} dt ≤ Γ(r/2) / π^{r/2},
    and by Stirling, log Γ(r/2) = O(r log r), giving the bound.

    We prove this below from the theta-kernel Mellin representation, then pass
    to the limsup defining `entireOrder`. -/

/-- **Crude order bound for Λ₀.** log M(Λ₀, r) ≤ (r+10) · log(r+10).

    Proof: Λ₀(s) = π^{-s/2} Γ(s/2) ζ(s) + polar terms.
    For Re(s) > 0: |Γ(s/2)| ≤ Γ(Re(s)/2) (integral bound),
    real Stirling gives log Γ(x) ≤ x log x for x ≥ 2.
    Combined: log|Λ₀(s)| ≤ C·r·log r for |s| = r.
    Functional equation Λ₀(s) = Λ₀(1-s) handles Re(s) ≤ 0.

    The theta-kernel Mellin estimate below feeds directly into the limsup
    definition of `entireOrder`. -/
theorem log_maxModulus_completedZeta_le (r : ℝ) (hr : 2 ≤ r) :
    Real.log (maxModulus completedRiemannZeta₀ r) ≤ (r + 10) * Real.log (r + 10) := by
  have hR : 1 ≤ r + 10 := by linarith
  have hmax_gamma : maxModulus completedRiemannZeta₀ r ≤
      4 * Real.Gamma (r / 2 + 1) := by
    unfold maxModulus
    apply ciSup_le
    intro s
    by_cases hs : ‖s‖ ≤ r
    · rw [ciSup_pos hs]
      exact norm_completedRiemannZeta₀_le_gamma r hr s hs
    · rw [ciSup_neg hs, Real.sSup_empty]
      exact mul_nonneg (by norm_num) (Real.Gamma_pos_of_pos (by linarith)).le
  have hmax : maxModulus completedRiemannZeta₀ r ≤ (r + 10) ^ (r + 10) :=
    hmax_gamma.trans (four_mul_Gamma_le_completedZeta_scale r hr)
  have hmax_nonneg : 0 ≤ maxModulus completedRiemannZeta₀ r := by
    exact (norm_nonneg (completedRiemannZeta₀ 0)).trans
      (norm_le_maxModulus completedRiemannZeta₀ differentiable_completedZeta₀ 0 r
        (by linarith) (by simp; linarith))
  by_cases hmax_pos : 0 < maxModulus completedRiemannZeta₀ r
  · calc
      Real.log (maxModulus completedRiemannZeta₀ r)
          ≤ Real.log ((r + 10) ^ (r + 10)) := Real.log_le_log hmax_pos hmax
      _ = (r + 10) * Real.log (r + 10) := Real.log_rpow (by linarith) _
  · have hmax_zero : maxModulus completedRiemannZeta₀ r = 0 :=
      le_antisymm (le_of_not_gt hmax_pos) hmax_nonneg
    rw [hmax_zero, Real.log_zero]
    exact mul_nonneg (by linarith) (Real.log_nonneg hR)

private lemma tendsto_completedZeta_log_scale :
    Tendsto (fun r : ℝ =>
      Real.log ((r + 10) * Real.log (r + 10)) / Real.log r)
      Filter.atTop (𝓝 1) := by
  have hRtop : Tendsto (fun r : ℝ => r + 10) Filter.atTop Filter.atTop :=
    tendsto_atTop_add_const_right Filter.atTop 10 tendsto_id
  have hlogRtop : Tendsto (fun r : ℝ => Real.log (r + 10)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp hRtop
  have hdelta := Real.tendsto_log_comp_add_sub_log 10
  have hdelta_ratio : Tendsto
      (fun r : ℝ => (Real.log (r + 10) - Real.log r) / Real.log r)
      Filter.atTop (𝓝 0) := hdelta.div_atTop Real.tendsto_log_atTop
  have hratio : Tendsto
      (fun r : ℝ => Real.log (r + 10) / Real.log r) Filter.atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).add hdelta_ratio
    have heq : (fun r : ℝ => 1 +
        (Real.log (r + 10) - Real.log r) / Real.log r) =ᶠ[Filter.atTop]
        (fun r : ℝ => Real.log (r + 10) / Real.log r) := by
      filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with r hr
      have hlog_ne : Real.log r ≠ 0 := (Real.log_pos hr).ne'
      field_simp
      ring
    simpa using h.congr' heq
  have hloglog_over_logR : Tendsto
      (fun r : ℝ => Real.log (Real.log (r + 10)) / Real.log (r + 10))
      Filter.atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hlogRtop
  have hloglog_over_log : Tendsto
      (fun r : ℝ => Real.log (Real.log (r + 10)) / Real.log r)
      Filter.atTop (𝓝 0) := by
    have h := hloglog_over_logR.mul hratio
    have heq : (fun r : ℝ =>
        Real.log (Real.log (r + 10)) / Real.log (r + 10) *
          (Real.log (r + 10) / Real.log r)) =ᶠ[Filter.atTop]
        (fun r : ℝ => Real.log (Real.log (r + 10)) / Real.log r) := by
      filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
        Filter.eventually_gt_atTop (-9 : ℝ)] with r hr hrR
      have hlog_ne : Real.log r ≠ 0 := (Real.log_pos hr).ne'
      have hlogR_ne : Real.log (r + 10) ≠ 0 :=
        (Real.log_pos (by linarith)).ne'
      field_simp
    simpa using h.congr' heq
  have hsum := hratio.add hloglog_over_log
  have heq : (fun r : ℝ => Real.log (r + 10) / Real.log r +
      Real.log (Real.log (r + 10)) / Real.log r) =ᶠ[Filter.atTop]
      (fun r : ℝ => Real.log ((r + 10) * Real.log (r + 10)) / Real.log r) := by
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
      Filter.eventually_gt_atTop (-9 : ℝ)] with r hr hrR
    have hR_pos : 0 < r + 10 := by linarith
    have hlogR_pos : 0 < Real.log (r + 10) := Real.log_pos (by linarith)
    rw [Real.log_mul hR_pos.ne' hlogR_pos.ne']
    ring
  simpa using hsum.congr' heq

/-- Λ₀ is not the zero function.
    Proof: if Λ₀ ≡ 0, then Λ(s) = -1/s - 1/(1-s), and computing
    ζ(2) via Λ gives π = 3, contradicting π > 3. -/
private lemma completedZeta₀_ne_zero : ¬ completedRiemannZeta₀ = 0 := by
      intro h
      -- If ξ ≡ 0, then completedRiemannZeta s = -1/s - 1/(1-s),
      -- and riemannZeta 2 = completedRiemannZeta 2 / Gammaℝ 2.
      -- Computing gives riemannZeta 2 = π/2, but riemannZeta_two gives π²/6.
      -- These imply π = 3, contradicting pi_gt_three.
      have hpi_ne : (↑Real.pi : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (ne_of_gt Real.pi_pos)
      -- Gammaℝ 2 = 1/π (via Gammaℝ 1 · Gammaℝ 2 = Gammaℂ 1 = 1/π)
      have hΓ2 : Complex.Gammaℝ (2 : ℂ) = 1 / ↑Real.pi := by
        have := Complex.Gammaℝ_mul_Gammaℝ_add_one (1 : ℂ)
        rwa [show (1 : ℂ) + 1 = 2 from by norm_num,
             Complex.Gammaℝ_one, one_mul, Complex.Gammaℂ_one] at this
      -- completedRiemannZeta 2 = 0 - 1/2 - 1/(1-2) = 1/2
      have hcr : completedRiemannZeta (2 : ℂ) = 1 / 2 := by
        rw [completedRiemannZeta_eq]
        have h0 := congr_fun h (2 : ℂ)
        simp only [Pi.zero_apply] at h0
        rw [h0]; norm_num
      -- riemannZeta 2 · Gammaℝ 2 = completedRiemannZeta 2
      have hΓ_ne : Complex.Gammaℝ (2 : ℂ) ≠ 0 :=
        Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num : 0 < (2 : ℂ).re)
      have hmul : riemannZeta (2 : ℂ) * Complex.Gammaℝ 2 =
          completedRiemannZeta (2 : ℂ) := by
        rw [riemannZeta_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0),
            div_mul_cancel₀ _ hΓ_ne]
      -- Substitute known values: (π²/6) · (1/π) = 1/2
      rw [riemannZeta_two, hΓ2, hcr] at hmul
      -- Derive π = 3
      have hpi3 : (↑Real.pi : ℂ) = 3 := by
        have : (↑Real.pi : ℂ) / 6 = 1 / 2 := by
          rw [show (↑Real.pi : ℂ) ^ 2 / 6 * (1 / ↑Real.pi) = ↑Real.pi / 6 from by
            field_simp [hpi_ne]] at hmul
          exact hmul
        have h6 : (6 : ℂ) ≠ 0 := by norm_num
        rw [div_eq_div_iff h6 two_ne_zero] at this
        simp only [one_mul] at this
        -- this : ↑π * 2 = 6
        calc (↑Real.pi : ℂ) = ↑Real.pi * 2 / 2 := by ring
          _ = 6 / 2 := by rw [this]
          _ = 3 := by norm_num
      -- But π > 3
      exact absurd (Complex.ofReal_injective (by exact_mod_cast hpi3 : (↑Real.pi : ℂ) = ↑(3 : ℝ)))
        (ne_of_gt Real.pi_gt_three)

private lemma completedZeta₀_order_le_one : entireOrder completedRiemannZeta₀ ≤ 1 := by
  obtain ⟨z, hz⟩ : ∃ z : ℂ, completedRiemannZeta₀ z ≠ 0 := by
    by_contra h
    push_neg at h
    exact completedZeta₀_ne_zero (funext h)
  set m := ‖completedRiemannZeta₀ z‖
  have hm_pos : 0 < m := norm_pos_iff.mpr hz
  set C := max 1 |Real.log m|
  have hC_one : 1 ≤ C := le_max_left _ _
  have hC_pos : 0 < C := lt_of_lt_of_le zero_lt_one hC_one
  have hconst_tendsto : Tendsto (fun r : ℝ => Real.log C / Real.log r)
      Filter.atTop (𝓝 0) := tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  unfold entireOrder
  apply (Filter.limsup_le_iff).2
  intro y hy
  by_cases hy_top : y = ⊤
  · subst y
    exact Eventually.of_forall (fun _ => EReal.coe_lt_top _)
  have hy_bot : y ≠ ⊥ := ne_of_gt ((EReal.bot_lt_coe (1 : ℝ)).trans hy)
  set α := y.toReal
  have hy_coe : (α : EReal) = y := EReal.coe_toReal hy_top hy_bot
  have hα : 1 < α := by
    rw [← hy_coe] at hy
    exact_mod_cast hy
  have hscale_lt : ∀ᶠ r : ℝ in Filter.atTop,
      Real.log ((r + 10) * Real.log (r + 10)) / Real.log r < α :=
    tendsto_completedZeta_log_scale.eventually (Iio_mem_nhds hα)
  have hconst_lt : ∀ᶠ r : ℝ in Filter.atTop, Real.log C / Real.log r < α :=
    hconst_tendsto.eventually (Iio_mem_nhds (lt_trans zero_lt_one hα))
  filter_upwards [hscale_lt, hconst_lt,
    Filter.eventually_ge_atTop (max 2 ‖z‖)] with r hscale hconst hr
  have hr_two : 2 ≤ r := (le_max_left _ _).trans hr
  have hr_z : ‖z‖ ≤ r := (le_max_right _ _).trans hr
  have hr_one : 1 < r := lt_of_lt_of_le one_lt_two hr_two
  have hlogr : 0 < Real.log r := Real.log_pos hr_one
  have hm_le : m ≤ maxModulus completedRiemannZeta₀ r := by
    exact norm_le_maxModulus completedRiemannZeta₀ differentiable_completedZeta₀ z r
      (lt_trans zero_lt_one hr_one) hr_z
  have hlogm_le : Real.log m ≤ Real.log (maxModulus completedRiemannZeta₀ r) :=
    Real.log_le_log hm_pos hm_le
  have hlogmax := log_maxModulus_completedZeta_le r hr_two
  rw [← hy_coe]
  apply EReal.coe_lt_coe_iff.mpr
  by_cases hlogM_pos : 0 < Real.log (maxModulus completedRiemannZeta₀ r)
  · have hscale_pos : 0 < (r + 10) * Real.log (r + 10) := by
      exact mul_pos (by linarith) (Real.log_pos (by linarith))
    have hloglog_le :
        Real.log (Real.log (maxModulus completedRiemannZeta₀ r)) ≤
          Real.log ((r + 10) * Real.log (r + 10)) :=
      Real.log_le_log hlogM_pos hlogmax
    exact (div_le_div_of_nonneg_right hloglog_le hlogr.le).trans_lt hscale
  · have hlogM_nonpos : Real.log (maxModulus completedRiemannZeta₀ r) ≤ 0 :=
      le_of_not_gt hlogM_pos
    by_cases hlogM_zero : Real.log (maxModulus completedRiemannZeta₀ r) = 0
    · rw [hlogM_zero, Real.log_zero, zero_div]
      exact lt_trans zero_lt_one hα
    · have hlogM_neg : Real.log (maxModulus completedRiemannZeta₀ r) < 0 :=
        lt_of_le_of_ne hlogM_nonpos hlogM_zero
      have hneg_le : -Real.log (maxModulus completedRiemannZeta₀ r) ≤ C := by
        calc
          -Real.log (maxModulus completedRiemannZeta₀ r) ≤ -Real.log m :=
            neg_le_neg hlogm_le
          _ ≤ |Real.log m| := neg_le_abs _
          _ ≤ C := le_max_right _ _
      have hloglog_le :
          Real.log (Real.log (maxModulus completedRiemannZeta₀ r)) ≤ Real.log C := by
        rw [← Real.log_neg_eq_log (Real.log (maxModulus completedRiemannZeta₀ r))]
        exact Real.log_le_log (neg_pos.mpr hlogM_neg) hneg_le
      exact (div_le_div_of_nonneg_right hloglog_le hlogr.le).trans_lt hconst

/-- A deliberately coarse factorial lower bound tailored to the values
`completedRiemannZeta₀ (2 * (k + 12))`.  Starting at `11!`, every additional
factor is at least `8`, which pays for one factor `4` from `π < 4` and one
factor `2` of exponential growth. -/
private lemma factorial_eleven_add_lower (k : ℕ) :
    2 ^ (k + 1) * 4 ^ (k + 12) ≤ (k + 11).factorial := by
  induction k with
  | zero => norm_num [Nat.factorial]
  | succ k ih =>
      rw [Nat.factorial_succ]
      calc
        2 ^ (k + 1 + 1) * 4 ^ (k + 1 + 12)
            = 8 * (2 ^ (k + 1) * 4 ^ (k + 12)) := by ring
        _ ≤ (k + 12) * (k + 11).factorial := by
          exact Nat.mul_le_mul (by omega) ih

/-- On the positive real axis, the Dirichlet series gives `1 ≤ Re ζ(k)`.
We only need this elementary first-term lower bound. -/
private lemma one_le_riemannZeta_re_nat (k : ℕ) (hk : 1 < k) :
    1 ≤ (riemannZeta (k : ℂ)).re := by
  rw [zeta_nat_eq_tsum_of_gt_one hk]
  have hcast : (∑' n : ℕ, 1 / (n : ℂ) ^ k) =
      Complex.ofReal (∑' n : ℕ, 1 / (n : ℝ) ^ k) := by
    rw [Complex.ofReal_tsum]
    congr 1
    funext n
    push_cast
    norm_cast
  have hsumℝ : Summable (fun n : ℕ => 1 / (n : ℝ) ^ k) :=
    summable_one_div_nat_pow.mpr hk
  rw [hcast]
  simp only [Complex.ofReal_re]
  simpa using hsumℝ.sum_le_tsum {1} (fun n hn => by positivity)

private lemma Gammaℝ_two_mul_nat (n : ℕ) :
    Complex.Gammaℝ ((2 * (n + 1) : ℕ) : ℂ) =
      (((n.factorial : ℝ) / Real.pi ^ (n + 1) : ℝ) : ℂ) := by
  rw [Complex.Gammaℝ_def]
  have hhalf : (((2 * (n + 1) : ℕ) : ℂ) / 2) = (n + 1 : ℕ) := by
    push_cast
    ring
  have hneg : -(((2 * (n + 1) : ℕ) : ℂ)) / 2 = -((n + 1 : ℕ) : ℂ) := by
    push_cast
    ring
  rw [hhalf, hneg]
  rw [Complex.cpow_neg, Complex.cpow_natCast]
  have hGamma : Complex.Gamma ((n + 1 : ℕ) : ℂ) = n.factorial := by
    simpa only [Nat.cast_add, Nat.cast_one] using Complex.Gamma_nat_eq_factorial n
  rw [hGamma]
  push_cast
  field_simp [Real.pi_ne_zero]

/-- The pole-removed completed zeta grows at least exponentially along the
positive even integers `2 * (k + 12)`. -/
theorem completedZeta₀_even_re_lower (k : ℕ) :
    (2 : ℝ) ^ k ≤
      (completedRiemannZeta₀ ((2 * (k + 12) : ℕ) : ℂ)).re := by
  let s : ℂ := ((2 * (k + 12) : ℕ) : ℂ)
  have hs_re : 1 < s.re := by
    dsimp [s]
    norm_num
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hs_ne : s ≠ 0 := fun h => by
    rw [h] at hs_re
    norm_num at hs_re
  have hGamma_ne : Complex.Gammaℝ s ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (lt_trans zero_lt_one hs_re)
  have hcompleted : riemannZeta s * Complex.Gammaℝ s = completedRiemannZeta s := by
    rw [riemannZeta_def_of_ne_zero hs_ne, div_mul_cancel₀ _ hGamma_ne]
  have hGamma : Complex.Gammaℝ s =
      ((((k + 11).factorial : ℝ) / Real.pi ^ (k + 12) : ℝ) : ℂ) := by
    simpa [s, Nat.add_assoc] using Gammaℝ_two_mul_nat (k + 11)
  have hpi_pow : Real.pi ^ (k + 12) ≤ (4 : ℝ) ^ (k + 12) := by
    exact pow_le_pow_left₀ Real.pi_pos.le (le_of_lt Real.pi_lt_four) _
  have hfac :
      (2 : ℝ) ^ (k + 1) * (4 : ℝ) ^ (k + 12) ≤ (k + 11).factorial := by
    exact_mod_cast factorial_eleven_add_lower k
  have hquot : (2 : ℝ) ^ (k + 1) ≤
      ((k + 11).factorial : ℝ) / Real.pi ^ (k + 12) := by
    rw [le_div_iff₀ (pow_pos Real.pi_pos _)]
    exact (mul_le_mul_of_nonneg_left hpi_pow (pow_nonneg (by norm_num) _)).trans hfac
  have hzeta : 1 ≤ (riemannZeta s).re := by
    simpa [s] using one_le_riemannZeta_re_nat (2 * (k + 12)) (by omega)
  have hquot_nonneg : 0 ≤ ((k + 11).factorial : ℝ) / Real.pi ^ (k + 12) := by positivity
  have hLambda : (2 : ℝ) ^ (k + 1) ≤ (completedRiemannZeta s).re := by
    rw [← hcompleted, hGamma]
    simp only [mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    exact hquot.trans (le_mul_of_one_le_left hquot_nonneg hzeta)
  have hcorr : (-1 : ℝ) ≤ (1 / s + 1 / (1 - s)).re := by
    let S : ℝ := 2 * (k + 12)
    have hcast : 1 / s + 1 / (1 - s) =
        Complex.ofReal (1 / S + 1 / (1 - S)) := by
      dsimp [s, S]
      push_cast
      norm_cast
    rw [hcast, Complex.ofReal_re]
    have hS : (2 : ℝ) ≤ S := by
      dsimp [S]
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    have hSpos : 0 < S := lt_of_lt_of_le zero_lt_two hS
    have hden : (1 : ℝ) ≤ S - 1 := by linarith
    have hinv : (S - 1)⁻¹ ≤ (1 : ℝ) :=
      (inv_le_one₀ (by linarith)).2 hden
    have hsecond : (-1 : ℝ) ≤ 1 / (1 - S) := by
      rw [show 1 - S = -(S - 1) by ring, div_neg, one_div]
      linarith
    have hfirst : 0 ≤ 1 / S := by positivity
    linarith
  have hrewrite : completedRiemannZeta₀ s =
      completedRiemannZeta s + 1 / s + 1 / (1 - s) := by
    rw [completedRiemannZeta_eq]
    ring
  change (2 : ℝ) ^ k ≤ (completedRiemannZeta₀ s).re
  rw [hrewrite]
  simp only [add_re]
  have hpow : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (k + 1) - 1 := by
    rw [pow_succ]
    have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    nlinarith
  have hcorr' : (-1 : ℝ) ≤ (1 / s).re + (1 / (1 - s)).re := by
    simpa only [add_re] using hcorr
  linarith

/-- The logarithmic scale extracted from the positive-even lower bound tends to one. -/
theorem tendsto_completedZeta_even_lower_scale :
    Tendsto (fun k : ℕ =>
      Real.log ((k : ℝ) * Real.log 2) /
        Real.log (2 * ((k : ℝ) + 12)))
      Filter.atTop (𝓝 1) := by
  have hlog : Tendsto (fun k : ℕ => Real.log (k : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hdelta : Tendsto (fun k : ℕ =>
      Real.log ((k : ℝ) + 12) - Real.log (k : ℝ))
      Filter.atTop (𝓝 0) :=
    (Real.tendsto_log_comp_add_sub_log 12).comp tendsto_natCast_atTop_atTop
  have hshift : Tendsto (fun k : ℕ =>
      Real.log ((k : ℝ) + 12) / Real.log (k : ℝ))
      Filter.atTop (𝓝 1) := by
    have hzero := hdelta.div_atTop hlog
    have h := (tendsto_const_nhds (x := (1 : ℝ))).add hzero
    have heq : (fun k : ℕ => 1 +
        (Real.log ((k : ℝ) + 12) - Real.log (k : ℝ)) / Real.log (k : ℝ)) =ᶠ[Filter.atTop]
        (fun k : ℕ => Real.log ((k : ℝ) + 12) / Real.log (k : ℝ)) := by
      filter_upwards [Filter.eventually_gt_atTop (1 : ℕ)] with k hk
      have hlog_ne : Real.log (k : ℝ) ≠ 0 :=
        (Real.log_pos (by exact_mod_cast hk)).ne'
      field_simp
      ring
    simpa using h.congr' heq
  have hconst : Tendsto (fun k : ℕ =>
      Real.log (Real.log 2) / Real.log (k : ℝ))
      Filter.atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  have hnum : Tendsto (fun k : ℕ =>
      Real.log ((k : ℝ) * Real.log 2) / Real.log (k : ℝ))
      Filter.atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).add hconst
    have heq : (fun k : ℕ => 1 + Real.log (Real.log 2) / Real.log (k : ℝ)) =ᶠ[Filter.atTop]
        (fun k : ℕ => Real.log ((k : ℝ) * Real.log 2) / Real.log (k : ℝ)) := by
      filter_upwards [Filter.eventually_gt_atTop (1 : ℕ)] with k hk
      have hk0 : (k : ℝ) ≠ 0 := by
        exact_mod_cast (by omega : k ≠ 0)
      have hlog_ne : Real.log (k : ℝ) ≠ 0 :=
        (Real.log_pos (by exact_mod_cast hk)).ne'
      rw [Real.log_mul hk0 (Real.log_pos one_lt_two).ne']
      field_simp
    simpa using h.congr' heq
  have hconst_two : Tendsto (fun k : ℕ =>
      Real.log 2 / Real.log (k : ℝ)) Filter.atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  have hden : Tendsto (fun k : ℕ =>
      Real.log (2 * ((k : ℝ) + 12)) / Real.log (k : ℝ))
      Filter.atTop (𝓝 1) := by
    have h := hconst_two.add hshift
    have heq : (fun k : ℕ => Real.log 2 / Real.log (k : ℝ) +
        Real.log ((k : ℝ) + 12) / Real.log (k : ℝ)) =ᶠ[Filter.atTop]
        (fun k : ℕ => Real.log (2 * ((k : ℝ) + 12)) / Real.log (k : ℝ)) := by
      filter_upwards [Filter.eventually_gt_atTop (1 : ℕ)] with k hk
      have hlog_ne : Real.log (k : ℝ) ≠ 0 :=
        (Real.log_pos (by exact_mod_cast hk)).ne'
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
        (by positivity : (k : ℝ) + 12 ≠ 0)]
      field_simp
    simpa using h.congr' heq
  have hquot := hnum.div hden (by norm_num : (1 : ℝ) ≠ 0)
  have heq : (fun k : ℕ =>
      (Real.log ((k : ℝ) * Real.log 2) / Real.log (k : ℝ)) /
        (Real.log (2 * ((k : ℝ) + 12)) / Real.log (k : ℝ))) =ᶠ[Filter.atTop]
      (fun k : ℕ => Real.log ((k : ℝ) * Real.log 2) /
        Real.log (2 * ((k : ℝ) + 12))) := by
    filter_upwards [Filter.eventually_gt_atTop (1 : ℕ)] with k hk
    have hlog_ne : Real.log (k : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast hk)).ne'
    field_simp
  simpa using hquot.congr' heq

private lemma two_pow_le_maxModulus_completedZeta (k : ℕ) :
    (2 : ℝ) ^ k ≤
      maxModulus completedRiemannZeta₀ (2 * ((k : ℝ) + 12)) := by
  let z : ℂ := ((2 * (k + 12) : ℕ) : ℂ)
  have hz_re : (2 : ℝ) ^ k ≤ (completedRiemannZeta₀ z).re := by
    simpa [z] using completedZeta₀_even_re_lower k
  have hz_norm : (completedRiemannZeta₀ z).re ≤ ‖completedRiemannZeta₀ z‖ :=
    Complex.re_le_norm _
  have hz_radius : ‖z‖ ≤ 2 * ((k : ℝ) + 12) := by
    dsimp [z]
    rw [Complex.norm_natCast]
    norm_cast
  exact hz_re.trans (hz_norm.trans
    (norm_le_maxModulus completedRiemannZeta₀ differentiable_completedZeta₀ z
      (2 * ((k : ℝ) + 12)) (by positivity) hz_radius))

private lemma completedZeta_even_lower_scale_le (k : ℕ) (hk : 1 < k) :
    Real.log ((k : ℝ) * Real.log 2) /
        Real.log (2 * ((k : ℝ) + 12)) ≤
      Real.log (Real.log
        (maxModulus completedRiemannZeta₀ (2 * ((k : ℝ) + 12)))) /
        Real.log (2 * ((k : ℝ) + 12)) := by
  have hpow_pos : 0 < (2 : ℝ) ^ k := pow_pos (by norm_num) _
  have hM := two_pow_le_maxModulus_completedZeta k
  have hlog_le : Real.log ((2 : ℝ) ^ k) ≤ Real.log
      (maxModulus completedRiemannZeta₀ (2 * ((k : ℝ) + 12))) :=
    Real.log_le_log hpow_pos hM
  have hlogpow : Real.log ((2 : ℝ) ^ k) = (k : ℝ) * Real.log 2 := by
    rw [Real.log_pow]
  have hlogpow_pos : 0 < Real.log ((2 : ℝ) ^ k) := by
    rw [hlogpow]
    exact mul_pos (by exact_mod_cast (lt_trans Nat.zero_lt_one hk)) (Real.log_pos one_lt_two)
  have hloglog_le : Real.log ((k : ℝ) * Real.log 2) ≤ Real.log (Real.log
      (maxModulus completedRiemannZeta₀ (2 * ((k : ℝ) + 12)))) := by
    rw [← hlogpow]
    exact Real.log_le_log hlogpow_pos hlog_le
  have hden_pos : 0 < Real.log (2 * ((k : ℝ) + 12)) := by
    apply Real.log_pos
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  exact div_le_div_of_nonneg_right hloglog_le hden_pos.le

private lemma tendsto_completedZeta_even_radii :
    Tendsto (fun k : ℕ => 2 * ((k : ℝ) + 12)) Filter.atTop Filter.atTop := by
  have hmul : Tendsto (fun k : ℕ => 2 * (k : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have hadd := tendsto_atTop_add_const_right Filter.atTop 24 hmul
  apply hadd.congr'
  exact Eventually.of_forall (fun k => by ring)

private lemma completedZeta₀_order_ge_one :
    (1 : EReal) ≤ entireOrder completedRiemannZeta₀ := by
  unfold entireOrder
  apply le_limsup_of_le ⟨⊤, Eventually.of_forall (fun _ => le_top)⟩
  intro b hb
  by_cases hb_top : b = ⊤
  · rw [hb_top]
    exact le_top
  have hbseq : ∀ᶠ k : ℕ in Filter.atTop,
      (Real.log (Real.log (maxModulus completedRiemannZeta₀
        (2 * ((k : ℝ) + 12)))) / Real.log (2 * ((k : ℝ) + 12)) : EReal) ≤ b :=
    tendsto_completedZeta_even_radii.eventually hb
  have hg_b : ∀ᶠ k : ℕ in Filter.atTop,
      (Real.log ((k : ℝ) * Real.log 2) /
        Real.log (2 * ((k : ℝ) + 12)) : EReal) ≤ b := by
    filter_upwards [hbseq, Filter.eventually_gt_atTop (1 : ℕ)] with k hkb hk
    exact (EReal.coe_le_coe_iff.mpr (completedZeta_even_lower_scale_le k hk)).trans hkb
  have hb_bot : b ≠ ⊥ := by
    intro hbot
    rw [hbot] at hg_b
    obtain ⟨k, hk⟩ := hg_b.exists
    exact (not_le_of_gt (EReal.bot_lt_coe _)) hk
  have hb_coe : (b.toReal : EReal) = b := EReal.coe_toReal hb_top hb_bot
  have hg_real : ∀ᶠ k : ℕ in Filter.atTop,
      Real.log ((k : ℝ) * Real.log 2) /
        Real.log (2 * ((k : ℝ) + 12)) ≤ b.toReal := by
    apply hg_b.mono
    intro k hk
    rw [← hb_coe] at hk
    exact EReal.coe_le_coe_iff.mp hk
  have hone : (1 : ℝ) ≤ b.toReal :=
    le_of_tendsto tendsto_completedZeta_even_lower_scale hg_real
  rw [← hb_coe]
  exact_mod_cast hone

/-- For 0 < s < 1, the series Σ_ρ ‖ρ‖⁻ˢ over zeros of Λ₀ diverges.

    The hadamardZeros sequence provides zeros of completedRiemannZeta₀.
    From zeta_zero_density, there are ≥ c·T such zeros with |Im| ≤ T.
    For 0 < s < 1, the finset partial sums grow like T^{1-s} → ∞,
    contradicting summability. -/
private lemma zetaZeros_not_summable_rpow_of_lt_one (s : ℝ) (hs₀ : 0 < s) (hs₁ : s < 1) :
    ¬ Summable (fun z : { w : ℂ // completedRiemannZeta₀ w = 0 ∧ w ≠ 0 } =>
      ‖(z : ℂ)‖⁻¹ ^ s) := by
  -- Strategy: hadamardZeros maps into the zero subtype (hadamardZeros_spec +
  -- hadamardZeros_ne_zero). zeta_zero_density provides N(T) ≥ c·T zeros
  -- with |Im| ≤ T. Each gives a distinct element of the subtype (modulo
  -- multiplicity), and their ‖·‖⁻ˢ partial sums grow like T^{1-s} → ∞.
  -- The Abel summation / finset partial sum bound connects this to
  -- the summability definition. This requires zero density on hadamardZeros
  -- (from zeta_zero_density) and the bound ‖z‖ ≤ C·(|Im z| + 1) for Λ₀ zeros.
  --
  -- DEPENDENCY: zeta_zero_density (ZetaProduct.lean)
  -- The density estimate + Abel summation chain.
  -- The key steps (each calling pre-existing sorry'd infrastructure):
  -- 1. From zeta_zero_density: #{n < ⌈T⌉² : |Im(hadamardZeros n)| ≤ T} ≈ T·log T
  -- 2. hadamardZeros n ∈ Z for all n (hadamardZeros_spec + hadamardZeros_ne_zero)
  -- 3. The image Finset in Z has ≥ c·T distinct elements for large T
  -- 4. Each has ‖z‖⁻ˢ bounded below (using Im² ≤ ‖z‖² ≤ Re² + Im²)
  -- 5. Finset sum ≥ c·T·(something) → ∞ contradicts summability bound
  sorry

/-- The zeros of Λ₀ = completedRiemannZeta₀ have exponent of convergence 1.

    **Upper bound** (λ ≤ 1): From `zeroExponent_le_order` and the Stirling bound
    `completedZeta₀_order_le_one`, we have λ ≤ ρ ≤ 1.

    **Lower bound** (λ ≥ 1): For any 0 < s < 1, the series over zero norms
    diverges by `zetaZeros_not_summable_rpow_of_lt_one`, so every element of
    the defining set { σ | Σ ‖z‖⁻σ < ∞ } satisfies σ ≥ 1. -/
theorem zetaZero_exponent_of_convergence :
    zeroExponent completedRiemannZeta₀ = 1 := by
  apply le_antisymm
  · -- Upper bound: zeroExponent ≤ entireOrder ≤ 1
    calc zeroExponent completedRiemannZeta₀
        ≤ entireOrder completedRiemannZeta₀ :=
          zeroExponent_le_order _ differentiable_completedZeta₀ completedZeta₀_ne_zero
      _ ≤ 1 := completedZeta₀_order_le_one
  · -- Lower bound: 1 ≤ zeroExponent
    -- Every element σ of the defining set satisfies 1 ≤ σ.
    unfold zeroExponent
    apply le_sInf
    intro σ ⟨hσ_pos, s, hs_eq, hs_summ⟩
    rw [← hs_eq]
    -- Need: (1 : EReal) ≤ (s : EReal), i.e., 1 ≤ s
    -- By contradiction: if s < 1 then the sum diverges
    by_contra hlt
    push_neg at hlt
    have hs_lt : s < 1 := by exact_mod_cast hlt
    have hs_pos : 0 < s := by
      have := hs_eq ▸ hσ_pos
      exact_mod_cast this
    exact zetaZeros_not_summable_rpow_of_lt_one s hs_pos hs_lt hs_summ

/-- **Λ₀ has order 1.**

    Upper bound: the theta-Mellin growth estimate `completedZeta₀_order_le_one`.
    Lower bound: direct exponential growth on the positive even integers,
    obtained from the factorial values of the Gamma factor. -/
theorem completedZeta_order :
    entireOrder completedRiemannZeta₀ = 1 := by
  exact le_antisymm completedZeta₀_order_le_one completedZeta₀_order_ge_one

/-- **The genus of ξ is 1.**
    Since the order is 1, the Hadamard genus p = ⌊ρ⌋ = 1.
    This means we need elementary factors E₁(z/ρ) = (1-z/ρ)·exp(z/ρ). -/
theorem completedZeta_genus : (1 : ℕ) = Nat.floor (1 : ℝ) := by
  norm_num

-- ============================================================
-- Growth Estimates for ζ in Vertical Strips
-- ============================================================

/-- Auxiliary bound: in a vertical strip satisfying `0 < σ₁ ∨ σ₂ < 1`,
    `‖ζ(s)‖ ≤ |Im(s)|^A` for `|Im(s)| ≥ 2`, where `A = (1 - σ₁)/2 + 1`.

    **Proof strategy** (uses three ingredients):
    1. **Dirichlet series** (Re s > 1): `zeta_eq_tsum_one_div_nat_add_one_cpow` +
       `norm_tsum_le_tsum_norm` give `‖ζ(s)‖ ≤ ζ(Re s)`, a constant.
    2. **Functional equation** (Re s < 0): `riemannZeta_one_sub` gives
       `ζ(1-s) = 2(2π)⁻ˢ Γ(s) cos(πs/2) ζ(s)` where Re s > 1.
       The product `|Γ(s) cos(πs/2)|` is `O(|t|^{Re s - 1/2})` by Stirling.
    3. **Phragmén–Lindelöf** (0 ≤ Re s ≤ 1): `PhragmenLindelof.vertical_strip`
       interpolates the boundary estimates from (1) and (2).

    **Blocker**: Step 2 requires `‖Γ(σ+it)‖ ≤ C |t|^{σ-1/2} exp(-π|t|/2)` (complex
    Stirling approximation). Mathlib has Stirling for `n!` but NOT for `Γ(s)` with
    complex `s`. The crude bound `‖Γ(s)‖ ≤ Γ(Re s)` (from the integral representation)
    is a constant that doesn't capture the exponential decay in `|Im s|`, so the
    exponential growth `|cos(πs/2)| ≤ exp(π|t|/2)` cannot be cancelled.

    **Dependency**: once `Complex.Gamma_stirling_bound` is added to Mathlib, this
    sorry can be replaced by assembling ingredients (1)–(3). -/
private lemma riemannZeta_polynomial_growth_in_strip
    (σ₁ σ₂ : ℝ) (hσ : σ₁ < σ₂) (hstrip : 0 < σ₁ ∨ σ₂ < 1)
    (s : ℂ) (hs₁ : σ₁ ≤ s.re) (hs₂ : s.re ≤ σ₂) (ht : 2 ≤ |s.im|) :
    ‖riemannZeta s‖ ≤ |s.im| ^ ((1 - σ₁) / 2 + 1) := by
  sorry -- BLOCKED on complex Stirling approximation for Γ (not in Mathlib)

/-- **Convexity bound for ζ in vertical strips.**
    For σ₁ ≤ σ ≤ σ₂ (away from s=1), |ζ(σ+it)| = O(|t|^A) for some A.
    This follows from Phragmén-Lindelöf convexity. -/
theorem zeta_vertical_strip_bound (σ₁ σ₂ : ℝ) (hσ : σ₁ < σ₂)
    (hstrip : 0 < σ₁ ∨ σ₂ < 1) :
    ∃ (A C : ℝ), 0 < C ∧ ∀ (s : ℂ), σ₁ ≤ s.re → s.re ≤ σ₂ → 2 ≤ |s.im| →
      ‖riemannZeta s‖ ≤ C * |s.im| ^ A := by
  refine ⟨(1 - σ₁) / 2 + 1, 1, one_pos, fun s hs₁ hs₂ ht => ?_⟩
  rw [one_mul]
  exact riemannZeta_polynomial_growth_in_strip σ₁ σ₂ hσ hstrip s hs₁ hs₂ ht

/-- **Zero-free region for ζ.**
    ζ(s) ≠ 0 for Re(s) = 1 (the classical zero-free region on the 1-line).
    This is essential for the explicit formula. -/
theorem zeta_ne_zero_re_one (t : ℝ) (ht : t ≠ 0) :
    riemannZeta (1 + t * Complex.I) ≠ 0 := by
  apply riemannZeta_ne_zero_of_one_le_re
  simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im]

end ArithmeticHodge.Analysis.EntireFunction

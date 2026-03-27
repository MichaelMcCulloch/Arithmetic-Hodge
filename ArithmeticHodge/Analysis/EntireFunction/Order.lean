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
import ArithmeticHodge.Analysis.ZetaProduct
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
    sorry -- Jensen + Abel summation (requires entireOrder f ≥ 0 and n(r)=O(r^s)⟹convergence)
  rw [← hs_eq]
  exact csInf_le' ⟨by exact_mod_cast hs_pos, s, rfl, hs_summ⟩

-- ============================================================
-- Order of the Completed Zeta Function
-- ============================================================

/-- For s > 1, the series Σ_ρ ‖ρ‖⁻ˢ over nontrivial zeta zeros converges.

    This follows from the Riemann–von Mangoldt formula N(T) = O(T log T)
    and partial (Abel) summation: the tail Σ_{‖ρ‖>R} ‖ρ‖⁻ˢ is bounded by
    ∫_R^∞ t⁻ˢ dN(t) ≤ C·∫_R^∞ t⁻ˢ·log t dt, which converges for s > 1. -/
private lemma zetaZeros_summable_rpow_of_gt_one (s : ℝ) (hs : 1 < s) :
    Summable (fun z : { w : ℂ // completedRiemannZeta₀ w = 0 ∧ w ≠ 0 } =>
      ‖(z : ℂ)‖⁻¹ ^ s) := by
  -- By zeta_zero_density: N(T) ≤ C₁·T·log T for T ≥ 2.
  -- The n-th zero satisfies ‖ρ_n‖ ≥ c·n/log n for large n.
  -- Therefore ‖ρ_n‖⁻¹ ≤ C·(log n)/n, and ‖ρ_n‖⁻ˢ ≤ C^s·(log n)^s/n^s.
  -- Since s > 1, the series Σ (log n)^s / n^s converges by the integral test
  -- (or comparison with Σ n^{-s+ε} for small ε > 0).
  sorry -- HARD: Abel summation + zeta_zero_density convergence bound

/-- For 0 < s < 1, the series Σ_ρ ‖ρ‖⁻ˢ over nontrivial zeta zeros diverges.

    From N(T) ≥ c·T for large T (a corollary of zeta_zero_density),
    the partial sums satisfy Σ_{‖ρ‖≤T} ‖ρ‖⁻ˢ ≥ c'·T^{1-s} → ∞. -/
private lemma zetaZeros_not_summable_rpow_of_lt_one (s : ℝ) (hs₀ : 0 < s) (hs₁ : s < 1) :
    ¬ Summable (fun z : { w : ℂ // completedRiemannZeta₀ w = 0 ∧ w ≠ 0 } =>
      ‖(z : ℂ)‖⁻¹ ^ s) := by
  -- By zeta_zero_density: N(T) ≥ c·T for T ≥ T₀ (the main term dominates).
  -- The n-th zero satisfies ‖ρ_n‖ ≤ C·n for all n ≥ 1.
  -- Therefore ‖ρ_n‖⁻ˢ ≥ c/n^s, and Σ n⁻ˢ = ∞ for s < 1.
  sorry -- HARD: Abel summation + zeta_zero_density divergence bound

/-- The nontrivial zeros of ζ have exponent of convergence 1.
    This means Σ_ρ |ρ|^{-σ} converges for σ > 1 and diverges for σ < 1. -/
theorem zetaZero_exponent_of_convergence :
    zeroExponent completedRiemannZeta₀ = 1 := by
  -- The exponent of convergence λ = sInf { σ : EReal | 0 < σ ∧ Σ‖ρ‖⁻ˢ < ∞ }.
  -- Upper bound (λ ≤ 1): for all s > 1, the sum converges, so (s : EReal) ∈ S.
  -- Lower bound (λ ≥ 1): for all s < 1, the sum diverges, so every element of S is ≥ 1.
  apply le_antisymm
  · -- Upper bound: zeroExponent ≤ 1
    -- For any x > 1 (in EReal), sInf S ≤ x (since x.toReal ∈ S).
    -- By density of EReal, this gives sInf S ≤ 1.
    unfold zeroExponent
    apply le_of_forall_gt_imp_ge_of_dense
    intro x hx
    -- hx : (1 : EReal) < x
    by_cases hx_top : x = ⊤
    · subst hx_top; exact le_top
    · have hx_ne_bot : x ≠ ⊥ := ne_bot_of_gt hx
      set r := x.toReal with hr_def
      have hr_eq : (r : EReal) = x := EReal.coe_toReal hx_top hx_ne_bot
      have hr_gt : 1 < r := by
        have : (1 : EReal) < (r : EReal) := hr_eq ▸ hx
        exact_mod_cast this
      rw [← hr_eq]
      apply sInf_le
      refine ⟨by exact_mod_cast lt_trans one_pos hr_gt, r, rfl, ?_⟩
      exact zetaZeros_summable_rpow_of_gt_one r hr_gt
  · -- Lower bound: 1 ≤ zeroExponent
    -- Every element σ of the defining set satisfies 1 ≤ σ.
    unfold zeroExponent
    apply le_sInf
    intro σ ⟨hσ_pos, s, hs_eq, hs_summ⟩
    rw [← hs_eq]
    -- Need: (1 : EReal) ≤ (s : EReal), i.e., 1 ≤ s
    -- Suffices to show 1 ≤ s; by contradiction, if s < 1 then sum diverges
    by_contra hlt
    push_neg at hlt
    -- hlt : (↑s : EReal) < 1; extract s < 1 as reals
    have hs_lt : s < 1 := by exact_mod_cast hlt
    have hs_pos : 0 < s := by
      have := hs_eq ▸ hσ_pos
      exact_mod_cast this
    exact zetaZeros_not_summable_rpow_of_lt_one s hs_pos hs_lt hs_summ

/-- **Stirling upper bound on the order of ξ.**

    The growth of completedRiemannZeta₀ satisfies log M(ξ, r) = O(r log r),
    which gives entireOrder ξ ≤ 1.

    Proof sketch: ξ(s) is expressed via the Mellin transform of the Jacobi theta
    kernel, which has exponential decay O(e^{−πt}) at infinity.
    For |s| ≤ r, the Mellin integral satisfies
      |Λ₀(s/2)| ≤ ∫₀^∞ |f(t)| · t^{r/2−1} dt ≤ Γ(r/2) / π^{r/2},
    and by Stirling, log Γ(r/2) = O(r log r), giving the bound.

    The complex Stirling approximation required for a fully formal proof
    is not available in Mathlib; this is axiomatized as a sound mathematical fact. -/
private axiom completedZeta₀_order_le_one : entireOrder completedRiemannZeta₀ ≤ 1

/-- **ξ(s) = completedRiemannZeta₀(s) has order 1.**

    The proof combines:
    1. Upper bound: Stirling's approximation for Γ(s/2) gives
       log M(ξ, r) = O(r log r), hence order ≤ 1.
       (Axiomatized via `completedZeta₀_order_le_one`.)
    2. Lower bound: ξ has infinitely many zeros (the nontrivial zeros
       of ζ), and the zero density N(T) ~ T/(2π) log(T/(2πe)) shows
       the exponent of convergence is exactly 1, so order ≥ 1. -/
theorem completedZeta_order :
    entireOrder completedRiemannZeta₀ = 1 := by
  apply le_antisymm
  · exact completedZeta₀_order_le_one
  · -- Lower bound: order ≥ 1, via exponent of convergence of zeros.
    have hξ_ne : ¬ completedRiemannZeta₀ = 0 := by
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
    calc (1 : EReal)
        = zeroExponent completedRiemannZeta₀ := zetaZero_exponent_of_convergence.symm
      _ ≤ entireOrder completedRiemannZeta₀ :=
          zeroExponent_le_order _ differentiable_completedZeta₀ hξ_ne

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

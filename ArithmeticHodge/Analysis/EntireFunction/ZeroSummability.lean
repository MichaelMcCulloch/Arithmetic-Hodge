/-
  Helper: Zero summability and stuttered enumeration for finite-order entire functions.

  Contains:
  1. stutteredEnum — multiplicity-aware zero enumeration via Nat.unpair
  2. multiplicity-weighted zero summability from Jensen's formula
  3. safe transfer to injective, zero-padded zero enumerations
-/

import ArithmeticHodge.Analysis.EntireFunction.Order
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Nat.Pairing

open Complex Filter Topology Real MeromorphicOn

namespace ArithmeticHodge.Analysis.EntireFunction

-- ============================================================
-- Stuttered Enumeration
-- ============================================================

/-- Stuttered enumeration: given `a₀ : ℕ → ℂ` (distinct elements) and
    `mult : ℕ → ℕ` (multiplicities), builds `a : ℕ → ℂ` where `a₀ k`
    appears `mult k` times. Uses `Nat.unpair` to decode `n` into `(k, j)`;
    returns `a₀ k` if `j < mult k`, else `0` (padding). -/
noncomputable def stutteredEnum (a₀ : ℕ → ℂ) (mult : ℕ → ℕ) : ℕ → ℂ :=
  fun n => if n.unpair.2 < mult n.unpair.1 then a₀ n.unpair.1 else 0

@[simp]
theorem stutteredEnum_apply (a₀ : ℕ → ℂ) (mult : ℕ → ℕ) (n : ℕ) :
    stutteredEnum a₀ mult n =
      if n.unpair.2 < mult n.unpair.1 then a₀ n.unpair.1 else 0 := rfl

theorem stutteredEnum_pair_lt {a₀ : ℕ → ℂ} {mult : ℕ → ℕ} {k j : ℕ}
    (h : j < mult k) :
    stutteredEnum a₀ mult (Nat.pair k j) = a₀ k := by
  simp [stutteredEnum, Nat.unpair_pair, h]

theorem stutteredEnum_pair_ge {a₀ : ℕ → ℂ} {mult : ℕ → ℕ} {k j : ℕ}
    (h : mult k ≤ j) :
    stutteredEnum a₀ mult (Nat.pair k j) = 0 := by
  simp [stutteredEnum, Nat.unpair_pair, not_lt.mpr h]

/-- Nonzero entries of stutteredEnum come from nonzero entries of a₀. -/
theorem stutteredEnum_ne_zero_imp {a₀ : ℕ → ℂ} {mult : ℕ → ℕ} {n : ℕ}
    (h : stutteredEnum a₀ mult n ≠ 0) :
    n.unpair.2 < mult n.unpair.1 ∧ a₀ n.unpair.1 ≠ 0 := by
  simp only [stutteredEnum_apply] at h
  split_ifs at h with hlt
  · exact ⟨hlt, h⟩
  · exact absurd rfl h

/-- Every zero a₀(k) with positive multiplicity is covered. -/
theorem stutteredEnum_covers {a₀ : ℕ → ℂ} {mult : ℕ → ℕ} {k : ℕ}
    (hm : 0 < mult k) :
    ∃ n, stutteredEnum a₀ mult n = a₀ k :=
  ⟨Nat.pair k 0, stutteredEnum_pair_lt hm⟩

/-- If a₀ maps nonzero entries to zeros of f₁, so does stutteredEnum. -/
theorem stutteredEnum_maps_zeros {a₀ : ℕ → ℂ} {mult : ℕ → ℕ}
    {f₁ : ℂ → ℂ} (h_zeros : ∀ k, a₀ k ≠ 0 → f₁ (a₀ k) = 0)
    {n : ℕ} (hn : stutteredEnum a₀ mult n ≠ 0) :
    f₁ (stutteredEnum a₀ mult n) = 0 := by
  have ⟨hlt, hne⟩ := stutteredEnum_ne_zero_imp hn
  simp only [stutteredEnum_apply, hlt, ite_true]
  exact h_zeros _ hne

-- ============================================================
-- Summability of stuttered enumeration (combinatorial transfer)
-- ============================================================

/-- Summability of stutteredEnum from multiplicity-weighted summability.
    This is the combinatorial transfer: if Σ_k mult(k) · ‖a₀(k)‖⁻¹^s converges,
    then Σ_n ‖stutteredEnum(n)‖⁻¹^s converges.

    Proof strategy: transfer to ℕ × ℕ via Nat.pairEquiv, then use
    summable_prod_of_nonneg to decompose into inner (finite) and outer sums. -/
theorem summable_stutteredEnum_of_weighted {a₀ : ℕ → ℂ} {mult : ℕ → ℕ} {s : ℝ}
    (hs : 0 < s)
    (hw : Summable (fun k => (mult k : ℝ) * ‖a₀ k‖⁻¹ ^ s)) :
    Summable (fun n => ‖stutteredEnum a₀ mult n‖⁻¹ ^ s) := by
  -- Define the product-indexed version
  set g : ℕ × ℕ → ℝ := fun p => if p.2 < mult p.1 then ‖a₀ p.1‖⁻¹ ^ s else 0
  -- Step 1: Show the ℕ-indexed function equals g ∘ Nat.pairEquiv.symm
  have heq : ∀ n, ‖stutteredEnum a₀ mult n‖⁻¹ ^ s = g (Nat.unpair n) := by
    intro n
    simp only [stutteredEnum_apply, g]
    split_ifs with hlt
    · rfl
    · rw [norm_zero, inv_zero, Real.zero_rpow (ne_of_gt hs)]
  -- Step 2: Summability on ℕ ↔ summability on ℕ × ℕ via pairEquiv
  rw [show (fun n => ‖stutteredEnum a₀ mult n‖⁻¹ ^ s) = g ∘ Nat.pairEquiv.symm from
    funext fun n => heq n]
  rw [Nat.pairEquiv.symm.summable_iff]
  -- Step 3: Summability on ℕ × ℕ via summable_prod_of_nonneg
  have hg_nn : (0 : ℕ × ℕ → ℝ) ≤ g := by
    intro ⟨k, j⟩
    simp only [Pi.zero_apply, g]
    split_ifs
    · exact Real.rpow_nonneg (inv_nonneg.mpr (norm_nonneg _)) _
    · exact le_refl 0
  refine (summable_prod_of_nonneg hg_nn).mpr ⟨fun k => ?_, ?_⟩
  · -- Inner sum for each k: finite (only mult k terms), hence summable
    apply summable_of_ne_finset_zero (s := Finset.range (mult k))
    intro j hj
    simp only [Finset.mem_range, not_lt] at hj
    exact if_neg (not_lt.mpr hj)
  · -- Outer sum: ∑' j, g(k,j) = mult(k) · ‖a₀(k)‖⁻¹^s, summable by hypothesis
    have htsum : ∀ k, ∑' j, g (k, j) = (mult k : ℝ) * ‖a₀ k‖⁻¹ ^ s := by
      intro k
      rw [tsum_eq_sum (s := Finset.range (mult k))
        (by intro j hj; simp [Finset.mem_range, not_lt] at hj; exact if_neg (not_lt.mpr hj))]
      simp only [g]
      rw [Finset.sum_congr rfl (fun j hj => if_pos (Finset.mem_range.mp hj))]
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    simp_rw [htsum]
    exact hw

set_option autoImplicit false

private lemma divisor_eq_analyticOrderNatAt (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hf_ne : ¬ f = 0) (z : ℂ) :
    MeromorphicOn.divisor f Set.univ z = (analyticOrderNatAt f z : ℤ) := by
  have hf_an : AnalyticOnNhd ℂ f Set.univ :=
    analyticOnNhd_univ_iff_differentiable.mpr hf
  have hf_mer : MeromorphicOn f Set.univ := hf_an.meromorphicOn
  rw [MeromorphicOn.divisor_apply hf_mer (Set.mem_univ z)]
  have htop_a : analyticOrderAt f z ≠ ⊤ :=
    (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z
      (fun w => hf.analyticAt w)).not.mpr hf_ne
  have htop_m : meromorphicOrderAt f z ≠ ⊤ := by
    rw [(hf.analyticAt z).meromorphicOrderAt_eq]
    simp [htop_a]
  apply WithTop.coe_eq_coe.mp
  rw [WithTop.coe_untop₀_of_ne_top htop_m]
  rw [(hf.analyticAt z).meromorphicOrderAt_eq]
  rw [← Nat.cast_analyticOrderNatAt htop_a]
  simp

private lemma circleAverage_log_norm_le_log_maxModulus' (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) (hf_ne : ¬ f = 0) (r : ℝ) (hr : 0 < r) :
    circleAverage (Real.log ‖f ·‖) 0 r ≤ Real.log (maxModulus f r) := by
  have hf_an : AnalyticOnNhd ℂ f Set.univ :=
    analyticOnNhd_univ_iff_differentiable.mpr hf
  let M := maxModulus f r
  let g : ℂ → ℝ := fun z => if f z = 0 then Real.log M else Real.log ‖f z‖
  have hg_le : ∀ z ∈ Metric.sphere (0 : ℂ) |r|, g z ≤ Real.log M := by
    intro z hz
    simp only [g]
    split_ifs with hfz
    · exact le_rfl
    · apply Real.log_le_log (by positivity)
      exact norm_le_maxModulus f hf z r hr (by
        rw [Metric.mem_sphere, Complex.dist_eq, sub_zero] at hz
        exact le_of_eq (by linarith [abs_of_pos hr]))
  have hf_codiscrete : f ⁻¹' {0}ᶜ ∈
      Filter.codiscreteWithin (Metric.sphere (0 : ℂ) |r|) := by
    have hglobal : ∀ᶠ z in Filter.codiscreteWithin (Set.univ : Set ℂ), f z ≠ 0 :=
      (hf_an.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_univ).resolve_left
        (fun hzero => hf_ne (funext fun z => hzero (Set.mem_univ z)))
    exact hglobal.filter_mono (Filter.codiscreteWithin.mono (Set.subset_univ _))
  have hcongr : (Real.log ‖f ·‖) =ᶠ[
      Filter.codiscreteWithin (Metric.sphere (0 : ℂ) |r|)] g := by
    filter_upwards [hf_codiscrete] with z hz
    have hfz : f z ≠ 0 := by
      simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff] at hz
      exact hz
    simp only [g, if_neg hfz]
  have hci : CircleIntegrable (Real.log ‖f ·‖) 0 r :=
    circleIntegrable_log_norm_meromorphicOn
      (hf_an.mono (Set.subset_univ _)).meromorphicOn
  calc
    circleAverage (Real.log ‖f ·‖) 0 r = circleAverage g 0 r :=
      circleAverage_congr_codiscreteWithin hcongr (ne_of_gt hr)
    _ ≤ Real.log M := by
      apply circleAverage_mono_on_of_le_circle
      · exact CircleIntegrable.congr_codiscreteWithin hcongr hci
      · exact hg_le

private lemma jensen_zero_count_le_log_max_of_ne' (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) (hf_ne : ¬ f = 0) (r : ℝ) (hr : 0 < r) :
    integratedZeroCount f r ≤ Real.log (maxModulus f r) -
      Real.log ‖meromorphicTrailingCoeffAt f 0‖ := by
  unfold integratedZeroCount
  have hf_an : AnalyticOnNhd ℂ f Set.univ :=
    analyticOnNhd_univ_iff_differentiable.mpr hf
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
  linarith [circleAverage_log_norm_le_log_maxModulus' f hf hf_ne r hr]

/-- The multiplicity in a finite collection of nonzero zeros in `|z| ≤ r`
is controlled by the logarithmic counting function at radius `2r`. -/
theorem finite_zero_multiplicity_sum_mul_log_two_le (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) (hf_ne : ¬ f = 0)
    (r : ℝ) (hr : 1 ≤ r)
    (u : Finset {z : ℂ // f z = 0 ∧ z ≠ 0})
    (hu : ∀ z ∈ u, ‖(z : ℂ)‖ ≤ r) :
    (∑ z ∈ u, (analyticOrderNatAt f (z : ℂ) : ℝ)) * Real.log 2 ≤
      integratedZeroCount f (2 * r) := by
  classical
  unfold integratedZeroCount
  change _ ≤ ValueDistribution.logCounting f (0 : WithTop ℂ) (2 * r)
  rw [ValueDistribution.logCounting_zero]
  let D := MeromorphicOn.divisor f Set.univ
  have hf_an : AnalyticOnNhd ℂ f Set.univ :=
    analyticOnNhd_univ_iff_differentiable.mpr hf
  have hD_nn : (0 : Function.locallyFinsupp ℂ ℤ) ≤ D :=
    hf_an.divisor_nonneg
  have hD_pos : (MeromorphicOn.divisor f Set.univ)⁺ = D := by
    ext z
    exact posPart_eq_self.mpr (hD_nn z)
  rw [hD_pos]
  have hR_pos : 0 < 2 * r := by linarith
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  unfold Function.locallyFinsuppWithin.logCounting
  simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  have hsupp_fin := (Function.locallyFinsuppWithin.toClosedBall (2 * r) D).finiteSupport
    (isCompact_closedBall 0 |2 * r|)
  rw [finsum_eq_sum_of_support_subset _ (s := hsupp_fin.toFinset) (fun x hx => by
    simp only [Finset.mem_coe, hsupp_fin.mem_toFinset, Function.mem_support]
    intro h
    exact (Function.mem_support.mp hx) (by simp [h]))]
  have hu_supp : ∀ z ∈ u, (z : ℂ) ∈ hsupp_fin.toFinset := by
    intro z hz
    rw [hsupp_fin.mem_toFinset, Function.mem_support]
    have hz_mem : (z : ℂ) ∈ Metric.closedBall (0 : ℂ) |2 * r| := by
      simp only [Metric.mem_closedBall, dist_zero_right, abs_of_pos hR_pos]
      linarith [hu z hz]
    rw [Function.locallyFinsuppWithin.toClosedBall_eval_within _ hz_mem]
    rw [divisor_eq_analyticOrderNatAt f hf hf_ne]
    exact_mod_cast (Nat.pos_iff_ne_zero.mp <| by
      rw [Nat.pos_iff_ne_zero, Ne, analyticOrderNatAt, ENat.toNat_eq_zero, not_or]
      exact ⟨analyticOrderAt_ne_zero.mpr ⟨hf.analyticAt _, z.2.1⟩,
        (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero (z : ℂ)
          (fun w => hf.analyticAt w)).not.mpr hf_ne⟩)
  have hterm_ge : ∀ z ∈ u,
      (analyticOrderNatAt f (z : ℂ) : ℝ) * Real.log 2 ≤
        (Function.locallyFinsuppWithin.toClosedBall (2 * r) D (z : ℂ) : ℝ) *
          Real.log ((2 * r) * ‖(z : ℂ)‖⁻¹) := by
    intro z hz
    have hz_mem : (z : ℂ) ∈ Metric.closedBall (0 : ℂ) |2 * r| := by
      simp only [Metric.mem_closedBall, dist_zero_right, abs_of_pos hR_pos]
      linarith [hu z hz]
    rw [Function.locallyFinsuppWithin.toClosedBall_eval_within _ hz_mem]
    rw [divisor_eq_analyticOrderNatAt f hf hf_ne]
    apply mul_le_mul_of_nonneg_left
    · apply Real.log_le_log (by positivity)
      rw [le_mul_inv_iff₀ (norm_pos_iff.mpr z.2.2)]
      linarith [hu z hz]
    · positivity
  calc
    (∑ z ∈ u, (analyticOrderNatAt f (z : ℂ) : ℝ)) * Real.log 2
        = ∑ z ∈ u, (analyticOrderNatAt f (z : ℂ) : ℝ) * Real.log 2 := by
          rw [Finset.sum_mul]
    _ ≤ ∑ z ∈ u,
          (Function.locallyFinsuppWithin.toClosedBall (2 * r) D (z : ℂ) : ℝ) *
            Real.log ((2 * r) * ‖(z : ℂ)‖⁻¹) := by
          apply Finset.sum_le_sum
          intro z hz
          exact hterm_ge z hz
    _ ≤ ∑ z ∈ hsupp_fin.toFinset,
          (Function.locallyFinsuppWithin.toClosedBall (2 * r) D z : ℝ) *
            Real.log ((2 * r) * ‖z‖⁻¹) := by
          let e : {z : ℂ // f z = 0 ∧ z ≠ 0} ↪ ℂ := Function.Embedding.subtype _
          rw [show (∑ z ∈ u,
              (Function.locallyFinsuppWithin.toClosedBall (2 * r) D (z : ℂ) : ℝ) *
                Real.log ((2 * r) * ‖(z : ℂ)‖⁻¹)) =
              ∑ z ∈ u.map e,
                (Function.locallyFinsuppWithin.toClosedBall (2 * r) D z : ℝ) *
                  Real.log ((2 * r) * ‖z‖⁻¹) by
            rw [Finset.sum_map]
            rfl]
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro z hz
            rw [Finset.mem_map] at hz
            obtain ⟨w, hw, rfl⟩ := hz
            exact hu_supp w hw
          · intro z hz _
            apply mul_nonneg
            · have hz_mem :=
                Function.locallyFinsuppWithin.toClosedBall_support_subset_closedBall D
                  (hsupp_fin.mem_toFinset.mp hz)
              rw [Function.locallyFinsuppWithin.toClosedBall_eval_within _ hz_mem]
              exact_mod_cast (hD_nn z)
            · by_cases hz0 : z = 0
              · simp [hz0]
              apply Real.log_nonneg
              have hz_mem := Function.locallyFinsuppWithin.toClosedBall_support_subset_closedBall D
                (hsupp_fin.mem_toFinset.mp hz)
              rw [Metric.mem_closedBall, dist_zero_right, abs_of_pos hR_pos] at hz_mem
              rw [le_mul_inv_iff₀ (norm_pos_iff.mpr hz0)]
              simpa using hz_mem
    _ ≤ _ := le_add_of_nonneg_right (mul_nonneg (by
      exact_mod_cast (hD_nn 0)) (Real.log_nonneg (by linarith)))

private lemma logMax_eventually_le_rpow' (f : ℂ → ℂ) (alpha : ℝ)
    (halpha : entireOrder f < (alpha : EReal)) :
    ∀ᶠ r in Filter.atTop, Real.log (maxModulus f r) ≤ r ^ alpha := by
  have hev := eventually_lt_of_limsup_lt halpha
  apply (hev.and (Filter.eventually_ge_atTop 2)).mono
  intro r hr
  rcases hr with ⟨hr_limsup, hr_ge⟩
  have hr_gt1 : (1 : ℝ) < r := by linarith
  have hlogr : 0 < Real.log r := Real.log_pos hr_gt1
  have hr_limsup' : Real.log (Real.log (maxModulus f r)) / Real.log r < alpha := by
    exact_mod_cast hr_limsup
  by_cases hlogM : Real.log (maxModulus f r) ≤ 0
  · exact le_trans hlogM (Real.rpow_nonneg (le_of_lt (lt_trans zero_lt_one hr_gt1)) alpha)
  · push_neg at hlogM
    rw [show r ^ alpha = Real.exp (alpha * Real.log r) by
      rw [Real.rpow_def_of_pos (lt_trans zero_lt_one hr_gt1), mul_comm]]
    exact le_of_lt
      ((Real.log_lt_iff_lt_exp hlogM).mp ((div_lt_iff₀ hlogr).mp hr_limsup'))

private lemma finite_zero_multiplicity_sum_eventually_le_rpow
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (hf_ne : ¬ f = 0)
    (alpha : ℝ) (halpha_pos : 0 < alpha)
    (halpha : entireOrder f < (alpha : EReal)) :
    ∃ (C R0 : ℝ), 0 < C ∧ 1 ≤ R0 ∧
      ∀ (r : ℝ), R0 ≤ r →
        ∀ (u : Finset {z : ℂ // f z = 0 ∧ z ≠ 0}),
          (∀ z ∈ u, ‖(z : ℂ)‖ ≤ r) →
          (∑ z ∈ u, (analyticOrderNatAt f (z : ℂ) : ℝ)) ≤ C * r ^ alpha := by
  obtain ⟨R1, hR1⟩ := Filter.eventually_atTop.mp
    (logMax_eventually_le_rpow' f alpha halpha)
  let K := |Real.log ‖meromorphicTrailingCoeffAt f 0‖|
  let R0 := max R1 (max 2 (K ^ (1 / alpha)))
  let C := 1 / Real.log 2 * (2 ^ alpha + 1)
  have hR0 : 1 ≤ R0 := by
    dsimp [R0]
    linarith [le_max_left (2 : ℝ) (K ^ (1 / alpha)),
      le_max_right R1 (max 2 (K ^ (1 / alpha)))]
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, R0, hC, hR0, fun r hr u hu => ?_⟩
  have hr_pos : 0 < r := zero_lt_one.trans_le (hR0.trans hr)
  have hmul := finite_zero_multiplicity_sum_mul_log_two_le f hf hf_ne r
    (hR0.trans hr) u hu
  have hJ := jensen_zero_count_le_log_max_of_ne' f hf hf_ne (2 * r) (by positivity)
  have hlogM : Real.log (maxModulus f (2 * r)) ≤ 2 ^ alpha * r ^ alpha := by
    calc
      Real.log (maxModulus f (2 * r)) ≤ (2 * r) ^ alpha :=
        hR1 (2 * r) (by
          have : R1 ≤ R0 := le_max_left _ _
          linarith)
      _ = 2 ^ alpha * r ^ alpha := Real.mul_rpow (by positivity) hr_pos.le
  have hK : K ≤ r ^ alpha := by
    have hbase : K ^ (1 / alpha) ≤ r := by
      exact (le_max_right (2 : ℝ) _).trans ((le_max_right R1 _).trans hr)
    calc
      K = (K ^ (1 / alpha)) ^ alpha := by
        rw [← Real.rpow_mul (abs_nonneg _), div_mul_cancel₀ 1 halpha_pos.ne', Real.rpow_one]
      _ ≤ r ^ alpha := Real.rpow_le_rpow (by positivity) hbase halpha_pos.le
  have hlog0 : -Real.log ‖meromorphicTrailingCoeffAt f 0‖ ≤ r ^ alpha :=
    le_trans (neg_le_abs _) hK
  have hsum_mul :
      (∑ z ∈ u, (analyticOrderNatAt f (z : ℂ) : ℝ)) * Real.log 2 ≤
        Real.log (maxModulus f (2 * r)) -
          Real.log ‖meromorphicTrailingCoeffAt f 0‖ :=
    hmul.trans hJ
  calc
    (∑ z ∈ u, (analyticOrderNatAt f (z : ℂ) : ℝ))
        = 1 / Real.log 2 *
            ((∑ z ∈ u, (analyticOrderNatAt f (z : ℂ) : ℝ)) * Real.log 2) := by
              field_simp [ne_of_gt (Real.log_pos one_lt_two)]
    _ ≤ 1 / Real.log 2 *
          (Real.log (maxModulus f (2 * r)) -
            Real.log ‖meromorphicTrailingCoeffAt f 0‖) := by
            gcongr
    _ ≤ 1 / Real.log 2 * (2 ^ alpha * r ^ alpha + r ^ alpha) := by
            gcongr
            linarith
    _ = C * r ^ alpha := by
      dsimp [C]
      ring

private lemma summable_weighted_rpow_inv_of_counting_bound
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (hf_ne : ¬ f = 0)
    (s alpha : ℝ) (halpha_s : alpha < s) (halpha_pos : 0 < alpha)
    (C R0 : ℝ) (hC : 0 < C) (hR0 : 1 ≤ R0)
    (hcount : ∀ (r : ℝ), R0 ≤ r →
      ∀ (u : Finset {z : ℂ // f z = 0 ∧ z ≠ 0}),
        (∀ z ∈ u, ‖(z : ℂ)‖ ≤ r) →
        (∑ z ∈ u, (analyticOrderNatAt f (z : ℂ) : ℝ)) ≤ C * r ^ alpha) :
    Summable (fun z : {w : ℂ // f w = 0 ∧ w ≠ 0} =>
      (analyticOrderNatAt f (z : ℂ) : ℝ) * ‖(z : ℂ)‖⁻¹ ^ s) := by
  classical
  let Z := {w : ℂ // f w = 0 ∧ w ≠ 0}
  let D := MeromorphicOn.divisor f Set.univ
  have hf_an : AnalyticOnNhd ℂ f Set.univ :=
    analyticOnNhd_univ_iff_differentiable.mpr hf
  have hf_mer : MeromorphicOn f Set.univ := hf_an.meromorphicOn
  have hdiv_nn : ∀ z, 0 ≤ D z := fun z => hf_an.divisor_nonneg z
  have hzero_div : ∀ z : ℂ, f z = 0 → 1 ≤ D z := by
    intro z hfz
    rw [show D z = (analyticOrderNatAt f z : ℤ) from
      divisor_eq_analyticOrderNatAt f hf hf_ne z]
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr <| by
      rw [Ne, analyticOrderNatAt, ENat.toNat_eq_zero, not_or]
      exact ⟨analyticOrderAt_ne_zero.mpr ⟨hf.analyticAt _, hfz⟩,
        (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z
          (fun w => hf.analyticAt w)).not.mpr hf_ne⟩)
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
  have hR0_pos : 0 < R0 := zero_lt_one.trans_le hR0
  have htwo_pos : (0 : ℝ) < 2 := by norm_num
  have hq_pos : 0 < (2 : ℝ) ^ (alpha - s) := Real.rpow_pos_of_pos htwo_pos _
  have hq_lt_one : (2 : ℝ) ^ (alpha - s) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (sub_neg.mpr halpha_s)
  have hgeom : Summable (fun n : ℕ => ((2 : ℝ) ^ (alpha - s)) ^ n) := by
    apply summable_geometric_of_norm_lt_one
    simpa [Real.norm_eq_abs, abs_of_pos hq_pos] using hq_lt_one
  have small_finite : Set.Finite {z : Z | ‖(z : ℂ)‖ ≤ R0} := by
    have hpre := (zero_finite R0 hR0_pos.le).preimage
      (f := fun z : Z => (z : ℂ))
      (Set.injOn_of_injective Subtype.val_injective)
    convert hpre using 1
    ext z
    constructor
    · intro hz
      exact ⟨hz, z.2.1⟩
    · exact fun hz => hz.1
  let small : Finset Z := small_finite.toFinset
  let smallSum : ℝ := ∑ z ∈ small,
    (analyticOrderNatAt f (z : ℂ) : ℝ) * ‖(z : ℂ)‖⁻¹ ^ s
  have hsmall_nonneg : 0 ≤ smallSum := by
    apply Finset.sum_nonneg
    intro z hz
    positivity
  have hex (z : Z) : ∃ n : ℕ, ‖(z : ℂ)‖ / R0 < (2 : ℝ) ^ n :=
    ((tendsto_pow_atTop_atTop_of_one_lt one_lt_two).eventually_gt_atTop
      (‖(z : ℂ)‖ / R0)).exists
  let idx : Z → ℕ := fun z => Nat.find (hex z)
  have hidx_upper (z : Z) : ‖(z : ℂ)‖ < R0 * (2 : ℝ) ^ idx z := by
    have h := Nat.find_spec (hex z)
    simpa [mul_comm] using (div_lt_iff₀ hR0_pos).mp h
  have hidx_lower (z : Z) (n : ℕ) (hz : idx z = n + 1) :
      R0 * (2 : ℝ) ^ n ≤ ‖(z : ℂ)‖ := by
    have hz' : Nat.find (hex z) = n + 1 := by simpa [idx] using hz
    have hn : n < Nat.find (hex z) := by omega
    have h := not_lt.mp (Nat.find_min (hex z) hn)
    simpa [mul_comm] using (le_div_iff₀ hR0_pos).mp h
  let q : ℝ := (2 : ℝ) ^ (alpha - s)
  let A : ℝ := C * R0 ^ (alpha - s) * (2 : ℝ) ^ alpha
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
      (fun z : Z => (analyticOrderNatAt f (z : ℂ) : ℝ) * ‖(z : ℂ)‖⁻¹ ^ s)]
    calc
      ∑ n ∈ u.image idx,
          ∑ z ∈ u with idx z = n,
            (analyticOrderNatAt f (z : ℂ) : ℝ) * ‖(z : ℂ)‖⁻¹ ^ s
          ≤ ∑ n ∈ u.image idx, bound n := by
            apply Finset.sum_le_sum
            intro n hn
            cases n with
            | zero =>
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · intro z hz
                simp only [Finset.mem_filter] at hz
                have hz_lt : ‖(z : ℂ)‖ < R0 := by
                  have h := hidx_upper z
                  rw [hz.2, pow_zero, mul_one] at h
                  exact h
                simp only [small, Set.Finite.mem_toFinset]
                exact hz_lt.le
              · intro z hz hnot
                positivity
            | succ n =>
              let v := u.filter (fun z => idx z = n + 1)
              have hv_radius : ∀ z ∈ v,
                  ‖(z : ℂ)‖ ≤ R0 * (2 : ℝ) ^ (n + 1) := by
                intro z hz
                have h := hidx_upper z
                rw [(Finset.mem_filter.mp hz).2] at h
                exact h.le
              have hv_weight :
                  (∑ z ∈ v, (analyticOrderNatAt f (z : ℂ) : ℝ)) ≤
                    C * (R0 * (2 : ℝ) ^ (n + 1)) ^ alpha := by
                apply hcount
                · have hp : (1 : ℝ) ≤ (2 : ℝ) ^ (n + 1) :=
                    one_le_pow₀ (by norm_num)
                  calc
                    R0 = R0 * 1 := by ring
                    _ ≤ R0 * (2 : ℝ) ^ (n + 1) :=
                      mul_le_mul_of_nonneg_left hp hR0_pos.le
                · exact hv_radius
              have hterm : ∀ z ∈ v,
                  (analyticOrderNatAt f (z : ℂ) : ℝ) * ‖(z : ℂ)‖⁻¹ ^ s ≤
                    (analyticOrderNatAt f (z : ℂ) : ℝ) *
                      (R0 * (2 : ℝ) ^ n) ^ (-s) := by
                intro z hz
                apply mul_le_mul_of_nonneg_left
                · have hz_lower := hidx_lower z n (Finset.mem_filter.mp hz).2
                  rw [Real.inv_rpow (norm_nonneg (z : ℂ)),
                    ← Real.rpow_neg (norm_nonneg (z : ℂ))]
                  exact Real.rpow_le_rpow_of_nonpos (by positivity) hz_lower (by linarith)
                · positivity
              calc
                ∑ z ∈ u with idx z = n + 1,
                    (analyticOrderNatAt f (z : ℂ) : ℝ) * ‖(z : ℂ)‖⁻¹ ^ s
                    ≤ ∑ z ∈ v,
                      (analyticOrderNatAt f (z : ℂ) : ℝ) *
                        (R0 * (2 : ℝ) ^ n) ^ (-s) := by
                          apply Finset.sum_le_sum
                          intro z hz
                          exact hterm z hz
                _ = (∑ z ∈ v, (analyticOrderNatAt f (z : ℂ) : ℝ)) *
                      (R0 * (2 : ℝ) ^ n) ^ (-s) := by
                        rw [Finset.sum_mul]
                _ ≤ C * (R0 * (2 : ℝ) ^ (n + 1)) ^ alpha *
                      (R0 * (2 : ℝ) ^ n) ^ (-s) := by
                        gcongr
                _ = bound (n + 1) := by
                  simp only [bound, A, q]
                  rw [Real.mul_rpow hR0_pos.le (by positivity),
                    Real.mul_rpow hR0_pos.le (by positivity)]
                  rw [show (((2 : ℝ) ^ (n + 1)) ^ alpha) =
                        ((2 : ℝ) ^ alpha) ^ (n + 1) by
                    rw [← Real.rpow_natCast, ← Real.rpow_mul htwo_pos.le,
                      mul_comm, Real.rpow_mul htwo_pos.le, Real.rpow_natCast]]
                  rw [show (((2 : ℝ) ^ n) ^ (-s)) = ((2 : ℝ) ^ (-s)) ^ n by
                    rw [← Real.rpow_natCast, ← Real.rpow_mul htwo_pos.le,
                      mul_comm, Real.rpow_mul htwo_pos.le, Real.rpow_natCast]]
                  rw [pow_succ]
                  rw [show R0 ^ (alpha - s) = R0 ^ alpha * R0 ^ (-s) by
                    rw [sub_eq_add_neg, Real.rpow_add hR0_pos]]
                  rw [show (2 : ℝ) ^ (alpha - s) = 2 ^ alpha * 2 ^ (-s) by
                    rw [sub_eq_add_neg, Real.rpow_add htwo_pos]]
                  rw [mul_pow]
                  ring
      _ ≤ ∑' n, bound n :=
        hbound_summable.sum_le_tsum _ (fun n hn => hbound_nonneg n)

/-- Multiplicity-weighted summability of the distinct nonzero zeros at every
real exponent strictly above the order. -/
theorem summable_zero_multiplicity_rpow_of_order_lt
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (hf_ne : ¬ f = 0)
    (s : ℝ) (hs_order : entireOrder f < (s : EReal)) :
    Summable (fun z : {w : ℂ // f w = 0 ∧ w ≠ 0} =>
      (analyticOrderNatAt f (z : ℂ) : ℝ) * ‖(z : ℂ)‖⁻¹ ^ s) := by
  have hord_ne_top : entireOrder f ≠ ⊤ :=
    ne_of_lt (hs_order.trans (EReal.coe_lt_top s))
  have hord_ne_bot : entireOrder f ≠ ⊥ :=
    ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (entireOrder_nonneg f hf hf_ne))
  let rho := (entireOrder f).toReal
  have hrho_nonneg : 0 ≤ rho :=
    EReal.toReal_nonneg (entireOrder_nonneg f hf hf_ne)
  have hrho_lt_s : rho < s := by
    have hcoe : (rho : EReal) = entireOrder f :=
      EReal.coe_toReal hord_ne_top hord_ne_bot
    rw [← hcoe] at hs_order
    exact_mod_cast hs_order
  let alpha := (rho + s) / 2
  have halpha_pos : 0 < alpha := by
    dsimp [alpha]
    linarith
  have hrho_lt_alpha : rho < alpha := by
    dsimp [alpha]
    linarith
  have halpha_lt_s : alpha < s := by
    dsimp [alpha]
    linarith
  have halpha_order : entireOrder f < (alpha : EReal) := by
    rw [← EReal.coe_toReal hord_ne_top hord_ne_bot]
    exact EReal.coe_lt_coe_iff.mpr hrho_lt_alpha
  obtain ⟨C, R0, hC, hR0, hcount⟩ :=
    finite_zero_multiplicity_sum_eventually_le_rpow f hf hf_ne alpha halpha_pos halpha_order
  exact summable_weighted_rpow_inv_of_counting_bound f hf hf_ne s alpha
    halpha_lt_s halpha_pos C R0 hC hR0 hcount

/-- Safe sequence-level transfer for Weierstrass enumeration. Nonzero entries
must be distinct, and the supplied multiplicity may not exceed the analytic
order of the corresponding zero. -/
theorem finite_order_zero_summable_weighted
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (hf_ne : ¬ f = 0)
    (hfin : HasFiniteOrder f)
    (a₀ : ℕ → ℂ) (ha₀ : ∀ k, a₀ k ≠ 0 → f (a₀ k) = 0)
    (ha₀_inj : Set.InjOn a₀ {k | a₀ k ≠ 0})
    (mult : ℕ → ℕ) (hmult_zero : ∀ k, a₀ k = 0 → mult k = 0)
    (hmult_le : ∀ k, a₀ k ≠ 0 → mult k ≤ analyticOrderNatAt f (a₀ k)) :
    let p := Nat.floor (entireOrder f).toReal
    Summable (fun k => (mult k : ℝ) * ‖a₀ k‖⁻¹ ^ ((p : ℝ) + 1)) := by
  dsimp only
  let p := Nat.floor (entireOrder f).toReal
  let s : ℝ := (p : ℝ) + 1
  have hord_ne_top : entireOrder f ≠ ⊤ := ne_of_lt hfin
  have hord_ne_bot : entireOrder f ≠ ⊥ :=
    ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (entireOrder_nonneg f hf hf_ne))
  have hs_order : entireOrder f < (s : EReal) := by
    rw [← EReal.coe_toReal hord_ne_top hord_ne_bot]
    exact_mod_cast (show (entireOrder f).toReal < s by
      simpa only [s, p, Nat.cast_add, Nat.cast_one] using
        Nat.lt_floor_add_one (entireOrder f).toReal)
  have hzero := summable_zero_multiplicity_rpow_of_order_lt f hf hf_ne s hs_order
  let K := {k : ℕ // a₀ k ≠ 0}
  let Z := {z : ℂ // f z = 0 ∧ z ≠ 0}
  let e : K → Z := fun k => ⟨a₀ k, ha₀ k k.2, k.2⟩
  have he_inj : Function.Injective e := by
    intro i j hij
    apply Subtype.ext
    apply ha₀_inj i.2 j.2
    exact congrArg Subtype.val hij
  have hmajorant : Summable (fun k : K =>
      (analyticOrderNatAt f (a₀ k) : ℝ) * ‖a₀ k‖⁻¹ ^ s) := by
    simpa only [e] using hzero.comp_injective he_inj
  have hrestricted : Summable (fun k : K =>
      (mult k : ℝ) * ‖a₀ k‖⁻¹ ^ s) := by
    apply hmajorant.of_nonneg_of_le
    · intro k
      positivity
    · intro k
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast hmult_le k k.2
      · positivity
  have hindicator : Summable ({k : ℕ | a₀ k ≠ 0}.indicator
      (fun k => (mult k : ℝ) * ‖a₀ k‖⁻¹ ^ s)) := by
    exact summable_subtype_iff_indicator.mp hrestricted
  have hfull : Summable (fun k => (mult k : ℝ) * ‖a₀ k‖⁻¹ ^ s) := by
    apply hindicator.congr
    intro k
    by_cases hk : a₀ k = 0
    · simp [hk, hmult_zero k hk]
    · simp [hk]
  simpa only [s, p] using hfull


end ArithmeticHodge.Analysis.EntireFunction

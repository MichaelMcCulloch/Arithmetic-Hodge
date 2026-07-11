import CanonicalFactorizationScratch
import CanonicalProductLowerScratch
import GrowthBoundSoundScratch
import ArithmeticHodge.Analysis.ZetaProduct
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Topology.Algebra.InfiniteSum.Real

set_option autoImplicit false

open Complex Filter Topology Real Set Metric

namespace ArithmeticHodge.Analysis.EntireFunction

/-- Transfer multiplicity-weighted zero summability to an opaque canonical
sequence using its analytic-order specification. -/
theorem canonical_sequence_summable_of_order_lt_scratch
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (hf_ne : ¬ f = 0)
    (a : ℕ → ℂ) (p : ℕ)
    (hzeros : ∀ n, a n ≠ 0 → f (a n) = 0)
    (hconv : Summable (fun n ↦ ‖a n‖⁻¹ ^ ((p : ℝ) + 1)))
    (horders : ∀ z, f z = 0 → z ≠ 0 →
      analyticOrderAt f z =
        analyticOrderAt (fun w ↦ ∏' n, weierstraßElementary p (w / a n)) z)
    (beta : ℝ) (hbeta : 0 < beta)
    (horder : entireOrder f < (beta : EReal)) :
    Summable (fun n ↦ ‖a n‖⁻¹ ^ beta) := by
  let K := {n : ℕ // a n ≠ 0}
  let Z := {z : ℂ // f z = 0 ∧ z ≠ 0}
  let e : K → Z := fun n ↦ ⟨a n, hzeros n n.2, n.2⟩
  let part : Z → Set K := fun z ↦ {n | e n = z}
  have hweighted : Summable (fun z : Z ↦
      (analyticOrderNatAt f (z : ℂ) : ℝ) * ‖(z : ℂ)‖⁻¹ ^ beta) := by
    simpa only [Z] using
      summable_zero_multiplicity_rpow_of_order_lt f hf hf_ne beta horder
  have hfiber_finite : ∀ z : Z, (part z).Finite := by
    intro z
    have hz_norm : 0 < ‖(z : ℂ)‖ := norm_pos_iff.mpr z.2.2
    have hindices : Set.Finite
        {n : ℕ | a n ≠ 0 ∧ ‖a n‖ ≤ ‖(z : ℂ)‖} :=
      finite_nonzero_indices_norm_le a ((p : ℝ) + 1) (by positivity)
        hconv ‖(z : ℂ)‖ hz_norm
    apply Set.Finite.of_finite_image
    · apply hindices.subset
      intro n hn
      obtain ⟨k, hk, rfl⟩ := hn
      have heq : e k = z := hk
      have haeq : a k = (z : ℂ) := congrArg Subtype.val heq
      exact ⟨k.2, by rw [haeq]⟩
    · exact Subtype.val_injective.injOn
  have hfiber_card_le : ∀ z : Z,
      Nat.card (part z) ≤ analyticOrderNatAt f (z : ℂ) := by
    intro z
    let I : Set ℕ := {n | a n = (z : ℂ)}
    have hI_finite : I.Finite := by
      have hz_norm : 0 < ‖(z : ℂ)‖ := norm_pos_iff.mpr z.2.2
      have hindices := finite_nonzero_indices_norm_le a ((p : ℝ) + 1)
        (by positivity) hconv ‖(z : ℂ)‖ hz_norm
      apply hindices.subset
      intro n hn
      exact ⟨by rw [hn]; exact z.2.2, by rw [hn]⟩
    let S : Finset ℕ := hI_finite.toFinset
    have hS_val : ∀ n ∈ S, a n = (z : ℂ) := by
      intro n hn
      simpa only [S, Set.Finite.mem_toFinset, I, Set.mem_setOf_eq] using hn
    have hS_compl : ∀ n, n ∉ S → a n ≠ (z : ℂ) := by
      intro n hn heq
      apply hn
      simpa only [S, Set.Finite.mem_toFinset, I, Set.mem_setOf_eq] using heq
    have hprod_order := analyticOrderAt_tprod_weierstraß a p hconv (z : ℂ)
      z.2.2 S hS_val hS_compl
    have horder_nat : analyticOrderNatAt f (z : ℂ) = S.card := by
      simp only [analyticOrderNatAt]
      rw [horders z z.2.1 z.2.2, hprod_order]
      simp
    let toS : part z → {n // n ∈ S} := fun k ↦ ⟨k.1.1, by
      have heq : e k.1 = z := k.2
      have haeq : a k.1.1 = (z : ℂ) := congrArg Subtype.val heq
      by_contra hn
      exact hS_compl k.1.1 hn haeq⟩
    have htoS : Function.Injective toS := by
      intro i j hij
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun n : {n // n ∈ S} ↦ (n : ℕ)) hij
    calc
      Nat.card (part z) ≤ Nat.card {n // n ∈ S} :=
        Nat.card_le_card_of_injective toS htoS
      _ = S.card := by simp
      _ = analyticOrderNatAt f (z : ℂ) := horder_nat.symm
  have hpart_unique : ∀ n : K, ∃! z : Z, n ∈ part z := by
    intro n
    refine ⟨e n, by simp [part], ?_⟩
    intro z hz
    simpa [part] using hz.symm
  have hK : Summable (fun n : K ↦ ‖a n‖⁻¹ ^ beta) := by
    rw [summable_partition (fun n : K ↦
      Real.rpow_nonneg (inv_nonneg.mpr (norm_nonneg (a n))) beta) hpart_unique]
    constructor
    · intro z
      simpa only [Function.comp_apply] using (hfiber_finite z).summable
        (fun n : K ↦ ‖a n‖⁻¹ ^ beta)
    · apply hweighted.of_nonneg_of_le
      · intro z
        positivity
      · intro z
        letI : Fintype (part z) := (hfiber_finite z).fintype
        rw [tsum_fintype]
        have hconst : ∀ n : part z,
            ‖a (n : K)‖⁻¹ ^ beta = ‖(z : ℂ)‖⁻¹ ^ beta := by
          intro n
          have heq : e n.1 = z := n.2
          rw [show a (n : K) = (z : ℂ) from congrArg Subtype.val heq]
        simp_rw [hconst]
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_eq_nat_card]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hfiber_card_le z)
          (Real.rpow_nonneg (inv_nonneg.mpr (norm_nonneg _)) _)
  have hindicator : Summable ({n : ℕ | a n ≠ 0}.indicator
      (fun n ↦ ‖a n‖⁻¹ ^ beta)) :=
    summable_subtype_iff_indicator.mp hK
  apply hindicator.congr
  intro n
  by_cases hn : a n = 0
  · simp [hn, Real.zero_rpow hbeta.ne']
  · simp [hn]

/-- An entire function with polynomial growth of exponent strictly below two
has affine logarithm.  This is the Cauchy-estimate step needed for the
order-one Hadamard factorization. -/
theorem affine_of_growth_lt_two_scratch
    (g : ℂ → ℂ) (hg : Differentiable ℂ g)
    (C alpha : ℝ) (hC : 0 < C) (halpha_nn : 0 ≤ alpha)
    (halpha_lt : alpha < 2)
    (hgrowth : ∀ z, ‖g z‖ ≤ C * (1 + ‖z‖) ^ alpha) :
    ∃ A B : ℂ, ∀ z, g z = A + B * z := by
  have hvan : ∀ c : ℂ, iteratedDeriv 2 g c = 0 := by
    have cauchy : ∀ (c : ℂ) (R : ℝ), 0 < R →
        ‖iteratedDeriv 2 g c‖ ≤
        ↑(2 : ℕ).factorial * (C * (1 + ‖c‖ + R) ^ alpha) / R ^ (2 : ℕ) :=
      fun c R hR => norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le _ hR
        hg.diffContOnCl fun z hz => by
          rw [mem_sphere_iff_norm] at hz
          exact (hgrowth z).trans (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (by positivity) (by linarith [norm_le_insert' z c]) halpha_nn)
            hC.le)
    set Bd := ↑(2 : ℕ).factorial * C * (2 : ℝ) ^ alpha with hBd_def
    have hBd_pos : 0 < Bd := by positivity
    have hbdd : ∀ c : ℂ, ‖iteratedDeriv 2 g c‖ ≤ Bd := by
      intro c
      have hR : (0 : ℝ) < ‖c‖ + 1 := by positivity
      have h1 := cauchy c (‖c‖ + 1) hR
      have h2 : 1 + ‖c‖ + (‖c‖ + 1) = 2 * (‖c‖ + 1) := by ring
      rw [h2] at h1
      have h3 : (2 * (‖c‖ + 1)) ^ alpha = 2 ^ alpha * (‖c‖ + 1) ^ alpha :=
        Real.mul_rpow (by positivity : (0 : ℝ) ≤ 2)
          (by positivity : (0 : ℝ) ≤ ‖c‖ + 1)
      have h4 : (‖c‖ + 1) ^ alpha ≤ (‖c‖ + 1) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le
          (by linarith [norm_nonneg c] : 1 ≤ ‖c‖ + 1) halpha_lt.le
      have h5 : (‖c‖ + 1) ^ (2 : ℝ) = (‖c‖ + 1) ^ (2 : ℕ) :=
        Real.rpow_natCast (‖c‖ + 1) 2
      calc
        ‖iteratedDeriv 2 g c‖
            ≤ ↑(2 : ℕ).factorial * (C * (2 * (‖c‖ + 1)) ^ alpha) /
                (‖c‖ + 1) ^ (2 : ℕ) := h1
        _ = ↑(2 : ℕ).factorial *
              (C * (2 ^ alpha * (‖c‖ + 1) ^ alpha)) /
                (‖c‖ + 1) ^ (2 : ℕ) := by rw [h3]
        _ ≤ ↑(2 : ℕ).factorial *
              (C * (2 ^ alpha * (‖c‖ + 1) ^ (2 : ℕ))) /
                (‖c‖ + 1) ^ (2 : ℕ) := by
          gcongr
          exact h4.trans (h5 ▸ le_refl _)
        _ = Bd := by
          rw [hBd_def]
          field_simp
    have hg2_diff : Differentiable ℂ (iteratedDeriv 2 g) :=
      hg.contDiff.differentiable_iteratedDeriv 2 (WithTop.coe_lt_top _)
    have hg2_bdd : Bornology.IsBounded (Set.range (iteratedDeriv 2 g)) :=
      (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := Bd)).subset
        (Set.range_subset_iff.mpr fun c => mem_closedBall_zero_iff.mpr (hbdd c))
    have hconst : ∀ c : ℂ, iteratedDeriv 2 g c = iteratedDeriv 2 g 0 :=
      fun c => hg2_diff.apply_eq_apply_of_bounded hg2_bdd c 0
    suffices h0 : iteratedDeriv 2 g 0 = 0 by
      intro c
      rw [hconst c, h0]
    by_contra hne
    rw [← ne_eq, ← norm_pos_iff] at hne
    set delta := ‖iteratedDeriv 2 g 0‖
    set beta := (2 : ℝ) - alpha with hbeta_def
    have hbeta_pos : 0 < beta := by simp [hbeta_def]; linarith
    obtain ⟨n, hn⟩ := exists_nat_gt (max 1 ((Bd / delta) ^ beta⁻¹))
    have hn_pos : (0 : ℝ) < n := by
      linarith [le_max_left 1 ((Bd / delta) ^ beta⁻¹)]
    have hn_large : (Bd / delta) ^ beta⁻¹ < (n : ℝ) := by
      linarith [le_max_right 1 ((Bd / delta) ^ beta⁻¹)]
    have hn_rpow : (n : ℝ) ^ beta > Bd / delta := by
      have h0 : (0 : ℝ) ≤ (Bd / delta) ^ beta⁻¹ := by positivity
      calc
        (n : ℝ) ^ beta > ((Bd / delta) ^ beta⁻¹) ^ beta :=
          Real.rpow_lt_rpow h0 hn_large hbeta_pos
        _ = Bd / delta := by
          rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ Bd / delta),
            inv_mul_cancel₀ hbeta_pos.ne', Real.rpow_one]
    have h_cauchy := cauchy 0 n hn_pos
    simp only [norm_zero, add_zero] at h_cauchy
    have h_1n : (1 : ℝ) + ↑n ≤ 2 * ↑n := by
      linarith [le_max_left 1 ((Bd / delta) ^ beta⁻¹)]
    have h_sphere : (1 + (n : ℝ)) ^ alpha ≤ (2 * (n : ℝ)) ^ alpha :=
      Real.rpow_le_rpow (by positivity) h_1n halpha_nn
    have h_split : (2 * (n : ℝ)) ^ alpha = 2 ^ alpha * (n : ℝ) ^ alpha :=
      Real.mul_rpow (by positivity : (0 : ℝ) ≤ 2) hn_pos.le
    have h_rpow_div : (n : ℝ) ^ alpha / (n : ℝ) ^ (2 : ℕ) =
        (n : ℝ) ^ (-beta) := by
      rw [hbeta_def, neg_sub, Real.rpow_sub hn_pos]
      exact congrArg (fun x : ℝ ↦ (n : ℝ) ^ alpha / x)
        (Real.rpow_natCast (n : ℝ) 2).symm
    have h_rpow_neg : (n : ℝ) ^ (-beta) = ((n : ℝ) ^ beta)⁻¹ :=
      Real.rpow_neg hn_pos.le beta
    have h_upper : delta ≤ Bd * ((n : ℝ) ^ beta)⁻¹ := by
      calc
        delta ≤ ↑(2 : ℕ).factorial * (C * (1 + ↑n) ^ alpha) /
            (↑n) ^ (2 : ℕ) := h_cauchy
        _ ≤ ↑(2 : ℕ).factorial * (C * (2 ^ alpha * (↑n) ^ alpha)) /
            (↑n) ^ (2 : ℕ) := by
          gcongr
          calc
            (1 + (↑n : ℝ)) ^ alpha ≤ (2 * ↑n) ^ alpha := h_sphere
            _ = 2 ^ alpha * (↑n) ^ alpha := h_split
        _ = Bd * ((n : ℝ) ^ alpha / (n : ℝ) ^ (2 : ℕ)) := by
          rw [hBd_def]
          field_simp
        _ = Bd * (n : ℝ) ^ (-beta) := by rw [h_rpow_div]
        _ = Bd * ((n : ℝ) ^ beta)⁻¹ := by rw [h_rpow_neg]
    have h_lower : Bd * ((n : ℝ) ^ beta)⁻¹ < delta := by
      rw [← div_eq_mul_inv, div_lt_iff₀ (by positivity : 0 < (n : ℝ) ^ beta), mul_comm]
      exact (div_lt_iff₀ hne).mp hn_rpow
    linarith
  have hd_diff : Differentiable ℂ (deriv g) :=
    hg.contDiff.differentiable_deriv_two
  have hdd : ∀ z, deriv (deriv g) z = 0 := by
    intro z
    simpa [iteratedDeriv_succ, iteratedDeriv_zero] using hvan z
  let B : ℂ := deriv g 0
  have hd_const : ∀ z, deriv g z = B := by
    intro z
    exact is_const_of_deriv_eq_zero hd_diff hdd z 0
  have hlin : Differentiable ℂ (fun z : ℂ ↦ B * z) :=
    (differentiable_const B).mul differentiable_id
  have hsub_diff : Differentiable ℂ (fun z : ℂ ↦ g z - B * z) :=
    hg.sub hlin
  have hsub_deriv : ∀ z, deriv (fun w : ℂ ↦ g w - B * w) z = 0 := by
    intro z
    have hg_at : HasDerivAt g (deriv g z) z :=
      hg.differentiableAt.hasDerivAt
    have hlin_at : HasDerivAt (fun w : ℂ ↦ B * w) B z :=
      by simpa using (hasDerivAt_id z).const_mul B
    calc
      deriv (fun w : ℂ ↦ g w - B * w) z = deriv g z - B :=
        (hg_at.sub hlin_at).deriv
      _ = 0 := by rw [hd_const z, sub_self]
  refine ⟨g 0, B, fun z ↦ ?_⟩
  have h := is_const_of_deriv_eq_zero hsub_diff hsub_deriv z 0
  simp only [mul_zero, sub_zero] at h
  calc
    g z = B * z + g 0 := eq_add_of_sub_eq' h
    _ = g 0 + B * z := add_comm _ _

/-- Unconditional genus-one Hadamard product for xi, derived through the
canonical factorization and the sound logarithm-growth bound. -/
theorem xi_hadamard_product_closed_scratch :
    ∃ (m : ℕ) (A B : ℂ) (zeros : ℕ → ℂ),
      (∀ n, zeros n ≠ 0) ∧
      (∀ n, xiFunction (zeros n) = 0) ∧
      Summable (fun n => (‖zeros n‖⁻¹) ^ (2 : ℝ)) ∧
      ∀ s, xiFunction s =
        s ^ m * Complex.exp (A + B * s) *
        ∏' n, weierstraßElementary 1 (s / zeros n) := by
  have hfin : HasFiniteOrder xiFunction := by
    show entireOrder xiFunction < ⊤
    rw [xiFunction_order]
    exact EReal.coe_lt_top 1
  obtain ⟨m, g, a, p, hg, hzeros, hconv, hfact, hp, _hcover, horders⟩ :=
    weierstraß_factorization_canonical_scratch xiFunction differentiable_xiFunction
      xiFunction_ne_const_zero hfin
  have hp1 : p = 1 := by
    rw [xiFunction_order] at hp
    simpa using hp
  rw [hp1] at hconv hfact horders
  have hsumm_beta : Summable (fun n ↦ ‖a n‖⁻¹ ^ (3 / 2 : ℝ)) :=
    canonical_sequence_summable_of_order_lt_scratch
      xiFunction differentiable_xiFunction xiFunction_ne_const_zero a 1
      hzeros hconv horders (3 / 2 : ℝ) (by norm_num) (by
        rw [xiFunction_order]
        exact EReal.coe_lt_coe_iff.mpr (by norm_num))
  obtain ⟨C, hC, hgrowth⟩ := canonical_factorization_growth
    xiFunction differentiable_xiFunction m g a 1 hg hfact
      (3 / 2 : ℝ) (7 / 4 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) hsumm_beta (by
        rw [xiFunction_order]
        exact EReal.coe_lt_coe_iff.mpr (by norm_num))
  obtain ⟨A, B, hg_affine⟩ := affine_of_growth_lt_two_scratch
    g hg C (7 / 4 : ℝ) hC (by norm_num) (by norm_num) hgrowth
  have hm : m = 0 := by
    by_contra hm
    have h0 := hfact 0
    rw [xiFunction_zero_val] at h0
    simp [zero_pow hm] at h0
  have hconv2 : Summable (fun n ↦ (‖a n‖⁻¹) ^ (2 : ℝ)) := by
    simpa only [Nat.cast_one, one_add_one_eq_two] using hconv
  have hfactorization : ∀ z, xiFunction z = Complex.exp (A + B * z) *
      ∏' n, weierstraßElementary 1 (z / a n) := by
    intro z
    simpa [hm, hg_affine z] using hfact z
  exact xi_hadamard_product_reindex_bridge A B a hzeros hconv2 hfactorization

#print axioms canonical_sequence_summable_of_order_lt_scratch
#print axioms affine_of_growth_lt_two_scratch
#print axioms xi_hadamard_product_closed_scratch

end ArithmeticHodge.Analysis.EntireFunction

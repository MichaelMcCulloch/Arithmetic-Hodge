import XiHadamardClosureScratch
import ZeroExponentScratch

set_option autoImplicit false

open Complex Filter Topology Real Set Metric

namespace ArithmeticHodge.Analysis.EntireFunction

/-- Any multiplicity-weighted summability bound on the distinct zeros
transfers to a canonical sequence whose fiber cardinalities are controlled by
analytic order. -/
theorem canonical_sequence_summable_of_weighted_repair2_scratch
    (f : ℂ → ℂ) (a : ℕ → ℂ) (p : ℕ)
    (hzeros : ∀ n, a n ≠ 0 → f (a n) = 0)
    (hconv : Summable (fun n ↦ ‖a n‖⁻¹ ^ ((p : ℝ) + 1)))
    (horders : ∀ z, f z = 0 → z ≠ 0 →
      analyticOrderAt f z =
        analyticOrderAt (fun w ↦ ∏' n, weierstraßElementary p (w / a n)) z)
    (beta : ℝ) (hbeta : 0 < beta)
    (hweighted : Summable (fun z : {w : ℂ // f w = 0 ∧ w ≠ 0} ↦
      (analyticOrderNatAt f (z : ℂ) : ℝ) * ‖(z : ℂ)‖⁻¹ ^ beta)) :
    Summable (fun n ↦ ‖a n‖⁻¹ ^ beta) := by
  let K := {n : ℕ // a n ≠ 0}
  let Z := {z : ℂ // f z = 0 ∧ z ≠ 0}
  let e : K → Z := fun n ↦ ⟨a n, hzeros n n.2, n.2⟩
  let part : Z → Set K := fun z ↦ {n | e n = z}
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
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
          Fintype.card_eq_nat_card]
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

/-- The completed-zeta analogue of the closed xi factorization. -/
theorem completedZeta_canonical_affine_repair2_scratch :
    ∃ (m : ℕ) (A B : ℂ) (a : ℕ → ℂ),
      (∀ n, a n ≠ 0 → completedRiemannZeta₀ (a n) = 0) ∧
      Summable (fun n => ‖a n‖⁻¹ ^ (2 : ℝ)) ∧
      (∀ beta : ℝ, 1 < beta → Summable (fun n => ‖a n‖⁻¹ ^ beta)) ∧
      (∀ z, completedRiemannZeta₀ z = 0 → z ≠ 0 →
        analyticOrderAt completedRiemannZeta₀ z =
          analyticOrderAt
            (fun w ↦ ∏' n, weierstraßElementary 1 (w / a n)) z) ∧
      ∀ z, completedRiemannZeta₀ z = z ^ m * Complex.exp (A + B * z) *
        ∏' n, weierstraßElementary 1 (z / a n) := by
  have hf_ne : ¬ completedRiemannZeta₀ = 0 := by
    intro hf
    have h := completedZeta₀_even_re_lower 0
    rw [show completedRiemannZeta₀ (((2 * (0 + 12) : ℕ) : ℂ)) = 0 from
      congr_fun hf (((2 * (0 + 12) : ℕ) : ℂ))] at h
    norm_num at h
  have hfin : HasFiniteOrder completedRiemannZeta₀ := by
    show entireOrder completedRiemannZeta₀ < ⊤
    rw [completedZeta_order]
    exact EReal.coe_lt_top 1
  obtain ⟨m, g, a, p, hg, hzeros, hconv, hfact, hp, _hcover, horders⟩ :=
    weierstraß_factorization_canonical_scratch completedRiemannZeta₀
      differentiable_completedZeta₀ hf_ne hfin
  have hp1 : p = 1 := by
    rw [completedZeta_order] at hp
    simpa using hp
  rw [hp1] at hconv hfact horders
  have hsumm_beta : Summable (fun n ↦ ‖a n‖⁻¹ ^ (3 / 2 : ℝ)) :=
    canonical_sequence_summable_of_order_lt_scratch
      completedRiemannZeta₀ differentiable_completedZeta₀ hf_ne a 1
      hzeros hconv horders (3 / 2 : ℝ) (by norm_num) (by
        rw [completedZeta_order]
        exact EReal.coe_lt_coe_iff.mpr (by norm_num))
  obtain ⟨C, hC, hgrowth⟩ := canonical_factorization_growth
    completedRiemannZeta₀ differentiable_completedZeta₀ m g a 1 hg hfact
      (3 / 2 : ℝ) (7 / 4 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) hsumm_beta (by
        rw [completedZeta_order]
        exact EReal.coe_lt_coe_iff.mpr (by norm_num))
  obtain ⟨A, B, hg_affine⟩ := affine_of_growth_lt_two_scratch
    g hg C (7 / 4 : ℝ) hC (by norm_num) (by norm_num) hgrowth
  refine ⟨m, A, B, a, hzeros, ?_, ?_, horders, ?_⟩
  · simpa only [Nat.cast_one, one_add_one_eq_two] using hconv
  · intro beta hbeta
    exact canonical_sequence_summable_of_order_lt_scratch
      completedRiemannZeta₀ differentiable_completedZeta₀ hf_ne a 1
      hzeros hconv horders beta (by linarith) (by
        rw [completedZeta_order]
        exact EReal.coe_lt_coe_iff.mpr hbeta)
  · intro z
    simpa [hg_affine z] using hfact z

#print axioms completedZeta_canonical_affine_repair2_scratch

/-- The strongest unconditional consequence currently supported by the
canonical product: a zero-padded, multiplicity-repeated completed-zeta zero
sequence has convergence exponent one. -/
theorem exists_completedZeta_zero_sequence_exponent_one_repair2_scratch :
    ∃ (m : ℕ) (A B : ℂ) (zeros : ℕ → ℂ),
      (∀ n, zeros n ≠ 0 → completedRiemannZeta₀ (zeros n) = 0) ∧
      Summable (fun n => ‖zeros n‖⁻¹ ^ (2 : ℝ)) ∧
      (∀ beta : ℝ, 1 < beta → Summable (fun n => ‖zeros n‖⁻¹ ^ beta)) ∧
      (∀ z, completedRiemannZeta₀ z = 0 → z ≠ 0 →
        analyticOrderAt completedRiemannZeta₀ z =
          analyticOrderAt
            (fun w ↦ ∏' n, weierstraßElementary 1 (w / zeros n)) z) ∧
      (∀ z, completedRiemannZeta₀ z = z ^ m * Complex.exp (A + B * z) *
        ∏' n, weierstraßElementary 1 (z / zeros n)) ∧
      ∀ s : ℝ, 0 < s → s < 1 →
        ¬ Summable (fun n => ‖zeros n‖⁻¹ ^ s) := by
  obtain ⟨m, A, B, zeros, hzeros, hsumm2, hsumm_above, horders,
      hfactorization⟩ :=
    completedZeta_canonical_affine_repair2_scratch
  refine ⟨m, A, B, zeros, hzeros, hsumm2, hsumm_above, horders,
    hfactorization, ?_⟩
  intro s hs₀ hs₁ hsumm
  exact completedZeta_no_genus_one_affine_with_inv_rpow_lt_one_scratch
    s hs₀ hs₁ ⟨m, A, B, zeros, hsumm, hfactorization⟩

#print axioms exists_completedZeta_zero_sequence_exponent_one_repair2_scratch

/-- A padding-free reindexing that preserves inverse-power
summability at every positive exponent, not just at the construction
exponent. -/
private theorem exists_nonzero_reindex_all_exponents_repair2_scratch
    (a : ℕ → ℂ) (hinf : Set.Infinite {n : ℕ | a n ≠ 0}) :
    ∃ b : ℕ → ℂ,
      (∀ n, b n ≠ 0) ∧
      (∀ beta : ℝ, 0 < beta →
        (Summable (fun n => ‖b n‖⁻¹ ^ beta) ↔
          Summable (fun n => ‖a n‖⁻¹ ^ beta))) ∧
      ∀ (p : ℕ) (z : ℂ),
        ∏' n, weierstraßElementary p (z / b n) =
          ∏' n, weierstraßElementary p (z / a n) := by
  let S : Set ℕ := {n : ℕ | a n ≠ 0}
  letI : Infinite S := hinf.to_subtype
  letI : Denumerable S := Classical.choice (nonempty_denumerable S)
  let e : ℕ ≃ S := (Denumerable.eqv S).symm
  let b : ℕ → ℂ := fun n => a (e n)
  refine ⟨b, ?_, ?_, ?_⟩
  · intro n
    exact (e n).property
  · intro beta hbeta
    constructor
    · intro hb
      have hsub : Summable (fun i : S => ‖a i‖⁻¹ ^ beta) := by
        exact e.summable_iff.mp hb
      have hindicator : Summable (S.indicator (fun n => ‖a n‖⁻¹ ^ beta)) :=
        summable_subtype_iff_indicator.mp hsub
      apply hindicator.congr
      intro n
      by_cases hn : a n = 0
      · simp [S, hn, Real.zero_rpow hbeta.ne']
      · simp [S, hn]
    · intro ha
      have hsub : Summable (fun i : S => ‖a i‖⁻¹ ^ beta) := ha.subtype S
      exact e.summable_iff.mpr hsub
  · intro p z
    have hsupport : Function.mulSupport (fun n => weierstraßElementary p (z / a n)) ⊆ S := by
      intro n hn
      change a n ≠ 0
      intro han
      apply hn
      simp [han, weierstraßElementary_zero]
    calc
      ∏' n, weierstraßElementary p (z / b n) =
          ∏' i : S, weierstraßElementary p (z / a i) := by
        exact e.tprod_eq (fun i : S => weierstraßElementary p (z / a i))
      _ = ∏' n, weierstraßElementary p (z / a n) :=
        tprod_subtype_eq_of_mulSupport_subset hsupport

/-- A padding-free multiplicity-repeated zero sequence for `Λ₀`
whose convergence exponent is exactly one. -/
theorem exists_completedZeta_nonzero_sequence_exponent_one_repair2_scratch :
    ∃ (m : ℕ) (A B : ℂ) (zeros : ℕ → ℂ),
      (∀ n, zeros n ≠ 0) ∧
      (∀ n, completedRiemannZeta₀ (zeros n) = 0) ∧
      Summable (fun n => ‖zeros n‖⁻¹ ^ (2 : ℝ)) ∧
      (∀ beta : ℝ, 1 < beta → Summable (fun n => ‖zeros n‖⁻¹ ^ beta)) ∧
      (∀ z, completedRiemannZeta₀ z = z ^ m * Complex.exp (A + B * z) *
        ∏' n, weierstraßElementary 1 (z / zeros n)) ∧
      ∀ s : ℝ, 0 < s → s < 1 →
        ¬ Summable (fun n => ‖zeros n‖⁻¹ ^ s) := by
  obtain ⟨m, A, B, a, ha_zeros, ha_summ2, ha_summ_above, _ha_orders,
      ha_factorization, ha_diverges⟩ :=
    exists_completedZeta_zero_sequence_exponent_one_repair2_scratch
  have ha_support_infinite : Set.Infinite {n : ℕ | a n ≠ 0} := by
    intro hfinite
    let F : Finset ℕ := hfinite.toFinset
    have hsumm_half : Summable (fun n => ‖a n‖⁻¹ ^ (1 / 2 : ℝ)) := by
      apply summable_of_ne_finset_zero (s := F)
      intro n hn
      have han : a n = 0 := by
        by_contra hne
        apply hn
        simp only [F, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
        exact hne
      simp [han]
    exact ha_diverges (1 / 2 : ℝ) (by norm_num) (by norm_num) hsumm_half
  obtain ⟨zeros, hzeros_ne, hsumm_iff, hproduct⟩ :=
    exists_nonzero_reindex_all_exponents_repair2_scratch a ha_support_infinite
  have hzeros_summ2 : Summable (fun n => ‖zeros n‖⁻¹ ^ (2 : ℝ)) :=
    (hsumm_iff 2 (by norm_num)).mpr ha_summ2
  have hzeros_summ_above : ∀ beta : ℝ, 1 < beta →
      Summable (fun n => ‖zeros n‖⁻¹ ^ beta) := by
    intro beta hbeta
    exact (hsumm_iff beta (by linarith)).mpr (ha_summ_above beta hbeta)
  have hzeros_factorization : ∀ z,
      completedRiemannZeta₀ z = z ^ m * Complex.exp (A + B * z) *
        ∏' n, weierstraßElementary 1 (z / zeros n) := by
    intro z
    rw [ha_factorization z, ← hproduct 1 z]
  have hzeros_spec : ∀ n, completedRiemannZeta₀ (zeros n) = 0 := by
    intro n
    have hfactor_zero : weierstraßElementary 1 (zeros n / zeros n) = 0 := by
      rw [div_self (hzeros_ne n)]
      simp [weierstraßElementary]
    have hproduct_zero :
        ∏' k, weierstraßElementary 1 (zeros n / zeros k) = 0 :=
      tprod_of_exists_eq_zero ⟨n, hfactor_zero⟩
    rw [hzeros_factorization (zeros n), hproduct_zero, mul_zero]
  refine ⟨m, A, B, zeros, hzeros_ne, hzeros_spec, hzeros_summ2,
    hzeros_summ_above,
    hzeros_factorization, ?_⟩
  intro s hs₀ hs₁ hsumm
  exact ha_diverges s hs₀ hs₁ ((hsumm_iff s hs₀).mp hsumm)

#print axioms exists_completedZeta_nonzero_sequence_exponent_one_repair2_scratch

/-- An injective genus-one zero factorization is precisely enough
to transfer the canonical-product divergence to the distinct-zero subtype. -/
theorem completedZeta_distinct_zeros_not_summable_of_injective_factorization_repair2_scratch
    (m : ℕ) (A B : ℂ) (zeros : ℕ → ℂ)
    (hzeros_ne : ∀ n, zeros n ≠ 0)
    (hzeros : ∀ n, completedRiemannZeta₀ (zeros n) = 0)
    (hzeros_inj : Function.Injective zeros)
    (hfactorization : ∀ z,
      completedRiemannZeta₀ z = z ^ m * Complex.exp (A + B * z) *
        ∏' n, weierstraßElementary 1 (z / zeros n))
    (s : ℝ) (hs₀ : 0 < s) (hs₁ : s < 1) :
    ¬ Summable (fun z : {w : ℂ // completedRiemannZeta₀ w = 0 ∧ w ≠ 0} =>
      ‖(z : ℂ)‖⁻¹ ^ s) := by
  intro hsumm
  let Z := {w : ℂ // completedRiemannZeta₀ w = 0 ∧ w ≠ 0}
  let e : ℕ → Z := fun n => ⟨zeros n, hzeros n, hzeros_ne n⟩
  have he_inj : Function.Injective e := by
    intro i j hij
    apply hzeros_inj
    exact congrArg Subtype.val hij
  have hsequence : Summable (fun n => ‖zeros n‖⁻¹ ^ s) := by
    have hcomp := hsumm.comp_injective he_inj
    simpa only [e] using hcomp
  exact completedZeta_no_genus_one_affine_with_inv_rpow_lt_one_scratch
    s hs₀ hs₁ ⟨m, A, B, zeros, hsequence, hfactorization⟩

#print axioms
  completedZeta_distinct_zeros_not_summable_of_injective_factorization_repair2_scratch

/-- The source theorem follows if its multiplicity-repeated
Hadamard sequence can be replaced by an injective one. -/
theorem zetaZero_exponent_of_convergence_of_injective_factorization_repair2_scratch
    (m : ℕ) (A B : ℂ) (zeros : ℕ → ℂ)
    (hzeros_ne : ∀ n, zeros n ≠ 0)
    (hzeros : ∀ n, completedRiemannZeta₀ (zeros n) = 0)
    (hzeros_inj : Function.Injective zeros)
    (hfactorization : ∀ z,
      completedRiemannZeta₀ z = z ^ m * Complex.exp (A + B * z) *
        ∏' n, weierstraßElementary 1 (z / zeros n)) :
    zeroExponent completedRiemannZeta₀ = 1 := by
  have hf_ne : ¬ completedRiemannZeta₀ = 0 := by
    intro hf
    have h := completedZeta₀_even_re_lower 0
    rw [show completedRiemannZeta₀ (((2 * (0 + 12) : ℕ) : ℂ)) = 0 from
      congr_fun hf (((2 * (0 + 12) : ℕ) : ℂ))] at h
    norm_num at h
  apply le_antisymm
  · calc
      zeroExponent completedRiemannZeta₀ ≤ entireOrder completedRiemannZeta₀ :=
        zeroExponent_le_order _ differentiable_completedZeta₀ hf_ne
      _ = 1 := completedZeta_order
  · unfold zeroExponent
    apply le_sInf
    intro sigma ⟨hsigma_pos, s, hs_eq, hs_summ⟩
    rw [← hs_eq]
    by_contra hlt
    push_neg at hlt
    have hs_lt : s < 1 := by exact_mod_cast hlt
    have hs_pos : 0 < s := by
      have := hs_eq ▸ hsigma_pos
      exact_mod_cast this
    exact
      completedZeta_distinct_zeros_not_summable_of_injective_factorization_repair2_scratch
        m A B zeros hzeros_ne hzeros hzeros_inj hfactorization
        s hs_pos hs_lt hs_summ

#print axioms
  zetaZero_exponent_of_convergence_of_injective_factorization_repair2_scratch

/-- Unlike the distinct-zero series, the analytically
multiplicity-weighted series is unconditionally divergent below exponent one. -/
theorem completedZeta_weighted_zeros_not_summable_repair2_scratch
    (s : ℝ) (hs₀ : 0 < s) (hs₁ : s < 1) :
    ¬ Summable
      (fun z : {w : ℂ // completedRiemannZeta₀ w = 0 ∧ w ≠ 0} ↦
        (analyticOrderNatAt completedRiemannZeta₀ (z : ℂ) : ℝ) *
          ‖(z : ℂ)‖⁻¹ ^ s) := by
  intro hweighted
  obtain ⟨m, A, B, a, hzeros, hconv2, _hconv_above, horders,
      hfactorization⟩ := completedZeta_canonical_affine_repair2_scratch
  have hconv : Summable (fun n ↦ ‖a n‖⁻¹ ^ (((1 : ℕ) : ℝ) + 1)) := by
    simpa only [Nat.cast_one, one_add_one_eq_two] using hconv2
  have hsequence : Summable (fun n ↦ ‖a n‖⁻¹ ^ s) :=
    canonical_sequence_summable_of_weighted_repair2_scratch
      completedRiemannZeta₀ a 1 hzeros hconv horders s hs₀ hweighted
  exact completedZeta_no_genus_one_affine_with_inv_rpow_lt_one_scratch
    s hs₀ hs₁ ⟨m, A, B, a, hsequence, hfactorization⟩

#print axioms completedZeta_weighted_zeros_not_summable_repair2_scratch

/-- Multiplicity-aware counterpart of the production `zeroExponent`. -/
noncomputable def weightedZeroExponentRepair2 (f : ℂ → ℂ) : EReal :=
  sInf { (sigma : EReal) | ∃ (_hsigma : 0 < sigma) (s : ℝ)
    (_hs : (s : EReal) = sigma),
    Summable (fun z : {w : ℂ // f w = 0 ∧ w ≠ 0} ↦
      (analyticOrderNatAt f (z : ℂ) : ℝ) * ‖(z : ℂ)‖⁻¹ ^ s) }

/-- The multiplicity-aware completed-zeta exponent is exactly one. -/
theorem completedZeta_weighted_zeroExponent_eq_one_repair2_scratch :
    weightedZeroExponentRepair2 completedRiemannZeta₀ = 1 := by
  have hf_ne : ¬ completedRiemannZeta₀ = 0 := by
    intro hf
    have h := completedZeta₀_even_re_lower 0
    rw [show completedRiemannZeta₀ (((2 * (0 + 12) : ℕ) : ℂ)) = 0 from
      congr_fun hf (((2 * (0 + 12) : ℕ) : ℂ))] at h
    norm_num at h
  apply le_antisymm
  · apply le_of_forall_gt_imp_ge_of_dense
    intro sigma hsigma
    by_cases hsigma_top : sigma = ⊤
    · exact hsigma_top ▸ le_top
    have hsigma_ne_bot : sigma ≠ ⊥ :=
      (lt_of_le_of_lt bot_le hsigma).ne'
    have hsigma_pos : (0 : EReal) < sigma :=
      lt_trans (by norm_num) hsigma
    let s := sigma.toReal
    have hs_eq : (s : EReal) = sigma :=
      EReal.coe_toReal hsigma_top hsigma_ne_bot
    have hs_pos : 0 < s := EReal.toReal_pos hsigma_pos hsigma_top
    have hs_one : 1 < s := by
      have h : (1 : EReal) < (s : EReal) := by simpa only [hs_eq] using hsigma
      exact EReal.coe_lt_coe_iff.mp h
    have hs_order : entireOrder completedRiemannZeta₀ < (s : EReal) := by
      rw [completedZeta_order]
      exact EReal.coe_lt_coe_iff.mpr hs_one
    have hsumm := summable_zero_multiplicity_rpow_of_order_lt
      completedRiemannZeta₀ differentiable_completedZeta₀ hf_ne s hs_order
    rw [← hs_eq]
    exact csInf_le' ⟨by exact_mod_cast hs_pos, s, rfl, hsumm⟩
  · unfold weightedZeroExponentRepair2
    apply le_sInf
    intro sigma ⟨hsigma_pos, s, hs_eq, hs_summ⟩
    rw [← hs_eq]
    by_contra hlt
    push_neg at hlt
    have hs_lt : s < 1 := by exact_mod_cast hlt
    have hs_pos : 0 < s := by
      have := hs_eq ▸ hsigma_pos
      exact_mod_cast this
    exact completedZeta_weighted_zeros_not_summable_repair2_scratch
      s hs_pos hs_lt hs_summ

#print axioms canonical_sequence_summable_of_weighted_repair2_scratch
#print axioms completedZeta_weighted_zeroExponent_eq_one_repair2_scratch

end ArithmeticHodge.Analysis.EntireFunction

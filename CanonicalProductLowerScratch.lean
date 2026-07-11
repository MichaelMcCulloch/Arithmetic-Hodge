import ProductLogScratch
import SequenceCountScratch
import MinimumModulusScratch

open Complex Filter Topology Real Set

namespace ArithmeticHodge.Analysis.EntireFunction

set_option autoImplicit false

/-- Raising the inverse-norm exponent preserves summability.  Zero padding is
harmless because `0⁻¹ = 0` in the ambient field. -/
theorem summable_inv_norm_rpow_of_le
    (a : ℕ → ℂ) (beta gamma : ℝ) (hbeta : 0 < beta)
    (hbg : beta ≤ gamma)
    (hsumm : Summable (fun n ↦ ‖a n‖⁻¹ ^ beta)) :
    Summable (fun n ↦ ‖a n‖⁻¹ ^ gamma) := by
  have hfinite : Set.Finite {n : ℕ | a n ≠ 0 ∧ ‖a n‖ ≤ 1} :=
    finite_nonzero_indices_norm_le_of_summable a beta hbeta hsumm 1 zero_lt_one
  apply hsumm.of_norm_bounded_eventually
  rw [Filter.eventually_cofinite]
  apply hfinite.subset
  intro n hn
  simp only [Set.mem_setOf_eq] at hn ⊢
  have han : a n ≠ 0 := by
    intro han
    simp [han, Real.zero_rpow (ne_of_gt hbeta),
      Real.zero_rpow (ne_of_gt (hbeta.trans_le hbg))] at hn
  refine ⟨han, ?_⟩
  by_contra hnorm
  have hnorm' : 1 < ‖a n‖ := lt_of_not_ge hnorm
  have hinv_pos : 0 < ‖a n‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr han)
  have hinv_one : ‖a n‖⁻¹ ≤ 1 := by
    exact (inv_le_one₀ (norm_pos_iff.mpr han)).mpr hnorm'.le
  apply hn
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hinv_pos.le gamma)]
  exact Real.rpow_le_rpow_of_exponent_ge hinv_pos hinv_one hbg

/-- A near factor can lose only a positive logarithm of the zero modulus,
plus the finite exponential correction. -/
theorem near_weierstraßElementary_log_lower
    (p : ℕ) (z a : ℂ) (alpha : ℝ) (ha : a ≠ 0)
    (halpha : 0 < alpha)
    (hsep : ‖a‖⁻¹ ^ alpha ≤ ‖z - a‖) :
    -(alpha + 1) * max (Real.log ‖a‖) 0 -
        ∑ k ∈ Finset.range p, ‖z / a‖ ^ (k + 1) / (k + 1 : ℝ) ≤
      Real.log ‖weierstraßElementary p (z / a)‖ := by
  have ha_pos : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hinv_pos : 0 < ‖a‖⁻¹ := inv_pos.mpr ha_pos
  have hdelta : 0 < ‖a‖⁻¹ ^ alpha := Real.rpow_pos_of_pos hinv_pos alpha
  have hbase := log_norm_weierstraßElementary_div_lower
    p z a ha (‖a‖⁻¹ ^ alpha) hdelta hsep
  have hlogdelta : Real.log (‖a‖⁻¹ ^ alpha) = -alpha * Real.log ‖a‖ := by
    rw [Real.log_rpow hinv_pos, Real.log_inv]
    ring
  rw [hlogdelta] at hbase
  by_cases hlog : 0 ≤ Real.log ‖a‖
  · rw [max_eq_left hlog]
    convert hbase using 1 <;> ring
  · rw [max_eq_right (le_of_not_ge hlog)]
    have hcoef : 0 < alpha + 1 := by linarith
    have hgain : 0 ≤ -(alpha + 1) * Real.log ‖a‖ :=
      mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hcoef.le) (le_of_not_ge hlog)
    linarith

/-- The positive logarithmic part of all near zero moduli is absorbed by
`R^alpha`.  Moduli below one contribute zero to the positive part. -/
theorem finite_sum_max_log_norm_le_rpow
    (a : ℕ → ℂ) (beta alpha : ℝ)
    (hbeta : 0 < beta) (hbeta_alpha : beta < alpha)
    (hsumm : Summable (fun n ↦ ‖a n‖⁻¹ ^ beta))
    (R : ℝ) (hR : 1 ≤ R)
    (u : Finset ℕ)
    (hu : ∀ n ∈ u, a n ≠ 0 ∧ ‖a n‖ ≤ 2 * R) :
    ∑ n ∈ u, max (Real.log ‖a n‖) 0 ≤
      (2 ^ alpha / (alpha - beta) * ∑' n, ‖a n‖⁻¹ ^ beta) * R ^ alpha := by
  classical
  let v := u.filter (fun n ↦ 1 ≤ ‖a n‖)
  have hv : ∀ n ∈ v, 1 ≤ ‖a n‖ ∧ ‖a n‖ ≤ 2 * R := by
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    exact ⟨hn'.2, (hu n hn'.1).2⟩
  calc
    ∑ n ∈ u, max (Real.log ‖a n‖) 0 =
        ∑ n ∈ u, if 1 ≤ ‖a n‖ then Real.log ‖a n‖ else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hnorm : 1 ≤ ‖a n‖
      · simp only [hnorm, if_true, max_eq_left (Real.log_nonneg hnorm)]
      · have hnorm_le : ‖a n‖ ≤ 1 := le_of_not_ge hnorm
        have hlog_le : Real.log ‖a n‖ ≤ 0 := Real.log_nonpos (norm_nonneg _) hnorm_le
        simp only [hnorm, if_false, max_eq_right hlog_le]
    _ = ∑ n ∈ v, Real.log ‖a n‖ := by
      simp only [v, Finset.sum_filter]
    _ ≤ (2 ^ alpha / (alpha - beta) * ∑' n, ‖a n‖⁻¹ ^ beta) * R ^ alpha :=
      finite_sum_log_norm_le_rpow a beta alpha hbeta hbeta_alpha hsumm R hR v hv

/-- The finite exponential corrections of all near factors are `O(R^alpha)`
when the canonical genus is strictly below the summability exponent. -/
theorem finite_sum_near_exp_correction_le_rpow
    (a : ℕ → ℂ) (p : ℕ) (beta alpha : ℝ)
    (hp_beta : (p : ℝ) < beta) (hbeta_alpha : beta < alpha)
    (hsumm : Summable (fun n ↦ ‖a n‖⁻¹ ^ beta))
    (z : ℂ) (R : ℝ) (hz : ‖z‖ = R) (hR : 1 ≤ R)
    (u : Finset ℕ)
    (hu : ∀ n ∈ u, a n ≠ 0 ∧ ‖a n‖ ≤ 2 * R) :
    ∑ n ∈ u, ∑ k ∈ Finset.range p,
        ‖z / a n‖ ^ (k + 1) / (k + 1 : ℝ) ≤
      (∑ k ∈ Finset.range p,
        (2 ^ (beta - ((k + 1 : ℕ) : ℝ)) * ∑' n, ‖a n‖⁻¹ ^ beta) /
          (k + 1 : ℝ)) * R ^ alpha := by
  rw [Finset.sum_comm, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro k hk
  have hkp : k + 1 ≤ p := Nat.succ_le_iff.mpr (Finset.mem_range.mp hk)
  have hkj_beta : ((k + 1 : ℕ) : ℝ) ≤ beta := by
    exact (by exact_mod_cast hkp : ((k + 1 : ℕ) : ℝ) ≤ (p : ℝ)).trans hp_beta.le
  have hpow := finite_sum_ratio_pow_le_rpow a beta alpha (k + 1) hsumm R hR
    hkj_beta hbeta_alpha.le u hu
  have hden : 0 ≤ (k + 1 : ℝ) := by positivity
  calc
    ∑ n ∈ u, ‖z / a n‖ ^ (k + 1) / (k + 1 : ℝ) =
        (∑ n ∈ u, (R / ‖a n‖) ^ (k + 1)) / (k + 1 : ℝ) := by
      rw [Finset.sum_div]
      congr 2
      ext n
      rw [norm_div, hz]
    _ ≤ ((2 ^ (beta - ((k + 1 : ℕ) : ℝ)) *
          ∑' n, ‖a n‖⁻¹ ^ beta) * R ^ alpha) / (k + 1 : ℝ) :=
      div_le_div_of_nonneg_right hpow hden
    _ = (2 ^ (beta - ((k + 1 : ℕ) : ℝ)) *
          ∑' n, ‖a n‖⁻¹ ^ beta) / (k + 1 : ℝ) * R ^ alpha := by
      ring

/-- Explicit coefficient for the loss from factors with `‖a n‖ ≤ 2R`. -/
noncomputable def canonicalProductNearConstant
    (a : ℕ → ℂ) (p : ℕ) (beta alpha : ℝ) : ℝ :=
  (alpha + 1) *
      (2 ^ alpha / (alpha - beta) * ∑' n, ‖a n‖⁻¹ ^ beta) +
    ∑ k ∈ Finset.range p,
      (2 ^ (beta - ((k + 1 : ℕ) : ℝ)) * ∑' n, ‖a n‖⁻¹ ^ beta) /
        (k + 1 : ℝ)

/-- Summing the factorwise bounds over any finite collection of near zeros. -/
theorem finite_sum_near_log_factor_lower
    (a : ℕ → ℂ) (p : ℕ) (beta alpha : ℝ)
    (hp_beta : (p : ℝ) < beta) (hbeta_alpha : beta < alpha)
    (hsumm : Summable (fun n ↦ ‖a n‖⁻¹ ^ beta))
    (z : ℂ) (R : ℝ) (hz : ‖z‖ = R) (hR : 1 ≤ R)
    (u : Finset ℕ)
    (hu : ∀ n ∈ u, a n ≠ 0 ∧ ‖a n‖ ≤ 2 * R)
    (hsep : ∀ n ∈ u, ‖a n‖⁻¹ ^ alpha ≤ ‖z - a n‖) :
    -canonicalProductNearConstant a p beta alpha * R ^ alpha ≤
      ∑ n ∈ u, Real.log ‖weierstraßElementary p (z / a n)‖ := by
  have hbeta : 0 < beta := lt_of_le_of_lt (Nat.cast_nonneg p) hp_beta
  have halpha : 0 < alpha := hbeta.trans hbeta_alpha
  let L : ℝ := ∑ n ∈ u, max (Real.log ‖a n‖) 0
  let P : ℝ := ∑ n ∈ u, ∑ k ∈ Finset.range p,
    ‖z / a n‖ ^ (k + 1) / (k + 1 : ℝ)
  let KL : ℝ := 2 ^ alpha / (alpha - beta) * ∑' n, ‖a n‖⁻¹ ^ beta
  let KP : ℝ := ∑ k ∈ Finset.range p,
    (2 ^ (beta - ((k + 1 : ℕ) : ℝ)) * ∑' n, ‖a n‖⁻¹ ^ beta) /
      (k + 1 : ℝ)
  have hL : L ≤ KL * R ^ alpha := by
    simpa only [L, KL] using finite_sum_max_log_norm_le_rpow
      a beta alpha hbeta hbeta_alpha hsumm R hR u hu
  have hP : P ≤ KP * R ^ alpha := by
    simpa only [P, KP] using finite_sum_near_exp_correction_le_rpow
      a p beta alpha hp_beta hbeta_alpha hsumm z R hz hR u hu
  have hcoef : 0 ≤ alpha + 1 := by linarith
  have hL' : (alpha + 1) * L ≤ (alpha + 1) * (KL * R ^ alpha) :=
    mul_le_mul_of_nonneg_left hL hcoef
  have hloss : (alpha + 1) * L + P ≤
      ((alpha + 1) * KL + KP) * R ^ alpha := by
    calc
      (alpha + 1) * L + P ≤ (alpha + 1) * (KL * R ^ alpha) + KP * R ^ alpha :=
        add_le_add hL' hP
      _ = ((alpha + 1) * KL + KP) * R ^ alpha := by ring
  have hlower_sum : -canonicalProductNearConstant a p beta alpha * R ^ alpha ≤
      ∑ n ∈ u, (-(alpha + 1) * max (Real.log ‖a n‖) 0 -
        ∑ k ∈ Finset.range p, ‖z / a n‖ ^ (k + 1) / (k + 1 : ℝ)) := by
    have heq :
        ∑ n ∈ u, (-(alpha + 1) * max (Real.log ‖a n‖) 0 -
          ∑ k ∈ Finset.range p, ‖z / a n‖ ^ (k + 1) / (k + 1 : ℝ)) =
        -(alpha + 1) * L - P := by
      dsimp only [L, P]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [heq]
    dsimp only [canonicalProductNearConstant, KL, KP]
    linarith
  exact hlower_sum.trans (Finset.sum_le_sum fun n hn ↦
    near_weierstraßElementary_log_lower p z (a n) alpha (hu n hn).1 halpha (hsep n hn))

/-- The logarithmic loss from all factors beyond `2R` is controlled by the
full inverse-`beta` sum.  Zero-padded entries contribute exactly zero. -/
theorem tsum_far_log_factor_lower
    (a : ℕ → ℂ) (p : ℕ) (beta : ℝ)
    (hbeta : 0 < beta) (hbeta_q : beta ≤ (p + 1 : ℕ))
    (hsumm : Summable (fun n ↦ ‖a n‖⁻¹ ^ beta))
    (z : ℂ) (R : ℝ) (hz : ‖z‖ = R) (hR : 0 < R)
    (u : Finset ℕ)
    (hfar : ∀ n, n ∉ u → a n = 0 ∨ 2 * R < ‖a n‖) :
    -2 * (∑' n, ‖a n‖⁻¹ ^ beta) * R ^ beta ≤
      ∑' n : {n : ℕ // n ∉ u},
        Real.log ‖weierstraßElementary p (z / a n)‖ := by
  let q : ℕ := p + 1
  have hq_pos : 0 < q := by dsimp [q]; omega
  have hconv_rpow : Summable (fun n ↦ ‖a n‖⁻¹ ^ (q : ℝ)) :=
    summable_inv_norm_rpow_of_le a beta q hbeta (by exact_mod_cast hbeta_q) hsumm
  have hconv_pow : Summable (fun n ↦ (‖a n‖⁻¹) ^ q) := by
    simpa only [Real.rpow_natCast] using hconv_rpow
  have hconv : Summable (fun n ↦ ‖a n‖⁻¹ ^ ((p : ℝ) + 1)) := by
    simpa only [q, Nat.cast_add, Nat.cast_one] using hconv_rpow
  have hratio : Summable (fun n ↦ (R / ‖a n‖) ^ q) := by
    have h := hconv_pow.mul_left (R ^ q)
    simpa only [div_eq_mul_inv, mul_pow] using h
  let term : ℕ → ℝ := fun n ↦ Real.log ‖weierstraßElementary p (z / a n)‖
  have hterm : Summable term := by
    let v : ℕ → ℂ := fun n ↦ weierstraßElementary p (z / a n) - 1
    have hv : Summable (fun n ↦ ‖v n‖) := by
      simpa only [v, q, Nat.cast_add, Nat.cast_one] using
        perturbation_summable' a p hconv z
    simpa only [term, v, add_sub_cancel] using hv.summable_log_norm_one_add
  have hpoint : ∀ n : {n : ℕ // n ∉ u},
      -2 * (R / ‖a n‖) ^ q ≤ term n := by
    intro n
    have hn_not : (n : ℕ) ∉ u := n.property
    rcases hfar n hn_not with han | hnfar
    · simp [term, han, q, weierstraßElementary_zero]
    · have han : a n ≠ 0 := by
        intro han
        rw [han, norm_zero] at hnfar
        linarith
      have hnorm_pos : 0 < ‖a n‖ := norm_pos_iff.mpr han
      have hhalf : ‖z / a n‖ ≤ 1 / 2 := by
        rw [norm_div, hz]
        apply (div_le_iff₀ hnorm_pos).2
        linarith
      simpa only [term, norm_div, hz, q] using
        neg_two_mul_norm_pow_le_log_norm_weierstraßElementary p (z / a n) hhalf
  have hratio_sub : Summable (fun n : {n : ℕ // n ∉ u} ↦ (R / ‖a n‖) ^ q) :=
    hratio.subtype _
  have hinv_sub : Summable (fun n : {n : ℕ // n ∉ u} ↦ ‖a n‖⁻¹ ^ beta) :=
    hsumm.subtype _
  have hratio_point : ∀ n : {n : ℕ // n ∉ u},
      (R / ‖a n‖) ^ q ≤ R ^ beta * (‖a n‖⁻¹ ^ beta) := by
    intro n
    have hn_not : (n : ℕ) ∉ u := n.property
    rcases hfar n hn_not with han | hnfar
    · simp [han, q, Real.zero_rpow (ne_of_gt hbeta)]
    · exact far_ratio_pow_le_inv_rpow ‖a n‖ R beta q
        (lt_of_lt_of_le (mul_pos two_pos hR) hnfar.le) hR hnfar.le hbeta_q
  have hratio_le_sub :
      ∑' n : {n : ℕ // n ∉ u}, (R / ‖a n‖) ^ q ≤
        R ^ beta * ∑' n : {n : ℕ // n ∉ u}, ‖a n‖⁻¹ ^ beta := by
    rw [← tsum_mul_left]
    exact hratio_sub.tsum_le_tsum hratio_point (hinv_sub.mul_left (R ^ beta))
  have hinv_sub_le : ∑' n : {n : ℕ // n ∉ u}, ‖a n‖⁻¹ ^ beta ≤
      ∑' n, ‖a n‖⁻¹ ^ beta :=
    hsumm.tsum_subtype_le (fun n ↦ ‖a n‖⁻¹ ^ beta) {n : ℕ | n ∉ u}
      (fun n ↦ Real.rpow_nonneg (inv_nonneg.mpr (norm_nonneg _)) _)
  have hratio_le : ∑' n : {n : ℕ // n ∉ u}, (R / ‖a n‖) ^ q ≤
      (∑' n, ‖a n‖⁻¹ ^ beta) * R ^ beta := by
    calc
      ∑' n : {n : ℕ // n ∉ u}, (R / ‖a n‖) ^ q ≤
          R ^ beta * ∑' n : {n : ℕ // n ∉ u}, ‖a n‖⁻¹ ^ beta := hratio_le_sub
      _ ≤ R ^ beta * ∑' n, ‖a n‖⁻¹ ^ beta :=
        mul_le_mul_of_nonneg_left hinv_sub_le (Real.rpow_nonneg hR.le beta)
      _ = (∑' n, ‖a n‖⁻¹ ^ beta) * R ^ beta := mul_comm _ _
  have hlower_tsum :
      -2 * (∑' n, ‖a n‖⁻¹ ^ beta) * R ^ beta ≤
        ∑' n : {n : ℕ // n ∉ u}, -2 * (R / ‖a n‖) ^ q := by
    rw [tsum_mul_left]
    nlinarith
  exact hlower_tsum.trans
    ((hratio_sub.mul_left (-2)).tsum_le_tsum hpoint (hterm.subtype _))

/-- Explicit coefficient in the full good-sphere lower bound. -/
noncomputable def canonicalProductLowerConstant
    (a : ℕ → ℂ) (p : ℕ) (beta alpha : ℝ) : ℝ :=
  canonicalProductNearConstant a p beta alpha +
    2 * ∑' n, ‖a n‖⁻¹ ^ beta

/-- The displayed coefficient really is a nonnegative constant under the
exponent inequalities used by the minimum-modulus theorem. -/
theorem canonicalProductLowerConstant_nonneg
    (a : ℕ → ℂ) (p : ℕ) (beta alpha : ℝ)
    (hp_beta : (p : ℝ) < beta) (hbeta_alpha : beta < alpha) :
    0 ≤ canonicalProductLowerConstant a p beta alpha := by
  have hbeta : 0 < beta := lt_of_le_of_lt (Nat.cast_nonneg p) hp_beta
  have halpha : 0 < alpha := hbeta.trans hbeta_alpha
  have hsum : 0 ≤ ∑' n, ‖a n‖⁻¹ ^ beta :=
    tsum_nonneg fun n ↦ Real.rpow_nonneg (inv_nonneg.mpr (norm_nonneg _)) _
  have hnear : 0 ≤ canonicalProductNearConstant a p beta alpha := by
    unfold canonicalProductNearConstant
    apply add_nonneg
    · apply mul_nonneg
      · linarith
      · exact mul_nonneg (div_nonneg (Real.rpow_nonneg (by norm_num) _)
          (sub_nonneg.mpr hbeta_alpha.le)) hsum
    · apply Finset.sum_nonneg
      intro k hk
      exact div_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hsum) (by positivity)
  exact add_nonneg hnear (mul_nonneg (by norm_num) hsum)

/-- **Minimum modulus on a good sphere for a canonical product.**

If `p < beta < alpha < p+1`, the inverse `beta` powers of the zero moduli
are summable, and every point of the sphere is separated from the `n`th zero
by at least `‖a n‖⁻ᵃˡᵖᴴᵃ`, then the full canonical product is bounded
below by `exp (-C Rᵃˡᵖᴴᵃ)`.  Entries equal to zero are treated as padding and
contribute the factor one. -/
theorem canonicalProduct_log_norm_lower_on_good_sphere
    (a : ℕ → ℂ) (p : ℕ) (beta alpha : ℝ)
    (hp_beta : (p : ℝ) < beta) (hbeta_alpha : beta < alpha)
    (hbeta_q : beta < (p : ℝ) + 1)
    (hsumm : Summable (fun n ↦ ‖a n‖⁻¹ ^ beta))
    (z : ℂ) (R : ℝ) (hz : ‖z‖ = R) (hR : 1 ≤ R)
    (hsep : ∀ n, ‖a n‖⁻¹ ^ alpha ≤ ‖z - a n‖) :
    -canonicalProductLowerConstant a p beta alpha * R ^ alpha ≤
      Real.log ‖∏' n, weierstraßElementary p (z / a n)‖ := by
  classical
  have hbeta : 0 < beta := lt_of_le_of_lt (Nat.cast_nonneg p) hp_beta
  have halpha : 0 < alpha := hbeta.trans hbeta_alpha
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hfinite : Set.Finite {n : ℕ | a n ≠ 0 ∧ ‖a n‖ ≤ 2 * R} :=
    finite_nonzero_indices_norm_le_of_summable a beta hbeta hsumm (2 * R)
      (mul_pos two_pos hRpos)
  let u : Finset ℕ := hfinite.toFinset
  have hu : ∀ n ∈ u, a n ≠ 0 ∧ ‖a n‖ ≤ 2 * R := by
    intro n hn
    exact (hfinite.mem_toFinset.mp hn)
  have hfar : ∀ n, n ∉ u → a n = 0 ∨ 2 * R < ‖a n‖ := by
    intro n hn
    by_cases han : a n = 0
    · exact Or.inl han
    · right
      have hnset : n ∉ {n : ℕ | a n ≠ 0 ∧ ‖a n‖ ≤ 2 * R} := by
        simpa only [u, hfinite.mem_toFinset] using hn
      exact lt_of_not_ge (fun h ↦ hnset ⟨han, h⟩)
  have hnear := finite_sum_near_log_factor_lower a p beta alpha hp_beta hbeta_alpha
    hsumm z R hz hR u hu (fun n hn ↦ hsep n)
  have hbeta_q_nat : beta ≤ (p + 1 : ℕ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hbeta_q.le
  have hfar_lower := tsum_far_log_factor_lower a p beta hbeta hbeta_q_nat hsumm
    z R hz hRpos u hfar
  have hsum_nonneg : 0 ≤ ∑' n, ‖a n‖⁻¹ ^ beta :=
    tsum_nonneg fun n ↦ Real.rpow_nonneg (inv_nonneg.mpr (norm_nonneg _)) _
  have hrpow_le : R ^ beta ≤ R ^ alpha :=
    Real.rpow_le_rpow_of_exponent_le hR hbeta_alpha.le
  have hfar_alpha :
      -2 * (∑' n, ‖a n‖⁻¹ ^ beta) * R ^ alpha ≤
        ∑' n : {n : ℕ // n ∉ u},
          Real.log ‖weierstraßElementary p (z / a n)‖ := by
    apply le_trans _ hfar_lower
    nlinarith [mul_le_mul_of_nonneg_left hrpow_le hsum_nonneg]
  let term : ℕ → ℝ := fun n ↦ Real.log ‖weierstraßElementary p (z / a n)‖
  have hbeta_q' : beta ≤ (p : ℝ) + 1 := by
    exact hbeta_q.le
  have hconv : Summable (fun n ↦ ‖a n‖⁻¹ ^ ((p : ℝ) + 1)) :=
    summable_inv_norm_rpow_of_le a beta ((p : ℝ) + 1) hbeta hbeta_q' hsumm
  have hterm : Summable term := by
    let v : ℕ → ℂ := fun n ↦ weierstraßElementary p (z / a n) - 1
    have hv : Summable (fun n ↦ ‖v n‖) := by
      simpa only [v] using perturbation_summable' a p hconv z
    simpa only [term, v, add_sub_cancel] using hv.summable_log_norm_one_add
  have hsplit :
      ∑ n ∈ u, term n + ∑' n : {n : ℕ // n ∉ u}, term n = ∑' n, term n := by
    simpa only [Set.mem_compl_iff, Finset.mem_coe] using hterm.sum_add_tsum_compl (s := u)
  have htotal :
      -canonicalProductLowerConstant a p beta alpha * R ^ alpha ≤ ∑' n, term n := by
    rw [← hsplit]
    have hadd := add_le_add hnear hfar_alpha
    dsimp only [canonicalProductLowerConstant]
    linarith
  have hne : ∀ n, z / a n ≠ 1 := by
    intro n heq
    have han : a n ≠ 0 := by
      intro han
      simp [han] at heq
    have hza : z = a n := (div_eq_one_iff_eq han).mp heq
    have hdelta : 0 < ‖a n‖⁻¹ ^ alpha :=
      Real.rpow_pos_of_pos (inv_pos.mpr (norm_pos_iff.mpr han)) alpha
    have := hsep n
    rw [hza, sub_self, norm_zero] at this
    linarith
  rw [log_norm_tprod_weierstraßElementary a p hconv z hne]
  exact htotal

end ArithmeticHodge.Analysis.EntireFunction

/-
  Sound canonical-product growth infrastructure.

  The former arbitrary-factorization growth theorem was false and has been
  removed. This module supplies the genus, multiplicity, separation, and
  summability data needed for the genuine Hadamard argument; `GrowthBound`
  now preserves only module-import compatibility by re-exporting this API.
-/

import ArithmeticHodge.Analysis.EntireFunction.WeierstraßProduct
import ArithmeticHodge.Analysis.BorelCaratheodory
import ArithmeticHodge.Analysis.EntireFunction.MinimumModulus
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Complex.CauchyIntegral

set_option autoImplicit false

open Complex Filter Topology Real Set Metric Finset BigOperators

namespace ArithmeticHodge.Analysis.EntireFunction

set_option autoImplicit false

/-- Triangle-inequality bound for the polynomial exponential correction in `E_p`. -/
private theorem norm_weierstraßExpSum_le (p : ℕ) (w : ℂ) :
    ‖weierstraßExpSum p w‖ ≤
      ∑ k ∈ Finset.range p, ‖w‖ ^ (k + 1) / (k + 1 : ℝ) := by
  rw [weierstraßExpSum]
  calc
    ‖∑ k ∈ Finset.range p, w ^ (k + 1) / ((k + 1 : ℕ) : ℂ)‖
        ≤ ∑ k ∈ Finset.range p, ‖w ^ (k + 1) / ((k + 1 : ℕ) : ℂ)‖ :=
          norm_sum_le _ _
    _ = ∑ k ∈ Finset.range p, ‖w‖ ^ (k + 1) / (k + 1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [norm_div, norm_pow]
      simp only [RCLike.norm_natCast]
      push_cast
      norm_num

/-- A separated factor has a logarithmic lower bound consisting of its
distance from the zero, the scale of that zero, and the exponential correction. -/
private theorem log_norm_weierstraßElementary_div_lower
    (p : ℕ) (z a : ℂ) (ha : a ≠ 0) (delta : ℝ) (hdelta : 0 < delta)
    (hsep : delta ≤ ‖z - a‖) :
    Real.log delta - Real.log ‖a‖ -
        ∑ k ∈ Finset.range p, ‖z / a‖ ^ (k + 1) / (k + 1 : ℝ) ≤
      Real.log ‖weierstraßElementary p (z / a)‖ := by
  have hza : z ≠ a := by
    intro h
    subst z
    simp at hsep
    linarith
  have hone_sub : (1 : ℂ) - z / a ≠ 0 := by
    rw [sub_ne_zero]
    exact fun h => hza ((div_eq_one_iff_eq ha).mp h.symm)
  have hnorm_one_sub : ‖(1 : ℂ) - z / a‖ = ‖z - a‖ / ‖a‖ := by
    have heq : (1 : ℂ) - z / a = (a - z) / a := by
      field_simp
    rw [heq, norm_div, norm_sub_rev]
  have hlog_sep : Real.log delta ≤ Real.log ‖z - a‖ :=
    Real.log_le_log hdelta hsep
  have hre_lower : -‖weierstraßExpSum p (z / a)‖ ≤
      (weierstraßExpSum p (z / a)).re := by
    exact (abs_le.mp (abs_re_le_norm (weierstraßExpSum p (z / a)))).1
  rw [weierstraßElementary_eq, norm_mul,
    Real.log_mul (norm_ne_zero_iff.mpr hone_sub)
      (norm_ne_zero_iff.mpr (Complex.exp_ne_zero _)),
    Complex.norm_exp, Real.log_exp, hnorm_one_sub,
    Real.log_div (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hza))
      (norm_ne_zero_iff.mpr ha)]
  have hsum := norm_weierstraßExpSum_le p (z / a)
  linarith

/-- Inside the half disk, a canonical factor has the standard tail lower bound. -/
private theorem neg_two_mul_norm_pow_le_log_norm_weierstraßElementary
    (p : ℕ) (w : ℂ) (hw : ‖w‖ ≤ 1 / 2) :
    -2 * ‖w‖ ^ (p + 1) ≤ Real.log ‖weierstraßElementary p w‖ := by
  let q : ℝ := ‖w‖ ^ (p + 1)
  have hw_nonneg : 0 ≤ ‖w‖ := norm_nonneg w
  have hw_one : ‖w‖ ≤ 1 := hw.trans (by norm_num)
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    positivity
  have hq_le_norm : q ≤ ‖w‖ := by
    dsimp [q]
    rw [pow_succ]
    exact mul_le_of_le_one_left hw_nonneg (pow_le_one₀ hw_nonneg hw_one)
  have hq_half : q ≤ 1 / 2 := hq_le_norm.trans hw
  have hclose : ‖1 - weierstraßElementary p w‖ ≤ q := by
    simpa only [q] using weierstraßElementary_bound p w hw
  have hE_lower : 1 - q ≤ ‖weierstraßElementary p w‖ := by
    calc
      1 - q ≤ 1 - ‖1 - weierstraßElementary p w‖ := sub_le_sub_left hclose 1
      _ ≤ ‖weierstraßElementary p w‖ := by
        simpa using norm_sub_norm_le (1 : ℂ) (1 - weierstraßElementary p w)
  have hden_pos : 0 < 1 - q := by linarith
  have hE_pos : 0 < ‖weierstraßElementary p w‖ := hden_pos.trans_le hE_lower
  have hinv_le : ‖weierstraßElementary p w‖⁻¹ ≤ (1 - q)⁻¹ :=
    (inv_le_inv₀ hE_pos hden_pos).2 hE_lower
  have hrat : (1 - q)⁻¹ ≤ 1 + 2 * q := by
    apply (inv_le_iff_one_le_mul₀ hden_pos).2
    nlinarith
  calc
    -2 * ‖w‖ ^ (p + 1) = 1 - (1 + 2 * q) := by simp only [q]; ring
    _ ≤ 1 - ‖weierstraßElementary p w‖⁻¹ :=
      sub_le_sub_left (hinv_le.trans hrat) 1
    _ ≤ Real.log ‖weierstraßElementary p w‖ :=
      Real.one_sub_inv_le_log_of_pos hE_pos

set_option autoImplicit false

/-- Away from the zero sequence, the logarithm of the norm of a convergent
canonical product is the sum of the logarithms of the factor norms. -/
private theorem log_norm_tprod_weierstraßElementary
    (zeros : ℕ → ℂ) (p : ℕ)
    (hconv : Summable (fun n => (‖zeros n‖⁻¹) ^ ((p : ℝ) + 1)))
    (z : ℂ) (hne : ∀ n, z / zeros n ≠ 1) :
    Real.log ‖∏' n, weierstraßElementary p (z / zeros n)‖ =
      ∑' n, Real.log ‖weierstraßElementary p (z / zeros n)‖ := by
  let u : ℕ → ℂ := fun n => weierstraßElementary p (z / zeros n) - 1
  have hu : Summable (fun n => ‖u n‖) := by
    simpa only [u] using perturbation_summable' zeros p hconv z
  have hlog : Summable (fun n => Real.log ‖1 + u n‖) :=
    hu.summable_log_norm_one_add
  have hpos : ∀ n, 0 < ‖1 + u n‖ := by
    intro n
    apply norm_pos_iff.mpr
    simpa only [u, add_sub_cancel] using
      weierstraßElementary_ne_zero p (z / zeros n) (hne n)
  have hmult : Multipliable (fun n => weierstraßElementary p (z / zeros n)) :=
    multipliable_weierstraßElementary_raw zeros p hconv z
  have hexp :
      Real.exp (∑' n, Real.log ‖1 + u n‖) = ∏' n, ‖1 + u n‖ :=
    Real.rexp_tsum_eq_tprod hpos hlog
  calc
    Real.log ‖∏' n, weierstraßElementary p (z / zeros n)‖ =
        Real.log (∏' n, ‖weierstraßElementary p (z / zeros n)‖) := by
          rw [hmult.norm_tprod]
    _ = Real.log (Real.exp (∑' n, Real.log ‖1 + u n‖)) := by
          rw [hexp]
          congr 2
          ext n
          simp only [u, add_sub_cancel]
    _ = ∑' n, Real.log ‖1 + u n‖ := Real.log_exp _
    _ = ∑' n, Real.log ‖weierstraßElementary p (z / zeros n)‖ := by
          congr 1
          ext n
          simp only [u, add_sub_cancel]

/-- Beyond the radius `2 * R`, every higher power of `R / x` is bounded by
the summable inverse-`beta` weight, provided `beta` does not exceed that
power.  The coarse constant one is sufficient for minimum-modulus bounds. -/
private theorem far_ratio_pow_le_inv_rpow
    (x R beta : ℝ) (q : ℕ)
    (hx : 0 < x) (hR : 0 < R) (hfar : 2 * R ≤ x)
    (hbeta_q : beta ≤ q) :
    (R / x) ^ q ≤ R ^ beta * (x⁻¹ ^ beta) := by
  have hratio_pos : 0 < R / x := div_pos hR hx
  have hratio_one : R / x ≤ 1 := by
    rw [div_le_one hx]
    linarith
  calc
    (R / x) ^ q = (R / x) ^ (q : ℝ) := by
      rw [Real.rpow_natCast]
    _ ≤ (R / x) ^ beta :=
      Real.rpow_le_rpow_of_exponent_ge hratio_pos hratio_one hbeta_q
    _ = R ^ beta * (x⁻¹ ^ beta) := by
      rw [Real.div_rpow hR.le hx.le, div_eq_mul_inv, Real.inv_rpow hx.le]

set_option autoImplicit false

/-- Summability of inverse `beta`-powers forces local finiteness of the
nonzero entries of a possibly zero-padded sequence. -/
private theorem finite_nonzero_indices_norm_le_of_summable
    (a : ℕ → ℂ) (beta : ℝ) (hbeta : 0 < beta)
    (hsumm : Summable (fun n => ‖a n‖⁻¹ ^ beta))
    (R : ℝ) (hR : 0 < R) :
    Set.Finite {n : ℕ | a n ≠ 0 ∧ ‖a n‖ ≤ R} := by
  let c : ℝ := R⁻¹ ^ beta
  have hc : 0 < c := Real.rpow_pos_of_pos (inv_pos.mpr hR) beta
  have hev : ∀ᶠ n in Filter.cofinite, ‖a n‖⁻¹ ^ beta < c :=
    hsumm.tendsto_cofinite_zero.eventually_lt_const hc
  have hfinite : Set.Finite {n : ℕ | c ≤ ‖a n‖⁻¹ ^ beta} := by
    simpa only [Filter.eventually_cofinite, Set.mem_setOf_eq, not_lt] using hev
  apply hfinite.subset
  intro n hn
  have han_pos : 0 < ‖a n‖ := norm_pos_iff.mpr hn.1
  have hinv : R⁻¹ ≤ ‖a n‖⁻¹ :=
    (inv_le_inv₀ hR han_pos).2 hn.2
  exact Real.rpow_le_rpow (inv_nonneg.mpr hR.le) hinv hbeta.le

/-- A pointwise interpolation bound: inside `x ≤ 2R`, a lower power of
`R/x` is controlled by the summable inverse `beta`-power. -/
private theorem ratio_rpow_le_inv_rpow
    (x R j beta : ℝ) (hx : 0 < x) (hR : 0 < R)
    (hxR : x ≤ 2 * R) (hjbeta : j ≤ beta) :
    (R / x) ^ j ≤ 2 ^ (beta - j) * R ^ beta * (x⁻¹ ^ beta) := by
  have hdiff : 0 ≤ beta - j := sub_nonneg.mpr hjbeta
  have hxpow : x ^ (beta - j) ≤ (2 * R) ^ (beta - j) :=
    Real.rpow_le_rpow hx.le hxR hdiff
  calc
    (R / x) ^ j = R ^ j * x ^ (-j) := by
      rw [Real.div_rpow hR.le hx.le, div_eq_mul_inv, Real.rpow_neg hx.le]
    _ = R ^ j * (x ^ (-beta) * x ^ (beta - j)) := by
      rw [← Real.rpow_add hx]
      congr 1
      ring_nf
    _ ≤ R ^ j * (x ^ (-beta) * (2 * R) ^ (beta - j)) := by
      gcongr
    _ = 2 ^ (beta - j) * R ^ beta * (x⁻¹ ^ beta) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hR.le,
        Real.inv_rpow hx.le, Real.rpow_neg hx.le]
      calc
        R ^ j * ((x ^ beta)⁻¹ * (2 ^ (beta - j) * R ^ (beta - j))) =
            2 ^ (beta - j) * (R ^ j * R ^ (beta - j)) * (x ^ beta)⁻¹ := by ring
        _ = 2 ^ (beta - j) * R ^ beta * (x ^ beta)⁻¹ := by
          rw [← Real.rpow_add hR]
          rw [show j + (beta - j) = beta by ring]

/-- Finite partial sums over `0 < ‖a n‖ ≤ 2R` are `O(R^beta)`.
The bound follows directly from inverse-`beta` summability, so a separate
counting hypothesis is not needed. -/
private theorem finite_sum_ratio_rpow_le
    (a : ℕ → ℂ) (beta j : ℝ)
    (hsumm : Summable (fun n => ‖a n‖⁻¹ ^ beta))
    (R : ℝ) (hR : 0 < R) (hjbeta : j ≤ beta)
    (u : Finset ℕ)
    (hu : ∀ n ∈ u, a n ≠ 0 ∧ ‖a n‖ ≤ 2 * R) :
    ∑ n ∈ u, (R / ‖a n‖) ^ j ≤
      (2 ^ (beta - j) * ∑' n, ‖a n‖⁻¹ ^ beta) * R ^ beta := by
  let K : ℝ := 2 ^ (beta - j) * R ^ beta
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  calc
    ∑ n ∈ u, (R / ‖a n‖) ^ j ≤
        ∑ n ∈ u, K * (‖a n‖⁻¹ ^ beta) := by
      apply Finset.sum_le_sum
      intro n hn
      simpa only [K, mul_assoc] using
        ratio_rpow_le_inv_rpow ‖a n‖ R j beta
          (norm_pos_iff.mpr (hu n hn).1) hR (hu n hn).2 hjbeta
    _ = K * ∑ n ∈ u, ‖a n‖⁻¹ ^ beta := by rw [Finset.mul_sum]
    _ ≤ K * ∑' n, ‖a n‖⁻¹ ^ beta := by
      apply mul_le_mul_of_nonneg_left _ hK
      exact hsumm.sum_le_tsum u (fun n hn => Real.rpow_nonneg (inv_nonneg.mpr (norm_nonneg _)) _)
    _ = (2 ^ (beta - j) * ∑' n, ‖a n‖⁻¹ ^ beta) * R ^ beta := by
      dsimp [K]
      ring

/-- Integer-exponent specialization used by the degree-`p` exponential sum. -/
private theorem finite_sum_ratio_pow_le
    (a : ℕ → ℂ) (beta : ℝ) (j : ℕ)
    (hsumm : Summable (fun n => ‖a n‖⁻¹ ^ beta))
    (R : ℝ) (hR : 0 < R) (hjbeta : (j : ℝ) ≤ beta)
    (u : Finset ℕ)
    (hu : ∀ n ∈ u, a n ≠ 0 ∧ ‖a n‖ ≤ 2 * R) :
    ∑ n ∈ u, (R / ‖a n‖) ^ j ≤
      (2 ^ (beta - (j : ℝ)) * ∑' n, ‖a n‖⁻¹ ^ beta) * R ^ beta := by
  simpa only [Real.rpow_natCast] using
    finite_sum_ratio_rpow_le a beta (j : ℝ) hsumm R hR hjbeta u hu

/-- The form used in a target growth exponent `alpha`: if `beta ≤ alpha` and
`R ≥ 1`, the same finite power sum is `O(R^alpha)`. -/
private theorem finite_sum_ratio_pow_le_rpow
    (a : ℕ → ℂ) (beta alpha : ℝ) (j : ℕ)
    (hsumm : Summable (fun n => ‖a n‖⁻¹ ^ beta))
    (R : ℝ) (hR : 1 ≤ R) (hjbeta : (j : ℝ) ≤ beta)
    (hbeta_alpha : beta ≤ alpha)
    (u : Finset ℕ)
    (hu : ∀ n ∈ u, a n ≠ 0 ∧ ‖a n‖ ≤ 2 * R) :
    ∑ n ∈ u, (R / ‖a n‖) ^ j ≤
      (2 ^ (beta - (j : ℝ)) * ∑' n, ‖a n‖⁻¹ ^ beta) * R ^ alpha := by
  have hbase := finite_sum_ratio_pow_le a beta j hsumm R
    (zero_lt_one.trans_le hR) hjbeta u hu
  exact hbase.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hR hbeta_alpha) (by positivity))

/-- On the annulus `1 ≤ x ≤ 2R`, a logarithm is absorbed by an
inverse `beta`-weight at any larger target exponent `alpha`.

This is the pointwise estimate needed to sum the logarithmic near-factor
loss using only inverse-`beta` summability. -/
private theorem log_le_scaled_inv_rpow
    (x R beta alpha : ℝ) (hx : 1 ≤ x) (hxR : x ≤ 2 * R)
    (hbeta : 0 < beta) (hbeta_alpha : beta < alpha) :
    Real.log x ≤
      (2 ^ alpha / (alpha - beta) * R ^ alpha) * (x⁻¹ ^ beta) := by
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hdiff : 0 < alpha - beta := sub_pos.mpr hbeta_alpha
  have halpha : 0 < alpha := hbeta.trans hbeta_alpha
  have hR : 0 < R := by linarith
  have hlog : Real.log x ≤ x ^ (alpha - beta) / (alpha - beta) := by
    apply (le_div_iff₀ hdiff).2
    calc
      Real.log x * (alpha - beta) =
          Real.log (x ^ (alpha - beta)) := by
            rw [Real.log_rpow hxpos]
            ring
      _ ≤ x ^ (alpha - beta) - 1 :=
        Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hxpos _)
      _ ≤ x ^ (alpha - beta) := sub_le_self _ zero_le_one
  calc
    Real.log x ≤ x ^ (alpha - beta) / (alpha - beta) := hlog
    _ = (x ^ alpha / (alpha - beta)) * (x⁻¹ ^ beta) := by
      rw [Real.rpow_sub hxpos, Real.inv_rpow hxpos.le]
      field_simp
    _ ≤ ((2 * R) ^ alpha / (alpha - beta)) * (x⁻¹ ^ beta) := by
      gcongr
    _ = (2 ^ alpha / (alpha - beta) * R ^ alpha) * (x⁻¹ ^ beta) := by
      rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ 2) hR.le]
      ring

/-- The logarithmic loss from all near factors with
`1 ≤ ‖a n‖ ≤ 2R` is `O(R^alpha)` whenever the inverse `beta`-powers
are summable and `beta < alpha`. -/
private theorem finite_sum_log_norm_le_rpow
    (a : ℕ → ℂ) (beta alpha : ℝ)
    (hbeta : 0 < beta) (hbeta_alpha : beta < alpha)
    (hsumm : Summable (fun n => ‖a n‖⁻¹ ^ beta))
    (R : ℝ) (hR : 1 ≤ R)
    (u : Finset ℕ)
    (hu : ∀ n ∈ u, 1 ≤ ‖a n‖ ∧ ‖a n‖ ≤ 2 * R) :
    ∑ n ∈ u, Real.log ‖a n‖ ≤
      (2 ^ alpha / (alpha - beta) * ∑' n, ‖a n‖⁻¹ ^ beta) * R ^ alpha := by
  let K : ℝ := 2 ^ alpha / (alpha - beta) * R ^ alpha
  have hdiff : 0 < alpha - beta := sub_pos.mpr hbeta_alpha
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  calc
    ∑ n ∈ u, Real.log ‖a n‖ ≤
        ∑ n ∈ u, K * (‖a n‖⁻¹ ^ beta) := by
      apply Finset.sum_le_sum
      intro n hn
      simpa only [K] using
        log_le_scaled_inv_rpow ‖a n‖ R beta alpha
          (hu n hn).1 (hu n hn).2 hbeta hbeta_alpha
    _ = K * ∑ n ∈ u, ‖a n‖⁻¹ ^ beta := by rw [Finset.mul_sum]
    _ ≤ K * ∑' n, ‖a n‖⁻¹ ^ beta := by
      apply mul_le_mul_of_nonneg_left _ hK
      exact hsumm.sum_le_tsum u
        (fun n hn => Real.rpow_nonneg (inv_nonneg.mpr (norm_nonneg _)) _)
    _ = (2 ^ alpha / (alpha - beta) * ∑' n, ‖a n‖⁻¹ ^ beta) *
          R ^ alpha := by
      dsimp [K]
      ring

set_option autoImplicit false

/-- Raising the inverse-norm exponent preserves summability.  Zero padding is
harmless because `0⁻¹ = 0` in the ambient field. -/
private theorem summable_inv_norm_rpow_of_le
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
private theorem near_weierstraßElementary_log_lower
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
private theorem finite_sum_max_log_norm_le_rpow
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
private theorem finite_sum_near_exp_correction_le_rpow
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
private noncomputable def canonicalProductNearConstant
    (a : ℕ → ℂ) (p : ℕ) (beta alpha : ℝ) : ℝ :=
  (alpha + 1) *
      (2 ^ alpha / (alpha - beta) * ∑' n, ‖a n‖⁻¹ ^ beta) +
    ∑ k ∈ Finset.range p,
      (2 ^ (beta - ((k + 1 : ℕ) : ℝ)) * ∑' n, ‖a n‖⁻¹ ^ beta) /
        (k + 1 : ℝ)

/-- Summing the factorwise bounds over any finite collection of near zeros. -/
private theorem finite_sum_near_log_factor_lower
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
private theorem tsum_far_log_factor_lower
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
private noncomputable def canonicalProductLowerConstant
    (a : ℕ → ℂ) (p : ℕ) (beta alpha : ℝ) : ℝ :=
  canonicalProductNearConstant a p beta alpha +
    2 * ∑' n, ‖a n‖⁻¹ ^ beta

/-- The displayed coefficient really is a nonnegative constant under the
exponent inequalities used by the minimum-modulus theorem. -/
private theorem canonicalProductLowerConstant_nonneg
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
private theorem canonicalProduct_log_norm_lower_on_good_sphere
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

set_option autoImplicit false

/-- A direct, reusable form of the finite-order maximum-modulus estimate. -/
private theorem log_maxModulus_eventually_le_rpow_of_order_lt
    (f : ℂ → ℂ) (alpha : ℝ)
    (horder : entireOrder f < (alpha : EReal)) :
    ∃ R₀ : ℝ, 1 < R₀ ∧ ∀ r : ℝ, R₀ ≤ r →
      Real.log (maxModulus f r) ≤ r ^ alpha := by
  have hev := eventually_lt_of_limsup_lt horder
  have hbound : ∀ᶠ r in Filter.atTop,
      Real.log (maxModulus f r) ≤ r ^ alpha := by
    apply (hev.and (Filter.eventually_ge_atTop 2)).mono
    intro r ⟨hr_limsup, hr_ge⟩
    have hr_gt1 : (1 : ℝ) < r := by linarith
    have hlogr : 0 < Real.log r := Real.log_pos hr_gt1
    have hr_limsup' :
        Real.log (Real.log (maxModulus f r)) / Real.log r < alpha := by
      exact_mod_cast hr_limsup
    by_cases hlogM : Real.log (maxModulus f r) ≤ 0
    · exact le_trans hlogM
        (rpow_nonneg (le_of_lt (lt_trans zero_lt_one hr_gt1)) alpha)
    · push_neg at hlogM
      rw [show r ^ alpha = Real.exp (alpha * Real.log r) from by
        rw [rpow_def_of_pos (lt_trans zero_lt_one hr_gt1), mul_comm]]
      exact le_of_lt
        ((Real.log_lt_iff_lt_exp hlogM).mp
          ((div_lt_iff₀ hlogr).mp hr_limsup'))
  obtain ⟨R₁, hR₁⟩ := Filter.eventually_atTop.mp hbound
  refine ⟨max R₁ 2, by linarith [le_max_right R₁ 2], ?_⟩
  intro r hr
  exact hR₁ r ((le_max_left R₁ 2).trans hr)

/-- On a sphere separated from every zero, the canonical product lower bound
turns a maximum-modulus bound for `f` into an upper bound for `Re g`. -/
private theorem re_le_on_canonical_good_sphere
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (m : ℕ) (g : ℂ → ℂ) (a : ℕ → ℂ) (p : ℕ)
    (hfact : ∀ z : ℂ, f z = z ^ m * Complex.exp (g z) *
      ∏' n, weierstraßElementary p (z / a n))
    (beta alpha : ℝ)
    (hp_beta : (p : ℝ) < beta) (hbeta_alpha : beta < alpha)
    (hbeta_q : beta < (p : ℝ) + 1)
    (hsumm : Summable (fun n ↦ ‖a n‖⁻¹ ^ beta))
    (R : ℝ) (hR : 1 ≤ R)
    (hlogMax : Real.log (maxModulus f R) ≤ R ^ alpha)
    (hsep : ∀ w : ℂ, ‖w‖ = R → ∀ n, ‖a n‖⁻¹ ^ alpha ≤ ‖w - a n‖) :
    ∀ w : ℂ, ‖w‖ = R →
      (g w).re ≤
        (canonicalProductLowerConstant a p beta alpha + 1) * R ^ alpha := by
  have hbeta : 0 < beta := lt_of_le_of_lt (Nat.cast_nonneg p) hp_beta
  have halpha : 0 < alpha := hbeta.trans hbeta_alpha
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hconv : Summable (fun n ↦ ‖a n‖⁻¹ ^ ((p : ℝ) + 1)) :=
    summable_inv_norm_rpow_of_le a beta ((p : ℝ) + 1)
      hbeta hbeta_q.le hsumm
  have hK_nonneg : 0 ≤ canonicalProductLowerConstant a p beta alpha :=
    canonicalProductLowerConstant_nonneg a p beta alpha hp_beta hbeta_alpha
  intro w hw
  let P : ℂ := ∏' n, weierstraßElementary p (w / a n)
  have hw_ne : w ≠ 0 := by
    intro hw0
    rw [hw0, norm_zero] at hw
    linarith
  have hne : ∀ n, w / a n ≠ 1 := by
    intro n heq
    have han : a n ≠ 0 := by
      intro han
      simp [han] at heq
    have hwa : w = a n := (div_eq_one_iff_eq han).mp heq
    have hdelta : 0 < ‖a n‖⁻¹ ^ alpha :=
      Real.rpow_pos_of_pos (inv_pos.mpr (norm_pos_iff.mpr han)) alpha
    have h := hsep w hw n
    rw [hwa, sub_self, norm_zero] at h
    linarith
  have hP_ne : P ≠ 0 := by
    exact tprod_weierstraßElementary_ne_zero a p hconv w hne
  have hfw_ne : f w ≠ 0 := by
    rw [hfact w]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero m hw_ne)
      (Complex.exp_ne_zero (g w))) hP_ne
  have hnorm_f_le : ‖f w‖ ≤ maxModulus f R :=
    norm_le_maxModulus f hf w R hRpos hw.le
  have hlog_f_le : Real.log ‖f w‖ ≤ R ^ alpha :=
    (Real.log_le_log (norm_pos_iff.mpr hfw_ne) hnorm_f_le).trans hlogMax
  have hP_lower :
      -canonicalProductLowerConstant a p beta alpha * R ^ alpha ≤
        Real.log ‖P‖ := by
    exact canonicalProduct_log_norm_lower_on_good_sphere
      a p beta alpha hp_beta hbeta_alpha hbeta_q hsumm w R hw hR (hsep w hw)
  have hlog_factorization :
      Real.log ‖f w‖ =
        (m : ℝ) * Real.log R + (g w).re + Real.log ‖P‖ := by
    rw [hfact w]
    change Real.log ‖w ^ m * Complex.exp (g w) * P‖ = _
    rw [norm_mul, norm_mul,
      Real.log_mul (mul_ne_zero (norm_ne_zero_iff.mpr (pow_ne_zero m hw_ne))
        (norm_ne_zero_iff.mpr (Complex.exp_ne_zero (g w))))
        (norm_ne_zero_iff.mpr hP_ne),
      Real.log_mul (norm_ne_zero_iff.mpr (pow_ne_zero m hw_ne))
        (norm_ne_zero_iff.mpr (Complex.exp_ne_zero (g w))),
      norm_pow, Real.log_pow, Complex.norm_exp, Real.log_exp, hw]
  have hmlog_nonneg : 0 ≤ (m : ℝ) * Real.log R :=
    mul_nonneg (Nat.cast_nonneg m) (Real.log_nonneg hR)
  rw [hlog_factorization] at hlog_f_le
  linarith

/-- **Sound real-part growth bound for a canonical factorization.**

The additional exponent `beta` records the genuinely necessary genus data:
`p < beta < alpha`, `beta < p+1`, and the inverse-`beta` power sum of the
zeros converges.  These hypotheses exclude the noncanonical factorization
counterexample to the old `re_bound_of_factorization` statement. -/
private theorem re_bound_of_canonical_factorization
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (m : ℕ) (g : ℂ → ℂ) (a : ℕ → ℂ) (p : ℕ)
    (hg_diff : Differentiable ℂ g)
    (hfact : ∀ z : ℂ, f z = z ^ m * Complex.exp (g z) *
      ∏' n, weierstraßElementary p (z / a n))
    (beta alpha : ℝ)
    (hp_beta : (p : ℝ) < beta) (hbeta_alpha : beta < alpha)
    (hbeta_q : beta < (p : ℝ) + 1)
    (hsumm : Summable (fun n ↦ ‖a n‖⁻¹ ^ beta))
    (horder : entireOrder f < (alpha : EReal)) :
    ∃ A : ℝ, 0 < A ∧ ∀ z : ℂ,
      (g z).re ≤ A * (1 + ‖z‖) ^ alpha := by
  have hbeta : 0 < beta := lt_of_le_of_lt (Nat.cast_nonneg p) hp_beta
  have halpha : 0 < alpha := hbeta.trans hbeta_alpha
  have hsumm_alpha : Summable (fun n ↦ ‖a n‖⁻¹ ^ alpha) :=
    summable_inv_norm_rpow_of_le a beta alpha hbeta hbeta_alpha.le hsumm
  obtain ⟨Rₑ, hRₑ, hlogMax⟩ :=
    log_maxModulus_eventually_le_rpow_of_order_lt f alpha horder
  obtain ⟨Rₒ, hRₒ, hgood⟩ :=
    canonicalProduct_exists_good_sphere a alpha hsumm_alpha
  let D : ℝ := max Rₑ Rₒ
  have hD_gt_one : 1 < D := hRₑ.trans_le (le_max_left Rₑ Rₒ)
  have hD_pos : 0 < D := zero_lt_one.trans hD_gt_one
  let K : ℝ := canonicalProductLowerConstant a p beta alpha
  have hK_nonneg : 0 ≤ K := by
    exact canonicalProductLowerConstant_nonneg a p beta alpha hp_beta hbeta_alpha
  let A : ℝ := (K + 1) * (4 * D) ^ alpha
  have hA_pos : 0 < A := by
    exact mul_pos (by linarith) (Real.rpow_pos_of_pos (mul_pos (by norm_num) hD_pos) alpha)
  refine ⟨A, hA_pos, ?_⟩
  intro z
  let r : ℝ := D * (1 + ‖z‖)
  have hfactor_one : 1 ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
  have hfactor_pos : 0 < 1 + ‖z‖ := zero_lt_one.trans_le hfactor_one
  have hr_pos : 0 < r := mul_pos hD_pos hfactor_pos
  have hD_le_r : D ≤ r := by
    calc
      D = D * 1 := by ring
      _ ≤ D * (1 + ‖z‖) := mul_le_mul_of_nonneg_left hfactor_one hD_pos.le
      _ = r := rfl
  have hRₑ_le_r : Rₑ ≤ r := (le_max_left Rₑ Rₒ).trans hD_le_r
  have hRₒ_le_r : Rₒ ≤ r := (le_max_right Rₑ Rₒ).trans hD_le_r
  obtain ⟨R, hR_lower, hR_upper, hsep⟩ := hgood r hRₒ_le_r
  have hr_le_R : r ≤ R := by linarith
  have hR_pos : 0 < R := hr_pos.trans_le hr_le_R
  have hR_one : 1 ≤ R := by
    exact le_trans hD_gt_one.le (hD_le_r.trans hr_le_R)
  have hRₑ_le_R : Rₑ ≤ R := hRₑ_le_r.trans hr_le_R
  have hboundary : ∀ w : ℂ, ‖w‖ = R →
      (g w).re ≤ (K + 1) * R ^ alpha := by
    simpa only [K] using re_le_on_canonical_good_sphere
      f hf m g a p hfact beta alpha hp_beta hbeta_alpha hbeta_q hsumm
      R hR_one (hlogMax R hRₑ_le_R)
      (fun w hw n ↦ (hsep w hw n).le)
  have hz_lt_r : ‖z‖ < r := by
    have hone_mul_lt : 1 * (1 + ‖z‖) < D * (1 + ‖z‖) :=
      mul_lt_mul_of_pos_right hD_gt_one hfactor_pos
    dsimp only [r]
    linarith
  have hz_lt_R : ‖z‖ < R := hz_lt_r.trans_le hr_le_R
  have hexp_bound :
      ‖(Complex.exp ∘ g) z‖ ≤ Real.exp ((K + 1) * R ^ alpha) := by
    apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
      ((Complex.differentiable_exp.comp hg_diff).diffContOnCl)
    · intro w hw
      rw [frontier_ball (0 : ℂ) hR_pos.ne'] at hw
      simp only [Metric.mem_sphere, dist_zero_right] at hw
      simp only [Function.comp_apply, Complex.norm_exp]
      exact Real.exp_le_exp.mpr (hboundary w hw)
    · exact subset_closure (mem_ball_zero_iff.mpr hz_lt_R)
  have hz_re_le : (g z).re ≤ (K + 1) * R ^ alpha := by
    simpa only [Function.comp_apply, Complex.norm_exp, Real.exp_le_exp] using hexp_bound
  have hR_rpow : R ^ alpha ≤ (4 * r) ^ alpha :=
    Real.rpow_le_rpow hR_pos.le hR_upper halpha.le
  have hKR_rpow : (K + 1) * R ^ alpha ≤ (K + 1) * (4 * r) ^ alpha :=
    mul_le_mul_of_nonneg_left hR_rpow (by linarith)
  calc
    (g z).re ≤ (K + 1) * R ^ alpha := hz_re_le
    _ ≤ (K + 1) * (4 * r) ^ alpha := hKR_rpow
    _ = A * (1 + ‖z‖) ^ alpha := by
      have h4D_nonneg : 0 ≤ 4 * D := (mul_pos (by norm_num) hD_pos).le
      have hfactor_nonneg : 0 ≤ 1 + ‖z‖ := hfactor_pos.le
      rw [show 4 * r = (4 * D) * (1 + ‖z‖) by simp only [r]; ring,
        Real.mul_rpow h4D_nonneg hfactor_nonneg]
      simp only [A]
      ring

/-- Borel–Carathéodory upgrades the sound real-part estimate to a norm bound
with the same exponent. -/
theorem canonical_factorization_growth
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (m : ℕ) (g : ℂ → ℂ) (a : ℕ → ℂ) (p : ℕ)
    (hg_diff : Differentiable ℂ g)
    (hfact : ∀ z : ℂ, f z = z ^ m * Complex.exp (g z) *
      ∏' n, weierstraßElementary p (z / a n))
    (beta alpha : ℝ)
    (hp_beta : (p : ℝ) < beta) (hbeta_alpha : beta < alpha)
    (hbeta_q : beta < (p : ℝ) + 1)
    (hsumm : Summable (fun n ↦ ‖a n‖⁻¹ ^ beta))
    (horder : entireOrder f < (alpha : EReal)) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ,
      ‖g z‖ ≤ C * (1 + ‖z‖) ^ alpha := by
  have hbeta : 0 < beta := lt_of_le_of_lt (Nat.cast_nonneg p) hp_beta
  have halpha : 0 < alpha := hbeta.trans hbeta_alpha
  obtain ⟨B, hB_pos, h_re⟩ := re_bound_of_canonical_factorization
    f hf m g a p hg_diff hfact beta alpha hp_beta hbeta_alpha hbeta_q hsumm horder
  let C₀ : ℝ := 2 * B * 3 ^ alpha + 3 * ‖g 0‖
  refine ⟨max C₀ 1, lt_max_of_lt_right one_pos, ?_⟩
  intro z
  let R : ℝ := 2 * (1 + ‖z‖)
  have hz_nonneg : 0 ≤ ‖z‖ := norm_nonneg z
  have hR_pos : 0 < R := by positivity
  have hz_R : z ∈ Metric.ball (0 : ℂ) R := by
    simp only [Metric.mem_ball, dist_zero_right]
    linarith
  have hR_sub : 0 < R - ‖z‖ := by linarith
  have h_maps : MapsTo g (Metric.ball 0 R)
      {w : ℂ | w.re ≤ B * (1 + R) ^ alpha} := by
    intro w hw
    simp only [mem_setOf_eq]
    have hw_norm : ‖w‖ < R := by
      rwa [Metric.mem_ball, dist_zero_right] at hw
    calc
      (g w).re ≤ B * (1 + ‖w‖) ^ alpha := h_re w
      _ ≤ B * (1 + R) ^ alpha := by gcongr
  let M : ℝ := B * (1 + R) ^ alpha
  have hM_pos : 0 < M := by positivity
  have h_bc := Complex.borelCaratheodory hM_pos hg_diff.differentiableOn
    h_maps hR_pos hz_R
  have h1R : 1 + R ≤ 3 * (1 + ‖z‖) := by linarith
  have h1R_alpha : (1 + R) ^ alpha ≤ (3 * (1 + ‖z‖)) ^ alpha :=
    Real.rpow_le_rpow (by positivity) h1R halpha.le
  have h3alpha :
      (3 * (1 + ‖z‖)) ^ alpha = 3 ^ alpha * (1 + ‖z‖) ^ alpha :=
    Real.mul_rpow (by norm_num) (by linarith)
  have h1alpha : 1 ≤ (1 + ‖z‖) ^ alpha := by
    calc
      (1 : ℝ) = 1 ^ alpha := (one_rpow alpha).symm
      _ ≤ (1 + ‖z‖) ^ alpha :=
        Real.rpow_le_rpow (by norm_num) (by linarith) halpha.le
  have ht₁ : 2 * M * ‖z‖ / (R - ‖z‖) ≤ 2 * M := by
    rw [div_le_iff₀ hR_sub]
    nlinarith [Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 1 + R) alpha]
  have ht₂ : ‖g 0‖ * (R + ‖z‖) / (R - ‖z‖) ≤ 3 * ‖g 0‖ := by
    rw [div_le_iff₀ hR_sub]
    nlinarith [norm_nonneg (g 0)]
  have hM_bound : M ≤ B * 3 ^ alpha * (1 + ‖z‖) ^ alpha := by
    show B * (1 + R) ^ alpha ≤ B * 3 ^ alpha * (1 + ‖z‖) ^ alpha
    calc
      B * (1 + R) ^ alpha ≤ B * (3 ^ alpha * (1 + ‖z‖) ^ alpha) := by
        gcongr
        linarith [h3alpha ▸ h1R_alpha]
      _ = B * 3 ^ alpha * (1 + ‖z‖) ^ alpha := by ring
  calc
    ‖g z‖ ≤
        2 * M * ‖z‖ / (R - ‖z‖) +
          ‖g 0‖ * (R + ‖z‖) / (R - ‖z‖) := h_bc
    _ ≤ 2 * M + 3 * ‖g 0‖ := by linarith
    _ ≤ 2 * (B * 3 ^ alpha * (1 + ‖z‖) ^ alpha) + 3 * ‖g 0‖ := by
      nlinarith
    _ = (2 * B * 3 ^ alpha) * (1 + ‖z‖) ^ alpha + 3 * ‖g 0‖ := by
      ring
    _ ≤ (2 * B * 3 ^ alpha) * (1 + ‖z‖) ^ alpha +
          3 * ‖g 0‖ * (1 + ‖z‖) ^ alpha := by
      nlinarith [le_mul_of_one_le_right (by positivity : (0 : ℝ) ≤ 3 * ‖g 0‖) h1alpha]
    _ = C₀ * (1 + ‖z‖) ^ alpha := by ring
    _ ≤ max C₀ 1 * (1 + ‖z‖) ^ alpha := by
      nlinarith [le_max_left C₀ 1,
        Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ 1 + ‖z‖) alpha]

/-- Strengthened companion to `weierstraß_factorization` exposing the construction's
    canonical genus, zero coverage, and analytic multiplicities. Zero padding is
    retained, so entries are asserted to be zeros only when nonzero. -/
theorem weierstraß_factorization_canonical (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) (hf_ne : ¬ f = 0) (hfin : HasFiniteOrder f) :
    ∃ (m : ℕ) (g : ℂ → ℂ) (a : ℕ → ℂ) (p : ℕ),
      Differentiable ℂ g ∧
      (∀ n, a n ≠ 0 → f (a n) = 0) ∧
      Summable (fun n => (‖a n‖⁻¹) ^ ((p : ℝ) + 1)) ∧
      (∀ z, f z = z ^ m * Complex.exp (g z) *
        ∏' n, weierstraßElementary p (z / a n)) ∧
      p = Nat.floor (entireOrder f).toReal ∧
      (∀ z, f z = 0 → z ≠ 0 → ∃ n, z = a n) ∧
      ∀ z, f z = 0 → z ≠ 0 →
        analyticOrderAt f z =
          analyticOrderAt (fun w => ∏' n, weierstraßElementary p (w / a n)) z := by
  -- Split into zero-free and has-zeros cases
  by_cases hzf : ∀ z, f z ≠ 0
  · -- f is zero-free: use entire logarithm theorem.
    -- Take m = 0, canonical p, and a = const 0, so every product factor is 1.
    obtain ⟨g, hg_diff, hg_eq⟩ := entire_logarithm f hf hzf
    set p₀ := Nat.floor (entireOrder f).toReal
    refine ⟨0, g, fun _ => 0, p₀, hg_diff,
      fun n h => absurd rfl h, ?_, ?_, rfl, ?_, ?_⟩
    · -- Summability: the padded sequence contributes only zero terms.
      exact summable_of_ne_finset_zero (s := ∅) (fun n _ => by
        simp [norm_zero, inv_zero,
          Real.zero_rpow (by positivity : (p₀ : ℝ) + 1 ≠ 0)])
    · intro z
      simp [hg_eq z, weierstraßElementary_zero]
    · intro z hfz _
      exact (hzf z hfz).elim
    · intro z hfz _
      exact (hzf z hfz).elim
  · -- f has zeros: Weierstraß product construction for finite-order functions.
    -- analyticOrderAt_tprod_weierstraß is now proved; remaining issues are
    -- stutteredEnum_pair_lt alignment and Encodable.decode₂ API mismatches.
    push_neg at hzf
    -- ═══════════════════════════════════════════════════════════
    -- Step 1: Factor out the zero at the origin
    -- f(z) = z^m · f₁(z) with f₁(0) ≠ 0, using analytic order at 0
    -- ═══════════════════════════════════════════════════════════
    obtain ⟨m, f₁, hf₁_diff, hf₁_nz, hf_eq⟩ :
        ∃ (m : ℕ) (f₁ : ℂ → ℂ), Differentiable ℂ f₁ ∧ f₁ 0 ≠ 0 ∧
          ∀ z, f z = z ^ m * f₁ z := by
      by_cases hf0 : f 0 ≠ 0
      · exact ⟨0, f, hf, hf0, fun z => by simp⟩
      · push_neg at hf0
        have hf_an : AnalyticAt ℂ f 0 := hf.analyticAt 0
        have hord_ne_top : analyticOrderAt f 0 ≠ ⊤ :=
          (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero 0
            (fun z => hf.analyticAt z)).not.mpr hf_ne
        set m' := analyticOrderNatAt f 0
        obtain ⟨g, hg_an, hg_nz, hg_eq⟩ := hf_an.analyticOrderAt_ne_top.mp hord_ne_top
        have hg_eq' : ∀ᶠ z in 𝓝 (0 : ℂ), f z = z ^ m' * g z :=
          hg_eq.mono fun z hz => by simp only [sub_zero, smul_eq_mul] at hz; exact hz
        refine ⟨m', Function.update (fun z => f z / z ^ m') 0 (g 0), ?_, ?_, ?_⟩
        · -- f₁ is entire
          intro z₀
          by_cases hz₀ : z₀ = 0
          · subst hz₀
            refine (hg_an.congr ?_).differentiableAt
            apply hg_eq'.mono
            intro z hz
            by_cases hz0 : z = 0
            · subst hz0; simp [Function.update_self]
            · rw [Function.update_of_ne hz0, hz,
                mul_div_cancel_left₀ _ (pow_ne_zero m' hz0)]
          · exact (hf.differentiableAt.div ((differentiable_pow m').differentiableAt)
              (pow_ne_zero m' hz₀)).congr_of_eventuallyEq
              ((isOpen_ne.eventually_mem hz₀).mono fun z hz =>
                Function.update_of_ne hz _ _)
        · simp [Function.update_self, hg_nz]
        · intro z
          by_cases hz : z = 0
          · subst hz; rw [Function.update_self]; exact hg_eq'.self_of_nhds
          · simp only [Function.update_of_ne hz]
            exact (mul_div_cancel₀ (f z) (pow_ne_zero m' hz)).symm
    -- ═══════════════════════════════════════════════════════════
    -- Step 2: Enumerate zeros with summability
    -- ═══════════════════════════════════════════════════════════
    obtain ⟨a, p, ha_zeros, hconv, ha_covers, ha_ord_eq, hp⟩ :
        ∃ (a : ℕ → ℂ) (p : ℕ),
          (∀ n, a n ≠ 0 → f₁ (a n) = 0) ∧
          Summable (fun n => (‖a n‖⁻¹) ^ ((p : ℝ) + 1)) ∧
          (∀ z, f₁ z = 0 → ∃ n, z = a n) ∧
          (∀ z, f₁ z = 0 → z ≠ 0 →
            analyticOrderAt f₁ z =
              analyticOrderAt (fun w => ∏' n, weierstraßElementary p (w / a n)) z) ∧
          p = Nat.floor (entireOrder f).toReal := by
      -- Step 2a: Zeros of f₁ are discrete and countable
      have hf₁_ne : ¬ f₁ = 0 := fun h => hf₁_nz (by rw [h]; simp)
      have hf₁_an : AnalyticOnNhd ℂ f₁ Set.univ := fun z _ => hf₁_diff.analyticAt z
      have hcodisc : f₁ ⁻¹' {0}ᶜ ∈ Filter.codiscrete ℂ :=
        hf₁_an.preimage_zero_mem_codiscrete hf₁_nz
      have hdisc : IsDiscrete (f₁ ⁻¹' {0}) := by
        have := (mem_codiscrete'.mp hcodisc).2
        rwa [Set.preimage_compl, compl_compl] at this
      have hcount : (f₁ ⁻¹' {0}).Countable :=
        (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete hdisc
      letI : Encodable (f₁ ⁻¹' {0}) := hcount.toEncodable
      -- Step 2b: Enumerate distinct zeros
      set a₀ : ℕ → ℂ := fun n =>
        match @Encodable.decode₂ (f₁ ⁻¹' {0}) hcount.toEncodable n with
        | some y => y | none => 0
      have ha₀_surj : ∀ z, f₁ z = 0 → ∃ k, z = a₀ k := by
        intro z hz
        refine ⟨@Encodable.encode _ hcount.toEncodable ⟨z, Set.mem_preimage.mpr
          (Set.mem_singleton_iff.mpr hz)⟩, ?_⟩
        simp only [a₀, Encodable.decode₂_encode]
      have ha₀_zeros : ∀ k, a₀ k ≠ 0 → f₁ (a₀ k) = 0 := by
        intro k hk
        simp only [a₀] at hk ⊢
        cases h : @Encodable.decode₂ (f₁ ⁻¹' {0}) hcount.toEncodable k with
        | none => simp [h] at hk
        | some val => simp; exact val.2
      have ha₀_inj : Set.InjOn a₀ {k | a₀ k ≠ 0} := by
        intro i hi j hj hij
        simp only [a₀] at hi hj hij
        cases hi_decode : @Encodable.decode₂ (f₁ ⁻¹' {0}) hcount.toEncodable i with
        | none => simp [hi_decode] at hi
        | some vi =>
          cases hj_decode : @Encodable.decode₂ (f₁ ⁻¹' {0}) hcount.toEncodable j with
          | none => simp [hj_decode] at hj
          | some vj =>
            have hv : vi = vj := by
              apply Subtype.ext
              simpa [hi_decode, hj_decode] using hij
            rw [Encodable.decode₂_eq_some] at hi_decode hj_decode
            rw [← hi_decode, ← hj_decode, hv]
      -- Step 2c: Define multiplicities and stuttered enumeration
      set mult' : ℕ → ℕ := fun k =>
        if a₀ k = 0 then 0 else analyticOrderNatAt f₁ (a₀ k)
      have hmult_pos : ∀ k, a₀ k ≠ 0 → 0 < mult' k := by
        intro k hk
        simp only [mult', hk, ite_false]
        rw [Nat.pos_iff_ne_zero, Ne, analyticOrderNatAt, ENat.toNat_eq_zero, not_or]
        exact ⟨analyticOrderAt_ne_zero.mpr ⟨hf₁_diff.analyticAt _, ha₀_zeros k hk⟩,
          (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero (a₀ k)
            (fun z => hf₁_diff.analyticAt z)).not.mpr hf₁_ne⟩
      have hmult_zero : ∀ k, a₀ k = 0 → mult' k = 0 :=
        fun k hk => by simp [mult', hk]
      have hmult_le : ∀ k, a₀ k ≠ 0 →
          mult' k ≤ analyticOrderNatAt f (a₀ k) := by
        intro k hk
        simp only [mult', hk, ite_false]
        apply le_of_eq
        have hfun : f = (fun w : ℂ => w ^ m) * f₁ := by
          funext w
          exact hf_eq w
        have hpow_an : AnalyticAt ℂ (fun w : ℂ => w ^ m) (a₀ k) :=
          (differentiable_pow m).analyticAt (a₀ k)
        have hpow_order_enat : analyticOrderAt (fun w : ℂ => w ^ m) (a₀ k) = 0 :=
          hpow_an.analyticOrderAt_eq_zero.mpr (pow_ne_zero m hk)
        have hpow_ne_top : analyticOrderAt (fun w : ℂ => w ^ m) (a₀ k) ≠ ⊤ := by
          rw [hpow_order_enat]
          exact ENat.zero_ne_top
        have hf₁_ne_top : analyticOrderAt f₁ (a₀ k) ≠ ⊤ :=
          (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero (a₀ k)
            (fun w => hf₁_diff.analyticAt w)).not.mpr hf₁_ne
        rw [hfun, analyticOrderNatAt_mul hpow_an (hf₁_diff.analyticAt (a₀ k))
          hpow_ne_top hf₁_ne_top]
        have hpow_order : analyticOrderNatAt (fun w : ℂ => w ^ m) (a₀ k) = 0 := by
          rw [analyticOrderNatAt, hpow_order_enat]
          rfl
        rw [hpow_order, zero_add]
      set a' := stutteredEnum a₀ mult'
      set p' := Nat.floor (entireOrder f).toReal
      -- Step 2d: Verify properties
      have ha_zeros' : ∀ n, a' n ≠ 0 → f₁ (a' n) = 0 :=
        fun n hn => stutteredEnum_maps_zeros ha₀_zeros hn
      have ha_covers' : ∀ z, f₁ z = 0 → ∃ n, z = a' n := by
        intro z hz
        obtain ⟨k, rfl⟩ := ha₀_surj z hz
        have hk : a₀ k ≠ 0 := fun h0 => hf₁_nz (h0 ▸ hz)
        obtain ⟨n, hn⟩ := stutteredEnum_covers (hmult_pos k hk)
        exact ⟨n, hn.symm⟩
      have hconv' : Summable (fun n => (‖a' n‖⁻¹) ^ ((p' : ℝ) + 1)) :=
        summable_stutteredEnum_of_weighted (Nat.cast_add_one_pos p')
          (finite_order_zero_summable_weighted f hf hf_ne hfin a₀
            (fun k hk => by have := ha₀_zeros k hk; rw [hf_eq]; simp [this])
            ha₀_inj mult' hmult_zero hmult_le)
      refine ⟨a', p', ha_zeros', hconv', ha_covers', ?_, rfl⟩
      -- Order equality: analytic order of Weierstraß product at each zero
      -- equals analyticOrderAt f₁ there.
      intro z hz hne
      obtain ⟨k, rfl⟩ := ha₀_surj z hz
      have hk : a₀ k ≠ 0 := hne
      -- The multiplicity m = analyticOrderNatAt f₁ (a₀ k)
      set m := mult' k with hm_def
      have hm_pos : 0 < m := hmult_pos k hk
      -- analyticOrderAt f₁ (a₀ k) = ↑m
      have hord_ne_top : analyticOrderAt f₁ (a₀ k) ≠ ⊤ :=
        (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero (a₀ k)
          (fun z => hf₁_diff.analyticAt z)).not.mpr hf₁_ne
      have hord_f₁ : analyticOrderAt f₁ (a₀ k) = ↑m := by
        simp only [m, mult', hk, ite_false]
        exact (Nat.cast_analyticOrderNatAt hord_ne_top).symm
      rw [hord_f₁]
      -- Use the standalone tprod order lemma
      set S : Finset ℕ := (Finset.range m).image (Nat.pair k)
      have hS_val : ∀ n ∈ S, a' n = a₀ k := by
        intro n hn; simp only [S, Finset.mem_image, Finset.mem_range] at hn
        obtain ⟨j, hj, rfl⟩ := hn; exact stutteredEnum_pair_lt hj
      have hS_compl : ∀ n, n ∉ S → a' n ≠ a₀ k := by
        intro n hn ha'n_eq
        have ha'n_ne : a' n ≠ 0 := ha'n_eq ▸ hk
        have ⟨hlt, ha₀_ne⟩ := stutteredEnum_ne_zero_imp ha'n_ne
        have ha'_simp : a' n = a₀ n.unpair.1 := by
          simp only [a', stutteredEnum_apply, hlt, if_true]
        have heq_a₀ : a₀ n.unpair.1 = a₀ k := ha'_simp ▸ ha'n_eq
        -- enumerateCountable injectivity: a₀ n.unpair.1 = a₀ k → n.unpair.1 = k
        have hfst_eq : n.unpair.1 = k := by
          simp only [a₀] at ha₀_ne heq_a₀
          revert ha₀_ne heq_a₀
          cases h1 : @Encodable.decode₂ (f₁ ⁻¹' {0}) hcount.toEncodable n.unpair.1 with
          | none => simp
          | some v1 =>
            cases h2 : @Encodable.decode₂ (f₁ ⁻¹' {0}) hcount.toEncodable k with
            | none => simp_all
            | some v2 =>
              intro _ heq
              have hv_eq : v1 = v2 := Subtype.val_injective heq
              rw [Encodable.decode₂_eq_some] at h1 h2
              rw [← h1, ← h2, hv_eq]
        have hlt' : n.unpair.2 < m := by
          simpa only [hm_def, hfst_eq] using hlt
        exact hn (by
          rw [show n = Nat.pair n.unpair.1 n.unpair.2 from (Nat.pair_unpair n).symm, hfst_eq]
          exact Finset.mem_image_of_mem _ (Finset.mem_range.mpr hlt'))
      have hS_card : S.card = m := by
        simp only [S]
        exact (Finset.card_image_of_injective _
          (fun j₁ j₂ h => (Nat.pair_eq_pair.mp h).2)).trans (Finset.card_range m)
      rw [← hS_card]
      exact (analyticOrderAt_tprod_weierstraß a' p' hconv' (a₀ k) hk S hS_val hS_compl).symm
    -- ═══════════════════════════════════════════════════════════
    -- Step 3–4: Quotient f₁/P is entire and zero-free
    -- ═══════════════════════════════════════════════════════════
    obtain ⟨h, hh_diff, hh_ne, hh_eq⟩ :
        ∃ (h : ℂ → ℂ), Differentiable ℂ h ∧ (∀ z, h z ≠ 0) ∧
          (∀ z, f₁ z = h z * ∏' n, weierstraßElementary p (z / a n)) := by
      set P : ℂ → ℂ := fun z => ∏' n, weierstraßElementary p (z / a n)
      have hP_diff : Differentiable ℂ P := tprod_weierstraßElementary_differentiable a p hconv
      have hq_diff : ∀ z, P z ≠ 0 → DifferentiableAt ℂ (fun w => f₁ w / P w) z :=
        fun z hz => hf₁_diff.differentiableAt.div hP_diff.differentiableAt hz
      set h₀ : ℂ → ℂ := fun z =>
        if P z ≠ 0 then f₁ z / P z
        else limUnder (𝓝[≠] z) (fun w => f₁ w / P w)
      have hh₀_eq : ∀ z, f₁ z = h₀ z * P z := by
        intro z
        by_cases hPz : P z ≠ 0
        · rw [show h₀ z = f₁ z / P z from if_pos hPz, div_mul_cancel₀ (f₁ z) hPz]
        · push_neg at hPz
          have hf₁z : f₁ z = 0 := by
            by_contra hf₁z_ne
            have hne : ∀ n, z / a n ≠ 1 := by
              intro n heq
              by_cases han : a n = 0
              · simp [han] at heq
              · exact hf₁z_ne ((div_eq_one_iff_eq han).mp heq ▸ ha_zeros n han)
            exact absurd hPz (tprod_weierstraßElementary_ne_zero a p hconv z hne)
          rw [hf₁z, hPz, mul_zero]
      have hh₀_diff : Differentiable ℂ h₀ := by
        intro z₀
        by_cases hPz₀ : P z₀ ≠ 0
        · have heq : h₀ =ᶠ[𝓝 z₀] fun w => f₁ w / P w := by
            have : ∀ᶠ w in 𝓝 z₀, P w ≠ 0 :=
              hP_diff.continuous.continuousAt.eventually_ne hPz₀
            exact this.mono fun w hw => by simp [h₀, hw]
          exact (hq_diff z₀ hPz₀).congr_of_eventuallyEq heq
        · push_neg at hPz₀
          have hP_an : AnalyticAt ℂ P z₀ := hP_diff.analyticAt z₀
          have hP_not_ev_zero : ¬ ∀ᶠ w in 𝓝 z₀, P w = 0 := by
            intro hev
            have hf₁_ev : ∀ᶠ w in 𝓝 z₀, f₁ w = 0 :=
              hev.mono fun w hw => by rw [hh₀_eq w, hw, mul_zero]
            have hf₁_eq : f₁ = 0 := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z₀
              (fun z => hf₁_diff.analyticAt z)).mp (analyticOrderAt_eq_top.mpr hf₁_ev)
            exact hf₁_nz (congr_fun hf₁_eq 0)
          have hP_ev_ne : ∀ᶠ w in 𝓝[≠] z₀, P w ≠ 0 :=
            hP_an.eventually_eq_zero_or_eventually_ne_zero.resolve_left hP_not_ev_zero
          have hh₀_diff_punct : ∀ᶠ w in 𝓝[≠] z₀, DifferentiableAt ℂ h₀ w := by
            apply hP_ev_ne.mono
            intro w hw
            have heq : h₀ =ᶠ[𝓝 w] fun v => f₁ v / P v :=
              (hP_diff.continuous.continuousAt.eventually_ne hw).mono
                fun v hv => by simp [h₀, hv]
            exact (hf₁_diff.differentiableAt.div hP_diff.differentiableAt hw).congr_of_eventuallyEq
              heq
          -- ContinuousAt h₀ z₀: factor f₁ and P by their equal analytic orders,
          -- cancel (z-z₀)^k to get h₀ = u/v, then use continuity of u/v.
          have hcont : ContinuousAt h₀ z₀ := by
            -- f₁ vanishes at z₀
            have hf₁z₀ : f₁ z₀ = 0 := by
              by_contra hne
              exact absurd hPz₀ (tprod_weierstraßElementary_ne_zero a p hconv z₀
                fun n heq => by
                  by_cases han : a n = 0
                  · simp [han] at heq
                  · exact hne ((div_eq_one_iff_eq han).mp heq ▸ ha_zeros n han))
            -- z₀ ≠ 0
            have hz₀_ne : z₀ ≠ 0 := by
              intro heq; rw [heq] at hPz₀
              have : P 0 = ∏' n, weierstraßElementary p (0 / a n) := rfl
              simp only [zero_div, weierstraßElementary_zero, tprod_one] at this
              exact one_ne_zero (this ▸ hPz₀)
            have hord := ha_ord_eq z₀ hf₁z₀ hz₀_ne
            -- Neither function is identically zero
            have hf₁_ne : ¬ f₁ = 0 := fun h => hf₁_nz (congr_fun h 0)
            have hP_ne : ¬ P = 0 := by
              intro heq
              have : P 0 = 0 := congr_fun heq 0
              simp only [P, zero_div, weierstraßElementary_zero, tprod_one] at this
              exact one_ne_zero this
            have hf₁_top : analyticOrderAt f₁ z₀ ≠ ⊤ :=
              (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z₀
                (fun z => hf₁_diff.analyticAt z)).not.mpr hf₁_ne
            have hP_top : analyticOrderAt P z₀ ≠ ⊤ := hord ▸ hf₁_top
            -- Factor: f₁(z) =ᶠ (z-z₀)^k • u(z), P(z) =ᶠ (z-z₀)^k • v(z)
            set k := analyticOrderNatAt f₁ z₀ with hk_def
            obtain ⟨u, hu_an, hu_ne, hu_eq⟩ :=
              (hf₁_diff.analyticAt z₀).analyticOrderAt_ne_top.mp hf₁_top
            obtain ⟨v, hv_an, hv_ne, hv_eq⟩ :=
              (hP_diff.analyticAt z₀).analyticOrderAt_ne_top.mp hP_top
            have hP_ord : analyticOrderNatAt P z₀ = k := by
              simp only [analyticOrderNatAt]; congr 1; exact hord.symm
            rw [hP_ord] at hv_eq
            -- u/v is continuous at z₀
            have huv_cont : ContinuousAt (fun w => u w / v w) z₀ :=
              hu_an.continuousAt.div hv_an.continuousAt hv_ne
            -- h₀ = u/v on 𝓝[≠] z₀ (cancel (z-z₀)^k via smul = mul in ℂ)
            have heq_uv : ∀ᶠ w in 𝓝[≠] z₀, h₀ w = u w / v w := by
              apply (hP_ev_ne.and ((hu_eq.and hv_eq).filter_mono nhdsWithin_le_nhds)).mono
              rintro w ⟨hwP, hwu, hwv⟩
              -- h₀ w = f₁ w / P w (since P w ≠ 0)
              change (if P w ≠ 0 then f₁ w / P w else _) = u w / v w
              rw [if_pos hwP]
              -- f₁ w = (w-z₀)^k • u w, P w = (w-z₀)^k • v w
              have hwne : (w - z₀) ^ k ≠ 0 := pow_ne_zero k (sub_ne_zero.mpr (by
                intro heq; rw [heq] at hwP; exact hwP hPz₀))
              simp only [hwu, hwv, smul_eq_mul]
              exact mul_div_mul_left (u w) (v w) hwne
            -- Tendsto h₀ (𝓝[≠] z₀) (𝓝 (u z₀ / v z₀))
            have htend : Tendsto h₀ (𝓝[≠] z₀) (𝓝 (u z₀ / v z₀)) :=
              (huv_cont.tendsto.mono_left nhdsWithin_le_nhds).congr'
                (heq_uv.mono fun w hw => hw.symm)
            -- h₀ z₀ = u z₀ / v z₀ (limUnder uniqueness in T2)
            have hval : h₀ z₀ = u z₀ / v z₀ := by
              -- h₀ z₀ = limUnder (𝓝[≠] z₀) h₀ by definition (P z₀ = 0 branch)
              -- limUnder h₀ = u z₀ / v z₀ by htend (T2 uniqueness)
              have hlim_eq : (𝓝[≠] z₀).limUnder h₀ = u z₀ / v z₀ := htend.limUnder_eq
              -- h₀ z₀ = limUnder (f₁/P) on 𝓝[≠] z₀
              -- limUnder (f₁/P) = limUnder h₀ since they agree eventually
              -- h₀ z₀ = limUnder h₀ on 𝓝[≠] z₀
              -- First: h₀ z₀ = limUnder (f₁/P)
              have h₀_val : h₀ z₀ = (𝓝[≠] z₀).limUnder (fun w => f₁ w / P w) := by
                simp only [h₀, show ¬(P z₀ ≠ 0) from not_not.mpr hPz₀, ↓reduceIte]
              -- Second: the Tendsto of f₁/P toward u z₀/v z₀ gives its limUnder
              have htend_fg : Tendsto (fun w => f₁ w / P w) (𝓝[≠] z₀) (𝓝 (u z₀ / v z₀)) := by
                apply htend.congr'
                have : ∀ᶠ w in 𝓝[≠] z₀, h₀ w = f₁ w / P w :=
                  hP_ev_ne.mono fun w hw => (if_pos hw : h₀ w = f₁ w / P w)
                exact this.mono fun w (hw : h₀ w = f₁ w / P w) =>
                  show h₀ w = (fun w => f₁ w / P w) w from hw
              rw [h₀_val, htend_fg.limUnder_eq]
            -- ContinuousAt via nhds = nhdsWithin ⊔ pure
            rw [ContinuousAt, hval, ← nhdsNE_sup_pure z₀]
            exact htend.sup (Filter.tendsto_pure_left.mpr fun _s hs =>
              hval ▸ mem_of_mem_nhds hs)
          exact (analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
            hh₀_diff_punct hcont).differentiableAt
      have hh₀_ne : ∀ z, h₀ z ≠ 0 := by
        intro z hz
        have hf₁z : f₁ z = 0 := by rw [hh₀_eq z, hz, zero_mul]
        obtain ⟨n, rfl⟩ := ha_covers z hf₁z
        have han : a n ≠ 0 := fun h => hf₁_nz (h ▸ hf₁z)
        -- All functions are entire and not identically zero
        have hf₁_ne : ¬ f₁ = 0 := fun h => hf₁_nz (congr_fun h 0)
        have hh₀_ne_fun : ¬ h₀ = 0 := by
          intro h; apply hf₁_ne; ext z; simp [hh₀_eq z, show h₀ z = 0 from congr_fun h z]
        have hP_ne_fun : ¬ P = 0 := by
          intro hP_eq
          have hP0 : P 0 = 0 := congr_fun hP_eq 0
          have : (fun n => weierstraßElementary p (0 / a n)) = fun _ => (1 : ℂ) :=
            funext fun n => by rw [zero_div, weierstraßElementary_zero]
          simp only [P, this, tprod_one] at hP0 -- hP0 : 1 = 0
          exact one_ne_zero hP0
        -- Orders are finite (not ⊤) since functions are analytic and not identically zero
        have hf₁_top : analyticOrderAt f₁ (a n) ≠ ⊤ :=
          (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero (a n)
            (fun z => hf₁_diff.analyticAt z)).not.mpr hf₁_ne
        have hh₀_top : analyticOrderAt h₀ (a n) ≠ ⊤ :=
          (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero (a n)
            (fun z => hh₀_diff.analyticAt z)).not.mpr hh₀_ne_fun
        have hP_top : analyticOrderAt P (a n) ≠ ⊤ :=
          (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero (a n)
            (fun z => hP_diff.analyticAt z)).not.mpr hP_ne_fun
        -- f₁ = h₀ * P ⟹ order(f₁) = order(h₀) + order(P) in ℕ
        have hord_eq : analyticOrderNatAt f₁ (a n) =
            analyticOrderNatAt h₀ (a n) + analyticOrderNatAt P (a n) := by
          have hfun_eq : f₁ = h₀ * P :=
            funext fun z => by rw [hh₀_eq z, Pi.mul_apply]
          conv_lhs => rw [hfun_eq]
          exact analyticOrderNatAt_mul (hh₀_diff.analyticAt _) (hP_diff.analyticAt _)
            hh₀_top hP_top
        -- h₀(a n) = 0 ⟹ order(h₀, a n) ≥ 1
        have hh₀_pos : 1 ≤ analyticOrderNatAt h₀ (a n) := by
          rw [Nat.one_le_iff_ne_zero, Ne, analyticOrderNatAt,
            ENat.toNat_eq_zero, not_or]
          exact ⟨analyticOrderAt_ne_zero.mpr ⟨hh₀_diff.analyticAt _, hz⟩, hh₀_top⟩
        -- From multiplicity-aware enumeration: order(P, a n) = order(f₁, a n)
        have hP_ge : analyticOrderNatAt f₁ (a n) ≤ analyticOrderNatAt P (a n) := by
          have h := ha_ord_eq (a n) hf₁z han
          -- h : analyticOrderAt f₁ (a n) = analyticOrderAt P (a n)
          simp only [analyticOrderNatAt]
          exact ENat.toNat_le_toNat h.le hP_top
        -- Contradiction: f₁_ord = h₀_ord + P_ord ≥ 1 + f₁_ord, impossible in ℕ
        omega
      exact ⟨h₀, hh₀_diff, hh₀_ne, hh₀_eq⟩
    -- ═══════════════════════════════════════════════════════════
    -- Step 5: entire_logarithm + assembly
    -- ═══════════════════════════════════════════════════════════
    obtain ⟨g, hg_diff, hg_eq⟩ := entire_logarithm h hh_diff hh_ne
    refine ⟨m, g, a, p, hg_diff,
      fun n hn => by rw [hf_eq (a n), ha_zeros n hn, mul_zero],
      hconv, ?_, hp, ?_, ?_⟩
    · intro z
      rw [hf_eq z, hh_eq z, hg_eq z, ← mul_assoc]
    · intro z hfz hz
      have hf₁z : f₁ z = 0 := by
        have hmul : z ^ m * f₁ z = 0 := by rw [← hf_eq z, hfz]
        exact (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero m hz)
      exact ha_covers z hf₁z
    · intro z hfz hz
      have hf₁z : f₁ z = 0 := by
        have hmul : z ^ m * f₁ z = 0 := by rw [← hf_eq z, hfz]
        exact (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero m hz)
      have hpow_an : AnalyticAt ℂ (fun w : ℂ => w ^ m) z :=
        (differentiable_pow m).analyticAt z
      have hpow_order : analyticOrderAt (fun w : ℂ => w ^ m) z = 0 :=
        hpow_an.analyticOrderAt_eq_zero.mpr (pow_ne_zero m hz)
      have hfun : f = (fun w : ℂ => w ^ m) * f₁ := by
        funext w
        exact hf_eq w
      calc
        analyticOrderAt f z =
            analyticOrderAt ((fun w : ℂ => w ^ m) * f₁) z := by rw [hfun]
        _ = analyticOrderAt (fun w : ℂ => w ^ m) z + analyticOrderAt f₁ z :=
          analyticOrderAt_mul hpow_an (hf₁_diff.analyticAt z)
        _ = analyticOrderAt f₁ z := by rw [hpow_order, zero_add]
        _ = analyticOrderAt
            (fun w => ∏' n, weierstraßElementary p (w / a n)) z :=
          ha_ord_eq z hf₁z hz

/-- Transfer multiplicity-weighted zero summability to an opaque canonical
sequence using its analytic-order specification. -/
theorem canonical_sequence_summable_of_order_lt
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
theorem affine_of_growth_lt_two
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

end ArithmeticHodge.Analysis.EntireFunction

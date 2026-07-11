import ArithmeticHodge.Analysis.EntireFunction.MinimumModulus
import ArithmeticHodge.Analysis.EntireFunction.WeierstraßProduct
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real

open Complex Filter Topology Real Set

namespace ArithmeticHodge.Analysis.EntireFunction

set_option autoImplicit false

/-- Summability of inverse `beta`-powers forces local finiteness of the
nonzero entries of a possibly zero-padded sequence. -/
theorem finite_nonzero_indices_norm_le_of_summable
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
theorem ratio_rpow_le_inv_rpow
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
theorem finite_sum_ratio_rpow_le
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
theorem finite_sum_ratio_pow_le
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
theorem finite_sum_ratio_pow_le_rpow
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
theorem log_le_scaled_inv_rpow
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
theorem finite_sum_log_norm_le_rpow
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

end ArithmeticHodge.Analysis.EntireFunction

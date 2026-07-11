import ArithmeticHodge.Analysis.ZetaZeroFreeRegionReduction

/-!
# Explicit zeta bounds immediately to the right of the pole

The positive Dirichlet series and Mathlib's exact zeta-asymptotic remainder
identity give the elementary estimate `ζ(1 + x) ≤ 1 + 1/x` for every
`x > 0`.  We then insert this estimate into the quantitative zero-free-region
reduction.
-/

set_option autoImplicit false

open Complex Real Set

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-- On the positive real axis to the right of the pole, the Riemann zeta
function is the real `p`-series. -/
theorem riemannZeta_one_add_eq_real_tsum
    {x : ℝ} (hx : 0 < x) :
    riemannZeta (1 + x) =
      (∑' n : ℕ, 1 / (n + 1 : ℝ) ^ (1 + x) : ℝ) := by
  have hs : 1 < ((1 + x : ℝ) : ℂ).re := by simp; linarith
  rw [show (1 : ℂ) + x = ((1 + x : ℝ) : ℂ) by norm_num]
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
  rw [Complex.ofReal_tsum]
  congr 1 with n
  rw [show (n + 1 : ℂ) = (((n : ℝ) + 1 : ℝ) : ℂ) by norm_num]
  rw [← Complex.ofReal_cpow (by positivity) (1 + x)]
  norm_cast

/-- The real positive `p`-series estimate underlying the zeta bound. -/
theorem tsum_one_div_nat_add_one_rpow_le_one_add_inv
    {x : ℝ} (hx : 0 < x) :
    (∑' n : ℕ, 1 / (n + 1 : ℝ) ^ (1 + x)) ≤ 1 + 1 / x := by
  let p : ℝ := 1 + x
  let Z : ℝ := ∑' n : ℕ, 1 / (n + 1 : ℝ) ^ p
  have hp : 1 < p := by dsimp only [p]; linarith
  have hterm : 0 ≤ ZetaAsymptotics.term_tsum p := by
    exact tsum_nonneg fun n => ZetaAsymptotics.term_nonneg (n + 1) p
  have hZ : Z - 1 / (p - 1) =
      1 - p * ZetaAsymptotics.term_tsum p := by
    simpa only [Z] using ZetaAsymptotics.zeta_limit_aux1 hp
  have hpnonneg : 0 ≤ p := by linarith
  have hprod : 0 ≤ p * ZetaAsymptotics.term_tsum p :=
    mul_nonneg hpnonneg hterm
  dsimp only [p] at hZ hprod
  rw [show 1 + x - 1 = x by ring] at hZ
  change Z ≤ 1 + 1 / x
  nlinarith

/-- Elementary near-pole bound, valid in fact for every `x > 0`. -/
theorem norm_riemannZeta_one_add_le_one_add_inv
    {x : ℝ} (hx : 0 < x) :
    ‖riemannZeta (1 + x)‖ ≤ 1 + 1 / x := by
  let Z : ℝ := ∑' n : ℕ, 1 / (n + 1 : ℝ) ^ (1 + x)
  have hZnonneg : 0 ≤ Z := by
    exact tsum_nonneg fun n => by positivity
  rw [riemannZeta_one_add_eq_real_tsum hx]
  change ‖(Z : ℂ)‖ ≤ 1 + 1 / x
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hZnonneg]
  exact tsum_one_div_nat_add_one_rpow_le_one_add_inv hx

/-- The same `1 + 1/x` estimate holds uniformly on the whole vertical line
`Re(s) = 1 + x`. -/
theorem norm_riemannZeta_one_add_add_I_mul_le_one_add_inv
    {x : ℝ} (hx : 0 < x) (t : ℝ) :
    ‖riemannZeta (1 + x + I * t)‖ ≤ 1 + 1 / x := by
  let s : ℂ := 1 + x + I * t
  have hs : 1 < s.re := by simp [s]; linarith
  have hsumm : Summable
      (fun n : ℕ => 1 / (n + 1 : ℂ) ^ s) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).2
        (Complex.summable_one_div_nat_cpow.mpr hs)
  rw [show (1 : ℂ) + x + I * t = s by rfl,
    zeta_eq_tsum_one_div_nat_add_one_cpow hs]
  calc
    ‖∑' n : ℕ, 1 / (n + 1 : ℂ) ^ s‖ ≤
        ∑' n : ℕ, ‖1 / (n + 1 : ℂ) ^ s‖ :=
      norm_tsum_le_tsum_norm hsumm.norm
    _ = ∑' n : ℕ, 1 / (n + 1 : ℝ) ^ (1 + x) := by
      apply tsum_congr
      intro n
      rw [norm_div, norm_one]
      have hbase : (0 : ℝ) < n + 1 := by positivity
      rw [show (n + 1 : ℂ) = (((n : ℝ) + 1 : ℝ) : ℂ) by norm_num,
        Complex.norm_cpow_eq_rpow_re_of_pos hbase]
      simp only [s, add_re, one_re, ofReal_re, mul_re, I_re,
        ofReal_im, I_im, zero_mul, mul_zero, sub_self, add_zero]
    _ ≤ 1 + 1 / x :=
      tsum_one_div_nat_add_one_rpow_le_one_add_inv hx

/-- Half-plane form of the positive Dirichlet-series majorant. -/
theorem norm_riemannZeta_le_one_add_inv_of_one_add_le_re
    {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : 1 + x ≤ s.re) :
    ‖riemannZeta s‖ ≤ 1 + 1 / x := by
  have hsone : 1 < s.re := by linarith
  have hsum : Summable (fun n : ℕ => 1 / (n + 1 : ℂ) ^ s) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).2
        (Complex.summable_one_div_nat_cpow.mpr hsone)
  have hmajor : Summable
      (fun n : ℕ => 1 / (n + 1 : ℝ) ^ (1 + x)) := by
    convert (summable_nat_add_iff 1).2
      (Real.summable_nat_rpow_inv.mpr (by linarith : 1 < 1 + x)) using 1 with n
    norm_num [one_div]
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hsone]
  have hpoint : ∀ n : ℕ,
      ‖1 / (n + 1 : ℂ) ^ s‖ ≤
        1 / (n + 1 : ℝ) ^ (1 + x) := by
    intro n
    rw [norm_div, norm_one]
    have hnpos : (0 : ℝ) < n + 1 := by positivity
    rw [show (n + 1 : ℂ) = ((n + 1 : ℕ) : ℂ) by push_cast; rfl]
    rw [show ‖((n + 1 : ℕ) : ℂ) ^ s‖ =
        (((n + 1 : ℕ) : ℝ) ^ s.re) by
      exact Complex.norm_natCast_cpow_of_pos (Nat.succ_pos n) s]
    norm_num only [Nat.cast_add, Nat.cast_one]
    apply (one_div_le_one_div_of_le
      (Real.rpow_pos_of_pos hnpos (1 + x))
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) hs))
  calc
    ‖∑' n : ℕ, 1 / (n + 1 : ℂ) ^ s‖ ≤
        ∑' n : ℕ, ‖1 / (n + 1 : ℂ) ^ s‖ :=
      norm_tsum_le_tsum_norm hsum.norm
    _ ≤ ∑' n : ℕ, 1 / (n + 1 : ℝ) ^ (1 + x) :=
      hsum.norm.tsum_le_tsum hpoint hmajor
    _ ≤ 1 + 1 / x :=
      tsum_one_div_nat_add_one_rpow_le_one_add_inv hx

/-- An explicit derivative bound on the line `Re(s)=1+x`, obtained from the
preceding half-plane zeta bound and Cauchy's estimate on a radius-`x/2`
circle. -/
theorem norm_deriv_riemannZeta_one_add_add_I_mul_le
    {x : ℝ} (hx : 0 < x) (t : ℝ) :
    ‖deriv riemannZeta (1 + x + I * t)‖ ≤
      2 / x + 4 / x ^ 2 := by
  let z : ℂ := 1 + x + I * t
  let r : ℝ := x / 2
  have hr : 0 < r := by dsimp only [r]; linarith
  have hd : DiffContOnCl ℂ riemannZeta (Metric.ball z r) := by
    apply DifferentiableOn.diffContOnCl
    intro w hw
    apply DifferentiableAt.differentiableWithinAt
    apply differentiableAt_riemannZeta
    intro hwone
    have hwclosed : w ∈ Metric.closedBall z r :=
      Metric.closure_ball_subset_closedBall hw
    have hdist : ‖w - z‖ ≤ r := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using hwclosed
    have hre : |w.re - z.re| ≤ ‖w - z‖ := by
      simpa only [Complex.sub_re] using Complex.abs_re_le_norm (w - z)
    rw [abs_le] at hre
    have hwre : 1 < w.re := by
      dsimp only [z, r] at hdist hre
      simp only [add_re, one_re, ofReal_re, mul_re, I_re,
        ofReal_im, I_im, zero_mul, mul_zero, sub_self, add_zero] at hre
      linarith
    rw [hwone] at hwre
    norm_num at hwre
  have hsphere : ∀ w ∈ Metric.sphere z r,
      ‖riemannZeta w‖ ≤ 1 + 1 / (x / 2) := by
    intro w hw
    have hdist : ‖w - z‖ = r := by
      simpa only [Metric.mem_sphere, dist_eq_norm] using hw
    have hre : |w.re - z.re| ≤ ‖w - z‖ := by
      simpa only [Complex.sub_re] using Complex.abs_re_le_norm (w - z)
    rw [abs_le] at hre
    have hwre : 1 + x / 2 ≤ w.re := by
      dsimp only [z, r] at hdist hre
      simp only [add_re, one_re, ofReal_re, mul_re, I_re,
        ofReal_im, I_im, zero_mul, mul_zero, sub_self, add_zero] at hre
      linarith
    exact norm_riemannZeta_le_one_add_inv_of_one_add_le_re
      (by linarith : 0 < x / 2) hwre
  have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    hr hd hsphere
  change ‖deriv riemannZeta z‖ ≤ 2 / x + 4 / x ^ 2
  calc
    ‖deriv riemannZeta z‖ ≤ (1 + 1 / (x / 2)) / (x / 2) := hcauchy
    _ = 2 / x + 4 / x ^ 2 := by field_simp [hx.ne']; ring

/-- Convenient `2/x` version on the range used by the zero-free reduction. -/
theorem norm_riemannZeta_one_add_le_two_div
    {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    ‖riemannZeta (1 + x)‖ ≤ 2 / x := by
  calc
    ‖riemannZeta (1 + x)‖ ≤ 1 + 1 / x :=
      norm_riemannZeta_one_add_le_one_add_inv hx
    _ ≤ 2 / x := by
      apply (le_div_iff₀ hx).2
      rw [add_mul, one_mul, div_mul_cancel₀ _ hx.ne']
      linarith

/-- The zero-free-region reduction with its near-pole zeta majorant discharged
explicitly by `1 + 1/x`. -/
theorem riemannZeta_zero_re_le_of_near_one_majorants
    {beta t x B D ell : ℝ}
    (hx : 0 < x) (ht : t ≠ 0) (hbeta : beta ≤ 1 + x)
    (hzero : riemannZeta (beta + t * I) = 0)
    (hD : ∀ z ∈ segment ℝ ((beta : ℂ) + t * I)
        (((1 + x : ℝ) : ℂ) + t * I),
      ‖deriv riemannZeta z‖ ≤ D)
    (hB : ‖riemannZeta (1 + x + 2 * I * t)‖ ≤ B)
    (hell : 0 < ell)
    (hmajor : (1 + 1 / x) ^ 3 * D ^ 4 * B ≤ ell ^ 4) :
    1 / ell - x ≤ 1 - beta := by
  exact riemannZeta_zero_re_le_of_majorants hx ht hbeta hzero hD
    (norm_riemannZeta_one_add_le_one_add_inv hx) hB hell hmajor

/-- Both zeta-value majorants in the `3-4-1` reduction are discharged by the
same vertical-line bound.  Only the horizontal derivative majorant remains. -/
theorem riemannZeta_zero_re_le_of_near_one_and_deriv_majorant
    {beta t x D ell : ℝ}
    (hx : 0 < x) (ht : t ≠ 0) (hbeta : beta ≤ 1 + x)
    (hzero : riemannZeta (beta + t * I) = 0)
    (hD : ∀ z ∈ segment ℝ ((beta : ℂ) + t * I)
        (((1 + x : ℝ) : ℂ) + t * I),
      ‖deriv riemannZeta z‖ ≤ D)
    (hell : 0 < ell)
    (hmajor : (1 + 1 / x) ^ 4 * D ^ 4 ≤ ell ^ 4) :
    1 / ell - x ≤ 1 - beta := by
  have hA := norm_riemannZeta_one_add_le_one_add_inv hx
  have hB : ‖riemannZeta (1 + x + 2 * I * t)‖ ≤ 1 + 1 / x := by
    rw [show (1 : ℂ) + x + 2 * I * t =
      1 + x + I * (2 * t : ℝ) by push_cast; ring]
    exact norm_riemannZeta_one_add_add_I_mul_le_one_add_inv hx (2 * t)
  apply riemannZeta_zero_re_le_of_majorants hx ht hbeta hzero hD hA hB hell
  calc
    (1 + 1 / x) ^ 3 * D ^ 4 * (1 + 1 / x) =
        (1 + 1 / x) ^ 4 * D ^ 4 := by ring
    _ ≤ ell ^ 4 := hmajor

/-- A cleaner corollary on `0 < x ≤ 1`, using the coarser majorant `2/x`. -/
theorem riemannZeta_zero_re_le_of_two_div_majorants
    {beta t x B D ell : ℝ}
    (hx : 0 < x) (hx1 : x ≤ 1)
    (ht : t ≠ 0) (hbeta : beta ≤ 1 + x)
    (hzero : riemannZeta (beta + t * I) = 0)
    (hD : ∀ z ∈ segment ℝ ((beta : ℂ) + t * I)
        (((1 + x : ℝ) : ℂ) + t * I),
      ‖deriv riemannZeta z‖ ≤ D)
    (hB : ‖riemannZeta (1 + x + 2 * I * t)‖ ≤ B)
    (hell : 0 < ell)
    (hmajor : (2 / x) ^ 3 * D ^ 4 * B ≤ ell ^ 4) :
    1 / ell - x ≤ 1 - beta := by
  exact riemannZeta_zero_re_le_of_majorants hx ht hbeta hzero hD
    (norm_riemannZeta_one_add_le_two_div hx hx1) hB hell hmajor

/-- `2/x` variant with both zeta-value majorants discharged. -/
theorem riemannZeta_zero_re_le_of_two_div_and_deriv_majorant
    {beta t x D ell : ℝ}
    (hx : 0 < x) (hx1 : x ≤ 1)
    (ht : t ≠ 0) (hbeta : beta ≤ 1 + x)
    (hzero : riemannZeta (beta + t * I) = 0)
    (hD : ∀ z ∈ segment ℝ ((beta : ℂ) + t * I)
        (((1 + x : ℝ) : ℂ) + t * I),
      ‖deriv riemannZeta z‖ ≤ D)
    (hell : 0 < ell)
    (hmajor : (2 / x) ^ 4 * D ^ 4 ≤ ell ^ 4) :
    1 / ell - x ≤ 1 - beta := by
  have hA := norm_riemannZeta_one_add_le_two_div hx hx1
  have hB : ‖riemannZeta (1 + x + 2 * I * t)‖ ≤ 2 / x := by
    calc
      ‖riemannZeta (1 + x + 2 * I * t)‖ ≤ 1 + 1 / x := by
        rw [show (1 : ℂ) + x + 2 * I * t =
          1 + x + I * (2 * t : ℝ) by push_cast; ring]
        exact norm_riemannZeta_one_add_add_I_mul_le_one_add_inv hx (2 * t)
      _ ≤ 2 / x := by
        apply (le_div_iff₀ hx).2
        rw [add_mul, one_mul, div_mul_cancel₀ _ hx.ne']
        linarith
  apply riemannZeta_zero_re_le_of_majorants hx ht hbeta hzero hD hA hB hell
  calc
    (2 / x) ^ 3 * D ^ 4 * (2 / x) =
        (2 / x) ^ 4 * D ^ 4 := by ring
    _ ≤ ell ^ 4 := hmajor

end

end ArithmeticHodge.Analysis.MultiplicativeWeil

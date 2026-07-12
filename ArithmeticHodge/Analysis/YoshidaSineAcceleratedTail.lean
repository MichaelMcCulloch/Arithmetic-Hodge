import ArithmeticHodge.Analysis.YoshidaSineSeriesTail

set_option autoImplicit false

open Filter Real
open scoped BigOperators Topology

namespace ArithmeticHodge.Analysis.YoshidaSineAcceleratedTail

noncomputable section

open YoshidaCauchyTailBounds
open YoshidaMomentSeries
open YoshidaOddGramPrefix
open YoshidaSineSeriesTail

/-!
# Accelerated tail bounds for Yoshida's sine moments

The existing tail enclosure keeps only the leading reciprocal-square term.
Here the exact identity

`y / (t^2 + y^2) = y/t^2 - y^3/t^4 + y^5/(t^4*(t^2+y^2))`

retains the next asymptotic term and bounds the positive remainder by a
reciprocal sixth-power tail.  This is intended to make the `10^-5` even
sine-moment targets scalable beyond the first few modes.
-/

def shiftedInvPow (x : ℝ) (p : ℕ) (k : ℕ) : ℝ :=
  1 / (x + k) ^ p

def shiftedInvPowLowerPotential (x : ℝ) (p : ℕ) (k : ℕ) : ℝ :=
  1 / ((p - 1 : ℕ) * (x + k) ^ (p - 1))

def shiftedInvPowUpperPotential (x : ℝ) (p : ℕ) (k : ℕ) : ℝ :=
  shiftedInvPow x p k + shiftedInvPowLowerPotential x p k

private theorem summable_shiftedInvPow
    {x : ℝ} (hx : 1 ≤ x) {p : ℕ} (hp : 1 < p) :
    Summable (shiftedInvPow x p) := by
  have hs := (Real.summable_one_div_nat_add_rpow x (p : ℝ)).2 (by
    exact_mod_cast hp)
  apply hs.congr
  intro k
  rw [shiftedInvPow, abs_of_pos (by positivity : 0 < (k : ℝ) + x),
    Real.rpow_natCast]
  congr 2
  ring

private theorem tendsto_inv_shifted (x : ℝ) :
    Tendsto (fun k : ℕ ↦ (x + (k : ℝ))⁻¹) atTop (nhds 0) := by
  have htop : Tendsto (fun k : ℕ ↦ x + (k : ℝ)) atTop atTop :=
    tendsto_const_nhds.add_atTop
      (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa only [one_div] using htop.const_div_atTop 1

private theorem tendsto_shiftedInvPow
    (x : ℝ) {p : ℕ} (hp : 0 < p) :
    Tendsto (shiftedInvPow x p) atTop (nhds 0) := by
  have h := (tendsto_inv_shifted x).pow p
  convert h using 1
  · funext k
    rw [shiftedInvPow, one_div, inv_pow]
  · simp [hp.ne']

private theorem tendsto_shiftedInvPowLowerPotential
    (x : ℝ) {p : ℕ} (hp : 1 < p) :
    Tendsto (shiftedInvPowLowerPotential x p) atTop (nhds 0) := by
  have hpow := tendsto_shiftedInvPow x (Nat.sub_pos_of_lt hp)
  have hscale := hpow.const_mul ((p - 1 : ℕ) : ℝ)⁻¹
  have heq : shiftedInvPowLowerPotential x p =
      fun k ↦ ((p - 1 : ℕ) : ℝ)⁻¹ * shiftedInvPow x (p - 1) k := by
    funext k
    rw [shiftedInvPowLowerPotential, shiftedInvPow]
    ring
  rw [heq]
  simpa using hscale

private theorem tendsto_shiftedInvPowUpperPotential
    (x : ℝ) {p : ℕ} (hp : 1 < p) :
    Tendsto (shiftedInvPowUpperPotential x p) atTop (nhds 0) := by
  simpa only [shiftedInvPowUpperPotential, zero_add] using
    (tendsto_shiftedInvPow x (by omega : 0 < p)).add
      (tendsto_shiftedInvPowLowerPotential x hp)

private theorem tsum_bounds_of_telescope
    {f lower upper : ℕ → ℝ}
    (hs : Summable f)
    (hlower : ∀ k, lower k - lower (k + 1) ≤ f k)
    (hupper : ∀ k, f k ≤ upper k - upper (k + 1))
    (hlowerLim : Tendsto lower atTop (nhds 0))
    (hupperLim : Tendsto upper atTop (nhds 0)) :
    lower 0 ≤ ∑' k, f k ∧ (∑' k, f k) ≤ upper 0 := by
  have hpartialLower (N : ℕ) :
      lower 0 - lower N ≤ ∑ k ∈ Finset.range N, f k := by
    rw [← Finset.sum_range_sub' lower]
    exact Finset.sum_le_sum fun k _ ↦ hlower k
  have hpartialUpper (N : ℕ) :
      (∑ k ∈ Finset.range N, f k) ≤ upper 0 - upper N := by
    rw [← Finset.sum_range_sub' upper]
    exact Finset.sum_le_sum fun k _ ↦ hupper k
  have hpartial := hs.hasSum.tendsto_sum_nat
  have hlowerLimit : Tendsto (fun N ↦ lower 0 - lower N)
      atTop (nhds (lower 0)) := by
    simpa using tendsto_const_nhds.sub hlowerLim
  have hupperLimit : Tendsto (fun N ↦ upper 0 - upper N)
      atTop (nhds (upper 0)) := by
    simpa using tendsto_const_nhds.sub hupperLim
  exact ⟨le_of_tendsto_of_tendsto hlowerLimit hpartial
      (Filter.Eventually.of_forall hpartialLower),
    le_of_tendsto_of_tendsto hpartial hupperLimit
      (Filter.Eventually.of_forall hpartialUpper)⟩

private theorem shiftedInvPowLowerPotential_sub_succ_le
    {x : ℝ} (hx : 1 ≤ x) {p : ℕ}
    (hp : p = 2 ∨ p = 4 ∨ p = 6) (k : ℕ) :
    shiftedInvPowLowerPotential x p k -
        shiftedInvPowLowerPotential x p (k + 1) ≤
      shiftedInvPow x p k := by
  let a : ℝ := x + k
  have ha : 0 < a := by dsimp only [a]; positivity
  have ha1 : 0 < a + 1 := by positivity
  rcases hp with (rfl | rfl | rfl)
  · dsimp [shiftedInvPowLowerPotential, shiftedInvPow, a]
    push_cast
    field_simp [ha.ne', ha1.ne']
    nlinarith
  · dsimp [shiftedInvPowLowerPotential, shiftedInvPow, a]
    push_cast
    field_simp [ha.ne', ha1.ne']
    nlinarith [sq_nonneg a, sq_nonneg (a + 1)]
  · dsimp [shiftedInvPowLowerPotential, shiftedInvPow, a]
    push_cast
    field_simp [ha.ne', ha1.ne']
    nlinarith [sq_nonneg a, sq_nonneg (a + 1),
      sq_nonneg (a ^ 2), sq_nonneg ((a + 1) ^ 2)]

private theorem shiftedInvPow_le_upperPotential_sub_succ
    {x : ℝ} (hx : 1 ≤ x) {p : ℕ}
    (hp : p = 2 ∨ p = 4 ∨ p = 6) (k : ℕ) :
    shiftedInvPow x p k ≤
      shiftedInvPowUpperPotential x p k -
        shiftedInvPowUpperPotential x p (k + 1) := by
  let a : ℝ := x + k
  have ha : 0 < a := by dsimp only [a]; positivity
  have ha1 : 0 < a + 1 := by positivity
  rcases hp with (rfl | rfl | rfl)
  · dsimp [shiftedInvPowUpperPotential, shiftedInvPowLowerPotential,
      shiftedInvPow, a]
    push_cast
    field_simp [ha.ne', ha1.ne']
    nlinarith
  · dsimp [shiftedInvPowUpperPotential, shiftedInvPowLowerPotential,
      shiftedInvPow, a]
    push_cast
    field_simp [ha.ne', ha1.ne']
    nlinarith [sq_nonneg a, sq_nonneg (a + 1),
      sq_nonneg (a ^ 2), sq_nonneg ((a + 1) ^ 2)]
  · dsimp [shiftedInvPowUpperPotential, shiftedInvPowLowerPotential,
      shiftedInvPow, a]
    push_cast
    field_simp [ha.ne', ha1.ne']
    nlinarith [sq_nonneg a, sq_nonneg (a + 1),
      sq_nonneg (a ^ 2), sq_nonneg ((a + 1) ^ 2),
      sq_nonneg (a ^ 3), sq_nonneg ((a + 1) ^ 3)]

/-- Integral-comparison-quality reciprocal-power tail boxes, specialized to
the three powers used by the accelerated Cauchy identity. -/
theorem shiftedInvPow_tsum_bounds
    {x : ℝ} (hx : 1 ≤ x) {p : ℕ}
    (hp : p = 2 ∨ p = 4 ∨ p = 6) :
    shiftedInvPowLowerPotential x p 0 ≤
        ∑' k, shiftedInvPow x p k ∧
      (∑' k, shiftedInvPow x p k) ≤
        shiftedInvPowUpperPotential x p 0 := by
  have hp1 : 1 < p := by rcases hp with (rfl | rfl | rfl) <;> norm_num
  exact tsum_bounds_of_telescope
    (summable_shiftedInvPow hx hp1)
    (shiftedInvPowLowerPotential_sub_succ_le hx hp)
    (shiftedInvPow_le_upperPotential_sub_succ hx hp)
    (tendsto_shiftedInvPowLowerPotential x hp1)
    (tendsto_shiftedInvPowUpperPotential x hp1)

def acceleratedMainLower (x y : ℝ) (k : ℕ) : ℝ :=
  y * shiftedInvPow x 2 k - y ^ 3 * shiftedInvPow x 4 k

def acceleratedMainUpper (x y : ℝ) (k : ℕ) : ℝ :=
  acceleratedMainLower x y k + y ^ 5 * shiftedInvPow x 6 k

private theorem cauchyTailTerm_sub_acceleratedMainLower
    {x y : ℝ} (hx : 1 ≤ x) (k : ℕ) :
    cauchyTailTerm x y k - acceleratedMainLower x y k =
      y ^ 5 /
        ((x + k) ^ 4 * ((x + k) ^ 2 + y ^ 2)) := by
  have ht : 0 < x + (k : ℝ) := by positivity
  have hden : 0 < (x + (k : ℝ)) ^ 2 + y ^ 2 := by positivity
  rw [cauchyTailTerm, acceleratedMainLower, shiftedInvPow,
    shiftedInvPow]
  field_simp [ht.ne', hden.ne']
  ring

private theorem cauchyTailTerm_accelerated_bounds
    {x y : ℝ} (hx : 1 ≤ x) (hy : 0 ≤ y) (k : ℕ) :
    acceleratedMainLower x y k ≤ cauchyTailTerm x y k ∧
      cauchyTailTerm x y k ≤ acceleratedMainUpper x y k := by
  have ht : 0 < x + (k : ℝ) := by positivity
  have hden : 0 < (x + (k : ℝ)) ^ 2 + y ^ 2 := by positivity
  have hid := cauchyTailTerm_sub_acceleratedMainLower (y := y) hx k
  constructor
  · rw [← sub_nonneg, hid]
    positivity
  · rw [acceleratedMainUpper]
    have hdenLe : (x + (k : ℝ)) ^ 6 ≤
        (x + (k : ℝ)) ^ 4 *
          ((x + (k : ℝ)) ^ 2 + y ^ 2) := by
      nlinarith [sq_nonneg ((x + (k : ℝ)) ^ 2 * y)]
    have hrem : cauchyTailTerm x y k - acceleratedMainLower x y k ≤
        y ^ 5 * shiftedInvPow x 6 k := by
      rw [hid, shiftedInvPow]
      simpa only [div_eq_mul_inv, one_mul] using
        (div_le_div_of_nonneg_left (pow_nonneg hy 5)
          (by positivity : 0 < (x + (k : ℝ)) ^ 6) hdenLe)
    simpa [add_comm] using (sub_le_iff_le_add.mp hrem)

private theorem summable_acceleratedMainLower
    {x y : ℝ} (hx : 1 ≤ x) :
    Summable (acceleratedMainLower x y) := by
  exact ((summable_shiftedInvPow hx (by norm_num : 1 < 2)).mul_left y).sub
    ((summable_shiftedInvPow hx (by norm_num : 1 < 4)).mul_left (y ^ 3))

private theorem summable_acceleratedMainUpper
    {x y : ℝ} (hx : 1 ≤ x) :
    Summable (acceleratedMainUpper x y) := by
  exact (summable_acceleratedMainLower hx).add
    ((summable_shiftedInvPow hx (by norm_num : 1 < 6)).mul_left (y ^ 5))

private theorem tsum_acceleratedMainLower
    {x y : ℝ} (hx : 1 ≤ x) :
    (∑' k, acceleratedMainLower x y k) =
      y * (∑' k, shiftedInvPow x 2 k) -
        y ^ 3 * (∑' k, shiftedInvPow x 4 k) := by
  let h2 := summable_shiftedInvPow hx (by norm_num : 1 < 2)
  let h4 := summable_shiftedInvPow hx (by norm_num : 1 < 4)
  change (∑' k : ℕ, (y * shiftedInvPow x 2 k -
      y ^ 3 * shiftedInvPow x 4 k)) = _
  rw [(h2.mul_left y).tsum_sub (h4.mul_left (y ^ 3)),
    tsum_mul_left, tsum_mul_left]

private theorem tsum_acceleratedMainUpper
    {x y : ℝ} (hx : 1 ≤ x) :
    (∑' k, acceleratedMainUpper x y k) =
      (∑' k, acceleratedMainLower x y k) +
        y ^ 5 * (∑' k, shiftedInvPow x 6 k) := by
  rw [show acceleratedMainUpper x y = fun k ↦
      acceleratedMainLower x y k + y ^ 5 * shiftedInvPow x 6 k by rfl]
  rw [Summable.tsum_add (summable_acceleratedMainLower hx)
    ((summable_shiftedInvPow hx (by norm_num : 1 < 6)).mul_left (y ^ 5)),
    (summable_shiftedInvPow hx (by norm_num : 1 < 6)).tsum_mul_left]

theorem cauchyTail_tsum_accelerated_bounds
    {x y : ℝ} (hx : 1 ≤ x) (hy : 0 ≤ y) :
    y * shiftedInvPowLowerPotential x 2 0 -
          y ^ 3 * shiftedInvPowUpperPotential x 4 0 ≤
        ∑' k, cauchyTailTerm x y k ∧
      (∑' k, cauchyTailTerm x y k) ≤
        y * shiftedInvPowUpperPotential x 2 0 -
          y ^ 3 * shiftedInvPowLowerPotential x 4 0 +
            y ^ 5 * shiftedInvPowUpperPotential x 6 0 := by
  have hmain := summable_cauchyTailTerm hx hy
  have hloPoint : ∀ k, acceleratedMainLower x y k ≤
      cauchyTailTerm x y k := fun k ↦
    (cauchyTailTerm_accelerated_bounds hx hy k).1
  have hupPoint : ∀ k, cauchyTailTerm x y k ≤
      acceleratedMainUpper x y k := fun k ↦
    (cauchyTailTerm_accelerated_bounds hx hy k).2
  have hloTsum := (summable_acceleratedMainLower hx).tsum_le_tsum
    hloPoint hmain
  have hupTsum := hmain.tsum_le_tsum hupPoint
    (summable_acceleratedMainUpper hx)
  have h2 := shiftedInvPow_tsum_bounds hx (Or.inl rfl : 2 = 2 ∨ 2 = 4 ∨ 2 = 6)
  have h4 := shiftedInvPow_tsum_bounds hx (Or.inr (Or.inl rfl) :
    4 = 2 ∨ 4 = 4 ∨ 4 = 6)
  have h6 := shiftedInvPow_tsum_bounds hx (Or.inr (Or.inr rfl) :
    6 = 2 ∨ 6 = 4 ∨ 6 = 6)
  rw [tsum_acceleratedMainLower hx] at hloTsum
  rw [tsum_acceleratedMainUpper hx, tsum_acceleratedMainLower hx] at hupTsum
  constructor
  · exact (sub_le_sub
      (mul_le_mul_of_nonneg_left h2.1 hy)
      (mul_le_mul_of_nonneg_left h4.2 (by positivity))).trans hloTsum
  · exact hupTsum.trans (add_le_add
      (sub_le_sub
        (mul_le_mul_of_nonneg_left h2.2 hy)
        (mul_le_mul_of_nonneg_left h4.1 (by positivity)))
      (mul_le_mul_of_nonneg_left h6.2 (by positivity)))

/-- The accelerated two-sided bound for the actual dyadically corrected sine
tail.  Unlike the original lower bound, its algebraic Cauchy remainder starts
at reciprocal fourth and sixth powers. -/
theorem sineCauchyTerm_tail_accelerated_bounds
    {n N : ℕ} (hn : n ≠ 0) (hN : 0 < N) :
    let x : ℝ := N + 1 / 4
    let y : ℝ := yoshidaScaledFrequency n
    y * shiftedInvPowLowerPotential x 2 0 -
          y ^ 3 * shiftedInvPowUpperPotential x 4 0 -
            2 * y / (4 : ℝ) ^ N ≤
        ∑' j : ℕ, sineCauchyTerm n (N + j) ∧
      (∑' j : ℕ, sineCauchyTerm n (N + j)) ≤
        y * shiftedInvPowUpperPotential x 2 0 -
          y ^ 3 * shiftedInvPowLowerPotential x 4 0 +
            y ^ 5 * shiftedInvPowUpperPotential x 6 0 := by
  dsimp only
  let x : ℝ := N + 1 / 4
  let y : ℝ := yoshidaScaledFrequency n
  have hx : 1 ≤ x := by
    dsimp only [x]
    have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hy : 0 ≤ y := by
    exact (yoshidaScaledFrequency_pos hn).le
  have hmain := cauchyTail_tsum_accelerated_bounds hx hy
  have hmainEq : (fun j : ℕ ↦ sineMainTerm n (N + j)) =
      cauchyTailTerm x y := by
    funext j
    simpa only [x, y] using sineMainTerm_shift n N j
  rw [← hmainEq] at hmain
  have hcorr := sineDyadicCorrection_tail_le hn hN
  have hmainSummable : Summable (fun j : ℕ ↦ sineMainTerm n (N + j)) := by
    simpa [Nat.add_comm] using
      (summable_nat_add_iff N).2 (summable_sineMainTerm hn)
  have hcorrSummable : Summable
      (fun j : ℕ ↦ sineDyadicCorrection n (N + j)) := by
    simpa [Nat.add_comm] using
      (summable_nat_add_iff N).2 (summable_sineDyadicCorrection hn)
  have htailEq :
      (∑' j : ℕ, sineCauchyTerm n (N + j)) =
        (∑' j : ℕ, sineMainTerm n (N + j)) -
          ∑' j : ℕ, sineDyadicCorrection n (N + j) := by
    rw [← hmainSummable.tsum_sub hcorrSummable]
    apply tsum_congr
    intro j
    exact sineCauchyTerm_eq_main_sub_correction n (N + j)
  have hcorr0 : 0 ≤ ∑' j : ℕ, sineDyadicCorrection n (N + j) :=
    tsum_nonneg (fun j ↦ sineDyadicCorrection_nonneg hn (N + j))
  rw [htailEq]
  constructor <;> linarith

end

end ArithmeticHodge.Analysis.YoshidaSineAcceleratedTail

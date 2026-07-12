import ArithmeticHodge.Analysis.YoshidaCauchyTailBounds
import ArithmeticHodge.Analysis.YoshidaMomentSeries

set_option autoImplicit false

open Filter Real
open scoped BigOperators Topology

namespace ArithmeticHodge.Analysis.YoshidaSineSeriesTail

noncomputable section

open YoshidaCauchyTailBounds
open YoshidaMomentSeries
open YoshidaOddGramPrefix
open YoshidaRenormalizedGeometricKernel

/-!
# Certified tails for the explicit Yoshida sine series

After scaling `κ = 2y`, the slow part of the sine Cauchy term is exactly

`y / ((k + 1/4)^2 + y^2)`.

The generic telescoping estimate in `YoshidaCauchyTailBounds` controls this
part.  The remaining dyadic correction is positive and is bounded by a
geometric series.  The result is a two-sided rational-function enclosure for
every tail beginning after a positive number of terms.
-/

/-- Half of Yoshida's angular frequency, `π n / log 2`. -/
def yoshidaScaledFrequency (n : ℕ) : ℝ := yoshidaKappa n / 2

/-- The unweighted quarter-shifted Cauchy summand. -/
def sineMainTerm (n k : ℕ) : ℝ :=
  cauchyTailTerm (1 / 4) (yoshidaScaledFrequency n) k

/-- The exponentially small dyadic correction to the main Cauchy summand. -/
def sineDyadicCorrection (n k : ℕ) : ℝ :=
  sineMainTerm n k * (Real.sqrt 2)⁻¹ / (4 : ℝ) ^ k

theorem yoshidaScaledFrequency_pos
    {n : ℕ} (hn : n ≠ 0) : 0 < yoshidaScaledFrequency n := by
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast Nat.pos_of_ne_zero hn
  rw [yoshidaScaledFrequency, yoshidaKappa]
  exact div_pos
    (div_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos) hnpos)
      yoshidaLength_pos)
    (by norm_num)

theorem sineCauchyTerm_eq_main_sub_correction (n k : ℕ) :
    sineCauchyTerm n k = sineMainTerm n k - sineDyadicCorrection n k := by
  rw [sineCauchyTerm, sineDyadicCorrection, sineMainTerm,
    cauchyTailTerm, yoshidaScaledFrequency, oddRate]
  ring_nf
  by_cases hk : yoshidaKappa n = 0
  · simp [hk]
  field_simp
  ring

theorem sineMainTerm_shift (n N j : ℕ) :
    sineMainTerm n (N + j) =
      cauchyTailTerm ((N : ℝ) + 1 / 4) (yoshidaScaledFrequency n) j := by
  rw [sineMainTerm, cauchyTailTerm, cauchyTailTerm]
  congr 2
  push_cast
  ring

theorem summable_sineMainTerm
    {n : ℕ} (hn : n ≠ 0) : Summable (sineMainTerm n) := by
  have hy : 0 ≤ yoshidaScaledFrequency n :=
    (yoshidaScaledFrequency_pos hn).le
  have htail : Summable
      (cauchyTailTerm ((1 : ℝ) + 1 / 4) (yoshidaScaledFrequency n)) :=
    summable_cauchyTailTerm (by norm_num) hy
  have hshift : Summable (fun j : ℕ ↦ sineMainTerm n (j + 1)) := by
    convert htail using 1
    funext j
    rw [show j + 1 = 1 + j by omega, sineMainTerm_shift]
    norm_num
  exact (summable_nat_add_iff 1).1 hshift

theorem sineMainTerm_nonneg
    {n : ℕ} (hn : n ≠ 0) (k : ℕ) : 0 ≤ sineMainTerm n k := by
  rw [sineMainTerm, cauchyTailTerm]
  exact div_nonneg (yoshidaScaledFrequency_pos hn).le
    (add_nonneg (sq_nonneg _) (sq_nonneg _))

theorem sineDyadicCorrection_nonneg
    {n : ℕ} (hn : n ≠ 0) (k : ℕ) :
    0 ≤ sineDyadicCorrection n k := by
  rw [sineDyadicCorrection]
  exact div_nonneg
    (mul_nonneg (sineMainTerm_nonneg hn k) (by positivity)) (by positivity)

theorem summable_sineDyadicCorrection
    {n : ℕ} (hn : n ≠ 0) : Summable (sineDyadicCorrection n) := by
  have hs := summable_sineMainTerm hn
  apply hs.of_nonneg_of_le (sineDyadicCorrection_nonneg hn)
  intro k
  rw [sineDyadicCorrection]
  have hsqrt : (Real.sqrt 2)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (by positivity)]
    exact Real.one_le_sqrt.mpr (by norm_num)
  have hpow : 1 ≤ (4 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have hfactor : (Real.sqrt 2)⁻¹ / (4 : ℝ) ^ k ≤ 1 := by
    calc
      (Real.sqrt 2)⁻¹ / (4 : ℝ) ^ k ≤ 1 / (4 : ℝ) ^ k := by gcongr
      _ ≤ 1 := by exact (div_le_one (by positivity)).2 hpow
  have hmain := sineMainTerm_nonneg hn k
  calc
    sineMainTerm n k * (Real.sqrt 2)⁻¹ / (4 : ℝ) ^ k =
        sineMainTerm n k * ((Real.sqrt 2)⁻¹ / (4 : ℝ) ^ k) := by ring
    _ ≤ sineMainTerm n k * 1 := mul_le_mul_of_nonneg_left hfactor hmain
    _ = sineMainTerm n k := by ring

theorem summable_sineCauchyTerm
    {n : ℕ} (hn : n ≠ 0) : Summable (sineCauchyTerm n) := by
  rw [show sineCauchyTerm n = fun k : ℕ ↦
      sineMainTerm n k - sineDyadicCorrection n k by
    funext k
    exact sineCauchyTerm_eq_main_sub_correction n k]
  exact (summable_sineMainTerm hn).sub (summable_sineDyadicCorrection hn)

private theorem inv_sqrt_two_le_one : (Real.sqrt 2)⁻¹ ≤ 1 := by
  rw [inv_le_one₀ (by positivity)]
  exact Real.one_le_sqrt.mpr (by norm_num)

private theorem sineDyadicCorrection_shift_le_geometric
    {n N : ℕ} (hn : n ≠ 0) (hN : 0 < N) (j : ℕ) :
    sineDyadicCorrection n (N + j) ≤
      (yoshidaScaledFrequency n / (4 : ℝ) ^ N) * (1 / 4 : ℝ) ^ j := by
  have hy : 0 ≤ yoshidaScaledFrequency n :=
    (yoshidaScaledFrequency_pos hn).le
  have hshift : (1 : ℝ) ≤ (N : ℝ) + 1 / 4 + j := by
    have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hjR : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  have hden : 1 ≤
      (((N : ℝ) + 1 / 4 + j) ^ 2 + yoshidaScaledFrequency n ^ 2) := by
    nlinarith [sq_nonneg (yoshidaScaledFrequency n),
      sq_nonneg ((N : ℝ) + 1 / 4 + j - 1)]
  have hmain : sineMainTerm n (N + j) ≤ yoshidaScaledFrequency n := by
    rw [sineMainTerm_shift, cauchyTailTerm]
    exact (div_le_iff₀ (by positivity :
      0 < (((N : ℝ) + 1 / 4 + j) ^ 2 + yoshidaScaledFrequency n ^ 2))).2
        (by nlinarith)
  rw [sineDyadicCorrection, pow_add]
  have hpowN : 0 < (4 : ℝ) ^ N := by positivity
  have hpowJ : 0 < (4 : ℝ) ^ j := by positivity
  have hcorr0 : 0 ≤ sineMainTerm n (N + j) := sineMainTerm_nonneg hn _
  have hsqrt0 : 0 ≤ (Real.sqrt 2)⁻¹ := by positivity
  rw [show (1 / 4 : ℝ) ^ j = ((4 : ℝ) ^ j)⁻¹ by
    rw [one_div, inv_pow]]
  rw [div_eq_mul_inv, div_eq_mul_inv]
  calc
    sineMainTerm n (N + j) * (Real.sqrt 2)⁻¹ *
          ((4 : ℝ) ^ N * (4 : ℝ) ^ j)⁻¹ =
        (sineMainTerm n (N + j) * (Real.sqrt 2)⁻¹ *
          ((4 : ℝ) ^ N)⁻¹) * ((4 : ℝ) ^ j)⁻¹ := by
            rw [mul_inv]
            ring
    _ ≤ (yoshidaScaledFrequency n * 1 * ((4 : ℝ) ^ N)⁻¹) *
          ((4 : ℝ) ^ j)⁻¹ := by
            gcongr
            exact inv_sqrt_two_le_one
    _ = yoshidaScaledFrequency n * ((4 : ℝ) ^ N)⁻¹ *
          ((4 : ℝ) ^ j)⁻¹ := by ring

/-- The dyadic correction after `N > 0` is bounded by a rational geometric
tail.  The factor `2` deliberately rounds `4/3` upward. -/
theorem sineDyadicCorrection_tail_le
    {n N : ℕ} (hn : n ≠ 0) (hN : 0 < N) :
    (∑' j : ℕ, sineDyadicCorrection n (N + j)) ≤
      2 * yoshidaScaledFrequency n / (4 : ℝ) ^ N := by
  let C : ℝ := yoshidaScaledFrequency n / (4 : ℝ) ^ N
  have hgeom : Summable (fun j : ℕ ↦ C * (1 / 4 : ℝ) ^ j) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 4 : ℝ)‖ < 1)).mul_left C
  have hcorr : Summable (fun j : ℕ ↦ sineDyadicCorrection n (N + j)) :=
    by
      simpa [Nat.add_comm] using
        (summable_nat_add_iff N).2 (summable_sineDyadicCorrection hn)
  have hle := hcorr.tsum_le_tsum
    (sineDyadicCorrection_shift_le_geometric hn hN) hgeom
  calc
    (∑' j : ℕ, sineDyadicCorrection n (N + j)) ≤
        ∑' j : ℕ, C * (1 / 4 : ℝ) ^ j := hle
    _ = C * ((1 - (1 / 4 : ℝ))⁻¹) := by
      rw [tsum_mul_left]
      rw [tsum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 4 : ℝ)‖ < 1)]
    _ ≤ 2 * yoshidaScaledFrequency n / (4 : ℝ) ^ N := by
      dsimp [C]
      have hy := (yoshidaScaledFrequency_pos hn).le
      field_simp
      nlinarith

/-- Two-sided bound for the tail of the actual explicit sine Cauchy series. -/
theorem sineCauchyTerm_tail_bounds
    {n N : ℕ} (hn : n ≠ 0) (hN : 0 < N) :
    let x : ℝ := N + 1 / 4
    let y : ℝ := yoshidaScaledFrequency n
    y / x - y ^ 3 / x ^ 3 - 2 * y / (4 : ℝ) ^ N ≤
        ∑' j : ℕ, sineCauchyTerm n (N + j) ∧
      (∑' j : ℕ, sineCauchyTerm n (N + j)) ≤
        y / x + y / x ^ 2 := by
  dsimp only
  let x : ℝ := N + 1 / 4
  let y : ℝ := yoshidaScaledFrequency n
  have hx : 1 ≤ x := by
    dsimp [x]
    have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hy : 0 ≤ y := by
    dsimp [y]
    exact (yoshidaScaledFrequency_pos hn).le
  have hmain := cauchyTail_tsum_bounds hx hy
  have hmainEq : (fun j : ℕ ↦ sineMainTerm n (N + j)) =
      cauchyTailTerm x y := by
    funext j
    simpa only [x, y] using sineMainTerm_shift n N j
  rw [← hmainEq] at hmain
  have hcorr := sineDyadicCorrection_tail_le hn hN
  have hmainSummable : Summable (fun j : ℕ ↦ sineMainTerm n (N + j)) :=
    by
      simpa [Nat.add_comm] using
        (summable_nat_add_iff N).2 (summable_sineMainTerm hn)
  have hcorrSummable : Summable
      (fun j : ℕ ↦ sineDyadicCorrection n (N + j)) :=
    by
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

/-- Split the exact moment into a kernel-computable finite head and the
certified tail above. -/
theorem yoshidaSineMoment_eq_finiteHead_sub_tail
    {n : ℕ} (hn : n ≠ 0) (N : ℕ) :
    yoshidaSineMoment n = sinePolarValue n -
      ((∑ k ∈ Finset.range N, sineCauchyTerm n k) +
        ∑' j : ℕ, sineCauchyTerm n (N + j)) := by
  rw [yoshidaSineMoment_eq_explicitCauchySeries hn]
  congr 1
  symm
  simpa [Nat.add_comm] using
    (summable_sineCauchyTerm hn).sum_add_tsum_nat_add N

end

end ArithmeticHodge.Analysis.YoshidaSineSeriesTail

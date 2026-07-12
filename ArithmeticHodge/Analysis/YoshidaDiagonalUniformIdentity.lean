import ArithmeticHodge.Analysis.DigammaTrapezoid
import ArithmeticHodge.Analysis.YoshidaDiagonalAcceleratedSeries

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaDiagonalUniformIdentity

noncomputable section

open DigammaTrapezoid
open YoshidaClippedMomentBridge
open YoshidaDiagonalAcceleratedSeries
open YoshidaDiagonalSeriesTail
open YoshidaOddGramPrefix

def yoshidaY (n : ℕ) : ℝ := yoshidaKappa n / 2

def diagonalHighProfile (y t : ℝ) : ℝ :=
  reciprocalRealPart y (t + 1 / 4)

def diagonalHighProfileDeriv (y t : ℝ) : ℝ :=
  reciprocalRealPartDeriv y (t + 1 / 4)

theorem two_mul_diagonalRampClosed_eq_profile_add_deriv
    {L y k : ℝ} (hL : L ≠ 0) (hy : y ≠ 0) :
    2 * diagonalRampClosed L ((2 * y) ^ 2) (2 * k + 1 / 2) 0 =
      diagonalHighProfile y k + diagonalHighProfileDeriv y k / (2 * L) := by
  unfold diagonalRampClosed diagonalHighProfile diagonalHighProfileDeriv
    reciprocalRealPart reciprocalRealPartDeriv
  field_simp [hL, hy]
  ring

def diagonalHighDerivativeTerm (n j : ℕ) : ℝ :=
  diagonalHighProfileDeriv (yoshidaY n) (j + 1)

def diagonalHighQTerm (n j : ℕ) : ℝ :=
  let k : ℝ := j + 1
  2 * ((Real.sqrt 2)⁻¹ / (4 : ℝ) ^ (j + 1)) *
    (((2 * k + 1 / 2) ^ 2 - yoshidaKappa n ^ 2) /
      (yoshidaLength *
        ((2 * k + 1 / 2) ^ 2 + yoshidaKappa n ^ 2) ^ 2))

def diagonalHighQ (n : ℕ) : ℝ :=
  ∑' j : ℕ, diagonalHighQTerm n j

private def diagonalHighProfileCorrectionTerm (n j : ℕ) : ℝ :=
  diagonalHighProfile (yoshidaY n) (j + 1) - 1 / (j + 1 : ℕ)

private def diagonalHighLogTerm (j : ℕ) : ℝ :=
  (1 / 4 : ℝ) ^ (j + 1) / (j + 1 : ℕ)

private def diagonalHighZetaTwoTerm (j : ℕ) : ℝ :=
  1 / (((j + 1 : ℕ) : ℝ) ^ 2)

private theorem two_mul_diagonalRampClosed_endpoint_split
    (L p a q : ℝ) :
    2 * diagonalRampClosed L p a q =
      2 * diagonalRampClosed L p a 0 +
        2 * q * (a ^ 2 - p) / (L * (a ^ 2 + p) ^ 2) := by
  unfold diagonalRampClosed
  ring

private theorem diagonalAcceleratedCorrection_eq_uniformTerms
    {n : ℕ} (hn : n ≠ 0) (j : ℕ) :
    diagonalAcceleratedCorrection n j =
      diagonalHighProfileCorrectionTerm n j +
        diagonalHighDerivativeTerm n j / (2 * yoshidaLength) +
        diagonalHighQTerm n j + diagonalHighLogTerm j +
        diagonalAccelerationCoefficient * diagonalHighZetaTwoTerm j := by
  have hy : yoshidaY n ≠ 0 := by
    exact div_ne_zero
      (YoshidaOddCorrelationIntegrability.yoshidaKappa_ne_zero hn)
      (by norm_num)
  have hzero := two_mul_diagonalRampClosed_eq_profile_add_deriv
    yoshidaLength_pos.ne' hy
    (L := yoshidaLength) (y := yoshidaY n)
    (k := ((j + 1 : ℕ) : ℝ))
  have hkappa : (2 * yoshidaY n) ^ 2 = yoshidaKappa n ^ 2 := by
    unfold yoshidaY
    ring
  rw [hkappa] at hzero
  unfold diagonalAcceleratedCorrection yoshidaDiagonalDyadicPairedCorrection
    diagonalDyadicPairedCorrection diagonalPairedCorrection
  rw [two_mul_diagonalRampClosed_endpoint_split, hzero]
  unfold diagonalHighProfileCorrectionTerm diagonalHighDerivativeTerm
    diagonalHighQTerm diagonalHighLogTerm diagonalHighZetaTwoTerm
    diagonalAccelerationCoefficient
  dsimp only
  push_cast
  rw [one_div_pow]
  ring

private theorem diagonalHighProfileCorrectionTerm_eq_neg_quarter
    (n j : ℕ) :
    diagonalHighProfileCorrectionTerm n j =
      -quarterDigammaSeriesTerm (yoshidaKappa n) j := by
  unfold diagonalHighProfileCorrectionTerm diagonalHighProfile
    quarterDigammaSeriesTerm shiftedReciprocalRealPart yoshidaY
  push_cast
  ring_nf

private theorem summable_diagonalHighProfileCorrectionTerm (n : ℕ) :
    Summable (diagonalHighProfileCorrectionTerm n) := by
  exact (summable_quarterDigammaSeriesTerm (yoshidaKappa n)).neg.congr
    (fun j ↦ (diagonalHighProfileCorrectionTerm_eq_neg_quarter n j).symm)

theorem diagonalHighProfileDeriv_abs_le (y : ℝ) (j : ℕ) :
    |diagonalHighProfileDeriv y (j + 1)| ≤
      1 / ((((j + 1 : ℕ) : ℝ) ^ 2)) := by
  let k : ℝ := ((j + 1 : ℕ) : ℝ)
  let u : ℝ := k + 1 / 4
  have hk : 0 < k := by
    dsimp [k]
    positivity
  have hu : 0 < u := by
    dsimp [u]
    positivity
  have hku : k ^ 2 ≤ u ^ 2 := by
    have hle : k ≤ u := by
      dsimp [u]
      norm_num
    nlinarith
  have hd : 0 < u ^ 2 + y ^ 2 := by
    nlinarith [sq_pos_of_pos hu, sq_nonneg y]
  have hnum : |y ^ 2 - u ^ 2| ≤ u ^ 2 + y ^ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg y, sq_nonneg u]
  unfold diagonalHighProfileDeriv reciprocalRealPartDeriv
  push_cast
  have hbound :
      |(y ^ 2 - u ^ 2) / (u ^ 2 + y ^ 2) ^ 2| ≤ 1 / k ^ 2 := by
    rw [abs_div, abs_pow, abs_of_pos hd]
    calc
      |y ^ 2 - u ^ 2| / (u ^ 2 + y ^ 2) ^ 2 ≤
          (u ^ 2 + y ^ 2) / (u ^ 2 + y ^ 2) ^ 2 :=
        div_le_div_of_nonneg_right hnum (sq_nonneg _)
      _ = 1 / (u ^ 2 + y ^ 2) := by
        field_simp [hd.ne']
      _ ≤ 1 / k ^ 2 := by
        apply one_div_le_one_div_of_le (sq_pos_of_pos hk)
        nlinarith [sq_nonneg y]
  simpa only [u, k, Nat.cast_add, Nat.cast_one] using hbound

theorem summable_diagonalHighDerivativeTerm (n : ℕ) :
    Summable (diagonalHighDerivativeTerm n) := by
  have hmajor : Summable (fun j : ℕ ↦
      1 / ((((j + 1 : ℕ) : ℝ) ^ 2))) := by
    have h := Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).2 h
  apply hmajor.of_norm_bounded
  intro j
  rw [Real.norm_eq_abs]
  exact diagonalHighProfileDeriv_abs_le (yoshidaY n) j

private theorem hasSum_diagonalHighLogTerm :
    HasSum diagonalHighLogTerm (Real.log (4 / 3)) := by
  have h := Real.hasSum_pow_div_log_of_abs_lt_one
    (x := (1 / 4 : ℝ)) (by norm_num)
  have hfun : diagonalHighLogTerm =
      fun j : ℕ ↦ (1 / 4 : ℝ) ^ (j + 1) / (j + 1) := by
    funext j
    unfold diagonalHighLogTerm
    push_cast
    ring
  have hlog : -Real.log (3 / 4) = Real.log (4 / 3) := by
    rw [show (4 / 3 : ℝ) = (3 / 4 : ℝ)⁻¹ by norm_num,
      Real.log_inv]
  rw [hfun, ← hlog]
  convert h using 1
  all_goals norm_num

private theorem hasSum_diagonalHighZetaTwoTerm :
    HasSum diagonalHighZetaTwoTerm (Real.pi ^ 2 / 6) := by
  have h := (hasSum_nat_add_iff' 1).2 hasSum_zeta_two
  convert h using 1
  all_goals norm_num [diagonalHighZetaTwoTerm, Nat.add_comm]

private theorem summable_diagonalHighQTerm
    {n : ℕ} (hn : n ≠ 0) :
    Summable (diagonalHighQTerm n) := by
  have hcorr := summable_diagonalAcceleratedCorrection hn
  have hprofile := summable_diagonalHighProfileCorrectionTerm n
  have hderiv :=
    (summable_diagonalHighDerivativeTerm n).div_const (2 * yoshidaLength)
  have hlog := hasSum_diagonalHighLogTerm.summable
  have hzeta := hasSum_diagonalHighZetaTwoTerm.summable.mul_left
    diagonalAccelerationCoefficient
  have hrest := (((hcorr.sub hprofile).sub hderiv).sub hlog).sub hzeta
  apply hrest.congr
  intro j
  rw [diagonalAcceleratedCorrection_eq_uniformTerms hn j]
  ring

private theorem tsum_diagonalHighProfileCorrectionTerm_eq (n : ℕ) :
    (∑' j : ℕ, diagonalHighProfileCorrectionTerm n j) =
      -(Complex.digamma
          ((1 / 4 : ℝ) + yoshidaY n * Complex.I)).re -
        Real.eulerMascheroniConstant -
        diagonalHighProfile (yoshidaY n) 0 := by
  have hdig := digamma_quarter_vertical_re_eq_trapezoid_series
    (yoshidaKappa n)
  have htsum :
      (∑' j : ℕ, quarterDigammaSeriesTerm (yoshidaKappa n) j) =
        -(∑' j : ℕ, diagonalHighProfileCorrectionTerm n j) := by
    rw [← tsum_neg]
    apply tsum_congr
    intro j
    rw [diagonalHighProfileCorrectionTerm_eq_neg_quarter]
    ring
  rw [htsum] at hdig
  have hdig' :
      (Complex.digamma
          ((1 / 4 : ℝ) + yoshidaY n * Complex.I)).re =
        -Real.eulerMascheroniConstant -
          diagonalHighProfile (yoshidaY n) 0 -
          (∑' j : ℕ, diagonalHighProfileCorrectionTerm n j) := by
    simpa [yoshidaY, diagonalHighProfile, shiftedReciprocalRealPart,
      add_comm, add_left_comm, add_assoc] using hdig
  linarith

theorem yoshidaDiagonalMoment_eq_uniformSeries
    {n : ℕ} (hn : n ≠ 0) :
    yoshidaDiagonalMoment n =
      (Complex.digamma ((1 / 4 : ℝ) + yoshidaY n * Complex.I)).re -
        Real.log Real.pi +
        2 * diagonalRampClosed yoshidaLength (yoshidaKappa n ^ 2)
          (-1 / 2) (Real.sqrt 2) +
        diagonalHighProfile (yoshidaY n) 0 -
        (∑' j : ℕ, diagonalHighDerivativeTerm n j) /
          (2 * yoshidaLength) -
        diagonalHighQ n := by
  have hprofile : HasSum (diagonalHighProfileCorrectionTerm n)
      (-(Complex.digamma
          ((1 / 4 : ℝ) + yoshidaY n * Complex.I)).re -
        Real.eulerMascheroniConstant -
        diagonalHighProfile (yoshidaY n) 0) := by
    rw [← tsum_diagonalHighProfileCorrectionTerm_eq n]
    exact (summable_diagonalHighProfileCorrectionTerm n).hasSum
  have hderiv : HasSum
      (fun j : ℕ ↦ diagonalHighDerivativeTerm n j /
        (2 * yoshidaLength))
      ((∑' j : ℕ, diagonalHighDerivativeTerm n j) /
        (2 * yoshidaLength)) :=
    (summable_diagonalHighDerivativeTerm n).hasSum.div_const _
  have hq : HasSum (diagonalHighQTerm n) (diagonalHighQ n) := by
    unfold diagonalHighQ
    exact (summable_diagonalHighQTerm hn).hasSum
  have hzeta := hasSum_diagonalHighZetaTwoTerm.mul_left
    diagonalAccelerationCoefficient
  have htotal := (((hprofile.add hderiv).add hq).add
    hasSum_diagonalHighLogTerm).add hzeta
  let total : ℝ :=
      ((((-(Complex.digamma
          ((1 / 4 : ℝ) + yoshidaY n * Complex.I)).re -
        Real.eulerMascheroniConstant -
        diagonalHighProfile (yoshidaY n) 0) +
        (∑' j : ℕ, diagonalHighDerivativeTerm n j) /
          (2 * yoshidaLength)) + diagonalHighQ n) +
        Real.log (4 / 3)) +
        diagonalAccelerationCoefficient * (Real.pi ^ 2 / 6)
  have hcorr : HasSum (diagonalAcceleratedCorrection n) total := by
    dsimp only [total]
    convert htotal using 1
    funext j
    exact diagonalAcceleratedCorrection_eq_uniformTerms hn j
  rw [yoshidaDiagonalMoment_eq_acceleratedSeries hn]
  rw [show (∑' j : ℕ,
      yoshidaDiagonalDyadicPairedCorrection n (j + 1)) = total by
    simpa only [diagonalAcceleratedCorrection] using hcorr.tsum_eq]
  dsimp only [total]
  unfold diagonalAcceleratedBase diagonalAccelerationCoefficient
  ring

end

end ArithmeticHodge.Analysis.YoshidaDiagonalUniformIdentity

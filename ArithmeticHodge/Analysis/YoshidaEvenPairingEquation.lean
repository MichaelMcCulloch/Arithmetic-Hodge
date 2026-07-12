import ArithmeticHodge.Analysis.YoshidaEvenCriticalCrossBridge
import ArithmeticHodge.Analysis.YoshidaEvenDigammaImagRemainder
import ArithmeticHodge.Analysis.YoshidaSineSeriesTail

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaEvenPairingEquation

noncomputable section

open Complex Real
open scoped BigOperators

open YoshidaClippedEvenMomentBridge
open YoshidaEvenCriticalCrossBridge
open YoshidaEvenCouplingReduction
open YoshidaEvenDigammaImagRemainder
open YoshidaEvenDistributionReduction
open YoshidaEvenIntervalCertificate
open YoshidaEvenPairingBridge
open YoshidaMomentSeries
open YoshidaOddGramPrefix
open YoshidaRenormalizedGeometricKernel
open YoshidaSineSeriesTail
open YoshidaWeightedTailBounds

private theorem yoshidaLength_eq_two_mul_a :
    yoshidaLength = 2 * yoshidaA := by
  rw [yoshidaLength, yoshidaA]
  ring

private theorem yoshidaHalfLength_eq_a :
    yoshidaHalfLength = yoshidaA := by
  rfl

private theorem yoshidaKappa_eq (n : ℕ) :
    yoshidaKappa n = Real.pi * (n : ℝ) / yoshidaA := by
  rw [yoshidaKappa, yoshidaLength_eq_two_mul_a]
  ring

private theorem oddRate_eq_halfOdd (k : ℕ) :
    oddRate k = halfOdd k := by
  rw [oddRate, halfOdd]

private theorem exp_a_eq_sqrt_two :
    Real.exp yoshidaA = Real.sqrt 2 := by
  rw [← exp_yoshidaLength_half]
  congr 1

private theorem exp_neg_a_eq_inv_sqrt_two :
    Real.exp (-yoshidaA) = (Real.sqrt 2)⁻¹ := by
  rw [Real.exp_neg, exp_a_eq_sqrt_two]

private theorem polarGap_sq :
    (Real.exp (yoshidaA / 2) - Real.exp (-yoshidaA / 2)) ^ 2 =
      Real.sqrt 2 + (Real.sqrt 2)⁻¹ - 2 := by
  have hposSq : Real.exp (yoshidaA / 2) ^ 2 = Real.exp yoshidaA := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hnegSq : Real.exp (-yoshidaA / 2) ^ 2 = Real.exp (-yoshidaA) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hprod :
      Real.exp (yoshidaA / 2) * Real.exp (-yoshidaA / 2) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    ring
  calc
    (Real.exp (yoshidaA / 2) - Real.exp (-yoshidaA / 2)) ^ 2 =
        Real.exp (yoshidaA / 2) ^ 2 +
          Real.exp (-yoshidaA / 2) ^ 2 -
            2 * (Real.exp (yoshidaA / 2) *
              Real.exp (-yoshidaA / 2)) := by ring
    _ = Real.sqrt 2 + (Real.sqrt 2)⁻¹ - 2 := by
      rw [hposSq, hnegSq, hprod, exp_a_eq_sqrt_two,
        exp_neg_a_eq_inv_sqrt_two]
      ring

private theorem sinePolarValue_eq (n : ℕ) :
    sinePolarValue n =
      -(2 * yoshidaKappa n *
        (Real.exp (yoshidaA / 2) - Real.exp (-yoshidaA / 2)) ^ 2 /
          ((1 / 2 : ℝ) ^ 2 + yoshidaKappa n ^ 2)) := by
  rw [sinePolarValue, polarGap_sq]
  ring

private theorem sineMainTerm_eq_evenDigammaCauchyTerm (n k : ℕ) :
    sineMainTerm n k = evenDigammaCauchyTerm n k := by
  rw [sineMainTerm, YoshidaCauchyTailBounds.cauchyTailTerm,
    yoshidaScaledFrequency, evenDigammaCauchyTerm, evenDigammaY,
    yoshidaKappa_eq]
  ring

private theorem sineDyadicCorrection_eq (n k : ℕ) :
    sineDyadicCorrection n k =
      2 * yoshidaKappa n *
          Real.exp (-2 * yoshidaA * halfOdd k) /
        (halfOdd k ^ 2 + yoshidaKappa n ^ 2) := by
  rw [sineDyadicCorrection, sineMainTerm,
    YoshidaCauchyTailBounds.cauchyTailTerm, yoshidaScaledFrequency]
  have hexp := exp_neg_oddRate_mul_length k
  rw [yoshidaLength_eq_two_mul_a, oddRate_eq_halfOdd] at hexp
  have hexp' :
      (Real.sqrt 2)⁻¹ / (4 : ℝ) ^ k =
        Real.exp (-2 * yoshidaA * halfOdd k) := by
    rw [← hexp]
    congr 1
    ring
  rw [show
      yoshidaKappa n / 2 /
            ((1 / 4 + (k : ℝ)) ^ 2 + (yoshidaKappa n / 2) ^ 2) *
          (Real.sqrt 2)⁻¹ / (4 : ℝ) ^ k =
        yoshidaKappa n / 2 /
            ((1 / 4 + (k : ℝ)) ^ 2 + (yoshidaKappa n / 2) ^ 2) *
          ((Real.sqrt 2)⁻¹ / (4 : ℝ) ^ k) by ring,
    hexp']
  have hdenMain :
      (1 / 4 + (k : ℝ)) ^ 2 + (yoshidaKappa n / 2) ^ 2 ≠ 0 := by
    positivity
  have hdenOut : halfOdd k ^ 2 + yoshidaKappa n ^ 2 ≠ 0 := by
    unfold halfOdd
    positivity
  field_simp [hdenMain, hdenOut]
  rw [halfOdd]
  ring

private theorem yoshidaSineMoment_eq_polar_sub_digamma_add_dyadic
    {n : ℕ} (hn : n ≠ 0) :
    yoshidaSineMoment n = sinePolarValue n - yoshidaEvenDigammaImag n +
      ∑' k : ℕ, sineDyadicCorrection n k := by
  rw [yoshidaSineMoment_eq_explicitCauchySeries hn]
  have hmain : Summable (sineMainTerm n) := summable_sineMainTerm hn
  have hcorr : Summable (sineDyadicCorrection n) :=
    summable_sineDyadicCorrection hn
  rw [show (∑' k : ℕ, sineCauchyTerm n k) =
      (∑' k : ℕ, sineMainTerm n k) -
        ∑' k : ℕ, sineDyadicCorrection n k by
    rw [← hmain.tsum_sub hcorr]
    apply tsum_congr
    exact sineCauchyTerm_eq_main_sub_correction n]
  rw [show (∑' k : ℕ, sineMainTerm n k) =
      yoshidaEvenDigammaImag n by
    rw [yoshidaEvenDigammaImag_eq_tsum]
    apply tsum_congr
    exact sineMainTerm_eq_evenDigammaCauchyTerm n]
  ring

private theorem polar_dividedDifference_eq_firstKernel
    {n m : ℕ} (hnm : n < m) :
    ((m : ℝ) * sinePolarValue m - (n : ℝ) * sinePolarValue n) /
        (Real.pi * ((n : ℝ) ^ 2 - (m : ℝ) ^ 2)) =
      (Real.exp (yoshidaA / 2) - Real.exp (-yoshidaA / 2)) ^ 2 *
        evenFirstKernel yoshidaA n m := by
  have ha : yoshidaA ≠ 0 := YoshidaCoercivityNumerics.yoshidaA_pos.ne'
  have hnR : (n : ℝ) < (m : ℝ) := by exact_mod_cast hnm
  have hdiff : (n : ℝ) ^ 2 - (m : ℝ) ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg ((n : ℝ) + m)]
  rw [sinePolarValue_eq, sinePolarValue_eq]
  unfold evenFirstKernel doubledDenominator
  rw [yoshidaKappa_eq, yoshidaKappa_eq]
  field_simp [ha, Real.pi_ne_zero, hdiff]
  ring

private theorem polar_zero_eq_firstKernel {m : ℕ} (hm : m ≠ 0) :
    -sinePolarValue m / (Real.pi * (m : ℝ)) =
      (Real.exp (yoshidaA / 2) - Real.exp (-yoshidaA / 2)) ^ 2 *
        evenFirstKernel yoshidaA 0 m := by
  have ha : yoshidaA ≠ 0 := YoshidaCoercivityNumerics.yoshidaA_pos.ne'
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  rw [sinePolarValue_eq]
  unfold evenFirstKernel doubledDenominator
  rw [yoshidaKappa_eq]
  norm_num
  field_simp [ha, hmR, Real.pi_ne_zero]
  ring

private theorem digamma_dividedDifference_eq_combination
    (y : ℕ → ℝ) {n m : ℕ} (hn : n ≠ 0) (hnm : n < m) :
    ((n : ℝ) * y n - (m : ℝ) * y m) /
        (Real.pi * ((n : ℝ) ^ 2 - (m : ℝ) ^ 2)) =
      evenDigammaCombination y n m := by
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hnmlt : (n : ℝ) < (m : ℝ) := by exact_mod_cast hnm
  have hdiff : (n : ℝ) - (m : ℝ) ≠ 0 := sub_ne_zero.mpr hnmlt.ne
  have hsum : (n : ℝ) + (m : ℝ) ≠ 0 := by positivity
  have hsqdiff : (n : ℝ) ^ 2 - (m : ℝ) ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg ((n : ℝ) + m)]
  unfold evenDigammaCombination
  field_simp [Real.pi_ne_zero, hdiff, hsum, hsqdiff]
  ring

private theorem yoshidaEvenDigammaImag_zero :
    yoshidaEvenDigammaImag 0 = 0 := by
  rw [yoshidaEvenDigammaImag_eq_tsum]
  simp [evenDigammaCauchyTerm, evenDigammaY]

private theorem digamma_zero_eq_combination {m : ℕ} (hm : m ≠ 0) :
    yoshidaEvenDigammaImag m / (Real.pi * (m : ℝ)) =
      evenDigammaCombination yoshidaEvenDigammaImag 0 m := by
  symm
  exact evenDigammaCombination_zero yoshidaEvenDigammaImag
    (Nat.pos_of_ne_zero hm) yoshidaEvenDigammaImag_zero

private theorem dyadic_dividedDifference_term_eq_geometric
    {n m : ℕ} (hnm : n < m) (k : ℕ) :
    ((m : ℝ) * sineDyadicCorrection m k -
        (n : ℝ) * sineDyadicCorrection n k) /
        (Real.pi * ((n : ℝ) ^ 2 - (m : ℝ) ^ 2)) =
      -(2 / yoshidaA) * evenGeometricTerm yoshidaA n m k := by
  have ha : yoshidaA ≠ 0 := YoshidaCoercivityNumerics.yoshidaA_pos.ne'
  have hnR : (n : ℝ) < (m : ℝ) := by exact_mod_cast hnm
  have hdiff : (n : ℝ) ^ 2 - (m : ℝ) ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg ((n : ℝ) + m)]
  have hq : 0 < halfOdd k := by unfold halfOdd; positivity
  rw [sineDyadicCorrection_eq, sineDyadicCorrection_eq]
  unfold evenGeometricTerm archDenominator
  rw [yoshidaKappa_eq, yoshidaKappa_eq]
  field_simp [ha, Real.pi_ne_zero, hdiff, hq.ne']
  ring

private theorem dyadic_zero_term_eq_geometric
    {m : ℕ} (hm : m ≠ 0) (k : ℕ) :
    sineDyadicCorrection m k / (Real.pi * (m : ℝ)) =
      (2 / yoshidaA) * evenGeometricTerm yoshidaA 0 m k := by
  have ha : yoshidaA ≠ 0 := YoshidaCoercivityNumerics.yoshidaA_pos.ne'
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hq : 0 < halfOdd k := by unfold halfOdd; positivity
  rw [sineDyadicCorrection_eq]
  unfold evenGeometricTerm archDenominator
  rw [yoshidaKappa_eq]
  norm_num
  field_simp [ha, hmR, Real.pi_ne_zero, hq.ne']

private theorem dyadic_dividedDifference_eq_geometricKernel
    {n m : ℕ} (hn : n ≠ 0) (hnm : n < m) :
    ((m : ℝ) * (∑' k : ℕ, sineDyadicCorrection m k) -
        (n : ℝ) * (∑' k : ℕ, sineDyadicCorrection n k)) /
        (Real.pi * ((n : ℝ) ^ 2 - (m : ℝ) ^ 2)) =
      -evenGeometricKernel yoshidaA n m := by
  have hm : m ≠ 0 := by omega
  have hM : Summable (fun k : ℕ ↦
      (m : ℝ) * sineDyadicCorrection m k) :=
    (summable_sineDyadicCorrection hm).mul_left (m : ℝ)
  have hN : Summable (fun k : ℕ ↦
      (n : ℝ) * sineDyadicCorrection n k) :=
    (summable_sineDyadicCorrection hn).mul_left (n : ℝ)
  calc
    ((m : ℝ) * (∑' k : ℕ, sineDyadicCorrection m k) -
          (n : ℝ) * (∑' k : ℕ, sineDyadicCorrection n k)) /
          (Real.pi * ((n : ℝ) ^ 2 - (m : ℝ) ^ 2)) =
        (∑' k : ℕ,
          ((m : ℝ) * sineDyadicCorrection m k -
            (n : ℝ) * sineDyadicCorrection n k)) /
          (Real.pi * ((n : ℝ) ^ 2 - (m : ℝ) ^ 2)) := by
      rw [hM.tsum_sub hN, tsum_mul_left, tsum_mul_left]
    _ = ∑' k : ℕ,
        (((m : ℝ) * sineDyadicCorrection m k -
            (n : ℝ) * sineDyadicCorrection n k) /
          (Real.pi * ((n : ℝ) ^ 2 - (m : ℝ) ^ 2))) := by
      rw [tsum_div_const]
    _ = ∑' k : ℕ,
        (-(2 / yoshidaA) * evenGeometricTerm yoshidaA n m k) := by
      apply tsum_congr
      exact dyadic_dividedDifference_term_eq_geometric hnm
    _ = -(2 / yoshidaA) *
        (∑' k : ℕ, evenGeometricTerm yoshidaA n m k) := by
      rw [tsum_mul_left]
    _ = -evenGeometricKernel yoshidaA n m := by
      unfold evenGeometricKernel
      ring

private theorem dyadic_zero_eq_geometricKernel
    {m : ℕ} (hm : m ≠ 0) :
    (∑' k : ℕ, sineDyadicCorrection m k) /
        (Real.pi * (m : ℝ)) = evenGeometricKernel yoshidaA 0 m := by
  calc
    (∑' k : ℕ, sineDyadicCorrection m k) /
          (Real.pi * (m : ℝ)) =
        ∑' k : ℕ,
          sineDyadicCorrection m k / (Real.pi * (m : ℝ)) := by
      rw [tsum_div_const]
    _ = ∑' k : ℕ,
        (2 / yoshidaA) * evenGeometricTerm yoshidaA 0 m k := by
      apply tsum_congr
      exact dyadic_zero_term_eq_geometric hm
    _ = (2 / yoshidaA) *
        (∑' k : ℕ, evenGeometricTerm yoshidaA 0 m k) := by
      rw [tsum_mul_left]
    _ = evenGeometricKernel yoshidaA 0 m := by
      rfl

private theorem evenMomentGram_positive_offdiag_eq_625
    {n m : ℕ} (hn : n ≠ 0) (hnm : n < m) :
    evenMomentGram yoshidaSineMoment yoshidaDiagonalMoment n m =
      (-1 : ℝ) ^ (n + m) *
        even625BaseRhs yoshidaA yoshidaEvenDigammaImag n m := by
  have hm : m ≠ 0 := by omega
  have hne : n ≠ m := Nat.ne_of_lt hnm
  have hmoment :
      ((m : ℝ) * yoshidaSineMoment m -
          (n : ℝ) * yoshidaSineMoment n) /
          (Real.pi * ((n : ℝ) ^ 2 - (m : ℝ) ^ 2)) =
        even625BaseRhs yoshidaA yoshidaEvenDigammaImag n m := by
    rw [yoshidaSineMoment_eq_polar_sub_digamma_add_dyadic hm,
      yoshidaSineMoment_eq_polar_sub_digamma_add_dyadic hn]
    rw [show
      ((m : ℝ) *
            (sinePolarValue m - yoshidaEvenDigammaImag m +
              ∑' k : ℕ, sineDyadicCorrection m k) -
          (n : ℝ) *
            (sinePolarValue n - yoshidaEvenDigammaImag n +
              ∑' k : ℕ, sineDyadicCorrection n k)) /
          (Real.pi * ((n : ℝ) ^ 2 - (m : ℝ) ^ 2)) =
        (((m : ℝ) * sinePolarValue m -
            (n : ℝ) * sinePolarValue n) /
          (Real.pi * ((n : ℝ) ^ 2 - (m : ℝ) ^ 2))) +
        (((n : ℝ) * yoshidaEvenDigammaImag n -
            (m : ℝ) * yoshidaEvenDigammaImag m) /
          (Real.pi * ((n : ℝ) ^ 2 - (m : ℝ) ^ 2))) +
        (((m : ℝ) * (∑' k : ℕ, sineDyadicCorrection m k) -
            (n : ℝ) * (∑' k : ℕ, sineDyadicCorrection n k)) /
          (Real.pi * ((n : ℝ) ^ 2 - (m : ℝ) ^ 2))) by ring]
    rw [polar_dividedDifference_eq_firstKernel hnm,
      digamma_dividedDifference_eq_combination
        yoshidaEvenDigammaImag hn hnm,
      dyadic_dividedDifference_eq_geometricKernel hn hnm]
    unfold even625BaseRhs
    ring
  rw [evenMomentGram_offDiagonal _ _ n m hn hm hne,
    coe_evenOffDiagonalCoeffQ]
  have hnR : (n : ℝ) < (m : ℝ) := by exact_mod_cast hnm
  have hdiff : (n : ℝ) ^ 2 - (m : ℝ) ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg ((n : ℝ) + m)]
  rw [show
      ((-1 : ℝ) ^ (n + m) /
          ((n : ℝ) ^ 2 - (m : ℝ) ^ 2)) * Real.pi⁻¹ *
          ((m : ℝ) * yoshidaSineMoment m -
            (n : ℝ) * yoshidaSineMoment n) =
        (-1 : ℝ) ^ (n + m) *
          (((m : ℝ) * yoshidaSineMoment m -
              (n : ℝ) * yoshidaSineMoment n) /
            (Real.pi * ((n : ℝ) ^ 2 - (m : ℝ) ^ 2))) by
              field_simp [Real.pi_ne_zero, hdiff],
    hmoment]

private theorem even625BaseRhs_zero_eq
    {m : ℕ} (hm : m ≠ 0) :
    even625BaseRhs yoshidaA yoshidaEvenDigammaImag 0 m =
      -yoshidaSineMoment m / (Real.pi * (m : ℝ)) := by
  rw [yoshidaSineMoment_eq_polar_sub_digamma_add_dyadic hm]
  rw [show
      -(sinePolarValue m - yoshidaEvenDigammaImag m +
          ∑' k : ℕ, sineDyadicCorrection m k) /
          (Real.pi * (m : ℝ)) =
        -sinePolarValue m / (Real.pi * (m : ℝ)) +
          yoshidaEvenDigammaImag m / (Real.pi * (m : ℝ)) -
          (∑' k : ℕ, sineDyadicCorrection m k) /
            (Real.pi * (m : ℝ)) by ring]
  rw [polar_zero_eq_firstKernel hm, digamma_zero_eq_combination hm,
    dyadic_zero_eq_geometricKernel hm]
  unfold even625BaseRhs
  ring

private theorem evenMomentGram_zero_positive_eq_625
    {m : ℕ} (hm : m ≠ 0) :
    evenMomentGram yoshidaSineMoment yoshidaDiagonalMoment 0 m =
      (-1 : ℝ) ^ m * (Real.sqrt 2)⁻¹ *
        even625BaseRhs yoshidaA yoshidaEvenDigammaImag 0 m := by
  rw [evenMomentGram_zero_nonzero _ _ m hm, coe_evenZeroCoeffQ,
    even625BaseRhs_zero_eq hm]
  rw [pow_succ]
  ring

private theorem evenLowPairingFormula_eq_evenMomentGram
    (i : YoshidaEvenIndex) (k : ℕ) :
    yoshidaClippedEvenLowModePairingFormula yoshidaA i (200 + k) =
      (evenMomentGram yoshidaSineMoment yoshidaDiagonalMoment
        i.1 (200 + k) : ℂ) := by
  have hm : 200 + k ≠ 0 := by omega
  calc
    yoshidaClippedEvenLowModePairingFormula yoshidaA i (200 + k) =
        yoshidaClippedLocalCriticalPairing yoshidaHalfLength
          yoshidaHalfLength_pos
          (yoshidaClippedEvenLowMode yoshidaHalfLength i)
          (yoshidaClippedEvenMode yoshidaHalfLength (200 + k)) := by
      simpa only [yoshidaHalfLength_eq_a] using
        (yoshidaClippedLocalCriticalPairing_evenLowMode_tail_eq_formula
          (a := yoshidaHalfLength) yoshidaHalfLength_pos i k).symm
    _ = yoshidaClippedLocalCriticalPairing yoshidaHalfLength
          yoshidaHalfLength_pos
          (clippedEvenUnifiedMode i.1)
          (clippedEvenUnifiedMode (200 + k)) := by
      rw [clippedEvenUnifiedMode_eq_lowMode]
      rw [clippedEvenUnifiedMode, if_neg hm]
    _ = (clippedEvenAdmissibleRealSpaceGram i.1 (200 + k) : ℂ) :=
      yoshidaClippedLocalCriticalPairing_even_eq_admissible
        clippedEvenCriticalCrossDistributionBridge i.1 (200 + k)
    _ = (evenMomentGram yoshidaSineMoment yoshidaDiagonalMoment
          i.1 (200 + k) : ℂ) := by
      rw [clippedEvenAdmissibleRealSpaceGram_eq_evenMomentGram]

/-- The actual removable-safe clipped pairing satisfies Yoshida's normalized
equation (6.25) on every canonical even low/high pair. -/
theorem actualEvenPairingEquation6_25 : ActualEvenPairingEquation6_25 := by
  intro i k
  rw [evenLowPairingFormula_eq_evenMomentGram]
  norm_cast
  push_cast
  by_cases hi : i.1 = 0
  · rw [hi]
    unfold normalizedEven625Rhs even625Normalization
    rw [if_pos rfl]
    simpa only [zero_add, mul_assoc] using
      (evenMomentGram_zero_positive_eq_625 (by omega : 200 + k ≠ 0))
  · have hlt : i.1 < 200 + k := by omega
    unfold normalizedEven625Rhs even625Normalization
    rw [if_neg hi, one_mul]
    exact evenMomentGram_positive_offdiag_eq_625 hi hlt


end


end ArithmeticHodge.Analysis.YoshidaEvenPairingEquation

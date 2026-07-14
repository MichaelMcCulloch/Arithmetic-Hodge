import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteLowMatrix
import ArithmeticHodge.Analysis.YoshidaClippedMomentBridge

set_option autoImplicit false
set_option maxRecDepth 100000

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteOddPerturbationFormula

noncomputable section

open ArithmeticHodge.Analysis
open YoshidaClippedMomentBridge
open YoshidaCoercivityNumerics
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointScaledCorrelation
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoEndpointParityPencil
open YoshidaFactorTwoPhaseConcreteLowMatrix
open YoshidaFactorTwoPhaseEnvelope
open YoshidaWeightedTailBounds

/-!
# Exact canonical odd perturbation entries

This file pulls the ordered centered correlation of two canonical odd modes
back to the physical clipped interval.  The existing diagonal and
off-diagonal clipped-sine formulas then give one explicit correlation kernel
whose weighted integral and two retained prime atoms are exactly the entries
of the concrete odd perturbation matrix.
-/

/-- Pulling two canonical odd modes from `[-yoshidaA,yoshidaA]` to `[-1,1]`
divides their ordered clipped correlation by `yoshidaA`. -/
theorem factorTwoCenteredCrossCorrelation_oddLow_eq_clipped
    (i j : YoshidaOddIndex) {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
    factorTwoCenteredCrossCorrelation
        (factorTwoCenteredOddLowProfile i)
        (factorTwoCenteredOddLowProfile j) t =
      clippedOddCorrelation yoshidaA (i.1 + 1) (j.1 + 1)
          (yoshidaA * t) / yoshidaA := by
  let F : ℝ → ℝ := fun y ↦
    (yoshidaClippedOddLowMode yoshidaA i (yoshidaA * t + y)).re *
      (yoshidaClippedOddLowMode yoshidaA j y).re
  have hpoint :
      (fun x : ℝ ↦
        factorTwoCenteredOddLowProfile i (t + x) *
          factorTwoCenteredOddLowProfile j x) =
        fun x ↦ F (yoshidaA * x) := by
    funext x
    simp only [factorTwoCenteredOddLowProfile, centeredRescale]
    dsimp only [F]
    congr 2
    ring_nf
  have hscale :
      (∫ x : ℝ in -1..1 - t, F (yoshidaA * x)) =
        yoshidaA⁻¹ *
          ∫ y : ℝ in yoshidaA * (-1)..yoshidaA * (1 - t), F y := by
    simpa only [smul_eq_mul] using
      (intervalIntegral.integral_comp_mul_left
        (a := (-1 : ℝ)) (b := 1 - t) F yoshidaA_pos.ne')
  have hle : -yoshidaA ≤ yoshidaA - yoshidaA * t := by
    nlinarith [yoshidaA_pos]
  calc
    factorTwoCenteredCrossCorrelation
        (factorTwoCenteredOddLowProfile i)
        (factorTwoCenteredOddLowProfile j) t =
        ∫ x : ℝ in -1..1 - t, F (yoshidaA * x) := by
      unfold factorTwoCenteredCrossCorrelation
      rw [hpoint]
    _ = yoshidaA⁻¹ *
          ∫ y : ℝ in yoshidaA * (-1)..yoshidaA * (1 - t), F y :=
      hscale
    _ = yoshidaA⁻¹ *
          ∫ y : ℝ in -yoshidaA..yoshidaA - yoshidaA * t, F y := by
      congr 2 <;> ring
    _ = yoshidaA⁻¹ *
          ∫ y : ℝ in -yoshidaA..yoshidaA - yoshidaA * t,
            clippedOddRealMode yoshidaA (i.1 + 1) (yoshidaA * t + y) *
              clippedOddRealMode yoshidaA (j.1 + 1) y := by
      congr 1
      apply intervalIntegral.integral_congr
      intro y hy
      rw [uIcc_of_le hle] at hy
      have hyIcc : y ∈ Set.Icc (-yoshidaA) yoshidaA := by
        constructor
        · exact hy.1
        · nlinarith [hy.2, yoshidaA_pos]
      have htyIcc : yoshidaA * t + y ∈
          Set.Icc (-yoshidaA) yoshidaA := by
        constructor <;> nlinarith [hy.1, hy.2, yoshidaA_pos]
      dsimp only [F]
      rw [yoshidaClippedOddLowMode, yoshidaClippedOddLowMode,
        yoshidaClippedOddMode_apply_of_mem yoshidaA_pos (i.1 + 1) htyIcc,
        yoshidaClippedOddMode_apply_of_mem yoshidaA_pos (j.1 + 1) hyIcc]
      simp only [clippedOddRealMode, Complex.ofReal_re]
    _ = clippedOddCorrelation yoshidaA (i.1 + 1) (j.1 + 1)
          (yoshidaA * t) / yoshidaA := by
      rw [clippedOddCorrelation]
      ring

/-- The symmetric centered correlation has the same scaling, since canonical
odd clipped correlations commute in their two positive frequencies. -/
theorem factorTwoCenteredCorrelationBilinear_oddLow_eq_clipped
    (i j : YoshidaOddIndex) {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
    factorTwoCenteredCorrelationBilinear
        (factorTwoCenteredOddLowProfile i)
        (factorTwoCenteredOddLowProfile j) t =
      clippedOddCorrelation yoshidaA (i.1 + 1) (j.1 + 1)
          (yoshidaA * t) / yoshidaA := by
  have hi : i.1 + 1 ≠ 0 := by omega
  have hj : j.1 + 1 ≠ 0 := by omega
  have hcomm :
      clippedOddCorrelation yoshidaA (i.1 + 1) (j.1 + 1)
          (yoshidaA * t) =
        clippedOddCorrelation yoshidaA (j.1 + 1) (i.1 + 1)
          (yoshidaA * t) := by
    by_cases hij : i = j
    · subst j
      rfl
    · have hnm : i.1 + 1 ≠ j.1 + 1 := by
        intro h
        apply hij
        apply Fin.ext
        omega
      rw [clippedOddCorrelation_offdiag yoshidaA_pos hi hj hnm,
        clippedOddCorrelation_offdiag yoshidaA_pos hj hi (Ne.symm hnm)]
      rw [add_comm (j.1 + 1) (i.1 + 1)]
      rw [show
        clippedOddFrequency yoshidaA (j.1 + 1) *
              Real.sin (clippedOddFrequency yoshidaA (i.1 + 1) *
                (yoshidaA * t)) -
            clippedOddFrequency yoshidaA (i.1 + 1) *
              Real.sin (clippedOddFrequency yoshidaA (j.1 + 1) *
                (yoshidaA * t)) =
          -(clippedOddFrequency yoshidaA (i.1 + 1) *
              Real.sin (clippedOddFrequency yoshidaA (j.1 + 1) *
                (yoshidaA * t)) -
            clippedOddFrequency yoshidaA (j.1 + 1) *
              Real.sin (clippedOddFrequency yoshidaA (i.1 + 1) *
                (yoshidaA * t))) by ring_nf]
      rw [show
        clippedOddFrequency yoshidaA (j.1 + 1) ^ 2 -
            clippedOddFrequency yoshidaA (i.1 + 1) ^ 2 =
          -(clippedOddFrequency yoshidaA (i.1 + 1) ^ 2 -
            clippedOddFrequency yoshidaA (j.1 + 1) ^ 2) by ring_nf]
      rw [mul_neg, neg_div_neg_eq]
  unfold factorTwoCenteredCorrelationBilinear
  rw [factorTwoCenteredCrossCorrelation_oddLow_eq_clipped i j ht0 ht2,
    factorTwoCenteredCrossCorrelation_oddLow_eq_clipped j i ht0 ht2,
    ← hcomm]
  ring

/-- Closed diagonal centered-correlation formula for the `i`th odd mode. -/
def factorTwoConcreteOddDiagonalCorrelationFormula
    (i : YoshidaOddIndex) (t : ℝ) : ℝ :=
  (((2 * yoshidaA - yoshidaA * t) *
          Real.cos
            (clippedOddFrequency yoshidaA (i.1 + 1) * (yoshidaA * t)) +
        Real.sin
            (clippedOddFrequency yoshidaA (i.1 + 1) * (yoshidaA * t)) /
          clippedOddFrequency yoshidaA (i.1 + 1)) /
      (2 * yoshidaA)) / yoshidaA

/-- Closed off-diagonal centered-correlation formula for two distinct odd
modes.  Its denominator is nonzero under the corresponding theorem's
`i ≠ j` hypothesis. -/
def factorTwoConcreteOddOffDiagonalCorrelationFormula
    (i j : YoshidaOddIndex) (t : ℝ) : ℝ :=
  ((((-1 : ℝ) ^ ((i.1 + 1) + (j.1 + 1)) / yoshidaA) *
          (clippedOddFrequency yoshidaA (i.1 + 1) *
              Real.sin
                (clippedOddFrequency yoshidaA (j.1 + 1) * (yoshidaA * t)) -
            clippedOddFrequency yoshidaA (j.1 + 1) *
              Real.sin
                (clippedOddFrequency yoshidaA (i.1 + 1) * (yoshidaA * t))) /
        (clippedOddFrequency yoshidaA (i.1 + 1) ^ 2 -
          clippedOddFrequency yoshidaA (j.1 + 1) ^ 2)) / yoshidaA)

/-- A single transparent formula for every centered odd correlation entry. -/
def factorTwoConcreteOddCorrelationFormula
    (i j : YoshidaOddIndex) (t : ℝ) : ℝ :=
  if i = j then factorTwoConcreteOddDiagonalCorrelationFormula i t
  else factorTwoConcreteOddOffDiagonalCorrelationFormula i j t

@[simp] theorem factorTwoConcreteOddCorrelationFormula_diag
    (i : YoshidaOddIndex) (t : ℝ) :
    factorTwoConcreteOddCorrelationFormula i i t =
      factorTwoConcreteOddDiagonalCorrelationFormula i t := by
  simp [factorTwoConcreteOddCorrelationFormula]

theorem factorTwoConcreteOddCorrelationFormula_offdiag
    {i j : YoshidaOddIndex} (hij : i ≠ j) (t : ℝ) :
    factorTwoConcreteOddCorrelationFormula i j t =
      factorTwoConcreteOddOffDiagonalCorrelationFormula i j t := by
  simp [factorTwoConcreteOddCorrelationFormula, hij]

/-- The symmetric centered correlation equals the explicit diagonal branch. -/
theorem factorTwoCenteredCorrelationBilinear_oddLow_diag
    (i : YoshidaOddIndex) {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
    factorTwoCenteredCorrelationBilinear
        (factorTwoCenteredOddLowProfile i)
        (factorTwoCenteredOddLowProfile i) t =
      factorTwoConcreteOddDiagonalCorrelationFormula i t := by
  rw [factorTwoCenteredCorrelationBilinear_oddLow_eq_clipped i i ht0 ht2,
    clippedOddCorrelation_diag yoshidaA_pos (by omega)]
  rfl

/-- The symmetric centered correlation equals the explicit off-diagonal
branch for distinct canonical modes. -/
theorem factorTwoCenteredCorrelationBilinear_oddLow_offdiag
    {i j : YoshidaOddIndex} (hij : i ≠ j) {t : ℝ}
    (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
    factorTwoCenteredCorrelationBilinear
        (factorTwoCenteredOddLowProfile i)
        (factorTwoCenteredOddLowProfile j) t =
      factorTwoConcreteOddOffDiagonalCorrelationFormula i j t := by
  have hnm : i.1 + 1 ≠ j.1 + 1 := by
    intro h
    apply hij
    apply Fin.ext
    omega
  rw [factorTwoCenteredCorrelationBilinear_oddLow_eq_clipped i j ht0 ht2,
    clippedOddCorrelation_offdiag yoshidaA_pos (by omega) (by omega) hnm]
  rfl

/-- The centered odd correlation is given by the unified exact formula on
the full perturbation integration interval. -/
theorem factorTwoCenteredCorrelationBilinear_oddLow_eq_formula
    (i j : YoshidaOddIndex) {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
    factorTwoCenteredCorrelationBilinear
        (factorTwoCenteredOddLowProfile i)
        (factorTwoCenteredOddLowProfile j) t =
      factorTwoConcreteOddCorrelationFormula i j t := by
  by_cases hij : i = j
  · subst j
    rw [factorTwoConcreteOddCorrelationFormula_diag,
      factorTwoCenteredCorrelationBilinear_oddLow_diag i ht0 ht2]
  · rw [factorTwoConcreteOddCorrelationFormula_offdiag hij,
      factorTwoCenteredCorrelationBilinear_oddLow_offdiag hij ht0 ht2]

/-- The exact perturbation functional applied to an explicit centered
correlation formula. -/
def factorTwoConcreteOddPerturbationEntryFormula (C : ℝ → ℝ) : ℝ :=
  yoshidaEndpointA *
      (∫ t : ℝ in 0..2,
        factorTwoSymmetricWeight (yoshidaEndpointA * t) * C t) -
    (Real.log 2 / Real.sqrt 2) * C 0 -
    (Real.log 3 / Real.sqrt 3) *
      C (factorTwoPrimeShift / yoshidaEndpointA)

/-- Every concrete odd perturbation entry is the weighted integral of its
closed diagonal/off-diagonal correlation branch, together with the exact
`p = 2` and `p = 3` atoms. -/
theorem factorTwoConcreteOddPerturbationMatrix_apply
    (i j : YoshidaOddIndex) :
    factorTwoConcreteOddPerturbationMatrix i j =
      factorTwoConcreteOddPerturbationEntryFormula
        (factorTwoConcreteOddCorrelationFormula i j) := by
  have hint :
      (∫ t : ℝ in 0..2,
        factorTwoSymmetricWeight (yoshidaEndpointA * t) *
          factorTwoCenteredCorrelationBilinear
            (factorTwoCenteredOddLowProfile i)
            (factorTwoCenteredOddLowProfile j) t) =
        ∫ t : ℝ in 0..2,
          factorTwoSymmetricWeight (yoshidaEndpointA * t) *
            factorTwoConcreteOddCorrelationFormula i j t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] at ht
    change factorTwoSymmetricWeight (yoshidaEndpointA * t) *
        factorTwoCenteredCorrelationBilinear
          (factorTwoCenteredOddLowProfile i)
          (factorTwoCenteredOddLowProfile j) t =
      factorTwoSymmetricWeight (yoshidaEndpointA * t) *
        factorTwoConcreteOddCorrelationFormula i j t
    rw [factorTwoCenteredCorrelationBilinear_oddLow_eq_formula
      i j ht.1 ht.2]
  have hzero := factorTwoCenteredCorrelationBilinear_oddLow_eq_formula
    i j (t := 0) (by norm_num) (by norm_num)
  have hprime := factorTwoCenteredCorrelationBilinear_oddLow_eq_formula
    i j (by linarith [factorTwoPrimeShift_div_endpointA_mem_one_two.1])
      factorTwoPrimeShift_div_endpointA_mem_one_two.2
  change factorTwoCenteredSymmetricPerturbationBilinear
      (factorTwoCenteredOddLowProfile i)
      (factorTwoCenteredOddLowProfile j) = _
  unfold factorTwoCenteredSymmetricPerturbationBilinear
    factorTwoConcreteOddPerturbationEntryFormula
  rw [hint, hzero, hprime]

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteOddPerturbationFormula

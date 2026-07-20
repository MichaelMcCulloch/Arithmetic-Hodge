import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteCleanEvenMomentFormula
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteCleanOddPositive
import ArithmeticHodge.Analysis.YoshidaFactorTwoScalarTargetSelectors

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoCleanEntryTargets

noncomputable section

open RatInterval
open YoshidaCoercivityNumerics
open YoshidaEvenIntervalCertificate
open YoshidaFactorTwoPhaseConcreteCleanEvenMatrix
open YoshidaFactorTwoPhaseConcreteCleanEvenMomentFormula
open YoshidaFactorTwoPhaseConcreteCleanOddMatrix
open YoshidaFactorTwoPhaseConcreteCleanOddPositive
open YoshidaFactorTwoPhaseEndpointAdaptedLow
open YoshidaFactorTwoPrimeTrigEnclosures
open YoshidaFactorTwoPhasePerturbationMomentSeries
open YoshidaFactorTwoScalarTargetSelectors
open YoshidaOddIntervalCertificate
open YoshidaOddGramPrefix
open YoshidaWeightedTailBounds

/-!
# Rational entry targets for the concrete clean blocks

The six scalar selectors already enclose every clean moment needed through
frequency `200`.  This module evaluates those boxes entrywise in the exact
moment formulas and through the endpoint-adaptation pullback.  It is the
sound matrix-entry interface needed by a robust congruence certificate.
-/

/-- The endpoint scale `A = log 2 / 2` as a rational interval. -/
def factorTwoEndpointScaleTarget : RatInterval :=
  ⟨factorTwoPrimeLogTwoInterval.lower / 2,
    factorTwoPrimeLogTwoInterval.upper / 2⟩

theorem factorTwoEndpointScaleTarget_contains :
    factorTwoEndpointScaleTarget.Contains yoshidaA := by
  have h := factorTwoPrimeLogTwoInterval_contains
  rw [factorTwoMomentLength_eq_yoshidaLength] at h
  unfold factorTwoEndpointScaleTarget Contains yoshidaA
  norm_num [factorTwoPrimeLogTwoInterval, yoshidaLength] at h ⊢
  constructor <;> linarith [h.1, h.2]

theorem factorTwoEndpointScaleTarget_lower_pos :
    0 < factorTwoEndpointScaleTarget.lower := by
  norm_num [factorTwoEndpointScaleTarget, factorTwoPrimeLogTwoInterval]

/-- Rational interval evaluation of one canonical even moment-Gram entry.
Unlike `evenMomentIntervalGram`, the indices are natural frequencies, so the
same definition also covers the endpoint-adaptation frequency `200`. -/
def factorTwoCanonicalEvenCleanTarget (n m : ℕ) : RatInterval :=
  if n = 0 then
    if m = 0 then cleanDiagonalTarget 0
    else pure (evenZeroCoeffQ m) * evenInvPiInterval *
      evenInvSqrtTwoInterval * cleanSineTarget m
  else if m = 0 then
    pure (evenZeroCoeffQ n) * evenInvPiInterval *
      evenInvSqrtTwoInterval * cleanSineTarget n
  else if n = m then
    cleanDiagonalTarget n -
      pure (evenDiagonalCoeffQ n) * evenInvPiInterval * cleanSineTarget n
  else
    pure (evenOffDiagonalCoeffQ n m) * evenInvPiInterval *
      (pure (m : ℚ) * cleanSineTarget m -
        pure (n : ℚ) * cleanSineTarget n)

/-- The canonical target encloses the true Section-6 entry through frequency
`200`, including the zero mode and every off-diagonal branch. -/
theorem factorTwoCanonicalEvenCleanTarget_contains
    {n m : ℕ} (hn200 : n ≤ 200) (hm200 : m ≤ 200) :
    (factorTwoCanonicalEvenCleanTarget n m).Contains
      (evenMomentGram yoshidaSineMoment yoshidaDiagonalMoment n m) := by
  by_cases hn : n = 0
  · subst n
    by_cases hm : m = 0
    · subst m
      simp only [factorTwoCanonicalEvenCleanTarget, if_pos]
      rw [evenMomentGram_zero_zero]
      exact cleanDiagonalTarget_contains (by norm_num)
    · simp only [factorTwoCanonicalEvenCleanTarget, if_pos, hm, if_false]
      rw [evenMomentGram_zero_nonzero _ _ m hm]
      exact contains_mul
        (contains_mul
          (contains_mul (contains_pure (evenZeroCoeffQ m))
            evenInvPiInterval_contains)
          evenInvSqrtTwoInterval_contains)
        (cleanSineTarget_contains hm200)
  · by_cases hm : m = 0
    · subst m
      simp only [factorTwoCanonicalEvenCleanTarget, hn, if_false, if_pos]
      rw [evenMomentGram_nonzero_zero _ _ n hn]
      exact contains_mul
        (contains_mul
          (contains_mul (contains_pure (evenZeroCoeffQ n))
            evenInvPiInterval_contains)
          evenInvSqrtTwoInterval_contains)
        (cleanSineTarget_contains hn200)
    · by_cases hnm : n = m
      · subst m
        simp only [factorTwoCanonicalEvenCleanTarget, hn, if_false,
          if_pos]
        rw [evenMomentGram_diagonal _ _ n hn]
        exact contains_sub (cleanDiagonalTarget_contains hn200)
          (contains_mul
            (contains_mul (contains_pure (evenDiagonalCoeffQ n))
              evenInvPiInterval_contains)
            (cleanSineTarget_contains hn200))
      · simp only [factorTwoCanonicalEvenCleanTarget, hn, hm, hnm,
          if_false]
        rw [evenMomentGram_offDiagonal _ _ n m hn hm hnm]
        exact contains_mul
          (contains_mul (contains_pure (evenOffDiagonalCoeffQ n m))
            evenInvPiInterval_contains)
          (contains_sub
            (contains_mul (by simpa using contains_pure (m : ℚ))
              (cleanSineTarget_contains hm200))
            (contains_mul (by simpa using contains_pure (n : ℚ))
              (cleanSineTarget_contains hn200)))

/-- Rational target for the trace ratio used in endpoint adaptation. -/
def factorTwoEndpointTraceTarget (i : YoshidaEvenIndex) : RatInterval :=
  if i.1 = 0 then evenInvSqrtTwoInterval
  else pure ((-1 : ℚ) ^ i.1)

theorem factorTwoEndpointTraceTarget_contains (i : YoshidaEvenIndex) :
    (factorTwoEndpointTraceTarget i).Contains
      (endpointEvenLowTraceRatio i) := by
  by_cases hi : i.1 = 0
  · simp only [factorTwoEndpointTraceTarget, endpointEvenLowTraceRatio,
      hi, if_pos]
    exact evenInvSqrtTwoInterval_contains
  · simp only [factorTwoEndpointTraceTarget, endpointEvenLowTraceRatio,
      hi, if_false]
    simpa using contains_pure ((-1 : ℚ) ^ i.1)

/-- The exact four-term endpoint-adaptation pullback, evaluated in rational
interval arithmetic and divided by the endpoint scale. -/
def factorTwoAdaptedEvenCleanTarget
    (i j : YoshidaEvenIndex) : RatInterval :=
  (factorTwoCanonicalEvenCleanTarget i.1 j.1 -
      factorTwoEndpointTraceTarget j *
        factorTwoCanonicalEvenCleanTarget i.1 200 -
      factorTwoEndpointTraceTarget i *
        factorTwoCanonicalEvenCleanTarget 200 j.1 +
      factorTwoEndpointTraceTarget i * factorTwoEndpointTraceTarget j *
        factorTwoCanonicalEvenCleanTarget 200 200) /
    factorTwoEndpointScaleTarget

/-- Every adapted-even clean target contains the corresponding true concrete
matrix entry. -/
theorem factorTwoAdaptedEvenCleanTarget_contains
    (i j : YoshidaEvenIndex) :
    (factorTwoAdaptedEvenCleanTarget i j).Contains
      (factorTwoConcreteAdaptedEvenCleanMatrix i j) := by
  rw [factorTwoConcreteAdaptedEvenCleanMatrix_apply]
  unfold factorTwoConcreteAdaptedEvenCleanMomentEntry
  apply contains_div_of_pos factorTwoEndpointScaleTarget_lower_pos
  · exact contains_add
      (contains_sub
        (contains_sub
          (factorTwoCanonicalEvenCleanTarget_contains
            (n := i.1) (m := j.1) (by omega) (by omega))
          (contains_mul (factorTwoEndpointTraceTarget_contains j)
            (factorTwoCanonicalEvenCleanTarget_contains
              (n := i.1) (m := 200) (by omega) (by norm_num))))
        (contains_mul (factorTwoEndpointTraceTarget_contains i)
          (factorTwoCanonicalEvenCleanTarget_contains
            (n := 200) (m := j.1) (by norm_num) (by omega))))
      (contains_mul
        (contains_mul (factorTwoEndpointTraceTarget_contains i)
          (factorTwoEndpointTraceTarget_contains j))
        (factorTwoCanonicalEvenCleanTarget_contains
          (n := 200) (m := 200) (by norm_num) (by norm_num)))
  · exact factorTwoEndpointScaleTarget_contains

/-- The existing odd moment interval formula, evaluated with the unified
clean scalar selectors and divided by the endpoint scale. -/
def factorTwoOddCleanTarget
    (i j : YoshidaOddIndex) : RatInterval :=
  oddMomentIntervalGram cleanSineTarget cleanDiagonalTarget i j /
    factorTwoEndpointScaleTarget

/-- Every odd clean target contains the corresponding true concrete matrix
entry. -/
theorem factorTwoOddCleanTarget_contains (i j : YoshidaOddIndex) :
    (factorTwoOddCleanTarget i j).Contains
      (factorTwoConcreteOddCleanMatrix i j) := by
  have hmoment := oddMomentIntervalGram_contains
    yoshidaSineMoment yoshidaDiagonalMoment
    cleanSineTarget cleanDiagonalTarget
    (fun n _hn hn10 ↦ cleanSineTarget_contains (n := n) (by omega))
    (fun n _hn hn10 ↦ cleanDiagonalTarget_contains (n := n) (by omega)) i j
  have hdiv := contains_div_of_pos factorTwoEndpointScaleTarget_lower_pos
    hmoment factorTwoEndpointScaleTarget_contains
  rw [factorTwoConcreteOddCleanMatrix_eq_scaled_oddMomentFullGram]
  simp only [Matrix.smul_apply, smul_eq_mul]
  convert hdiv using 1
  all_goals field_simp [yoshidaA_pos.ne']

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoCleanEntryTargets

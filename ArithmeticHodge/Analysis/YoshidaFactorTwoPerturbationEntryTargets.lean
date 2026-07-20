import ArithmeticHodge.Analysis.YoshidaFactorTwoCleanEntryTargets

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPerturbationEntryTargets

noncomputable section

open RatInterval
open YoshidaCoercivityNumerics
open YoshidaEvenIntervalCertificate
open YoshidaFactorTwoCleanEntryTargets
open YoshidaFactorTwoPhaseConcreteEvenPerturbationAdaptation
open YoshidaFactorTwoPhaseConcreteLowMatrix
open YoshidaFactorTwoPhaseConcretePerturbationMoments
open YoshidaFactorTwoPhaseEndpointAdaptedLow
open YoshidaFactorTwoScalarTargetSelectors
open YoshidaWeightedTailBounds

/-!
# Rational entry targets for the concrete perturbation blocks

The unified scalar targets for the symmetric moments `s`, `c` and the
antisymmetric moments `r`, `u` are evaluated in the exact branch formulas
for the concrete even, odd, and alternating matrices.  The resulting
intervals are the entrywise perturbation interface for the factor-two Schur
certificate.
-/

/-- Rational interval evaluation of one canonical-even symmetric
perturbation entry. -/
def factorTwoCanonicalEvenPerturbationTarget
    (n m : FactorTwoCanonicalEvenIndex) : RatInterval :=
  if n.1 = 0 then
    if m.1 = 0 then
      (pure (1 / 2 : ℚ) * symmetricAffineCosTarget n) /
        factorTwoEndpointScaleTarget
    else
      (pure (evenZeroCoeffQ m.1) * evenInvPiInterval *
          evenInvSqrtTwoInterval * symmetricSinTarget m) /
        factorTwoEndpointScaleTarget
  else if m.1 = 0 then
    (pure (evenZeroCoeffQ n.1) * evenInvPiInterval *
        evenInvSqrtTwoInterval * symmetricSinTarget n) /
      factorTwoEndpointScaleTarget
  else if n = m then
    (pure (1 / 2 : ℚ) *
        (symmetricAffineCosTarget n -
          pure (1 / (n.1 : ℚ)) * evenInvPiInterval *
            symmetricSinTarget n)) /
      factorTwoEndpointScaleTarget
  else
    (pure (evenOffDiagonalCoeffQ n.1 m.1) * evenInvPiInterval *
        (pure (m.1 : ℚ) * symmetricSinTarget m -
          pure (n.1 : ℚ) * symmetricSinTarget n)) /
      factorTwoEndpointScaleTarget

/-- The canonical-even target contains the exact scalar moment formula. -/
theorem factorTwoCanonicalEvenPerturbationTarget_contains
    (n m : FactorTwoCanonicalEvenIndex) :
    (factorTwoCanonicalEvenPerturbationTarget n m).Contains
      (factorTwoCanonicalEvenPerturbationMomentFormula n m) := by
  by_cases hn : n.1 = 0
  · by_cases hm : m.1 = 0
    · have hnum := contains_mul (contains_pure (1 / 2 : ℚ))
          (symmetricAffineCosTarget_contains n)
      have hdiv := contains_div_of_pos
        factorTwoEndpointScaleTarget_lower_pos hnum
        factorTwoEndpointScaleTarget_contains
      simp only [factorTwoCanonicalEvenPerturbationTarget, hn, hm, if_pos,
        factorTwoCanonicalEvenPerturbationMomentFormula]
      convert hdiv using 1
      simp only [hn]
      field_simp [yoshidaA_pos.ne']
      ring
    · have hnum := contains_mul
          (contains_mul
            (contains_mul (contains_pure (evenZeroCoeffQ m.1))
              evenInvPiInterval_contains)
            evenInvSqrtTwoInterval_contains)
          (symmetricSinTarget_contains m)
      have hdiv := contains_div_of_pos
        factorTwoEndpointScaleTarget_lower_pos hnum
        factorTwoEndpointScaleTarget_contains
      simp only [factorTwoCanonicalEvenPerturbationTarget, hn, hm, if_pos,
        if_false, factorTwoCanonicalEvenPerturbationMomentFormula]
      convert hdiv using 1
      unfold evenZeroCoeffQ factorTwoNaturalFrequency
      push_cast
      field_simp [Real.pi_ne_zero, yoshidaA_pos.ne', Nat.cast_ne_zero.mpr hm]
  · by_cases hm : m.1 = 0
    · have hnum := contains_mul
          (contains_mul
            (contains_mul (contains_pure (evenZeroCoeffQ n.1))
              evenInvPiInterval_contains)
            evenInvSqrtTwoInterval_contains)
          (symmetricSinTarget_contains n)
      have hdiv := contains_div_of_pos
        factorTwoEndpointScaleTarget_lower_pos hnum
        factorTwoEndpointScaleTarget_contains
      simp only [factorTwoCanonicalEvenPerturbationTarget, hn, hm, if_pos,
        if_false, factorTwoCanonicalEvenPerturbationMomentFormula]
      convert hdiv using 1
      unfold evenZeroCoeffQ factorTwoNaturalFrequency
      push_cast
      field_simp [Real.pi_ne_zero, yoshidaA_pos.ne', Nat.cast_ne_zero.mpr hn]
    · by_cases hnm : n = m
      · subst m
        have hnum := contains_mul (contains_pure (1 / 2 : ℚ))
          (contains_sub (symmetricAffineCosTarget_contains n)
            (contains_mul
              (contains_mul (contains_pure (1 / (n.1 : ℚ)))
                evenInvPiInterval_contains)
              (symmetricSinTarget_contains n)))
        have hdiv := contains_div_of_pos
          factorTwoEndpointScaleTarget_lower_pos hnum
          factorTwoEndpointScaleTarget_contains
        simp only [factorTwoCanonicalEvenPerturbationTarget, hn, if_false,
          if_pos, factorTwoCanonicalEvenPerturbationMomentFormula]
        convert hdiv using 1
        unfold factorTwoNaturalFrequency
        push_cast
        field_simp [Real.pi_ne_zero, yoshidaA_pos.ne',
          Nat.cast_ne_zero.mpr hn]
      · have hval : n.1 ≠ m.1 := fun h ↦ hnm (Fin.ext h)
        have hsq : (n.1 : ℚ) ^ 2 - (m.1 : ℚ) ^ 2 ≠ 0 := by
          apply sub_ne_zero.mpr
          intro h
          have hcast : (n.1 : ℚ) = (m.1 : ℚ) := by
            have hn0 : 0 ≤ (n.1 : ℚ) := by positivity
            have hm0 : 0 ≤ (m.1 : ℚ) := by positivity
            nlinarith
          exact hval (by exact_mod_cast hcast)
        have hnum := contains_mul
          (contains_mul
            (contains_pure (evenOffDiagonalCoeffQ n.1 m.1))
            evenInvPiInterval_contains)
          (contains_sub
            (contains_mul (contains_pure (m.1 : ℚ))
              (symmetricSinTarget_contains m))
            (contains_mul (contains_pure (n.1 : ℚ))
              (symmetricSinTarget_contains n)))
        have hdiv := contains_div_of_pos
          factorTwoEndpointScaleTarget_lower_pos hnum
          factorTwoEndpointScaleTarget_contains
        simp only [factorTwoCanonicalEvenPerturbationTarget, hn, hm, hnm,
          if_false, factorTwoCanonicalEvenPerturbationMomentFormula]
        convert hdiv using 1
        unfold evenOffDiagonalCoeffQ factorTwoNaturalFrequency
        push_cast
        field_simp [Real.pi_ne_zero, yoshidaA_pos.ne', hsq]

/-- Four-term endpoint-adapted target for the concrete even perturbation
matrix. -/
def factorTwoConcreteEvenPerturbationTarget
    (i j : YoshidaEvenIndex) : RatInterval :=
  factorTwoCanonicalEvenPerturbationTarget
      (factorTwoCanonicalEvenLowIndex i)
      (factorTwoCanonicalEvenLowIndex j) -
    factorTwoEndpointTraceTarget j *
      factorTwoCanonicalEvenPerturbationTarget
        (factorTwoCanonicalEvenLowIndex i) factorTwoCanonicalEvenTopIndex -
    factorTwoEndpointTraceTarget i *
      factorTwoCanonicalEvenPerturbationTarget
        factorTwoCanonicalEvenTopIndex (factorTwoCanonicalEvenLowIndex j) +
    factorTwoEndpointTraceTarget i * factorTwoEndpointTraceTarget j *
      factorTwoCanonicalEvenPerturbationTarget
        factorTwoCanonicalEvenTopIndex factorTwoCanonicalEvenTopIndex

theorem factorTwoConcreteEvenPerturbationTarget_contains
    (i j : YoshidaEvenIndex) :
    (factorTwoConcreteEvenPerturbationTarget i j).Contains
      (factorTwoConcreteEvenPerturbationMatrix i j) := by
  rw [factorTwoConcreteEvenPerturbationMatrix_eq_moments]
  exact contains_add
    (contains_sub
      (contains_sub
        (factorTwoCanonicalEvenPerturbationTarget_contains _ _)
        (contains_mul (factorTwoEndpointTraceTarget_contains j)
          (factorTwoCanonicalEvenPerturbationTarget_contains _ _)))
      (contains_mul (factorTwoEndpointTraceTarget_contains i)
        (factorTwoCanonicalEvenPerturbationTarget_contains _ _)))
      (contains_mul
        (contains_mul (factorTwoEndpointTraceTarget_contains i)
          (factorTwoEndpointTraceTarget_contains j))
      (factorTwoCanonicalEvenPerturbationTarget_contains _ _))

/-- Rational interval evaluation of a concrete odd symmetric perturbation
entry. -/
def factorTwoConcreteOddPerturbationTarget
    (i j : YoshidaOddIndex) : RatInterval :=
  let n := factorTwoOddCanonicalFrequencyIndex i
  let m := factorTwoOddCanonicalFrequencyIndex j
  if i = j then
    (pure (1 / 2 : ℚ) *
        (symmetricAffineCosTarget n +
          pure (1 / (n.1 : ℚ)) * evenInvPiInterval *
            symmetricSinTarget n)) /
      factorTwoEndpointScaleTarget
  else
    (pure (evenOffDiagonalCoeffQ n.1 m.1) * evenInvPiInterval *
        (pure (n.1 : ℚ) * symmetricSinTarget m -
          pure (m.1 : ℚ) * symmetricSinTarget n)) /
      factorTwoEndpointScaleTarget

theorem factorTwoConcreteOddPerturbationTarget_contains
    (i j : YoshidaOddIndex) :
    (factorTwoConcreteOddPerturbationTarget i j).Contains
      (factorTwoConcreteOddPerturbationMatrix i j) := by
  rw [factorTwoConcreteOddPerturbationMatrix_eq_moments]
  let n := factorTwoOddCanonicalFrequencyIndex i
  let m := factorTwoOddCanonicalFrequencyIndex j
  have hn : n.1 ≠ 0 := by
    dsimp only [n, factorTwoOddCanonicalFrequencyIndex]
    omega
  have hm : m.1 ≠ 0 := by
    dsimp only [m, factorTwoOddCanonicalFrequencyIndex]
    omega
  by_cases hij : i = j
  · subst j
    have hnum := contains_mul (contains_pure (1 / 2 : ℚ))
      (contains_add (symmetricAffineCosTarget_contains n)
        (contains_mul
          (contains_mul (contains_pure (1 / (n.1 : ℚ)))
            evenInvPiInterval_contains)
          (symmetricSinTarget_contains n)))
    have hdiv := contains_div_of_pos
      factorTwoEndpointScaleTarget_lower_pos hnum
      factorTwoEndpointScaleTarget_contains
    simp only [factorTwoConcreteOddPerturbationTarget,
      factorTwoConcreteOddPerturbationMomentFormula]
    change ((RatInterval.pure (1 / 2 : ℚ) *
        (symmetricAffineCosTarget n +
          RatInterval.pure (1 / (n.1 : ℚ)) * evenInvPiInterval *
            symmetricSinTarget n)) /
      factorTwoEndpointScaleTarget).Contains
        ((1 / (2 * yoshidaA)) *
          (factorTwoSymmetricAffineCosMoment n.1 +
            (1 / factorTwoNaturalFrequency n.1) *
              factorTwoSymmetricSinMoment n.1))
    convert hdiv using 1
    unfold factorTwoNaturalFrequency
    push_cast
    field_simp [Real.pi_ne_zero, yoshidaA_pos.ne',
      Nat.cast_ne_zero.mpr hn]
  · have hval : n.1 ≠ m.1 := by
      intro h
      apply hij
      apply Fin.ext
      dsimp only [n, m, factorTwoOddCanonicalFrequencyIndex] at h ⊢
      omega
    have hsq : (n.1 : ℚ) ^ 2 - (m.1 : ℚ) ^ 2 ≠ 0 := by
      apply sub_ne_zero.mpr
      intro h
      have hcast : (n.1 : ℚ) = (m.1 : ℚ) := by
        have hn0 : 0 ≤ (n.1 : ℚ) := by positivity
        have hm0 : 0 ≤ (m.1 : ℚ) := by positivity
        nlinarith
      exact hval (by exact_mod_cast hcast)
    have hnum := contains_mul
      (contains_mul (contains_pure (evenOffDiagonalCoeffQ n.1 m.1))
        evenInvPiInterval_contains)
      (contains_sub
        (contains_mul (contains_pure (n.1 : ℚ))
          (symmetricSinTarget_contains m))
        (contains_mul (contains_pure (m.1 : ℚ))
          (symmetricSinTarget_contains n)))
    have hdiv := contains_div_of_pos
      factorTwoEndpointScaleTarget_lower_pos hnum
      factorTwoEndpointScaleTarget_contains
    simp only [factorTwoConcreteOddPerturbationTarget,
      factorTwoConcreteOddPerturbationMomentFormula, hij, if_false]
    change ((RatInterval.pure (evenOffDiagonalCoeffQ n.1 m.1) *
        evenInvPiInterval *
        (RatInterval.pure (n.1 : ℚ) * symmetricSinTarget m -
          RatInterval.pure (m.1 : ℚ) * symmetricSinTarget n)) /
      factorTwoEndpointScaleTarget).Contains
        ((((-1 : ℝ) ^ (n.1 + m.1) /
            (factorTwoNaturalFrequency n.1 ^ 2 -
              factorTwoNaturalFrequency m.1 ^ 2)) / yoshidaA) *
          (factorTwoNaturalFrequency n.1 *
              factorTwoSymmetricSinMoment m.1 -
            factorTwoNaturalFrequency m.1 *
              factorTwoSymmetricSinMoment n.1))
    convert hdiv using 1
    unfold evenOffDiagonalCoeffQ factorTwoNaturalFrequency
    push_cast
    field_simp [Real.pi_ne_zero, yoshidaA_pos.ne', hsq]

/-- Rational coefficient in the zero-even-mode branch of the alternating
moment formula. -/
def factorTwoAlternatingZeroCoeffQ (m : ℕ) : ℚ :=
  (-1 : ℚ) ^ m / m

/-- Rational coefficient remaining after cancelling one factor of `π` in
the alternating off-diagonal branch. -/
def factorTwoAlternatingOffDiagonalCoeffQ (n m : ℕ) : ℚ :=
  ((-1 : ℚ) ^ (n + m) * (m : ℚ)) /
    ((m : ℚ) ^ 2 - (n : ℚ) ^ 2)

/-- Rational interval evaluation of one canonical even--odd alternating
moment.  The second index is represented canonically so all scalar-selector
bounds are available without a separate range hypothesis. -/
def factorTwoCanonicalAlternatingTarget
    (n m : FactorTwoCanonicalEvenIndex) : RatInterval :=
  if n.1 = 0 then
    (pure (factorTwoAlternatingZeroCoeffQ m.1) *
        evenInvSqrtTwoInterval * evenInvPiInterval *
        antisymmetricOneSubCosTarget m) /
      factorTwoEndpointScaleTarget
  else if n.1 = m.1 then
    (pure (-1 / 2 : ℚ) * antisymmetricAffineSinTarget m) /
      factorTwoEndpointScaleTarget
  else
    (pure (factorTwoAlternatingOffDiagonalCoeffQ n.1 m.1) *
        evenInvPiInterval *
        (antisymmetricOneSubCosTarget m -
          antisymmetricOneSubCosTarget n)) /
      factorTwoEndpointScaleTarget

/-- The canonical alternating target contains the exact moment formula at
every positive odd frequency. -/
theorem factorTwoCanonicalAlternatingTarget_contains
    (n m : FactorTwoCanonicalEvenIndex) (hm : m.1 ≠ 0) :
    (factorTwoCanonicalAlternatingTarget n m).Contains
      (factorTwoCanonicalAlternatingMomentFormula n m.1) := by
  have hsqrt : Real.sqrt 2 ≠ 0 := by positivity
  by_cases hn : n.1 = 0
  · have hnum := contains_mul
      (contains_mul
        (contains_mul
          (contains_pure (factorTwoAlternatingZeroCoeffQ m.1))
          evenInvSqrtTwoInterval_contains)
        evenInvPiInterval_contains)
      (antisymmetricOneSubCosTarget_contains m)
    have hdiv := contains_div_of_pos
      factorTwoEndpointScaleTarget_lower_pos hnum
      factorTwoEndpointScaleTarget_contains
    simp only [factorTwoCanonicalAlternatingTarget,
      factorTwoCanonicalAlternatingMomentFormula, hn, if_pos]
    convert hdiv using 1
    unfold factorTwoAlternatingZeroCoeffQ factorTwoNaturalFrequency
    push_cast
    field_simp [hsqrt, Real.pi_ne_zero, yoshidaA_pos.ne',
      Nat.cast_ne_zero.mpr hm]
  · by_cases hnm : n.1 = m.1
    · have hnmFin : n = m := Fin.ext hnm
      subst n
      have hnum := contains_mul (contains_pure (-1 / 2 : ℚ))
        (antisymmetricAffineSinTarget_contains m)
      have hdiv := contains_div_of_pos
        factorTwoEndpointScaleTarget_lower_pos hnum
        factorTwoEndpointScaleTarget_contains
      simp only [factorTwoCanonicalAlternatingTarget,
        factorTwoCanonicalAlternatingMomentFormula, hm, if_pos, if_false]
      convert hdiv using 1
      field_simp [yoshidaA_pos.ne']
      ring
    · have hsq : (m.1 : ℚ) ^ 2 - (n.1 : ℚ) ^ 2 ≠ 0 := by
        apply sub_ne_zero.mpr
        intro h
        have hcast : (m.1 : ℚ) = (n.1 : ℚ) := by
          have hm0 : 0 ≤ (m.1 : ℚ) := by positivity
          have hn0 : 0 ≤ (n.1 : ℚ) := by positivity
          nlinarith
        apply hnm
        exact_mod_cast hcast.symm
      have hnum := contains_mul
        (contains_mul
          (contains_pure
            (factorTwoAlternatingOffDiagonalCoeffQ n.1 m.1))
          evenInvPiInterval_contains)
        (contains_sub
          (antisymmetricOneSubCosTarget_contains m)
          (antisymmetricOneSubCosTarget_contains n))
      have hdiv := contains_div_of_pos
        factorTwoEndpointScaleTarget_lower_pos hnum
        factorTwoEndpointScaleTarget_contains
      simp only [factorTwoCanonicalAlternatingTarget,
        factorTwoCanonicalAlternatingMomentFormula, hn, hnm, if_false]
      convert hdiv using 1
      unfold factorTwoAlternatingOffDiagonalCoeffQ
        factorTwoNaturalFrequency
      push_cast
      field_simp [Real.pi_ne_zero, yoshidaA_pos.ne', hsq]

/-- One-step endpoint-adapted alternating target. -/
def factorTwoAdaptedAlternatingTarget
    (i : YoshidaEvenIndex) (m : FactorTwoCanonicalEvenIndex) : RatInterval :=
  factorTwoCanonicalAlternatingTarget
      (factorTwoCanonicalEvenLowIndex i) m -
    factorTwoEndpointTraceTarget i *
      factorTwoCanonicalAlternatingTarget factorTwoCanonicalEvenTopIndex m

theorem factorTwoAdaptedAlternatingTarget_contains
    (i : YoshidaEvenIndex) (m : FactorTwoCanonicalEvenIndex)
    (hm : m.1 ≠ 0) :
    (factorTwoAdaptedAlternatingTarget i m).Contains
      (factorTwoAdaptedAlternatingMomentFormula i m.1) := by
  exact contains_sub
    (factorTwoCanonicalAlternatingTarget_contains _ _ hm)
    (contains_mul (factorTwoEndpointTraceTarget_contains i)
      (factorTwoCanonicalAlternatingTarget_contains _ _ hm))

/-- Concrete alternating matrix target, with the odd frequency embedded in
the common canonical range. -/
def factorTwoConcreteAlternatingTarget
    (i : YoshidaEvenIndex) (j : YoshidaOddIndex) : RatInterval :=
  factorTwoAdaptedAlternatingTarget i
    (factorTwoOddCanonicalFrequencyIndex j)

theorem factorTwoConcreteAlternatingTarget_contains
    (i : YoshidaEvenIndex) (j : YoshidaOddIndex) :
    (factorTwoConcreteAlternatingTarget i j).Contains
      (factorTwoConcreteAlternatingMatrix i j) := by
  rw [factorTwoConcreteAlternatingMatrix_eq_moments]
  exact factorTwoAdaptedAlternatingTarget_contains i
    (factorTwoOddCanonicalFrequencyIndex j) (by
      simp [factorTwoOddCanonicalFrequencyIndex])

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPerturbationEntryTargets

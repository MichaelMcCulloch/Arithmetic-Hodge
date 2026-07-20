import ArithmeticHodge.Analysis.YoshidaFactorTwoCleanHighDiagonalEnclosures
import ArithmeticHodge.Analysis.YoshidaFactorTwoCleanLowDiagonalEnclosures
import ArithmeticHodge.Analysis.YoshidaFactorTwoCleanLowSineEnclosures
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhasePerturbationAffineCosEnclosures
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhasePerturbationAffineSinEnclosures
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhasePerturbationOneSubCosLowEnclosures
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhasePerturbationSinLowEnclosures

/-!
# Unified factor-two scalar target selectors

This module exposes one proof-transparent target API for each scalar family
`S`, `D`, `s`, `c`, `r`, and `u`.  Existing all-mode targets are reused by
abbreviation.  Only the clean diagonal and symmetric perturbation sine
families need new low/high selectors.
-/

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoScalarTargetSelectors

open RatInterval
open YoshidaFactorTwoCleanHighDiagonalEnclosures
open YoshidaFactorTwoCleanLowDiagonalEnclosures
open YoshidaFactorTwoCleanLowSineEnclosures
open YoshidaFactorTwoPhaseConcreteEvenPerturbationAdaptation
open YoshidaFactorTwoPhaseConcretePerturbationMoments
open YoshidaFactorTwoPhasePerturbationAffineCosEnclosures
open YoshidaFactorTwoPhasePerturbationAffineSinEnclosures
open YoshidaFactorTwoPhasePerturbationOneSubCosLowEnclosures
open YoshidaFactorTwoPhasePerturbationSinEnclosures
open YoshidaFactorTwoPhasePerturbationSinLowEnclosures
open YoshidaOddGramPrefix

/-! ## Clean scalar families -/

/-- Unified clean sine (`S`) target through mode `200`. -/
abbrev cleanSineTarget (n : ℕ) : RatInterval :=
  yoshidaFactorTwoCleanSineTarget n

theorem cleanSineTarget_contains {n : ℕ} (hn200 : n ≤ 200) :
    (cleanSineTarget n).Contains (yoshidaSineMoment n) :=
  yoshidaFactorTwoCleanSineTarget_contains hn200

theorem cleanSineTarget_width_le {n : ℕ} (hn200 : n ≤ 200) :
    width (cleanSineTarget n) ≤ (1 / 1000000000 : ℚ) :=
  yoshidaFactorTwoCleanSineTarget_width_le hn200

/-- Unified clean diagonal (`D`) target: the exact low construction is used
on modes `0, ..., 59`, and the uniform high construction thereafter. -/
def cleanDiagonalTarget (n : ℕ) : RatInterval :=
  if n ≤ 59 then
    yoshidaFactorTwoCleanLowDiagonalTarget n
  else
    yoshidaFactorTwoCleanHighDiagonalTarget n

theorem cleanDiagonalTarget_contains {n : ℕ} (hn200 : n ≤ 200) :
    (cleanDiagonalTarget n).Contains (yoshidaDiagonalMoment n) := by
  by_cases hn59 : n ≤ 59
  · simp only [cleanDiagonalTarget, hn59, if_pos]
    exact yoshidaFactorTwoCleanLowDiagonalTarget_contains hn59
  · simp only [cleanDiagonalTarget, hn59, if_false]
    exact yoshidaFactorTwoCleanHighDiagonalTarget_contains (by omega)

theorem cleanDiagonalTarget_width_le {n : ℕ} (hn200 : n ≤ 200) :
    width (cleanDiagonalTarget n) ≤ (1 / 1000000000 : ℚ) := by
  by_cases hn59 : n ≤ 59
  · simp only [cleanDiagonalTarget, hn59, if_pos]
    exact yoshidaFactorTwoCleanLowDiagonalTarget_width_le hn59
  · simp only [cleanDiagonalTarget, hn59, if_false]
    exact yoshidaFactorTwoCleanHighDiagonalTarget_width_le (by omega) hn200

/-! ## Perturbation scalar families -/

/-- Unified symmetric sine (`s`) target.  The checkpointed construction is
used exactly on positive modes `1, ..., 152`; the direct construction handles
the exact zero mode and high modes `153, ..., 200`. -/
def symmetricSinTarget (n : FactorTwoCanonicalEvenIndex) : RatInterval :=
  if 1 ≤ n.1 ∧ n.1 ≤ 152 then
    factorTwoSymmetricSinLowInterval n
  else
    factorTwoSymmetricSinMomentInterval n

theorem symmetricSinTarget_contains (n : FactorTwoCanonicalEvenIndex) :
    (symmetricSinTarget n).Contains (factorTwoSymmetricSinMoment n.1) := by
  by_cases hlow : 1 ≤ n.1 ∧ n.1 ≤ 152
  · simp only [symmetricSinTarget, hlow, if_pos]
    exact factorTwoSymmetricSinLowInterval_contains n (by omega)
  · simp only [symmetricSinTarget, hlow, if_false]
    exact factorTwoSymmetricSinMomentInterval_contains n

theorem symmetricSinTarget_width_le (n : FactorTwoCanonicalEvenIndex) :
    width (symmetricSinTarget n) ≤ (1 / 1000000000 : ℚ) := by
  by_cases hlow : 1 ≤ n.1 ∧ n.1 ≤ 152
  · simp only [symmetricSinTarget, hlow, if_pos]
    exact factorTwoSymmetricSinLowInterval_width_le n hlow.1 hlow.2
  · simp only [symmetricSinTarget, hlow, if_false]
    apply factorTwoSymmetricSinMomentInterval_width_le_certified n
    by_cases hn0 : n.1 = 0
    · exact Or.inl hn0
    · exact Or.inr (by omega)

/-- Unified symmetric affine-cosine (`c`) target. -/
abbrev symmetricAffineCosTarget
    (n : FactorTwoCanonicalEvenIndex) : RatInterval :=
  factorTwoSymmetricAffineCosMomentInterval n

theorem symmetricAffineCosTarget_contains
    (n : FactorTwoCanonicalEvenIndex) :
    (symmetricAffineCosTarget n).Contains
      (factorTwoSymmetricAffineCosMoment n.1) :=
  factorTwoSymmetricAffineCosMomentInterval_contains n

theorem symmetricAffineCosTarget_width_le
    (n : FactorTwoCanonicalEvenIndex) :
    width (symmetricAffineCosTarget n) ≤ (1 / 1000000000 : ℚ) :=
  factorTwoSymmetricAffineCosMomentInterval_width_le n

/-- Unified antisymmetric one-minus-cosine (`r`) target. -/
abbrev antisymmetricOneSubCosTarget
    (n : FactorTwoCanonicalEvenIndex) : RatInterval :=
  factorTwoAntisymmetricOneSubCosCertifiedInterval n

theorem antisymmetricOneSubCosTarget_contains
    (n : FactorTwoCanonicalEvenIndex) :
    (antisymmetricOneSubCosTarget n).Contains
      (factorTwoAntisymmetricOneSubCosMoment n.1) :=
  factorTwoAntisymmetricOneSubCosCertifiedInterval_contains n

theorem antisymmetricOneSubCosTarget_width_le
    (n : FactorTwoCanonicalEvenIndex) :
    width (antisymmetricOneSubCosTarget n) ≤ (1 / 1000000000 : ℚ) :=
  factorTwoAntisymmetricOneSubCosCertifiedInterval_width_le n

/-- Unified antisymmetric affine-sine (`u`) target. -/
abbrev antisymmetricAffineSinTarget
    (n : FactorTwoCanonicalEvenIndex) : RatInterval :=
  factorTwoAntisymmetricAffineSinMomentInterval n

theorem antisymmetricAffineSinTarget_contains
    (n : FactorTwoCanonicalEvenIndex) :
    (antisymmetricAffineSinTarget n).Contains
      (factorTwoAntisymmetricAffineSinMoment n.1) :=
  factorTwoAntisymmetricAffineSinMomentInterval_contains n

theorem antisymmetricAffineSinTarget_width_le
    (n : FactorTwoCanonicalEvenIndex) :
    width (antisymmetricAffineSinTarget n) ≤ (1 / 1000000000 : ℚ) :=
  factorTwoAntisymmetricAffineSinMomentInterval_width_le n

end ArithmeticHodge.Analysis.YoshidaFactorTwoScalarTargetSelectors

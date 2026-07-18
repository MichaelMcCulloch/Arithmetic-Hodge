import ArithmeticHodge.Analysis.TwoByTwoSchur
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicRetainedSingularGapStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseSingularWeightedCauchyStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseRetainedSingularSchurStructural

open TwoByTwoSchur
open UnitIntervalLogEnergyAffine
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseSingularWeightedCauchyStructural

noncomputable section

/-!
# Low--tail Schur completion with a retained singular operator

The potential/reflected-pole cross is one half of the polarization of a
positive singular Gram.  This module may spend different fractions of that
Gram on the low and tail diagonals and removes a geometrically compatible
fraction from the mixed row before asking for a scalar complement estimate.
This is the lossless operator-valued replacement for bounding the entire
survivor by a coarse scalar reserve.
-/

/-- If the low and tail phases retain fractions `alpha` and `beta` of the
singular Gram, a coefficient `gamma` can be removed from the mixed row as
soon as `gamma² ≤ alpha * beta`.  No sign condition on `gamma` is needed. -/
theorem factorTwoEndpointLowTailMixed_sq_le_of_asymmetrically_retained_singular
    (uLow vLow uR vR : ℝ → ℝ)
    (huLow : Continuous uLow) (hvLow : Continuous vLow)
    (huR : Continuous uR) (hvR : Continuous vR)
    (hlocaluLow : LocallyLipschitzOn (Icc (-1) 1) uLow)
    (hlocalvLow : LocallyLipschitzOn (Icc (-1) 1) vLow)
    (hlocaluR : LocallyLipschitzOn (Icc (-1) 1) uR)
    (hlocalvR : LocallyLipschitzOn (Icc (-1) 1) vR)
    (a b alpha beta gamma lowComplement tailComplement : ℝ)
    (hab : a ^ 2 + b ^ 2 ≤ 1)
    (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta)
    (hgamma : gamma ^ 2 ≤ alpha * beta)
    (huRaw : centeredRawLogEnergy (uLow + uR) =
      centeredRawLogEnergy uLow + centeredRawLogEnergy uR)
    (hvRaw : centeredRawLogEnergy (vLow + vR) =
      centeredRawLogEnergy vLow + centeredRawLogEnergy vR)
    (huOrth : (∫ x : ℝ in -1..1, uLow x * uR x) = 0)
    (hvOrth : (∫ x : ℝ in -1..1, vLow x * vR x) = 0)
    (hlowComplement : 0 ≤ lowComplement)
    (htailComplement : 0 ≤ tailComplement)
    (hlowRetains :
      alpha * ((1 / 2 : ℝ) *
          factorTwoPhaseSingularWeightedEnergy uLow vLow a b) +
        lowComplement ≤ factorTwoEndpointChannelPhase uLow vLow a b)
    (htailRetains :
      beta * ((1 / 2 : ℝ) *
          factorTwoPhaseSingularWeightedEnergy uR vR a b) +
        tailComplement ≤ factorTwoEndpointChannelPhase uR vR a b)
    (hremaining :
      (factorTwoEndpointLowTailMixed uLow uR vLow vR a b -
          gamma * factorTwoPhasePotentialPoleMixed
            uLow vLow uR vR a b) ^ 2 ≤
        lowComplement * tailComplement) :
    factorTwoEndpointLowTailMixed uLow uR vLow vR a b ^ 2 ≤
      factorTwoEndpointChannelPhase uLow vLow a b *
        factorTwoEndpointChannelPhase uR vR a b := by
  let low := factorTwoEndpointChannelPhase uLow vLow a b
  let tail := factorTwoEndpointChannelPhase uR vR a b
  let lowSingular := (1 / 2 : ℝ) *
    factorTwoPhaseSingularWeightedEnergy uLow vLow a b
  let tailSingular := (1 / 2 : ℝ) *
    factorTwoPhaseSingularWeightedEnergy uR vR a b
  let pole := factorTwoPhasePotentialPoleMixed uLow vLow uR vR a b
  let x := alpha * lowSingular
  let y := beta * tailSingular
  let z := gamma * pole
  let s := factorTwoEndpointLowTailMixed uLow uR vLow vR a b - z
  have hLowSingular : 0 ≤ lowSingular := by
    dsimp only [lowSingular]
    exact mul_nonneg (by norm_num)
      (factorTwoPhaseSingularWeightedEnergy_nonneg uLow vLow a b hab)
  have hTailSingular : 0 ≤ tailSingular := by
    dsimp only [tailSingular]
    exact mul_nonneg (by norm_num)
      (factorTwoPhaseSingularWeightedEnergy_nonneg uR vR a b hab)
  have hx : 0 ≤ x := by
    exact mul_nonneg halpha hLowSingular
  have hy : 0 ≤ y := by
    exact mul_nonneg hbeta hTailSingular
  have hpole : pole ^ 2 ≤ lowSingular * tailSingular := by
    simpa only [pole, lowSingular, tailSingular] using
      factorTwoPhasePotentialPoleMixed_sq_le_half_energy_mul_half_energy
        uLow vLow uR vR huLow hvLow huR hvR
        hlocaluLow hlocalvLow hlocaluR hlocalvR a b
        (hab.trans (by norm_num)) huRaw hvRaw huOrth hvOrth
  have hz : z ^ 2 ≤ x * y := by
    have hpoleScaled := mul_le_mul_of_nonneg_left hpole (sq_nonneg gamma)
    have hcoeffScaled := mul_le_mul_of_nonneg_right hgamma
      (mul_nonneg hLowSingular hTailSingular)
    calc
      z ^ 2 = gamma ^ 2 * pole ^ 2 := by
        dsimp only [z]
        ring
      _ ≤ gamma ^ 2 * (lowSingular * tailSingular) := hpoleScaled
      _ ≤ (alpha * beta) * (lowSingular * tailSingular) := hcoeffScaled
      _ = x * y := by
        dsimp only [x, y]
        ring
  have hlow : 0 ≤ low - x := by
    dsimp only [low, x, lowSingular]
    linarith
  have htail : 0 ≤ tail - y := by
    dsimp only [tail, y, tailSingular]
    linarith
  have hs : s ^ 2 ≤ (low - x) * (tail - y) := by
    have hlowBound : lowComplement ≤ low - x := by
      dsimp only [low, x, lowSingular]
      linarith
    have htailBound : tailComplement ≤ tail - y := by
      dsimp only [tail, y, tailSingular]
      linarith
    have hproduct := mul_le_mul hlowBound htailBound
      htailComplement hlow
    calc
      s ^ 2 ≤ lowComplement * tailComplement := by
        simpa only [s, z, pole] using hremaining
      _ ≤ (low - x) * (tail - y) := hproduct
  have hdet := determinant_bound_add_complements
    low tail x y z s hx hy hlow htail hz hs
  have hsum : z + s = factorTwoEndpointLowTailMixed
      uLow uR vLow vR a b := by
    dsimp only [s]
    ring
  rw [hsum] at hdet
  simpa only [low, tail] using hdet

/-- Strict retained-singular Schur completion for arbitrary named diagonal
targets and an arbitrary mixed scalar.  This form is needed when a finite
border uses a charged tail diagonal smaller than the original endpoint phase
form.  The singular pole is still controlled analytically, while the strict
residual contraction supplies the determinant margin. -/
theorem mixed_sq_lt_of_asymmetrically_retained_singular_targets
    (uLow vLow uR vR : ℝ → ℝ)
    (huLow : Continuous uLow) (hvLow : Continuous vLow)
    (huR : Continuous uR) (hvR : Continuous vR)
    (hlocaluLow : LocallyLipschitzOn (Icc (-1) 1) uLow)
    (hlocalvLow : LocallyLipschitzOn (Icc (-1) 1) vLow)
    (hlocaluR : LocallyLipschitzOn (Icc (-1) 1) uR)
    (hlocalvR : LocallyLipschitzOn (Icc (-1) 1) vR)
    (a b alpha beta gamma lowTarget tailTarget
      lowComplement tailComplement mixed : ℝ)
    (hab : a ^ 2 + b ^ 2 ≤ 1)
    (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta)
    (hgamma : gamma ^ 2 ≤ alpha * beta)
    (huRaw : centeredRawLogEnergy (uLow + uR) =
      centeredRawLogEnergy uLow + centeredRawLogEnergy uR)
    (hvRaw : centeredRawLogEnergy (vLow + vR) =
      centeredRawLogEnergy vLow + centeredRawLogEnergy vR)
    (huOrth : (∫ x : ℝ in -1..1, uLow x * uR x) = 0)
    (hvOrth : (∫ x : ℝ in -1..1, vLow x * vR x) = 0)
    (hlowComplement : 0 ≤ lowComplement)
    (htailComplement : 0 ≤ tailComplement)
    (hlowRetains :
      alpha * ((1 / 2 : ℝ) *
          factorTwoPhaseSingularWeightedEnergy uLow vLow a b) +
        lowComplement ≤ lowTarget)
    (htailRetains :
      beta * ((1 / 2 : ℝ) *
          factorTwoPhaseSingularWeightedEnergy uR vR a b) +
        tailComplement ≤ tailTarget)
    (hremaining :
      (mixed - gamma * factorTwoPhasePotentialPoleMixed
          uLow vLow uR vR a b) ^ 2 <
        lowComplement * tailComplement) :
    mixed ^ 2 < lowTarget * tailTarget := by
  let lowSingular := (1 / 2 : ℝ) *
    factorTwoPhaseSingularWeightedEnergy uLow vLow a b
  let tailSingular := (1 / 2 : ℝ) *
    factorTwoPhaseSingularWeightedEnergy uR vR a b
  let pole := factorTwoPhasePotentialPoleMixed uLow vLow uR vR a b
  let x := alpha * lowSingular
  let y := beta * tailSingular
  let z := gamma * pole
  let s := mixed - z
  have hLowSingular : 0 ≤ lowSingular := by
    dsimp only [lowSingular]
    exact mul_nonneg (by norm_num)
      (factorTwoPhaseSingularWeightedEnergy_nonneg uLow vLow a b hab)
  have hTailSingular : 0 ≤ tailSingular := by
    dsimp only [tailSingular]
    exact mul_nonneg (by norm_num)
      (factorTwoPhaseSingularWeightedEnergy_nonneg uR vR a b hab)
  have hx : 0 ≤ x := mul_nonneg halpha hLowSingular
  have hy : 0 ≤ y := mul_nonneg hbeta hTailSingular
  have hpole : pole ^ 2 ≤ lowSingular * tailSingular := by
    simpa only [pole, lowSingular, tailSingular] using
      factorTwoPhasePotentialPoleMixed_sq_le_half_energy_mul_half_energy
        uLow vLow uR vR huLow hvLow huR hvR
        hlocaluLow hlocalvLow hlocaluR hlocalvR a b
        (hab.trans (by norm_num)) huRaw hvRaw huOrth hvOrth
  have hz : z ^ 2 ≤ x * y := by
    have hpoleScaled := mul_le_mul_of_nonneg_left hpole (sq_nonneg gamma)
    have hcoeffScaled := mul_le_mul_of_nonneg_right hgamma
      (mul_nonneg hLowSingular hTailSingular)
    calc
      z ^ 2 = gamma ^ 2 * pole ^ 2 := by
        dsimp only [z]
        ring
      _ ≤ gamma ^ 2 * (lowSingular * tailSingular) := hpoleScaled
      _ ≤ (alpha * beta) * (lowSingular * tailSingular) := hcoeffScaled
      _ = x * y := by
        dsimp only [x, y]
        ring
  have hlow : 0 ≤ lowTarget - x := by
    dsimp only [x, lowSingular]
    linarith
  have htail : 0 ≤ tailTarget - y := by
    dsimp only [y, tailSingular]
    linarith
  have hs : s ^ 2 < (lowTarget - x) * (tailTarget - y) := by
    have hlowBound : lowComplement ≤ lowTarget - x := by
      dsimp only [x, lowSingular]
      linarith
    have htailBound : tailComplement ≤ tailTarget - y := by
      dsimp only [y, tailSingular]
      linarith
    have hproduct := mul_le_mul hlowBound htailBound
      htailComplement hlow
    exact lt_of_lt_of_le (by simpa only [s, z, pole] using hremaining)
      hproduct
  have hdet := determinant_bound_add_complements_lt
    lowTarget tailTarget x y z s hx hy hlow htail hz hs
  have hsum : z + s = mixed := by
    dsimp only [s]
    ring
  rw [hsum] at hdet
  exact hdet

/-- Symmetric specialization of the asymmetric retained-singular Schur
theorem. -/
theorem factorTwoEndpointLowTailMixed_sq_le_of_retained_singular
    (uLow vLow uR vR : ℝ → ℝ)
    (huLow : Continuous uLow) (hvLow : Continuous vLow)
    (huR : Continuous uR) (hvR : Continuous vR)
    (hlocaluLow : LocallyLipschitzOn (Icc (-1) 1) uLow)
    (hlocalvLow : LocallyLipschitzOn (Icc (-1) 1) vLow)
    (hlocaluR : LocallyLipschitzOn (Icc (-1) 1) uR)
    (hlocalvR : LocallyLipschitzOn (Icc (-1) 1) vR)
    (a b theta lowComplement tailComplement : ℝ)
    (hab : a ^ 2 + b ^ 2 ≤ 1) (htheta : 0 ≤ theta)
    (huRaw : centeredRawLogEnergy (uLow + uR) =
      centeredRawLogEnergy uLow + centeredRawLogEnergy uR)
    (hvRaw : centeredRawLogEnergy (vLow + vR) =
      centeredRawLogEnergy vLow + centeredRawLogEnergy vR)
    (huOrth : (∫ x : ℝ in -1..1, uLow x * uR x) = 0)
    (hvOrth : (∫ x : ℝ in -1..1, vLow x * vR x) = 0)
    (hlowComplement : 0 ≤ lowComplement)
    (htailComplement : 0 ≤ tailComplement)
    (hlowRetains :
      theta * ((1 / 2 : ℝ) *
          factorTwoPhaseSingularWeightedEnergy uLow vLow a b) +
        lowComplement ≤ factorTwoEndpointChannelPhase uLow vLow a b)
    (htailRetains :
      theta * ((1 / 2 : ℝ) *
          factorTwoPhaseSingularWeightedEnergy uR vR a b) +
        tailComplement ≤ factorTwoEndpointChannelPhase uR vR a b)
    (hremaining :
      (factorTwoEndpointLowTailMixed uLow uR vLow vR a b -
          theta * factorTwoPhasePotentialPoleMixed
            uLow vLow uR vR a b) ^ 2 ≤
        lowComplement * tailComplement) :
    factorTwoEndpointLowTailMixed uLow uR vLow vR a b ^ 2 ≤
      factorTwoEndpointChannelPhase uLow vLow a b *
        factorTwoEndpointChannelPhase uR vR a b := by
  exact
    factorTwoEndpointLowTailMixed_sq_le_of_asymmetrically_retained_singular
      uLow vLow uR vR huLow hvLow huR hvR
      hlocaluLow hlocalvLow hlocaluR hlocalvR
      a b theta theta theta lowComplement tailComplement
      hab htheta htheta (by simp [pow_two])
      huRaw hvRaw huOrth hvOrth hlowComplement htailComplement
      hlowRetains htailRetains hremaining

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseRetainedSingularSchurStructural

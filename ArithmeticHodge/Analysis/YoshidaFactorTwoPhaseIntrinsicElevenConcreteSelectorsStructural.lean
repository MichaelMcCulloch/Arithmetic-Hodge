import ArithmeticHodge.Analysis.YoshidaEndpointEvenTailRepresenter
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenConstrainedWeightedDualStructural

set_option autoImplicit false

open Complex MeasureTheory Polynomial Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenConcreteSelectorsStructural

open ShiftedLegendreLogEnergyOrthogonalProjection
open UnitIntervalLogEnergyAffine
open YoshidaEndpointEvenConstantCross
open YoshidaEndpointEvenFullPolarization
open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointPotentialBound
open YoshidaEndpointPotentialIntegrable
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseIntrinsicElevenConstrainedWeightedDualStructural
open YoshidaFactorTwoPhaseIntrinsicHigherResidual
open YoshidaFactorTwoPhaseIntrinsicNineFullMixedDecompositionStructural

noncomputable section

/-!
# Concrete selector support at the eleventh gap

The complete low--tail phase representers have not yet been exposed by the
production decomposition.  This module isolates the part which can already
be made completely concrete: the clean endpoint functional of an arbitrary
transported polynomial.  The formula works for both reflection parities.

The last two lemmas record the structural selector operation used by the
gap-eleven weighted dual.  Adding a transported polynomial to a representer
and to its selector leaves the residual, and hence its weighted cost,
*exactly* unchanged.  Thus polynomial cancellation is performed before any
estimate and does not enumerate tail modes.
-/

/-- The clean endpoint survivor representer of a transported polynomial.

The raw-log and ordinary-mass rows are absent: both are killed exactly by a
moment gap above the degree of `p`.  The remaining potential, regular-kernel,
and hyperbolic rows are retained with their signs.  Unlike the historical
even-tail representer, this definition includes the odd `sinh` rank and is
therefore valid for either parity. -/
def factorTwoIntrinsicElevenCleanSurvivorRepresenter
    (p : ℝ[X]) (x : ℝ) : ℝ :=
  yoshidaEndpointPotential x * centeredPolynomialLift p x -
    yoshidaEndpointA *
      yoshidaEndpointEvenRegularRepresenter (centeredPolynomialLift p) x +
    2 * yoshidaEndpointA *
      (yoshidaEndpointCoshMoment (centeredPolynomialLift p) *
          Real.cosh (yoshidaEndpointA * x / 2) -
        yoshidaEndpointSinhMoment (centeredPolynomialLift p) *
          Real.sinh (yoshidaEndpointA * x / 2))

/-- The canonical first selector for the clean survivor is the low
polynomial which generated it. -/
def factorTwoIntrinsicElevenCleanSelector (p : ℝ[X]) : ℝ[X] := p

@[simp] theorem factorTwoIntrinsicElevenCleanSelector_natDegree_lt
    (p : ℝ[X]) (hp : p.natDegree < 11) :
    (factorTwoIntrinsicElevenCleanSelector p).natDegree < 11 := by
  exact hp

/-- Pointwise form of the clean selector residual.  This is the genuinely
nonpolynomial quantity charged to the multiplication reserve. -/
theorem factorTwoIntrinsicElevenCleanSelectorResidual_eq
    (p : ℝ[X]) (x : ℝ) :
    factorTwoIntrinsicElevenSelectorResidual
        (factorTwoIntrinsicElevenCleanSurvivorRepresenter p)
        (factorTwoIntrinsicElevenCleanSelector p) x =
      (yoshidaEndpointPotential x - 1) * centeredPolynomialLift p x -
        yoshidaEndpointA *
          yoshidaEndpointEvenRegularRepresenter
            (centeredPolynomialLift p) x +
        2 * yoshidaEndpointA *
          (yoshidaEndpointCoshMoment (centeredPolynomialLift p) *
              Real.cosh (yoshidaEndpointA * x / 2) -
            yoshidaEndpointSinhMoment (centeredPolynomialLift p) *
              Real.sinh (yoshidaEndpointA * x / 2)) := by
  unfold factorTwoIntrinsicElevenSelectorResidual
    factorTwoIntrinsicElevenCleanSurvivorRepresenter
    factorTwoIntrinsicElevenCleanSelector
  ring

/-- The clean selector dual is exactly the weighted norm of the displayed
survivor.  No triangle inequality has been introduced. -/
theorem factorTwoIntrinsicElevenCleanSelectorDual_eq
    (W : ℝ → ℝ) (p : ℝ[X]) :
    factorTwoIntrinsicElevenSelectorDual W
        (factorTwoIntrinsicElevenCleanSurvivorRepresenter p)
        (factorTwoIntrinsicElevenCleanSelector p) =
      ∫ x : ℝ in -1..1,
        (((yoshidaEndpointPotential x - 1) * centeredPolynomialLift p x -
            yoshidaEndpointA *
              yoshidaEndpointEvenRegularRepresenter
                (centeredPolynomialLift p) x +
            2 * yoshidaEndpointA *
              (yoshidaEndpointCoshMoment (centeredPolynomialLift p) *
                  Real.cosh (yoshidaEndpointA * x / 2) -
                yoshidaEndpointSinhMoment (centeredPolynomialLift p) *
                  Real.sinh (yoshidaEndpointA * x / 2))) ^ 2) / W x := by
  unfold factorTwoIntrinsicElevenSelectorDual
  apply intervalIntegral.integral_congr
  intro x _hx
  dsimp only
  rw [factorTwoIntrinsicElevenCleanSelectorResidual_eq]

/-- Exact clean low--tail representer identity at the eleventh moment gap.

This proof uses the all-degree logarithmic eigenidentity to remove the raw
logarithmic cross, moment orthogonality to remove the mass cross, and Fubini
for the bounded regular kernel.  It is a structural identity, not a finite
mode calculation. -/
theorem factorTwoCenteredCleanPolarization_centeredPolynomialLift_tail_eq
    (p : ℝ[X]) (r : ℝ → ℝ)
    (hr : Continuous r)
    (hlocal : LocallyLipschitzOn (Icc (-1) 1) r)
    (hlow : centeredLegendreMomentsVanishBelow r 11)
    (hp : p.natDegree < 11) :
    factorTwoCenteredCleanPolarization (centeredPolynomialLift p) r =
      ∫ x : ℝ in -1..1,
        factorTwoIntrinsicElevenCleanSurvivorRepresenter p x * r x := by
  let q : ℝ → ℝ := centeredPolynomialLift p
  have hq : Continuous q := by
    have hpcont : Continuous (fun x : ℝ ↦ p.eval x) := by
      rw [continuous_iff_continuousAt]
      intro x
      exact (p.hasDerivAt x).continuousAt
    dsimp only [q, centeredPolynomialLift]
    exact hpcont.comp ((continuous_id.add continuous_const).div_const 2)
  have hraw : centeredRawLogEnergy (q + r) =
      centeredRawLogEnergy q + centeredRawLogEnergy r := by
    simpa only [q] using
      centeredRawLogEnergy_centeredPolynomialLift_add_tail
        p r hr hlocal hlow hp
  have hmassZero : (∫ x : ℝ in -1..1, q x * r x) = 0 := by
    simpa only [q] using
      intervalIntegral_centeredPolynomialLift_mul_tail_eq_zero
        p r hr hlow hp
  have hpotential := integral_endpointPotential_add_sq q r hq hr
  have hmass := integral_add_sq q r hq hr
  have hregular := yoshidaEndpointRegularQuadratic_add_ofReal q r hq hr
  have hhyper := yoshidaEndpointHyperbolicQuadratic_add_ofReal q r hq hr
  have hregularPair :=
    yoshidaEndpointRegularRealBilinear_eq_integral_representer q r hq hr
  have hregularPair' :
      (yoshidaEndpointRegularRealBilinear q r).re +
          (yoshidaEndpointRegularRealBilinear r q).re =
        2 * ∫ x : ℝ in -1..1,
          yoshidaEndpointEvenRegularRepresenter q x * r x := by
    simpa only [add_re] using hregularPair
  have hpolar :
      factorTwoCenteredCleanPolarization q r =
        (∫ x : ℝ in -1..1,
            yoshidaEndpointPotential x * q x * r x) -
          yoshidaEndpointA *
            (∫ x : ℝ in -1..1,
              yoshidaEndpointEvenRegularRepresenter q x * r x) +
          2 * yoshidaEndpointA *
            (yoshidaEndpointCoshMoment q * yoshidaEndpointCoshMoment r -
              yoshidaEndpointSinhMoment q * yoshidaEndpointSinhMoment r) := by
    unfold factorTwoCenteredCleanPolarization
    change
      (yoshidaEndpointOddCleanQuadratic (q + r) -
          yoshidaEndpointOddCleanQuadratic q -
          yoshidaEndpointOddCleanQuadratic r) / 2 = _
    unfold yoshidaEndpointOddCleanQuadratic
    dsimp only
    rw [hraw]
    simp only [Pi.add_apply]
    rw [hpotential, hmass, hmassZero, hregular, hhyper]
    simp only [add_re]
    rw [hregularPair']
    ring
  have hV : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * q x * r x)
      volume (-1) 1 := intervalIntegrable_endpointPotential_mul q r hq hr
  have hR : IntervalIntegrable
      (fun x : ℝ ↦
        yoshidaEndpointEvenRegularRepresenter q x * r x)
      volume (-1) 1 := intervalIntegrable_regularRepresenter_mul q r hq hr
  have hC : IntervalIntegrable
      (fun x : ℝ ↦ Real.cosh (yoshidaEndpointA * x / 2) * r x)
      volume (-1) 1 := (by fun_prop : Continuous
        (fun x : ℝ ↦ Real.cosh (yoshidaEndpointA * x / 2) * r x))
          |>.intervalIntegrable (-1) 1
  have hS : IntervalIntegrable
      (fun x : ℝ ↦ Real.sinh (yoshidaEndpointA * x / 2) * r x)
      volume (-1) 1 := (by fun_prop : Continuous
        (fun x : ℝ ↦ Real.sinh (yoshidaEndpointA * x / 2) * r x))
          |>.intervalIntegrable (-1) 1
  have hRank : IntervalIntegrable
      (fun x : ℝ ↦
        yoshidaEndpointCoshMoment q *
            (Real.cosh (yoshidaEndpointA * x / 2) * r x) -
          yoshidaEndpointSinhMoment q *
            (Real.sinh (yoshidaEndpointA * x / 2) * r x))
      volume (-1) 1 :=
    (hC.const_mul (yoshidaEndpointCoshMoment q)).sub
      (hS.const_mul (yoshidaEndpointSinhMoment q))
  have hpair :
      (∫ x : ℝ in -1..1,
        factorTwoIntrinsicElevenCleanSurvivorRepresenter p x * r x) =
        (∫ x : ℝ in -1..1,
            yoshidaEndpointPotential x * q x * r x) -
          yoshidaEndpointA *
            (∫ x : ℝ in -1..1,
              yoshidaEndpointEvenRegularRepresenter q x * r x) +
          2 * yoshidaEndpointA *
            (yoshidaEndpointCoshMoment q * yoshidaEndpointCoshMoment r -
              yoshidaEndpointSinhMoment q * yoshidaEndpointSinhMoment r) := by
    rw [show (fun x : ℝ ↦
        factorTwoIntrinsicElevenCleanSurvivorRepresenter p x * r x) =
      fun x ↦
        (yoshidaEndpointPotential x * q x * r x -
          yoshidaEndpointA *
            (yoshidaEndpointEvenRegularRepresenter q x * r x)) +
        2 * yoshidaEndpointA *
          (yoshidaEndpointCoshMoment q *
              (Real.cosh (yoshidaEndpointA * x / 2) * r x) -
            yoshidaEndpointSinhMoment q *
              (Real.sinh (yoshidaEndpointA * x / 2) * r x)) by
      funext x
      dsimp only [q]
      unfold factorTwoIntrinsicElevenCleanSurvivorRepresenter
      ring,
      intervalIntegral.integral_add
        (hV.sub (hR.const_mul yoshidaEndpointA))
        (hRank.const_mul (2 * yoshidaEndpointA)),
      intervalIntegral.integral_sub hV (hR.const_mul yoshidaEndpointA),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub
        (hC.const_mul (yoshidaEndpointCoshMoment q))
        (hS.const_mul (yoshidaEndpointSinhMoment q)),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    unfold yoshidaEndpointCoshMoment yoshidaEndpointSinhMoment
    ring
  change factorTwoCenteredCleanPolarization q r = _
  rw [hpolar, hpair]

/-- The two concrete clean survivor functions are exactly the `FE/FO`
pairing for the clean part of the production low--tail block. -/
theorem factorTwoIntrinsicElevenCleanMixedPairing_eq
    (pE pO : ℝ[X]) (e o : ℝ → ℝ)
    (he : Continuous e) (ho : Continuous o)
    (heLocal : LocallyLipschitzOn (Icc (-1) 1) e)
    (hoLocal : LocallyLipschitzOn (Icc (-1) 1) o)
    (heLow : centeredLegendreMomentsVanishBelow e 11)
    (hoLow : centeredLegendreMomentsVanishBelow o 11)
    (hpE : pE.natDegree < 11) (hpO : pO.natDegree < 11) :
    factorTwoIntrinsicElevenMixedPairing
        (factorTwoIntrinsicElevenCleanSurvivorRepresenter pE)
        (factorTwoIntrinsicElevenCleanSurvivorRepresenter pO) e o =
      factorTwoCenteredCleanPolarization (centeredPolynomialLift pE) e +
        factorTwoCenteredCleanPolarization (centeredPolynomialLift pO) o := by
  unfold factorTwoIntrinsicElevenMixedPairing
  rw [factorTwoCenteredCleanPolarization_centeredPolynomialLift_tail_eq
      pE e he heLocal heLow hpE,
    factorTwoCenteredCleanPolarization_centeredPolynomialLift_tail_eq
      pO o ho hoLocal hoLow hpO]

/-! ## Polynomial translation of selectors -/

/-- Adding the same transported polynomial to the representer and selector
does not change the residual. -/
theorem factorTwoIntrinsicElevenSelectorResidual_add_polynomial
    (F : ℝ → ℝ) (p q : ℝ[X]) (x : ℝ) :
    factorTwoIntrinsicElevenSelectorResidual
        (fun y ↦ F y + centeredPolynomialLift q y) (p + q) x =
      factorTwoIntrinsicElevenSelectorResidual F p x := by
  unfold factorTwoIntrinsicElevenSelectorResidual centeredPolynomialLift
  simp only [Polynomial.eval_add]
  ring

/-- Consequently the one-channel weighted dual cost is invariant under the
same polynomial translation. -/
theorem factorTwoIntrinsicElevenSelectorDual_add_polynomial
    (W F : ℝ → ℝ) (p q : ℝ[X]) :
    factorTwoIntrinsicElevenSelectorDual W
        (fun x ↦ F x + centeredPolynomialLift q x) (p + q) =
      factorTwoIntrinsicElevenSelectorDual W F p := by
  unfold factorTwoIntrinsicElevenSelectorDual
  apply intervalIntegral.integral_congr
  intro x _hx
  dsimp only
  rw [factorTwoIntrinsicElevenSelectorResidual_add_polynomial]

/-- Degree below eleven is preserved when two structural selectors are
assembled. -/
theorem natDegree_add_lt_eleven
    (p q : ℝ[X]) (hp : p.natDegree < 11) (hq : q.natDegree < 11) :
    (p + q).natDegree < 11 := by
  exact lt_of_le_of_lt (natDegree_add_le p q) (max_lt hp hq)

/-- Two-channel form of polynomial-translation invariance. -/
theorem factorTwoIntrinsicElevenConstrainedSelectorDual_add_polynomials
    (FE FO : ℝ → ℝ) (pE pO qE qO : ℝ[X]) :
    factorTwoIntrinsicElevenConstrainedSelectorDual
        (fun x ↦ FE x + centeredPolynomialLift qE x)
        (fun x ↦ FO x + centeredPolynomialLift qO x)
        (pE + qE) (pO + qO) =
      factorTwoIntrinsicElevenConstrainedSelectorDual FE FO pE pO := by
  unfold factorTwoIntrinsicElevenConstrainedSelectorDual
  rw [factorTwoIntrinsicElevenSelectorDual_add_polynomial,
    factorTwoIntrinsicElevenSelectorDual_add_polynomial]

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenConcreteSelectorsStructural

import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCoupledRankLimit
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseFullProfile

set_option autoImplicit false

open MeasureTheory Real

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCoupledCleanReduction

noncomputable section

open CenteredEndpointCorrelation
open YoshidaEndpointHyperbolicBound
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointChannelRadius
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoPhaseCoupledRankLimit
open YoshidaFactorTwoPhaseEnvelope
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseSymmetricCoercivity

/-!
# Coupled-rank reduction of the complete endpoint phase

The archimedean symmetric and alternating terms are kept in their common
hyperbolic-rank expansion.  The two retained prime atoms are likewise kept as
one phase correlation.  Consequently the only remaining sufficient estimate
is a comparison between the clean diagonal and a manifestly positive rank
energy plus the sharp retained-prime mass budget.
-/

/-- The phase-independent mass budget for the two retained prime atoms. -/
def factorTwoCoupledPrimeMassBudget (e o : ℝ → ℝ) : ℝ :=
  (Real.log 2 / Real.sqrt 2 +
      (Real.log 3 / Real.sqrt 3) / 2) *
    ((∫ x : ℝ in -1..1, e x ^ 2) +
      ∫ x : ℝ in -1..1, o x ^ 2)

/-- The exact complete endpoint phase is bounded below by the clean diagonal
minus the coupled archimedean rank energy and the phase-dependent retained-
prime mass budget.  No symmetric/alternating triangle split occurs in the
archimedean term. -/
theorem factorTwoEndpointChannelPhase_lower_by_coupledRank
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o)
    (heven : Function.Even e) (hodd : Function.Odd o)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    factorTwoEndpointChannelCleanSum e o -
        (factorTwoCoupledRankEnergy e o +
          ((Real.log 2 / Real.sqrt 2) * |a| +
              (Real.log 3 / Real.sqrt 3) / 2) *
            ((∫ x : ℝ in -1..1, e x ^ 2) +
              ∫ x : ℝ in -1..1, o x ^ 2)) ≤
      factorTwoEndpointChannelPhase e o a b := by
  let M : ℝ := (∫ x : ℝ in -1..1, e x ^ 2) +
    ∫ x : ℝ in -1..1, o x ^ 2
  let D : ℝ :=
    factorTwoCenteredCrossCorrelation o e
        (factorTwoPrimeShift / yoshidaEndpointA) -
      factorTwoCenteredCrossCorrelation e o
        (factorTwoPrimeShift / yoshidaEndpointA)
  let Aalt : ℝ := yoshidaEndpointA *
    ∫ t : ℝ in 0..2,
      factorTwoAntisymmetricWeight (yoshidaEndpointA * t) *
        (factorTwoCenteredCrossCorrelation o e t -
          factorTwoCenteredCrossCorrelation e o t)
  let X : ℝ :=
    a * (factorTwoCenteredArchBlock e + factorTwoCenteredArchBlock o) +
      b * Aalt
  let Y : ℝ :=
    -a * (factorTwoCenteredPrimeBlock e +
      factorTwoCenteredPrimeBlock o) -
      b * (Real.log 3 / Real.sqrt 3) * D
  have harchAbs := abs_factorTwoCoupledRankPhase_le_energy
    e o hec hoc heven hodd a b hab
  have harch : -factorTwoCoupledRankEnergy e o ≤ X := by
    change |X| ≤ factorTwoCoupledRankEnergy e o at harchAbs
    nlinarith [neg_abs_le X]
  have hprime := phase_prime_terms_lower e o hec hoc a b hab
  have hprimeEq :
      -((Real.log 2 / Real.sqrt 2) * a *
            (centeredEndpointCorrelation e 0 +
              centeredEndpointCorrelation o 0)) -
          (Real.log 3 / Real.sqrt 3) *
            factorTwoCenteredPhaseCorrelation e o a b
              (factorTwoPrimeShift / yoshidaEndpointA) = Y := by
    dsimp only [Y, D]
    unfold factorTwoCenteredPrimeBlock
      factorTwoCenteredPhaseCorrelation
    rw [centeredEndpointCorrelation_zero,
      centeredEndpointCorrelation_zero]
    ring
  rw [hprimeEq] at hprime
  change (-(Real.log 2 / Real.sqrt 2 * |a| +
      (Real.log 3 / Real.sqrt 3) / 2)) * M ≤ Y at hprime
  have hphaseEq :
      factorTwoEndpointChannelPhase e o a b =
        factorTwoEndpointChannelCleanSum e o + X + Y := by
    unfold factorTwoEndpointChannelPhase
      factorTwoEndpointChannelSymmetricSum
    rw [symmetricPerturbation_eq_arch_sub_primeBlock,
      symmetricPerturbation_eq_arch_sub_primeBlock]
    unfold factorTwoCenteredAlternatingCoupling
    dsimp only [X, Y, Aalt, D]
    ring
  rw [hphaseEq]
  nlinarith

/-- A single phase-independent clean domination proves the complete endpoint
channel for every phase in the closed disk. -/
theorem factorTwoEndpointChannelPhase_nonneg_of_coupledRank_domination
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o)
    (heven : Function.Even e) (hodd : Function.Odd o)
    (hdom : factorTwoCoupledRankEnergy e o +
        factorTwoCoupledPrimeMassBudget e o ≤
      factorTwoEndpointChannelCleanSum e o)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    0 ≤ factorTwoEndpointChannelPhase e o a b := by
  have ha : |a| ≤ 1 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg b, sq_nonneg (a + 1),
      sq_nonneg (a - 1)]
  have hM : 0 ≤
      (∫ x : ℝ in -1..1, e x ^ 2) +
        ∫ x : ℝ in -1..1, o x ^ 2 := by
    apply add_nonneg
    · exact intervalIntegral.integral_nonneg (by norm_num)
        (fun x _hx ↦ sq_nonneg (e x))
    · exact intervalIntegral.integral_nonneg (by norm_num)
        (fun x _hx ↦ sq_nonneg (o x))
  have halpha : 0 ≤ Real.log 2 / Real.sqrt 2 := by positivity
  have hbudget :
      ((Real.log 2 / Real.sqrt 2) * |a| +
          (Real.log 3 / Real.sqrt 3) / 2) *
          ((∫ x : ℝ in -1..1, e x ^ 2) +
            ∫ x : ℝ in -1..1, o x ^ 2) ≤
        factorTwoCoupledPrimeMassBudget e o := by
    unfold factorTwoCoupledPrimeMassBudget
    apply mul_le_mul_of_nonneg_right _ hM
    exact add_le_add
      (by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left ha halpha) le_rfl
  have hlower := factorTwoEndpointChannelPhase_lower_by_coupledRank
    e o hec hoc heven hodd a b hab
  have hdom' :
      factorTwoCoupledRankEnergy e o +
          ((Real.log 2 / Real.sqrt 2) * |a| +
              (Real.log 3 / Real.sqrt 3) / 2) *
            ((∫ x : ℝ in -1..1, e x ^ 2) +
              ∫ x : ℝ in -1..1, o x ^ 2) ≤
        factorTwoEndpointChannelCleanSum e o := by
    exact (add_le_add le_rfl hbudget).trans hdom
  nlinarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCoupledCleanReduction

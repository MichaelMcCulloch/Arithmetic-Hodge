import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCoupledRankLimit
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseDiskSchur

set_option autoImplicit false

open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseSignedRankPrime

noncomputable section

open CenteredEndpointCorrelation
open YoshidaEndpointHyperbolicBound
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointChannelRadius
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoPhaseCoupledRankLimit
open YoshidaFactorTwoPhaseDiskSchur
open YoshidaFactorTwoPhaseEnvelope
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseRankLimit
open YoshidaFactorTwoPhaseSymmetricCoercivity
open YoshidaRenormalizedGeometricKernel

/-!
# Signed rank-and-prime normal form

The complete phase is expanded into its growing hyperbolic rank, its genuine
infinite decaying-rank sum, and the two retained prime correlations.  No
absolute value is taken.  In particular, the symmetric phase coordinate has
opposite signs on the growing and decaying ranks, while the alternating
coordinate remains coupled rank by rank.
-/

/-- One decaying hyperbolic rank of the complete signed phase. -/
def factorTwoSignedCoupledRank
    (e o : ℝ → ℝ) (a b : ℝ) (m : ℕ) : ℝ :=
  Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
    ((-a) *
        (centeredCoshMoment e
              (yoshidaEndpointA * oddRate (m + 1)) ^ 2 -
          centeredSinhMoment o
              (yoshidaEndpointA * oddRate (m + 1)) ^ 2) +
      2 * b *
        centeredCoshMoment e
          (yoshidaEndpointA * oddRate (m + 1)) *
        centeredSinhMoment o
          (yoshidaEndpointA * oddRate (m + 1)))

/-- The signed decaying-rank family is absolutely summable. -/
theorem summable_factorTwoSignedCoupledRank
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o)
    (heven : Function.Even e) (hodd : Function.Odd o)
    (a b : ℝ) :
    Summable (factorTwoSignedCoupledRank e o a b) := by
  let qe : ℕ → ℝ := fun m ↦
    Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
      centeredCoshMoment e
        (yoshidaEndpointA * oddRate (m + 1)) ^ 2
  let qo : ℕ → ℝ := fun m ↦
    Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
      centeredSinhMoment o
        (yoshidaEndpointA * oddRate (m + 1)) ^ 2
  let qj : ℕ → ℝ := fun m ↦
    2 * Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
      centeredCoshMoment e
        (yoshidaEndpointA * oddRate (m + 1)) *
      centeredSinhMoment o
        (yoshidaEndpointA * oddRate (m + 1))
  have he : Summable qe := by
    simpa only [qe] using
      (hasSum_factorTwoCenteredArch_evenRankSquares e hec heven).summable
  have ho : Summable qo := by
    simpa only [qo] using
      (hasSum_factorTwoCenteredArch_oddRankSquares o hoc hodd).summable
  have hj : Summable qj := by
    simpa only [qj] using
      summable_factorTwoCenteredAlternatingRankProducts
        e o hec hoc heven hodd
  have hsum : Summable (fun m ↦ (-a) * qe m + a * qo m + b * qj m) :=
    ((he.mul_left (-a)).add (ho.mul_left a)).add (hj.mul_left b)
  convert hsum using 1
  funext m
  unfold factorTwoSignedCoupledRank
  dsimp only [qe, qo, qj]
  ring

private theorem tsum_factorTwoSignedCoupledRank_eq
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o)
    (heven : Function.Even e) (hodd : Function.Odd o)
    (a b : ℝ) :
    (∑' m : ℕ, factorTwoSignedCoupledRank e o a b m) =
      (-a) *
          (∑' m : ℕ,
            Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
              centeredCoshMoment e
                (yoshidaEndpointA * oddRate (m + 1)) ^ 2) +
        a *
          (∑' m : ℕ,
            Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
              centeredSinhMoment o
                (yoshidaEndpointA * oddRate (m + 1)) ^ 2) +
        b *
          (∑' m : ℕ,
            2 * Real.exp
                (-2 * yoshidaEndpointA * oddRate (m + 1)) *
              centeredCoshMoment e
                (yoshidaEndpointA * oddRate (m + 1)) *
              centeredSinhMoment o
                (yoshidaEndpointA * oddRate (m + 1))) := by
  let qe : ℕ → ℝ := fun m ↦
    Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
      centeredCoshMoment e
        (yoshidaEndpointA * oddRate (m + 1)) ^ 2
  let qo : ℕ → ℝ := fun m ↦
    Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
      centeredSinhMoment o
        (yoshidaEndpointA * oddRate (m + 1)) ^ 2
  let qj : ℕ → ℝ := fun m ↦
    2 * Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
      centeredCoshMoment e
        (yoshidaEndpointA * oddRate (m + 1)) *
      centeredSinhMoment o
        (yoshidaEndpointA * oddRate (m + 1))
  have he : Summable qe := by
    simpa only [qe] using
      (hasSum_factorTwoCenteredArch_evenRankSquares e hec heven).summable
  have ho : Summable qo := by
    simpa only [qo] using
      (hasSum_factorTwoCenteredArch_oddRankSquares o hoc hodd).summable
  have hj : Summable qj := by
    simpa only [qj] using
      summable_factorTwoCenteredAlternatingRankProducts
        e o hec hoc heven hodd
  have hpoint : factorTwoSignedCoupledRank e o a b =
      fun m ↦ (-a) * qe m + a * qo m + b * qj m := by
    funext m
    unfold factorTwoSignedCoupledRank
    dsimp only [qe, qo, qj]
    ring
  rw [hpoint,
    ((he.mul_left (-a)).add (ho.mul_left a)).tsum_add (hj.mul_left b),
    (he.mul_left (-a)).tsum_add (ho.mul_left a)]
  simp only [tsum_mul_left]
  dsimp only [qe, qo, qj]

/-- Exact complete phase normal form with signed growing/decaying ranks and
the two retained prime atoms kept as complete phase correlations. -/
theorem factorTwoEndpointChannelPhase_eq_signedRankPrime
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o)
    (heven : Function.Even e) (hodd : Function.Odd o)
    (a b : ℝ) :
    factorTwoEndpointChannelPhase e o a b =
      factorTwoEndpointChannelCleanSum e o +
        yoshidaEndpointA *
          (Real.exp yoshidaEndpointA *
              (a *
                  (centeredCoshMoment e (yoshidaEndpointA / 2) ^ 2 -
                    centeredSinhMoment o (yoshidaEndpointA / 2) ^ 2) +
                2 * b *
                  centeredCoshMoment e (yoshidaEndpointA / 2) *
                  centeredSinhMoment o (yoshidaEndpointA / 2)) +
            ∑' m : ℕ, factorTwoSignedCoupledRank e o a b m) -
        ((Real.log 2 / Real.sqrt 2) *
            factorTwoCenteredPhaseCorrelation e o a b 0 +
          (Real.log 3 / Real.sqrt 3) *
            factorTwoCenteredPhaseCorrelation e o a b
              (factorTwoPrimeShift / yoshidaEndpointA)) := by
  have heArch := factorTwoCenteredArchBlock_eq_evenRankSquares
    e hec heven
  have hoArch := factorTwoCenteredArchBlock_eq_oddRankSquares
    o hoc hodd
  have hjArch := factorTwoCenteredAlternatingArch_eq_rankProducts
    e o hec hoc heven hodd
  have htail := tsum_factorTwoSignedCoupledRank_eq
    e o hec hoc heven hodd a b
  unfold factorTwoEndpointChannelPhase
    factorTwoEndpointChannelSymmetricSum
  rw [symmetricPerturbation_eq_arch_sub_primeBlock,
    symmetricPerturbation_eq_arch_sub_primeBlock,
    heArch, hoArch]
  unfold factorTwoCenteredAlternatingCoupling
  rw [hjArch, htail, factorTwoCenteredPhaseCorrelation_zero]
  unfold factorTwoCenteredPrimeBlock
    factorTwoCenteredPhaseCorrelation
  ring

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseSignedRankPrime

import ArithmeticHodge.Analysis.MultiplicativeWeilFourCellRealRescaleStructural
import ArithmeticHodge.Analysis.YoshidaGeneralEndpointPhysicalRealQuadraticStructural

set_option autoImplicit false

open Complex Real Set
open scoped ContDiff

namespace ArithmeticHodge.Analysis.MultiplicativeWeilFourCellRealDiagonalStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilFourCellRealRescaleStructural
open MultiplicativeWeilFourCellSingleProfileStructural
open MultiplicativeWeilMonotoneFourCellPrimeGeometryStructural
open YoshidaEndpointScaledCorrelation
open YoshidaFourCellEndpointVarianceStructural
open YoshidaGeneralEndpointPhysicalRealQuadraticStructural
open YoshidaSectionSixAnalytic

/-!
# Exact real diagonal for the production four-cell profile

The common four-cell crop is smooth after its endpoint-zero extension.  Its
complete local critical diagonal therefore has the arbitrary-halfwidth
physical expression, with no coercive relaxation or discarded kernel term.
-/

/-- The normalized complete four-cell profile retains one full derivative. -/
theorem fourCellNormalizedRealProfile_contDiff
    (parent : BombieriTest) (k : ℤ) :
    ContDiff ℝ 1 (fourCellNormalizedRealProfile parent k) := by
  have hsupported :=
    fourCellWholeCentered_criticalPullbackSupported parent k
  have hscale : ContDiff ℝ 1
      (fun x : ℝ ↦ fourCellWholeHalfWidth k * x) := by
    fun_prop
  have hpullback : ContDiff ℝ 1
      (fun x : ℝ ↦
        (fourCellWholeCentered parent k).logarithmicPullbackSchwartz (1 / 2)
          (fourCellWholeHalfWidth k * x)) :=
    ((fourCellWholeCentered parent k).logarithmicPullbackSchwartz (1 / 2)).smooth 1
      |>.comp hscale
  unfold fourCellNormalizedRealProfile centeredRescale
  rw [show (fourCellWholeProfile parent k : ℝ → ℂ) =
      (fourCellWholeCentered parent k).logarithmicPullbackSchwartz (1 / 2) by
    exact yoshidaCriticalPullbackCrop_eq_logarithmicPullbackSchwartz hsupported]
  exact Complex.reCLM.contDiff.comp hpullback

/-- The normalized complete four-cell profile is smooth, hence locally
Lipschitz on the centered physical interval. -/
theorem fourCellNormalizedRealProfile_locallyLipschitzOn
    (parent : BombieriTest) (k : ℤ) :
    LocallyLipschitzOn (Icc (-1) 1)
      (fourCellNormalizedRealProfile parent k) := by
  exact (fourCellNormalizedRealProfile_contDiff parent k).contDiffOn
    |>.locallyLipschitzOn (convex_Icc (-1) 1)

/-- The local critical diagonal of a conjugation-fixed production four-cell
block is exactly the halfwidth times the centered physical quadratic. -/
theorem fourCell_clippedLocalCritical_re_eq_centeredPhysical
    (parent : BombieriTest) (k : ℤ)
    (hparent : bombieriConjugateTest parent = parent) :
    (yoshidaClippedLocalCriticalForm (fourCellWholeHalfWidth k)
      (fourCellWholeHalfWidth_pos k)
      (fourCellWholeProfile parent k)
      (fourCellWholeProfile parent k)).re =
        fourCellWholeHalfWidth k *
          centeredClippedPhysicalQuadratic (fourCellWholeHalfWidth k)
            (fourCellNormalizedRealProfile parent k) := by
  let f := fourCellWholeProfile parent k
  have hends := fourCellWholeProfile_endpoints_zero parent k
  have hreal : ∀ x ∈ Icc (-fourCellWholeHalfWidth k)
      (fourCellWholeHalfWidth k), f x = ((f x).re : ℂ) := by
    intro x _hx
    apply Complex.ext
    · simp
    · simp only [Complex.ofReal_im]
      exact fourCellWholeProfile_im_eq_zero parent k hparent x
  have hdiag :=
    clippedCriticalFormValue_eq_centeredClippedPhysicalQuadratic_of_endpoints_zero
      (fourCellWholeHalfWidth_pos k) f hreal hends.1 hends.2
      (fourCellNormalizedRealProfile_locallyLipschitzOn parent k)
  simpa only [clippedCriticalFormValue, f, fourCellNormalizedRealProfile]
    using hdiag

/-- Exact normalized four-cell target: the complete Bombieri value is the
physical quadratic minus the prime-two endpoint pairing of the same real
profile, all at one common positive scale. -/
theorem bombieriFunctional_fourBlock_re_eq_centeredPhysical_sub_pairing
    (parent : BombieriTest) (k : ℤ)
    (hparent : bombieriConjugateTest parent = parent) :
    (bombieriFunctional
      (bombieriQuadraticTest (monotoneQuarterFourBlock parent k))).re =
        fourCellWholeHalfWidth k *
          (centeredClippedPhysicalQuadratic (fourCellWholeHalfWidth k)
              (fourCellNormalizedRealProfile parent k) -
            Real.sqrt 2 * Real.log 2 *
              fourCellEndpointPairing
                (fourCellNormalizedRealProfile parent k)) := by
  rw [bombieriFunctional_fourBlock_re_eq_singleProfile,
    fourCell_clippedLocalCritical_re_eq_centeredPhysical parent k hparent,
    fourCellWholeProfile_crossCorrelation_neg_log_re_eq_normalizedPairing
      parent k hparent]
  ring

end

end ArithmeticHodge.Analysis.MultiplicativeWeilFourCellRealDiagonalStructural

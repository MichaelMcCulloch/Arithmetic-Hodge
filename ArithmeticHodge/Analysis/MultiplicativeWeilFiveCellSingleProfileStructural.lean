import ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellResidualFactorTwoStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilFourCellRealDiagonalStructural

set_option autoImplicit false

open Complex MeasureTheory Real Set
open scoped ContDiff

namespace ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellSingleProfileStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilAllLengthEndpointReserveStructural
open MultiplicativeWeilFiveCellResidualFactorTwoStructural
open MultiplicativeWeilFourCellEndpointStripStructural
open MultiplicativeWeilMinimalNegativeBlockStructural
open MultiplicativeWeilMonotonePrimeAtomAggregateObstructionStructural
open MultiplicativeWeilMonotoneQuarterPartitionStructural
open MultiplicativeWeilQuarterLogLatticePartitionStructural
open YoshidaCauchyPairing
open YoshidaCriticalLogCorrelation
open YoshidaEndpointScaledCorrelation
open YoshidaFactorTwoCrossDistribution
open YoshidaFactorTwoEndpointClean
open YoshidaGeneralEndpointPhysicalRealQuadraticStructural
open YoshidaSectionSixAnalytic

/-!
# The exact five-cell single-profile operator

The preceding below-three reduction leaves one local critical form and the
single factor-two autocorrelation.  Here both are transported, without a
lossy estimate, to one real endpoint-zero profile on `[-1,1]`.  The five-cell
halfwidth is `3 log 2 / 4` and the normalized factor-two lag is `4/3`.
-/

/-- Logarithmic halfwidth of the six-quarter-step five-cell support band. -/
def fiveCellWholeHalfWidth (k : ℤ) : ℝ :=
  logarithmicHalfWidth (quarterLogLatticePoint k)
    (quarterLogLatticePoint (k + 6))

/-- Multiplicative center of the complete five-cell support band. -/
def fiveCellWholeCenter (k : ℤ) : ℝ :=
  logarithmicCenter (quarterLogLatticePoint k)
    (quarterLogLatticePoint (k + 6))

/-- The complete five-cell block after common logarithmic centering. -/
def fiveCellWholeCentered
    (parent : BombieriTest) (k : ℤ) : BombieriTest :=
  normalizedDilation (fiveCellWholeCenter k)
    (logarithmicCenter_pos _ _) (monotoneQuarterFiveBlock parent k)

/-- The single clipped critical profile of the centered five-cell block. -/
def fiveCellWholeProfile
    (parent : BombieriTest) (k : ℤ) :
    YoshidaClippedSmooth (fiveCellWholeHalfWidth k) :=
  yoshidaCriticalPullbackCropLinear (fiveCellWholeHalfWidth k)
    (fiveCellWholeCentered parent k)

theorem fiveCellWholeHalfWidth_eq (k : ℤ) :
    fiveCellWholeHalfWidth k = 3 * Real.log 2 / 4 := by
  unfold fiveCellWholeHalfWidth logarithmicHalfWidth
  unfold quarterLogLatticePoint
  rw [Real.log_exp, Real.log_exp]
  push_cast
  ring

theorem fiveCellWholeHalfWidth_pos (k : ℤ) :
    0 < fiveCellWholeHalfWidth k := by
  rw [fiveCellWholeHalfWidth_eq]
  positivity

theorem fiveCellWholeCentered_criticalPullbackSupported
    (parent : BombieriTest) (k : ℤ) :
    YoshidaCriticalPullbackSupported (fiveCellWholeHalfWidth k)
      (fiveCellWholeCentered parent k) := by
  intro u hu
  unfold fiveCellWholeCentered fiveCellWholeCenter
  apply logCenteredNormalizedDilation_logarithmicPullback_eq_zero_outside
    (monotoneQuarterFiveBlock parent k)
    (quarterLogLatticePoint_pos k)
    (quarterLogLatticePoint_mono (by omega))
    (monotoneQuarterFiveBlock_tsupport_subset parent k)
  exact hu

private theorem bombieriLocalCriticalForm_self_normalizedDilation_fiveCell
    (lambda : ℝ) (hlambda : 0 < lambda) (g : BombieriTest) :
    bombieriLocalCriticalForm (normalizedDilation lambda hlambda g)
        (normalizedDilation lambda hlambda g) =
      bombieriLocalCriticalForm g g := by
  have hd := bombieriFunctional_quadratic_eq_localCritical_sub_prime
    (normalizedDilation lambda hlambda g)
  have hg := bombieriFunctional_quadratic_eq_localCritical_sub_prime g
  rw [bombieriQuadraticTest_normalizedDilation] at hd
  have h := hd.symm.trans hg
  simpa only [sub_left_inj] using h

/-- The complete local reserve is one clipped critical quadratic. -/
theorem fiveCellWhole_clippedLocal_eq_localCritical
    (parent : BombieriTest) (k : ℤ) :
    yoshidaClippedLocalCriticalForm (fiveCellWholeHalfWidth k)
        (fiveCellWholeHalfWidth_pos k)
        (fiveCellWholeProfile parent k)
        (fiveCellWholeProfile parent k) =
      bombieriLocalCriticalForm (monotoneQuarterFiveBlock parent k)
        (monotoneQuarterFiveBlock parent k) := by
  let lambda := fiveCellWholeCenter k
  have hlambda : 0 < lambda := logarithmicCenter_pos _ _
  let g := monotoneQuarterFiveBlock parent k
  let gc := fiveCellWholeCentered parent k
  have hsupported := fiveCellWholeCentered_criticalPullbackSupported parent k
  have hcrop := yoshidaClippedLocalCriticalForm_crop_eq_bombieriLocalCriticalForm
    (fiveCellWholeHalfWidth_pos k) gc gc hsupported hsupported
  change yoshidaClippedLocalCriticalForm (fiveCellWholeHalfWidth k)
      (fiveCellWholeHalfWidth_pos k)
      (fiveCellWholeProfile parent k) (fiveCellWholeProfile parent k) =
    bombieriLocalCriticalForm g g
  calc
    _ = bombieriLocalCriticalForm gc gc := hcrop
    _ = bombieriLocalCriticalForm g g := by
      dsimp only [gc, g, fiveCellWholeCentered, lambda, fiveCellWholeCenter]
      exact bombieriLocalCriticalForm_self_normalizedDilation_fiveCell
        (fiveCellWholeCenter k) hlambda g

/-- The cropped profile autocorrelation is exactly the centered critical
self-correlation. -/
theorem fiveCellWholeProfile_crossCorrelation_eq
    (parent : BombieriTest) (k : ℤ) (s : ℝ) :
    crossCorrelation
        (fiveCellWholeProfile parent k : ℝ → ℂ)
        (fiveCellWholeProfile parent k : ℝ → ℂ) s =
      factorTwoSelfCorrelation (fiveCellWholeCentered parent k) s := by
  have hsupported := fiveCellWholeCentered_criticalPullbackSupported parent k
  have hprofile :
      (fiveCellWholeProfile parent k : ℝ → ℂ) =
        (fiveCellWholeCentered parent k).logarithmicPullbackSchwartz
          (1 / 2) :=
    yoshidaCriticalPullbackCrop_eq_logarithmicPullbackSchwartz hsupported
  rw [factorTwoSelfCorrelation, crossCorrelation_apply,
    crossCorrelation_apply]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with x
  rw [hprofile]

/-- The factor-two quadratic is the lag `-log 2` autocorrelation of the same
single profile. -/
theorem sqrt_two_mul_fiveCell_quadratic_eq_profileCorrelation
    (parent : BombieriTest) (k : ℤ) :
    ((Real.sqrt 2 : ℝ) : ℂ) *
        bombieriQuadraticTest (monotoneQuarterFiveBlock parent k) 2 =
      crossCorrelation
        (fiveCellWholeProfile parent k : ℝ → ℂ)
        (fiveCellWholeProfile parent k : ℝ → ℂ) (-Real.log 2) := by
  let g := monotoneQuarterFiveBlock parent k
  let gc := fiveCellWholeCentered parent k
  have hcorr := factorTwoSelfCorrelation_neg_log_eq_sqrt_mul_quadratic
    gc 2 (by norm_num)
  dsimp only [gc, fiveCellWholeCentered] at hcorr
  rw [bombieriQuadraticTest_normalizedDilation] at hcorr
  rw [fiveCellWholeProfile_crossCorrelation_eq parent k]
  simpa only [g] using hcorr.symm

/-- Exact single-profile form of five-cell production. -/
theorem bombieriFunctional_fiveBlock_re_eq_singleProfile
    (parent : BombieriTest) (k : ℤ) :
    (bombieriFunctional
        (bombieriQuadraticTest (monotoneQuarterFiveBlock parent k))).re =
      (yoshidaClippedLocalCriticalForm (fiveCellWholeHalfWidth k)
        (fiveCellWholeHalfWidth_pos k)
        (fiveCellWholeProfile parent k)
        (fiveCellWholeProfile parent k)).re -
      Real.sqrt 2 * Real.log 2 *
        (crossCorrelation
          (fiveCellWholeProfile parent k : ℝ → ℂ)
          (fiveCellWholeProfile parent k : ℝ → ℂ)
          (-Real.log 2)).re := by
  rw [bombieriFunctional_fiveBlock_re_eq_localCritical_sub_factorTwo,
    ← fiveCellWhole_clippedLocal_eq_localCritical parent k]
  have hprime := congrArg Complex.re
    (sqrt_two_mul_fiveCell_quadratic_eq_profileCorrelation parent k)
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero] at hprime
  have hcritical := congrArg Complex.re
    (criticalDilationCorrelation_eq_sqrt_mul_quadraticTest
      (monotoneQuarterFiveBlock parent k) 2)
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero] at hcritical
  rw [hcritical, hprime]

/-! ## Real normalized coordinates -/

/-- The real part of the complete five-cell profile, normalized to
`[-1,1]`. -/
def fiveCellNormalizedRealProfile
    (parent : BombieriTest) (k : ℤ) : ℝ → ℝ :=
  centeredRescale (fiveCellWholeHalfWidth k)
    (fun y ↦ (fiveCellWholeProfile parent k y).re)

/-- The normalized right-to-left pairing at the five-cell factor-two lag. -/
def fiveCellEndpointPairing (w : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ in (1 / 3 : ℝ)..1, w x * w (x - 4 / 3)

theorem bombieriConjugateTest_fiveCellWholeCentered
    (parent : BombieriTest) (k : ℤ)
    (hparent : bombieriConjugateTest parent = parent) :
    bombieriConjugateTest (fiveCellWholeCentered parent k) =
      fiveCellWholeCentered parent k := by
  have hblock :
      bombieriConjugateTest (monotoneQuarterFiveBlock parent k) =
        monotoneQuarterFiveBlock parent k := by
    exact bombieriConjugateTest_monotoneQuarterFiniteBlock
      parent hparent k 0 5
  apply TestFunction.ext
  intro x
  have hvalue := congrArg
    (fun g : BombieriTest ↦ g (fiveCellWholeCenter k * x)) hblock
  simp only [bombieriConjugateTest_apply] at hvalue
  simp only [fiveCellWholeCentered, bombieriConjugateTest_apply,
    normalizedDilation_apply, map_mul, Complex.conj_ofReal]
  rw [hvalue]

theorem fiveCellWholeProfile_im_eq_zero
    (parent : BombieriTest) (k : ℤ)
    (hparent : bombieriConjugateTest parent = parent) (x : ℝ) :
    (fiveCellWholeProfile parent k x).im = 0 := by
  let gc := fiveCellWholeCentered parent k
  have hgc : bombieriConjugateTest gc = gc :=
    bombieriConjugateTest_fiveCellWholeCentered parent k hparent
  have hrealPart : bombieriRealPartTest gc = gc := by
    unfold bombieriRealPartTest
    rw [hgc]
    apply TestFunction.ext
    intro y
    simp
    ring
  have hsupported := fiveCellWholeCentered_criticalPullbackSupported parent k
  have hprofile :=
    yoshidaCriticalPullbackCrop_eq_logarithmicPullbackSchwartz hsupported
  change ((fiveCellWholeProfile parent k : ℝ → ℂ) x).im = 0
  rw [show (fiveCellWholeProfile parent k : ℝ → ℂ) =
      gc.logarithmicPullbackSchwartz (1 / 2) by
    simpa only [gc, fiveCellWholeProfile] using hprofile]
  rw [← hrealPart]
  exact bombieriRealPartTest_criticalPullback_im_eq_zero gc x

theorem fiveCellWholeProfile_continuous
    (parent : BombieriTest) (k : ℤ) :
    Continuous (fiveCellWholeProfile parent k : ℝ → ℂ) := by
  have hsupported := fiveCellWholeCentered_criticalPullbackSupported parent k
  change Continuous
    (yoshidaCriticalPullbackCropLinear (fiveCellWholeHalfWidth k)
      (fiveCellWholeCentered parent k) : ℝ → ℂ)
  rw [yoshidaCriticalPullbackCrop_eq_logarithmicPullbackSchwartz hsupported]
  exact (fiveCellWholeCentered parent k).logarithmicPullback_contDiff
    (1 / 2) |>.continuous

theorem fiveCellWholeProfile_endpoints_zero
    (parent : BombieriTest) (k : ℤ) :
    fiveCellWholeProfile parent k (-fiveCellWholeHalfWidth k) = 0 ∧
      fiveCellWholeProfile parent k (fiveCellWholeHalfWidth k) = 0 := by
  have hsupported := fiveCellWholeCentered_criticalPullbackSupported parent k
  have hend := criticalPullback_endpoints_zero_of_supported
    (fiveCellWholeCentered parent k) hsupported
  have hprofile :=
    yoshidaCriticalPullbackCrop_eq_logarithmicPullbackSchwartz hsupported
  simpa only [fiveCellWholeProfile, hprofile] using hend

theorem fiveCellNormalizedRealProfile_endpoints_zero
    (parent : BombieriTest) (k : ℤ) :
    fiveCellNormalizedRealProfile parent k (-1) = 0 ∧
      fiveCellNormalizedRealProfile parent k 1 = 0 := by
  have hends := fiveCellWholeProfile_endpoints_zero parent k
  constructor
  · unfold fiveCellNormalizedRealProfile centeredRescale
    rw [show fiveCellWholeHalfWidth k * (-1 : ℝ) =
        -fiveCellWholeHalfWidth k by ring]
    simpa using congrArg Complex.re hends.1
  · unfold fiveCellNormalizedRealProfile centeredRescale
    rw [show fiveCellWholeHalfWidth k * (1 : ℝ) =
        fiveCellWholeHalfWidth k by ring]
    simpa using congrArg Complex.re hends.2

theorem fiveCellNormalizedRealProfile_contDiff
    (parent : BombieriTest) (k : ℤ) :
    ContDiff ℝ 1 (fiveCellNormalizedRealProfile parent k) := by
  have hsupported := fiveCellWholeCentered_criticalPullbackSupported parent k
  have hscale : ContDiff ℝ 1
      (fun x : ℝ ↦ fiveCellWholeHalfWidth k * x) := by fun_prop
  have hpullback : ContDiff ℝ 1
      (fun x : ℝ ↦
        (fiveCellWholeCentered parent k).logarithmicPullbackSchwartz (1 / 2)
          (fiveCellWholeHalfWidth k * x)) :=
    ((fiveCellWholeCentered parent k).logarithmicPullbackSchwartz (1 / 2)).smooth 1
      |>.comp hscale
  unfold fiveCellNormalizedRealProfile centeredRescale
  rw [show (fiveCellWholeProfile parent k : ℝ → ℂ) =
      (fiveCellWholeCentered parent k).logarithmicPullbackSchwartz (1 / 2) by
    exact yoshidaCriticalPullbackCrop_eq_logarithmicPullbackSchwartz hsupported]
  exact Complex.reCLM.contDiff.comp hpullback

theorem fiveCellNormalizedRealProfile_locallyLipschitzOn
    (parent : BombieriTest) (k : ℤ) :
    LocallyLipschitzOn (Icc (-1) 1)
      (fiveCellNormalizedRealProfile parent k) := by
  exact (fiveCellNormalizedRealProfile_contDiff parent k).contDiffOn
    |>.locallyLipschitzOn (convex_Icc (-1) 1)

/-- Exact physical endpoint strip of the five-cell factor-two overlap. -/
theorem fiveCellWholeProfile_crossCorrelation_neg_log_re_eq_endpointSquares
    (parent : BombieriTest) (k : ℤ) :
    (crossCorrelation
        (fiveCellWholeProfile parent k : ℝ → ℂ)
        (fiveCellWholeProfile parent k : ℝ → ℂ)
        (-Real.log 2)).re =
      (1 / 4 : ℝ) *
        ∫ x : ℝ in Real.log 2 / 4..3 * Real.log 2 / 4,
          (Complex.normSq
              (fiveCellWholeProfile parent k x +
                fiveCellWholeProfile parent k (x - Real.log 2)) -
            Complex.normSq
              (fiveCellWholeProfile parent k x -
                fiveCellWholeProfile parent k (x - Real.log 2))) := by
  have hs : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have hs2 : Real.log 2 ≤ 2 * fiveCellWholeHalfWidth k := by
    rw [fiveCellWholeHalfWidth_eq]
    nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  rw [crossCorrelation_neg_re_eq_matched_sub_antimatched
    (fiveCellWholeProfile parent k) (fiveCellWholeProfile parent k) hs hs2]
  have hlower : Real.log 2 - fiveCellWholeHalfWidth k =
      Real.log 2 / 4 := by
    rw [fiveCellWholeHalfWidth_eq]
    ring
  have hupper : fiveCellWholeHalfWidth k = 3 * Real.log 2 / 4 :=
    fiveCellWholeHalfWidth_eq k
  rw [hlower]
  congr 2

/-- Scaling the five-cell endpoint strip to `[-1,1]` turns the prime-two lag
into exactly `4/3`. -/
theorem fiveCellPhysicalEndpointPairing_eq_normalized
    (parent : BombieriTest) (k : ℤ) :
    (∫ x : ℝ in Real.log 2 / 4..3 * Real.log 2 / 4,
        (fiveCellWholeProfile parent k x).re *
          (fiveCellWholeProfile parent k (x - Real.log 2)).re) =
      fiveCellWholeHalfWidth k *
        fiveCellEndpointPairing (fiveCellNormalizedRealProfile parent k) := by
  let a : ℝ := fiveCellWholeHalfWidth k
  let f : ℝ → ℝ := fun x ↦ (fiveCellWholeProfile parent k x).re
  let q : ℝ → ℝ := fun x ↦ f x * f (x - Real.log 2)
  have hsubst := intervalIntegral.smul_integral_comp_mul_add
    (a := (1 / 3 : ℝ)) (b := 1) q a 0
  have ha : a = 3 * Real.log 2 / 4 := fiveCellWholeHalfWidth_eq k
  have hlag : a * (4 / 3 : ℝ) = Real.log 2 := by rw [ha]; ring
  have hlower : a * (1 / 3 : ℝ) + 0 = Real.log 2 / 4 := by
    rw [ha]
    ring
  have hupper : a * (1 : ℝ) + 0 = 3 * Real.log 2 / 4 := by
    rw [ha]
    ring
  rw [← hlower, ← hupper]
  calc
    (∫ x : ℝ in a * (1 / 3 : ℝ) + 0..a * (1 : ℝ) + 0,
        (fiveCellWholeProfile parent k x).re *
          (fiveCellWholeProfile parent k (x - Real.log 2)).re) =
        a * ∫ t : ℝ in (1 / 3 : ℝ)..1, q (a * t + 0) := by
      simpa only [q, f, smul_eq_mul] using hsubst.symm
    _ = a * fiveCellEndpointPairing
        (fiveCellNormalizedRealProfile parent k) := by
      congr 1
      unfold fiveCellEndpointPairing fiveCellNormalizedRealProfile
      apply intervalIntegral.integral_congr
      intro t _ht
      dsimp only [q, f, centeredRescale]
      simp only [add_zero]
      rw [show a * t - Real.log 2 = a * (t - 4 / 3) by
        rw [mul_sub, hlag]]

/-- For a real parent, the complete factor-two autocorrelation is the
halfwidth times the normalized five-cell endpoint pairing. -/
theorem fiveCellWholeProfile_crossCorrelation_neg_log_re_eq_normalizedPairing
    (parent : BombieriTest) (k : ℤ)
    (hparent : bombieriConjugateTest parent = parent) :
    (crossCorrelation
        (fiveCellWholeProfile parent k : ℝ → ℂ)
        (fiveCellWholeProfile parent k : ℝ → ℂ)
        (-Real.log 2)).re =
      fiveCellWholeHalfWidth k *
        fiveCellEndpointPairing (fiveCellNormalizedRealProfile parent k) := by
  rw [fiveCellWholeProfile_crossCorrelation_neg_log_re_eq_endpointSquares]
  let f := fiveCellWholeProfile parent k
  have hintegrand (x : ℝ) :
      Complex.normSq (f x + f (x - Real.log 2)) -
          Complex.normSq (f x - f (x - Real.log 2)) =
        4 * (f x).re * (f (x - Real.log 2)).re := by
    have hx : (f x).im = 0 := by
      simpa only [f] using fiveCellWholeProfile_im_eq_zero parent k hparent x
    have hy : (f (x - Real.log 2)).im = 0 := by
      simpa only [f] using
        fiveCellWholeProfile_im_eq_zero parent k hparent (x - Real.log 2)
    simp only [Complex.normSq_apply, add_re, add_im, sub_re, sub_im]
    rw [hx, hy]
    ring
  rw [show (∫ x : ℝ in Real.log 2 / 4..3 * Real.log 2 / 4,
      (Complex.normSq (f x + f (x - Real.log 2)) -
        Complex.normSq (f x - f (x - Real.log 2)))) =
      ∫ x : ℝ in Real.log 2 / 4..3 * Real.log 2 / 4,
        4 * (f x).re * (f (x - Real.log 2)).re by
    apply intervalIntegral.integral_congr
    intro x _hx
    exact hintegrand x]
  rw [show (fun x : ℝ ↦ 4 * (f x).re * (f (x - Real.log 2)).re) =
      fun x ↦ 4 * ((f x).re * (f (x - Real.log 2)).re) by
    funext x
    ring,
    intervalIntegral.integral_const_mul]
  rw [show (∫ x : ℝ in Real.log 2 / 4..3 * Real.log 2 / 4,
      (f x).re * (f (x - Real.log 2)).re) =
      fiveCellWholeHalfWidth k *
        fiveCellEndpointPairing (fiveCellNormalizedRealProfile parent k) by
    simpa only [f] using fiveCellPhysicalEndpointPairing_eq_normalized parent k]
  ring

/-- The local critical diagonal of a real five-cell block is exactly the
normalized physical quadratic at halfwidth `3 log 2 / 4`. -/
theorem fiveCell_clippedLocalCritical_re_eq_centeredPhysical
    (parent : BombieriTest) (k : ℤ)
    (hparent : bombieriConjugateTest parent = parent) :
    (yoshidaClippedLocalCriticalForm (fiveCellWholeHalfWidth k)
      (fiveCellWholeHalfWidth_pos k)
      (fiveCellWholeProfile parent k)
      (fiveCellWholeProfile parent k)).re =
        fiveCellWholeHalfWidth k *
          centeredClippedPhysicalQuadratic (fiveCellWholeHalfWidth k)
            (fiveCellNormalizedRealProfile parent k) := by
  let f := fiveCellWholeProfile parent k
  have hends := fiveCellWholeProfile_endpoints_zero parent k
  have hreal : ∀ x ∈ Icc (-fiveCellWholeHalfWidth k)
      (fiveCellWholeHalfWidth k), f x = ((f x).re : ℂ) := by
    intro x _hx
    apply Complex.ext
    · simp
    · simp only [Complex.ofReal_im]
      exact fiveCellWholeProfile_im_eq_zero parent k hparent x
  have hdiag :=
    clippedCriticalFormValue_eq_centeredClippedPhysicalQuadratic_of_endpoints_zero
      (fiveCellWholeHalfWidth_pos k) f hreal hends.1 hends.2
      (fiveCellNormalizedRealProfile_locallyLipschitzOn parent k)
  simpa only [clippedCriticalFormValue, f, fiveCellNormalizedRealProfile]
    using hdiag

/-- Exact normalized five-cell target.  This is the first residual
determinant problem as one endpoint-zero real operator at width
`3 log 2 / 4` and lag `4/3`. -/
theorem bombieriFunctional_fiveBlock_re_eq_centeredPhysical_sub_pairing
    (parent : BombieriTest) (k : ℤ)
    (hparent : bombieriConjugateTest parent = parent) :
    (bombieriFunctional
      (bombieriQuadraticTest (monotoneQuarterFiveBlock parent k))).re =
        fiveCellWholeHalfWidth k *
          (centeredClippedPhysicalQuadratic (fiveCellWholeHalfWidth k)
              (fiveCellNormalizedRealProfile parent k) -
            Real.sqrt 2 * Real.log 2 *
              fiveCellEndpointPairing
                (fiveCellNormalizedRealProfile parent k)) := by
  rw [bombieriFunctional_fiveBlock_re_eq_singleProfile,
    fiveCell_clippedLocalCritical_re_eq_centeredPhysical parent k hparent,
    fiveCellWholeProfile_crossCorrelation_neg_log_re_eq_normalizedPairing
      parent k hparent]
  ring

end

end ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellSingleProfileStructural

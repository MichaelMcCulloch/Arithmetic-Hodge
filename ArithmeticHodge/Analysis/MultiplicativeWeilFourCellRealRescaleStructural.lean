import ArithmeticHodge.Analysis.MultiplicativeWeilFourCellEndpointStripStructural
import ArithmeticHodge.Analysis.YoshidaFourCellEndpointVarianceStructural

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.MultiplicativeWeilFourCellRealRescaleStructural

noncomputable section

open CenteredEndpointCorrelation
open MultiplicativeWeil
open MultiplicativeWeilFourCellEndpointStripStructural
open MultiplicativeWeilFourCellSingleProfileStructural
open MultiplicativeWeilMinimalNegativeBlockStructural
open MultiplicativeWeilMonotoneFourCellPrimeGeometryStructural
open UnitIntervalLogEnergyAffine
open YoshidaEndpointScaledCorrelation
open YoshidaFactorTwoEndpointClean
open YoshidaFourCellEndpointVarianceStructural
open YoshidaCauchyPairing

/-!
# Real normalized coordinates for the four-cell endpoint channel

For a conjugation-fixed Bombieri parent, the centered four-cell profile is
real.  Pulling its real part back from the physical interval of halfwidth
`5 * log 2 / 8` to `[-1,1]` turns the prime-two lag into `8/5`, exactly the
pairing controlled by `YoshidaFourCellEndpointVarianceStructural`.
-/

/-- The real part of the complete four-cell profile, normalized to
`[-1,1]`. -/
def fourCellNormalizedRealProfile
    (parent : BombieriTest) (k : ℤ) : ℝ → ℝ :=
  centeredRescale (fourCellWholeHalfWidth k)
    (fun y ↦ (fourCellWholeProfile parent k y).re)

/-- Conjugation-fixity is preserved by centering the complete four-cell
block. -/
theorem bombieriConjugateTest_fourCellWholeCentered
    (parent : BombieriTest) (k : ℤ)
    (hparent : bombieriConjugateTest parent = parent) :
    bombieriConjugateTest (fourCellWholeCentered parent k) =
      fourCellWholeCentered parent k := by
  have hblock :
      bombieriConjugateTest (monotoneQuarterFourBlock parent k) =
        monotoneQuarterFourBlock parent k := by
    exact bombieriConjugateTest_monotoneQuarterFiniteBlock
      parent hparent k 0 4
  apply TestFunction.ext
  intro x
  have hvalue := congrArg
    (fun g : BombieriTest ↦ g (fourCellWholeCenter k * x)) hblock
  simp only [bombieriConjugateTest_apply] at hvalue
  simp only [fourCellWholeCentered, bombieriConjugateTest_apply,
    normalizedDilation_apply, map_mul, Complex.conj_ofReal]
  rw [hvalue]

/-- A real Bombieri parent produces a pointwise real complete four-cell
profile. -/
theorem fourCellWholeProfile_im_eq_zero
    (parent : BombieriTest) (k : ℤ)
    (hparent : bombieriConjugateTest parent = parent) (x : ℝ) :
    (fourCellWholeProfile parent k x).im = 0 := by
  let gc := fourCellWholeCentered parent k
  have hgc : bombieriConjugateTest gc = gc := by
    exact bombieriConjugateTest_fourCellWholeCentered parent k hparent
  have hrealPart : bombieriRealPartTest gc = gc := by
    unfold bombieriRealPartTest
    rw [hgc]
    apply TestFunction.ext
    intro y
    simp
    ring
  have hsupported := fourCellWholeCentered_criticalPullbackSupported parent k
  have hprofile :=
    yoshidaCriticalPullbackCrop_eq_logarithmicPullbackSchwartz hsupported
  change ((fourCellWholeProfile parent k : ℝ → ℂ) x).im = 0
  rw [show (fourCellWholeProfile parent k : ℝ → ℂ) =
      gc.logarithmicPullbackSchwartz (1 / 2) by
    simpa only [gc, fourCellWholeProfile] using hprofile]
  rw [← hrealPart]
  exact bombieriRealPartTest_criticalPullback_im_eq_zero gc x

/-- The production four-cell profile is globally continuous because its crop
agrees with the supported Schwartz pullback. -/
theorem fourCellWholeProfile_continuous
    (parent : BombieriTest) (k : ℤ) :
    Continuous (fourCellWholeProfile parent k : ℝ → ℂ) := by
  have hsupported := fourCellWholeCentered_criticalPullbackSupported parent k
  change Continuous
    (yoshidaCriticalPullbackCropLinear (fourCellWholeHalfWidth k)
      (fourCellWholeCentered parent k) : ℝ → ℂ)
  rw [yoshidaCriticalPullbackCrop_eq_logarithmicPullbackSchwartz hsupported]
  exact (fourCellWholeCentered parent k).logarithmicPullback_contDiff
    (1 / 2) |>.continuous

/-- Consequently the normalized real profile is continuous on the whole
line. -/
theorem fourCellNormalizedRealProfile_continuous
    (parent : BombieriTest) (k : ℤ) :
    Continuous (fourCellNormalizedRealProfile parent k) := by
  unfold fourCellNormalizedRealProfile centeredRescale
  exact Complex.continuous_re.comp
    ((fourCellWholeProfile_continuous parent k).comp
      (continuous_const.mul continuous_id))

/-- The supported production pullback has zero physical endpoint traces. -/
theorem fourCellWholeProfile_endpoints_zero
    (parent : BombieriTest) (k : ℤ) :
    fourCellWholeProfile parent k (-fourCellWholeHalfWidth k) = 0 ∧
      fourCellWholeProfile parent k (fourCellWholeHalfWidth k) = 0 := by
  have hsupported := fourCellWholeCentered_criticalPullbackSupported parent k
  have hend := criticalPullback_endpoints_zero_of_supported
    (fourCellWholeCentered parent k) hsupported
  have hprofile :=
    yoshidaCriticalPullbackCrop_eq_logarithmicPullbackSchwartz hsupported
  simpa only [fourCellWholeProfile, hprofile] using hend

/-- The normalized right-to-left endpoint pairing is the usual centered
one-sided autocorrelation at lag `8/5`. -/
theorem fourCellEndpointPairing_eq_centeredEndpointCorrelation
    (w : ℝ → ℝ) :
    fourCellEndpointPairing w = centeredEndpointCorrelation w (8 / 5) := by
  let q : ℝ → ℝ := fun x ↦ w (x + 8 / 5) * w x
  have hshift := intervalIntegral.integral_comp_sub_right
    (f := q) (a := (3 / 5 : ℝ)) (b := 1) (8 / 5 : ℝ)
  unfold fourCellEndpointPairing centeredEndpointCorrelation
  dsimp only [q] at hshift
  norm_num at hshift ⊢
  convert hshift using 1
  all_goals ring

/-- Scaling from the physical endpoint strip to `[-1,1]` turns the prime-two
lag into exactly `8/5`. -/
theorem fourCellPhysicalEndpointPairing_eq_normalized
    (parent : BombieriTest) (k : ℤ) :
    (∫ x : ℝ in 3 * Real.log 2 / 8..5 * Real.log 2 / 8,
        (fourCellWholeProfile parent k x).re *
          (fourCellWholeProfile parent k (x - Real.log 2)).re) =
      fourCellWholeHalfWidth k *
        fourCellEndpointPairing (fourCellNormalizedRealProfile parent k) := by
  let a : ℝ := fourCellWholeHalfWidth k
  let f : ℝ → ℝ := fun x ↦ (fourCellWholeProfile parent k x).re
  let q : ℝ → ℝ := fun x ↦ f x * f (x - Real.log 2)
  have hsubst := intervalIntegral.smul_integral_comp_mul_add
    (a := (3 / 5 : ℝ)) (b := 1) q a 0
  have ha : a = 5 * Real.log 2 / 8 := by
    exact fourCellWholeHalfWidth_eq k
  have hlag : a * (8 / 5 : ℝ) = Real.log 2 := by
    rw [ha]
    ring
  have hlower : a * (3 / 5 : ℝ) + 0 = 3 * Real.log 2 / 8 := by
    rw [ha]
    ring
  have hupper : a * (1 : ℝ) + 0 = 5 * Real.log 2 / 8 := by
    rw [ha]
    ring
  rw [← hlower, ← hupper]
  calc
    (∫ x : ℝ in a * (3 / 5 : ℝ) + 0..a * (1 : ℝ) + 0,
        (fourCellWholeProfile parent k x).re *
          (fourCellWholeProfile parent k (x - Real.log 2)).re) =
        a * ∫ t : ℝ in (3 / 5 : ℝ)..1, q (a * t + 0) := by
      simpa only [q, f, smul_eq_mul] using hsubst.symm
    _ = a * fourCellEndpointPairing
        (fourCellNormalizedRealProfile parent k) := by
      congr 1
      unfold fourCellEndpointPairing fourCellNormalizedRealProfile
      apply intervalIntegral.integral_congr
      intro t _ht
      dsimp only [q, f, centeredRescale]
      simp only [add_zero]
      rw [show a * t - Real.log 2 = a * (t - 8 / 5) by
        rw [mul_sub, hlag]]

/-- For a real parent, the complete prime-two autocorrelation is exactly the
halfwidth times the normalized endpoint pairing. -/
theorem fourCellWholeProfile_crossCorrelation_neg_log_re_eq_normalizedPairing
    (parent : BombieriTest) (k : ℤ)
    (hparent : bombieriConjugateTest parent = parent) :
    (crossCorrelation
        (fourCellWholeProfile parent k : ℝ → ℂ)
        (fourCellWholeProfile parent k : ℝ → ℂ)
        (-Real.log 2)).re =
      fourCellWholeHalfWidth k *
        fourCellEndpointPairing (fourCellNormalizedRealProfile parent k) := by
  rw [fourCellWholeProfile_crossCorrelation_neg_log_re_eq_endpointSquares]
  let f := fourCellWholeProfile parent k
  have hintegrand (x : ℝ) :
      Complex.normSq (f x + f (x - Real.log 2)) -
          Complex.normSq (f x - f (x - Real.log 2)) =
        4 * (f x).re * (f (x - Real.log 2)).re := by
    have hx : (f x).im = 0 := by
      simpa only [f] using
        fourCellWholeProfile_im_eq_zero parent k hparent x
    have hy : (f (x - Real.log 2)).im = 0 := by
      simpa only [f] using
        fourCellWholeProfile_im_eq_zero parent k hparent (x - Real.log 2)
    simp only [Complex.normSq_apply, add_re, add_im, sub_re, sub_im]
    rw [hx, hy]
    ring
  rw [show (∫ x : ℝ in 3 * Real.log 2 / 8..5 * Real.log 2 / 8,
      (Complex.normSq (f x + f (x - Real.log 2)) -
        Complex.normSq (f x - f (x - Real.log 2)))) =
      ∫ x : ℝ in 3 * Real.log 2 / 8..5 * Real.log 2 / 8,
        4 * (f x).re * (f (x - Real.log 2)).re by
    apply intervalIntegral.integral_congr
    intro x _hx
    exact hintegrand x]
  rw [show (fun x : ℝ ↦ 4 * (f x).re * (f (x - Real.log 2)).re) =
      fun x ↦ 4 * ((f x).re * (f (x - Real.log 2)).re) by
    funext x
    ring,
    intervalIntegral.integral_const_mul]
  rw [show (∫ x : ℝ in 3 * Real.log 2 / 8..5 * Real.log 2 / 8,
      (f x).re * (f (x - Real.log 2)).re) =
      fourCellWholeHalfWidth k *
        fourCellEndpointPairing (fourCellNormalizedRealProfile parent k) by
    simpa only [f] using
      fourCellPhysicalEndpointPairing_eq_normalized parent k]
  ring

end

end ArithmeticHodge.Analysis.MultiplicativeWeilFourCellRealRescaleStructural

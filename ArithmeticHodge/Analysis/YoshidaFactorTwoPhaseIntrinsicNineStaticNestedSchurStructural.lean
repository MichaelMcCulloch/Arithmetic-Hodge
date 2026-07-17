import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseNestedThreeSchurStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineUnbalancedStaticDiskStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP8StructuralReserve

set_option autoImplicit false

open MeasureTheory Real Set
open scoped unitInterval

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineStaticNestedSchurStructural

noncomputable section

open ThreeByThreeRankOneSchur
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointEvenConstantCross
open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOcticPotential
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointOddLowGramExpansion
open YoshidaEndpointOddResidualRegularity
open YoshidaEndpointPotentialBound
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointParityPencil
open YoshidaFactorTwoPhaseDiskSchur
open YoshidaFactorTwoPhaseIntrinsicEightUnbalancedStaticDiskStructural
open YoshidaFactorTwoPhaseIntrinsicNineUnbalancedStaticDiskStructural
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicSixSchurReduction
open YoshidaFactorTwoPhaseIntrinsicSixStaticPlusObstruction
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedDiskStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticSchurReductionStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticSplitStructural
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoPhaseNestedThreeSchurStructural
open YoshidaFactorTwoPhaseP8StructuralReserve
open YoshidaFactorTwoPhaseProfileStaticSquareAssemblyStructural
open YoshidaRegularKernelBound
open UnitIntervalIntegralBridge
open UnitIntervalLogEnergyAffine
open UnitIntervalLogEnergyLipschitz
open UnitIntervalLogEnergyProjection
open YoshidaEndpointPullbackLipschitz

/-!
# A concrete nested Schur interface for the retained nine-mode endpoints

The coordinate order is

* `E = (P0,P2,P4)`,
* `O = (P1,P3,P5)`, and
* `N = (P6,P8,P7)`.

The last block is reduced after subtracting the structural reserve

`(1/100) E6 + (33/100) E8 + (1/100) E7`.

Since the centered Legendre energies are respectively `2/13`, `2/17`, and
`2/15`, its three coordinate entries are `1/650`, `33/850`, and `1/750`.
The reduction is nested and fraction-free.  In particular, no determinant
of the full `9 x 9` matrix is introduced.
-/

/-! ## Exact endpoint entries -/

/-- Polarization of one signed endpoint diagonal. -/
def factorTwoIntrinsicNinePhasePair
    (sigma : ℝ) (u v : ℝ → ℝ) : ℝ :=
  yoshidaEndpointEvenCleanBilinear u v +
    sigma * factorTwoCenteredSymmetricPerturbationBilinear u v

theorem factorTwoIntrinsicNinePhasePair_self
    (sigma : ℝ) (u : ℝ → ℝ) :
    factorTwoIntrinsicNinePhasePair sigma u u =
      factorTwoEndpointPhaseDiagonal u sigma := by
  unfold factorTwoIntrinsicNinePhasePair factorTwoEndpointPhaseDiagonal
  rw [yoshidaEndpointEvenCleanBilinear_self,
    factorTwoCenteredSymmetricPerturbationBilinear_self]

private theorem contDiff_centeredEvenP0 : ContDiff ℝ 1 centeredEvenP0 := by
  unfold centeredEvenP0
  fun_prop

private theorem contDiff_centeredEvenP2 : ContDiff ℝ 1 centeredEvenP2 := by
  unfold centeredEvenP2
  fun_prop

private theorem contDiff_centeredP1 : ContDiff ℝ 1 centeredP1 := by
  unfold centeredP1
  fun_prop

private theorem contDiff_centeredP3 : ContDiff ℝ 1 centeredP3 := by
  unfold centeredP3
  fun_prop

private theorem contDiff_factorTwoCenteredP4 :
    ContDiff ℝ 1 factorTwoCenteredP4 := by
  unfold factorTwoCenteredP4
  fun_prop

private theorem contDiff_factorTwoCenteredP5 :
    ContDiff ℝ 1 factorTwoCenteredP5 := by
  unfold factorTwoCenteredP5
  fun_prop

private theorem contDiff_factorTwoCenteredP6 :
    ContDiff ℝ 1 factorTwoCenteredP6 := by
  rw [show factorTwoCenteredP6 = fun x ↦
      (231 * x ^ 6 - 315 * x ^ 4 + 105 * x ^ 2 - 5) / 16 by
    funext x
    exact factorTwoCenteredP6_eq x]
  fun_prop

private theorem contDiff_factorTwoCenteredP7 :
    ContDiff ℝ 1 factorTwoCenteredP7 := by
  rw [show factorTwoCenteredP7 = fun x ↦
      (429 * x ^ 7 - 693 * x ^ 5 + 315 * x ^ 3 - 35 * x) / 16 by
    funext x
    exact factorTwoCenteredP7_eq x]
  fun_prop

private theorem contDiff_factorTwoCenteredP8 :
    ContDiff ℝ 1 factorTwoCenteredP8 := by
  rw [show factorTwoCenteredP8 = fun x ↦
      (6435 * x ^ 8 - 12012 * x ^ 6 + 6930 * x ^ 4 -
        1260 * x ^ 2 + 35) / 128 by
    funext x
    exact factorTwoCenteredP8_eq x]
  fun_prop

private theorem continuous_const_smul_of_contDiff
    (c : ℝ) (u : ℝ → ℝ) (hu : ContDiff ℝ 1 u) :
    Continuous (c • u) :=
  hu.continuous.const_smul c

private theorem locallyLipschitzOn_const_smul_of_contDiff
    (c : ℝ) (u : ℝ → ℝ) (hu : ContDiff ℝ 1 u) :
    LocallyLipschitzOn (Icc (-1 : ℝ) 1) (c • u) := by
  have hcu : ContDiff ℝ 1 (fun x ↦ c * u x) := contDiff_const.mul hu
  simpa only [Pi.smul_apply, smul_eq_mul] using
    hcu.locallyLipschitz.locallyLipschitzOn

private def unitIntervalRawLogCrossIntegrand
    (f g : unitInterval → ℝ) (z : unitInterval × unitInterval) : ℝ :=
  ((f z.1 - f z.2) * (g z.1 - g z.2)) /
    |(z.1 : ℝ) - (z.2 : ℝ)|

private theorem integrable_unitIntervalRawLogCrossIntegrand_of_lipschitzWith
    (f g : unitInterval → ℝ) {C D : NNReal}
    (hf : LipschitzWith C f) (hg : LipschitzWith D g) :
    Integrable (unitIntervalRawLogCrossIntegrand f g) := by
  have hfE := integrable_unitIntervalRawLogEnergyIntegrand_of_lipschitzWith f hf
  have hgE := integrable_unitIntervalRawLogEnergyIntegrand_of_lipschitzWith g hg
  have hfgE := integrable_unitIntervalRawLogEnergyIntegrand_of_lipschitzWith
    (f + g) (hf.add hg)
  have hcombo : Integrable (fun z : unitInterval × unitInterval ↦
      (1 / 2 : ℝ) *
        (unitIntervalRawLogEnergyIntegrand (f + g) z -
          unitIntervalRawLogEnergyIntegrand f z -
          unitIntervalRawLogEnergyIntegrand g z)) :=
    ((hfgE.sub hfE).sub hgE).const_mul (1 / 2 : ℝ)
  apply hcombo.congr
  filter_upwards [] with z
  unfold unitIntervalRawLogCrossIntegrand
    unitIntervalRawLogEnergyIntegrand
  simp only [Pi.add_apply]
  ring

private theorem centeredRawLogBilinear_eq_two_mul_unitCross
    (u v : ℝ → ℝ)
    (hu : LocallyLipschitzOn (Icc (-1 : ℝ) 1) u)
    (hv : LocallyLipschitzOn (Icc (-1 : ℝ) 1) v) :
    centeredRawLogBilinear u v =
      2 * ∫ z : unitInterval × unitInterval,
        unitIntervalRawLogCrossIntegrand
          (fun t ↦ centeredPullback u (t : ℝ))
          (fun t ↦ centeredPullback v (t : ℝ)) z := by
  let f : unitInterval → ℝ := fun t ↦ centeredPullback u (t : ℝ)
  let g : unitInterval → ℝ := fun t ↦ centeredPullback v (t : ℝ)
  let H : ℝ → ℝ → ℝ := fun x y ↦
    ((u x - u y) * (v x - v y)) / |x - y|
  obtain ⟨C, hf⟩ := exists_lipschitzWith_centeredPullback u hu
  obtain ⟨D, hg⟩ := exists_lipschitzWith_centeredPullback v hv
  have hInt : Integrable (unitIntervalRawLogCrossIntegrand f g) :=
    integrable_unitIntervalRawLogCrossIntegrand_of_lipschitzWith f g hf hg
  have hprod :
      (∫ z : unitInterval × unitInterval,
          unitIntervalRawLogCrossIntegrand f g z) =
        ∫ s : unitInterval, ∫ t : unitInterval,
          unitIntervalRawLogCrossIntegrand f g (s, t) :=
    MeasureTheory.integral_prod _ hInt
  have hpoint (s t : ℝ) :
      ((centeredPullback u s - centeredPullback u t) *
          (centeredPullback v s - centeredPullback v t)) / |s - t| =
        2 * H (2 * s - 1) (2 * t - 1) := by
    unfold H centeredPullback
    rw [show (2 * s - 1) - (2 * t - 1) = 2 * (s - t) by ring,
      abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    by_cases hst : |s - t| = 0
    · simp [hst]
    · field_simp [hst]
  have hiter :
      (∫ z : unitInterval × unitInterval,
          unitIntervalRawLogCrossIntegrand f g z) =
        ∫ s : ℝ in 0..1, ∫ t : ℝ in 0..1,
          2 * H (2 * s - 1) (2 * t - 1) := by
    calc
      _ = ∫ s : unitInterval, ∫ t : ℝ in 0..1,
          ((centeredPullback u (s : ℝ) - centeredPullback u t) *
            (centeredPullback v (s : ℝ) - centeredPullback v t)) /
              |(s : ℝ) - t| := by
        rw [hprod]
        apply integral_congr_ae
        filter_upwards [] with s
        rw [← integral_unitInterval_eq_intervalIntegral]
        apply integral_congr_ae
        filter_upwards [] with t
        rfl
      _ = ∫ s : ℝ in 0..1, ∫ t : ℝ in 0..1,
          ((centeredPullback u s - centeredPullback u t) *
            (centeredPullback v s - centeredPullback v t)) / |s - t| := by
        rw [← integral_unitInterval_eq_intervalIntegral]
      _ = _ := by
        apply intervalIntegral.integral_congr
        intro s _hs
        apply intervalIntegral.integral_congr
        intro t _ht
        exact hpoint s t
  have hscale :
      (∫ s : ℝ in 0..1, ∫ t : ℝ in 0..1,
          2 * H (2 * s - 1) (2 * t - 1)) =
        (1 / 2 : ℝ) * centeredRawLogBilinear u v := by
    calc
      _ = 2 * (∫ s : ℝ in 0..1, ∫ t : ℝ in 0..1,
          H (2 * s - 1) (2 * t - 1)) := by
        rw [show (fun s : ℝ ↦ ∫ t : ℝ in 0..1,
            2 * H (2 * s - 1) (2 * t - 1)) =
            fun s ↦ 2 * ∫ t : ℝ in 0..1,
              H (2 * s - 1) (2 * t - 1) by
          funext s
          rw [intervalIntegral.integral_const_mul],
          intervalIntegral.integral_const_mul]
      _ = 2 * ((1 / 4 : ℝ) *
          ∫ x : ℝ in -1..1, ∫ y : ℝ in -1..1, H x y) := by
        rw [integral_integral_comp_two_mul_sub_one H]
      _ = _ := by
        unfold centeredRawLogBilinear
        dsimp only [H]
        ring
  rw [hiter, hscale]
  ring

private theorem centeredRawLogBilinear_add_left
    (u v w : ℝ → ℝ)
    (hu : LocallyLipschitzOn (Icc (-1 : ℝ) 1) u)
    (hv : LocallyLipschitzOn (Icc (-1 : ℝ) 1) v)
    (hw : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w) :
    centeredRawLogBilinear (u + v) w =
      centeredRawLogBilinear u w + centeredRawLogBilinear v w := by
  rw [centeredRawLogBilinear_eq_two_mul_unitCross (u + v) w (hu.add hv) hw,
    centeredRawLogBilinear_eq_two_mul_unitCross u w hu hw,
    centeredRawLogBilinear_eq_two_mul_unitCross v w hv hw]
  let fu : unitInterval → ℝ := fun t ↦ centeredPullback u (t : ℝ)
  let fv : unitInterval → ℝ := fun t ↦ centeredPullback v (t : ℝ)
  let fw : unitInterval → ℝ := fun t ↦ centeredPullback w (t : ℝ)
  obtain ⟨C, hfu⟩ := exists_lipschitzWith_centeredPullback u hu
  obtain ⟨D, hfv⟩ := exists_lipschitzWith_centeredPullback v hv
  obtain ⟨E, hfw⟩ := exists_lipschitzWith_centeredPullback w hw
  have huInt := integrable_unitIntervalRawLogCrossIntegrand_of_lipschitzWith
    fu fw hfu hfw
  have hvInt := integrable_unitIntervalRawLogCrossIntegrand_of_lipschitzWith
    fv fw hfv hfw
  rw [show (fun z : unitInterval × unitInterval ↦
      unitIntervalRawLogCrossIntegrand
        (fun t ↦ centeredPullback (u + v) (t : ℝ)) fw z) =
      fun z ↦ unitIntervalRawLogCrossIntegrand fu fw z +
        unitIntervalRawLogCrossIntegrand fv fw z by
    funext z
    unfold unitIntervalRawLogCrossIntegrand fu fv fw centeredPullback
    simp only [Pi.add_apply]
    ring,
    integral_add huInt hvInt]
  ring

private theorem integrable_regularComplexPairing
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    Integrable
      (fun z : ℝ × ℝ ↦
        (yoshidaRegularKernel (yoshidaEndpointA * |z.1 - z.2|) : ℂ) *
          (u z.2 : ℂ) * star (v z.1 : ℂ))
      ((volume.restrict (Icc (-1) 1)).prod
        (volume.restrict (Icc (-1) 1))) := by
  have hreal : Integrable
      (fun z : ℝ × ℝ ↦
        ((yoshidaRegularKernel (yoshidaEndpointA * |z.1 - z.2|) *
          u z.2 * v z.1 : ℝ) : ℂ))
      ((volume.restrict (Icc (-1) 1)).prod
        (volume.restrict (Icc (-1) 1))) :=
    (integrable_regular_pairing u v hu hv).ofReal
  apply hreal.congr
  filter_upwards [] with z
  push_cast
  simp

private theorem yoshidaEndpointRegularRealBilinear_add_left
    (u v w : ℝ → ℝ)
    (hu : Continuous u) (hv : Continuous v) (hw : Continuous w) :
    yoshidaEndpointRegularRealBilinear (u + v) w =
      yoshidaEndpointRegularRealBilinear u w +
        yoshidaEndpointRegularRealBilinear v w := by
  have huInt := integrable_regularComplexPairing u w hu hw
  have hvInt := integrable_regularComplexPairing v w hv hw
  unfold yoshidaEndpointRegularRealBilinear
  dsimp only
  rw [show (fun z : ℝ × ℝ ↦
      (yoshidaRegularKernel (yoshidaEndpointA * |z.1 - z.2|) : ℂ) *
        (((u + v) z.2 : ℝ) : ℂ) * star (w z.1 : ℂ)) =
      fun z ↦
        (yoshidaRegularKernel (yoshidaEndpointA * |z.1 - z.2|) : ℂ) *
            (u z.2 : ℂ) * star (w z.1 : ℂ) +
          (yoshidaRegularKernel (yoshidaEndpointA * |z.1 - z.2|) : ℂ) *
            (v z.2 : ℂ) * star (w z.1 : ℂ) by
    funext z
    simp only [Pi.add_apply, Complex.ofReal_add]
    ring_nf,
    integral_add huInt hvInt]

private theorem yoshidaEndpointRegularRealBilinear_add_right
    (w u v : ℝ → ℝ)
    (hw : Continuous w) (hu : Continuous u) (hv : Continuous v) :
    yoshidaEndpointRegularRealBilinear w (u + v) =
      yoshidaEndpointRegularRealBilinear w u +
        yoshidaEndpointRegularRealBilinear w v := by
  have huInt := integrable_regularComplexPairing w u hw hu
  have hvInt := integrable_regularComplexPairing w v hw hv
  unfold yoshidaEndpointRegularRealBilinear
  dsimp only
  rw [show (fun z : ℝ × ℝ ↦
      (yoshidaRegularKernel (yoshidaEndpointA * |z.1 - z.2|) : ℂ) *
        (w z.2 : ℂ) * star ((((u + v) z.1 : ℝ) : ℂ))) =
      fun z ↦
        (yoshidaRegularKernel (yoshidaEndpointA * |z.1 - z.2|) : ℂ) *
            (w z.2 : ℂ) * star (u z.1 : ℂ) +
          (yoshidaRegularKernel (yoshidaEndpointA * |z.1 - z.2|) : ℂ) *
    (w z.2 : ℂ) * star (v z.1 : ℂ) by
    funext z
    simp only [Pi.add_apply, Complex.ofReal_add, star_add]
    ring_nf,
    integral_add huInt hvInt]

private theorem yoshidaEndpointCoshMoment_add
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    yoshidaEndpointCoshMoment (u + v) =
      yoshidaEndpointCoshMoment u + yoshidaEndpointCoshMoment v := by
  have hcu : Continuous (fun x : ℝ ↦
      Real.cosh (yoshidaEndpointA * x / 2) * u x) := by fun_prop
  have hcv : Continuous (fun x : ℝ ↦
      Real.cosh (yoshidaEndpointA * x / 2) * v x) := by fun_prop
  unfold yoshidaEndpointCoshMoment
  rw [show (fun x : ℝ ↦
      Real.cosh (yoshidaEndpointA * x / 2) * (u + v) x) =
      fun x ↦ Real.cosh (yoshidaEndpointA * x / 2) * u x +
        Real.cosh (yoshidaEndpointA * x / 2) * v x by
    funext x
    simp only [Pi.add_apply]
    ring,
    intervalIntegral.integral_add
      (hcu.intervalIntegrable (-1) 1) (hcv.intervalIntegrable (-1) 1)]

private theorem yoshidaEndpointSinhMoment_add
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    yoshidaEndpointSinhMoment (u + v) =
      yoshidaEndpointSinhMoment u + yoshidaEndpointSinhMoment v := by
  have hsu : Continuous (fun x : ℝ ↦
      Real.sinh (yoshidaEndpointA * x / 2) * u x) := by fun_prop
  have hsv : Continuous (fun x : ℝ ↦
      Real.sinh (yoshidaEndpointA * x / 2) * v x) := by fun_prop
  unfold yoshidaEndpointSinhMoment
  rw [show (fun x : ℝ ↦
      Real.sinh (yoshidaEndpointA * x / 2) * (u + v) x) =
      fun x ↦ Real.sinh (yoshidaEndpointA * x / 2) * u x +
        Real.sinh (yoshidaEndpointA * x / 2) * v x by
    funext x
    simp only [Pi.add_apply]
    ring,
    intervalIntegral.integral_add
      (hsu.intervalIntegrable (-1) 1) (hsv.intervalIntegrable (-1) 1)]

private theorem yoshidaEndpointEvenCleanBilinear_add_left
    (u v w : ℝ → ℝ)
    (hu : Continuous u) (hv : Continuous v) (hw : Continuous w)
    (huL : LocallyLipschitzOn (Icc (-1 : ℝ) 1) u)
    (hvL : LocallyLipschitzOn (Icc (-1 : ℝ) 1) v)
    (hwL : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w) :
    yoshidaEndpointEvenCleanBilinear (u + v) w =
      yoshidaEndpointEvenCleanBilinear u w +
        yoshidaEndpointEvenCleanBilinear v w := by
  have hpu := intervalIntegrable_endpointPotential_mul u w hu hw
  have hpv := intervalIntegrable_endpointPotential_mul v w hv hw
  have hmu : IntervalIntegrable (fun x : ℝ ↦ u x * w x) volume (-1) 1 :=
    (hu.mul hw).intervalIntegrable (-1) 1
  have hmv : IntervalIntegrable (fun x : ℝ ↦ v x * w x) volume (-1) 1 :=
    (hv.mul hw).intervalIntegrable (-1) 1
  unfold yoshidaEndpointEvenCleanBilinear
  rw [centeredRawLogBilinear_add_left u v w huL hvL hwL,
    show (fun x : ℝ ↦ yoshidaEndpointPotential x * (u + v) x * w x) =
        fun x ↦ yoshidaEndpointPotential x * u x * w x +
          yoshidaEndpointPotential x * v x * w x by
      funext x
      simp only [Pi.add_apply]
      ring,
    intervalIntegral.integral_add hpu hpv,
    show (fun x : ℝ ↦ (u + v) x * w x) =
        fun x ↦ u x * w x + v x * w x by
      funext x
      simp only [Pi.add_apply]
      ring,
    intervalIntegral.integral_add hmu hmv,
    yoshidaEndpointRegularRealBilinear_add_left u v w hu hv hw,
    yoshidaEndpointRegularRealBilinear_add_right w u v hw hu hv,
    yoshidaEndpointCoshMoment_add u v hu hv,
    yoshidaEndpointSinhMoment_add u v hu hv]
  simp only [Complex.add_re]
  ring

private theorem yoshidaEndpointEvenCleanBilinear_add_right
    (w u v : ℝ → ℝ)
    (hw : Continuous w) (hu : Continuous u) (hv : Continuous v)
    (hwL : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w)
    (huL : LocallyLipschitzOn (Icc (-1 : ℝ) 1) u)
    (hvL : LocallyLipschitzOn (Icc (-1 : ℝ) 1) v) :
    yoshidaEndpointEvenCleanBilinear w (u + v) =
      yoshidaEndpointEvenCleanBilinear w u +
        yoshidaEndpointEvenCleanBilinear w v := by
  rw [yoshidaEndpointEvenCleanBilinear_symm,
    yoshidaEndpointEvenCleanBilinear_add_left u v w hu hv hw huL hvL hwL,
    yoshidaEndpointEvenCleanBilinear_symm u w,
    yoshidaEndpointEvenCleanBilinear_symm v w]

private theorem symmetricPerturbationBilinear_comm
    (u v : ℝ → ℝ) :
    factorTwoCenteredSymmetricPerturbationBilinear u v =
      factorTwoCenteredSymmetricPerturbationBilinear v u := by
  unfold factorTwoCenteredSymmetricPerturbationBilinear
  simp_rw [factorTwoCenteredCorrelationBilinear_comm u v]

private theorem factorTwoIntrinsicNinePhasePair_add_left
    (sigma : ℝ) (u v w : ℝ → ℝ)
    (hu : Continuous u) (hv : Continuous v) (hw : Continuous w)
    (huL : LocallyLipschitzOn (Icc (-1 : ℝ) 1) u)
    (hvL : LocallyLipschitzOn (Icc (-1 : ℝ) 1) v)
    (hwL : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w) :
    factorTwoIntrinsicNinePhasePair sigma (u + v) w =
      factorTwoIntrinsicNinePhasePair sigma u w +
        factorTwoIntrinsicNinePhasePair sigma v w := by
  unfold factorTwoIntrinsicNinePhasePair
  rw [yoshidaEndpointEvenCleanBilinear_add_left u v w hu hv hw huL hvL hwL,
    factorTwoCenteredSymmetricPerturbationBilinear_add_left
      u v w hu hv hw]
  ring

private theorem factorTwoIntrinsicNinePhasePair_add_right
    (sigma : ℝ) (w u v : ℝ → ℝ)
    (hw : Continuous w) (hu : Continuous u) (hv : Continuous v)
    (hwL : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w)
    (huL : LocallyLipschitzOn (Icc (-1 : ℝ) 1) u)
    (hvL : LocallyLipschitzOn (Icc (-1 : ℝ) 1) v) :
    factorTwoIntrinsicNinePhasePair sigma w (u + v) =
      factorTwoIntrinsicNinePhasePair sigma w u +
        factorTwoIntrinsicNinePhasePair sigma w v := by
  unfold factorTwoIntrinsicNinePhasePair
  rw [yoshidaEndpointEvenCleanBilinear_add_right w u v hw hu hv hwL huL hvL,
    symmetricPerturbationBilinear_comm w (u + v),
    factorTwoCenteredSymmetricPerturbationBilinear_add_left
      u v w hu hv hw,
    symmetricPerturbationBilinear_comm u w,
    symmetricPerturbationBilinear_comm v w]
  ring

private theorem factorTwoIntrinsicNinePhasePair_smul_smul
    (sigma c d : ℝ) (u v : ℝ → ℝ) :
    factorTwoIntrinsicNinePhasePair sigma (c • u) (d • v) =
      c * d * factorTwoIntrinsicNinePhasePair sigma u v := by
  unfold factorTwoIntrinsicNinePhasePair
  change yoshidaEndpointEvenCleanBilinear
      (fun x ↦ c * u x) (fun x ↦ d * v x) + _ = _
  rw [yoshidaEndpointEvenCleanBilinear_const_mul_const_mul,
    factorTwoCenteredSymmetricPerturbationBilinear_smul_smul]
  ring

private theorem factorTwoEndpointPhaseDiagonal_add
    (sigma : ℝ) (u v : ℝ → ℝ)
    (hu : Continuous u) (hv : Continuous v)
    (huL : LocallyLipschitzOn (Icc (-1 : ℝ) 1) u)
    (hvL : LocallyLipschitzOn (Icc (-1 : ℝ) 1) v) :
    factorTwoEndpointPhaseDiagonal (u + v) sigma =
      factorTwoEndpointPhaseDiagonal u sigma +
        2 * factorTwoIntrinsicNinePhasePair sigma u v +
        factorTwoEndpointPhaseDiagonal v sigma := by
  rw [← factorTwoIntrinsicNinePhasePair_self,
    factorTwoIntrinsicNinePhasePair_add_left sigma u v (u + v)
      hu hv (hu.add hv) huL hvL (huL.add hvL),
    factorTwoIntrinsicNinePhasePair_add_right sigma u u v
      hu hu hv huL huL hvL,
    factorTwoIntrinsicNinePhasePair_add_right sigma v u v
      hv hu hv hvL huL hvL,
    factorTwoIntrinsicNinePhasePair_self,
    factorTwoIntrinsicNinePhasePair_self]
  unfold factorTwoIntrinsicNinePhasePair
  rw [yoshidaEndpointEvenCleanBilinear_symm v u,
    symmetricPerturbationBilinear_comm v u]
  ring

private theorem factorTwoEndpointPhaseDiagonal_smul
    (sigma c : ℝ) (u : ℝ → ℝ) :
    factorTwoEndpointPhaseDiagonal (c • u) sigma =
      c ^ 2 * factorTwoEndpointPhaseDiagonal u sigma := by
  rw [← factorTwoIntrinsicNinePhasePair_self,
    factorTwoIntrinsicNinePhasePair_smul_smul,
    factorTwoIntrinsicNinePhasePair_self]
  ring

private theorem factorTwoEndpointPhaseDiagonal_intrinsicSixEven_eq
    (sigma c0 c2 c4 : ℝ) :
    factorTwoEndpointPhaseDiagonal
        (factorTwoEvenStructuralLowProfile c0 c2 +
          factorTwoIntrinsicSixEvenTail c4) sigma =
      factorTwoIntrinsicSixStaticEven sigma c0 c2 c4 := by
  have h := factorTwoEndpointChannelPhase_intrinsicSix_eq_static_coordinates
    c0 c2 c4 0 0 0 sigma 0
  have ho : factorTwoIntrinsicSixOddTail 0 0 0 = (0 : ℝ → ℝ) := by
    funext x
    unfold factorTwoIntrinsicSixOddTail factorTwoOddStructuralLowProfile
      factorTwoCenteredP5
    simp
  rw [factorTwoEndpointChannelPhase_eq_diagonals, ho] at h
  have hzero : factorTwoEndpointPhaseDiagonal (0 : ℝ → ℝ) sigma = 0 := by
    simpa using
      (factorTwoEndpointPhaseDiagonal_smul sigma 0 centeredEvenP0)
  have hcross : factorTwoCenteredAlternatingCoupling
      (factorTwoEvenStructuralLowProfile c0 c2 +
        factorTwoIntrinsicSixEvenTail c4) (0 : ℝ → ℝ) = 0 := by
    simpa using (factorTwoCenteredAlternatingCoupling_smul_right 0
      (factorTwoEvenStructuralLowProfile c0 c2 +
        factorTwoIntrinsicSixEvenTail c4) centeredEvenP0)
  rw [hzero, hcross] at h
  unfold factorTwoIntrinsicSixStaticOdd
    factorTwoIntrinsicOddPhaseQuadratic at h
  simpa using h

private theorem factorTwoEndpointPhaseDiagonal_intrinsicSixOdd_eq
    (sigma c1 c3 c5 : ℝ) :
    factorTwoEndpointPhaseDiagonal
        (factorTwoIntrinsicSixOddTail c1 c3 c5) (-sigma) =
      factorTwoIntrinsicSixStaticOdd sigma c1 c3 c5 := by
  have h := factorTwoEndpointChannelPhase_intrinsicSix_eq_static_coordinates
    0 0 0 c1 c3 c5 (-sigma) 0
  have he : factorTwoEvenStructuralLowProfile 0 0 +
      factorTwoIntrinsicSixEvenTail 0 = (0 : ℝ → ℝ) := by
    funext x
    unfold factorTwoEvenStructuralLowProfile factorTwoIntrinsicSixEvenTail
      centeredEvenP0
    simp
  rw [factorTwoEndpointChannelPhase_eq_diagonals, he] at h
  have hzero : factorTwoEndpointPhaseDiagonal (0 : ℝ → ℝ) (-sigma) = 0 := by
    simpa using
      (factorTwoEndpointPhaseDiagonal_smul (-sigma) 0 centeredEvenP0)
  have hcross : factorTwoCenteredAlternatingCoupling
      (0 : ℝ → ℝ) (factorTwoIntrinsicSixOddTail c1 c3 c5) = 0 := by
    simpa using (factorTwoCenteredAlternatingCoupling_smul_left 0
      centeredEvenP0 (factorTwoIntrinsicSixOddTail c1 c3 c5))
  rw [hzero, hcross] at h
  simpa [factorTwoIntrinsicSixStaticEven] using h

private theorem factorTwoEndpointPhaseDiagonal_intrinsicNineEven_eq
    (sigma c0 c2 c4 c6 c8 : ℝ) :
    factorTwoEndpointPhaseDiagonal
        (factorTwoIntrinsicNineEvenProfile c0 c2 c4 c6 c8) sigma =
      factorTwoIntrinsicSixStaticEven sigma c0 c2 c4 +
        2 * c6 * (c0 * factorTwoIntrinsicNinePhasePair sigma
            centeredEvenP0 factorTwoCenteredP6 +
          c2 * factorTwoIntrinsicNinePhasePair sigma
            centeredEvenP2 factorTwoCenteredP6 +
          c4 * factorTwoIntrinsicNinePhasePair sigma
            factorTwoCenteredP4 factorTwoCenteredP6) +
        2 * c8 * (c0 * factorTwoIntrinsicNinePhasePair sigma
            centeredEvenP0 factorTwoCenteredP8 +
          c2 * factorTwoIntrinsicNinePhasePair sigma
            centeredEvenP2 factorTwoCenteredP8 +
          c4 * factorTwoIntrinsicNinePhasePair sigma
            factorTwoCenteredP4 factorTwoCenteredP8) +
        c6 ^ 2 * factorTwoEndpointPhaseDiagonal factorTwoCenteredP6 sigma +
        2 * c6 * c8 * factorTwoIntrinsicNinePhasePair sigma
          factorTwoCenteredP6 factorTwoCenteredP8 +
        c8 ^ 2 * factorTwoEndpointPhaseDiagonal factorTwoCenteredP8 sigma := by
  let e0 := c0 • centeredEvenP0
  let e2 := c2 • centeredEvenP2
  let e4 := c4 • factorTwoCenteredP4
  let e6 := c6 • factorTwoCenteredP6
  let e8 := c8 • factorTwoCenteredP8
  have h0 : Continuous e0 := by
    dsimp only [e0]
    exact continuous_const_smul_of_contDiff c0 centeredEvenP0
      contDiff_centeredEvenP0
  have h2 : Continuous e2 := by
    dsimp only [e2]
    exact continuous_const_smul_of_contDiff c2 centeredEvenP2
      contDiff_centeredEvenP2
  have h4 : Continuous e4 := by
    dsimp only [e4]
    exact continuous_const_smul_of_contDiff c4 factorTwoCenteredP4
      contDiff_factorTwoCenteredP4
  have h6 : Continuous e6 := by
    dsimp only [e6]
    exact continuous_const_smul_of_contDiff c6 factorTwoCenteredP6
      contDiff_factorTwoCenteredP6
  have h8 : Continuous e8 := by
    dsimp only [e8]
    exact continuous_const_smul_of_contDiff c8 factorTwoCenteredP8
      contDiff_factorTwoCenteredP8
  have h0L : LocallyLipschitzOn (Icc (-1 : ℝ) 1) e0 := by
    dsimp only [e0]
    exact locallyLipschitzOn_const_smul_of_contDiff c0 centeredEvenP0
      contDiff_centeredEvenP0
  have h2L : LocallyLipschitzOn (Icc (-1 : ℝ) 1) e2 := by
    dsimp only [e2]
    exact locallyLipschitzOn_const_smul_of_contDiff c2 centeredEvenP2
      contDiff_centeredEvenP2
  have h4L : LocallyLipschitzOn (Icc (-1 : ℝ) 1) e4 := by
    dsimp only [e4]
    exact locallyLipschitzOn_const_smul_of_contDiff c4 factorTwoCenteredP4
      contDiff_factorTwoCenteredP4
  have h6L : LocallyLipschitzOn (Icc (-1 : ℝ) 1) e6 := by
    dsimp only [e6]
    exact locallyLipschitzOn_const_smul_of_contDiff c6 factorTwoCenteredP6
      contDiff_factorTwoCenteredP6
  have h8L : LocallyLipschitzOn (Icc (-1 : ℝ) 1) e8 := by
    dsimp only [e8]
    exact locallyLipschitzOn_const_smul_of_contDiff c8 factorTwoCenteredP8
      contDiff_factorTwoCenteredP8
  let eBase := (e0 + e2) + e4
  have hBase : Continuous eBase := (h0.add h2).add h4
  have hBaseL : LocallyLipschitzOn (Icc (-1 : ℝ) 1) eBase :=
    (h0L.add h2L).add h4L
  have hprofile : factorTwoIntrinsicNineEvenProfile c0 c2 c4 c6 c8 =
      (eBase + e6) + e8 := by
    funext x
    unfold factorTwoIntrinsicNineEvenProfile factorTwoIntrinsicEightEvenProfile
      factorTwoEvenStructuralLowProfile factorTwoIntrinsicSixEvenTail
    dsimp only [eBase, e0, e2, e4, e6, e8]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hprofile,
    factorTwoEndpointPhaseDiagonal_add sigma (eBase + e6) e8
      (hBase.add h6) h8 (hBaseL.add h6L) h8L,
    factorTwoEndpointPhaseDiagonal_add sigma eBase e6
      hBase h6 hBaseL h6L,
    factorTwoIntrinsicNinePhasePair_add_left sigma eBase e6 e8
      hBase h6 h8 hBaseL h6L h8L,
    factorTwoIntrinsicNinePhasePair_add_left sigma (e0 + e2) e4 e6
      (h0.add h2) h4 h6 (h0L.add h2L) h4L h6L,
    factorTwoIntrinsicNinePhasePair_add_left sigma e0 e2 e6
      h0 h2 h6 h0L h2L h6L,
    factorTwoIntrinsicNinePhasePair_add_left sigma (e0 + e2) e4 e8
      (h0.add h2) h4 h8 (h0L.add h2L) h4L h8L,
    factorTwoIntrinsicNinePhasePair_add_left sigma e0 e2 e8
      h0 h2 h8 h0L h2L h8L]
  have hbase := factorTwoEndpointPhaseDiagonal_intrinsicSixEven_eq
    sigma c0 c2 c4
  have hbaseProfile : factorTwoEvenStructuralLowProfile c0 c2 +
      factorTwoIntrinsicSixEvenTail c4 = eBase := by
    funext x
    unfold factorTwoEvenStructuralLowProfile factorTwoIntrinsicSixEvenTail
    dsimp only [eBase, e0, e2, e4]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hbaseProfile] at hbase
  rw [← hbase]
  repeat rw [factorTwoEndpointPhaseDiagonal_smul]
  repeat rw [factorTwoIntrinsicNinePhasePair_smul_smul]
  ring

private theorem factorTwoEndpointPhaseDiagonal_intrinsicNineOdd_eq
    (sigma c1 c3 c5 c7 : ℝ) :
    factorTwoEndpointPhaseDiagonal
        (factorTwoIntrinsicNineOddProfile c1 c3 c5 c7) (-sigma) =
      factorTwoIntrinsicSixStaticOdd sigma c1 c3 c5 +
        2 * c7 * (c1 * factorTwoIntrinsicNinePhasePair (-sigma)
            centeredP1 factorTwoCenteredP7 +
          c3 * factorTwoIntrinsicNinePhasePair (-sigma)
            centeredP3 factorTwoCenteredP7 +
          c5 * factorTwoIntrinsicNinePhasePair (-sigma)
            factorTwoCenteredP5 factorTwoCenteredP7) +
        c7 ^ 2 * factorTwoEndpointPhaseDiagonal factorTwoCenteredP7 (-sigma) := by
  let o1 := c1 • centeredP1
  let o3 := c3 • centeredP3
  let o5 := c5 • factorTwoCenteredP5
  let o7 := c7 • factorTwoCenteredP7
  have h1 : Continuous o1 := by
    dsimp only [o1]
    exact continuous_const_smul_of_contDiff c1 centeredP1 contDiff_centeredP1
  have h3 : Continuous o3 := by
    dsimp only [o3]
    exact continuous_const_smul_of_contDiff c3 centeredP3 contDiff_centeredP3
  have h5 : Continuous o5 := by
    dsimp only [o5]
    exact continuous_const_smul_of_contDiff c5 factorTwoCenteredP5
      contDiff_factorTwoCenteredP5
  have h7 : Continuous o7 := by
    dsimp only [o7]
    exact continuous_const_smul_of_contDiff c7 factorTwoCenteredP7
      contDiff_factorTwoCenteredP7
  have h1L : LocallyLipschitzOn (Icc (-1 : ℝ) 1) o1 := by
    dsimp only [o1]
    exact locallyLipschitzOn_const_smul_of_contDiff c1 centeredP1
      contDiff_centeredP1
  have h3L : LocallyLipschitzOn (Icc (-1 : ℝ) 1) o3 := by
    dsimp only [o3]
    exact locallyLipschitzOn_const_smul_of_contDiff c3 centeredP3
      contDiff_centeredP3
  have h5L : LocallyLipschitzOn (Icc (-1 : ℝ) 1) o5 := by
    dsimp only [o5]
    exact locallyLipschitzOn_const_smul_of_contDiff c5 factorTwoCenteredP5
      contDiff_factorTwoCenteredP5
  have h7L : LocallyLipschitzOn (Icc (-1 : ℝ) 1) o7 := by
    dsimp only [o7]
    exact locallyLipschitzOn_const_smul_of_contDiff c7 factorTwoCenteredP7
      contDiff_factorTwoCenteredP7
  let oBase := (o1 + o3) + o5
  have hBase : Continuous oBase := (h1.add h3).add h5
  have hBaseL : LocallyLipschitzOn (Icc (-1 : ℝ) 1) oBase :=
    (h1L.add h3L).add h5L
  have hprofile : factorTwoIntrinsicNineOddProfile c1 c3 c5 c7 =
      oBase + o7 := by
    funext x
    unfold factorTwoIntrinsicNineOddProfile factorTwoIntrinsicEightOddProfile
      factorTwoIntrinsicSixOddTail factorTwoOddStructuralLowProfile
    dsimp only [oBase, o1, o3, o5, o7]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hprofile,
    factorTwoEndpointPhaseDiagonal_add (-sigma) oBase o7
      hBase h7 hBaseL h7L,
    factorTwoIntrinsicNinePhasePair_add_left (-sigma) (o1 + o3) o5 o7
      (h1.add h3) h5 h7 (h1L.add h3L) h5L h7L,
    factorTwoIntrinsicNinePhasePair_add_left (-sigma) o1 o3 o7
      h1 h3 h7 h1L h3L h7L]
  have hbase := factorTwoEndpointPhaseDiagonal_intrinsicSixOdd_eq
    sigma c1 c3 c5
  have hbaseProfile : factorTwoIntrinsicSixOddTail c1 c3 c5 =
      oBase := by
    funext x
    unfold factorTwoIntrinsicSixOddTail factorTwoOddStructuralLowProfile
    dsimp only [oBase, o1, o3, o5]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hbaseProfile] at hbase
  rw [← hbase]
  repeat rw [factorTwoEndpointPhaseDiagonal_smul]
  repeat rw [factorTwoIntrinsicNinePhasePair_smul_smul]
  ring

private theorem factorTwoCenteredAlternatingCoupling_intrinsicSix_eq
    (c0 c2 c4 c1 c3 c5 : ℝ) :
    factorTwoCenteredAlternatingCoupling
        (factorTwoEvenStructuralLowProfile c0 c2 +
          factorTwoIntrinsicSixEvenTail c4)
        (factorTwoIntrinsicSixOddTail c1 c3 c5) =
      factorTwoIntrinsicSixStaticAlternating c0 c2 c4 c1 c3 c5 := by
  have h1 := factorTwoEndpointChannelPhase_intrinsicSix_eq_static_coordinates
    c0 c2 c4 c1 c3 c5 0 1
  have h0 := factorTwoEndpointChannelPhase_intrinsicSix_eq_static_coordinates
    c0 c2 c4 c1 c3 c5 0 0
  rw [factorTwoEndpointChannelPhase_eq_diagonals] at h1 h0
  linarith

/-- Exact alternating-channel expansion on the retained nine modes.  It is
obtained from bilinearity and the already-proved six-mode coordinate
identity, rather than by evaluating any endpoint integral. -/
theorem factorTwoCenteredAlternatingCoupling_intrinsicNine_eq
    (c0 c2 c4 c6 c8 c1 c3 c5 c7 : ℝ) :
    factorTwoCenteredAlternatingCoupling
        (factorTwoIntrinsicNineEvenProfile c0 c2 c4 c6 c8)
        (factorTwoIntrinsicNineOddProfile c1 c3 c5 c7) =
      factorTwoIntrinsicSixStaticAlternating c0 c2 c4 c1 c3 c5 +
        c7 * (c0 * factorTwoCenteredAlternatingCoupling
            centeredEvenP0 factorTwoCenteredP7 +
          c2 * factorTwoCenteredAlternatingCoupling
            centeredEvenP2 factorTwoCenteredP7 +
          c4 * factorTwoCenteredAlternatingCoupling
            factorTwoCenteredP4 factorTwoCenteredP7) +
        c6 * (c1 * factorTwoCenteredAlternatingCoupling
            factorTwoCenteredP6 centeredP1 +
          c3 * factorTwoCenteredAlternatingCoupling
            factorTwoCenteredP6 centeredP3 +
          c5 * factorTwoCenteredAlternatingCoupling
            factorTwoCenteredP6 factorTwoCenteredP5) +
        c6 * c7 * factorTwoCenteredAlternatingCoupling
          factorTwoCenteredP6 factorTwoCenteredP7 +
        c8 * (c1 * factorTwoCenteredAlternatingCoupling
            factorTwoCenteredP8 centeredP1 +
          c3 * factorTwoCenteredAlternatingCoupling
            factorTwoCenteredP8 centeredP3 +
          c5 * factorTwoCenteredAlternatingCoupling
            factorTwoCenteredP8 factorTwoCenteredP5) +
        c8 * c7 * factorTwoCenteredAlternatingCoupling
          factorTwoCenteredP8 factorTwoCenteredP7 := by
  let e0 := c0 • centeredEvenP0
  let e2 := c2 • centeredEvenP2
  let e4 := c4 • factorTwoCenteredP4
  let e6 := c6 • factorTwoCenteredP6
  let e8 := c8 • factorTwoCenteredP8
  let o1 := c1 • centeredP1
  let o3 := c3 • centeredP3
  let o5 := c5 • factorTwoCenteredP5
  let o7 := c7 • factorTwoCenteredP7
  let eBase := (e0 + e2) + e4
  let oBase := (o1 + o3) + o5
  have he0 : Continuous e0 := by
    dsimp only [e0]
    exact continuous_const_smul_of_contDiff c0 centeredEvenP0
      contDiff_centeredEvenP0
  have he2 : Continuous e2 := by
    dsimp only [e2]
    exact continuous_const_smul_of_contDiff c2 centeredEvenP2
      contDiff_centeredEvenP2
  have he4 : Continuous e4 := by
    dsimp only [e4]
    exact continuous_const_smul_of_contDiff c4 factorTwoCenteredP4
      contDiff_factorTwoCenteredP4
  have he6 : Continuous e6 := by
    dsimp only [e6]
    exact continuous_const_smul_of_contDiff c6 factorTwoCenteredP6
      contDiff_factorTwoCenteredP6
  have he8 : Continuous e8 := by
    dsimp only [e8]
    exact continuous_const_smul_of_contDiff c8 factorTwoCenteredP8
      contDiff_factorTwoCenteredP8
  have ho1 : Continuous o1 := by
    dsimp only [o1]
    exact continuous_const_smul_of_contDiff c1 centeredP1 contDiff_centeredP1
  have ho3 : Continuous o3 := by
    dsimp only [o3]
    exact continuous_const_smul_of_contDiff c3 centeredP3 contDiff_centeredP3
  have ho5 : Continuous o5 := by
    dsimp only [o5]
    exact continuous_const_smul_of_contDiff c5 factorTwoCenteredP5
      contDiff_factorTwoCenteredP5
  have ho7 : Continuous o7 := by
    dsimp only [o7]
    exact continuous_const_smul_of_contDiff c7 factorTwoCenteredP7
      contDiff_factorTwoCenteredP7
  have heBase : Continuous eBase := (he0.add he2).add he4
  have hoBase : Continuous oBase := (ho1.add ho3).add ho5
  have heProfile : factorTwoIntrinsicNineEvenProfile c0 c2 c4 c6 c8 =
      (eBase + e6) + e8 := by
    funext x
    unfold factorTwoIntrinsicNineEvenProfile factorTwoIntrinsicEightEvenProfile
      factorTwoEvenStructuralLowProfile factorTwoIntrinsicSixEvenTail
    dsimp only [eBase, e0, e2, e4, e6, e8]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hoProfile : factorTwoIntrinsicNineOddProfile c1 c3 c5 c7 =
      oBase + o7 := by
    funext x
    unfold factorTwoIntrinsicNineOddProfile factorTwoIntrinsicEightOddProfile
      factorTwoIntrinsicSixOddTail factorTwoOddStructuralLowProfile
    dsimp only [oBase, o1, o3, o5, o7]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hbase := factorTwoCenteredAlternatingCoupling_intrinsicSix_eq
    c0 c2 c4 c1 c3 c5
  have heBaseProfile : factorTwoEvenStructuralLowProfile c0 c2 +
      factorTwoIntrinsicSixEvenTail c4 = eBase := by
    funext x
    unfold factorTwoEvenStructuralLowProfile factorTwoIntrinsicSixEvenTail
    dsimp only [eBase, e0, e2, e4]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hoBaseProfile : factorTwoIntrinsicSixOddTail c1 c3 c5 = oBase := by
    funext x
    unfold factorTwoIntrinsicSixOddTail factorTwoOddStructuralLowProfile
    dsimp only [oBase, o1, o3, o5]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [heBaseProfile, hoBaseProfile] at hbase
  rw [heProfile, hoProfile,
    factorTwoCenteredAlternatingCoupling_add_left
      (eBase + e6) e8 (oBase + o7)
      (heBase.add he6) he8 (hoBase.add ho7),
    factorTwoCenteredAlternatingCoupling_add_left
      eBase e6 (oBase + o7) heBase he6 (hoBase.add ho7),
    factorTwoCenteredAlternatingCoupling_add_right
      eBase oBase o7 heBase hoBase ho7,
    factorTwoCenteredAlternatingCoupling_add_right
      e6 oBase o7 he6 hoBase ho7,
    factorTwoCenteredAlternatingCoupling_add_right
      e8 oBase o7 he8 hoBase ho7,
    factorTwoCenteredAlternatingCoupling_add_left
      (e0 + e2) e4 o7 (he0.add he2) he4 ho7,
    factorTwoCenteredAlternatingCoupling_add_left
      e0 e2 o7 he0 he2 ho7,
    factorTwoCenteredAlternatingCoupling_add_right
      e6 (o1 + o3) o5 he6 (ho1.add ho3) ho5,
    factorTwoCenteredAlternatingCoupling_add_right
      e6 o1 o3 he6 ho1 ho3,
    factorTwoCenteredAlternatingCoupling_add_right
      e8 (o1 + o3) o5 he8 (ho1.add ho3) ho5,
    factorTwoCenteredAlternatingCoupling_add_right
      e8 o1 o3 he8 ho1 ho3,
    hbase]
  repeat rw [factorTwoCenteredAlternatingCoupling_smul_left]
  repeat rw [factorTwoCenteredAlternatingCoupling_smul_right]
  ring

/-- The endpoint cross entry between two even retained modes. -/
def factorTwoIntrinsicNineEvenEntry
    (sigma : ℝ) (u v : ℝ → ℝ) : ℝ :=
  factorTwoIntrinsicNinePhasePair sigma u v

/-- The endpoint cross entry between two odd retained modes.  The odd
diagonal is evaluated at the opposite signed endpoint. -/
def factorTwoIntrinsicNineOddEntry
    (sigma : ℝ) (u v : ℝ → ℝ) : ℝ :=
  factorTwoIntrinsicNinePhasePair (-sigma) u v

/-- Off-diagonal convention for the corrected plus endpoint. -/
def factorTwoIntrinsicNineKPlusEntry
    (h : ℝ) (e o : ℝ → ℝ) : ℝ :=
  factorTwoCenteredAlternatingCoupling e o / 2 - h

/-- Off-diagonal convention for the corrected minus endpoint. -/
def factorTwoIntrinsicNineKMinusEntry
    (h : ℝ) (e o : ℝ → ℝ) : ℝ :=
  factorTwoCenteredAlternatingCoupling e o / 2 + h

def factorTwoIntrinsicNineReserve6 : ℝ := 1 / 650
def factorTwoIntrinsicNineReserve8 : ℝ := 33 / 850
def factorTwoIntrinsicNineReserve7 : ℝ := 1 / 750

/-! ### New even endpoint rows -/

def factorTwoIntrinsicNineEPlus06 : ℝ :=
  factorTwoIntrinsicNineEvenEntry 1 centeredEvenP0 factorTwoCenteredP6
def factorTwoIntrinsicNineEPlus08 : ℝ :=
  factorTwoIntrinsicNineEvenEntry 1 centeredEvenP0 factorTwoCenteredP8
def factorTwoIntrinsicNineEPlus26 : ℝ :=
  factorTwoIntrinsicNineEvenEntry 1 centeredEvenP2 factorTwoCenteredP6
def factorTwoIntrinsicNineEPlus28 : ℝ :=
  factorTwoIntrinsicNineEvenEntry 1 centeredEvenP2 factorTwoCenteredP8
def factorTwoIntrinsicNineEPlus46 : ℝ :=
  factorTwoIntrinsicNineEvenEntry 1 factorTwoCenteredP4 factorTwoCenteredP6
def factorTwoIntrinsicNineEPlus48 : ℝ :=
  factorTwoIntrinsicNineEvenEntry 1 factorTwoCenteredP4 factorTwoCenteredP8
def factorTwoIntrinsicNineEPlus66 : ℝ :=
  factorTwoEndpointPhaseDiagonal factorTwoCenteredP6 1
def factorTwoIntrinsicNineEPlus68 : ℝ :=
  factorTwoIntrinsicNineEvenEntry 1 factorTwoCenteredP6 factorTwoCenteredP8
def factorTwoIntrinsicNineEPlus88 : ℝ :=
  factorTwoEndpointPhaseDiagonal factorTwoCenteredP8 1

def factorTwoIntrinsicNineEMinus06 : ℝ :=
  factorTwoIntrinsicNineEvenEntry (-1) centeredEvenP0 factorTwoCenteredP6
def factorTwoIntrinsicNineEMinus08 : ℝ :=
  factorTwoIntrinsicNineEvenEntry (-1) centeredEvenP0 factorTwoCenteredP8
def factorTwoIntrinsicNineEMinus26 : ℝ :=
  factorTwoIntrinsicNineEvenEntry (-1) centeredEvenP2 factorTwoCenteredP6
def factorTwoIntrinsicNineEMinus28 : ℝ :=
  factorTwoIntrinsicNineEvenEntry (-1) centeredEvenP2 factorTwoCenteredP8
def factorTwoIntrinsicNineEMinus46 : ℝ :=
  factorTwoIntrinsicNineEvenEntry (-1) factorTwoCenteredP4 factorTwoCenteredP6
def factorTwoIntrinsicNineEMinus48 : ℝ :=
  factorTwoIntrinsicNineEvenEntry (-1) factorTwoCenteredP4 factorTwoCenteredP8
def factorTwoIntrinsicNineEMinus66 : ℝ :=
  factorTwoEndpointPhaseDiagonal factorTwoCenteredP6 (-1)
def factorTwoIntrinsicNineEMinus68 : ℝ :=
  factorTwoIntrinsicNineEvenEntry (-1) factorTwoCenteredP6 factorTwoCenteredP8
def factorTwoIntrinsicNineEMinus88 : ℝ :=
  factorTwoEndpointPhaseDiagonal factorTwoCenteredP8 (-1)

/-! ### New odd endpoint row -/

def factorTwoIntrinsicNineOMinus17 : ℝ :=
  factorTwoIntrinsicNineOddEntry 1 centeredP1 factorTwoCenteredP7
def factorTwoIntrinsicNineOMinus37 : ℝ :=
  factorTwoIntrinsicNineOddEntry 1 centeredP3 factorTwoCenteredP7
def factorTwoIntrinsicNineOMinus57 : ℝ :=
  factorTwoIntrinsicNineOddEntry 1 factorTwoCenteredP5 factorTwoCenteredP7
def factorTwoIntrinsicNineOMinus77 : ℝ :=
  factorTwoEndpointPhaseDiagonal factorTwoCenteredP7 (-1)

def factorTwoIntrinsicNineOPlus17 : ℝ :=
  factorTwoIntrinsicNineOddEntry (-1) centeredP1 factorTwoCenteredP7
def factorTwoIntrinsicNineOPlus37 : ℝ :=
  factorTwoIntrinsicNineOddEntry (-1) centeredP3 factorTwoCenteredP7
def factorTwoIntrinsicNineOPlus57 : ℝ :=
  factorTwoIntrinsicNineOddEntry (-1) factorTwoCenteredP5 factorTwoCenteredP7
def factorTwoIntrinsicNineOPlus77 : ℝ :=
  factorTwoEndpointPhaseDiagonal factorTwoCenteredP7 1

/-! ### The eleven variable transfer entries -/

def factorTwoIntrinsicNineKPlus07 (h07 : ℝ) : ℝ :=
  factorTwoIntrinsicNineKPlusEntry h07 centeredEvenP0 factorTwoCenteredP7
def factorTwoIntrinsicNineKPlus27 (h27 : ℝ) : ℝ :=
  factorTwoIntrinsicNineKPlusEntry h27 centeredEvenP2 factorTwoCenteredP7
def factorTwoIntrinsicNineKPlus47 (h47 : ℝ) : ℝ :=
  factorTwoIntrinsicNineKPlusEntry h47 factorTwoCenteredP4 factorTwoCenteredP7
def factorTwoIntrinsicNineKPlus61 (h61 : ℝ) : ℝ :=
  factorTwoIntrinsicNineKPlusEntry h61 factorTwoCenteredP6 centeredP1
def factorTwoIntrinsicNineKPlus63 (h63 : ℝ) : ℝ :=
  factorTwoIntrinsicNineKPlusEntry h63 factorTwoCenteredP6 centeredP3
def factorTwoIntrinsicNineKPlus65 (h65 : ℝ) : ℝ :=
  factorTwoIntrinsicNineKPlusEntry h65 factorTwoCenteredP6 factorTwoCenteredP5
def factorTwoIntrinsicNineKPlus67 (h67 : ℝ) : ℝ :=
  factorTwoIntrinsicNineKPlusEntry h67 factorTwoCenteredP6 factorTwoCenteredP7
def factorTwoIntrinsicNineKPlus81 (h81 : ℝ) : ℝ :=
  factorTwoIntrinsicNineKPlusEntry h81 factorTwoCenteredP8 centeredP1
def factorTwoIntrinsicNineKPlus83 (h83 : ℝ) : ℝ :=
  factorTwoIntrinsicNineKPlusEntry h83 factorTwoCenteredP8 centeredP3
def factorTwoIntrinsicNineKPlus85 (h85 : ℝ) : ℝ :=
  factorTwoIntrinsicNineKPlusEntry h85 factorTwoCenteredP8 factorTwoCenteredP5
def factorTwoIntrinsicNineKPlus87 (h87 : ℝ) : ℝ :=
  factorTwoIntrinsicNineKPlusEntry h87 factorTwoCenteredP8 factorTwoCenteredP7

def factorTwoIntrinsicNineKMinus07 (h07 : ℝ) : ℝ :=
  factorTwoIntrinsicNineKMinusEntry h07 centeredEvenP0 factorTwoCenteredP7
def factorTwoIntrinsicNineKMinus27 (h27 : ℝ) : ℝ :=
  factorTwoIntrinsicNineKMinusEntry h27 centeredEvenP2 factorTwoCenteredP7
def factorTwoIntrinsicNineKMinus47 (h47 : ℝ) : ℝ :=
  factorTwoIntrinsicNineKMinusEntry h47 factorTwoCenteredP4 factorTwoCenteredP7
def factorTwoIntrinsicNineKMinus61 (h61 : ℝ) : ℝ :=
  factorTwoIntrinsicNineKMinusEntry h61 factorTwoCenteredP6 centeredP1
def factorTwoIntrinsicNineKMinus63 (h63 : ℝ) : ℝ :=
  factorTwoIntrinsicNineKMinusEntry h63 factorTwoCenteredP6 centeredP3
def factorTwoIntrinsicNineKMinus65 (h65 : ℝ) : ℝ :=
  factorTwoIntrinsicNineKMinusEntry h65 factorTwoCenteredP6 factorTwoCenteredP5
def factorTwoIntrinsicNineKMinus67 (h67 : ℝ) : ℝ :=
  factorTwoIntrinsicNineKMinusEntry h67 factorTwoCenteredP6 factorTwoCenteredP7
def factorTwoIntrinsicNineKMinus81 (h81 : ℝ) : ℝ :=
  factorTwoIntrinsicNineKMinusEntry h81 factorTwoCenteredP8 centeredP1
def factorTwoIntrinsicNineKMinus83 (h83 : ℝ) : ℝ :=
  factorTwoIntrinsicNineKMinusEntry h83 factorTwoCenteredP8 centeredP3
def factorTwoIntrinsicNineKMinus85 (h85 : ℝ) : ℝ :=
  factorTwoIntrinsicNineKMinusEntry h85 factorTwoCenteredP8 factorTwoCenteredP5
def factorTwoIntrinsicNineKMinus87 (h87 : ℝ) : ℝ :=
  factorTwoIntrinsicNineKMinusEntry h87 factorTwoCenteredP8 factorTwoCenteredP7

/-! ## Fraction-free `T`, `R`, `U`, and `W` blocks -/

/-- One entry of `R = det(E) F - Bᵀ adj(E) D`. -/
def factorTwoIntrinsicNineRentry
    (d a00 a01 a02 a11 a12 a22
      f b0 b1 b2 n0 n1 n2 : ℝ) : ℝ :=
  d * f - unbalancedThreeAdjugatePair
    a00 a01 a02 a11 a12 a22 b0 b1 b2 n0 n1 n2

/-- One entry of `U = det(E) G - Dᵀ adj(E) D`. -/
def factorTwoIntrinsicNineUentry
    (d a00 a01 a02 a11 a12 a22
      g u0 u1 u2 v0 v1 v2 : ℝ) : ℝ :=
  d * g - unbalancedThreeAdjugatePair
    a00 a01 a02 a11 a12 a22 u0 u1 u2 v0 v1 v2

/-- One entry of the final block `W = det(T) U - Rᵀ adj(T) R`. -/
def factorTwoIntrinsicNineWentry
    (t00 t01 t02 t11 t12 t22
      u r0 r1 r2 s0 s1 s2 : ℝ) : ℝ :=
  symmetricDeterminant t00 t01 t02 t11 t12 t22 * u -
    unbalancedThreeAdjugatePair
      t00 t01 t02 t11 t12 t22 r0 r1 r2 s0 s1 s2

/-! The following small indexed tables merely keep the displayed Schur
formulas readable.  Indices `0,1,2` mean `P1,P3,P5` in an `O` table and
`P6,P8,P7` in an `N` table. -/

def factorTwoIntrinsicNineBPlus (i r : Fin 3) : ℝ :=
  match i.1, r.1 with
  | 0, 0 => factorTwoIntrinsicSixUnbalancedKPlus01
  | 0, 1 => factorTwoIntrinsicSixUnbalancedKPlus21
  | 0, _ => factorTwoIntrinsicSixUnbalancedKPlus41
  | 1, 0 => factorTwoIntrinsicSixUnbalancedKPlus03
  | 1, 1 => factorTwoIntrinsicSixUnbalancedKPlus23
  | 1, _ => factorTwoIntrinsicSixUnbalancedKPlus43
  | _, 0 => factorTwoIntrinsicSixUnbalancedKPlus05
  | _, 1 => factorTwoIntrinsicSixUnbalancedKPlus25
  | _, _ => factorTwoIntrinsicSixUnbalancedKPlus45

def factorTwoIntrinsicNineBMinus (i r : Fin 3) : ℝ :=
  match i.1, r.1 with
  | 0, 0 => factorTwoIntrinsicSixUnbalancedKMinus01
  | 0, 1 => factorTwoIntrinsicSixUnbalancedKMinus21
  | 0, _ => factorTwoIntrinsicSixUnbalancedKMinus41
  | 1, 0 => factorTwoIntrinsicSixUnbalancedKMinus03
  | 1, 1 => factorTwoIntrinsicSixUnbalancedKMinus23
  | 1, _ => factorTwoIntrinsicSixUnbalancedKMinus43
  | _, 0 => factorTwoIntrinsicSixUnbalancedKMinus05
  | _, 1 => factorTwoIntrinsicSixUnbalancedKMinus25
  | _, _ => factorTwoIntrinsicSixUnbalancedKMinus45

def factorTwoIntrinsicNineDPlus
    (h07 h27 h47 : ℝ) (n r : Fin 3) : ℝ :=
  match n.1, r.1 with
  | 0, 0 => factorTwoIntrinsicNineEPlus06
  | 0, 1 => factorTwoIntrinsicNineEPlus26
  | 0, _ => factorTwoIntrinsicNineEPlus46
  | 1, 0 => factorTwoIntrinsicNineEPlus08
  | 1, 1 => factorTwoIntrinsicNineEPlus28
  | 1, _ => factorTwoIntrinsicNineEPlus48
  | _, 0 => factorTwoIntrinsicNineKPlus07 h07
  | _, 1 => factorTwoIntrinsicNineKPlus27 h27
  | _, _ => factorTwoIntrinsicNineKPlus47 h47

def factorTwoIntrinsicNineDMinus
    (h07 h27 h47 : ℝ) (n r : Fin 3) : ℝ :=
  match n.1, r.1 with
  | 0, 0 => factorTwoIntrinsicNineEMinus06
  | 0, 1 => factorTwoIntrinsicNineEMinus26
  | 0, _ => factorTwoIntrinsicNineEMinus46
  | 1, 0 => factorTwoIntrinsicNineEMinus08
  | 1, 1 => factorTwoIntrinsicNineEMinus28
  | 1, _ => factorTwoIntrinsicNineEMinus48
  | _, 0 => factorTwoIntrinsicNineKMinus07 h07
  | _, 1 => factorTwoIntrinsicNineKMinus27 h27
  | _, _ => factorTwoIntrinsicNineKMinus47 h47

def factorTwoIntrinsicNineFPlus
    (h61 h63 h65 h81 h83 h85 : ℝ) (i n : Fin 3) : ℝ :=
  match i.1, n.1 with
  | 0, 0 => factorTwoIntrinsicNineKPlus61 h61
  | 1, 0 => factorTwoIntrinsicNineKPlus63 h63
  | _, 0 => factorTwoIntrinsicNineKPlus65 h65
  | 0, 1 => factorTwoIntrinsicNineKPlus81 h81
  | 1, 1 => factorTwoIntrinsicNineKPlus83 h83
  | _, 1 => factorTwoIntrinsicNineKPlus85 h85
  | 0, _ => factorTwoIntrinsicNineOMinus17
  | 1, _ => factorTwoIntrinsicNineOMinus37
  | _, _ => factorTwoIntrinsicNineOMinus57

def factorTwoIntrinsicNineFMinus
    (h61 h63 h65 h81 h83 h85 : ℝ) (i n : Fin 3) : ℝ :=
  match i.1, n.1 with
  | 0, 0 => factorTwoIntrinsicNineKMinus61 h61
  | 1, 0 => factorTwoIntrinsicNineKMinus63 h63
  | _, 0 => factorTwoIntrinsicNineKMinus65 h65
  | 0, 1 => factorTwoIntrinsicNineKMinus81 h81
  | 1, 1 => factorTwoIntrinsicNineKMinus83 h83
  | _, 1 => factorTwoIntrinsicNineKMinus85 h85
  | 0, _ => factorTwoIntrinsicNineOPlus17
  | 1, _ => factorTwoIntrinsicNineOPlus37
  | _, _ => factorTwoIntrinsicNineOPlus57

def factorTwoIntrinsicNineGPlus
    (h67 h87 : ℝ) (n m : Fin 3) : ℝ :=
  match n.1, m.1 with
  | 0, 0 => factorTwoIntrinsicNineEPlus66 - factorTwoIntrinsicNineReserve6
  | 0, 1 => factorTwoIntrinsicNineEPlus68
  | 1, 0 => factorTwoIntrinsicNineEPlus68
  | 0, _ => factorTwoIntrinsicNineKPlus67 h67
  | _, 0 => factorTwoIntrinsicNineKPlus67 h67
  | 1, 1 => factorTwoIntrinsicNineEPlus88 - factorTwoIntrinsicNineReserve8
  | 1, _ => factorTwoIntrinsicNineKPlus87 h87
  | _, 1 => factorTwoIntrinsicNineKPlus87 h87
  | _, _ => factorTwoIntrinsicNineOMinus77 - factorTwoIntrinsicNineReserve7

def factorTwoIntrinsicNineGMinus
    (h67 h87 : ℝ) (n m : Fin 3) : ℝ :=
  match n.1, m.1 with
  | 0, 0 => factorTwoIntrinsicNineEMinus66 - factorTwoIntrinsicNineReserve6
  | 0, 1 => factorTwoIntrinsicNineEMinus68
  | 1, 0 => factorTwoIntrinsicNineEMinus68
  | 0, _ => factorTwoIntrinsicNineKMinus67 h67
  | _, 0 => factorTwoIntrinsicNineKMinus67 h67
  | 1, 1 => factorTwoIntrinsicNineEMinus88 - factorTwoIntrinsicNineReserve8
  | 1, _ => factorTwoIntrinsicNineKMinus87 h87
  | _, 1 => factorTwoIntrinsicNineKMinus87 h87
  | _, _ => factorTwoIntrinsicNineOPlus77 - factorTwoIntrinsicNineReserve7

def factorTwoIntrinsicNineTPlus (i j : Fin 3) : ℝ :=
  match i.1, j.1 with
  | 0, 0 => factorTwoIntrinsicSixUnbalancedTPlus11
  | 0, 1 => factorTwoIntrinsicSixUnbalancedTPlus13
  | 1, 0 => factorTwoIntrinsicSixUnbalancedTPlus13
  | 0, _ => factorTwoIntrinsicSixUnbalancedTPlus15
  | _, 0 => factorTwoIntrinsicSixUnbalancedTPlus15
  | 1, 1 => factorTwoIntrinsicSixUnbalancedTPlus33
  | 1, _ => factorTwoIntrinsicSixUnbalancedTPlus35
  | _, 1 => factorTwoIntrinsicSixUnbalancedTPlus35
  | _, _ => factorTwoIntrinsicSixUnbalancedTPlus55

def factorTwoIntrinsicNineTMinus (i j : Fin 3) : ℝ :=
  match i.1, j.1 with
  | 0, 0 => factorTwoIntrinsicSixUnbalancedTMinus11
  | 0, 1 => factorTwoIntrinsicSixUnbalancedTMinus13
  | 1, 0 => factorTwoIntrinsicSixUnbalancedTMinus13
  | 0, _ => factorTwoIntrinsicSixUnbalancedTMinus15
  | _, 0 => factorTwoIntrinsicSixUnbalancedTMinus15
  | 1, 1 => factorTwoIntrinsicSixUnbalancedTMinus33
  | 1, _ => factorTwoIntrinsicSixUnbalancedTMinus35
  | _, 1 => factorTwoIntrinsicSixUnbalancedTMinus35
  | _, _ => factorTwoIntrinsicSixUnbalancedTMinus55

def factorTwoIntrinsicNineRPlus
    (h07 h27 h47 h61 h63 h65 h81 h83 h85 : ℝ)
    (i n : Fin 3) : ℝ :=
  factorTwoIntrinsicNineRentry
    factorTwoIntrinsicSixUnbalancedEPlusDet
    factorTwoIntrinsicSixUnbalancedEPlus00
    factorTwoIntrinsicSixUnbalancedEPlus02
    factorTwoIntrinsicSixUnbalancedEPlus04
    factorTwoIntrinsicSixUnbalancedEPlus22
    factorTwoIntrinsicSixUnbalancedEPlus24
    factorTwoIntrinsicSixUnbalancedEPlus44
    (factorTwoIntrinsicNineFPlus h61 h63 h65 h81 h83 h85 i n)
    (factorTwoIntrinsicNineBPlus i 0)
    (factorTwoIntrinsicNineBPlus i 1)
    (factorTwoIntrinsicNineBPlus i 2)
    (factorTwoIntrinsicNineDPlus h07 h27 h47 n 0)
    (factorTwoIntrinsicNineDPlus h07 h27 h47 n 1)
    (factorTwoIntrinsicNineDPlus h07 h27 h47 n 2)

def factorTwoIntrinsicNineRMinus
    (h07 h27 h47 h61 h63 h65 h81 h83 h85 : ℝ)
    (i n : Fin 3) : ℝ :=
  factorTwoIntrinsicNineRentry
    factorTwoIntrinsicSixUnbalancedEMinusDet
    factorTwoIntrinsicSixUnbalancedEMinus00
    factorTwoIntrinsicSixUnbalancedEMinus02
    factorTwoIntrinsicSixUnbalancedEMinus04
    factorTwoIntrinsicSixUnbalancedEMinus22
    factorTwoIntrinsicSixUnbalancedEMinus24
    factorTwoIntrinsicSixUnbalancedEMinus44
    (factorTwoIntrinsicNineFMinus h61 h63 h65 h81 h83 h85 i n)
    (factorTwoIntrinsicNineBMinus i 0)
    (factorTwoIntrinsicNineBMinus i 1)
    (factorTwoIntrinsicNineBMinus i 2)
    (factorTwoIntrinsicNineDMinus h07 h27 h47 n 0)
    (factorTwoIntrinsicNineDMinus h07 h27 h47 n 1)
    (factorTwoIntrinsicNineDMinus h07 h27 h47 n 2)

def factorTwoIntrinsicNineUPlus
    (h07 h27 h47 h67 h87 : ℝ) (n m : Fin 3) : ℝ :=
  factorTwoIntrinsicNineUentry
    factorTwoIntrinsicSixUnbalancedEPlusDet
    factorTwoIntrinsicSixUnbalancedEPlus00
    factorTwoIntrinsicSixUnbalancedEPlus02
    factorTwoIntrinsicSixUnbalancedEPlus04
    factorTwoIntrinsicSixUnbalancedEPlus22
    factorTwoIntrinsicSixUnbalancedEPlus24
    factorTwoIntrinsicSixUnbalancedEPlus44
    (factorTwoIntrinsicNineGPlus h67 h87 n m)
    (factorTwoIntrinsicNineDPlus h07 h27 h47 n 0)
    (factorTwoIntrinsicNineDPlus h07 h27 h47 n 1)
    (factorTwoIntrinsicNineDPlus h07 h27 h47 n 2)
    (factorTwoIntrinsicNineDPlus h07 h27 h47 m 0)
    (factorTwoIntrinsicNineDPlus h07 h27 h47 m 1)
    (factorTwoIntrinsicNineDPlus h07 h27 h47 m 2)

def factorTwoIntrinsicNineUMinus
    (h07 h27 h47 h67 h87 : ℝ) (n m : Fin 3) : ℝ :=
  factorTwoIntrinsicNineUentry
    factorTwoIntrinsicSixUnbalancedEMinusDet
    factorTwoIntrinsicSixUnbalancedEMinus00
    factorTwoIntrinsicSixUnbalancedEMinus02
    factorTwoIntrinsicSixUnbalancedEMinus04
    factorTwoIntrinsicSixUnbalancedEMinus22
    factorTwoIntrinsicSixUnbalancedEMinus24
    factorTwoIntrinsicSixUnbalancedEMinus44
    (factorTwoIntrinsicNineGMinus h67 h87 n m)
    (factorTwoIntrinsicNineDMinus h07 h27 h47 n 0)
    (factorTwoIntrinsicNineDMinus h07 h27 h47 n 1)
    (factorTwoIntrinsicNineDMinus h07 h27 h47 n 2)
    (factorTwoIntrinsicNineDMinus h07 h27 h47 m 0)
    (factorTwoIntrinsicNineDMinus h07 h27 h47 m 1)
    (factorTwoIntrinsicNineDMinus h07 h27 h47 m 2)

def factorTwoIntrinsicNineWPlus
    (h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 : ℝ)
    (n m : Fin 3) : ℝ :=
  factorTwoIntrinsicNineWentry
    (factorTwoIntrinsicNineTPlus 0 0)
    (factorTwoIntrinsicNineTPlus 0 1)
    (factorTwoIntrinsicNineTPlus 0 2)
    (factorTwoIntrinsicNineTPlus 1 1)
    (factorTwoIntrinsicNineTPlus 1 2)
    (factorTwoIntrinsicNineTPlus 2 2)
    (factorTwoIntrinsicNineUPlus h07 h27 h47 h67 h87 n m)
    (factorTwoIntrinsicNineRPlus h07 h27 h47 h61 h63 h65 h81 h83 h85 0 n)
    (factorTwoIntrinsicNineRPlus h07 h27 h47 h61 h63 h65 h81 h83 h85 1 n)
    (factorTwoIntrinsicNineRPlus h07 h27 h47 h61 h63 h65 h81 h83 h85 2 n)
    (factorTwoIntrinsicNineRPlus h07 h27 h47 h61 h63 h65 h81 h83 h85 0 m)
    (factorTwoIntrinsicNineRPlus h07 h27 h47 h61 h63 h65 h81 h83 h85 1 m)
    (factorTwoIntrinsicNineRPlus h07 h27 h47 h61 h63 h65 h81 h83 h85 2 m)

def factorTwoIntrinsicNineWMinus
    (h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 : ℝ)
    (n m : Fin 3) : ℝ :=
  factorTwoIntrinsicNineWentry
    (factorTwoIntrinsicNineTMinus 0 0)
    (factorTwoIntrinsicNineTMinus 0 1)
    (factorTwoIntrinsicNineTMinus 0 2)
    (factorTwoIntrinsicNineTMinus 1 1)
    (factorTwoIntrinsicNineTMinus 1 2)
    (factorTwoIntrinsicNineTMinus 2 2)
    (factorTwoIntrinsicNineUMinus h07 h27 h47 h67 h87 n m)
    (factorTwoIntrinsicNineRMinus h07 h27 h47 h61 h63 h65 h81 h83 h85 0 n)
    (factorTwoIntrinsicNineRMinus h07 h27 h47 h61 h63 h65 h81 h83 h85 1 n)
    (factorTwoIntrinsicNineRMinus h07 h27 h47 h61 h63 h65 h81 h83 h85 2 n)
    (factorTwoIntrinsicNineRMinus h07 h27 h47 h61 h63 h65 h81 h83 h85 0 m)
    (factorTwoIntrinsicNineRMinus h07 h27 h47 h61 h63 h65 h81 h83 h85 1 m)
    (factorTwoIntrinsicNineRMinus h07 h27 h47 h61 h63 h65 h81 h83 h85 2 m)

/-! ## Exact block forms -/

def factorTwoIntrinsicNineReserveQuadratic
    (c6 c8 c7 : ℝ) : ℝ :=
  factorTwoIntrinsicNineReserve6 * c6 ^ 2 +
    factorTwoIntrinsicNineReserve8 * c8 ^ 2 +
    factorTwoIntrinsicNineReserve7 * c7 ^ 2

def factorTwoIntrinsicNinePlusBlock
    (h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 : ℝ)
    (c0 c2 c4 c1 c3 c5 c6 c8 c7 : ℝ) : ℝ :=
  symmetricQuadratic
      factorTwoIntrinsicSixUnbalancedEPlus00
      factorTwoIntrinsicSixUnbalancedEPlus02
      factorTwoIntrinsicSixUnbalancedEPlus04
      factorTwoIntrinsicSixUnbalancedEPlus22
      factorTwoIntrinsicSixUnbalancedEPlus24
      factorTwoIntrinsicSixUnbalancedEPlus44 c0 c2 c4 +
    2 * (c0 *
        (factorTwoIntrinsicNineBPlus 0 0 * c1 +
          factorTwoIntrinsicNineBPlus 1 0 * c3 +
          factorTwoIntrinsicNineBPlus 2 0 * c5 +
          factorTwoIntrinsicNineDPlus h07 h27 h47 0 0 * c6 +
          factorTwoIntrinsicNineDPlus h07 h27 h47 1 0 * c8 +
          factorTwoIntrinsicNineDPlus h07 h27 h47 2 0 * c7) +
      c2 *
        (factorTwoIntrinsicNineBPlus 0 1 * c1 +
          factorTwoIntrinsicNineBPlus 1 1 * c3 +
          factorTwoIntrinsicNineBPlus 2 1 * c5 +
          factorTwoIntrinsicNineDPlus h07 h27 h47 0 1 * c6 +
          factorTwoIntrinsicNineDPlus h07 h27 h47 1 1 * c8 +
          factorTwoIntrinsicNineDPlus h07 h27 h47 2 1 * c7) +
      c4 *
        (factorTwoIntrinsicNineBPlus 0 2 * c1 +
          factorTwoIntrinsicNineBPlus 1 2 * c3 +
          factorTwoIntrinsicNineBPlus 2 2 * c5 +
          factorTwoIntrinsicNineDPlus h07 h27 h47 0 2 * c6 +
          factorTwoIntrinsicNineDPlus h07 h27 h47 1 2 * c8 +
          factorTwoIntrinsicNineDPlus h07 h27 h47 2 2 * c7)) +
    (symmetricQuadratic
      factorTwoIntrinsicSixUnbalancedOMinus11
      factorTwoIntrinsicSixUnbalancedOMinus13
      factorTwoIntrinsicSixUnbalancedOMinus15
      factorTwoIntrinsicSixUnbalancedOMinus33
      factorTwoIntrinsicSixUnbalancedOMinus35
      factorTwoIntrinsicSixUnbalancedOMinus55 c1 c3 c5 +
    2 * (c1 *
        (factorTwoIntrinsicNineFPlus h61 h63 h65 h81 h83 h85 0 0 * c6 +
          factorTwoIntrinsicNineFPlus h61 h63 h65 h81 h83 h85 0 1 * c8 +
          factorTwoIntrinsicNineFPlus h61 h63 h65 h81 h83 h85 0 2 * c7) +
      c3 *
        (factorTwoIntrinsicNineFPlus h61 h63 h65 h81 h83 h85 1 0 * c6 +
          factorTwoIntrinsicNineFPlus h61 h63 h65 h81 h83 h85 1 1 * c8 +
          factorTwoIntrinsicNineFPlus h61 h63 h65 h81 h83 h85 1 2 * c7) +
      c5 *
        (factorTwoIntrinsicNineFPlus h61 h63 h65 h81 h83 h85 2 0 * c6 +
          factorTwoIntrinsicNineFPlus h61 h63 h65 h81 h83 h85 2 1 * c8 +
          factorTwoIntrinsicNineFPlus h61 h63 h65 h81 h83 h85 2 2 * c7)) +
    symmetricQuadratic
      (factorTwoIntrinsicNineGPlus h67 h87 0 0)
      (factorTwoIntrinsicNineGPlus h67 h87 0 1)
      (factorTwoIntrinsicNineGPlus h67 h87 0 2)
      (factorTwoIntrinsicNineGPlus h67 h87 1 1)
      (factorTwoIntrinsicNineGPlus h67 h87 1 2)
      (factorTwoIntrinsicNineGPlus h67 h87 2 2) c6 c8 c7)

def factorTwoIntrinsicNineMinusBlock
    (h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 : ℝ)
    (c0 c2 c4 c1 c3 c5 c6 c8 c7 : ℝ) : ℝ :=
  symmetricQuadratic
      factorTwoIntrinsicSixUnbalancedEMinus00
      factorTwoIntrinsicSixUnbalancedEMinus02
      factorTwoIntrinsicSixUnbalancedEMinus04
      factorTwoIntrinsicSixUnbalancedEMinus22
      factorTwoIntrinsicSixUnbalancedEMinus24
      factorTwoIntrinsicSixUnbalancedEMinus44 c0 c2 c4 +
    2 * (c0 *
        (factorTwoIntrinsicNineBMinus 0 0 * c1 +
          factorTwoIntrinsicNineBMinus 1 0 * c3 +
          factorTwoIntrinsicNineBMinus 2 0 * c5 +
          factorTwoIntrinsicNineDMinus h07 h27 h47 0 0 * c6 +
          factorTwoIntrinsicNineDMinus h07 h27 h47 1 0 * c8 +
          factorTwoIntrinsicNineDMinus h07 h27 h47 2 0 * c7) +
      c2 *
        (factorTwoIntrinsicNineBMinus 0 1 * c1 +
          factorTwoIntrinsicNineBMinus 1 1 * c3 +
          factorTwoIntrinsicNineBMinus 2 1 * c5 +
          factorTwoIntrinsicNineDMinus h07 h27 h47 0 1 * c6 +
          factorTwoIntrinsicNineDMinus h07 h27 h47 1 1 * c8 +
          factorTwoIntrinsicNineDMinus h07 h27 h47 2 1 * c7) +
      c4 *
        (factorTwoIntrinsicNineBMinus 0 2 * c1 +
          factorTwoIntrinsicNineBMinus 1 2 * c3 +
          factorTwoIntrinsicNineBMinus 2 2 * c5 +
          factorTwoIntrinsicNineDMinus h07 h27 h47 0 2 * c6 +
          factorTwoIntrinsicNineDMinus h07 h27 h47 1 2 * c8 +
          factorTwoIntrinsicNineDMinus h07 h27 h47 2 2 * c7)) +
    (symmetricQuadratic
      factorTwoIntrinsicSixUnbalancedOPlus11
      factorTwoIntrinsicSixUnbalancedOPlus13
      factorTwoIntrinsicSixUnbalancedOPlus15
      factorTwoIntrinsicSixUnbalancedOPlus33
      factorTwoIntrinsicSixUnbalancedOPlus35
      factorTwoIntrinsicSixUnbalancedOPlus55 c1 c3 c5 +
    2 * (c1 *
        (factorTwoIntrinsicNineFMinus h61 h63 h65 h81 h83 h85 0 0 * c6 +
          factorTwoIntrinsicNineFMinus h61 h63 h65 h81 h83 h85 0 1 * c8 +
          factorTwoIntrinsicNineFMinus h61 h63 h65 h81 h83 h85 0 2 * c7) +
      c3 *
        (factorTwoIntrinsicNineFMinus h61 h63 h65 h81 h83 h85 1 0 * c6 +
          factorTwoIntrinsicNineFMinus h61 h63 h65 h81 h83 h85 1 1 * c8 +
          factorTwoIntrinsicNineFMinus h61 h63 h65 h81 h83 h85 1 2 * c7) +
      c5 *
        (factorTwoIntrinsicNineFMinus h61 h63 h65 h81 h83 h85 2 0 * c6 +
          factorTwoIntrinsicNineFMinus h61 h63 h65 h81 h83 h85 2 1 * c8 +
          factorTwoIntrinsicNineFMinus h61 h63 h65 h81 h83 h85 2 2 * c7)) +
    symmetricQuadratic
      (factorTwoIntrinsicNineGMinus h67 h87 0 0)
      (factorTwoIntrinsicNineGMinus h67 h87 0 1)
      (factorTwoIntrinsicNineGMinus h67 h87 0 2)
      (factorTwoIntrinsicNineGMinus h67 h87 1 1)
      (factorTwoIntrinsicNineGMinus h67 h87 1 2)
      (factorTwoIntrinsicNineGMinus h67 h87 2 2) c6 c8 c7)

/-! ## Identification with the corrected static endpoints -/

/-- The corrected plus static endpoint, after subtracting the retained
`P6/P8/P7` reserve, is exactly the displayed `3 + 3 + 3` block form. -/
theorem factorTwoIntrinsicNineUnbalancedStaticPlus_sub_reserve_eq_block
    (h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 : ℝ)
    (c0 c2 c4 c6 c8 c1 c3 c5 c7 : ℝ) :
    factorTwoIntrinsicNineUnbalancedStaticPlus
          h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87
          c0 c2 c4 c6 c8 c1 c3 c5 c7 -
        factorTwoIntrinsicNineReserveQuadratic c6 c8 c7 =
      factorTwoIntrinsicNinePlusBlock
        h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87
        c0 c2 c4 c1 c3 c5 c6 c8 c7 := by
  have hsix := factorTwoIntrinsicSixUnbalancedStaticPlus_eq_block
    c0 c2 c4 c1 c3 c5
  unfold factorTwoIntrinsicSixUnbalancedStaticPlus at hsix
  unfold factorTwoIntrinsicNineUnbalancedStaticPlus
    factorTwoProfileStaticBranchForm
  rw [factorTwoEndpointPhaseDiagonal_intrinsicNineEven_eq,
    factorTwoEndpointPhaseDiagonal_intrinsicNineOdd_eq,
    factorTwoCenteredAlternatingCoupling_intrinsicNine_eq]
  unfold factorTwoIntrinsicNineUnbalancedTransfer
    factorTwoIntrinsicEightUnbalancedTransfer
    factorTwoIntrinsicNineReserveQuadratic
    factorTwoIntrinsicNinePlusBlock
  simp only [factorTwoIntrinsicNineBPlus, factorTwoIntrinsicNineDPlus,
    factorTwoIntrinsicNineFPlus, factorTwoIntrinsicNineGPlus]
  unfold factorTwoIntrinsicNineEPlus06 factorTwoIntrinsicNineEPlus08
    factorTwoIntrinsicNineEPlus26 factorTwoIntrinsicNineEPlus28
    factorTwoIntrinsicNineEPlus46 factorTwoIntrinsicNineEPlus48
    factorTwoIntrinsicNineEPlus66 factorTwoIntrinsicNineEPlus68
    factorTwoIntrinsicNineEPlus88
    factorTwoIntrinsicNineOMinus17 factorTwoIntrinsicNineOMinus37
    factorTwoIntrinsicNineOMinus57 factorTwoIntrinsicNineOMinus77
    factorTwoIntrinsicNineKPlus07 factorTwoIntrinsicNineKPlus27
    factorTwoIntrinsicNineKPlus47 factorTwoIntrinsicNineKPlus61
    factorTwoIntrinsicNineKPlus63 factorTwoIntrinsicNineKPlus65
    factorTwoIntrinsicNineKPlus67 factorTwoIntrinsicNineKPlus81
    factorTwoIntrinsicNineKPlus83 factorTwoIntrinsicNineKPlus85
    factorTwoIntrinsicNineKPlus87
    factorTwoIntrinsicNineEvenEntry factorTwoIntrinsicNineOddEntry
    factorTwoIntrinsicNineKPlusEntry
    factorTwoIntrinsicNineReserve6 factorTwoIntrinsicNineReserve8
    factorTwoIntrinsicNineReserve7
  unfold symmetricQuadratic at hsix ⊢
  linear_combination hsix

/-- The corrected minus static endpoint has the same retained reserve and
the opposite endpoint/transfer signs in its exact `3 + 3 + 3` block form. -/
theorem factorTwoIntrinsicNineUnbalancedStaticMinus_sub_reserve_eq_block
    (h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 : ℝ)
    (c0 c2 c4 c6 c8 c1 c3 c5 c7 : ℝ) :
    factorTwoIntrinsicNineUnbalancedStaticMinus
          h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87
          c0 c2 c4 c6 c8 c1 c3 c5 c7 -
        factorTwoIntrinsicNineReserveQuadratic c6 c8 c7 =
      factorTwoIntrinsicNineMinusBlock
        h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87
        c0 c2 c4 c1 c3 c5 c6 c8 c7 := by
  have hsix := factorTwoIntrinsicSixUnbalancedStaticMinus_eq_block
    c0 c2 c4 c1 c3 c5
  unfold factorTwoIntrinsicSixUnbalancedStaticMinus at hsix
  unfold factorTwoIntrinsicNineUnbalancedStaticMinus
    factorTwoProfileStaticBranchForm
  rw [factorTwoEndpointPhaseDiagonal_intrinsicNineEven_eq,
    factorTwoEndpointPhaseDiagonal_intrinsicNineOdd_eq,
    factorTwoCenteredAlternatingCoupling_intrinsicNine_eq]
  unfold factorTwoIntrinsicNineUnbalancedTransfer
    factorTwoIntrinsicEightUnbalancedTransfer
    factorTwoIntrinsicNineReserveQuadratic
    factorTwoIntrinsicNineMinusBlock
  simp only [factorTwoIntrinsicNineBMinus, factorTwoIntrinsicNineDMinus,
    factorTwoIntrinsicNineFMinus, factorTwoIntrinsicNineGMinus]
  unfold factorTwoIntrinsicNineEMinus06 factorTwoIntrinsicNineEMinus08
    factorTwoIntrinsicNineEMinus26 factorTwoIntrinsicNineEMinus28
    factorTwoIntrinsicNineEMinus46 factorTwoIntrinsicNineEMinus48
    factorTwoIntrinsicNineEMinus66 factorTwoIntrinsicNineEMinus68
    factorTwoIntrinsicNineEMinus88
    factorTwoIntrinsicNineOPlus17 factorTwoIntrinsicNineOPlus37
    factorTwoIntrinsicNineOPlus57 factorTwoIntrinsicNineOPlus77
    factorTwoIntrinsicNineKMinus07 factorTwoIntrinsicNineKMinus27
    factorTwoIntrinsicNineKMinus47 factorTwoIntrinsicNineKMinus61
    factorTwoIntrinsicNineKMinus63 factorTwoIntrinsicNineKMinus65
    factorTwoIntrinsicNineKMinus67 factorTwoIntrinsicNineKMinus81
    factorTwoIntrinsicNineKMinus83 factorTwoIntrinsicNineKMinus85
    factorTwoIntrinsicNineKMinus87
    factorTwoIntrinsicNineEvenEntry factorTwoIntrinsicNineOddEntry
    factorTwoIntrinsicNineKMinusEntry
    factorTwoIntrinsicNineReserve6 factorTwoIntrinsicNineReserve8
    factorTwoIntrinsicNineReserve7
  simp only [neg_neg]
  unfold symmetricQuadratic at hsix ⊢
  linear_combination hsix

/-! ## The two fraction-free first completions -/

theorem factorTwoIntrinsicNinePlus_firstSchur_eq
    (h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 : ℝ)
    (c1 c3 c5 c6 c8 c7 : ℝ) :
    factorTwoIntrinsicSixUnbalancedEPlusDet *
          (symmetricQuadratic
              factorTwoIntrinsicSixUnbalancedOMinus11
              factorTwoIntrinsicSixUnbalancedOMinus13
              factorTwoIntrinsicSixUnbalancedOMinus15
              factorTwoIntrinsicSixUnbalancedOMinus33
              factorTwoIntrinsicSixUnbalancedOMinus35
              factorTwoIntrinsicSixUnbalancedOMinus55 c1 c3 c5 +
            2 * (c1 *
                (factorTwoIntrinsicNineFPlus h61 h63 h65 h81 h83 h85 0 0 * c6 +
                  factorTwoIntrinsicNineFPlus h61 h63 h65 h81 h83 h85 0 1 * c8 +
                  factorTwoIntrinsicNineFPlus h61 h63 h65 h81 h83 h85 0 2 * c7) +
              c3 *
                (factorTwoIntrinsicNineFPlus h61 h63 h65 h81 h83 h85 1 0 * c6 +
                  factorTwoIntrinsicNineFPlus h61 h63 h65 h81 h83 h85 1 1 * c8 +
                  factorTwoIntrinsicNineFPlus h61 h63 h65 h81 h83 h85 1 2 * c7) +
              c5 *
                (factorTwoIntrinsicNineFPlus h61 h63 h65 h81 h83 h85 2 0 * c6 +
                  factorTwoIntrinsicNineFPlus h61 h63 h65 h81 h83 h85 2 1 * c8 +
                  factorTwoIntrinsicNineFPlus h61 h63 h65 h81 h83 h85 2 2 * c7)) +
            symmetricQuadratic
              (factorTwoIntrinsicNineGPlus h67 h87 0 0)
              (factorTwoIntrinsicNineGPlus h67 h87 0 1)
              (factorTwoIntrinsicNineGPlus h67 h87 0 2)
              (factorTwoIntrinsicNineGPlus h67 h87 1 1)
              (factorTwoIntrinsicNineGPlus h67 h87 1 2)
              (factorTwoIntrinsicNineGPlus h67 h87 2 2) c6 c8 c7) -
        adjugateQuadratic
          factorTwoIntrinsicSixUnbalancedEPlus00
          factorTwoIntrinsicSixUnbalancedEPlus02
          factorTwoIntrinsicSixUnbalancedEPlus04
          factorTwoIntrinsicSixUnbalancedEPlus22
          factorTwoIntrinsicSixUnbalancedEPlus24
          factorTwoIntrinsicSixUnbalancedEPlus44
          (factorTwoIntrinsicNineBPlus 0 0 * c1 +
            factorTwoIntrinsicNineBPlus 1 0 * c3 +
            factorTwoIntrinsicNineBPlus 2 0 * c5 +
            factorTwoIntrinsicNineDPlus h07 h27 h47 0 0 * c6 +
            factorTwoIntrinsicNineDPlus h07 h27 h47 1 0 * c8 +
            factorTwoIntrinsicNineDPlus h07 h27 h47 2 0 * c7)
          (factorTwoIntrinsicNineBPlus 0 1 * c1 +
            factorTwoIntrinsicNineBPlus 1 1 * c3 +
            factorTwoIntrinsicNineBPlus 2 1 * c5 +
            factorTwoIntrinsicNineDPlus h07 h27 h47 0 1 * c6 +
            factorTwoIntrinsicNineDPlus h07 h27 h47 1 1 * c8 +
            factorTwoIntrinsicNineDPlus h07 h27 h47 2 1 * c7)
          (factorTwoIntrinsicNineBPlus 0 2 * c1 +
            factorTwoIntrinsicNineBPlus 1 2 * c3 +
            factorTwoIntrinsicNineBPlus 2 2 * c5 +
            factorTwoIntrinsicNineDPlus h07 h27 h47 0 2 * c6 +
            factorTwoIntrinsicNineDPlus h07 h27 h47 1 2 * c8 +
            factorTwoIntrinsicNineDPlus h07 h27 h47 2 2 * c7) =
      symmetricQuadratic
          (factorTwoIntrinsicNineTPlus 0 0)
          (factorTwoIntrinsicNineTPlus 0 1)
          (factorTwoIntrinsicNineTPlus 0 2)
          (factorTwoIntrinsicNineTPlus 1 1)
          (factorTwoIntrinsicNineTPlus 1 2)
          (factorTwoIntrinsicNineTPlus 2 2) c1 c3 c5 +
        2 * (c1 *
            (factorTwoIntrinsicNineRPlus
                h07 h27 h47 h61 h63 h65 h81 h83 h85 0 0 * c6 +
              factorTwoIntrinsicNineRPlus
                h07 h27 h47 h61 h63 h65 h81 h83 h85 0 1 * c8 +
              factorTwoIntrinsicNineRPlus
                h07 h27 h47 h61 h63 h65 h81 h83 h85 0 2 * c7) +
          c3 *
            (factorTwoIntrinsicNineRPlus
                h07 h27 h47 h61 h63 h65 h81 h83 h85 1 0 * c6 +
              factorTwoIntrinsicNineRPlus
                h07 h27 h47 h61 h63 h65 h81 h83 h85 1 1 * c8 +
              factorTwoIntrinsicNineRPlus
                h07 h27 h47 h61 h63 h65 h81 h83 h85 1 2 * c7) +
          c5 *
            (factorTwoIntrinsicNineRPlus
                h07 h27 h47 h61 h63 h65 h81 h83 h85 2 0 * c6 +
              factorTwoIntrinsicNineRPlus
                h07 h27 h47 h61 h63 h65 h81 h83 h85 2 1 * c8 +
              factorTwoIntrinsicNineRPlus
                h07 h27 h47 h61 h63 h65 h81 h83 h85 2 2 * c7)) +
        symmetricQuadratic
          (factorTwoIntrinsicNineUPlus h07 h27 h47 h67 h87 0 0)
          (factorTwoIntrinsicNineUPlus h07 h27 h47 h67 h87 0 1)
          (factorTwoIntrinsicNineUPlus h07 h27 h47 h67 h87 0 2)
          (factorTwoIntrinsicNineUPlus h07 h27 h47 h67 h87 1 1)
          (factorTwoIntrinsicNineUPlus h07 h27 h47 h67 h87 1 2)
          (factorTwoIntrinsicNineUPlus h07 h27 h47 h67 h87 2 2) c6 c8 c7 := by
  rw [show symmetricQuadratic
      (factorTwoIntrinsicNineTPlus 0 0)
      (factorTwoIntrinsicNineTPlus 0 1)
      (factorTwoIntrinsicNineTPlus 0 2)
      (factorTwoIntrinsicNineTPlus 1 1)
      (factorTwoIntrinsicNineTPlus 1 2)
      (factorTwoIntrinsicNineTPlus 2 2) c1 c3 c5 =
        factorTwoIntrinsicSixUnbalancedTPlusQuadratic c1 c3 c5 by rfl,
    factorTwoIntrinsicSixUnbalancedTPlusQuadratic_eq_fractionFree]
  unfold factorTwoIntrinsicNineRPlus factorTwoIntrinsicNineUPlus
    factorTwoIntrinsicNineRentry factorTwoIntrinsicNineUentry
  simp only [factorTwoIntrinsicNineBPlus, factorTwoIntrinsicNineDPlus,
    factorTwoIntrinsicNineFPlus, factorTwoIntrinsicNineGPlus]
  unfold symmetricQuadratic unbalancedThreeAdjugatePair adjugateQuadratic
  ring

theorem factorTwoIntrinsicNineMinus_firstSchur_eq
    (h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 : ℝ)
    (c1 c3 c5 c6 c8 c7 : ℝ) :
    factorTwoIntrinsicSixUnbalancedEMinusDet *
          (symmetricQuadratic
              factorTwoIntrinsicSixUnbalancedOPlus11
              factorTwoIntrinsicSixUnbalancedOPlus13
              factorTwoIntrinsicSixUnbalancedOPlus15
              factorTwoIntrinsicSixUnbalancedOPlus33
              factorTwoIntrinsicSixUnbalancedOPlus35
              factorTwoIntrinsicSixUnbalancedOPlus55 c1 c3 c5 +
            2 * (c1 *
                (factorTwoIntrinsicNineFMinus h61 h63 h65 h81 h83 h85 0 0 * c6 +
                  factorTwoIntrinsicNineFMinus h61 h63 h65 h81 h83 h85 0 1 * c8 +
                  factorTwoIntrinsicNineFMinus h61 h63 h65 h81 h83 h85 0 2 * c7) +
              c3 *
                (factorTwoIntrinsicNineFMinus h61 h63 h65 h81 h83 h85 1 0 * c6 +
                  factorTwoIntrinsicNineFMinus h61 h63 h65 h81 h83 h85 1 1 * c8 +
                  factorTwoIntrinsicNineFMinus h61 h63 h65 h81 h83 h85 1 2 * c7) +
              c5 *
                (factorTwoIntrinsicNineFMinus h61 h63 h65 h81 h83 h85 2 0 * c6 +
                  factorTwoIntrinsicNineFMinus h61 h63 h65 h81 h83 h85 2 1 * c8 +
                  factorTwoIntrinsicNineFMinus h61 h63 h65 h81 h83 h85 2 2 * c7)) +
            symmetricQuadratic
              (factorTwoIntrinsicNineGMinus h67 h87 0 0)
              (factorTwoIntrinsicNineGMinus h67 h87 0 1)
              (factorTwoIntrinsicNineGMinus h67 h87 0 2)
              (factorTwoIntrinsicNineGMinus h67 h87 1 1)
              (factorTwoIntrinsicNineGMinus h67 h87 1 2)
              (factorTwoIntrinsicNineGMinus h67 h87 2 2) c6 c8 c7) -
        adjugateQuadratic
          factorTwoIntrinsicSixUnbalancedEMinus00
          factorTwoIntrinsicSixUnbalancedEMinus02
          factorTwoIntrinsicSixUnbalancedEMinus04
          factorTwoIntrinsicSixUnbalancedEMinus22
          factorTwoIntrinsicSixUnbalancedEMinus24
          factorTwoIntrinsicSixUnbalancedEMinus44
          (factorTwoIntrinsicNineBMinus 0 0 * c1 +
            factorTwoIntrinsicNineBMinus 1 0 * c3 +
            factorTwoIntrinsicNineBMinus 2 0 * c5 +
            factorTwoIntrinsicNineDMinus h07 h27 h47 0 0 * c6 +
            factorTwoIntrinsicNineDMinus h07 h27 h47 1 0 * c8 +
            factorTwoIntrinsicNineDMinus h07 h27 h47 2 0 * c7)
          (factorTwoIntrinsicNineBMinus 0 1 * c1 +
            factorTwoIntrinsicNineBMinus 1 1 * c3 +
            factorTwoIntrinsicNineBMinus 2 1 * c5 +
            factorTwoIntrinsicNineDMinus h07 h27 h47 0 1 * c6 +
            factorTwoIntrinsicNineDMinus h07 h27 h47 1 1 * c8 +
            factorTwoIntrinsicNineDMinus h07 h27 h47 2 1 * c7)
          (factorTwoIntrinsicNineBMinus 0 2 * c1 +
            factorTwoIntrinsicNineBMinus 1 2 * c3 +
            factorTwoIntrinsicNineBMinus 2 2 * c5 +
            factorTwoIntrinsicNineDMinus h07 h27 h47 0 2 * c6 +
            factorTwoIntrinsicNineDMinus h07 h27 h47 1 2 * c8 +
            factorTwoIntrinsicNineDMinus h07 h27 h47 2 2 * c7) =
      symmetricQuadratic
          (factorTwoIntrinsicNineTMinus 0 0)
          (factorTwoIntrinsicNineTMinus 0 1)
          (factorTwoIntrinsicNineTMinus 0 2)
          (factorTwoIntrinsicNineTMinus 1 1)
          (factorTwoIntrinsicNineTMinus 1 2)
          (factorTwoIntrinsicNineTMinus 2 2) c1 c3 c5 +
        2 * (c1 *
            (factorTwoIntrinsicNineRMinus
                h07 h27 h47 h61 h63 h65 h81 h83 h85 0 0 * c6 +
              factorTwoIntrinsicNineRMinus
                h07 h27 h47 h61 h63 h65 h81 h83 h85 0 1 * c8 +
              factorTwoIntrinsicNineRMinus
                h07 h27 h47 h61 h63 h65 h81 h83 h85 0 2 * c7) +
          c3 *
            (factorTwoIntrinsicNineRMinus
                h07 h27 h47 h61 h63 h65 h81 h83 h85 1 0 * c6 +
              factorTwoIntrinsicNineRMinus
                h07 h27 h47 h61 h63 h65 h81 h83 h85 1 1 * c8 +
              factorTwoIntrinsicNineRMinus
                h07 h27 h47 h61 h63 h65 h81 h83 h85 1 2 * c7) +
          c5 *
            (factorTwoIntrinsicNineRMinus
                h07 h27 h47 h61 h63 h65 h81 h83 h85 2 0 * c6 +
              factorTwoIntrinsicNineRMinus
                h07 h27 h47 h61 h63 h65 h81 h83 h85 2 1 * c8 +
              factorTwoIntrinsicNineRMinus
                h07 h27 h47 h61 h63 h65 h81 h83 h85 2 2 * c7)) +
        symmetricQuadratic
          (factorTwoIntrinsicNineUMinus h07 h27 h47 h67 h87 0 0)
          (factorTwoIntrinsicNineUMinus h07 h27 h47 h67 h87 0 1)
          (factorTwoIntrinsicNineUMinus h07 h27 h47 h67 h87 0 2)
          (factorTwoIntrinsicNineUMinus h07 h27 h47 h67 h87 1 1)
          (factorTwoIntrinsicNineUMinus h07 h27 h47 h67 h87 1 2)
          (factorTwoIntrinsicNineUMinus h07 h27 h47 h67 h87 2 2) c6 c8 c7 := by
  rw [show symmetricQuadratic
      (factorTwoIntrinsicNineTMinus 0 0)
      (factorTwoIntrinsicNineTMinus 0 1)
      (factorTwoIntrinsicNineTMinus 0 2)
      (factorTwoIntrinsicNineTMinus 1 1)
      (factorTwoIntrinsicNineTMinus 1 2)
      (factorTwoIntrinsicNineTMinus 2 2) c1 c3 c5 =
        factorTwoIntrinsicSixUnbalancedTMinusQuadratic c1 c3 c5 by rfl,
    factorTwoIntrinsicSixUnbalancedTMinusQuadratic_eq_fractionFree]
  unfold factorTwoIntrinsicNineRMinus factorTwoIntrinsicNineUMinus
    factorTwoIntrinsicNineRentry factorTwoIntrinsicNineUentry
  simp only [factorTwoIntrinsicNineBMinus, factorTwoIntrinsicNineDMinus,
    factorTwoIntrinsicNineFMinus, factorTwoIntrinsicNineGMinus]
  unfold symmetricQuadratic unbalancedThreeAdjugatePair adjugateQuadratic
  ring

/-! ## Concrete nested Schur conclusions -/

/-- Scalar Sylvester gates for the first two plus blocks, together with
positive semidefiniteness of the final fraction-free `W` block, imply
nonnegativity of the complete reserve-subtracted nine-mode block. -/
theorem factorTwoIntrinsicNinePlusBlock_nonnegative_of_nested_schur
    (h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 : ℝ)
    (hE00 : 0 < factorTwoIntrinsicSixUnbalancedEPlus00)
    (hEMinor : 0 < leadingMinorTwo
      factorTwoIntrinsicSixUnbalancedEPlus00
      factorTwoIntrinsicSixUnbalancedEPlus02
      factorTwoIntrinsicSixUnbalancedEPlus22)
    (hEDet : 0 < factorTwoIntrinsicSixUnbalancedEPlusDet)
    (hT11 : 0 < factorTwoIntrinsicSixUnbalancedTPlus11)
    (hTMinor : 0 < factorTwoIntrinsicSixUnbalancedTPlusMinor)
    (hTDet : 0 < factorTwoIntrinsicSixUnbalancedTPlusDet)
    (hW : ∀ z6 z8 z7 : ℝ, 0 ≤ symmetricQuadratic
      (factorTwoIntrinsicNineWPlus
        h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 0 0)
      (factorTwoIntrinsicNineWPlus
        h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 0 1)
      (factorTwoIntrinsicNineWPlus
        h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 0 2)
      (factorTwoIntrinsicNineWPlus
        h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 1 1)
      (factorTwoIntrinsicNineWPlus
        h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 1 2)
      (factorTwoIntrinsicNineWPlus
        h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 2 2)
      z6 z8 z7)
    (c0 c2 c4 c1 c3 c5 c6 c8 c7 : ℝ) :
    0 ≤ factorTwoIntrinsicNinePlusBlock
      h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87
      c0 c2 c4 c1 c3 c5 c6 c8 c7 := by
  unfold factorTwoIntrinsicNinePlusBlock
  apply nineBlock_nonneg_of_nested_fractionFreeSchur
    factorTwoIntrinsicSixUnbalancedEPlus00
    factorTwoIntrinsicSixUnbalancedEPlus02
    factorTwoIntrinsicSixUnbalancedEPlus04
    factorTwoIntrinsicSixUnbalancedEPlus22
    factorTwoIntrinsicSixUnbalancedEPlus24
    factorTwoIntrinsicSixUnbalancedEPlus44
    (factorTwoIntrinsicNineTPlus 0 0)
    (factorTwoIntrinsicNineTPlus 0 1)
    (factorTwoIntrinsicNineTPlus 0 2)
    (factorTwoIntrinsicNineTPlus 1 1)
    (factorTwoIntrinsicNineTPlus 1 2)
    (factorTwoIntrinsicNineTPlus 2 2)
    (factorTwoIntrinsicNineRPlus
      h07 h27 h47 h61 h63 h65 h81 h83 h85 0 0)
    (factorTwoIntrinsicNineRPlus
      h07 h27 h47 h61 h63 h65 h81 h83 h85 0 1)
    (factorTwoIntrinsicNineRPlus
      h07 h27 h47 h61 h63 h65 h81 h83 h85 0 2)
    (factorTwoIntrinsicNineRPlus
      h07 h27 h47 h61 h63 h65 h81 h83 h85 1 0)
    (factorTwoIntrinsicNineRPlus
      h07 h27 h47 h61 h63 h65 h81 h83 h85 1 1)
    (factorTwoIntrinsicNineRPlus
      h07 h27 h47 h61 h63 h65 h81 h83 h85 1 2)
    (factorTwoIntrinsicNineRPlus
      h07 h27 h47 h61 h63 h65 h81 h83 h85 2 0)
    (factorTwoIntrinsicNineRPlus
      h07 h27 h47 h61 h63 h65 h81 h83 h85 2 1)
    (factorTwoIntrinsicNineRPlus
      h07 h27 h47 h61 h63 h65 h81 h83 h85 2 2)
    (factorTwoIntrinsicNineUPlus h07 h27 h47 h67 h87 0 0)
    (factorTwoIntrinsicNineUPlus h07 h27 h47 h67 h87 0 1)
    (factorTwoIntrinsicNineUPlus h07 h27 h47 h67 h87 0 2)
    (factorTwoIntrinsicNineUPlus h07 h27 h47 h67 h87 1 1)
    (factorTwoIntrinsicNineUPlus h07 h27 h47 h67 h87 1 2)
    (factorTwoIntrinsicNineUPlus h07 h27 h47 h67 h87 2 2)
  · exact hE00
  · exact hEMinor
  · simpa only [factorTwoIntrinsicSixUnbalancedEPlusDet] using hEDet
  · simpa only [factorTwoIntrinsicNineTPlus] using hT11
  · simpa only [factorTwoIntrinsicSixUnbalancedTPlusMinor,
      factorTwoIntrinsicNineTPlus] using hTMinor
  · simpa only [factorTwoIntrinsicSixUnbalancedTPlusDet,
      factorTwoIntrinsicNineTPlus] using hTDet
  · intro z6 z8 z7
    simpa only [factorTwoIntrinsicNineWPlus,
      factorTwoIntrinsicNineWentry] using hW z6 z8 z7
  · exact factorTwoIntrinsicNinePlus_firstSchur_eq
      h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87
      c1 c3 c5 c6 c8 c7

/-- Minus-endpoint counterpart of
`factorTwoIntrinsicNinePlusBlock_nonnegative_of_nested_schur`. -/
theorem factorTwoIntrinsicNineMinusBlock_nonnegative_of_nested_schur
    (h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 : ℝ)
    (hE00 : 0 < factorTwoIntrinsicSixUnbalancedEMinus00)
    (hEMinor : 0 < leadingMinorTwo
      factorTwoIntrinsicSixUnbalancedEMinus00
      factorTwoIntrinsicSixUnbalancedEMinus02
      factorTwoIntrinsicSixUnbalancedEMinus22)
    (hEDet : 0 < factorTwoIntrinsicSixUnbalancedEMinusDet)
    (hT11 : 0 < factorTwoIntrinsicSixUnbalancedTMinus11)
    (hTMinor : 0 < factorTwoIntrinsicSixUnbalancedTMinusMinor)
    (hTDet : 0 < factorTwoIntrinsicSixUnbalancedTMinusDet)
    (hW : ∀ z6 z8 z7 : ℝ, 0 ≤ symmetricQuadratic
      (factorTwoIntrinsicNineWMinus
        h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 0 0)
      (factorTwoIntrinsicNineWMinus
        h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 0 1)
      (factorTwoIntrinsicNineWMinus
        h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 0 2)
      (factorTwoIntrinsicNineWMinus
        h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 1 1)
      (factorTwoIntrinsicNineWMinus
        h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 1 2)
      (factorTwoIntrinsicNineWMinus
        h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 2 2)
      z6 z8 z7)
    (c0 c2 c4 c1 c3 c5 c6 c8 c7 : ℝ) :
    0 ≤ factorTwoIntrinsicNineMinusBlock
      h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87
      c0 c2 c4 c1 c3 c5 c6 c8 c7 := by
  unfold factorTwoIntrinsicNineMinusBlock
  apply nineBlock_nonneg_of_nested_fractionFreeSchur
    factorTwoIntrinsicSixUnbalancedEMinus00
    factorTwoIntrinsicSixUnbalancedEMinus02
    factorTwoIntrinsicSixUnbalancedEMinus04
    factorTwoIntrinsicSixUnbalancedEMinus22
    factorTwoIntrinsicSixUnbalancedEMinus24
    factorTwoIntrinsicSixUnbalancedEMinus44
    (factorTwoIntrinsicNineTMinus 0 0)
    (factorTwoIntrinsicNineTMinus 0 1)
    (factorTwoIntrinsicNineTMinus 0 2)
    (factorTwoIntrinsicNineTMinus 1 1)
    (factorTwoIntrinsicNineTMinus 1 2)
    (factorTwoIntrinsicNineTMinus 2 2)
    (factorTwoIntrinsicNineRMinus
      h07 h27 h47 h61 h63 h65 h81 h83 h85 0 0)
    (factorTwoIntrinsicNineRMinus
      h07 h27 h47 h61 h63 h65 h81 h83 h85 0 1)
    (factorTwoIntrinsicNineRMinus
      h07 h27 h47 h61 h63 h65 h81 h83 h85 0 2)
    (factorTwoIntrinsicNineRMinus
      h07 h27 h47 h61 h63 h65 h81 h83 h85 1 0)
    (factorTwoIntrinsicNineRMinus
      h07 h27 h47 h61 h63 h65 h81 h83 h85 1 1)
    (factorTwoIntrinsicNineRMinus
      h07 h27 h47 h61 h63 h65 h81 h83 h85 1 2)
    (factorTwoIntrinsicNineRMinus
      h07 h27 h47 h61 h63 h65 h81 h83 h85 2 0)
    (factorTwoIntrinsicNineRMinus
      h07 h27 h47 h61 h63 h65 h81 h83 h85 2 1)
    (factorTwoIntrinsicNineRMinus
      h07 h27 h47 h61 h63 h65 h81 h83 h85 2 2)
    (factorTwoIntrinsicNineUMinus h07 h27 h47 h67 h87 0 0)
    (factorTwoIntrinsicNineUMinus h07 h27 h47 h67 h87 0 1)
    (factorTwoIntrinsicNineUMinus h07 h27 h47 h67 h87 0 2)
    (factorTwoIntrinsicNineUMinus h07 h27 h47 h67 h87 1 1)
    (factorTwoIntrinsicNineUMinus h07 h27 h47 h67 h87 1 2)
    (factorTwoIntrinsicNineUMinus h07 h27 h47 h67 h87 2 2)
  · exact hE00
  · exact hEMinor
  · simpa only [factorTwoIntrinsicSixUnbalancedEMinusDet] using hEDet
  · simpa only [factorTwoIntrinsicNineTMinus] using hT11
  · simpa only [factorTwoIntrinsicSixUnbalancedTMinusMinor,
      factorTwoIntrinsicNineTMinus] using hTMinor
  · simpa only [factorTwoIntrinsicSixUnbalancedTMinusDet,
      factorTwoIntrinsicNineTMinus] using hTDet
  · intro z6 z8 z7
    simpa only [factorTwoIntrinsicNineWMinus,
      factorTwoIntrinsicNineWentry] using hW z6 z8 z7
  · exact factorTwoIntrinsicNineMinus_firstSchur_eq
      h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87
      c1 c3 c5 c6 c8 c7

/-- The plus nested-Schur gates certify the explicit diagonal reserve inside
the original corrected static endpoint. -/
theorem factorTwoIntrinsicNineUnbalancedStaticPlus_reserve_nonnegative_of_nested_schur
    (h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 : ℝ)
    (hE00 : 0 < factorTwoIntrinsicSixUnbalancedEPlus00)
    (hEMinor : 0 < leadingMinorTwo
      factorTwoIntrinsicSixUnbalancedEPlus00
      factorTwoIntrinsicSixUnbalancedEPlus02
      factorTwoIntrinsicSixUnbalancedEPlus22)
    (hEDet : 0 < factorTwoIntrinsicSixUnbalancedEPlusDet)
    (hT11 : 0 < factorTwoIntrinsicSixUnbalancedTPlus11)
    (hTMinor : 0 < factorTwoIntrinsicSixUnbalancedTPlusMinor)
    (hTDet : 0 < factorTwoIntrinsicSixUnbalancedTPlusDet)
    (hW : ∀ z6 z8 z7 : ℝ, 0 ≤ symmetricQuadratic
      (factorTwoIntrinsicNineWPlus
        h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 0 0)
      (factorTwoIntrinsicNineWPlus
        h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 0 1)
      (factorTwoIntrinsicNineWPlus
        h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 0 2)
      (factorTwoIntrinsicNineWPlus
        h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 1 1)
      (factorTwoIntrinsicNineWPlus
        h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 1 2)
      (factorTwoIntrinsicNineWPlus
        h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 2 2)
      z6 z8 z7)
    (c0 c2 c4 c6 c8 c1 c3 c5 c7 : ℝ) :
    factorTwoIntrinsicNineReserveQuadratic c6 c8 c7 ≤
      factorTwoIntrinsicNineUnbalancedStaticPlus
        h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87
        c0 c2 c4 c6 c8 c1 c3 c5 c7 := by
  have hBlock := factorTwoIntrinsicNinePlusBlock_nonnegative_of_nested_schur
    h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87
    hE00 hEMinor hEDet hT11 hTMinor hTDet hW
    c0 c2 c4 c1 c3 c5 c6 c8 c7
  rw [← factorTwoIntrinsicNineUnbalancedStaticPlus_sub_reserve_eq_block]
    at hBlock
  exact sub_nonneg.mp hBlock

/-- The minus nested-Schur gates certify the same explicit diagonal reserve
inside the opposite corrected static endpoint. -/
theorem factorTwoIntrinsicNineUnbalancedStaticMinus_reserve_nonnegative_of_nested_schur
    (h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 : ℝ)
    (hE00 : 0 < factorTwoIntrinsicSixUnbalancedEMinus00)
    (hEMinor : 0 < leadingMinorTwo
      factorTwoIntrinsicSixUnbalancedEMinus00
      factorTwoIntrinsicSixUnbalancedEMinus02
      factorTwoIntrinsicSixUnbalancedEMinus22)
    (hEDet : 0 < factorTwoIntrinsicSixUnbalancedEMinusDet)
    (hT11 : 0 < factorTwoIntrinsicSixUnbalancedTMinus11)
    (hTMinor : 0 < factorTwoIntrinsicSixUnbalancedTMinusMinor)
    (hTDet : 0 < factorTwoIntrinsicSixUnbalancedTMinusDet)
    (hW : ∀ z6 z8 z7 : ℝ, 0 ≤ symmetricQuadratic
      (factorTwoIntrinsicNineWMinus
        h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 0 0)
      (factorTwoIntrinsicNineWMinus
        h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 0 1)
      (factorTwoIntrinsicNineWMinus
        h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 0 2)
      (factorTwoIntrinsicNineWMinus
        h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 1 1)
      (factorTwoIntrinsicNineWMinus
        h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 1 2)
      (factorTwoIntrinsicNineWMinus
        h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 2 2)
      z6 z8 z7)
    (c0 c2 c4 c6 c8 c1 c3 c5 c7 : ℝ) :
    factorTwoIntrinsicNineReserveQuadratic c6 c8 c7 ≤
      factorTwoIntrinsicNineUnbalancedStaticMinus
        h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87
        c0 c2 c4 c6 c8 c1 c3 c5 c7 := by
  have hBlock := factorTwoIntrinsicNineMinusBlock_nonnegative_of_nested_schur
    h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87
    hE00 hEMinor hEDet hT11 hTMinor hTDet hW
    c0 c2 c4 c1 c3 c5 c6 c8 c7
  rw [← factorTwoIntrinsicNineUnbalancedStaticMinus_sub_reserve_eq_block]
    at hBlock
  exact sub_nonneg.mp hBlock

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineStaticNestedSchurStructural

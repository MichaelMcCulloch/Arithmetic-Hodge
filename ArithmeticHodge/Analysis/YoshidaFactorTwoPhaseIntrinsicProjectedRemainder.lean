import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseEvenSymmetricBound
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicRemainderBound
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseOddSymmetricBound

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicProjectedRemainder

open CenteredEndpointCorrelation
open CenteredOddOneThreeEnergy
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointOddSharpMassLoss
open YoshidaEndpointSingularCorrelation
open YoshidaFactorTwoAdjacentKernel
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoPhaseEnvelope
open YoshidaFactorTwoPhaseAlternatingCoercivity
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFactorTwoPhaseIntrinsicRemainderBound
open YoshidaFactorTwoPhaseSymmetricCarleman
open YoshidaFactorTwoPhaseSymmetricCoercivity
open YoshidaFactorTwoPhaseTailCoercivity
open YoshidaRegularKernelSchur

noncomputable section

/-!
# Residual-projected smooth phase remainder

The intrinsic moment conditions force both self-correlation means to vanish.
Consequently the symmetric forward/reflected scalar can be centered at the
midpoint of its structural range.  This replaces the unprojected `11/8`
mass cost by half the scalar width.  The alternating branch and both prime
atoms remain signed and coupled below.
-/

/-- Pointwise integrand of the nonsingular phase block. -/
def factorTwoIntrinsicRegularPhaseIntegrand
    (u v : ℝ → ℝ) (a b t : ℝ) : ℝ :=
  yoshidaEndpointA *
      factorTwoCenteredForwardPhaseKernel u v a b t +
    factorTwoCenteredReflectedDesingularizedPhaseKernel u v a b t

/-- One-profile symmetric regular block. -/
def factorTwoIntrinsicSelfRegularBlock (w : ℝ → ℝ) : ℝ :=
  factorTwoIntrinsicRegularPhaseBlock w 0 1 0

/-- The pure alternating nonsingular regular block. -/
def factorTwoIntrinsicAlternatingRegularBlock
    (e o : ℝ → ℝ) : ℝ :=
  factorTwoIntrinsicRegularPhaseBlock e o 0 1

/-- Half-width of the structural symmetric regular scalar interval. -/
def factorTwoIntrinsicSelfRegularHalfWidth : ℝ :=
  ((11 / 8 : ℝ) - (11 / 4 : ℝ) * yoshidaEndpointA) / 2

/-- Energy coefficient after projecting the regular self channels onto
zero-correlation-mean profiles while retaining the dyadic sign. -/
def factorTwoIntrinsicProjectedEvenRemainderLoss (a b : ℝ) : ℝ :=
  factorTwoIntrinsicSelfRegularHalfWidth * |a| +
    (203 / 640 : ℝ) * |b| +
    (Real.log 2 / Real.sqrt 2) * a +
    (Real.log 3 / Real.sqrt 3) / 2 +
    yoshidaEndpointScalarMassLoss + Real.log 2 / 64

def factorTwoIntrinsicProjectedOddRemainderLoss (a b : ℝ) : ℝ :=
  factorTwoIntrinsicProjectedEvenRemainderLoss a b +
    (1 / Real.sqrt 2 - Real.log 2)

def factorTwoIntrinsicProjectedEvenRemainderGap (a b : ℝ) : ℝ :=
  factorTwoIntrinsicProjectedEvenRemainderLoss a b -
    (25 / 12 - Real.log 2 / 2)

def factorTwoIntrinsicProjectedOddRemainderGap (a b : ℝ) : ℝ :=
  factorTwoIntrinsicProjectedOddRemainderLoss a b -
    (137 / 60 - Real.log 2 / 2)

/-- The self regular integrand is the autocorrelation times the sum of the
two regular scalar branches. -/
theorem factorTwoIntrinsic_selfRegularIntegrand_eq
    (w : ℝ → ℝ) {t : ℝ} (ht2 : t < 2) :
    factorTwoIntrinsicRegularPhaseIntegrand w 0 1 0 t =
      yoshidaEndpointA *
        (factorTwoAdjacentSmoothKernel (yoshidaEndpointA * (2 + t)) +
          factorTwoCenteredReflectedRegularKernel t) *
        centeredEndpointCorrelation w t := by
  have hreflected :=
    factorTwo_reflectedDesingularizedPhaseKernel_eq_regular
      w 0 1 0 ht2
  unfold factorTwoIntrinsicRegularPhaseIntegrand
  rw [hreflected]
  unfold factorTwoCenteredForwardPhaseKernel
    factorTwoCenteredPhaseCorrelation
  simp [centeredEndpointCorrelation]
  ring

/-- A zero mean annihilates the mean of the positive-lag autocorrelation. -/
theorem integral_centeredEndpointCorrelation_eq_zero_of_even_mean_zero
    (w : ℝ → ℝ) (hw : Continuous w) (heven : Function.Even w)
    (hmean : (∫ x : ℝ in -1..1, w x) = 0) :
    (∫ t : ℝ in 0..2, centeredEndpointCorrelation w t) = 0 := by
  have h := two_mul_integral_cosh_mul_centeredCorrelation_of_even
    w hw heven 0
  have h' : 2 * (∫ t : ℝ in 0..2,
      centeredEndpointCorrelation w t) =
      (∫ x : ℝ in -1..1, w x) ^ 2 := by
    simpa [centeredCoshMoment] using h
  rw [hmean] at h'
  norm_num at h'
  linarith

/-- Midpoint centering of the regular scalar on any profile whose
autocorrelation mean vanishes. -/
theorem abs_factorTwoIntrinsicSelfRegularBlock_le_halfWidth
    (w : ℝ → ℝ) (hw : Continuous w)
    (hcorrelationMean :
      (∫ t : ℝ in 0..2, centeredEndpointCorrelation w t) = 0) :
    |factorTwoIntrinsicSelfRegularBlock w| ≤
      factorTwoIntrinsicSelfRegularHalfWidth *
        factorTwoIntrinsicEnergy w := by
  let C : ℝ → ℝ := centeredEndpointCorrelation w
  let L : ℝ := (11 / 4 : ℝ) * yoshidaEndpointA
  let U : ℝ := 11 / 8
  let k : ℝ := (L + U) / 2
  let d : ℝ := (U - L) / 2
  let G : ℝ → ℝ := fun t ↦
    factorTwoIntrinsicRegularPhaseIntegrand w 0 1 0 t
  let g : ℝ → ℝ := fun t ↦ G t - k * C t
  have hforward := intervalIntegrable_factorTwoCenteredForwardPhaseKernel
    w 0 hw continuous_zero 1 0
  have hreflected :=
    intervalIntegrable_factorTwoCenteredReflectedDesingularizedPhaseKernel
      w 0 hw continuous_zero 1 0
  have hG : IntervalIntegrable G volume 0 2 := by
    dsimp only [G, factorTwoIntrinsicRegularPhaseIntegrand]
    exact (hforward.const_mul yoshidaEndpointA).add hreflected
  have hCcont : Continuous C := by
    dsimp only [C]
    exact continuous_centeredEndpointCorrelation_of_continuous w hw
  have hCint : IntervalIntegrable C volume 0 2 :=
    hCcont.intervalIntegrable 0 2
  have hg : IntervalIntegrable g volume 0 2 := by
    dsimp only [g]
    exact hG.sub (hCint.const_mul k)
  have hd0 : 0 ≤ d := by
    have hlog : Real.log 2 < (7 / 10 : ℝ) :=
      log_two_lt_one_thousand_seven_hundred_thirty_three_div_two_thousand_five_hundred.trans
        (by norm_num)
    dsimp only [d, U, L]
    unfold yoshidaEndpointA
    linarith
  have hpoint : ∀ t ∈ Ioo (0 : ℝ) 2, |g t| ≤ d * |C t| := by
    intro t ht
    have hb := factorTwo_regular_phase_scalar_bounds ht.1.le ht.2.le
    let F : ℝ := factorTwoAdjacentSmoothKernel
      (yoshidaEndpointA * (2 + t))
    let R : ℝ := factorTwoCenteredReflectedRegularKernel t
    change (1 : ℝ) ≤ F ∧ F ≤ 2 ∧
      (7 / 4 : ℝ) ≤ R ∧ R ≤ (61 / 32 : ℝ) ∧
      yoshidaEndpointA * (F + R) ≤ (11 / 8 : ℝ) ∧
      yoshidaEndpointA * |F - R| ≤ (203 / 640 : ℝ) at hb
    have hscalarLower : L ≤ yoshidaEndpointA * (F + R) := by
      rcases hb with ⟨hF, _hF', hR, _⟩
      dsimp only [L]
      nlinarith [yoshidaEndpointA_pos.le]
    have hscalarUpper : yoshidaEndpointA * (F + R) ≤ U := by
      exact hb.2.2.2.2.1
    have hdev : |yoshidaEndpointA * (F + R) - k| ≤ d := by
      rw [abs_le]
      dsimp only [k, d]
      constructor <;> linarith
    have heq := factorTwoIntrinsic_selfRegularIntegrand_eq w ht.2
    dsimp only [g, G, C]
    rw [heq]
    rw [show yoshidaEndpointA *
          (factorTwoAdjacentSmoothKernel (yoshidaEndpointA * (2 + t)) +
            factorTwoCenteredReflectedRegularKernel t) *
            centeredEndpointCorrelation w t -
          k * centeredEndpointCorrelation w t =
        (yoshidaEndpointA * (F + R) - k) *
          centeredEndpointCorrelation w t by
      dsimp only [F, R]
      ring]
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hdev (abs_nonneg _)
  have hmajor : IntervalIntegrable (fun t : ℝ ↦ d * |C t|)
      volume 0 2 := hCint.abs.const_mul d
  have habsIntegral :
      |(∫ t : ℝ in 0..2, g t)| ≤
        ∫ t : ℝ in 0..2, d * |C t| := by
    calc
      |(∫ t : ℝ in 0..2, g t)| ≤
          ∫ t : ℝ in 0..2, |g t| :=
        intervalIntegral.abs_integral_le_integral_abs (by norm_num)
      _ ≤ ∫ t : ℝ in 0..2, d * |C t| := by
        apply intervalIntegral.integral_mono_on_of_le_Ioo
          (by norm_num) hg.abs hmajor
        exact hpoint
  have hGIntegral : (∫ t : ℝ in 0..2, G t) =
      yoshidaEndpointA *
          (∫ t : ℝ in 0..2,
            factorTwoCenteredForwardPhaseKernel w 0 1 0 t) +
        (∫ t : ℝ in 0..2,
          factorTwoCenteredReflectedDesingularizedPhaseKernel
            w 0 1 0 t) := by
    dsimp only [G, factorTwoIntrinsicRegularPhaseIntegrand]
    rw [intervalIntegral.integral_add
      (hforward.const_mul yoshidaEndpointA) hreflected,
      intervalIntegral.integral_const_mul]
  have hcenter : factorTwoIntrinsicSelfRegularBlock w =
      ∫ t : ℝ in 0..2, g t := by
    have hCzero : (∫ t : ℝ in 0..2, C t) = 0 := by
      simpa only [C] using hcorrelationMean
    unfold factorTwoIntrinsicSelfRegularBlock
      factorTwoIntrinsicRegularPhaseBlock
    dsimp only [g, G, C]
    rw [intervalIntegral.integral_sub hG (hCint.const_mul k),
      hGIntegral, intervalIntegral.integral_const_mul,
      hCzero]
    ring
  have hcorrAbs := integral_abs_centeredEndpointCorrelation_le_energy w hw
  have hscaled := mul_le_mul_of_nonneg_left hcorrAbs hd0
  rw [hcenter]
  calc
    |(∫ t : ℝ in 0..2, g t)| ≤
        ∫ t : ℝ in 0..2, d * |C t| := habsIntegral
    _ = d * (∫ t : ℝ in 0..2, |C t|) := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ d * factorTwoIntrinsicEnergy w := by
      dsimp only [C]
      exact hscaled
    _ = factorTwoIntrinsicSelfRegularHalfWidth *
        factorTwoIntrinsicEnergy w := by
      unfold factorTwoIntrinsicSelfRegularHalfWidth
      dsimp only [d, U, L]

/-- Exact linearity of the regular phase integrand in the two disk
coordinates, with its two self channels separated. -/
theorem factorTwoIntrinsicRegularPhaseIntegrand_eq_self_add_alternating
    (e o : ℝ → ℝ) (a b t : ℝ) :
    factorTwoIntrinsicRegularPhaseIntegrand e o a b t =
      a * (factorTwoIntrinsicRegularPhaseIntegrand e 0 1 0 t +
        factorTwoIntrinsicRegularPhaseIntegrand o 0 1 0 t) +
      b * factorTwoIntrinsicRegularPhaseIntegrand e o 0 1 t := by
  unfold factorTwoIntrinsicRegularPhaseIntegrand
    factorTwoCenteredForwardPhaseKernel
    factorTwoCenteredReflectedDesingularizedPhaseKernel
    factorTwoCenteredPhaseCorrelation
  simp [centeredEndpointCorrelation]
  ring

theorem intervalIntegrable_factorTwoIntrinsicRegularPhaseIntegrand
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    (a b : ℝ) :
    IntervalIntegrable
      (factorTwoIntrinsicRegularPhaseIntegrand u v a b) volume 0 2 := by
  have hforward := intervalIntegrable_factorTwoCenteredForwardPhaseKernel
    u v hu hv a b
  have hreflected :=
    intervalIntegrable_factorTwoCenteredReflectedDesingularizedPhaseKernel
      u v hu hv a b
  unfold factorTwoIntrinsicRegularPhaseIntegrand
  exact (hforward.const_mul yoshidaEndpointA).add hreflected

theorem factorTwoIntrinsicRegularPhaseBlock_eq_integral
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    (a b : ℝ) :
    factorTwoIntrinsicRegularPhaseBlock u v a b =
      ∫ t : ℝ in 0..2,
        factorTwoIntrinsicRegularPhaseIntegrand u v a b t := by
  have hforward := intervalIntegrable_factorTwoCenteredForwardPhaseKernel
    u v hu hv a b
  have hreflected :=
    intervalIntegrable_factorTwoCenteredReflectedDesingularizedPhaseKernel
      u v hu hv a b
  unfold factorTwoIntrinsicRegularPhaseBlock
    factorTwoIntrinsicRegularPhaseIntegrand
  rw [intervalIntegral.integral_add
    (hforward.const_mul yoshidaEndpointA) hreflected,
    intervalIntegral.integral_const_mul]

/-- Exact decomposition of the integrated regular block. -/
theorem factorTwoIntrinsicRegularPhaseBlock_eq_self_add_alternating
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o)
    (a b : ℝ) :
    factorTwoIntrinsicRegularPhaseBlock e o a b =
      a * (factorTwoIntrinsicSelfRegularBlock e +
        factorTwoIntrinsicSelfRegularBlock o) +
      b * factorTwoIntrinsicAlternatingRegularBlock e o := by
  have he0 : Continuous (0 : ℝ → ℝ) := continuous_zero
  rw [factorTwoIntrinsicRegularPhaseBlock_eq_integral e o hec hoc a b]
  rw [show (fun t : ℝ ↦
      factorTwoIntrinsicRegularPhaseIntegrand e o a b t) = fun t ↦
        a * (factorTwoIntrinsicRegularPhaseIntegrand e 0 1 0 t +
          factorTwoIntrinsicRegularPhaseIntegrand o 0 1 0 t) +
        b * factorTwoIntrinsicRegularPhaseIntegrand e o 0 1 t by
    funext t
    exact factorTwoIntrinsicRegularPhaseIntegrand_eq_self_add_alternating
      e o a b t]
  have heInt : IntervalIntegrable
      (fun t : ℝ ↦ factorTwoIntrinsicRegularPhaseIntegrand e 0 1 0 t)
      volume 0 2 :=
    intervalIntegrable_factorTwoIntrinsicRegularPhaseIntegrand
      e 0 hec he0 1 0
  have hoInt : IntervalIntegrable
      (fun t : ℝ ↦ factorTwoIntrinsicRegularPhaseIntegrand o 0 1 0 t)
      volume 0 2 :=
    intervalIntegrable_factorTwoIntrinsicRegularPhaseIntegrand
      o 0 hoc he0 1 0
  have haltInt : IntervalIntegrable
      (fun t : ℝ ↦ factorTwoIntrinsicRegularPhaseIntegrand e o 0 1 t)
      volume 0 2 :=
    intervalIntegrable_factorTwoIntrinsicRegularPhaseIntegrand
      e o hec hoc 0 1
  rw [intervalIntegral.integral_add
      ((heInt.add hoInt).const_mul a) (haltInt.const_mul b),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add heInt hoInt]
  unfold factorTwoIntrinsicSelfRegularBlock
    factorTwoIntrinsicAlternatingRegularBlock
  rw [factorTwoIntrinsicRegularPhaseBlock_eq_integral e 0 hec he0 1 0,
    factorTwoIntrinsicRegularPhaseBlock_eq_integral o 0 hoc he0 1 0,
    factorTwoIntrinsicRegularPhaseBlock_eq_integral e o hec hoc 0 1]

/-- For an even/odd pair the alternating regular integrand is the branch
difference times the single ordered cross-correlation. -/
theorem factorTwoIntrinsic_alternatingRegularIntegrand_eq
    (e o : ℝ → ℝ) (he : Function.Even e) (ho : Function.Odd o)
    {t : ℝ} (ht2 : t < 2) :
    factorTwoIntrinsicRegularPhaseIntegrand e o 0 1 t =
      -2 * yoshidaEndpointA *
        (factorTwoAdjacentSmoothKernel (yoshidaEndpointA * (2 + t)) -
          factorTwoCenteredReflectedRegularKernel t) *
        factorTwoCenteredCrossCorrelation e o t := by
  have hreflected :=
    factorTwo_reflectedDesingularizedPhaseKernel_eq_regular
      e o 0 1 ht2
  have hcross := factorTwo_crossDifference_eq_neg_two_cross_of_even_odd
    he ho t
  unfold factorTwoIntrinsicRegularPhaseIntegrand
  rw [hreflected]
  unfold factorTwoCenteredForwardPhaseKernel
    factorTwoCenteredPhaseCorrelation
  rw [hcross]
  ring

/-- Integrated absolute cross-correlation bound obtained from the exact
two-vector endpoint tails. -/
theorem integral_abs_crossCorrelation_le_half_energy_add
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o)
    (he : Function.Even e) (ho : Function.Odd o) :
    (∫ t : ℝ in 0..2,
        |factorTwoCenteredCrossCorrelation e o t|) ≤
      (1 / 2 : ℝ) *
        (factorTwoIntrinsicEnergy e + factorTwoIntrinsicEnergy o) := by
  let C : ℝ → ℝ := fun t ↦ |factorTwoCenteredCrossCorrelation e o t|
  let B : ℝ → ℝ := fun t ↦
    (1 / 4 : ℝ) *
      (centeredEndpointBoundaryTail e (2 - t) +
        centeredEndpointBoundaryTail o (2 - t))
  have hC : Continuous C :=
    (continuous_factorTwoCenteredCrossCorrelation e o hec hoc).abs
  have hB : Continuous B := by
    dsimp only [B]
    exact continuous_const.mul
      (((continuous_centeredEndpointBoundaryTail e hec).comp
        (continuous_const.sub continuous_id)).add
      ((continuous_centeredEndpointBoundaryTail o hoc).comp
        (continuous_const.sub continuous_id)))
  have hpoint : ∀ t ∈ Icc (0 : ℝ) 2, C t ≤ B t := by
    intro t ht
    have h := two_mul_abs_phaseCorrelation_two_sub_le_boundaryTail
      e o hec hoc 0 1 (by norm_num) (t := 2 - t)
        (sub_nonneg.mpr ht.2)
    rw [show 2 - (2 - t) = t by ring] at h
    have hcross := factorTwo_crossDifference_eq_neg_two_cross_of_even_odd
      he ho t
    simp only [factorTwoCenteredPhaseCorrelation, zero_mul, one_mul,
      zero_add, hcross, abs_neg, abs_mul, abs_of_nonneg (by norm_num :
        (0 : ℝ) ≤ 2)] at h
    dsimp only [C, B]
    nlinarith
  have hmono : (∫ t : ℝ in 0..2, C t) ≤ ∫ t : ℝ in 0..2, B t := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      (hC.intervalIntegrable 0 2) (hB.intervalIntegrable 0 2)
    exact hpoint
  have heReflect := intervalIntegral.integral_comp_sub_left
    (f := centeredEndpointBoundaryTail e) (a := (0 : ℝ)) (b := 2) 2
  have hoReflect := intervalIntegral.integral_comp_sub_left
    (f := centeredEndpointBoundaryTail o) (a := (0 : ℝ)) (b := 2) 2
  calc
    (∫ t : ℝ in 0..2,
        |factorTwoCenteredCrossCorrelation e o t|) =
        ∫ t : ℝ in 0..2, C t := by rfl
    _ ≤ ∫ t : ℝ in 0..2, B t := hmono
    _ = (1 / 2 : ℝ) *
        (factorTwoIntrinsicEnergy e + factorTwoIntrinsicEnergy o) := by
      dsimp only [B]
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add]
      · rw [heReflect, hoReflect]
        norm_num only [sub_self, sub_zero]
        rw [integral_centeredEndpointBoundaryTail_eq_two_mul_energy e hec,
          integral_centeredEndpointBoundaryTail_eq_two_mul_energy o hoc]
        unfold factorTwoIntrinsicEnergy
        ring
      · exact ((continuous_centeredEndpointBoundaryTail e hec).comp
          (continuous_const.sub continuous_id)).intervalIntegrable 0 2
      · exact ((continuous_centeredEndpointBoundaryTail o hoc).comp
          (continuous_const.sub continuous_id)).intervalIntegrable 0 2

/-- The alternating regular branch costs only `203/640` of the total mass,
using the branch-difference coefficient rather than the symmetric sum. -/
theorem abs_factorTwoIntrinsicAlternatingRegularBlock_le
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o)
    (he : Function.Even e) (ho : Function.Odd o) :
    |factorTwoIntrinsicAlternatingRegularBlock e o| ≤
      (203 / 640 : ℝ) *
        (factorTwoIntrinsicEnergy e + factorTwoIntrinsicEnergy o) := by
  let G : ℝ → ℝ := fun t ↦
    factorTwoIntrinsicRegularPhaseIntegrand e o 0 1 t
  let C : ℝ → ℝ := fun t ↦ |factorTwoCenteredCrossCorrelation e o t|
  have hG : IntervalIntegrable G volume 0 2 := by
    have hforward := intervalIntegrable_factorTwoCenteredForwardPhaseKernel
      e o hec hoc 0 1
    have hreflected :=
      intervalIntegrable_factorTwoCenteredReflectedDesingularizedPhaseKernel
        e o hec hoc 0 1
    dsimp only [G, factorTwoIntrinsicRegularPhaseIntegrand]
    exact (hforward.const_mul yoshidaEndpointA).add hreflected
  have hC : Continuous C :=
    (continuous_factorTwoCenteredCrossCorrelation e o hec hoc).abs
  have hpoint : ∀ t ∈ Ioo (0 : ℝ) 2,
      |G t| ≤ (203 / 320 : ℝ) * C t := by
    intro t ht
    have heq := factorTwoIntrinsic_alternatingRegularIntegrand_eq
      e o he ho ht.2
    have hb := factorTwo_regular_phase_scalar_bounds ht.1.le ht.2.le
    let F : ℝ := factorTwoAdjacentSmoothKernel
      (yoshidaEndpointA * (2 + t))
    let R : ℝ := factorTwoCenteredReflectedRegularKernel t
    change (1 : ℝ) ≤ F ∧ F ≤ 2 ∧
      (7 / 4 : ℝ) ≤ R ∧ R ≤ (61 / 32 : ℝ) ∧
      yoshidaEndpointA * (F + R) ≤ (11 / 8 : ℝ) ∧
      yoshidaEndpointA * |F - R| ≤ (203 / 640 : ℝ) at hb
    have hdiff := hb.2.2.2.2.2
    dsimp only [G, C]
    rw [heq, abs_mul, abs_mul, abs_mul,
      abs_neg,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_pos yoshidaEndpointA_pos]
    dsimp only [F, R] at hdiff
    nlinarith [abs_nonneg (factorTwoCenteredCrossCorrelation e o t)]
  have hmajor : IntervalIntegrable (fun t : ℝ ↦
      (203 / 320 : ℝ) * C t) volume 0 2 :=
    (hC.intervalIntegrable 0 2).const_mul (203 / 320 : ℝ)
  have habsIntegral : |(∫ t : ℝ in 0..2, G t)| ≤
      ∫ t : ℝ in 0..2, (203 / 320 : ℝ) * C t := by
    calc
      |(∫ t : ℝ in 0..2, G t)| ≤
          ∫ t : ℝ in 0..2, |G t| :=
        intervalIntegral.abs_integral_le_integral_abs (by norm_num)
      _ ≤ ∫ t : ℝ in 0..2, (203 / 320 : ℝ) * C t := by
        apply intervalIntegral.integral_mono_on_of_le_Ioo
          (by norm_num) hG.abs hmajor
        exact hpoint
  have hcross := integral_abs_crossCorrelation_le_half_energy_add
    e o hec hoc he ho
  unfold factorTwoIntrinsicAlternatingRegularBlock
  rw [factorTwoIntrinsicRegularPhaseBlock_eq_integral e o hec hoc 0 1]
  change |∫ t : ℝ in 0..2, G t| ≤ _
  calc
    |∫ t : ℝ in 0..2, G t| ≤
        ∫ t : ℝ in 0..2, (203 / 320 : ℝ) * C t := habsIntegral
    _ = (203 / 320 : ℝ) * (∫ t : ℝ in 0..2, C t) := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ (203 / 320 : ℝ) *
        ((1 / 2 : ℝ) *
          (factorTwoIntrinsicEnergy e + factorTwoIntrinsicEnergy o)) :=
      mul_le_mul_of_nonneg_left hcross (by norm_num)
    _ = _ := by ring

/-- The two residual self blocks have the projected half-width bound. -/
theorem abs_intrinsic_selfRegularBlocks_le
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o)
    (he : Function.Even e) (ho : Function.Odd o)
    (he0 : centeredEvenP0Coefficient e = 0) :
    |factorTwoIntrinsicSelfRegularBlock e| ≤
        factorTwoIntrinsicSelfRegularHalfWidth * factorTwoIntrinsicEnergy e ∧
      |factorTwoIntrinsicSelfRegularBlock o| ≤
        factorTwoIntrinsicSelfRegularHalfWidth * factorTwoIntrinsicEnergy o := by
  have heMean : (∫ x : ℝ in -1..1, e x) = 0 := by
    unfold centeredEvenP0Coefficient at he0
    linarith
  have heCorr := integral_centeredEndpointCorrelation_eq_zero_of_even_mean_zero
    e hec he heMean
  have hoCorr := integral_centeredEndpointCorrelation_eq_zero_of_odd o hoc ho
  exact ⟨abs_factorTwoIntrinsicSelfRegularBlock_le_halfWidth e hec heCorr,
    abs_factorTwoIntrinsicSelfRegularBlock_le_halfWidth o hoc hoCorr⟩

/-- Projected phase-uniform lower bound for the complete regular block. -/
theorem neg_factorTwoIntrinsicRegularPhaseBlock_le_projected
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o)
    (he : Function.Even e) (ho : Function.Odd o)
    (he0 : centeredEvenP0Coefficient e = 0)
    (a b : ℝ) :
    -factorTwoIntrinsicRegularPhaseBlock e o a b ≤
      (factorTwoIntrinsicSelfRegularHalfWidth * |a| +
        (203 / 640 : ℝ) * |b|) *
      (factorTwoIntrinsicEnergy e + factorTwoIntrinsicEnergy o) := by
  let Se := factorTwoIntrinsicSelfRegularBlock e
  let So := factorTwoIntrinsicSelfRegularBlock o
  let A := factorTwoIntrinsicAlternatingRegularBlock e o
  let d := factorTwoIntrinsicSelfRegularHalfWidth
  let M := factorTwoIntrinsicEnergy e + factorTwoIntrinsicEnergy o
  have hself := abs_intrinsic_selfRegularBlocks_le
    e o hec hoc he ho he0
  change |Se| ≤ d * factorTwoIntrinsicEnergy e ∧
    |So| ≤ d * factorTwoIntrinsicEnergy o at hself
  have hd0 : 0 ≤ d := by
    have hlog : Real.log 2 < (7 / 10 : ℝ) :=
      log_two_lt_one_thousand_seven_hundred_thirty_three_div_two_thousand_five_hundred.trans
        (by norm_num)
    dsimp only [d, factorTwoIntrinsicSelfRegularHalfWidth]
    unfold yoshidaEndpointA
    linarith
  have hselfSum : |Se + So| ≤ d * M := by
    calc
      |Se + So| ≤ |Se| + |So| := abs_add_le Se So
      _ ≤ d * factorTwoIntrinsicEnergy e +
          d * factorTwoIntrinsicEnergy o := add_le_add hself.1 hself.2
      _ = d * M := by dsimp only [M]; ring
  have halt := abs_factorTwoIntrinsicAlternatingRegularBlock_le
    e o hec hoc he ho
  change |A| ≤ (203 / 640 : ℝ) * M at halt
  have hdecomp := factorTwoIntrinsicRegularPhaseBlock_eq_self_add_alternating
    e o hec hoc a b
  change factorTwoIntrinsicRegularPhaseBlock e o a b =
    a * (Se + So) + b * A at hdecomp
  rw [hdecomp]
  calc
    -(a * (Se + So) + b * A) ≤ |a * (Se + So) + b * A| :=
      neg_le_abs _
    _ ≤ |a * (Se + So)| + |b * A| := abs_add_le _ _
    _ = |a| * |Se + So| + |b| * |A| := by rw [abs_mul, abs_mul]
    _ ≤ |a| * (d * M) + |b| * ((203 / 640 : ℝ) * M) :=
      add_le_add
        (mul_le_mul_of_nonneg_left hselfSum (abs_nonneg a))
        (mul_le_mul_of_nonneg_left halt (abs_nonneg b))
    _ = (d * |a| + (203 / 640 : ℝ) * |b|) * M := by ring

/-- The residual projection improves the previous mass-norm coefficient by
at least `237/640` uniformly on the closed phase disk. -/
theorem projectedEvenRemainderLoss_add_margin_le_massLoss
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    factorTwoIntrinsicProjectedEvenRemainderLoss a b + 237 / 640 ≤
      factorTwoIntrinsicEvenRemainderLoss a := by
  have ha : |a| ≤ 1 := by
    have ha2 : a ^ 2 ≤ 1 := by nlinarith [sq_nonneg b]
    nlinarith [sq_abs a]
  have hb : |b| ≤ 1 := by
    have hb2 : b ^ 2 ≤ 1 := by nlinarith [sq_nonneg a]
    nlinarith [sq_abs b]
  have hd0 : 0 ≤ factorTwoIntrinsicSelfRegularHalfWidth := by
    have hlog : Real.log 2 < (7 / 10 : ℝ) :=
      log_two_lt_one_thousand_seven_hundred_thirty_three_div_two_thousand_five_hundred.trans
        (by norm_num)
    unfold factorTwoIntrinsicSelfRegularHalfWidth yoshidaEndpointA
    linarith
  have hdUpper : factorTwoIntrinsicSelfRegularHalfWidth ≤ 11 / 16 := by
    unfold factorTwoIntrinsicSelfRegularHalfWidth
    nlinarith [yoshidaEndpointA_pos.le]
  have hda := mul_le_mul hdUpper ha (abs_nonneg a) (by norm_num :
    (0 : ℝ) ≤ 11 / 16)
  have hdb := mul_le_mul_of_nonneg_left hb (by norm_num :
    (0 : ℝ) ≤ 203 / 640)
  have halpha :
      (Real.log 2 / Real.sqrt 2) * a ≤
        (Real.log 2 / Real.sqrt 2) * |a| :=
    mul_le_mul_of_nonneg_left (le_abs_self a) (by positivity)
  unfold factorTwoIntrinsicProjectedEvenRemainderLoss
    factorTwoIntrinsicEvenRemainderLoss
  nlinarith

/-- Projected structural bound for the exact signed smooth remainder. -/
theorem neg_factorTwoIntrinsicSignedRemainder_le_projected_energy
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o)
    (he : Function.Even e) (ho : Function.Odd o)
    (he0 : centeredEvenP0Coefficient e = 0)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    -factorTwoIntrinsicSignedRemainder e o a b ≤
      factorTwoIntrinsicProjectedEvenRemainderLoss a b *
          factorTwoIntrinsicEnergy e +
        factorTwoIntrinsicProjectedOddRemainderLoss a b *
          factorTwoIntrinsicEnergy o := by
  let Ee := factorTwoIntrinsicEnergy e
  let Eo := factorTwoIntrinsicEnergy o
  let M := Ee + Eo
  let R := factorTwoIntrinsicRegularPhaseBlock e o a b
  let C := factorTwoCenteredPhaseCorrelation e o a b
    (factorTwoPrimeShift / yoshidaEndpointA)
  let H := yoshidaEndpointHyperbolicQuadratic (fun x ↦ (e x : ℂ)) +
    yoshidaEndpointHyperbolicQuadratic (fun x ↦ (o x : ℂ))
  let K := yoshidaEndpointA *
    ((yoshidaEndpointRegularQuadratic (fun x ↦ (e x : ℂ))).re +
      (yoshidaEndpointRegularQuadratic (fun x ↦ (o x : ℂ))).re)
  let alpha := Real.log 2 / Real.sqrt 2
  let beta := Real.log 3 / Real.sqrt 3
  let delta := 1 / Real.sqrt 2 - Real.log 2
  let rho := factorTwoIntrinsicSelfRegularHalfWidth * |a| +
    (203 / 640 : ℝ) * |b|
  have hregular := neg_factorTwoIntrinsicRegularPhaseBlock_le_projected
    e o hec hoc he ho he0 a b
  change -R ≤ rho * M at hregular
  have hprime := weighted_prime_phase_le_half_mass
    e o hec hoc a b hab
  change beta * C ≤ (beta / 2) * M at hprime
  have hkernel := endpoint_mul_regularQuadratic_re_sum_le
    e o hec hoc he0 ho
  change K ≤ (Real.log 2 / 64) * M at hkernel
  have hhyper := neg_hyperbolic_sum_le_odd_energy e o hoc he
  change -H ≤ delta * Eo at hhyper
  have hdecomp :
      -factorTwoIntrinsicSignedRemainder e o a b =
        -R + alpha * a * M + beta * C +
          yoshidaEndpointScalarMassLoss * M + K - H := by
    dsimp only [R, M, Ee, Eo, C, H, K, alpha, beta]
    unfold factorTwoIntrinsicSignedRemainder
      factorTwoIntrinsicRegularPhaseBlock
    ring
  rw [hdecomp]
  calc
    -R + alpha * a * M + beta * C +
          yoshidaEndpointScalarMassLoss * M + K - H ≤
        rho * M + alpha * a * M + (beta / 2) * M +
          yoshidaEndpointScalarMassLoss * M +
          (Real.log 2 / 64) * M + delta * Eo := by
      linarith
    _ = factorTwoIntrinsicProjectedEvenRemainderLoss a b *
          factorTwoIntrinsicEnergy e +
        factorTwoIntrinsicProjectedOddRemainderLoss a b *
          factorTwoIntrinsicEnergy o := by
      dsimp only [rho, M, Ee, Eo, alpha, beta, delta]
      unfold factorTwoIntrinsicProjectedOddRemainderLoss
        factorTwoIntrinsicProjectedEvenRemainderLoss
      ring

/-- Exact remaining sufficient inequality after the residual-projected
smooth estimate. -/
theorem factorTwoEndpointChannelPhase_nonneg_of_projectedPotentialGap
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o)
    (he : Function.Even e) (ho : Function.Odd o)
    (he0 : centeredEvenP0Coefficient e = 0)
    (he2 : centeredEvenP2Coefficient e = 0)
    (ho1 : centeredOddP1Coefficient o = 0)
    (ho3 : centeredOddP3Coefficient o = 0)
    (helocal : LocallyLipschitzOn (Icc (-1) 1) e)
    (holocal : LocallyLipschitzOn (Icc (-1) 1) o)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1)
    (hpotential :
      factorTwoIntrinsicProjectedEvenRemainderGap a b *
            factorTwoIntrinsicEnergy e +
          factorTwoIntrinsicProjectedOddRemainderGap a b *
            factorTwoIntrinsicEnergy o ≤
        (1 / 2 : ℝ) *
          (factorTwoIntrinsicPotentialEnergy e +
            factorTwoIntrinsicPotentialEnergy o)) :
    0 ≤ YoshidaFactorTwoPhaseFullProfile.factorTwoEndpointChannelPhase
      e o a b := by
  have hrem := neg_factorTwoIntrinsicSignedRemainder_le_projected_energy
    e o hec hoc he ho he0 a b hab
  apply factorTwoEndpointChannelPhase_nonneg_of_intrinsic_signedRemainder
    e o hec hoc he ho he0 he2 ho1 ho3 helocal holocal a b hab
  unfold factorTwoIntrinsicProjectedEvenRemainderGap
    factorTwoIntrinsicProjectedOddRemainderGap at hpotential
  linarith

/-!
## A phase endpoint closed by the projected estimate

At `a = -1`, the signed dyadic atom cancels enough of the smooth loss for
the projected estimate to fit inside both raw spectral reserves.  This is a
genuine phase-positivity consequence, not merely a reformulation of a
missing estimate.
-/

theorem projectedEvenRemainderLoss_neg_one_zero_lt_five_thirds :
    factorTwoIntrinsicProjectedEvenRemainderLoss (-1) 0 < 5 / 3 := by
  have hlogLower : (2 / 3 : ℝ) < Real.log 2 :=
    (by norm_num : (2 / 3 : ℝ) < 693 / 1000).trans
      six_hundred_ninety_three_div_thousand_lt_log_two
  have hlogUpper : Real.log 2 < (7 / 10 : ℝ) :=
    log_two_lt_one_thousand_seven_hundred_thirty_three_div_two_thousand_five_hundred.trans
      (by norm_num)
  have hgamma :=
    eulerMascheroniConstant_lt_two_hundred_eighty_nine_div_five_hundred
  have hrenorm :=
    log_pi_mul_log_two_lt_seven_hundred_seventy_nine_div_thousand
  have hbeta := factorTwoPrimeThreeWeight_lt_one
  have hsqrtPos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrtSq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrtUpper : Real.sqrt 2 < (3 / 2 : ℝ) := by
    nlinarith [Real.sqrt_nonneg 2]
  have halpha : (4 / 9 : ℝ) < Real.log 2 / Real.sqrt 2 := by
    rw [lt_div_iff₀ hsqrtPos]
    nlinarith
  have hd : factorTwoIntrinsicSelfRegularHalfWidth < 11 / 48 := by
    unfold factorTwoIntrinsicSelfRegularHalfWidth yoshidaEndpointA
    linarith
  unfold factorTwoIntrinsicProjectedEvenRemainderLoss
    yoshidaEndpointScalarMassLoss
  norm_num only [abs_neg, abs_one, abs_zero, mul_one, mul_zero, add_zero]
  linarith

theorem projectedEvenRemainderLoss_neg_one_zero_le_raw_reserve :
    factorTwoIntrinsicProjectedEvenRemainderLoss (-1) 0 ≤
      25 / 12 - Real.log 2 / 2 := by
  have hloss := projectedEvenRemainderLoss_neg_one_zero_lt_five_thirds
  have hlog : Real.log 2 < (7 / 10 : ℝ) :=
    log_two_lt_one_thousand_seven_hundred_thirty_three_div_two_thousand_five_hundred.trans
      (by norm_num)
  linarith

theorem projectedOddRemainderLoss_neg_one_zero_le_raw_reserve :
    factorTwoIntrinsicProjectedOddRemainderLoss (-1) 0 ≤
      137 / 60 - Real.log 2 / 2 := by
  have heven := projectedEvenRemainderLoss_neg_one_zero_lt_five_thirds
  have hsqrt := inv_sqrt_two_lt_one_hundred_seventy_seven_div_two_hundred_fifty
  have hlogLower := six_hundred_ninety_three_div_thousand_lt_log_two
  have hlogUpper : Real.log 2 < (7 / 10 : ℝ) :=
    log_two_lt_one_thousand_seven_hundred_thirty_three_div_two_thousand_five_hundred.trans
      (by norm_num)
  unfold factorTwoIntrinsicProjectedOddRemainderLoss
  linarith

/-- Complete intrinsic-residual phase positivity at the negative symmetric
endpoint. -/
theorem factorTwoEndpointChannelPhase_neg_one_zero_nonneg
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o)
    (he : Function.Even e) (ho : Function.Odd o)
    (he0 : centeredEvenP0Coefficient e = 0)
    (he2 : centeredEvenP2Coefficient e = 0)
    (ho1 : centeredOddP1Coefficient o = 0)
    (ho3 : centeredOddP3Coefficient o = 0)
    (helocal : LocallyLipschitzOn (Icc (-1) 1) e)
    (holocal : LocallyLipschitzOn (Icc (-1) 1) o) :
    0 ≤ YoshidaFactorTwoPhaseFullProfile.factorTwoEndpointChannelPhase
      e o (-1) 0 := by
  apply factorTwoEndpointChannelPhase_nonneg_of_projectedPotentialGap
    e o hec hoc he ho he0 he2 ho1 ho3 helocal holocal (-1) 0 (by norm_num)
  have heGap : factorTwoIntrinsicProjectedEvenRemainderGap (-1) 0 ≤ 0 := by
    unfold factorTwoIntrinsicProjectedEvenRemainderGap
    linarith [projectedEvenRemainderLoss_neg_one_zero_le_raw_reserve]
  have hoGap : factorTwoIntrinsicProjectedOddRemainderGap (-1) 0 ≤ 0 := by
    unfold factorTwoIntrinsicProjectedOddRemainderGap
    linarith [projectedOddRemainderLoss_neg_one_zero_le_raw_reserve]
  have heEnergy := factorTwoIntrinsicEnergy_nonneg e
  have hoEnergy := factorTwoIntrinsicEnergy_nonneg o
  have heTerm := mul_nonpos_of_nonpos_of_nonneg heGap heEnergy
  have hoTerm := mul_nonpos_of_nonpos_of_nonneg hoGap hoEnergy
  have hpotential : 0 ≤ (1 / 2 : ℝ) *
      (factorTwoIntrinsicPotentialEnergy e +
        factorTwoIntrinsicPotentialEnergy o) := by
    exact mul_nonneg (by norm_num)
      (add_nonneg (factorTwoIntrinsicPotentialEnergy_nonneg e)
        (factorTwoIntrinsicPotentialEnergy_nonneg o))
  linarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicProjectedRemainder

import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowControlStep01Positive
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseSingularSquare

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowControlStep01CauchyStructural

open CenteredEndpointCorrelation
open UnitIntervalLogEnergyAffine
open YoshidaEndpointBoundaryTailFold
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddResidualRegularity
open YoshidaEndpointOcticPotential
open YoshidaEndpointPotentialBound
open YoshidaEndpointSingularCorrelation
open YoshidaEndpointTriangleFoldLipschitz
open YoshidaFactorTwoAdjacentKernel
open YoshidaFactorTwoCenteredPhysical
open YoshidaEndpointOddCleanPositive
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoPhaseEnvelope
open YoshidaFactorTwoPhaseIntrinsicEvenLowEndpointPositive
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicLowControlStep01Positive
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoPhaseOddLowSchur
open YoshidaFactorTwoPhaseOddLowEndpointPositive
open YoshidaFactorTwoPhaseOddStructuralPerturbation
open YoshidaRegularKernelSchur

noncomputable section

/-!
# A structural singular square for the first intrinsic control

The exact first-control Cauchy budget has two unequal self-channel weights.
Writing

`s = evenDetCoefficient1 / evenDetCoefficient0`,

the even clean/symmetric weights are `1, 1`, whereas the odd weights are
`s / 4, (s - 2) / 4`.  The reflected alternating pole must therefore be
completed with an asymmetric two-vector square.  This file records that
completion without separating its four alternating entries.

No finite enumeration, interval subdivision, sampling, or computational
certificate is used.
-/

/-- The logarithmic determinant slope appearing in the exact odd budget. -/
def factorTwoIntrinsicStep01Slope : ℝ :=
  factorTwoIntrinsicEvenDetCoefficient1 /
    factorTwoIntrinsicEvenDetCoefficient0

/-- The endpoint pairing left by the unequal clean and symmetric weights.
Here `(x₀,y₀)` is the left endpoint vector and `(x₁,y₁)` is its
translated right-endpoint partner. -/
def factorTwoIntrinsicStep01WeightedEndpointPairing
    (s x₀ y₀ x₁ y₁ : ℝ) : ℝ :=
  x₁ ^ 2 + x₀ ^ 2 +
      (s / 4) * (y₁ ^ 2 + y₀ ^ 2) -
    (x₁ * x₀ + ((s - 2) / 4) * (y₁ * y₀) -
      (y₁ * x₀ - x₁ * y₀))

/-- Exact sum-of-squares decomposition of the asymmetric endpoint pairing.
The coefficient `s - 2`, rather than the tiny Step01 determinant margin, is
the scalar reserve exposed by the completion. -/
theorem factorTwoIntrinsicStep01WeightedEndpointPairing_eq_squares
    (s x₀ y₀ x₁ y₁ : ℝ) :
    factorTwoIntrinsicStep01WeightedEndpointPairing s x₀ y₀ x₁ y₁ =
      (1 / 2 : ℝ) * (x₁ - x₀) ^ 2 +
        ((s - 2) / 8) * (y₁ - y₀) ^ 2 +
        (1 / 2 : ℝ) * (y₁ + x₀) ^ 2 +
        (1 / 2 : ℝ) * (x₁ - y₀) ^ 2 +
        ((s - 2) / 8) * (y₁ ^ 2 + y₀ ^ 2) := by
  unfold factorTwoIntrinsicStep01WeightedEndpointPairing
  ring

/-- The asymmetric endpoint completion is pointwise nonnegative as soon as
the determinant slope is at least two.  The expected production slope is
well inside this structural region; no near-zero determinant is used here. -/
theorem factorTwoIntrinsicStep01WeightedEndpointPairing_nonneg
    {s : ℝ} (hs : 2 ≤ s) (x₀ y₀ x₁ y₁ : ℝ) :
    0 ≤ factorTwoIntrinsicStep01WeightedEndpointPairing s x₀ y₀ x₁ y₁ := by
  rw [factorTwoIntrinsicStep01WeightedEndpointPairing_eq_squares]
  have hs8 : 0 ≤ (s - 2) / 8 := by linarith
  positivity

/-- Functional version of the endpoint square at reflected distance `r`. -/
def factorTwoIntrinsicStep01WeightedEndpointSquare
    (e o : ℝ → ℝ) (s r x : ℝ) : ℝ :=
  factorTwoIntrinsicStep01WeightedEndpointPairing s
    (e x) (o x) (e (2 - r + x)) (o (2 - r + x))

theorem factorTwoIntrinsicStep01WeightedEndpointSquare_nonneg
    (e o : ℝ → ℝ) {s : ℝ} (hs : 2 ≤ s) (r x : ℝ) :
    0 ≤ factorTwoIntrinsicStep01WeightedEndpointSquare e o s r x := by
  exact factorTwoIntrinsicStep01WeightedEndpointPairing_nonneg hs
    (e x) (o x) (e (2 - r + x)) (o (2 - r + x))

/-- The single reflected correlation retained by the asymmetric square. -/
def factorTwoIntrinsicStep01WeightedReflectedCorrelation
    (e o : ℝ → ℝ) (s t : ℝ) : ℝ :=
  centeredEndpointCorrelation e t +
    ((s - 2) / 4) * centeredEndpointCorrelation o t -
    (factorTwoCenteredCrossCorrelation o e t -
      factorTwoCenteredCrossCorrelation e o t)

/-- Correlation form of the asymmetric fixed-distance numerator.  Its
reflected correlation is exactly the combination contributed by one even
`+` endpoint, `(s-2)/4` odd symmetric endpoints, and the complete signed
alternating channel. -/
def factorTwoIntrinsicStep01WeightedCorrelationNumerator
    (e o : ℝ → ℝ) (s r : ℝ) : ℝ :=
    centeredPositiveDistanceEnergy e r +
    (s / 4) * centeredPositiveDistanceEnergy o r +
    centeredEndpointBoundaryTail e r +
    (s / 4) * centeredEndpointBoundaryTail o r -
    factorTwoIntrinsicStep01WeightedReflectedCorrelation e o s (2 - r)

/-- Square form of the same numerator.  The overlap term is already a
weighted square; only the reflected endpoint interval needs completion. -/
def factorTwoIntrinsicStep01WeightedSquareNumerator
    (e o : ℝ → ℝ) (s r : ℝ) : ℝ :=
  (centeredPositiveDistanceEnergy e r +
      (s / 4) * centeredPositiveDistanceEnergy o r) +
    ∫ x : ℝ in -1..-1 + r,
      factorTwoIntrinsicStep01WeightedEndpointSquare e o s r x

/-- Exact completion of the weighted endpoint tails and the complete signed
reflected correlation. -/
theorem factorTwoIntrinsicStep01WeightedEndpointTail_eq_square
    (e o : ℝ → ℝ) (he : Continuous e) (ho : Continuous o)
    (s r : ℝ) :
    centeredEndpointBoundaryTail e r +
          (s / 4) * centeredEndpointBoundaryTail o r -
        factorTwoIntrinsicStep01WeightedReflectedCorrelation e o s (2 - r) =
      ∫ x : ℝ in -1..-1 + r,
        factorTwoIntrinsicStep01WeightedEndpointSquare e o s r x := by
  let z : ℝ := s / 4
  let p : ℝ := (s - 2) / 4
  unfold factorTwoIntrinsicStep01WeightedReflectedCorrelation
  have heShift :
      (∫ x : ℝ in -1..-1 + r, e (2 - r + x) ^ 2) =
        ∫ x : ℝ in 1 - r..1, e x ^ 2 := by
    convert intervalIntegral.integral_comp_add_left
      (a := (-1 : ℝ)) (b := -1 + r) (fun y : ℝ ↦ e y ^ 2) (2 - r) using 1
    all_goals ring_nf
  have hoShift :
      (∫ x : ℝ in -1..-1 + r, o (2 - r + x) ^ 2) =
        ∫ x : ℝ in 1 - r..1, o x ^ 2 := by
    convert intervalIntegral.integral_comp_add_left
      (a := (-1 : ℝ)) (b := -1 + r) (fun y : ℝ ↦ o y ^ 2) (2 - r) using 1
    all_goals ring_nf
  have he1sq : IntervalIntegrable
      (fun x : ℝ ↦ e (2 - r + x) ^ 2) volume (-1) (-1 + r) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have he0sq : IntervalIntegrable
      (fun x : ℝ ↦ e x ^ 2) volume (-1) (-1 + r) :=
    (he.pow 2).intervalIntegrable _ _
  have ho1sq : IntervalIntegrable
      (fun x : ℝ ↦ o (2 - r + x) ^ 2) volume (-1) (-1 + r) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have ho0sq : IntervalIntegrable
      (fun x : ℝ ↦ o x ^ 2) volume (-1) (-1 + r) :=
    (ho.pow 2).intervalIntegrable _ _
  have hee : IntervalIntegrable
      (fun x : ℝ ↦ e (2 - r + x) * e x) volume (-1) (-1 + r) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hoo : IntervalIntegrable
      (fun x : ℝ ↦ o (2 - r + x) * o x) volume (-1) (-1 + r) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hoe : IntervalIntegrable
      (fun x : ℝ ↦ o (2 - r + x) * e x) volume (-1) (-1 + r) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have heo : IntervalIntegrable
      (fun x : ℝ ↦ e (2 - r + x) * o x) volume (-1) (-1 + r) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have htails :
      centeredEndpointBoundaryTail e r +
          z * centeredEndpointBoundaryTail o r =
        ∫ x : ℝ in -1..-1 + r,
          (e (2 - r + x) ^ 2 + e x ^ 2) +
            z * (o (2 - r + x) ^ 2 + o x ^ 2) := by
    unfold centeredEndpointBoundaryTail
    rw [← heShift, ← hoShift]
    rw [← intervalIntegral.integral_add he1sq he0sq,
      ← intervalIntegral.integral_add ho1sq ho0sq,
      ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add
        (he1sq.add he0sq) ((ho1sq.add ho0sq).const_mul z)]
  have hcorrelation :
      centeredEndpointCorrelation e (2 - r) +
          p * centeredEndpointCorrelation o (2 - r) -
          (factorTwoCenteredCrossCorrelation o e (2 - r) -
            factorTwoCenteredCrossCorrelation e o (2 - r)) =
        ∫ x : ℝ in -1..-1 + r,
          e (2 - r + x) * e x +
            p * (o (2 - r + x) * o x) -
            (o (2 - r + x) * e x - e (2 - r + x) * o x) := by
    unfold centeredEndpointCorrelation factorTwoCenteredCrossCorrelation
    rw [show 1 - (2 - r) = -1 + r by ring]
    rw [intervalIntegral.integral_sub
        (hee.add (hoo.const_mul p)) (hoe.sub heo),
      intervalIntegral.integral_add hee (hoo.const_mul p),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub hoe heo]
  rw [show s / 4 = z by rfl, show (s - 2) / 4 = p by rfl,
    htails, hcorrelation]
  rw [← intervalIntegral.integral_sub
    ((he1sq.add he0sq).add ((ho1sq.add ho0sq).const_mul z))
    ((hee.add (hoo.const_mul p)).sub (hoe.sub heo))]
  apply intervalIntegral.integral_congr
  intro x _hx
  unfold factorTwoIntrinsicStep01WeightedEndpointSquare
    factorTwoIntrinsicStep01WeightedEndpointPairing
  dsimp only [z, p]

/-- The correlation and square presentations of the asymmetric numerator
agree at every distance. -/
theorem factorTwoIntrinsicStep01WeightedCorrelationNumerator_eq_square
    (e o : ℝ → ℝ) (he : Continuous e) (ho : Continuous o)
    (s r : ℝ) :
    factorTwoIntrinsicStep01WeightedCorrelationNumerator e o s r =
      factorTwoIntrinsicStep01WeightedSquareNumerator e o s r := by
  rw [factorTwoIntrinsicStep01WeightedCorrelationNumerator,
    factorTwoIntrinsicStep01WeightedSquareNumerator,
    ← factorTwoIntrinsicStep01WeightedEndpointTail_eq_square e o he ho s r]
  ring

/-- Fixed-distance structural nonnegativity.  The only scalar hypothesis is
the broad slope reserve `2 ≤ s`. -/
theorem factorTwoIntrinsicStep01WeightedSquareNumerator_nonneg
    (e o : ℝ → ℝ) {s r : ℝ} (hs : 2 ≤ s)
    (hr0 : 0 ≤ r) (hr2 : r ≤ 2) :
    0 ≤ factorTwoIntrinsicStep01WeightedSquareNumerator e o s r := by
  unfold factorTwoIntrinsicStep01WeightedSquareNumerator
  apply add_nonneg
  · apply add_nonneg
    · unfold centeredPositiveDistanceEnergy
      apply intervalIntegral.integral_nonneg (by linarith)
      intro x _hx
      positivity
    · apply mul_nonneg
      · linarith
      · unfold centeredPositiveDistanceEnergy
        apply intervalIntegral.integral_nonneg (by linarith)
        intro x _hx
        positivity
  · apply intervalIntegral.integral_nonneg (by linarith)
    intro x _hx
    exact factorTwoIntrinsicStep01WeightedEndpointSquare_nonneg e o hs r x

theorem factorTwoIntrinsicStep01WeightedCorrelationNumerator_nonneg
    (e o : ℝ → ℝ) (he : Continuous e) (ho : Continuous o)
    {s r : ℝ} (hs : 2 ≤ s) (hr0 : 0 ≤ r) (hr2 : r ≤ 2) :
    0 ≤ factorTwoIntrinsicStep01WeightedCorrelationNumerator e o s r := by
  rw [factorTwoIntrinsicStep01WeightedCorrelationNumerator_eq_square
    e o he ho s r]
  exact factorTwoIntrinsicStep01WeightedSquareNumerator_nonneg
    e o hs hr0 hr2

/-- Integrated form of the kernel-level Cauchy completion. -/
theorem integral_factorTwoIntrinsicStep01WeightedSquareNumerator_div_nonneg
    (e o : ℝ → ℝ) {s : ℝ} (hs : 2 ≤ s) :
    0 ≤ ∫ r : ℝ in 0..2,
      factorTwoIntrinsicStep01WeightedSquareNumerator e o s r / r := by
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro r hr
  exact div_nonneg
    (factorTwoIntrinsicStep01WeightedSquareNumerator_nonneg
      e o hs hr.1 hr.2)
    hr.1

/-- Exact integrated recombination of the asymmetrically weighted raw and
endpoint-potential energies with their single signed reflected pole. -/
theorem factorTwoIntrinsicStep01WeightedEnergy_sub_pole_eq_square
    (e o : ℝ → ℝ) (he : Continuous e) (ho : Continuous o)
    (hlocale : LocallyLipschitzOn (Icc (-1) 1) e)
    (hlocalo : LocallyLipschitzOn (Icc (-1) 1) o)
    (s : ℝ) :
    (centeredRawLogEnergy e / 4 +
          (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * e x ^ 2) +
          Real.log 2 * (∫ x : ℝ in -1..1, e x ^ 2)) +
        (s / 4) *
          (centeredRawLogEnergy o / 4 +
            (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * o x ^ 2) +
            Real.log 2 * (∫ x : ℝ in -1..1, o x ^ 2)) -
        (1 / 2 : ℝ) *
          (∫ t : ℝ in 0..2,
            factorTwoIntrinsicStep01WeightedReflectedCorrelation e o s t /
              (2 - t)) =
      (1 / 2 : ℝ) *
        (∫ r : ℝ in 0..2,
          factorTwoIntrinsicStep01WeightedSquareNumerator e o s r / r) := by
  let z : ℝ := s / 4
  let p : ℝ := (s - 2) / 4
  have heEnergy :=
    intervalIntegrable_centeredPositiveDistanceEnergy_div_of_locallyLipschitzOn
      e hlocale
  have hoEnergy :=
    intervalIntegrable_centeredPositiveDistanceEnergy_div_of_locallyLipschitzOn
      o hlocalo
  have heTail := intervalIntegrable_centeredEndpointBoundaryTail_div e he
  have hoTail := intervalIntegrable_centeredEndpointBoundaryTail_div o ho
  have hePole :=
    intervalIntegrable_factorTwoCenteredPhaseCorrelation_two_sub_div
      e 0 he continuous_zero 1 0
  have hoPole :=
    intervalIntegrable_factorTwoCenteredPhaseCorrelation_two_sub_div
      o 0 ho continuous_zero 1 0
  have haltPole :=
    intervalIntegrable_factorTwoCenteredPhaseCorrelation_two_sub_div
      e o he ho 0 (-1)
  have hweightedPole : IntervalIntegrable
      (fun r : ℝ ↦
        factorTwoIntrinsicStep01WeightedReflectedCorrelation e o s (2 - r) /
          r) volume 0 2 := by
    apply ((hePole.add (hoPole.const_mul p)).add haltPole).congr
    intro r _hr
    unfold factorTwoIntrinsicStep01WeightedReflectedCorrelation
      factorTwoCenteredPhaseCorrelation
    simp [centeredEndpointCorrelation, factorTwoCenteredCrossCorrelation]
    dsimp only [p]
    ring
  have heRaw :=
    half_integral_positiveDistanceEnergy_eq_centeredRaw_of_locallyLipschitzOn
      e hlocale
  have hoRaw :=
    half_integral_positiveDistanceEnergy_eq_centeredRaw_of_locallyLipschitzOn
      o hlocalo
  have heBoundary := half_integral_centeredEndpointBoundaryTail_div_eq e he
  have hoBoundary := half_integral_centeredEndpointBoundaryTail_div_eq o ho
  have heFold :
      centeredRawLogEnergy e / 4 +
          (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * e x ^ 2) +
          Real.log 2 * (∫ x : ℝ in -1..1, e x ^ 2) =
        (1 / 2 : ℝ) *
            (∫ r : ℝ in 0..2, centeredPositiveDistanceEnergy e r / r) +
          (1 / 2 : ℝ) *
            (∫ r : ℝ in 0..2, centeredEndpointBoundaryTail e r / r) := by
    rw [heRaw, heBoundary]
    ring
  have hoFold :
      centeredRawLogEnergy o / 4 +
          (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * o x ^ 2) +
          Real.log 2 * (∫ x : ℝ in -1..1, o x ^ 2) =
        (1 / 2 : ℝ) *
            (∫ r : ℝ in 0..2, centeredPositiveDistanceEnergy o r / r) +
          (1 / 2 : ℝ) *
            (∫ r : ℝ in 0..2, centeredEndpointBoundaryTail o r / r) := by
    rw [hoRaw, hoBoundary]
    ring
  have hpoleReflect :
      (∫ t : ℝ in 0..2,
          factorTwoIntrinsicStep01WeightedReflectedCorrelation e o s t /
            (2 - t)) =
        ∫ r : ℝ in 0..2,
          factorTwoIntrinsicStep01WeightedReflectedCorrelation e o s (2 - r) /
            r := by
    have hreflect := intervalIntegral.integral_comp_sub_left
      (f := fun t : ℝ ↦
        factorTwoIntrinsicStep01WeightedReflectedCorrelation e o s t /
          (2 - t))
      (a := (0 : ℝ)) (b := 2) 2
    simpa only [sub_zero, sub_self, sub_sub_cancel] using hreflect.symm
  rw [show s / 4 = z by rfl, heFold, hoFold, hpoleReflect]
  rw [show (fun r : ℝ ↦
      factorTwoIntrinsicStep01WeightedSquareNumerator e o s r / r) =
    fun r ↦
      centeredPositiveDistanceEnergy e r / r +
        z * (centeredPositiveDistanceEnergy o r / r) +
        centeredEndpointBoundaryTail e r / r +
        z * (centeredEndpointBoundaryTail o r / r) -
        factorTwoIntrinsicStep01WeightedReflectedCorrelation e o s (2 - r) /
          r by
    funext r
    rw [← factorTwoIntrinsicStep01WeightedCorrelationNumerator_eq_square
      e o he ho s r]
    unfold factorTwoIntrinsicStep01WeightedCorrelationNumerator
    dsimp only [z]
    ring]
  rw [intervalIntegral.integral_sub
      (((heEnergy.add (hoEnergy.const_mul z)).add heTail).add
        (hoTail.const_mul z)) hweightedPole,
    intervalIntegral.integral_add
      ((heEnergy.add (hoEnergy.const_mul z)).add heTail)
      (hoTail.const_mul z),
    intervalIntegral.integral_add
      (heEnergy.add (hoEnergy.const_mul z)) heTail,
    intervalIntegral.integral_add heEnergy (hoEnergy.const_mul z),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  ring

/-- Profile-level quadratic whose discriminant is the exact Step01 Cauchy
inequality.  The unequal odd clean and symmetric weights are retained. -/
def factorTwoIntrinsicStep01WeightedProfileForm
    (e o : ℝ → ℝ) (s : ℝ) : ℝ :=
  yoshidaEndpointOddCleanQuadratic e +
    factorTwoCenteredSymmetricPerturbation e +
    (s / 4) * yoshidaEndpointOddCleanQuadratic o +
    ((s - 2) / 4) * factorTwoCenteredSymmetricPerturbation o +
    factorTwoCenteredAlternatingCoupling e o

/-- The exact smooth, scalar-mass, and retained-prime complement after the
asymmetric reflected pole has been absorbed into the structural square. -/
def factorTwoIntrinsicStep01WeightedSignedRemainder
    (e o : ℝ → ℝ) (s : ℝ) : ℝ :=
  -(yoshidaEndpointScalarMassLoss + Real.log 2) *
      ((∫ x : ℝ in -1..1, e x ^ 2) +
        (s / 4) * (∫ x : ℝ in -1..1, o x ^ 2)) -
    (Real.log 2 / Real.sqrt 2) *
      ((∫ x : ℝ in -1..1, e x ^ 2) +
        ((s - 2) / 4) * (∫ x : ℝ in -1..1, o x ^ 2)) -
    yoshidaEndpointA *
      ((yoshidaEndpointRegularQuadratic (fun x : ℝ ↦ (e x : ℂ))).re +
        (s / 4) *
          (yoshidaEndpointRegularQuadratic (fun x : ℝ ↦ (o x : ℂ))).re) +
    (yoshidaEndpointHyperbolicQuadratic (fun x : ℝ ↦ (e x : ℂ)) +
      (s / 4) *
        yoshidaEndpointHyperbolicQuadratic (fun x : ℝ ↦ (o x : ℂ))) +
    yoshidaEndpointA *
      ((∫ t : ℝ in 0..2,
          factorTwoCenteredForwardPhaseKernel e 0 1 0 t) +
        ((s - 2) / 4) *
          (∫ t : ℝ in 0..2,
            factorTwoCenteredForwardPhaseKernel o 0 1 0 t) +
        (∫ t : ℝ in 0..2,
          factorTwoCenteredForwardPhaseKernel e o 0 1 t)) +
    ((∫ t : ℝ in 0..2,
        factorTwoCenteredReflectedDesingularizedPhaseKernel e 0 1 0 t) +
      ((s - 2) / 4) *
        (∫ t : ℝ in 0..2,
          factorTwoCenteredReflectedDesingularizedPhaseKernel o 0 1 0 t) +
      (∫ t : ℝ in 0..2,
        factorTwoCenteredReflectedDesingularizedPhaseKernel e o 0 1 t)) -
    (Real.log 3 / Real.sqrt 3) *
      (factorTwoCenteredPhaseCorrelation e 0 1 0
          (factorTwoPrimeShift / yoshidaEndpointA) +
        ((s - 2) / 4) *
          factorTwoCenteredPhaseCorrelation o 0 1 0
            (factorTwoPrimeShift / yoshidaEndpointA) +
        factorTwoCenteredPhaseCorrelation e o 0 1
          (factorTwoPrimeShift / yoshidaEndpointA))

/-- Exact structural normal form of the asymmetric profile quadratic.  Its
first term is the manifestly nonnegative five-square integral; all work
still outstanding is displayed in the signed smooth/mass/prime remainder. -/
theorem factorTwoIntrinsicStep01WeightedProfileForm_eq_square_add_remainder
    (e o : ℝ → ℝ) (he : Continuous e) (ho : Continuous o)
    (hlocale : LocallyLipschitzOn (Icc (-1) 1) e)
    (hlocalo : LocallyLipschitzOn (Icc (-1) 1) o)
    (s : ℝ) :
    factorTwoIntrinsicStep01WeightedProfileForm e o s =
      (1 / 2 : ℝ) *
          (∫ r : ℝ in 0..2,
            factorTwoIntrinsicStep01WeightedSquareNumerator e o s r / r) +
        factorTwoIntrinsicStep01WeightedSignedRemainder e o s := by
  let p : ℝ := (s - 2) / 4
  have heSymm :=
    phase_symmetric_add_alternating_eq_regular_sub_pole_sub_primes
      e 0 he continuous_zero 1 0
  have hoSymm :=
    phase_symmetric_add_alternating_eq_regular_sub_pole_sub_primes
      o 0 ho continuous_zero 1 0
  have hAlt :=
    phase_symmetric_add_alternating_eq_regular_sub_pole_sub_primes
      e o he ho 0 1
  have hzeroSymm :
      factorTwoCenteredSymmetricPerturbation (0 : ℝ → ℝ) = 0 := by
    simp [factorTwoCenteredSymmetricPerturbation,
      centeredEndpointCorrelation]
  have heSymm' :
      factorTwoCenteredSymmetricPerturbation e =
        yoshidaEndpointA *
            (∫ t : ℝ in 0..2,
              factorTwoCenteredForwardPhaseKernel e 0 1 0 t) +
          (∫ t : ℝ in 0..2,
            factorTwoCenteredReflectedDesingularizedPhaseKernel e 0 1 0 t) -
          (1 / 2 : ℝ) *
            (∫ t : ℝ in 0..2,
              factorTwoCenteredPhaseCorrelation e 0 1 0 t / (2 - t)) -
          (Real.log 2 / Real.sqrt 2) *
            (∫ x : ℝ in -1..1, e x ^ 2) -
          (Real.log 3 / Real.sqrt 3) *
            factorTwoCenteredPhaseCorrelation e 0 1 0
              (factorTwoPrimeShift / yoshidaEndpointA) := by
    simpa [hzeroSymm] using heSymm
  have hoSymm' :
      factorTwoCenteredSymmetricPerturbation o =
        yoshidaEndpointA *
            (∫ t : ℝ in 0..2,
              factorTwoCenteredForwardPhaseKernel o 0 1 0 t) +
          (∫ t : ℝ in 0..2,
            factorTwoCenteredReflectedDesingularizedPhaseKernel o 0 1 0 t) -
          (1 / 2 : ℝ) *
            (∫ t : ℝ in 0..2,
              factorTwoCenteredPhaseCorrelation o 0 1 0 t / (2 - t)) -
          (Real.log 2 / Real.sqrt 2) *
            (∫ x : ℝ in -1..1, o x ^ 2) -
          (Real.log 3 / Real.sqrt 3) *
            factorTwoCenteredPhaseCorrelation o 0 1 0
              (factorTwoPrimeShift / yoshidaEndpointA) := by
    simpa [hzeroSymm] using hoSymm
  have hAlt' :
      factorTwoCenteredAlternatingCoupling e o =
        yoshidaEndpointA *
            (∫ t : ℝ in 0..2,
              factorTwoCenteredForwardPhaseKernel e o 0 1 t) +
          (∫ t : ℝ in 0..2,
            factorTwoCenteredReflectedDesingularizedPhaseKernel e o 0 1 t) -
          (1 / 2 : ℝ) *
            (∫ t : ℝ in 0..2,
              factorTwoCenteredPhaseCorrelation e o 0 (-1) t / (2 - t)) -
          (Real.log 3 / Real.sqrt 3) *
            factorTwoCenteredPhaseCorrelation e o 0 1
              (factorTwoPrimeShift / yoshidaEndpointA) := by
    simpa using hAlt
  have hePole :=
    intervalIntegrable_factorTwoCenteredPhaseCorrelation_div_two_sub
      e 0 he continuous_zero 1 0
  have hoPole :=
    intervalIntegrable_factorTwoCenteredPhaseCorrelation_div_two_sub
      o 0 ho continuous_zero 1 0
  have haltPole :=
    intervalIntegrable_factorTwoCenteredPhaseCorrelation_div_two_sub
      e o he ho 0 (-1)
  have hPole :
      (∫ t : ℝ in 0..2,
          factorTwoCenteredPhaseCorrelation e 0 1 0 t / (2 - t)) +
          p * (∫ t : ℝ in 0..2,
            factorTwoCenteredPhaseCorrelation o 0 1 0 t / (2 - t)) +
          (∫ t : ℝ in 0..2,
            factorTwoCenteredPhaseCorrelation e o 0 (-1) t / (2 - t)) =
        ∫ t : ℝ in 0..2,
          factorTwoIntrinsicStep01WeightedReflectedCorrelation e o s t /
            (2 - t) := by
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add hePole (hoPole.const_mul p),
      ← intervalIntegral.integral_add (hePole.add (hoPole.const_mul p))
        haltPole]
    apply intervalIntegral.integral_congr
    intro t _ht
    unfold factorTwoIntrinsicStep01WeightedReflectedCorrelation
      factorTwoCenteredPhaseCorrelation
    simp [centeredEndpointCorrelation, factorTwoCenteredCrossCorrelation]
    dsimp only [p]
    ring
  have hsingular :=
    factorTwoIntrinsicStep01WeightedEnergy_sub_pole_eq_square
      e o he ho hlocale hlocalo s
  rw [← hPole] at hsingular
  unfold factorTwoIntrinsicStep01WeightedProfileForm
    factorTwoIntrinsicStep01WeightedSignedRemainder
    yoshidaEndpointOddCleanQuadratic
  rw [heSymm', hoSymm', hAlt']
  rw [← hsingular]
  dsimp only [p]
  ring

/-! ## Exact contact with the intrinsic Step01 form -/

private theorem factorTwoIntrinsicStep01_evenPlus_eq_profile
    (u v : ℝ) :
    factorTwoIntrinsicEvenPlusQuadratic u v =
      yoshidaEndpointOddCleanQuadratic
          (factorTwoEvenStructuralLowProfile u v) +
        factorTwoCenteredSymmetricPerturbation
          (factorTwoEvenStructuralLowProfile u v) := by
  unfold factorTwoIntrinsicEvenPlusQuadratic
  simpa only [one_mul] using
    factorTwoStructuralPhaseLow_endpoint_quadratic 1 u v

private theorem factorTwoIntrinsicStep01_oddPlus_eq_profile
    (c d : ℝ) :
    factorTwoIntrinsicOddPhaseQuadratic 1 c d =
      yoshidaEndpointOddCleanQuadratic
          (factorTwoOddStructuralLowProfile c d) +
        factorTwoCenteredSymmetricPerturbation
          (factorTwoOddStructuralLowProfile c d) := by
  unfold factorTwoIntrinsicOddPhaseQuadratic
    factorTwoIntrinsicOddPhaseLow11 factorTwoIntrinsicOddPhaseLow13
    factorTwoIntrinsicOddPhaseLow33
  simpa only [factorTwoOddStructuralPhaseLow11,
    factorTwoOddStructuralPhaseLow13, factorTwoOddStructuralPhaseLow33,
    one_mul] using
    factorTwoOddStructuralPhaseLow_quadratic 1 c d

private theorem factorTwoIntrinsicStep01_oddDirection_eq_profile
    (c d : ℝ) :
    factorTwoIntrinsicOddDirectionQuadratic c d =
      -2 * factorTwoCenteredSymmetricPerturbation
        (factorTwoOddStructuralLowProfile c d) := by
  have hdirection :
      factorTwoIntrinsicOddDirectionQuadratic c d =
        factorTwoIntrinsicOddPhaseQuadratic (-1) c d -
          factorTwoIntrinsicOddPhaseQuadratic 1 c d := by
    unfold factorTwoIntrinsicOddDirectionQuadratic
      factorTwoIntrinsicOddPhaseQuadratic
      factorTwoIntrinsicOddPhaseLow11 factorTwoIntrinsicOddPhaseLow13
      factorTwoIntrinsicOddPhaseLow33
    ring
  have hminus :
      factorTwoIntrinsicOddPhaseQuadratic (-1) c d =
        yoshidaEndpointOddCleanQuadratic
            (factorTwoOddStructuralLowProfile c d) -
          factorTwoCenteredSymmetricPerturbation
            (factorTwoOddStructuralLowProfile c d) := by
    unfold factorTwoIntrinsicOddPhaseQuadratic
      factorTwoIntrinsicOddPhaseLow11 factorTwoIntrinsicOddPhaseLow13
      factorTwoIntrinsicOddPhaseLow33
    simpa only [factorTwoOddStructuralPhaseLow11,
      factorTwoOddStructuralPhaseLow13, factorTwoOddStructuralPhaseLow33,
      neg_one_mul, sub_eq_add_neg] using
      factorTwoOddStructuralPhaseLow_quadratic (-1) c d
  rw [hdirection, hminus, factorTwoIntrinsicStep01_oddPlus_eq_profile]
  ring

private theorem factorTwoIntrinsicStep01_alternating_eq_profile
    (u v c d : ℝ) :
    factorTwoIntrinsicAlternatingBilinear u v c d =
      factorTwoCenteredAlternatingCoupling
        (factorTwoEvenStructuralLowProfile u v)
        (factorTwoOddStructuralLowProfile c d) := by
  have hEven := factorTwoCenteredAlternatingCoupling_structuralLow
    u v (factorTwoOddStructuralLowProfile c d)
      (continuous_factorTwoOddStructuralLowProfile c d)
  have h0 := factorTwoCenteredAlternatingCoupling_oddStructuralLow_right
    centeredEvenP0 (by unfold centeredEvenP0; fun_prop) c d
  have h2 := factorTwoCenteredAlternatingCoupling_oddStructuralLow_right
    centeredEvenP2 (by unfold centeredEvenP2; fun_prop) c d
  unfold factorTwoIntrinsicAlternatingBilinear
  rw [hEven, h0, h2]
  unfold factorTwoIntrinsicAlternatingRow0
    factorTwoIntrinsicAlternatingRow2 factorTwoIntrinsicAlternating01
    factorTwoIntrinsicAlternating03 factorTwoIntrinsicAlternating21
    factorTwoIntrinsicAlternating23
  ring

/-- The intrinsic quadratic `E₊ + B/4 + J` is exactly the asymmetric
profile form above.  Thus its singular part is controlled by the preceding
five-square identity, with no entrywise estimate of `J`. -/
theorem factorTwoIntrinsicStep01WeightedProfileForm_eq_intrinsic
    (u v c d : ℝ) :
    factorTwoIntrinsicStep01WeightedProfileForm
        (factorTwoEvenStructuralLowProfile u v)
        (factorTwoOddStructuralLowProfile c d)
        factorTwoIntrinsicStep01Slope =
      factorTwoIntrinsicEvenPlusQuadratic u v +
        (1 / 4 : ℝ) * factorTwoIntrinsicStep01ExactOddBudget c d +
        factorTwoIntrinsicAlternatingBilinear u v c d := by
  rw [factorTwoIntrinsicStep01_evenPlus_eq_profile,
    factorTwoIntrinsicStep01_alternating_eq_profile]
  unfold factorTwoIntrinsicStep01WeightedProfileForm
    factorTwoIntrinsicStep01ExactOddBudget factorTwoIntrinsicStep01Slope
  rw [factorTwoIntrinsicStep01_oddDirection_eq_profile,
    factorTwoIntrinsicStep01_oddPlus_eq_profile]
  ring

/-- Nonnegativity of the asymmetric profile form in every intrinsic
direction implies the exact coupled Cauchy inequality.  This is the genuine
quadratic discriminant step; no alternating entry is bounded separately. -/
theorem factorTwoIntrinsicStep01ExactCauchy_of_weightedProfileForm_nonneg
    (hform : ∀ u v c d : ℝ,
      0 ≤ factorTwoIntrinsicStep01WeightedProfileForm
        (factorTwoEvenStructuralLowProfile u v)
        (factorTwoOddStructuralLowProfile c d)
        factorTwoIntrinsicStep01Slope) :
    FactorTwoIntrinsicStep01ExactCauchy := by
  intro u v c d
  let E : ℝ := factorTwoIntrinsicEvenPlusQuadratic u v
  let B : ℝ := factorTwoIntrinsicStep01ExactOddBudget c d
  let J : ℝ := factorTwoIntrinsicAlternatingBilinear u v c d
  have hpencil : ∀ r s : ℝ,
      0 ≤ E * r ^ 2 + 2 * (J / 2) * r * s + (B / 4) * s ^ 2 := by
    intro r s
    have h := hform (r * u) (r * v) (s * c) (s * d)
    rw [factorTwoIntrinsicStep01WeightedProfileForm_eq_intrinsic] at h
    dsimp only [E, B, J]
    unfold factorTwoIntrinsicEvenPlusQuadratic
      factorTwoIntrinsicStep01ExactOddBudget
      factorTwoIntrinsicOddDirectionQuadratic
      factorTwoIntrinsicOddPhaseQuadratic
      factorTwoIntrinsicAlternatingBilinear
      factorTwoIntrinsicAlternatingRow0
      factorTwoIntrinsicAlternatingRow2 at h ⊢
    nlinarith
  have hcoeff :=
    (real_quadratic_pencil_nonneg_iff E (B / 4) (J / 2)).mp hpencil
  dsimp only [E, B, J] at hcoeff ⊢
  nlinarith [hcoeff.2.2]

/-- Division-free form of the broad slope reserve exposed by the endpoint
completion. -/
theorem factorTwoIntrinsicStep01Slope_two_le_iff
    (hdet0 : 0 < factorTwoIntrinsicEvenDetCoefficient0) :
    2 ≤ factorTwoIntrinsicStep01Slope ↔
      2 * factorTwoIntrinsicEvenDetCoefficient0 ≤
        factorTwoIntrinsicEvenDetCoefficient1 := by
  unfold factorTwoIntrinsicStep01Slope
  rw [le_div_iff₀ hdet0]

/-- Final structural handoff for Step01.  The singular Cauchy pole is already
closed by the five-square theorem; it remains only to prove the displayed
smooth/mass/prime remainder nonnegative on the two intrinsic profiles and
the division-free slope reserve above. -/
theorem factorTwoIntrinsicStep01ExactCauchy_of_slope_and_signedRemainder
    (hslope : 2 ≤ factorTwoIntrinsicStep01Slope)
    (hremainder : ∀ u v c d : ℝ,
      0 ≤ factorTwoIntrinsicStep01WeightedSignedRemainder
        (factorTwoEvenStructuralLowProfile u v)
        (factorTwoOddStructuralLowProfile c d)
        factorTwoIntrinsicStep01Slope) :
    FactorTwoIntrinsicStep01ExactCauchy := by
  apply factorTwoIntrinsicStep01ExactCauchy_of_weightedProfileForm_nonneg
  intro u v c d
  let e : ℝ → ℝ := factorTwoEvenStructuralLowProfile u v
  let o : ℝ → ℝ := factorTwoOddStructuralLowProfile c d
  have he : Continuous e := by
    simpa only [e] using continuous_factorTwoEvenStructuralLowProfile u v
  have ho : Continuous o := by
    simpa only [o] using continuous_factorTwoOddStructuralLowProfile c d
  have helocal : LocallyLipschitzOn (Icc (-1) 1) e := by
    have hedifferentiable : ContDiff ℝ 1 e := by
      dsimp only [e]
      unfold factorTwoEvenStructuralLowProfile centeredEvenP0 centeredEvenP2
      fun_prop
    exact hedifferentiable.contDiffOn.locallyLipschitzOn
      (convex_Icc (-1) 1)
  have holocal : LocallyLipschitzOn (Icc (-1) 1) o := by
    have hodifferentiable : ContDiff ℝ 1 o := by
      dsimp only [o]
      unfold factorTwoOddStructuralLowProfile centeredP1 centeredP3
      fun_prop
    exact hodifferentiable.contDiffOn.locallyLipschitzOn
      (convex_Icc (-1) 1)
  have hnormal :=
    factorTwoIntrinsicStep01WeightedProfileForm_eq_square_add_remainder
      e o he ho helocal holocal factorTwoIntrinsicStep01Slope
  have hsquare :=
    integral_factorTwoIntrinsicStep01WeightedSquareNumerator_div_nonneg
      e o hslope
  have hrem := hremainder u v c d
  dsimp only [e, o] at hnormal hrem ⊢
  rw [hnormal]
  positivity

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowControlStep01CauchyStructural

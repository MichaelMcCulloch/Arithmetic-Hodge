import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseProfileStaticPoleSquareStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseSquareAssembly

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseProfileStaticSquareAssemblyStructural

noncomputable section

open CenteredEndpointCorrelation
open UnitIntervalLogEnergyAffine
open YoshidaEndpointBoundaryTailFold
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointPotentialBound
open YoshidaEndpointSingularCorrelation
open YoshidaEndpointTriangleFoldLipschitz
open YoshidaFactorTwoAdjacentKernel
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoEndpointParityPencil
open YoshidaFactorTwoPhaseDiskSchur
open YoshidaFactorTwoPhaseEnvelope
open YoshidaFactorTwoPhaseProfileStaticPoleSquareStructural
open YoshidaFactorTwoPhaseSingularSquare
open YoshidaRegularKernelSchur

/-!
# Exact assembly of the profile-static Hadamard square

For a static sign `sigma`, the even diagonal carries `sigma` and the odd
diagonal carries `-sigma`.  The forward adjacent branch therefore sees the
sum of the oriented cross-correlation, whereas the reflected branch sees its
difference.  The latter is exactly the pairing completed by
`factorTwoProfileStaticPoleHadamardSquare`.

This module keeps that completed pole coupled to every remaining signed
smooth, mass, hyperbolic, and retained-prime term.  No positivity is asserted
for the signed remainder by itself.
-/

/-- The oriented ordered cross-correlation used by both static branches. -/
def factorTwoProfileStaticCrossDifference
    (e o : ℝ → ℝ) (t : ℝ) : ℝ :=
  factorTwoCenteredCrossCorrelation o e t -
    factorTwoCenteredCrossCorrelation e o t

/-- The forward adjacent branch: the oriented cross-correlation has positive
sign here. -/
def factorTwoProfileStaticForwardCorrelation
    (e o : ℝ → ℝ) (sigma t : ℝ) : ℝ :=
  sigma *
      (centeredEndpointCorrelation e t - centeredEndpointCorrelation o t) +
    factorTwoProfileStaticCrossDifference e o t

/-- The reflected adjacent branch: the oriented cross-correlation has
negative sign here. -/
def factorTwoProfileStaticReflectedCorrelation
    (e o : ℝ → ℝ) (sigma t : ℝ) : ℝ :=
  sigma *
      (centeredEndpointCorrelation e t - centeredEndpointCorrelation o t) -
    factorTwoProfileStaticCrossDifference e o t

/-- The complete static profile form.  `sigma = 1` is the even-plus/odd-minus
split, and `sigma = -1` is the opposite split. -/
def factorTwoProfileStaticBranchForm
    (e o : ℝ → ℝ) (sigma : ℝ) : ℝ :=
  factorTwoEndpointPhaseDiagonal e sigma +
    factorTwoEndpointPhaseDiagonal o (-sigma) +
    factorTwoCenteredAlternatingCoupling e o

/-- The complete static adjacent kernel before its reflected pole is
separated. -/
def factorTwoProfileStaticKernel
    (e o : ℝ → ℝ) (sigma t : ℝ) : ℝ :=
  sigma *
      (factorTwoSymmetricWeight (yoshidaEndpointA * t) *
          centeredEndpointCorrelation e t -
        factorTwoSymmetricWeight (yoshidaEndpointA * t) *
          centeredEndpointCorrelation o t) +
    factorTwoAntisymmetricWeight (yoshidaEndpointA * t) *
      factorTwoProfileStaticCrossDifference e o t

/-- The nonsingular forward contribution to the static adjacent kernel. -/
def factorTwoProfileStaticForwardKernel
    (e o : ℝ → ℝ) (sigma t : ℝ) : ℝ :=
  factorTwoAdjacentSmoothKernel (yoshidaEndpointA * (2 + t)) *
    factorTwoProfileStaticForwardCorrelation e o sigma t

/-- The reflected contribution with its dimensionless half-pole added back.
Both written summands are interval-integrable on the continuous form domain. -/
def factorTwoProfileStaticReflectedDesingularizedKernel
    (e o : ℝ → ℝ) (sigma t : ℝ) : ℝ :=
  yoshidaEndpointA *
      factorTwoAdjacentSmoothKernel (yoshidaEndpointA * (2 - t)) *
      factorTwoProfileStaticReflectedCorrelation e o sigma t +
    (1 / 2 : ℝ) *
      (factorTwoProfileStaticReflectedCorrelation e o sigma t / (2 - t))

/-- The positive-distance energies together with the completed static pole. -/
def factorTwoProfileStaticSingularSquareNumerator
    (e o : ℝ → ℝ) (sigma r : ℝ) : ℝ :=
  centeredPositiveDistanceEnergy e r +
    centeredPositiveDistanceEnergy o r +
    factorTwoProfileStaticPoleDefectNumerator e o sigma r

/-- Every term left after the raw/potential block and reflected pole have been
placed in the exact static singular square.  The zero-lag `p = 2` atom is the
signed mass difference; the `p = 3` atom uses the forward correlation. -/
def factorTwoProfileStaticSignedRemainder
    (e o : ℝ → ℝ) (sigma : ℝ) : ℝ :=
  -(yoshidaEndpointScalarMassLoss + Real.log 2) *
      ((∫ x : ℝ in -1..1, e x ^ 2) + ∫ x : ℝ in -1..1, o x ^ 2) -
    (Real.log 2 / Real.sqrt 2) * sigma *
      ((∫ x : ℝ in -1..1, e x ^ 2) - ∫ x : ℝ in -1..1, o x ^ 2) -
    yoshidaEndpointA *
      ((yoshidaEndpointRegularQuadratic (fun x : ℝ ↦ (e x : ℂ))).re +
        (yoshidaEndpointRegularQuadratic (fun x : ℝ ↦ (o x : ℂ))).re) +
    (yoshidaEndpointHyperbolicQuadratic (fun x : ℝ ↦ (e x : ℂ)) +
      yoshidaEndpointHyperbolicQuadratic (fun x : ℝ ↦ (o x : ℂ))) +
    yoshidaEndpointA *
      (∫ t : ℝ in 0..2,
        factorTwoProfileStaticForwardKernel e o sigma t) +
    (∫ t : ℝ in 0..2,
      factorTwoProfileStaticReflectedDesingularizedKernel e o sigma t) -
    (Real.log 3 / Real.sqrt 3) *
      factorTwoProfileStaticForwardCorrelation e o sigma
        (factorTwoPrimeShift / yoshidaEndpointA)

@[simp] private theorem centeredEndpointCorrelation_zero_profile (t : ℝ) :
    centeredEndpointCorrelation (0 : ℝ → ℝ) t = 0 := by
  unfold centeredEndpointCorrelation
  simp

@[simp] private theorem factorTwoCenteredCrossCorrelation_zero_left
    (w : ℝ → ℝ) (t : ℝ) :
    factorTwoCenteredCrossCorrelation (0 : ℝ → ℝ) w t = 0 := by
  unfold factorTwoCenteredCrossCorrelation
  simp

@[simp] private theorem factorTwoCenteredCrossCorrelation_zero_right
    (w : ℝ → ℝ) (t : ℝ) :
    factorTwoCenteredCrossCorrelation w (0 : ℝ → ℝ) t = 0 := by
  unfold factorTwoCenteredCrossCorrelation
  simp

private theorem intervalIntegrable_factorTwoProfileStaticKernel
    (e o : ℝ → ℝ) (he : Continuous e) (ho : Continuous o)
    (sigma : ℝ) :
    IntervalIntegrable (factorTwoProfileStaticKernel e o sigma) volume 0 2 := by
  have hee0 := intervalIntegrable_factorTwoCenteredSymmetricKernel e e he he
  have hoo0 := intervalIntegrable_factorTwoCenteredSymmetricKernel o o ho ho
  have hee : IntervalIntegrable
      (fun t : ℝ ↦ factorTwoSymmetricWeight (yoshidaEndpointA * t) *
        centeredEndpointCorrelation e t) volume 0 2 := by
    simpa only [factorTwoCenteredCorrelationBilinear_self] using hee0
  have hoo : IntervalIntegrable
      (fun t : ℝ ↦ factorTwoSymmetricWeight (yoshidaEndpointA * t) *
        centeredEndpointCorrelation o t) volume 0 2 := by
    simpa only [factorTwoCenteredCorrelationBilinear_self] using hoo0
  have hcross := intervalIntegrable_factorTwoCenteredAlternatingKernel e o he ho
  exact ((hee.sub hoo).const_mul sigma).add hcross

private theorem intervalIntegrable_factorTwoProfileStaticForwardKernel
    (e o : ℝ → ℝ) (he : Continuous e) (ho : Continuous o)
    (sigma : ℝ) :
    IntervalIntegrable
      (factorTwoProfileStaticForwardKernel e o sigma) volume 0 2 := by
  have he0 := intervalIntegrable_factorTwoCenteredForwardPhaseKernel
    e (0 : ℝ → ℝ) he continuous_zero sigma 0
  have ho0 := intervalIntegrable_factorTwoCenteredForwardPhaseKernel
    o (0 : ℝ → ℝ) ho continuous_zero (-sigma) 0
  have heo := intervalIntegrable_factorTwoCenteredForwardPhaseKernel
    e o he ho 0 1
  apply ((he0.add ho0).add heo).congr
  intro t _ht
  unfold factorTwoProfileStaticForwardKernel
    factorTwoProfileStaticForwardCorrelation
    factorTwoProfileStaticCrossDifference
    factorTwoCenteredForwardPhaseKernel factorTwoCenteredPhaseCorrelation
  simp only [centeredEndpointCorrelation_zero_profile,
    factorTwoCenteredCrossCorrelation_zero_left,
    factorTwoCenteredCrossCorrelation_zero_right, zero_mul, add_zero, sub_zero,
    neg_mul, one_mul]
  ring

private theorem
    intervalIntegrable_factorTwoProfileStaticReflectedDesingularizedKernel
    (e o : ℝ → ℝ) (he : Continuous e) (ho : Continuous o)
    (sigma : ℝ) :
    IntervalIntegrable
      (factorTwoProfileStaticReflectedDesingularizedKernel e o sigma)
      volume 0 2 := by
  have he0 :=
    intervalIntegrable_factorTwoCenteredReflectedDesingularizedPhaseKernel
      e (0 : ℝ → ℝ) he continuous_zero sigma 0
  have ho0 :=
    intervalIntegrable_factorTwoCenteredReflectedDesingularizedPhaseKernel
      o (0 : ℝ → ℝ) ho continuous_zero (-sigma) 0
  have heo :=
    intervalIntegrable_factorTwoCenteredReflectedDesingularizedPhaseKernel
      e o he ho 0 1
  apply ((he0.add ho0).add heo).congr
  intro t _ht
  unfold factorTwoProfileStaticReflectedDesingularizedKernel
    factorTwoProfileStaticReflectedCorrelation
    factorTwoProfileStaticCrossDifference
    factorTwoCenteredReflectedDesingularizedPhaseKernel
    factorTwoCenteredPhaseCorrelation
  simp only [centeredEndpointCorrelation_zero_profile,
    factorTwoCenteredCrossCorrelation_zero_left,
    factorTwoCenteredCrossCorrelation_zero_right, zero_mul, add_zero, sub_zero,
    neg_mul, one_mul]
  ring

private theorem
    intervalIntegrable_factorTwoProfileStaticReflectedCorrelation_div_two_sub
    (e o : ℝ → ℝ) (he : Continuous e) (ho : Continuous o)
    (sigma : ℝ) :
    IntervalIntegrable
      (fun t : ℝ ↦
        factorTwoProfileStaticReflectedCorrelation e o sigma t / (2 - t))
      volume 0 2 := by
  have he0 := intervalIntegrable_factorTwoCenteredPhaseCorrelation_div_two_sub
    e (0 : ℝ → ℝ) he continuous_zero sigma 0
  have ho0 := intervalIntegrable_factorTwoCenteredPhaseCorrelation_div_two_sub
    o (0 : ℝ → ℝ) ho continuous_zero (-sigma) 0
  have heo := intervalIntegrable_factorTwoCenteredPhaseCorrelation_div_two_sub
    e o he ho 0 (-1)
  apply ((he0.add ho0).add heo).congr
  intro t _ht
  unfold factorTwoProfileStaticReflectedCorrelation
    factorTwoProfileStaticCrossDifference factorTwoCenteredPhaseCorrelation
  simp only [centeredEndpointCorrelation_zero_profile,
    factorTwoCenteredCrossCorrelation_zero_left,
    factorTwoCenteredCrossCorrelation_zero_right, zero_mul, add_zero, sub_zero,
    neg_mul, one_mul]
  ring

private theorem
    intervalIntegrable_factorTwoProfileStaticReflectedCorrelation_two_sub_div
    (e o : ℝ → ℝ) (he : Continuous e) (ho : Continuous o)
    (sigma : ℝ) :
    IntervalIntegrable
      (fun r : ℝ ↦
        factorTwoProfileStaticReflectedCorrelation e o sigma (2 - r) / r)
      volume 0 2 := by
  have he0 := intervalIntegrable_factorTwoCenteredPhaseCorrelation_two_sub_div
    e (0 : ℝ → ℝ) he continuous_zero sigma 0
  have ho0 := intervalIntegrable_factorTwoCenteredPhaseCorrelation_two_sub_div
    o (0 : ℝ → ℝ) ho continuous_zero (-sigma) 0
  have heo := intervalIntegrable_factorTwoCenteredPhaseCorrelation_two_sub_div
    e o he ho 0 (-1)
  apply ((he0.add ho0).add heo).congr
  intro r _hr
  unfold factorTwoProfileStaticReflectedCorrelation
    factorTwoProfileStaticCrossDifference factorTwoCenteredPhaseCorrelation
  simp only [centeredEndpointCorrelation_zero_profile,
    factorTwoCenteredCrossCorrelation_zero_left,
    factorTwoCenteredCrossCorrelation_zero_right, zero_mul, add_zero, sub_zero,
    neg_mul, one_mul]
  ring

/-- The static kernel is the forward branch plus the reflected branch with
the correct opposite cross sign. -/
theorem factorTwoProfileStaticKernel_eq_forward_add_reflected
    (e o : ℝ → ℝ) (sigma t : ℝ) :
    factorTwoProfileStaticKernel e o sigma t =
      factorTwoProfileStaticForwardKernel e o sigma t +
        factorTwoAdjacentSmoothKernel (yoshidaEndpointA * (2 - t)) *
          factorTwoProfileStaticReflectedCorrelation e o sigma t := by
  unfold factorTwoProfileStaticKernel factorTwoProfileStaticForwardKernel
    factorTwoProfileStaticForwardCorrelation
    factorTwoProfileStaticReflectedCorrelation
    factorTwoProfileStaticCrossDifference factorTwoSymmetricWeight
    factorTwoAntisymmetricWeight
  rw [factorTwoLogLength_eq_two_mul_yoshidaEndpointA]
  rw [show 2 * yoshidaEndpointA + yoshidaEndpointA * t =
        yoshidaEndpointA * (2 + t) by ring,
    show 2 * yoshidaEndpointA - yoshidaEndpointA * t =
        yoshidaEndpointA * (2 - t) by ring]
  ring

/-- Exact integral separation of the static adjacent kernel into its forward
branch, reflected desingularized branch, and signed half-pole. -/
theorem endpoint_mul_integral_profileStaticKernel_eq_regular_sub_half_pole
    (e o : ℝ → ℝ) (he : Continuous e) (ho : Continuous o)
    (sigma : ℝ) :
    yoshidaEndpointA *
        (∫ t : ℝ in 0..2, factorTwoProfileStaticKernel e o sigma t) =
      yoshidaEndpointA *
          (∫ t : ℝ in 0..2,
            factorTwoProfileStaticForwardKernel e o sigma t) +
        (∫ t : ℝ in 0..2,
          factorTwoProfileStaticReflectedDesingularizedKernel e o sigma t) -
        (1 / 2 : ℝ) *
          (∫ t : ℝ in 0..2,
            factorTwoProfileStaticReflectedCorrelation e o sigma t / (2 - t)) := by
  have hcomplete := intervalIntegrable_factorTwoProfileStaticKernel
    e o he ho sigma
  have hforward := intervalIntegrable_factorTwoProfileStaticForwardKernel
    e o he ho sigma
  have hreflected :=
    intervalIntegrable_factorTwoProfileStaticReflectedDesingularizedKernel
      e o he ho sigma
  have hpole :=
    intervalIntegrable_factorTwoProfileStaticReflectedCorrelation_div_two_sub
      e o he ho sigma
  have hregular :=
    (hforward.const_mul yoshidaEndpointA).add hreflected
  calc
    yoshidaEndpointA *
          (∫ t : ℝ in 0..2, factorTwoProfileStaticKernel e o sigma t) =
        ∫ t : ℝ in 0..2,
          yoshidaEndpointA * factorTwoProfileStaticKernel e o sigma t := by
      rw [intervalIntegral.integral_const_mul]
    _ = ∫ t : ℝ in 0..2,
          (yoshidaEndpointA *
              factorTwoProfileStaticForwardKernel e o sigma t +
            factorTwoProfileStaticReflectedDesingularizedKernel
              e o sigma t) -
            (1 / 2 : ℝ) *
              (factorTwoProfileStaticReflectedCorrelation e o sigma t /
                (2 - t)) := by
      apply intervalIntegral.integral_congr
      intro t _ht
      change yoshidaEndpointA * factorTwoProfileStaticKernel e o sigma t = _
      rw [factorTwoProfileStaticKernel_eq_forward_add_reflected]
      unfold factorTwoProfileStaticReflectedDesingularizedKernel
      ring
    _ = (∫ t : ℝ in 0..2,
            yoshidaEndpointA *
                factorTwoProfileStaticForwardKernel e o sigma t +
              factorTwoProfileStaticReflectedDesingularizedKernel
                e o sigma t) -
          ∫ t : ℝ in 0..2,
            (1 / 2 : ℝ) *
              (factorTwoProfileStaticReflectedCorrelation e o sigma t /
                (2 - t)) := by
      rw [intervalIntegral.integral_sub hregular
        (hpole.const_mul (1 / 2 : ℝ))]
    _ = _ := by
      rw [intervalIntegral.integral_add
          (hforward.const_mul yoshidaEndpointA) hreflected,
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]

/-- Exact static perturbation before the reflected pole is completed.  The
reflected pole uses the minus-cross correlation, while the `p = 3` atom uses
the plus-cross forward correlation. -/
theorem profileStatic_symmetric_sub_add_alternating_eq_regular_sub_pole_sub_primes
    (e o : ℝ → ℝ) (he : Continuous e) (ho : Continuous o)
    (sigma : ℝ) :
    sigma *
          (factorTwoCenteredSymmetricPerturbation e -
            factorTwoCenteredSymmetricPerturbation o) +
        factorTwoCenteredAlternatingCoupling e o =
      yoshidaEndpointA *
          (∫ t : ℝ in 0..2,
            factorTwoProfileStaticForwardKernel e o sigma t) +
        (∫ t : ℝ in 0..2,
          factorTwoProfileStaticReflectedDesingularizedKernel e o sigma t) -
        (1 / 2 : ℝ) *
          (∫ t : ℝ in 0..2,
            factorTwoProfileStaticReflectedCorrelation e o sigma t / (2 - t)) -
        (Real.log 2 / Real.sqrt 2) * sigma *
          ((∫ x : ℝ in -1..1, e x ^ 2) - ∫ x : ℝ in -1..1, o x ^ 2) -
        (Real.log 3 / Real.sqrt 3) *
          factorTwoProfileStaticForwardCorrelation e o sigma
            (factorTwoPrimeShift / yoshidaEndpointA) := by
  have hee0 := intervalIntegrable_factorTwoCenteredSymmetricKernel e e he he
  have hoo0 := intervalIntegrable_factorTwoCenteredSymmetricKernel o o ho ho
  have hee : IntervalIntegrable
      (fun t : ℝ ↦ factorTwoSymmetricWeight (yoshidaEndpointA * t) *
        centeredEndpointCorrelation e t) volume 0 2 := by
    simpa only [factorTwoCenteredCorrelationBilinear_self] using hee0
  have hoo : IntervalIntegrable
      (fun t : ℝ ↦ factorTwoSymmetricWeight (yoshidaEndpointA * t) *
        centeredEndpointCorrelation o t) volume 0 2 := by
    simpa only [factorTwoCenteredCorrelationBilinear_self] using hoo0
  have hcross := intervalIntegrable_factorTwoCenteredAlternatingKernel e o he ho
  have hkernel :
      sigma *
            (factorTwoCenteredSymmetricPerturbation e -
              factorTwoCenteredSymmetricPerturbation o) +
          factorTwoCenteredAlternatingCoupling e o =
        yoshidaEndpointA *
            (∫ t : ℝ in 0..2, factorTwoProfileStaticKernel e o sigma t) -
          (Real.log 2 / Real.sqrt 2) * sigma *
            ((∫ x : ℝ in -1..1, e x ^ 2) -
              ∫ x : ℝ in -1..1, o x ^ 2) -
          (Real.log 3 / Real.sqrt 3) *
            factorTwoProfileStaticForwardCorrelation e o sigma
              (factorTwoPrimeShift / yoshidaEndpointA) := by
    unfold factorTwoCenteredSymmetricPerturbation
      factorTwoCenteredAlternatingCoupling
    rw [show (fun t : ℝ ↦ factorTwoProfileStaticKernel e o sigma t) =
        fun t ↦
          sigma *
              (factorTwoSymmetricWeight (yoshidaEndpointA * t) *
                  centeredEndpointCorrelation e t -
                factorTwoSymmetricWeight (yoshidaEndpointA * t) *
                  centeredEndpointCorrelation o t) +
            factorTwoAntisymmetricWeight (yoshidaEndpointA * t) *
              (factorTwoCenteredCrossCorrelation o e t -
                factorTwoCenteredCrossCorrelation e o t) by
          rfl,
      intervalIntegral.integral_add ((hee.sub hoo).const_mul sigma) hcross,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub hee hoo,
      centeredEndpointCorrelation_zero,
      centeredEndpointCorrelation_zero]
    unfold factorTwoProfileStaticForwardCorrelation
      factorTwoProfileStaticCrossDifference
    ring
  rw [hkernel,
    endpoint_mul_integral_profileStaticKernel_eq_regular_sub_half_pole
      e o he ho sigma]

/-- The reflected static correlation is the interval integral of the pointwise
pairing completed in the preceding Hadamard-square module. -/
theorem factorTwoProfileStaticReflectedCorrelation_two_sub_eq_pairIntegral
    (e o : ℝ → ℝ) (he : Continuous e) (ho : Continuous o)
    (sigma r : ℝ) :
    factorTwoProfileStaticReflectedCorrelation e o sigma (2 - r) =
      ∫ x : ℝ in -1..-1 + r,
        factorTwoProfileStaticReflectedPair e o sigma r x := by
  have hee : IntervalIntegrable
      (fun x : ℝ ↦ e (2 - r + x) * e x) volume (-1) (-1 + r) :=
    ((he.comp (continuous_const.add continuous_id)).mul he).intervalIntegrable _ _
  have hoo : IntervalIntegrable
      (fun x : ℝ ↦ o (2 - r + x) * o x) volume (-1) (-1 + r) :=
    ((ho.comp (continuous_const.add continuous_id)).mul ho).intervalIntegrable _ _
  have hoe : IntervalIntegrable
      (fun x : ℝ ↦ o (2 - r + x) * e x) volume (-1) (-1 + r) :=
    ((ho.comp (continuous_const.add continuous_id)).mul he).intervalIntegrable _ _
  have heo : IntervalIntegrable
      (fun x : ℝ ↦ e (2 - r + x) * o x) volume (-1) (-1 + r) :=
    ((he.comp (continuous_const.add continuous_id)).mul ho).intervalIntegrable _ _
  unfold factorTwoProfileStaticReflectedCorrelation
    factorTwoProfileStaticCrossDifference centeredEndpointCorrelation
    factorTwoCenteredCrossCorrelation factorTwoProfileStaticReflectedPair
  rw [show 1 - (2 - r) = -1 + r by ring,
    intervalIntegral.integral_sub ((hee.sub hoo).const_mul sigma)
      (hoe.sub heo),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub hee hoo,
    intervalIntegral.integral_sub hoe heo]

/-- The new pole-defect numerator is exactly the two boundary tails minus the
reflected static correlation. -/
theorem factorTwoProfileStaticPoleDefectNumerator_eq_boundaryTail_sub_reflected
    (e o : ℝ → ℝ) (he : Continuous e) (ho : Continuous o)
    (sigma r : ℝ) :
    factorTwoProfileStaticPoleDefectNumerator e o sigma r =
      centeredEndpointBoundaryTail e r + centeredEndpointBoundaryTail o r -
        factorTwoProfileStaticReflectedCorrelation e o sigma (2 - r) := by
  have heShift :
      (∫ x : ℝ in -1..-1 + r, e (2 - r + x) ^ 2) =
        ∫ x : ℝ in 1 - r..1, e x ^ 2 := by
    convert intervalIntegral.integral_comp_add_left
      (a := (-1 : ℝ)) (b := -1 + r) (fun y : ℝ ↦ e y ^ 2) (2 - r)
      using 1
    all_goals ring_nf
  have hoShift :
      (∫ x : ℝ in -1..-1 + r, o (2 - r + x) ^ 2) =
        ∫ x : ℝ in 1 - r..1, o x ^ 2 := by
    convert intervalIntegral.integral_comp_add_left
      (a := (-1 : ℝ)) (b := -1 + r) (fun y : ℝ ↦ o y ^ 2) (2 - r)
      using 1
    all_goals ring_nf
  have heShiftInt : IntervalIntegrable
      (fun x : ℝ ↦ e (2 - r + x) ^ 2) volume (-1) (-1 + r) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hoShiftInt : IntervalIntegrable
      (fun x : ℝ ↦ o (2 - r + x) ^ 2) volume (-1) (-1 + r) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have heInt : IntervalIntegrable (fun x : ℝ ↦ e x ^ 2)
      volume (-1) (-1 + r) := (he.pow 2).intervalIntegrable _ _
  have hoInt : IntervalIntegrable (fun x : ℝ ↦ o x ^ 2)
      volume (-1) (-1 + r) := (ho.pow 2).intervalIntegrable _ _
  have hpair : IntervalIntegrable
      (fun x : ℝ ↦ factorTwoProfileStaticReflectedPair e o sigma r x)
      volume (-1) (-1 + r) := by
    apply Continuous.intervalIntegrable
    unfold factorTwoProfileStaticReflectedPair
    fun_prop
  have hreflected :=
    factorTwoProfileStaticReflectedCorrelation_two_sub_eq_pairIntegral
      e o he ho sigma r
  unfold factorTwoProfileStaticPoleDefectNumerator
    factorTwoProfileStaticPoleDefectIntegrand centeredEndpointBoundaryTail
  rw [intervalIntegral.integral_sub
      (((heShiftInt.add hoShiftInt).add heInt).add hoInt) hpair,
    intervalIntegral.integral_add ((heShiftInt.add hoShiftInt).add heInt) hoInt,
    intervalIntegral.integral_add (heShiftInt.add hoShiftInt) heInt,
    intervalIntegral.integral_add heShiftInt hoShiftInt,
    heShift, hoShift, ← hreflected]
  ring

/-- Reflection exchanges the two presentations of the static pole. -/
theorem integral_profileStaticReflectedCorrelation_div_two_sub_eq_reflected
    (e o : ℝ → ℝ) (sigma : ℝ) :
    (∫ t : ℝ in 0..2,
        factorTwoProfileStaticReflectedCorrelation e o sigma t / (2 - t)) =
      ∫ r : ℝ in 0..2,
        factorTwoProfileStaticReflectedCorrelation e o sigma (2 - r) / r := by
  have hreflect := intervalIntegral.integral_comp_sub_left
    (f := fun t : ℝ ↦
      factorTwoProfileStaticReflectedCorrelation e o sigma t / (2 - t))
    (a := (0 : ℝ)) (b := 2) 2
  simpa only [sub_zero, sub_self, sub_sub_cancel] using hreflect.symm

private theorem intervalIntegrable_factorTwoProfileStaticPoleDefectNumerator_div
    (e o : ℝ → ℝ) (he : Continuous e) (ho : Continuous o)
    (sigma : ℝ) :
    IntervalIntegrable
      (fun r : ℝ ↦
        factorTwoProfileStaticPoleDefectNumerator e o sigma r / r)
      volume 0 2 := by
  have heTail := intervalIntegrable_centeredEndpointBoundaryTail_div e he
  have hoTail := intervalIntegrable_centeredEndpointBoundaryTail_div o ho
  have hreflected :=
    intervalIntegrable_factorTwoProfileStaticReflectedCorrelation_two_sub_div
      e o he ho sigma
  apply ((heTail.add hoTail).sub hreflected).congr
  intro r _hr
  change centeredEndpointBoundaryTail e r / r +
      centeredEndpointBoundaryTail o r / r -
      factorTwoProfileStaticReflectedCorrelation e o sigma (2 - r) / r =
    factorTwoProfileStaticPoleDefectNumerator e o sigma r / r
  rw [factorTwoProfileStaticPoleDefectNumerator_eq_boundaryTail_sub_reflected
    e o he ho sigma r]
  ring

/-- Exact fold of the two raw/potential blocks and the reflected static pole
into the positive-distance energy plus the three-square pole defect. -/
theorem centeredEnergy_add_potential_add_logMass_sub_half_staticPole_eq_square
    (e o : ℝ → ℝ) (he : Continuous e) (ho : Continuous o)
    (hlocale : LocallyLipschitzOn (Icc (-1) 1) e)
    (hlocalo : LocallyLipschitzOn (Icc (-1) 1) o)
    (sigma : ℝ) :
    (centeredRawLogEnergy e / 4 +
          (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * e x ^ 2) +
          Real.log 2 * (∫ x : ℝ in -1..1, e x ^ 2)) +
        (centeredRawLogEnergy o / 4 +
          (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * o x ^ 2) +
          Real.log 2 * (∫ x : ℝ in -1..1, o x ^ 2)) -
        (1 / 2 : ℝ) *
          (∫ t : ℝ in 0..2,
            factorTwoProfileStaticReflectedCorrelation e o sigma t / (2 - t)) =
      (1 / 2 : ℝ) *
        (∫ r : ℝ in 0..2,
          factorTwoProfileStaticSingularSquareNumerator e o sigma r / r) := by
  have heEnergy :=
    intervalIntegrable_centeredPositiveDistanceEnergy_div_of_locallyLipschitzOn
      e hlocale
  have hoEnergy :=
    intervalIntegrable_centeredPositiveDistanceEnergy_div_of_locallyLipschitzOn
      o hlocalo
  have heTail := intervalIntegrable_centeredEndpointBoundaryTail_div e he
  have hoTail := intervalIntegrable_centeredEndpointBoundaryTail_div o ho
  have hreflected :=
    intervalIntegrable_factorTwoProfileStaticReflectedCorrelation_two_sub_div
      e o he ho sigma
  have heRaw :=
    half_integral_positiveDistanceEnergy_eq_centeredRaw_of_locallyLipschitzOn
      e hlocale
  have hoRaw :=
    half_integral_positiveDistanceEnergy_eq_centeredRaw_of_locallyLipschitzOn
      o hlocalo
  have heFold := half_integral_centeredEndpointBoundaryTail_div_eq e he
  have hoFold := half_integral_centeredEndpointBoundaryTail_div_eq o ho
  have heCombined :
      centeredRawLogEnergy e / 4 +
            (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * e x ^ 2) +
            Real.log 2 * (∫ x : ℝ in -1..1, e x ^ 2) =
        (1 / 2 : ℝ) *
            (∫ r : ℝ in 0..2, centeredPositiveDistanceEnergy e r / r) +
          (1 / 2 : ℝ) *
            (∫ r : ℝ in 0..2, centeredEndpointBoundaryTail e r / r) := by
    rw [heRaw, heFold]
    ring
  have hoCombined :
      centeredRawLogEnergy o / 4 +
            (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * o x ^ 2) +
            Real.log 2 * (∫ x : ℝ in -1..1, o x ^ 2) =
        (1 / 2 : ℝ) *
            (∫ r : ℝ in 0..2, centeredPositiveDistanceEnergy o r / r) +
          (1 / 2 : ℝ) *
            (∫ r : ℝ in 0..2, centeredEndpointBoundaryTail o r / r) := by
    rw [hoRaw, hoFold]
    ring
  rw [heCombined, hoCombined,
    integral_profileStaticReflectedCorrelation_div_two_sub_eq_reflected]
  rw [show (fun r : ℝ ↦
      factorTwoProfileStaticSingularSquareNumerator e o sigma r / r) =
      fun r ↦
        centeredPositiveDistanceEnergy e r / r +
          centeredPositiveDistanceEnergy o r / r +
          centeredEndpointBoundaryTail e r / r +
          centeredEndpointBoundaryTail o r / r -
          factorTwoProfileStaticReflectedCorrelation e o sigma (2 - r) / r by
    funext r
    unfold factorTwoProfileStaticSingularSquareNumerator
    rw [factorTwoProfileStaticPoleDefectNumerator_eq_boundaryTail_sub_reflected
      e o he ho sigma r]
    ring]
  rw [intervalIntegral.integral_sub
      (((heEnergy.add hoEnergy).add heTail).add hoTail) hreflected,
    intervalIntegral.integral_add ((heEnergy.add hoEnergy).add heTail) hoTail,
    intervalIntegral.integral_add (heEnergy.add hoEnergy) heTail,
    intervalIntegral.integral_add heEnergy hoEnergy]
  ring

/-- Exact square-preserving normal form for either profile-static split. -/
theorem factorTwoProfileStaticBranchForm_eq_singularSquare_add_signedRemainder
    (e o : ℝ → ℝ) (he : Continuous e) (ho : Continuous o)
    (hlocale : LocallyLipschitzOn (Icc (-1) 1) e)
    (hlocalo : LocallyLipschitzOn (Icc (-1) 1) o)
    (sigma : ℝ) :
    factorTwoProfileStaticBranchForm e o sigma =
      (1 / 2 : ℝ) *
          (∫ r : ℝ in 0..2,
            factorTwoProfileStaticSingularSquareNumerator e o sigma r / r) +
        factorTwoProfileStaticSignedRemainder e o sigma := by
  have hphase :=
    profileStatic_symmetric_sub_add_alternating_eq_regular_sub_pole_sub_primes
      e o he ho sigma
  have hsquare :=
    centeredEnergy_add_potential_add_logMass_sub_half_staticPole_eq_square
      e o he ho hlocale hlocalo sigma
  unfold factorTwoProfileStaticBranchForm factorTwoEndpointPhaseDiagonal
  rw [show yoshidaEndpointOddCleanQuadratic e +
          sigma * factorTwoCenteredSymmetricPerturbation e +
          (yoshidaEndpointOddCleanQuadratic o +
            -sigma * factorTwoCenteredSymmetricPerturbation o) +
          factorTwoCenteredAlternatingCoupling e o =
      yoshidaEndpointOddCleanQuadratic e +
        yoshidaEndpointOddCleanQuadratic o +
        (sigma *
            (factorTwoCenteredSymmetricPerturbation e -
              factorTwoCenteredSymmetricPerturbation o) +
          factorTwoCenteredAlternatingCoupling e o) by ring,
    hphase]
  unfold yoshidaEndpointOddCleanQuadratic
    factorTwoProfileStaticSignedRemainder
  rw [← hsquare]
  ring

/-- Strongest unconditional coupled handoff from the exact assembly: the
whole inherent half of the three-square pole remains beside the signed
remainder, and only the nonnegative positive-distance energy is dropped. -/
theorem half_integral_staticPoleSquare_add_signedRemainder_le_staticBranch
    (e o : ℝ → ℝ) (he : Continuous e) (ho : Continuous o)
    (hlocale : LocallyLipschitzOn (Icc (-1) 1) e)
    (hlocalo : LocallyLipschitzOn (Icc (-1) 1) o)
    (sigma : ℝ) (hsigma : sigma ^ 2 = 1) :
    (1 / 2 : ℝ) *
          (∫ r : ℝ in 0..2,
            factorTwoProfileStaticPoleSquareNumerator e o sigma r / r) +
        factorTwoProfileStaticSignedRemainder e o sigma ≤
      factorTwoProfileStaticBranchForm e o sigma := by
  have heEnergy :=
    intervalIntegrable_centeredPositiveDistanceEnergy_div_of_locallyLipschitzOn
      e hlocale
  have hoEnergy :=
    intervalIntegrable_centeredPositiveDistanceEnergy_div_of_locallyLipschitzOn
      o hlocalo
  have hpole := intervalIntegrable_factorTwoProfileStaticPoleDefectNumerator_div
    e o he ho sigma
  have hsingular : IntervalIntegrable
      (fun r : ℝ ↦
        factorTwoProfileStaticSingularSquareNumerator e o sigma r / r)
      volume 0 2 := by
    apply ((heEnergy.add hoEnergy).add hpole).congr
    intro r _hr
    unfold factorTwoProfileStaticSingularSquareNumerator
    ring
  have hmono :
      (∫ r : ℝ in 0..2,
          factorTwoProfileStaticPoleDefectNumerator e o sigma r / r) ≤
        ∫ r : ℝ in 0..2,
          factorTwoProfileStaticSingularSquareNumerator e o sigma r / r := by
    apply intervalIntegral.integral_mono_on (by norm_num) hpole hsingular
    intro r hr
    by_cases hrzero : r = 0
    · simp [hrzero]
    · have hrpos : 0 < r := lt_of_le_of_ne hr.1 (Ne.symm hrzero)
      have heNonneg : 0 ≤ centeredPositiveDistanceEnergy e r := by
        unfold centeredPositiveDistanceEnergy
        apply intervalIntegral.integral_nonneg (by linarith [hr.2])
        intro x _hx
        positivity
      have hoNonneg : 0 ≤ centeredPositiveDistanceEnergy o r := by
        unfold centeredPositiveDistanceEnergy
        apply intervalIntegral.integral_nonneg (by linarith [hr.2])
        intro x _hx
        positivity
      unfold factorTwoProfileStaticSingularSquareNumerator
      exact div_le_div_of_nonneg_right (by linarith) hrpos.le
  have hpoleEq :
      (∫ r : ℝ in 0..2,
          factorTwoProfileStaticPoleDefectNumerator e o sigma r / r) =
        ∫ r : ℝ in 0..2,
          factorTwoProfileStaticPoleSquareNumerator e o sigma r / r := by
    apply intervalIntegral.integral_congr
    intro r _hr
    change factorTwoProfileStaticPoleDefectNumerator e o sigma r / r =
      factorTwoProfileStaticPoleSquareNumerator e o sigma r / r
    rw [factorTwoProfileStaticPoleDefectNumerator_eq_square
      e o sigma hsigma r]
  rw [← hpoleEq]
  rw [factorTwoProfileStaticBranchForm_eq_singularSquare_add_signedRemainder
    e o he ho hlocale hlocalo sigma]
  nlinarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseProfileStaticSquareAssemblyStructural

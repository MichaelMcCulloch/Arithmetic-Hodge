import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseEnvelope
import ArithmeticHodge.Analysis.YoshidaEndpointTriangleFoldLipschitz

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseSingularSquare

open CenteredEndpointCorrelation
open UnitIntervalLogEnergyAffine
open YoshidaEndpointBoundaryTailFold
open YoshidaEndpointPotentialBound
open YoshidaEndpointSingularCorrelation
open YoshidaEndpointTriangleFoldLipschitz
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoPhaseEnvelope

noncomputable section

/-!
# Exact square for the reflected factor-two pole

The reflected phase correlation pairs the two endpoint intervals left out by
the positive-distance overlap.  Keeping this pairing signed, rather than
bounding its absolute value, completes the endpoint tails to a two-vector
square.  The positive-distance overlap energy remains as a second, already
positive, square.
-/

/-- The pointwise endpoint square obtained by pairing the left endpoint
vector with the translated right endpoint vector. -/
def factorTwoPhaseEndpointSquare
    (u v : ℝ → ℝ) (a b r x : ℝ) : ℝ :=
  (u (2 - r + x) - (a * u x + b * v x) / 2) ^ 2 +
    (v (2 - r + x) - (-b * u x + a * v x) / 2) ^ 2 +
    (1 - (a ^ 2 + b ^ 2) / 4) * (u x ^ 2 + v x ^ 2)

/-- The exact algebra behind the endpoint square.  The sign is the one in
the reflected phase `factorTwoCenteredPhaseCorrelation u v a (-b)`. -/
theorem endpoint_phase_pair_eq_square
    (a b u₀ v₀ u₁ v₁ : ℝ) :
    u₁ ^ 2 + v₁ ^ 2 + u₀ ^ 2 + v₀ ^ 2 -
        (a * (u₁ * u₀ + v₁ * v₀) -
          b * (v₁ * u₀ - u₁ * v₀)) =
      (u₁ - (a * u₀ + b * v₀) / 2) ^ 2 +
        (v₁ - (-b * u₀ + a * v₀) / 2) ^ 2 +
        (1 - (a ^ 2 + b ^ 2) / 4) * (u₀ ^ 2 + v₀ ^ 2) := by
  ring

/-- The endpoint square is pointwise nonnegative for every phase in the
closed unit disk. -/
theorem factorTwoPhaseEndpointSquare_nonneg
    (u v : ℝ → ℝ) (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1)
    (r x : ℝ) :
    0 ≤ factorTwoPhaseEndpointSquare u v a b r x := by
  unfold factorTwoPhaseEndpointSquare
  have hcoeff : 0 ≤ 1 - (a ^ 2 + b ^ 2) / 4 := by
    nlinarith
  positivity

/-- The sum of the positive-distance overlap squares and the completed
endpoint square at distance `r`. -/
def factorTwoPhaseSingularSquareNumerator
    (u v : ℝ → ℝ) (a b r : ℝ) : ℝ :=
  (∫ x : ℝ in -1..1 - r,
      (u (r + x) - u x) ^ 2 + (v (r + x) - v x) ^ 2) +
    ∫ x : ℝ in -1..-1 + r,
      factorTwoPhaseEndpointSquare u v a b r x

/-- Before completing squares, the same numerator is the two fixed-distance
correlation defects minus the signed reflected phase correlation. -/
def factorTwoPhaseSingularCorrelationNumerator
    (u v : ℝ → ℝ) (a b r : ℝ) : ℝ :=
  centeredPositiveDistanceEnergy u r +
    centeredPositiveDistanceEnergy v r +
    centeredEndpointBoundaryTail u r +
    centeredEndpointBoundaryTail v r -
    factorTwoCenteredPhaseCorrelation u v a (-b) (2 - r)

/-- Exact fixed-distance completion of the endpoint tails.  The first
integral on the right is the positive-distance energy at shift `r`; only the
second integral completes the reflected endpoint pairing to a square. -/
theorem factorTwoPhaseSingularCorrelationNumerator_eq_square
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    (a b r : ℝ) :
    factorTwoPhaseSingularCorrelationNumerator u v a b r =
      factorTwoPhaseSingularSquareNumerator u v a b r := by
  have huShift :
      (∫ x : ℝ in -1..-1 + r, u (2 - r + x) ^ 2) =
        ∫ x : ℝ in 1 - r..1, u x ^ 2 := by
    convert intervalIntegral.integral_comp_add_left
      (a := (-1 : ℝ)) (b := -1 + r) (fun y : ℝ ↦ u y ^ 2) (2 - r) using 1
    all_goals ring_nf
  have hvShift :
      (∫ x : ℝ in -1..-1 + r, v (2 - r + x) ^ 2) =
        ∫ x : ℝ in 1 - r..1, v x ^ 2 := by
    convert intervalIntegral.integral_comp_add_left
      (a := (-1 : ℝ)) (b := -1 + r) (fun y : ℝ ↦ v y ^ 2) (2 - r) using 1
    all_goals ring_nf
  have huu : IntervalIntegrable
      (fun x : ℝ ↦ u (2 - r + x) * u x) volume (-1) (-1 + r) :=
    ((hu.comp (continuous_const.add continuous_id)).mul hu).intervalIntegrable _ _
  have hvv : IntervalIntegrable
      (fun x : ℝ ↦ v (2 - r + x) * v x) volume (-1) (-1 + r) :=
    ((hv.comp (continuous_const.add continuous_id)).mul hv).intervalIntegrable _ _
  have hvu : IntervalIntegrable
      (fun x : ℝ ↦ v (2 - r + x) * u x) volume (-1) (-1 + r) :=
    ((hv.comp (continuous_const.add continuous_id)).mul hu).intervalIntegrable _ _
  have huv : IntervalIntegrable
      (fun x : ℝ ↦ u (2 - r + x) * v x) volume (-1) (-1 + r) :=
    ((hu.comp (continuous_const.add continuous_id)).mul hv).intervalIntegrable _ _
  have hphase :
      factorTwoCenteredPhaseCorrelation u v a (-b) (2 - r) =
        ∫ x : ℝ in -1..-1 + r,
          a * (u (2 - r + x) * u x + v (2 - r + x) * v x) -
            b * (v (2 - r + x) * u x - u (2 - r + x) * v x) := by
    unfold factorTwoCenteredPhaseCorrelation centeredEndpointCorrelation
      factorTwoCenteredCrossCorrelation
    rw [show 1 - (2 - r) = -1 + r by ring,
      intervalIntegral.integral_sub
        ((huu.add hvv).const_mul a) ((hvu.sub huv).const_mul b),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add huu hvv,
      intervalIntegral.integral_sub hvu huv]
    ring
  have huSq : Continuous (fun x : ℝ ↦ u x ^ 2) := hu.pow 2
  have hvSq : Continuous (fun x : ℝ ↦ v x ^ 2) := hv.pow 2
  have huShiftSq : Continuous (fun x : ℝ ↦ u (2 - r + x) ^ 2) := by
    fun_prop
  have hvShiftSq : Continuous (fun x : ℝ ↦ v (2 - r + x) ^ 2) := by
    fun_prop
  have huShiftSqInt : IntervalIntegrable
      (fun x : ℝ ↦ u (2 - r + x) ^ 2) volume (-1) (-1 + r) :=
    huShiftSq.intervalIntegrable _ _
  have hvShiftSqInt : IntervalIntegrable
      (fun x : ℝ ↦ v (2 - r + x) ^ 2) volume (-1) (-1 + r) :=
    hvShiftSq.intervalIntegrable _ _
  have huSqInt : IntervalIntegrable
      (fun x : ℝ ↦ u x ^ 2) volume (-1) (-1 + r) :=
    huSq.intervalIntegrable _ _
  have hvSqInt : IntervalIntegrable
      (fun x : ℝ ↦ v x ^ 2) volume (-1) (-1 + r) :=
    hvSq.intervalIntegrable _ _
  have hpairInt : IntervalIntegrable
      (fun x : ℝ ↦
        u (2 - r + x) ^ 2 + v (2 - r + x) ^ 2 +
          u x ^ 2 + v x ^ 2) volume (-1) (-1 + r) :=
    (((huShiftSq.add hvShiftSq).add huSq).add hvSq).intervalIntegrable _ _
  have hphaseInt : IntervalIntegrable
      (fun x : ℝ ↦
        a * (u (2 - r + x) * u x + v (2 - r + x) * v x) -
          b * (v (2 - r + x) * u x - u (2 - r + x) * v x))
      volume (-1) (-1 + r) :=
    ((huu.add hvv).const_mul a).sub ((hvu.sub huv).const_mul b)
  have hpair :
      ((∫ x : ℝ in -1..-1 + r, u (2 - r + x) ^ 2) +
          ∫ x : ℝ in -1..-1 + r, u x ^ 2) +
        ((∫ x : ℝ in -1..-1 + r, v (2 - r + x) ^ 2) +
          ∫ x : ℝ in -1..-1 + r, v x ^ 2) =
        ∫ x : ℝ in -1..-1 + r,
          u (2 - r + x) ^ 2 + v (2 - r + x) ^ 2 +
            u x ^ 2 + v x ^ 2 := by
    calc
      _ = ((∫ x : ℝ in -1..-1 + r, u (2 - r + x) ^ 2) +
            ∫ x : ℝ in -1..-1 + r, v (2 - r + x) ^ 2) +
          ((∫ x : ℝ in -1..-1 + r, u x ^ 2) +
            ∫ x : ℝ in -1..-1 + r, v x ^ 2) := by ring
      _ = (∫ x : ℝ in -1..-1 + r,
              u (2 - r + x) ^ 2 + v (2 - r + x) ^ 2) +
            ∫ x : ℝ in -1..-1 + r, u x ^ 2 + v x ^ 2 := by
        rw [intervalIntegral.integral_add huShiftSqInt hvShiftSqInt,
          intervalIntegral.integral_add huSqInt hvSqInt]
      _ = ∫ x : ℝ in -1..-1 + r,
          (u (2 - r + x) ^ 2 + v (2 - r + x) ^ 2) +
            (u x ^ 2 + v x ^ 2) := by
        rw [intervalIntegral.integral_add
          (huShiftSqInt.add hvShiftSqInt) (huSqInt.add hvSqInt)]
      _ = _ := by
        apply intervalIntegral.integral_congr
        intro x _hx
        ring
  have hendpoint :
      centeredEndpointBoundaryTail u r +
          centeredEndpointBoundaryTail v r -
          factorTwoCenteredPhaseCorrelation u v a (-b) (2 - r) =
        ∫ x : ℝ in -1..-1 + r,
          factorTwoPhaseEndpointSquare u v a b r x := by
    rw [hphase]
    unfold centeredEndpointBoundaryTail
    rw [← huShift, ← hvShift]
    rw [hpair, ← intervalIntegral.integral_sub hpairInt hphaseInt]
    apply intervalIntegral.integral_congr
    intro x _hx
    unfold factorTwoPhaseEndpointSquare
    exact endpoint_phase_pair_eq_square
      a b (u x) (v x) (u (2 - r + x)) (v (2 - r + x))
  have huDiffSq : Continuous
      (fun x : ℝ ↦ (u (r + x) - u x) ^ 2) := by
    fun_prop
  have hvDiffSq : Continuous
      (fun x : ℝ ↦ (v (r + x) - v x) ^ 2) := by
    fun_prop
  have huDiffSqInt : IntervalIntegrable
      (fun x : ℝ ↦ (u (r + x) - u x) ^ 2) volume (-1) (1 - r) :=
    huDiffSq.intervalIntegrable _ _
  have hvDiffSqInt : IntervalIntegrable
      (fun x : ℝ ↦ (v (r + x) - v x) ^ 2) volume (-1) (1 - r) :=
    hvDiffSq.intervalIntegrable _ _
  unfold factorTwoPhaseSingularCorrelationNumerator
    factorTwoPhaseSingularSquareNumerator centeredPositiveDistanceEnergy
  rw [← intervalIntegral.integral_add
      huDiffSqInt hvDiffSqInt]
  rw [← hendpoint]
  ring

/-- The completed fixed-distance numerator is nonnegative throughout the
distance interval for every phase in the closed unit disk. -/
theorem factorTwoPhaseSingularSquareNumerator_nonneg
    (u v : ℝ → ℝ) (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1)
    {r : ℝ} (hr0 : 0 ≤ r) (hr2 : r ≤ 2) :
    0 ≤ factorTwoPhaseSingularSquareNumerator u v a b r := by
  unfold factorTwoPhaseSingularSquareNumerator
  apply add_nonneg
  · apply intervalIntegral.integral_nonneg (by linarith)
    intro x _hx
    positivity
  · apply intervalIntegral.integral_nonneg (by linarith)
    intro x _hx
    exact factorTwoPhaseEndpointSquare_nonneg u v a b hab r x

/-- Correlation form of the same fixed-distance nonnegativity statement. -/
theorem factorTwoPhaseSingularCorrelationNumerator_nonneg
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1)
    {r : ℝ} (hr0 : 0 ≤ r) (hr2 : r ≤ 2) :
    0 ≤ factorTwoPhaseSingularCorrelationNumerator u v a b r := by
  rw [factorTwoPhaseSingularCorrelationNumerator_eq_square u v hu hv a b r]
  exact factorTwoPhaseSingularSquareNumerator_nonneg u v a b hab hr0 hr2

/-- The completed singular density is interval-integrable on the locally
Lipschitz source domain. -/
theorem intervalIntegrable_factorTwoPhaseSingularSquareNumerator_div
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    (hlocalu : LocallyLipschitzOn (Icc (-1) 1) u)
    (hlocalv : LocallyLipschitzOn (Icc (-1) 1) v)
    (a b : ℝ) :
    IntervalIntegrable
      (fun r : ℝ ↦ factorTwoPhaseSingularSquareNumerator u v a b r / r)
      volume 0 2 := by
  have huEnergy :=
    intervalIntegrable_centeredPositiveDistanceEnergy_div_of_locallyLipschitzOn
      u hlocalu
  have hvEnergy :=
    intervalIntegrable_centeredPositiveDistanceEnergy_div_of_locallyLipschitzOn
      v hlocalv
  have huBoundary := intervalIntegrable_centeredEndpointBoundaryTail_div u hu
  have hvBoundary := intervalIntegrable_centeredEndpointBoundaryTail_div v hv
  have hphase :=
    intervalIntegrable_factorTwoCenteredPhaseCorrelation_two_sub_div
      u v hu hv a (-b)
  have hcorrelation :=
    (((huEnergy.add hvEnergy).add huBoundary).add hvBoundary).sub hphase
  apply hcorrelation.congr
  intro r _hr
  change
    centeredPositiveDistanceEnergy u r / r +
          centeredPositiveDistanceEnergy v r / r +
          centeredEndpointBoundaryTail u r / r +
          centeredEndpointBoundaryTail v r / r -
          factorTwoCenteredPhaseCorrelation u v a (-b) (2 - r) / r =
      factorTwoPhaseSingularSquareNumerator u v a b r / r
  rw [← factorTwoPhaseSingularCorrelationNumerator_eq_square
    u v hu hv a b r]
  unfold factorTwoPhaseSingularCorrelationNumerator
  ring

/-- The singular square integral is nonnegative for every closed-disk phase. -/
theorem integral_factorTwoPhaseSingularSquareNumerator_div_nonneg
    (u v : ℝ → ℝ) (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    0 ≤ ∫ r : ℝ in 0..2,
      factorTwoPhaseSingularSquareNumerator u v a b r / r := by
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro r hr
  exact div_nonneg
    (factorTwoPhaseSingularSquareNumerator_nonneg u v a b hab hr.1 hr.2)
    hr.1

/-- The same nonnegative singular integral in the original correlation
variables, before the endpoint square is exposed. -/
theorem integral_factorTwoPhaseSingularCorrelationNumerator_div_nonneg
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    0 ≤ ∫ r : ℝ in 0..2,
      factorTwoPhaseSingularCorrelationNumerator u v a b r / r := by
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro r hr
  exact div_nonneg
    (factorTwoPhaseSingularCorrelationNumerator_nonneg
      u v hu hv a b hab hr.1 hr.2)
    hr.1

/-- Exact integrated recombination of the two raw/potential energies with
the signed reflected Cauchy pole.  No absolute value or separate-channel
estimate occurs: after the exact `log 2` mass cancellation, the remainder is
one half of the singular square integral. -/
theorem centeredEnergy_add_potential_add_logMass_sub_half_phasePole_eq_square
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    (hlocalu : LocallyLipschitzOn (Icc (-1) 1) u)
    (hlocalv : LocallyLipschitzOn (Icc (-1) 1) v)
    (a b : ℝ) :
    (centeredRawLogEnergy u / 4 +
          (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * u x ^ 2) +
          Real.log 2 * (∫ x : ℝ in -1..1, u x ^ 2)) +
        (centeredRawLogEnergy v / 4 +
          (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * v x ^ 2) +
          Real.log 2 * (∫ x : ℝ in -1..1, v x ^ 2)) -
        (1 / 2 : ℝ) *
          (∫ t : ℝ in 0..2,
            factorTwoCenteredPhaseCorrelation u v a (-b) t / (2 - t)) =
      (1 / 2 : ℝ) *
        (∫ r : ℝ in 0..2,
          factorTwoPhaseSingularSquareNumerator u v a b r / r) := by
  have huEnergy :=
    intervalIntegrable_centeredPositiveDistanceEnergy_div_of_locallyLipschitzOn
      u hlocalu
  have hvEnergy :=
    intervalIntegrable_centeredPositiveDistanceEnergy_div_of_locallyLipschitzOn
      v hlocalv
  have huBoundary := intervalIntegrable_centeredEndpointBoundaryTail_div u hu
  have hvBoundary := intervalIntegrable_centeredEndpointBoundaryTail_div v hv
  have hphase :=
    intervalIntegrable_factorTwoCenteredPhaseCorrelation_two_sub_div
      u v hu hv a (-b)
  have huRaw :=
    half_integral_positiveDistanceEnergy_eq_centeredRaw_of_locallyLipschitzOn
      u hlocalu
  have hvRaw :=
    half_integral_positiveDistanceEnergy_eq_centeredRaw_of_locallyLipschitzOn
      v hlocalv
  have huTail := half_integral_centeredEndpointBoundaryTail_div_eq u hu
  have hvTail := half_integral_centeredEndpointBoundaryTail_div_eq v hv
  have huFold :
      centeredRawLogEnergy u / 4 +
          (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * u x ^ 2) +
          Real.log 2 * (∫ x : ℝ in -1..1, u x ^ 2) =
        (1 / 2 : ℝ) *
            (∫ r : ℝ in 0..2, centeredPositiveDistanceEnergy u r / r) +
          (1 / 2 : ℝ) *
            (∫ r : ℝ in 0..2, centeredEndpointBoundaryTail u r / r) := by
    rw [huRaw, huTail]
    ring
  have hvFold :
      centeredRawLogEnergy v / 4 +
          (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * v x ^ 2) +
          Real.log 2 * (∫ x : ℝ in -1..1, v x ^ 2) =
        (1 / 2 : ℝ) *
            (∫ r : ℝ in 0..2, centeredPositiveDistanceEnergy v r / r) +
          (1 / 2 : ℝ) *
            (∫ r : ℝ in 0..2, centeredEndpointBoundaryTail v r / r) := by
    rw [hvRaw, hvTail]
    ring
  rw [huFold, hvFold,
    integral_phaseCorrelation_div_two_sub_eq_reflected]
  rw [show (fun r : ℝ ↦
      factorTwoPhaseSingularSquareNumerator u v a b r / r) =
      fun r ↦
        centeredPositiveDistanceEnergy u r / r +
          centeredPositiveDistanceEnergy v r / r +
          centeredEndpointBoundaryTail u r / r +
          centeredEndpointBoundaryTail v r / r -
          factorTwoCenteredPhaseCorrelation u v a (-b) (2 - r) / r by
    funext r
    rw [← factorTwoPhaseSingularCorrelationNumerator_eq_square
      u v hu hv a b r]
    unfold factorTwoPhaseSingularCorrelationNumerator
    ring]
  rw [intervalIntegral.integral_sub
      (((huEnergy.add hvEnergy).add huBoundary).add hvBoundary) hphase,
    intervalIntegral.integral_add
      ((huEnergy.add hvEnergy).add huBoundary) hvBoundary,
    intervalIntegral.integral_add (huEnergy.add hvEnergy) huBoundary,
    intervalIntegral.integral_add huEnergy hvEnergy]
  ring

/-- Consequently the exact raw/potential block plus the reflected pole is
bounded below only by the scalar `-log 2` mass term. -/
theorem neg_logMass_le_centeredEnergy_add_potential_sub_half_phasePole
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    (hlocalu : LocallyLipschitzOn (Icc (-1) 1) u)
    (hlocalv : LocallyLipschitzOn (Icc (-1) 1) v)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    -(Real.log 2 *
        ((∫ x : ℝ in -1..1, u x ^ 2) +
          ∫ x : ℝ in -1..1, v x ^ 2)) ≤
      (centeredRawLogEnergy u / 4 +
          (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * u x ^ 2)) +
        (centeredRawLogEnergy v / 4 +
          (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * v x ^ 2)) -
        (1 / 2 : ℝ) *
          (∫ t : ℝ in 0..2,
            factorTwoCenteredPhaseCorrelation u v a (-b) t / (2 - t)) := by
  have hid :=
    centeredEnergy_add_potential_add_logMass_sub_half_phasePole_eq_square
      u v hu hv hlocalu hlocalv a b
  have hnonneg :=
    integral_factorTwoPhaseSingularSquareNumerator_div_nonneg u v a b hab
  nlinarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseSingularSquare

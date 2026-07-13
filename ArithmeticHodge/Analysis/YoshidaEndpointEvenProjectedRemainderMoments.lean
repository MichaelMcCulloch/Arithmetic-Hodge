import ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedRemainderMajorant

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedRemainderMoments

open YoshidaEndpointEvenAtanhReciprocalMajorant
open YoshidaEndpointEvenProjectedDualIdentity
open YoshidaEndpointEvenProjectedRemainderMajorant

noncomputable section

def fixedProjectedShiftedRemainder0 : ℝ → ℝ :=
  fixedProjectedShiftedRemainder 1 0

def fixedProjectedShiftedRemainder2 : ℝ → ℝ :=
  fixedProjectedShiftedRemainder 0 1

theorem fixedProjectedShiftedRemainder_linear (c b x : ℝ) :
    fixedProjectedShiftedRemainder c b x =
      c * fixedProjectedShiftedRemainder0 x +
        b * fixedProjectedShiftedRemainder2 x := by
  unfold fixedProjectedShiftedRemainder0 fixedProjectedShiftedRemainder2
  unfold fixedProjectedShiftedRemainder
    fixedProjectedBoundedRemainder fixedProjectionPolynomial
    fixedEvenLowProfile
  ring

def fixedProjectedPolynomialRemainderGram00 : ℝ :=
  ∫ x : ℝ in -1..1,
    atanhTailWeightReciprocalMajorant x *
      fixedProjectedShiftedRemainder0 x ^ 2

def fixedProjectedPolynomialRemainderGram02 : ℝ :=
  ∫ x : ℝ in -1..1,
    atanhTailWeightReciprocalMajorant x *
      fixedProjectedShiftedRemainder0 x *
        fixedProjectedShiftedRemainder2 x

def fixedProjectedPolynomialRemainderGram22 : ℝ :=
  ∫ x : ℝ in -1..1,
    atanhTailWeightReciprocalMajorant x *
      fixedProjectedShiftedRemainder2 x ^ 2

theorem fixedProjectedPolynomialRemainderIntegrand_eq_gram
    (c b x : ℝ) :
    fixedProjectedPolynomialRemainderIntegrand c b x =
      c ^ 2 *
          (atanhTailWeightReciprocalMajorant x *
            fixedProjectedShiftedRemainder0 x ^ 2) +
        2 * c * b *
          (atanhTailWeightReciprocalMajorant x *
            fixedProjectedShiftedRemainder0 x *
              fixedProjectedShiftedRemainder2 x) +
        b ^ 2 *
          (atanhTailWeightReciprocalMajorant x *
            fixedProjectedShiftedRemainder2 x ^ 2) := by
  unfold fixedProjectedPolynomialRemainderIntegrand
  rw [fixedProjectedShiftedRemainder_linear]
  ring

/-- The universal polynomial remainder is exactly the quadratic form of three
fixed ordinary moments. -/
theorem integral_fixedProjectedPolynomialRemainder_eq_gram
    (c b : ℝ)
    (h00 : IntervalIntegrable
      (fun x ↦ atanhTailWeightReciprocalMajorant x *
        fixedProjectedShiftedRemainder0 x ^ 2) volume (-1) 1)
    (h02 : IntervalIntegrable
      (fun x ↦ atanhTailWeightReciprocalMajorant x *
        fixedProjectedShiftedRemainder0 x *
          fixedProjectedShiftedRemainder2 x) volume (-1) 1)
    (h22 : IntervalIntegrable
      (fun x ↦ atanhTailWeightReciprocalMajorant x *
        fixedProjectedShiftedRemainder2 x ^ 2) volume (-1) 1) :
    (∫ x : ℝ in -1..1,
      fixedProjectedPolynomialRemainderIntegrand c b x) =
        fixedProjectedPolynomialRemainderGram00 * c ^ 2 +
          2 * fixedProjectedPolynomialRemainderGram02 * c * b +
          fixedProjectedPolynomialRemainderGram22 * b ^ 2 := by
  rw [show (fun x : ℝ ↦ fixedProjectedPolynomialRemainderIntegrand c b x) =
      fun x ↦ c ^ 2 *
          (atanhTailWeightReciprocalMajorant x *
            fixedProjectedShiftedRemainder0 x ^ 2) +
        ((2 * c * b) *
            (atanhTailWeightReciprocalMajorant x *
              fixedProjectedShiftedRemainder0 x *
                fixedProjectedShiftedRemainder2 x) +
          b ^ 2 *
            (atanhTailWeightReciprocalMajorant x *
              fixedProjectedShiftedRemainder2 x ^ 2)) by
    funext x
    rw [fixedProjectedPolynomialRemainderIntegrand_eq_gram]
    ring,
    intervalIntegral.integral_add (h00.const_mul (c ^ 2))
      ((h02.const_mul (2 * c * b)).add (h22.const_mul (b ^ 2))),
    intervalIntegral.integral_add (h02.const_mul (2 * c * b))
      (h22.const_mul (b ^ 2)),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  unfold fixedProjectedPolynomialRemainderGram00
    fixedProjectedPolynomialRemainderGram02
    fixedProjectedPolynomialRemainderGram22
  ring

end

end ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedRemainderMoments

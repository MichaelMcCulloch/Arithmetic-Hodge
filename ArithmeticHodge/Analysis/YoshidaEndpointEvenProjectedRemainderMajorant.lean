import ArithmeticHodge.Analysis.YoshidaEndpointEvenAtanhReciprocalMajorant
import ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedDualIntegral

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedRemainderMajorant

open YoshidaEndpointEvenAtanhReciprocalMajorant
open YoshidaEndpointEvenProjectedDualIdentity
open YoshidaEndpointEvenProjectedDualIntegral
open YoshidaEndpointOddCleanPositive

noncomputable section

/-- The final ordinary polynomial-weighted square after both endpoint
singularities have been eliminated. -/
def fixedProjectedPolynomialRemainderIntegrand (c b x : ℝ) : ℝ :=
  atanhTailWeightReciprocalMajorant x *
    fixedProjectedShiftedRemainder c b x ^ 2

theorem fixedProjectedAtanhRemainder_le_polynomial
    (c b : ℝ) {x : ℝ} (hx : x ∈ Icc (-1) 1) :
    fixedProjectedAtanhRemainderIntegrand c b x ≤
      fixedProjectedPolynomialRemainderIntegrand c b x := by
  unfold fixedProjectedAtanhRemainderIntegrand
    fixedProjectedPolynomialRemainderIntegrand
  exact sq_div_atanhTailWeight_le_majorant_mul_sq
    (fixedProjectedShiftedRemainder c b x) hx

/-- The rationally weighted remainder is bounded by an ordinary polynomial
moment. -/
theorem fixedProjectedAtanhRemainder_integral_le_polynomial
    (c b : ℝ)
    (hatanh : IntervalIntegrable
      (fixedProjectedAtanhRemainderIntegrand c b) volume (-1) 1)
    (hpoly : IntervalIntegrable
      (fixedProjectedPolynomialRemainderIntegrand c b) volume (-1) 1) :
    (∫ x : ℝ in -1..1,
      fixedProjectedAtanhRemainderIntegrand c b x) ≤
        ∫ x : ℝ in -1..1,
          fixedProjectedPolynomialRemainderIntegrand c b x := by
  apply intervalIntegral.integral_mono_on
    (by norm_num : (-1 : ℝ) ≤ 1) hatanh hpoly
  intro x hx
  exact fixedProjectedAtanhRemainder_le_polynomial c b hx

/-- Full projected dual control now follows from one nonsingular
polynomial-moment inequality. -/
theorem fixedProjectedDual_integral_le_clean_of_polynomial_remainder
    (c b : ℝ)
    (hbase : IntervalIntegrable
      (fixedProjectedDualBaseIntegrand c b) volume (-1) 1)
    (htrue : IntervalIntegrable
      (fixedProjectedTrueRemainderIntegrand c b) volume (-1) 1)
    (hatanh : IntervalIntegrable
      (fixedProjectedAtanhRemainderIntegrand c b) volume (-1) 1)
    (hpoly : IntervalIntegrable
      (fixedProjectedPolynomialRemainderIntegrand c b) volume (-1) 1)
    (hbound :
      (∫ x : ℝ in -1..1,
          fixedProjectedPolynomialRemainderIntegrand c b x) ≤
        yoshidaEndpointOddCleanQuadratic
            (fun x ↦ fixedEvenLowProfile c b x) -
          ∫ x : ℝ in -1..1,
            fixedProjectedDualBaseIntegrand c b x) :
    (∫ x : ℝ in -1..1, fixedProjectedDualIntegrand c b x) ≤
      yoshidaEndpointOddCleanQuadratic
        (fun x ↦ fixedEvenLowProfile c b x) := by
  have hrem := fixedProjectedAtanhRemainder_integral_le_polynomial
    c b hatanh hpoly
  apply fixedProjectedDual_integral_le_clean_of_atanh_remainder
    c b hbase htrue hatanh
  linarith

end

end ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedRemainderMajorant

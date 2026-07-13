import ArithmeticHodge.Analysis.YoshidaEndpointEvenAtanhTailWeight

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedDualIntegral

open YoshidaEndpointEvenAtanhTailWeight
open YoshidaEndpointEvenProjectedDualIdentity
open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointPotentialBound

noncomputable section

/-- The fixed projected weighted-dual integrand. -/
def fixedProjectedDualIntegrand (c b x : ℝ) : ℝ :=
  (c * fixedProjectedTailRepresenter0 x +
      b * fixedProjectedTailRepresenter2 x) ^ 2 /
    yoshidaEndpointEvenTailWeight x

/-- The part obtained after exactly extracting the endpoint potential and
before the final bounded square. -/
def fixedProjectedDualBaseIntegrand (c b x : ℝ) : ℝ :=
  yoshidaEndpointPotential x * fixedEvenLowProfile c b x ^ 2 +
    2 * fixedEvenLowProfile c b x *
      fixedProjectedBoundedRemainder c b x -
    (41 / 60 : ℝ) * fixedEvenLowProfile c b x ^ 2

/-- The bounded remainder over the true logarithmic tail weight. -/
def fixedProjectedTrueRemainderIntegrand (c b x : ℝ) : ℝ :=
  fixedProjectedShiftedRemainder c b x ^ 2 /
    yoshidaEndpointEvenTailWeight x

/-- The same bounded remainder over the smaller rational transformed weight. -/
def fixedProjectedAtanhRemainderIntegrand (c b x : ℝ) : ℝ :=
  fixedProjectedShiftedRemainder c b x ^ 2 /
    yoshidaEndpointEvenAtanhTailWeight x

theorem fixedProjectedDual_pointwise_decomposition
    (c b : ℝ) {x : ℝ} (hx : x ∈ Icc (-1) 1) :
    fixedProjectedDualIntegrand c b x =
      fixedProjectedDualBaseIntegrand c b x +
        fixedProjectedTrueRemainderIntegrand c b x := by
  unfold fixedProjectedDualIntegrand fixedProjectedDualBaseIntegrand
    fixedProjectedTrueRemainderIntegrand
  exact fixedProjectedTailRepresenter_sq_div_weight c b x hx

/-- Exact integral decomposition.  The hypotheses record only the two
ordinary interval-integrability obligations needed for linearity. -/
theorem fixedProjectedDual_integral_decomposition
    (c b : ℝ)
    (hbase : IntervalIntegrable
      (fixedProjectedDualBaseIntegrand c b) volume (-1) 1)
    (hrem : IntervalIntegrable
      (fixedProjectedTrueRemainderIntegrand c b) volume (-1) 1) :
    (∫ x : ℝ in -1..1, fixedProjectedDualIntegrand c b x) =
      (∫ x : ℝ in -1..1, fixedProjectedDualBaseIntegrand c b x) +
        ∫ x : ℝ in -1..1,
          fixedProjectedTrueRemainderIntegrand c b x := by
  calc
    (∫ x : ℝ in -1..1, fixedProjectedDualIntegrand c b x) =
        ∫ x : ℝ in -1..1,
          (fixedProjectedDualBaseIntegrand c b x +
            fixedProjectedTrueRemainderIntegrand c b x) := by
      apply intervalIntegral.integral_congr
      intro x hx
      apply fixedProjectedDual_pointwise_decomposition
      simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hx
    _ = _ := intervalIntegral.integral_add hbase hrem

/-- The transformed rational weight bounds the true bounded-remainder
integral from above; the open-interval theorem handles the null endpoints. -/
theorem fixedProjectedTrueRemainder_integral_le_atanh
    (c b : ℝ)
    (htrue : IntervalIntegrable
      (fixedProjectedTrueRemainderIntegrand c b) volume (-1) 1)
    (hatanh : IntervalIntegrable
      (fixedProjectedAtanhRemainderIntegrand c b) volume (-1) 1) :
    (∫ x : ℝ in -1..1,
      fixedProjectedTrueRemainderIntegrand c b x) ≤
        ∫ x : ℝ in -1..1,
          fixedProjectedAtanhRemainderIntegrand c b x := by
  apply intervalIntegral.integral_mono_on_of_le_Ioo
    (by norm_num : (-1 : ℝ) ≤ 1) htrue hatanh
  intro x hx
  unfold fixedProjectedTrueRemainderIntegrand
    fixedProjectedAtanhRemainderIntegrand
  exact sq_div_tailWeight_le_sq_div_atanhTailWeight
    (fixedProjectedShiftedRemainder c b x) hx

/-- The remaining make-or-break statement is now only an upper bound for the
rationally weighted bounded remainder.  Any such bound immediately gives the
projected dual inequality against the exact clean low quadratic. -/
theorem fixedProjectedDual_integral_le_clean_of_atanh_remainder
    (c b : ℝ)
    (hbase : IntervalIntegrable
      (fixedProjectedDualBaseIntegrand c b) volume (-1) 1)
    (htrue : IntervalIntegrable
      (fixedProjectedTrueRemainderIntegrand c b) volume (-1) 1)
    (hatanh : IntervalIntegrable
      (fixedProjectedAtanhRemainderIntegrand c b) volume (-1) 1)
    (hbound :
      (∫ x : ℝ in -1..1,
          fixedProjectedAtanhRemainderIntegrand c b x) ≤
        yoshidaEndpointOddCleanQuadratic
            (fun x ↦ fixedEvenLowProfile c b x) -
          ∫ x : ℝ in -1..1,
            fixedProjectedDualBaseIntegrand c b x) :
    (∫ x : ℝ in -1..1, fixedProjectedDualIntegrand c b x) ≤
      yoshidaEndpointOddCleanQuadratic
        (fun x ↦ fixedEvenLowProfile c b x) := by
  rw [fixedProjectedDual_integral_decomposition c b hbase htrue]
  have hrem := fixedProjectedTrueRemainder_integral_le_atanh
    c b htrue hatanh
  linarith

end

end ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedDualIntegral

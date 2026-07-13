import ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedGapMoments
import ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedRemainderMoments

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedMatrixClosure

open TwoByTwoSchur
open YoshidaEndpointEvenAtanhReciprocalMajorant
open YoshidaEndpointEvenProjectedDualExactLow
open YoshidaEndpointEvenProjectedDualIdentity
open YoshidaEndpointEvenProjectedDualIntegral
open YoshidaEndpointEvenProjectedGapMoments
open YoshidaEndpointEvenProjectedRemainderMajorant
open YoshidaEndpointEvenProjectedRemainderMoments
open YoshidaEndpointEvenTailRepresenter

noncomputable section

/-- Strict positive definiteness of the exact gap minus polynomial-remainder
Gram gives the universal fixed-moment inequality. -/
theorem polynomialRemainder_integral_le_exactGap_of_matrix_pos
    (c b : ℝ)
    (hr00 : IntervalIntegrable
      (fun x ↦ atanhTailWeightReciprocalMajorant x *
        fixedProjectedShiftedRemainder0 x ^ 2) volume (-1) 1)
    (hr02 : IntervalIntegrable
      (fun x ↦ atanhTailWeightReciprocalMajorant x *
        fixedProjectedShiftedRemainder0 x *
          fixedProjectedShiftedRemainder2 x) volume (-1) 1)
    (hr22 : IntervalIntegrable
      (fun x ↦ atanhTailWeightReciprocalMajorant x *
        fixedProjectedShiftedRemainder2 x ^ 2) volume (-1) 1)
    (hb00 : IntervalIntegrable
      (fixedProjectedDualBaseIntegrand 1 0) volume (-1) 1)
    (hb02 : IntervalIntegrable
      fixedProjectedDualBaseCrossIntegrand volume (-1) 1)
    (hb22 : IntervalIntegrable
      (fixedProjectedDualBaseIntegrand 0 1) volume (-1) 1)
    (h00 : 0 < fixedProjectedGapGram00 -
      fixedProjectedPolynomialRemainderGram00)
    (hdet : 0 <
      (fixedProjectedGapGram00 - fixedProjectedPolynomialRemainderGram00) *
          (fixedProjectedGapGram22 - fixedProjectedPolynomialRemainderGram22) -
        (fixedProjectedGapGram02 -
          fixedProjectedPolynomialRemainderGram02) ^ 2) :
    (∫ x : ℝ in -1..1,
        fixedProjectedPolynomialRemainderIntegrand c b x) ≤
      (yoshidaEndpointEvenLowGram00 * c ^ 2 +
          2 * yoshidaEndpointEvenLowGram02 * c * b +
          yoshidaEndpointEvenLowGram22 * b ^ 2) -
        ∫ x : ℝ in -1..1,
          fixedProjectedDualBaseIntegrand c b x := by
  rw [integral_fixedProjectedPolynomialRemainder_eq_gram
      c b hr00 hr02 hr22,
    exactLowGram_sub_baseIntegral_eq_gapGram
      c b hb00 hb02 hb22]
  have hquad := quadratic_add_tail_nonneg
    (fixedProjectedGapGram00 - fixedProjectedPolynomialRemainderGram00)
    (fixedProjectedGapGram02 - fixedProjectedPolynomialRemainderGram02)
    (fixedProjectedGapGram22 - fixedProjectedPolynomialRemainderGram22)
    0 0 0 c b h00 hdet (by norm_num)
  norm_num at hquad
  linarith

/-- The same two principal-minor inequalities discharge the literal exact-low
weighted-dual theorem. -/
theorem fixedProjectedWeightedDual_le_exactLowGram_of_matrix_pos
    (c b : ℝ)
    (hr00 : IntervalIntegrable
      (fun x ↦ atanhTailWeightReciprocalMajorant x *
        fixedProjectedShiftedRemainder0 x ^ 2) volume (-1) 1)
    (hr02 : IntervalIntegrable
      (fun x ↦ atanhTailWeightReciprocalMajorant x *
        fixedProjectedShiftedRemainder0 x *
          fixedProjectedShiftedRemainder2 x) volume (-1) 1)
    (hr22 : IntervalIntegrable
      (fun x ↦ atanhTailWeightReciprocalMajorant x *
        fixedProjectedShiftedRemainder2 x ^ 2) volume (-1) 1)
    (hb00 : IntervalIntegrable
      (fixedProjectedDualBaseIntegrand 1 0) volume (-1) 1)
    (hb02 : IntervalIntegrable
      fixedProjectedDualBaseCrossIntegrand volume (-1) 1)
    (hb22 : IntervalIntegrable
      (fixedProjectedDualBaseIntegrand 0 1) volume (-1) 1)
    (htrue : IntervalIntegrable
      (fixedProjectedTrueRemainderIntegrand c b) volume (-1) 1)
    (hatanh : IntervalIntegrable
      (fixedProjectedAtanhRemainderIntegrand c b) volume (-1) 1)
    (h00 : 0 < fixedProjectedGapGram00 -
      fixedProjectedPolynomialRemainderGram00)
    (hdet : 0 <
      (fixedProjectedGapGram00 - fixedProjectedPolynomialRemainderGram00) *
          (fixedProjectedGapGram22 - fixedProjectedPolynomialRemainderGram22) -
        (fixedProjectedGapGram02 -
          fixedProjectedPolynomialRemainderGram02) ^ 2) :
    (∫ x : ℝ in -1..1,
      (c * fixedProjectedTailRepresenter0 x +
        b * fixedProjectedTailRepresenter2 x) ^ 2 /
          yoshidaEndpointEvenTailWeight x) ≤
      yoshidaEndpointEvenLowGram00 * c ^ 2 +
        2 * yoshidaEndpointEvenLowGram02 * c * b +
        yoshidaEndpointEvenLowGram22 * b ^ 2 := by
  have hbase : IntervalIntegrable
      (fixedProjectedDualBaseIntegrand c b) volume (-1) 1 := by
    apply ((hb00.const_mul (c ^ 2)).add
      ((hb02.const_mul (2 * c * b)).add (hb22.const_mul (b ^ 2)))).congr
    intro x _hx
    rw [fixedProjectedDualBaseIntegrand_eq_gram]
    ring
  have hpoly : IntervalIntegrable
      (fixedProjectedPolynomialRemainderIntegrand c b) volume (-1) 1 := by
    apply ((hr00.const_mul (c ^ 2)).add
      ((hr02.const_mul (2 * c * b)).add (hr22.const_mul (b ^ 2)))).congr
    intro x _hx
    rw [fixedProjectedPolynomialRemainderIntegrand_eq_gram]
    ring
  have hbound := polynomialRemainder_integral_le_exactGap_of_matrix_pos
    c b hr00 hr02 hr22 hb00 hb02 hb22 h00 hdet
  exact fixedProjectedWeightedDual_le_exactLowGram_of_polynomial_remainder
    c b hbase htrue hatanh hpoly hbound

end

end ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedMatrixClosure

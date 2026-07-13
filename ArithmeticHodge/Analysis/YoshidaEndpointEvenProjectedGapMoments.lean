import ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedDualExactLow

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedGapMoments

open YoshidaEndpointEvenProjectedDualIdentity
open YoshidaEndpointEvenProjectedDualIntegral
open YoshidaEndpointEvenTailRepresenter

noncomputable section

/-- Mixed coefficient of the pointwise extracted base quadratic, obtained by
exact polarization of its two fixed basis values. -/
def fixedProjectedDualBaseCrossIntegrand (x : ℝ) : ℝ :=
  (fixedProjectedDualBaseIntegrand 1 1 x -
      fixedProjectedDualBaseIntegrand 1 0 x -
      fixedProjectedDualBaseIntegrand 0 1 x) / 2

theorem fixedProjectedDualBaseIntegrand_eq_gram (c b x : ℝ) :
    fixedProjectedDualBaseIntegrand c b x =
      c ^ 2 * fixedProjectedDualBaseIntegrand 1 0 x +
        2 * c * b * fixedProjectedDualBaseCrossIntegrand x +
        b ^ 2 * fixedProjectedDualBaseIntegrand 0 1 x := by
  unfold fixedProjectedDualBaseCrossIntegrand
    fixedProjectedDualBaseIntegrand fixedEvenLowProfile
    fixedProjectedBoundedRemainder fixedProjectionPolynomial
  ring

def fixedProjectedDualBaseGram00 : ℝ :=
  ∫ x : ℝ in -1..1, fixedProjectedDualBaseIntegrand 1 0 x

def fixedProjectedDualBaseGram02 : ℝ :=
  ∫ x : ℝ in -1..1, fixedProjectedDualBaseCrossIntegrand x

def fixedProjectedDualBaseGram22 : ℝ :=
  ∫ x : ℝ in -1..1, fixedProjectedDualBaseIntegrand 0 1 x

theorem integral_fixedProjectedDualBase_eq_gram
    (c b : ℝ)
    (h00 : IntervalIntegrable
      (fixedProjectedDualBaseIntegrand 1 0) volume (-1) 1)
    (h02 : IntervalIntegrable
      fixedProjectedDualBaseCrossIntegrand volume (-1) 1)
    (h22 : IntervalIntegrable
      (fixedProjectedDualBaseIntegrand 0 1) volume (-1) 1) :
    (∫ x : ℝ in -1..1, fixedProjectedDualBaseIntegrand c b x) =
      fixedProjectedDualBaseGram00 * c ^ 2 +
        2 * fixedProjectedDualBaseGram02 * c * b +
        fixedProjectedDualBaseGram22 * b ^ 2 := by
  rw [show (fun x : ℝ ↦ fixedProjectedDualBaseIntegrand c b x) =
      fun x ↦ c ^ 2 * fixedProjectedDualBaseIntegrand 1 0 x +
        ((2 * c * b) * fixedProjectedDualBaseCrossIntegrand x +
          b ^ 2 * fixedProjectedDualBaseIntegrand 0 1 x) by
    funext x
    rw [fixedProjectedDualBaseIntegrand_eq_gram]
    ring,
    intervalIntegral.integral_add (h00.const_mul (c ^ 2))
      ((h02.const_mul (2 * c * b)).add (h22.const_mul (b ^ 2))),
    intervalIntegral.integral_add (h02.const_mul (2 * c * b))
      (h22.const_mul (b ^ 2)),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  unfold fixedProjectedDualBaseGram00 fixedProjectedDualBaseGram02
    fixedProjectedDualBaseGram22
  ring

def fixedProjectedGapGram00 : ℝ :=
  yoshidaEndpointEvenLowGram00 - fixedProjectedDualBaseGram00

def fixedProjectedGapGram02 : ℝ :=
  yoshidaEndpointEvenLowGram02 - fixedProjectedDualBaseGram02

def fixedProjectedGapGram22 : ℝ :=
  yoshidaEndpointEvenLowGram22 - fixedProjectedDualBaseGram22

/-- Exact low Gram minus the extracted base integral is itself the fixed gap
Gram. -/
theorem exactLowGram_sub_baseIntegral_eq_gapGram
    (c b : ℝ)
    (h00 : IntervalIntegrable
      (fixedProjectedDualBaseIntegrand 1 0) volume (-1) 1)
    (h02 : IntervalIntegrable
      fixedProjectedDualBaseCrossIntegrand volume (-1) 1)
    (h22 : IntervalIntegrable
      (fixedProjectedDualBaseIntegrand 0 1) volume (-1) 1) :
    (yoshidaEndpointEvenLowGram00 * c ^ 2 +
          2 * yoshidaEndpointEvenLowGram02 * c * b +
          yoshidaEndpointEvenLowGram22 * b ^ 2) -
        (∫ x : ℝ in -1..1, fixedProjectedDualBaseIntegrand c b x) =
      fixedProjectedGapGram00 * c ^ 2 +
        2 * fixedProjectedGapGram02 * c * b +
        fixedProjectedGapGram22 * b ^ 2 := by
  rw [integral_fixedProjectedDualBase_eq_gram c b h00 h02 h22]
  unfold fixedProjectedGapGram00 fixedProjectedGapGram02
    fixedProjectedGapGram22
  ring

end

end ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedGapMoments

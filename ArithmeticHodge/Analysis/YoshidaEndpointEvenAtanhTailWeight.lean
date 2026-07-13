import ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedDualIdentity
import ArithmeticHodge.Analysis.YoshidaEndpointPotentialAtanhLower

set_option autoImplicit false

open Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointEvenAtanhTailWeight

open YoshidaEndpointEvenProjectedDualIdentity
open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointPotentialAtanhLower
open YoshidaEndpointPotentialBound

noncomputable section

/-- Rational transformed-series weight below the true endpoint tail weight on
the open interval. -/
def yoshidaEndpointEvenAtanhTailWeight (x : ℝ) : ℝ :=
  (41 / 60 : ℝ) + yoshidaEndpointPotentialAtanhTwoTerm x

theorem yoshidaEndpointEvenAtanhTailWeight_pos_on_Icc
    {x : ℝ} (hx : x ∈ Icc (-1) 1) :
    0 < yoshidaEndpointEvenAtanhTailWeight x := by
  have hxAbs : |x| ≤ 1 := abs_le.mpr hx
  have hxSq : x ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one x).2 hxAbs
  have hden : 0 < 2 - x ^ 2 := by linarith
  have ht : 0 ≤ x ^ 2 / (2 - x ^ 2) :=
    div_nonneg (sq_nonneg x) hden.le
  have htCube : 0 ≤ (x ^ 2 / (2 - x ^ 2)) ^ 3 := by positivity
  unfold yoshidaEndpointEvenAtanhTailWeight
    yoshidaEndpointPotentialAtanhTwoTerm
  dsimp only
  linarith

/-- The transformed two-term weight is below the true logarithmic weight at
every interior point.  Endpoints are excluded because `Real.log 0 = 0`; they
are null for all subsequent interval integrals. -/
theorem atanhTailWeight_le_tailWeight
    {x : ℝ} (hx : x ∈ Ioo (-1) 1) :
    yoshidaEndpointEvenAtanhTailWeight x ≤
      yoshidaEndpointEvenTailWeight x := by
  have hxAbs : |x| < 1 := abs_lt.mpr hx
  have hV := atanhTwoTerm_le_yoshidaEndpointPotential hxAbs
  unfold yoshidaEndpointEvenAtanhTailWeight yoshidaEndpointEvenTailWeight
  linarith

/-- Replacing the true tail weight by the smaller transformed-series weight
gives a structural upper bound for every square quotient. -/
theorem sq_div_tailWeight_le_sq_div_atanhTailWeight
    (h : ℝ) {x : ℝ} (hx : x ∈ Ioo (-1) 1) :
    h ^ 2 / yoshidaEndpointEvenTailWeight x ≤
      h ^ 2 / yoshidaEndpointEvenAtanhTailWeight x := by
  have hIcc : x ∈ Icc (-1) 1 := ⟨hx.1.le, hx.2.le⟩
  have hD := yoshidaEndpointEvenAtanhTailWeight_pos_on_Icc hIcc
  have hW := yoshidaEndpointEvenTailWeight_pos_on_Icc hIcc
  have hle := atanhTailWeight_le_tailWeight hx
  rw [div_le_div_iff₀ hW hD]
  exact mul_le_mul_of_nonneg_left hle (sq_nonneg h)

end

end ArithmeticHodge.Analysis.YoshidaEndpointEvenAtanhTailWeight

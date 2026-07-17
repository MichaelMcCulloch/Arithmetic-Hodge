import ArithmeticHodge.Analysis.ThreeByThreePositiveMixedDeterminant
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorStructural

set_option autoImplicit false

open Matrix

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorSOSStructural

open ThreeByThreePositiveMixedDeterminant
open ThreeByThreeRankOneSchur

noncomputable section

/-!
# A rational interval reserve for the retained `P₀/P₂/P₄` selector pencil

The boundary gap is a quadratic matrix polynomial in the symmetric phase.
Its matrix-SOS certificate uses the following fixed rational reserve.  The
reserve is proved positive by exact Sylvester pivots; no decimal approximation
enters the theorem.
-/

/-- Rational reserve selected for the affine-lift matrix-SOS decomposition of
the sharp retained selector gap. -/
def retainedP024SelectorSOSReserve : Matrix (Fin 3) (Fin 3) ℝ :=
  symmetricMatrix3
    (1661 / 10000 : ℝ) (1535 / 10000 : ℝ) (-67 / 10000 : ℝ)
    (1492 / 10000 : ℝ) (262 / 10000 : ℝ) (1470 / 10000 : ℝ)

/-- The rational SOS reserve is strictly positive definite. -/
theorem retainedP024SelectorSOSReserve_posDef :
    retainedP024SelectorSOSReserve.PosDef := by
  unfold retainedP024SelectorSOSReserve
  apply symmetricMatrix3_posDef
  · norm_num
  · unfold leadingMinorTwo
    norm_num
  · unfold symmetricDeterminant
    norm_num

/-- Semidefinite form used directly by the interval matrix-SOS theorem. -/
theorem retainedP024SelectorSOSReserve_posSemidef :
    retainedP024SelectorSOSReserve.PosSemidef :=
  retainedP024SelectorSOSReserve_posDef.posSemidef

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorSOSStructural

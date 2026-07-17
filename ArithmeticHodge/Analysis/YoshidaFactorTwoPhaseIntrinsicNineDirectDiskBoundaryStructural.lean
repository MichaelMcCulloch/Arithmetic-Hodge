import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseDiskBoundaryStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectMatrixStructural

set_option autoImplicit false

open Matrix

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectDiskBoundaryStructural

noncomputable section

open YoshidaFactorTwoPhaseDiskBoundaryStructural
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseIntrinsicNineDirectMatrixStructural

/-!
# Boundary reduction for the direct cutoff-nine matrix

The direct balanced matrix depends affinely on the two phase coordinates.
Consequently its positive semidefiniteness on the unit circle implies the
same statement on the entire closed disk, without sampling the circle.
-/

theorem factorTwoIntrinsicNineDirectCoordinateQuadratic_affine_phase
    (a b : ℝ) (x : Fin 9 → ℝ) :
    factorTwoIntrinsicNineDirectCoordinateQuadratic a b x =
      factorTwoIntrinsicNineDirectCoordinateQuadratic 0 0 x +
        a * (factorTwoIntrinsicNineDirectCoordinateQuadratic 1 0 x -
          factorTwoIntrinsicNineDirectCoordinateQuadratic 0 0 x) +
        b * (factorTwoIntrinsicNineDirectCoordinateQuadratic 0 1 x -
          factorTwoIntrinsicNineDirectCoordinateQuadratic 0 0 x) := by
  unfold factorTwoIntrinsicNineDirectCoordinateQuadratic
  repeat' rw [factorTwoIntrinsicNineDirectLowQuadratic_eq_phase_sub_reserve]
  unfold factorTwoEndpointChannelPhase
  ring

/-- It is enough to prove positive semidefiniteness of the direct matrix on
the phase circle. -/
theorem factorTwoIntrinsicNineDirectLowMatrix_posSemidef_of_unitCircle
    (hcircle : ∀ a b : ℝ, a ^ 2 + b ^ 2 = 1 →
      (factorTwoIntrinsicNineDirectLowMatrix a b).PosSemidef)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    (factorTwoIntrinsicNineDirectLowMatrix a b).PosSemidef := by
  apply factorTwoIntrinsicNineDirectLowMatrix_posSemidef_of_nonneg
  intro x
  rw [factorTwoIntrinsicNineDirectCoordinateQuadratic_affine_phase]
  apply real_closedDisk_phase_nonneg_of_unitCircle
  intro s t hst
  rw [← factorTwoIntrinsicNineDirectCoordinateQuadratic_affine_phase]
  have hx := (hcircle s t hst).dotProduct_mulVec_nonneg x
  simp only [star_trivial] at hx
  rwa [factorTwoIntrinsicNineDirectLowMatrix_quadratic] at hx
  exact hab

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectDiskBoundaryStructural

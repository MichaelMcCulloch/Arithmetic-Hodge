import ArithmeticHodge.Analysis.YoshidaFourCellOddP11ConcreteWeightedDualClosureStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP11WeightedDualSelectorStructural

noncomputable section

open CenteredOddOneThreeEnergy
open YoshidaEndpointOcticPotential
open YoshidaFourCellOddP11ConcreteWeightedDualClosureStructural
open YoshidaFourCellOddP11CoupledRieszClosureStructural
open YoshidaFourCellOddP11CoupledRieszDefectClosureStructural
open YoshidaFourCellOddP11FormDualProbeStructural
open YoshidaFourCellOddP1OrthogonalFormDualClosureStructural
open YoshidaFourCellOddStripCapacityClosureStructural

/-!
# Joint weighted dual for the odd `P₁₁+` selector

The previous weighted-dual interface allocates a scalar `D₀` independently
between the pure `P₁` tail row and the corrected finite--tail row.  That
forgets their correlation.  The invariant actually needed by the corrected
determinant is the single joint inequality

`F * x² + X² ≤ F * A * W`,

where `F = A*C-b²` and `X = A*y-b*x`.  This is the inverse-free `2 × 2`
Loewner condition for the two selector rows.  It is strictly weaker than a
diagonal `D₀` allocation and feeds the production corrected determinant
directly.
-/

/-- Direct joint weighted-dual closure of the corrected determinant.  The
first row keeps the pure tail pivot nonnegative; the second row is the exact
two-row Loewner inequality, with no independent allocation of its two
summands. -/
theorem coupledP1TailSchurDefect_nonneg_of_jointWeightedDual
    {A b C x y z W : ℝ}
    (hA : 0 ≤ A)
    (hfinite : 0 ≤ A * C - b ^ 2)
    (hWz : W ≤ z)
    (hpure : x ^ 2 ≤ A * W)
    (hjoint :
      (A * C - b ^ 2) * x ^ 2 + (A * y - b * x) ^ 2 ≤
        (A * C - b ^ 2) * A * W) :
    0 ≤ coupledP1TailSchurDefect A b C x y z := by
  let F := A * C - b ^ 2
  let X := A * y - b * x
  let T := A * z - x ^ 2
  have hAW : A * W ≤ A * z := mul_le_mul_of_nonneg_left hWz hA
  have htail : 0 ≤ T := by
    dsimp only [T]
    linarith [hpure.trans hAW]
  have hFW : F * A * W ≤ F * (A * z) := by
    have := mul_le_mul_of_nonneg_left hAW hfinite
    simpa only [F, mul_assoc] using this
  have hcross : X ^ 2 ≤ F * T := by
    dsimp only [F, X, T] at hjoint hFW ⊢
    nlinarith
  exact coupledP1TailSchurDefect_nonneg_of_correctedCross
    hfinite htail hcross

/-- Algebraic equivalence between the joint two-row energy and its
inverse-free Loewner formulation.  The reverse implication tests the
Loewner inequality at the output vector `(x,X)` itself, so there is no
dimension-two trace loss. -/
theorem jointWeightedDual_iff_twoRowLoewner
    {A F W x X : ℝ} (hA : 0 ≤ A) (hF : 0 ≤ F) (hW : 0 ≤ W) :
    F * x ^ 2 + X ^ 2 ≤ F * A * W ↔
      ∀ s t : ℝ,
        (F * s * x + t * X) ^ 2 ≤
          F * A * (F * s ^ 2 + t ^ 2) * W := by
  constructor
  · intro hjoint s t
    have hcoeff : 0 ≤ F * s ^ 2 + t ^ 2 := by positivity
    have hcauchy :
        (F * s * x + t * X) ^ 2 ≤
          (F * s ^ 2 + t ^ 2) * (F * x ^ 2 + X ^ 2) := by
      nlinarith [mul_nonneg hF (sq_nonneg (s * X - t * x))]
    have hmul := mul_le_mul_of_nonneg_left hjoint hcoeff
    calc
      (F * s * x + t * X) ^ 2 ≤
          (F * s ^ 2 + t ^ 2) * (F * x ^ 2 + X ^ 2) := hcauchy
      _ ≤ (F * s ^ 2 + t ^ 2) * (F * A * W) := hmul
      _ = F * A * (F * s ^ 2 + t ^ 2) * W := by ring
  · intro hloewner
    let S := F * x ^ 2 + X ^ 2
    have hS : 0 ≤ S := by dsimp only [S]; positivity
    have hK : 0 ≤ F * A * W := by positivity
    have htest := hloewner x X
    have hsq : S ^ 2 ≤ (F * A * W) * S := by
      dsimp only [S]
      convert htest using 1 <;> ring
    by_cases hS0 : S = 0
    · change S ≤ F * A * W
      rw [hS0]
      exact hK
    · have hSpos : 0 < S := lt_of_le_of_ne hS (Ne.symm hS0)
      nlinarith

/-- Correlation-preserving replacement for
`FourCellOddP11CoupledWeightedDualCertificate`.  Its second inequality is a
single quadratic inequality for the two selector rows, rather than two
independent norm allocations. -/
def FourCellOddP11CoupledJointWeightedDualCertificate : Prop :=
  ∀ (d e f g : ℝ) (r : ℝ → ℝ),
    ContDiff ℝ 1 r → Function.Odd r →
    centeredOddP1Coefficient r = 0 →
    centeredOddP3Coefficient r = 0 →
    centeredOddP5Coefficient r = 0 →
    centeredOddP7Coefficient r = 0 →
    centeredOddP9Coefficient r = 0 →
    fourCellOddCoreLocalBilinear centeredP1 r ^ 2 ≤
        fourCellOddCoreLocalQuadratic centeredP1 *
          fourCellOddP1ExactTailWeight r ∧
      fourCellOddP11FiniteCorrectedReserve d e f g *
            fourCellOddCoreLocalBilinear centeredP1 r ^ 2 +
          fourCellOddP11FiniteTailCorrectedCross d e f g r ^ 2 ≤
        fourCellOddP11FiniteCorrectedReserve d e f g *
          fourCellOddCoreLocalQuadratic centeredP1 *
            fourCellOddP1ExactTailWeight r

/-- The selector-facing version of the joint certificate.  For every finite
profile and tail, the two output rows define a contraction from the weighted
tail space to the two-dimensional metric `diag(F,1)`.  This is the exact
`2 × 2` Loewner inequality a pair of degree-`< 11` selectors must prove. -/
def FourCellOddP11CoupledSelectorLoewnerCertificate : Prop :=
  ∀ (d e f g : ℝ) (r : ℝ → ℝ),
    ContDiff ℝ 1 r → Function.Odd r →
    centeredOddP1Coefficient r = 0 →
    centeredOddP3Coefficient r = 0 →
    centeredOddP5Coefficient r = 0 →
    centeredOddP7Coefficient r = 0 →
    centeredOddP9Coefficient r = 0 →
    fourCellOddCoreLocalBilinear centeredP1 r ^ 2 ≤
        fourCellOddCoreLocalQuadratic centeredP1 *
          fourCellOddP1ExactTailWeight r ∧
      ∀ s t : ℝ,
        (fourCellOddP11FiniteCorrectedReserve d e f g * s *
              fourCellOddCoreLocalBilinear centeredP1 r +
            t * fourCellOddP11FiniteTailCorrectedCross d e f g r) ^ 2 ≤
          fourCellOddP11FiniteCorrectedReserve d e f g *
            fourCellOddCoreLocalQuadratic centeredP1 *
              (fourCellOddP11FiniteCorrectedReserve d e f g * s ^ 2 +
                t ^ 2) * fourCellOddP1ExactTailWeight r

/-- The joint-energy and two-row Loewner interfaces are exactly equivalent.
The finite corrected reserve is already nonnegative unconditionally. -/
theorem fourCellOddP11CoupledSelectorLoewnerCertificate_iff_joint :
    FourCellOddP11CoupledSelectorLoewnerCertificate ↔
      FourCellOddP11CoupledJointWeightedDualCertificate := by
  constructor
  · intro hloewner d e f g r hr hrodd hr1 hr3 hr5 hr7 hr9
    rcases hloewner d e f g r hr hrodd hr1 hr3 hr5 hr7 hr9 with
      ⟨hpure, hloewner⟩
    constructor
    · exact hpure
    · apply (jointWeightedDual_iff_twoRowLoewner
        (A := fourCellOddCoreLocalQuadratic centeredP1)
        (F := fourCellOddP11FiniteCorrectedReserve d e f g)
        (W := fourCellOddP1ExactTailWeight r)
        (x := fourCellOddCoreLocalBilinear centeredP1 r)
        (X := fourCellOddP11FiniteTailCorrectedCross d e f g r)
        fourCellOddCoreLocalQuadratic_centeredP1_nonneg
        (fourCellOddP11FiniteCorrectedReserve_nonnegative d e f g)
        (fourCellOddP1ExactTailWeight_nonneg r hr.continuous)).2
      exact hloewner
  · intro hjoint d e f g r hr hrodd hr1 hr3 hr5 hr7 hr9
    rcases hjoint d e f g r hr hrodd hr1 hr3 hr5 hr7 hr9 with
      ⟨hpure, hjoint⟩
    constructor
    · exact hpure
    · apply (jointWeightedDual_iff_twoRowLoewner
        (A := fourCellOddCoreLocalQuadratic centeredP1)
        (F := fourCellOddP11FiniteCorrectedReserve d e f g)
        (W := fourCellOddP1ExactTailWeight r)
        (x := fourCellOddCoreLocalBilinear centeredP1 r)
        (X := fourCellOddP11FiniteTailCorrectedCross d e f g r)
        fourCellOddCoreLocalQuadratic_centeredP1_nonneg
        (fourCellOddP11FiniteCorrectedReserve_nonnegative d e f g)
        (fourCellOddP1ExactTailWeight_nonneg r hr.continuous)).1
      exact hjoint

/-- The old diagonal allocation implies the joint certificate.  The reverse
direction is intentionally not asserted: the joint condition retains the
off-diagonal correlation discarded by `D₀`. -/
theorem fourCellOddP11CoupledJointWeightedDualCertificate_of_diagonal
    (hdual : FourCellOddP11CoupledWeightedDualCertificate) :
    FourCellOddP11CoupledJointWeightedDualCertificate := by
  rcases hdual with ⟨D₀, hD₀, hdual⟩
  intro d e f g r hr hrodd hr1 hr3 hr5 hr7 hr9
  rcases hdual d e f g r hr hrodd hr1 hr3 hr5 hr7 hr9 with
    ⟨hpure, hcross⟩
  let A := fourCellOddCoreLocalQuadratic centeredP1
  let F := fourCellOddP11FiniteCorrectedReserve d e f g
  let W := fourCellOddP1ExactTailWeight r
  let x := fourCellOddCoreLocalBilinear centeredP1 r
  let X := fourCellOddP11FiniteTailCorrectedCross d e f g r
  have hF : 0 ≤ F := by
    dsimp only [F]
    exact fourCellOddP11FiniteCorrectedReserve_nonnegative d e f g
  have hW : 0 ≤ W := by
    dsimp only [W]
    exact fourCellOddP1ExactTailWeight_nonneg r hr.continuous
  have hFD : F * D₀ * W ≤ F * A * W := by
    have hmul := mul_le_mul_of_nonneg_left hD₀ hF
    exact mul_le_mul_of_nonneg_right hmul hW
  have hpureA : x ^ 2 ≤ A * W := by
    dsimp only [x, A, W] at hpure ⊢
    exact hpure.trans (mul_le_mul_of_nonneg_right hD₀ hW)
  constructor
  · exact hpureA
  · dsimp only [F, W, x, X, A] at hpure hcross hFD ⊢
    nlinarith

/-- The joint selector inequality closes the actual universal corrected
`P₁₁+` defect without passing through the stronger diagonal allocation. -/
theorem fourCellOddP11CoupledRieszDefectNonnegative_of_jointWeightedDual
    (hjoint : FourCellOddP11CoupledJointWeightedDualCertificate) :
    FourCellOddP11CoupledRieszDefectNonnegative := by
  intro d e f g r hr hrodd hr1 hr3 hr5 hr7 hr9
  let p := fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g
  let A := fourCellOddCoreLocalQuadratic centeredP1
  let b := fourCellOddCoreLocalBilinear centeredP1 p
  let C := fourCellOddCoreLocalQuadratic p
  let x := fourCellOddCoreLocalBilinear centeredP1 r
  let y := fourCellOddCoreLocalBilinear p r
  let z := fourCellOddCoreLocalQuadratic r
  let W := fourCellOddP1ExactTailWeight r
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact fourCellOddCoreLocalQuadratic_centeredP1_nonneg
  have hF : 0 ≤ A * C - b ^ 2 := by
    simpa only [A, b, C, p, fourCellOddP11FiniteCorrectedReserve] using
      fourCellOddP11FiniteCorrectedReserve_nonnegative d e f g
  have hWz : W ≤ z := by
    dsimp only [W, z]
    exact fourCellOddP1ExactTailWeight_le_core r hr hrodd hr1
  rcases hjoint d e f g r hr hrodd hr1 hr3 hr5 hr7 hr9 with
    ⟨hpure, hcoupled⟩
  have h := coupledP1TailSchurDefect_nonneg_of_jointWeightedDual
    (A := A) (b := b) (C := C) (x := x) (y := y) (z := z) (W := W)
    hA hF hWz
    (by simpa only [A, x, W] using hpure)
    (by simpa only [A, b, C, x, y, W, p,
        fourCellOddP11FiniteCorrectedReserve,
        fourCellOddP11FiniteTailCorrectedCross] using hcoupled)
  simpa only [fourCellOddP11CoupledRieszDefect, p, A, b, C, x, y, z]
    using h

/-- Final selector-facing handoff to the production corrected defect. -/
theorem fourCellOddP11CoupledRieszDefectNonnegative_of_selectorLoewner
    (hselector : FourCellOddP11CoupledSelectorLoewnerCertificate) :
    FourCellOddP11CoupledRieszDefectNonnegative :=
  fourCellOddP11CoupledRieszDefectNonnegative_of_jointWeightedDual
    (fourCellOddP11CoupledSelectorLoewnerCertificate_iff_joint.mp hselector)

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP11WeightedDualSelectorStructural

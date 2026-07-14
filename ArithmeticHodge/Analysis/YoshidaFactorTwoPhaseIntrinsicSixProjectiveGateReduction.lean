import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveSchur

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveGateReduction

noncomputable section

open ThreeByThreeRankOneSchur
open YoshidaFactorTwoPhaseDiskSchur
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseIntrinsicFourP45MixedExpansion
open YoshidaFactorTwoPhaseIntrinsicSixP4Schur
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveSchur
open YoshidaFactorTwoPhaseIntrinsicSixSchurReduction
open YoshidaFactorTwoPhaseLowSchur

/-!
# Sign-free projective gates for the intrinsic six-mode block

The rational phase coordinate has `x = t^2`.  Although the projective base
matrix contains entries linear in `t`, its two principal minors and the final
adjugate quadratic contain only paired occurrences of `t`.  This file writes
those three gates directly in `x`, proves the exact identities, and packages
the existing projective closure with no choice of sign for `t` left in its
hypotheses.
-/

/-! ## Exact `x`-only gates -/

/-- The second leading principal minor after replacing `t^2` by `x`. -/
def factorTwoIntrinsicSixProjectiveBaseMinorTwoX (x : ℝ) : ℝ :=
  factorTwoIntrinsicSixProjectiveP4Pivot x *
      factorTwoIntrinsicSixProjectiveOddResidual x 0 0 -
    x * factorTwoIntrinsicSixProjectiveP4OddCross x 0 ^ 2

/-- The `3 x 3` base determinant, displayed as a scalar Schur determinant
in the lower odd `2 x 2` block. -/
def factorTwoIntrinsicSixProjectiveBaseDetX (x : ℝ) : ℝ :=
  factorTwoIntrinsicSixProjectiveP4Pivot x *
      (factorTwoIntrinsicSixProjectiveOddResidual x 0 0 *
          factorTwoIntrinsicSixProjectiveOddResidual x 1 1 -
        factorTwoIntrinsicSixProjectiveOddResidual x 0 1 ^ 2) -
    x * factorTwoIntrinsicSixAdjugateBilinear
      (factorTwoIntrinsicSixProjectiveOddResidual x 0 0)
      (factorTwoIntrinsicSixProjectiveOddResidual x 0 1)
      (factorTwoIntrinsicSixProjectiveOddResidual x 1 1)
      (factorTwoIntrinsicSixProjectiveP4OddCross x 0)
      (factorTwoIntrinsicSixProjectiveP4OddCross x 1)
      (factorTwoIntrinsicSixProjectiveP4OddCross x 0)
      (factorTwoIntrinsicSixProjectiveP4OddCross x 1)

/-- The final `P5` adjugate quadratic with every paired occurrence of `t`
replaced by `x`. -/
def factorTwoIntrinsicSixProjectiveP5AdjugateX (x : ℝ) : ℝ :=
  let A := factorTwoIntrinsicSixProjectiveP4Pivot x
  let B0 := factorTwoIntrinsicSixProjectiveP4OddCross x 0
  let B1 := factorTwoIntrinsicSixProjectiveP4OddCross x 1
  let B2 := factorTwoIntrinsicSixProjectiveP4OddCross x 2
  let R00 := factorTwoIntrinsicSixProjectiveOddResidual x 0 0
  let R01 := factorTwoIntrinsicSixProjectiveOddResidual x 0 1
  let R11 := factorTwoIntrinsicSixProjectiveOddResidual x 1 1
  let R02 := factorTwoIntrinsicSixProjectiveOddResidual x 0 2
  let R12 := factorTwoIntrinsicSixProjectiveOddResidual x 1 2
  x * (R00 * R11 - R01 ^ 2) * B2 ^ 2 +
    2 * x * (B1 * R01 - B0 * R11) * B2 * R02 +
    2 * x * (B0 * R01 - B1 * R00) * B2 * R12 +
    (A * R11 - x * B1 ^ 2) * R02 ^ 2 +
    2 * (x * B0 * B1 - A * R01) * R02 * R12 +
    (A * R00 - x * B0 ^ 2) * R12 ^ 2

/-- The four projective Schur conditions, now all functions of `x` alone. -/
def FactorTwoIntrinsicSixProjectiveXGates (x : ℝ) : Prop :=
  0 < factorTwoIntrinsicSixProjectiveP4Pivot x ∧
    0 < factorTwoIntrinsicSixProjectiveBaseMinorTwoX x ∧
    0 < factorTwoIntrinsicSixProjectiveBaseDetX x ∧
    factorTwoIntrinsicSixProjectiveP5AdjugateX x ≤
      factorTwoIntrinsicSixProjectiveBaseDetX x *
        factorTwoIntrinsicSixProjectiveP5DiagonalResidual x

/-- The original four projective Schur conditions before eliminating the
sign-bearing coordinate `t`. -/
def FactorTwoIntrinsicSixProjectiveGates (t x : ℝ) : Prop :=
  0 < factorTwoIntrinsicSixProjectiveP4Pivot x ∧
    0 < factorTwoIntrinsicSixProjectiveBaseMinorTwo t x ∧
    0 < factorTwoIntrinsicSixProjectiveBaseDet t x ∧
    factorTwoIntrinsicSixProjectiveP5Adjugate t x ≤
      factorTwoIntrinsicSixProjectiveBaseDet t x *
        factorTwoIntrinsicSixProjectiveP5DiagonalResidual x

/-! ## Elimination of the sign of `t` -/

theorem factorTwoIntrinsicSixProjectiveBaseMinorTwo_eq_x
    (t x : ℝ) (hx : x = t ^ 2) :
    factorTwoIntrinsicSixProjectiveBaseMinorTwo t x =
      factorTwoIntrinsicSixProjectiveBaseMinorTwoX x := by
  subst x
  unfold factorTwoIntrinsicSixProjectiveBaseMinorTwo
    factorTwoIntrinsicSixProjectiveBaseMinorTwoX leadingMinorTwo
  ring

theorem factorTwoIntrinsicSixProjectiveBaseDet_eq_x
    (t x : ℝ) (hx : x = t ^ 2) :
    factorTwoIntrinsicSixProjectiveBaseDet t x =
      factorTwoIntrinsicSixProjectiveBaseDetX x := by
  subst x
  unfold factorTwoIntrinsicSixProjectiveBaseDet
    factorTwoIntrinsicSixProjectiveBaseDetX symmetricDeterminant
    factorTwoIntrinsicSixAdjugateBilinear
  ring

theorem factorTwoIntrinsicSixProjectiveP5Adjugate_eq_x
    (t x : ℝ) (hx : x = t ^ 2) :
    factorTwoIntrinsicSixProjectiveP5Adjugate t x =
      factorTwoIntrinsicSixProjectiveP5AdjugateX x := by
  subst x
  unfold factorTwoIntrinsicSixProjectiveP5Adjugate
    factorTwoIntrinsicSixProjectiveP5AdjugateX adjugateQuadratic
  dsimp only
  ring

/-! ## The homogeneous first pivot -/

/-- The projective `P4` pivot is exactly the cubic homogenization of the
original phase-dependent `P0/P2/P4` determinant. -/
theorem factorTwoIntrinsicSixProjectiveP4Pivot_eq_homogeneous
    (x : ℝ) (hden : 1 + x ≠ 0) :
    factorTwoIntrinsicSixProjectiveP4Pivot x =
      (1 + x) ^ 3 * factorTwoIntrinsicSixP4SchurLeading
        ((1 - x) / (1 + x)) := by
  unfold factorTwoIntrinsicSixProjectiveP4Pivot
  change
    factorTwoIntrinsicSixProjectiveLowDet x *
          factorTwoIntrinsicSixProjectiveP4Diagonal x -
        factorTwoIntrinsicSixAdjugateBilinear
          (factorTwoIntrinsicSixProjectiveLow00 x)
          (factorTwoIntrinsicSixProjectiveLow02 x)
          (factorTwoIntrinsicSixProjectiveLow22 x)
          (factorTwoIntrinsicSixProjectiveCross04 x)
          (factorTwoIntrinsicSixProjectiveCross24 x)
          (factorTwoIntrinsicSixProjectiveCross04 x)
          (factorTwoIntrinsicSixProjectiveCross24 x) = _
  unfold factorTwoIntrinsicSixProjectiveLowDet
    factorTwoIntrinsicSixProjectiveLow00
    factorTwoIntrinsicSixProjectiveLow02
    factorTwoIntrinsicSixProjectiveLow22
    factorTwoIntrinsicSixProjectiveCross04
    factorTwoIntrinsicSixProjectiveCross24
    factorTwoIntrinsicSixProjectiveP4Diagonal
    factorTwoIntrinsicSixP4Diagonal
    factorTwoIntrinsicSixAdjugateBilinear
    factorTwoIntrinsicSixP4SchurLeading
    factorTwoIntrinsicSixLowDet
    factorTwoIntrinsicSixP4Low0
    factorTwoIntrinsicSixP4Low2
    factorTwoStructuralPhaseLow00
    factorTwoStructuralPhaseLow02
    factorTwoStructuralPhaseLow22
    factorTwoIntrinsicFourP45Cross04
    factorTwoIntrinsicFourP45Cross24
    factorTwoIntrinsicP4PhaseDiagonal
    factorTwoEndpointPhaseDiagonal
  field_simp [hden]
  ring

/-- On the projective half-line, strict positivity of the first projective
pivot is equivalent to strict positivity of the original `P0/P2/P4`
determinant at the corresponding phase coordinate. -/
theorem factorTwoIntrinsicSixProjectiveP4Pivot_pos_iff
    (x : ℝ) (hx : 0 ≤ x) :
    0 < factorTwoIntrinsicSixProjectiveP4Pivot x ↔
      0 < factorTwoIntrinsicSixP4SchurLeading
        ((1 - x) / (1 + x)) := by
  have hdenPos : 0 < 1 + x := by linarith
  rw [factorTwoIntrinsicSixProjectiveP4Pivot_eq_homogeneous
    x hdenPos.ne']
  have hfactor : 0 < (1 + x) ^ 3 := pow_pos hdenPos 3
  constructor
  · intro hproduct
    rcases (mul_pos_iff.mp hproduct) with hpos | hneg
    · exact hpos.2
    · exact (not_lt_of_ge hfactor.le hneg.1).elim
  · exact mul_pos hfactor

/-! ## Sign-free closure -/

/-- Under `x = t^2`, the original four projective gates are exactly the
`x`-only gates. -/
theorem factorTwoIntrinsicSixProjective_schur_gates_iff_x
    (t x : ℝ) (hx : x = t ^ 2) :
    FactorTwoIntrinsicSixProjectiveGates t x ↔
      FactorTwoIntrinsicSixProjectiveXGates x := by
  rw [FactorTwoIntrinsicSixProjectiveGates,
    FactorTwoIntrinsicSixProjectiveXGates,
    factorTwoIntrinsicSixProjectiveBaseMinorTwo_eq_x t x hx,
    factorTwoIntrinsicSixProjectiveBaseDet_eq_x t x hx,
    factorTwoIntrinsicSixProjectiveP5Adjugate_eq_x t x hx]

/-- Reversing the sign of the rational phase coordinate changes none of the
four projective Schur gates. -/
theorem factorTwoIntrinsicSixProjective_schur_gates_neg_iff
    (t x : ℝ) (hx : x = t ^ 2) :
    FactorTwoIntrinsicSixProjectiveGates (-t) x ↔
      FactorTwoIntrinsicSixProjectiveGates t x := by
  have hxneg : x = (-t) ^ 2 := by
    rw [hx]
    ring
  rw [factorTwoIntrinsicSixProjective_schur_gates_iff_x (-t) x hxneg,
    factorTwoIntrinsicSixProjective_schur_gates_iff_x t x hx]

/-- The complete intrinsic six-mode phase closure with hypotheses depending
only on the nonnegative projective coordinate `x`; the sign of `t` affects
the phase point but not any Schur gate. -/
theorem factorTwoEndpointChannelPhase_intrinsicSix_nonneg_of_projective_x_gates
    (c0 c2 c4 c1 c3 c5 t x : ℝ) (hx : x = t ^ 2)
    (hGates : FactorTwoIntrinsicSixProjectiveXGates x) :
    0 ≤ factorTwoEndpointChannelPhase
      (factorTwoEvenStructuralLowProfile c0 c2 +
        factorTwoIntrinsicSixEvenTail c4)
      (factorTwoIntrinsicSixOddTail c1 c3 c5)
      ((1 - x) / (1 + x)) (2 * t / (1 + x)) := by
  rcases hGates with ⟨h00, hminor, hdet, hfinal⟩
  apply factorTwoEndpointChannelPhase_intrinsicSix_nonneg_of_projective_schur
    c0 c2 c4 c1 c3 c5 t x hx h00
  · rwa [factorTwoIntrinsicSixProjectiveBaseMinorTwo_eq_x t x hx]
  · rwa [factorTwoIntrinsicSixProjectiveBaseDet_eq_x t x hx]
  · rwa [factorTwoIntrinsicSixProjectiveP5Adjugate_eq_x t x hx,
      factorTwoIntrinsicSixProjectiveBaseDet_eq_x t x hx]

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveGateReduction

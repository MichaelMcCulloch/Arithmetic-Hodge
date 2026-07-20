import ArithmeticHodge.Analysis.YoshidaFourCellOddStripCapacityClosureStructural

set_option autoImplicit false

open Real

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddCoreGroundStatePiconeStructural

noncomputable section

open YoshidaFourCellParityOperatorStructural
open YoshidaFourCellOddStripCapacityClosureStructural
open YoshidaRegularKernelBound

/-!
# Ground-state algebra for the complete odd four-cell core

This file isolates the exact pointwise algebra needed by a structural
ground-state proof.  It makes no positivity assumption about the unresolved
complete odd core.

There are two distinct facts.  First, both the same-sign and reflected raw
channels admit the same Picone remainder, so they can be transformed together
against one positive profile.  Second, the signed regular convolution has an
exact Dirichlet-minus-row decomposition.  The final lemmas record why a
*scalar* Stieltjes treatment of the complete kernel cannot simply absorb the
removed strip-odd raw energy: that term has a strictly positive reflected
off-diagonal polarization.
-/

/-! ## Pointwise two-channel Picone identities -/

/-- Picone's identity for a difference square, in the exact normalization
used by the same-sign raw channel. -/
theorem picone_sub_sq_identity
    {phiX phiY wX wY : ℝ} (hphiX : phiX ≠ 0) (hphiY : phiY ≠ 0) :
    (wX - wY) ^ 2 =
      phiX * phiY * (wX / phiX - wY / phiY) ^ 2 +
        (phiX - phiY) * (wX ^ 2 / phiX - wY ^ 2 / phiY) := by
  field_simp [hphiX, hphiY]
  ring

/-- The reflected (plus-square) raw channel has exactly the same Picone
remainder as the same-sign channel. -/
theorem picone_add_sq_identity
    {phiX phiY wX wY : ℝ} (hphiX : phiX ≠ 0) (hphiY : phiY ≠ 0) :
    (wX + wY) ^ 2 =
      phiX * phiY * (wX / phiX + wY / phiY) ^ 2 +
        (phiX - phiY) * (wX ^ 2 / phiX - wY ^ 2 / phiY) := by
  field_simp [hphiX, hphiY]
  ring

/-- Simultaneous Picone transform for arbitrary same-sign and reflected
kernel weights.  This is the pointwise identity whose symmetric integral
turns the last line into the ground-state row `L phi / phi`. -/
theorem picone_two_channel_identity
    {kSub kAdd phiX phiY wX wY : ℝ}
    (hphiX : phiX ≠ 0) (hphiY : phiY ≠ 0) :
    kSub * (wX - wY) ^ 2 + kAdd * (wX + wY) ^ 2 =
      phiX * phiY *
          (kSub * (wX / phiX - wY / phiY) ^ 2 +
            kAdd * (wX / phiX + wY / phiY) ^ 2) +
        (kSub + kAdd) * (phiX - phiY) *
          (wX ^ 2 / phiX - wY ^ 2 / phiY) := by
  rw [picone_sub_sq_identity hphiX hphiY,
    picone_add_sq_identity hphiX hphiY]
  ring

/-- Under the expected positive-profile and positive-kernel hypotheses, the
two quotient squares in the Picone transform are genuinely nonnegative. -/
theorem picone_two_channel_square_nonneg
    {kSub kAdd phiX phiY wX wY : ℝ}
    (hkSub : 0 ≤ kSub) (hkAdd : 0 ≤ kAdd)
    (hphiX : 0 ≤ phiX) (hphiY : 0 ≤ phiY) :
    0 ≤ phiX * phiY *
      (kSub * (wX / phiX - wY / phiY) ^ 2 +
        kAdd * (wX / phiX + wY / phiY) ^ 2) := by
  positivity

/-- Pointwise supersolution form of the two-channel Picone transform.  After
integration, its left-hand side is the raw ground-state row; proving that row
dominates the remaining local potential is the genuinely new analytic lemma
needed by this route. -/
theorem picone_two_channel_row_le
    {kSub kAdd phiX phiY wX wY : ℝ}
    (hkSub : 0 ≤ kSub) (hkAdd : 0 ≤ kAdd)
    (hphiX : 0 < phiX) (hphiY : 0 < phiY) :
    (kSub + kAdd) * (phiX - phiY) *
        (wX ^ 2 / phiX - wY ^ 2 / phiY) ≤
      kSub * (wX - wY) ^ 2 + kAdd * (wX + wY) ^ 2 := by
  rw [picone_two_channel_identity hphiX.ne' hphiY.ne']
  exact le_add_of_nonneg_left
    (picone_two_channel_square_nonneg hkSub hkAdd hphiX.le hphiY.le)

/-! ## The folded signed regular row -/

/-- Difference between the same-sign and reflected regular kernels after the
odd positive-half fold. -/
def fourCellOddFoldedRegularDifferenceKernel (x y : ℝ) : ℝ :=
  yoshidaRegularKernel (fourCellOperatorHalfWidth * |x - y|) -
    yoshidaRegularKernel (fourCellOperatorHalfWidth * (x + y))

/-- The negative folded regular correlation is exactly a positive Dirichlet
square minus its two row masses.  Thus the regular term itself introduces no
positive off-diagonal coefficient whenever the folded difference kernel is
nonnegative. -/
theorem foldedRegularCorrelation_eq_dirichlet_sub_rows
    (x y wX wY : ℝ) :
    -2 * fourCellOperatorHalfWidth *
          fourCellOddFoldedRegularDifferenceKernel x y * wX * wY =
      fourCellOperatorHalfWidth *
          fourCellOddFoldedRegularDifferenceKernel x y * (wX - wY) ^ 2 -
        fourCellOperatorHalfWidth *
          fourCellOddFoldedRegularDifferenceKernel x y * wX ^ 2 -
        fourCellOperatorHalfWidth *
          fourCellOddFoldedRegularDifferenceKernel x y * wY ^ 2 := by
  ring

/-- Conditional sign statement separated from the still-needed analytic
monotonicity theorem for `yoshidaRegularKernel`. -/
theorem foldedRegularDirichletSquare_nonneg
    {x y wX wY : ℝ}
    (hkernel : 0 ≤ fourCellOddFoldedRegularDifferenceKernel x y) :
    0 ≤ fourCellOperatorHalfWidth *
      fourCellOddFoldedRegularDifferenceKernel x y * (wX - wY) ^ 2 := by
  have hwidth : 0 ≤ fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  positivity

/-! ## Fatal sign obstruction for a scalar Stieltjes fold -/

/-- One ordered-pair contribution of the adverse strip-odd raw energy.  The
four values are those at `x`, its strip reflection, `y`, and its strip
reflection. -/
def adverseStripOddPairQuadratic
    (distance wX wXRef wY wYRef : ℝ) : ℝ :=
  -(1 / 2 : ℝ) *
    (((wX - wXRef) / 2 - (wY - wYRef) / 2) ^ 2 / distance)

/-- Full algebraic expansion of one adverse strip-odd pair.  In particular,
the `wX*wXRef` and `wY*wYRef` coefficients have the opposite sign from a
scalar Stieltjes kernel. -/
theorem adverseStripOddPairQuadratic_expansion
    {distance wX wXRef wY wYRef : ℝ} (hdistance : distance ≠ 0) :
    adverseStripOddPairQuadratic distance wX wXRef wY wYRef =
      -(wX ^ 2 + wXRef ^ 2 + wY ^ 2 + wYRef ^ 2) /
          (8 * distance) +
        (wX * wXRef + wX * wY + wXRef * wYRef + wY * wYRef) /
          (4 * distance) -
        (wX * wYRef + wXRef * wY) / (4 * distance) := by
  unfold adverseStripOddPairQuadratic
  field_simp [hdistance]
  ring

/-- The polarized coefficient coupling a strip value to its own reflection
is exactly positive `1/(8 distance)`. -/
theorem adverseStripOddPair_reflection_polarization_eq
    {distance : ℝ} (hdistance : distance ≠ 0) :
    (adverseStripOddPairQuadratic distance 1 1 0 0 -
        adverseStripOddPairQuadratic distance 1 0 0 0 -
        adverseStripOddPairQuadratic distance 0 1 0 0) / 2 =
      1 / (8 * distance) := by
  unfold adverseStripOddPairQuadratic
  field_simp [hdistance]
  ring

/-- Hence every positive strip distance gives a strictly positive reflected
off-diagonal polarization.  A successful ground-state proof must retain the
strip parity block (or its already-proved positive reserve) rather than model
the complete core as one scalar Stieltjes kernel. -/
theorem adverseStripOddPair_reflection_polarization_pos
    {distance : ℝ} (hdistance : 0 < distance) :
    0 <
      (adverseStripOddPairQuadratic distance 1 1 0 0 -
          adverseStripOddPairQuadratic distance 1 0 0 0 -
          adverseStripOddPairQuadratic distance 0 1 0 0) / 2 := by
  rw [adverseStripOddPair_reflection_polarization_eq hdistance.ne']
  positivity

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddCoreGroundStatePiconeStructural

import ArithmeticHodge.Analysis.YoshidaFourCellOddP11RationalRieszGroundProfileStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddCoreGroundStatePiconeStructural

set_option autoImplicit false

open Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddCoreBlockPiconeStructural

noncomputable section

open YoshidaFourCellOddCoreGroundStatePiconeStructural
open YoshidaFourCellOddEndpointStripCoercivityStructural
open YoshidaFourCellOddP11RationalRieszGroundProfileStructural
open YoshidaFourCellOddStripCapacityClosureStructural
open YoshidaFourCellParityOperatorStructural

/-!
# Strip-parity block Picone transform for the odd four-cell core

The adverse strip-odd raw form is not a scalar Stieltjes kernel in the two
physical strip values.  In strip-even/strip-odd coordinates, however, it
cancels exactly the odd part of the same-sign strip energy.  What remains is
one positive strip-even Dirichlet channel.  The reflected raw channels stay
as positive plus-squares.  This file records that block transform exactly and
instantiates it with the positive rational Riesz ground profile.
-/

/-! ## Exact cancellation in strip-parity coordinates -/

/-- Physical value reconstructed from strip-even and strip-odd coordinates.
The sign is `1` on the right half of the strip and `-1` on the left half. -/
def stripParityValue (even odd sign : ℝ) : ℝ := even + sign * odd

/-- Same-sign strip energy in both same-parity and cross-parity quadrants,
minus the adverse strip-odd raw block.  The two kernel weights are left
abstract so the algebra has no diagonal singularity. -/
def stripSameAdverseBlockPair
    (kDiff kSum eZ oZ eS oS : ℝ) : ℝ :=
  (kDiff / 2) *
      ((stripParityValue eZ oZ 1 - stripParityValue eS oS 1) ^ 2 +
        (stripParityValue eZ oZ (-1) -
          stripParityValue eS oS (-1)) ^ 2 -
        2 * (oZ - oS) ^ 2) +
    (kSum / 2) *
      ((stripParityValue eZ oZ 1 -
          stripParityValue eS oS (-1)) ^ 2 +
        (stripParityValue eZ oZ (-1) -
          stripParityValue eS oS 1) ^ 2 -
        2 * (oZ + oS) ^ 2)

/-- Exact block cancellation: both adverse strip-odd channels disappear,
leaving only the strip-even difference square. -/
theorem stripSameAdverseBlockPair_eq_even
    (kDiff kSum eZ oZ eS oS : ℝ) :
    stripSameAdverseBlockPair kDiff kSum eZ oZ eS oS =
      (kDiff + kSum) * (eZ - eS) ^ 2 := by
  unfold stripSameAdverseBlockPair stripParityValue
  ring

/-- Picone transform of the surviving strip-even channel. -/
theorem stripSameAdverseBlockPair_picone
    {kDiff kSum phiZ phiS eZ oZ eS oS : ℝ}
    (hphiZ : phiZ ≠ 0) (hphiS : phiS ≠ 0) :
    stripSameAdverseBlockPair kDiff kSum eZ oZ eS oS =
      (kDiff + kSum) * phiZ * phiS *
          (eZ / phiZ - eS / phiS) ^ 2 +
        (kDiff + kSum) * (phiZ - phiS) *
          (eZ ^ 2 / phiZ - eS ^ 2 / phiS) := by
  rw [stripSameAdverseBlockPair_eq_even,
    picone_sub_sq_identity hphiZ hphiS]
  ring

/-- The quotient-square remainder of the same/adverse strip block is
nonnegative for positive raw weights and a positive strip-even ground
profile. -/
theorem stripSameAdverseBlockPair_square_nonneg
    {kDiff kSum phiZ phiS eZ eS : ℝ}
    (hkDiff : 0 ≤ kDiff) (hkSum : 0 ≤ kSum)
    (hphiZ : 0 ≤ phiZ) (hphiS : 0 ≤ phiS) :
    0 ≤ (kDiff + kSum) * phiZ * phiS *
      (eZ / phiZ - eS / phiS) ^ 2 := by
  positivity

/-- A Picone row is already diagonal in the two endpoint values.  This is
the pointwise algebra used when the symmetric pair integral is turned into
the ground-state supersolution row. -/
theorem piconeRow_eq_diagonalRows
    (k phiX phiY wX wY : ℝ) :
    k * (phiX - phiY) *
        (wX ^ 2 / phiX - wY ^ 2 / phiY) =
      (k * (phiX - phiY) / phiX) * wX ^ 2 +
        (k * (phiY - phiX) / phiY) * wY ^ 2 := by
  ring

/-! ## Four reflected plus-square channels -/

/-- The four reflected raw channels between two paired strip points. -/
def stripReflectedRawBlockPair
    (kPP kMM kPM kMP wPZ wMZ wPS wMS : ℝ) : ℝ :=
  kPP * (wPZ + wPS) ^ 2 +
    kMM * (wMZ + wMS) ^ 2 +
    kPM * (wPZ + wMS) ^ 2 +
    kMP * (wMZ + wPS) ^ 2

/-- Positive quotient-square part of the reflected block Picone transform. -/
def stripReflectedRawBlockPiconeSquare
    (kPP kMM kPM kMP phiPZ phiMZ phiPS phiMS
      wPZ wMZ wPS wMS : ℝ) : ℝ :=
  kPP * phiPZ * phiPS * (wPZ / phiPZ + wPS / phiPS) ^ 2 +
    kMM * phiMZ * phiMS * (wMZ / phiMZ + wMS / phiMS) ^ 2 +
    kPM * phiPZ * phiMS * (wPZ / phiPZ + wMS / phiMS) ^ 2 +
    kMP * phiMZ * phiPS * (wMZ / phiMZ + wPS / phiPS) ^ 2

/-- Ground-state row left by the four reflected plus-square channels. -/
def stripReflectedRawBlockPiconeRow
    (kPP kMM kPM kMP phiPZ phiMZ phiPS phiMS
      wPZ wMZ wPS wMS : ℝ) : ℝ :=
  kPP * (phiPZ - phiPS) * (wPZ ^ 2 / phiPZ - wPS ^ 2 / phiPS) +
    kMM * (phiMZ - phiMS) * (wMZ ^ 2 / phiMZ - wMS ^ 2 / phiMS) +
    kPM * (phiPZ - phiMS) * (wPZ ^ 2 / phiPZ - wMS ^ 2 / phiMS) +
    kMP * (phiMZ - phiPS) * (wMZ ^ 2 / phiMZ - wPS ^ 2 / phiPS)

/-- Exact simultaneous Picone transform of all reflected channels. -/
theorem stripReflectedRawBlockPair_picone
    {kPP kMM kPM kMP phiPZ phiMZ phiPS phiMS
      wPZ wMZ wPS wMS : ℝ}
    (hphiPZ : phiPZ ≠ 0) (hphiMZ : phiMZ ≠ 0)
    (hphiPS : phiPS ≠ 0) (hphiMS : phiMS ≠ 0) :
    stripReflectedRawBlockPair kPP kMM kPM kMP wPZ wMZ wPS wMS =
      stripReflectedRawBlockPiconeSquare
          kPP kMM kPM kMP phiPZ phiMZ phiPS phiMS
          wPZ wMZ wPS wMS +
        stripReflectedRawBlockPiconeRow
          kPP kMM kPM kMP phiPZ phiMZ phiPS phiMS
          wPZ wMZ wPS wMS := by
  have hPP : kPP * (wPZ + wPS) ^ 2 =
      kPP * (phiPZ * phiPS *
        (wPZ / phiPZ + wPS / phiPS) ^ 2 +
          (phiPZ - phiPS) *
            (wPZ ^ 2 / phiPZ - wPS ^ 2 / phiPS)) := by
    exact congrArg (fun t : ℝ ↦ kPP * t)
      (picone_add_sq_identity hphiPZ hphiPS)
  have hMM : kMM * (wMZ + wMS) ^ 2 =
      kMM * (phiMZ * phiMS *
        (wMZ / phiMZ + wMS / phiMS) ^ 2 +
          (phiMZ - phiMS) *
            (wMZ ^ 2 / phiMZ - wMS ^ 2 / phiMS)) := by
    exact congrArg (fun t : ℝ ↦ kMM * t)
      (picone_add_sq_identity hphiMZ hphiMS)
  have hPM : kPM * (wPZ + wMS) ^ 2 =
      kPM * (phiPZ * phiMS *
        (wPZ / phiPZ + wMS / phiMS) ^ 2 +
          (phiPZ - phiMS) *
            (wPZ ^ 2 / phiPZ - wMS ^ 2 / phiMS)) := by
    exact congrArg (fun t : ℝ ↦ kPM * t)
      (picone_add_sq_identity hphiPZ hphiMS)
  have hMP : kMP * (wMZ + wPS) ^ 2 =
      kMP * (phiMZ * phiPS *
        (wMZ / phiMZ + wPS / phiPS) ^ 2 +
          (phiMZ - phiPS) *
            (wMZ ^ 2 / phiMZ - wPS ^ 2 / phiPS)) := by
    exact congrArg (fun t : ℝ ↦ kMP * t)
      (picone_add_sq_identity hphiMZ hphiPS)
  unfold stripReflectedRawBlockPair stripReflectedRawBlockPiconeSquare
    stripReflectedRawBlockPiconeRow
  rw [hPP, hMM, hPM, hMP]
  ring

/-- The reflected quotient-square block is nonnegative under its actual
positive-kernel and positive-ground-state signs. -/
theorem stripReflectedRawBlockPiconeSquare_nonneg
    {kPP kMM kPM kMP phiPZ phiMZ phiPS phiMS
      wPZ wMZ wPS wMS : ℝ}
    (hkPP : 0 ≤ kPP) (hkMM : 0 ≤ kMM)
    (hkPM : 0 ≤ kPM) (hkMP : 0 ≤ kMP)
    (hphiPZ : 0 ≤ phiPZ) (hphiMZ : 0 ≤ phiMZ)
    (hphiPS : 0 ≤ phiPS) (hphiMS : 0 ≤ phiMS) :
    0 ≤ stripReflectedRawBlockPiconeSquare
      kPP kMM kPM kMP phiPZ phiMZ phiPS phiMS
      wPZ wMZ wPS wMS := by
  unfold stripReflectedRawBlockPiconeSquare
  positivity

/-! ## Actual raw-reserve kernel weights -/

/-- Same-sign kernel in the global positive-half raw reserve.  The factor
`1 / 2` is the coefficient of that reserve before the endpoint square is
split off. -/
def positiveHalfSameReserveWeight (x y : ℝ) : ℝ :=
  1 / (2 * |x - y|)

/-- Reflected-plus kernel in the global positive-half raw reserve. -/
def positiveHalfReflectedReserveWeight (x y : ℝ) : ℝ :=
  1 / (2 * (x + y))

/-- Difference-quadrant kernel after the affine endpoint-strip pullback.
The affine Jacobian and the outer half-reserve coefficient are both already
accounted for by the paired block normalization. -/
def stripSameDifferenceReserveWeight (z s : ℝ) : ℝ :=
  1 / (5 * |z - s|)

/-- Cross-quadrant kernel after the affine endpoint-strip pullback. -/
def stripSameCrossReserveWeight (z s : ℝ) : ℝ :=
  1 / (5 * (z + s))

/-- The four actual reflected-plus reserve weights on paired normalized
strip points.  The denominators are the physical sums multiplied by five;
the factor ten includes both affine Jacobians and the outer half reserve. -/
def stripReflectedPPReserveWeight (z s : ℝ) : ℝ :=
  1 / (10 * (8 + z + s))

def stripReflectedMMReserveWeight (z s : ℝ) : ℝ :=
  1 / (10 * (8 - z - s))

def stripReflectedPMReserveWeight (z s : ℝ) : ℝ :=
  1 / (10 * (8 + z - s))

def stripReflectedMPReserveWeight (z s : ℝ) : ℝ :=
  1 / (10 * (8 - z + s))

theorem positiveHalfSameReserveWeight_nonneg (x y : ℝ) :
    0 ≤ positiveHalfSameReserveWeight x y := by
  unfold positiveHalfSameReserveWeight
  positivity

theorem positiveHalfReflectedReserveWeight_pos
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    0 < positiveHalfReflectedReserveWeight x y := by
  unfold positiveHalfReflectedReserveWeight
  positivity

theorem stripSameDifferenceReserveWeight_nonneg (z s : ℝ) :
    0 ≤ stripSameDifferenceReserveWeight z s := by
  unfold stripSameDifferenceReserveWeight
  positivity

theorem stripSameCrossReserveWeight_pos
    {z s : ℝ} (hz : 0 < z) (hs : 0 < s) :
    0 < stripSameCrossReserveWeight z s := by
  unfold stripSameCrossReserveWeight
  positivity

/-- Every reflected denominator stays uniformly positive on the normalized
half-strip; this is the sign input for the four-channel block remainder. -/
theorem stripReflectedReserveWeights_pos
    {z s : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 < stripReflectedPPReserveWeight z s ∧
      0 < stripReflectedMMReserveWeight z s ∧
      0 < stripReflectedPMReserveWeight z s ∧
      0 < stripReflectedMPReserveWeight z s := by
  unfold stripReflectedPPReserveWeight stripReflectedMMReserveWeight
    stripReflectedPMReserveWeight stripReflectedMPReserveWeight
  constructor
  · positivity
  constructor
  · have : 0 < 8 - z - s := by linarith
    positivity
  constructor
  · have : 0 < 8 + z - s := by linarith
    positivity
  · have : 0 < 8 - z + s := by linarith
    positivity

/-! ## The concrete rational Riesz strip ground block -/

def rationalRieszStripEvenGround (z : ℝ) : ℝ :=
  fourCellOddEndpointStripEven
    fourCellOddP11RationalRieszGroundProfile z

def rationalRieszStripOddPositiveGround (z : ℝ) : ℝ :=
  -fourCellOddEndpointStripOdd
    fourCellOddP11RationalRieszGroundProfile z

def rationalRieszStripPlusGround (z : ℝ) : ℝ :=
  fourCellOddEndpointStripPullback
    fourCellOddP11RationalRieszGroundProfile z

def rationalRieszStripMinusGround (z : ℝ) : ℝ :=
  fourCellOddEndpointStripPullback
    fourCellOddP11RationalRieszGroundProfile (-z)

/-- All four ground-state signs needed by the block transform hold on the
positive normalized half-strip. -/
theorem rationalRieszStripGroundBlock_pos
    {z : ℝ} (hz : 0 < z) (hz1 : z ≤ 1) :
    0 < rationalRieszStripEvenGround z ∧
      0 < rationalRieszStripOddPositiveGround z ∧
      0 < rationalRieszStripPlusGround z ∧
      0 < rationalRieszStripMinusGround z := by
  have hzIcc : z ∈ Icc (-1 : ℝ) 1 := ⟨by linarith, hz1⟩
  have hminusPoint : 0 < 4 / 5 - z / 5 := by linarith
  have hminusPoint1 : 4 / 5 - z / 5 ≤ 1 := by linarith
  have hplusPoint : 0 < 4 / 5 + z / 5 := by linarith
  have hplusPoint1 : 4 / 5 + z / 5 ≤ 1 := by linarith
  constructor
  · exact fourCellOddEndpointStripEven_rationalRiesz_pos hzIcc
  constructor
  · exact neg_pos.mpr
      (fourCellOddEndpointStripOdd_rationalRiesz_neg hz hz1)
  constructor
  · unfold rationalRieszStripPlusGround fourCellOddEndpointStripPullback
    exact fourCellOddP11RationalRieszGroundProfile_pos
      hplusPoint hplusPoint1
  · unfold rationalRieszStripMinusGround fourCellOddEndpointStripPullback
    simpa only [neg_div, sub_eq_add_neg] using
      (fourCellOddP11RationalRieszGroundProfile_pos
        hminusPoint hminusPoint1)

/-- The two physical strip values are reconstructed from the positive
strip-even ground and the negative strip-odd ground.  Thus the block uses
the certified signs of all three objects: `q`, its strip-even part, and its
strip-odd part. -/
theorem rationalRieszStripParityGround_eq (z : ℝ) :
    rationalRieszStripPlusGround z =
        stripParityValue (rationalRieszStripEvenGround z)
          (-rationalRieszStripOddPositiveGround z) 1 ∧
      rationalRieszStripMinusGround z =
        stripParityValue (rationalRieszStripEvenGround z)
          (-rationalRieszStripOddPositiveGround z) (-1) := by
  unfold rationalRieszStripPlusGround rationalRieszStripMinusGround
    rationalRieszStripEvenGround rationalRieszStripOddPositiveGround
    stripParityValue fourCellOddEndpointStripEven
    fourCellOddEndpointStripOdd
  constructor <;> ring

/-! ## Global raw pair off the endpoint square -/

/-- One pointwise pair in the half-reserve made from the same-sign raw
difference square and the odd reflected-plus square.  On the complement of
the endpoint square this is the raw part of the exact `A/B` partition. -/
def positiveHalfRawReservePair
    (x y wX wY : ℝ) : ℝ :=
  positiveHalfSameReserveWeight x y * (wX - wY) ^ 2 +
    positiveHalfReflectedReserveWeight x y * (wX + wY) ^ 2

def rationalRieszPositiveHalfRawPiconeSquare
    (x y wX wY : ℝ) : ℝ :=
  fourCellOddP11RationalRieszGroundProfile x *
      fourCellOddP11RationalRieszGroundProfile y *
    (positiveHalfSameReserveWeight x y *
        (wX / fourCellOddP11RationalRieszGroundProfile x -
          wY / fourCellOddP11RationalRieszGroundProfile y) ^ 2 +
      positiveHalfReflectedReserveWeight x y *
        (wX / fourCellOddP11RationalRieszGroundProfile x +
          wY / fourCellOddP11RationalRieszGroundProfile y) ^ 2)

def rationalRieszPositiveHalfRawPiconeRow
    (x y wX wY : ℝ) : ℝ :=
  (positiveHalfSameReserveWeight x y +
      positiveHalfReflectedReserveWeight x y) *
    (fourCellOddP11RationalRieszGroundProfile x -
      fourCellOddP11RationalRieszGroundProfile y) *
    (wX ^ 2 / fourCellOddP11RationalRieszGroundProfile x -
      wY ^ 2 / fourCellOddP11RationalRieszGroundProfile y)

/-- Actual Picone transform of every raw pair outside the endpoint square.
The endpoint square itself is replaced by the block identity below. -/
theorem positiveHalfRawReservePair_rationalRiesz_picone
    {x y wX wY : ℝ}
    (hx : 0 < x) (hx1 : x ≤ 1)
    (hy : 0 < y) (hy1 : y ≤ 1) :
    positiveHalfRawReservePair x y wX wY =
      rationalRieszPositiveHalfRawPiconeSquare x y wX wY +
        rationalRieszPositiveHalfRawPiconeRow x y wX wY := by
  have hqx := fourCellOddP11RationalRieszGroundProfile_pos hx hx1
  have hqy := fourCellOddP11RationalRieszGroundProfile_pos hy hy1
  simpa only [positiveHalfRawReservePair,
    rationalRieszPositiveHalfRawPiconeSquare,
    rationalRieszPositiveHalfRawPiconeRow] using
    (picone_two_channel_identity
      (kSub := positiveHalfSameReserveWeight x y)
      (kAdd := positiveHalfReflectedReserveWeight x y)
      (phiX := fourCellOddP11RationalRieszGroundProfile x)
      (phiY := fourCellOddP11RationalRieszGroundProfile y)
      (wX := wX) (wY := wY) hqx.ne' hqy.ne')

theorem rationalRieszPositiveHalfRawPiconeSquare_nonneg
    {x y wX wY : ℝ}
    (hx : 0 < x) (hx1 : x ≤ 1)
    (hy : 0 < y) (hy1 : y ≤ 1) :
    0 ≤ rationalRieszPositiveHalfRawPiconeSquare x y wX wY := by
  have hqx := fourCellOddP11RationalRieszGroundProfile_pos hx hx1
  have hqy := fourCellOddP11RationalRieszGroundProfile_pos hy hy1
  exact picone_two_channel_square_nonneg
    (positiveHalfSameReserveWeight_nonneg x y)
    (positiveHalfReflectedReserveWeight_pos hx hy).le
    hqx.le hqy.le

/-! ## Actual endpoint-strip parity block -/

/-- The complete endpoint-square raw reserve at a paired point `(z,s)`.
The first summand is same-sign raw minus the adverse strip-odd raw block;
the second is the full reflected-plus raw block. -/
def endpointStripRawReserveBlockPair
    (z s eZ oZ eS oS : ℝ) : ℝ :=
  stripSameAdverseBlockPair
      (stripSameDifferenceReserveWeight z s)
      (stripSameCrossReserveWeight z s)
      eZ oZ eS oS +
    stripReflectedRawBlockPair
      (stripReflectedPPReserveWeight z s)
      (stripReflectedMMReserveWeight z s)
      (stripReflectedPMReserveWeight z s)
      (stripReflectedMPReserveWeight z s)
      (stripParityValue eZ oZ 1)
      (stripParityValue eZ oZ (-1))
      (stripParityValue eS oS 1)
      (stripParityValue eS oS (-1))

def rationalRieszStripSamePiconeSquare
    (z s eZ eS : ℝ) : ℝ :=
  (stripSameDifferenceReserveWeight z s +
      stripSameCrossReserveWeight z s) *
    rationalRieszStripEvenGround z * rationalRieszStripEvenGround s *
      (eZ / rationalRieszStripEvenGround z -
        eS / rationalRieszStripEvenGround s) ^ 2

def rationalRieszStripSamePiconeRow
    (z s eZ eS : ℝ) : ℝ :=
  (stripSameDifferenceReserveWeight z s +
      stripSameCrossReserveWeight z s) *
    (rationalRieszStripEvenGround z -
      rationalRieszStripEvenGround s) *
      (eZ ^ 2 / rationalRieszStripEvenGround z -
        eS ^ 2 / rationalRieszStripEvenGround s)

def rationalRieszStripReflectedPiconeSquare
    (z s eZ oZ eS oS : ℝ) : ℝ :=
  stripReflectedRawBlockPiconeSquare
    (stripReflectedPPReserveWeight z s)
    (stripReflectedMMReserveWeight z s)
    (stripReflectedPMReserveWeight z s)
    (stripReflectedMPReserveWeight z s)
    (rationalRieszStripPlusGround z)
    (rationalRieszStripMinusGround z)
    (rationalRieszStripPlusGround s)
    (rationalRieszStripMinusGround s)
    (stripParityValue eZ oZ 1)
    (stripParityValue eZ oZ (-1))
    (stripParityValue eS oS 1)
    (stripParityValue eS oS (-1))

def rationalRieszStripReflectedPiconeRow
    (z s eZ oZ eS oS : ℝ) : ℝ :=
  stripReflectedRawBlockPiconeRow
    (stripReflectedPPReserveWeight z s)
    (stripReflectedMMReserveWeight z s)
    (stripReflectedPMReserveWeight z s)
    (stripReflectedMPReserveWeight z s)
    (rationalRieszStripPlusGround z)
    (rationalRieszStripMinusGround z)
    (rationalRieszStripPlusGround s)
    (rationalRieszStripMinusGround s)
    (stripParityValue eZ oZ 1)
    (stripParityValue eZ oZ (-1))
    (stripParityValue eS oS 1)
    (stripParityValue eS oS (-1))

/-- The nonnegative quotient-square remainder in the actual strip block. -/
def rationalRieszEndpointStripBlockPiconeSquare
    (z s eZ oZ eS oS : ℝ) : ℝ :=
  rationalRieszStripSamePiconeSquare z s eZ eS +
    rationalRieszStripReflectedPiconeSquare z s eZ oZ eS oS

/-- The exact ground-state row left by the actual strip block. -/
def rationalRieszEndpointStripBlockPiconeRow
    (z s eZ oZ eS oS : ℝ) : ℝ :=
  rationalRieszStripSamePiconeRow z s eZ eS +
    rationalRieszStripReflectedPiconeRow z s eZ oZ eS oS

/-- Exact pointwise block Picone identity for the endpoint square.  The
adverse strip-odd raw energy has disappeared algebraically; no estimate or
scalar matched-factor reduction is used. -/
theorem endpointStripRawReserveBlockPair_rationalRiesz_picone
    {z s eZ oZ eS oS : ℝ}
    (hz : 0 < z) (hz1 : z ≤ 1)
    (hs : 0 < s) (hs1 : s ≤ 1) :
    endpointStripRawReserveBlockPair z s eZ oZ eS oS =
      rationalRieszEndpointStripBlockPiconeSquare
          z s eZ oZ eS oS +
        rationalRieszEndpointStripBlockPiconeRow
          z s eZ oZ eS oS := by
  rcases rationalRieszStripGroundBlock_pos hz hz1 with
    ⟨hEvenZ, _hOddZ, hPlusZ, hMinusZ⟩
  rcases rationalRieszStripGroundBlock_pos hs hs1 with
    ⟨hEvenS, _hOddS, hPlusS, hMinusS⟩
  have hsame := stripSameAdverseBlockPair_picone
    (kDiff := stripSameDifferenceReserveWeight z s)
    (kSum := stripSameCrossReserveWeight z s)
    (phiZ := rationalRieszStripEvenGround z)
    (phiS := rationalRieszStripEvenGround s)
    (eZ := eZ) (oZ := oZ) (eS := eS) (oS := oS)
    hEvenZ.ne' hEvenS.ne'
  have hreflected := stripReflectedRawBlockPair_picone
    (kPP := stripReflectedPPReserveWeight z s)
    (kMM := stripReflectedMMReserveWeight z s)
    (kPM := stripReflectedPMReserveWeight z s)
    (kMP := stripReflectedMPReserveWeight z s)
    (phiPZ := rationalRieszStripPlusGround z)
    (phiMZ := rationalRieszStripMinusGround z)
    (phiPS := rationalRieszStripPlusGround s)
    (phiMS := rationalRieszStripMinusGround s)
    (wPZ := stripParityValue eZ oZ 1)
    (wMZ := stripParityValue eZ oZ (-1))
    (wPS := stripParityValue eS oS 1)
    (wMS := stripParityValue eS oS (-1))
    hPlusZ.ne' hMinusZ.ne' hPlusS.ne' hMinusS.ne'
  unfold endpointStripRawReserveBlockPair
    rationalRieszEndpointStripBlockPiconeSquare
    rationalRieszEndpointStripBlockPiconeRow
    rationalRieszStripSamePiconeSquare
    rationalRieszStripSamePiconeRow
    rationalRieszStripReflectedPiconeSquare
    rationalRieszStripReflectedPiconeRow
  rw [hsame, hreflected]
  ring

/-- Every quotient-square term in the actual endpoint block is
nonnegative.  This simultaneously uses positivity of the strip-even ground,
negativity of the strip-odd ground (through the physical parity values), and
positivity of `q` itself at both reflected strip points. -/
theorem rationalRieszEndpointStripBlockPiconeSquare_nonneg
    {z s eZ oZ eS oS : ℝ}
    (hz : 0 < z) (hz1 : z ≤ 1)
    (hs : 0 < s) (hs1 : s ≤ 1) :
    0 ≤ rationalRieszEndpointStripBlockPiconeSquare
      z s eZ oZ eS oS := by
  rcases rationalRieszStripGroundBlock_pos hz hz1 with
    ⟨hEvenZ, _hOddZ, hPlusZ, hMinusZ⟩
  rcases rationalRieszStripGroundBlock_pos hs hs1 with
    ⟨hEvenS, _hOddS, hPlusS, hMinusS⟩
  rcases stripReflectedReserveWeights_pos hz.le hz1 hs.le hs1 with
    ⟨hkPP, hkMM, hkPM, hkMP⟩
  unfold rationalRieszEndpointStripBlockPiconeSquare
    rationalRieszStripSamePiconeSquare
    rationalRieszStripReflectedPiconeSquare
  apply add_nonneg
  · exact stripSameAdverseBlockPair_square_nonneg
      (stripSameDifferenceReserveWeight_nonneg z s)
      (stripSameCrossReserveWeight_pos hz hs).le
      hEvenZ.le hEvenS.le
  · exact stripReflectedRawBlockPiconeSquare_nonneg
      hkPP.le hkMM.le hkPM.le hkMP.le
      hPlusZ.le hMinusZ.le hPlusS.le hMinusS.le

/-! ## Folded regular Dirichlet square and the remaining row -/

def rationalRieszFoldedRegularPiconeSquare
    (x y wX wY : ℝ) : ℝ :=
  fourCellOperatorHalfWidth *
      fourCellOddFoldedRegularDifferenceKernel x y *
      fourCellOddP11RationalRieszGroundProfile x *
      fourCellOddP11RationalRieszGroundProfile y *
    (wX / fourCellOddP11RationalRieszGroundProfile x -
      wY / fourCellOddP11RationalRieszGroundProfile y) ^ 2

/-- The regular Picone row includes the two negative diagonal masses from
the exact Dirichlet-minus-rows decomposition. -/
def rationalRieszFoldedRegularPiconeRow
    (x y wX wY : ℝ) : ℝ :=
  fourCellOperatorHalfWidth *
      fourCellOddFoldedRegularDifferenceKernel x y *
    (fourCellOddP11RationalRieszGroundProfile x -
      fourCellOddP11RationalRieszGroundProfile y) *
    (wX ^ 2 / fourCellOddP11RationalRieszGroundProfile x -
      wY ^ 2 / fourCellOddP11RationalRieszGroundProfile y) -
    fourCellOperatorHalfWidth *
      fourCellOddFoldedRegularDifferenceKernel x y * wX ^ 2 -
    fourCellOperatorHalfWidth *
      fourCellOddFoldedRegularDifferenceKernel x y * wY ^ 2

/-- The signed folded regular correlation is a positive Picone square plus
an explicit diagonal ground-state row. -/
theorem foldedRegularCorrelation_rationalRiesz_picone
    {x y wX wY : ℝ}
    (hx : 0 < x) (hx1 : x ≤ 1)
    (hy : 0 < y) (hy1 : y ≤ 1) :
    -2 * fourCellOperatorHalfWidth *
        fourCellOddFoldedRegularDifferenceKernel x y * wX * wY =
      rationalRieszFoldedRegularPiconeSquare x y wX wY +
        rationalRieszFoldedRegularPiconeRow x y wX wY := by
  have hqx := fourCellOddP11RationalRieszGroundProfile_pos hx hx1
  have hqy := fourCellOddP11RationalRieszGroundProfile_pos hy hy1
  have hpicone :
      fourCellOperatorHalfWidth *
          fourCellOddFoldedRegularDifferenceKernel x y * (wX - wY) ^ 2 =
        fourCellOperatorHalfWidth *
          fourCellOddFoldedRegularDifferenceKernel x y *
          (fourCellOddP11RationalRieszGroundProfile x *
              fourCellOddP11RationalRieszGroundProfile y *
              (wX / fourCellOddP11RationalRieszGroundProfile x -
                wY / fourCellOddP11RationalRieszGroundProfile y) ^ 2 +
            (fourCellOddP11RationalRieszGroundProfile x -
                fourCellOddP11RationalRieszGroundProfile y) *
              (wX ^ 2 / fourCellOddP11RationalRieszGroundProfile x -
                wY ^ 2 /
                  fourCellOddP11RationalRieszGroundProfile y)) := by
    exact congrArg
      (fun t : ℝ ↦ fourCellOperatorHalfWidth *
        fourCellOddFoldedRegularDifferenceKernel x y * t)
      (picone_sub_sq_identity hqx.ne' hqy.ne')
  rw [foldedRegularCorrelation_eq_dirichlet_sub_rows,
    hpicone]
  unfold rationalRieszFoldedRegularPiconeSquare
    rationalRieszFoldedRegularPiconeRow
  ring

theorem rationalRieszFoldedRegularPiconeSquare_nonneg
    {x y wX wY : ℝ}
    (hx : 0 < x) (hx1 : x ≤ 1)
    (hy : 0 < y) (hy1 : y ≤ 1) :
    0 ≤ rationalRieszFoldedRegularPiconeSquare x y wX wY := by
  have hqx := fourCellOddP11RationalRieszGroundProfile_pos hx hx1
  have hqy := fourCellOddP11RationalRieszGroundProfile_pos hy hy1
  have hkernel := fourCellOddFoldedRegularDifferenceKernel_nonneg
    hx.le hx1 hy.le hy1
  have hwidth : 0 ≤ fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  unfold rationalRieszFoldedRegularPiconeSquare
  positivity

/-! ## Explicit diagonal supersolution frontier -/

/-- The coefficient of `wX²` after the off-strip raw pair and folded
regular pair are Picone transformed against the rational Riesz ground. -/
def rationalRieszRawRegularDiagonalCoefficientX (x y : ℝ) : ℝ :=
  (positiveHalfSameReserveWeight x y +
      positiveHalfReflectedReserveWeight x y) *
      (fourCellOddP11RationalRieszGroundProfile x -
        fourCellOddP11RationalRieszGroundProfile y) /
        fourCellOddP11RationalRieszGroundProfile x +
    fourCellOperatorHalfWidth *
      fourCellOddFoldedRegularDifferenceKernel x y *
      (fourCellOddP11RationalRieszGroundProfile x -
        fourCellOddP11RationalRieszGroundProfile y) /
        fourCellOddP11RationalRieszGroundProfile x -
    fourCellOperatorHalfWidth *
      fourCellOddFoldedRegularDifferenceKernel x y

/-- The coefficient at the second point, written with the same symmetric
pair kernels so no kernel-symmetry theorem is hidden in the algebra. -/
def rationalRieszRawRegularDiagonalCoefficientY (x y : ℝ) : ℝ :=
  (positiveHalfSameReserveWeight x y +
      positiveHalfReflectedReserveWeight x y) *
      (fourCellOddP11RationalRieszGroundProfile y -
        fourCellOddP11RationalRieszGroundProfile x) /
        fourCellOddP11RationalRieszGroundProfile y +
    fourCellOperatorHalfWidth *
      fourCellOddFoldedRegularDifferenceKernel x y *
      (fourCellOddP11RationalRieszGroundProfile y -
        fourCellOddP11RationalRieszGroundProfile x) /
        fourCellOddP11RationalRieszGroundProfile y -
    fourCellOperatorHalfWidth *
      fourCellOddFoldedRegularDifferenceKernel x y

def rationalRieszRawRegularDiagonalRowPair
    (x y wX wY : ℝ) : ℝ :=
  rationalRieszRawRegularDiagonalCoefficientX x y * wX ^ 2 +
    rationalRieszRawRegularDiagonalCoefficientY x y * wY ^ 2

/-- The sum of both Picone rows is literally diagonal.  This is the row
that remains to be integrated and compared with the local prime/potential
and scalar-mass coefficients. -/
theorem rationalRiesz_raw_add_regular_rows_eq_diagonal
    (x y wX wY : ℝ) :
    rationalRieszPositiveHalfRawPiconeRow x y wX wY +
        rationalRieszFoldedRegularPiconeRow x y wX wY =
      rationalRieszRawRegularDiagonalRowPair x y wX wY := by
  unfold rationalRieszPositiveHalfRawPiconeRow
    rationalRieszFoldedRegularPiconeRow
    rationalRieszRawRegularDiagonalRowPair
    rationalRieszRawRegularDiagonalCoefficientX
    rationalRieszRawRegularDiagonalCoefficientY
  ring

/-- Combined off-endpoint-square identity: the actual raw reserve plus the
signed folded regular correlation is the sum of two nonnegative quotient
squares and one explicit diagonal row. -/
theorem positiveHalfRawRegularPair_rationalRiesz_picone
    {x y wX wY : ℝ}
    (hx : 0 < x) (hx1 : x ≤ 1)
    (hy : 0 < y) (hy1 : y ≤ 1) :
    positiveHalfRawReservePair x y wX wY -
        2 * fourCellOperatorHalfWidth *
          fourCellOddFoldedRegularDifferenceKernel x y * wX * wY =
      rationalRieszPositiveHalfRawPiconeSquare x y wX wY +
        rationalRieszFoldedRegularPiconeSquare x y wX wY +
        rationalRieszRawRegularDiagonalRowPair x y wX wY := by
  rw [positiveHalfRawReservePair_rationalRiesz_picone hx hx1 hy hy1]
  have hregular := foldedRegularCorrelation_rationalRiesz_picone
    (wX := wX) (wY := wY) hx hx1 hy hy1
  have hrows := rationalRiesz_raw_add_regular_rows_eq_diagonal
    x y wX wY
  calc
    rationalRieszPositiveHalfRawPiconeSquare x y wX wY +
          rationalRieszPositiveHalfRawPiconeRow x y wX wY -
        2 * fourCellOperatorHalfWidth *
          fourCellOddFoldedRegularDifferenceKernel x y * wX * wY =
      rationalRieszPositiveHalfRawPiconeSquare x y wX wY +
        rationalRieszPositiveHalfRawPiconeRow x y wX wY +
        (-2 * fourCellOperatorHalfWidth *
          fourCellOddFoldedRegularDifferenceKernel x y * wX * wY) := by
            ring
    _ = rationalRieszPositiveHalfRawPiconeSquare x y wX wY +
        rationalRieszPositiveHalfRawPiconeRow x y wX wY +
        (rationalRieszFoldedRegularPiconeSquare x y wX wY +
          rationalRieszFoldedRegularPiconeRow x y wX wY) := by
            rw [hregular]
    _ = _ := by rw [← hrows]; ring

/-- A deliberately pointwise sufficient row condition for one off-strip
pair.  It is not claimed here and is not equivalent to the integrated odd
core target: integration can exploit cancellation between `y`-rows and the
retained local diagonal forms.  It records the remaining analytic frontier
without replacing it by sampling or a matched scalar factor. -/
def RationalRieszRawRegularPointwiseRowCondition (x y : ℝ) : Prop :=
  0 ≤ rationalRieszRawRegularDiagonalCoefficientX x y ∧
    0 ≤ rationalRieszRawRegularDiagonalCoefficientY x y

theorem rationalRieszRawRegularDiagonalRowPair_nonneg_of_pointwise
    {x y wX wY : ℝ}
    (hrow : RationalRieszRawRegularPointwiseRowCondition x y) :
    0 ≤ rationalRieszRawRegularDiagonalRowPair x y wX wY := by
  rcases hrow with ⟨hrowX, hrowY⟩
  unfold rationalRieszRawRegularDiagonalRowPair
  positivity

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddCoreBlockPiconeStructural

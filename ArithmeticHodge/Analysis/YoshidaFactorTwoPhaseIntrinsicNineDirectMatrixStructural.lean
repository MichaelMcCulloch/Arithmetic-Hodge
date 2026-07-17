import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineComplementSchurStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineStaticNestedSchurStructural

set_option autoImplicit false

open Matrix

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectMatrixStructural

noncomputable section

open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointOcticPotential
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoPhaseDiskSchur
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseIntrinsicNineComplementSchurStructural
open YoshidaFactorTwoPhaseIntrinsicNineStaticNestedSchurStructural
open YoshidaFactorTwoPhaseIntrinsicNineUnbalancedStaticDiskStructural
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicSixSchurReduction
open YoshidaFactorTwoPhaseIntrinsicSixStaticPlusObstruction
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
open YoshidaFactorTwoPhaseLowSchur

/-!
# The direct phase-native cutoff-nine matrix

The coordinate order is

`(c0,c2,c4,c1,c3,c5,c6,c8,c7)`.

Unlike the two static endpoint splittings, this matrix retains the actual disk
coordinates `(a,b)`.  Its diagonal blocks are the exact polarizations of the
signed endpoint quadratics and its off-diagonal block is the alternating
coupling.  The already-certified `P6/P7/P8` family is charged exactly
`15 / 16` of its low reserve.
-/

/-- The nine retained centered Legendre profiles, in direct-matrix order. -/
def factorTwoIntrinsicNineDirectBasis : Fin 9 → (ℝ → ℝ) :=
  ![centeredEvenP0, centeredEvenP2, factorTwoCenteredP4,
    centeredP1, centeredP3, factorTwoCenteredP5,
    factorTwoCenteredP6, factorTwoCenteredP8, factorTwoCenteredP7]

/-- The coordinate unit vector used to polarize the direct quadratic. -/
def factorTwoIntrinsicNineDirectUnit (i : Fin 9) : Fin 9 → ℝ :=
  Pi.single i 1

/-- Exact even diagonal on the retained degrees `0,2,4,6,8`. -/
def factorTwoIntrinsicNineDirectEvenQuadratic
    (a c0 c2 c4 c6 c8 : ℝ) : ℝ :=
  factorTwoIntrinsicSixStaticEven a c0 c2 c4 +
    2 * c6 * (c0 * factorTwoIntrinsicNinePhasePair a
        centeredEvenP0 factorTwoCenteredP6 +
      c2 * factorTwoIntrinsicNinePhasePair a
        centeredEvenP2 factorTwoCenteredP6 +
      c4 * factorTwoIntrinsicNinePhasePair a
        factorTwoCenteredP4 factorTwoCenteredP6) +
    2 * c8 * (c0 * factorTwoIntrinsicNinePhasePair a
        centeredEvenP0 factorTwoCenteredP8 +
      c2 * factorTwoIntrinsicNinePhasePair a
        centeredEvenP2 factorTwoCenteredP8 +
      c4 * factorTwoIntrinsicNinePhasePair a
        factorTwoCenteredP4 factorTwoCenteredP8) +
    c6 ^ 2 * factorTwoEndpointPhaseDiagonal factorTwoCenteredP6 a +
    2 * c6 * c8 * factorTwoIntrinsicNinePhasePair a
      factorTwoCenteredP6 factorTwoCenteredP8 +
    c8 ^ 2 * factorTwoEndpointPhaseDiagonal factorTwoCenteredP8 a

/-- Exact odd diagonal on the retained degrees `1,3,5,7`. -/
def factorTwoIntrinsicNineDirectOddQuadratic
    (a c1 c3 c5 c7 : ℝ) : ℝ :=
  factorTwoIntrinsicSixStaticOdd (-a) c1 c3 c5 +
    2 * c7 * (c1 * factorTwoIntrinsicNinePhasePair a
        centeredP1 factorTwoCenteredP7 +
      c3 * factorTwoIntrinsicNinePhasePair a
        centeredP3 factorTwoCenteredP7 +
      c5 * factorTwoIntrinsicNinePhasePair a
        factorTwoCenteredP5 factorTwoCenteredP7) +
    c7 ^ 2 * factorTwoEndpointPhaseDiagonal factorTwoCenteredP7 a

/-- Exact alternating block on all retained even--odd pairs. -/
def factorTwoIntrinsicNineDirectAlternating
    (c0 c2 c4 c6 c8 c1 c3 c5 c7 : ℝ) : ℝ :=
  factorTwoIntrinsicSixStaticAlternating c0 c2 c4 c1 c3 c5 +
    c7 * (c0 * factorTwoCenteredAlternatingCoupling
        centeredEvenP0 factorTwoCenteredP7 +
      c2 * factorTwoCenteredAlternatingCoupling
        centeredEvenP2 factorTwoCenteredP7 +
      c4 * factorTwoCenteredAlternatingCoupling
        factorTwoCenteredP4 factorTwoCenteredP7) +
    c6 * (c1 * factorTwoCenteredAlternatingCoupling
        factorTwoCenteredP6 centeredP1 +
      c3 * factorTwoCenteredAlternatingCoupling
        factorTwoCenteredP6 centeredP3 +
      c5 * factorTwoCenteredAlternatingCoupling
        factorTwoCenteredP6 factorTwoCenteredP5) +
    c6 * c7 * factorTwoCenteredAlternatingCoupling
      factorTwoCenteredP6 factorTwoCenteredP7 +
    c8 * (c1 * factorTwoCenteredAlternatingCoupling
        factorTwoCenteredP8 centeredP1 +
      c3 * factorTwoCenteredAlternatingCoupling
        factorTwoCenteredP8 centeredP3 +
      c5 * factorTwoCenteredAlternatingCoupling
        factorTwoCenteredP8 factorTwoCenteredP5) +
    c8 * c7 * factorTwoCenteredAlternatingCoupling
      factorTwoCenteredP8 factorTwoCenteredP7

/-- The balanced cutoff-nine low quadratic in scalar coordinates. -/
def factorTwoIntrinsicNineDirectLowQuadratic
    (a b c0 c2 c4 c1 c3 c5 c6 c8 c7 : ℝ) : ℝ :=
  factorTwoIntrinsicNineDirectEvenQuadratic a c0 c2 c4 c6 c8 +
    factorTwoIntrinsicNineDirectOddQuadratic a c1 c3 c5 c7 +
    b * factorTwoIntrinsicNineDirectAlternating
      c0 c2 c4 c6 c8 c1 c3 c5 c7 -
    (15 / 16 : ℝ) * factorTwoIntrinsicNineP678LowReserve c6 c7 c8

/-- Vector presentation of the direct low quadratic. -/
def factorTwoIntrinsicNineDirectCoordinateQuadratic
    (a b : ℝ) (x : Fin 9 → ℝ) : ℝ :=
  factorTwoIntrinsicNineDirectLowQuadratic a b
    (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8)

/-- Polarization of the displayed direct coordinate quadratic. -/
def factorTwoIntrinsicNineDirectCoordinateBilinear
    (a b : ℝ) (x y : Fin 9 → ℝ) : ℝ :=
  (factorTwoIntrinsicNineDirectCoordinateQuadratic a b (x + y) -
      factorTwoIntrinsicNineDirectCoordinateQuadratic a b x -
    factorTwoIntrinsicNineDirectCoordinateQuadratic a b y) / 2

/-- The exact phase-native balanced low matrix.  Polarization is used only as
an algebraic packaging of the displayed homogeneous coordinate quadratic. -/
def factorTwoIntrinsicNineDirectLowMatrix
    (a b : ℝ) : Matrix (Fin 9) (Fin 9) ℝ :=
  fun i j ↦ factorTwoIntrinsicNineDirectCoordinateBilinear a b
    (factorTwoIntrinsicNineDirectUnit i) (factorTwoIntrinsicNineDirectUnit j)

theorem factorTwoIntrinsicNineDirectLowMatrix_transpose
    (a b : ℝ) :
    (factorTwoIntrinsicNineDirectLowMatrix a b)ᵀ =
      factorTwoIntrinsicNineDirectLowMatrix a b := by
  ext i j
  simp only [transpose_apply, factorTwoIntrinsicNineDirectLowMatrix,
    factorTwoIntrinsicNineDirectCoordinateBilinear]
  rw [add_comm (factorTwoIntrinsicNineDirectUnit j)
    (factorTwoIntrinsicNineDirectUnit i)]
  ring

/-- The displayed coordinate quadratic is the actual retained channel phase
after spending `15 / 16` of the structural `P6/P7/P8` reserve. -/
theorem factorTwoIntrinsicNineDirectLowQuadratic_eq_phase_sub_reserve
    (a b c0 c2 c4 c1 c3 c5 c6 c8 c7 : ℝ) :
    factorTwoIntrinsicNineDirectLowQuadratic a b
        c0 c2 c4 c1 c3 c5 c6 c8 c7 =
      factorTwoEndpointChannelPhase
          (factorTwoIntrinsicNineEvenProfile c0 c2 c4 c6 c8)
          (factorTwoIntrinsicNineOddProfile c1 c3 c5 c7) a b -
        (15 / 16 : ℝ) *
          factorTwoIntrinsicNineP678LowReserve c6 c7 c8 := by
  rw [factorTwoEndpointChannelPhase_eq_diagonals,
    factorTwoEndpointPhaseDiagonal_intrinsicNineEven_eq]
  have hodd := factorTwoEndpointPhaseDiagonal_intrinsicNineOdd_eq
    (-a) c1 c3 c5 c7
  simp only [neg_neg] at hodd
  rw [hodd, factorTwoCenteredAlternatingCoupling_intrinsicNine_eq]
  unfold factorTwoIntrinsicNineDirectLowQuadratic
    factorTwoIntrinsicNineDirectEvenQuadratic
    factorTwoIntrinsicNineDirectOddQuadratic
    factorTwoIntrinsicNineDirectAlternating
  ring

private theorem factorTwoIntrinsicNineDirectCoordinateBilinear_add_left
    (a b : ℝ) (x y z : Fin 9 → ℝ) :
    factorTwoIntrinsicNineDirectCoordinateBilinear a b (x + y) z =
      factorTwoIntrinsicNineDirectCoordinateBilinear a b x z +
        factorTwoIntrinsicNineDirectCoordinateBilinear a b y z := by
  unfold factorTwoIntrinsicNineDirectCoordinateBilinear
    factorTwoIntrinsicNineDirectCoordinateQuadratic
    factorTwoIntrinsicNineDirectLowQuadratic
    factorTwoIntrinsicNineDirectEvenQuadratic
    factorTwoIntrinsicNineDirectOddQuadratic
    factorTwoIntrinsicNineDirectAlternating
    factorTwoIntrinsicSixStaticEven
    factorTwoIntrinsicSixStaticOdd
    factorTwoIntrinsicSixStaticAlternating
    factorTwoIntrinsicOddPhaseQuadratic
    factorTwoIntrinsicNineP678LowReserve
  simp only [Pi.add_apply]
  ring

private theorem factorTwoIntrinsicNineDirectCoordinateBilinear_smul_left
    (a b r : ℝ) (x y : Fin 9 → ℝ) :
    factorTwoIntrinsicNineDirectCoordinateBilinear a b (r • x) y =
      r * factorTwoIntrinsicNineDirectCoordinateBilinear a b x y := by
  unfold factorTwoIntrinsicNineDirectCoordinateBilinear
    factorTwoIntrinsicNineDirectCoordinateQuadratic
    factorTwoIntrinsicNineDirectLowQuadratic
    factorTwoIntrinsicNineDirectEvenQuadratic
    factorTwoIntrinsicNineDirectOddQuadratic
    factorTwoIntrinsicNineDirectAlternating
    factorTwoIntrinsicSixStaticEven
    factorTwoIntrinsicSixStaticOdd
    factorTwoIntrinsicSixStaticAlternating
    factorTwoIntrinsicOddPhaseQuadratic
    factorTwoIntrinsicNineP678LowReserve
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

private theorem factorTwoIntrinsicNineDirectCoordinateBilinear_symm
    (a b : ℝ) (x y : Fin 9 → ℝ) :
    factorTwoIntrinsicNineDirectCoordinateBilinear a b x y =
      factorTwoIntrinsicNineDirectCoordinateBilinear a b y x := by
  unfold factorTwoIntrinsicNineDirectCoordinateBilinear
  rw [add_comm x y]
  ring

private theorem factorTwoIntrinsicNineDirectCoordinateBilinear_add_right
    (a b : ℝ) (x y z : Fin 9 → ℝ) :
    factorTwoIntrinsicNineDirectCoordinateBilinear a b x (y + z) =
      factorTwoIntrinsicNineDirectCoordinateBilinear a b x y +
        factorTwoIntrinsicNineDirectCoordinateBilinear a b x z := by
  rw [factorTwoIntrinsicNineDirectCoordinateBilinear_symm,
    factorTwoIntrinsicNineDirectCoordinateBilinear_add_left,
    factorTwoIntrinsicNineDirectCoordinateBilinear_symm a b y x,
    factorTwoIntrinsicNineDirectCoordinateBilinear_symm a b z x]

private theorem factorTwoIntrinsicNineDirectCoordinateBilinear_smul_right
    (a b r : ℝ) (x y : Fin 9 → ℝ) :
    factorTwoIntrinsicNineDirectCoordinateBilinear a b x (r • y) =
      r * factorTwoIntrinsicNineDirectCoordinateBilinear a b x y := by
  rw [factorTwoIntrinsicNineDirectCoordinateBilinear_symm,
    factorTwoIntrinsicNineDirectCoordinateBilinear_smul_left,
    factorTwoIntrinsicNineDirectCoordinateBilinear_symm a b y x]

private theorem factorTwoIntrinsicNineDirectCoordinateBilinear_self
    (a b : ℝ) (x : Fin 9 → ℝ) :
    factorTwoIntrinsicNineDirectCoordinateBilinear a b x x =
      factorTwoIntrinsicNineDirectCoordinateQuadratic a b x := by
  unfold factorTwoIntrinsicNineDirectCoordinateBilinear
    factorTwoIntrinsicNineDirectCoordinateQuadratic
    factorTwoIntrinsicNineDirectLowQuadratic
    factorTwoIntrinsicNineDirectEvenQuadratic
    factorTwoIntrinsicNineDirectOddQuadratic
    factorTwoIntrinsicNineDirectAlternating
    factorTwoIntrinsicSixStaticEven
    factorTwoIntrinsicSixStaticOdd
    factorTwoIntrinsicSixStaticAlternating
    factorTwoIntrinsicOddPhaseQuadratic
    factorTwoIntrinsicNineP678LowReserve
  simp only [Pi.add_apply]
  ring

private theorem factorTwoIntrinsicNineDirectCoordinateBilinear_zero_left
    (a b : ℝ) (y : Fin 9 → ℝ) :
    factorTwoIntrinsicNineDirectCoordinateBilinear a b 0 y = 0 := by
  have h := factorTwoIntrinsicNineDirectCoordinateBilinear_smul_left
    a b 0 (0 : Fin 9 → ℝ) y
  simpa using h

private theorem factorTwoIntrinsicNineDirectCoordinateBilinear_sum_left
    {ι : Type*} [DecidableEq ι]
    (a b : ℝ) (s : Finset ι) (f : ι → Fin 9 → ℝ) (y : Fin 9 → ℝ) :
    factorTwoIntrinsicNineDirectCoordinateBilinear a b (∑ i ∈ s, f i) y =
      ∑ i ∈ s, factorTwoIntrinsicNineDirectCoordinateBilinear a b (f i) y := by
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact factorTwoIntrinsicNineDirectCoordinateBilinear_zero_left a b y
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi,
        factorTwoIntrinsicNineDirectCoordinateBilinear_add_left,
        ih, Finset.sum_insert hi]

private theorem factorTwoIntrinsicNineDirectCoordinateBilinear_sum_right
    {ι : Type*} [DecidableEq ι]
    (a b : ℝ) (x : Fin 9 → ℝ) (s : Finset ι) (f : ι → Fin 9 → ℝ) :
    factorTwoIntrinsicNineDirectCoordinateBilinear a b x (∑ i ∈ s, f i) =
      ∑ i ∈ s, factorTwoIntrinsicNineDirectCoordinateBilinear a b x (f i) := by
  rw [factorTwoIntrinsicNineDirectCoordinateBilinear_symm,
    factorTwoIntrinsicNineDirectCoordinateBilinear_sum_left]
  apply Finset.sum_congr rfl
  intro i _hi
  exact factorTwoIntrinsicNineDirectCoordinateBilinear_symm a b (f i) x

private theorem factorTwoIntrinsicNine_sum_single
    (x : Fin 9 → ℝ) :
    (∑ i, x i • factorTwoIntrinsicNineDirectUnit i) = x := by
  funext j
  simp [factorTwoIntrinsicNineDirectUnit, Pi.single_apply]

/-- Exact quadratic-form identity for the direct matrix. -/
theorem factorTwoIntrinsicNineDirectLowMatrix_quadratic
    (a b : ℝ) (x : Fin 9 → ℝ) :
    x ⬝ᵥ (factorTwoIntrinsicNineDirectLowMatrix a b *ᵥ x) =
      factorTwoIntrinsicNineDirectCoordinateQuadratic a b x := by
  classical
  simp only [dotProduct, mulVec, factorTwoIntrinsicNineDirectLowMatrix]
  calc
    (∑ i, x i * ∑ j,
        factorTwoIntrinsicNineDirectCoordinateBilinear a b
          (factorTwoIntrinsicNineDirectUnit i)
          (factorTwoIntrinsicNineDirectUnit j) * x j) =
      ∑ i, ∑ j,
        factorTwoIntrinsicNineDirectCoordinateBilinear a b
          (x i • factorTwoIntrinsicNineDirectUnit i)
          (x j • factorTwoIntrinsicNineDirectUnit j) := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _hj
        rw [factorTwoIntrinsicNineDirectCoordinateBilinear_smul_left,
          factorTwoIntrinsicNineDirectCoordinateBilinear_smul_right]
        ring
    _ = factorTwoIntrinsicNineDirectCoordinateBilinear a b
        (∑ i, x i • factorTwoIntrinsicNineDirectUnit i)
        (∑ j, x j • factorTwoIntrinsicNineDirectUnit j) := by
      rw [factorTwoIntrinsicNineDirectCoordinateBilinear_sum_left]
      apply Finset.sum_congr rfl
      intro i _hi
      exact (factorTwoIntrinsicNineDirectCoordinateBilinear_sum_right
        a b (x i • factorTwoIntrinsicNineDirectUnit i) Finset.univ
          (fun j ↦ x j • factorTwoIntrinsicNineDirectUnit j)).symm
    _ = factorTwoIntrinsicNineDirectCoordinateBilinear a b x x := by
      simp only [factorTwoIntrinsicNine_sum_single]
    _ = factorTwoIntrinsicNineDirectCoordinateQuadratic a b x :=
      factorTwoIntrinsicNineDirectCoordinateBilinear_self a b x

/-- Final semantic matrix identity in the requested coordinate order. -/
theorem factorTwoIntrinsicNineDirectLowMatrix_quadratic_eq_phase_sub_reserve
    (a b : ℝ) (x : Fin 9 → ℝ) :
    x ⬝ᵥ (factorTwoIntrinsicNineDirectLowMatrix a b *ᵥ x) =
      factorTwoEndpointChannelPhase
          (factorTwoIntrinsicNineEvenProfile (x 0) (x 1) (x 2) (x 6) (x 7))
          (factorTwoIntrinsicNineOddProfile (x 3) (x 4) (x 5) (x 8)) a b -
        (15 / 16 : ℝ) *
          factorTwoIntrinsicNineP678LowReserve (x 6) (x 8) (x 7) := by
  rw [factorTwoIntrinsicNineDirectLowMatrix_quadratic]
  exact factorTwoIntrinsicNineDirectLowQuadratic_eq_phase_sub_reserve
    a b (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8)

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectMatrixStructural

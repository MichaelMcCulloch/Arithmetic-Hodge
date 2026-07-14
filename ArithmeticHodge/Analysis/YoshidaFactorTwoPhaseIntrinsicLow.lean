import ArithmeticHodge.Analysis.YoshidaEndpointOddLowGramExpansion
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseOddStructuralPerturbation

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLow

noncomputable section

open CenteredOddOneThreeEnergy
open YoshidaEndpointEvenExactLowGramPositive
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointOddFullPolarization
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointOddLowGramExpansion
open YoshidaEndpointOddResidualRegularity
open YoshidaEndpointOcticPotential
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointChannelRadius
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoEndpointParityPencil
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoPhaseOddStructuralPerturbation
open TwoByTwoSchur

/-!
# The intrinsic four-mode phase block

The complete `P₀/P₂`--`P₁/P₃` phase is a genuine `2 x 2` block pencil.
For fixed symmetric phase coordinate `a`, its even and odd diagonal blocks
are affine `2 x 2` pencils and the alternating coordinate `b` multiplies a
fixed cross block.

The structural closure below does not inspect phase values.  It first takes
the exact Schur complement of the even block.  On the boundary
`b² = 1 - a²`, the remaining odd quadratic is a cubic in
`x = (1-a)/2`; its degree-three Bernstein form is a convex combination of
four fixed intrinsic quadratic forms.  Inside the disk, the adjugate penalty
can only decrease.
-/

/-! ## Exact scalar entries -/

/-- The phase-dependent `P₁,P₁` entry of the odd low block. -/
def factorTwoIntrinsicOddPhaseLow11 (a : ℝ) : ℝ :=
  yoshidaEndpointOddLowGram11 +
    a * factorTwoCenteredSymmetricPerturbation centeredP1

/-- The phase-dependent `P₁,P₃` entry of the odd low block. -/
def factorTwoIntrinsicOddPhaseLow13 (a : ℝ) : ℝ :=
  yoshidaEndpointOddLowGram13 +
    a * factorTwoCenteredSymmetricPerturbationBilinear
      centeredP1 centeredP3

/-- The phase-dependent `P₃,P₃` entry of the odd low block. -/
def factorTwoIntrinsicOddPhaseLow33 (a : ℝ) : ℝ :=
  yoshidaEndpointOddLowGram33 +
    a * factorTwoCenteredSymmetricPerturbation centeredP3

/-- The four entries of the fixed even--odd alternating block. -/
def factorTwoIntrinsicAlternating01 : ℝ :=
  factorTwoCenteredAlternatingCoupling centeredEvenP0 centeredP1

def factorTwoIntrinsicAlternating03 : ℝ :=
  factorTwoCenteredAlternatingCoupling centeredEvenP0 centeredP3

def factorTwoIntrinsicAlternating21 : ℝ :=
  factorTwoCenteredAlternatingCoupling centeredEvenP2 centeredP1

def factorTwoIntrinsicAlternating23 : ℝ :=
  factorTwoCenteredAlternatingCoupling centeredEvenP2 centeredP3

/-- The odd diagonal quadratic at symmetric phase `a`. -/
def factorTwoIntrinsicOddPhaseQuadratic
    (a c1 c3 : ℝ) : ℝ :=
  factorTwoIntrinsicOddPhaseLow11 a * c1 ^ 2 +
    2 * factorTwoIntrinsicOddPhaseLow13 a * c1 * c3 +
    factorTwoIntrinsicOddPhaseLow33 a * c3 ^ 2

/-- The two alternating coordinates obtained after fixing the odd
coefficients.  The factor `b / 2` is deliberately not included here. -/
def factorTwoIntrinsicAlternatingRow0 (c1 c3 : ℝ) : ℝ :=
  factorTwoIntrinsicAlternating01 * c1 +
    factorTwoIntrinsicAlternating03 * c3

def factorTwoIntrinsicAlternatingRow2 (c1 c3 : ℝ) : ℝ :=
  factorTwoIntrinsicAlternating21 * c1 +
    factorTwoIntrinsicAlternating23 * c3

/-- Exact expansion of the complete intrinsic four-mode phase. -/
theorem factorTwoEndpointChannelPhase_intrinsicLow_expansion
    (c0 c2 c1 c3 a b : ℝ) :
    factorTwoEndpointChannelPhase
        (factorTwoEvenStructuralLowProfile c0 c2)
        (factorTwoOddStructuralLowProfile c1 c3) a b =
      factorTwoStructuralPhaseLow00 a * c0 ^ 2 +
        2 * factorTwoStructuralPhaseLow02 a * c0 * c2 +
        factorTwoStructuralPhaseLow22 a * c2 ^ 2 +
        factorTwoIntrinsicOddPhaseQuadratic a c1 c3 +
        b * (c0 * factorTwoIntrinsicAlternatingRow0 c1 c3 +
          c2 * factorTwoIntrinsicAlternatingRow2 c1 c3) := by
  have heClean := yoshidaEndpointEvenLowGram_quadratic_eq_clean c0 c2
  have heClean' :
      yoshidaEndpointOddCleanQuadratic
          (factorTwoEvenStructuralLowProfile c0 c2) =
        yoshidaEndpointEvenLowGram00 * c0 ^ 2 +
          2 * yoshidaEndpointEvenLowGram02 * c0 * c2 +
          yoshidaEndpointEvenLowGram22 * c2 ^ 2 := by
    simpa only [factorTwoEvenStructuralLowProfile] using heClean
  have hoClean := yoshidaEndpointOddLowGram_quadratic c1 c3
  have heSymm :=
    factorTwoCenteredSymmetricPerturbation_structuralLow c0 c2
  have hoSymm :=
    factorTwoCenteredSymmetricPerturbation_oddStructuralLow c1 c3
  have hAltEven := factorTwoCenteredAlternatingCoupling_structuralLow
    c0 c2 (factorTwoOddStructuralLowProfile c1 c3)
      (continuous_factorTwoOddStructuralLowProfile c1 c3)
  have hAlt0 :=
    factorTwoCenteredAlternatingCoupling_oddStructuralLow_right
      centeredEvenP0 (by unfold centeredEvenP0; fun_prop) c1 c3
  have hAlt2 :=
    factorTwoCenteredAlternatingCoupling_oddStructuralLow_right
      centeredEvenP2 (by unfold centeredEvenP2; fun_prop) c1 c3
  unfold factorTwoEndpointChannelPhase factorTwoEndpointChannelCleanSum
    factorTwoEndpointChannelSymmetricSum
    factorTwoStructuralPhaseLow00 factorTwoStructuralPhaseLow02
    factorTwoStructuralPhaseLow22
    factorTwoIntrinsicOddPhaseQuadratic
    factorTwoIntrinsicOddPhaseLow11 factorTwoIntrinsicOddPhaseLow13
    factorTwoIntrinsicOddPhaseLow33
    factorTwoIntrinsicAlternatingRow0 factorTwoIntrinsicAlternatingRow2
    factorTwoIntrinsicAlternating01 factorTwoIntrinsicAlternating03
    factorTwoIntrinsicAlternating21 factorTwoIntrinsicAlternating23
  rw [heClean', hoClean, heSymm, hoSymm, hAltEven, hAlt0, hAlt2]
  ring

/-! ## Exact even-block Schur complement -/

/-- Determinant of the affine intrinsic even block. -/
def factorTwoIntrinsicEvenPhaseDet (a : ℝ) : ℝ :=
  factorTwoStructuralPhaseLow00 a * factorTwoStructuralPhaseLow22 a -
    factorTwoStructuralPhaseLow02 a ^ 2

/-- The adjugate quadratic evaluated on the two alternating rows. -/
def factorTwoIntrinsicEvenAdjugateCoupling
    (a c1 c3 : ℝ) : ℝ :=
  factorTwoStructuralPhaseLow22 a *
      factorTwoIntrinsicAlternatingRow0 c1 c3 ^ 2 -
    2 * factorTwoStructuralPhaseLow02 a *
      factorTwoIntrinsicAlternatingRow0 c1 c3 *
      factorTwoIntrinsicAlternatingRow2 c1 c3 +
    factorTwoStructuralPhaseLow00 a *
      factorTwoIntrinsicAlternatingRow2 c1 c3 ^ 2

/-- A positive definite `2 x 2` form has a nonnegative adjugate form. -/
theorem twoByTwo_adjugateQuadratic_nonneg
    (q00 q02 q22 l0 l2 : ℝ)
    (h00 : 0 < q00) (hdet : 0 < q00 * q22 - q02 ^ 2) :
    0 ≤ q22 * l0 ^ 2 - 2 * q02 * l0 * l2 + q00 * l2 ^ 2 := by
  have hid :
      q00 * (q22 * l0 ^ 2 - 2 * q02 * l0 * l2 + q00 * l2 ^ 2) =
        (q00 * l2 - q02 * l0) ^ 2 +
          (q00 * q22 - q02 ^ 2) * l0 ^ 2 := by
    ring
  have hscaled : 0 ≤ q00 *
      (q22 * l0 ^ 2 - 2 * q02 * l0 * l2 + q00 * l2 ^ 2) := by
    rw [hid]
    exact add_nonneg (sq_nonneg _)
      (mul_nonneg hdet.le (sq_nonneg _))
  nlinarith

/-- Boundary Schur residual of the odd block after eliminating the even
block. -/
def factorTwoIntrinsicBoundarySchurResidual
    (a c1 c3 : ℝ) : ℝ :=
  factorTwoIntrinsicEvenPhaseDet a *
      factorTwoIntrinsicOddPhaseQuadratic a c1 c3 -
    ((1 - a ^ 2) / 4) *
      factorTwoIntrinsicEvenAdjugateCoupling a c1 c3

/-- Exact disk closure from the boundary Schur residual.  The passage from
`b² = 1-a²` to `b² ≤ 1-a²` is monotone because the even adjugate quadratic
is nonnegative. -/
theorem factorTwoEndpointChannelPhase_intrinsicLow_nonneg_of_boundarySchur
    (c0 c2 c1 c3 a b : ℝ)
    (hab : a ^ 2 + b ^ 2 ≤ 1)
    (h00 : 0 < factorTwoStructuralPhaseLow00 a)
    (hdet : 0 < factorTwoIntrinsicEvenPhaseDet a)
    (hboundary : 0 ≤
      factorTwoIntrinsicBoundarySchurResidual a c1 c3) :
    0 ≤ factorTwoEndpointChannelPhase
      (factorTwoEvenStructuralLowProfile c0 c2)
      (factorTwoOddStructuralLowProfile c1 c3) a b := by
  let j0 := factorTwoIntrinsicAlternatingRow0 c1 c3
  let j2 := factorTwoIntrinsicAlternatingRow2 c1 c3
  let A := factorTwoIntrinsicEvenAdjugateCoupling a c1 c3
  let O := factorTwoIntrinsicOddPhaseQuadratic a c1 c3
  let D := factorTwoIntrinsicEvenPhaseDet a
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact twoByTwo_adjugateQuadratic_nonneg
      (factorTwoStructuralPhaseLow00 a)
      (factorTwoStructuralPhaseLow02 a)
      (factorTwoStructuralPhaseLow22 a) j0 j2 h00 (by
        simpa only [factorTwoIntrinsicEvenPhaseDet] using hdet)
  have hbsq : b ^ 2 ≤ 1 - a ^ 2 := by nlinarith
  have hboundary' : ((1 - a ^ 2) / 4) * A ≤ D * O := by
    dsimp only [factorTwoIntrinsicBoundarySchurResidual] at hboundary
    dsimp only [A, O, D]
    linarith
  have hactual : (b ^ 2 / 4) * A ≤ D * O := by
    have hfour : (0 : ℝ) ≤ 4 := by norm_num
    have hscaled := mul_le_mul_of_nonneg_right hbsq hA
    nlinarith
  have hschur :
      factorTwoStructuralPhaseLow22 a * ((b / 2) * j0) ^ 2 -
          2 * factorTwoStructuralPhaseLow02 a *
            ((b / 2) * j0) * ((b / 2) * j2) +
        factorTwoStructuralPhaseLow00 a * ((b / 2) * j2) ^ 2 ≤
      (factorTwoStructuralPhaseLow00 a *
          factorTwoStructuralPhaseLow22 a -
        factorTwoStructuralPhaseLow02 a ^ 2) * O := by
    dsimp only [j0, j2, A, D, O] at hactual ⊢
    calc
      _ = (b ^ 2 / 4) *
          factorTwoIntrinsicEvenAdjugateCoupling a c1 c3 := by
        unfold factorTwoIntrinsicEvenAdjugateCoupling
        ring
      _ ≤ factorTwoIntrinsicEvenPhaseDet a *
          factorTwoIntrinsicOddPhaseQuadratic a c1 c3 := hactual
      _ = _ := by
        unfold factorTwoIntrinsicEvenPhaseDet
        rfl
  have hresult := quadratic_add_tail_nonneg
    (factorTwoStructuralPhaseLow00 a)
    (factorTwoStructuralPhaseLow02 a)
    (factorTwoStructuralPhaseLow22 a)
    ((b / 2) * j0) ((b / 2) * j2) O c0 c2 h00
    (by simpa only [factorTwoIntrinsicEvenPhaseDet] using hdet) hschur
  rw [factorTwoEndpointChannelPhase_intrinsicLow_expansion]
  dsimp only [j0, j2, O] at hresult
  nlinarith

/-! ## Bernstein factorization of the boundary residual -/

/-- Direction of the even pencil when `a = 1 - 2x`. -/
def factorTwoIntrinsicEvenDirection00 : ℝ :=
  -2 * factorTwoCenteredSymmetricPerturbation centeredEvenP0

def factorTwoIntrinsicEvenDirection02 : ℝ :=
  -2 * factorTwoCenteredSymmetricPerturbationBilinear
    centeredEvenP0 centeredEvenP2

def factorTwoIntrinsicEvenDirection22 : ℝ :=
  -2 * factorTwoCenteredSymmetricPerturbation centeredEvenP2

/-- Direction of the odd pencil when `a = 1 - 2x`. -/
def factorTwoIntrinsicOddDirectionQuadratic (c1 c3 : ℝ) : ℝ :=
  (-2 * factorTwoCenteredSymmetricPerturbation centeredP1) * c1 ^ 2 +
    2 * (-2 * factorTwoCenteredSymmetricPerturbationBilinear
      centeredP1 centeredP3) * c1 * c3 +
    (-2 * factorTwoCenteredSymmetricPerturbation centeredP3) * c3 ^ 2

/-- Constant, linear, and quadratic coefficients of the even determinant
in `x = (1-a)/2`. -/
def factorTwoIntrinsicEvenDetCoefficient0 : ℝ :=
  factorTwoIntrinsicEvenPhaseDet 1

def factorTwoIntrinsicEvenDetCoefficient1 : ℝ :=
  factorTwoStructuralPhaseLow00 1 * factorTwoIntrinsicEvenDirection22 +
    factorTwoIntrinsicEvenDirection00 * factorTwoStructuralPhaseLow22 1 -
    2 * factorTwoStructuralPhaseLow02 1 *
      factorTwoIntrinsicEvenDirection02

def factorTwoIntrinsicEvenDetCoefficient2 : ℝ :=
  factorTwoIntrinsicEvenDirection00 * factorTwoIntrinsicEvenDirection22 -
    factorTwoIntrinsicEvenDirection02 ^ 2

/-- The affine coefficients of the even adjugate penalty. -/
def factorTwoIntrinsicAdjugateCoefficient0 (c1 c3 : ℝ) : ℝ :=
  factorTwoIntrinsicEvenAdjugateCoupling 1 c1 c3

def factorTwoIntrinsicAdjugateCoefficient1 (c1 c3 : ℝ) : ℝ :=
  factorTwoIntrinsicEvenDirection22 *
      factorTwoIntrinsicAlternatingRow0 c1 c3 ^ 2 -
    2 * factorTwoIntrinsicEvenDirection02 *
      factorTwoIntrinsicAlternatingRow0 c1 c3 *
      factorTwoIntrinsicAlternatingRow2 c1 c3 +
    factorTwoIntrinsicEvenDirection00 *
      factorTwoIntrinsicAlternatingRow2 c1 c3 ^ 2

/-- Power-basis coefficients of the cubic boundary Schur residual. -/
def factorTwoIntrinsicBoundaryPower0 (c1 c3 : ℝ) : ℝ :=
  factorTwoIntrinsicEvenDetCoefficient0 *
    factorTwoIntrinsicOddPhaseQuadratic 1 c1 c3

def factorTwoIntrinsicBoundaryPower1 (c1 c3 : ℝ) : ℝ :=
  factorTwoIntrinsicEvenDetCoefficient0 *
      factorTwoIntrinsicOddDirectionQuadratic c1 c3 +
    factorTwoIntrinsicEvenDetCoefficient1 *
      factorTwoIntrinsicOddPhaseQuadratic 1 c1 c3 -
    factorTwoIntrinsicAdjugateCoefficient0 c1 c3

def factorTwoIntrinsicBoundaryPower2 (c1 c3 : ℝ) : ℝ :=
  factorTwoIntrinsicEvenDetCoefficient1 *
      factorTwoIntrinsicOddDirectionQuadratic c1 c3 +
    factorTwoIntrinsicEvenDetCoefficient2 *
      factorTwoIntrinsicOddPhaseQuadratic 1 c1 c3 +
    factorTwoIntrinsicAdjugateCoefficient0 c1 c3 -
    factorTwoIntrinsicAdjugateCoefficient1 c1 c3

def factorTwoIntrinsicBoundaryPower3 (c1 c3 : ℝ) : ℝ :=
  factorTwoIntrinsicEvenDetCoefficient2 *
      factorTwoIntrinsicOddDirectionQuadratic c1 c3 +
    factorTwoIntrinsicAdjugateCoefficient1 c1 c3

/-- The four degree-three Bernstein control quadratics. -/
def factorTwoIntrinsicBoundaryControl0 (c1 c3 : ℝ) : ℝ :=
  factorTwoIntrinsicBoundaryPower0 c1 c3

def factorTwoIntrinsicBoundaryControl1 (c1 c3 : ℝ) : ℝ :=
  factorTwoIntrinsicBoundaryPower0 c1 c3 +
    factorTwoIntrinsicBoundaryPower1 c1 c3 / 3

def factorTwoIntrinsicBoundaryControl2 (c1 c3 : ℝ) : ℝ :=
  factorTwoIntrinsicBoundaryPower0 c1 c3 +
    2 * factorTwoIntrinsicBoundaryPower1 c1 c3 / 3 +
    factorTwoIntrinsicBoundaryPower2 c1 c3 / 3

def factorTwoIntrinsicBoundaryControl3 (c1 c3 : ℝ) : ℝ :=
  factorTwoIntrinsicBoundaryPower0 c1 c3 +
    factorTwoIntrinsicBoundaryPower1 c1 c3 +
    factorTwoIntrinsicBoundaryPower2 c1 c3 +
    factorTwoIntrinsicBoundaryPower3 c1 c3

/-- The first Bernstein control is exactly the decoupled `a = 1`
endpoint Schur form. -/
theorem factorTwoIntrinsicBoundaryControl0_eq_endpoint
    (c1 c3 : ℝ) :
    factorTwoIntrinsicBoundaryControl0 c1 c3 =
      factorTwoIntrinsicEvenPhaseDet 1 *
        factorTwoIntrinsicOddPhaseQuadratic 1 c1 c3 := by
  rfl

/-- The last Bernstein control is exactly the decoupled `a = -1`
endpoint Schur form.  The alternating penalty vanishes at both endpoints. -/
theorem factorTwoIntrinsicBoundaryControl3_eq_endpoint
    (c1 c3 : ℝ) :
    factorTwoIntrinsicBoundaryControl3 c1 c3 =
      factorTwoIntrinsicEvenPhaseDet (-1) *
        factorTwoIntrinsicOddPhaseQuadratic (-1) c1 c3 := by
  unfold factorTwoIntrinsicBoundaryControl3
    factorTwoIntrinsicBoundaryPower0 factorTwoIntrinsicBoundaryPower1
    factorTwoIntrinsicBoundaryPower2 factorTwoIntrinsicBoundaryPower3
    factorTwoIntrinsicEvenDetCoefficient0
    factorTwoIntrinsicEvenDetCoefficient1
    factorTwoIntrinsicEvenDetCoefficient2
    factorTwoIntrinsicAdjugateCoefficient0
    factorTwoIntrinsicAdjugateCoefficient1
    factorTwoIntrinsicOddDirectionQuadratic
    factorTwoIntrinsicEvenDirection00 factorTwoIntrinsicEvenDirection02
    factorTwoIntrinsicEvenDirection22
    factorTwoIntrinsicEvenPhaseDet
    factorTwoIntrinsicOddPhaseQuadratic
    factorTwoIntrinsicOddPhaseLow11 factorTwoIntrinsicOddPhaseLow13
    factorTwoIntrinsicOddPhaseLow33
    factorTwoStructuralPhaseLow00 factorTwoStructuralPhaseLow02
    factorTwoStructuralPhaseLow22
  ring

/-- Exact cubic Bernstein identity for the boundary Schur residual. -/
theorem factorTwoIntrinsicBoundarySchurResidual_eq_bernstein
    (a c1 c3 : ℝ) :
    let x := (1 - a) / 2
    factorTwoIntrinsicBoundarySchurResidual a c1 c3 =
      (1 - x) ^ 3 * factorTwoIntrinsicBoundaryControl0 c1 c3 +
        3 * x * (1 - x) ^ 2 *
          factorTwoIntrinsicBoundaryControl1 c1 c3 +
        3 * x ^ 2 * (1 - x) *
          factorTwoIntrinsicBoundaryControl2 c1 c3 +
        x ^ 3 * factorTwoIntrinsicBoundaryControl3 c1 c3 := by
  dsimp only
  simp only [factorTwoIntrinsicBoundaryControl0,
    factorTwoIntrinsicBoundaryControl1,
    factorTwoIntrinsicBoundaryControl2,
    factorTwoIntrinsicBoundaryControl3,
    factorTwoIntrinsicBoundaryPower0, factorTwoIntrinsicBoundaryPower1,
    factorTwoIntrinsicBoundaryPower2, factorTwoIntrinsicBoundaryPower3,
    factorTwoIntrinsicEvenDetCoefficient0,
    factorTwoIntrinsicEvenDetCoefficient1,
    factorTwoIntrinsicEvenDetCoefficient2,
    factorTwoIntrinsicAdjugateCoefficient0,
    factorTwoIntrinsicAdjugateCoefficient1,
    factorTwoIntrinsicEvenDirection00, factorTwoIntrinsicEvenDirection02,
    factorTwoIntrinsicEvenDirection22,
    factorTwoIntrinsicOddDirectionQuadratic,
    factorTwoIntrinsicBoundarySchurResidual,
    factorTwoIntrinsicEvenPhaseDet,
    factorTwoIntrinsicEvenAdjugateCoupling,
    factorTwoIntrinsicOddPhaseQuadratic,
    factorTwoIntrinsicOddPhaseLow11, factorTwoIntrinsicOddPhaseLow13,
    factorTwoIntrinsicOddPhaseLow33,
    factorTwoStructuralPhaseLow00, factorTwoStructuralPhaseLow02,
    factorTwoStructuralPhaseLow22]
  ring

/-- Nonnegativity of all four fixed control quadratics implies
nonnegativity of the boundary Schur residual throughout `[-1,1]`. -/
theorem factorTwoIntrinsicBoundarySchurResidual_nonneg_of_controls
    (a c1 c3 : ℝ) (haLower : -1 ≤ a) (haUpper : a ≤ 1)
    (h0 : 0 ≤ factorTwoIntrinsicBoundaryControl0 c1 c3)
    (h1 : 0 ≤ factorTwoIntrinsicBoundaryControl1 c1 c3)
    (h2 : 0 ≤ factorTwoIntrinsicBoundaryControl2 c1 c3)
    (h3 : 0 ≤ factorTwoIntrinsicBoundaryControl3 c1 c3) :
    0 ≤ factorTwoIntrinsicBoundarySchurResidual a c1 c3 := by
  have hx0 : 0 ≤ (1 - a) / 2 := by linarith
  have hx1 : 0 ≤ 1 - (1 - a) / 2 := by linarith
  rw [factorTwoIntrinsicBoundarySchurResidual_eq_bernstein]
  positivity

/-- Final structural four-mode closure.  The only fixed obligations are the
two signed endpoint certificates for the even block and nonnegativity of the
four Bernstein control quadratics. -/
theorem factorTwoEndpointChannelPhase_intrinsicLow_nonneg_of_controls
    (c0 c2 c1 c3 a b : ℝ)
    (hab : a ^ 2 + b ^ 2 ≤ 1)
    (hplus00 : 0 < factorTwoStructuralPhaseLow00 1)
    (hplusDet : 0 < factorTwoIntrinsicEvenPhaseDet 1)
    (hminus00 : 0 < factorTwoStructuralPhaseLow00 (-1))
    (hminusDet : 0 < factorTwoIntrinsicEvenPhaseDet (-1))
    (h0 : 0 ≤ factorTwoIntrinsicBoundaryControl0 c1 c3)
    (h1 : 0 ≤ factorTwoIntrinsicBoundaryControl1 c1 c3)
    (h2 : 0 ≤ factorTwoIntrinsicBoundaryControl2 c1 c3)
    (h3 : 0 ≤ factorTwoIntrinsicBoundaryControl3 c1 c3) :
    0 ≤ factorTwoEndpointChannelPhase
      (factorTwoEvenStructuralLowProfile c0 c2)
      (factorTwoOddStructuralLowProfile c1 c3) a b := by
  have haLower : -1 ≤ a := by
    nlinarith [sq_nonneg b, sq_nonneg (a + 1)]
  have haUpper : a ≤ 1 := by
    nlinarith [sq_nonneg b, sq_nonneg (a - 1)]
  have heven := factorTwoStructuralPhaseLow_pos_of_endpoint_certificates
    a b hab hplus00 (by
      simpa only [factorTwoIntrinsicEvenPhaseDet] using hplusDet)
      hminus00 (by
        simpa only [factorTwoIntrinsicEvenPhaseDet] using hminusDet)
  exact factorTwoEndpointChannelPhase_intrinsicLow_nonneg_of_boundarySchur
    c0 c2 c1 c3 a b hab heven.1
      (by simpa only [factorTwoIntrinsicEvenPhaseDet] using heven.2)
      (factorTwoIntrinsicBoundarySchurResidual_nonneg_of_controls
        a c1 c3 haLower haUpper h0 h1 h2 h3)

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLow

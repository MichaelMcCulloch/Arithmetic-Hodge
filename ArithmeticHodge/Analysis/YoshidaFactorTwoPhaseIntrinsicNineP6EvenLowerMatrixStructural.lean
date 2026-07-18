import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineP6EvenCleanPolynomialGramStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineP6EvenEndpointLowerModelStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineP6EvenHyperbolicStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineP6EvenPerturbationGramStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineP6EvenProfileCorrelationStructural

set_option autoImplicit false

open Complex Matrix MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineP6EvenLowerMatrixStructural

noncomputable section

open YoshidaEndpointHyperbolicBound
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoPhaseDiskSchur
open YoshidaFactorTwoPhaseIntrinsicNineP6EvenCleanPolynomialGramStructural
open YoshidaFactorTwoPhaseIntrinsicNineP6EvenEndpointLowerModelStructural
open YoshidaFactorTwoPhaseIntrinsicNineP6EvenHyperbolicStructural
open YoshidaFactorTwoPhaseIntrinsicNineP6EvenPerturbationGramStructural
open YoshidaFactorTwoPhaseIntrinsicNineP6EvenProfileCorrelationStructural
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFactorTwoPhaseIntrinsicSixP4EndpointProfile
open YoshidaFactorTwoPhaseIntrinsicSixSchurReduction
open YoshidaFactorTwoPhaseLowSchur

/-!
# Structural lower matrices on the `P0/P2/P4/P6` block

The exact endpoint hyperbolic term is replaced by the globally valid retained
degree-six rank-one term.  Everything else is kept in the endpoint polynomial
lower model.  Thus the two coefficient quadratics below are honest lower
bounds for the two actual endpoint phase diagonals; no sampled or exhaustive
calculation occurs here.
-/

/-- The exact diagonal energy coordinate of the four retained even modes. -/
def factorTwoP6EvenCoefficientEnergy
    (c0 c2 c4 c6 : ℝ) : ℝ :=
  2 * c0 ^ 2 + (2 / 5 : ℝ) * c2 ^ 2 +
    (2 / 9 : ℝ) * c4 ^ 2 + (2 / 13 : ℝ) * c6 ^ 2

/-- The retained rank-one hyperbolic lower term, including its single global
Taylor-error energy charge. -/
def factorTwoP6EvenRetainedHyperbolicLower
    (c0 c2 c4 c6 : ℝ) : ℝ :=
  yoshidaEndpointA *
      factorTwoIntrinsicP0246CoshPolynomialMoment c0 c2 c4 c6 ^ 2 -
    4 * yoshidaEndpointA * (1 / 48000000000 : ℝ) ^ 2 *
      factorTwoP6EvenCoefficientEnergy c0 c2 c4 c6

/-- Coefficient-level lower quadratic for the positive endpoint sign. -/
def factorTwoP6EvenPlusLowerQuadratic
    (c0 c2 c4 c6 : ℝ) : ℝ :=
  let e := factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6
  factorTwoP6EvenEndpointPlusLowerModel e -
      yoshidaEndpointHyperbolicQuadratic (fun x ↦ (e x : ℂ)) +
    factorTwoP6EvenRetainedHyperbolicLower c0 c2 c4 c6

/-- Coefficient-level lower quadratic for the negative endpoint sign. -/
def factorTwoP6EvenMinusLowerQuadratic
    (c0 c2 c4 c6 : ℝ) : ℝ :=
  let e := factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6
  factorTwoP6EvenEndpointMinusLowerModel e -
      yoshidaEndpointHyperbolicQuadratic (fun x ↦ (e x : ℂ)) +
    factorTwoP6EvenRetainedHyperbolicLower c0 c2 c4 c6

theorem factorTwoIntrinsicEvenP0246Profile_eq_hyperbolicProfile
    (c0 c2 c4 c6 : ℝ) :
    factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6 =
      factorTwoIntrinsicP0246Profile c0 c2 c4 c6 := by
  funext x
  unfold factorTwoIntrinsicEvenP0246Profile
    factorTwoIntrinsicEvenP024Profile factorTwoIntrinsicSixEvenTail
    factorTwoEvenStructuralLowProfile factorTwoIntrinsicP0246Profile
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]

/-! ## Four-coordinate polarization -/

/-- Coefficient vector in the fixed coordinate order `P0,P2,P4,P6`. -/
def factorTwoP6EvenCoefficients
    (c0 c2 c4 c6 : ℝ) : Fin 4 → ℝ :=
  ![c0, c2, c4, c6]

/-- The symmetric matrix obtained by polarizing a real quadratic in the
ordered coordinates `P0,P2,P4,P6`. -/
def factorTwoP6EvenPolarizedMatrix
    (q00 q02 q04 q06 q22 q24 q26 q44 q46 q66 : ℝ) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  !![q00, q02, q04, q06;
    q02, q22, q24, q26;
    q04, q24, q44, q46;
    q06, q26, q46, q66]

theorem factorTwoP6EvenPolarizedMatrix_isHermitian
    (q00 q02 q04 q06 q22 q24 q26 q44 q46 q66 : ℝ) :
    (factorTwoP6EvenPolarizedMatrix
      q00 q02 q04 q06 q22 q24 q26 q44 q46 q66).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [factorTwoP6EvenPolarizedMatrix]

/-- Exact quadratic-form identity for the four-coordinate polarization. -/
theorem factorTwoP6EvenPolarizedMatrix_quadratic
    (q00 q02 q04 q06 q22 q24 q26 q44 q46 q66 : ℝ)
    (c0 c2 c4 c6 : ℝ) :
    star (factorTwoP6EvenCoefficients c0 c2 c4 c6) ⬝ᵥ
        (factorTwoP6EvenPolarizedMatrix
          q00 q02 q04 q06 q22 q24 q26 q44 q46 q66 *ᵥ
            factorTwoP6EvenCoefficients c0 c2 c4 c6) =
      q00 * c0 ^ 2 + 2 * q02 * c0 * c2 +
        2 * q04 * c0 * c4 + 2 * q06 * c0 * c6 +
        q22 * c2 ^ 2 + 2 * q24 * c2 * c4 +
        2 * q26 * c2 * c6 + q44 * c4 ^ 2 +
        2 * q46 * c4 * c6 + q66 * c6 ^ 2 := by
  simp [factorTwoP6EvenCoefficients, factorTwoP6EvenPolarizedMatrix,
    dotProduct, mulVec, Fin.sum_univ_succ]
  ring

/-! ## Energy and retained-hyperbolic matrices -/

/-- Diagonal matrix for a scalar multiple of the exact `P0/P2/P4/P6`
energy. -/
def factorTwoP6EvenEnergyMatrix (k : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  factorTwoP6EvenPolarizedMatrix
    (2 * k) 0 0 0 ((2 / 5 : ℝ) * k) 0 0
      ((2 / 9 : ℝ) * k) 0 ((2 / 13 : ℝ) * k)

theorem factorTwoP6EvenEnergyMatrix_isHermitian (k : ℝ) :
    (factorTwoP6EvenEnergyMatrix k).IsHermitian := by
  exact factorTwoP6EvenPolarizedMatrix_isHermitian _ _ _ _ _ _ _ _ _ _

theorem factorTwoP6EvenEnergyMatrix_quadratic
    (k c0 c2 c4 c6 : ℝ) :
    star (factorTwoP6EvenCoefficients c0 c2 c4 c6) ⬝ᵥ
        (factorTwoP6EvenEnergyMatrix k *ᵥ
          factorTwoP6EvenCoefficients c0 c2 c4 c6) =
      k * factorTwoP6EvenCoefficientEnergy c0 c2 c4 c6 := by
  rw [factorTwoP6EvenEnergyMatrix,
    factorTwoP6EvenPolarizedMatrix_quadratic]
  unfold factorTwoP6EvenCoefficientEnergy
  ring

/-- Coefficient of the `P0` direction in the retained cosh-polynomial
moment. -/
def factorTwoP6EvenCoshCoordinate0 : ℝ :=
  2 + yoshidaEndpointA ^ 2 / 12 + yoshidaEndpointA ^ 4 / 960 +
    yoshidaEndpointA ^ 6 / 161280

/-- Coefficient of the `P2` direction in the retained cosh-polynomial
moment. -/
def factorTwoP6EvenCoshCoordinate2 : ℝ :=
  yoshidaEndpointA ^ 2 / 30 + yoshidaEndpointA ^ 4 / 1680 +
    yoshidaEndpointA ^ 6 / 241920

/-- Coefficient of the `P4` direction in the retained cosh-polynomial
moment. -/
def factorTwoP6EvenCoshCoordinate4 : ℝ :=
  yoshidaEndpointA ^ 4 / 7560 + yoshidaEndpointA ^ 6 / 665280

/-- Coefficient of the `P6` direction in the retained cosh-polynomial
moment. -/
def factorTwoP6EvenCoshCoordinate6 : ℝ :=
  yoshidaEndpointA ^ 6 / 4324320

/-- Polarization matrix of the retained hyperbolic rank-one term together
with its global Taylor-error energy charge. -/
def factorTwoP6EvenRetainedHyperbolicMatrix : Matrix (Fin 4) (Fin 4) ℝ :=
  let m0 := factorTwoP6EvenCoshCoordinate0
  let m2 := factorTwoP6EvenCoshCoordinate2
  let m4 := factorTwoP6EvenCoshCoordinate4
  let m6 := factorTwoP6EvenCoshCoordinate6
  let d := 4 * yoshidaEndpointA * (1 / 48000000000 : ℝ) ^ 2
  factorTwoP6EvenPolarizedMatrix
    (yoshidaEndpointA * m0 * m0 - d * 2)
    (yoshidaEndpointA * m0 * m2)
    (yoshidaEndpointA * m0 * m4)
    (yoshidaEndpointA * m0 * m6)
    (yoshidaEndpointA * m2 * m2 - d * (2 / 5 : ℝ))
    (yoshidaEndpointA * m2 * m4)
    (yoshidaEndpointA * m2 * m6)
    (yoshidaEndpointA * m4 * m4 - d * (2 / 9 : ℝ))
    (yoshidaEndpointA * m4 * m6)
    (yoshidaEndpointA * m6 * m6 - d * (2 / 13 : ℝ))

theorem factorTwoP6EvenRetainedHyperbolicMatrix_isHermitian :
    factorTwoP6EvenRetainedHyperbolicMatrix.IsHermitian := by
  unfold factorTwoP6EvenRetainedHyperbolicMatrix
  exact factorTwoP6EvenPolarizedMatrix_isHermitian _ _ _ _ _ _ _ _ _ _

/-- The retained rank-one lower term is exactly the quadratic form of its
polarization matrix. -/
theorem factorTwoP6EvenRetainedHyperbolicMatrix_quadratic
    (c0 c2 c4 c6 : ℝ) :
    star (factorTwoP6EvenCoefficients c0 c2 c4 c6) ⬝ᵥ
        (factorTwoP6EvenRetainedHyperbolicMatrix *ᵥ
          factorTwoP6EvenCoefficients c0 c2 c4 c6) =
      factorTwoP6EvenRetainedHyperbolicLower c0 c2 c4 c6 := by
  rw [factorTwoP6EvenRetainedHyperbolicMatrix,
    factorTwoP6EvenPolarizedMatrix_quadratic]
  unfold factorTwoP6EvenRetainedHyperbolicLower
    factorTwoP6EvenCoefficientEnergy
    factorTwoIntrinsicP0246CoshPolynomialMoment
    factorTwoP6EvenCoshCoordinate0 factorTwoP6EvenCoshCoordinate2
    factorTwoP6EvenCoshCoordinate4 factorTwoP6EvenCoshCoordinate6
  ring

/-- Matrix of the clean-envelope and perturbation-envelope energy charges
already present in the endpoint lower model. -/
def factorTwoP6EvenEndpointEnergyChargeMatrix :
    Matrix (Fin 4) (Fin 4) ℝ :=
  factorTwoP6EvenEnergyMatrix
    (yoshidaEndpointA / 250000 + 3 / 40000)

theorem factorTwoP6EvenEndpointEnergyChargeMatrix_isHermitian :
    factorTwoP6EvenEndpointEnergyChargeMatrix.IsHermitian := by
  exact factorTwoP6EvenEnergyMatrix_isHermitian _

theorem factorTwoP6EvenEndpointEnergyChargeMatrix_quadratic
    (c0 c2 c4 c6 : ℝ) :
    star (factorTwoP6EvenCoefficients c0 c2 c4 c6) ⬝ᵥ
        (factorTwoP6EvenEndpointEnergyChargeMatrix *ᵥ
          factorTwoP6EvenCoefficients c0 c2 c4 c6) =
      (yoshidaEndpointA / 250000 + 3 / 40000) *
        factorTwoP6EvenCoefficientEnergy c0 c2 c4 c6 := by
  exact factorTwoP6EvenEnergyMatrix_quadratic _ _ _ _ _

theorem factorTwoP6EvenEndpointEnergyCharge_intrinsicEvenP0246
    (c0 c2 c4 c6 : ℝ) :
    factorTwoP6EvenEndpointEnergyCharge
        (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) =
      (yoshidaEndpointA / 250000 + 3 / 40000) *
        factorTwoP6EvenCoefficientEnergy c0 c2 c4 c6 := by
  unfold factorTwoP6EvenEndpointEnergyCharge
    factorTwoP6EvenCoefficientEnergy
  change (yoshidaEndpointA / 250000 + 3 / 40000) *
      factorTwoIntrinsicEnergy
        (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) = _
  rw [factorTwoIntrinsicEnergy_intrinsicEvenP0246]

theorem factorTwoP6EvenPerturbationGramMatrix_isHermitian :
    factorTwoP6EvenPerturbationGramMatrix.IsHermitian := by
  simpa only [Matrix.IsHermitian, Matrix.conjTranspose, star_trivial] using
    factorTwoP6EvenPerturbationGramMatrix_isSymm

theorem factorTwoP6EvenPerturbationPolynomialModel_intrinsicEvenP0246
    (c0 c2 c4 c6 : ℝ) :
    factorTwoP6EvenPerturbationPolynomialModel
        (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) =
      star (factorTwoP6EvenCoefficients c0 c2 c4 c6) ⬝ᵥ
        (factorTwoP6EvenPerturbationGramMatrix *ᵥ
          factorTwoP6EvenCoefficients c0 c2 c4 c6) := by
  simpa only [factorTwoP6EvenCoefficients] using
    factorTwoP6EvenPerturbationPolynomialModel_intrinsicEvenP0246_eq_matrixQuadratic
      c0 c2 c4 c6

/-! ## Matrix assembly laws -/

/-- Real matrix quadratic form at the retained coefficient vector. -/
def factorTwoP6EvenMatrixQuadratic
    (A : Matrix (Fin 4) (Fin 4) ℝ) (c0 c2 c4 c6 : ℝ) : ℝ :=
  star (factorTwoP6EvenCoefficients c0 c2 c4 c6) ⬝ᵥ
    (A *ᵥ factorTwoP6EvenCoefficients c0 c2 c4 c6)

theorem factorTwoP6EvenMatrixQuadratic_endpointEnergyCharge
    (c0 c2 c4 c6 : ℝ) :
    factorTwoP6EvenMatrixQuadratic
        factorTwoP6EvenEndpointEnergyChargeMatrix c0 c2 c4 c6 =
      (yoshidaEndpointA / 250000 + 3 / 40000) *
        factorTwoP6EvenCoefficientEnergy c0 c2 c4 c6 := by
  simpa only [factorTwoP6EvenMatrixQuadratic] using
    factorTwoP6EvenEndpointEnergyChargeMatrix_quadratic c0 c2 c4 c6

theorem factorTwoP6EvenMatrixQuadratic_retainedHyperbolic
    (c0 c2 c4 c6 : ℝ) :
    factorTwoP6EvenMatrixQuadratic
        factorTwoP6EvenRetainedHyperbolicMatrix c0 c2 c4 c6 =
      factorTwoP6EvenRetainedHyperbolicLower c0 c2 c4 c6 := by
  simpa only [factorTwoP6EvenMatrixQuadratic] using
    factorTwoP6EvenRetainedHyperbolicMatrix_quadratic c0 c2 c4 c6

theorem factorTwoP6EvenMatrixQuadratic_add
    (A B : Matrix (Fin 4) (Fin 4) ℝ) (c0 c2 c4 c6 : ℝ) :
    factorTwoP6EvenMatrixQuadratic (A + B) c0 c2 c4 c6 =
      factorTwoP6EvenMatrixQuadratic A c0 c2 c4 c6 +
        factorTwoP6EvenMatrixQuadratic B c0 c2 c4 c6 := by
  simp only [factorTwoP6EvenMatrixQuadratic, Matrix.add_mulVec,
    dotProduct_add]

theorem factorTwoP6EvenMatrixQuadratic_sub
    (A B : Matrix (Fin 4) (Fin 4) ℝ) (c0 c2 c4 c6 : ℝ) :
    factorTwoP6EvenMatrixQuadratic (A - B) c0 c2 c4 c6 =
      factorTwoP6EvenMatrixQuadratic A c0 c2 c4 c6 -
        factorTwoP6EvenMatrixQuadratic B c0 c2 c4 c6 := by
  simp only [factorTwoP6EvenMatrixQuadratic, Matrix.sub_mulVec,
    dotProduct_sub]

/-- Assemble the positive endpoint lower matrix from a clean and a
perturbation Gram. -/
def factorTwoP6EvenPlusMatrixAssembly
    (C P : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  C + factorTwoP6EvenRetainedHyperbolicMatrix + P -
    factorTwoP6EvenEndpointEnergyChargeMatrix

/-- Assemble the negative endpoint lower matrix from a clean and a
perturbation Gram. -/
def factorTwoP6EvenMinusMatrixAssembly
    (C P : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  C + factorTwoP6EvenRetainedHyperbolicMatrix - P -
    factorTwoP6EvenEndpointEnergyChargeMatrix

theorem factorTwoP6EvenPlusMatrixAssembly_isHermitian
    {C P : Matrix (Fin 4) (Fin 4) ℝ}
    (hC : C.IsHermitian) (hP : P.IsHermitian) :
    (factorTwoP6EvenPlusMatrixAssembly C P).IsHermitian := by
  exact ((hC.add factorTwoP6EvenRetainedHyperbolicMatrix_isHermitian).add
    hP).sub factorTwoP6EvenEndpointEnergyChargeMatrix_isHermitian

theorem factorTwoP6EvenMinusMatrixAssembly_isHermitian
    {C P : Matrix (Fin 4) (Fin 4) ℝ}
    (hC : C.IsHermitian) (hP : P.IsHermitian) :
    (factorTwoP6EvenMinusMatrixAssembly C P).IsHermitian := by
  exact ((hC.add factorTwoP6EvenRetainedHyperbolicMatrix_isHermitian).sub
    hP).sub factorTwoP6EvenEndpointEnergyChargeMatrix_isHermitian

theorem factorTwoP6EvenPlusMatrixAssembly_quadratic
    (C P : Matrix (Fin 4) (Fin 4) ℝ) (c0 c2 c4 c6 : ℝ) :
    factorTwoP6EvenMatrixQuadratic
        (factorTwoP6EvenPlusMatrixAssembly C P) c0 c2 c4 c6 =
      factorTwoP6EvenMatrixQuadratic C c0 c2 c4 c6 +
        factorTwoP6EvenRetainedHyperbolicLower c0 c2 c4 c6 +
        factorTwoP6EvenMatrixQuadratic P c0 c2 c4 c6 -
        (yoshidaEndpointA / 250000 + 3 / 40000) *
          factorTwoP6EvenCoefficientEnergy c0 c2 c4 c6 := by
  rw [factorTwoP6EvenPlusMatrixAssembly,
    factorTwoP6EvenMatrixQuadratic_sub,
    factorTwoP6EvenMatrixQuadratic_add,
    factorTwoP6EvenMatrixQuadratic_add,
    factorTwoP6EvenMatrixQuadratic_endpointEnergyCharge,
    factorTwoP6EvenMatrixQuadratic_retainedHyperbolic]

theorem factorTwoP6EvenMinusMatrixAssembly_quadratic
    (C P : Matrix (Fin 4) (Fin 4) ℝ) (c0 c2 c4 c6 : ℝ) :
    factorTwoP6EvenMatrixQuadratic
        (factorTwoP6EvenMinusMatrixAssembly C P) c0 c2 c4 c6 =
      factorTwoP6EvenMatrixQuadratic C c0 c2 c4 c6 +
        factorTwoP6EvenRetainedHyperbolicLower c0 c2 c4 c6 -
        factorTwoP6EvenMatrixQuadratic P c0 c2 c4 c6 -
        (yoshidaEndpointA / 250000 + 3 / 40000) *
          factorTwoP6EvenCoefficientEnergy c0 c2 c4 c6 := by
  rw [factorTwoP6EvenMinusMatrixAssembly,
    factorTwoP6EvenMatrixQuadratic_sub,
    factorTwoP6EvenMatrixQuadratic_sub,
    factorTwoP6EvenMatrixQuadratic_add,
    factorTwoP6EvenMatrixQuadratic_endpointEnergyCharge,
    factorTwoP6EvenMatrixQuadratic_retainedHyperbolic]

/-! ## Concrete endpoint lower matrices -/

/-- Exact polarization matrix of the non-hyperbolic clean polynomial model. -/
def factorTwoP6EvenNonHyperbolicCleanMatrix :
    Matrix (Fin 4) (Fin 4) ℝ :=
  factorTwoP6EvenPolarizedMatrix
    factorTwoP6EvenCleanPolynomialGram00
    factorTwoP6EvenCleanPolynomialGram02
    factorTwoP6EvenCleanPolynomialGram04
    factorTwoP6EvenCleanPolynomialGram06
    factorTwoP6EvenCleanPolynomialGram22
    factorTwoP6EvenCleanPolynomialGram24
    factorTwoP6EvenCleanPolynomialGram26
    factorTwoP6EvenCleanPolynomialGram44
    factorTwoP6EvenCleanPolynomialGram46
    factorTwoP6EvenCleanPolynomialGram66

theorem factorTwoP6EvenNonHyperbolicCleanMatrix_isHermitian :
    factorTwoP6EvenNonHyperbolicCleanMatrix.IsHermitian := by
  exact factorTwoP6EvenPolarizedMatrix_isHermitian _ _ _ _ _ _ _ _ _ _

theorem factorTwoP6EvenNonHyperbolicCleanMatrix_quadratic
    (c0 c2 c4 c6 : ℝ) :
    factorTwoP6EvenMatrixQuadratic
        factorTwoP6EvenNonHyperbolicCleanMatrix c0 c2 c4 c6 =
      factorTwoP6EvenCleanPolynomialGram c0 c2 c4 c6 := by
  unfold factorTwoP6EvenMatrixQuadratic
    factorTwoP6EvenNonHyperbolicCleanMatrix
  rw [factorTwoP6EvenPolarizedMatrix_quadratic]
  unfold factorTwoP6EvenCleanPolynomialGram
  ring

/-- Positive endpoint matrix in component order: clean non-hyperbolic,
retained hyperbolic, positive perturbation, then the endpoint energy charge. -/
def factorTwoP6EvenPlusLowerMatrix : Matrix (Fin 4) (Fin 4) ℝ :=
  factorTwoP6EvenNonHyperbolicCleanMatrix +
    factorTwoP6EvenRetainedHyperbolicMatrix +
    factorTwoP6EvenPerturbationGramMatrix -
    factorTwoP6EvenEndpointEnergyChargeMatrix

/-- Negative endpoint matrix in component order: clean non-hyperbolic,
retained hyperbolic, negative perturbation, then the endpoint energy charge. -/
def factorTwoP6EvenMinusLowerMatrix : Matrix (Fin 4) (Fin 4) ℝ :=
  factorTwoP6EvenNonHyperbolicCleanMatrix +
    factorTwoP6EvenRetainedHyperbolicMatrix -
    factorTwoP6EvenPerturbationGramMatrix -
    factorTwoP6EvenEndpointEnergyChargeMatrix

theorem factorTwoP6EvenPlusLowerMatrix_isHermitian :
    factorTwoP6EvenPlusLowerMatrix.IsHermitian := by
  exact factorTwoP6EvenPlusMatrixAssembly_isHermitian
    factorTwoP6EvenNonHyperbolicCleanMatrix_isHermitian
    factorTwoP6EvenPerturbationGramMatrix_isHermitian

theorem factorTwoP6EvenMinusLowerMatrix_isHermitian :
    factorTwoP6EvenMinusLowerMatrix.IsHermitian := by
  exact factorTwoP6EvenMinusMatrixAssembly_isHermitian
    factorTwoP6EvenNonHyperbolicCleanMatrix_isHermitian
    factorTwoP6EvenPerturbationGramMatrix_isHermitian

/-- The retained coefficient-level hyperbolic term is below the exact
hyperbolic endpoint quadratic on the same genuine profile. -/
theorem factorTwoP6EvenRetainedHyperbolicLower_le_exact
    (c0 c2 c4 c6 : ℝ) :
    factorTwoP6EvenRetainedHyperbolicLower c0 c2 c4 c6 ≤
      yoshidaEndpointHyperbolicQuadratic
        (fun x ↦
          (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6 x : ℂ)) := by
  have h := P0246_coshPolynomial_rankOne_sub_error_le_hyperbolicQuadratic
    c0 c2 c4 c6
  rw [← factorTwoIntrinsicEvenP0246Profile_eq_hyperbolicProfile] at h
  simpa only [factorTwoP6EvenRetainedHyperbolicLower,
    factorTwoP6EvenCoefficientEnergy] using h

theorem factorTwoP6EvenPlusLowerQuadratic_eq_components
    (c0 c2 c4 c6 : ℝ) :
    factorTwoP6EvenPlusLowerQuadratic c0 c2 c4 c6 =
      (factorTwoP6EvenCleanPolynomialModel
          (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) -
        yoshidaEndpointHyperbolicQuadratic
          (fun x ↦
            (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6 x : ℂ))) +
      factorTwoP6EvenPerturbationPolynomialModel
        (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) -
      factorTwoP6EvenEndpointEnergyCharge
        (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) +
      factorTwoP6EvenRetainedHyperbolicLower c0 c2 c4 c6 := by
  unfold factorTwoP6EvenPlusLowerQuadratic
    factorTwoP6EvenEndpointPlusLowerModel
  ring

theorem factorTwoP6EvenMinusLowerQuadratic_eq_components
    (c0 c2 c4 c6 : ℝ) :
    factorTwoP6EvenMinusLowerQuadratic c0 c2 c4 c6 =
      (factorTwoP6EvenCleanPolynomialModel
          (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) -
        yoshidaEndpointHyperbolicQuadratic
          (fun x ↦
            (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6 x : ℂ))) -
      factorTwoP6EvenPerturbationPolynomialModel
        (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) -
      factorTwoP6EvenEndpointEnergyCharge
        (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) +
      factorTwoP6EvenRetainedHyperbolicLower c0 c2 c4 c6 := by
  unfold factorTwoP6EvenMinusLowerQuadratic
    factorTwoP6EvenEndpointMinusLowerModel
  ring

/-- The positive coefficient lower quadratic is exactly the quadratic form
of the concrete positive endpoint matrix. -/
theorem factorTwoP6EvenPlusLowerQuadratic_eq_matrixQuadratic
    (c0 c2 c4 c6 : ℝ) :
    factorTwoP6EvenPlusLowerQuadratic c0 c2 c4 c6 =
      star (factorTwoP6EvenCoefficients c0 c2 c4 c6) ⬝ᵥ
        (factorTwoP6EvenPlusLowerMatrix *ᵥ
          factorTwoP6EvenCoefficients c0 c2 c4 c6) := by
  change factorTwoP6EvenPlusLowerQuadratic c0 c2 c4 c6 =
    factorTwoP6EvenMatrixQuadratic factorTwoP6EvenPlusLowerMatrix
      c0 c2 c4 c6
  calc
    factorTwoP6EvenPlusLowerQuadratic c0 c2 c4 c6 =
        factorTwoP6EvenMatrixQuadratic
            factorTwoP6EvenNonHyperbolicCleanMatrix c0 c2 c4 c6 +
          factorTwoP6EvenRetainedHyperbolicLower c0 c2 c4 c6 +
          factorTwoP6EvenMatrixQuadratic
            factorTwoP6EvenPerturbationGramMatrix c0 c2 c4 c6 -
          (yoshidaEndpointA / 250000 + 3 / 40000) *
            factorTwoP6EvenCoefficientEnergy c0 c2 c4 c6 := by
      rw [factorTwoP6EvenPlusLowerQuadratic_eq_components,
        factorTwoP6EvenNonHyperbolicCleanPolynomialModel_intrinsicEvenP0246_eq_gram,
        factorTwoP6EvenPerturbationPolynomialModel_intrinsicEvenP0246,
        factorTwoP6EvenEndpointEnergyCharge_intrinsicEvenP0246,
        factorTwoP6EvenNonHyperbolicCleanMatrix_quadratic]
      unfold factorTwoP6EvenMatrixQuadratic
      ring
    _ = factorTwoP6EvenMatrixQuadratic
        (factorTwoP6EvenPlusMatrixAssembly
          factorTwoP6EvenNonHyperbolicCleanMatrix
          factorTwoP6EvenPerturbationGramMatrix) c0 c2 c4 c6 :=
      (factorTwoP6EvenPlusMatrixAssembly_quadratic
        factorTwoP6EvenNonHyperbolicCleanMatrix
        factorTwoP6EvenPerturbationGramMatrix c0 c2 c4 c6).symm
    _ = factorTwoP6EvenMatrixQuadratic factorTwoP6EvenPlusLowerMatrix
        c0 c2 c4 c6 := rfl

/-- The negative coefficient lower quadratic is exactly the quadratic form
of the concrete negative endpoint matrix. -/
theorem factorTwoP6EvenMinusLowerQuadratic_eq_matrixQuadratic
    (c0 c2 c4 c6 : ℝ) :
    factorTwoP6EvenMinusLowerQuadratic c0 c2 c4 c6 =
      star (factorTwoP6EvenCoefficients c0 c2 c4 c6) ⬝ᵥ
        (factorTwoP6EvenMinusLowerMatrix *ᵥ
          factorTwoP6EvenCoefficients c0 c2 c4 c6) := by
  change factorTwoP6EvenMinusLowerQuadratic c0 c2 c4 c6 =
    factorTwoP6EvenMatrixQuadratic factorTwoP6EvenMinusLowerMatrix
      c0 c2 c4 c6
  calc
    factorTwoP6EvenMinusLowerQuadratic c0 c2 c4 c6 =
        factorTwoP6EvenMatrixQuadratic
            factorTwoP6EvenNonHyperbolicCleanMatrix c0 c2 c4 c6 +
          factorTwoP6EvenRetainedHyperbolicLower c0 c2 c4 c6 -
          factorTwoP6EvenMatrixQuadratic
            factorTwoP6EvenPerturbationGramMatrix c0 c2 c4 c6 -
          (yoshidaEndpointA / 250000 + 3 / 40000) *
            factorTwoP6EvenCoefficientEnergy c0 c2 c4 c6 := by
      rw [factorTwoP6EvenMinusLowerQuadratic_eq_components,
        factorTwoP6EvenNonHyperbolicCleanPolynomialModel_intrinsicEvenP0246_eq_gram,
        factorTwoP6EvenPerturbationPolynomialModel_intrinsicEvenP0246,
        factorTwoP6EvenEndpointEnergyCharge_intrinsicEvenP0246,
        factorTwoP6EvenNonHyperbolicCleanMatrix_quadratic]
      unfold factorTwoP6EvenMatrixQuadratic
      ring
    _ = factorTwoP6EvenMatrixQuadratic
        (factorTwoP6EvenMinusMatrixAssembly
          factorTwoP6EvenNonHyperbolicCleanMatrix
          factorTwoP6EvenPerturbationGramMatrix) c0 c2 c4 c6 :=
      (factorTwoP6EvenMinusMatrixAssembly_quadratic
        factorTwoP6EvenNonHyperbolicCleanMatrix
        factorTwoP6EvenPerturbationGramMatrix c0 c2 c4 c6).symm
    _ = factorTwoP6EvenMatrixQuadratic factorTwoP6EvenMinusLowerMatrix
        c0 c2 c4 c6 := rfl

/-- The positive coefficient quadratic is a structural lower bound for the
actual positive endpoint phase diagonal. -/
theorem factorTwoP6EvenPlusLowerQuadratic_le_phaseDiagonal
    (c0 c2 c4 c6 : ℝ) :
    factorTwoP6EvenPlusLowerQuadratic c0 c2 c4 c6 ≤
      factorTwoEndpointPhaseDiagonal
        (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) 1 := by
  let e := factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6
  have hhyper := factorTwoP6EvenRetainedHyperbolicLower_le_exact
    c0 c2 c4 c6
  have hlower := factorTwoP6EvenEndpointPlusLowerModel_le_phaseDiagonal
    e (continuous_factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6)
  unfold factorTwoP6EvenPlusLowerQuadratic
  dsimp only [e] at hlower ⊢
  linarith

/-- The negative coefficient quadratic is a structural lower bound for the
actual negative endpoint phase diagonal. -/
theorem factorTwoP6EvenMinusLowerQuadratic_le_phaseDiagonal
    (c0 c2 c4 c6 : ℝ) :
    factorTwoP6EvenMinusLowerQuadratic c0 c2 c4 c6 ≤
      factorTwoEndpointPhaseDiagonal
        (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) (-1) := by
  let e := factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6
  have hhyper := factorTwoP6EvenRetainedHyperbolicLower_le_exact
    c0 c2 c4 c6
  have hlower := factorTwoP6EvenEndpointMinusLowerModel_le_phaseDiagonal
    e (continuous_factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6)
  unfold factorTwoP6EvenMinusLowerQuadratic
  dsimp only [e] at hlower ⊢
  linarith

/-- Matrix form of the structural lower bound at the positive endpoint. -/
theorem factorTwoP6EvenPlusLowerMatrix_quadratic_le_phaseDiagonal
    (c0 c2 c4 c6 : ℝ) :
    star (factorTwoP6EvenCoefficients c0 c2 c4 c6) ⬝ᵥ
        (factorTwoP6EvenPlusLowerMatrix *ᵥ
          factorTwoP6EvenCoefficients c0 c2 c4 c6) ≤
      factorTwoEndpointPhaseDiagonal
        (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) 1 := by
  rw [← factorTwoP6EvenPlusLowerQuadratic_eq_matrixQuadratic]
  exact factorTwoP6EvenPlusLowerQuadratic_le_phaseDiagonal c0 c2 c4 c6

/-- Matrix form of the structural lower bound at the negative endpoint. -/
theorem factorTwoP6EvenMinusLowerMatrix_quadratic_le_phaseDiagonal
    (c0 c2 c4 c6 : ℝ) :
    star (factorTwoP6EvenCoefficients c0 c2 c4 c6) ⬝ᵥ
        (factorTwoP6EvenMinusLowerMatrix *ᵥ
          factorTwoP6EvenCoefficients c0 c2 c4 c6) ≤
      factorTwoEndpointPhaseDiagonal
        (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) (-1) := by
  rw [← factorTwoP6EvenMinusLowerQuadratic_eq_matrixQuadratic]
  exact factorTwoP6EvenMinusLowerQuadratic_le_phaseDiagonal c0 c2 c4 c6

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineP6EvenLowerMatrixStructural

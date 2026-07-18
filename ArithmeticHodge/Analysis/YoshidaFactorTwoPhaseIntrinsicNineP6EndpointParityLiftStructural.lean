import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineP6EvenLowerMatrixStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawSixEndpointPositiveStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedDiskStructural

set_option autoImplicit false

open Complex Matrix Real

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineP6EndpointParityLiftStructural

noncomputable section

open ThreeByThreePositiveMixedDeterminant
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointOddLowGramExpansion
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseDiskSchur
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicNineP6EvenLowerMatrixStructural
open YoshidaFactorTwoPhaseIntrinsicNineP6EvenProfileCorrelationStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4Schur
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveSchur
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawSixEndpointPositiveStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawSixOddPencilStructural
open YoshidaFactorTwoPhaseIntrinsicSixSchurReduction
open YoshidaFactorTwoPhaseIntrinsicSixStaticPlusObstruction
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedDiskStructural
open YoshidaFactorTwoPhaseLowSchur

/-!
# Structural endpoint parity lift through `P6`

At an endpoint of the symmetric phase coordinate the alternating coordinate
is zero.  Hence the retained `P0/P2/P4/P6` and `P1/P3/P5` profiles decouple
exactly.  The odd block is already positive definite at both endpoints.  This
module combines it with any positive-definite certificate for the two even
lower matrices.  It records separately the literal channel convention
(same endpoint sign on both profiles) and the crossed static-branch
convention forced by the definition of `factorTwoIntrinsicSixStaticOdd`.

All matrices below are ordered as
`P0,P2,P4,P6,P1,P3,P5`.  No coefficient enumeration enters the lift.
-/

/-! ## Generic structural block lemmas -/

/-- A zero-off-diagonal block matrix is positive definite when its two
diagonal blocks are positive definite. -/
private theorem posDef_fromBlocks_zero_offDiagonal
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {A : Matrix ι ι ℝ} {D : Matrix κ κ ℝ}
    (hA : A.PosDef) (hD : D.PosDef) :
    (Matrix.fromBlocks A 0 0 D).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · exact Matrix.IsHermitian.fromBlocks hA.isHermitian (by simp) hD.isHermitian
  · intro x hx
    have hsplit : (x ∘ Sum.inl) ≠ 0 ∨ (x ∘ Sum.inr) ≠ 0 := by
      by_contra h
      push_neg at h
      rcases h with ⟨he, ho⟩
      apply hx
      funext i
      rcases i with i | i
      · exact congrFun he i
      · exact congrFun ho i
    rcases hsplit with he | ho
    · have hEven := hA.dotProduct_mulVec_pos he
      have hOdd := hD.posSemidef.re_dotProduct_nonneg (x ∘ Sum.inr)
      simpa [dotProduct, mulVec, Fintype.sum_sum_type] using
        add_pos_of_pos_of_nonneg hEven hOdd
    · have hEven := hA.posSemidef.re_dotProduct_nonneg (x ∘ Sum.inl)
      have hOdd := hD.dotProduct_mulVec_pos ho
      simpa [dotProduct, mulVec, Fintype.sum_sum_type] using
        add_pos_of_nonneg_of_pos hEven hOdd

/-- Exact quadratic splitting for a zero-off-diagonal block matrix. -/
private theorem fromBlocks_zero_offDiagonal_quadratic
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι ι ℝ) (D : Matrix κ κ ℝ)
    (x : ι → ℝ) (y : κ → ℝ) :
    star (Sum.elim x y) ⬝ᵥ
        (Matrix.fromBlocks A 0 0 D *ᵥ Sum.elim x y) =
      star x ⬝ᵥ (A *ᵥ x) + star y ⬝ᵥ (D *ᵥ y) := by
  simp [dotProduct, mulVec, Fintype.sum_sum_type]

/-- Reindexing both axes along an equivalence preserves positive
definiteness. -/
private theorem posDef_submatrix_equiv
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {A : Matrix ι ι ℝ} (hA : A.PosDef) (e : κ ≃ ι) :
    (A.submatrix e e).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (hA.isHermitian.submatrix e)
  intro x hx
  simp only [star_trivial]
  let y : ι → ℝ := x ∘ e.symm
  have hy : y ≠ 0 := by
    intro hzero
    apply hx
    funext i
    have hi := congrFun hzero (e i)
    simpa only [y, Function.comp_apply, Equiv.symm_apply_apply,
      Pi.zero_apply] using hi
  have hpositive := hA.dotProduct_mulVec_pos hy
  simp only [star_trivial] at hpositive
  have hmul :
      A.submatrix e e *ᵥ x = (A *ᵥ y) ∘ e := by
    simpa only [y] using Matrix.submatrix_mulVec_equiv A x e e
  rw [hmul]
  have hxcomp : x = y ∘ e := by
    funext i
    simp only [y, Function.comp_apply, Equiv.symm_apply_apply]
  rw [hxcomp]
  rw [comp_equiv_dotProduct_comp_equiv]
  exact hpositive

/-- Homogeneity of one endpoint diagonal, used only to identify its value on
the zero profile. -/
private theorem factorTwoEndpointPhaseDiagonal_smul
    (w : ℝ → ℝ) (c a : ℝ) :
    factorTwoEndpointPhaseDiagonal (c • w) a =
      c ^ 2 * factorTwoEndpointPhaseDiagonal w a := by
  have hclean : yoshidaEndpointOddCleanQuadratic (c • w) =
      c ^ 2 * yoshidaEndpointOddCleanQuadratic w := by
    simpa only [Pi.smul_apply, smul_eq_mul] using
      yoshidaEndpointOddCleanQuadratic_const_mul w c
  unfold factorTwoEndpointPhaseDiagonal
  rw [hclean, factorTwoCenteredSymmetricPerturbation_smul]
  ring_nf

/-! ## Exact odd endpoint block -/

/-- Coefficients of the odd block in order `P1,P3,P5`. -/
def factorTwoP135OddCoefficients
    (c1 c3 c5 : ℝ) : Fin 3 → ℝ :=
  ![c1, c3, c5]

/-- The raw odd endpoint matrix is exactly the oppositely signed static odd
quadratic. -/
theorem rawSixOddEndpointMatrix_quadratic_eq_staticOdd
    (a c1 c3 c5 : ℝ) :
    star (factorTwoP135OddCoefficients c1 c3 c5) ⬝ᵥ
        (rawSixOddEndpointMatrix a *ᵥ
          factorTwoP135OddCoefficients c1 c3 c5) =
      factorTwoIntrinsicSixStaticOdd (-a) c1 c3 c5 := by
  simp [factorTwoP135OddCoefficients, rawSixOddEndpointMatrix,
    symmetricMatrix3, dotProduct, mulVec, Fin.sum_univ_succ,
    factorTwoIntrinsicSixStaticOdd, factorTwoIntrinsicOddPhaseQuadratic,
    factorTwoIntrinsicSixP5Diagonal,
    factorTwoIntrinsicP5PhaseDiagonal, factorTwoEndpointPhaseDiagonal]
  ring

/-- Exact profile meaning of the odd `P1/P3/P5` static endpoint block. -/
theorem factorTwoEndpointPhaseDiagonal_intrinsicP135_eq_staticOdd
    (a c1 c3 c5 : ℝ) :
    factorTwoEndpointPhaseDiagonal
        (factorTwoIntrinsicSixOddTail c1 c3 c5) a =
      factorTwoIntrinsicSixStaticOdd (-a) c1 c3 c5 := by
  have h := factorTwoEndpointChannelPhase_intrinsicSix_eq_static_coordinates
    0 0 0 c1 c3 c5 a 0
  have he : factorTwoEvenStructuralLowProfile 0 0 +
      factorTwoIntrinsicSixEvenTail 0 = (0 : ℝ → ℝ) := by
    funext x
    unfold factorTwoEvenStructuralLowProfile factorTwoIntrinsicSixEvenTail
      centeredEvenP0
    simp
  rw [factorTwoEndpointChannelPhase_eq_diagonals, he] at h
  have hzero : factorTwoEndpointPhaseDiagonal (0 : ℝ → ℝ) a = 0 := by
    simpa using
      (factorTwoEndpointPhaseDiagonal_smul (0 : ℝ → ℝ) 0 a)
  have hcross : factorTwoCenteredAlternatingCoupling
      (0 : ℝ → ℝ) (factorTwoIntrinsicSixOddTail c1 c3 c5) = 0 := by
    simpa using (factorTwoCenteredAlternatingCoupling_smul_left 0
      (0 : ℝ → ℝ) (factorTwoIntrinsicSixOddTail c1 c3 c5))
  rw [hzero, hcross] at h
  simpa [factorTwoIntrinsicSixStaticEven] using h

/-- The raw odd matrix quadratic is the complete odd profile diagonal. -/
theorem rawSixOddEndpointMatrix_quadratic_eq_phaseDiagonal
    (a c1 c3 c5 : ℝ) :
    star (factorTwoP135OddCoefficients c1 c3 c5) ⬝ᵥ
        (rawSixOddEndpointMatrix a *ᵥ
          factorTwoP135OddCoefficients c1 c3 c5) =
      factorTwoEndpointPhaseDiagonal
        (factorTwoIntrinsicSixOddTail c1 c3 c5) a := by
  rw [rawSixOddEndpointMatrix_quadratic_eq_staticOdd,
    factorTwoEndpointPhaseDiagonal_intrinsicP135_eq_staticOdd]

/-- Re-exposure of the committed structural odd endpoint certificates. -/
theorem factorTwoP135OddEndpointMatrices_posDef :
    rawSixOddPlusMatrix.PosDef ∧ rawSixOddMinusMatrix.PosDef :=
  rawSixOddEndpointMatrices_posDef

/-! ## Exact endpoint parity cancellation -/

/-- At `b = 0`, the complete `P0/P2/P4/P6`--`P1/P3/P5` cross-parity
coordinate vanishes exactly. -/
theorem factorTwoEndpointChannelPhase_intrinsicP0246_P135_b_zero
    (c0 c2 c4 c6 c1 c3 c5 a : ℝ) :
    factorTwoEndpointChannelPhase
        (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6)
        (factorTwoIntrinsicSixOddTail c1 c3 c5) a 0 =
      factorTwoEndpointPhaseDiagonal
          (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) a +
        factorTwoEndpointPhaseDiagonal
          (factorTwoIntrinsicSixOddTail c1 c3 c5) a := by
  simpa using factorTwoEndpointChannelPhase_eq_diagonals
    (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6)
    (factorTwoIntrinsicSixOddTail c1 c3 c5) a 0

/-- Canonical coordinate equivalence for the order
`P0,P2,P4,P6,P1,P3,P5`. -/
def factorTwoP6EndpointParityEquiv :
    (Fin 4 ⊕ Fin 3) ≃ Fin 7 :=
  finSumFinEquiv

/-! ## Crossed static-branch convention -/

/-- Positive static branch: even plus is paired with odd minus because
`factorTwoIntrinsicSixStaticOdd 1` evaluates the odd entries at `-1`.  This
is deliberately distinguished from the literal channel endpoint below. -/
def factorTwoP6StaticPlusSplitLowerMatrix :
    Matrix (Fin 4 ⊕ Fin 3) (Fin 4 ⊕ Fin 3) ℝ :=
  Matrix.fromBlocks factorTwoP6EvenPlusLowerMatrix 0 0
    rawSixOddMinusMatrix

/-- Negative static branch: even minus is paired with odd plus. -/
def factorTwoP6StaticMinusSplitLowerMatrix :
    Matrix (Fin 4 ⊕ Fin 3) (Fin 4 ⊕ Fin 3) ℝ :=
  Matrix.fromBlocks factorTwoP6EvenMinusLowerMatrix 0 0
    rawSixOddPlusMatrix

theorem factorTwoP6StaticPlusSplitLowerMatrix_posDef
    (hEven : factorTwoP6EvenPlusLowerMatrix.PosDef) :
    factorTwoP6StaticPlusSplitLowerMatrix.PosDef := by
  exact posDef_fromBlocks_zero_offDiagonal hEven
    rawSixOddMinusMatrix_posDef

theorem factorTwoP6StaticMinusSplitLowerMatrix_posDef
    (hEven : factorTwoP6EvenMinusLowerMatrix.PosDef) :
    factorTwoP6StaticMinusSplitLowerMatrix.PosDef := by
  exact posDef_fromBlocks_zero_offDiagonal hEven
    rawSixOddPlusMatrix_posDef

/-- Crossed positive static-branch matrix on `Fin 7`. -/
def factorTwoP6StaticPlusLowerMatrix : Matrix (Fin 7) (Fin 7) ℝ :=
  factorTwoP6StaticPlusSplitLowerMatrix.submatrix
    factorTwoP6EndpointParityEquiv.symm factorTwoP6EndpointParityEquiv.symm

/-- Crossed negative static-branch matrix on `Fin 7`. -/
def factorTwoP6StaticMinusLowerMatrix : Matrix (Fin 7) (Fin 7) ℝ :=
  factorTwoP6StaticMinusSplitLowerMatrix.submatrix
    factorTwoP6EndpointParityEquiv.symm factorTwoP6EndpointParityEquiv.symm

/-- Conditional positive definiteness of both crossed `Fin 7` static-branch
lower matrices. -/
theorem factorTwoP6StaticLowerMatrices_posDef
    (hEvenPlus : factorTwoP6EvenPlusLowerMatrix.PosDef)
    (hEvenMinus : factorTwoP6EvenMinusLowerMatrix.PosDef) :
    factorTwoP6StaticPlusLowerMatrix.PosDef ∧
      factorTwoP6StaticMinusLowerMatrix.PosDef := by
  constructor
  · unfold factorTwoP6StaticPlusLowerMatrix
    exact posDef_submatrix_equiv
      (factorTwoP6StaticPlusSplitLowerMatrix_posDef hEvenPlus)
      factorTwoP6EndpointParityEquiv.symm
  · unfold factorTwoP6StaticMinusLowerMatrix
    exact posDef_submatrix_equiv
      (factorTwoP6StaticMinusSplitLowerMatrix_posDef hEvenMinus)
      factorTwoP6EndpointParityEquiv.symm

/-! ## Literal channel endpoint matrices and profile consequences -/

/-- Coefficients on the split parity index in the order
`P0,P2,P4,P6 | P1,P3,P5`. -/
def factorTwoP6EndpointSplitCoefficients
    (c0 c2 c4 c6 c1 c3 c5 : ℝ) : (Fin 4 ⊕ Fin 3) → ℝ :=
  Sum.elim (factorTwoP6EvenCoefficients c0 c2 c4 c6)
    (factorTwoP135OddCoefficients c1 c3 c5)

/-- At the literal positive channel endpoint, both profile diagonals are
evaluated at `+1`. -/
def factorTwoP6EndpointPlusSplitLowerMatrix :
    Matrix (Fin 4 ⊕ Fin 3) (Fin 4 ⊕ Fin 3) ℝ :=
  Matrix.fromBlocks factorTwoP6EvenPlusLowerMatrix 0 0
    rawSixOddPlusMatrix

/-- At the literal negative channel endpoint, both profile diagonals are
evaluated at `-1`. -/
def factorTwoP6EndpointMinusSplitLowerMatrix :
    Matrix (Fin 4 ⊕ Fin 3) (Fin 4 ⊕ Fin 3) ℝ :=
  Matrix.fromBlocks factorTwoP6EvenMinusLowerMatrix 0 0
    rawSixOddMinusMatrix

theorem factorTwoP6EndpointPlusSplitLowerMatrix_posDef
    (hEven : factorTwoP6EvenPlusLowerMatrix.PosDef) :
    factorTwoP6EndpointPlusSplitLowerMatrix.PosDef := by
  exact posDef_fromBlocks_zero_offDiagonal hEven
    rawSixOddPlusMatrix_posDef

theorem factorTwoP6EndpointMinusSplitLowerMatrix_posDef
    (hEven : factorTwoP6EvenMinusLowerMatrix.PosDef) :
    factorTwoP6EndpointMinusSplitLowerMatrix.PosDef := by
  exact posDef_fromBlocks_zero_offDiagonal hEven
    rawSixOddMinusMatrix_posDef

/-- Literal positive channel endpoint lower matrix on `Fin 7`. -/
def factorTwoP6EndpointPlusLowerMatrix : Matrix (Fin 7) (Fin 7) ℝ :=
  factorTwoP6EndpointPlusSplitLowerMatrix.submatrix
    factorTwoP6EndpointParityEquiv.symm factorTwoP6EndpointParityEquiv.symm

/-- Literal negative channel endpoint lower matrix on `Fin 7`. -/
def factorTwoP6EndpointMinusLowerMatrix : Matrix (Fin 7) (Fin 7) ℝ :=
  factorTwoP6EndpointMinusSplitLowerMatrix.submatrix
    factorTwoP6EndpointParityEquiv.symm factorTwoP6EndpointParityEquiv.symm

/-- Conditional positive definiteness of both literal `Fin 7` channel
endpoint lower matrices. -/
theorem factorTwoP6EndpointLowerMatrices_posDef
    (hEvenPlus : factorTwoP6EvenPlusLowerMatrix.PosDef)
    (hEvenMinus : factorTwoP6EvenMinusLowerMatrix.PosDef) :
    factorTwoP6EndpointPlusLowerMatrix.PosDef ∧
      factorTwoP6EndpointMinusLowerMatrix.PosDef := by
  constructor
  · unfold factorTwoP6EndpointPlusLowerMatrix
    exact posDef_submatrix_equiv
      (factorTwoP6EndpointPlusSplitLowerMatrix_posDef hEvenPlus)
      factorTwoP6EndpointParityEquiv.symm
  · unfold factorTwoP6EndpointMinusLowerMatrix
    exact posDef_submatrix_equiv
      (factorTwoP6EndpointMinusSplitLowerMatrix_posDef hEvenMinus)
      factorTwoP6EndpointParityEquiv.symm

/-- The positive literal endpoint block quadratic is the sum of the even
lower quadratic and the exact odd profile diagonal. -/
theorem factorTwoP6EndpointPlusSplitLowerMatrix_quadratic
    (c0 c2 c4 c6 c1 c3 c5 : ℝ) :
    star (factorTwoP6EndpointSplitCoefficients
        c0 c2 c4 c6 c1 c3 c5) ⬝ᵥ
      (factorTwoP6EndpointPlusSplitLowerMatrix *ᵥ
        factorTwoP6EndpointSplitCoefficients
          c0 c2 c4 c6 c1 c3 c5) =
      factorTwoP6EvenPlusLowerQuadratic c0 c2 c4 c6 +
        factorTwoEndpointPhaseDiagonal
          (factorTwoIntrinsicSixOddTail c1 c3 c5) 1 := by
  unfold factorTwoP6EndpointSplitCoefficients
    factorTwoP6EndpointPlusSplitLowerMatrix
  rw [fromBlocks_zero_offDiagonal_quadratic,
    ← factorTwoP6EvenPlusLowerQuadratic_eq_matrixQuadratic]
  change factorTwoP6EvenPlusLowerQuadratic c0 c2 c4 c6 +
      star (factorTwoP135OddCoefficients c1 c3 c5) ⬝ᵥ
        (rawSixOddEndpointMatrix 1 *ᵥ
          factorTwoP135OddCoefficients c1 c3 c5) = _
  rw [rawSixOddEndpointMatrix_quadratic_eq_phaseDiagonal]

/-- The negative literal endpoint block quadratic is the sum of the even
lower quadratic and the exact odd profile diagonal. -/
theorem factorTwoP6EndpointMinusSplitLowerMatrix_quadratic
    (c0 c2 c4 c6 c1 c3 c5 : ℝ) :
    star (factorTwoP6EndpointSplitCoefficients
        c0 c2 c4 c6 c1 c3 c5) ⬝ᵥ
      (factorTwoP6EndpointMinusSplitLowerMatrix *ᵥ
        factorTwoP6EndpointSplitCoefficients
          c0 c2 c4 c6 c1 c3 c5) =
      factorTwoP6EvenMinusLowerQuadratic c0 c2 c4 c6 +
        factorTwoEndpointPhaseDiagonal
          (factorTwoIntrinsicSixOddTail c1 c3 c5) (-1) := by
  unfold factorTwoP6EndpointSplitCoefficients
    factorTwoP6EndpointMinusSplitLowerMatrix
  rw [fromBlocks_zero_offDiagonal_quadratic,
    ← factorTwoP6EvenMinusLowerQuadratic_eq_matrixQuadratic]
  change factorTwoP6EvenMinusLowerQuadratic c0 c2 c4 c6 +
      star (factorTwoP135OddCoefficients c1 c3 c5) ⬝ᵥ
        (rawSixOddEndpointMatrix (-1) *ᵥ
          factorTwoP135OddCoefficients c1 c3 c5) = _
  rw [rawSixOddEndpointMatrix_quadratic_eq_phaseDiagonal]

/-- Conditional strict positivity of the actual positive endpoint profile
for every nonzero retained coefficient vector. -/
theorem factorTwoEndpointChannelPhase_intrinsicP0246_P135_one_zero_pos
    (hEven : factorTwoP6EvenPlusLowerMatrix.PosDef)
    (c0 c2 c4 c6 c1 c3 c5 : ℝ)
    (hne : factorTwoP6EndpointSplitCoefficients
      c0 c2 c4 c6 c1 c3 c5 ≠ 0) :
    0 < factorTwoEndpointChannelPhase
      (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6)
      (factorTwoIntrinsicSixOddTail c1 c3 c5) 1 0 := by
  have hlower :=
    (factorTwoP6EndpointPlusSplitLowerMatrix_posDef hEven).dotProduct_mulVec_pos
      hne
  rw [factorTwoP6EndpointPlusSplitLowerMatrix_quadratic] at hlower
  have heven := factorTwoP6EvenPlusLowerQuadratic_le_phaseDiagonal
    c0 c2 c4 c6
  rw [factorTwoEndpointChannelPhase_intrinsicP0246_P135_b_zero]
  linarith

/-- Conditional strict positivity of the actual negative endpoint profile
for every nonzero retained coefficient vector. -/
theorem factorTwoEndpointChannelPhase_intrinsicP0246_P135_neg_one_zero_pos
    (hEven : factorTwoP6EvenMinusLowerMatrix.PosDef)
    (c0 c2 c4 c6 c1 c3 c5 : ℝ)
    (hne : factorTwoP6EndpointSplitCoefficients
      c0 c2 c4 c6 c1 c3 c5 ≠ 0) :
    0 < factorTwoEndpointChannelPhase
      (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6)
      (factorTwoIntrinsicSixOddTail c1 c3 c5) (-1) 0 := by
  have hlower :=
    (factorTwoP6EndpointMinusSplitLowerMatrix_posDef hEven).dotProduct_mulVec_pos
      hne
  rw [factorTwoP6EndpointMinusSplitLowerMatrix_quadratic] at hlower
  have heven := factorTwoP6EvenMinusLowerQuadratic_le_phaseDiagonal
    c0 c2 c4 c6
  rw [factorTwoEndpointChannelPhase_intrinsicP0246_P135_b_zero]
  linarith

/-- Conditional nonnegativity of both actual endpoint profiles, including
the zero coefficient vector. -/
theorem factorTwoEndpointChannelPhase_intrinsicP0246_P135_endpoints_nonneg
    (hEvenPlus : factorTwoP6EvenPlusLowerMatrix.PosDef)
    (hEvenMinus : factorTwoP6EvenMinusLowerMatrix.PosDef)
    (c0 c2 c4 c6 c1 c3 c5 : ℝ) :
    0 ≤ factorTwoEndpointChannelPhase
        (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6)
        (factorTwoIntrinsicSixOddTail c1 c3 c5) 1 0 ∧
      0 ≤ factorTwoEndpointChannelPhase
        (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6)
        (factorTwoIntrinsicSixOddTail c1 c3 c5) (-1) 0 := by
  have hPlusLower :=
    (factorTwoP6EndpointPlusSplitLowerMatrix_posDef hEvenPlus).posSemidef
      |>.dotProduct_mulVec_nonneg
        (factorTwoP6EndpointSplitCoefficients c0 c2 c4 c6 c1 c3 c5)
  have hMinusLower :=
    (factorTwoP6EndpointMinusSplitLowerMatrix_posDef hEvenMinus).posSemidef
      |>.dotProduct_mulVec_nonneg
        (factorTwoP6EndpointSplitCoefficients c0 c2 c4 c6 c1 c3 c5)
  rw [factorTwoP6EndpointPlusSplitLowerMatrix_quadratic] at hPlusLower
  rw [factorTwoP6EndpointMinusSplitLowerMatrix_quadratic] at hMinusLower
  have hPlusEven := factorTwoP6EvenPlusLowerQuadratic_le_phaseDiagonal
    c0 c2 c4 c6
  have hMinusEven := factorTwoP6EvenMinusLowerQuadratic_le_phaseDiagonal
    c0 c2 c4 c6
  constructor
  · rw [factorTwoEndpointChannelPhase_intrinsicP0246_P135_b_zero]
    linarith
  · rw [factorTwoEndpointChannelPhase_intrinsicP0246_P135_b_zero]
    linarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineP6EndpointParityLiftStructural

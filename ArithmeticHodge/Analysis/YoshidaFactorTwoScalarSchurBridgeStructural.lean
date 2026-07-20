import ArithmeticHodge.Analysis.SparseEntriesRobustCertificate
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteEndpointPencilConvexity
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteLowToeplitz
import ArithmeticHodge.Analysis.YoshidaFactorTwoScalarTargetSelectors

set_option autoImplicit false

open Matrix

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoScalarSchurBridgeStructural

noncomputable section

open RatInterval
open SparseEntriesCertificate
open SparseEntriesRobustCertificate
open YoshidaFactorTwoPhaseConcreteEvenPerturbationAdaptation
open YoshidaFactorTwoPhaseConcreteCleanEvenMatrix
open YoshidaFactorTwoPhaseConcreteCleanOddMatrix
open YoshidaFactorTwoPhaseConcreteEndpointPencilConvexity
open YoshidaFactorTwoPhaseConcreteLowDiskSchur
open YoshidaFactorTwoPhaseConcreteLowMatrix
open YoshidaFactorTwoPhaseConcreteLowToeplitz
open YoshidaFactorTwoPhaseConcretePerturbationMoments
open YoshidaFactorTwoScalarTargetSelectors
open YoshidaOddGramPrefix

/-!
# Scalar-target handoff to robust matrix certificates

The production scalar selectors expose exact rational intervals through a
`Contains`/`width_le` API, whereas the robust-congruence theorem consumes a
rational center matrix together with a uniform absolute entrywise error.
The midpoint construction below is the exact bridge between those APIs.

In particular, every one of the six scalar families used by the concrete
factor-two matrices is within `1 / 2000000000` of a rational center.  This
uses half of the already compiled `1 / 1000000000` selector width and does
not introduce a numerical replay.
-/

/-- Rational midpoint of an exact rational interval. -/
def targetCenter (I : RatInterval) : ℚ := (I.lower + I.upper) / 2

/-- A contained real point is close to the rational midpoint by any rational
bound which dominates the interval half-width. -/
theorem abs_sub_targetCenter_le
    {I : RatInterval} {x : ℝ} {epsilon : ℚ}
    (hx : I.Contains x) (hwidth : width I / 2 ≤ epsilon) :
    |x - (targetCenter I : ℝ)| ≤ (epsilon : ℝ) := by
  have hhalf := abs_sub_center_le_halfWidth hx
  calc
    |x - (targetCenter I : ℝ)| ≤
        (((I.upper - I.lower) / 2 : ℚ) : ℝ) := by
      simpa only [targetCenter] using hhalf
    _ = ((width I / 2 : ℚ) : ℝ) := by rfl
    _ ≤ (epsilon : ℝ) := by exact_mod_cast hwidth

/-- Entrywise rational midpoint matrix attached to an interval matrix. -/
def targetCenterMatrix
    {n : Type*} (targets : Matrix n n RatInterval) : Matrix n n ℚ :=
  fun i j ↦ targetCenter (targets i j)

@[simp] theorem targetCenterMatrix_apply
    {n : Type*} (targets : Matrix n n RatInterval) (i j : n) :
    targetCenterMatrix targets i j = targetCenter (targets i j) := rfl

/-- Pointwise interval containment and half-width bounds give exactly the
entrywise closeness premise expected by robust congruence. -/
theorem matrix_entrywise_close_to_targetCenter
    {n : Type*} (A : Matrix n n ℝ)
    (targets : Matrix n n RatInterval) (epsilon : ℚ)
    (hcontains : ∀ i j, (targets i j).Contains (A i j))
    (hwidth : ∀ i j, width (targets i j) / 2 ≤ epsilon) :
    ∀ i j,
      |A i j - (targetCenterMatrix targets i j : ℝ)| ≤
        (epsilon : ℝ) := by
  intro i j
  exact abs_sub_targetCenter_le (hcontains i j) (hwidth i j)

/-- Interval-matrix specialization of the robust-congruence theorem.  A
caller can build every target entry compositionally from the scalar target
selectors, then discharge the analytic-to-rational `hclose` premise solely
from interval containment and width. -/
theorem posDef_of_intervalTargets_sparseEntries_robust_congruence
    {n : Type*} [Fintype n] [LinearOrder n]
    (A : Matrix n n ℝ) (targets : Matrix n n RatInterval)
    (entries : n → SparseEntries n) (epsilon : ℚ) (weights : n → ℚ)
    (hA : A.IsHermitian) (hcenter : (targetCenterMatrix targets).IsSymm)
    (hlower : ∀ i j, entriesValue (entries i) j ≠ 0 → j ≤ i)
    (hdiag : ∀ i, entriesValue (entries i) i ≠ 0)
    (hepsilon : 0 ≤ epsilon)
    (hcontains : ∀ i j, (targets i j).Contains (A i j))
    (hwidth : ∀ i j, width (targets i j) / 2 ≤ epsilon)
    (hweights : ∀ i, 0 < weights i)
    (hdominance : ∀ i,
      (∑ j ∈ Finset.univ.erase i,
          entriesRobustRadius entries (targetCenterMatrix targets)
              epsilon i j * weights j) <
        entriesRobustDiagonalLower entries (targetCenterMatrix targets)
            epsilon i * weights i) :
    A.PosDef := by
  exact posDef_of_sparseEntries_robust_congruence
    A entries (targetCenterMatrix targets) epsilon weights hA hcenter
    hlower hdiag hepsilon
    (matrix_entrywise_close_to_targetCenter
      A targets epsilon hcontains hwidth)
    hweights hdominance

/-! ## The six production scalar centers -/

/-- Uniform half-width error obtained from the compiled `1e-9` scalar
targets. -/
def factorTwoScalarTargetError : ℚ := 1 / 2000000000

private theorem half_width_le_factorTwoScalarTargetError
    {I : RatInterval} (hwidth : width I ≤ (1 / 1000000000 : ℚ)) :
    width I / 2 ≤ factorTwoScalarTargetError := by
  unfold factorTwoScalarTargetError
  nlinarith

/-- Rational center of the unified clean sine target. -/
def cleanSineCenter (n : ℕ) : ℚ := targetCenter (cleanSineTarget n)

/-- The clean sine moment is within `5e-10` of its rational center. -/
theorem cleanSineMoment_close_to_center {n : ℕ} (hn200 : n ≤ 200) :
    |yoshidaSineMoment n - (cleanSineCenter n : ℝ)| ≤
      (factorTwoScalarTargetError : ℝ) := by
  unfold cleanSineCenter
  exact abs_sub_targetCenter_le (cleanSineTarget_contains hn200)
    (half_width_le_factorTwoScalarTargetError
      (cleanSineTarget_width_le hn200))

/-- Rational center of the unified clean diagonal target. -/
def cleanDiagonalCenter (n : ℕ) : ℚ :=
  targetCenter (cleanDiagonalTarget n)

/-- The clean diagonal moment is within `5e-10` of its rational center. -/
theorem cleanDiagonalMoment_close_to_center {n : ℕ} (hn200 : n ≤ 200) :
    |yoshidaDiagonalMoment n - (cleanDiagonalCenter n : ℝ)| ≤
      (factorTwoScalarTargetError : ℝ) := by
  unfold cleanDiagonalCenter
  exact abs_sub_targetCenter_le (cleanDiagonalTarget_contains hn200)
    (half_width_le_factorTwoScalarTargetError
      (cleanDiagonalTarget_width_le hn200))

/-- Rational center of the unified symmetric sine target. -/
def symmetricSinCenter (n : FactorTwoCanonicalEvenIndex) : ℚ :=
  targetCenter (symmetricSinTarget n)

/-- The symmetric sine perturbation moment is within `5e-10` of its
rational center. -/
theorem symmetricSinMoment_close_to_center
    (n : FactorTwoCanonicalEvenIndex) :
    |factorTwoSymmetricSinMoment n.1 - (symmetricSinCenter n : ℝ)| ≤
      (factorTwoScalarTargetError : ℝ) := by
  unfold symmetricSinCenter
  exact abs_sub_targetCenter_le (symmetricSinTarget_contains n)
    (half_width_le_factorTwoScalarTargetError
      (symmetricSinTarget_width_le n))

/-- Rational center of the unified symmetric affine-cosine target. -/
def symmetricAffineCosCenter
    (n : FactorTwoCanonicalEvenIndex) : ℚ :=
  targetCenter (symmetricAffineCosTarget n)

/-- The symmetric affine-cosine perturbation moment is within `5e-10` of
its rational center. -/
theorem symmetricAffineCosMoment_close_to_center
    (n : FactorTwoCanonicalEvenIndex) :
    |factorTwoSymmetricAffineCosMoment n.1 -
        (symmetricAffineCosCenter n : ℝ)| ≤
      (factorTwoScalarTargetError : ℝ) := by
  unfold symmetricAffineCosCenter
  exact abs_sub_targetCenter_le (symmetricAffineCosTarget_contains n)
    (half_width_le_factorTwoScalarTargetError
      (symmetricAffineCosTarget_width_le n))

/-- Rational center of the unified antisymmetric one-minus-cosine target. -/
def antisymmetricOneSubCosCenter
    (n : FactorTwoCanonicalEvenIndex) : ℚ :=
  targetCenter (antisymmetricOneSubCosTarget n)

/-- The antisymmetric one-minus-cosine moment is within `5e-10` of its
rational center. -/
theorem antisymmetricOneSubCosMoment_close_to_center
    (n : FactorTwoCanonicalEvenIndex) :
    |factorTwoAntisymmetricOneSubCosMoment n.1 -
        (antisymmetricOneSubCosCenter n : ℝ)| ≤
      (factorTwoScalarTargetError : ℝ) := by
  unfold antisymmetricOneSubCosCenter
  exact abs_sub_targetCenter_le (antisymmetricOneSubCosTarget_contains n)
    (half_width_le_factorTwoScalarTargetError
      (antisymmetricOneSubCosTarget_width_le n))

/-- Rational center of the unified antisymmetric affine-sine target. -/
def antisymmetricAffineSinCenter
    (n : FactorTwoCanonicalEvenIndex) : ℚ :=
  targetCenter (antisymmetricAffineSinTarget n)

/-- The antisymmetric affine-sine moment is within `5e-10` of its rational
center. -/
theorem antisymmetricAffineSinMoment_close_to_center
    (n : FactorTwoCanonicalEvenIndex) :
    |factorTwoAntisymmetricAffineSinMoment n.1 -
        (antisymmetricAffineSinCenter n : ℝ)| ≤
      (factorTwoScalarTargetError : ℝ) := by
  unfold antisymmetricAffineSinCenter
  exact abs_sub_targetCenter_le (antisymmetricAffineSinTarget_contains n)
    (half_width_le_factorTwoScalarTargetError
      (antisymmetricAffineSinTarget_width_le n))

/-! ## Named true endpoint matrices and the scalar handoff -/

/-- True endpoint-adapted even pencil matrix at `a = 1`. -/
def factorTwoConcreteEvenPlusPencilMatrix :
    Matrix YoshidaEvenIndex YoshidaEvenIndex ℝ :=
  factorTwoConcreteAdaptedEvenCleanMatrix +
    factorTwoConcreteEvenPerturbationMatrix

/-- True endpoint-adapted even pencil matrix at `a = -1`. -/
def factorTwoConcreteEvenMinusPencilMatrix :
    Matrix YoshidaEvenIndex YoshidaEvenIndex ℝ :=
  factorTwoConcreteAdaptedEvenCleanMatrix -
    factorTwoConcreteEvenPerturbationMatrix

/-- True canonical odd pencil matrix at `a = 1`. -/
def factorTwoConcreteOddPlusPencilMatrix :
    Matrix YoshidaOddIndex YoshidaOddIndex ℝ :=
  factorTwoConcreteOddCleanMatrix + factorTwoConcreteOddPerturbationMatrix

/-- True canonical odd pencil matrix at `a = -1`. -/
def factorTwoConcreteOddMinusPencilMatrix :
    Matrix YoshidaOddIndex YoshidaOddIndex ℝ :=
  factorTwoConcreteOddCleanMatrix - factorTwoConcreteOddPerturbationMatrix

theorem factorTwoConcreteEvenPlusPencilMatrix_isHermitian :
    factorTwoConcreteEvenPlusPencilMatrix.IsHermitian :=
  factorTwoConcreteAdaptedEvenCleanMatrix_isHermitian.add
    factorTwoConcreteEvenPerturbationMatrix_isHermitian

theorem factorTwoConcreteEvenMinusPencilMatrix_isHermitian :
    factorTwoConcreteEvenMinusPencilMatrix.IsHermitian :=
  factorTwoConcreteAdaptedEvenCleanMatrix_isHermitian.sub
    factorTwoConcreteEvenPerturbationMatrix_isHermitian

theorem factorTwoConcreteOddPlusPencilMatrix_isHermitian :
    factorTwoConcreteOddPlusPencilMatrix.IsHermitian :=
  factorTwoConcreteOddCleanMatrix_isHermitian.add
    factorTwoConcreteOddPerturbationMatrix_isHermitian

theorem factorTwoConcreteOddMinusPencilMatrix_isHermitian :
    factorTwoConcreteOddMinusPencilMatrix.IsHermitian :=
  factorTwoConcreteOddCleanMatrix_isHermitian.sub
    factorTwoConcreteOddPerturbationMatrix_isHermitian

/-- The positive even endpoint pencil value is the quadratic form of its
named true matrix. -/
theorem factorTwoConcreteEvenPencilValue_one_eq_matrixQuadratic
    (e : YoshidaEvenIndex → ℝ) :
    factorTwoConcreteEvenPencilValue 1 e =
      e ⬝ᵥ (factorTwoConcreteEvenPlusPencilMatrix *ᵥ e) := by
  simp [factorTwoConcreteEvenPencilValue,
    factorTwoConcreteEvenPlusPencilMatrix]

/-- The negative even endpoint pencil value is the quadratic form of its
named true matrix. -/
theorem factorTwoConcreteEvenPencilValue_neg_one_eq_matrixQuadratic
    (e : YoshidaEvenIndex → ℝ) :
    factorTwoConcreteEvenPencilValue (-1) e =
      e ⬝ᵥ (factorTwoConcreteEvenMinusPencilMatrix *ᵥ e) := by
  simp [factorTwoConcreteEvenPencilValue,
    factorTwoConcreteEvenMinusPencilMatrix, sub_eq_add_neg]

/-- The positive odd endpoint pencil value is the quadratic form of its
named true matrix. -/
theorem factorTwoConcreteOddPencilValue_one_eq_matrixQuadratic
    (o : YoshidaOddIndex → ℝ) :
    factorTwoConcreteOddPencilValue 1 o =
      o ⬝ᵥ (factorTwoConcreteOddPlusPencilMatrix *ᵥ o) := by
  simp [factorTwoConcreteOddPencilValue,
    factorTwoConcreteOddPlusPencilMatrix]

/-- The negative odd endpoint pencil value is the quadratic form of its
named true matrix. -/
theorem factorTwoConcreteOddPencilValue_neg_one_eq_matrixQuadratic
    (o : YoshidaOddIndex → ℝ) :
    factorTwoConcreteOddPencilValue (-1) o =
      o ⬝ᵥ (factorTwoConcreteOddMinusPencilMatrix *ᵥ o) := by
  simp [factorTwoConcreteOddPencilValue,
    factorTwoConcreteOddMinusPencilMatrix, sub_eq_add_neg]

/-- Positive semidefiniteness of the four named endpoint matrices supplies
exactly the four scalar endpoint hypotheses consumed by pencil convexity. -/
theorem factorTwoConcreteEndpointPencilValues_nonneg_of_posSemidef
    (hEvenPlus : factorTwoConcreteEvenPlusPencilMatrix.PosSemidef)
    (hEvenMinus : factorTwoConcreteEvenMinusPencilMatrix.PosSemidef)
    (hOddPlus : factorTwoConcreteOddPlusPencilMatrix.PosSemidef)
    (hOddMinus : factorTwoConcreteOddMinusPencilMatrix.PosSemidef) :
    (∀ e : YoshidaEvenIndex → ℝ,
      0 ≤ factorTwoConcreteEvenPencilValue 1 e) ∧
    (∀ e : YoshidaEvenIndex → ℝ,
      0 ≤ factorTwoConcreteEvenPencilValue (-1) e) ∧
    (∀ o : YoshidaOddIndex → ℝ,
      0 ≤ factorTwoConcreteOddPencilValue 1 o) ∧
    (∀ o : YoshidaOddIndex → ℝ,
      0 ≤ factorTwoConcreteOddPencilValue (-1) o) := by
  constructor
  · intro e
    rw [factorTwoConcreteEvenPencilValue_one_eq_matrixQuadratic]
    simpa only [star_trivial] using hEvenPlus.dotProduct_mulVec_nonneg e
  constructor
  · intro e
    rw [factorTwoConcreteEvenPencilValue_neg_one_eq_matrixQuadratic]
    simpa only [star_trivial] using hEvenMinus.dotProduct_mulVec_nonneg e
  constructor
  · intro o
    rw [factorTwoConcreteOddPencilValue_one_eq_matrixQuadratic]
    simpa only [star_trivial] using hOddPlus.dotProduct_mulVec_nonneg o
  · intro o
    rw [factorTwoConcreteOddPencilValue_neg_one_eq_matrixQuadratic]
    simpa only [star_trivial] using hOddMinus.dotProduct_mulVec_nonneg o

/-- Robust congruence proves positive definiteness; this corollary erases
only the strictness that the division-free scalar Schur criterion does not
need. -/
theorem factorTwoConcreteEndpointPencilValues_nonneg_of_posDef
    (hEvenPlus : factorTwoConcreteEvenPlusPencilMatrix.PosDef)
    (hEvenMinus : factorTwoConcreteEvenMinusPencilMatrix.PosDef)
    (hOddPlus : factorTwoConcreteOddPlusPencilMatrix.PosDef)
    (hOddMinus : factorTwoConcreteOddMinusPencilMatrix.PosDef) :
    (∀ e : YoshidaEvenIndex → ℝ,
      0 ≤ factorTwoConcreteEvenPencilValue 1 e) ∧
    (∀ e : YoshidaEvenIndex → ℝ,
      0 ≤ factorTwoConcreteEvenPencilValue (-1) e) ∧
    (∀ o : YoshidaOddIndex → ℝ,
      0 ≤ factorTwoConcreteOddPencilValue 1 o) ∧
    (∀ o : YoshidaOddIndex → ℝ,
      0 ≤ factorTwoConcreteOddPencilValue (-1) o) :=
  factorTwoConcreteEndpointPencilValues_nonneg_of_posSemidef
    hEvenPlus.posSemidef hEvenMinus.posSemidef
    hOddPlus.posSemidef hOddMinus.posSemidef

/-! ## Quantitative floor handoff -/

/-- Lower bounds for the two diagonal pencils and an upper bound for the
alternating square imply the inverse-free scalar Schur inequality once their
rational budget closes.  This records the direction of every bound needed by
the eventual finite certificate. -/
theorem factorTwoConcreteDiskSchur_of_floors
    (a : ℝ) (ha : a ^ 2 ≤ 1)
    (e : YoshidaEvenIndex → ℝ) (o : YoshidaOddIndex → ℝ)
    (evenFloor oddFloor alternatingSquareCap : ℝ)
    (hEvenFloorNonneg : 0 ≤ evenFloor)
    (hOddFloorNonneg : 0 ≤ oddFloor)
    (hEvenFloor : evenFloor ≤ factorTwoConcreteEvenPencilValue a e)
    (hOddFloor : oddFloor ≤ factorTwoConcreteOddPencilValue a o)
    (hAlternatingCap :
      factorTwoConcreteAlternatingValue e o ^ 2 ≤ alternatingSquareCap)
    (hBudget :
      (1 - a ^ 2) * alternatingSquareCap ≤
        4 * evenFloor * oddFloor) :
    (1 - a ^ 2) * factorTwoConcreteAlternatingValue e o ^ 2 ≤
      4 * factorTwoConcreteEvenPencilValue a e *
        factorTwoConcreteOddPencilValue a o := by
  have hPhaseNonneg : 0 ≤ 1 - a ^ 2 := sub_nonneg.mpr ha
  have hEvenNonneg : 0 ≤ factorTwoConcreteEvenPencilValue a e :=
    hEvenFloorNonneg.trans hEvenFloor
  have hFloorProduct :
      evenFloor * oddFloor ≤
        factorTwoConcreteEvenPencilValue a e *
          factorTwoConcreteOddPencilValue a o :=
    mul_le_mul hEvenFloor hOddFloor hOddFloorNonneg hEvenNonneg
  calc
    (1 - a ^ 2) * factorTwoConcreteAlternatingValue e o ^ 2 ≤
        (1 - a ^ 2) * alternatingSquareCap :=
      mul_le_mul_of_nonneg_left hAlternatingCap hPhaseNonneg
    _ ≤ 4 * evenFloor * oddFloor := hBudget
    _ ≤ 4 * factorTwoConcreteEvenPencilValue a e *
          factorTwoConcreteOddPencilValue a o := by
      nlinarith

/-- Family form of the quantitative-floor handoff.  Once the four endpoint
matrices are certified positive definite, concrete floor/cap functions and a
rational budget are sufficient for the complete finite-low phase theorem. -/
theorem factorTwoConcreteLowPhase_nonneg_of_endpoint_posDef_and_floors
    (hEvenPlus : factorTwoConcreteEvenPlusPencilMatrix.PosDef)
    (hEvenMinus : factorTwoConcreteEvenMinusPencilMatrix.PosDef)
    (hOddPlus : factorTwoConcreteOddPlusPencilMatrix.PosDef)
    (hOddMinus : factorTwoConcreteOddMinusPencilMatrix.PosDef)
    (evenFloor : ℝ → (YoshidaEvenIndex → ℝ) → ℝ)
    (oddFloor : ℝ → (YoshidaOddIndex → ℝ) → ℝ)
    (alternatingSquareCap :
      (YoshidaEvenIndex → ℝ) → (YoshidaOddIndex → ℝ) → ℝ)
    (hEvenFloorNonneg : ∀ a e, 0 ≤ evenFloor a e)
    (hOddFloorNonneg : ∀ a o, 0 ≤ oddFloor a o)
    (hEvenFloor : ∀ a e,
      evenFloor a e ≤ factorTwoConcreteEvenPencilValue a e)
    (hOddFloor : ∀ a o,
      oddFloor a o ≤ factorTwoConcreteOddPencilValue a o)
    (hAlternatingCap : ∀ e o,
      factorTwoConcreteAlternatingValue e o ^ 2 ≤
        alternatingSquareCap e o)
    (hBudget : ∀ a : ℝ, a ^ 2 ≤ 1 →
      ∀ (e : YoshidaEvenIndex → ℝ) (o : YoshidaOddIndex → ℝ),
        (1 - a ^ 2) * alternatingSquareCap e o ≤
          4 * evenFloor a e * oddFloor a o)
    (e : YoshidaEvenIndex → ℝ) (o : YoshidaOddIndex → ℝ)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    0 ≤ YoshidaFactorTwoPhaseFullProfile.factorTwoEndpointChannelPhase
      (factorTwoAdaptedEvenLowSynthesis e)
      (factorTwoOddLowSynthesis o) a b := by
  obtain ⟨hEvenPlus', hEvenMinus', hOddPlus', hOddMinus'⟩ :=
    factorTwoConcreteEndpointPencilValues_nonneg_of_posDef
      hEvenPlus hEvenMinus hOddPlus hOddMinus
  exact factorTwoConcreteLowPhase_nonneg_of_endpoint_pencils_and_disk_schur
    hEvenPlus' hEvenMinus' hOddPlus' hOddMinus' (by
      intro a' ha' e' o'
      exact factorTwoConcreteDiskSchur_of_floors a' ha' e' o'
        (evenFloor a' e') (oddFloor a' o') (alternatingSquareCap e' o')
        (hEvenFloorNonneg a' e') (hOddFloorNonneg a' o')
        (hEvenFloor a' e') (hOddFloor a' o')
        (hAlternatingCap e' o') (hBudget a' ha' e' o'))
      e o a b hab

/-- Final structural handoff for the production finite-low scalar-Schur
track.  Robust congruence is expected to prove the four endpoint `PosDef`
hypotheses.  Endpoint chord interpolation then supplies both diagonal pencils
throughout `a² ≤ 1`; the only remaining hypothesis is the inverse-free
coupling inequality itself. -/
theorem factorTwoConcreteLowPhase_nonneg_of_endpoint_posDef_and_disk_schur
    (hEvenPlus : factorTwoConcreteEvenPlusPencilMatrix.PosDef)
    (hEvenMinus : factorTwoConcreteEvenMinusPencilMatrix.PosDef)
    (hOddPlus : factorTwoConcreteOddPlusPencilMatrix.PosDef)
    (hOddMinus : factorTwoConcreteOddMinusPencilMatrix.PosDef)
    (hSchur : ∀ a : ℝ, a ^ 2 ≤ 1 →
      ∀ (e : YoshidaEvenIndex → ℝ) (o : YoshidaOddIndex → ℝ),
        (1 - a ^ 2) * factorTwoConcreteAlternatingValue e o ^ 2 ≤
          4 * factorTwoConcreteEvenPencilValue a e *
            factorTwoConcreteOddPencilValue a o)
    (e : YoshidaEvenIndex → ℝ) (o : YoshidaOddIndex → ℝ)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    0 ≤ YoshidaFactorTwoPhaseFullProfile.factorTwoEndpointChannelPhase
      (factorTwoAdaptedEvenLowSynthesis e)
      (factorTwoOddLowSynthesis o) a b := by
  obtain ⟨hEvenPlus', hEvenMinus', hOddPlus', hOddMinus'⟩ :=
    factorTwoConcreteEndpointPencilValues_nonneg_of_posDef
      hEvenPlus hEvenMinus hOddPlus hOddMinus
  exact factorTwoConcreteLowPhase_nonneg_of_endpoint_pencils_and_disk_schur
    hEvenPlus' hEvenMinus' hOddPlus' hOddMinus' hSchur e o a b hab

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoScalarSchurBridgeStructural

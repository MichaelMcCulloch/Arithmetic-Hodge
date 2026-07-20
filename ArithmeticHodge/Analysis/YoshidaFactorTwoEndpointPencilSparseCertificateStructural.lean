import ArithmeticHodge.Analysis.YoshidaFactorTwoCanonicalEndpointPencilBridgeStructural

set_option autoImplicit false

open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoEndpointPencilSparseCertificateStructural

noncomputable section

open SparseEntriesCertificate
open SparseEntriesRobustCertificate
open YoshidaFactorTwoCanonicalEndpointPencilBridgeStructural
open YoshidaFactorTwoEndpointPencilEntryTargets
open YoshidaFactorTwoScalarSchurBridgeStructural
open YoshidaOddGramPrefix

/-!
# Sparse certificates for the four factor-two endpoint pencils

This module fixes the analytic side of the robust-congruence interface.  A
generated certificate only has to provide its sparse rows, a uniform target
half-width, positive weights, and the exact rational weighted-dominance
checks.  For the two even signs the robust certificate is applied to the
canonical frequencies `0, ..., 200`; the resulting positive definiteness is
then pulled back to the production endpoint-adapted basis.
-/

@[reducible] noncomputable def factorTwoCanonicalEndpointLinearOrder :
    LinearOrder FactorTwoCanonicalEndpointEvenIndex :=
  LinearOrder.lift' factorTwoCanonicalEndpointIndex
    factorTwoCanonicalEndpointIndex_injective

local instance : LinearOrder FactorTwoCanonicalEndpointEvenIndex :=
  factorTwoCanonicalEndpointLinearOrder

local instance : DecidableEq FactorTwoCanonicalEndpointEvenIndex :=
  factorTwoCanonicalEndpointLinearOrder.toDecidableEq

/-! ## Arbitrary rational centers -/

/-- An exact rational interval is covered by the closed box of radius
`epsilon` about `center`.  This is the interface used by generated rounded
centers: the rounding error is included in `epsilon`, then checked against
both exact interval endpoints. -/
def IntervalTargetCoveredByCenter
    (I : RatInterval) (center epsilon : ℚ) : Prop :=
  center - epsilon ≤ I.lower ∧ I.upper ≤ center + epsilon

/-- A real point contained in an interval covered by a rational center box is
entrywise close to that center. -/
theorem abs_sub_center_le_of_intervalTargetCoveredByCenter
    {I : RatInterval} {x : ℝ} {center epsilon : ℚ}
    (hx : I.Contains x)
    (hcover : IntervalTargetCoveredByCenter I center epsilon) :
    |x - (center : ℝ)| ≤ (epsilon : ℝ) := by
  rcases hx with ⟨hxLower, hxUpper⟩
  rcases hcover with ⟨hcoverLower, hcoverUpper⟩
  have hcoverLowerReal :
      ((center - epsilon : ℚ) : ℝ) ≤ (I.lower : ℝ) := by
    exact_mod_cast hcoverLower
  have hcoverUpperReal :
      (I.upper : ℝ) ≤ ((center + epsilon : ℚ) : ℝ) := by
    exact_mod_cast hcoverUpper
  rw [abs_le]
  constructor <;> push_cast at hcoverLowerReal hcoverUpperReal ⊢ <;>
    linarith

/-- Interval containment and exact center-box coverage provide the closeness
hypothesis for an arbitrary rational center matrix. -/
theorem matrix_entrywise_close_to_coveredCenter
    {n : Type*} (A : Matrix n n ℝ)
    (targets : Matrix n n RatInterval) (centers : Matrix n n ℚ)
    (epsilon : ℚ)
    (hcontains : ∀ i j, (targets i j).Contains (A i j))
    (hcover : ∀ i j,
      IntervalTargetCoveredByCenter (targets i j) (centers i j) epsilon) :
    ∀ i j, |A i j - (centers i j : ℝ)| ≤ (epsilon : ℝ) := by
  intro i j
  exact abs_sub_center_le_of_intervalTargetCoveredByCenter
    (hcontains i j) (hcover i j)

/-- Robust sparse congruence specialized to interval targets covered by an
arbitrary rational center matrix. -/
theorem posDef_of_intervalTargets_sparseEntries_robust_congruence_atCenter
    {n : Type*} [Fintype n] [LinearOrder n]
    (A : Matrix n n ℝ) (targets : Matrix n n RatInterval)
    (centers : Matrix n n ℚ) (entries : n → SparseEntries n)
    (epsilon : ℚ) (weights : n → ℚ)
    (hA : A.IsHermitian) (hcenters : centers.IsSymm)
    (hlower : ∀ i j, entriesValue (entries i) j ≠ 0 → j ≤ i)
    (hdiag : ∀ i, entriesValue (entries i) i ≠ 0)
    (hepsilon : 0 ≤ epsilon)
    (hcontains : ∀ i j, (targets i j).Contains (A i j))
    (hcover : ∀ i j,
      IntervalTargetCoveredByCenter (targets i j) (centers i j) epsilon)
    (hweights : ∀ i, 0 < weights i)
    (hdominance : ∀ i,
      (∑ j ∈ Finset.univ.erase i,
          entriesRobustRadius entries centers epsilon i j * weights j) <
        entriesRobustDiagonalLower entries centers epsilon i * weights i) :
    A.PosDef := by
  exact posDef_of_sparseEntries_robust_congruence
    A entries centers epsilon weights hA hcenters hlower hdiag hepsilon
    (matrix_entrywise_close_to_coveredCenter
      A targets centers epsilon hcontains hcover)
    hweights hdominance

/-- A robust sparse certificate for the positive canonical even endpoint
pulls back to the positive production endpoint pencil. -/
theorem factorTwoConcreteEvenPlusPencilMatrix_posDef_of_sparseCertificate
    (entries : FactorTwoCanonicalEndpointEvenIndex →
      SparseEntries FactorTwoCanonicalEndpointEvenIndex)
    (epsilon : ℚ)
    (weights : FactorTwoCanonicalEndpointEvenIndex → ℚ)
    (hlower : ∀ i j, entriesValue (entries i) j ≠ 0 →
      factorTwoCanonicalEndpointLinearOrder.le j i)
    (hdiag : ∀ i, entriesValue (entries i) i ≠ 0)
    (hepsilon : 0 ≤ epsilon)
    (hwidth : ∀ i j,
      RatInterval.width
          (factorTwoCanonicalEndpointEvenPlusPencilTargetMatrix i j) / 2 ≤
        epsilon)
    (hweights : ∀ i, 0 < weights i)
    (hdominance : ∀ i,
      (∑ j ∈ Finset.univ.erase i,
          entriesRobustRadius entries
              (targetCenterMatrix
                factorTwoCanonicalEndpointEvenPlusPencilTargetMatrix)
              epsilon i j * weights j) <
        entriesRobustDiagonalLower entries
            (targetCenterMatrix
              factorTwoCanonicalEndpointEvenPlusPencilTargetMatrix)
            epsilon i * weights i) :
    factorTwoConcreteEvenPlusPencilMatrix.PosDef := by
  apply factorTwoConcreteEvenPlusPencilMatrix_posDef_of_canonical
  exact posDef_of_intervalTargets_sparseEntries_robust_congruence
    factorTwoCanonicalEndpointEvenPlusPencilMatrix
    factorTwoCanonicalEndpointEvenPlusPencilTargetMatrix
    entries epsilon weights
    factorTwoCanonicalEndpointEvenPlusPencilMatrix_isHermitian
    factorTwoCanonicalEndpointEvenPlusPencilTargetMatrix_center_isSymm
    hlower hdiag hepsilon
    factorTwoCanonicalEndpointEvenPlusPencilTargetMatrix_contains
    hwidth hweights hdominance

/-- A robust sparse certificate for the negative canonical even endpoint
pulls back to the negative production endpoint pencil. -/
theorem factorTwoConcreteEvenMinusPencilMatrix_posDef_of_sparseCertificate
    (entries : FactorTwoCanonicalEndpointEvenIndex →
      SparseEntries FactorTwoCanonicalEndpointEvenIndex)
    (epsilon : ℚ)
    (weights : FactorTwoCanonicalEndpointEvenIndex → ℚ)
    (hlower : ∀ i j, entriesValue (entries i) j ≠ 0 →
      factorTwoCanonicalEndpointLinearOrder.le j i)
    (hdiag : ∀ i, entriesValue (entries i) i ≠ 0)
    (hepsilon : 0 ≤ epsilon)
    (hwidth : ∀ i j,
      RatInterval.width
          (factorTwoCanonicalEndpointEvenMinusPencilTargetMatrix i j) / 2 ≤
        epsilon)
    (hweights : ∀ i, 0 < weights i)
    (hdominance : ∀ i,
      (∑ j ∈ Finset.univ.erase i,
          entriesRobustRadius entries
              (targetCenterMatrix
                factorTwoCanonicalEndpointEvenMinusPencilTargetMatrix)
              epsilon i j * weights j) <
        entriesRobustDiagonalLower entries
            (targetCenterMatrix
              factorTwoCanonicalEndpointEvenMinusPencilTargetMatrix)
            epsilon i * weights i) :
    factorTwoConcreteEvenMinusPencilMatrix.PosDef := by
  apply factorTwoConcreteEvenMinusPencilMatrix_posDef_of_canonical
  exact posDef_of_intervalTargets_sparseEntries_robust_congruence
    factorTwoCanonicalEndpointEvenMinusPencilMatrix
    factorTwoCanonicalEndpointEvenMinusPencilTargetMatrix
    entries epsilon weights
    factorTwoCanonicalEndpointEvenMinusPencilMatrix_isHermitian
    factorTwoCanonicalEndpointEvenMinusPencilTargetMatrix_center_isSymm
    hlower hdiag hepsilon
    factorTwoCanonicalEndpointEvenMinusPencilTargetMatrix_contains
    hwidth hweights hdominance

/-- A robust sparse certificate for the positive odd target proves the true
positive odd endpoint pencil positive definite. -/
theorem factorTwoConcreteOddPlusPencilMatrix_posDef_of_sparseCertificate
    (entries : YoshidaOddIndex → SparseEntries YoshidaOddIndex)
    (epsilon : ℚ) (weights : YoshidaOddIndex → ℚ)
    (hlower : ∀ i j, entriesValue (entries i) j ≠ 0 → j ≤ i)
    (hdiag : ∀ i, entriesValue (entries i) i ≠ 0)
    (hepsilon : 0 ≤ epsilon)
    (hwidth : ∀ i j,
      RatInterval.width
          (factorTwoConcreteOddPlusPencilTargetMatrix i j) / 2 ≤ epsilon)
    (hweights : ∀ i, 0 < weights i)
    (hdominance : ∀ i,
      (∑ j ∈ Finset.univ.erase i,
          entriesRobustRadius entries
              (targetCenterMatrix factorTwoConcreteOddPlusPencilTargetMatrix)
              epsilon i j * weights j) <
        entriesRobustDiagonalLower entries
            (targetCenterMatrix factorTwoConcreteOddPlusPencilTargetMatrix)
            epsilon i * weights i) :
    factorTwoConcreteOddPlusPencilMatrix.PosDef := by
  exact posDef_of_intervalTargets_sparseEntries_robust_congruence
    factorTwoConcreteOddPlusPencilMatrix
    factorTwoConcreteOddPlusPencilTargetMatrix
    entries epsilon weights factorTwoConcreteOddPlusPencilMatrix_isHermitian
    factorTwoConcreteOddPlusPencilTargetMatrix_center_isSymm
    hlower hdiag hepsilon factorTwoConcreteOddPlusPencilTargetMatrix_contains
    hwidth hweights hdominance

/-- A robust sparse certificate for the negative odd target proves the true
negative odd endpoint pencil positive definite. -/
theorem factorTwoConcreteOddMinusPencilMatrix_posDef_of_sparseCertificate
    (entries : YoshidaOddIndex → SparseEntries YoshidaOddIndex)
    (epsilon : ℚ) (weights : YoshidaOddIndex → ℚ)
    (hlower : ∀ i j, entriesValue (entries i) j ≠ 0 → j ≤ i)
    (hdiag : ∀ i, entriesValue (entries i) i ≠ 0)
    (hepsilon : 0 ≤ epsilon)
    (hwidth : ∀ i j,
      RatInterval.width
          (factorTwoConcreteOddMinusPencilTargetMatrix i j) / 2 ≤ epsilon)
    (hweights : ∀ i, 0 < weights i)
    (hdominance : ∀ i,
      (∑ j ∈ Finset.univ.erase i,
          entriesRobustRadius entries
              (targetCenterMatrix factorTwoConcreteOddMinusPencilTargetMatrix)
              epsilon i j * weights j) <
        entriesRobustDiagonalLower entries
            (targetCenterMatrix factorTwoConcreteOddMinusPencilTargetMatrix)
            epsilon i * weights i) :
    factorTwoConcreteOddMinusPencilMatrix.PosDef := by
  exact posDef_of_intervalTargets_sparseEntries_robust_congruence
    factorTwoConcreteOddMinusPencilMatrix
    factorTwoConcreteOddMinusPencilTargetMatrix
    entries epsilon weights factorTwoConcreteOddMinusPencilMatrix_isHermitian
    factorTwoConcreteOddMinusPencilTargetMatrix_center_isSymm
    hlower hdiag hepsilon factorTwoConcreteOddMinusPencilTargetMatrix_contains
    hwidth hweights hdominance

/-! ## Rounded-center endpoint adapters -/

/-- A rounded-center sparse certificate for the positive canonical even
endpoint pulls back to the production endpoint-adapted matrix. -/
theorem factorTwoConcreteEvenPlusPencilMatrix_posDef_of_sparseCertificate_atCenter
    (centers : Matrix FactorTwoCanonicalEndpointEvenIndex
      FactorTwoCanonicalEndpointEvenIndex ℚ)
    (entries : FactorTwoCanonicalEndpointEvenIndex →
      SparseEntries FactorTwoCanonicalEndpointEvenIndex)
    (epsilon : ℚ)
    (weights : FactorTwoCanonicalEndpointEvenIndex → ℚ)
    (hcenters : centers.IsSymm)
    (hlower : ∀ i j, entriesValue (entries i) j ≠ 0 →
      factorTwoCanonicalEndpointLinearOrder.le j i)
    (hdiag : ∀ i, entriesValue (entries i) i ≠ 0)
    (hepsilon : 0 ≤ epsilon)
    (hcover : ∀ i j,
      IntervalTargetCoveredByCenter
        (factorTwoCanonicalEndpointEvenPlusPencilTargetMatrix i j)
        (centers i j) epsilon)
    (hweights : ∀ i, 0 < weights i)
    (hdominance : ∀ i,
      (∑ j ∈ Finset.univ.erase i,
          entriesRobustRadius entries centers epsilon i j * weights j) <
        entriesRobustDiagonalLower entries centers epsilon i * weights i) :
    factorTwoConcreteEvenPlusPencilMatrix.PosDef := by
  apply factorTwoConcreteEvenPlusPencilMatrix_posDef_of_canonical
  exact posDef_of_intervalTargets_sparseEntries_robust_congruence_atCenter
    factorTwoCanonicalEndpointEvenPlusPencilMatrix
    factorTwoCanonicalEndpointEvenPlusPencilTargetMatrix centers entries
    epsilon weights factorTwoCanonicalEndpointEvenPlusPencilMatrix_isHermitian
    hcenters hlower hdiag hepsilon
    factorTwoCanonicalEndpointEvenPlusPencilTargetMatrix_contains hcover
    hweights hdominance

/-- A rounded-center sparse certificate for the negative canonical even
endpoint pulls back to the production endpoint-adapted matrix. -/
theorem factorTwoConcreteEvenMinusPencilMatrix_posDef_of_sparseCertificate_atCenter
    (centers : Matrix FactorTwoCanonicalEndpointEvenIndex
      FactorTwoCanonicalEndpointEvenIndex ℚ)
    (entries : FactorTwoCanonicalEndpointEvenIndex →
      SparseEntries FactorTwoCanonicalEndpointEvenIndex)
    (epsilon : ℚ)
    (weights : FactorTwoCanonicalEndpointEvenIndex → ℚ)
    (hcenters : centers.IsSymm)
    (hlower : ∀ i j, entriesValue (entries i) j ≠ 0 →
      factorTwoCanonicalEndpointLinearOrder.le j i)
    (hdiag : ∀ i, entriesValue (entries i) i ≠ 0)
    (hepsilon : 0 ≤ epsilon)
    (hcover : ∀ i j,
      IntervalTargetCoveredByCenter
        (factorTwoCanonicalEndpointEvenMinusPencilTargetMatrix i j)
        (centers i j) epsilon)
    (hweights : ∀ i, 0 < weights i)
    (hdominance : ∀ i,
      (∑ j ∈ Finset.univ.erase i,
          entriesRobustRadius entries centers epsilon i j * weights j) <
        entriesRobustDiagonalLower entries centers epsilon i * weights i) :
    factorTwoConcreteEvenMinusPencilMatrix.PosDef := by
  apply factorTwoConcreteEvenMinusPencilMatrix_posDef_of_canonical
  exact posDef_of_intervalTargets_sparseEntries_robust_congruence_atCenter
    factorTwoCanonicalEndpointEvenMinusPencilMatrix
    factorTwoCanonicalEndpointEvenMinusPencilTargetMatrix centers entries
    epsilon weights factorTwoCanonicalEndpointEvenMinusPencilMatrix_isHermitian
    hcenters hlower hdiag hepsilon
    factorTwoCanonicalEndpointEvenMinusPencilTargetMatrix_contains hcover
    hweights hdominance

/-- A rounded-center sparse certificate proves the positive odd endpoint
matrix positive definite. -/
theorem factorTwoConcreteOddPlusPencilMatrix_posDef_of_sparseCertificate_atCenter
    (centers : Matrix YoshidaOddIndex YoshidaOddIndex ℚ)
    (entries : YoshidaOddIndex → SparseEntries YoshidaOddIndex)
    (epsilon : ℚ) (weights : YoshidaOddIndex → ℚ)
    (hcenters : centers.IsSymm)
    (hlower : ∀ i j, entriesValue (entries i) j ≠ 0 → j ≤ i)
    (hdiag : ∀ i, entriesValue (entries i) i ≠ 0)
    (hepsilon : 0 ≤ epsilon)
    (hcover : ∀ i j,
      IntervalTargetCoveredByCenter
        (factorTwoConcreteOddPlusPencilTargetMatrix i j)
        (centers i j) epsilon)
    (hweights : ∀ i, 0 < weights i)
    (hdominance : ∀ i,
      (∑ j ∈ Finset.univ.erase i,
          entriesRobustRadius entries centers epsilon i j * weights j) <
        entriesRobustDiagonalLower entries centers epsilon i * weights i) :
    factorTwoConcreteOddPlusPencilMatrix.PosDef := by
  exact posDef_of_intervalTargets_sparseEntries_robust_congruence_atCenter
    factorTwoConcreteOddPlusPencilMatrix
    factorTwoConcreteOddPlusPencilTargetMatrix centers entries epsilon weights
    factorTwoConcreteOddPlusPencilMatrix_isHermitian hcenters hlower hdiag
    hepsilon factorTwoConcreteOddPlusPencilTargetMatrix_contains hcover
    hweights hdominance

/-- A rounded-center sparse certificate proves the negative odd endpoint
matrix positive definite. -/
theorem factorTwoConcreteOddMinusPencilMatrix_posDef_of_sparseCertificate_atCenter
    (centers : Matrix YoshidaOddIndex YoshidaOddIndex ℚ)
    (entries : YoshidaOddIndex → SparseEntries YoshidaOddIndex)
    (epsilon : ℚ) (weights : YoshidaOddIndex → ℚ)
    (hcenters : centers.IsSymm)
    (hlower : ∀ i j, entriesValue (entries i) j ≠ 0 → j ≤ i)
    (hdiag : ∀ i, entriesValue (entries i) i ≠ 0)
    (hepsilon : 0 ≤ epsilon)
    (hcover : ∀ i j,
      IntervalTargetCoveredByCenter
        (factorTwoConcreteOddMinusPencilTargetMatrix i j)
        (centers i j) epsilon)
    (hweights : ∀ i, 0 < weights i)
    (hdominance : ∀ i,
      (∑ j ∈ Finset.univ.erase i,
          entriesRobustRadius entries centers epsilon i j * weights j) <
        entriesRobustDiagonalLower entries centers epsilon i * weights i) :
    factorTwoConcreteOddMinusPencilMatrix.PosDef := by
  exact posDef_of_intervalTargets_sparseEntries_robust_congruence_atCenter
    factorTwoConcreteOddMinusPencilMatrix
    factorTwoConcreteOddMinusPencilTargetMatrix centers entries epsilon weights
    factorTwoConcreteOddMinusPencilMatrix_isHermitian hcenters hlower hdiag
    hepsilon factorTwoConcreteOddMinusPencilTargetMatrix_contains hcover
    hweights hdominance

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoEndpointPencilSparseCertificateStructural

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

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoEndpointPencilSparseCertificateStructural

import ArithmeticHodge.Analysis.YoshidaFourCellEvenEndpointSeedFiniteSevenClosureStructural
import ArithmeticHodge.Analysis.YoshidaFourCellRegularKernelLowerStructural

set_option autoImplicit false

open MeasureTheory Polynomial Real Set
open scoped Interval

namespace ArithmeticHodge.Analysis.YoshidaFourCellEvenFiniteSevenTailAssemblyStructural

noncomputable section

open ShiftedLegendreLogEnergyOrthogonalProjection
open ShiftedLegendreBasis
open ShiftedLegendreFiniteEnergyGap
open ShiftedLegendreL2Basis
open CenteredEndpointCorrelation
open TwoByTwoSchur
open UnitIntervalLogEnergyAffine
open YoshidaConstantBounds
open YoshidaFactorTwoIntegrableLagRepresenterStructural
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoContinuousLagRepresenterStructural
open YoshidaFactorTwoFixedLagRepresenterStructural
open YoshidaFactorTwoPhaseHigherLegendreDecomposition
open YoshidaFactorTwoPhaseIntrinsicHigherResidual
open YoshidaFactorTwoPhaseIntrinsicNineFullMixedDecompositionStructural
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFourCellEvenEndpointCapacityCauchyStructural
open YoshidaFourCellEvenEndpointCoshSchurStructural
open YoshidaFourCellEvenEndpointSeedCutoffEightBridgeStructural
open YoshidaFourCellEvenEndpointSeedCapacityCrossStructural
open YoshidaFourCellEvenEndpointSeedFiniteSevenClosureStructural
open YoshidaFourCellEvenEndpointSeedRegularRemainderStructural
open YoshidaFourCellEvenEndpointSeedUniversalClosureStructural
open YoshidaFourCellEvenPolarSchurStructural
open YoshidaFourCellEvenZeroCoshRegularStructural
open YoshidaFourCellParityHalfFoldStructural
open YoshidaFourCellParityOperatorStructural
open YoshidaFourCellRegularKernelLowerStructural
open YoshidaEndpointPotentialIntegrable
open YoshidaEndpointPotentialBound
open YoshidaRegularKernelBound

/-!
# Exact finite-seven / `P14+` tail assembly

The finite-seven certificate controls the bordered diagonal of the six
cosh-quotient modes.  The cutoff-fourteen theorem controls the complete
endpoint row by that finite diagonal plus a tail charge.  This file records
the exact scalar left after those two results are put together.

No entry enclosure is asserted here.  In particular, the theorem below
shows that the current `1 / 16` tail charge cannot simply be discarded: the
fixed endpoint seed diagonal is strictly smaller than `1 / 16`.  A final
assembly therefore has to retain the actual low--tail polarization or sharpen
the tail-row charge (for example by the exact cosh-border Schur complement).
-/

/-- The fixed endpoint-seed diagonal, abbreviated only to make the assembly
identities readable. -/
def fourCellEvenFiniteSevenSeedDiagonal : ℝ :=
  fourCellEvenExactBracket fourCellEvenEndpointCoshSeed

/-- The canonical finite profile through degree twelve. -/
def fourCellEvenFiniteSevenCanonicalLow
    (w : ℝ → ℝ) (hw : Continuous w) : ℝ → ℝ :=
  centeredLegendreLowProjection w hw 14

/-- The genuine `P14+` residual. -/
def fourCellEvenFiniteSevenCanonicalTail
    (w : ℝ → ℝ) (hw : Continuous w) : ℝ → ℝ :=
  centeredLegendreHigherResidual w hw 14

/-- The finite bordered diagonal before choosing quotient coordinates. -/
def fourCellEvenFiniteSevenCanonicalLowBorder
    (w : ℝ → ℝ) (hw : Continuous w) : ℝ :=
  fourCellEvenFiniteSevenSeedDiagonal *
      fourCellEvenPolarFreeOperator
        (fourCellEvenFiniteSevenCanonicalLow w hw) -
    (251 / 250 : ℝ) *
      fourCellEvenEndpointSeedCanonicalLowThroughTwelveRow w hw ^ 2

/-- The exact part of the global determinant not contained in the finite
border after spending the existing `1 / 16` tail-row budget. -/
def fourCellEvenFiniteSevenCanonicalTailCoupling
    (w : ℝ → ℝ) (hw : Continuous w) : ℝ :=
  2 * fourCellEvenFiniteSevenSeedDiagonal *
      fourCellEvenFiniteSevenPolarFreePolarization
        (fourCellEvenFiniteSevenCanonicalLow w hw)
        (fourCellEvenFiniteSevenCanonicalTail w hw) +
    (fourCellEvenFiniteSevenSeedDiagonal - (1 / 16 : ℝ)) *
      fourCellEvenPolarFreeOperator
        (fourCellEvenFiniteSevenCanonicalTail w hw)

/-- Lossless low--mixed--tail expansion of the polar-free operator at the
canonical cutoff fourteen.  This uses only the definition of polarization;
no bilinearity or analytic estimate is hidden in the identity. -/
theorem fourCellEvenPolarFreeOperator_eq_finiteSevenLow_add_mixed_add_tail
    (w : ℝ → ℝ) (hw : Continuous w) :
    fourCellEvenPolarFreeOperator w =
      fourCellEvenPolarFreeOperator
          (fourCellEvenFiniteSevenCanonicalLow w hw) +
        2 * fourCellEvenFiniteSevenPolarFreePolarization
          (fourCellEvenFiniteSevenCanonicalLow w hw)
          (fourCellEvenFiniteSevenCanonicalTail w hw) +
        fourCellEvenPolarFreeOperator
          (fourCellEvenFiniteSevenCanonicalTail w hw) := by
  have hsplit := centeredLegendreLowProjection_add_higherResidual w hw 14
  unfold fourCellEvenFiniteSevenPolarFreePolarization
    fourCellEvenFiniteSevenCanonicalLow
    fourCellEvenFiniteSevenCanonicalTail
  rw [hsplit]
  ring

/-! ## Exact cancellation inside the bordered mixed entry -/

/-- The canonical cutoff-fourteen polynomial really has degree below the
cutoff.  This is the structural fact which lets the whole singular
low--tail cross vanish at once, without inspecting any of the six even
coordinates. -/
private theorem finiteSeven_projectionPolynomial_natDegree_lt_fourteen
    (w : ℝ → ℝ) (hw : Continuous w) :
    (centeredLegendreProjectionPolynomial w hw 14).natDegree < 14 := by
  unfold centeredLegendreProjectionPolynomial
    shiftedLegendrePartialProjectionPolynomial
  have hle :
      (∑ n ∈ Finset.range 14,
        shiftedLegendreHilbertBasis.repr (centeredPullbackL2 w hw) n •
          normalizedShiftedLegendrePolynomial n).natDegree ≤ 13 :=
    Polynomial.natDegree_sum_le_of_forall_le (Finset.range 14) _
      (fun n hn ↦
        (Polynomial.natDegree_smul_le _ _).trans (by
          unfold normalizedShiftedLegendrePolynomial
          apply (Polynomial.natDegree_smul_le _ _).trans
          rw [natDegree_shiftedLegendreReal]
          simp only [Finset.mem_range] at hn
          omega))
  omega

/-- The singular logarithmic form is exactly block diagonal at the
canonical cutoff fourteen.  Thus the unresolved bordered mixed determinant
does not contain a hidden singular cross term. -/
theorem centeredRawLogEnergy_eq_finiteSevenLow_add_tail
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w) :
    centeredRawLogEnergy w =
      centeredRawLogEnergy (fourCellEvenFiniteSevenCanonicalLow w hw) +
        centeredRawLogEnergy
          (fourCellEvenFiniteSevenCanonicalTail w hw) := by
  let p : ℝ[X] := centeredLegendreProjectionPolynomial w hw 14
  let r : ℝ → ℝ := fourCellEvenFiniteSevenCanonicalTail w hw
  have hr : Continuous r := by
    simpa only [r, fourCellEvenFiniteSevenCanonicalTail] using
      continuous_centeredLegendreHigherResidual w hw 14
  have hrLocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) r := by
    simpa only [r, fourCellEvenFiniteSevenCanonicalTail] using
      locallyLipschitzOn_centeredLegendreHigherResidual w hw hlocal 14
  have hrGap : centeredLegendreMomentsVanishBelow r 14 := by
    simpa only [r, fourCellEvenFiniteSevenCanonicalTail] using
      centeredLegendreHigherResidual_momentsVanishBelow w hw 14
  have hpdeg : p.natDegree < 14 := by
    simpa only [p] using
      finiteSeven_projectionPolynomial_natDegree_lt_fourteen w hw
  have hraw :=
    centeredRawLogEnergy_centeredPolynomialLift_add_tail
      p r hr hrLocal hrGap hpdeg
  have hlow : centeredPolynomialLift p =
      fourCellEvenFiniteSevenCanonicalLow w hw := by
    rfl
  have hsum : fourCellEvenFiniteSevenCanonicalLow w hw + r = w := by
    simpa only [r, fourCellEvenFiniteSevenCanonicalLow,
      fourCellEvenFiniteSevenCanonicalTail] using
      centeredLegendreLowProjection_add_higherResidual w hw 14
  rw [hlow, hsum] at hraw
  simpa only [r] using hraw

/-- The ordinary scalar-mass row is also block diagonal at cutoff fourteen.
Together with the previous theorem this leaves only the endpoint-capacity
and nonconstant regular-kernel correlations in the exact mixed entry. -/
theorem finiteSevenCanonicalLow_mul_tail_integral_eq_zero
    (w : ℝ → ℝ) (hw : Continuous w) :
    (∫ x : ℝ in -1..1,
      fourCellEvenFiniteSevenCanonicalLow w hw x *
        fourCellEvenFiniteSevenCanonicalTail w hw x) = 0 := by
  let p : ℝ[X] := centeredLegendreProjectionPolynomial w hw 14
  let r : ℝ → ℝ := fourCellEvenFiniteSevenCanonicalTail w hw
  have hr : Continuous r := by
    simpa only [r, fourCellEvenFiniteSevenCanonicalTail] using
      continuous_centeredLegendreHigherResidual w hw 14
  have hrGap : centeredLegendreMomentsVanishBelow r 14 := by
    simpa only [r, fourCellEvenFiniteSevenCanonicalTail] using
      centeredLegendreHigherResidual_momentsVanishBelow w hw 14
  have hpdeg : p.natDegree < 14 := by
    simpa only [p] using
      finiteSeven_projectionPolynomial_natDegree_lt_fourteen w hw
  have hmass := intervalIntegral_centeredPolynomialLift_mul_tail_eq_zero
    p r hr hrGap hpdeg
  have hlow : centeredPolynomialLift p =
      fourCellEvenFiniteSevenCanonicalLow w hw := by
    rfl
  rw [hlow] at hmass
  simpa only [r] using hmass

/-- Exact nonsingular normal form of the polar-free low--tail
polarization.  Legendre orthogonality removes the complete raw logarithmic
cross and the scalar-mass cross; the displayed two correlations are the
only infinite-dimensional interaction still present. -/
theorem finiteSevenPolarFreePolarization_eq_capacity_sub_regular
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w)
    (heven : Function.Even w) :
    fourCellEvenFiniteSevenPolarFreePolarization
        (fourCellEvenFiniteSevenCanonicalLow w hw)
        (fourCellEvenFiniteSevenCanonicalTail w hw) =
      fourCellEvenEndpointCapacityPolarization
          (fourCellEvenFiniteSevenCanonicalLow w hw)
          (fourCellEvenFiniteSevenCanonicalTail w hw) -
        2 * fourCellOperatorHalfWidth *
          (∫ t : ℝ in 0..2,
            yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
              factorTwoCenteredCorrelationBilinear
                (fourCellEvenFiniteSevenCanonicalLow w hw)
                (fourCellEvenFiniteSevenCanonicalTail w hw) t) := by
  let u : ℝ → ℝ := fourCellEvenFiniteSevenCanonicalLow w hw
  let r : ℝ → ℝ := fourCellEvenFiniteSevenCanonicalTail w hw
  have hu : Continuous u := by
    simpa only [u, fourCellEvenFiniteSevenCanonicalLow] using
      continuous_centeredLegendreLowProjection w hw 14
  have hr : Continuous r := by
    simpa only [r, fourCellEvenFiniteSevenCanonicalTail] using
      continuous_centeredLegendreHigherResidual w hw 14
  have huLocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) u := by
    simpa only [u, fourCellEvenFiniteSevenCanonicalLow] using
      locallyLipschitzOn_centeredLegendreLowProjection w hw 14
  have hrLocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) r := by
    simpa only [r, fourCellEvenFiniteSevenCanonicalTail] using
      locallyLipschitzOn_centeredLegendreHigherResidual w hw hlocal 14
  have huEven : Function.Even u := by
    simpa only [u, fourCellEvenFiniteSevenCanonicalLow] using
      centeredLegendreLowProjection_even w hw heven 14
  have hrEven : Function.Even r := by
    simpa only [r, fourCellEvenFiniteSevenCanonicalTail] using
      centeredLegendreHigherResidual_even w hw heven 14
  have hraw : centeredRawLogEnergy (u + r) =
      centeredRawLogEnergy u + centeredRawLogEnergy r := by
    have h := centeredRawLogEnergy_eq_finiteSevenLow_add_tail
      w hw hlocal
    have hsum : u + r = w := by
      simpa only [u, r, fourCellEvenFiniteSevenCanonicalLow,
        fourCellEvenFiniteSevenCanonicalTail] using
        centeredLegendreLowProjection_add_higherResidual w hw 14
    rw [hsum]
    simpa only [u, r] using h
  have hmass : (∫ x : ℝ in -1..1, u x * r x) = 0 := by
    simpa only [u, r] using
      finiteSevenCanonicalLow_mul_tail_integral_eq_zero w hw
  have hcapacity := fourCellEvenEndpointCapacityQuadratic_add
    u r hu hr
  have hsigned := fourCellEvenSignedMassRegularQuadratic_add
    u r hu hr
  have hcore : fourCellEvenZeroCoshCoupledCore (u + r) =
      fourCellEvenZeroCoshCoupledCore u +
        2 * fourCellEvenEndpointCapacityPolarization u r +
          fourCellEvenZeroCoshCoupledCore r := by
    unfold fourCellEvenZeroCoshCoupledCore
    unfold fourCellEvenEndpointCapacityQuadratic at hcapacity
    rw [hraw]
    linarith only [hcapacity]
  have hnormalAdd : fourCellEvenPolarFreeOperator (u + r) =
      fourCellEvenZeroCoshCoupledCore (u + r) -
        fourCellEvenSignedMassRegularQuadratic (u + r) := by
    rw [fourCellEvenPolarFreeOperator_eq_coupledCore_sub_scalar_sub_regular_of_even
      (u + r) (hu.add hr) (huLocal.add hrLocal) (huEven.add hrEven)]
    unfold fourCellEvenSignedMassRegularQuadratic
    ring
  have hnormalU : fourCellEvenPolarFreeOperator u =
      fourCellEvenZeroCoshCoupledCore u -
        fourCellEvenSignedMassRegularQuadratic u := by
    rw [fourCellEvenPolarFreeOperator_eq_coupledCore_sub_scalar_sub_regular_of_even
      u hu huLocal huEven]
    unfold fourCellEvenSignedMassRegularQuadratic
    ring
  have hnormalR : fourCellEvenPolarFreeOperator r =
      fourCellEvenZeroCoshCoupledCore r -
        fourCellEvenSignedMassRegularQuadratic r := by
    rw [fourCellEvenPolarFreeOperator_eq_coupledCore_sub_scalar_sub_regular_of_even
      r hr hrLocal hrEven]
    unfold fourCellEvenSignedMassRegularQuadratic
    ring
  have hpolar : fourCellEvenFiniteSevenPolarFreePolarization u r =
      fourCellEvenEndpointCapacityPolarization u r -
        fourCellEvenSignedMassRegularPolarization u r := by
    unfold fourCellEvenFiniteSevenPolarFreePolarization
    rw [hnormalAdd, hnormalU, hnormalR, hcore, hsigned]
    ring
  rw [hpolar]
  unfold fourCellEvenSignedMassRegularPolarization
  rw [hmass]
  dsimp only [u, r]
  ring

/-- Exact determinant accounting after the current universal endpoint-row
bound is inserted.  This is the structural assembly identity: the first
summand is the finite seven-coordinate border and the second is the sole
remaining low--tail coupling. -/
theorem finiteSevenCanonicalLowBorder_add_tailCoupling_eq_global_sub_budget
    (w : ℝ → ℝ) (hw : Continuous w) :
    fourCellEvenFiniteSevenCanonicalLowBorder w hw +
        fourCellEvenFiniteSevenCanonicalTailCoupling w hw =
      fourCellEvenFiniteSevenSeedDiagonal *
          fourCellEvenPolarFreeOperator w -
        ((251 / 250 : ℝ) *
            fourCellEvenEndpointSeedCanonicalLowThroughTwelveRow w hw ^ 2 +
          (1 / 16 : ℝ) *
            fourCellEvenPolarFreeOperator
              (fourCellEvenFiniteSevenCanonicalTail w hw)) := by
  have hsplit :=
    fourCellEvenPolarFreeOperator_eq_finiteSevenLow_add_mixed_add_tail w hw
  unfold fourCellEvenFiniteSevenCanonicalLowBorder
    fourCellEvenFiniteSevenCanonicalTailCoupling
  rw [hsplit]
  ring

/-- The exact remaining structural condition after the six-mode matrix is
identified with the canonical low border.  Under this one condition, the
existing cutoff-fourteen row theorem gives the desired universal endpoint
Schur determinant. -/
theorem fourCellEvenEndpointSeedRow_sq_le_seed_mul_polarFree_of_tailAssembly
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w)
    (heven : Function.Even w)
    (hzero : fourCellPositiveCoshMoment w
      (fourCellOperatorHalfWidth / 2) = 0)
    (hassembly : 0 ≤
      fourCellEvenFiniteSevenCanonicalLowBorder w hw +
        fourCellEvenFiniteSevenCanonicalTailCoupling w hw) :
    fourCellEvenEndpointSeedRow w ^ 2 ≤
      fourCellEvenFiniteSevenSeedDiagonal *
        fourCellEvenPolarFreeOperator w := by
  have hrow :=
    fourCellEvenEndpointSeedRow_sq_le_251_div_250_lowThroughTwelve_add_one_sixteenth_tailPolarFree
      w hw hlocal heven hzero
  have hrow' : fourCellEvenEndpointSeedRow w ^ 2 ≤
      (251 / 250 : ℝ) *
          fourCellEvenEndpointSeedCanonicalLowThroughTwelveRow w hw ^ 2 +
        (1 / 16 : ℝ) * fourCellEvenPolarFreeOperator
          (fourCellEvenFiniteSevenCanonicalTail w hw) := by
    simpa only [fourCellEvenFiniteSevenCanonicalTail] using hrow
  have hid :=
    finiteSevenCanonicalLowBorder_add_tailCoupling_eq_global_sub_budget w hw
  linarith only [hrow', hassembly, hid]

/-- Direct handoff from the named six-coordinate certificate.  The equality
`hmatrix` is the exact quotient-coordinate synthesis identity; `hcoupling`
is the genuinely infinite low--tail reserve.  Thus the twenty-one entry boxes
and the operator assembly are kept as logically independent obligations. -/
theorem fourCellEvenEndpointSeedRow_sq_le_seed_mul_polarFree_of_finiteSeven
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w)
    (heven : Function.Even w)
    (hzero : fourCellPositiveCoshMoment w
      (fourCellOperatorHalfWidth / 2) = 0)
    (hbox : fourCellEvenFiniteSevenTrueBorderEntryBox)
    (x₂ x₄ x₆ x₈ x₁₀ x₁₂ : ℝ)
    (hmatrix :
      fourCellEvenFiniteSevenTrueBorderMatrixQuadratic
          x₂ x₄ x₆ x₈ x₁₀ x₁₂ =
        fourCellEvenFiniteSevenCanonicalLowBorder w hw)
    (hcoupling : 0 ≤ fourCellEvenFiniteSevenCanonicalTailCoupling w hw) :
    fourCellEvenEndpointSeedRow w ^ 2 ≤
      fourCellEvenFiniteSevenSeedDiagonal *
        fourCellEvenPolarFreeOperator w := by
  have hfinite :=
    finiteSevenTrueBorderMatrixQuadratic_nonnegative_of_entryBox hbox
      x₂ x₄ x₆ x₈ x₁₀ x₁₂
  have hassembly : 0 ≤
      fourCellEvenFiniteSevenCanonicalLowBorder w hw +
        fourCellEvenFiniteSevenCanonicalTailCoupling w hw := by
    rw [← hmatrix]
    exact add_nonneg hfinite hcoupling
  exact
    fourCellEvenEndpointSeedRow_sq_le_seed_mul_polarFree_of_tailAssembly
      w hw hlocal heven hzero hassembly

/-! ## Lossless bordered low--tail Schur alternative -/

/-- The actual finite bordered diagonal, without a Young loss. -/
def fourCellEvenFiniteSevenExactLowDiagonal
    (w : ℝ → ℝ) (hw : Continuous w) : ℝ :=
  fourCellEvenFiniteSevenSeedDiagonal *
      fourCellEvenPolarFreeOperator
        (fourCellEvenFiniteSevenCanonicalLow w hw) -
    fourCellEvenEndpointSeedCanonicalLowThroughTwelveRow w hw ^ 2

/-- The actual `P14+` bordered diagonal, without a Young loss. -/
def fourCellEvenFiniteSevenExactTailDiagonal
    (w : ℝ → ℝ) (hw : Continuous w) : ℝ :=
  fourCellEvenFiniteSevenSeedDiagonal *
      fourCellEvenPolarFreeOperator
        (fourCellEvenFiniteSevenCanonicalTail w hw) -
    fourCellEvenEndpointSeedCanonicalTailRow
        (fourCellEvenFiniteSevenCanonicalTail w hw) ^ 2

/-- The one exact mixed entry of the bordered determinant.  This is the
operator polarization minus the product of the two endpoint-row pieces. -/
def fourCellEvenFiniteSevenExactBorderMixed
    (w : ℝ → ℝ) (hw : Continuous w) : ℝ :=
  fourCellEvenFiniteSevenSeedDiagonal *
      fourCellEvenFiniteSevenPolarFreePolarization
        (fourCellEvenFiniteSevenCanonicalLow w hw)
        (fourCellEvenFiniteSevenCanonicalTail w hw) -
    fourCellEvenEndpointSeedCanonicalLowThroughTwelveRow w hw *
      fourCellEvenEndpointSeedCanonicalTailRow
        (fourCellEvenFiniteSevenCanonicalTail w hw)

/-- Consequently the single unresolved bordered mixed entry is a smooth
capacity/regular functional of the `P14+` residual, minus the product of the
two endpoint rows.  There is no singular or scalar-mass contribution left
to estimate in its determinant. -/
theorem fourCellEvenFiniteSevenExactBorderMixed_eq_nonsingular
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w)
    (heven : Function.Even w) :
    fourCellEvenFiniteSevenExactBorderMixed w hw =
      fourCellEvenFiniteSevenSeedDiagonal *
        (fourCellEvenEndpointCapacityPolarization
            (fourCellEvenFiniteSevenCanonicalLow w hw)
            (fourCellEvenFiniteSevenCanonicalTail w hw) -
          2 * fourCellOperatorHalfWidth *
            (∫ t : ℝ in 0..2,
              yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
                factorTwoCenteredCorrelationBilinear
                  (fourCellEvenFiniteSevenCanonicalLow w hw)
                  (fourCellEvenFiniteSevenCanonicalTail w hw) t)) -
        fourCellEvenEndpointSeedCanonicalLowThroughTwelveRow w hw *
          fourCellEvenEndpointSeedCanonicalTailRow
            (fourCellEvenFiniteSevenCanonicalTail w hw) := by
  unfold fourCellEvenFiniteSevenExactBorderMixed
  rw [finiteSevenPolarFreePolarization_eq_capacity_sub_regular
    w hw hlocal heven]

/-! ## One explicit representer for the surviving mixed entry -/

/-- The physical regular-lag weight, named so the remaining mixed
functional can be written as one one-variable Riesz representer. -/
def fourCellEvenFiniteSevenRegularLagWeight (t : ℝ) : ℝ :=
  yoshidaRegularKernel (fourCellOperatorHalfWidth * t)

/-- The exact nonsingular representer of the polar-free low--tail
polarization.  Its three terms are respectively the endpoint potential, the
retained `p = 3` translate, and the complete smooth regular correlation. -/
def fourCellEvenFiniteSevenNonsingularOperatorRepresenter
    (u : ℝ → ℝ) (x : ℝ) : ℝ :=
  yoshidaEndpointPotential x * u x -
    (Real.sqrt 2 * Real.log 2 / 2) *
      factorTwoFixedLagK (8 / 5) u x -
    fourCellOperatorHalfWidth *
      factorTwoContinuousLagK fourCellEvenFiniteSevenRegularLagWeight u x

/-- The complete bordered mixed representer before removing any additional
degree-`<14` selector. -/
def fourCellEvenFiniteSevenExactBorderRepresenter
    (w : ℝ → ℝ) (hw : Continuous w) (x : ℝ) : ℝ :=
  fourCellEvenFiniteSevenSeedDiagonal *
      fourCellEvenFiniteSevenNonsingularOperatorRepresenter
        (fourCellEvenFiniteSevenCanonicalLow w hw) x -
    fourCellEvenEndpointSeedCanonicalLowThroughTwelveRow w hw *
      fourCellEvenEndpointSeedTailFourteenRepresenter 0 x

/-- The same representer in the genuine `P14+` quotient.  Every selector
of degree below fourteen has zero pairing with the canonical tail, so `q`
is free and can be chosen to minimize the exact dual norm. -/
def fourCellEvenFiniteSevenProjectedBorderRepresenter
    (w : ℝ → ℝ) (hw : Continuous w) (q : ℝ[X]) (x : ℝ) : ℝ :=
  fourCellEvenFiniteSevenExactBorderRepresenter w hw x -
    centeredPolynomialLift q x

private theorem finiteSeven_regularLagWeight_measurable :
    Measurable fourCellEvenFiniteSevenRegularLagWeight := by
  unfold fourCellEvenFiniteSevenRegularLagWeight
  exact measurable_yoshidaRegularKernel.comp
    (measurable_const.mul measurable_id)

private theorem finiteSeven_regularLagWeight_abs_le_quarter
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 2) :
    |fourCellEvenFiniteSevenRegularLagWeight t| ≤ (1 / 4 : ℝ) := by
  have ha0 : 0 ≤ fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  have harg0 : 0 ≤ fourCellOperatorHalfWidth * t :=
    mul_nonneg ha0 ht.1
  have harg4 : fourCellOperatorHalfWidth * t ≤
      5 * Real.log 2 / 4 := by
    calc
      fourCellOperatorHalfWidth * t ≤ fourCellOperatorHalfWidth * 2 :=
        mul_le_mul_of_nonneg_left ht.2 ha0
      _ = 5 * Real.log 2 / 4 := by
        unfold fourCellOperatorHalfWidth
        ring
  have hk0 := yoshidaRegularKernel_nonneg_fourCellRange harg0 harg4
  unfold fourCellEvenFiniteSevenRegularLagWeight
  rw [abs_of_nonneg hk0]
  exact yoshidaRegularKernel_le_quarter harg0

private theorem finiteSeven_intervalIntegrable_log_sq_zero_one :
    IntervalIntegrable (fun x : ℝ ↦ Real.log x ^ 2) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
  have hr : IntegrableOn
      (fun x : ℝ ↦ 16 * x ^ (-(1 / 2 : ℝ))) (Ioc 0 1) volume := by
    have h := intervalIntegral.intervalIntegrable_rpow'
      (a := (0 : ℝ)) (b := 1) (r := -(1 / 2 : ℝ)) (by norm_num)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)] at h
    exact h.const_mul 16
  apply Integrable.mono' hr
  · exact (Real.measurable_log.pow_const 2).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hx0 : 0 < x := hx.1
    have hx1 : x ≤ 1 := hx.2
    let y : ℝ := x ^ (1 / 4 : ℝ)
    have hy : 0 < y := Real.rpow_pos_of_pos hx0 _
    have hlog := Real.abs_log_mul_self_rpow_lt x (1 / 4 : ℝ)
      hx0 hx1 (by norm_num)
    norm_num at hlog
    have hprod : |Real.log x| * y < 4 := by
      dsimp only [y]
      simpa only [abs_mul,
        abs_of_pos (Real.rpow_pos_of_pos hx0 _)] using hlog
    have hp0 : 0 ≤ |Real.log x| * y :=
      mul_nonneg (abs_nonneg _) hy.le
    have hmul :
        0 ≤ (4 - |Real.log x| * y) * (4 + |Real.log x| * y) :=
      mul_nonneg (sub_nonneg.mpr hprod.le) (add_nonneg (by norm_num) hp0)
    have hsq : |Real.log x| ^ 2 * y ^ 2 ≤ 16 := by
      nlinarith only [hmul]
    have hySq : y ^ 2 = x ^ (1 / 2 : ℝ) := by
      dsimp only [y]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
      norm_num
    have hneg : x ^ (-(1 / 2 : ℝ)) = (y ^ 2)⁻¹ := by
      rw [Real.rpow_neg hx0.le, hySq]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs, hneg,
      ← div_eq_mul_inv]
    exact (le_div_iff₀ (sq_pos_of_pos hy)).2 hsq

private theorem finiteSeven_intervalIntegrable_log_sq_zero_two :
    IntervalIntegrable (fun x : ℝ ↦ Real.log x ^ 2) volume 0 2 := by
  apply finiteSeven_intervalIntegrable_log_sq_zero_one.trans
  apply ContinuousOn.intervalIntegrable
  exact (Real.continuousOn_log.mono (by
    intro x hx
    rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at hx
    simp only [mem_compl_iff, mem_singleton_iff]
    linarith [hx.1])).pow 2

private theorem finiteSeven_intervalIntegrable_endpointPotential_sq :
    IntervalIntegrable (fun x : ℝ ↦ yoshidaEndpointPotential x ^ 2)
      volume (-1) 1 := by
  have hlog := finiteSeven_intervalIntegrable_log_sq_zero_two
  have hminus : IntervalIntegrable
      (fun x : ℝ ↦ Real.log (1 - x) ^ 2) volume (-1) 1 := by
    convert (hlog.comp_sub_left 1).symm using 1 <;> norm_num
  have hplus : IntervalIntegrable
      (fun x : ℝ ↦ Real.log (1 + x) ^ 2) volume (-1) 1 := by
    convert hlog.comp_add_left 1 using 1 <;> norm_num
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
    at hminus hplus ⊢
  have hdom : IntegrableOn
      (fun x : ℝ ↦ (1 / 2 : ℝ) *
        (Real.log (1 - x) ^ 2 + Real.log (1 + x) ^ 2))
      (Ioc (-1) 1) volume := (hminus.add hplus).const_mul (1 / 2)
  apply Integrable.mono' hdom
  · unfold yoshidaEndpointPotential
    exact (((Real.measurable_log.comp
      (measurable_const.sub (measurable_id.pow_const 2))).neg.div_const 2)
        |>.pow_const 2).aestronglyMeasurable
  · have hne1 : ∀ᵐ x : ℝ ∂(volume.restrict (Ioc (-1 : ℝ) 1)), x ≠ 1 :=
      (MeasureTheory.Measure.ae_ne volume (1 : ℝ)).filter_mono
        (ae_mono Measure.restrict_le_self)
    filter_upwards [ae_restrict_mem measurableSet_Ioc, hne1] with x hx hx1
    have hxneg1 : x ≠ -1 := ne_of_gt hx.1
    have hsub : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx1)
    have hadd : 1 + x ≠ 0 := by
      intro hzero
      apply hxneg1
      linarith
    unfold yoshidaEndpointPotential
    rw [show 1 - x ^ 2 = (1 - x) * (1 + x) by ring,
      Real.log_mul hsub hadd]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith only [sq_nonneg (Real.log (1 - x) - Real.log (1 + x))]

private theorem finiteSeven_memLp_two_restrict_of_continuous
    (f : ℝ → ℝ) (hf : Continuous f) :
    MemLp f 2 (volume.restrict (Ioc (-1 : ℝ) 1)) := by
  have hmeas : AEStronglyMeasurable f
      (volume.restrict (Ioc (-1 : ℝ) 1)) :=
    hf.aestronglyMeasurable.restrict
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  have hcompact : IntegrableOn (fun x : ℝ ↦ ‖f x‖ ^ 2)
      (Icc (-1 : ℝ) 1) :=
    (hf.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  exact hcompact.mono_set Ioc_subset_Icc_self

private theorem finiteSeven_memLp_endpointPotential_mul_continuous
    (u : ℝ → ℝ) (hu : Continuous u) :
    MemLp (fun x : ℝ ↦ yoshidaEndpointPotential x * u x) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * u x)
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
    apply Measurable.aestronglyMeasurable
    unfold yoshidaEndpointPotential
    exact ((Real.measurable_log.comp
      (measurable_const.sub (measurable_id.pow_const 2))).neg.div_const 2).mul
        hu.measurable
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  have hI : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x ^ 2 * u x ^ 2)
      volume (-1) 1 := by
    simpa only [mul_comm] using
      finiteSeven_intervalIntegrable_endpointPotential_sq.continuousOn_mul
        (hu.pow 2).continuousOn
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)] at hI
  apply hI.congr
  filter_upwards with x
  rw [Real.norm_eq_abs, sq_abs]
  ring

private theorem finiteSeven_memLp_fixedLagK
    (tau : ℝ) (u : ℝ → ℝ) (hu : Continuous u) :
    MemLp (factorTwoFixedLagK tau u) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
  have hrightBase : MemLp (fun x : ℝ ↦ u (tau + x)) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) :=
    finiteSeven_memLp_two_restrict_of_continuous _
      (hu.comp (continuous_const.add continuous_id))
  have hright : MemLp (factorTwoFixedLagRightRepresenter tau u) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
    simpa only [factorTwoFixedLagRightRepresenter] using
      hrightBase.indicator (measurableSet_Icc :
        MeasurableSet (Icc (-1 : ℝ) (1 - tau)))
  have hleftBase : MemLp (fun x : ℝ ↦ u (x - tau)) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) :=
    finiteSeven_memLp_two_restrict_of_continuous _
      (hu.comp (continuous_id.sub continuous_const))
  have hleft : MemLp (factorTwoFixedLagLeftRepresenter tau u) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
    simpa only [factorTwoFixedLagLeftRepresenter] using
      hleftBase.indicator (measurableSet_Icc :
        MeasurableSet (Icc (-1 + tau) 1))
  simpa only [factorTwoFixedLagK] using hright.add hleft

private theorem finiteSeven_memLp_regularLagK
    (u : ℝ → ℝ) (hu : Continuous u) :
    MemLp
      (factorTwoContinuousLagK fourCellEvenFiniteSevenRegularLagWeight u) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
  let k : ℝ → ℝ := fourCellEvenFiniteSevenRegularLagWeight
  have hkMeas : Measurable k := by
    simpa only [k] using finiteSeven_regularLagWeight_measurable
  have hkBound : ∀ t ∈ Icc (0 : ℝ) 2, |k t| ≤ (1 / 4 : ℝ) := by
    intro t ht
    simpa only [k] using
      finiteSeven_regularLagWeight_abs_le_quarter t ht
  have hrightI :=
    intervalIntegrable_mul_factorTwoContinuousLagRightRepresenter_of_bounded
      k u (fun _ : ℝ ↦ 1) hkMeas hu continuous_const (1 / 4) hkBound
  have hleftI :=
    intervalIntegrable_mul_factorTwoContinuousLagLeftRepresenter_of_bounded
      k (fun _ : ℝ ↦ 1) u hkMeas continuous_const hu (1 / 4) hkBound
  have hKI : IntervalIntegrable (factorTwoContinuousLagK k u)
      volume (-1) 1 := by
    apply (hrightI.add hleftI).congr
    intro x _hx
    unfold factorTwoContinuousLagK
    simp only [one_mul]
  obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image hu.norm.continuousOn
  let B : ℝ := max 1 M
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left 1 M)
  have huB : ∀ x ∈ Icc (-1 : ℝ) 1, ‖u x‖ ≤ B := by
    intro x hx
    exact (hM (Set.mem_image_of_mem _ hx)).trans (le_max_right 1 M)
  have hKBound : ∀ x ∈ Ioc (-1 : ℝ) 1,
      ‖factorTwoContinuousLagK k u x‖ ≤ B := by
    intro x hx
    have hrightPoint : ∀ y ∈ Ι x 1,
        ‖k (y - x) * u y‖ ≤ (1 / 4 : ℝ) * B := by
      intro y hy
      rw [uIoc_of_le hx.2] at hy
      have hyIcc : y ∈ Icc (-1 : ℝ) 1 :=
        ⟨by linarith [hx.1, hy.1], hy.2⟩
      have hlag : y - x ∈ Icc (0 : ℝ) 2 :=
        ⟨by linarith [hy.1], by linarith [hx.1, hy.2]⟩
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul (hkBound (y - x) hlag) (huB y hyIcc)
        (norm_nonneg _) (by norm_num)
    have hleftPoint : ∀ y ∈ Ι (-1) x,
        ‖k (x - y) * u y‖ ≤ (1 / 4 : ℝ) * B := by
      intro y hy
      rw [uIoc_of_le hx.1.le] at hy
      have hyIcc : y ∈ Icc (-1 : ℝ) 1 :=
        ⟨hy.1.le, by linarith [hy.2, hx.2]⟩
      have hlag : x - y ∈ Icc (0 : ℝ) 2 :=
        ⟨by linarith [hy.2], by linarith [hy.1, hx.2]⟩
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul (hkBound (x - y) hlag) (huB y hyIcc)
        (norm_nonneg _) (by norm_num)
    have hright :=
      intervalIntegral.norm_integral_le_of_norm_le_const hrightPoint
    have hleft :=
      intervalIntegral.norm_integral_le_of_norm_le_const hleftPoint
    have hright' :
        ‖factorTwoContinuousLagRightRepresenter k u x‖ ≤ B / 2 := by
      change ‖∫ y : ℝ in x..1, k (y - x) * u y‖ ≤ B / 2
      have hlen : |1 - x| ≤ 2 := by
        rw [abs_of_nonneg (by linarith [hx.2])]
        linarith [hx.1]
      nlinarith only [hright, hlen, hBpos]
    have hleft' :
        ‖factorTwoContinuousLagLeftRepresenter k u x‖ ≤ B / 2 := by
      change ‖∫ y : ℝ in -1..x, k (x - y) * u y‖ ≤ B / 2
      have hlen : |x - (-1)| ≤ 2 := by
        rw [abs_of_nonneg (by linarith [hx.1.le])]
        linarith [hx.2]
      nlinarith only [hleft, hlen, hBpos]
    unfold factorTwoContinuousLagK
    exact (norm_add_le _ _).trans (by linarith only [hright', hleft'])
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)] at hKI
  have hmeas : AEStronglyMeasurable (factorTwoContinuousLagK k u)
      (volume.restrict (Ioc (-1 : ℝ) 1)) := hKI.aestronglyMeasurable
  have hLp : MemLp (factorTwoContinuousLagK k u) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
    apply MemLp.of_bound hmeas B
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact hKBound x hx
  simpa only [k] using hLp

private theorem finiteSeven_memLp_endpointSeedTailRepresenter_zero :
    MemLp (fourCellEvenEndpointSeedTailFourteenRepresenter 0) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
  have heq : fourCellEvenEndpointSeedTailFourteenRepresenter 0 =
      fourCellEvenEndpointSeedProjectedTailRowRepresenter
        fourCellEvenEndpointSeedCanonicalTailSelectorPolynomial := by
    funext x
    unfold fourCellEvenEndpointSeedTailFourteenRepresenter
      centeredPolynomialLift
    simp
  rw [heq]
  exact memLp_fourCellEvenEndpointSeedProjectedTailRowRepresenter
    fourCellEvenEndpointSeedCanonicalTailSelectorPolynomial

/-- Fubini turns both surviving correlation channels into the displayed
single tail pairing.  This identity is exact; no norm or triangle estimate
is used. -/
theorem finiteSevenNonsingularPolarization_eq_representerPairing
    (w : ℝ → ℝ) (hw : Continuous w) :
    fourCellEvenEndpointCapacityPolarization
          (fourCellEvenFiniteSevenCanonicalLow w hw)
          (fourCellEvenFiniteSevenCanonicalTail w hw) -
        2 * fourCellOperatorHalfWidth *
          (∫ t : ℝ in 0..2,
            yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
              factorTwoCenteredCorrelationBilinear
                (fourCellEvenFiniteSevenCanonicalLow w hw)
                (fourCellEvenFiniteSevenCanonicalTail w hw) t) =
      ∫ x : ℝ in -1..1,
        fourCellEvenFiniteSevenNonsingularOperatorRepresenter
            (fourCellEvenFiniteSevenCanonicalLow w hw) x *
          fourCellEvenFiniteSevenCanonicalTail w hw x := by
  let u : ℝ → ℝ := fourCellEvenFiniteSevenCanonicalLow w hw
  let r : ℝ → ℝ := fourCellEvenFiniteSevenCanonicalTail w hw
  let k : ℝ → ℝ := fourCellEvenFiniteSevenRegularLagWeight
  have hu : Continuous u := by
    simpa only [u, fourCellEvenFiniteSevenCanonicalLow] using
      continuous_centeredLegendreLowProjection w hw 14
  have hr : Continuous r := by
    simpa only [r, fourCellEvenFiniteSevenCanonicalTail] using
      continuous_centeredLegendreHigherResidual w hw 14
  have hkMeas : Measurable k := by
    simpa only [k] using finiteSeven_regularLagWeight_measurable
  have hkBound : ∀ t ∈ Icc (0 : ℝ) 2, |k t| ≤ (1 / 4 : ℝ) := by
    intro t ht
    simpa only [k] using
      finiteSeven_regularLagWeight_abs_le_quarter t ht
  have hfixed := correlationBilinear_eq_fixedLagK
    (8 / 5 : ℝ) u r hu hr (by norm_num)
  have hregular := integral_boundedLag_mul_correlationBilinear_eq_K
    k u r hkMeas hu hr (1 / 4) hkBound
  have hV : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * u x * r x)
      volume (-1) 1 := by
    have h := intervalIntegrable_endpointPotential_mul
      (fun x : ℝ ↦ u x * r x) (hu.mul hr)
    exact h.congr (fun x _hx ↦ by ring)
  have hfixedRight :=
    intervalIntegrable_mul_factorTwoFixedLagRightRepresenter
      (8 / 5 : ℝ) u r hu hr
  have hfixedLeft :=
    intervalIntegrable_mul_factorTwoFixedLagLeftRepresenter
      (8 / 5 : ℝ) r u hr hu
  have hfixedI : IntervalIntegrable
      (fun x : ℝ ↦ factorTwoFixedLagK (8 / 5) u x * r x)
      volume (-1) 1 := by
    apply (hfixedRight.add hfixedLeft).congr
    intro x _hx
    unfold factorTwoFixedLagK
    ring
  have hregularRight :=
    intervalIntegrable_mul_factorTwoContinuousLagRightRepresenter_of_bounded
      k u r hkMeas hu hr (1 / 4) hkBound
  have hregularLeft :=
    intervalIntegrable_mul_factorTwoContinuousLagLeftRepresenter_of_bounded
      k r u hkMeas hr hu (1 / 4) hkBound
  have hregularI : IntervalIntegrable
      (fun x : ℝ ↦ factorTwoContinuousLagK k u x * r x)
      volume (-1) 1 := by
    apply (hregularRight.add hregularLeft).congr
    intro x _hx
    unfold factorTwoContinuousLagK
    ring
  unfold fourCellEvenEndpointCapacityPolarization
  rw [show factorTwoCenteredCorrelationBilinear u r (8 / 5) =
      (1 / 2 : ℝ) * ∫ x : ℝ in -1..1,
        factorTwoFixedLagK (8 / 5) u x * r x by
        simpa only using hfixed,
    show (∫ t : ℝ in 0..2,
        yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
          factorTwoCenteredCorrelationBilinear u r t) =
      (1 / 2 : ℝ) * ∫ x : ℝ in -1..1,
        r x * factorTwoContinuousLagK k u x by
          simpa only [k, fourCellEvenFiniteSevenRegularLagWeight] using hregular]
  rw [show (fun x : ℝ ↦
      fourCellEvenFiniteSevenNonsingularOperatorRepresenter u x * r x) =
      fun x ↦
        yoshidaEndpointPotential x * u x * r x -
          (Real.sqrt 2 * Real.log 2 / 2) *
            (factorTwoFixedLagK (8 / 5) u x * r x) -
          fourCellOperatorHalfWidth *
            (factorTwoContinuousLagK k u x * r x) by
      funext x
      unfold fourCellEvenFiniteSevenNonsingularOperatorRepresenter
      dsimp only [k]
      ring,
    intervalIntegral.integral_sub
      (hV.sub (hfixedI.const_mul (Real.sqrt 2 * Real.log 2 / 2)))
      (hregularI.const_mul fourCellOperatorHalfWidth),
    intervalIntegral.integral_sub hV
      (hfixedI.const_mul (Real.sqrt 2 * Real.log 2 / 2)),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  have hregularComm :
      (∫ x : ℝ in -1..1,
        r x * factorTwoContinuousLagK k u x) =
        ∫ x : ℝ in -1..1,
          factorTwoContinuousLagK k u x * r x := by
    apply intervalIntegral.integral_congr
    intro x _hx
    ring
  rw [hregularComm]
  dsimp only [u, r, k]
  ring

/-- The projected bordered representer is a genuine `L²(-1,1)` vector for
every finite selector.  This is analytic square-integrability, not an
assumed formal norm. -/
theorem memLp_fourCellEvenFiniteSevenProjectedBorderRepresenter
    (w : ℝ → ℝ) (hw : Continuous w) (q : ℝ[X]) :
    MemLp (fourCellEvenFiniteSevenProjectedBorderRepresenter w hw q) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
  let u : ℝ → ℝ := fourCellEvenFiniteSevenCanonicalLow w hw
  have hu : Continuous u := by
    simpa only [u, fourCellEvenFiniteSevenCanonicalLow] using
      continuous_centeredLegendreLowProjection w hw 14
  have hpotential :=
    finiteSeven_memLp_endpointPotential_mul_continuous u hu
  have hfixed := finiteSeven_memLp_fixedLagK (8 / 5) u hu
  have hregular := finiteSeven_memLp_regularLagK u hu
  have hop : MemLp
      (fourCellEvenFiniteSevenNonsingularOperatorRepresenter u) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
    simpa only [fourCellEvenFiniteSevenNonsingularOperatorRepresenter,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using
      (hpotential.sub
        (hfixed.const_mul (Real.sqrt 2 * Real.log 2 / 2))).sub
          (hregular.const_mul fourCellOperatorHalfWidth)
  have htail : MemLp
      (fourCellEvenEndpointSeedTailFourteenRepresenter 0) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
    exact finiteSeven_memLp_endpointSeedTailRepresenter_zero
  have hbase : MemLp (fourCellEvenFiniteSevenExactBorderRepresenter w hw) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
    simpa only [fourCellEvenFiniteSevenExactBorderRepresenter, u,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using
      (hop.const_mul fourCellEvenFiniteSevenSeedDiagonal).sub
        (htail.const_mul
          (fourCellEvenEndpointSeedCanonicalLowThroughTwelveRow w hw))
  have hpoly : MemLp (centeredPolynomialLift q) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) :=
    finiteSeven_memLp_two_restrict_of_continuous _ (by
      unfold centeredPolynomialLift
      fun_prop)
  simpa only [fourCellEvenFiniteSevenProjectedBorderRepresenter] using
    hbase.sub hpoly

/-- The exact bordered mixed scalar is the pairing of the canonical `P14+`
tail with the explicit projected representer.  The selector `q` is
arbitrary below degree fourteen, so this is already the quotient norm that
the final Schur determinant must control. -/
theorem fourCellEvenFiniteSevenExactBorderMixed_eq_projectedRepresenterPairing
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w)
    (heven : Function.Even w)
    (q : ℝ[X]) (hq : q.natDegree < 14) :
    fourCellEvenFiniteSevenExactBorderMixed w hw =
      ∫ x : ℝ in -1..1,
        fourCellEvenFiniteSevenProjectedBorderRepresenter w hw q x *
          fourCellEvenFiniteSevenCanonicalTail w hw x := by
  let r : ℝ → ℝ := fourCellEvenFiniteSevenCanonicalTail w hw
  let G : ℝ → ℝ := fourCellEvenFiniteSevenExactBorderRepresenter w hw
  let P : ℝ → ℝ := centeredPolynomialLift q
  let mu : Measure ℝ := volume.restrict (Ioc (-1 : ℝ) 1)
  have hr : Continuous r := by
    simpa only [r, fourCellEvenFiniteSevenCanonicalTail] using
      continuous_centeredLegendreHigherResidual w hw 14
  have hrGap : centeredLegendreMomentsVanishBelow r 14 := by
    simpa only [r, fourCellEvenFiniteSevenCanonicalTail] using
      centeredLegendreHigherResidual_momentsVanishBelow w hw 14
  have hrLp : MemLp r 2 mu := by
    dsimp only [mu]
    exact finiteSeven_memLp_two_restrict_of_continuous r hr
  have hOpLp : MemLp
      (fourCellEvenFiniteSevenNonsingularOperatorRepresenter
        (fourCellEvenFiniteSevenCanonicalLow w hw)) 2 mu := by
    let u : ℝ → ℝ := fourCellEvenFiniteSevenCanonicalLow w hw
    have hu : Continuous u := by
      simpa only [u, fourCellEvenFiniteSevenCanonicalLow] using
        continuous_centeredLegendreLowProjection w hw 14
    have hpotential :=
      finiteSeven_memLp_endpointPotential_mul_continuous u hu
    have hfixed := finiteSeven_memLp_fixedLagK (8 / 5) u hu
    have hregular := finiteSeven_memLp_regularLagK u hu
    dsimp only [mu]
    simpa only [u, fourCellEvenFiniteSevenNonsingularOperatorRepresenter,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using
      (hpotential.sub
        (hfixed.const_mul (Real.sqrt 2 * Real.log 2 / 2))).sub
          (hregular.const_mul fourCellOperatorHalfWidth)
  have hTailLp : MemLp
      (fourCellEvenEndpointSeedTailFourteenRepresenter 0) 2 mu := by
    dsimp only [mu]
    exact finiteSeven_memLp_endpointSeedTailRepresenter_zero
  have hOpI : IntervalIntegrable (fun x : ℝ ↦
      fourCellEvenFiniteSevenNonsingularOperatorRepresenter
          (fourCellEvenFiniteSevenCanonicalLow w hw) x * r x)
      volume (-1) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
    exact (hrLp.mul' hOpLp : MemLp (fun x : ℝ ↦
      fourCellEvenFiniteSevenNonsingularOperatorRepresenter
          (fourCellEvenFiniteSevenCanonicalLow w hw) x * r x) 1 mu).integrable
      (by norm_num)
  have hTailI : IntervalIntegrable (fun x : ℝ ↦
      fourCellEvenEndpointSeedTailFourteenRepresenter 0 x * r x)
      volume (-1) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
    exact (hrLp.mul' hTailLp : MemLp (fun x : ℝ ↦
      fourCellEvenEndpointSeedTailFourteenRepresenter 0 x * r x) 1 mu)
        |>.integrable (by norm_num)
  have hNonsingular := finiteSevenNonsingularPolarization_eq_representerPairing
    w hw
  have hTail :=
    fourCellEvenEndpointSeedCanonicalTailRow_eq_tailFourteenRepresenterPairing
      r hr hrGap 0 (by simp)
  have hMixed := fourCellEvenFiniteSevenExactBorderMixed_eq_nonsingular
    w hw hlocal heven
  rw [hNonsingular] at hMixed
  have hMixedBase : fourCellEvenFiniteSevenExactBorderMixed w hw =
      ∫ x : ℝ in -1..1, G x * r x := by
    rw [hTail] at hMixed
    calc
      fourCellEvenFiniteSevenExactBorderMixed w hw =
          fourCellEvenFiniteSevenSeedDiagonal *
              (∫ x : ℝ in -1..1,
                fourCellEvenFiniteSevenNonsingularOperatorRepresenter
                    (fourCellEvenFiniteSevenCanonicalLow w hw) x * r x) -
            fourCellEvenEndpointSeedCanonicalLowThroughTwelveRow w hw *
              (∫ x : ℝ in -1..1,
                fourCellEvenEndpointSeedTailFourteenRepresenter 0 x * r x) := by
        simpa only [r] using hMixed
      _ = ∫ x : ℝ in -1..1, G x * r x := by
        rw [← intervalIntegral.integral_const_mul,
          ← intervalIntegral.integral_const_mul,
          ← intervalIntegral.integral_sub
            (hOpI.const_mul fourCellEvenFiniteSevenSeedDiagonal)
            (hTailI.const_mul
              (fourCellEvenEndpointSeedCanonicalLowThroughTwelveRow w hw))]
        apply intervalIntegral.integral_congr
        intro x _hx
        dsimp only [G, fourCellEvenFiniteSevenExactBorderRepresenter]
        ring
  have hGLp : MemLp G 2 mu := by
    dsimp only [mu]
    simpa only [G, fourCellEvenFiniteSevenExactBorderRepresenter,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using
      (hOpLp.const_mul fourCellEvenFiniteSevenSeedDiagonal).sub
        (hTailLp.const_mul
          (fourCellEvenEndpointSeedCanonicalLowThroughTwelveRow w hw))
  have hPLp : MemLp P 2 mu := by
    dsimp only [P, mu]
    exact finiteSeven_memLp_two_restrict_of_continuous _ (by
      unfold centeredPolynomialLift
      fun_prop)
  have hGI : IntervalIntegrable (fun x : ℝ ↦ G x * r x)
      volume (-1) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
    exact (hrLp.mul' hGLp : MemLp (fun x : ℝ ↦ G x * r x) 1 mu)
      |>.integrable (by norm_num)
  have hPI : IntervalIntegrable (fun x : ℝ ↦ P x * r x)
      volume (-1) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
    exact (hrLp.mul' hPLp : MemLp (fun x : ℝ ↦ P x * r x) 1 mu)
      |>.integrable (by norm_num)
  have hPzero : (∫ x : ℝ in -1..1, P x * r x) = 0 := by
    simpa only [P] using
      intervalIntegral_centeredPolynomialLift_mul_tail_eq_zero
        q r hr hrGap hq
  calc
    fourCellEvenFiniteSevenExactBorderMixed w hw =
        ∫ x : ℝ in -1..1, G x * r x := hMixedBase
    _ = (∫ x : ℝ in -1..1, G x * r x) -
        ∫ x : ℝ in -1..1, P x * r x := by rw [hPzero, sub_zero]
    _ = ∫ x : ℝ in -1..1, (G x - P x) * r x := by
      rw [← intervalIntegral.integral_sub hGI hPI]
      apply intervalIntegral.integral_congr
      intro x _hx
      ring
    _ = ∫ x : ℝ in -1..1,
        fourCellEvenFiniteSevenProjectedBorderRepresenter w hw q x *
          fourCellEvenFiniteSevenCanonicalTail w hw x := by
      apply intervalIntegral.integral_congr
      intro x _hx
      dsimp only [G, P, r,
        fourCellEvenFiniteSevenProjectedBorderRepresenter]

/-- Exact bordered determinant decomposition with no separate tail
allocation.  The `1/16` obstruction disappears: the tail keeps its true row
square and the mixed operator keeps its true polarization. -/
theorem finiteSevenExactBorderDeterminant_eq_low_add_mixed_add_tail
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w)
    (heven : Function.Even w)
    (hzero : fourCellPositiveCoshMoment w
      (fourCellOperatorHalfWidth / 2) = 0) :
    fourCellEvenFiniteSevenSeedDiagonal *
          fourCellEvenPolarFreeOperator w -
        fourCellEvenEndpointSeedRow w ^ 2 =
      fourCellEvenFiniteSevenExactLowDiagonal w hw +
        2 * fourCellEvenFiniteSevenExactBorderMixed w hw +
        fourCellEvenFiniteSevenExactTailDiagonal w hw := by
  have hop :=
    fourCellEvenPolarFreeOperator_eq_finiteSevenLow_add_mixed_add_tail w hw
  have hrow :=
    fourCellEvenEndpointSeedRow_eq_canonicalLowThroughTwelve_add_tailFourteen
      w hw hlocal heven hzero
  rw [hop, hrow]
  unfold fourCellEvenFiniteSevenExactLowDiagonal
    fourCellEvenFiniteSevenExactBorderMixed
    fourCellEvenFiniteSevenExactTailDiagonal
    fourCellEvenFiniteSevenCanonicalLow
    fourCellEvenFiniteSevenCanonicalTail
  ring

/-- The existing harmonic representer estimate is already far stronger than
the fixed-seed determinant needs on a pure `P14+` tail.  No zero-cosh
hypothesis is required. -/
theorem fourCellEvenEndpointSeedCanonicalTailRow_sq_le_one_div_eighty_polarFree
    (r : ℝ → ℝ) (hr : Continuous r)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) r)
    (heven : Function.Even r)
    (hlow : centeredLegendreMomentsVanishBelow r 14) :
    fourCellEvenEndpointSeedCanonicalTailRow r ^ 2 ≤
      (1 / 80 : ℝ) * fourCellEvenPolarFreeOperator r := by
  have hweighted :=
    harmonic_fourteen_mul_fourCellEvenEndpointSeedCanonicalTailRow_sq_le_raw
      r hr hlocal hlow
  have hcoercive :=
    two_fifths_rawEnergy_le_fourCellEvenPolarFreeOperator_of_tailFourteen
      r hr hlocal heven hlow
  have hE : 0 ≤ centeredRawLogEnergy r / 4 :=
    div_nonneg (centeredRawLogEnergy_nonnegative r) (by norm_num)
  norm_num [harmonic, Finset.sum_range_succ,
    fourCellEvenEndpointSeedCanonicalTailNormBudget] at hweighted
  nlinarith only [hweighted, hcoercive, hE]

/-- The actual harmonic representer constant is much smaller than the
`1/80` seed pivot: only `1/4000` of the tail operator is needed for the
endpoint row.  The remaining `49/4000` is the quantitative diagonal used by
the exact mixed-representer Schur estimate below. -/
theorem fourCellEvenEndpointSeedCanonicalTailRow_sq_le_one_div_fourThousand_polarFree
    (r : ℝ → ℝ) (hr : Continuous r)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) r)
    (heven : Function.Even r)
    (hlow : centeredLegendreMomentsVanishBelow r 14) :
    fourCellEvenEndpointSeedCanonicalTailRow r ^ 2 ≤
      (1 / 4000 : ℝ) * fourCellEvenPolarFreeOperator r := by
  have hweighted :=
    harmonic_fourteen_mul_fourCellEvenEndpointSeedCanonicalTailRow_sq_le_raw
      r hr hlocal hlow
  have hcoercive :=
    two_fifths_rawEnergy_le_fourCellEvenPolarFreeOperator_of_tailFourteen
      r hr hlocal heven hlow
  have hE : 0 ≤ centeredRawLogEnergy r / 4 :=
    div_nonneg (centeredRawLogEnergy_nonnegative r) (by norm_num)
  norm_num [harmonic, Finset.sum_range_succ,
    fourCellEvenEndpointSeedCanonicalTailNormBudget] at hweighted
  nlinarith only [hweighted, hcoercive, hE]

/-- Pure-tail endpoint Schur closure at cutoff fourteen, with the *actual*
fixed seed diagonal rather than the coarse `1/16` Young allocation. -/
theorem fourCellEvenEndpointSeedCanonicalTailRow_sq_le_seedDiagonal_polarFree
    (r : ℝ → ℝ) (hr : Continuous r)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) r)
    (heven : Function.Even r)
    (hlow : centeredLegendreMomentsVanishBelow r 14) :
    fourCellEvenEndpointSeedCanonicalTailRow r ^ 2 ≤
      fourCellEvenFiniteSevenSeedDiagonal *
        fourCellEvenPolarFreeOperator r := by
  have hrow :=
    fourCellEvenEndpointSeedCanonicalTailRow_sq_le_one_div_eighty_polarFree
      r hr hlocal heven hlow
  have hcoercive :=
    two_fifths_rawEnergy_le_fourCellEvenPolarFreeOperator_of_tailFourteen
      r hr hlocal heven hlow
  have hE : 0 ≤ centeredRawLogEnergy r / 4 :=
    div_nonneg (centeredRawLogEnergy_nonnegative r) (by norm_num)
  have hQ : 0 ≤ fourCellEvenPolarFreeOperator r := by
    nlinarith only [hcoercive, hE]
  have hseed : (1 / 80 : ℝ) ≤ fourCellEvenFiniteSevenSeedDiagonal := by
    unfold fourCellEvenFiniteSevenSeedDiagonal
    exact one_div_eighty_lt_fourCellEvenExactBracket_endpointCoshSeed.le
  exact hrow.trans (mul_le_mul_of_nonneg_right hseed hQ)

/-- The exact tail diagonal is nonnegative for every canonical cutoff-
fourteen residual. -/
theorem fourCellEvenFiniteSevenExactTailDiagonal_nonnegative
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w)
    (heven : Function.Even w) :
    0 ≤ fourCellEvenFiniteSevenExactTailDiagonal w hw := by
  let r : ℝ → ℝ := fourCellEvenFiniteSevenCanonicalTail w hw
  have hr : Continuous r := by
    simpa only [r, fourCellEvenFiniteSevenCanonicalTail] using
      continuous_centeredLegendreHigherResidual w hw 14
  have hrLocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) r := by
    simpa only [r, fourCellEvenFiniteSevenCanonicalTail] using
      locallyLipschitzOn_centeredLegendreHigherResidual w hw hlocal 14
  have hrEven : Function.Even r := by
    simpa only [r, fourCellEvenFiniteSevenCanonicalTail] using
      centeredLegendreHigherResidual_even w hw heven 14
  have hrGap : centeredLegendreMomentsVanishBelow r 14 := by
    simpa only [r, fourCellEvenFiniteSevenCanonicalTail] using
      centeredLegendreHigherResidual_momentsVanishBelow w hw 14
  have htail :=
    fourCellEvenEndpointSeedCanonicalTailRow_sq_le_seedDiagonal_polarFree
      r hr hrLocal hrEven hrGap
  unfold fourCellEvenFiniteSevenExactTailDiagonal
  simpa only [r] using sub_nonneg.mpr htail

/-- Quantitative reserve in the true tail diagonal.  The seed contributes
at least `1/80` of the tail operator while its endpoint row spends at most
`1/4000`, leaving the exact fraction `49/4000`. -/
theorem fortyNine_div_fourThousand_polarFree_le_exactTailDiagonal
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w)
    (heven : Function.Even w) :
    (49 / 4000 : ℝ) *
        fourCellEvenPolarFreeOperator
          (fourCellEvenFiniteSevenCanonicalTail w hw) ≤
      fourCellEvenFiniteSevenExactTailDiagonal w hw := by
  let r : ℝ → ℝ := fourCellEvenFiniteSevenCanonicalTail w hw
  have hr : Continuous r := by
    simpa only [r, fourCellEvenFiniteSevenCanonicalTail] using
      continuous_centeredLegendreHigherResidual w hw 14
  have hrLocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) r := by
    simpa only [r, fourCellEvenFiniteSevenCanonicalTail] using
      locallyLipschitzOn_centeredLegendreHigherResidual w hw hlocal 14
  have hrEven : Function.Even r := by
    simpa only [r, fourCellEvenFiniteSevenCanonicalTail] using
      centeredLegendreHigherResidual_even w hw heven 14
  have hrGap : centeredLegendreMomentsVanishBelow r 14 := by
    simpa only [r, fourCellEvenFiniteSevenCanonicalTail] using
      centeredLegendreHigherResidual_momentsVanishBelow w hw 14
  have hrow :=
    fourCellEvenEndpointSeedCanonicalTailRow_sq_le_one_div_fourThousand_polarFree
      r hr hrLocal hrEven hrGap
  have hcoercive :=
    two_fifths_rawEnergy_le_fourCellEvenPolarFreeOperator_of_tailFourteen
      r hr hrLocal hrEven hrGap
  have hE : 0 ≤ centeredRawLogEnergy r / 4 :=
    div_nonneg (centeredRawLogEnergy_nonnegative r) (by norm_num)
  have hQ : 0 ≤ fourCellEvenPolarFreeOperator r := by
    nlinarith only [hcoercive, hE]
  have hseed : (1 / 80 : ℝ) ≤ fourCellEvenFiniteSevenSeedDiagonal := by
    unfold fourCellEvenFiniteSevenSeedDiagonal
    exact one_div_eighty_lt_fourCellEvenExactBracket_endpointCoshSeed.le
  unfold fourCellEvenFiniteSevenExactTailDiagonal
  dsimp only [r] at hrow hQ ⊢
  nlinarith only [hrow, hQ,
    mul_le_mul_of_nonneg_right hseed hQ]

/-- The same reserve measured in the raw logarithmic tail energy.  This is
the natural scale for the degree-fourteen harmonic Cauchy inequality. -/
theorem fortyNine_div_tenThousand_raw_le_exactTailDiagonal
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w)
    (heven : Function.Even w) :
    (49 / 10000 : ℝ) *
        (centeredRawLogEnergy
          (fourCellEvenFiniteSevenCanonicalTail w hw) / 4) ≤
      fourCellEvenFiniteSevenExactTailDiagonal w hw := by
  let r : ℝ → ℝ := fourCellEvenFiniteSevenCanonicalTail w hw
  have hr : Continuous r := by
    simpa only [r, fourCellEvenFiniteSevenCanonicalTail] using
      continuous_centeredLegendreHigherResidual w hw 14
  have hrLocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) r := by
    simpa only [r, fourCellEvenFiniteSevenCanonicalTail] using
      locallyLipschitzOn_centeredLegendreHigherResidual w hw hlocal 14
  have hrEven : Function.Even r := by
    simpa only [r, fourCellEvenFiniteSevenCanonicalTail] using
      centeredLegendreHigherResidual_even w hw heven 14
  have hrGap : centeredLegendreMomentsVanishBelow r 14 := by
    simpa only [r, fourCellEvenFiniteSevenCanonicalTail] using
      centeredLegendreHigherResidual_momentsVanishBelow w hw 14
  have hcoercive :=
    two_fifths_rawEnergy_le_fourCellEvenPolarFreeOperator_of_tailFourteen
      r hr hrLocal hrEven hrGap
  have hscaled := mul_le_mul_of_nonneg_left hcoercive
    (by norm_num : (0 : ℝ) ≤ 49 / 4000)
  have hreserve :=
    fortyNine_div_fourThousand_polarFree_le_exactTailDiagonal
      w hw hlocal heven
  dsimp only [r] at hscaled hreserve ⊢
  nlinarith only [hscaled, hreserve]

/-- The exact mixed determinant follows from one quotient-norm estimate for
the explicit bordered representer.  The proof loses nothing beyond ordinary
`L²` Cauchy: the `P₁₄+` harmonic inequality converts tail mass to raw
logarithmic energy, and the sharp `49/10000` reserve above converts that raw
energy to the true tail diagonal. -/
theorem fourCellEvenFiniteSevenExactBorderMixed_sq_le_of_projectedRepresenterNorm
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w)
    (heven : Function.Even w)
    (hlow : 0 ≤ fourCellEvenFiniteSevenExactLowDiagonal w hw)
    (q : ℝ[X]) (hq : q.natDegree < 14)
    (hnorm :
      (∫ x : ℝ in -1..1,
        fourCellEvenFiniteSevenProjectedBorderRepresenter w hw q x ^ 2) ≤
          ((49 / 10000 : ℝ) * (harmonic 14 : ℝ)) *
            fourCellEvenFiniteSevenExactLowDiagonal w hw) :
    fourCellEvenFiniteSevenExactBorderMixed w hw ^ 2 ≤
      fourCellEvenFiniteSevenExactLowDiagonal w hw *
        fourCellEvenFiniteSevenExactTailDiagonal w hw := by
  let r : ℝ → ℝ := fourCellEvenFiniteSevenCanonicalTail w hw
  let G : ℝ → ℝ :=
    fourCellEvenFiniteSevenProjectedBorderRepresenter w hw q
  let mu : Measure ℝ := volume.restrict (Ioc (-1 : ℝ) 1)
  have hr : Continuous r := by
    simpa only [r, fourCellEvenFiniteSevenCanonicalTail] using
      continuous_centeredLegendreHigherResidual w hw 14
  have hrLocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) r := by
    simpa only [r, fourCellEvenFiniteSevenCanonicalTail] using
      locallyLipschitzOn_centeredLegendreHigherResidual w hw hlocal 14
  have hrGap : centeredLegendreMomentsVanishBelow r 14 := by
    simpa only [r, fourCellEvenFiniteSevenCanonicalTail] using
      centeredLegendreHigherResidual_momentsVanishBelow w hw 14
  have hG : MemLp G 2 mu := by
    simpa only [G, mu] using
      memLp_fourCellEvenFiniteSevenProjectedBorderRepresenter w hw q
  have hrLp : MemLp r 2 mu := by
    dsimp only [mu]
    exact finiteSeven_memLp_two_restrict_of_continuous r hr
  have hcauchy :=
    YoshidaEndpointWeightedCauchy.sq_integral_mul_le_weighted
      mu (fun _ : ℝ ↦ 1) G r (by simp)
        (by simpa only [div_one, Real.sqrt_one] using hG)
        (by simpa only [Real.sqrt_one, one_mul] using hrLp)
  have hcauchy' :
      (∫ x : ℝ in -1..1, G x * r x) ^ 2 ≤
        (∫ x : ℝ in -1..1, G x ^ 2) *
          (∫ x : ℝ in -1..1, r x ^ 2) := by
    repeat rw [intervalIntegral.integral_of_le (by norm_num)]
    simpa only [mu, div_one, one_mul] using hcauchy
  have hmass : 0 ≤ ∫ x : ℝ in -1..1, r x ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun _ _ ↦ sq_nonneg _)
  have hraw := harmonic_mul_intrinsicEnergy_le_raw_div_four
    r hr hrLocal 14 hrGap
  have hnormScaled := mul_le_mul_of_nonneg_right hnorm hmass
  have hfactor : 0 ≤
      (49 / 10000 : ℝ) *
        fourCellEvenFiniteSevenExactLowDiagonal w hw :=
    mul_nonneg (by norm_num) hlow
  have hrawScaled := mul_le_mul_of_nonneg_left hraw hfactor
  have hreserve := fortyNine_div_tenThousand_raw_le_exactTailDiagonal
    w hw hlocal heven
  have hreserveScaled := mul_le_mul_of_nonneg_left hreserve hlow
  have hpair :=
    fourCellEvenFiniteSevenExactBorderMixed_eq_projectedRepresenterPairing
      w hw hlocal heven q hq
  unfold factorTwoIntrinsicEnergy at hrawScaled
  dsimp only [G, r] at hcauchy' hnormScaled hrawScaled hreserveScaled
  rw [hpair]
  calc
    _ ≤
        (∫ x : ℝ in -1..1,
          fourCellEvenFiniteSevenProjectedBorderRepresenter w hw q x ^ 2) *
            (∫ x : ℝ in -1..1,
              fourCellEvenFiniteSevenCanonicalTail w hw x ^ 2) := hcauchy'
    _ ≤
        (((49 / 10000 : ℝ) * (harmonic 14 : ℝ)) *
            fourCellEvenFiniteSevenExactLowDiagonal w hw) *
          (∫ x : ℝ in -1..1,
            fourCellEvenFiniteSevenCanonicalTail w hw x ^ 2) := hnormScaled
    _ = ((49 / 10000 : ℝ) *
          fourCellEvenFiniteSevenExactLowDiagonal w hw) *
        ((harmonic 14 : ℝ) *
          (∫ x : ℝ in -1..1,
            fourCellEvenFiniteSevenCanonicalTail w hw x ^ 2)) := by ring
    _ ≤ ((49 / 10000 : ℝ) *
          fourCellEvenFiniteSevenExactLowDiagonal w hw) *
        (centeredRawLogEnergy
          (fourCellEvenFiniteSevenCanonicalTail w hw) / 4) := hrawScaled
    _ = fourCellEvenFiniteSevenExactLowDiagonal w hw *
        ((49 / 10000 : ℝ) *
          (centeredRawLogEnergy
            (fourCellEvenFiniteSevenCanonicalTail w hw) / 4)) := by ring
    _ ≤ fourCellEvenFiniteSevenExactLowDiagonal w hw *
        fourCellEvenFiniteSevenExactTailDiagonal w hw := hreserveScaled

/-- Lossless coupled-Schur assembly.  Once the finite diagonal and the true
mixed bordered entry satisfy their scalar determinant, the endpoint row is
closed without any coarse Young allocation. -/
theorem fourCellEvenEndpointSeedRow_sq_le_seed_mul_polarFree_of_exactBorderSchur
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w)
    (heven : Function.Even w)
    (hzero : fourCellPositiveCoshMoment w
      (fourCellOperatorHalfWidth / 2) = 0)
    (hlow : 0 ≤ fourCellEvenFiniteSevenExactLowDiagonal w hw)
    (hmixed : fourCellEvenFiniteSevenExactBorderMixed w hw ^ 2 ≤
      fourCellEvenFiniteSevenExactLowDiagonal w hw *
        fourCellEvenFiniteSevenExactTailDiagonal w hw) :
    fourCellEvenEndpointSeedRow w ^ 2 ≤
      fourCellEvenFiniteSevenSeedDiagonal *
        fourCellEvenPolarFreeOperator w := by
  have htail :=
    fourCellEvenFiniteSevenExactTailDiagonal_nonnegative
      w hw hlocal heven
  have hsum : 0 ≤
      fourCellEvenFiniteSevenExactLowDiagonal w hw +
        2 * fourCellEvenFiniteSevenExactBorderMixed w hw +
        fourCellEvenFiniteSevenExactTailDiagonal w hw :=
    scalar_low_tail_nonneg _ _ _ hlow htail hmixed
  have hid :=
    finiteSevenExactBorderDeterminant_eq_low_add_mixed_add_tail
      w hw hlocal heven hzero
  linarith only [hsum, hid]

/-- The finite-seven certificate supplies the exact low diagonal with an
extra positive `1/250` row reserve.  The only remaining infinite obligation
is therefore the displayed mixed bordered Schur inequality. -/
theorem fourCellEvenEndpointSeedRow_sq_le_seed_mul_polarFree_of_finiteSeven_exactSchur
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w)
    (heven : Function.Even w)
    (hzero : fourCellPositiveCoshMoment w
      (fourCellOperatorHalfWidth / 2) = 0)
    (hbox : fourCellEvenFiniteSevenTrueBorderEntryBox)
    (x₂ x₄ x₆ x₈ x₁₀ x₁₂ : ℝ)
    (hmatrix :
      fourCellEvenFiniteSevenTrueBorderMatrixQuadratic
          x₂ x₄ x₆ x₈ x₁₀ x₁₂ =
        fourCellEvenFiniteSevenCanonicalLowBorder w hw)
    (hmixed : fourCellEvenFiniteSevenExactBorderMixed w hw ^ 2 ≤
      fourCellEvenFiniteSevenExactLowDiagonal w hw *
        fourCellEvenFiniteSevenExactTailDiagonal w hw) :
    fourCellEvenEndpointSeedRow w ^ 2 ≤
      fourCellEvenFiniteSevenSeedDiagonal *
        fourCellEvenPolarFreeOperator w := by
  have hmatrixNonneg :=
    finiteSevenTrueBorderMatrixQuadratic_nonnegative_of_entryBox hbox
      x₂ x₄ x₆ x₈ x₁₀ x₁₂
  have hborder : 0 ≤ fourCellEvenFiniteSevenCanonicalLowBorder w hw := by
    rw [← hmatrix]
    exact hmatrixNonneg
  have hlow : 0 ≤ fourCellEvenFiniteSevenExactLowDiagonal w hw := by
    have hrowSq : 0 ≤
        fourCellEvenEndpointSeedCanonicalLowThroughTwelveRow w hw ^ 2 :=
      sq_nonneg _
    unfold fourCellEvenFiniteSevenCanonicalLowBorder at hborder
    unfold fourCellEvenFiniteSevenExactLowDiagonal
    nlinarith only [hborder, hrowSq]
  exact
    fourCellEvenEndpointSeedRow_sq_le_seed_mul_polarFree_of_exactBorderSchur
      w hw hlocal heven hzero hlow hmixed

/-- Structural finite-seven handoff in its final analytic form.  The finite
border supplies the low diagonal, while one explicit quotient-norm estimate
for the bordered representer supplies the exact mixed determinant.  Thus no
entrywise tail boxes or independent Young split remain in the assembly. -/
theorem fourCellEvenEndpointSeedRow_sq_le_seed_mul_polarFree_of_finiteSeven_projectedRepresenterNorm
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w)
    (heven : Function.Even w)
    (hzero : fourCellPositiveCoshMoment w
      (fourCellOperatorHalfWidth / 2) = 0)
    (hbox : fourCellEvenFiniteSevenTrueBorderEntryBox)
    (x₂ x₄ x₆ x₈ x₁₀ x₁₂ : ℝ)
    (hmatrix :
      fourCellEvenFiniteSevenTrueBorderMatrixQuadratic
          x₂ x₄ x₆ x₈ x₁₀ x₁₂ =
        fourCellEvenFiniteSevenCanonicalLowBorder w hw)
    (q : ℝ[X]) (hq : q.natDegree < 14)
    (hnorm :
      (∫ x : ℝ in -1..1,
        fourCellEvenFiniteSevenProjectedBorderRepresenter w hw q x ^ 2) ≤
          ((49 / 10000 : ℝ) * (harmonic 14 : ℝ)) *
            fourCellEvenFiniteSevenExactLowDiagonal w hw) :
    fourCellEvenEndpointSeedRow w ^ 2 ≤
      fourCellEvenFiniteSevenSeedDiagonal *
        fourCellEvenPolarFreeOperator w := by
  have hmatrixNonneg :=
    finiteSevenTrueBorderMatrixQuadratic_nonnegative_of_entryBox hbox
      x₂ x₄ x₆ x₈ x₁₀ x₁₂
  have hborder : 0 ≤ fourCellEvenFiniteSevenCanonicalLowBorder w hw := by
    rw [← hmatrix]
    exact hmatrixNonneg
  have hlow : 0 ≤ fourCellEvenFiniteSevenExactLowDiagonal w hw := by
    have hrowSq : 0 ≤
        fourCellEvenEndpointSeedCanonicalLowThroughTwelveRow w hw ^ 2 :=
      sq_nonneg _
    unfold fourCellEvenFiniteSevenCanonicalLowBorder at hborder
    unfold fourCellEvenFiniteSevenExactLowDiagonal
    nlinarith only [hborder, hrowSq]
  have hmixed :=
    fourCellEvenFiniteSevenExactBorderMixed_sq_le_of_projectedRepresenterNorm
      w hw hlocal heven hlow q hq hnorm
  exact
    fourCellEvenEndpointSeedRow_sq_le_seed_mul_polarFree_of_exactBorderSchur
      w hw hlocal heven hzero hlow hmixed

/-! ## The current `1/16` budget is not a closable pure-tail allocation -/

private theorem finiteSeven_integral_polynomial_five
    (a₀ a₁ a₂ a₃ a₄ a₅ l r : ℝ) :
    (∫ x : ℝ in l..r,
      a₀ + a₁ * x + a₂ * x ^ 2 + a₃ * x ^ 3 +
        a₄ * x ^ 4 + a₅ * x ^ 5) =
      a₀ * (r - l) + a₁ * (r ^ 2 - l ^ 2) / 2 +
        a₂ * (r ^ 3 - l ^ 3) / 3 +
          a₃ * (r ^ 4 - l ^ 4) / 4 +
            a₄ * (r ^ 5 - l ^ 5) / 5 +
              a₅ * (r ^ 6 - l ^ 6) / 6 := by
  rw [show (fun x : ℝ ↦
      a₀ + a₁ * x + a₂ * x ^ 2 + a₃ * x ^ 3 +
        a₄ * x ^ 4 + a₅ * x ^ 5) =
      fun x ↦ a₀ * x ^ 0 + a₁ * x ^ 1 + a₂ * x ^ 2 +
        a₃ * x ^ 3 + a₄ * x ^ 4 + a₅ * x ^ 5 by
    funext x
    ring]
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) l r)
    (Continuous.intervalIntegrable (by fun_prop) l r)]
  repeat rw [intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  ring

private theorem finiteSeven_cosh_le_fortyOne_fortieths
    {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ (7 / 32 : ℝ)) :
    Real.cosh u ≤ (41 / 40 : ℝ) := by
  have huSqRaw : u ^ 2 ≤ (7 / 32 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hu0 hu 2
  have hv0 : 0 ≤ u ^ 2 / 2 := by positivity
  have hv : u ^ 2 / 2 ≤ (49 / 2048 : ℝ) := by
    norm_num at huSqRaw ⊢
    linarith
  have hv1 : u ^ 2 / 2 < 1 := hv.trans_lt (by norm_num)
  have hexp : Real.exp (u ^ 2 / 2) ≤ 1 / (1 - u ^ 2 / 2) :=
    Real.exp_bound_div_one_sub_of_interval hv0 hv1
  have hfrac : 1 / (1 - u ^ 2 / 2) ≤ (41 / 40 : ℝ) := by
    rw [div_le_iff₀ (sub_pos.mpr hv1)]
    nlinarith
  exact (Real.cosh_le_exp_half_sq u).trans (hexp.trans hfrac)

private theorem finiteSeven_cosh_le_one_add_fortyOne_eightieths_sq
    {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ (7 / 32 : ℝ)) :
    Real.cosh u ≤ 1 + (41 / 80 : ℝ) * u ^ 2 := by
  let v : ℝ := u ^ 2 / 2
  have hv0 : 0 ≤ v := by dsimp only [v]; positivity
  have huSqRaw : u ^ 2 ≤ (7 / 32 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hu0 hu 2
  have hv : v ≤ (49 / 2048 : ℝ) := by
    dsimp only [v]
    norm_num at huSqRaw ⊢
    linarith
  have hv1 : v < 1 := hv.trans_lt (by norm_num)
  have hexp : Real.exp v ≤ 1 / (1 - v) :=
    Real.exp_bound_div_one_sub_of_interval hv0 hv1
  have hlinear : 1 / (1 - v) ≤ 1 + (41 / 40 : ℝ) * v := by
    rw [div_le_iff₀ (sub_pos.mpr hv1)]
    have hvSharp : 41 * v ≤ 1 := by
      calc
        41 * v ≤ 41 * (49 / 2048 : ℝ) :=
          mul_le_mul_of_nonneg_left hv (by norm_num)
        _ ≤ 1 := by norm_num
    nlinarith only [hv0, hvSharp]
  calc
    Real.cosh u ≤ Real.exp (u ^ 2 / 2) := Real.cosh_le_exp_half_sq u
    _ = Real.exp v := by rfl
    _ ≤ 1 / (1 - v) := hexp
    _ ≤ 1 + (41 / 40 : ℝ) * v := hlinear
    _ = 1 + (41 / 80 : ℝ) * u ^ 2 := by
      dsimp only [v]
      ring

private theorem endpointSeed_coshMoment_le_sixtySeven_hundredths :
    fourCellPositiveCoshMoment fourCellEvenEndpointCoshSeed
        (fourCellOperatorHalfWidth / 2) ≤ (67 / 100 : ℝ) := by
  let lambda : ℝ := fourCellOperatorHalfWidth / 2
  have hlambda0 : 0 ≤ lambda := by
    dsimp only [lambda]
    unfold fourCellOperatorHalfWidth
    positivity
  have hlambda : lambda ≤ (7 / 32 : ℝ) := by
    dsimp only [lambda]
    have hlog := strict_log_two_bounds.2
    unfold fourCellOperatorHalfWidth
    nlinarith
  have hpoint : ∀ x ∈ Icc (0 : ℝ) 1,
      Real.cosh (lambda * x) * fourCellEvenEndpointCoshSeed x ≤
        (1 + (41 / 80 : ℝ) * lambda ^ 2 * x ^ 2) *
          (1 - x ^ 2) := by
    intro x hx
    have hx0 : 0 ≤ x := hx.1
    have hx1 : x ≤ 1 := hx.2
    have hz0 : 0 ≤ lambda * x := mul_nonneg hlambda0 hx0
    have hz : lambda * x ≤ (7 / 32 : ℝ) := by
      calc
        lambda * x ≤ lambda * 1 :=
          mul_le_mul_of_nonneg_left hx1 hlambda0
        _ ≤ (7 / 32 : ℝ) := by simpa using hlambda
    have hcosh :=
      finiteSeven_cosh_le_one_add_fortyOne_eightieths_sq hz0 hz
    have hseed : 0 ≤ 1 - x ^ 2 := by nlinarith [sq_nonneg x]
    unfold fourCellEvenEndpointCoshSeed
    have hmul := mul_le_mul_of_nonneg_right hcosh hseed
    nlinarith only [hmul]
  have hint :
      (∫ x : ℝ in 0..1,
          Real.cosh (lambda * x) * fourCellEvenEndpointCoshSeed x) ≤
        ∫ x : ℝ in 0..1,
          (1 + (41 / 80 : ℝ) * lambda ^ 2 * x ^ 2) *
            (1 - x ^ 2) := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      ((Continuous.mul (by fun_prop)
        fourCellEvenEndpointCoshSeed_continuous).intervalIntegrable 0 1)
      ((by fun_prop : Continuous (fun x : ℝ ↦
        (1 + (41 / 80 : ℝ) * lambda ^ 2 * x ^ 2) *
          (1 - x ^ 2))).intervalIntegrable 0 1)
      hpoint
  have hlambdaSq : lambda ^ 2 ≤ (7 / 32 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hlambda0 hlambda 2
  unfold fourCellPositiveCoshMoment
  change (∫ x : ℝ in 0..1,
      Real.cosh (lambda * x) * fourCellEvenEndpointCoshSeed x) ≤ _
  calc
    _ ≤ ∫ x : ℝ in 0..1,
        (1 + (41 / 80 : ℝ) * lambda ^ 2 * x ^ 2) *
          (1 - x ^ 2) := hint
    _ = (2 / 3 : ℝ) + (41 / 600 : ℝ) * lambda ^ 2 := by
      rw [show (fun x : ℝ ↦
          (1 + (41 / 80 : ℝ) * lambda ^ 2 * x ^ 2) *
            (1 - x ^ 2)) =
        fun x ↦ (1 : ℝ) + 0 * x +
          ((41 / 80 : ℝ) * lambda ^ 2 - 1) * x ^ 2 +
          0 * x ^ 3 + (-(41 / 80 : ℝ) * lambda ^ 2) * x ^ 4 +
          0 * x ^ 5 by
        funext x
        ring,
        finiteSeven_integral_polynomial_five]
      ring
    _ ≤ (2 / 3 : ℝ) + (41 / 600) * (7 / 32 : ℝ) ^ 2 := by
      have hscaled : (41 / 600 : ℝ) * lambda ^ 2 ≤
          (41 / 600 : ℝ) * (7 / 32) ^ 2 :=
        mul_le_mul_of_nonneg_left hlambdaSq (by norm_num)
      simpa only [add_comm] using add_le_add_left hscaled (2 / 3 : ℝ)
    _ ≤ (67 / 100 : ℝ) := by norm_num

private theorem log_five_four_gt_2231_div_10000 :
    (2231 / 10000 : ℝ) < Real.log (5 / 4 : ℝ) := by
  have h := Real.sum_range_le_log_div (x := (1 / 9 : ℝ))
    (by norm_num) (by norm_num) 3
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

private theorem fourCellScalar_gt_15783_div_10000 :
    (15783 / 10000 : ℝ) <
      Real.log (2 * fourCellOperatorHalfWidth) +
        Real.eulerMascheroniConstant + Real.log Real.pi := by
  have hlogTwo : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hwidth :
      Real.log (2 * fourCellOperatorHalfWidth) =
        Real.log (5 / 4 : ℝ) + Real.log (Real.log 2) := by
    rw [show 2 * fourCellOperatorHalfWidth =
        (5 / 4 : ℝ) * Real.log 2 by
      unfold fourCellOperatorHalfWidth
      ring,
      Real.log_mul (by norm_num : (5 / 4 : ℝ) ≠ 0) hlogTwo]
  rw [hwidth]
  linarith [log_five_four_gt_2231_div_10000,
    strict_log_log_two_bounds.1, strict_euler_gamma_bounds.1,
    strict_log_pi_bounds.1]

private theorem finiteSeven_centeredEndpointCorrelation_endpointCoshSeed
    (t : ℝ) :
    centeredEndpointCorrelation fourCellEvenEndpointCoshSeed t =
      16 / 15 - (4 / 3 : ℝ) * t ^ 2 + (2 / 3 : ℝ) * t ^ 3 -
        t ^ 5 / 30 := by
  unfold centeredEndpointCorrelation
  rw [show (fun x : ℝ ↦
      fourCellEvenEndpointCoshSeed (t + x) *
        fourCellEvenEndpointCoshSeed x) =
      fun x ↦
        (1 - t ^ 2) + (-2 * t) * x + (t ^ 2 - 2) * x ^ 2 +
          (2 * t) * x ^ 3 + 1 * x ^ 4 + 0 * x ^ 5 by
    funext x
    unfold fourCellEvenEndpointCoshSeed
    ring,
    finiteSeven_integral_polynomial_five]
  ring

private theorem endpointSeed_regularCorrelation_ge_eight_fortyFifths :
    (8 / 45 : ℝ) ≤
      ∫ t : ℝ in 0..2,
        yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
          centeredEndpointCorrelation fourCellEvenEndpointCoshSeed t := by
  -- The kernel is at least `1/5` on the four-cell range, while the exact
  -- autocorrelation mass of `1 - x^2` is `8/9`.
  let C : ℝ → ℝ := fun t ↦
    centeredEndpointCorrelation fourCellEvenEndpointCoshSeed t
  have hC : Continuous C := by
    rw [show C = fun t : ℝ ↦
        16 / 15 - (4 / 3 : ℝ) * t ^ 2 + (2 / 3 : ℝ) * t ^ 3 -
          t ^ 5 / 30 by
      funext t
      exact finiteSeven_centeredEndpointCorrelation_endpointCoshSeed t]
    fun_prop
  have hCnonneg : ∀ t ∈ Icc (0 : ℝ) 2, 0 ≤ C t := by
    intro t ht
    dsimp only [C]
    rw [finiteSeven_centeredEndpointCorrelation_endpointCoshSeed]
    have hcube : 0 ≤ (2 - t) ^ 3 :=
      pow_nonneg (sub_nonneg.mpr ht.2) 3
    have hquad : 0 ≤ t ^ 2 + 6 * t + 4 := by
      nlinarith [sq_nonneg t, ht.1]
    have hfactor :
        30 * (16 / 15 - (4 / 3 : ℝ) * t ^ 2 +
          (2 / 3 : ℝ) * t ^ 3 - t ^ 5 / 30) =
            (2 - t) ^ 3 * (t ^ 2 + 6 * t + 4) := by ring
    nlinarith [mul_nonneg hcube hquad]
  have hmono :
      (∫ t : ℝ in 0..2, (1 / 5 : ℝ) * C t) ≤
        ∫ t : ℝ in 0..2,
          yoshidaRegularKernel (fourCellOperatorHalfWidth * t) * C t := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      ((continuous_const.mul hC).intervalIntegrable 0 2)
      (intervalIntegrable_boundedLag_mul_continuous
        (fun t : ℝ ↦ yoshidaRegularKernel (fourCellOperatorHalfWidth * t))
        C (measurable_yoshidaRegularKernel.comp
          (measurable_const.mul measurable_id)) hC (1 / 4) (by
            intro t ht
            have ha0 : 0 ≤ fourCellOperatorHalfWidth := by
              unfold fourCellOperatorHalfWidth
              positivity
            have harg0 : 0 ≤ fourCellOperatorHalfWidth * t :=
              mul_nonneg ha0 ht.1
            have harg4 : fourCellOperatorHalfWidth * t ≤
                5 * Real.log 2 / 4 := by
              calc
                fourCellOperatorHalfWidth * t ≤
                    fourCellOperatorHalfWidth * 2 :=
                  mul_le_mul_of_nonneg_left ht.2 ha0
                _ = 5 * Real.log 2 / 4 := by
                  unfold fourCellOperatorHalfWidth
                  ring
            have hk0 := yoshidaRegularKernel_nonneg_fourCellRange harg0 harg4
            rw [abs_of_nonneg hk0]
            exact yoshidaRegularKernel_le_quarter harg0))
    intro t ht
    exact mul_le_mul_of_nonneg_right
      (one_fifth_le_yoshidaRegularKernel_fourCellRange
        (mul_nonneg (by unfold fourCellOperatorHalfWidth; positivity) ht.1)
        (by
          calc
            fourCellOperatorHalfWidth * t ≤ fourCellOperatorHalfWidth * 2 :=
              mul_le_mul_of_nonneg_left ht.2
                (by unfold fourCellOperatorHalfWidth; positivity)
            _ = 5 * Real.log 2 / 4 := by
              unfold fourCellOperatorHalfWidth
              ring))
      (hCnonneg t ht)
  have hCint : (∫ t : ℝ in 0..2, C t) = 8 / 9 := by
    dsimp only [C]
    simp_rw [finiteSeven_centeredEndpointCorrelation_endpointCoshSeed]
    rw [show (fun t : ℝ ↦
        16 / 15 - (4 / 3 : ℝ) * t ^ 2 + (2 / 3 : ℝ) * t ^ 3 -
          t ^ 5 / 30) =
      fun t ↦ (16 / 15) + 0 * t + (-4 / 3) * t ^ 2 +
        (2 / 3) * t ^ 3 + 0 * t ^ 4 + (-1 / 30) * t ^ 5 by
      funext t
      ring,
      finiteSeven_integral_polynomial_five]
    norm_num
  rw [intervalIntegral.integral_const_mul, hCint] at hmono
  norm_num at hmono
  simpa only [C] using hmono

/-- The fixed seed diagonal is strictly below the `1 / 16` tail allocation.
This is a structural inequality, proved from a global kernel lower bound and
elementary hyperbolic/logarithmic bounds; it is not one of the twenty-one
finite entry boxes. -/
theorem fourCellEvenFiniteSevenSeedDiagonal_lt_one_sixteenth :
    fourCellEvenFiniteSevenSeedDiagonal < (1 / 16 : ℝ) := by
  let L : ℝ := Real.log 2
  let S : ℝ := Real.log (2 * fourCellOperatorHalfWidth) +
    Real.eulerMascheroniConstant + Real.log Real.pi
  let R : ℝ := ∫ t : ℝ in 0..2,
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
      centeredEndpointCorrelation fourCellEvenEndpointCoshSeed t
  let H : ℝ := fourCellPositiveCoshMoment fourCellEvenEndpointCoshSeed
    (fourCellOperatorHalfWidth / 2)
  have hL := strict_log_two_bounds
  have hL0 : (6931 / 10000 : ℝ) ≤ L := by
    dsimp only [L]
    exact hL.1.le
  have hL1 : L ≤ (6932 / 10000 : ℝ) := by
    dsimp only [L]
    exact hL.2.le
  have hS : (15783 / 10000 : ℝ) ≤ S := by
    dsimp only [S]
    exact fourCellScalar_gt_15783_div_10000.le
  have hR : (8 / 45 : ℝ) ≤ R := by
    simpa only [R] using endpointSeed_regularCorrelation_ge_eight_fortyFifths
  have hH : H ≤ (67 / 100 : ℝ) := by
    simpa only [H] using endpointSeed_coshMoment_le_sixtySeven_hundredths
  have hH0 : 0 ≤ H := by
    dsimp only [H]
    unfold fourCellPositiveCoshMoment
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro x hx
    exact mul_nonneg (Real.cosh_pos _).le
      (by
        unfold fourCellEvenEndpointCoshSeed
        nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hx.2)])
  have hHSq : H ^ 2 ≤ (67 / 100 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hH0 hH 2
  have hLnonneg : 0 ≤ L := by
    dsimp only [L]
    exact (Real.log_pos (by norm_num)).le
  have hRnonneg : 0 ≤ R := (by norm_num : (0 : ℝ) ≤ 8 / 45).trans hR
  have hnegLog : -(16 / 15 : ℝ) * L ≤
      -(16 / 15) * (6931 / 10000 : ℝ) := by
    nlinarith only [hL0]
  have hnegScalar : -S * (16 / 15 : ℝ) ≤
      -(15783 / 10000 : ℝ) * (16 / 15) := by
    nlinarith only [hS]
  have hLR : (6931 / 10000 : ℝ) * (8 / 45) ≤ L * R := by
    exact mul_le_mul hL0 hR (by norm_num) hLnonneg
  have hnegRegular : -(5 / 4 : ℝ) * (L * R) ≤
      -(5 / 4) * ((6931 / 10000 : ℝ) * (8 / 45)) := by
    nlinarith only [hLR]
  have hPolar : 5 * L * H ^ 2 ≤
      5 * (6932 / 10000 : ℝ) * (67 / 100) ^ 2 := by
    calc
      5 * L * H ^ 2 ≤ 5 * (6932 / 10000 : ℝ) * H ^ 2 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hL1 (by norm_num)) (sq_nonneg H)
      _ ≤ 5 * (6932 / 10000 : ℝ) * (67 / 100) ^ 2 :=
        mul_le_mul_of_nonneg_left hHSq (by norm_num)
  have hsqrt : (7 / 5 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      Real.sqrt_nonneg 2]
  have hprimeProduct :
      (7 / 5 : ℝ) * (6931 / 10000) ≤ Real.sqrt 2 * L := by
    exact mul_le_mul hsqrt hL0 (by norm_num) (Real.sqrt_nonneg 2)
  have hnegPrime :
      -(Real.sqrt 2 * L) * (1616 / 46875 : ℝ) ≤
        -((7 / 5 : ℝ) * (6931 / 10000)) * (1616 / 46875) := by
    exact mul_le_mul_of_nonneg_right (neg_le_neg hprimeProduct) (by norm_num)
  unfold fourCellEvenFiniteSevenSeedDiagonal
  rw [fourCellEvenExactBracket_endpointCoshSeed_formula]
  change 248 / 225 - (16 / 15 : ℝ) * L - S * (16 / 15) -
      (5 * L / 4) * R + 5 * L * H ^ 2 -
        Real.sqrt 2 * L * (1616 / 46875) < _
  have hrat :
      248 / 225 - (16 / 15 : ℝ) * (6931 / 10000) -
          (15783 / 10000 : ℝ) * (16 / 15) -
          (5 / 4 : ℝ) * ((6931 / 10000) * (8 / 45)) +
          5 * (6932 / 10000 : ℝ) * (67 / 100) ^ 2 -
          ((7 / 5 : ℝ) * (6931 / 10000)) * (1616 / 46875) <
        (1 / 16 : ℝ) := by norm_num
  nlinarith only [hnegLog, hnegScalar, hnegRegular, hPolar, hnegPrime, hrat]

/-- Consequently, the existing `1 / 16` upper-bound allocation is already
too large on a hypothetical positive pure tail.  This does *not* refute the
actual endpoint determinant; it proves that composing the current two upper
bounds while dropping the mixed/exact tail structure cannot close it. -/
theorem one_sixteenth_tailBudget_strictly_exceeds_seedDiagonal
    {T : ℝ} (hT : 0 < T) :
    fourCellEvenFiniteSevenSeedDiagonal * T < (1 / 16 : ℝ) * T := by
  exact mul_lt_mul_of_pos_right
    fourCellEvenFiniteSevenSeedDiagonal_lt_one_sixteenth hT

end

end ArithmeticHodge.Analysis.YoshidaFourCellEvenFiniteSevenTailAssemblyStructural

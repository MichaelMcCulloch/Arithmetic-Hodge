import ArithmeticHodge.Analysis.YoshidaFourCellEvenEndpointSeedRowStructural
import ArithmeticHodge.Analysis.YoshidaFourCellEvenZeroCoshCoupledCoreStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellEvenEndpointSeedCutoffEightBridgeStructural

noncomputable section

open MultiplicativeWeilFourCellRealRescaleStructural
open ShiftedLegendreOrthogonality
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointPotentialBound
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoPhaseIntrinsicNineP6EvenProfileCorrelationStructural
open YoshidaFactorTwoPhaseIntrinsicHigherResidual
open YoshidaFactorTwoPhaseIntrinsicSixP4EndpointProfile
open YoshidaFactorTwoPhaseIntrinsicSixSchurReduction
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFourCellEvenEndpointCapacityCauchyStructural
open YoshidaFourCellEvenEndpointCoshSchurStructural
open YoshidaFourCellEvenEndpointSeedRowStructural
open YoshidaFourCellEvenPolarSchurStructural
open YoshidaFourCellParityHalfFoldStructural
open YoshidaFourCellParityOperatorStructural
open YoshidaFourCellEvenZeroCoshCoupledCoreStructural
open YoshidaFourCellEvenZeroCoshRegularStructural

/-!
# The endpoint seed in the cutoff-eight coordinates

The fixed outer Schur row uses the endpoint-zero seed `1 - x^2`.  The
cutoff-eight core proof uses the first four even Legendre coordinates.  This
file identifies the seed with its exact `P0/P2/P4/P6` vector and shows that
its mixed coupled-core row against a `P8+` residual is precisely the retained
endpoint-capacity row.  Thus no raw-log tail term survives in the outer
determinant.
-/

/-- The endpoint-zero seed is the exact low vector
`(2/3, -2/3, 0, 0)` in the cutoff-eight even Legendre basis. -/
theorem fourCellEvenEndpointCoshSeed_eq_intrinsicEvenP0246Profile :
    fourCellEvenEndpointCoshSeed =
      factorTwoIntrinsicEvenP0246Profile (2 / 3) (-2 / 3) 0 0 := by
  funext x
  unfold fourCellEvenEndpointCoshSeed
    factorTwoIntrinsicEvenP0246Profile
    factorTwoIntrinsicEvenP024Profile
    factorTwoEvenStructuralLowProfile
    factorTwoIntrinsicSixEvenTail centeredEvenP0 centeredEvenP2
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Symmetry of the retained endpoint-capacity polarization. -/
theorem fourCellEvenEndpointCapacityPolarization_comm
    (u v : ℝ → ℝ) :
    fourCellEvenEndpointCapacityPolarization u v =
      fourCellEvenEndpointCapacityPolarization v u := by
  have hpotential :
      (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * u x * v x) =
        ∫ x : ℝ in -1..1,
          yoshidaEndpointPotential x * v x * u x := by
    apply intervalIntegral.integral_congr
    intro x _hx
    ring
  unfold fourCellEvenEndpointCapacityPolarization
  rw [hpotential, factorTwoCenteredCorrelationBilinear_comm]

private theorem endpointSeedProfile_add_intrinsicEvenP0246
    (c0 c2 c4 c6 : ℝ) :
    factorTwoIntrinsicEvenP0246Profile (2 / 3) (-2 / 3) 0 0 +
        factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6 =
      factorTwoIntrinsicEvenP0246Profile
        (2 / 3 + c0) (-2 / 3 + c2) c4 c6 := by
  funext x
  unfold factorTwoIntrinsicEvenP0246Profile
    factorTwoIntrinsicEvenP024Profile
    factorTwoEvenStructuralLowProfile
    factorTwoIntrinsicSixEvenTail centeredEvenP0 centeredEvenP2
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Against a genuine `P8+` tail, the endpoint seed has no raw-log mixed
entry.  Its complete coupled-core polarization is exactly the retained
endpoint-potential/prime capacity polarization. -/
theorem
    fourCellEvenZeroCoshCoupledCorePolarization_endpointSeed_tail_eq_capacity
    (r : ℝ → ℝ) (hr : Continuous r)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) r)
    (hlow : centeredLegendreMomentsVanishBelow r 8) :
    fourCellEvenZeroCoshCoupledCorePolarization
        fourCellEvenEndpointCoshSeed r =
      fourCellEvenEndpointCapacityPolarization
        fourCellEvenEndpointCoshSeed r := by
  rw [fourCellEvenEndpointCoshSeed_eq_intrinsicEvenP0246Profile]
  unfold fourCellEvenZeroCoshCoupledCorePolarization
  rw [fourCellEvenZeroCoshCoupledCore_intrinsicEvenP0246_add_tail
    (2 / 3) (-2 / 3) 0 0 r hr hlocal hlow]
  ring

/-- Exact mixed-row decomposition for the complete cutoff-eight split.  The
seed-to-low term is finite-dimensional, while the seed-to-tail term is the
single retained endpoint-capacity row. -/
theorem
    fourCellEvenZeroCoshCoupledCorePolarization_endpointSeed_P0246_add_tail
    (c0 c2 c4 c6 : ℝ) (r : ℝ → ℝ) (hr : Continuous r)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) r)
    (hlow : centeredLegendreMomentsVanishBelow r 8) :
    fourCellEvenZeroCoshCoupledCorePolarization
        fourCellEvenEndpointCoshSeed
        (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6 + r) =
      fourCellEvenZeroCoshCoupledCorePolarization
          fourCellEvenEndpointCoshSeed
          (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) +
        fourCellEvenEndpointCapacityPolarization
          fourCellEvenEndpointCoshSeed r := by
  let s : ℝ → ℝ :=
    factorTwoIntrinsicEvenP0246Profile (2 / 3) (-2 / 3) 0 0
  let p : ℝ → ℝ :=
    factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6
  let q : ℝ → ℝ :=
    factorTwoIntrinsicEvenP0246Profile
      (2 / 3 + c0) (-2 / 3 + c2) c4 c6
  have hs : Continuous s := by
    simpa only [s] using
      continuous_factorTwoIntrinsicEvenP0246Profile
        (2 / 3) (-2 / 3) 0 0
  have hp : Continuous p := by
    simpa only [p] using
      continuous_factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6
  have hsp : s + p = q := by
    simpa only [s, p, q] using
      endpointSeedProfile_add_intrinsicEvenP0246 c0 c2 c4 c6
  have hsall : s + (p + r) = q + r := by
    rw [← hsp]
    exact (add_assoc s p r).symm
  have hcapacity :
      fourCellEvenEndpointCapacityPolarization q r =
        fourCellEvenEndpointCapacityPolarization s r +
          fourCellEvenEndpointCapacityPolarization p r := by
    rw [← hsp,
      fourCellEvenEndpointCapacityPolarization_comm (s + p) r,
      fourCellEvenEndpointCapacityPolarization_add_right r s p hr hs hp,
      fourCellEvenEndpointCapacityPolarization_comm r s,
      fourCellEvenEndpointCapacityPolarization_comm r p]
  rw [fourCellEvenEndpointCoshSeed_eq_intrinsicEvenP0246Profile]
  change fourCellEvenZeroCoshCoupledCorePolarization s (p + r) =
    fourCellEvenZeroCoshCoupledCorePolarization s p +
      fourCellEvenEndpointCapacityPolarization s r
  unfold fourCellEvenZeroCoshCoupledCorePolarization
  rw [hsall,
    fourCellEvenZeroCoshCoupledCore_intrinsicEvenP0246_add_tail
      (2 / 3 + c0) (-2 / 3 + c2) c4 c6 r hr hlocal hlow,
    fourCellEvenZeroCoshCoupledCore_intrinsicEvenP0246_add_tail
      c0 c2 c4 c6 r hr hlocal hlow,
    hsp, hcapacity]
  ring

/-- Exact fixed-row normal form on the cutoff-eight tail.  The singular
coupled core has collapsed to the one capacity row, while the signed
mass/regular row remains coupled rather than being bounded separately. -/
theorem fourCellEvenEndpointSeedRow_tail_eq_capacity_sub_signed
    (r : ℝ → ℝ) (hr : Continuous r)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) r)
    (heven : Function.Even r)
    (hzero : fourCellPositiveCoshMoment r
      (fourCellOperatorHalfWidth / 2) = 0)
    (hlow : centeredLegendreMomentsVanishBelow r 8) :
    fourCellEvenEndpointSeedRow r =
      fourCellEvenEndpointCapacityPolarization
          fourCellEvenEndpointCoshSeed r -
        fourCellEvenSignedMassRegularPolarization
          fourCellEvenEndpointCoshSeed r := by
  rw [fourCellEvenEndpointSeedRow_eq_core_sub_signed r hr hlocal heven hzero,
    fourCellEvenZeroCoshCoupledCorePolarization_endpointSeed_tail_eq_capacity
      r hr hlocal hlow]

/-- Full fixed-row normal form after the canonical cutoff-eight split.  This
is the exact outer determinant row: one finite `P0246` core entry, one
endpoint-capacity tail entry, and the still-coupled signed mass/regular row. -/
theorem fourCellEvenEndpointSeedRow_P0246_add_tail_eq
    (c0 c2 c4 c6 : ℝ) (r : ℝ → ℝ) (hr : Continuous r)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) r)
    (hre : Function.Even r)
    (hzero : fourCellPositiveCoshMoment
      (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6 + r)
        (fourCellOperatorHalfWidth / 2) = 0)
    (hlow : centeredLegendreMomentsVanishBelow r 8) :
    fourCellEvenEndpointSeedRow
        (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6 + r) =
      fourCellEvenZeroCoshCoupledCorePolarization
          fourCellEvenEndpointCoshSeed
          (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) +
        fourCellEvenEndpointCapacityPolarization
          fourCellEvenEndpointCoshSeed r -
        fourCellEvenSignedMassRegularPolarization
          fourCellEvenEndpointCoshSeed
          (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6 + r) := by
  let p : ℝ → ℝ :=
    factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6
  have hp : Continuous p := by
    simpa only [p] using
      continuous_factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6
  have hpPoly : p = fun x : ℝ ↦
      c0 + c2 * ((3 * x ^ 2 - 1) / 2) +
        c4 * ((35 * x ^ 4 - 30 * x ^ 2 + 3) / 8) +
          c6 * ((231 * x ^ 6 - 315 * x ^ 4 + 105 * x ^ 2 - 5) / 16) := by
    funext x
    dsimp only [p]
    unfold factorTwoIntrinsicEvenP0246Profile
      factorTwoIntrinsicEvenP024Profile
      factorTwoEvenStructuralLowProfile
      factorTwoIntrinsicSixEvenTail centeredEvenP0 centeredEvenP2
      factorTwoCenteredP4
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [factorTwoCenteredP6_eq]
    ring
  have hpDiff : ContDiff ℝ 1 p := by
    rw [hpPoly]
    fun_prop
  have hpLocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) p :=
    hpDiff.contDiffOn.locallyLipschitzOn (convex_Icc (-1 : ℝ) 1)
  have hpe : Function.Even p := by
    simpa only [p] using
      even_factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6
  have hrow := fourCellEvenEndpointSeedRow_eq_core_sub_signed
    (p + r) (hp.add hr) (hpLocal.add hlocal) (hpe.add hre)
      (by simpa only [p] using hzero)
  rw [fourCellEvenZeroCoshCoupledCorePolarization_endpointSeed_P0246_add_tail
    c0 c2 c4 c6 r hr hlocal hlow] at hrow
  simpa only [p] using hrow

end

end ArithmeticHodge.Analysis.YoshidaFourCellEvenEndpointSeedCutoffEightBridgeStructural

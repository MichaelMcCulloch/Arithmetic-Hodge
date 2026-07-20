import ArithmeticHodge.Analysis.YoshidaFourCellOddP51SparseP11AnchorBesselStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddP11GalerkinResidualRepresenterStructural

set_option autoImplicit false

open MeasureTheory Polynomial Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP51SparseP11AnchorRepresenterStructural

noncomputable section

open CenteredOddOneThreeEnergy
open ShiftedLegendreCenteredL2Structural
open ShiftedLegendreCenteredLowModes
open ShiftedLegendreOrthogonality
open UnitIntervalLogEnergyAffine
open YoshidaEndpointOcticPotential
open YoshidaFactorTwoPhaseCenteredP9Structural
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
open YoshidaFourCellOddFiniteLegendreSolveStructural
open YoshidaFourCellOddP11GalerkinFiniteSolveStructural
open YoshidaFourCellOddP11GalerkinResidualRepresenterStructural
open YoshidaFourCellOddP11GalerkinSolutionBoxStructural
open YoshidaFourCellOddP51SparseP11AnchorBesselStructural
open YoshidaFourCellOddP51SparseP11AnchorMassStructural
open YoshidaFourCellOddStripCapacityClosureStructural

/-!
# Common row representer for the sparse P11 anchor

The exact old Galerkin row already has a two-strip representer.  Joining its
two pieces at `3/5` and subtracting one common five-mode selector gives a
single `L²(0,1)` function representing every normal row
`P11,P13,...,P51`.  Combined with the Bessel module, the sparse pivot
certificate is therefore one piecewise selector-norm inequality.
-/

/-- One exact piecewise row after subtracting a common low five-mode
selector. -/
def fourCellOddP51SparseP11HighSelectorRepresenter
    (b₁ b₃ b₅ b₇ b₉ : ℝ) (x : ℝ) : ℝ :=
  if x ≤ (3 / 5 : ℝ) then
    fourCellOddP11GalerkinResidualLowerSelectorResidual
      (fourCellOddP11GalerkinRetainedSolution 0)
      (fourCellOddP11GalerkinRetainedSolution 1)
      (fourCellOddP11GalerkinRetainedSolution 2)
      (fourCellOddP11GalerkinRetainedSolution 3)
      b₁ b₃ b₅ b₇ b₉ x
  else
    fourCellOddP11GalerkinResidualUpperSelectorResidual
      (fourCellOddP11GalerkinRetainedSolution 0)
      (fourCellOddP11GalerkinRetainedSolution 1)
      (fourCellOddP11GalerkinRetainedSolution 2)
      (fourCellOddP11GalerkinRetainedSolution 3)
      b₁ b₃ b₅ b₇ b₉ x

private theorem memLp_mono_zero_one
    {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioc (-1 : ℝ) 1))) :
    MemLp f 2 (volume.restrict (Ioc (0 : ℝ) 1)) := by
  exact hf.mono_measure (Measure.restrict_mono (by
    intro x hx
    exact ⟨by linarith [hx.1], hx.2⟩) le_rfl)

/-- The joined exact selector residual belongs to `L²(0,1)`. -/
theorem memLp_fourCellOddP51SparseP11HighSelectorRepresenter_two_restrict
    (b₁ b₃ b₅ b₇ b₉ : ℝ) :
    MemLp (fourCellOddP51SparseP11HighSelectorRepresenter
      b₁ b₃ b₅ b₇ b₉) 2
      (volume.restrict (Ioc (0 : ℝ) 1)) := by
  let L : ℝ → ℝ :=
    fourCellOddP11GalerkinResidualLowerSelectorResidual
      (fourCellOddP11GalerkinRetainedSolution 0)
      (fourCellOddP11GalerkinRetainedSolution 1)
      (fourCellOddP11GalerkinRetainedSolution 2)
      (fourCellOddP11GalerkinRetainedSolution 3)
      b₁ b₃ b₅ b₇ b₉
  let U : ℝ → ℝ :=
    fourCellOddP11GalerkinResidualUpperSelectorResidual
      (fourCellOddP11GalerkinRetainedSolution 0)
      (fourCellOddP11GalerkinRetainedSolution 1)
      (fourCellOddP11GalerkinRetainedSolution 2)
      (fourCellOddP11GalerkinRetainedSolution 3)
      b₁ b₃ b₅ b₇ b₉
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)
  have hL : MemLp L 2 μ := by
    dsimp only [L, μ]
    apply memLp_mono_zero_one
    exact
      memLp_fourCellOddP11GalerkinResidualLowerSelectorResidual_two_restrict
        (fourCellOddP11GalerkinRetainedSolution 0)
        (fourCellOddP11GalerkinRetainedSolution 1)
        (fourCellOddP11GalerkinRetainedSolution 2)
        (fourCellOddP11GalerkinRetainedSolution 3)
        b₁ b₃ b₅ b₇ b₉
  have hU : MemLp U 2 μ := by
    dsimp only [U, μ]
    apply memLp_mono_zero_one
    exact
      memLp_fourCellOddP11GalerkinResidualUpperSelectorResidual_two_restrict
        (fourCellOddP11GalerkinRetainedSolution 0)
        (fourCellOddP11GalerkinRetainedSolution 1)
        (fourCellOddP11GalerkinRetainedSolution 2)
        (fourCellOddP11GalerkinRetainedSolution 3)
        b₁ b₃ b₅ b₇ b₉
  have hpiece := MemLp.piecewise (s := Iic (3 / 5 : ℝ))
    measurableSet_Iic
    (hL.mono_measure Measure.restrict_le_self)
    (hU.mono_measure Measure.restrict_le_self)
  simpa only [μ, L, U, Set.piecewise, mem_Iic,
    fourCellOddP51SparseP11HighSelectorRepresenter] using hpiece

private theorem centeredP1_eq_neg_centeredLegendre_one :
    centeredP1 = fun x ↦ -(centeredShiftedLegendreReal 1).eval x := by
  funext x
  rw [eval_centeredShiftedLegendreReal_one]
  unfold centeredP1
  ring

private theorem centeredP3_eq_neg_centeredLegendre_three :
    centeredP3 = fun x ↦ -(centeredShiftedLegendreReal 3).eval x := by
  funext x
  norm_num [centeredShiftedLegendreReal, shiftedLegendreReal,
    Polynomial.shiftedLegendre, Polynomial.eval_comp,
    Polynomial.eval_map, Polynomial.eval_finset_sum,
    Finset.sum_range_succ, Nat.choose, centeredP3,
    Polynomial.smul_eq_C_mul]
  ring

private theorem centeredP5_eq_neg_centeredLegendre_five :
    factorTwoCenteredP5 =
      fun x ↦ -(centeredShiftedLegendreReal 5).eval x := by
  funext x
  norm_num [centeredShiftedLegendreReal, shiftedLegendreReal,
    Polynomial.shiftedLegendre, Polynomial.eval_comp,
    Polynomial.eval_map, Polynomial.eval_finset_sum,
    Finset.sum_range_succ, Nat.choose, factorTwoCenteredP5,
    Polynomial.smul_eq_C_mul]
  ring

private theorem centeredP7_eq_neg_centeredLegendre_seven :
    factorTwoCenteredP7 =
      fun x ↦ -(centeredShiftedLegendreReal 7).eval x := by
  funext x
  have h := centeredPullback_factorTwoCenteredP7 ((x + 1) / 2)
  unfold centeredPullback at h
  rw [show 2 * ((x + 1) / 2) - 1 = x by ring] at h
  rw [eval_centeredShiftedLegendreReal]
  linarith

private theorem centeredP9_eq_neg_centeredLegendre_nine :
    factorTwoCenteredP9 =
      fun x ↦ -(centeredShiftedLegendreReal 9).eval x := by
  funext x
  have h := centeredPullback_factorTwoCenteredP9 ((x + 1) / 2)
  unfold centeredPullback at h
  rw [show 2 * ((x + 1) / 2) - 1 = x by ring] at h
  rw [eval_centeredShiftedLegendreReal]
  linarith

private theorem integral_highBasis_mul_centeredLegendre_eq_zero
    (i : Fin 21) (n : ℕ) (hn : n < 11) :
    (∫ x : ℝ in -1..1,
      fourCellOddFiniteRetainedBasis (Fin.natAdd 4 i : Fin 25) x *
        (-(centeredShiftedLegendreReal n).eval x)) = 0 := by
  have hne : fourCellOddFiniteRetainedDegree
      (Fin.natAdd 4 i : Fin 25) ≠ n := by
    unfold fourCellOddFiniteRetainedDegree
    simp only [Fin.val_natAdd]
    omega
  have horth := centeredPolynomialPair_legendre_eq_zero hne
  unfold centeredPolynomialPair at horth
  unfold fourCellOddFiniteRetainedBasis
  simpa only [neg_mul_neg] using horth

/-- Every high retained basis vector is a genuine `P11+` mode, uniformly in
its index. -/
theorem fourCellOddP51HighBasis_P11Plus_moments (i : Fin 21) :
    centeredOddP1Coefficient
        (fourCellOddFiniteRetainedBasis (Fin.natAdd 4 i : Fin 25)) = 0 ∧
      centeredOddP3Coefficient
        (fourCellOddFiniteRetainedBasis (Fin.natAdd 4 i : Fin 25)) = 0 ∧
      centeredOddP5Coefficient
        (fourCellOddFiniteRetainedBasis (Fin.natAdd 4 i : Fin 25)) = 0 ∧
      centeredOddP7Coefficient
        (fourCellOddFiniteRetainedBasis (Fin.natAdd 4 i : Fin 25)) = 0 ∧
      centeredOddP9Coefficient
        (fourCellOddFiniteRetainedBasis (Fin.natAdd 4 i : Fin 25)) = 0 := by
  have h1 := integral_highBasis_mul_centeredLegendre_eq_zero i 1 (by omega)
  have h3 := integral_highBasis_mul_centeredLegendre_eq_zero i 3 (by omega)
  have h5 := integral_highBasis_mul_centeredLegendre_eq_zero i 5 (by omega)
  have h7 := integral_highBasis_mul_centeredLegendre_eq_zero i 7 (by omega)
  have h9 := integral_highBasis_mul_centeredLegendre_eq_zero i 9 (by omega)
  unfold centeredOddP1Coefficient centeredOddP3Coefficient
    centeredOddP5Coefficient centeredOddP7Coefficient
    centeredOddP9Coefficient
  rw [centeredP1_eq_neg_centeredLegendre_one,
    centeredP3_eq_neg_centeredLegendre_three,
    centeredP5_eq_neg_centeredLegendre_five,
    centeredP7_eq_neg_centeredLegendre_seven,
    centeredP9_eq_neg_centeredLegendre_nine,
    h1, h3, h5, h7, h9]
  norm_num

private theorem memLp_two_zero_one_of_continuous
    (r : ℝ → ℝ) (hr : Continuous r) :
    MemLp r 2 (volume.restrict (Ioc (0 : ℝ) 1)) := by
  have hrMeas : AEStronglyMeasurable r
      (volume.restrict (Ioc (0 : ℝ) 1)) :=
    hr.aestronglyMeasurable.restrict
  rw [memLp_two_iff_integrable_sq_norm hrMeas]
  have hcompact : IntegrableOn (fun x : ℝ ↦ ‖r x‖ ^ 2)
      (Icc (0 : ℝ) 1) :=
    (hr.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  exact hcompact.mono_set Ioc_subset_Icc_self

/-- The joined selector residual represents the exact old Galerkin row on
every `P11+` profile. -/
theorem fourCellOddCoreLocalBilinear_sparseP11_eq_highSelectorRepresenter
    (b₁ b₃ b₅ b₇ b₉ : ℝ) (r : ℝ → ℝ)
    (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r)
    (h1 : centeredOddP1Coefficient r = 0)
    (h3 : centeredOddP3Coefficient r = 0)
    (h5 : centeredOddP5Coefficient r = 0)
    (h7 : centeredOddP7Coefficient r = 0)
    (h9 : centeredOddP9Coefficient r = 0) :
    fourCellOddCoreLocalBilinear
        fourCellOddP11GalerkinRetainedResidualProfile r =
      ∫ x : ℝ in 0..1,
        fourCellOddP51SparseP11HighSelectorRepresenter
          b₁ b₃ b₅ b₇ b₉ x * r x := by
  let L : ℝ → ℝ :=
    fourCellOddP11GalerkinResidualLowerSelectorResidual
      (fourCellOddP11GalerkinRetainedSolution 0)
      (fourCellOddP11GalerkinRetainedSolution 1)
      (fourCellOddP11GalerkinRetainedSolution 2)
      (fourCellOddP11GalerkinRetainedSolution 3)
      b₁ b₃ b₅ b₇ b₉
  let U : ℝ → ℝ :=
    fourCellOddP11GalerkinResidualUpperSelectorResidual
      (fourCellOddP11GalerkinRetainedSolution 0)
      (fourCellOddP11GalerkinRetainedSolution 1)
      (fourCellOddP11GalerkinRetainedSolution 2)
      (fourCellOddP11GalerkinRetainedSolution 3)
      b₁ b₃ b₅ b₇ b₉
  let F : ℝ → ℝ :=
    fourCellOddP51SparseP11HighSelectorRepresenter b₁ b₃ b₅ b₇ b₉
  have hFLp : MemLp F 2 (volume.restrict (Ioc (0 : ℝ) 1)) := by
    dsimp only [F]
    exact
      memLp_fourCellOddP51SparseP11HighSelectorRepresenter_two_restrict
        b₁ b₃ b₅ b₇ b₉
  have hrLp := memLp_two_zero_one_of_continuous r hr.continuous
  have hFI : IntervalIntegrable (fun x : ℝ ↦ F x * r x) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
    exact hFLp.integrable_mul hrLp
  have hFL : IntervalIntegrable (fun x : ℝ ↦ F x * r x)
      volume 0 (3 / 5) := hFI.mono_set (by
    intro x hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 3 / 5)] at hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact ⟨hx.1, by linarith [hx.2]⟩)
  have hFU : IntervalIntegrable (fun x : ℝ ↦ F x * r x)
      volume (3 / 5) 1 := hFI.mono_set (by
    intro x hx
    rw [uIcc_of_le (by norm_num : (3 / 5 : ℝ) ≤ 1)] at hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact ⟨by linarith [hx.1], hx.2⟩)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hFL hFU
  have hlower : (∫ x : ℝ in 0..3 / 5, F x * r x) =
      ∫ x : ℝ in 0..3 / 5, L x * r x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 3 / 5)] at hx
    dsimp only [F, L]
    unfold fourCellOddP51SparseP11HighSelectorRepresenter
    rw [if_pos hx.2]
  have hupper : (∫ x : ℝ in 3 / 5..1, F x * r x) =
      ∫ x : ℝ in 3 / 5..1, U x * r x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [MeasureTheory.Measure.ae_ne volume (3 / 5 : ℝ)] with x hxne
    intro hx
    rw [uIoc_of_le (by norm_num : (3 / 5 : ℝ) ≤ 1)] at hx
    dsimp only [F, U]
    unfold fourCellOddP51SparseP11HighSelectorRepresenter
    rw [if_neg (by linarith [hx.1])]
  have hrow :=
    fourCellOddCoreLocalBilinear_galerkinResidual_P11Plus_eq_selectorResiduals
      (fourCellOddP11GalerkinRetainedSolution 0)
      (fourCellOddP11GalerkinRetainedSolution 1)
      (fourCellOddP11GalerkinRetainedSolution 2)
      (fourCellOddP11GalerkinRetainedSolution 3)
      b₁ b₃ b₅ b₇ b₉ r hr hodd h1 h3 h5 h7 h9
  change fourCellOddCoreLocalBilinear
      fourCellOddP11GalerkinRetainedResidualProfile r =
    (∫ x : ℝ in 0..3 / 5, L x * r x) +
      ∫ x : ℝ in 3 / 5..1, U x * r x at hrow
  rw [← hlower, ← hupper, hsplit] at hrow
  exact hrow

/-- Uniform specialization to every sparse-anchor high normal row. -/
theorem fourCellOddCoreLocalBilinear_sparseP11_highBasis_eq_representer
    (b₁ b₃ b₅ b₇ b₉ : ℝ) (i : Fin 21) :
    fourCellOddCoreLocalBilinear
        fourCellOddP11GalerkinRetainedResidualProfile
        (fourCellOddFiniteRetainedBasis (Fin.natAdd 4 i : Fin 25)) =
      ∫ x : ℝ in 0..1,
        fourCellOddP51SparseP11HighSelectorRepresenter
            b₁ b₃ b₅ b₇ b₉ x *
          fourCellOddFiniteRetainedBasis (Fin.natAdd 4 i : Fin 25) x := by
  rcases fourCellOddP51HighBasis_P11Plus_moments i with
    ⟨h1, h3, h5, h7, h9⟩
  exact
    fourCellOddCoreLocalBilinear_sparseP11_eq_highSelectorRepresenter
      b₁ b₃ b₅ b₇ b₉
      (fourCellOddFiniteRetainedBasis (Fin.natAdd 4 i : Fin 25))
      (contDiff_fourCellOddFiniteRetainedBasis _)
      (odd_fourCellOddFiniteRetainedBasis _) h1 h3 h5 h7 h9

/-- The sparse high-normal energy is bounded by one exact piecewise
selector norm. -/
theorem fourCellOddP51SparseP11HighNormalResidualEnergy_le_selector_l2
    (b₁ b₃ b₅ b₇ b₉ : ℝ) :
    fourCellOddP51SparseP11HighNormalResidualEnergy ≤
      ∫ x : ℝ in 0..1,
        fourCellOddP51SparseP11HighSelectorRepresenter
          b₁ b₃ b₅ b₇ b₉ x ^ 2 := by
  apply
    fourCellOddP51SparseP11HighNormalResidualEnergy_le_l2_of_representer
  · exact
      memLp_fourCellOddP51SparseP11HighSelectorRepresenter_two_restrict
        b₁ b₃ b₅ b₇ b₉
  · exact
      fourCellOddCoreLocalBilinear_sparseP11_highBasis_eq_representer
        b₁ b₃ b₅ b₇ b₉

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP51SparseP11AnchorRepresenterStructural

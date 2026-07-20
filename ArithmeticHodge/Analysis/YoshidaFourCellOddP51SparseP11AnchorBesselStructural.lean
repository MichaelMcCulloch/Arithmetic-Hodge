import ArithmeticHodge.Analysis.YoshidaFourCellOddP51SparseP11AnchorMassStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddP51TailBudgetAssemblyStructural

set_option autoImplicit false

open MeasureTheory Real Set
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP51SparseP11AnchorBesselStructural

noncomputable section

open YoshidaFourCellOddFiniteLegendreSolveStructural
open YoshidaFourCellOddCoreNineteenTwentiethsCoercivityStructural
open YoshidaFourCellOddP11GalerkinSolutionBoxStructural
open YoshidaFourCellOddP51GalerkinRieszStructural
open YoshidaFourCellOddP51SparseP11AnchorMassStructural
open YoshidaFourCellOddP51TailBudgetAssemblyStructural
open YoshidaFourCellOddStripCapacityClosureStructural

/-!
# Bessel reduction for the sparse P11 anchor

The twenty-one unsolved normal rows of the sparse `P11` anchor are an
orthogonal Legendre block.  Therefore their weighted square sum is bounded
by the `L²` norm of any common row representer.  This is a genuine Bessel
argument: it does not estimate the rows separately and introduces no factor
of twenty-one.
-/

/-- Pad a coefficient vector on `P11,P13,...,P51` by four zero low
coordinates. -/
def fourCellOddP51PadHighCoefficients (c : Fin 21 → ℝ) :
    FourCellOddP51RetainedIndex → ℝ :=
  @Fin.addCases 4 21 (fun _ ↦ ℝ) (fun _ ↦ 0) c

/-- The weighted Legendre coefficients of the projection of `F` onto the
twenty-one high retained coordinates. -/
def fourCellOddP51HighRowProjectionCoefficients
    (F : ℝ → ℝ) (i : Fin 21) : ℝ :=
  (2 * (@fourCellOddFiniteRetainedDegree 24
      (Fin.natAdd 4 i : Fin 25) : ℝ) + 1) *
    (∫ x : ℝ in 0..1,
      F x * fourCellOddFiniteRetainedBasis
        (Fin.natAdd 4 i : Fin 25) x)

/-- Orthogonal projection of `F` onto `P11,P13,...,P51`. -/
def fourCellOddP51HighRowProjection (F : ℝ → ℝ) : ℝ → ℝ :=
  fourCellOddP51RetainedProfile
    (fourCellOddP51PadHighCoefficients
      (fourCellOddP51HighRowProjectionCoefficients F))

private theorem high_weight_pos (i : Fin 21) :
    0 < 2 * (@fourCellOddFiniteRetainedDegree 24
      (Fin.natAdd 4 i : Fin 25) : ℝ) + 1 := by
  positivity

theorem continuous_fourCellOddP51HighRowProjection (F : ℝ → ℝ) :
    Continuous (fourCellOddP51HighRowProjection F) := by
  unfold fourCellOddP51HighRowProjection fourCellOddP51RetainedProfile
  exact (contDiff_fourCellOddFiniteRetainedProfile 24 _).continuous

/-- Exact norm of the finite high-row projection. -/
theorem integral_zero_one_fourCellOddP51HighRowProjection_sq
    (F : ℝ → ℝ) :
    (∫ x : ℝ in 0..1, fourCellOddP51HighRowProjection F x ^ 2) =
      ∑ i : Fin 21,
        (2 * (@fourCellOddFiniteRetainedDegree 24
            (Fin.natAdd 4 i : Fin 25) : ℝ) + 1) *
          (∫ x : ℝ in 0..1,
            F x * fourCellOddFiniteRetainedBasis
              (Fin.natAdd 4 i : Fin 25) x) ^ 2 := by
  rw [show fourCellOddP51HighRowProjection F =
      fourCellOddFiniteRetainedProfile 24
        (fourCellOddP51PadHighCoefficients
          (fourCellOddP51HighRowProjectionCoefficients F)) by rfl,
    integral_zero_one_fourCellOddFiniteRetainedProfile_sq]
  change (∑ i : Fin (4 + 21),
      fourCellOddP51PadHighCoefficients
          (fourCellOddP51HighRowProjectionCoefficients F) i ^ 2 /
        (2 * (fourCellOddFiniteRetainedDegree i : ℝ) + 1)) = _
  rw [Fin.sum_univ_add]
  simp only [fourCellOddP51PadHighCoefficients, Fin.addCases_left,
    Fin.addCases_right, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_div,
    Finset.sum_const_zero, zero_add]
  apply Finset.sum_congr rfl
  intro i hi
  unfold fourCellOddP51HighRowProjectionCoefficients
  have hw := (high_weight_pos i).ne'
  field_simp

private theorem memLp_basis_zero_one (i : Fin 21) :
    MemLp
      (fourCellOddFiniteRetainedBasis (Fin.natAdd 4 i : Fin 25)) 2
      (volume.restrict (Ioc (0 : ℝ) 1)) := by
  let p : ℝ → ℝ :=
    fourCellOddFiniteRetainedBasis (Fin.natAdd 4 i : Fin 25)
  have hp : Continuous p := by
    dsimp only [p]
    exact (contDiff_fourCellOddFiniteRetainedBasis _).continuous
  have hpMeas : AEStronglyMeasurable p
      (volume.restrict (Ioc (0 : ℝ) 1)) :=
    hp.aestronglyMeasurable.restrict
  rw [memLp_two_iff_integrable_sq_norm hpMeas]
  have hcompact : IntegrableOn (fun x : ℝ ↦ ‖p x‖ ^ 2)
      (Icc (0 : ℝ) 1) :=
    (hp.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  exact hcompact.mono_set Ioc_subset_Icc_self

/-- Pairing `F` with its high-row projection reproduces the same weighted
square sum. -/
theorem integral_zero_one_mul_fourCellOddP51HighRowProjection
    (F : ℝ → ℝ)
    (hF : MemLp F 2 (volume.restrict (Ioc (0 : ℝ) 1))) :
    (∫ x : ℝ in 0..1, F x * fourCellOddP51HighRowProjection F x) =
      ∑ i : Fin 21,
        (2 * (@fourCellOddFiniteRetainedDegree 24
            (Fin.natAdd 4 i : Fin 25) : ℝ) + 1) *
          (∫ x : ℝ in 0..1,
            F x * fourCellOddFiniteRetainedBasis
              (Fin.natAdd 4 i : Fin 25) x) ^ 2 := by
  have hprod (i : Fin 21) : IntervalIntegrable
      (fun x : ℝ ↦ F x *
        fourCellOddFiniteRetainedBasis (Fin.natAdd 4 i : Fin 25) x)
      volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
    exact hF.integrable_mul (memLp_basis_zero_one i)
  rw [show (fun x : ℝ ↦ F x * fourCellOddP51HighRowProjection F x) =
      fun x ↦ ∑ i : Fin 21,
        fourCellOddP51HighRowProjectionCoefficients F i *
          (F x * fourCellOddFiniteRetainedBasis
            (Fin.natAdd 4 i : Fin 25) x) by
    funext x
    unfold fourCellOddP51HighRowProjection fourCellOddP51RetainedProfile
      fourCellOddFiniteRetainedProfile
    simp only [Finset.sum_apply]
    change F x * (∑ i : Fin (4 + 21),
      fourCellOddP51PadHighCoefficients
          (fourCellOddP51HighRowProjectionCoefficients F) i *
        fourCellOddFiniteRetainedBasis i x) = _
    rw [Fin.sum_univ_add]
    simp only [fourCellOddP51PadHighCoefficients, Fin.addCases_left,
      zero_mul, Finset.sum_const_zero, Fin.addCases_right, zero_add]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring,
    intervalIntegral.integral_finset_sum]
  · simp_rw [intervalIntegral.integral_const_mul]
    apply Finset.sum_congr rfl
    intro i hi
    unfold fourCellOddP51HighRowProjectionCoefficients
    ring
  · intro i hi
    exact (hprod i).const_mul _

/-- Bessel's inequality for the complete high retained block. -/
theorem fourCellOddP51HighRowProjection_energy_le
    (F : ℝ → ℝ)
    (hF : MemLp F 2 (volume.restrict (Ioc (0 : ℝ) 1))) :
    (∑ i : Fin 21,
        (2 * (@fourCellOddFiniteRetainedDegree 24
            (Fin.natAdd 4 i : Fin 25) : ℝ) + 1) *
          (∫ x : ℝ in 0..1,
            F x * fourCellOddFiniteRetainedBasis
              (Fin.natAdd 4 i : Fin 25) x) ^ 2) ≤
      ∫ x : ℝ in 0..1, F x ^ 2 := by
  let E : ℝ := ∑ i : Fin 21,
    (2 * (@fourCellOddFiniteRetainedDegree 24
        (Fin.natAdd 4 i : Fin 25) : ℝ) + 1) *
      (∫ x : ℝ in 0..1,
        F x * fourCellOddFiniteRetainedBasis
          (Fin.natAdd 4 i : Fin 25) x) ^ 2
  have hE0 : 0 ≤ E := by
    dsimp only [E]
    exact Finset.sum_nonneg (fun i _hi ↦
      mul_nonneg (high_weight_pos i).le (sq_nonneg _))
  have hcauchy := sq_intervalIntegral_mul_le_zero_one_of_memLp
    F (fourCellOddP51HighRowProjection F) hF
      (continuous_fourCellOddP51HighRowProjection F)
  rw [integral_zero_one_mul_fourCellOddP51HighRowProjection F hF,
    integral_zero_one_fourCellOddP51HighRowProjection_sq F] at hcauchy
  change E ^ 2 ≤ (∫ x : ℝ in 0..1, F x ^ 2) * E at hcauchy
  change E ≤ ∫ x : ℝ in 0..1, F x ^ 2
  by_cases hE : E = 0
  · rw [hE]
    have hFmass : 0 ≤ ∫ x : ℝ in 0..1, F x ^ 2 := by
      apply intervalIntegral.integral_nonneg (by norm_num)
      intro x hx
      exact sq_nonneg (F x)
    exact hFmass
  · have hEpos : 0 < E := lt_of_le_of_ne hE0 (Ne.symm hE)
    nlinarith

/-- Any common `L²` representer of the twenty-one sparse-anchor normal
rows bounds their complete weighted residual energy with no dimension
loss. -/
theorem fourCellOddP51SparseP11HighNormalResidualEnergy_le_l2_of_representer
    (F : ℝ → ℝ)
    (hF : MemLp F 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hrow : ∀ i : Fin 21,
      fourCellOddCoreLocalBilinear
          fourCellOddP11GalerkinRetainedResidualProfile
          (fourCellOddFiniteRetainedBasis (Fin.natAdd 4 i : Fin 25)) =
        ∫ x : ℝ in 0..1,
          F x * fourCellOddFiniteRetainedBasis
            (Fin.natAdd 4 i : Fin 25) x) :
    fourCellOddP51SparseP11HighNormalResidualEnergy ≤
      ∫ x : ℝ in 0..1, F x ^ 2 := by
  unfold fourCellOddP51SparseP11HighNormalResidualEnergy
  simp_rw [hrow]
  exact fourCellOddP51HighRowProjection_energy_le F hF

/-- A single representer norm certificate discharges the sparse-anchor
scalar premise used by the final P51 assembly. -/
theorem fourCellOddP51SparseP11HighCertificate_of_representer_l2
    (F : ℝ → ℝ)
    (hF : MemLp F 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hrow : ∀ i : Fin 21,
      fourCellOddCoreLocalBilinear
          fourCellOddP11GalerkinRetainedResidualProfile
          (fourCellOddFiniteRetainedBasis (Fin.natAdd 4 i : Fin 25)) =
        ∫ x : ℝ in 0..1,
          F x * fourCellOddFiniteRetainedBasis
            (Fin.natAdd 4 i : Fin 25) x)
    (hl2 : (∫ x : ℝ in 0..1, F x ^ 2) ≤
      fourCellOddNineteenTwentiethsCoercivityConstant *
        (fourCellOddCoreLocalQuadratic
            fourCellOddP11GalerkinRetainedResidualProfile -
          (7 / 10000 : ℝ))) :
    fourCellOddP51SparseP11HighNormalResidualEnergy ≤
      fourCellOddNineteenTwentiethsCoercivityConstant *
        (fourCellOddCoreLocalQuadratic
            fourCellOddP11GalerkinRetainedResidualProfile -
          (7 / 10000 : ℝ)) :=
  (fourCellOddP51SparseP11HighNormalResidualEnergy_le_l2_of_representer
    F hF hrow).trans hl2

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP51SparseP11AnchorBesselStructural

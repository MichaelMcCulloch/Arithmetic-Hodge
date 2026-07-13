import ArithmeticHodge.Analysis.ShiftedLegendreCenteredParity
import ArithmeticHodge.Analysis.ShiftedLegendreL2HigherGap

set_option autoImplicit false

open MeasureTheory
open scoped unitInterval

namespace ArithmeticHodge.Analysis.ShiftedLegendreParityGap

open ShiftedLegendreCenteredParity
open ShiftedLegendreFiniteEnergyGap
open ShiftedLegendreL2Basis
open ShiftedLegendreL2HigherGap
open UnitIntervalLogEnergyProjection

noncomputable section

/-!
# Exact logarithmic gaps in the parity sectors

Parity removes every coefficient of the opposite parity.  Once the genuine
low mode in a sector is removed, the complete remaining tail therefore starts
at degree two in the even sector and degree three in the odd sector.
-/

/-- A reflection-even mean-zero function has exact logarithmic gap `2 H₂ = 3`.
-/
theorem three_mul_integral_sq_le_unitIntervalLogEnergy_of_symm_even
    (f : unitInterval → ℝ)
    (hf : MemLp f 2 (volume : Measure unitInterval))
    (henergy : Integrable (unitIntervalRawLogEnergyIntegrand f))
    (hsymm : ∀ t, f (unitInterval.symm t) = f t)
    (hmean : (∫ t : unitInterval, f t) = 0) :
    3 * (∫ t : unitInterval, f t ^ 2) ≤ unitIntervalLogEnergy f := by
  have hlow : ∀ n < 2,
      shiftedLegendreHilbertBasis.repr (hf.toLp f) n = 0 := by
    intro n hn
    have hcases : n = 0 ∨ n = 1 := by omega
    rcases hcases with rfl | rfl
    · exact shiftedLegendreHilbertBasis_repr_zero_eq_zero_of_integral_eq_zero
        f hf hmean
    · exact shiftedLegendreHilbertBasis_repr_eq_zero_of_symm_eq_of_odd
        f hf hsymm 1 (by norm_num)
  have hgap := harmonic_mul_integral_sq_le_unitIntervalLogEnergy
    f hf henergy 2 hlow
  norm_num [harmonic, Finset.sum_range_succ] at hgap
  exact hgap

/-- A reflection-odd function with its degree-one coefficient removed has
exact logarithmic gap `2 H₃ = 11/3`. -/
theorem eleven_div_three_mul_integral_sq_le_unitIntervalLogEnergy_of_symm_odd
    (f : unitInterval → ℝ)
    (hf : MemLp f 2 (volume : Measure unitInterval))
    (henergy : Integrable (unitIntervalRawLogEnergyIntegrand f))
    (hsymm : ∀ t, f (unitInterval.symm t) = -f t)
    (hone : shiftedLegendreHilbertBasis.repr (hf.toLp f) 1 = 0) :
    (11 / 3 : ℝ) * (∫ t : unitInterval, f t ^ 2) ≤
      unitIntervalLogEnergy f := by
  have hlow : ∀ n < 3,
      shiftedLegendreHilbertBasis.repr (hf.toLp f) n = 0 := by
    intro n hn
    have hcases : n = 0 ∨ n = 1 ∨ n = 2 := by omega
    rcases hcases with rfl | rfl | rfl
    · exact shiftedLegendreHilbertBasis_repr_eq_zero_of_symm_neg_of_even
        f hf hsymm 0 (by norm_num)
    · exact hone
    · exact shiftedLegendreHilbertBasis_repr_eq_zero_of_symm_neg_of_even
        f hf hsymm 2 (by norm_num)
  have hgap := harmonic_mul_integral_sq_le_unitIntervalLogEnergy
    f hf henergy 3 hlow
  norm_num [harmonic, Finset.sum_range_succ] at hgap
  exact hgap

end

end ArithmeticHodge.Analysis.ShiftedLegendreParityGap

import ArithmeticHodge.Analysis.ShiftedLegendreFiniteEnergyGap
import ArithmeticHodge.Analysis.UnitIntervalLogEnergyAffine

set_option autoImplicit false

open MeasureTheory Polynomial
open scoped unitInterval InnerProductSpace

namespace ArithmeticHodge.Analysis.ShiftedLegendreCenteredParity

open ShiftedLegendreOrthogonality
open ShiftedLegendreL2Basis
open ShiftedLegendreFiniteEnergyGap
open UnitIntervalLogEnergyAffine

noncomputable section

/-!
# Centered parity of the shifted-Legendre basis

Reflection of the unit interval corresponds exactly to negation after the
affine map `t ↦ 2t - 1`.  The structural shifted-Legendre reflection law
therefore removes every basis coefficient of the opposite parity at once.
-/

/-- Shifted Legendre degree `n` has reflection sign `(-1) ^ n` on the unit
interval. -/
theorem shiftedLegendreReal_eval_symm (n : ℕ) (t : unitInterval) :
    (shiftedLegendreReal n).eval (unitInterval.symm t : ℝ) =
      (-1 : ℝ) ^ n * (shiftedLegendreReal n).eval (t : ℝ) := by
  simp only [shiftedLegendreReal, Polynomial.eval_map]
  change Polynomial.aeval (1 - (t : ℝ)) (Polynomial.shiftedLegendre n) =
    (-1 : ℝ) ^ n *
      Polynomial.aeval (t : ℝ) (Polynomial.shiftedLegendre n)
  simpa using Polynomial.shiftedLegendre_eval_symm n (1 - (t : ℝ))

/-- A function antisymmetric under unit-interval reflection has zero
integral. -/
theorem unitIntervalIntegral_eq_zero_of_symm_neg
    (g : unitInterval → ℝ)
    (hsymm : ∀ t, g (unitInterval.symm t) = -g t) :
    (∫ t : unitInterval, g t) = 0 := by
  have hchange : (∫ t : unitInterval, g (unitInterval.symm t)) =
      ∫ t : unitInterval, g t :=
    unitInterval.measurePreserving_symm.integral_comp
      unitInterval.symmMeasurableEquiv.measurableEmbedding g
  have hneg : (∫ t : unitInterval, g (unitInterval.symm t)) =
      -(∫ t : unitInterval, g t) := by
    calc
      _ = ∫ t : unitInterval, -g t := by
        apply integral_congr_ae
        filter_upwards [] with t
        exact hsymm t
      _ = _ := integral_neg g
  linarith

/-- Every shifted-Legendre Hilbert coefficient is its unnormalized
polynomial pairing times the nonzero basis normalization. -/
theorem shiftedLegendreHilbertBasis_repr_eq
    (f : unitInterval → ℝ)
    (hf : MemLp f 2 (volume : Measure unitInterval)) (n : ℕ) :
    shiftedLegendreHilbertBasis.repr (hf.toLp f) n =
      ‖shiftedLegendreL2 n‖⁻¹ *
        ∫ t : unitInterval,
          f t * (shiftedLegendreReal n).eval (t : ℝ) := by
  rw [shiftedLegendreHilbertBasis.repr_apply_apply,
    shiftedLegendreHilbertBasis_apply, normalizedShiftedLegendreL2,
    real_inner_smul_left, real_inner_comm, shiftedLegendreL2,
    ← integral_mul_polynomial_eq_inner f hf]

/-- Reflection-odd functions have no even shifted-Legendre coefficients. -/
theorem shiftedLegendreHilbertBasis_repr_eq_zero_of_symm_neg_of_even
    (f : unitInterval → ℝ)
    (hf : MemLp f 2 (volume : Measure unitInterval))
    (hsymm : ∀ t, f (unitInterval.symm t) = -f t)
    (n : ℕ) (hn : Even n) :
    shiftedLegendreHilbertBasis.repr (hf.toLp f) n = 0 := by
  rw [shiftedLegendreHilbertBasis_repr_eq f hf n]
  suffices (∫ t : unitInterval,
      f t * (shiftedLegendreReal n).eval (t : ℝ)) = 0 by
    rw [this, mul_zero]
  apply unitIntervalIntegral_eq_zero_of_symm_neg
  intro t
  rw [hsymm, shiftedLegendreReal_eval_symm, hn.neg_one_pow]
  ring

/-- Reflection-even functions have no odd shifted-Legendre coefficients. -/
theorem shiftedLegendreHilbertBasis_repr_eq_zero_of_symm_eq_of_odd
    (f : unitInterval → ℝ)
    (hf : MemLp f 2 (volume : Measure unitInterval))
    (hsymm : ∀ t, f (unitInterval.symm t) = f t)
    (n : ℕ) (hn : Odd n) :
    shiftedLegendreHilbertBasis.repr (hf.toLp f) n = 0 := by
  rw [shiftedLegendreHilbertBasis_repr_eq f hf n]
  suffices (∫ t : unitInterval,
      f t * (shiftedLegendreReal n).eval (t : ℝ)) = 0 by
    rw [this, mul_zero]
  apply unitIntervalIntegral_eq_zero_of_symm_neg
  intro t
  rw [hsymm, shiftedLegendreReal_eval_symm, hn.neg_one_pow]
  ring

/-- A centered odd function pulls back to a reflection-odd unit-interval
function. -/
theorem centeredPullback_symm_of_odd
    (w : ℝ → ℝ) (hw : Function.Odd w) (t : unitInterval) :
    centeredPullback w (unitInterval.symm t : ℝ) =
      -centeredPullback w (t : ℝ) := by
  unfold centeredPullback
  rw [show 2 * (unitInterval.symm t : ℝ) - 1 =
      -(2 * (t : ℝ) - 1) by
    rw [unitInterval.coe_symm_eq]
    ring]
  exact hw _

/-- A centered even function pulls back to a reflection-even unit-interval
function. -/
theorem centeredPullback_symm_of_even
    (w : ℝ → ℝ) (hw : Function.Even w) (t : unitInterval) :
    centeredPullback w (unitInterval.symm t : ℝ) =
      centeredPullback w (t : ℝ) := by
  unfold centeredPullback
  rw [show 2 * (unitInterval.symm t : ℝ) - 1 =
      -(2 * (t : ℝ) - 1) by
    rw [unitInterval.coe_symm_eq]
    ring]
  exact hw _

/-- Centered odd functions have no even shifted-Legendre coefficients. -/
theorem centeredPullback_repr_eq_zero_of_odd_of_even
    (w : ℝ → ℝ)
    (hf : MemLp (fun t : unitInterval ↦ centeredPullback w (t : ℝ)) 2)
    (hw : Function.Odd w) (n : ℕ) (hn : Even n) :
    shiftedLegendreHilbertBasis.repr
        (hf.toLp (fun t : unitInterval ↦ centeredPullback w (t : ℝ))) n = 0 := by
  exact shiftedLegendreHilbertBasis_repr_eq_zero_of_symm_neg_of_even
    _ hf (centeredPullback_symm_of_odd w hw) n hn

/-- Centered even functions have no odd shifted-Legendre coefficients. -/
theorem centeredPullback_repr_eq_zero_of_even_of_odd
    (w : ℝ → ℝ)
    (hf : MemLp (fun t : unitInterval ↦ centeredPullback w (t : ℝ)) 2)
    (hw : Function.Even w) (n : ℕ) (hn : Odd n) :
    shiftedLegendreHilbertBasis.repr
        (hf.toLp (fun t : unitInterval ↦ centeredPullback w (t : ℝ))) n = 0 := by
  exact shiftedLegendreHilbertBasis_repr_eq_zero_of_symm_eq_of_odd
    _ hf (centeredPullback_symm_of_even w hw) n hn

end

end ArithmeticHodge.Analysis.ShiftedLegendreCenteredParity

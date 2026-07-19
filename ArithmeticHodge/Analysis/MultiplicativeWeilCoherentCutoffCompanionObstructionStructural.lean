import ArithmeticHodge.Analysis.MultiplicativeWeilDirectedCorrelationDerivativeStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilMellinBumpSequence
import ArithmeticHodge.Analysis.MultiplicativeWeilCorrectedChebyshevPotentialStructural

set_option autoImplicit false

open Complex MeasureTheory Real Set
open scoped ContDiff

namespace ArithmeticHodge.Analysis.MultiplicativeWeilCoherentCutoffCompanionObstructionStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilDirectedCorrelationDerivativeStructural
open MultiplicativeWeilCorrectedChebyshevPotentialStructural

/-!
# The cutoff-derivative companion and its mass obstruction

The derivative of a coherent partition weight would become an ordinary
Bombieri cross if it were the derivative of a compactly supported companion.
This module proves that representation conditionally and identifies its sharp
compatibility condition: every such derivative source must have total mass
zero.  A unit-mass Bombieri bump shows that an uncompensated companion cannot
be constructed for arbitrary smooth weights.
-/

/-- If the literal companion equation existed, its conjugated directed-
correlation derivative integrand would be exactly the `eta'` summand in the
coherent derivative integrand. -/
theorem coherentCutoffDerivative_eq_literalCompanionIntegrand
    (parent h U : BombieriTest) (eta theta : ℝ → ℝ)
    (hh : ∀ z : ℝ, h z = (theta z : ℂ) * parent z)
    (hU : ∀ z : ℝ,
      deriv U z = ((deriv eta z : ℝ) : ℂ) * parent z)
    (x y : ℝ) :
    (((y * deriv eta (x * y) * theta y : ℝ) : ℂ) *
        (starRingEnd ℂ (parent (x * y)) * parent y)) =
      ((y : ℂ) * starRingEnd ℂ (deriv U (x * y))) * h y := by
  rw [hU, hh]
  simp only [map_mul, starRingEnd_apply]
  simp only [RCLike.star_def, Complex.conj_ofReal]
  push_cast
  ring

/-- Conditionally on a literal companion, the complete inner cutoff term is
the derivative of its conjugated directed correlation with the window cell. -/
theorem integral_coherentCutoffDerivative_eq_deriv_star_companion
    (parent h U : BombieriTest) (eta theta : ℝ → ℝ)
    (hh : ∀ z : ℝ, h z = (theta z : ℂ) * parent z)
    (hU : ∀ z : ℝ,
      deriv U z = ((deriv eta z : ℝ) : ℂ) * parent z)
    (x : ℝ) :
    (∫ y : ℝ in Set.Ioi 0,
      (((y * deriv eta (x * y) * theta y : ℝ) : ℂ) *
        (starRingEnd ℂ (parent (x * y)) * parent y))) =
      deriv (fun z : ℝ ↦
        starRingEnd ℂ (bombieriDirectedCorrelation U h z)) x := by
  rw [deriv_star_bombieriDirectedCorrelation_eq_integral]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y _hy
  exact coherentCutoffDerivative_eq_literalCompanionIntegrand
    parent h U eta theta hh hU x y

/-- Under support separation, a hypothetical literal companion packages the
full outer corrected-potential pairing of the cutoff term as one global
cross. -/
theorem bombieriTwoBlockGlobalCrossSymbol_eq_cutoffDerivativePotential_of_literalCompanion
    (parent h U : BombieriTest) (eta theta : ℝ → ℝ)
    (hh : ∀ z : ℝ, h z = (theta z : ℂ) * parent z)
    (hU : ∀ z : ℝ,
      deriv U z = ((deriv eta z : ℝ) : ℂ) * parent z)
    {aU bU ah bh : ℝ}
    (hah : 0 < ah) (hbh : 0 < bh)
    (hUsupport : tsupport U ⊆ Set.Icc aU bU)
    (hhsupport : tsupport h ⊆ Set.Icc ah bh)
    (hsep : bh < aU) :
    bombieriTwoBlockGlobalCrossSymbol U h =
      (∫ x : ℝ in Set.Ioi 0,
        ((Chebyshev.psi x - x : ℝ) : ℂ) *
          ∫ y : ℝ in Set.Ioi 0,
            (((y * deriv eta (x * y) * theta y : ℝ) : ℂ) *
              (starRingEnd ℂ (parent (x * y)) * parent y))) +
      ∫ x : ℝ in Set.Ioi 0,
        ((correctedChebyshevPotential x : ℝ) : ℂ) *
          ∫ y : ℝ in Set.Ioi 0,
            (((y * deriv eta (x * y) * theta y : ℝ) : ℂ) *
              (starRingEnd ℂ (parent (x * y)) * parent y)) := by
  have haU : 0 < aU := hbh.trans hsep
  have hratio : bh / aU < 1 := by
    rw [div_lt_one haU]
    exact hsep
  have H :=
    sqrt_mul_bombieriTwoBlockGlobalCrossSymbol_normalizedDilation_eq_chebyshevError_add_correctedPotential
      U h (r := 1) (by norm_num) haU hah hbh
      hUsupport hhsupport hratio
  simp only [Real.sqrt_one, Complex.ofReal_one, one_mul,
    normalizedDilation_one] at H
  rw [H]
  congr 1
  · apply setIntegral_congr_fun measurableSet_Ioi
    intro x _hx
    simp only
    congr 1
    exact (integral_coherentCutoffDerivative_eq_deriv_star_companion
      parent h U eta theta hh hU x).symm
  · apply setIntegral_congr_fun measurableSet_Ioi
    intro x _hx
    simp only
    congr 1
    exact (integral_coherentCutoffDerivative_eq_deriv_star_companion
      parent h U eta theta hh hU x).symm

/-- Every literal Bombieri companion has derivative of total mass zero on
the positive half-line. -/
theorem integral_Ioi_deriv_bombieriTest_eq_zero (u : BombieriTest) :
    (∫ z : ℝ in Set.Ioi 0, deriv u z) = 0 := by
  have h := HasCompactSupport.integral_Ioi_deriv_eq
    (u.contDiff.of_le (by norm_num)) u.hasCompactSupport 0
  exact h.trans (by simp [u.apply_eq_zero_of_nonpos])

/-- Therefore the literal equation `U' = eta' * parent` has a necessary
mean-zero condition. -/
theorem cutoffDerivative_companion_forces_zeroMass
    (parent U : BombieriTest) (eta : ℝ → ℝ)
    (hU : ∀ z : ℝ,
      deriv U z = ((deriv eta z : ℝ) : ℂ) * parent z) :
    (∫ z : ℝ in Set.Ioi 0,
      ((deriv eta z : ℝ) : ℂ) * parent z) = 0 := by
  rw [← integral_Ioi_deriv_bombieriTest_eq_zero U]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro z _hz
  exact (hU z).symm

private theorem integral_Ioi_mellinBumpSequence_eq_one (n : ℕ) :
    (∫ z : ℝ in Set.Ioi 0, mellinBumpSequence n z) = 1 := by
  have hIoi : Set.indicator (Set.Ioi (0 : ℝ))
      (mellinBumpSequence n : ℝ → ℂ) = mellinBumpSequence n := by
    funext z
    by_cases hz : z ∈ Set.Ioi (0 : ℝ)
    · simp [hz]
    · rw [Set.indicator_of_notMem hz]
      exact (mellinBumpSequence n).apply_eq_zero_of_nonpos
        hz |>.symm
  rw [← integral_indicator measurableSet_Ioi, hIoi]
  have hreal : (mellinBumpSequence n : ℝ → ℂ) =
      fun z : ℝ ↦ ((mellinBumpSequence n z).re : ℂ) := by
    funext z
    apply Complex.ext
    · simp
    · simp [mellinBumpSequence_real_nonnegative n z |>.2]
  rw [hreal]
  calc
    (∫ z : ℝ, (((mellinBumpSequence n z).re : ℝ) : ℂ)) =
        (((∫ z : ℝ, (mellinBumpSequence n z).re) : ℝ) : ℂ) :=
      integral_ofReal
    _ = 1 := by rw [mellinBumpSequence_unit_mass]; norm_num

/-- The obstruction is genuine: for the smooth identity weight and a
unit-mass positive Bombieri bump, no exact compactly supported companion can
have `U' = eta' * parent`. -/
theorem no_literal_cutoffDerivative_companion_for_unitBump (n : ℕ) :
    ¬ ∃ U : BombieriTest, ∀ z : ℝ,
      deriv U z =
        ((deriv (fun w : ℝ ↦ w) z : ℝ) : ℂ) *
          mellinBumpSequence n z := by
  intro h
  obtain ⟨U, hU⟩ := h
  have hzero := cutoffDerivative_companion_forces_zeroMass
    (mellinBumpSequence n) U (fun w : ℝ ↦ w) hU
  simp only [deriv_id'', ofReal_one, one_mul] at hzero
  rw [integral_Ioi_mellinBumpSequence_eq_one] at hzero
  norm_num at hzero

end

end ArithmeticHodge.Analysis.MultiplicativeWeilCoherentCutoffCompanionObstructionStructural

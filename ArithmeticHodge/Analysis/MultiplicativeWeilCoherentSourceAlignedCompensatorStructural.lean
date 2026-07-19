import ArithmeticHodge.Analysis.MultiplicativeWeilCoherentCompensatedEnergyCovarianceStructural

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.MultiplicativeWeilCoherentSourceAlignedCompensatorStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilCoherentCompensatedEnergyCovarianceStructural

/-!
# The source-aligned compensator obstruction

The most direct compensator normalizes the actual cutoff derivative source by
its ordinary mass.  This choice is exactly covariant under derivative-source
dilation, but it annihilates the compensated source.  Consequently the
rank-one energy expansion is saturated: this canonical choice creates no
positive companion-energy reserve.
-/

/-- Normalize a nonzero-mass derivative source to ordinary mass one. -/
def sourceAlignedCompensator (q : BombieriTest) : BombieriTest :=
  (ordinaryMass q)⁻¹ • q

/-- A source-aligned compensator has ordinary mass one whenever the source
mass is nonzero. -/
theorem ordinaryMass_sourceAlignedCompensator
    (q : BombieriTest) (hmass : ordinaryMass q ≠ 0) :
    ordinaryMass (sourceAlignedCompensator q) = 1 := by
  unfold sourceAlignedCompensator ordinaryMass
  change (∫ x : ℝ in Set.Ioi 0, (ordinaryMass q)⁻¹ * q x) = 1
  calc
    (∫ x : ℝ in Set.Ioi 0, (ordinaryMass q)⁻¹ * q x) =
        (ordinaryMass q)⁻¹ * ∫ x : ℝ in Set.Ioi 0, q x := by
          exact MeasureTheory.integral_const_mul
            (μ := volume.restrict (Set.Ioi 0))
            (ordinaryMass q)⁻¹ (q : ℝ → ℂ)
    _ = 1 := inv_mul_cancel₀ hmass

/-- Source alignment is exactly covariant: derivative-source dilation of the
source induces the mass-preserving dilation of its compensator. -/
theorem sourceAlignedCompensator_dilation_covariant
    (lambda : ℝ) (hlambda : 0 < lambda) (q : BombieriTest)
    (hmass : ordinaryMass q ≠ 0) :
    sourceAlignedCompensator
        (derivativeSourceDilation lambda hlambda q) =
      unitMassBumpDilation lambda hlambda
        (sourceAlignedCompensator q) := by
  rw [sourceAlignedCompensator, ordinaryMass_derivativeSourceDilation]
  ext x
  simp only [derivativeSourceDilation, unitMassBumpDilation,
    sourceAlignedCompensator, TestFunction.coe_smul, Pi.smul_apply,
    smul_eq_mul, normalizedDilation_apply]
  have hsqrt : Real.sqrt lambda ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hlambda)
  have hsqrt_sq : (((Real.sqrt lambda : ℝ) : ℂ) ^ 2) = (lambda : ℂ) := by
    norm_cast
    exact Real.sq_sqrt hlambda.le
  field_simp [hsqrt, hmass]
  rw [hsqrt_sq]

/-- The source-aligned rank-one subtraction removes the source identically. -/
theorem compensatedSource_sourceAlignedCompensator_eq_zero
    (q : BombieriTest) (hmass : ordinaryMass q ≠ 0) :
    compensatedSource q (sourceAlignedCompensator q) = 0 := by
  ext x
  simp only [compensatedSource, sourceAlignedCompensator,
    TestFunction.coe_sub, Pi.sub_apply, TestFunction.coe_smul, Pi.smul_apply,
    smul_eq_mul, TestFunction.coe_zero, Pi.zero_apply]
  field_simp [hmass]
  ring

/-- Exact energy saturation for the source-aligned compensator.  The
compensated energy is zero, so the cross term equals the complete sum of the
two diagonal terms. -/
theorem sourceAlignedCompensator_energy_saturation
    (q : BombieriTest) (hmass : ordinaryMass q ≠ 0) :
    (bombieriFunctional (bombieriQuadraticTest q)).re +
        Complex.normSq (ordinaryMass q) *
          (bombieriFunctional
            (bombieriQuadraticTest (sourceAlignedCompensator q))).re =
      2 * (ordinaryMass q *
        bombieriTwoBlockGlobalCrossSymbol q
          (sourceAlignedCompensator q)).re := by
  have H := compensatedSource_energy_rankOne q (sourceAlignedCompensator q)
  rw [compensatedSource_sourceAlignedCompensator_eq_zero q hmass] at H
  have htest : bombieriQuadraticTest (0 : BombieriTest) = 0 := by
    ext x
    simp [bombieriQuadraticTest_apply, autocorrelation]
  rw [htest] at H
  simp only [map_zero, Complex.zero_re] at H
  linarith

end


end ArithmeticHodge.Analysis.MultiplicativeWeilCoherentSourceAlignedCompensatorStructural

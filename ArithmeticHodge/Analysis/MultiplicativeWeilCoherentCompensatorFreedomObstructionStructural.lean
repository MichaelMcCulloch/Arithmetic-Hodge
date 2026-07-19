import ArithmeticHodge.Analysis.MultiplicativeWeilCoherentCompensatedEnergyCovarianceStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilCoherentCutoffCompanionObstructionStructural

set_option autoImplicit false

open Complex MeasureTheory Real Set
open scoped ContDiff Distributions

namespace ArithmeticHodge.Analysis.MultiplicativeWeilCoherentCompensatorFreedomObstructionStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilCoherentCompensatedEnergyCovarianceStructural
open MultiplicativeWeilCoherentCutoffCompanionObstructionStructural

/-!
# Freedom in the coherent compensating bump

The compensated companion construction permits any same-window unit-mass
Bombieri bump.  Adding the derivative of an existing companion preserves
both support and mass, but rescales the compensated source and its primitive.
Consequently no companion-energy budget can hold uniformly over every bump
allowed by the bare existence theorem.  A positivity proof using companions
must choose a canonical bump or impose additional quantitative structure.
-/

/-- The derivative of a Bombieri test, bundled again as a Bombieri test. -/
def bombieriDerivative (U : BombieriTest) : BombieriTest :=
  TestFunction.mk
    (deriv U)
    ((contDiff_infty_iff_deriv.mp U.contDiff).2)
    U.hasCompactSupport.deriv
    (tsupport_deriv_subset.trans U.tsupport_subset)

@[simp]
theorem bombieriDerivative_apply (U : BombieriTest) (x : ℝ) :
    bombieriDerivative U x = deriv U x :=
  rfl

theorem bombieriDerivative_tsupport_subset (U : BombieriTest) :
    tsupport (bombieriDerivative U) ⊆ tsupport U :=
  tsupport_deriv_subset

theorem ordinaryMass_add (f g : BombieriTest) :
    ordinaryMass (f + g) = ordinaryMass f + ordinaryMass g := by
  unfold ordinaryMass
  change (∫ x : ℝ in Set.Ioi 0, f x + g x) = _
  have hf : Integrable (f : ℝ → ℂ)
      (volume.restrict (Set.Ioi 0)) :=
    f.contDiff.continuous.integrable_of_hasCompactSupport
      f.hasCompactSupport |>.integrableOn
  have hg : Integrable (g : ℝ → ℂ)
      (volume.restrict (Set.Ioi 0)) :=
    g.contDiff.continuous.integrable_of_hasCompactSupport
      g.hasCompactSupport |>.integrableOn
  exact integral_add hf hg

theorem ordinaryMass_smul (c : ℂ) (f : BombieriTest) :
    ordinaryMass (c • f) = c * ordinaryMass f := by
  unfold ordinaryMass
  change (∫ x : ℝ in Set.Ioi 0, c * f x) =
    c * ∫ x : ℝ in Set.Ioi 0, f x
  exact integral_const_mul c (f : ℝ → ℂ)

theorem ordinaryMass_bombieriDerivative_eq_zero (U : BombieriTest) :
    ordinaryMass (bombieriDerivative U) = 0 := by
  exact integral_Ioi_deriv_bombieriTest_eq_zero U

/-- Perturb a compensating bump by the derivative of an existing companion. -/
def perturbedCompensator
    (rho U : BombieriTest) (t : ℂ) : BombieriTest :=
  rho + t • bombieriDerivative U

/-- The perturbation preserves ordinary mass. -/
theorem perturbedCompensator_mass
    (rho U : BombieriTest) (t : ℂ) :
    ordinaryMass (perturbedCompensator rho U t) = ordinaryMass rho := by
  rw [perturbedCompensator, ordinaryMass_add, ordinaryMass_smul,
    ordinaryMass_bombieriDerivative_eq_zero, mul_zero, add_zero]

/-- The perturbation preserves any common closed support window. -/
theorem perturbedCompensator_tsupport_subset
    (rho U : BombieriTest) (t : ℂ) {a b : ℝ}
    (hrho : tsupport rho ⊆ Set.Icc a b)
    (hU : tsupport U ⊆ Set.Icc a b) :
    tsupport (perturbedCompensator rho U t) ⊆ Set.Icc a b := by
  exact (tsupport_add (rho : ℝ → ℂ)
    (t • bombieriDerivative U : BombieriTest)).trans
      (Set.union_subset hrho
        ((tsupport_smul_subset_right (fun _ : ℝ ↦ t)
          (bombieriDerivative U : ℝ → ℂ)).trans
            ((bombieriDerivative_tsupport_subset U).trans hU)))

/-- If `U' = q - mass(q) rho`, perturbing `rho` by `t U'` rescales the
compensated source by `1 - mass(q) t`. -/
theorem compensatedSource_perturbedCompensator
    (q rho U : BombieriTest) (t : ℂ)
    (hU : ∀ x : ℝ, deriv U x = compensatedSource q rho x) :
    compensatedSource q (perturbedCompensator rho U t) =
      (1 - ordinaryMass q * t) • bombieriDerivative U := by
  ext x
  have hx : q x = deriv U x + ordinaryMass q * rho x := by
    have hx' := hU x
    change deriv U x = q x - ordinaryMass q * rho x at hx'
    rw [eq_sub_iff_add_eq] at hx'
    exact hx'.symm
  simp only [compensatedSource, perturbedCompensator,
    TestFunction.coe_sub, Pi.sub_apply, TestFunction.coe_add, Pi.add_apply,
    TestFunction.coe_smul, Pi.smul_apply, smul_eq_mul,
    bombieriDerivative_apply]
  rw [hx]
  ring

/-- The companion corresponding to the perturbed bump. -/
def perturbedCompanion
    (q U : BombieriTest) (t : ℂ) : BombieriTest :=
  (1 - ordinaryMass q * t) • U

theorem perturbedCompanion_deriv
    (q rho U : BombieriTest) (t : ℂ)
    (hU : ∀ x : ℝ, deriv U x = compensatedSource q rho x) (x : ℝ) :
    deriv (perturbedCompanion q U t : ℝ → ℂ) x =
      compensatedSource q (perturbedCompensator rho U t) x := by
  rw [compensatedSource_perturbedCompensator q rho U t hU]
  change deriv (fun y : ℝ ↦ (1 - ordinaryMass q * t) * U y) x =
    (1 - ordinaryMass q * t) * deriv U x
  exact deriv_const_mul _
    ((U.contDiff.differentiable (by norm_num)).differentiableAt)

/-- Real Bombieri energy of a companion. -/
def companionEnergy (U : BombieriTest) : ℝ :=
  (bombieriFunctional (bombieriQuadraticTest U)).re

theorem perturbedCompanion_energy
    (q U : BombieriTest) (t : ℂ) :
    companionEnergy (perturbedCompanion q U t) =
      Complex.normSq (1 - ordinaryMass q * t) * companionEnergy U := by
  rw [companionEnergy, perturbedCompanion,
    bombieriFunctional_quadratic_smul]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  rfl

/-- If the source mass is nonzero and one companion has positive energy,
equally supported mass-preserving compensator perturbations give companions
of arbitrarily large energy. -/
theorem exists_perturbedCompanion_energy_gt
    (q U : BombieriTest)
    (hmass : ordinaryMass q ≠ 0)
    (henergy : 0 < companionEnergy U) (B : ℝ) :
    ∃ t : ℂ, B < companionEnergy (perturbedCompanion q U t) := by
  obtain ⟨n : ℕ, hn⟩ := exists_nat_gt (max 1 (B / companionEnergy U))
  have hnOne : (1 : ℝ) < (n : ℝ) :=
    lt_of_le_of_lt (le_max_left _ _) hn
  have hnRatio : B / companionEnergy U < (n : ℝ) :=
    lt_of_le_of_lt (le_max_right _ _) hn
  have hlinear : B < (n : ℝ) * companionEnergy U := by
    exact (div_lt_iff₀ henergy).mp hnRatio
  have hquadratic :
      B < (n : ℝ) ^ 2 * companionEnergy U := by
    have hnNonneg : 0 ≤ (n : ℝ) := by positivity
    have hnn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
      nlinarith
    have hmono : (n : ℝ) * companionEnergy U ≤
        (n : ℝ) ^ 2 * companionEnergy U := by
      exact mul_le_mul_of_nonneg_right hnn henergy.le
    exact hlinear.trans_le hmono
  let t : ℂ := (((1 - (n : ℝ) : ℝ) : ℂ) / ordinaryMass q)
  refine ⟨t, ?_⟩
  rw [perturbedCompanion_energy]
  have hcoefficient : 1 - ordinaryMass q * t = ((n : ℝ) : ℂ) := by
    dsimp only [t]
    field_simp [hmass]
    push_cast
    ring
  rw [hcoefficient, Complex.normSq_ofReal]
  simpa only [pow_two] using hquadratic

end

end ArithmeticHodge.Analysis.MultiplicativeWeilCoherentCompensatorFreedomObstructionStructural

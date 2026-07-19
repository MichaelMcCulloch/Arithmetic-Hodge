import ArithmeticHodge.Analysis.MultiplicativeWeilCoherentCompensatedCutoffCompanionStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilLogLatticeCovarianceStructural

set_option autoImplicit false

open Complex MeasureTheory Real Set
open scoped ContDiff Distributions

namespace ArithmeticHodge.Analysis.MultiplicativeWeilCoherentCompensatedEnergyCovarianceStructural

noncomputable section

open MultiplicativeWeil

/-!
# Dilation covariance of compensated cutoff companions

These are exact normalization, covariance, and quadratic-expansion
identities for the compensated derivative source and its primitive.  They do
not assert a collective companion-energy estimate or a consequence for the
Riemann hypothesis.
-/

/-- The ordinary `dx` mass used by the compact-primitive compatibility
condition. -/
def ordinaryMass (g : BombieriTest) : ℂ :=
  ∫ x : ℝ in Set.Ioi 0, g x

/-- A derivative source carries one extra factor of the dilation scale. -/
def derivativeSourceDilation
    (lambda : ℝ) (hlambda : 0 < lambda) (q : BombieriTest) : BombieriTest :=
  (lambda : ℂ) • normalizedDilation lambda hlambda q

/-- The `L¹(dx)`-normalized dilation of a unit-mass compensating bump.
This is `sqrt(lambda)` times the `L²(dx)`-normalized Bombieri dilation. -/
def unitMassBumpDilation
    (lambda : ℝ) (hlambda : 0 < lambda) (rho : BombieriTest) : BombieriTest :=
  ((Real.sqrt lambda : ℝ) : ℂ) • normalizedDilation lambda hlambda rho

/-- Rank-one removal of the ordinary-mass direction selected by `rho`.
It is a projection when `ordinaryMass rho = 1`. -/
def compensatedSource (q rho : BombieriTest) : BombieriTest :=
  q - ordinaryMass q • rho

/-- Ordinary mass has weight `lambda⁻¹ᵗ²` under the `L²(dx)`-normalized
Bombieri dilation. -/
theorem ordinaryMass_normalizedDilation
    (lambda : ℝ) (hlambda : 0 < lambda) (g : BombieriTest) :
    ordinaryMass (normalizedDilation lambda hlambda g) =
      ((Real.sqrt lambda : ℝ) : ℂ) *
        (((lambda⁻¹ : ℝ) : ℂ) * ordinaryMass g) := by
  unfold ordinaryMass
  simp_rw [normalizedDilation_apply]
  have hscale := integral_comp_mul_left_Ioi (g : ℝ → ℂ) 0 hlambda
  rw [mul_zero] at hscale
  calc
    (∫ x : ℝ in Set.Ioi 0,
        ((Real.sqrt lambda : ℝ) : ℂ) * g (lambda * x)) =
        ((Real.sqrt lambda : ℝ) : ℂ) *
          ∫ x : ℝ in Set.Ioi 0, g (lambda * x) := by
      exact MeasureTheory.integral_const_mul
        (μ := volume.restrict (Set.Ioi 0))
          ((Real.sqrt lambda : ℝ) : ℂ) (fun x : ℝ ↦ g (lambda * x))
    _ = ((Real.sqrt lambda : ℝ) : ℂ) *
        (((lambda⁻¹ : ℝ) : ℂ) *
          ∫ x : ℝ in Set.Ioi 0, g x) := by
      rw [hscale]
      rfl

/-- The ordinary mass of a derivative-source dilation has weight
`lambda¹ᵗ²`. -/
theorem ordinaryMass_derivativeSourceDilation
    (lambda : ℝ) (hlambda : 0 < lambda) (q : BombieriTest) :
    ordinaryMass (derivativeSourceDilation lambda hlambda q) =
      ((Real.sqrt lambda : ℝ) : ℂ) * ordinaryMass q := by
  change ordinaryMass
      ((lambda : ℂ) • normalizedDilation lambda hlambda q) = _
  unfold ordinaryMass
  change (∫ x : ℝ in Set.Ioi 0,
      (lambda : ℂ) * normalizedDilation lambda hlambda q x) = _
  calc
    (∫ x : ℝ in Set.Ioi 0,
        (lambda : ℂ) * normalizedDilation lambda hlambda q x) =
        (lambda : ℂ) * ordinaryMass
          (normalizedDilation lambda hlambda q) := by
      exact MeasureTheory.integral_const_mul
        (μ := volume.restrict (Set.Ioi 0)) (lambda : ℂ)
          (normalizedDilation lambda hlambda q : ℝ → ℂ)
    _ = ((Real.sqrt lambda : ℝ) : ℂ) * ordinaryMass q := by
      rw [ordinaryMass_normalizedDilation]
      push_cast
      field_simp [hlambda.ne']

/-- Multiplying normalized dilation by `sqrt(lambda)` preserves ordinary
mass exactly. -/
theorem ordinaryMass_unitMassBumpDilation
    (lambda : ℝ) (hlambda : 0 < lambda) (rho : BombieriTest) :
    ordinaryMass (unitMassBumpDilation lambda hlambda rho) =
      ordinaryMass rho := by
  change ordinaryMass (((Real.sqrt lambda : ℝ) : ℂ) •
    normalizedDilation lambda hlambda rho) = ordinaryMass rho
  unfold ordinaryMass
  change (∫ x : ℝ in Set.Ioi 0,
      ((Real.sqrt lambda : ℝ) : ℂ) *
        normalizedDilation lambda hlambda rho x) = _
  calc
    (∫ x : ℝ in Set.Ioi 0,
        ((Real.sqrt lambda : ℝ) : ℂ) *
          normalizedDilation lambda hlambda rho x) =
        ((Real.sqrt lambda : ℝ) : ℂ) * ordinaryMass
          (normalizedDilation lambda hlambda rho) := by
      exact MeasureTheory.integral_const_mul
        (μ := volume.restrict (Set.Ioi 0))
          ((Real.sqrt lambda : ℝ) : ℂ)
            (normalizedDilation lambda hlambda rho : ℝ → ℂ)
    _ = ordinaryMass rho := by
      rw [ordinaryMass_normalizedDilation]
      have hsqrt :
          (((Real.sqrt lambda : ℝ) : ℂ) ^ 2) = (lambda : ℂ) := by
        norm_cast
        exact Real.sq_sqrt hlambda.le
      push_cast
      rw [← mul_assoc, ← pow_two]
      rw [hsqrt]
      field_simp [hlambda.ne']

/-- The rank-one correction commutes exactly with derivative-source
dilation when the compensating bump uses the mass-preserving normalization. -/
theorem compensatedSource_dilation_covariant
    (lambda : ℝ) (hlambda : 0 < lambda) (q rho : BombieriTest) :
    compensatedSource (derivativeSourceDilation lambda hlambda q)
        (unitMassBumpDilation lambda hlambda rho) =
      derivativeSourceDilation lambda hlambda (compensatedSource q rho) := by
  ext x
  rw [compensatedSource, compensatedSource,
    ordinaryMass_derivativeSourceDilation]
  simp only [derivativeSourceDilation, unitMassBumpDilation,
    TestFunction.coe_sub, Pi.sub_apply, TestFunction.coe_smul, Pi.smul_apply,
    smul_eq_mul, normalizedDilation_apply]
  have hsqrt :
      (((Real.sqrt lambda : ℝ) : ℂ) ^ 2) = (lambda : ℂ) := by
    norm_cast
    exact Real.sq_sqrt hlambda.le
  have hcube :
      (((Real.sqrt lambda : ℝ) : ℂ) ^ 3) =
        (lambda : ℂ) * ((Real.sqrt lambda : ℝ) : ℂ) := by
    calc
      (((Real.sqrt lambda : ℝ) : ℂ) ^ 3) =
          (((Real.sqrt lambda : ℝ) : ℂ) ^ 2) *
            ((Real.sqrt lambda : ℝ) : ℂ) := by ring
      _ = (lambda : ℂ) * ((Real.sqrt lambda : ℝ) : ℂ) := by
        rw [hsqrt]
  ring_nf
  rw [hcube]

/-- Normalized dilation differentiates with the derivative-source factor
`lambda`. -/
theorem deriv_normalizedDilation
    (lambda : ℝ) (hlambda : 0 < lambda) (U : BombieriTest) (x : ℝ) :
    deriv (normalizedDilation lambda hlambda U : ℝ → ℂ) x =
      ((Real.sqrt lambda : ℝ) : ℂ) *
        (lambda : ℝ) • deriv U (lambda * x) := by
  change deriv (fun y : ℝ ↦
    ((Real.sqrt lambda : ℝ) : ℂ) * U (lambda * y)) x = _
  have hcomp : ContDiff ℝ ∞ (fun y : ℝ ↦ U (lambda * y)) :=
    U.contDiff.comp (by fun_prop)
  rw [deriv_const_mul _
    ((hcomp.differentiable (by norm_num)).differentiableAt)]
  have hd : deriv (fun y : ℝ ↦ U (lambda * y)) x =
      (lambda : ℝ) • deriv U (lambda * x) := by
    simpa only using deriv_comp_mul_left lambda (U : ℝ → ℂ) x
  rw [hd]

/-- A normalized dilation of a primitive is a primitive of the covariantly
scaled compensated source. -/
theorem scaled_companion_deriv
    (lambda : ℝ) (hlambda : 0 < lambda) (q rho U : BombieriTest)
    (hU : ∀ x : ℝ, deriv U x = compensatedSource q rho x) (x : ℝ) :
    deriv (normalizedDilation lambda hlambda U : ℝ → ℂ) x =
      compensatedSource (derivativeSourceDilation lambda hlambda q)
        (unitMassBumpDilation lambda hlambda rho) x := by
  rw [compensatedSource_dilation_covariant]
  rw [deriv_normalizedDilation, hU]
  simp only [derivativeSourceDilation, TestFunction.coe_smul, Pi.smul_apply,
    smul_eq_mul, normalizedDilation_apply, Complex.real_smul]
  ring

/-- The Bombieri quadratic value of the primitive companion is invariant
under the scale-covariant construction. -/
theorem scaled_companionEnergy_invariant
    (lambda : ℝ) (hlambda : 0 < lambda) (U : BombieriTest) :
    bombieriFunctional
        (bombieriQuadraticTest (normalizedDilation lambda hlambda U)) =
      bombieriFunctional (bombieriQuadraticTest U) :=
  bombieriFunctional_quadratic_normalizedDilation lambda hlambda U

/-- The Bombieri quadratic value of the derivative source itself has
homogeneity `lambda²`. -/
theorem derivativeSourceEnergy_scales_sq
    (lambda : ℝ) (hlambda : 0 < lambda) (q : BombieriTest) :
    bombieriFunctional
        (bombieriQuadraticTest
          (derivativeSourceDilation lambda hlambda q)) =
      (lambda ^ 2 : ℝ) *
        bombieriFunctional (bombieriQuadraticTest q) := by
  rw [derivativeSourceDilation,
    bombieriFunctional_quadratic_smul_normalizedDilation]
  congr 1
  norm_cast
  simp only [Complex.normSq_ofReal]
  ring

/-- Exact rank-one expansion of the compensated source's real Bombieri
quadratic value. -/
theorem compensatedSource_energy_rankOne
    (q rho : BombieriTest) :
    (bombieriFunctional
      (bombieriQuadraticTest (compensatedSource q rho))).re =
      (bombieriFunctional (bombieriQuadraticTest q)).re +
        Complex.normSq (ordinaryMass q) *
          (bombieriFunctional (bombieriQuadraticTest rho)).re -
        2 * (ordinaryMass q *
          bombieriTwoBlockGlobalCrossSymbol q rho).re := by
  have hsource : compensatedSource q rho =
      q + (-ordinaryMass q) • rho := by
    ext x
    change q x - ordinaryMass q * rho x =
      q x + (-ordinaryMass q) * rho x
    ring
  rw [hsource, bombieriFunctional_twoBlock_re]
  rw [Complex.normSq_neg]
  simp only [neg_mul, Complex.neg_re]
  ring

end

end ArithmeticHodge.Analysis.MultiplicativeWeilCoherentCompensatedEnergyCovarianceStructural

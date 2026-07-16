import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseBoundaryContinuousCleanPolarizationStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseBoundaryContinuousProfileLinearStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseEndpointTailMixedCauchyStructural

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseBoundaryContinuousTailMixedCauchyStructural

noncomputable section

open ArithmeticHodge.Analysis
open YoshidaCoercivityNumerics
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointScaledCorrelation
open YoshidaEvenHomogeneousCoercivity
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointChannelRadius
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoEndpointParityPencil
open YoshidaFactorTwoPhaseBoundaryContinuousCleanPolarizationStructural
open YoshidaFactorTwoPhaseBoundaryContinuousProfileLinearStructural
open YoshidaFactorTwoPhaseBoundaryContinuousTailStructural
open YoshidaFactorTwoPhaseCleanPolarizationCritical
open YoshidaFactorTwoPhaseEndpointAdaptedTail
open YoshidaFactorTwoPhaseEndpointTailMixedCauchyStructural
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoPhaseRadiusClosure
open YoshidaFactorTwoPhaseTailCoercivity
open YoshidaPointwiseParityCore
open YoshidaWeightedTailBounds

/-!
# Structural Cauchy inequality on the boundary-continuous tail space

The standard cutoff-`199` even tail need not vanish at the endpoints.  Its
boundary-continuous representative nevertheless has a nonnegative phase form
at every point of the closed phase disk.  Applying that theorem to every real
two-dimensional pencil and using exact real bilinearity gives the sharp
Cauchy--Schwarz inequality for the complete mixed block.
-/

/-- The clipped critical pairing is homogeneous in two real scalar
directions. -/
private theorem yoshidaClippedLocalCriticalForm_smul_real_smul_real
    (r s : YoshidaClippedPeriodicCore yoshidaA) (c d : ℝ) :
    yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
        (((c : ℂ) • r : YoshidaClippedPeriodicCore yoshidaA) :
          YoshidaClippedSmooth yoshidaA)
        (((d : ℂ) • s : YoshidaClippedPeriodicCore yoshidaA) :
          YoshidaClippedSmooth yoshidaA) =
      ((c * d : ℝ) : ℂ) *
        yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
          (r : YoshidaClippedSmooth yoshidaA)
          (s : YoshidaClippedSmooth yoshidaA) := by
  calc
    yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
        (((c : ℂ) • r : YoshidaClippedPeriodicCore yoshidaA) :
          YoshidaClippedSmooth yoshidaA)
        (((d : ℂ) • s : YoshidaClippedPeriodicCore yoshidaA) :
          YoshidaClippedSmooth yoshidaA) =
        star (c : ℂ) *
          yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
            (r : YoshidaClippedSmooth yoshidaA)
            (((d : ℂ) • s : YoshidaClippedPeriodicCore yoshidaA) :
              YoshidaClippedSmooth yoshidaA) := by
          simpa only [Submodule.coe_smul, smul_eq_mul] using
            (LinearMap.map_smulₛₗ₂
              (yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos)
              (c : ℂ) (r : YoshidaClippedSmooth yoshidaA)
              ((((d : ℂ) • s : YoshidaClippedPeriodicCore yoshidaA) :
                YoshidaClippedSmooth yoshidaA)))
    _ = star (c : ℂ) * ((d : ℂ) *
          yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
            (r : YoshidaClippedSmooth yoshidaA)
            (s : YoshidaClippedSmooth yoshidaA)) := by
          change star (c : ℂ) *
            yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
              (r : YoshidaClippedSmooth yoshidaA)
              ((d : ℂ) • (s : YoshidaClippedSmooth yoshidaA)) = _
          rw [map_smul]
          simp only [smul_eq_mul]
    _ = ((c * d : ℝ) : ℂ) *
          yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
            (r : YoshidaClippedSmooth yoshidaA)
            (s : YoshidaClippedSmooth yoshidaA) := by
          rw [Complex.star_def, Complex.conj_ofReal]
          push_cast
          ring

/-- Exact two-sided real homogeneity of the clean pairing on
boundary-continuous even representatives. -/
theorem factorTwoCenteredCleanPolarization_boundaryContinuous_smul_smul
    (f g : yoshidaPointwiseEvenPeriodicCoreSubmodule yoshidaA)
    (hfReal : ∀ x : ℝ,
      ((((f.1 : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) x).im = 0))
    (hgReal : ∀ x : ℝ,
      ((((g.1 : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) x).im = 0))
    (c d : ℝ) :
    factorTwoCenteredCleanPolarization
        (c • boundaryContinuousEvenProfile f)
        (d • boundaryContinuousEvenProfile g) =
      c * d * factorTwoCenteredCleanPolarization
        (boundaryContinuousEvenProfile f)
        (boundaryContinuousEvenProfile g) := by
  let fc : yoshidaPointwiseEvenPeriodicCoreSubmodule yoshidaA :=
    (c : ℂ) • f
  let gd : yoshidaPointwiseEvenPeriodicCoreSubmodule yoshidaA :=
    (d : ℂ) • g
  have hfcReal : ∀ x : ℝ,
      ((fc.1 : YoshidaClippedSmooth yoshidaA) x).im = 0 := by
    intro x
    dsimp only [fc]
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      add_zero]
    rw [hfReal x]
    ring
  have hgdReal : ∀ x : ℝ,
      ((gd.1 : YoshidaClippedSmooth yoshidaA) x).im = 0 := by
    intro x
    dsimp only [gd]
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      add_zero]
    rw [hgReal x]
    ring
  have hfcProfile :
      boundaryContinuousEvenProfile fc =
        c • boundaryContinuousEvenProfile f := by
    simpa only [fc] using boundaryContinuousEvenProfile_smul_real c f
  have hgdProfile :
      boundaryContinuousEvenProfile gd =
        d • boundaryContinuousEvenProfile g := by
    simpa only [gd] using boundaryContinuousEvenProfile_smul_real d g
  have hbase :=
    factorTwoCenteredCleanPolarization_boundaryContinuous_eq_clippedCriticalForm_re_div
      f g hfReal hgReal
  have hscaled :=
    factorTwoCenteredCleanPolarization_boundaryContinuous_eq_clippedCriticalForm_re_div
      fc gd hfcReal hgdReal
  rw [hfcProfile, hgdProfile] at hscaled
  have hform := yoshidaClippedLocalCriticalForm_smul_real_smul_real
    (f.1 : YoshidaClippedPeriodicCore yoshidaA)
    (g.1 : YoshidaClippedPeriodicCore yoshidaA) c d
  change yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
      (fc.1 : YoshidaClippedSmooth yoshidaA)
      (gd.1 : YoshidaClippedSmooth yoshidaA) = _ at hform
  calc
    factorTwoCenteredCleanPolarization
        (c • boundaryContinuousEvenProfile f)
        (d • boundaryContinuousEvenProfile g) =
      (yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
        (fc.1 : YoshidaClippedSmooth yoshidaA)
        (gd.1 : YoshidaClippedSmooth yoshidaA)).re / yoshidaA := hscaled
    _ = ((((c * d : ℝ) : ℂ) *
          yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
            (f.1 : YoshidaClippedSmooth yoshidaA)
            (g.1 : YoshidaClippedSmooth yoshidaA)).re) / yoshidaA := by
          rw [hform]
    _ = c * d *
        ((yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
          (f.1 : YoshidaClippedSmooth yoshidaA)
          (g.1 : YoshidaClippedSmooth yoshidaA)).re / yoshidaA) := by
          simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
            zero_mul, sub_zero]
          ring
    _ = c * d * factorTwoCenteredCleanPolarization
        (boundaryContinuousEvenProfile f)
        (boundaryContinuousEvenProfile g) := by
          rw [hbase]

/-- Exact two-sided real homogeneity of the clean pairing for real profiles
with zero endpoint traces. -/
private theorem factorTwoCenteredCleanPolarization_zeroTrace_smul_smul
    (r s : YoshidaClippedPeriodicCore yoshidaA)
    (hrReal : ∀ x : ℝ,
      ((r : YoshidaClippedSmooth yoshidaA) x).im = 0)
    (hsReal : ∀ x : ℝ,
      ((s : YoshidaClippedSmooth yoshidaA) x).im = 0)
    (hrNeg : (r : YoshidaClippedSmooth yoshidaA) (-yoshidaA) = 0)
    (hrPos : (r : YoshidaClippedSmooth yoshidaA) yoshidaA = 0)
    (hsNeg : (s : YoshidaClippedSmooth yoshidaA) (-yoshidaA) = 0)
    (hsPos : (s : YoshidaClippedSmooth yoshidaA) yoshidaA = 0)
    (c d : ℝ) :
    let u := centeredRescale yoshidaA (fun x ↦
      ((r : YoshidaClippedSmooth yoshidaA) x).re)
    let v := centeredRescale yoshidaA (fun x ↦
      ((s : YoshidaClippedSmooth yoshidaA) x).re)
    factorTwoCenteredCleanPolarization (c • u) (d • v) =
      c * d * factorTwoCenteredCleanPolarization u v := by
  dsimp only
  let rc : YoshidaClippedPeriodicCore yoshidaA := (c : ℂ) • r
  let sd : YoshidaClippedPeriodicCore yoshidaA := (d : ℂ) • s
  let u : ℝ → ℝ := centeredRescale yoshidaA (fun x ↦
    ((r : YoshidaClippedSmooth yoshidaA) x).re)
  let v : ℝ → ℝ := centeredRescale yoshidaA (fun x ↦
    ((s : YoshidaClippedSmooth yoshidaA) x).re)
  have hrcReal : ∀ x : ℝ,
      ((rc : YoshidaClippedSmooth yoshidaA) x).im = 0 := by
    intro x
    simp [rc, hrReal x]
  have hsdReal : ∀ x : ℝ,
      ((sd : YoshidaClippedSmooth yoshidaA) x).im = 0 := by
    intro x
    simp [sd, hsReal x]
  have hrcNeg : (rc : YoshidaClippedSmooth yoshidaA) (-yoshidaA) = 0 := by
    simp [rc, hrNeg]
  have hrcPos : (rc : YoshidaClippedSmooth yoshidaA) yoshidaA = 0 := by
    simp [rc, hrPos]
  have hsdNeg : (sd : YoshidaClippedSmooth yoshidaA) (-yoshidaA) = 0 := by
    simp [sd, hsNeg]
  have hsdPos : (sd : YoshidaClippedSmooth yoshidaA) yoshidaA = 0 := by
    simp [sd, hsPos]
  have hrcProfile :
      centeredRescale yoshidaA (fun x ↦
        ((rc : YoshidaClippedSmooth yoshidaA) x).re) = c • u := by
    funext x
    simp [rc, u, centeredRescale]
  have hsdProfile :
      centeredRescale yoshidaA (fun x ↦
        ((sd : YoshidaClippedSmooth yoshidaA) x).re) = d • v := by
    funext x
    simp [sd, v, centeredRescale]
  have hbase :=
    factorTwoCenteredCleanPolarization_eq_clippedCriticalForm_re_div
      r s hrReal hsReal hrNeg hrPos hsNeg hsPos
  have hscaled :=
    factorTwoCenteredCleanPolarization_eq_clippedCriticalForm_re_div
      rc sd hrcReal hsdReal hrcNeg hrcPos hsdNeg hsdPos
  rw [hrcProfile, hsdProfile] at hscaled
  have hform := yoshidaClippedLocalCriticalForm_smul_real_smul_real
    r s c d
  change yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
      (rc : YoshidaClippedSmooth yoshidaA)
      (sd : YoshidaClippedSmooth yoshidaA) = _ at hform
  calc
    factorTwoCenteredCleanPolarization (c • u) (d • v) =
        (yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
          (rc : YoshidaClippedSmooth yoshidaA)
          (sd : YoshidaClippedSmooth yoshidaA)).re / yoshidaA := hscaled
    _ = ((((c * d : ℝ) : ℂ) *
          yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
            (r : YoshidaClippedSmooth yoshidaA)
            (s : YoshidaClippedSmooth yoshidaA)).re) / yoshidaA := by
          rw [hform]
    _ = c * d *
        ((yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
          (r : YoshidaClippedSmooth yoshidaA)
          (s : YoshidaClippedSmooth yoshidaA)).re / yoshidaA) := by
          simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
            zero_mul, sub_zero]
          ring
    _ = c * d * factorTwoCenteredCleanPolarization u v := by
          rw [hbase]

/-! ## Additivity of the algebraic mixed form -/

/-- Additivity in the first boundary-continuous even entry of the clean
pairing. -/
theorem factorTwoCenteredCleanPolarization_boundaryContinuous_add_left
    (f₁ f₂ g : yoshidaPointwiseEvenPeriodicCoreSubmodule yoshidaA)
    (hfReal₁ : ∀ x : ℝ,
      ((f₁.1 : YoshidaClippedSmooth yoshidaA) x).im = 0)
    (hfReal₂ : ∀ x : ℝ,
      ((f₂.1 : YoshidaClippedSmooth yoshidaA) x).im = 0)
    (hgReal : ∀ x : ℝ,
      ((g.1 : YoshidaClippedSmooth yoshidaA) x).im = 0) :
    factorTwoCenteredCleanPolarization
        (boundaryContinuousEvenProfile f₁ +
          boundaryContinuousEvenProfile f₂)
        (boundaryContinuousEvenProfile g) =
      factorTwoCenteredCleanPolarization
          (boundaryContinuousEvenProfile f₁)
          (boundaryContinuousEvenProfile g) +
        factorTwoCenteredCleanPolarization
          (boundaryContinuousEvenProfile f₂)
          (boundaryContinuousEvenProfile g) := by
  have hsumReal : ∀ x : ℝ,
      (((f₁ + f₂).1 : YoshidaClippedSmooth yoshidaA) x).im = 0 := by
    intro x
    simp only [Submodule.coe_add, Pi.add_apply, Complex.add_im,
      hfReal₁ x, hfReal₂ x, add_zero]
  have hsum :=
    factorTwoCenteredCleanPolarization_boundaryContinuous_eq_clippedCriticalForm_re_div
      (f₁ + f₂) g hsumReal hgReal
  rw [boundaryContinuousEvenProfile_add] at hsum
  have h₁ :=
    factorTwoCenteredCleanPolarization_boundaryContinuous_eq_clippedCriticalForm_re_div
      f₁ g hfReal₁ hgReal
  have h₂ :=
    factorTwoCenteredCleanPolarization_boundaryContinuous_eq_clippedCriticalForm_re_div
      f₂ g hfReal₂ hgReal
  calc
    factorTwoCenteredCleanPolarization
        (boundaryContinuousEvenProfile f₁ +
          boundaryContinuousEvenProfile f₂)
        (boundaryContinuousEvenProfile g) =
      (yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
        ((f₁ + f₂).1 : YoshidaClippedSmooth yoshidaA)
        (g.1 : YoshidaClippedSmooth yoshidaA)).re / yoshidaA := hsum
    _ = ((yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
            (f₁.1 : YoshidaClippedSmooth yoshidaA)
            (g.1 : YoshidaClippedSmooth yoshidaA)).re / yoshidaA) +
          ((yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
            (f₂.1 : YoshidaClippedSmooth yoshidaA)
            (g.1 : YoshidaClippedSmooth yoshidaA)).re / yoshidaA) := by
          simp only [Submodule.coe_add, map_add, LinearMap.add_apply,
            Complex.add_re]
          ring
    _ = factorTwoCenteredCleanPolarization
          (boundaryContinuousEvenProfile f₁)
          (boundaryContinuousEvenProfile g) +
        factorTwoCenteredCleanPolarization
          (boundaryContinuousEvenProfile f₂)
          (boundaryContinuousEvenProfile g) := by
          rw [h₁, h₂]

/-- Additivity in the second boundary-continuous even entry of the clean
pairing. -/
theorem factorTwoCenteredCleanPolarization_boundaryContinuous_add_right
    (f g₁ g₂ : yoshidaPointwiseEvenPeriodicCoreSubmodule yoshidaA)
    (hfReal : ∀ x : ℝ,
      ((f.1 : YoshidaClippedSmooth yoshidaA) x).im = 0)
    (hgReal₁ : ∀ x : ℝ,
      ((g₁.1 : YoshidaClippedSmooth yoshidaA) x).im = 0)
    (hgReal₂ : ∀ x : ℝ,
      ((g₂.1 : YoshidaClippedSmooth yoshidaA) x).im = 0) :
    factorTwoCenteredCleanPolarization
        (boundaryContinuousEvenProfile f)
        (boundaryContinuousEvenProfile g₁ +
          boundaryContinuousEvenProfile g₂) =
      factorTwoCenteredCleanPolarization
          (boundaryContinuousEvenProfile f)
          (boundaryContinuousEvenProfile g₁) +
        factorTwoCenteredCleanPolarization
          (boundaryContinuousEvenProfile f)
          (boundaryContinuousEvenProfile g₂) := by
  have hsumReal : ∀ x : ℝ,
      (((g₁ + g₂).1 : YoshidaClippedSmooth yoshidaA) x).im = 0 := by
    intro x
    simp only [Submodule.coe_add, Pi.add_apply, Complex.add_im,
      hgReal₁ x, hgReal₂ x, add_zero]
  have hsum :=
    factorTwoCenteredCleanPolarization_boundaryContinuous_eq_clippedCriticalForm_re_div
      f (g₁ + g₂) hfReal hsumReal
  rw [boundaryContinuousEvenProfile_add] at hsum
  have h₁ :=
    factorTwoCenteredCleanPolarization_boundaryContinuous_eq_clippedCriticalForm_re_div
      f g₁ hfReal hgReal₁
  have h₂ :=
    factorTwoCenteredCleanPolarization_boundaryContinuous_eq_clippedCriticalForm_re_div
      f g₂ hfReal hgReal₂
  calc
    factorTwoCenteredCleanPolarization
        (boundaryContinuousEvenProfile f)
        (boundaryContinuousEvenProfile g₁ +
          boundaryContinuousEvenProfile g₂) =
      (yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
        (f.1 : YoshidaClippedSmooth yoshidaA)
        ((g₁ + g₂).1 : YoshidaClippedSmooth yoshidaA)).re /
          yoshidaA := hsum
    _ = ((yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
            (f.1 : YoshidaClippedSmooth yoshidaA)
            (g₁.1 : YoshidaClippedSmooth yoshidaA)).re / yoshidaA) +
          ((yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
            (f.1 : YoshidaClippedSmooth yoshidaA)
            (g₂.1 : YoshidaClippedSmooth yoshidaA)).re / yoshidaA) := by
          simp only [Submodule.coe_add, map_add, Complex.add_re]
          ring
    _ = factorTwoCenteredCleanPolarization
          (boundaryContinuousEvenProfile f)
          (boundaryContinuousEvenProfile g₁) +
        factorTwoCenteredCleanPolarization
          (boundaryContinuousEvenProfile f)
          (boundaryContinuousEvenProfile g₂) := by
          rw [h₁, h₂]

/-- Additivity in the first zero-trace real profile entry of the clean
pairing. -/
private theorem factorTwoCenteredCleanPolarization_zeroTrace_add_left
    (r₁ r₂ s : YoshidaClippedPeriodicCore yoshidaA)
    (hrReal₁ : ∀ x : ℝ,
      ((r₁ : YoshidaClippedSmooth yoshidaA) x).im = 0)
    (hrReal₂ : ∀ x : ℝ,
      ((r₂ : YoshidaClippedSmooth yoshidaA) x).im = 0)
    (hsReal : ∀ x : ℝ,
      ((s : YoshidaClippedSmooth yoshidaA) x).im = 0)
    (hrNeg₁ : (r₁ : YoshidaClippedSmooth yoshidaA) (-yoshidaA) = 0)
    (hrPos₁ : (r₁ : YoshidaClippedSmooth yoshidaA) yoshidaA = 0)
    (hrNeg₂ : (r₂ : YoshidaClippedSmooth yoshidaA) (-yoshidaA) = 0)
    (hrPos₂ : (r₂ : YoshidaClippedSmooth yoshidaA) yoshidaA = 0)
    (hsNeg : (s : YoshidaClippedSmooth yoshidaA) (-yoshidaA) = 0)
    (hsPos : (s : YoshidaClippedSmooth yoshidaA) yoshidaA = 0) :
    let u₁ := centeredRescale yoshidaA (fun x ↦
      ((r₁ : YoshidaClippedSmooth yoshidaA) x).re)
    let u₂ := centeredRescale yoshidaA (fun x ↦
      ((r₂ : YoshidaClippedSmooth yoshidaA) x).re)
    let v := centeredRescale yoshidaA (fun x ↦
      ((s : YoshidaClippedSmooth yoshidaA) x).re)
    factorTwoCenteredCleanPolarization (u₁ + u₂) v =
      factorTwoCenteredCleanPolarization u₁ v +
        factorTwoCenteredCleanPolarization u₂ v := by
  dsimp only
  have hrsReal : ∀ x : ℝ,
      (((r₁ + r₂ : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) x).im = 0 := by
    intro x
    simp only [Submodule.coe_add, Pi.add_apply, Complex.add_im,
      hrReal₁ x, hrReal₂ x, add_zero]
  have hrsNeg :
      ((r₁ + r₂ : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) (-yoshidaA) = 0 := by
    simp only [Submodule.coe_add, Pi.add_apply, hrNeg₁, hrNeg₂, add_zero]
  have hrsPos :
      ((r₁ + r₂ : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) yoshidaA = 0 := by
    simp only [Submodule.coe_add, Pi.add_apply, hrPos₁, hrPos₂, add_zero]
  have hsum :=
    factorTwoCenteredCleanPolarization_eq_clippedCriticalForm_re_div
      (r₁ + r₂) s hrsReal hsReal hrsNeg hrsPos hsNeg hsPos
  have hprofile :
      centeredRescale yoshidaA (fun x ↦
        (((r₁ + r₂ : YoshidaClippedPeriodicCore yoshidaA) :
          YoshidaClippedSmooth yoshidaA) x).re) =
        centeredRescale yoshidaA (fun x ↦
          ((r₁ : YoshidaClippedSmooth yoshidaA) x).re) +
        centeredRescale yoshidaA (fun x ↦
          ((r₂ : YoshidaClippedSmooth yoshidaA) x).re) := by
    funext x
    rfl
  rw [hprofile] at hsum
  have h₁ := factorTwoCenteredCleanPolarization_eq_clippedCriticalForm_re_div
    r₁ s hrReal₁ hsReal hrNeg₁ hrPos₁ hsNeg hsPos
  have h₂ := factorTwoCenteredCleanPolarization_eq_clippedCriticalForm_re_div
    r₂ s hrReal₂ hsReal hrNeg₂ hrPos₂ hsNeg hsPos
  calc
    factorTwoCenteredCleanPolarization
        (centeredRescale yoshidaA (fun x ↦
          ((r₁ : YoshidaClippedSmooth yoshidaA) x).re) +
         centeredRescale yoshidaA (fun x ↦
          ((r₂ : YoshidaClippedSmooth yoshidaA) x).re))
        (centeredRescale yoshidaA (fun x ↦
          ((s : YoshidaClippedSmooth yoshidaA) x).re)) =
      (yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
        ((r₁ + r₂ : YoshidaClippedPeriodicCore yoshidaA) :
          YoshidaClippedSmooth yoshidaA)
        (s : YoshidaClippedSmooth yoshidaA)).re / yoshidaA := hsum
    _ = ((yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
            (r₁ : YoshidaClippedSmooth yoshidaA)
            (s : YoshidaClippedSmooth yoshidaA)).re / yoshidaA) +
          ((yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
            (r₂ : YoshidaClippedSmooth yoshidaA)
            (s : YoshidaClippedSmooth yoshidaA)).re / yoshidaA) := by
          simp only [Submodule.coe_add, map_add, LinearMap.add_apply,
            Complex.add_re]
          ring
    _ = factorTwoCenteredCleanPolarization
          (centeredRescale yoshidaA (fun x ↦
            ((r₁ : YoshidaClippedSmooth yoshidaA) x).re))
          (centeredRescale yoshidaA (fun x ↦
            ((s : YoshidaClippedSmooth yoshidaA) x).re)) +
        factorTwoCenteredCleanPolarization
          (centeredRescale yoshidaA (fun x ↦
            ((r₂ : YoshidaClippedSmooth yoshidaA) x).re))
          (centeredRescale yoshidaA (fun x ↦
            ((s : YoshidaClippedSmooth yoshidaA) x).re)) := by
          rw [h₁, h₂]

/-- Additivity in the second zero-trace real profile entry of the clean
pairing. -/
private theorem factorTwoCenteredCleanPolarization_zeroTrace_add_right
    (r s₁ s₂ : YoshidaClippedPeriodicCore yoshidaA)
    (hrReal : ∀ x : ℝ,
      ((r : YoshidaClippedSmooth yoshidaA) x).im = 0)
    (hsReal₁ : ∀ x : ℝ,
      ((s₁ : YoshidaClippedSmooth yoshidaA) x).im = 0)
    (hsReal₂ : ∀ x : ℝ,
      ((s₂ : YoshidaClippedSmooth yoshidaA) x).im = 0)
    (hrNeg : (r : YoshidaClippedSmooth yoshidaA) (-yoshidaA) = 0)
    (hrPos : (r : YoshidaClippedSmooth yoshidaA) yoshidaA = 0)
    (hsNeg₁ : (s₁ : YoshidaClippedSmooth yoshidaA) (-yoshidaA) = 0)
    (hsPos₁ : (s₁ : YoshidaClippedSmooth yoshidaA) yoshidaA = 0)
    (hsNeg₂ : (s₂ : YoshidaClippedSmooth yoshidaA) (-yoshidaA) = 0)
    (hsPos₂ : (s₂ : YoshidaClippedSmooth yoshidaA) yoshidaA = 0) :
    let u := centeredRescale yoshidaA (fun x ↦
      ((r : YoshidaClippedSmooth yoshidaA) x).re)
    let v₁ := centeredRescale yoshidaA (fun x ↦
      ((s₁ : YoshidaClippedSmooth yoshidaA) x).re)
    let v₂ := centeredRescale yoshidaA (fun x ↦
      ((s₂ : YoshidaClippedSmooth yoshidaA) x).re)
    factorTwoCenteredCleanPolarization u (v₁ + v₂) =
      factorTwoCenteredCleanPolarization u v₁ +
        factorTwoCenteredCleanPolarization u v₂ := by
  dsimp only
  have hssReal : ∀ x : ℝ,
      (((s₁ + s₂ : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) x).im = 0 := by
    intro x
    simp only [Submodule.coe_add, Pi.add_apply, Complex.add_im,
      hsReal₁ x, hsReal₂ x, add_zero]
  have hssNeg :
      ((s₁ + s₂ : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) (-yoshidaA) = 0 := by
    simp only [Submodule.coe_add, Pi.add_apply, hsNeg₁, hsNeg₂, add_zero]
  have hssPos :
      ((s₁ + s₂ : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) yoshidaA = 0 := by
    simp only [Submodule.coe_add, Pi.add_apply, hsPos₁, hsPos₂, add_zero]
  have hsum :=
    factorTwoCenteredCleanPolarization_eq_clippedCriticalForm_re_div
      r (s₁ + s₂) hrReal hssReal hrNeg hrPos hssNeg hssPos
  have hprofile :
      centeredRescale yoshidaA (fun x ↦
        (((s₁ + s₂ : YoshidaClippedPeriodicCore yoshidaA) :
          YoshidaClippedSmooth yoshidaA) x).re) =
        centeredRescale yoshidaA (fun x ↦
          ((s₁ : YoshidaClippedSmooth yoshidaA) x).re) +
        centeredRescale yoshidaA (fun x ↦
          ((s₂ : YoshidaClippedSmooth yoshidaA) x).re) := by
    funext x
    rfl
  rw [hprofile] at hsum
  have h₁ := factorTwoCenteredCleanPolarization_eq_clippedCriticalForm_re_div
    r s₁ hrReal hsReal₁ hrNeg hrPos hsNeg₁ hsPos₁
  have h₂ := factorTwoCenteredCleanPolarization_eq_clippedCriticalForm_re_div
    r s₂ hrReal hsReal₂ hrNeg hrPos hsNeg₂ hsPos₂
  calc
    factorTwoCenteredCleanPolarization
        (centeredRescale yoshidaA (fun x ↦
          ((r : YoshidaClippedSmooth yoshidaA) x).re))
        (centeredRescale yoshidaA (fun x ↦
          ((s₁ : YoshidaClippedSmooth yoshidaA) x).re) +
         centeredRescale yoshidaA (fun x ↦
          ((s₂ : YoshidaClippedSmooth yoshidaA) x).re)) =
      (yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
        (r : YoshidaClippedSmooth yoshidaA)
        ((s₁ + s₂ : YoshidaClippedPeriodicCore yoshidaA) :
          YoshidaClippedSmooth yoshidaA)).re / yoshidaA := hsum
    _ = ((yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
            (r : YoshidaClippedSmooth yoshidaA)
            (s₁ : YoshidaClippedSmooth yoshidaA)).re / yoshidaA) +
          ((yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
            (r : YoshidaClippedSmooth yoshidaA)
            (s₂ : YoshidaClippedSmooth yoshidaA)).re / yoshidaA) := by
          simp only [Submodule.coe_add, map_add, Complex.add_re]
          ring
    _ = factorTwoCenteredCleanPolarization
          (centeredRescale yoshidaA (fun x ↦
            ((r : YoshidaClippedSmooth yoshidaA) x).re))
          (centeredRescale yoshidaA (fun x ↦
            ((s₁ : YoshidaClippedSmooth yoshidaA) x).re)) +
        factorTwoCenteredCleanPolarization
          (centeredRescale yoshidaA (fun x ↦
            ((r : YoshidaClippedSmooth yoshidaA) x).re))
          (centeredRescale yoshidaA (fun x ↦
            ((s₂ : YoshidaClippedSmooth yoshidaA) x).re)) := by
          rw [h₁, h₂]

/-- Symmetry of the complete perturbation polarization. -/
private theorem factorTwoCenteredSymmetricPerturbationBilinear_comm
    (u v : ℝ → ℝ) :
    factorTwoCenteredSymmetricPerturbationBilinear u v =
      factorTwoCenteredSymmetricPerturbationBilinear v u := by
  unfold factorTwoCenteredSymmetricPerturbationBilinear
  simp_rw [factorTwoCenteredCorrelationBilinear_comm u v]

/-- Additivity in the second perturbation-polarization entry. -/
private theorem factorTwoCenteredSymmetricPerturbationBilinear_add_right
    (u v w : ℝ → ℝ)
    (hu : Continuous u) (hv : Continuous v) (hw : Continuous w) :
    factorTwoCenteredSymmetricPerturbationBilinear u (v + w) =
      factorTwoCenteredSymmetricPerturbationBilinear u v +
        factorTwoCenteredSymmetricPerturbationBilinear u w := by
  rw [factorTwoCenteredSymmetricPerturbationBilinear_comm u (v + w),
    factorTwoCenteredSymmetricPerturbationBilinear_add_left v w u hv hw hu,
    factorTwoCenteredSymmetricPerturbationBilinear_comm v u,
    factorTwoCenteredSymmetricPerturbationBilinear_comm w u]

/-- Exact two-sided real homogeneity of the complete mixed block on two
standard boundary-continuous tail pairs. -/
theorem factorTwoEndpointLowTailMixed_boundaryContinuous_smul_smul
    (fe₁ fe₂ : yoshidaPointwiseEvenPeriodicCoreSubmodule yoshidaA)
    (ro₁ ro₂ : YoshidaClippedPeriodicCore yoshidaA)
    (heReal₁ : ∀ x : ℝ,
      ((((fe₁.1 : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) x).im = 0))
    (heReal₂ : ∀ x : ℝ,
      ((((fe₂.1 : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) x).im = 0))
    (hoReal₁ : ∀ x : ℝ,
      ((ro₁ : YoshidaClippedSmooth yoshidaA) x).im = 0)
    (hoReal₂ : ∀ x : ℝ,
      ((ro₂ : YoshidaClippedSmooth yoshidaA) x).im = 0)
    (hoNeg₁ : (ro₁ : YoshidaClippedSmooth yoshidaA) (-yoshidaA) = 0)
    (hoPos₁ : (ro₁ : YoshidaClippedSmooth yoshidaA) yoshidaA = 0)
    (hoNeg₂ : (ro₂ : YoshidaClippedSmooth yoshidaA) (-yoshidaA) = 0)
    (hoPos₂ : (ro₂ : YoshidaClippedSmooth yoshidaA) yoshidaA = 0)
    (c d a b : ℝ) :
    let e₁ := boundaryContinuousEvenProfile fe₁
    let o₁ := centeredRescale yoshidaA (fun x ↦
      ((ro₁ : YoshidaClippedSmooth yoshidaA) x).re)
    let e₂ := boundaryContinuousEvenProfile fe₂
    let o₂ := centeredRescale yoshidaA (fun x ↦
      ((ro₂ : YoshidaClippedSmooth yoshidaA) x).re)
    factorTwoEndpointLowTailMixed
        (c • e₁) (d • e₂) (c • o₁) (d • o₂) a b =
      c * d * factorTwoEndpointLowTailMixed e₁ e₂ o₁ o₂ a b := by
  dsimp only
  have heClean :=
    factorTwoCenteredCleanPolarization_boundaryContinuous_smul_smul
      fe₁ fe₂ heReal₁ heReal₂ c d
  have hoClean := factorTwoCenteredCleanPolarization_zeroTrace_smul_smul
    ro₁ ro₂ hoReal₁ hoReal₂ hoNeg₁ hoPos₁ hoNeg₂ hoPos₂ c d
  unfold factorTwoEndpointLowTailMixed
  rw [heClean, hoClean,
    factorTwoCenteredSymmetricPerturbationBilinear_smul_smul,
    factorTwoCenteredSymmetricPerturbationBilinear_smul_smul,
    factorTwoCenteredAlternatingCoupling_smul_left,
    factorTwoCenteredAlternatingCoupling_smul_right,
    factorTwoCenteredAlternatingCoupling_smul_left,
    factorTwoCenteredAlternatingCoupling_smul_right]
  ring

/-- Additivity of the complete boundary-continuous mixed block in its first
real tail-pair argument. -/
theorem factorTwoEndpointLowTailMixed_boundaryContinuous_add_left
    (fe₁ fe₂ fe₃ : yoshidaPointwiseEvenPeriodicCoreSubmodule yoshidaA)
    (ro₁ ro₂ ro₃ : YoshidaClippedPeriodicCore yoshidaA)
    (heReal₁ : ∀ x : ℝ,
      ((fe₁.1 : YoshidaClippedSmooth yoshidaA) x).im = 0)
    (heReal₂ : ∀ x : ℝ,
      ((fe₂.1 : YoshidaClippedSmooth yoshidaA) x).im = 0)
    (heReal₃ : ∀ x : ℝ,
      ((fe₃.1 : YoshidaClippedSmooth yoshidaA) x).im = 0)
    (hoReal₁ : ∀ x : ℝ,
      ((ro₁ : YoshidaClippedSmooth yoshidaA) x).im = 0)
    (hoReal₂ : ∀ x : ℝ,
      ((ro₂ : YoshidaClippedSmooth yoshidaA) x).im = 0)
    (hoReal₃ : ∀ x : ℝ,
      ((ro₃ : YoshidaClippedSmooth yoshidaA) x).im = 0)
    (hoNeg₁ : (ro₁ : YoshidaClippedSmooth yoshidaA) (-yoshidaA) = 0)
    (hoPos₁ : (ro₁ : YoshidaClippedSmooth yoshidaA) yoshidaA = 0)
    (hoNeg₂ : (ro₂ : YoshidaClippedSmooth yoshidaA) (-yoshidaA) = 0)
    (hoPos₂ : (ro₂ : YoshidaClippedSmooth yoshidaA) yoshidaA = 0)
    (hoNeg₃ : (ro₃ : YoshidaClippedSmooth yoshidaA) (-yoshidaA) = 0)
    (hoPos₃ : (ro₃ : YoshidaClippedSmooth yoshidaA) yoshidaA = 0)
    (a b : ℝ) :
    let e₁ := boundaryContinuousEvenProfile fe₁
    let e₂ := boundaryContinuousEvenProfile fe₂
    let e₃ := boundaryContinuousEvenProfile fe₃
    let o₁ := centeredRescale yoshidaA (fun x ↦
      ((ro₁ : YoshidaClippedSmooth yoshidaA) x).re)
    let o₂ := centeredRescale yoshidaA (fun x ↦
      ((ro₂ : YoshidaClippedSmooth yoshidaA) x).re)
    let o₃ := centeredRescale yoshidaA (fun x ↦
      ((ro₃ : YoshidaClippedSmooth yoshidaA) x).re)
    factorTwoEndpointLowTailMixed (e₁ + e₂) e₃ (o₁ + o₂) o₃ a b =
      factorTwoEndpointLowTailMixed e₁ e₃ o₁ o₃ a b +
        factorTwoEndpointLowTailMixed e₂ e₃ o₂ o₃ a b := by
  dsimp only
  have hec₁ := continuous_boundaryContinuousEvenProfile fe₁
  have hec₂ := continuous_boundaryContinuousEvenProfile fe₂
  have hec₃ := continuous_boundaryContinuousEvenProfile fe₃
  have hoc₁ := continuous_centeredRescale_re_of_endpoints_zero
    yoshidaA_pos ro₁ hoNeg₁ hoPos₁
  have hoc₂ := continuous_centeredRescale_re_of_endpoints_zero
    yoshidaA_pos ro₂ hoNeg₂ hoPos₂
  have hoc₃ := continuous_centeredRescale_re_of_endpoints_zero
    yoshidaA_pos ro₃ hoNeg₃ hoPos₃
  have heClean :=
    factorTwoCenteredCleanPolarization_boundaryContinuous_add_left
      fe₁ fe₂ fe₃ heReal₁ heReal₂ heReal₃
  have hoClean := factorTwoCenteredCleanPolarization_zeroTrace_add_left
    ro₁ ro₂ ro₃ hoReal₁ hoReal₂ hoReal₃
    hoNeg₁ hoPos₁ hoNeg₂ hoPos₂ hoNeg₃ hoPos₃
  unfold factorTwoEndpointLowTailMixed
  rw [heClean, hoClean,
    factorTwoCenteredSymmetricPerturbationBilinear_add_left
      _ _ _ hec₁ hec₂ hec₃,
    factorTwoCenteredSymmetricPerturbationBilinear_add_left
      _ _ _ hoc₁ hoc₂ hoc₃,
    factorTwoCenteredAlternatingCoupling_add_left
      _ _ _ hec₁ hec₂ hoc₃,
    factorTwoCenteredAlternatingCoupling_add_right
      _ _ _ hec₃ hoc₁ hoc₂]
  ring

/-- Additivity of the complete boundary-continuous mixed block in its second
real tail-pair argument. -/
theorem factorTwoEndpointLowTailMixed_boundaryContinuous_add_right
    (fe₁ fe₂ fe₃ : yoshidaPointwiseEvenPeriodicCoreSubmodule yoshidaA)
    (ro₁ ro₂ ro₃ : YoshidaClippedPeriodicCore yoshidaA)
    (heReal₁ : ∀ x : ℝ,
      ((fe₁.1 : YoshidaClippedSmooth yoshidaA) x).im = 0)
    (heReal₂ : ∀ x : ℝ,
      ((fe₂.1 : YoshidaClippedSmooth yoshidaA) x).im = 0)
    (heReal₃ : ∀ x : ℝ,
      ((fe₃.1 : YoshidaClippedSmooth yoshidaA) x).im = 0)
    (hoReal₁ : ∀ x : ℝ,
      ((ro₁ : YoshidaClippedSmooth yoshidaA) x).im = 0)
    (hoReal₂ : ∀ x : ℝ,
      ((ro₂ : YoshidaClippedSmooth yoshidaA) x).im = 0)
    (hoReal₃ : ∀ x : ℝ,
      ((ro₃ : YoshidaClippedSmooth yoshidaA) x).im = 0)
    (hoNeg₁ : (ro₁ : YoshidaClippedSmooth yoshidaA) (-yoshidaA) = 0)
    (hoPos₁ : (ro₁ : YoshidaClippedSmooth yoshidaA) yoshidaA = 0)
    (hoNeg₂ : (ro₂ : YoshidaClippedSmooth yoshidaA) (-yoshidaA) = 0)
    (hoPos₂ : (ro₂ : YoshidaClippedSmooth yoshidaA) yoshidaA = 0)
    (hoNeg₃ : (ro₃ : YoshidaClippedSmooth yoshidaA) (-yoshidaA) = 0)
    (hoPos₃ : (ro₃ : YoshidaClippedSmooth yoshidaA) yoshidaA = 0)
    (a b : ℝ) :
    let e₁ := boundaryContinuousEvenProfile fe₁
    let e₂ := boundaryContinuousEvenProfile fe₂
    let e₃ := boundaryContinuousEvenProfile fe₃
    let o₁ := centeredRescale yoshidaA (fun x ↦
      ((ro₁ : YoshidaClippedSmooth yoshidaA) x).re)
    let o₂ := centeredRescale yoshidaA (fun x ↦
      ((ro₂ : YoshidaClippedSmooth yoshidaA) x).re)
    let o₃ := centeredRescale yoshidaA (fun x ↦
      ((ro₃ : YoshidaClippedSmooth yoshidaA) x).re)
    factorTwoEndpointLowTailMixed e₁ (e₂ + e₃) o₁ (o₂ + o₃) a b =
      factorTwoEndpointLowTailMixed e₁ e₂ o₁ o₂ a b +
        factorTwoEndpointLowTailMixed e₁ e₃ o₁ o₃ a b := by
  dsimp only
  have hec₁ := continuous_boundaryContinuousEvenProfile fe₁
  have hec₂ := continuous_boundaryContinuousEvenProfile fe₂
  have hec₃ := continuous_boundaryContinuousEvenProfile fe₃
  have hoc₁ := continuous_centeredRescale_re_of_endpoints_zero
    yoshidaA_pos ro₁ hoNeg₁ hoPos₁
  have hoc₂ := continuous_centeredRescale_re_of_endpoints_zero
    yoshidaA_pos ro₂ hoNeg₂ hoPos₂
  have hoc₃ := continuous_centeredRescale_re_of_endpoints_zero
    yoshidaA_pos ro₃ hoNeg₃ hoPos₃
  have heClean :=
    factorTwoCenteredCleanPolarization_boundaryContinuous_add_right
      fe₁ fe₂ fe₃ heReal₁ heReal₂ heReal₃
  have hoClean := factorTwoCenteredCleanPolarization_zeroTrace_add_right
    ro₁ ro₂ ro₃ hoReal₁ hoReal₂ hoReal₃
    hoNeg₁ hoPos₁ hoNeg₂ hoPos₂ hoNeg₃ hoPos₃
  unfold factorTwoEndpointLowTailMixed
  rw [heClean, hoClean,
    factorTwoCenteredSymmetricPerturbationBilinear_add_right
      _ _ _ hec₁ hec₂ hec₃,
    factorTwoCenteredSymmetricPerturbationBilinear_add_right
      _ _ _ hoc₁ hoc₂ hoc₃,
    factorTwoCenteredAlternatingCoupling_add_right
      _ _ _ hec₁ hoc₂ hoc₃,
    factorTwoCenteredAlternatingCoupling_add_left
      _ _ _ hec₂ hec₃ hoc₁]
  ring

/-- The boundary-continuous phase form is nonnegative on every standard real
tail pair, with no endpoint condition on the even source tail. -/
theorem boundaryContinuous_tail_phase_nonneg
    (re ro : YoshidaClippedPeriodicCore yoshidaA)
    (heTail : re ∈ yoshidaPeriodicCoreEvenTailSubmodule yoshidaA_pos 199)
    (hoTail : ro ∈ yoshidaPeriodicCoreOddTailSubmodule yoshidaA_pos 10)
    (heReal : ∀ x : ℝ,
      ((re : YoshidaClippedSmooth yoshidaA) x).im = 0)
    (hoReal : ∀ x : ℝ,
      ((ro : YoshidaClippedSmooth yoshidaA) x).im = 0)
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    let fe : yoshidaPointwiseEvenPeriodicCoreSubmodule yoshidaA :=
      ⟨re, evenTail_pointwise_even yoshidaA_pos 199 re heTail⟩
    let e := boundaryContinuousEvenProfile fe
    let o := centeredRescale yoshidaA (fun x ↦
      ((ro : YoshidaClippedSmooth yoshidaA) x).re)
    0 ≤ factorTwoEndpointChannelPhase e o a b := by
  dsimp only
  let fe : yoshidaPointwiseEvenPeriodicCoreSubmodule yoshidaA :=
    ⟨re, evenTail_pointwise_even yoshidaA_pos 199 re heTail⟩
  let e : ℝ → ℝ := boundaryContinuousEvenProfile fe
  let o : ℝ → ℝ := centeredRescale yoshidaA (fun x ↦
    ((ro : YoshidaClippedSmooth yoshidaA) x).re)
  let Ee : ℝ := ∫ x : ℝ in -1..1, e x ^ 2
  let Eo : ℝ := ∫ x : ℝ in -1..1, o x ^ 2
  obtain ⟨hoNeg, hoPos⟩ := oddTail_endpoints_zero ro hoTail
  have hEe : 0 ≤ Ee := by
    dsimp only [Ee]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun x _ ↦ sq_nonneg (e x))
  have hEo : 0 ≤ Eo := by
    dsimp only [Eo]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun x _ ↦ sq_nonneg (o x))
  have hQeBound : (102 / 25 : ℝ) * Ee ≤
      yoshidaEndpointOddCleanQuadratic e := by
    simpa only [e, Ee, fe] using
      evenTail_boundaryContinuous_clean_coercive re heTail heReal
  have hQoBound : (38 / 25 : ℝ) * Eo ≤
      yoshidaEndpointOddCleanQuadratic o := by
    simpa only [o, Eo] using
      oddTail_endpoint_clean_coercive ro hoTail hoReal hoNeg hoPos
  have hQe : 0 ≤ yoshidaEndpointOddCleanQuadratic e := by
    nlinarith
  have hQo : 0 ≤ yoshidaEndpointOddCleanQuadratic o := by
    nlinarith
  have hreserve := boundaryContinuous_tail_phase_uniform_clean_reserve
    re ro heTail hoTail heReal hoReal a b hphase
  have hreserve' :
      (1 / 200 : ℝ) *
          (yoshidaEndpointOddCleanQuadratic e +
            yoshidaEndpointOddCleanQuadratic o) ≤
        factorTwoEndpointChannelPhase e o a b := by
    simpa only [e, o, fe] using hreserve
  have hleft : 0 ≤ (1 / 200 : ℝ) *
      (yoshidaEndpointOddCleanQuadratic e +
        yoshidaEndpointOddCleanQuadratic o) := by
    positivity
  exact hleft.trans hreserve'

/-- Exact Cauchy--Schwarz inequality for the complete fixed-disk mixed block
on two standard real tail pairs.  The even tails remain in the original
cutoff-`199` carrier and require no endpoint-zero hypotheses. -/
theorem factorTwoEndpointLowTailMixed_sq_le_boundaryContinuous_tail_phase_mul
    (re₁ ro₁ re₂ ro₂ : YoshidaClippedPeriodicCore yoshidaA)
    (heTail₁ : re₁ ∈ yoshidaPeriodicCoreEvenTailSubmodule yoshidaA_pos 199)
    (hoTail₁ : ro₁ ∈ yoshidaPeriodicCoreOddTailSubmodule yoshidaA_pos 10)
    (heTail₂ : re₂ ∈ yoshidaPeriodicCoreEvenTailSubmodule yoshidaA_pos 199)
    (hoTail₂ : ro₂ ∈ yoshidaPeriodicCoreOddTailSubmodule yoshidaA_pos 10)
    (heReal₁ : ∀ x : ℝ,
      ((re₁ : YoshidaClippedSmooth yoshidaA) x).im = 0)
    (hoReal₁ : ∀ x : ℝ,
      ((ro₁ : YoshidaClippedSmooth yoshidaA) x).im = 0)
    (heReal₂ : ∀ x : ℝ,
      ((re₂ : YoshidaClippedSmooth yoshidaA) x).im = 0)
    (hoReal₂ : ∀ x : ℝ,
      ((ro₂ : YoshidaClippedSmooth yoshidaA) x).im = 0)
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    let fe₁ : yoshidaPointwiseEvenPeriodicCoreSubmodule yoshidaA :=
      ⟨re₁, evenTail_pointwise_even yoshidaA_pos 199 re₁ heTail₁⟩
    let e₁ := boundaryContinuousEvenProfile fe₁
    let o₁ := centeredRescale yoshidaA (fun x ↦
      ((ro₁ : YoshidaClippedSmooth yoshidaA) x).re)
    let fe₂ : yoshidaPointwiseEvenPeriodicCoreSubmodule yoshidaA :=
      ⟨re₂, evenTail_pointwise_even yoshidaA_pos 199 re₂ heTail₂⟩
    let e₂ := boundaryContinuousEvenProfile fe₂
    let o₂ := centeredRescale yoshidaA (fun x ↦
      ((ro₂ : YoshidaClippedSmooth yoshidaA) x).re)
    factorTwoEndpointLowTailMixed e₁ e₂ o₁ o₂ a b ^ 2 ≤
      factorTwoEndpointChannelPhase e₁ o₁ a b *
        factorTwoEndpointChannelPhase e₂ o₂ a b := by
  dsimp only
  let fe₁ : yoshidaPointwiseEvenPeriodicCoreSubmodule yoshidaA :=
    ⟨re₁, evenTail_pointwise_even yoshidaA_pos 199 re₁ heTail₁⟩
  let e₁ : ℝ → ℝ := boundaryContinuousEvenProfile fe₁
  let o₁ : ℝ → ℝ := centeredRescale yoshidaA (fun x ↦
    ((ro₁ : YoshidaClippedSmooth yoshidaA) x).re)
  let fe₂ : yoshidaPointwiseEvenPeriodicCoreSubmodule yoshidaA :=
    ⟨re₂, evenTail_pointwise_even yoshidaA_pos 199 re₂ heTail₂⟩
  let e₂ : ℝ → ℝ := boundaryContinuousEvenProfile fe₂
  let o₂ : ℝ → ℝ := centeredRescale yoshidaA (fun x ↦
    ((ro₂ : YoshidaClippedSmooth yoshidaA) x).re)
  have hec₁ : Continuous e₁ := by
    simpa only [e₁] using continuous_boundaryContinuousEvenProfile fe₁
  have hec₂ : Continuous e₂ := by
    simpa only [e₂] using continuous_boundaryContinuousEvenProfile fe₂
  obtain ⟨hoNeg₁, hoPos₁⟩ := oddTail_endpoints_zero ro₁ hoTail₁
  obtain ⟨hoNeg₂, hoPos₂⟩ := oddTail_endpoints_zero ro₂ hoTail₂
  have hoc₁ : Continuous o₁ := by
    simpa only [o₁] using continuous_centeredRescale_re_of_endpoints_zero
      yoshidaA_pos ro₁ hoNeg₁ hoPos₁
  have hoc₂ : Continuous o₂ := by
    simpa only [o₂] using continuous_centeredRescale_re_of_endpoints_zero
      yoshidaA_pos ro₂ hoNeg₂ hoPos₂
  apply factorTwoEndpointLowTailMixed_sq_le_of_quadratic_pencil
  intro c d
  let re : YoshidaClippedPeriodicCore yoshidaA :=
    (c : ℂ) • re₁ + (d : ℂ) • re₂
  let ro : YoshidaClippedPeriodicCore yoshidaA :=
    (c : ℂ) • ro₁ + (d : ℂ) • ro₂
  have heTail : re ∈
      yoshidaPeriodicCoreEvenTailSubmodule yoshidaA_pos 199 := by
    exact (yoshidaPeriodicCoreEvenTailSubmodule yoshidaA_pos 199).add_mem
      ((yoshidaPeriodicCoreEvenTailSubmodule yoshidaA_pos 199).smul_mem
        (c : ℂ) heTail₁)
      ((yoshidaPeriodicCoreEvenTailSubmodule yoshidaA_pos 199).smul_mem
        (d : ℂ) heTail₂)
  have hoTail : ro ∈
      yoshidaPeriodicCoreOddTailSubmodule yoshidaA_pos 10 := by
    exact (yoshidaPeriodicCoreOddTailSubmodule yoshidaA_pos 10).add_mem
      ((yoshidaPeriodicCoreOddTailSubmodule yoshidaA_pos 10).smul_mem
        (c : ℂ) hoTail₁)
      ((yoshidaPeriodicCoreOddTailSubmodule yoshidaA_pos 10).smul_mem
        (d : ℂ) hoTail₂)
  have heReal : ∀ x : ℝ,
      ((re : YoshidaClippedSmooth yoshidaA) x).im = 0 := by
    intro x
    dsimp only [re]
    simp only [Submodule.coe_add, Submodule.coe_smul, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    rw [heReal₁ x, heReal₂ x]
    ring
  have hoReal : ∀ x : ℝ,
      ((ro : YoshidaClippedSmooth yoshidaA) x).im = 0 := by
    intro x
    dsimp only [ro]
    simp only [Submodule.coe_add, Submodule.coe_smul, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    rw [hoReal₁ x, hoReal₂ x]
    ring
  let fe : yoshidaPointwiseEvenPeriodicCoreSubmodule yoshidaA :=
    ⟨re, evenTail_pointwise_even yoshidaA_pos 199 re heTail⟩
  let e : ℝ → ℝ := boundaryContinuousEvenProfile fe
  let o : ℝ → ℝ := centeredRescale yoshidaA (fun x ↦
    ((ro : YoshidaClippedSmooth yoshidaA) x).re)
  have hfe : fe = (c : ℂ) • fe₁ + (d : ℂ) • fe₂ := by
    apply Subtype.ext
    rfl
  have heProfile : e = c • e₁ + d • e₂ := by
    dsimp only [e]
    rw [hfe, boundaryContinuousEvenProfile_add,
      boundaryContinuousEvenProfile_smul_real,
      boundaryContinuousEvenProfile_smul_real]
  have hoProfile : o = c • o₁ + d • o₂ := by
    funext x
    dsimp only [o, ro, o₁, o₂, centeredRescale]
    simp only [Submodule.coe_add, Submodule.coe_smul, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rfl
  have hnonneg : 0 ≤ factorTwoEndpointChannelPhase e o a b := by
    simpa only [e, o, fe] using boundaryContinuous_tail_phase_nonneg
      re ro heTail hoTail heReal hoReal a b hphase
  have hnonneg' : 0 ≤ factorTwoEndpointChannelPhase
      (c • e₁ + d • e₂) (c • o₁ + d • o₂) a b := by
    rw [← heProfile, ← hoProfile]
    exact hnonneg
  rw [factorTwoEndpointChannelPhase_add_add_eq_low_mixed_tail
      (c • e₁) (d • e₂) (c • o₁) (d • o₂)
      (hec₁.const_smul c) (hec₂.const_smul d)
      (hoc₁.const_smul c) (hoc₂.const_smul d) a b,
    factorTwoEndpointChannelPhase_smul,
    factorTwoEndpointChannelPhase_smul,
    factorTwoEndpointLowTailMixed_boundaryContinuous_smul_smul
      fe₁ fe₂ ro₁ ro₂ heReal₁ heReal₂ hoReal₁ hoReal₂
      hoNeg₁ hoPos₁ hoNeg₂ hoPos₂ c d a b] at hnonneg'
  nlinarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseBoundaryContinuousTailMixedCauchyStructural

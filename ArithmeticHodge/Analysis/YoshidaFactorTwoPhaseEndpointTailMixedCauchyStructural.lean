import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCleanPolarizationCritical
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseDirectionalTail
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseLowSchur
import ArithmeticHodge.Analysis.YoshidaEndpointOddLowGramExpansion

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseEndpointTailMixedCauchyStructural

noncomputable section

open ArithmeticHodge.Analysis
open YoshidaCoercivityNumerics
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointOddLowGramExpansion
open YoshidaEndpointScaledCorrelation
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointChannelRadius
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoPhaseCleanPolarizationCritical
open YoshidaFactorTwoPhaseDirectionalTail
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoPhaseRadiusClosure
open YoshidaWeightedTailBounds

/-!
# Structural Cauchy inequality on the endpoint-tail phase space

At a fixed point of the closed phase disk, the already-proved endpoint-tail
theorem makes the phase form nonnegative on every real two-dimensional tail
pencil.  Exact polarization therefore gives its Cauchy--Schwarz inequality.

Both entries below are genuine endpoint tails.  In the eventual low--tail
Schur argument the first entry can be a tail-space representer of a finite-low
functional; this theorem does not incorrectly place a finite-low mode in the
Fourier tail submodule.
-/

/-- Simultaneous real scaling of the two parity entries scales the phase
quadratically. -/
theorem factorTwoEndpointChannelPhase_smul
    (u v : ℝ → ℝ) (c a b : ℝ) :
    factorTwoEndpointChannelPhase (c • u) (c • v) a b =
      c ^ 2 * factorTwoEndpointChannelPhase u v a b := by
  have hQu : yoshidaEndpointOddCleanQuadratic (c • u) =
      c ^ 2 * yoshidaEndpointOddCleanQuadratic u := by
    simpa only [Pi.smul_apply, smul_eq_mul] using
      yoshidaEndpointOddCleanQuadratic_const_mul u c
  have hQv : yoshidaEndpointOddCleanQuadratic (c • v) =
      c ^ 2 * yoshidaEndpointOddCleanQuadratic v := by
    simpa only [Pi.smul_apply, smul_eq_mul] using
      yoshidaEndpointOddCleanQuadratic_const_mul v c
  unfold factorTwoEndpointChannelPhase factorTwoEndpointChannelCleanSum
    factorTwoEndpointChannelSymmetricSum
  rw [hQu, hQv,
    factorTwoCenteredSymmetricPerturbation_smul,
    factorTwoCenteredSymmetricPerturbation_smul,
    factorTwoCenteredAlternatingCoupling_smul_left,
    factorTwoCenteredAlternatingCoupling_smul_right]
  ring

/-- On endpoint-zero real periodic profiles, the clean polarization inherits
two-sided real homogeneity from the clipped critical sesquilinear form. -/
private theorem factorTwoCenteredCleanPolarization_tailProfiles_smul_smul
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
  have hform :
      yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
          (rc : YoshidaClippedSmooth yoshidaA)
          (sd : YoshidaClippedSmooth yoshidaA) =
        ((c * d : ℝ) : ℂ) *
          yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
            (r : YoshidaClippedSmooth yoshidaA)
            (s : YoshidaClippedSmooth yoshidaA) := by
    dsimp only [rc, sd]
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
  rw [hrcProfile, hsdProfile] at hscaled
  calc
    factorTwoCenteredCleanPolarization (c • u) (d • v) =
        (yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
          (rc : YoshidaClippedSmooth yoshidaA)
          (sd : YoshidaClippedSmooth yoshidaA)).re / yoshidaA := hscaled
    _ = (((c * d : ℝ) : ℂ) *
          yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
            (r : YoshidaClippedSmooth yoshidaA)
            (s : YoshidaClippedSmooth yoshidaA)).re / yoshidaA := by
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

/-- Two-sided real homogeneity of the exact mixed block for two endpoint-tail
pairs. -/
private theorem factorTwoEndpointLowTailMixed_tailProfiles_smul_smul
    (re₁ ro₁ re₂ ro₂ : YoshidaClippedPeriodicCore yoshidaA)
    (heReal₁ : ∀ x : ℝ,
      ((re₁ : YoshidaClippedSmooth yoshidaA) x).im = 0)
    (hoReal₁ : ∀ x : ℝ,
      ((ro₁ : YoshidaClippedSmooth yoshidaA) x).im = 0)
    (heReal₂ : ∀ x : ℝ,
      ((re₂ : YoshidaClippedSmooth yoshidaA) x).im = 0)
    (hoReal₂ : ∀ x : ℝ,
      ((ro₂ : YoshidaClippedSmooth yoshidaA) x).im = 0)
    (heNeg₁ : (re₁ : YoshidaClippedSmooth yoshidaA) (-yoshidaA) = 0)
    (hePos₁ : (re₁ : YoshidaClippedSmooth yoshidaA) yoshidaA = 0)
    (hoNeg₁ : (ro₁ : YoshidaClippedSmooth yoshidaA) (-yoshidaA) = 0)
    (hoPos₁ : (ro₁ : YoshidaClippedSmooth yoshidaA) yoshidaA = 0)
    (heNeg₂ : (re₂ : YoshidaClippedSmooth yoshidaA) (-yoshidaA) = 0)
    (hePos₂ : (re₂ : YoshidaClippedSmooth yoshidaA) yoshidaA = 0)
    (hoNeg₂ : (ro₂ : YoshidaClippedSmooth yoshidaA) (-yoshidaA) = 0)
    (hoPos₂ : (ro₂ : YoshidaClippedSmooth yoshidaA) yoshidaA = 0)
    (c d a b : ℝ) :
    let e₁ := centeredRescale yoshidaA (fun x ↦
      ((re₁ : YoshidaClippedSmooth yoshidaA) x).re)
    let o₁ := centeredRescale yoshidaA (fun x ↦
      ((ro₁ : YoshidaClippedSmooth yoshidaA) x).re)
    let e₂ := centeredRescale yoshidaA (fun x ↦
      ((re₂ : YoshidaClippedSmooth yoshidaA) x).re)
    let o₂ := centeredRescale yoshidaA (fun x ↦
      ((ro₂ : YoshidaClippedSmooth yoshidaA) x).re)
    factorTwoEndpointLowTailMixed
        (c • e₁) (d • e₂) (c • o₁) (d • o₂) a b =
      c * d * factorTwoEndpointLowTailMixed e₁ e₂ o₁ o₂ a b := by
  dsimp only
  let e₁ : ℝ → ℝ := centeredRescale yoshidaA (fun x ↦
    ((re₁ : YoshidaClippedSmooth yoshidaA) x).re)
  let o₁ : ℝ → ℝ := centeredRescale yoshidaA (fun x ↦
    ((ro₁ : YoshidaClippedSmooth yoshidaA) x).re)
  let e₂ : ℝ → ℝ := centeredRescale yoshidaA (fun x ↦
    ((re₂ : YoshidaClippedSmooth yoshidaA) x).re)
  let o₂ : ℝ → ℝ := centeredRescale yoshidaA (fun x ↦
    ((ro₂ : YoshidaClippedSmooth yoshidaA) x).re)
  have heClean := factorTwoCenteredCleanPolarization_tailProfiles_smul_smul
    re₁ re₂ heReal₁ heReal₂ heNeg₁ hePos₁ heNeg₂ hePos₂ c d
  have hoClean := factorTwoCenteredCleanPolarization_tailProfiles_smul_smul
    ro₁ ro₂ hoReal₁ hoReal₂ hoNeg₁ hoPos₁ hoNeg₂ hoPos₂ c d
  dsimp only [e₁, e₂] at heClean
  dsimp only [o₁, o₂] at hoClean
  unfold factorTwoEndpointLowTailMixed
  rw [heClean, hoClean,
    factorTwoCenteredSymmetricPerturbationBilinear_smul_smul,
    factorTwoCenteredSymmetricPerturbationBilinear_smul_smul,
    factorTwoCenteredAlternatingCoupling_smul_left,
    factorTwoCenteredAlternatingCoupling_smul_right,
    factorTwoCenteredAlternatingCoupling_smul_left,
    factorTwoCenteredAlternatingCoupling_smul_right]
  ring

/-- The scalar discriminant step, separated from the tail construction. -/
theorem factorTwoEndpointLowTailMixed_sq_le_of_quadratic_pencil
    (u₁ u₂ v₁ v₂ : ℝ → ℝ) (a b : ℝ)
    (hpencil : ∀ c d : ℝ,
      0 ≤ factorTwoEndpointChannelPhase u₁ v₁ a b * c ^ 2 +
        2 * factorTwoEndpointLowTailMixed u₁ u₂ v₁ v₂ a b * c * d +
        factorTwoEndpointChannelPhase u₂ v₂ a b * d ^ 2) :
    factorTwoEndpointLowTailMixed u₁ u₂ v₁ v₂ a b ^ 2 ≤
      factorTwoEndpointChannelPhase u₁ v₁ a b *
        factorTwoEndpointChannelPhase u₂ v₂ a b := by
  exact ((real_quadratic_pencil_nonneg_iff
    (factorTwoEndpointChannelPhase u₁ v₁ a b)
    (factorTwoEndpointChannelPhase u₂ v₂ a b)
    (factorTwoEndpointLowTailMixed u₁ u₂ v₁ v₂ a b)).mp
      hpencil).2.2

/-- Exact Cauchy--Schwarz inequality for the fixed-disk endpoint-tail phase
form.  Both arguments are honest members of the production even/odd tail
submodules and have zero endpoint traces. -/
theorem factorTwoEndpointLowTailMixed_sq_le_tail_phase_mul
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
    (heNeg₁ : (re₁ : YoshidaClippedSmooth yoshidaA) (-yoshidaA) = 0)
    (hePos₁ : (re₁ : YoshidaClippedSmooth yoshidaA) yoshidaA = 0)
    (hoNeg₁ : (ro₁ : YoshidaClippedSmooth yoshidaA) (-yoshidaA) = 0)
    (hoPos₁ : (ro₁ : YoshidaClippedSmooth yoshidaA) yoshidaA = 0)
    (heNeg₂ : (re₂ : YoshidaClippedSmooth yoshidaA) (-yoshidaA) = 0)
    (hePos₂ : (re₂ : YoshidaClippedSmooth yoshidaA) yoshidaA = 0)
    (hoNeg₂ : (ro₂ : YoshidaClippedSmooth yoshidaA) (-yoshidaA) = 0)
    (hoPos₂ : (ro₂ : YoshidaClippedSmooth yoshidaA) yoshidaA = 0)
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    let e₁ := centeredRescale yoshidaA (fun x ↦
      ((re₁ : YoshidaClippedSmooth yoshidaA) x).re)
    let o₁ := centeredRescale yoshidaA (fun x ↦
      ((ro₁ : YoshidaClippedSmooth yoshidaA) x).re)
    let e₂ := centeredRescale yoshidaA (fun x ↦
      ((re₂ : YoshidaClippedSmooth yoshidaA) x).re)
    let o₂ := centeredRescale yoshidaA (fun x ↦
      ((ro₂ : YoshidaClippedSmooth yoshidaA) x).re)
    factorTwoEndpointLowTailMixed e₁ e₂ o₁ o₂ a b ^ 2 ≤
      factorTwoEndpointChannelPhase e₁ o₁ a b *
        factorTwoEndpointChannelPhase e₂ o₂ a b := by
  dsimp only
  let e₁ : ℝ → ℝ := centeredRescale yoshidaA (fun x ↦
    ((re₁ : YoshidaClippedSmooth yoshidaA) x).re)
  let o₁ : ℝ → ℝ := centeredRescale yoshidaA (fun x ↦
    ((ro₁ : YoshidaClippedSmooth yoshidaA) x).re)
  let e₂ : ℝ → ℝ := centeredRescale yoshidaA (fun x ↦
    ((re₂ : YoshidaClippedSmooth yoshidaA) x).re)
  let o₂ : ℝ → ℝ := centeredRescale yoshidaA (fun x ↦
    ((ro₂ : YoshidaClippedSmooth yoshidaA) x).re)
  have hec₁ : Continuous e₁ := by
    simpa only [e₁] using continuous_centeredRescale_re_of_endpoints_zero
      yoshidaA_pos re₁ heNeg₁ hePos₁
  have hoc₁ : Continuous o₁ := by
    simpa only [o₁] using continuous_centeredRescale_re_of_endpoints_zero
      yoshidaA_pos ro₁ hoNeg₁ hoPos₁
  have hec₂ : Continuous e₂ := by
    simpa only [e₂] using continuous_centeredRescale_re_of_endpoints_zero
      yoshidaA_pos re₂ heNeg₂ hePos₂
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
  have heNeg : (re : YoshidaClippedSmooth yoshidaA) (-yoshidaA) = 0 := by
    dsimp only [re]
    simp only [Submodule.coe_add, Submodule.coe_smul, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, heNeg₁, heNeg₂, mul_zero, add_zero]
  have hePos : (re : YoshidaClippedSmooth yoshidaA) yoshidaA = 0 := by
    dsimp only [re]
    simp only [Submodule.coe_add, Submodule.coe_smul, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, hePos₁, hePos₂, mul_zero, add_zero]
  have hoNeg : (ro : YoshidaClippedSmooth yoshidaA) (-yoshidaA) = 0 := by
    dsimp only [ro]
    simp only [Submodule.coe_add, Submodule.coe_smul, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, hoNeg₁, hoNeg₂, mul_zero, add_zero]
  have hoPos : (ro : YoshidaClippedSmooth yoshidaA) yoshidaA = 0 := by
    dsimp only [ro]
    simp only [Submodule.coe_add, Submodule.coe_smul, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, hoPos₁, hoPos₂, mul_zero, add_zero]
  have heProfile :
      centeredRescale yoshidaA (fun x ↦
        ((re : YoshidaClippedSmooth yoshidaA) x).re) = c • e₁ + d • e₂ := by
    funext x
    dsimp only [re, e₁, e₂, centeredRescale]
    simp only [Submodule.coe_add, Submodule.coe_smul, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rfl
  have hoProfile :
      centeredRescale yoshidaA (fun x ↦
        ((ro : YoshidaClippedSmooth yoshidaA) x).re) = c • o₁ + d • o₂ := by
    funext x
    dsimp only [ro, o₁, o₂, centeredRescale]
    simp only [Submodule.coe_add, Submodule.coe_smul, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rfl
  have hnonneg := endpoint_tail_phase_uniform re ro
    (by simpa only [YoshidaWeightedTailBounds.yoshidaA,
        YoshidaEndpointHyperbolicBound.yoshidaEndpointA] using heTail)
    (by simpa only [YoshidaWeightedTailBounds.yoshidaA,
        YoshidaEndpointHyperbolicBound.yoshidaEndpointA] using hoTail)
    (by simpa only [YoshidaWeightedTailBounds.yoshidaA,
        YoshidaEndpointHyperbolicBound.yoshidaEndpointA] using heReal)
    (by simpa only [YoshidaWeightedTailBounds.yoshidaA,
        YoshidaEndpointHyperbolicBound.yoshidaEndpointA] using hoReal)
    (by simpa only [YoshidaWeightedTailBounds.yoshidaA,
        YoshidaEndpointHyperbolicBound.yoshidaEndpointA] using heNeg)
    (by simpa only [YoshidaWeightedTailBounds.yoshidaA,
        YoshidaEndpointHyperbolicBound.yoshidaEndpointA] using hePos)
    (by simpa only [YoshidaWeightedTailBounds.yoshidaA,
        YoshidaEndpointHyperbolicBound.yoshidaEndpointA] using hoNeg)
    (by simpa only [YoshidaWeightedTailBounds.yoshidaA,
        YoshidaEndpointHyperbolicBound.yoshidaEndpointA] using hoPos)
    a b hphase
  have hnonneg' : 0 ≤ factorTwoEndpointChannelPhase
      (c • e₁ + d • e₂) (c • o₁ + d • o₂) a b := by
    rw [← heProfile, ← hoProfile]
    simpa only [factorTwoEndpointChannelPhase,
      factorTwoEndpointChannelCleanSum, factorTwoEndpointChannelSymmetricSum,
      YoshidaWeightedTailBounds.yoshidaA,
      YoshidaEndpointHyperbolicBound.yoshidaEndpointA] using hnonneg
  rw [factorTwoEndpointChannelPhase_add_add_eq_low_mixed_tail
      (c • e₁) (d • e₂) (c • o₁) (d • o₂)
      (hec₁.const_smul c) (hec₂.const_smul d)
      (hoc₁.const_smul c) (hoc₂.const_smul d) a b,
    factorTwoEndpointChannelPhase_smul,
    factorTwoEndpointChannelPhase_smul,
    factorTwoEndpointLowTailMixed_tailProfiles_smul_smul
      re₁ ro₁ re₂ ro₂ heReal₁ hoReal₁ heReal₂ hoReal₂
      heNeg₁ hePos₁ hoNeg₁ hoPos₁ heNeg₂ hePos₂ hoNeg₂ hoPos₂
      c d a b] at hnonneg'
  nlinarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseEndpointTailMixedCauchyStructural

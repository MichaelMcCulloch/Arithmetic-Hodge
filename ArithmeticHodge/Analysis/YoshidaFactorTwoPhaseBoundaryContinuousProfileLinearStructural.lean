import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseBoundaryContinuousTailStructural

set_option autoImplicit false

open Complex Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseBoundaryContinuousProfileLinearStructural

noncomputable section

open ArithmeticHodge.Analysis
open YoshidaEndpointEvenBoundaryResidual
open YoshidaEndpointScaledCorrelation
open YoshidaFactorTwoPhaseBoundaryContinuousTailStructural
open YoshidaPointwiseParityCore
open YoshidaWeightedTailBounds

/-!
# Real linearity of the boundary-continuous even representative

The endpoint correction used by `boundaryContinuousEvenProfile` is linear in
the source profile.  These identities let the standard finite-low plus tail
decomposition pass to globally continuous real representatives.
-/

/-- Pointwise expansion of the boundary-continuous representative into its
endpoint constant and boundary residual. -/
theorem boundaryContinuousEvenProfile_apply
    (f : yoshidaPointwiseEvenPeriodicCoreSubmodule yoshidaA) (x : ℝ) :
    boundaryContinuousEvenProfile f x =
      ((f.1 : YoshidaClippedSmooth yoshidaA) yoshidaA).re +
      (((f.1 : YoshidaClippedSmooth yoshidaA) (yoshidaA * x) -
        ((f.1 : YoshidaClippedSmooth yoshidaA) yoshidaA) *
        ((periodicCoreOne yoshidaA : YoshidaClippedSmooth yoshidaA)
          (yoshidaA * x)))).re := by
  rfl

@[simp] theorem boundaryContinuousEvenProfile_zero :
    boundaryContinuousEvenProfile
      (0 : yoshidaPointwiseEvenPeriodicCoreSubmodule yoshidaA) = 0 := by
  funext x
  rw [boundaryContinuousEvenProfile_apply]
  simp

theorem boundaryContinuousEvenProfile_add
    (f g : yoshidaPointwiseEvenPeriodicCoreSubmodule yoshidaA) :
    boundaryContinuousEvenProfile (f + g) =
      boundaryContinuousEvenProfile f + boundaryContinuousEvenProfile g := by
  funext x
  change boundaryContinuousEvenProfile (f + g) x =
    boundaryContinuousEvenProfile f x + boundaryContinuousEvenProfile g x
  rw [boundaryContinuousEvenProfile_apply,
    boundaryContinuousEvenProfile_apply,
    boundaryContinuousEvenProfile_apply]
  simp [add_mul]
  ring

theorem boundaryContinuousEvenProfile_smul_real
    (r : ℝ) (f : yoshidaPointwiseEvenPeriodicCoreSubmodule yoshidaA) :
    boundaryContinuousEvenProfile ((r : ℂ) • f) =
      r • boundaryContinuousEvenProfile f := by
  funext x
  change boundaryContinuousEvenProfile ((r : ℂ) • f) x =
    r * boundaryContinuousEvenProfile f x
  rw [boundaryContinuousEvenProfile_apply,
    boundaryContinuousEvenProfile_apply]
  simp [mul_sub, mul_assoc]
  ring

/-- If the source has zero real endpoint value, its boundary-continuous
representative is globally, not merely on `[-1,1]`, the raw centered real
profile.  No pointwise-reality assumption is needed. -/
theorem boundaryContinuousEvenProfile_eq_centeredRescale_of_endpoint_re_eq_zero
    (f : yoshidaPointwiseEvenPeriodicCoreSubmodule yoshidaA)
    (hzero :
      ((((f.1 : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) yoshidaA).re = 0)) :
    boundaryContinuousEvenProfile f =
      centeredRescale yoshidaA (fun y ↦
        (((f.1 : YoshidaClippedPeriodicCore yoshidaA) :
          YoshidaClippedSmooth yoshidaA) y).re) := by
  funext x
  have honeIm :
      ((((periodicCoreOne yoshidaA : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) (yoshidaA * x)).im = 0) := by
    change (if yoshidaA * x ∈ Icc (-yoshidaA) yoshidaA then
      (1 : ℂ) else 0).im = 0
    split <;> simp
  rw [boundaryContinuousEvenProfile_apply]
  unfold centeredRescale
  rw [Complex.sub_re, Complex.mul_re, hzero, honeIm]
  ring

/-- Complex endpoint vanishing is a convenient stronger hypothesis for the
global raw-profile identification. -/
theorem boundaryContinuousEvenProfile_eq_centeredRescale_of_endpoint_eq_zero
    (f : yoshidaPointwiseEvenPeriodicCoreSubmodule yoshidaA)
    (hzero :
      (((f.1 : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) yoshidaA = 0)) :
    boundaryContinuousEvenProfile f =
      centeredRescale yoshidaA (fun y ↦
        (((f.1 : YoshidaClippedPeriodicCore yoshidaA) :
          YoshidaClippedSmooth yoshidaA) y).re) := by
  apply boundaryContinuousEvenProfile_eq_centeredRescale_of_endpoint_re_eq_zero
  rw [hzero]
  rfl

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseBoundaryContinuousProfileLinearStructural

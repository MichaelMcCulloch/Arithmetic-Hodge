import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLow

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowControlsPositive

noncomputable section

open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseLowSchur
open YoshidaEndpointOddResidualRegularity

/-!
# Exact scalar gates for the intrinsic Bernstein controls

Each Bernstein control from the intrinsic four-mode phase is a homogeneous
binary quadratic in the `P₁/P₃` coefficients.  This file extracts its genuine
`2 x 2` Gram entries and proves the exact positive-semidefinite criterion.
There is no phase sampling, mode enumeration, or numerical decision
certificate: the remaining obligations are fixed analytic inequalities
between named endpoint forms.

The endpoint controls are also reduced to their decoupled endpoint products.
For the two interior controls, the scalar Gram criterion below is the sharp
structural gate; proving its six inequalities requires analytic information
about the complete clean/adjacent-kernel forms, rather than a coarse absolute
bound on their separate summands.
-/

/-! ## Canonical Gram extraction for a binary quadratic -/

/-- Leading diagonal entry extracted from a binary quadratic. -/
def intrinsicBinaryQuadratic00 (F : ℝ → ℝ → ℝ) : ℝ :=
  F 1 0

/-- Off-diagonal entry extracted by exact polarization. -/
def intrinsicBinaryQuadratic02 (F : ℝ → ℝ → ℝ) : ℝ :=
  (F 1 1 - F 1 0 - F 0 1) / 2

/-- Trailing diagonal entry extracted from a binary quadratic. -/
def intrinsicBinaryQuadratic22 (F : ℝ → ℝ → ℝ) : ℝ :=
  F 0 1

/-- The sharp three-scalar PSD gate for a binary quadratic. -/
def IntrinsicBinaryQuadraticPSD (F : ℝ → ℝ → ℝ) : Prop :=
  0 ≤ intrinsicBinaryQuadratic00 F ∧
    0 ≤ intrinsicBinaryQuadratic22 F ∧
    intrinsicBinaryQuadratic02 F ^ 2 ≤
      intrinsicBinaryQuadratic00 F * intrinsicBinaryQuadratic22 F

/-- Once a function has its exact homogeneous quadratic expansion, its
universal nonnegativity is equivalent to the three scalar Gram inequalities. -/
theorem intrinsicBinaryQuadratic_nonneg_iff_of_expansion
    (F : ℝ → ℝ → ℝ)
    (hexpansion : ∀ c d : ℝ,
      F c d = intrinsicBinaryQuadratic00 F * c ^ 2 +
        2 * intrinsicBinaryQuadratic02 F * c * d +
        intrinsicBinaryQuadratic22 F * d ^ 2) :
    (∀ c d : ℝ, 0 ≤ F c d) ↔ IntrinsicBinaryQuadraticPSD F := by
  have hcriterion := real_quadratic_pencil_nonneg_iff
    (intrinsicBinaryQuadratic00 F)
    (intrinsicBinaryQuadratic22 F)
    (intrinsicBinaryQuadratic02 F)
  constructor
  · intro hnonneg
    apply hcriterion.mp
    intro c d
    rw [← hexpansion c d]
    exact hnonneg c d
  · intro hpsd c d
    rw [hexpansion c d]
    exact hcriterion.mpr hpsd c d

/-! ## Exact Gram expansions of the four fixed controls -/

private theorem control0_expansion (c d : ℝ) :
    factorTwoIntrinsicBoundaryControl0 c d =
      intrinsicBinaryQuadratic00 factorTwoIntrinsicBoundaryControl0 * c ^ 2 +
        2 * intrinsicBinaryQuadratic02
          factorTwoIntrinsicBoundaryControl0 * c * d +
        intrinsicBinaryQuadratic22
          factorTwoIntrinsicBoundaryControl0 * d ^ 2 := by
  unfold intrinsicBinaryQuadratic00 intrinsicBinaryQuadratic02
    intrinsicBinaryQuadratic22
    factorTwoIntrinsicBoundaryControl0
    factorTwoIntrinsicBoundaryPower0
    factorTwoIntrinsicOddPhaseQuadratic
  ring

private theorem control1_expansion (c d : ℝ) :
    factorTwoIntrinsicBoundaryControl1 c d =
      intrinsicBinaryQuadratic00 factorTwoIntrinsicBoundaryControl1 * c ^ 2 +
        2 * intrinsicBinaryQuadratic02
          factorTwoIntrinsicBoundaryControl1 * c * d +
        intrinsicBinaryQuadratic22
          factorTwoIntrinsicBoundaryControl1 * d ^ 2 := by
  unfold intrinsicBinaryQuadratic00 intrinsicBinaryQuadratic02
    intrinsicBinaryQuadratic22
    factorTwoIntrinsicBoundaryControl1
    factorTwoIntrinsicBoundaryPower0 factorTwoIntrinsicBoundaryPower1
    factorTwoIntrinsicOddPhaseQuadratic
    factorTwoIntrinsicOddDirectionQuadratic
    factorTwoIntrinsicAdjugateCoefficient0
    factorTwoIntrinsicEvenAdjugateCoupling
    factorTwoIntrinsicAlternatingRow0 factorTwoIntrinsicAlternatingRow2
  ring

private theorem control2_expansion (c d : ℝ) :
    factorTwoIntrinsicBoundaryControl2 c d =
      intrinsicBinaryQuadratic00 factorTwoIntrinsicBoundaryControl2 * c ^ 2 +
        2 * intrinsicBinaryQuadratic02
          factorTwoIntrinsicBoundaryControl2 * c * d +
        intrinsicBinaryQuadratic22
          factorTwoIntrinsicBoundaryControl2 * d ^ 2 := by
  unfold intrinsicBinaryQuadratic00 intrinsicBinaryQuadratic02
    intrinsicBinaryQuadratic22
    factorTwoIntrinsicBoundaryControl2
    factorTwoIntrinsicBoundaryPower0 factorTwoIntrinsicBoundaryPower1
    factorTwoIntrinsicBoundaryPower2
    factorTwoIntrinsicOddPhaseQuadratic
    factorTwoIntrinsicOddDirectionQuadratic
    factorTwoIntrinsicAdjugateCoefficient0
    factorTwoIntrinsicAdjugateCoefficient1
    factorTwoIntrinsicEvenAdjugateCoupling
    factorTwoIntrinsicAlternatingRow0 factorTwoIntrinsicAlternatingRow2
  ring

private theorem control3_expansion (c d : ℝ) :
    factorTwoIntrinsicBoundaryControl3 c d =
      intrinsicBinaryQuadratic00 factorTwoIntrinsicBoundaryControl3 * c ^ 2 +
        2 * intrinsicBinaryQuadratic02
          factorTwoIntrinsicBoundaryControl3 * c * d +
        intrinsicBinaryQuadratic22
          factorTwoIntrinsicBoundaryControl3 * d ^ 2 := by
  unfold intrinsicBinaryQuadratic00 intrinsicBinaryQuadratic02
    intrinsicBinaryQuadratic22
    factorTwoIntrinsicBoundaryControl3
    factorTwoIntrinsicBoundaryPower0 factorTwoIntrinsicBoundaryPower1
    factorTwoIntrinsicBoundaryPower2 factorTwoIntrinsicBoundaryPower3
    factorTwoIntrinsicOddPhaseQuadratic
    factorTwoIntrinsicOddDirectionQuadratic
    factorTwoIntrinsicAdjugateCoefficient0
    factorTwoIntrinsicAdjugateCoefficient1
    factorTwoIntrinsicEvenAdjugateCoupling
    factorTwoIntrinsicAlternatingRow0 factorTwoIntrinsicAlternatingRow2
  ring

theorem factorTwoIntrinsicBoundaryControl0_nonneg_iff :
    (∀ c d : ℝ, 0 ≤ factorTwoIntrinsicBoundaryControl0 c d) ↔
      IntrinsicBinaryQuadraticPSD factorTwoIntrinsicBoundaryControl0 :=
  intrinsicBinaryQuadratic_nonneg_iff_of_expansion
    factorTwoIntrinsicBoundaryControl0 control0_expansion

theorem factorTwoIntrinsicBoundaryControl1_nonneg_iff :
    (∀ c d : ℝ, 0 ≤ factorTwoIntrinsicBoundaryControl1 c d) ↔
      IntrinsicBinaryQuadraticPSD factorTwoIntrinsicBoundaryControl1 :=
  intrinsicBinaryQuadratic_nonneg_iff_of_expansion
    factorTwoIntrinsicBoundaryControl1 control1_expansion

theorem factorTwoIntrinsicBoundaryControl2_nonneg_iff :
    (∀ c d : ℝ, 0 ≤ factorTwoIntrinsicBoundaryControl2 c d) ↔
      IntrinsicBinaryQuadraticPSD factorTwoIntrinsicBoundaryControl2 :=
  intrinsicBinaryQuadratic_nonneg_iff_of_expansion
    factorTwoIntrinsicBoundaryControl2 control2_expansion

theorem factorTwoIntrinsicBoundaryControl3_nonneg_iff :
    (∀ c d : ℝ, 0 ≤ factorTwoIntrinsicBoundaryControl3 c d) ↔
      IntrinsicBinaryQuadraticPSD factorTwoIntrinsicBoundaryControl3 :=
  intrinsicBinaryQuadratic_nonneg_iff_of_expansion
    factorTwoIntrinsicBoundaryControl3 control3_expansion

/-! ## Endpoint controls and inward monotonicity -/

/-- The first endpoint control is nonnegative from the two corresponding
decoupled endpoint factors. -/
theorem factorTwoIntrinsicBoundaryControl0_nonneg_of_endpoint
    (c d : ℝ)
    (heven : 0 ≤ factorTwoIntrinsicEvenPhaseDet 1)
    (hodd : 0 ≤ factorTwoIntrinsicOddPhaseQuadratic 1 c d) :
    0 ≤ factorTwoIntrinsicBoundaryControl0 c d := by
  rw [factorTwoIntrinsicBoundaryControl0_eq_endpoint]
  exact mul_nonneg heven hodd

/-- The last endpoint control is nonnegative from the two corresponding
decoupled endpoint factors. -/
theorem factorTwoIntrinsicBoundaryControl3_nonneg_of_endpoint
    (c d : ℝ)
    (heven : 0 ≤ factorTwoIntrinsicEvenPhaseDet (-1))
    (hodd : 0 ≤ factorTwoIntrinsicOddPhaseQuadratic (-1) c d) :
    0 ≤ factorTwoIntrinsicBoundaryControl3 c d := by
  rw [factorTwoIntrinsicBoundaryControl3_eq_endpoint]
  exact mul_nonneg heven hodd

/-- The three fixed differences between successive Bernstein controls. -/
def factorTwoIntrinsicBoundaryControlStep01 (c d : ℝ) : ℝ :=
  factorTwoIntrinsicBoundaryControl1 c d -
    factorTwoIntrinsicBoundaryControl0 c d

def factorTwoIntrinsicBoundaryControlStep12 (c d : ℝ) : ℝ :=
  factorTwoIntrinsicBoundaryControl2 c d -
    factorTwoIntrinsicBoundaryControl1 c d

def factorTwoIntrinsicBoundaryControlStep23 (c d : ℝ) : ℝ :=
  factorTwoIntrinsicBoundaryControl3 c d -
    factorTwoIntrinsicBoundaryControl2 c d

/-- A nonnegative endpoint control and nonnegative inward Bernstein steps
give all four control inequalities.  This is the matrix-monotonicity form of
the fixed analytic obligation. -/
theorem factorTwoIntrinsicBoundaryControls_nonneg_of_steps
    (c d : ℝ)
    (h0 : 0 ≤ factorTwoIntrinsicBoundaryControl0 c d)
    (h01 : 0 ≤ factorTwoIntrinsicBoundaryControlStep01 c d)
    (h12 : 0 ≤ factorTwoIntrinsicBoundaryControlStep12 c d)
    (h23 : 0 ≤ factorTwoIntrinsicBoundaryControlStep23 c d) :
    0 ≤ factorTwoIntrinsicBoundaryControl0 c d ∧
      0 ≤ factorTwoIntrinsicBoundaryControl1 c d ∧
      0 ≤ factorTwoIntrinsicBoundaryControl2 c d ∧
      0 ≤ factorTwoIntrinsicBoundaryControl3 c d := by
  unfold factorTwoIntrinsicBoundaryControlStep01 at h01
  unfold factorTwoIntrinsicBoundaryControlStep12 at h12
  unfold factorTwoIntrinsicBoundaryControlStep23 at h23
  constructor
  · exact h0
  constructor
  · linarith
  constructor <;> linarith

/-! ## Uniform four-mode closure from the fixed scalar gates -/

/-- The four exact `2 x 2` Gram gates are sufficient for all four controls,
and hence for the complete intrinsic low phase throughout the disk. -/
theorem factorTwoEndpointChannelPhase_intrinsicLow_nonneg_of_controlPSD
    (c0 c2 c1 c3 a b : ℝ)
    (hab : a ^ 2 + b ^ 2 ≤ 1)
    (hplus00 : 0 < factorTwoStructuralPhaseLow00 1)
    (hplusDet : 0 < factorTwoIntrinsicEvenPhaseDet 1)
    (hminus00 : 0 < factorTwoStructuralPhaseLow00 (-1))
    (hminusDet : 0 < factorTwoIntrinsicEvenPhaseDet (-1))
    (hcontrol0 :
      IntrinsicBinaryQuadraticPSD factorTwoIntrinsicBoundaryControl0)
    (hcontrol1 :
      IntrinsicBinaryQuadraticPSD factorTwoIntrinsicBoundaryControl1)
    (hcontrol2 :
      IntrinsicBinaryQuadraticPSD factorTwoIntrinsicBoundaryControl2)
    (hcontrol3 :
      IntrinsicBinaryQuadraticPSD factorTwoIntrinsicBoundaryControl3) :
    0 ≤ factorTwoEndpointChannelPhase
      (factorTwoEvenStructuralLowProfile c0 c2)
      (factorTwoOddStructuralLowProfile c1 c3) a b := by
  exact factorTwoEndpointChannelPhase_intrinsicLow_nonneg_of_controls
    c0 c2 c1 c3 a b hab hplus00 hplusDet hminus00 hminusDet
      (factorTwoIntrinsicBoundaryControl0_nonneg_iff.mpr hcontrol0 c1 c3)
      (factorTwoIntrinsicBoundaryControl1_nonneg_iff.mpr hcontrol1 c1 c3)
      (factorTwoIntrinsicBoundaryControl2_nonneg_iff.mpr hcontrol2 c1 c3)
      (factorTwoIntrinsicBoundaryControl3_nonneg_iff.mpr hcontrol3 c1 c3)

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowControlsPositive

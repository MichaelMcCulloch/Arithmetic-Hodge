import ArithmeticHodge.Analysis.YoshidaPointwiseParityCore

set_option autoImplicit false

open Complex Real Set
open scoped ContDiff

namespace ArithmeticHodge.Analysis.YoshidaEndpointEvenBoundaryResidual

open ArithmeticHodge.Analysis
open YoshidaPointwiseParityCore

noncomputable section

/-- The clipped profile equal to one on the source interval and zero
outside. -/
def yoshidaClippedOne (a : ℝ) : YoshidaClippedSmooth a := by
  refine ⟨fun x ↦ if x ∈ Icc (-a) a then 1 else 0, ?_, ?_⟩
  · exact (contDiffOn_const : ContDiffOn ℝ ∞
      (fun _ : ℝ ↦ (1 : ℂ)) (Icc (-a) a)).congr
      (fun x hx ↦ by simp [hx])
  · intro x hx
    simp [hx]

/-- The clipped unit profile has the global constant-one periodic
extension. -/
theorem yoshidaClippedOne_mem_periodicCore (a : ℝ) :
    yoshidaClippedOne a ∈ yoshidaClippedPeriodicCoreSubmodule a := by
  refine ⟨fun _ ↦ 1, contDiff_const, ?_, ?_⟩
  · intro x
    rfl
  · intro x hx
    change (1 : ℂ) = if x ∈ Icc (-a) a then 1 else 0
    simp [hx]

/-- The unit clipped profile as an element of the periodic source core. -/
def periodicCoreOne (a : ℝ) : YoshidaClippedPeriodicCore a :=
  ⟨yoshidaClippedOne a, yoshidaClippedOne_mem_periodicCore a⟩

@[simp] theorem periodicCoreOne_apply_of_mem {a x : ℝ}
    (hx : x ∈ Icc (-a) a) :
    (((periodicCoreOne a : YoshidaClippedPeriodicCore a) :
      YoshidaClippedSmooth a) : ℝ → ℂ) x = 1 := by
  change (if x ∈ Icc (-a) a then (1 : ℂ) else 0) = 1
  rw [if_pos hx]

theorem periodicCoreOne_even (a : ℝ) : Function.Even
    ((((periodicCoreOne a : YoshidaClippedPeriodicCore a) :
      YoshidaClippedSmooth a) : ℝ → ℂ)) := by
  intro x
  change (if -x ∈ Icc (-a) a then (1 : ℂ) else 0) =
    if x ∈ Icc (-a) a then 1 else 0
  have hmem : -x ∈ Icc (-a) a ↔ x ∈ Icc (-a) a := by
    constructor
    · intro hx
      exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
    · intro hx
      exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
  by_cases hx : -x ∈ Icc (-a) a
  · simp [hx, hmem.mp hx]
  · have hx' : x ∉ Icc (-a) a := by
      intro h
      exact hx (hmem.mpr h)
    simp [hx, hx']

/-- The constant part matching an even periodic profile's identified
endpoint value. -/
def evenBoundaryConstantPart {a : ℝ}
    (f : yoshidaPointwiseEvenPeriodicCoreSubmodule a) :
    YoshidaClippedPeriodicCore a :=
  (((f.1 : YoshidaClippedPeriodicCore a) : YoshidaClippedSmooth a) a) •
    periodicCoreOne a

/-- Subtract the identified endpoint value, producing a periodic residual
with zero traces. -/
def evenBoundaryResidual {a : ℝ}
    (f : yoshidaPointwiseEvenPeriodicCoreSubmodule a) :
    YoshidaClippedPeriodicCore a :=
  f.1 - evenBoundaryConstantPart f

theorem evenBoundaryResidual_pointwise_even {a : ℝ}
    (f : yoshidaPointwiseEvenPeriodicCoreSubmodule a) : Function.Even
      ((((evenBoundaryResidual f : YoshidaClippedPeriodicCore a) :
        YoshidaClippedSmooth a) : ℝ → ℂ)) := by
  intro x
  change
    (((f.1 : YoshidaClippedPeriodicCore a) : YoshidaClippedSmooth a) (-x) -
      (((f.1 : YoshidaClippedPeriodicCore a) : YoshidaClippedSmooth a) a) *
        (((periodicCoreOne a : YoshidaClippedPeriodicCore a) :
          YoshidaClippedSmooth a) (-x))) =
    (((f.1 : YoshidaClippedPeriodicCore a) : YoshidaClippedSmooth a) x -
      (((f.1 : YoshidaClippedPeriodicCore a) : YoshidaClippedSmooth a) a) *
        (((periodicCoreOne a : YoshidaClippedPeriodicCore a) :
          YoshidaClippedSmooth a) x))
  rw [f.property x, periodicCoreOne_even a x]

/-- Boundary residual as a member of the literal even carrier. -/
def pointwiseEvenBoundaryResidual {a : ℝ}
    (f : yoshidaPointwiseEvenPeriodicCoreSubmodule a) :
    yoshidaPointwiseEvenPeriodicCoreSubmodule a :=
  ⟨evenBoundaryResidual f, evenBoundaryResidual_pointwise_even f⟩

theorem evenBoundaryResidual_endpoints_zero {a : ℝ} (ha : 0 < a)
    (f : yoshidaPointwiseEvenPeriodicCoreSubmodule a) :
    (((evenBoundaryResidual f : YoshidaClippedPeriodicCore a) :
      YoshidaClippedSmooth a) (-a) = 0) ∧
    (((evenBoundaryResidual f : YoshidaClippedPeriodicCore a) :
      YoshidaClippedSmooth a) a = 0) := by
  have hneg :
      (((f.1 : YoshidaClippedPeriodicCore a) : YoshidaClippedSmooth a) (-a)) =
        (((f.1 : YoshidaClippedPeriodicCore a) : YoshidaClippedSmooth a) a) :=
    f.property a
  have hnegMem : -a ∈ Icc (-a) a := ⟨le_rfl, by linarith⟩
  have hposMem : a ∈ Icc (-a) a := ⟨by linarith, le_rfl⟩
  constructor
  · change
      (((f.1 : YoshidaClippedPeriodicCore a) : YoshidaClippedSmooth a) (-a)) -
        (((f.1 : YoshidaClippedPeriodicCore a) : YoshidaClippedSmooth a) a) *
          (((periodicCoreOne a : YoshidaClippedPeriodicCore a) :
            YoshidaClippedSmooth a) (-a)) = 0
    rw [periodicCoreOne_apply_of_mem hnegMem, hneg]
    ring
  · change
      (((f.1 : YoshidaClippedPeriodicCore a) : YoshidaClippedSmooth a) a) -
        (((f.1 : YoshidaClippedPeriodicCore a) : YoshidaClippedSmooth a) a) *
          (((periodicCoreOne a : YoshidaClippedPeriodicCore a) :
            YoshidaClippedSmooth a) a) = 0
    rw [periodicCoreOne_apply_of_mem hposMem]
    ring

/-- Exact endpoint-constant plus zero-trace residual decomposition. -/
theorem evenBoundaryConstantPart_add_residual {a : ℝ}
    (f : yoshidaPointwiseEvenPeriodicCoreSubmodule a) :
    evenBoundaryConstantPart f + evenBoundaryResidual f = f.1 := by
  unfold evenBoundaryResidual
  abel

theorem evenBoundaryResidual_im_zero {a : ℝ}
    (f : yoshidaPointwiseEvenPeriodicCoreSubmodule a)
    (hf_real : ∀ x : ℝ,
      ((((f.1 : YoshidaClippedPeriodicCore a) :
        YoshidaClippedSmooth a) : ℝ → ℂ) x).im = 0) (x : ℝ) :
    ((((evenBoundaryResidual f : YoshidaClippedPeriodicCore a) :
      YoshidaClippedSmooth a) : ℝ → ℂ) x).im = 0 := by
  have honeIm :
      ((((periodicCoreOne a : YoshidaClippedPeriodicCore a) :
        YoshidaClippedSmooth a) : ℝ → ℂ) x).im = 0 := by
    change (if x ∈ Icc (-a) a then (1 : ℂ) else 0).im = 0
    split <;> simp
  change
    ((((f.1 : YoshidaClippedPeriodicCore a) : YoshidaClippedSmooth a) x) -
      (((f.1 : YoshidaClippedPeriodicCore a) : YoshidaClippedSmooth a) a) *
        (((periodicCoreOne a : YoshidaClippedPeriodicCore a) :
          YoshidaClippedSmooth a) x)).im = 0
  rw [Complex.sub_im, Complex.mul_im, hf_real x, hf_real a]
  rw [honeIm]
  ring

end

end ArithmeticHodge.Analysis.YoshidaEndpointEvenBoundaryResidual

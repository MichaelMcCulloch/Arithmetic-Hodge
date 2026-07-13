import ArithmeticHodge.Analysis.YoshidaClippedParityOrthogonality
import ArithmeticHodge.Analysis.YoshidaPointwiseOddPeriodicCore

set_option autoImplicit false

open Complex Real Set

namespace ArithmeticHodge.Analysis.YoshidaPointwiseParityCore

open ArithmeticHodge.Analysis
open YoshidaPointwiseOddPeriodicCore

noncomputable section

/-- Structural periodic even carrier, defined by literal pointwise evenness. -/
def yoshidaPointwiseEvenPeriodicCoreSubmodule (a : ℝ) :
    Submodule ℂ (YoshidaClippedPeriodicCore a) where
  carrier := {f | Function.Even
    (((f : YoshidaClippedPeriodicCore a) : YoshidaClippedSmooth a) : ℝ → ℂ)}
  zero_mem' := by
    intro x
    simp
  add_mem' := by
    intro f g hf hg x
    simp only [Submodule.coe_add, Pi.add_apply]
    rw [hf x, hg x]
  smul_mem' := by
    intro c f hf x
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
    rw [hf x]

/-- Pointwise reflection in the clipped smooth carrier. -/
def clippedReflection {a : ℝ} (f : YoshidaClippedSmooth a) :
    YoshidaClippedSmooth a := by
  refine ⟨fun x ↦ f (-x), ?_, ?_⟩
  · simpa only [Function.comp_def] using
      f.property.1.comp contDiff_neg.contDiffOn (by
        intro x hx
        exact ⟨by linarith [hx.2], by linarith [hx.1]⟩)
  · intro x hx
    apply yoshidaClippedSmooth_eq_zero_outside f
    intro hneg
    apply hx
    exact ⟨by linarith [hneg.2], by linarith [hneg.1]⟩

/-- Reflection preserves the periodic smooth source core. -/
theorem clippedReflection_mem_periodicCore {a : ℝ}
    (f : YoshidaClippedPeriodicCore a) :
    clippedReflection (f : YoshidaClippedSmooth a) ∈
      yoshidaClippedPeriodicCoreSubmodule a := by
  rcases f.property with ⟨F, hFdiff, hFperiodic, hFeq⟩
  refine ⟨fun x ↦ F (-x), hFdiff.comp contDiff_neg, ?_, ?_⟩
  · intro x
    calc
      F (-(x + 2 * a)) = F (-(x + 2 * a) + 2 * a) :=
        (hFperiodic (-(x + 2 * a))).symm
      _ = F (-x) := by ring_nf
  · intro x hx
    change F (-x) = (f : YoshidaClippedSmooth a) (-x)
    apply hFeq
    exact ⟨by linarith [hx.2], by linarith [hx.1]⟩

/-- Reflection inside the periodic source core. -/
def periodicCoreReflection {a : ℝ} (f : YoshidaClippedPeriodicCore a) :
    YoshidaClippedPeriodicCore a :=
  ⟨clippedReflection (f : YoshidaClippedSmooth a),
    clippedReflection_mem_periodicCore f⟩

@[simp] theorem periodicCoreReflection_apply {a x : ℝ}
    (f : YoshidaClippedPeriodicCore a) :
    (((periodicCoreReflection f : YoshidaClippedPeriodicCore a) :
      YoshidaClippedSmooth a) : ℝ → ℂ) x =
      ((f : YoshidaClippedSmooth a) : ℝ → ℂ) (-x) := rfl

/-- Canonical pointwise even part without importing a spectral certificate
layer. -/
def periodicCoreEvenPart {a : ℝ} (f : YoshidaClippedPeriodicCore a) :
    YoshidaClippedPeriodicCore a :=
  (2 : ℂ)⁻¹ • (f + periodicCoreReflection f)

/-- Canonical pointwise odd part without importing a spectral certificate
layer. -/
def periodicCoreOddPart {a : ℝ} (f : YoshidaClippedPeriodicCore a) :
    YoshidaClippedPeriodicCore a :=
  (2 : ℂ)⁻¹ • (f - periodicCoreReflection f)

@[simp] theorem periodicCoreEvenPart_apply {a x : ℝ}
    (f : YoshidaClippedPeriodicCore a) :
    (((periodicCoreEvenPart f : YoshidaClippedPeriodicCore a) :
      YoshidaClippedSmooth a) : ℝ → ℂ) x =
      (2 : ℂ)⁻¹ *
        (((f : YoshidaClippedSmooth a) : ℝ → ℂ) x +
          ((f : YoshidaClippedSmooth a) : ℝ → ℂ) (-x)) := rfl

@[simp] theorem periodicCoreOddPart_apply {a x : ℝ}
    (f : YoshidaClippedPeriodicCore a) :
    (((periodicCoreOddPart f : YoshidaClippedPeriodicCore a) :
      YoshidaClippedSmooth a) : ℝ → ℂ) x =
      (2 : ℂ)⁻¹ *
        (((f : YoshidaClippedSmooth a) : ℝ → ℂ) x -
          ((f : YoshidaClippedSmooth a) : ℝ → ℂ) (-x)) := rfl

theorem periodicCoreEvenPart_pointwise_even {a : ℝ}
    (f : YoshidaClippedPeriodicCore a) : Function.Even
      ((((periodicCoreEvenPart f : YoshidaClippedPeriodicCore a) :
        YoshidaClippedSmooth a) : ℝ → ℂ)) := by
  intro x
  simp only [periodicCoreEvenPart_apply, neg_neg]
  ring

theorem periodicCoreOddPart_pointwise_odd {a : ℝ}
    (f : YoshidaClippedPeriodicCore a) : Function.Odd
      ((((periodicCoreOddPart f : YoshidaClippedPeriodicCore a) :
        YoshidaClippedSmooth a) : ℝ → ℂ)) := by
  intro x
  simp only [periodicCoreOddPart_apply, neg_neg]
  ring

/-- Canonical even part as an element of the structural even carrier. -/
def pointwiseEvenPart {a : ℝ} (f : YoshidaClippedPeriodicCore a) :
    yoshidaPointwiseEvenPeriodicCoreSubmodule a :=
  ⟨periodicCoreEvenPart f, periodicCoreEvenPart_pointwise_even f⟩

/-- Canonical odd part as an element of the structural odd carrier. -/
def pointwiseOddPart {a : ℝ} (f : YoshidaClippedPeriodicCore a) :
    yoshidaPointwiseOddPeriodicCoreSubmodule a :=
  ⟨periodicCoreOddPart f, periodicCoreOddPart_pointwise_odd f⟩

/-- Exact structural parity decomposition. -/
theorem periodicCoreEvenPart_add_oddPart {a : ℝ}
    (f : YoshidaClippedPeriodicCore a) :
    periodicCoreEvenPart f + periodicCoreOddPart f = f := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  simp only [Submodule.coe_add, Pi.add_apply,
    periodicCoreEvenPart_apply, periodicCoreOddPart_apply]
  ring

/-- The production diagonal splits exactly across the two structural parity
parts. -/
theorem yoshidaClippedLocalCriticalForm_self_eq_even_add_odd
    {a : ℝ} (ha : 0 < a) (f : YoshidaClippedPeriodicCore a) :
    yoshidaClippedLocalCriticalForm a ha
        (f : YoshidaClippedSmooth a) (f : YoshidaClippedSmooth a) =
      yoshidaClippedLocalCriticalForm a ha
          ((periodicCoreEvenPart f : YoshidaClippedPeriodicCore a) :
            YoshidaClippedSmooth a)
          ((periodicCoreEvenPart f : YoshidaClippedPeriodicCore a) :
            YoshidaClippedSmooth a) +
        yoshidaClippedLocalCriticalForm a ha
          ((periodicCoreOddPart f : YoshidaClippedPeriodicCore a) :
            YoshidaClippedSmooth a)
          ((periodicCoreOddPart f : YoshidaClippedPeriodicCore a) :
            YoshidaClippedSmooth a) := by
  let B := yoshidaClippedLocalCriticalForm a ha
  let e : YoshidaClippedSmooth a :=
    ((periodicCoreEvenPart f : YoshidaClippedPeriodicCore a) :
      YoshidaClippedSmooth a)
  let o : YoshidaClippedSmooth a :=
    ((periodicCoreOddPart f : YoshidaClippedPeriodicCore a) :
      YoshidaClippedSmooth a)
  have hdecomp : (f : YoshidaClippedSmooth a) = e + o := by
    have hsmooth := congrArg
      (fun g : YoshidaClippedPeriodicCore a ↦
        (g : YoshidaClippedSmooth a))
      (periodicCoreEvenPart_add_oddPart f)
    simpa only [e, o, Submodule.coe_add] using hsmooth.symm
  have heven : ∀ x : ℝ, e (-x) = e x :=
    periodicCoreEvenPart_pointwise_even f
  have hodd : ∀ x : ℝ, o (-x) = -o x :=
    periodicCoreOddPart_pointwise_odd f
  have hcrossEO : B e o = 0 :=
    yoshidaClippedLocalCriticalForm_even_odd_eq_zero ha e o heven hodd
  have hcrossOE : B o e = 0 :=
    yoshidaClippedLocalCriticalForm_odd_even_eq_zero ha o e hodd heven
  change B (f : YoshidaClippedSmooth a) (f : YoshidaClippedSmooth a) =
    B e e + B o o
  rw [hdecomp, map_add]
  simp only [map_add]
  change (B e e + B o e) + (B e o + B o o) = B e e + B o o
  rw [hcrossEO, hcrossOE]
  ring

/-- Nonnegativity on the two literal parity carriers recombines into
nonnegativity on the complete periodic source core. -/
theorem yoshidaClippedLocalCriticalForm_re_nonneg_of_pointwise_parity
    {a : ℝ} (ha : 0 < a)
    (hEven : ∀ g : yoshidaPointwiseEvenPeriodicCoreSubmodule a,
      0 ≤ (yoshidaClippedLocalCriticalForm a ha
        (g.1 : YoshidaClippedSmooth a)
        (g.1 : YoshidaClippedSmooth a)).re)
    (hOdd : ∀ g : yoshidaPointwiseOddPeriodicCoreSubmodule a,
      0 ≤ (yoshidaClippedLocalCriticalForm a ha
        (g.1 : YoshidaClippedSmooth a)
        (g.1 : YoshidaClippedSmooth a)).re)
    (f : YoshidaClippedPeriodicCore a) :
    0 ≤ (yoshidaClippedLocalCriticalForm a ha
      (f : YoshidaClippedSmooth a) (f : YoshidaClippedSmooth a)).re := by
  have hsplit := yoshidaClippedLocalCriticalForm_self_eq_even_add_odd ha f
  have hsplitRe := congrArg Complex.re hsplit
  rw [Complex.add_re] at hsplitRe
  rw [hsplitRe]
  exact add_nonneg (hEven (pointwiseEvenPart f))
    (hOdd (pointwiseOddPart f))

end

end ArithmeticHodge.Analysis.YoshidaPointwiseParityCore

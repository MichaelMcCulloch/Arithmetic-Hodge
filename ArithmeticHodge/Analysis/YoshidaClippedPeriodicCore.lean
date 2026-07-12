import ArithmeticHodge.Analysis.YoshidaClippedCircleBridge

set_option autoImplicit false

open Complex Real Set
open scoped ContDiff
open ArithmeticHodge.Analysis.YoshidaClippedCircleBridge

namespace ArithmeticHodge.Analysis

noncomputable section

/-!
# The periodic source core of Yoshida's clipped carrier

The clipped carrier only asks for smoothness on `[-a, a]`; it does not make
an arbitrary clipped function periodic.  This module singles out the
source-faithful submodule whose members are restrictions of globally smooth,
`2 * a`-periodic functions.  Its Fourier-tail submodules are literal comaps
of the circle tails through the established clipped-to-circle coordinate map.
-/

/-- A clipped function admits a globally smooth, `2 * a`-periodic source
representative agreeing with it throughout the closed clipping interval. -/
def HasPeriodicSmoothExtension (a : ℝ) (f : YoshidaClippedSmooth a) : Prop :=
  ∃ F : ℝ → ℂ,
    ContDiff ℝ ∞ F ∧
      Function.Periodic F (2 * a) ∧
        Set.EqOn F (f : ℝ → ℂ) (Set.Icc (-a) a)

/-- The source-faithful periodic submodule of `YoshidaClippedSmooth a`. -/
def yoshidaClippedPeriodicCoreSubmodule (a : ℝ) :
    Submodule ℂ (YoshidaClippedSmooth a) where
  carrier := HasPeriodicSmoothExtension a
  zero_mem' := by
    refine ⟨fun _ ↦ 0, contDiff_const, ?_, ?_⟩
    · intro x
      rfl
    · intro x hx
      rfl
  add_mem' := by
    rintro f g ⟨F, hFsmooth, hFperiodic, hF⟩
      ⟨G, hGsmooth, hGperiodic, hG⟩
    refine ⟨fun x ↦ F x + G x, hFsmooth.add hGsmooth, ?_, ?_⟩
    · intro x
      change F (x + 2 * a) + G (x + 2 * a) = F x + G x
      rw [hFperiodic x, hGperiodic x]
    · intro x hx
      simp only [Submodule.coe_add, Pi.add_apply]
      rw [hF hx, hG hx]
  smul_mem' := by
    rintro c f ⟨F, hFsmooth, hFperiodic, hF⟩
    refine ⟨fun x ↦ c * F x, contDiff_const.mul hFsmooth, ?_, ?_⟩
    · intro x
      change c * F (x + 2 * a) = c * F x
      rw [hFperiodic x]
    · intro x hx
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
      rw [hF hx]

/-- The subtype of clipped functions carrying a global periodic smooth
witness. -/
abbrev YoshidaClippedPeriodicCore (a : ℝ) :=
  yoshidaClippedPeriodicCoreSubmodule a

theorem mem_yoshidaClippedPeriodicCore_iff
    {a : ℝ} (f : YoshidaClippedSmooth a) :
    f ∈ yoshidaClippedPeriodicCoreSubmodule a ↔
      HasPeriodicSmoothExtension a f :=
  Iff.rfl

@[simp] theorem zero_mem_yoshidaClippedPeriodicCore (a : ℝ) :
    (0 : YoshidaClippedSmooth a) ∈
      yoshidaClippedPeriodicCoreSubmodule a :=
  (yoshidaClippedPeriodicCoreSubmodule a).zero_mem

theorem add_mem_yoshidaClippedPeriodicCore
    {a : ℝ} {f g : YoshidaClippedSmooth a}
    (hf : f ∈ yoshidaClippedPeriodicCoreSubmodule a)
    (hg : g ∈ yoshidaClippedPeriodicCoreSubmodule a) :
    f + g ∈ yoshidaClippedPeriodicCoreSubmodule a :=
  (yoshidaClippedPeriodicCoreSubmodule a).add_mem hf hg

theorem smul_mem_yoshidaClippedPeriodicCore
    {a : ℝ} (c : ℂ) {f : YoshidaClippedSmooth a}
    (hf : f ∈ yoshidaClippedPeriodicCoreSubmodule a) :
    c • f ∈ yoshidaClippedPeriodicCoreSubmodule a :=
  (yoshidaClippedPeriodicCoreSubmodule a).smul_mem c hf

/-- A chosen global smooth periodic representative of a periodic-core
element.  The following three theorems expose exactly the witness guarantees
and no properties outside them. -/
def periodicExtension {a : ℝ} (f : YoshidaClippedPeriodicCore a) : ℝ → ℂ :=
  Classical.choose f.property

theorem periodicExtension_contDiff
    {a : ℝ} (f : YoshidaClippedPeriodicCore a) :
    ContDiff ℝ ∞ (periodicExtension f) :=
  (Classical.choose_spec f.property).1

theorem periodicExtension_periodic
    {a : ℝ} (f : YoshidaClippedPeriodicCore a) :
    Function.Periodic (periodicExtension f) (2 * a) :=
  (Classical.choose_spec f.property).2.1

theorem periodicExtension_eqOn
    {a : ℝ} (f : YoshidaClippedPeriodicCore a) :
    Set.EqOn (periodicExtension f)
      (f : YoshidaClippedSmooth a) (Set.Icc (-a) a) :=
  (Classical.choose_spec f.property).2.2

@[simp] theorem periodicExtension_apply_of_mem
    {a x : ℝ} (f : YoshidaClippedPeriodicCore a)
    (hx : x ∈ Set.Icc (-a) a) :
    periodicExtension f x = (f : YoshidaClippedSmooth a) x :=
  periodicExtension_eqOn f hx

/-- The explicit global exponential whose restriction is Yoshida's clipped
exponential. -/
def yoshidaPeriodicExponential (a : ℝ) (n : ℤ) (x : ℝ) : ℂ :=
  ((Real.sqrt (2 * a))⁻¹ : ℂ) *
    Complex.exp
      (Real.pi * Complex.I * (n : ℂ) * (x : ℂ) / (a : ℝ))

theorem yoshidaPeriodicExponential_contDiff (a : ℝ) (n : ℤ) :
    ContDiff ℝ ∞ (yoshidaPeriodicExponential a n) := by
  unfold yoshidaPeriodicExponential
  have hcast : ContDiff ℝ ∞ (fun x : ℝ ↦ (x : ℂ)) :=
    Complex.ofRealCLM.contDiff
  have harg : ContDiff ℝ ∞ (fun x : ℝ ↦
      Real.pi * Complex.I * (n : ℂ) * (x : ℂ) /
        (a : ℝ)) := by
    fun_prop
  exact contDiff_const.mul (Complex.contDiff_exp.comp harg)

theorem yoshidaPeriodicExponential_periodic
    {a : ℝ} (ha : 0 < a) (n : ℤ) :
    Function.Periodic (yoshidaPeriodicExponential a n) (2 * a) := by
  intro x
  unfold yoshidaPeriodicExponential
  congr 1
  rw [show
      Real.pi * Complex.I * (n : ℂ) * ((x + 2 * a : ℝ) : ℂ) / (a : ℝ) =
        Real.pi * Complex.I * (n : ℂ) * (x : ℂ) / (a : ℝ) +
          (n : ℂ) * (2 * Real.pi * Complex.I) by
    push_cast
    field_simp [ha.ne']]
  rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I]
  simp

theorem yoshidaClippedExponential_mem_periodicCore
    {a : ℝ} (ha : 0 < a) (n : ℤ) :
    yoshidaClippedExponential a n ∈
      yoshidaClippedPeriodicCoreSubmodule a := by
  refine ⟨yoshidaPeriodicExponential a n,
    yoshidaPeriodicExponential_contDiff a n,
    yoshidaPeriodicExponential_periodic ha n, ?_⟩
  intro x hx
  rw [yoshidaClippedExponential_apply_of_mem n hx]
  rfl

theorem yoshidaClippedOddMode_mem_periodicCore
    {a : ℝ} (ha : 0 < a) (n : ℕ) :
    yoshidaClippedOddMode a n ∈
      yoshidaClippedPeriodicCoreSubmodule a := by
  unfold yoshidaClippedOddMode
  exact (yoshidaClippedPeriodicCoreSubmodule a).smul_mem _
    ((yoshidaClippedPeriodicCoreSubmodule a).sub_mem
      (yoshidaClippedExponential_mem_periodicCore ha (n : ℤ))
      (yoshidaClippedExponential_mem_periodicCore ha (-(n : ℤ))))

theorem yoshidaClippedEvenMode_mem_periodicCore
    {a : ℝ} (ha : 0 < a) (n : ℕ) :
    yoshidaClippedEvenMode a n ∈
      yoshidaClippedPeriodicCoreSubmodule a := by
  unfold yoshidaClippedEvenMode
  exact (yoshidaClippedPeriodicCoreSubmodule a).smul_mem _
    ((yoshidaClippedPeriodicCoreSubmodule a).add_mem
      (yoshidaClippedExponential_mem_periodicCore ha (n : ℤ))
      (yoshidaClippedExponential_mem_periodicCore ha (-(n : ℤ))))

theorem yoshidaClippedEvenZeroMode_mem_periodicCore
    {a : ℝ} (ha : 0 < a) :
    yoshidaClippedEvenZeroMode a ∈
      yoshidaClippedPeriodicCoreSubmodule a := by
  exact yoshidaClippedExponential_mem_periodicCore ha 0

theorem yoshidaClippedOddLowMode_mem_periodicCore
    {a : ℝ} (ha : 0 < a) (i : YoshidaOddIndex) :
    yoshidaClippedOddLowMode a i ∈
      yoshidaClippedPeriodicCoreSubmodule a :=
  yoshidaClippedOddMode_mem_periodicCore ha (i.1 + 1)

theorem yoshidaClippedEvenLowMode_mem_periodicCore
    {a : ℝ} (ha : 0 < a) (i : YoshidaEvenIndex) :
    yoshidaClippedEvenLowMode a i ∈
      yoshidaClippedPeriodicCoreSubmodule a := by
  unfold yoshidaClippedEvenLowMode
  split_ifs
  · exact yoshidaClippedEvenZeroMode_mem_periodicCore ha
  · exact yoshidaClippedEvenMode_mem_periodicCore ha i.1

/-- Circle coordinates restricted to the periodic source core. -/
def yoshidaPeriodicCoreCircleL2Linear
    {a : ℝ} (ha : 0 < a) :
    letI : Fact (0 < 2 * a) := ⟨by positivity⟩
    YoshidaClippedPeriodicCore a →ₗ[ℂ] CircleL2 (T := 2 * a) := by
  letI : Fact (0 < 2 * a) := ⟨by positivity⟩
  exact (yoshidaClippedCircleL2Linear ha).comp
    (yoshidaClippedPeriodicCoreSubmodule a).subtype

@[simp] theorem yoshidaPeriodicCoreCircleL2Linear_apply
    {a : ℝ} (ha : 0 < a) (f : YoshidaClippedPeriodicCore a) :
    letI : Fact (0 < 2 * a) := ⟨by positivity⟩
    yoshidaPeriodicCoreCircleL2Linear ha f =
      yoshidaClippedCircleL2 ha (f : YoshidaClippedSmooth a) :=
  rfl

/-- Periodic-core functions whose circle coordinate is in the odd Fourier
tail beyond cutoff `N`. -/
def yoshidaPeriodicCoreOddTailSubmodule
    {a : ℝ} (ha : 0 < a) (N : ℕ) :
    Submodule ℂ (YoshidaClippedPeriodicCore a) := by
  letI : Fact (0 < 2 * a) := ⟨by positivity⟩
  exact (oddFourierTailSubmodule (T := 2 * a) N).comap
    (yoshidaPeriodicCoreCircleL2Linear ha)

/-- Periodic-core functions whose circle coordinate is in the even Fourier
tail beyond cutoff `N`. -/
def yoshidaPeriodicCoreEvenTailSubmodule
    {a : ℝ} (ha : 0 < a) (N : ℕ) :
    Submodule ℂ (YoshidaClippedPeriodicCore a) := by
  letI : Fact (0 < 2 * a) := ⟨by positivity⟩
  exact (evenFourierTailSubmodule (T := 2 * a) N).comap
    (yoshidaPeriodicCoreCircleL2Linear ha)

@[simp] theorem mem_yoshidaPeriodicCoreOddTailSubmodule_iff
    {a : ℝ} (ha : 0 < a) (N : ℕ)
    (f : YoshidaClippedPeriodicCore a) :
    f ∈ yoshidaPeriodicCoreOddTailSubmodule ha N ↔
      letI : Fact (0 < 2 * a) := ⟨by positivity⟩
      yoshidaClippedCircleL2 ha (f : YoshidaClippedSmooth a) ∈
        oddFourierTailSubmodule (T := 2 * a) N := by
  letI : Fact (0 < 2 * a) := ⟨by positivity⟩
  rfl

@[simp] theorem mem_yoshidaPeriodicCoreEvenTailSubmodule_iff
    {a : ℝ} (ha : 0 < a) (N : ℕ)
    (f : YoshidaClippedPeriodicCore a) :
    f ∈ yoshidaPeriodicCoreEvenTailSubmodule ha N ↔
      letI : Fact (0 < 2 * a) := ⟨by positivity⟩
      yoshidaClippedCircleL2 ha (f : YoshidaClippedSmooth a) ∈
        evenFourierTailSubmodule (T := 2 * a) N := by
  letI : Fact (0 < 2 * a) := ⟨by positivity⟩
  rfl

end

end ArithmeticHodge.Analysis

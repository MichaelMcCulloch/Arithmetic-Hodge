import ArithmeticHodge.Analysis.YoshidaEvenTailLowFunctional
import ArithmeticHodge.Analysis.CenteredAddCircleFourierSymmetry

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped ComplexConjugate ContDiff InnerProductSpace

namespace ArithmeticHodge.Analysis.YoshidaEvenCorrectionReality

noncomputable section

open ArithmeticHodge.Analysis
open YoshidaEvenHomogeneousCoercivity
open YoshidaEvenTailLowFunctional
open YoshidaEvenCouplingReduction
open YoshidaEvenPairingBridge
open YoshidaEvenPairingEquation
open YoshidaCoercivityNumerics
open YoshidaWeightedTailBounds

private theorem star_I_eq_neg_I : star (Complex.I : ℂ) = -Complex.I :=
  Complex.conj_I

private theorem swap_square_difference_div_four (A B : ℝ) :
    (B * B - A * A) / 4 = -((A * A - B * B) / 4) := by
  ring

/-- Pointwise complex conjugation preserves the clipped smooth carrier. -/
def clippedConj {a : ℝ} (f : YoshidaClippedSmooth a) :
    YoshidaClippedSmooth a :=
  ⟨fun x ↦ star (f x), by
    constructor
    · simpa only [Complex.star_def] using
        Complex.conjCLE.contDiff.comp_contDiffOn f.property.1
    · intro x hx
      simp [yoshidaClippedSmooth_eq_zero_outside f hx]⟩

@[simp] theorem clippedConj_apply {a x : ℝ}
    (f : YoshidaClippedSmooth a) :
    clippedConj f x = star (f x) := rfl

@[simp] theorem clippedConj_zero {a : ℝ} :
    clippedConj (0 : YoshidaClippedSmooth a) = 0 := by
  ext x
  simp

@[simp] theorem clippedConj_add {a : ℝ}
    (f g : YoshidaClippedSmooth a) :
    clippedConj (f + g) = clippedConj f + clippedConj g := by
  ext x
  simp

@[simp] theorem clippedConj_smul {a : ℝ} (c : ℂ)
  (f : YoshidaClippedSmooth a) :
    clippedConj (c • f) = star c • clippedConj f := by
  ext x
  simp [star_mul, mul_comm]

@[simp] theorem clippedConj_involutive {a : ℝ}
    (f : YoshidaClippedSmooth a) :
    clippedConj (clippedConj f) = f := by
  ext x
  simp

/-- Pointwise conjugation preserves the periodic source core. -/
theorem clippedConj_mem_periodicCore {a : ℝ}
    (f : YoshidaClippedPeriodicCore a) :
    clippedConj (f : YoshidaClippedSmooth a) ∈
      yoshidaClippedPeriodicCoreSubmodule a := by
  rcases f.property with ⟨F, hFdiff, hFperiodic, hFeq⟩
  refine ⟨fun x ↦ star (F x), ?_, ?_, ?_⟩
  · simpa only [Complex.star_def] using
      Complex.conjCLE.contDiff.comp hFdiff
  · intro x
    change star (F (x + 2 * a)) = star (F x)
    rw [hFperiodic]
  · intro x hx
    simp only [clippedConj_apply]
    rw [hFeq hx]

def periodicCoreConj {a : ℝ} (f : YoshidaClippedPeriodicCore a) :
    YoshidaClippedPeriodicCore a :=
  ⟨clippedConj (f : YoshidaClippedSmooth a),
    clippedConj_mem_periodicCore f⟩

@[simp] theorem periodicCoreConj_apply {a x : ℝ}
    (f : YoshidaClippedPeriodicCore a) :
    ((periodicCoreConj f : YoshidaClippedSmooth a) : ℝ → ℂ) x =
      star (((f : YoshidaClippedSmooth a) : ℝ → ℂ) x) := rfl

theorem centeredLift_clippedConj {a : ℝ} (ha : 0 < a)
    (f : YoshidaClippedSmooth a) (x : CenteredAddCircle a) :
    letI : Fact (0 < 2 * a) := ⟨by positivity⟩
    centeredLift a ((clippedConj f : YoshidaClippedSmooth a) : ℝ → ℂ) x =
      star (centeredLift a ((f : YoshidaClippedSmooth a) : ℝ → ℂ) x) := by
  letI : Fact (0 < 2 * a) := ⟨by positivity⟩
  rfl

/-- The clipped-to-circle coordinate map commutes with pointwise
conjugation. -/
theorem yoshidaClippedCircleL2_clippedConj {a : ℝ} (ha : 0 < a)
    (f : YoshidaClippedSmooth a) :
    letI : Fact (0 < 2 * a) := ⟨by positivity⟩
    YoshidaClippedCircleBridge.yoshidaClippedCircleL2 ha (clippedConj f) =
      star (YoshidaClippedCircleBridge.yoshidaClippedCircleL2 ha f) := by
  letI : Fact (0 < 2 * a) := ⟨by positivity⟩
  apply Lp.ext
  filter_upwards [
    (centeredLift_memLp ha
      (YoshidaClippedCircleBridge.yoshidaClippedSmooth_memLp_two
        (clippedConj f))).coeFn_toLp,
    (centeredLift_memLp ha
      (YoshidaClippedCircleBridge.yoshidaClippedSmooth_memLp_two f)).coeFn_toLp,
    Lp.coeFn_star
      (YoshidaClippedCircleBridge.yoshidaClippedCircleL2 ha f)] with x hcf hf hs
  calc
    (YoshidaClippedCircleBridge.yoshidaClippedCircleL2 ha (clippedConj f) :
        CircleL2 (T := 2 * a)) x =
        centeredLift a ((clippedConj f : YoshidaClippedSmooth a) : ℝ → ℂ) x := hcf
    _ = star (centeredLift a ((f : YoshidaClippedSmooth a) : ℝ → ℂ) x) :=
      centeredLift_clippedConj ha f x
    _ = star ((YoshidaClippedCircleBridge.yoshidaClippedCircleL2 ha f :
        CircleL2 (T := 2 * a)) x) := congrArg star hf.symm
    _ = (star (YoshidaClippedCircleBridge.yoshidaClippedCircleL2 ha f) :
        CircleL2 (T := 2 * a)) x := hs.symm

/-- Pointwise conjugation of an `L²` class preserves circle evenness. -/
theorem star_mem_evenL2Submodule {T : ℝ} [Fact (0 < T)]
    {f : CircleL2 (T := T)}
    (hf : f ∈ evenL2Submodule (T := T)) :
    star f ∈ evenL2Submodule (T := T) := by
  rw [mem_evenL2Submodule_iff]
  have heven := reflectionL2_ae (T := T) f
  rw [(mem_evenL2Submodule_iff f).mp hf] at heven
  have hstarNeg :=
    (circleNegMeasurePreserving (T := T)).quasiMeasurePreserving.tendsto_ae
      (Lp.coeFn_star f)
  apply Lp.ext
  filter_upwards [
    reflectionL2_ae (T := T) (star f),
    Lp.coeFn_star f,
    hstarNeg,
    heven] with x href hstar hstarNegX hevenX
  calc
    (reflectionL2 (T := T) (star f) : CircleL2 (T := T)) x =
        (star f : CircleL2 (T := T)) (-x) := href
    _ = star ((f : CircleL2 (T := T)) (-x)) := hstarNegX
    _ = star ((f : CircleL2 (T := T)) x) := congrArg star hevenX.symm
    _ = (star f : CircleL2 (T := T)) x := hstar.symm

/-- Conjugation preserves an actual periodic even Fourier tail. -/
theorem periodicCoreConj_mem_evenTail {a : ℝ} (ha : 0 < a) (N : ℕ)
    (f : YoshidaClippedPeriodicCore a)
    (hf : f ∈ yoshidaPeriodicCoreEvenTailSubmodule ha N) :
    periodicCoreConj f ∈ yoshidaPeriodicCoreEvenTailSubmodule ha N := by
  letI : Fact (0 < 2 * a) := ⟨by positivity⟩
  rw [mem_yoshidaPeriodicCoreEvenTailSubmodule_iff]
  have htail :
      YoshidaClippedCircleBridge.yoshidaClippedCircleL2 ha
          (f : YoshidaClippedSmooth a) ∈
        evenFourierTailSubmodule (T := 2 * a) N :=
    (mem_yoshidaPeriodicCoreEvenTailSubmodule_iff ha N f).mp hf
  constructor
  · rw [show
        YoshidaClippedCircleBridge.yoshidaClippedCircleL2 ha
            ((periodicCoreConj f : YoshidaClippedPeriodicCore a) :
              YoshidaClippedSmooth a) =
          star (YoshidaClippedCircleBridge.yoshidaClippedCircleL2 ha
            (f : YoshidaClippedSmooth a)) by
        exact yoshidaClippedCircleL2_clippedConj ha
          (f : YoshidaClippedSmooth a)]
    exact star_mem_evenL2Submodule htail.1
  · change
      YoshidaClippedCircleBridge.yoshidaClippedCircleL2 ha
          ((periodicCoreConj f : YoshidaClippedPeriodicCore a) :
            YoshidaClippedSmooth a) ∈
        fourierTailSubmodule (T := 2 * a) N
    rw [mem_fourierTailSubmodule_iff]
    intro n hn
    have hneg := neg_mem_lowIndex hn
    have hzero :=
      (mem_fourierTailSubmodule_iff N
        (YoshidaClippedCircleBridge.yoshidaClippedCircleL2 ha
          (f : YoshidaClippedSmooth a))).mp htail.2 (-n) hneg
    calc
      fourierCoeff
          (YoshidaClippedCircleBridge.yoshidaClippedCircleL2 ha
            ((periodicCoreConj f : YoshidaClippedPeriodicCore a) :
              YoshidaClippedSmooth a)) n =
          centeredFourierCoeff ha
            (((periodicCoreConj f : YoshidaClippedPeriodicCore a) :
              YoshidaClippedSmooth a) : ℝ → ℂ) n :=
        YoshidaClippedCircleBridge.fourierCoeff_yoshidaClippedCircleL2
          ha _ n
      _ = star (centeredFourierCoeff ha
          (((f : YoshidaClippedPeriodicCore a) :
            YoshidaClippedSmooth a) : ℝ → ℂ) (-n)) := by
        exact centeredFourierCoeff_conj ha _ n
      _ = star (fourierCoeff
          (YoshidaClippedCircleBridge.yoshidaClippedCircleL2 ha
            (f : YoshidaClippedSmooth a)) (-n)) := by
        rw [YoshidaClippedCircleBridge.fourierCoeff_yoshidaClippedCircleL2]
      _ = 0 := by simpa using congrArg star hzero

/-- Centered Laplace evaluation intertwines pointwise conjugation with
conjugation of the spectral parameter. -/
theorem yoshidaCenteredLaplace_clippedConj {a : ℝ} (ha : 0 < a)
    (z : ℂ) (f : YoshidaClippedSmooth a) :
    yoshidaCenteredLaplaceLinear a ha z (clippedConj f) =
      star (yoshidaCenteredLaplaceLinear a ha (star z) f) := by
  rw [yoshidaCenteredLaplaceLinear_apply,
    yoshidaCenteredLaplaceLinear_apply]
  have hint : IntervalIntegrable
      (fun x : ℝ ↦ Complex.exp (-(star z * (x : ℂ))) * f x)
      volume (-a) a := by
    have hw : Continuous (fun x : ℝ ↦
        Complex.exp (-(star z * (x : ℂ)))) := by
      fun_prop
    exact (hw.continuousOn.mul f.property.1.continuousOn).intervalIntegrable_of_Icc
      (by linarith)
  change (∫ x : ℝ in -a..a,
      Complex.exp (-(z * (x : ℂ))) * star (f x)) =
    Complex.conjCLE (∫ x : ℝ in -a..a,
      Complex.exp (-(star z * (x : ℂ))) * f x)
  calc
    (∫ x : ℝ in -a..a,
        Complex.exp (-(z * (x : ℂ))) * star (f x)) =
        ∫ x : ℝ in -a..a,
          Complex.conjCLE
            (Complex.exp (-(star z * (x : ℂ))) * f x) := by
      apply intervalIntegral.integral_congr
      intro x _
      change Complex.exp (-(z * (x : ℂ))) * star (f x) =
        Complex.conjCLE
          (Complex.exp (-(star z * (x : ℂ))) * f x)
      rw [Complex.conjCLE_apply, map_mul, ← Complex.exp_conj]
      simp only [map_neg, map_mul, conj_ofReal]
      rw [show (starRingEnd ℂ) (star z) = z by simp]
      rw [starRingEnd_apply]
    _ = Complex.conjCLE (∫ x : ℝ in -a..a,
        Complex.exp (-(star z * (x : ℂ))) * f x) :=
      Complex.conjCLE.toContinuousLinearMap.intervalIntegral_comp_comm hint

/-- A pointwise even clipped function has an even centered Laplace
transform. -/
theorem yoshidaCenteredLaplace_neg_of_even {a : ℝ} (ha : 0 < a)
    (z : ℂ) (f : YoshidaClippedSmooth a)
    (hf : ∀ x : ℝ, f (-x) = f x) :
    yoshidaCenteredLaplaceLinear a ha (-z) f =
      yoshidaCenteredLaplaceLinear a ha z f := by
  rw [yoshidaCenteredLaplaceLinear_apply,
    yoshidaCenteredLaplaceLinear_apply]
  calc
    (∫ x : ℝ in -a..a,
        Complex.exp (-((-z) * (x : ℂ))) * f x) =
        ∫ x : ℝ in -a..a,
          (fun y : ℝ ↦ Complex.exp (-(z * (y : ℂ))) * f y) (-x) := by
      apply intervalIntegral.integral_congr
      intro x _
      change Complex.exp (-((-z) * (x : ℂ))) * f x =
        Complex.exp (-(z * ((-x : ℝ) : ℂ))) * f (-x)
      rw [hf]
      push_cast
      ring_nf
    _ = ∫ x : ℝ in -a..a,
        Complex.exp (-(z * (x : ℂ))) * f x := by
      simpa using intervalIntegral.integral_comp_neg
        (a := -a) (b := a)
        (fun x : ℝ ↦ Complex.exp (-(z * (x : ℂ))) * f x)

theorem yoshidaPositivePolar_clippedConj {a : ℝ} (ha : 0 < a)
    (f : YoshidaClippedSmooth a) :
    yoshidaPositivePolarLinear a ha (clippedConj f) =
      star (yoshidaPositivePolarLinear a ha f) := by
  unfold yoshidaPositivePolarLinear
  rw [yoshidaCenteredLaplace_clippedConj]
  congr 2
  norm_num

theorem yoshidaNegativePolar_clippedConj {a : ℝ} (ha : 0 < a)
    (f : YoshidaClippedSmooth a) :
    yoshidaNegativePolarLinear a ha (clippedConj f) =
      star (yoshidaNegativePolarLinear a ha f) := by
  unfold yoshidaNegativePolarLinear
  rw [yoshidaCenteredLaplace_clippedConj]
  congr 2
  norm_num

theorem yoshidaCriticalSample_clippedConj_of_even {a : ℝ} (ha : 0 < a)
    (f : YoshidaClippedSmooth a)
    (hf : ∀ x : ℝ, f (-x) = f x) (v : ℝ) :
    yoshidaCriticalSampleLinear a ha v (clippedConj f) =
      star (yoshidaCriticalSampleLinear a ha v f) := by
  unfold yoshidaCriticalSampleLinear
  rw [yoshidaCenteredLaplace_clippedConj]
  have hz : star ((v : ℂ) * Complex.I) = -((v : ℂ) * Complex.I) := by
    simp [star_mul]
    ring
  rw [hz, yoshidaCenteredLaplace_neg_of_even ha _ f hf]

/-- Conjugation preserves the production quadratic form on any pointwise
even clipped vector. -/
theorem yoshidaClippedLocalCriticalPairing_clippedConj_self_of_even
    {a : ℝ} (ha : 0 < a) (f : YoshidaClippedSmooth a)
    (hf : ∀ x : ℝ, f (-x) = f x) :
    yoshidaClippedLocalCriticalPairing a ha (clippedConj f) (clippedConj f) =
      yoshidaClippedLocalCriticalPairing a ha f f := by
  have hcross :
      (∫ v : ℝ, yoshidaClippedCriticalCrossIntegrand a ha
        (clippedConj f) (clippedConj f) v) =
      ∫ v : ℝ, yoshidaClippedCriticalCrossIntegrand a ha f f v := by
    apply integral_congr_ae
    filter_upwards [] with v
    rw [yoshidaClippedCriticalCrossIntegrand,
      yoshidaClippedCriticalCrossIntegrand,
      yoshidaCriticalSample_clippedConj_of_even ha f hf]
    simp only [star_star]
    ring
  simp only [yoshidaClippedLocalCriticalPairing]
  rw [yoshidaPositivePolar_clippedConj,
    yoshidaNegativePolar_clippedConj, hcross]
  simp only [star_star]
  ring

/-- Pointwise conjugation on the actual mode-`200` even tail. -/
def evenTailConj (f : YoshidaEvenOneNinetyNineTail) :
    YoshidaEvenOneNinetyNineTail :=
  ⟨periodicCoreConj (f : YoshidaClippedPeriodicCore yoshidaA),
    periodicCoreConj_mem_evenTail yoshidaA_pos 199
      (f : YoshidaClippedPeriodicCore yoshidaA) f.property⟩

@[simp] theorem evenTailConj_toClippedSmooth
    (f : YoshidaEvenOneNinetyNineTail) :
    evenOneNinetyNineTailToClippedSmooth (evenTailConj f) =
      clippedConj (evenOneNinetyNineTailToClippedSmooth f) := rfl

@[simp] theorem evenTailConj_zero :
    evenTailConj (0 : YoshidaEvenOneNinetyNineTail) = 0 := by
  apply Subtype.ext
  apply Subtype.ext
  exact clippedConj_zero

@[simp] theorem evenTailConj_add
    (f g : YoshidaEvenOneNinetyNineTail) :
    evenTailConj (f + g) = evenTailConj f + evenTailConj g := by
  apply Subtype.ext
  apply Subtype.ext
  exact clippedConj_add _ _

@[simp] theorem evenTailConj_smul (c : ℂ)
    (f : YoshidaEvenOneNinetyNineTail) :
    evenTailConj (c • f) = star c • evenTailConj f := by
  apply Subtype.ext
  apply Subtype.ext
  exact clippedConj_smul c _

@[simp] theorem evenTailConj_involutive
    (f : YoshidaEvenOneNinetyNineTail) :
    evenTailConj (evenTailConj f) = f := by
  apply Subtype.ext
  apply Subtype.ext
  exact clippedConj_involutive _

theorem evenTailCriticalForm_conj_self
    (f : YoshidaEvenOneNinetyNineTail) :
    evenOneNinetyNineTailCriticalForm (evenTailConj f) (evenTailConj f) =
      evenOneNinetyNineTailCriticalForm f f := by
  rw [evenOneNinetyNineTailCriticalForm_apply,
    evenOneNinetyNineTailCriticalForm_apply,
    evenTailConj_toClippedSmooth]
  exact yoshidaClippedLocalCriticalPairing_clippedConj_self_of_even
    yoshidaA_pos (evenOneNinetyNineTailToClippedSmooth f)
    (evenTail_pointwise_even yoshidaA_pos 199
      (f : YoshidaClippedPeriodicCore yoshidaA) f.property)

/-- Conjugation on the algebraic form space. -/
def formSpaceConj
    (x : FormSpace evenOneNinetyNineTailPositiveHermitianForm) :
    FormSpace evenOneNinetyNineTailPositiveHermitianForm :=
  FormSpace.of (evenTailConj x.toV)

private theorem formSpace_eq_of_toV_eq
    {x y : FormSpace evenOneNinetyNineTailPositiveHermitianForm}
    (h : x.toV = y.toV) : x = y := by
  rcases x with ⟨x⟩
  rcases y with ⟨y⟩
  cases h
  rfl

@[simp] theorem formSpaceConj_toV
    (x : FormSpace evenOneNinetyNineTailPositiveHermitianForm) :
    (formSpaceConj x).toV = evenTailConj x.toV := rfl

@[simp] theorem formSpaceConj_zero :
    formSpaceConj
      (0 : FormSpace evenOneNinetyNineTailPositiveHermitianForm) = 0 := by
  apply formSpace_eq_of_toV_eq
  exact evenTailConj_zero

@[simp] theorem formSpaceConj_add
    (x y : FormSpace evenOneNinetyNineTailPositiveHermitianForm) :
    formSpaceConj (x + y) = formSpaceConj x + formSpaceConj y := by
  apply formSpace_eq_of_toV_eq
  exact evenTailConj_add x.toV y.toV

@[simp] theorem formSpaceConj_smul (c : ℂ)
    (x : FormSpace evenOneNinetyNineTailPositiveHermitianForm) :
    formSpaceConj (c • x) = star c • formSpaceConj x := by
  apply formSpace_eq_of_toV_eq
  exact evenTailConj_smul c x.toV

@[simp] theorem formSpaceConj_involutive
    (x : FormSpace evenOneNinetyNineTailPositiveHermitianForm) :
    formSpaceConj (formSpaceConj x) = x := by
  apply formSpace_eq_of_toV_eq
  exact evenTailConj_involutive x.toV

@[simp] theorem norm_formSpaceConj
    (x : FormSpace evenOneNinetyNineTailPositiveHermitianForm) :
    ‖formSpaceConj x‖ = ‖x‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
    FormSpace.norm_sq_eq_form_re, FormSpace.norm_sq_eq_form_re]
  exact congrArg Complex.re (evenTailCriticalForm_conj_self x.toV)

def formSpaceConjNormedAddGroupHom :
    NormedAddGroupHom
      (FormSpace evenOneNinetyNineTailPositiveHermitianForm)
      (FormSpace.Completion
        evenOneNinetyNineTailPositiveHermitianForm) where
  toFun := fun x ↦
    (formSpaceConj x : FormSpace.Completion
      evenOneNinetyNineTailPositiveHermitianForm)
  map_add' := fun x y ↦ by
    rw [formSpaceConj_add, UniformSpace.Completion.coe_add]
  bound' := ⟨1, fun x ↦ by simp⟩

/-- The continuous conjugation operator on the completed actual even tail. -/
noncomputable def completionConj :
    FormSpace.Completion evenOneNinetyNineTailPositiveHermitianForm →
      FormSpace.Completion evenOneNinetyNineTailPositiveHermitianForm :=
  formSpaceConjNormedAddGroupHom.extension

@[simp] theorem completionConj_coe
    (x : FormSpace evenOneNinetyNineTailPositiveHermitianForm) :
    completionConj
        (x : FormSpace.Completion evenOneNinetyNineTailPositiveHermitianForm) =
      (formSpaceConj x :
        FormSpace.Completion evenOneNinetyNineTailPositiveHermitianForm) := by
  exact NormedAddGroupHom.extension_coe formSpaceConjNormedAddGroupHom x

theorem continuous_completionConj : Continuous completionConj :=
  formSpaceConjNormedAddGroupHom.extension.continuous

@[simp] theorem completionConj_add
    (x y : FormSpace.Completion
      evenOneNinetyNineTailPositiveHermitianForm) :
    completionConj (x + y) = completionConj x + completionConj y :=
  formSpaceConjNormedAddGroupHom.extension.map_add' x y

@[simp] theorem norm_completionConj
    (z : FormSpace.Completion
      evenOneNinetyNineTailPositiveHermitianForm) :
    ‖completionConj z‖ = ‖z‖ := by
  refine UniformSpace.Completion.induction_on z
    (isClosed_eq ?_ ?_) ?_
  · exact continuous_norm.comp continuous_completionConj
  · exact continuous_norm
  · intro x
    simp

@[simp] theorem completionConj_smul (c : ℂ)
    (z : FormSpace.Completion
      evenOneNinetyNineTailPositiveHermitianForm) :
    completionConj (c • z) = star c • completionConj z := by
  let g := formSpaceConjNormedAddGroupHom.extension
  have heq :
      (fun w : FormSpace.Completion
          evenOneNinetyNineTailPositiveHermitianForm ↦ g (c • w)) =
        fun w ↦ star c • g w := by
    apply UniformSpace.Completion.denseRange_coe.equalizer
    · exact g.continuous.comp (continuous_const_smul c)
    · exact (continuous_const_smul (star c)).comp g.continuous
    · funext x
      change completionConj
          (c • (x : FormSpace.Completion
            evenOneNinetyNineTailPositiveHermitianForm)) =
        star c • completionConj
          (x : FormSpace.Completion
            evenOneNinetyNineTailPositiveHermitianForm)
      rw [← UniformSpace.Completion.coe_smul,
        completionConj_coe, completionConj_coe,
        formSpaceConj_smul,
        UniformSpace.Completion.coe_smul]
  exact congrFun heq z

@[simp] theorem completionConj_neg
    (z : FormSpace.Completion
      evenOneNinetyNineTailPositiveHermitianForm) :
    completionConj (-z) = -completionConj z := by
  simpa only [neg_one_smul, map_neg, starRingEnd_apply, star_neg,
    star_one] using completionConj_smul (-1 : ℂ) z

@[simp] theorem completionConj_sub
    (x y : FormSpace.Completion
      evenOneNinetyNineTailPositiveHermitianForm) :
    completionConj (x - y) = completionConj x - completionConj y := by
  simp only [sub_eq_add_neg, completionConj_add, completionConj_neg]

@[simp] theorem completionConj_involutive
    (z : FormSpace.Completion
      evenOneNinetyNineTailPositiveHermitianForm) :
    completionConj (completionConj z) = z := by
  have heq :
      (fun w : FormSpace.Completion
          evenOneNinetyNineTailPositiveHermitianForm ↦
        completionConj (completionConj w)) = id := by
    apply UniformSpace.Completion.denseRange_coe.equalizer
    · exact continuous_completionConj.comp continuous_completionConj
    · exact continuous_id
    · funext x
      simp
  exact congrFun heq z

noncomputable def completionConjLinearIsometry :
    FormSpace.Completion evenOneNinetyNineTailPositiveHermitianForm
      →ₗᵢ⋆[ℂ]
    FormSpace.Completion evenOneNinetyNineTailPositiveHermitianForm where
  toFun := completionConj
  map_add' := completionConj_add
  map_smul' := completionConj_smul
  norm_map' := norm_completionConj

/-- The completed conjugation is antiunitary. -/
theorem inner_completionConj
    (x y : FormSpace.Completion
      evenOneNinetyNineTailPositiveHermitianForm) :
    ⟪completionConj x, completionConj y⟫_ℂ = star ⟪x, y⟫_ℂ := by
  apply Complex.ext
  · change RCLike.re ⟪completionConj x, completionConj y⟫_ℂ =
      RCLike.re ⟪x, y⟫_ℂ
    rw [
      re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four,
      re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four,
      ← completionConj_add, ← completionConj_sub,
      norm_completionConj, norm_completionConj]
  · change RCLike.im ⟪completionConj x, completionConj y⟫_ℂ =
      -RCLike.im ⟪x, y⟫_ℂ
    rw [
      im_inner_eq_norm_sub_i_smul_mul_self_sub_norm_add_i_smul_mul_self_div_four,
      im_inner_eq_norm_sub_i_smul_mul_self_sub_norm_add_i_smul_mul_self_div_four]
    have hI :
        completionConj (Complex.I • y) =
          (-Complex.I) • completionConj y := by
      calc
        completionConj (Complex.I • y) =
            star Complex.I • completionConj y :=
          completionConj_smul Complex.I y
        _ = (-Complex.I) • completionConj y :=
          congrArg (fun c : ℂ ↦ c • completionConj y) star_I_eq_neg_I
    have hplus :
        completionConj (x + Complex.I • y) =
          completionConj x - Complex.I • completionConj y := by
      calc
        completionConj (x + Complex.I • y) =
            completionConj x + completionConj (Complex.I • y) :=
          completionConj_add x (Complex.I • y)
        _ = completionConj x + (-Complex.I) • completionConj y :=
          congrArg (fun z ↦ completionConj x + z) hI
        _ = completionConj x + -(Complex.I • completionConj y) :=
          congrArg (fun z ↦ completionConj x + z)
            (neg_smul Complex.I (completionConj y))
        _ = completionConj x - Complex.I • completionConj y :=
          (sub_eq_add_neg _ _).symm
    have hminus :
        completionConj (x - Complex.I • y) =
          completionConj x + Complex.I • completionConj y := by
      calc
        completionConj (x - Complex.I • y) =
            completionConj x - completionConj (Complex.I • y) :=
          completionConj_sub x (Complex.I • y)
        _ = completionConj x - (-Complex.I) • completionConj y :=
          congrArg (fun z ↦ completionConj x - z) hI
        _ = completionConj x - -(Complex.I • completionConj y) :=
          congrArg (fun z ↦ completionConj x - z)
            (neg_smul Complex.I (completionConj y))
        _ = completionConj x + Complex.I • completionConj y :=
          sub_neg_eq_add _ _
    have hnplus :
        ‖completionConj x - Complex.I • completionConj y‖ =
          ‖x + Complex.I • y‖ := by
      calc
        ‖completionConj x - Complex.I • completionConj y‖ =
            ‖completionConj (x + Complex.I • y)‖ :=
          congrArg norm hplus.symm
        _ = ‖x + Complex.I • y‖ := norm_completionConj _
    have hnminus :
        ‖completionConj x + Complex.I • completionConj y‖ =
          ‖x - Complex.I • y‖ := by
      calc
        ‖completionConj x + Complex.I • completionConj y‖ =
            ‖completionConj (x - Complex.I • y)‖ :=
          congrArg norm hminus.symm
        _ = ‖x - Complex.I • y‖ := norm_completionConj _
    exact
      (congrArg₂ (fun A B : ℝ ↦ (A * A - B * B) / 4)
        hnplus hnminus).trans
          (swap_square_difference_div_four
            ‖x - Complex.I • y‖ ‖x + Complex.I • y‖)

theorem evenTailCosineCoefficient_conj
    (f : YoshidaEvenOneNinetyNineTail) (k : ℕ) :
    evenTailCosineCoefficient (evenTailConj f) k =
      star (evenTailCosineCoefficient f k) := by
  rw [evenTailCosineCoefficient, evenTailCosineCoefficient,
    evenTailConj_toClippedSmooth]
  change (((Real.sqrt (4 * yoshidaA) : ℝ) : ℂ)) *
      centeredFourierCoeff yoshidaA_pos
        (fun x ↦ conj
          ((evenOneNinetyNineTailToClippedSmooth f :
            YoshidaClippedSmooth yoshidaA) x))
        ((200 + k : ℕ) : ℤ) =
    star ((((Real.sqrt (4 * yoshidaA) : ℝ) : ℂ)) *
      centeredFourierCoeff yoshidaA_pos
        ((evenOneNinetyNineTailToClippedSmooth f :
          YoshidaClippedSmooth yoshidaA) : ℝ → ℂ)
        ((200 + k : ℕ) : ℤ))
  rw [centeredFourierCoeff_conj]
  rw [centeredFourierCoeff_even yoshidaA_pos
    ((evenOneNinetyNineTailToClippedSmooth f :
      YoshidaClippedSmooth yoshidaA) : ℝ → ℂ)
    (evenTail_pointwise_even yoshidaA_pos 199
      (f : YoshidaClippedPeriodicCore yoshidaA) f.property)]
  simp [star_mul, mul_comm]

theorem star_evenTailLowCoupling
    (i : YoshidaEvenIndex) (k : ℕ) :
    star (evenTailLowCoupling i k) = evenTailLowCoupling i k := by
  unfold evenTailLowCoupling
  rw [yoshidaClippedLocalCriticalForm_apply,
    yoshidaClippedLocalCriticalPairing_evenTail_lowMode_eq_formula,
    actualEvenPairingEquation6_25 i k]
  simp

/-- Each actual low-mode functional is compatible with the real structure
on the even tail. -/
theorem evenTailLowPairing_conj
    (f : YoshidaEvenOneNinetyNineTail) (i : YoshidaEvenIndex) :
    yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
        (evenOneNinetyNineTailToClippedSmooth (evenTailConj f))
        (yoshidaClippedEvenLowMode yoshidaA i) =
      star (yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
        (evenOneNinetyNineTailToClippedSmooth f)
        (yoshidaClippedEvenLowMode yoshidaA i)) := by
  have hconj := evenTailLowFourierInterchange (evenTailConj f) i
  have horig := evenTailLowFourierInterchange f i
  have hstar' : HasSum
      (fun k : ℕ ↦ star
        (star (evenTailCosineCoefficient f k) * evenTailLowCoupling i k))
      (star (yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
        (evenOneNinetyNineTailToClippedSmooth f)
        (yoshidaClippedEvenLowMode yoshidaA i))) := by
    apply (RCLike.hasSum_conj ℂ).2
    simpa only [starRingEnd_apply, star_star] using horig
  have hterms (k : ℕ) :
      star (evenTailCosineCoefficient (evenTailConj f) k) *
          evenTailLowCoupling i k =
        star (star (evenTailCosineCoefficient f k) *
          evenTailLowCoupling i k) := by
    rw [evenTailCosineCoefficient_conj, star_mul,
      star_evenTailLowCoupling]
    simp only [star_star]
    ring
  exact hconj.unique (hstar'.congr_fun hterms)

/-- The production Riesz vector for every canonical even low mode is fixed
by completed conjugation. -/
theorem completionConj_actualEvenTailLowRieszCorrection
    (i : YoshidaEvenIndex) :
    completionConj (actualEvenTailLowRieszCorrection i) =
      actualEvenTailLowRieszCorrection i := by
  refine UniformSpace.Completion.denseRange_coe.eq_of_inner_right ℂ fun x ↦ ?_
  calc
    ⟪(x : FormSpace.Completion evenOneNinetyNineTailPositiveHermitianForm),
        completionConj (actualEvenTailLowRieszCorrection i)⟫_ℂ =
        ⟪completionConj (completionConj
            (x : FormSpace.Completion
              evenOneNinetyNineTailPositiveHermitianForm)),
          completionConj (actualEvenTailLowRieszCorrection i)⟫_ℂ := by
      rw [completionConj_involutive]
    _ = star ⟪completionConj
          (x : FormSpace.Completion
            evenOneNinetyNineTailPositiveHermitianForm),
        actualEvenTailLowRieszCorrection i⟫_ℂ :=
      inner_completionConj _ _
    _ = star ⟪(formSpaceConj x :
          FormSpace.Completion
            evenOneNinetyNineTailPositiveHermitianForm),
        actualEvenTailLowRieszCorrection i⟫_ℂ := by
      rw [completionConj_coe]
    _ = star (yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
        (evenOneNinetyNineTailToClippedSmooth (evenTailConj x.toV))
        (yoshidaClippedEvenLowMode yoshidaA i)) := by
      rw [formSpace_inner_actualEvenTailLowRieszCorrection]
      rfl
    _ = star (star (yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
        (evenOneNinetyNineTailToClippedSmooth x.toV)
        (yoshidaClippedEvenLowMode yoshidaA i))) := by
      rw [evenTailLowPairing_conj]
    _ = yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
        (evenOneNinetyNineTailToClippedSmooth x.toV)
        (yoshidaClippedEvenLowMode yoshidaA i) := by
      rw [star_star]
    _ = ⟪(x : FormSpace.Completion
          evenOneNinetyNineTailPositiveHermitianForm),
        actualEvenTailLowRieszCorrection i⟫_ℂ := by
      rw [formSpace_inner_actualEvenTailLowRieszCorrection]

theorem star_actualEvenTailCorrectionGram
    (i j : YoshidaEvenIndex) :
    star (actualEvenTailCorrectionGram i j) =
      actualEvenTailCorrectionGram i j := by
  rw [actualEvenTailCorrectionGram]
  rw [← inner_completionConj]
  rw [completionConj_actualEvenTailLowRieszCorrection,
    completionConj_actualEvenTailLowRieszCorrection]

/-- The actual complex Schur correction is entrywise real, so it is exactly
eligible for the certified real interval perturbation theorem. -/
theorem actualEvenTailCorrectionGram_eq_ofReal
    (i j : YoshidaEvenIndex) :
    actualEvenTailCorrectionGram i j =
      ((actualEvenTailCorrectionGram i j).re : ℂ) := by
  exact (Complex.conj_eq_iff_re.mp (by
    simpa only [Complex.star_def] using
      star_actualEvenTailCorrectionGram i j)).symm

end

end ArithmeticHodge.Analysis.YoshidaEvenCorrectionReality

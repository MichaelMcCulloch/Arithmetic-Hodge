import ArithmeticHodge.Analysis.YoshidaClippedParityOrthogonality
import ArithmeticHodge.Analysis.YoshidaOddInfiniteSchur

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped BigOperators ComplexConjugate

namespace ArithmeticHodge.Analysis.YoshidaParityRecombination

noncomputable section

open ArithmeticHodge.Analysis
open ArithmeticHodge.Analysis.YoshidaClippedCircleBridge
open ArithmeticHodge.Analysis.YoshidaCoercivityNumerics
open ArithmeticHodge.Analysis.YoshidaOddInfiniteSchur
open ArithmeticHodge.Analysis.YoshidaWeightedTailBounds

/-!
# Parity recombination on Yoshida's periodic clipped core

The pointwise reflection of a clipped periodic-core function is again in the
periodic core.  The only delicate coordinate issue is the identified pair of
endpoints: periodicity makes their values agree, so pointwise reflection is
exactly circle reflection in `L²`.  Consequently the canonical pointwise even
and odd parts are the canonical circle parts as well.

The production clipped critical form is already known to have zero even/odd
cross terms.  The final theorem below packages the purely algebraic last step:
strict positivity on the two parity carriers implies strict positivity on the
whole periodic core.
-/

/-- Reflection within the clipped smooth carrier. -/
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

@[simp] theorem clippedReflection_apply
    {a x : ℝ} (f : YoshidaClippedSmooth a) :
    clippedReflection f x = f (-x) :=
  rfl

/-- Reflection preserves the globally smooth periodic source condition. -/
theorem clippedReflection_mem_periodicCore
    {a : ℝ} (f : YoshidaClippedPeriodicCore a) :
    clippedReflection (f : YoshidaClippedSmooth a) ∈
      yoshidaClippedPeriodicCoreSubmodule a := by
  obtain ⟨F, hFsmooth, hFperiodic, hFeq⟩ := f.property
  refine ⟨fun x ↦ F (-x), hFsmooth.comp contDiff_neg, ?_, ?_⟩
  · intro x
    calc
      F (-(x + 2 * a)) = F (-(x + 2 * a) + 2 * a) :=
        (hFperiodic (-(x + 2 * a))).symm
      _ = F (-x) := by ring_nf
  · intro x hx
    change F (-x) = (f : YoshidaClippedSmooth a) (-x)
    apply hFeq
    exact ⟨by linarith [hx.2], by linarith [hx.1]⟩

/-- Linear reflection on the actual periodic clipped core. -/
def periodicCoreReflectionLinear (a : ℝ) :
    YoshidaClippedPeriodicCore a →ₗ[ℂ] YoshidaClippedPeriodicCore a where
  toFun f :=
    ⟨clippedReflection (f : YoshidaClippedSmooth a),
      clippedReflection_mem_periodicCore f⟩
  map_add' f g := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    rfl
  map_smul' c f := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    rfl

@[simp] theorem periodicCoreReflectionLinear_toSmooth_apply
    {a x : ℝ} (f : YoshidaClippedPeriodicCore a) :
    (((periodicCoreReflectionLinear a f : YoshidaClippedPeriodicCore a) :
        YoshidaClippedSmooth a) : ℝ → ℂ) x =
      (f : YoshidaClippedSmooth a) (-x) :=
  rfl

/-- Periodicity resolves the two representatives of the identified endpoint. -/
theorem periodicCore_endpoint_eq
    {a : ℝ} (ha : 0 < a) (f : YoshidaClippedPeriodicCore a) :
    (f : YoshidaClippedSmooth a) (-a) =
      (f : YoshidaClippedSmooth a) a := by
  have hperiod := periodicExtension_periodic f (-a)
  rw [show -a + 2 * a = a by ring] at hperiod
  calc
    (f : YoshidaClippedSmooth a) (-a) = periodicExtension f (-a) :=
      (periodicExtension_apply_of_mem f ⟨le_rfl, by linarith⟩).symm
    _ = periodicExtension f a := hperiod.symm
    _ = (f : YoshidaClippedSmooth a) a :=
      periodicExtension_apply_of_mem f ⟨by linarith, le_rfl⟩

/-- The centered lift of pointwise reflection agrees almost everywhere with
reflection on the circle.  The endpoint branch is where source periodicity is
essential. -/
theorem centeredLift_clippedReflection_ae
    {a : ℝ} (ha : 0 < a) (f : YoshidaClippedPeriodicCore a) :
    letI : Fact (0 < 2 * a) := ⟨by positivity⟩
    centeredLift a
        (clippedReflection (f : YoshidaClippedSmooth a) : ℝ → ℂ) =ᵐ[
          AddCircle.haarAddCircle]
      fun x ↦ centeredLift a
        ((f : YoshidaClippedSmooth a) : ℝ → ℂ) (-x) := by
  letI : Fact (0 < 2 * a) := ⟨by positivity⟩
  filter_upwards [] with x
  let r := AddCircle.equivIoc (2 * a) (-a) x
  have hr : (r : ℝ) ∈ Set.Ioc (-a) a := by
    simpa only [show -a + 2 * a = a by ring] using r.property
  have hrepr : (((r : ℝ) : CenteredAddCircle a)) = x :=
    (AddCircle.equivIoc (2 * a) (-a)).symm_apply_apply x
  rw [← hrepr, centeredLift_apply_Ioc _ hr]
  change (f : YoshidaClippedSmooth a) (-(r : ℝ)) = centeredLift a
    ((f : YoshidaClippedSmooth a) : ℝ → ℂ)
      (-(((r : ℝ) : CenteredAddCircle a)))
  by_cases hra : (r : ℝ) = a
  · have hcircle : -(((r : ℝ) : CenteredAddCircle a)) =
        ((a : ℝ) : CenteredAddCircle a) := by
      rw [hra]
      change (((-a : ℝ) : CenteredAddCircle a)) =
        ((a : ℝ) : CenteredAddCircle a)
      calc
        (((-a : ℝ) : CenteredAddCircle a)) =
            (((-a + 2 * a : ℝ) : CenteredAddCircle a)) :=
          (AddCircle.coe_add_period (2 * a) (-a)).symm
        _ = ((a : ℝ) : CenteredAddCircle a) := by ring_nf
    rw [hcircle, centeredLift_apply_Ioc _ ⟨by linarith, le_rfl⟩, hra]
    exact periodicCore_endpoint_eq ha f
  · have hrlt : (r : ℝ) < a := lt_of_le_of_ne hr.2 hra
    have hneg : (-(r : ℝ)) ∈ Set.Ioc (-a) a :=
      ⟨by linarith, by linarith [hr.1]⟩
    rw [show -(((r : ℝ) : CenteredAddCircle a)) =
        ((-(r : ℝ) : ℝ) : CenteredAddCircle a) by rfl]
    rw [centeredLift_apply_Ioc _ hneg]

/-- Pointwise reflection on the periodic source is exactly `reflectionL2` in
the faithful circle coordinate. -/
theorem yoshidaPeriodicCoreCircleL2_reflection
    {a : ℝ} (ha : 0 < a) (f : YoshidaClippedPeriodicCore a) :
    letI : Fact (0 < 2 * a) := ⟨by positivity⟩
    yoshidaPeriodicCoreCircleL2Linear ha
        (periodicCoreReflectionLinear a f) =
      reflectionL2 (T := 2 * a)
        (yoshidaPeriodicCoreCircleL2Linear ha f) := by
  letI : Fact (0 < 2 * a) := ⟨by positivity⟩
  apply Lp.ext
  have href := reflectionL2_ae
    (yoshidaClippedCircleL2 ha (f : YoshidaClippedSmooth a))
  have hleft := (centeredLift_memLp ha
    (yoshidaClippedSmooth_memLp_two
      (clippedReflection (f : YoshidaClippedSmooth a)))).coeFn_toLp
  have hright := (centeredLift_memLp ha
    (yoshidaClippedSmooth_memLp_two
      (f : YoshidaClippedSmooth a))).coeFn_toLp
  have hleft' : (yoshidaClippedCircleL2 ha
      (clippedReflection (f : YoshidaClippedSmooth a)) :
      CenteredAddCircle a → ℂ) =ᵐ[AddCircle.haarAddCircle]
      centeredLift a
        (clippedReflection (f : YoshidaClippedSmooth a) : ℝ → ℂ) := by
    simpa only [yoshidaClippedCircleL2] using hleft
  have hright' : (yoshidaClippedCircleL2 ha
      (f : YoshidaClippedSmooth a) : CenteredAddCircle a → ℂ) =ᵐ[
        AddCircle.haarAddCircle]
      centeredLift a ((f : YoshidaClippedSmooth a) : ℝ → ℂ) := by
    simpa only [yoshidaClippedCircleL2] using hright
  have hrightNeg :=
    (circleNegMeasurePreserving (T := 2 * a)).quasiMeasurePreserving
      |>.ae_eq_comp hright'
  filter_upwards [hleft', href, hrightNeg,
    centeredLift_clippedReflection_ae ha f] with x hl hrefx hr hreflect
  change (yoshidaClippedCircleL2 ha
      (clippedReflection (f : YoshidaClippedSmooth a)) :
        CircleL2 (T := 2 * a)) x =
    (reflectionL2 (T := 2 * a)
      (yoshidaClippedCircleL2 ha
        (f : YoshidaClippedSmooth a)) : CircleL2 (T := 2 * a)) x
  rw [hl, hrefx]
  have hr' : (yoshidaClippedCircleL2 ha
      (f : YoshidaClippedSmooth a) : CenteredAddCircle a → ℂ) (-x) =
      centeredLift a ((f : YoshidaClippedSmooth a) : ℝ → ℂ) (-x) := by
    simpa only [Function.comp_apply] using hr
  rw [hr']
  exact hreflect

/-! ## Canonical parity parts -/

/-- Canonical pointwise even part of a periodic-core vector. -/
def periodicCoreEvenPart {a : ℝ} (f : YoshidaClippedPeriodicCore a) :
    YoshidaClippedPeriodicCore a :=
  (2 : ℂ)⁻¹ • (f + periodicCoreReflectionLinear a f)

/-- Canonical pointwise odd part of a periodic-core vector. -/
def periodicCoreOddPart {a : ℝ} (f : YoshidaClippedPeriodicCore a) :
    YoshidaClippedPeriodicCore a :=
  (2 : ℂ)⁻¹ • (f - periodicCoreReflectionLinear a f)

@[simp] theorem periodicCoreEvenPart_toSmooth_apply
    {a x : ℝ} (f : YoshidaClippedPeriodicCore a) :
    (((periodicCoreEvenPart f : YoshidaClippedPeriodicCore a) :
        YoshidaClippedSmooth a) : ℝ → ℂ) x =
      (2 : ℂ)⁻¹ *
        ((f : YoshidaClippedSmooth a) x +
          (f : YoshidaClippedSmooth a) (-x)) :=
  rfl

@[simp] theorem periodicCoreOddPart_toSmooth_apply
    {a x : ℝ} (f : YoshidaClippedPeriodicCore a) :
    (((periodicCoreOddPart f : YoshidaClippedPeriodicCore a) :
        YoshidaClippedSmooth a) : ℝ → ℂ) x =
      (2 : ℂ)⁻¹ *
        ((f : YoshidaClippedSmooth a) x -
          (f : YoshidaClippedSmooth a) (-x)) :=
  rfl

/-- The canonical even part is genuinely pointwise even, including both
clipped endpoints. -/
theorem periodicCoreEvenPart_pointwise_even
    {a : ℝ} (f : YoshidaClippedPeriodicCore a) (x : ℝ) :
    ((periodicCoreEvenPart f : YoshidaClippedPeriodicCore a) :
        YoshidaClippedSmooth a) (-x) =
      ((periodicCoreEvenPart f : YoshidaClippedPeriodicCore a) :
        YoshidaClippedSmooth a) x := by
  simp only [periodicCoreEvenPart_toSmooth_apply, neg_neg]
  ring

/-- The canonical odd part is genuinely pointwise odd, including both
clipped endpoints. -/
theorem periodicCoreOddPart_pointwise_odd
    {a : ℝ} (f : YoshidaClippedPeriodicCore a) (x : ℝ) :
    ((periodicCoreOddPart f : YoshidaClippedPeriodicCore a) :
        YoshidaClippedSmooth a) (-x) =
      -((periodicCoreOddPart f : YoshidaClippedPeriodicCore a) :
        YoshidaClippedSmooth a) x := by
  simp only [periodicCoreOddPart_toSmooth_apply, neg_neg]
  ring

/-- Canonical parity decomposition in the actual periodic clipped core. -/
theorem periodicCoreEvenPart_add_oddPart
    {a : ℝ} (f : YoshidaClippedPeriodicCore a) :
    periodicCoreEvenPart f + periodicCoreOddPart f = f := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  simp only [Submodule.coe_add, Pi.add_apply,
    periodicCoreEvenPart_toSmooth_apply,
    periodicCoreOddPart_toSmooth_apply]
  ring

/-- The pointwise even part is exactly the canonical even circle projection. -/
theorem yoshidaPeriodicCoreCircleL2_evenPart
    {a : ℝ} (ha : 0 < a) (f : YoshidaClippedPeriodicCore a) :
    letI : Fact (0 < 2 * a) := ⟨by positivity⟩
    yoshidaPeriodicCoreCircleL2Linear ha (periodicCoreEvenPart f) =
      evenPart (T := 2 * a)
        (yoshidaPeriodicCoreCircleL2Linear ha f) := by
  letI : Fact (0 < 2 * a) := ⟨by positivity⟩
  change yoshidaPeriodicCoreCircleL2Linear ha
      ((2 : ℂ)⁻¹ • (f + periodicCoreReflectionLinear a f)) = _
  rw [map_smul, map_add, yoshidaPeriodicCoreCircleL2_reflection ha]
  rfl

/-- The pointwise odd part is exactly the canonical odd circle projection. -/
theorem yoshidaPeriodicCoreCircleL2_oddPart
    {a : ℝ} (ha : 0 < a) (f : YoshidaClippedPeriodicCore a) :
    letI : Fact (0 < 2 * a) := ⟨by positivity⟩
    yoshidaPeriodicCoreCircleL2Linear ha (periodicCoreOddPart f) =
      oddPart (T := 2 * a)
        (yoshidaPeriodicCoreCircleL2Linear ha f) := by
  letI : Fact (0 < 2 * a) := ⟨by positivity⟩
  change yoshidaPeriodicCoreCircleL2Linear ha
      ((2 : ℂ)⁻¹ • (f - periodicCoreReflectionLinear a f)) = _
  rw [map_smul]
  have hsub : yoshidaPeriodicCoreCircleL2Linear ha
        (f - periodicCoreReflectionLinear a f) =
      yoshidaPeriodicCoreCircleL2Linear ha f -
        yoshidaPeriodicCoreCircleL2Linear ha
          (periodicCoreReflectionLinear a f) := by
    exact map_sub (yoshidaPeriodicCoreCircleL2Linear ha) f
      (periodicCoreReflectionLinear a f)
  rw [hsub]
  rw [yoshidaPeriodicCoreCircleL2_reflection ha]
  rfl

/-! ## Actual parity carriers -/

/-- Periodic-core functions whose faithful circle coordinate is even. -/
def yoshidaPeriodicCoreEvenSubmodule :
    Submodule ℂ (YoshidaClippedPeriodicCore yoshidaA) := by
  letI : Fact (0 < 2 * yoshidaA) :=
    ⟨mul_pos (by norm_num) yoshidaA_pos⟩
  exact (evenL2Submodule (T := 2 * yoshidaA)).comap
    (yoshidaPeriodicCoreCircleL2Linear yoshidaA_pos)

/-- The actual canonical periodic even carrier. -/
abbrev YoshidaPeriodicEvenCore := yoshidaPeriodicCoreEvenSubmodule

theorem periodicCoreEvenPart_mem_evenCore
    (f : YoshidaClippedPeriodicCore yoshidaA) :
    periodicCoreEvenPart f ∈ yoshidaPeriodicCoreEvenSubmodule := by
  letI : Fact (0 < 2 * yoshidaA) :=
    ⟨mul_pos (by norm_num) yoshidaA_pos⟩
  change yoshidaPeriodicCoreCircleL2Linear yoshidaA_pos
      (periodicCoreEvenPart f) ∈ evenL2Submodule
  rw [yoshidaPeriodicCoreCircleL2_evenPart yoshidaA_pos]
  exact evenPart_mem _

theorem periodicCoreOddPart_mem_oddCore
    (f : YoshidaClippedPeriodicCore yoshidaA) :
    periodicCoreOddPart f ∈ yoshidaPeriodicCoreOddSubmodule := by
  letI : Fact (0 < 2 * yoshidaA) :=
    ⟨mul_pos (by norm_num) yoshidaA_pos⟩
  change yoshidaPeriodicCoreCircleL2Linear yoshidaA_pos
      (periodicCoreOddPart f) ∈ oddL2Submodule
  rw [yoshidaPeriodicCoreCircleL2_oddPart yoshidaA_pos]
  exact oddPart_mem _

/-! ## Production-form orthogonality and recombination -/

/-- The production clipped form has zero even/odd cross term on the canonical
parts of an actual periodic-core vector. -/
theorem clippedCriticalForm_evenPart_oddPart_eq_zero
    (f : YoshidaClippedPeriodicCore yoshidaA) :
    yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
        ((periodicCoreEvenPart f : YoshidaClippedPeriodicCore yoshidaA) :
          YoshidaClippedSmooth yoshidaA)
        ((periodicCoreOddPart f : YoshidaClippedPeriodicCore yoshidaA) :
          YoshidaClippedSmooth yoshidaA) = 0 := by
  apply yoshidaClippedLocalCriticalForm_even_odd_eq_zero
  · exact periodicCoreEvenPart_pointwise_even f
  · exact periodicCoreOddPart_pointwise_odd f

/-- The reversed production cross term also vanishes, with the conjugation
orientation fixed by the Hermitian form. -/
theorem clippedCriticalForm_oddPart_evenPart_eq_zero
    (f : YoshidaClippedPeriodicCore yoshidaA) :
    yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
        ((periodicCoreOddPart f : YoshidaClippedPeriodicCore yoshidaA) :
          YoshidaClippedSmooth yoshidaA)
        ((periodicCoreEvenPart f : YoshidaClippedPeriodicCore yoshidaA) :
          YoshidaClippedSmooth yoshidaA) = 0 := by
  apply yoshidaClippedLocalCriticalForm_odd_even_eq_zero
  · exact periodicCoreOddPart_pointwise_odd f
  · exact periodicCoreEvenPart_pointwise_even f

/-- Exact diagonal splitting of the actual production clipped form into its
even and odd values.  No bounded-extension or abstract orthogonality premise
is used. -/
theorem clippedCriticalForm_eq_evenPart_add_oddPart
    (f : YoshidaClippedPeriodicCore yoshidaA) :
    yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
        (f : YoshidaClippedSmooth yoshidaA)
        (f : YoshidaClippedSmooth yoshidaA) =
      yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
          ((periodicCoreEvenPart f : YoshidaClippedPeriodicCore yoshidaA) :
            YoshidaClippedSmooth yoshidaA)
          ((periodicCoreEvenPart f : YoshidaClippedPeriodicCore yoshidaA) :
            YoshidaClippedSmooth yoshidaA) +
        yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
          ((periodicCoreOddPart f : YoshidaClippedPeriodicCore yoshidaA) :
            YoshidaClippedSmooth yoshidaA)
          ((periodicCoreOddPart f : YoshidaClippedPeriodicCore yoshidaA) :
            YoshidaClippedSmooth yoshidaA) := by
  let B := yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
  let e : YoshidaClippedSmooth yoshidaA :=
    ((periodicCoreEvenPart f : YoshidaClippedPeriodicCore yoshidaA) :
      YoshidaClippedSmooth yoshidaA)
  let o : YoshidaClippedSmooth yoshidaA :=
    ((periodicCoreOddPart f : YoshidaClippedPeriodicCore yoshidaA) :
      YoshidaClippedSmooth yoshidaA)
  have hdecomp : (f : YoshidaClippedSmooth yoshidaA) = e + o := by
    have h := periodicCoreEvenPart_add_oddPart f
    have hsmooth := congrArg
      (fun g : YoshidaClippedPeriodicCore yoshidaA ↦
        (g : YoshidaClippedSmooth yoshidaA)) h
    simpa only [e, o, Submodule.coe_add] using hsmooth.symm
  have hcrossEO : B e o = 0 := by
    exact clippedCriticalForm_evenPart_oddPart_eq_zero f
  have hcrossOE : B o e = 0 := by
    exact clippedCriticalForm_oddPart_evenPart_eq_zero f
  change B (f : YoshidaClippedSmooth yoshidaA)
      (f : YoshidaClippedSmooth yoshidaA) = B e e + B o o
  rw [hdecomp]
  rw [map_add]
  simp only [map_add]
  change (B e e + B o e) + (B e o + B o o) = B e e + B o o
  rw [hcrossEO, hcrossOE]
  ring

/-- Pure parity recombination: strict positivity of the production clipped
form on both actual parity carriers gives strict positivity on every nonzero
vector of the entire periodic source core. -/
theorem periodicCore_clippedCriticalForm_re_pos_of_parity
    (hEven : ∀ g : YoshidaPeriodicEvenCore, g ≠ 0 →
      0 < (yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
        ((g.1 : YoshidaClippedPeriodicCore yoshidaA) :
          YoshidaClippedSmooth yoshidaA)
        ((g.1 : YoshidaClippedPeriodicCore yoshidaA) :
          YoshidaClippedSmooth yoshidaA)).re)
    (hOdd : ∀ g : YoshidaPeriodicOddCore, g ≠ 0 →
      0 < (yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
        ((g.1 : YoshidaClippedPeriodicCore yoshidaA) :
          YoshidaClippedSmooth yoshidaA)
        ((g.1 : YoshidaClippedPeriodicCore yoshidaA) :
          YoshidaClippedSmooth yoshidaA)).re)
    (f : YoshidaClippedPeriodicCore yoshidaA) (hf : f ≠ 0) :
    0 < (yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
      (f : YoshidaClippedSmooth yoshidaA)
      (f : YoshidaClippedSmooth yoshidaA)).re := by
  let e : YoshidaPeriodicEvenCore :=
    ⟨periodicCoreEvenPart f, periodicCoreEvenPart_mem_evenCore f⟩
  let o : YoshidaPeriodicOddCore :=
    ⟨periodicCoreOddPart f, periodicCoreOddPart_mem_oddCore f⟩
  have hsplit := clippedCriticalForm_eq_evenPart_add_oddPart f
  by_cases he : periodicCoreEvenPart f = 0
  · have ho : periodicCoreOddPart f ≠ 0 := by
      intro ho
      apply hf
      rw [← periodicCoreEvenPart_add_oddPart f, he, ho]
      exact zero_add 0
    have hoSubtype : o ≠ 0 := by
      intro hzero
      apply ho
      exact congrArg Subtype.val hzero
    have hpos := hOdd o hoSubtype
    have heSmooth :
        ((periodicCoreEvenPart f : YoshidaClippedPeriodicCore yoshidaA) :
          YoshidaClippedSmooth yoshidaA) = 0 := by
      rw [he]
      rfl
    rw [hsplit, heSmooth]
    simp only [map_zero, zero_add]
    simpa only [o] using hpos
  · by_cases ho : periodicCoreOddPart f = 0
    · have heSubtype : e ≠ 0 := by
        intro hzero
        apply he
        exact congrArg Subtype.val hzero
      have hpos := hEven e heSubtype
      have hoSmooth :
          ((periodicCoreOddPart f : YoshidaClippedPeriodicCore yoshidaA) :
            YoshidaClippedSmooth yoshidaA) = 0 := by
        rw [ho]
        rfl
      rw [hsplit, hoSmooth]
      simp only [map_zero, add_zero]
      simpa only [e] using hpos
    · have heSubtype : e ≠ 0 := by
        intro hzero
        apply he
        exact congrArg Subtype.val hzero
      have hoSubtype : o ≠ 0 := by
        intro hzero
        apply ho
        exact congrArg Subtype.val hzero
      have hePos := hEven e heSubtype
      have hoPos := hOdd o hoSubtype
      rw [hsplit]
      simp only [Complex.add_re]
      exact add_pos hePos hoPos

/-- With the odd infinite Schur theorem already discharged, only strict
positivity of the actual even carrier remains as an input to full periodic-core
positivity. -/
theorem periodicCore_clippedCriticalForm_re_pos_of_even
    (hEven : ∀ g : YoshidaPeriodicEvenCore, g ≠ 0 →
      0 < (yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
        ((g.1 : YoshidaClippedPeriodicCore yoshidaA) :
          YoshidaClippedSmooth yoshidaA)
        ((g.1 : YoshidaClippedPeriodicCore yoshidaA) :
          YoshidaClippedSmooth yoshidaA)).re)
    (f : YoshidaClippedPeriodicCore yoshidaA) (hf : f ≠ 0) :
    0 < (yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
      (f : YoshidaClippedSmooth yoshidaA)
      (f : YoshidaClippedSmooth yoshidaA)).re := by
  apply periodicCore_clippedCriticalForm_re_pos_of_parity hEven
  · exact periodicOddCore_clippedCriticalForm_re_pos
  · exact hf

end

end ArithmeticHodge.Analysis.YoshidaParityRecombination

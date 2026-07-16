import ArithmeticHodge.Analysis.YoshidaClippedParityOrthogonality
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseTailRealification
import ArithmeticHodge.Analysis.YoshidaOddInfiniteSchur

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped ComplexConjugate InnerProductSpace

namespace ArithmeticHodge.Analysis.YoshidaOddCompletionConjugationStructural

noncomputable section

open ArithmeticHodge.Analysis
open YoshidaEvenCorrectionReality
open YoshidaFactorTwoPhaseTailRealification
open YoshidaCoercivityNumerics
open YoshidaOddHomogeneousCoercivity
open YoshidaOddInfiniteSchur
open YoshidaOddSpectralMassBridge
open YoshidaWeightedTailBounds

/-!
# Conjugation on the completed actual odd tail

Pointwise conjugation preserves the actual tenth odd Fourier tail and its
production critical form.  Its continuous extension is therefore an
involutive conjugate-linear isometry of `OddTailCompletion`.  The resulting
real and imaginary projections expose the conjugation-fixed real slice
without replacing the complex Hilbert completion by an ad hoc carrier.
-/

private theorem star_I_eq_neg_I : star (Complex.I : ℂ) = -Complex.I :=
  Complex.conj_I

private theorem swap_square_difference_div_four (A B : ℝ) :
    (B * B - A * A) / 4 = -((A * A - B * B) / 4) := by
  ring

/-- Pointwise conjugation of the actual tenth odd tail. -/
def oddTailConj (f : YoshidaOddTenTail) : YoshidaOddTenTail :=
  ⟨periodicCoreConj (f : YoshidaClippedPeriodicCore yoshidaA),
    periodicCoreConj_mem_oddTail yoshidaA_pos 10
      (f : YoshidaClippedPeriodicCore yoshidaA) f.property⟩

@[simp] theorem oddTailConj_toClippedSmooth (f : YoshidaOddTenTail) :
    oddTenTailToClippedSmooth (oddTailConj f) =
      clippedConj (oddTenTailToClippedSmooth f) :=
  rfl

@[simp] theorem oddTailConj_zero :
    oddTailConj (0 : YoshidaOddTenTail) = 0 := by
  apply Subtype.ext
  apply Subtype.ext
  exact clippedConj_zero

@[simp] theorem oddTailConj_add (f g : YoshidaOddTenTail) :
    oddTailConj (f + g) = oddTailConj f + oddTailConj g := by
  apply Subtype.ext
  apply Subtype.ext
  exact clippedConj_add _ _

@[simp] theorem oddTailConj_smul (c : ℂ) (f : YoshidaOddTenTail) :
    oddTailConj (c • f) = star c • oddTailConj f := by
  apply Subtype.ext
  apply Subtype.ext
  exact clippedConj_smul c _

@[simp] theorem oddTailConj_involutive (f : YoshidaOddTenTail) :
    oddTailConj (oddTailConj f) = f := by
  apply Subtype.ext
  apply Subtype.ext
  exact clippedConj_involutive _

/-- Conjugating a pointwise odd clipped function conjugates its critical
sample and contributes the parity sign. -/
theorem yoshidaCriticalSample_clippedConj_of_odd
    {a : ℝ} (ha : 0 < a) (f : YoshidaClippedSmooth a)
    (hf : ∀ x : ℝ, f (-x) = -f x) (v : ℝ) :
    yoshidaCriticalSampleLinear a ha v (clippedConj f) =
      -star (yoshidaCriticalSampleLinear a ha v f) := by
  unfold yoshidaCriticalSampleLinear
  rw [yoshidaCenteredLaplace_clippedConj]
  have hz : star ((v : ℂ) * Complex.I) = -((v : ℂ) * Complex.I) := by
    simp [star_mul]
    ring
  rw [hz, yoshidaCenteredLaplaceLinear_odd_neg ha f hf]
  simp

/-- Pointwise conjugation preserves the production quadratic value on a
pointwise odd clipped vector. -/
theorem yoshidaClippedLocalCriticalPairing_clippedConj_self_of_odd
    {a : ℝ} (ha : 0 < a) (f : YoshidaClippedSmooth a)
    (hf : ∀ x : ℝ, f (-x) = -f x) :
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
      yoshidaCriticalSample_clippedConj_of_odd ha f hf]
    simp only [star_neg, star_star]
    ring
  simp only [yoshidaClippedLocalCriticalPairing]
  rw [yoshidaPositivePolar_clippedConj,
    yoshidaNegativePolar_clippedConj, hcross]
  simp only [star_star]
  ring

/-- Algebraic odd-tail conjugation preserves the restricted production
quadratic form. -/
theorem oddTailCriticalForm_conj_self (f : YoshidaOddTenTail) :
    oddTenTailCriticalForm (oddTailConj f) (oddTailConj f) =
      oddTenTailCriticalForm f f := by
  rw [oddTenTailCriticalForm_apply, oddTenTailCriticalForm_apply,
    oddTailConj_toClippedSmooth]
  exact yoshidaClippedLocalCriticalPairing_clippedConj_self_of_odd
    yoshidaA_pos (oddTenTailToClippedSmooth f)
    (oddTail_pointwise_odd yoshidaA_pos 10
      (f : YoshidaClippedPeriodicCore yoshidaA) f.property)

/-- Conjugation on the algebraic odd-tail form space. -/
def oddFormSpaceConj
    (x : FormSpace oddTenTailPositiveHermitianForm) :
    FormSpace oddTenTailPositiveHermitianForm :=
  FormSpace.of (oddTailConj x.toV)

private theorem oddFormSpace_eq_of_toV_eq
    {x y : FormSpace oddTenTailPositiveHermitianForm}
    (h : x.toV = y.toV) : x = y := by
  rcases x with ⟨x⟩
  rcases y with ⟨y⟩
  cases h
  rfl

@[simp] theorem oddFormSpaceConj_toV
    (x : FormSpace oddTenTailPositiveHermitianForm) :
    (oddFormSpaceConj x).toV = oddTailConj x.toV :=
  rfl

@[simp] theorem oddFormSpaceConj_zero :
    oddFormSpaceConj (0 : FormSpace oddTenTailPositiveHermitianForm) = 0 := by
  apply oddFormSpace_eq_of_toV_eq
  exact oddTailConj_zero

@[simp] theorem oddFormSpaceConj_add
    (x y : FormSpace oddTenTailPositiveHermitianForm) :
    oddFormSpaceConj (x + y) = oddFormSpaceConj x + oddFormSpaceConj y := by
  apply oddFormSpace_eq_of_toV_eq
  exact oddTailConj_add x.toV y.toV

@[simp] theorem oddFormSpaceConj_smul (c : ℂ)
    (x : FormSpace oddTenTailPositiveHermitianForm) :
    oddFormSpaceConj (c • x) = star c • oddFormSpaceConj x := by
  apply oddFormSpace_eq_of_toV_eq
  exact oddTailConj_smul c x.toV

@[simp] theorem oddFormSpaceConj_involutive
    (x : FormSpace oddTenTailPositiveHermitianForm) :
    oddFormSpaceConj (oddFormSpaceConj x) = x := by
  apply oddFormSpace_eq_of_toV_eq
  exact oddTailConj_involutive x.toV

@[simp] theorem norm_oddFormSpaceConj
    (x : FormSpace oddTenTailPositiveHermitianForm) :
    ‖oddFormSpaceConj x‖ = ‖x‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
    FormSpace.norm_sq_eq_form_re, FormSpace.norm_sq_eq_form_re]
  exact congrArg Complex.re (oddTailCriticalForm_conj_self x.toV)

def oddFormSpaceConjNormedAddGroupHom :
    NormedAddGroupHom
      (FormSpace oddTenTailPositiveHermitianForm)
      OddTailCompletion where
  toFun := fun x ↦ (oddFormSpaceConj x : OddTailCompletion)
  map_add' := fun x y ↦ by
    rw [oddFormSpaceConj_add, UniformSpace.Completion.coe_add]
  bound' := ⟨1, fun x ↦ by simp⟩

/-- Continuous conjugation on the completed actual odd tail. -/
noncomputable def oddCompletionConj : OddTailCompletion → OddTailCompletion :=
  oddFormSpaceConjNormedAddGroupHom.extension

@[simp] theorem oddCompletionConj_coe
    (x : FormSpace oddTenTailPositiveHermitianForm) :
    oddCompletionConj (x : OddTailCompletion) =
      (oddFormSpaceConj x : OddTailCompletion) := by
  exact NormedAddGroupHom.extension_coe oddFormSpaceConjNormedAddGroupHom x

theorem continuous_oddCompletionConj : Continuous oddCompletionConj :=
  oddFormSpaceConjNormedAddGroupHom.extension.continuous

@[simp] theorem oddCompletionConj_add (x y : OddTailCompletion) :
    oddCompletionConj (x + y) = oddCompletionConj x + oddCompletionConj y :=
  oddFormSpaceConjNormedAddGroupHom.extension.map_add' x y

@[simp] theorem norm_oddCompletionConj (z : OddTailCompletion) :
    ‖oddCompletionConj z‖ = ‖z‖ := by
  refine UniformSpace.Completion.induction_on z
    (isClosed_eq ?_ ?_) ?_
  · exact continuous_norm.comp continuous_oddCompletionConj
  · exact continuous_norm
  · intro x
    simp

@[simp] theorem oddCompletionConj_smul (c : ℂ) (z : OddTailCompletion) :
    oddCompletionConj (c • z) = star c • oddCompletionConj z := by
  let g := oddFormSpaceConjNormedAddGroupHom.extension
  have heq :
      (fun w : OddTailCompletion ↦ g (c • w)) =
        fun w ↦ star c • g w := by
    apply UniformSpace.Completion.denseRange_coe.equalizer
    · exact g.continuous.comp (continuous_const_smul c)
    · exact (continuous_const_smul (star c)).comp g.continuous
    · funext x
      change oddCompletionConj (c • (x : OddTailCompletion)) =
        star c • oddCompletionConj (x : OddTailCompletion)
      rw [← UniformSpace.Completion.coe_smul,
        oddCompletionConj_coe, oddCompletionConj_coe,
        oddFormSpaceConj_smul, UniformSpace.Completion.coe_smul]
  exact congrFun heq z

@[simp] theorem oddCompletionConj_neg (z : OddTailCompletion) :
    oddCompletionConj (-z) = -oddCompletionConj z := by
  simpa only [neg_one_smul, map_neg, starRingEnd_apply, star_neg,
    star_one] using oddCompletionConj_smul (-1 : ℂ) z

@[simp] theorem oddCompletionConj_sub (x y : OddTailCompletion) :
    oddCompletionConj (x - y) = oddCompletionConj x - oddCompletionConj y := by
  simp only [sub_eq_add_neg, oddCompletionConj_add, oddCompletionConj_neg]

@[simp] theorem oddCompletionConj_involutive (z : OddTailCompletion) :
    oddCompletionConj (oddCompletionConj z) = z := by
  have heq : (fun w : OddTailCompletion ↦
      oddCompletionConj (oddCompletionConj w)) = id := by
    apply UniformSpace.Completion.denseRange_coe.equalizer
    · exact continuous_oddCompletionConj.comp continuous_oddCompletionConj
    · exact continuous_id
    · funext x
      simp
  exact congrFun heq z

noncomputable def oddCompletionConjLinearIsometry :
    OddTailCompletion →ₗᵢ⋆[ℂ] OddTailCompletion where
  toFun := oddCompletionConj
  map_add' := oddCompletionConj_add
  map_smul' := oddCompletionConj_smul
  norm_map' := norm_oddCompletionConj

/-- Completed odd-tail conjugation is antiunitary. -/
theorem inner_oddCompletionConj (x y : OddTailCompletion) :
    ⟪oddCompletionConj x, oddCompletionConj y⟫_ℂ = star ⟪x, y⟫_ℂ := by
  apply Complex.ext
  · change RCLike.re ⟪oddCompletionConj x, oddCompletionConj y⟫_ℂ =
      RCLike.re ⟪x, y⟫_ℂ
    rw [re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four,
      re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four,
      ← oddCompletionConj_add, ← oddCompletionConj_sub,
      norm_oddCompletionConj, norm_oddCompletionConj]
  · change RCLike.im ⟪oddCompletionConj x, oddCompletionConj y⟫_ℂ =
      -RCLike.im ⟪x, y⟫_ℂ
    rw [im_inner_eq_norm_sub_i_smul_mul_self_sub_norm_add_i_smul_mul_self_div_four,
      im_inner_eq_norm_sub_i_smul_mul_self_sub_norm_add_i_smul_mul_self_div_four]
    have hI : oddCompletionConj (Complex.I • y) =
        (-Complex.I) • oddCompletionConj y := by
      calc
        oddCompletionConj (Complex.I • y) =
            star Complex.I • oddCompletionConj y :=
          oddCompletionConj_smul Complex.I y
        _ = (-Complex.I) • oddCompletionConj y :=
          congrArg (fun c : ℂ ↦ c • oddCompletionConj y) star_I_eq_neg_I
    have hplus : oddCompletionConj (x + Complex.I • y) =
        oddCompletionConj x - Complex.I • oddCompletionConj y := by
      calc
        oddCompletionConj (x + Complex.I • y) =
            oddCompletionConj x + oddCompletionConj (Complex.I • y) :=
          oddCompletionConj_add x (Complex.I • y)
        _ = oddCompletionConj x + (-Complex.I) • oddCompletionConj y :=
          congrArg (fun z ↦ oddCompletionConj x + z) hI
        _ = oddCompletionConj x + -(Complex.I • oddCompletionConj y) :=
          congrArg (fun z ↦ oddCompletionConj x + z)
            (neg_smul Complex.I (oddCompletionConj y))
        _ = oddCompletionConj x - Complex.I • oddCompletionConj y :=
          (sub_eq_add_neg _ _).symm
    have hminus : oddCompletionConj (x - Complex.I • y) =
        oddCompletionConj x + Complex.I • oddCompletionConj y := by
      calc
        oddCompletionConj (x - Complex.I • y) =
            oddCompletionConj x - oddCompletionConj (Complex.I • y) :=
          oddCompletionConj_sub x (Complex.I • y)
        _ = oddCompletionConj x - (-Complex.I) • oddCompletionConj y :=
          congrArg (fun z ↦ oddCompletionConj x - z) hI
        _ = oddCompletionConj x - -(Complex.I • oddCompletionConj y) :=
          congrArg (fun z ↦ oddCompletionConj x - z)
            (neg_smul Complex.I (oddCompletionConj y))
        _ = oddCompletionConj x + Complex.I • oddCompletionConj y :=
          sub_neg_eq_add _ _
    have hnplus :
        ‖oddCompletionConj x - Complex.I • oddCompletionConj y‖ =
          ‖x + Complex.I • y‖ := by
      calc
        ‖oddCompletionConj x - Complex.I • oddCompletionConj y‖ =
            ‖oddCompletionConj (x + Complex.I • y)‖ :=
          congrArg norm hplus.symm
        _ = ‖x + Complex.I • y‖ := norm_oddCompletionConj _
    have hnminus :
        ‖oddCompletionConj x + Complex.I • oddCompletionConj y‖ =
          ‖x - Complex.I • y‖ := by
      calc
        ‖oddCompletionConj x + Complex.I • oddCompletionConj y‖ =
            ‖oddCompletionConj (x - Complex.I • y)‖ :=
          congrArg norm hminus.symm
        _ = ‖x - Complex.I • y‖ := norm_oddCompletionConj _
    exact
      (congrArg₂ (fun A B : ℝ ↦ (A * A - B * B) / 4)
        hnplus hnminus).trans
          (swap_square_difference_div_four
            ‖x - Complex.I • y‖ ‖x + Complex.I • y‖)

/-- The full algebraic odd-tail form intertwines pointwise conjugation with
scalar conjugation. -/
theorem oddTailCriticalForm_conj (f g : YoshidaOddTenTail) :
    oddTenTailCriticalForm (oddTailConj f) (oddTailConj g) =
      star (oddTenTailCriticalForm f g) := by
  calc
    oddTenTailCriticalForm (oddTailConj f) (oddTailConj g) =
        ⟪((FormSpace.of (oddTailConj f) :
            FormSpace oddTenTailPositiveHermitianForm) : OddTailCompletion),
          ((FormSpace.of (oddTailConj g) :
            FormSpace oddTenTailPositiveHermitianForm) : OddTailCompletion)⟫_ℂ := by
      rw [FormSpace.completion_inner_coe]
      rfl
    _ = ⟪oddCompletionConj
          ((FormSpace.of f : FormSpace oddTenTailPositiveHermitianForm) :
            OddTailCompletion),
        oddCompletionConj
          ((FormSpace.of g : FormSpace oddTenTailPositiveHermitianForm) :
            OddTailCompletion)⟫_ℂ := by
      rw [oddCompletionConj_coe, oddCompletionConj_coe]
      rfl
    _ = star ⟪((FormSpace.of f :
            FormSpace oddTenTailPositiveHermitianForm) : OddTailCompletion),
          ((FormSpace.of g :
            FormSpace oddTenTailPositiveHermitianForm) : OddTailCompletion)⟫_ℂ :=
      inner_oddCompletionConj _ _
    _ = star (oddTenTailCriticalForm f g) := by
      rw [FormSpace.completion_inner_coe]
      rfl

/-- The conjugation-fixed predicate defining the real slice of the completed
odd tail. -/
def OddCompletionConjugationFixed (z : OddTailCompletion) : Prop :=
  oddCompletionConj z = z

/-- Canonical real projection for the completed conjugation. -/
noncomputable def oddCompletionRealPart (z : OddTailCompletion) :
    OddTailCompletion :=
  (1 / 2 : ℂ) • (z + oddCompletionConj z)

/-- Canonical imaginary-coordinate projection for the completed
conjugation.  This is itself in the fixed real slice. -/
noncomputable def oddCompletionImaginaryPart (z : OddTailCompletion) :
    OddTailCompletion :=
  (-Complex.I / 2 : ℂ) • (z - oddCompletionConj z)

@[simp] theorem oddCompletionConj_realPart (z : OddTailCompletion) :
    oddCompletionConj (oddCompletionRealPart z) =
      oddCompletionRealPart z := by
  unfold oddCompletionRealPart
  rw [oddCompletionConj_smul, oddCompletionConj_add,
    oddCompletionConj_involutive]
  have hhalf : star (1 / 2 : ℂ) = (1 / 2 : ℂ) := by
    norm_num
  rw [hhalf]
  module

@[simp] theorem oddCompletionConj_imaginaryPart (z : OddTailCompletion) :
    oddCompletionConj (oddCompletionImaginaryPart z) =
      oddCompletionImaginaryPart z := by
  unfold oddCompletionImaginaryPart
  rw [oddCompletionConj_smul, oddCompletionConj_sub,
    oddCompletionConj_involutive]
  have hcoeff : star (-Complex.I / 2 : ℂ) =
      Complex.I * (1 / 2 : ℂ) := by
    simp [star_I_eq_neg_I]
    ring
  rw [hcoeff]
  module

theorem oddCompletion_real_add_I_smul_imaginary (z : OddTailCompletion) :
    oddCompletionRealPart z +
        Complex.I • oddCompletionImaginaryPart z = z := by
  unfold oddCompletionRealPart oddCompletionImaginaryPart
  have hcoeff : Complex.I * (-Complex.I / 2 : ℂ) = (1 / 2 : ℂ) := by
    calc
      Complex.I * (-Complex.I / 2 : ℂ) = -(Complex.I ^ 2) / 2 := by
        ring
      _ = (1 / 2 : ℂ) := by
        rw [Complex.I_sq]
        ring
  rw [smul_smul, hcoeff]
  module

theorem oddCompletionRealPart_eq_self_of_fixed
    {z : OddTailCompletion} (hz : OddCompletionConjugationFixed z) :
    oddCompletionRealPart z = z := by
  unfold OddCompletionConjugationFixed at hz
  unfold oddCompletionRealPart
  rw [hz]
  module

theorem oddCompletionImaginaryPart_eq_zero_of_fixed
    {z : OddTailCompletion} (hz : OddCompletionConjugationFixed z) :
    oddCompletionImaginaryPart z = 0 := by
  unfold OddCompletionConjugationFixed at hz
  simp [oddCompletionImaginaryPart, hz]

theorem oddCompletionConjugationFixed_iff_imaginaryPart_eq_zero
    (z : OddTailCompletion) :
    OddCompletionConjugationFixed z ↔ oddCompletionImaginaryPart z = 0 := by
  constructor
  · exact oddCompletionImaginaryPart_eq_zero_of_fixed
  · intro him
    have hdecomp := oddCompletion_real_add_I_smul_imaginary z
    rw [him, smul_zero, add_zero] at hdecomp
    unfold OddCompletionConjugationFixed
    calc
      oddCompletionConj z =
          oddCompletionConj (oddCompletionRealPart z) :=
        congrArg oddCompletionConj hdecomp.symm
      _ = oddCompletionRealPart z := oddCompletionConj_realPart z
      _ = z := hdecomp

end

end ArithmeticHodge.Analysis.YoshidaOddCompletionConjugationStructural

import ArithmeticHodge.Analysis.CenteredAddCircleFourier
import ArithmeticHodge.Analysis.YoshidaClippedDomain
import ArithmeticHodge.Analysis.YoshidaClippedLowModes

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace

namespace ArithmeticHodge.Analysis.YoshidaClippedCircleBridge

noncomputable section

/-!
# Circle coordinates for Yoshida's clipped smooth carrier

Every clipped smooth function has an `L²` class on the centered circle.  This
module proves the linear coordinate map, its exact Fourier coefficients and
series, compatibility with Yoshida's normalized clipped modes, and the
canonical even-low/even-tail plus odd-low/odd-tail decomposition.

This is only a coordinate and parity bridge.  It does **not** assert that the
critical form is bounded on ordinary circle `L²`, that the coordinate map is
injective, that arbitrary closed-tail vectors lift to clipped smooth
functions, or that every clipped smooth function belongs to Yoshida's
periodic source core.  Those are separate Gate 1 obligations.
-/

theorem yoshidaClippedSmooth_memLp_two
    {a : ℝ} (f : YoshidaClippedSmooth a) :
    MemLp (f : ℝ → ℂ) 2 (volume.restrict (Set.Ioc (-a) a)) := by
  have hmeas : AEStronglyMeasurable (f : ℝ → ℂ)
      (volume.restrict (Set.Ioc (-a) a)) :=
    f.property.1.continuousOn.aestronglyMeasurable_of_subset_isCompact
      isCompact_Icc measurableSet_Ioc Ioc_subset_Icc_self
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  exact (f.property.1.continuousOn.norm.pow 2).integrableOn_Icc.mono_set
    Ioc_subset_Icc_self

noncomputable def yoshidaClippedCircleL2
    {a : ℝ} (ha : 0 < a) (f : YoshidaClippedSmooth a) :
    @CircleL2 (2 * a) ⟨by positivity⟩ := by
  letI : Fact (0 < 2 * a) := ⟨by positivity⟩
  exact (centeredLift_memLp ha (yoshidaClippedSmooth_memLp_two f)).toLp
    (centeredLift a (f : ℝ → ℂ))

noncomputable def yoshidaClippedCircleL2Linear
    {a : ℝ} (ha : 0 < a) :
    letI : Fact (0 < 2 * a) := ⟨by positivity⟩
    YoshidaClippedSmooth a →ₗ[ℂ] CircleL2 (T := 2 * a) := by
  letI : Fact (0 < 2 * a) := ⟨by positivity⟩
  refine
    { toFun := yoshidaClippedCircleL2 ha
      map_add' := ?_
      map_smul' := ?_ }
  · intro f g
    apply Lp.ext
    filter_upwards [
      (centeredLift_memLp ha
        (yoshidaClippedSmooth_memLp_two (f + g))).coeFn_toLp,
      (centeredLift_memLp ha
        (yoshidaClippedSmooth_memLp_two f)).coeFn_toLp,
      (centeredLift_memLp ha
        (yoshidaClippedSmooth_memLp_two g)).coeFn_toLp,
      Lp.coeFn_add (yoshidaClippedCircleL2 ha f)
        (yoshidaClippedCircleL2 ha g)] with x hfg hf hg hadd
    calc
      (yoshidaClippedCircleL2 ha (f + g) : CircleL2 (T := 2 * a)) x =
          centeredLift a (f + g) x := hfg
      _ = centeredLift a f x + centeredLift a g x := rfl
      _ = (yoshidaClippedCircleL2 ha f : CircleL2 (T := 2 * a)) x +
          (yoshidaClippedCircleL2 ha g : CircleL2 (T := 2 * a)) x := by
            simp only [yoshidaClippedCircleL2]
            rw [← hf, ← hg]
      _ = ((yoshidaClippedCircleL2 ha f + yoshidaClippedCircleL2 ha g :
          CircleL2 (T := 2 * a))) x := hadd.symm
  · intro c f
    apply Lp.ext
    filter_upwards [
      (centeredLift_memLp ha
        (yoshidaClippedSmooth_memLp_two (c • f))).coeFn_toLp,
      (centeredLift_memLp ha
        (yoshidaClippedSmooth_memLp_two f)).coeFn_toLp,
      Lp.coeFn_smul c (yoshidaClippedCircleL2 ha f)] with x hcf hf hsmul
    calc
      (yoshidaClippedCircleL2 ha (c • f) : CircleL2 (T := 2 * a)) x =
          centeredLift a (c • f) x := hcf
      _ = c • centeredLift a f x := rfl
      _ = c • (yoshidaClippedCircleL2 ha f : CircleL2 (T := 2 * a)) x := by
            simp only [yoshidaClippedCircleL2]
            rw [← hf]
      _ = (c • (yoshidaClippedCircleL2 ha f :
          CircleL2 (T := 2 * a))) x := hsmul.symm

@[simp] theorem yoshidaClippedCircleL2Linear_apply
    {a : ℝ} (ha : 0 < a) (f : YoshidaClippedSmooth a) :
    letI : Fact (0 < 2 * a) := ⟨by positivity⟩
    yoshidaClippedCircleL2Linear ha f = yoshidaClippedCircleL2 ha f := rfl

theorem centeredLift_yoshidaClippedExponential
    {a : ℝ} (ha : 0 < a) (n : ℤ) (x : CenteredAddCircle a) :
    letI : Fact (0 < 2 * a) := ⟨by positivity⟩
    centeredLift a (yoshidaClippedExponential a n : ℝ → ℂ) x =
      ((Real.sqrt (2 * a))⁻¹ : ℂ) * fourier n x := by
  letI : Fact (0 < 2 * a) := ⟨by positivity⟩
  let r := AddCircle.equivIoc (2 * a) (-a) x
  have hr : (r : ℝ) ∈ Set.Ioc (-a) a := by
    simpa only [show -a + 2 * a = a by ring] using r.property
  have hx : ((r : ℝ) : CenteredAddCircle a) = x := by
    have h := (AddCircle.equivIoc (2 * a) (-a)).symm_apply_apply x
    change ((r : ℝ) : CenteredAddCircle a) = x at h
    exact h
  rw [← hx, centeredLift_apply_Ioc _ hr]
  rw [yoshidaClippedExponential_apply_of_mem n (Ioc_subset_Icc_self hr)]
  rw [fourier_coe_apply]
  congr 1
  congr 1
  push_cast
  field_simp [ha.ne']

theorem yoshidaClippedCircleL2_exponential
    {a : ℝ} (ha : 0 < a) (n : ℤ) :
    letI : Fact (0 < 2 * a) := ⟨by positivity⟩
    yoshidaClippedCircleL2 ha (yoshidaClippedExponential a n) =
      lebesgueNormalizedExponential (T := 2 * a) n := by
  letI : Fact (0 < 2 * a) := ⟨by positivity⟩
  apply Lp.ext
  filter_upwards [
    (centeredLift_memLp ha (yoshidaClippedSmooth_memLp_two
      (yoshidaClippedExponential a n))).coeFn_toLp,
    coeFn_fourierLp (T := 2 * a) 2 n,
    Lp.coeFn_smul ((Real.sqrt (2 * a))⁻¹ : ℂ)
      (fourierLp (T := 2 * a) 2 n)] with x hleft hfourier hsmul
  calc
    (yoshidaClippedCircleL2 ha (yoshidaClippedExponential a n) :
        CircleL2 (T := 2 * a)) x =
        centeredLift a (yoshidaClippedExponential a n : ℝ → ℂ) x := hleft
    _ = ((Real.sqrt (2 * a))⁻¹ : ℂ) * fourier n x :=
      centeredLift_yoshidaClippedExponential ha n x
    _ = ((Real.sqrt (2 * a))⁻¹ : ℂ) •
        (fourierLp (T := 2 * a) 2 n : CircleL2 (T := 2 * a)) x := by
      rw [hfourier, smul_eq_mul]
    _ = (((Real.sqrt (2 * a))⁻¹ : ℂ) •
        (fourierLp (T := 2 * a) 2 n : CircleL2 (T := 2 * a))) x :=
      hsmul.symm
    _ = (lebesgueNormalizedExponential (T := 2 * a) n) x := rfl

theorem yoshidaClippedCircleL2_oddMode
    {a : ℝ} (ha : 0 < a) (n : ℕ) :
    letI : Fact (0 < 2 * a) := ⟨by positivity⟩
    yoshidaClippedCircleL2 ha (yoshidaClippedOddMode a n) =
      yoshidaOddMode (T := 2 * a) n := by
  letI : Fact (0 < 2 * a) := ⟨by positivity⟩
  change yoshidaClippedCircleL2Linear ha (yoshidaClippedOddMode a n) = _
  rw [yoshidaClippedOddMode, map_smul, map_sub]
  simp only [yoshidaClippedCircleL2Linear_apply,
    yoshidaClippedCircleL2_exponential]
  rfl

theorem yoshidaClippedCircleL2_evenMode
    {a : ℝ} (ha : 0 < a) (n : ℕ) :
    letI : Fact (0 < 2 * a) := ⟨by positivity⟩
    yoshidaClippedCircleL2 ha (yoshidaClippedEvenMode a n) =
      yoshidaEvenMode (T := 2 * a) n := by
  letI : Fact (0 < 2 * a) := ⟨by positivity⟩
  change yoshidaClippedCircleL2Linear ha (yoshidaClippedEvenMode a n) = _
  rw [yoshidaClippedEvenMode, map_smul, map_add]
  simp only [yoshidaClippedCircleL2Linear_apply,
    yoshidaClippedCircleL2_exponential]
  rfl

theorem yoshidaClippedCircleL2_evenZeroMode
    {a : ℝ} (ha : 0 < a) :
    letI : Fact (0 < 2 * a) := ⟨by positivity⟩
    yoshidaClippedCircleL2 ha (yoshidaClippedEvenZeroMode a) =
      yoshidaEvenZeroMode (T := 2 * a) := by
  letI : Fact (0 < 2 * a) := ⟨by positivity⟩
  exact yoshidaClippedCircleL2_exponential ha 0

theorem yoshidaClippedCircleL2_oddLowMode
    {a : ℝ} (ha : 0 < a) (i : YoshidaOddIndex) :
    letI : Fact (0 < 2 * a) := ⟨by positivity⟩
    yoshidaClippedCircleL2 ha (yoshidaClippedOddLowMode a i) =
      yoshidaOddLowMode (T := 2 * a) i :=
  yoshidaClippedCircleL2_oddMode ha (i.1 + 1)

theorem yoshidaClippedCircleL2_evenLowMode
    {a : ℝ} (ha : 0 < a) (i : YoshidaEvenIndex) :
    letI : Fact (0 < 2 * a) := ⟨by positivity⟩
    yoshidaClippedCircleL2 ha (yoshidaClippedEvenLowMode a i) =
      yoshidaEvenLowMode (T := 2 * a) i := by
  letI : Fact (0 < 2 * a) := ⟨by positivity⟩
  by_cases hi : i.1 = 0
  · simp [yoshidaClippedEvenLowMode, yoshidaEvenLowMode, hi,
      yoshidaClippedCircleL2_evenZeroMode ha]
  · simp [yoshidaClippedEvenLowMode, yoshidaEvenLowMode, hi,
      yoshidaClippedCircleL2_evenMode ha]

theorem fourierCoeff_yoshidaClippedCircleL2
    {a : ℝ} (ha : 0 < a) (f : YoshidaClippedSmooth a) (n : ℤ) :
    letI : Fact (0 < 2 * a) := ⟨by positivity⟩
    fourierCoeff (yoshidaClippedCircleL2 ha f) n =
      centeredFourierCoeff ha (f : ℝ → ℂ) n := by
  letI : Fact (0 < 2 * a) := ⟨by positivity⟩
  exact centeredLift_toLp_fourierCoeff ha
    (yoshidaClippedSmooth_memLp_two f) n

theorem hasSum_yoshidaClippedCircleL2_fourier
    {a : ℝ} (ha : 0 < a) (f : YoshidaClippedSmooth a) :
    letI : Fact (0 < 2 * a) := ⟨by positivity⟩
    HasSum
      (fun n : ℤ ↦ centeredFourierCoeff ha (f : ℝ → ℂ) n • fourierLp 2 n)
      (yoshidaClippedCircleL2 ha f) := by
  letI : Fact (0 < 2 * a) := ⟨by positivity⟩
  exact hasSum_centered_fourier_series_L2 ha
    (yoshidaClippedSmooth_memLp_two f)

theorem yoshidaClippedCircleL2_low_tail_decomposition
    {a : ℝ} (ha : 0 < a) (f : YoshidaClippedSmooth a) :
    letI : Fact (0 < 2 * a) := ⟨by positivity⟩
    let F := yoshidaClippedCircleL2 ha f
    F =
      ((yoshidaEvenLowComponent (T := 2 * a)
          (evenPart (T := 2 * a) F) : CircleL2 (T := 2 * a)) +
        (evenTailRemainder (T := 2 * a) 199
          (evenPart_mem (T := 2 * a) F) : CircleL2 (T := 2 * a))) +
      ((yoshidaOddLowComponent (T := 2 * a)
          (oddPart (T := 2 * a) F) : CircleL2 (T := 2 * a)) +
        (oddTailRemainder (T := 2 * a) 10
          (oddPart_mem (T := 2 * a) F) : CircleL2 (T := 2 * a))) := by
  letI : Fact (0 < 2 * a) := ⟨by positivity⟩
  dsimp only
  calc
    yoshidaClippedCircleL2 ha f =
        evenPart (T := 2 * a) (yoshidaClippedCircleL2 ha f) +
          oddPart (T := 2 * a) (yoshidaClippedCircleL2 ha f) :=
      (evenPart_add_oddPart (T := 2 * a)
        (yoshidaClippedCircleL2 ha f)).symm
    _ = _ := congrArg₂ (· + ·)
      (yoshida_even_twoHundred_modeSpan_add_tail
        (T := 2 * a) (evenPart_mem (T := 2 * a)
          (yoshidaClippedCircleL2 ha f)))
      (yoshida_odd_ten_modeSpan_add_tail
        (T := 2 * a) (oddPart_mem (T := 2 * a)
          (yoshidaClippedCircleL2 ha f)))

theorem exists_yoshidaClippedCircleL2_coefficients_add_tails
    {a : ℝ} (ha : 0 < a) (f : YoshidaClippedSmooth a) :
    letI : Fact (0 < 2 * a) := ⟨by positivity⟩
    let F := yoshidaClippedCircleL2 ha f
    ∃ cEven : YoshidaEvenIndex → ℂ, ∃ cOdd : YoshidaOddIndex → ℂ,
      F =
        ((∑ i, cEven i • yoshidaEvenLowMode (T := 2 * a) i) +
          (evenTailRemainder (T := 2 * a) 199
            (evenPart_mem (T := 2 * a) F) : CircleL2 (T := 2 * a))) +
        ((∑ i, cOdd i • yoshidaOddLowMode (T := 2 * a) i) +
          (oddTailRemainder (T := 2 * a) 10
            (oddPart_mem (T := 2 * a) F) : CircleL2 (T := 2 * a))) := by
  letI : Fact (0 < 2 * a) := ⟨by positivity⟩
  let F := yoshidaClippedCircleL2 ha f
  obtain ⟨cEven, hcEven⟩ := exists_yoshidaEvenLowMode_coefficients
    (T := 2 * a) (evenPart (T := 2 * a) F)
  obtain ⟨cOdd, hcOdd⟩ := exists_yoshidaOddLowMode_coefficients
    (T := 2 * a) (oddPart (T := 2 * a) F)
  refine ⟨cEven, cOdd, ?_⟩
  dsimp only
  rw [hcEven, hcOdd]
  exact yoshidaClippedCircleL2_low_tail_decomposition ha f

end


end ArithmeticHodge.Analysis.YoshidaClippedCircleBridge

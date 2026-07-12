import ArithmeticHodge.Analysis.YoshidaClippedCircleBridge
import ArithmeticHodge.Analysis.YoshidaSectionSixAnalytic

set_option autoImplicit false

open AddCircle Complex MeasureTheory Real Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

namespace ArithmeticHodge.Analysis.YoshidaInfiniteCriticalSample

noncomputable section

open YoshidaClippedCircleBridge
open YoshidaSectionSixAnalytic

/-- The clipped nonperiodic exponential representing evaluation of the
angular Fourier transform at `v`.  Its circle class is used only as an `L²`
Riesz vector for the individual critical-sample functional. -/
def clippedCriticalKernel (a v : ℝ) : YoshidaClippedSmooth a :=
  ⟨fun x ↦ if x ∈ Set.Icc (-a) a then
      Complex.exp (((v * x : ℝ) : ℂ) * Complex.I) else 0, by
    constructor
    · have hcore : ContDiff ℝ ∞ (fun x : ℝ ↦
          Complex.exp (((v * x : ℝ) : ℂ) * Complex.I)) := by
        have hcast : ContDiff ℝ ∞ (fun x : ℝ ↦ (x : ℂ)) :=
          Complex.ofRealCLM.contDiff
        have harg : ContDiff ℝ ∞ (fun x : ℝ ↦
            (((v * x : ℝ) : ℂ) * Complex.I)) := by
          fun_prop
        exact Complex.contDiff_exp.comp harg
      exact hcore.contDiffOn.congr fun x hx ↦ by simp [hx]
    · intro x hx
      simp [hx]⟩

@[simp] theorem clippedCriticalKernel_apply_of_mem
    {a v x : ℝ} (hx : x ∈ Set.Icc (-a) a) :
    clippedCriticalKernel a v x =
      Complex.exp (((v * x : ℝ) : ℂ) * Complex.I) := by
  change (if x ∈ Set.Icc (-a) a then
    Complex.exp (((v * x : ℝ) : ℂ) * Complex.I) else 0) = _
  rw [if_pos hx]

/-- On clipped functions, the individual critical sample is the `L²` inner
product with the clipped exponential kernel.  This is not continuity of the
Yoshida form on ordinary `L²`; it is continuity of one fixed Fourier sample. -/
theorem criticalSample_eq_circle_inner
    {a : ℝ} (ha : 0 < a) (v : ℝ) (f : YoshidaClippedSmooth a) :
    letI : Fact (0 < 2 * a) := ⟨by positivity⟩
    yoshidaCriticalSampleLinear a ha v f =
      ((2 * a : ℝ) : ℂ) *
        inner ℂ
          (yoshidaClippedCircleL2 ha (clippedCriticalKernel a v))
          (yoshidaClippedCircleL2 ha f) := by
  letI : Fact (0 < 2 * a) := ⟨by positivity⟩
  rw [MeasureTheory.L2.inner_def]
  have hinner : (∫ x : AddCircle (2 * a),
      inner ℂ
        ((yoshidaClippedCircleL2 ha (clippedCriticalKernel a v) :
          CircleL2 (T := 2 * a)) x)
        ((yoshidaClippedCircleL2 ha f : CircleL2 (T := 2 * a)) x)
        ∂AddCircle.haarAddCircle) =
    ∫ x : AddCircle (2 * a),
      star (centeredLift a (clippedCriticalKernel a v : ℝ → ℂ) x) *
        centeredLift a (f : ℝ → ℂ) x
        ∂AddCircle.haarAddCircle := by
    apply integral_congr_ae
    filter_upwards [
      (centeredLift_memLp ha (yoshidaClippedSmooth_memLp_two
        (clippedCriticalKernel a v))).coeFn_toLp,
      (centeredLift_memLp ha
        (yoshidaClippedSmooth_memLp_two f)).coeFn_toLp] with x hk hf
    have hk' :
        ((yoshidaClippedCircleL2 ha (clippedCriticalKernel a v) :
          CircleL2 (T := 2 * a)) x) =
            centeredLift a (clippedCriticalKernel a v : ℝ → ℂ) x := hk
    have hf' :
        ((yoshidaClippedCircleL2 ha f : CircleL2 (T := 2 * a)) x) =
          centeredLift a (f : ℝ → ℂ) x := hf
    rw [hk', hf']
    simp only [RCLike.inner_apply', starRingEnd_apply]
  apply Eq.trans ?_ (congrArg (fun z : ℂ ↦ ((2 * a : ℝ) : ℂ) * z) hinner.symm)
  rw [AddCircle.integral_haarAddCircle]
  dsimp only
  have hcancel :
      ((2 * a : ℝ) : ℂ) * (((2 * a : ℝ)⁻¹ : ℝ) : ℂ) = 1 := by
    push_cast
    field_simp [ha.ne']
  change yoshidaCriticalSampleLinear a ha v f =
    ((2 * a : ℝ) : ℂ) *
      ((((2 * a : ℝ)⁻¹ : ℝ) : ℂ) *
        (∫ t : AddCircle (2 * a),
        star (centeredLift a (clippedCriticalKernel a v : ℝ → ℂ) t) *
          centeredLift a (f : ℝ → ℂ) t))
  rw [← mul_assoc, hcancel, one_mul]
  have hsample : yoshidaCriticalSampleLinear a ha v f =
      ∫ x : AddCircle (2 * a),
        star (centeredLift a (clippedCriticalKernel a v : ℝ → ℂ) x) *
          centeredLift a (f : ℝ → ℂ) x := by
    rw [show (fun x : AddCircle (2 * a) ↦
          star (centeredLift a (clippedCriticalKernel a v : ℝ → ℂ) x) *
            centeredLift a (f : ℝ → ℂ) x) =
        centeredLift a (fun x : ℝ ↦
          star (clippedCriticalKernel a v x) * f x) by rfl]
    rw [centeredLift, AddCircle.integral_liftIoc_eq_intervalIntegral]
    rw [show -a + 2 * a = a by ring]
    rw [yoshidaCriticalSampleLinear, yoshidaCenteredLaplaceLinear_apply]
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp only
    have hxIcc : x ∈ Set.Icc (-a) a := by
      simpa only [uIcc_of_le (by linarith : -a ≤ a)] using hx
    rw [clippedCriticalKernel_apply_of_mem hxIcc]
    rw [Complex.star_def, ← Complex.exp_conj, map_mul,
      Complex.conj_ofReal, Complex.conj_I]
    congr 1
    push_cast
    ring_nf
  exact hsample

/-- The fixed critical-sample functional applied to a probability-Haar
Fourier basis vector is the exact removable Section 6 multiplier. -/
theorem scaled_circle_inner_fourierLp_eq_intervalExpQuotient
    {a : ℝ} (ha : 0 < a) (v : ℝ) (n : ℤ) :
    letI : Fact (0 < 2 * a) := ⟨by positivity⟩
    ((2 * a : ℝ) : ℂ) *
        inner ℂ
          (yoshidaClippedCircleL2 ha (clippedCriticalKernel a v))
          (fourierLp (T := 2 * a) 2 n) =
      yoshidaIntervalExpQuotient a
        (yoshidaModeLaplaceExponent a n (v * Complex.I)) := by
  letI : Fact (0 < 2 * a) := ⟨by positivity⟩
  have hsample := criticalSample_eq_circle_inner ha v
    (yoshidaClippedExponential a n)
  have hmode := yoshidaCenteredLaplace_clippedExponential
    ha (v * Complex.I) n
  change yoshidaCriticalSampleLinear a ha v
      (yoshidaClippedExponential a n) =
    ((Real.sqrt (2 * a))⁻¹ : ℂ) *
      yoshidaIntervalExpQuotient a
        (yoshidaModeLaplaceExponent a n (v * Complex.I)) at hmode
  rw [yoshidaClippedCircleL2_exponential ha n,
    lebesgueNormalizedExponential, inner_smul_right] at hsample
  rw [hmode] at hsample
  have hsqrt : Real.sqrt (2 * a) ≠ 0 := by positivity
  have hsqrtC : (((Real.sqrt (2 * a) : ℝ) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hsqrt
  have hsample' :
      yoshidaIntervalExpQuotient a
          (yoshidaModeLaplaceExponent a n (v * Complex.I)) /
            ((Real.sqrt (2 * a) : ℝ) : ℂ) =
        (((2 * a : ℝ) : ℂ) *
          inner ℂ
            (yoshidaClippedCircleL2 ha (clippedCriticalKernel a v))
            (fourierLp (T := 2 * a) 2 n)) /
              ((Real.sqrt (2 * a) : ℝ) : ℂ) := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hsample
  exact ((div_left_inj' hsqrtC).mp hsample').symm

/-- Exact infinite critical-sample expansion with the removable multiplier.
It is obtained by applying one bounded `L²` sample functional to the centered
Fourier `HasSum`; it does not extend the full Yoshida form to ordinary `L²`. -/
theorem hasSum_criticalSample_intervalExpQuotient
    {a : ℝ} (ha : 0 < a) (v : ℝ) (f : YoshidaClippedSmooth a) :
    HasSum
      (fun n : ℤ ↦
        centeredFourierCoeff ha (f : ℝ → ℂ) n *
          yoshidaIntervalExpQuotient a
            (yoshidaModeLaplaceExponent a n (v * Complex.I)))
      (yoshidaCriticalSampleLinear a ha v f) := by
  letI : Fact (0 < 2 * a) := ⟨by positivity⟩
  let K := yoshidaClippedCircleL2 ha (clippedCriticalKernel a v)
  let F := yoshidaClippedCircleL2 ha f
  have hseries : HasSum
      (fun n : ℤ ↦
        centeredFourierCoeff ha (f : ℝ → ℂ) n •
          fourierLp (T := 2 * a) 2 n) F := by
    simpa only [F] using hasSum_yoshidaClippedCircleL2_fourier ha f
  have hinner := (innerSL ℂ K).hasSum hseries
  have hscaled := hinner.mul_left (((2 * a : ℝ) : ℂ))
  have hcrit := criticalSample_eq_circle_inner ha v f
  change yoshidaCriticalSampleLinear a ha v f =
    ((2 * a : ℝ) : ℂ) * inner ℂ K F at hcrit
  simp only [innerSL_apply_apply] at hscaled
  rw [← hcrit] at hscaled
  refine hscaled.congr_fun ?_
  intro n
  dsimp only [K]
  rw [inner_smul_right]
  rw [show ((2 * a : ℝ) : ℂ) *
        (centeredFourierCoeff ha (f : ℝ → ℂ) n *
          inner ℂ
            (yoshidaClippedCircleL2 ha (clippedCriticalKernel a v))
            (fourierLp (T := 2 * a) 2 n)) =
      centeredFourierCoeff ha (f : ℝ → ℂ) n *
        (((2 * a : ℝ) : ℂ) *
          inner ℂ
            (yoshidaClippedCircleL2 ha (clippedCriticalKernel a v))
            (fourierLp (T := 2 * a) 2 n)) by ring]
  rw [scaled_circle_inner_fourierLp_eq_intervalExpQuotient ha v n]

end

end ArithmeticHodge.Analysis.YoshidaInfiniteCriticalSample

import ArithmeticHodge.Analysis.YoshidaClippedCircleBridge

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace

namespace ArithmeticHodge.Analysis.YoshidaClippedCircleFaithful

noncomputable section

open YoshidaClippedCircleBridge

/-!
# Faithfulness and clipped-carrier residuals

The centered-circle coordinate of a clipped smooth function preserves its
Lebesgue `L²` norm exactly.  Consequently the coordinate map is injective:
an almost-everywhere zero coordinate first gives an almost-everywhere zero
function on the clipped interval, and continuity upgrades that equality to
the whole closed interval.

The final theorem subtracts the clipped representatives of the canonical
even and odd low Fourier components.  Its residual remains in the original
clipped smooth carrier, and its circle coordinate is exactly the sum of the
canonical even and odd tails.  No converse lifting or tail-surjectivity claim
is made.
-/

/-- The centered-circle coordinate has exactly the original interval's
Lebesgue `L²` norm. -/
theorem lebesgueNormSq_yoshidaClippedCircleL2
    {a : ℝ} (ha : 0 < a) (f : YoshidaClippedSmooth a) :
    letI : Fact (0 < 2 * a) := ⟨by positivity⟩
    lebesgueNormSq (T := 2 * a) (yoshidaClippedCircleL2 ha f) =
      ∫ x in -a..a, ‖f x‖ ^ 2 := by
  letI : Fact (0 < 2 * a) := ⟨by positivity⟩
  rw [← integral_norm_sq_volume_eq_lebesgueNormSq]
  calc
    ∫ x : CenteredAddCircle a, ‖(yoshidaClippedCircleL2 ha f) x‖ ^ 2 =
        ∫ x : CenteredAddCircle a,
          ‖centeredLift a (f : ℝ → ℂ) x‖ ^ 2 := by
      apply integral_congr_ae
      rw [AddCircle.volume_eq_smul_haarAddCircle]
      exact Measure.ae_smul_measure
        ((centeredLift_memLp ha
          (yoshidaClippedSmooth_memLp_two f)).coeFn_toLp.fun_comp
            (fun z : ℂ ↦ ‖z‖ ^ 2)) _
    _ = ∫ x in -a..a, ‖f x‖ ^ 2 := by
      simpa only [centeredLift, AddCircle.liftIoc_comp_apply,
        show -a + 2 * a = a by ring] using
        (AddCircle.integral_liftIoc_eq_intervalIntegral
          (T := 2 * a) (t := -a) (f := fun x : ℝ ↦ ‖f x‖ ^ 2))

/-- A clipped smooth function is determined by its centered-circle `L²`
coordinate.  The proof derives rather than assumes the required a.e.-zero
statement, then uses continuity on the closed clipped interval. -/
theorem yoshidaClippedCircleL2_injective
    {a : ℝ} (ha : 0 < a) :
    Function.Injective (yoshidaClippedCircleL2 ha :
      YoshidaClippedSmooth a → @CircleL2 (2 * a) ⟨by positivity⟩) := by
  letI : Fact (0 < 2 * a) := ⟨by positivity⟩
  intro f g hfg
  have hcoord : yoshidaClippedCircleL2 ha (f - g) = 0 := by
    change yoshidaClippedCircleL2Linear ha (f - g) = 0
    rw [map_sub]
    simp [yoshidaClippedCircleL2Linear_apply, hfg]
  have hIntegral : ∫ x in -a..a, ‖(f - g) x‖ ^ 2 = 0 := by
    rw [← lebesgueNormSq_yoshidaClippedCircleL2 ha (f - g), hcoord]
    simp [lebesgueNormSq]
  have hContinuous : ContinuousOn
      (fun x : ℝ ↦ ‖(f - g) x‖ ^ 2) (Set.Icc (-a) a) :=
    (f - g).property.1.continuousOn.norm.pow 2
  have hIntervalIntegrable : IntervalIntegrable
      (fun x : ℝ ↦ ‖(f - g) x‖ ^ 2) volume (-a) a :=
    hContinuous.intervalIntegrable_of_Icc (by linarith)
  have hSqAE : (fun x : ℝ ↦ ‖(f - g) x‖ ^ 2) =ᵐ[
      volume.restrict (Set.Ioc (-a) a)] 0 :=
    (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae
      (by linarith)
      (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _)
      hIntervalIntegrable).mp hIntegral
  have hSubAE : (fun x : ℝ ↦ (f - g) x) =ᵐ[
      volume.restrict (Set.Ioc (-a) a)] 0 := by
    filter_upwards [hSqAE] with x hx
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hx)
  have hEqAE : (fun x : ℝ ↦ f x) =ᵐ[
      volume.restrict (Set.Icc (-a) a)] fun x ↦ g x := by
    rw [← Measure.restrict_congr_set Ioc_ae_eq_Icc]
    filter_upwards [hSubAE] with x hx
    change f x - g x = 0 at hx
    exact sub_eq_zero.mp hx
  have hEqOn : Set.EqOn (fun x : ℝ ↦ f x) (fun x ↦ g x)
      (Set.Icc (-a) a) :=
    Measure.eqOn_Icc_of_ae_eq (volume : Measure ℝ)
      (by linarith : -a ≠ a) hEqAE
      f.property.1.continuousOn g.property.1.continuousOn
  apply Subtype.ext
  funext x
  by_cases hx : x ∈ Set.Icc (-a) a
  · exact hEqOn hx
  · rw [yoshidaClippedSmooth_eq_zero_outside f hx,
      yoshidaClippedSmooth_eq_zero_outside g hx]

/-- Every clipped smooth function splits in its original carrier into the
clipped even and odd low modes plus a clipped residual.  The residual's circle
coordinate is precisely the sum of the canonical even and odd Fourier tails.

This only constructs the tail attached to the given clipped function; it does
not claim that an arbitrary vector in either closed tail submodule has a
clipped smooth preimage. -/
theorem exists_yoshidaClipped_low_coefficients_residual_tails
    {a : ℝ} (ha : 0 < a) (f : YoshidaClippedSmooth a) :
    letI : Fact (0 < 2 * a) := ⟨by positivity⟩
    let F := yoshidaClippedCircleL2 ha f
    ∃ cEven : YoshidaEvenIndex → ℂ,
      ∃ cOdd : YoshidaOddIndex → ℂ,
        ∃ residual : YoshidaClippedSmooth a,
          f =
              (∑ i, cEven i • yoshidaClippedEvenLowMode a i) +
                (∑ i, cOdd i • yoshidaClippedOddLowMode a i) +
                residual ∧
            yoshidaClippedCircleL2 ha residual =
              (evenTailRemainder (T := 2 * a) 199
                (evenPart_mem (T := 2 * a) F) : CircleL2 (T := 2 * a)) +
              (oddTailRemainder (T := 2 * a) 10
                (oddPart_mem (T := 2 * a) F) : CircleL2 (T := 2 * a)) := by
  letI : Fact (0 < 2 * a) := ⟨by positivity⟩
  let F := yoshidaClippedCircleL2 ha f
  obtain ⟨cEven, hcEven⟩ := exists_yoshidaEvenLowMode_coefficients
    (T := 2 * a) (evenPart (T := 2 * a) F)
  obtain ⟨cOdd, hcOdd⟩ := exists_yoshidaOddLowMode_coefficients
    (T := 2 * a) (oddPart (T := 2 * a) F)
  dsimp only [F] at hcEven hcOdd ⊢
  let evenLow : YoshidaClippedSmooth a :=
    ∑ i, cEven i • yoshidaClippedEvenLowMode a i
  let oddLow : YoshidaClippedSmooth a :=
    ∑ i, cOdd i • yoshidaClippedOddLowMode a i
  let residual : YoshidaClippedSmooth a := f - evenLow - oddLow
  have hEvenCoordinate : yoshidaClippedCircleL2 ha evenLow =
      ∑ i, cEven i • yoshidaEvenLowMode (T := 2 * a) i := by
    change yoshidaClippedCircleL2Linear ha evenLow = _
    simp [evenLow, yoshidaClippedCircleL2Linear_apply,
      yoshidaClippedCircleL2_evenLowMode]
  have hOddCoordinate : yoshidaClippedCircleL2 ha oddLow =
      ∑ i, cOdd i • yoshidaOddLowMode (T := 2 * a) i := by
    change yoshidaClippedCircleL2Linear ha oddLow = _
    simp [oddLow, yoshidaClippedCircleL2Linear_apply,
      yoshidaClippedCircleL2_oddLowMode]
  refine ⟨cEven, cOdd, residual, ?_, ?_⟩
  · dsimp only [evenLow, oddLow, residual]
    abel
  · change yoshidaClippedCircleL2Linear ha residual = _
    rw [show residual = f - evenLow - oddLow by rfl, map_sub, map_sub]
    simp only [yoshidaClippedCircleL2Linear_apply]
    rw [hEvenCoordinate, hOddCoordinate, hcEven, hcOdd]
    nth_rewrite 1 [yoshidaClippedCircleL2_low_tail_decomposition ha f]
    abel

end

end ArithmeticHodge.Analysis.YoshidaClippedCircleFaithful

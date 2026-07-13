import ArithmeticHodge.Analysis.YoshidaEndpointPositiveDistanceFold
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Prod

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointTriangleInterchange

open UnitIntervalLogEnergyAffine
open YoshidaEndpointPositiveDistanceFold

noncomputable section

/-!
# Triangle-to-square interchange

The positive-distance shear `(t,x) ↦ (x+t,x)` identifies the overlap
triangle with the upper half of the centered square.  Symmetry of the
logarithmic difference kernel then supplies the factor `1/2`.
-/

/-- Positive-distance coordinates in the `(t,x)` plane. -/
def positiveDistanceTriangle : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ p.1 ≤ 2 ∧ -1 ≤ p.2 ∧ p.2 ≤ 1 - p.1}

/-- The upper half of the centered `(y,x)` square. -/
def centeredUpperTriangle : Set (ℝ × ℝ) :=
  {p | -1 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ 1}

/-- The unit-Jacobian shear sends the positive-distance triangle to the
upper centered triangle. -/
theorem setIntegral_positiveDistanceTriangle_shear
    (F : ℝ × ℝ → ℝ) :
    (∫ p : ℝ × ℝ in positiveDistanceTriangle,
      F (p.1 + p.2, p.2)) =
      ∫ p : ℝ × ℝ in centeredUpperTriangle, F p := by
  let S : ℝ × ℝ → ℝ × ℝ := fun p ↦ (p.1 + p.2, p.2)
  have hpre : S ⁻¹' centeredUpperTriangle = positiveDistanceTriangle := by
    ext p
    change (-1 ≤ p.2 ∧ p.2 ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ 1) ↔
      (0 ≤ p.1 ∧ p.1 ≤ 2 ∧ -1 ≤ p.2 ∧ p.2 ≤ 1 - p.1)
    constructor
    · rintro ⟨hxlow, hxy, hyhigh⟩
      constructor
      · linarith
      constructor
      · linarith
      exact ⟨hxlow, by linarith⟩
    · rintro ⟨htlow, _hthigh, hxlow, hxhigh⟩
      exact ⟨hxlow, by linarith, by linarith⟩
  have hmem (p : ℝ × ℝ) :
      S p ∈ centeredUpperTriangle ↔ p ∈ positiveDistanceTriangle := by
    change p ∈ S ⁻¹' centeredUpperTriangle ↔ _
    rw [hpre]
  have hmeasure : MeasurePreserving S
      ((volume : Measure ℝ).prod volume) ((volume : Measure ℝ).prod volume) := by
    exact measurePreserving_add_prod volume volume
  let e : ℝ × ℝ ≃ᵐ ℝ × ℝ :=
    MeasurableEquiv.prodComm.trans
      ((MeasurableEquiv.shearAddRight ℝ).trans MeasurableEquiv.prodComm)
  have he_apply (p : ℝ × ℝ) : e p = S p := by
    change (p.2 + p.1, p.2) = (p.1 + p.2, p.2)
    congr 1
    ring
  have hTmeas : MeasurableSet positiveDistanceTriangle := by
    unfold positiveDistanceTriangle
    measurability
  have hUmeas : MeasurableSet centeredUpperTriangle := by
    unfold centeredUpperTriangle
    measurability
  have hcomp := hmeasure.integral_comp
    (by
      rw [← funext he_apply]
      exact e.measurableEmbedding)
    (centeredUpperTriangle.indicator F)
  calc
    _ = ∫ p : ℝ × ℝ,
        positiveDistanceTriangle.indicator (fun p ↦ F (p.1 + p.2, p.2)) p :=
      (integral_indicator hTmeas).symm
    _ = ∫ p : ℝ × ℝ, (centeredUpperTriangle.indicator F) (S p) := by
      apply integral_congr_ae
      filter_upwards [] with p
      by_cases hp : p ∈ positiveDistanceTriangle
      · rw [Set.indicator_of_mem hp,
          Set.indicator_of_mem ((hmem p).2 hp)]
      · rw [Set.indicator_of_notMem hp,
          Set.indicator_of_notMem (mt (hmem p).1 hp)]
    _ = _ := hcomp
    _ = _ := integral_indicator hUmeas

end

end ArithmeticHodge.Analysis.YoshidaEndpointTriangleInterchange

import ArithmeticHodge.Analysis.MultiplicativeWeilQuadraticEndpoint

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped ContDiff Distributions SchwartzMap FourierTransform

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

private theorem bombieriCriticalMellin_norm_le
    (f : BombieriTest) (v : ℝ) :
    ‖mellin (f : ℝ → ℂ)
        ((1 / 2 : ℝ) + v * Complex.I)‖ ≤
      ‖SchwartzMap.toBoundedContinuousFunction
        (𝓕 (f.logarithmicPullbackSchwartz (1 / 2)))‖ := by
  rw [bombieriMellin_vertical_eq_fourier]
  simpa only [SchwartzMap.toBoundedContinuousFunction_apply] using
    BoundedContinuousFunction.norm_coe_le_norm
      (SchwartzMap.toBoundedContinuousFunction
        (𝓕 (f.logarithmicPullbackSchwartz (1 / 2))))
      (v / (2 * Real.pi))

def bombieriLocalCriticalKernel (v : ℝ) : ℂ :=
  (((Complex.digamma
    ((1 / 4 : ℝ) + (v / 2) * Complex.I)).re -
      Real.log Real.pi : ℝ) : ℂ)

private theorem star_bombieriLocalCriticalKernel (v : ℝ) :
    star (bombieriLocalCriticalKernel v) =
      bombieriLocalCriticalKernel v := by
  simp [bombieriLocalCriticalKernel]

def bombieriLocalCriticalCrossIntegrand
    (f g : BombieriTest) (v : ℝ) : ℂ :=
  bombieriLocalCriticalKernel v *
    star (mellinLinearMap
      ((1 / 2 : ℝ) + v * Complex.I) f) *
    mellinLinearMap
      ((1 / 2 : ℝ) + v * Complex.I) g

theorem bombieriLocalCriticalCrossIntegrand_integrable
    (f g : BombieriTest) :
    Integrable (bombieriLocalCriticalCrossIntegrand f g) := by
  have hg := bombieriCriticalArchKernel_integrable g
  have hf_cont : Continuous (fun v : ℝ ↦
      star (mellin (f : ℝ → ℂ)
        ((1 / 2 : ℝ) + v * Complex.I))) := by
    exact ((bombieriMellin_differentiable f).continuous.comp
      (by fun_prop)).star
  have hprod := hg.bdd_mul hf_cont.aestronglyMeasurable
    (c := ‖SchwartzMap.toBoundedContinuousFunction
      (𝓕 (f.logarithmicPullbackSchwartz (1 / 2)))‖)
    (by
      filter_upwards [] with v
      simpa using bombieriCriticalMellin_norm_le f v)
  apply hprod.congr
  filter_upwards [] with v
  simp only [bombieriLocalCriticalCrossIntegrand,
    bombieriLocalCriticalKernel, mellinLinearMap_apply]
  ring

private theorem integral_bombieriLocalCriticalCrossIntegrand_add_right
    (f g h : BombieriTest) :
    (∫ v : ℝ, bombieriLocalCriticalCrossIntegrand f (g + h) v) =
      (∫ v : ℝ, bombieriLocalCriticalCrossIntegrand f g v) +
        ∫ v : ℝ, bombieriLocalCriticalCrossIntegrand f h v := by
  rw [← integral_add
    (bombieriLocalCriticalCrossIntegrand_integrable f g)
    (bombieriLocalCriticalCrossIntegrand_integrable f h)]
  apply integral_congr_ae
  filter_upwards [] with v
  simp only [bombieriLocalCriticalCrossIntegrand, map_add]
  ring

private theorem integral_bombieriLocalCriticalCrossIntegrand_smul_right
    (f g : BombieriTest) (c : ℂ) :
    (∫ v : ℝ, bombieriLocalCriticalCrossIntegrand f (c • g) v) =
      c * ∫ v : ℝ, bombieriLocalCriticalCrossIntegrand f g v := by
  calc
    (∫ v : ℝ, bombieriLocalCriticalCrossIntegrand f (c • g) v) =
        ∫ v : ℝ, c * bombieriLocalCriticalCrossIntegrand f g v := by
      apply integral_congr_ae
      filter_upwards [] with v
      simp [bombieriLocalCriticalCrossIntegrand]
      ring
    _ = c * ∫ v : ℝ, bombieriLocalCriticalCrossIntegrand f g v :=
      MeasureTheory.integral_const_mul (μ := volume) c _

private theorem integral_bombieriLocalCriticalCrossIntegrand_add_left
    (f g h : BombieriTest) :
    (∫ v : ℝ, bombieriLocalCriticalCrossIntegrand (f + g) h v) =
      (∫ v : ℝ, bombieriLocalCriticalCrossIntegrand f h v) +
        ∫ v : ℝ, bombieriLocalCriticalCrossIntegrand g h v := by
  rw [← integral_add
    (bombieriLocalCriticalCrossIntegrand_integrable f h)
    (bombieriLocalCriticalCrossIntegrand_integrable g h)]
  apply integral_congr_ae
  filter_upwards [] with v
  simp [bombieriLocalCriticalCrossIntegrand, map_add]
  ring

private theorem integral_bombieriLocalCriticalCrossIntegrand_smul_left
    (f g : BombieriTest) (c : ℂ) :
    (∫ v : ℝ, bombieriLocalCriticalCrossIntegrand (c • f) g v) =
      star c * ∫ v : ℝ, bombieriLocalCriticalCrossIntegrand f g v := by
  calc
    (∫ v : ℝ, bombieriLocalCriticalCrossIntegrand (c • f) g v) =
        ∫ v : ℝ, star c * bombieriLocalCriticalCrossIntegrand f g v := by
      apply integral_congr_ae
      filter_upwards [] with v
      simp [bombieriLocalCriticalCrossIntegrand]
      ring
    _ = star c * ∫ v : ℝ, bombieriLocalCriticalCrossIntegrand f g v :=
      MeasureTheory.integral_const_mul (μ := volume) (star c) _

def bombieriLocalCriticalPairing (f g : BombieriTest) : ℂ :=
  star (mellinLinearMap 1 f) * mellinLinearMap 0 g +
    star (mellinLinearMap 0 f) * mellinLinearMap 1 g +
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ v : ℝ, bombieriLocalCriticalCrossIntegrand f g v)

def bombieriLocalCriticalForm :
    BombieriTest →ₗ⋆[ℂ] BombieriTest →ₗ[ℂ] ℂ where
  toFun f :=
    { toFun := bombieriLocalCriticalPairing f
      map_add' := fun g h ↦ by
        simp only [bombieriLocalCriticalPairing, map_add,
          integral_bombieriLocalCriticalCrossIntegrand_add_right]
        ring
      map_smul' := fun c g ↦ by
        simp only [bombieriLocalCriticalPairing, map_smul,
          integral_bombieriLocalCriticalCrossIntegrand_smul_right,
          smul_eq_mul, RingHom.id_apply]
        ring }
  map_add' f g := by
    ext h
    change bombieriLocalCriticalPairing (f + g) h =
      bombieriLocalCriticalPairing f h +
        bombieriLocalCriticalPairing g h
    simp only [bombieriLocalCriticalPairing, map_add,
      integral_bombieriLocalCriticalCrossIntegrand_add_left]
    simp only [star_add]
    ring
  map_smul' c f := by
    ext g
    change bombieriLocalCriticalPairing (c • f) g =
      star c * bombieriLocalCriticalPairing f g
    simp only [bombieriLocalCriticalPairing, map_smul,
      integral_bombieriLocalCriticalCrossIntegrand_smul_left,
      smul_eq_mul]
    simp only [star_mul]
    ring

@[simp] theorem bombieriLocalCriticalForm_apply
    (f g : BombieriTest) :
    bombieriLocalCriticalForm f g =
      bombieriLocalCriticalPairing f g := rfl

private theorem star_integral_bombieriLocalCriticalCrossIntegrand
    (f g : BombieriTest) :
    star (∫ v : ℝ, bombieriLocalCriticalCrossIntegrand g f v) =
      ∫ v : ℝ, bombieriLocalCriticalCrossIntegrand f g v := by
  change (starRingEnd ℂ)
    (∫ v : ℝ, bombieriLocalCriticalCrossIntegrand g f v) = _
  calc
    (starRingEnd ℂ)
        (∫ v : ℝ, bombieriLocalCriticalCrossIntegrand g f v) =
        ∫ v : ℝ, (starRingEnd ℂ)
          (bombieriLocalCriticalCrossIntegrand g f v) :=
      (integral_conj
        (f := fun v : ℝ ↦
          bombieriLocalCriticalCrossIntegrand g f v)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with v
      simp only [bombieriLocalCriticalCrossIntegrand,
        map_mul, starRingEnd_apply, star_star,
        star_bombieriLocalCriticalKernel]
      ring

theorem bombieriLocalCriticalPairing_conj
    (f g : BombieriTest) :
    star (bombieriLocalCriticalPairing g f) =
      bombieriLocalCriticalPairing f g := by
  have hc :
      star ((((1 / (2 * Real.pi) : ℝ) : ℂ))) =
        (((1 / (2 * Real.pi) : ℝ) : ℂ)) := by
    simp
  simp only [bombieriLocalCriticalPairing, star_add, star_mul, star_star,
    star_integral_bombieriLocalCriticalCrossIntegrand]
  rw [hc]
  ring

theorem bombieriLocalCriticalForm_conj_apply
    (f g : BombieriTest) :
    star (bombieriLocalCriticalForm g f) =
      bombieriLocalCriticalForm f g := by
  exact bombieriLocalCriticalPairing_conj f g

def bombieriLocalCriticalQuadraticIntegrand
    (f : BombieriTest) (v : ℝ) : ℂ :=
  bombieriLocalCriticalKernel v *
    (Complex.normSq (mellinLinearMap
      ((1 / 2 : ℝ) + v * Complex.I) f) : ℂ)

def bombieriLocalCriticalQuadratic (f : BombieriTest) : ℂ :=
  ((2 * (mellinLinearMap 1 f *
    star (mellinLinearMap 0 f)).re : ℝ) : ℂ) +
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ v : ℝ, bombieriLocalCriticalQuadraticIntegrand f v)

private theorem star_mul_add_star_mul_eq_two_re
    (a b : ℂ) :
    star a * b + star b * a =
      ((2 * (a * star b).re : ℝ) : ℂ) := by
  apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im] <;> ring

theorem bombieriLocalCriticalPairing_self
    (f : BombieriTest) :
    bombieriLocalCriticalPairing f f =
      bombieriLocalCriticalQuadratic f := by
  rw [bombieriLocalCriticalPairing,
    bombieriLocalCriticalQuadratic,
    star_mul_add_star_mul_eq_two_re]
  congr 1
  apply congrArg (fun z : ℂ ↦
    (((1 / (2 * Real.pi) : ℝ) : ℂ) * z))
  apply integral_congr_ae
  filter_upwards [] with v
  simp [bombieriLocalCriticalCrossIntegrand,
    bombieriLocalCriticalQuadraticIntegrand,
    Complex.normSq_eq_conj_mul_self]
  ring

theorem bombieriLocalCriticalForm_self
    (f : BombieriTest) :
    bombieriLocalCriticalForm f f =
      bombieriLocalCriticalQuadratic f := by
  exact bombieriLocalCriticalPairing_self f

theorem bombieriFunctional_quadratic_eq_bombieriLocalCriticalForm_le_two
    (g : BombieriTest) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    bombieriFunctional (bombieriQuadraticTest g) =
      bombieriLocalCriticalForm g g := by
  rw [bombieriFunctional_quadratic_eq_local_critical_form_le_two
    g ha hab hsupport hratio]
  rw [bombieriLocalCriticalForm_self]
  rfl

end

end ArithmeticHodge.Analysis.MultiplicativeWeil

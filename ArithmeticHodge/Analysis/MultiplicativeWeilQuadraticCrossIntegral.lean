import ArithmeticHodge.Analysis.MultiplicativeWeilQuadraticPolarization

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped ContDiff Distributions

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-!
# Real-space formula for mixed multiplicative autocorrelations

This is the pointwise content hidden by a support decomposition: the mixed
Bombieri test is the sum of the two directed correlations.
-/

/-- Directed multiplicative correlation between two Bombieri tests. -/
def bombieriDirectedCorrelation
    (f g : BombieriTest) (x : ℝ) : ℂ :=
  ∫ y : ℝ in Set.Ioi 0,
    f (x * y) * starRingEnd ℂ (g y)

private theorem bombieriDirectedCorrelation_integrableOn
    (f g : BombieriTest) (x : ℝ) :
    IntegrableOn
      (fun y : ℝ ↦ f (x * y) * starRingEnd ℂ (g y))
      (Set.Ioi 0) := by
  have hcont : Continuous
      (fun y : ℝ ↦ f (x * y) * starRingEnd ℂ (g y)) := by
    fun_prop
  have hgcompact : HasCompactSupport
      (fun y : ℝ ↦ starRingEnd ℂ (g y)) := by
    exact g.hasCompactSupport.comp_left (by simp)
  have hcompact : HasCompactSupport
      (fun y : ℝ ↦ f (x * y) * starRingEnd ℂ (g y)) := by
    simpa only [Pi.mul_apply] using
      hgcompact.mul_left (f := fun y : ℝ ↦ f (x * y))
  exact (hcont.integrable_of_hasCompactSupport hcompact).integrableOn

/-- The mixed quadratic test is exactly the sum of the two directed
correlations. -/
theorem bombieriQuadraticCrossTest_apply
    (f g : BombieriTest) (x : ℝ) :
    bombieriQuadraticCrossTest f g x =
      bombieriDirectedCorrelation f g x +
        bombieriDirectedCorrelation g f x := by
  change bombieriQuadraticTest (f + g) x -
      bombieriQuadraticTest f x - bombieriQuadraticTest g x = _
  simp only [bombieriQuadraticTest_apply]
  unfold autocorrelation bombieriDirectedCorrelation
  change ((∫ y : ℝ in Set.Ioi 0,
      (f (x * y) + g (x * y)) *
        starRingEnd ℂ (f y + g y)) -
      ∫ y : ℝ in Set.Ioi 0,
        f (x * y) * starRingEnd ℂ (f y)) -
      ∫ y : ℝ in Set.Ioi 0,
        g (x * y) * starRingEnd ℂ (g y) =
    (∫ y : ℝ in Set.Ioi 0,
      f (x * y) * starRingEnd ℂ (g y)) +
      ∫ y : ℝ in Set.Ioi 0,
        g (x * y) * starRingEnd ℂ (f y)
  simp only [map_add]
  let A : ℝ → ℂ := fun y ↦
    f (x * y) * starRingEnd ℂ (f y)
  let B : ℝ → ℂ := fun y ↦
    f (x * y) * starRingEnd ℂ (g y)
  let C : ℝ → ℂ := fun y ↦
    g (x * y) * starRingEnd ℂ (f y)
  let D : ℝ → ℂ := fun y ↦
    g (x * y) * starRingEnd ℂ (g y)
  have hA : IntegrableOn A (Set.Ioi 0) := by
    exact bombieriDirectedCorrelation_integrableOn f f x
  have hB : IntegrableOn B (Set.Ioi 0) := by
    exact bombieriDirectedCorrelation_integrableOn f g x
  have hC : IntegrableOn C (Set.Ioi 0) := by
    exact bombieriDirectedCorrelation_integrableOn g f x
  have hD : IntegrableOn D (Set.Ioi 0) := by
    exact bombieriDirectedCorrelation_integrableOn g g x
  have hfull :
      (∫ y : ℝ in Set.Ioi 0,
        (f (x * y) + g (x * y)) *
          (starRingEnd ℂ (f y) + starRingEnd ℂ (g y))) =
        ∫ y : ℝ in Set.Ioi 0,
          (A y + B y) + (C y + D y) := by
    apply integral_congr_ae
    filter_upwards [] with y
    dsimp only [A, B, C, D]
    ring
  have hAB :
      (∫ y : ℝ in Set.Ioi 0, A y + B y) =
        (∫ y : ℝ in Set.Ioi 0, A y) +
          ∫ y : ℝ in Set.Ioi 0, B y := by
    exact integral_add hA hB
  have hCD :
      (∫ y : ℝ in Set.Ioi 0, C y + D y) =
        (∫ y : ℝ in Set.Ioi 0, C y) +
          ∫ y : ℝ in Set.Ioi 0, D y := by
    exact integral_add hC hD
  have hsum :
      (∫ y : ℝ in Set.Ioi 0, (A y + B y) + (C y + D y)) =
        (∫ y : ℝ in Set.Ioi 0, A y + B y) +
          ∫ y : ℝ in Set.Ioi 0, C y + D y := by
    exact integral_add (hA.add hB) (hC.add hD)
  rw [hfull, hsum, hAB, hCD]
  dsimp only [A, B, C, D]
  ring

end

end ArithmeticHodge.Analysis.MultiplicativeWeil

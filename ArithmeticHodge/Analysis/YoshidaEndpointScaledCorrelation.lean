import ArithmeticHodge.Analysis.CenteredEndpointCorrelation

set_option autoImplicit false

open MeasureTheory Real

namespace ArithmeticHodge.Analysis.YoshidaEndpointScaledCorrelation

open CenteredEndpointCorrelation

noncomputable section

/-- Autocorrelation on `[-a,a]` of the dilation `x ↦ w (x/a)`. -/
def scaledEndpointCorrelation (a : ℝ) (w : ℝ → ℝ) (u : ℝ) : ℝ :=
  ∫ x : ℝ in -a..a - u, w ((u + x) / a) * w (x / a)

theorem scaledEndpointCorrelation_mul
    {a : ℝ} (ha : 0 < a) (w : ℝ → ℝ) (t : ℝ) :
    scaledEndpointCorrelation a w (a * t) =
      a * centeredEndpointCorrelation w t := by
  let g : ℝ → ℝ := fun y ↦ w (t + y) * w y
  have hpoint :
      (fun x : ℝ ↦ w ((a * t + x) / a) * w (x / a)) =
        fun x ↦ g (x / a) := by
    funext x
    dsimp only [g]
    congr 2
    field_simp [ha.ne']
  unfold scaledEndpointCorrelation
  rw [hpoint]
  have hsubst :
      (∫ x : ℝ in -a..a - a * t, g (x / a)) =
        a • ∫ y : ℝ in (-a) / a..(a - a * t) / a, g y := by
    exact intervalIntegral.integral_comp_div g ha.ne'
  rw [hsubst]
  simp only [smul_eq_mul]
  unfold centeredEndpointCorrelation
  have hleft : -a / a = (-1 : ℝ) := by field_simp [ha.ne']
  have hright : (a - a * t) / a = 1 - t := by field_simp [ha.ne']
  rw [hleft, hright]

/-- A weighted correlation integral acquires two factors of the dilation:
one from the correlation and one from the outer change of variables. -/
theorem integral_weight_mul_scaledEndpointCorrelation
    {a : ℝ} (ha : 0 < a) (w F : ℝ → ℝ) :
    (∫ u : ℝ in 0..2 * a, F u * scaledEndpointCorrelation a w u) =
      a ^ 2 * ∫ t : ℝ in 0..2,
        F (a * t) * centeredEndpointCorrelation w t := by
  let G : ℝ → ℝ := fun u ↦ F u * scaledEndpointCorrelation a w u
  have hsubst :
      a • (∫ t : ℝ in 0..2, G (a * t)) =
        ∫ u : ℝ in a * 0..a * 2, G u := by
    exact intervalIntegral.smul_integral_comp_mul_left G a
  calc
    (∫ u : ℝ in 0..2 * a, F u * scaledEndpointCorrelation a w u) =
        ∫ u : ℝ in 0..2 * a, G u := rfl
    _ = a * ∫ t : ℝ in 0..2, G (a * t) := by
      simpa only [mul_zero, smul_eq_mul, mul_comm] using hsubst.symm
    _ = a * ∫ t : ℝ in 0..2,
          a * (F (a * t) * centeredEndpointCorrelation w t) := by
      congr 1
      apply intervalIntegral.integral_congr
      intro t _ht
      dsimp only [G]
      rw [scaledEndpointCorrelation_mul ha]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_const_mul]
      ring

end

end ArithmeticHodge.Analysis.YoshidaEndpointScaledCorrelation

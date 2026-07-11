import ArithmeticHodge.Analysis.MultiplicativeWeilQuadraticReality
import ArithmeticHodge.Analysis.MultiplicativeWeilLogSupport

/-!
# Normalized multiplicative dilation

The dilation `g(x) ↦ sqrt(lambda) * g(lambda * x)` preserves Bombieri's
multiplicative autocorrelation.  On the critical logarithmic line it acts by
translation, which lets us center a positive support interval without
changing the quadratic functional.
-/

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped ContDiff Distributions SchwartzMap Topology

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

private def normalizedDilationRaw (lambda : ℝ) (g : BombieriTest) (x : ℝ) : ℂ :=
  ((Real.sqrt lambda : ℝ) : ℂ) * g (lambda * x)

private theorem normalizedDilationRaw_contDiff
    (lambda : ℝ) (g : BombieriTest) :
    ContDiff ℝ ∞ (normalizedDilationRaw lambda g) := by
  unfold normalizedDilationRaw
  have hargument : ContDiff ℝ ∞ (fun x : ℝ ↦ lambda * x) := by
    fun_prop
  exact contDiff_const.mul (g.contDiff.comp hargument)

private theorem normalizedDilationRaw_hasCompactSupport
    (lambda : ℝ) (hlambda : 0 < lambda) (g : BombieriTest) :
    HasCompactSupport (normalizedDilationRaw lambda g) := by
  have hcomp := g.hasCompactSupport.comp_homeomorph
    (Homeomorph.mulLeft₀ lambda hlambda.ne')
  simpa only [normalizedDilationRaw, Function.comp_apply, Pi.mul_apply] using
    hcomp.mul_left

private theorem normalizedDilationRaw_tsupport
    (lambda : ℝ) (hlambda : 0 < lambda) (g : BombieriTest) :
    tsupport (normalizedDilationRaw lambda g) =
      (Homeomorph.mulLeft₀ lambda hlambda.ne') ⁻¹' tsupport g := by
  have hsqrt : Real.sqrt lambda ≠ 0 := (Real.sqrt_pos.2 hlambda).ne'
  have hsupport :
      Function.support (normalizedDilationRaw lambda g) =
        Function.support
          (g ∘ (Homeomorph.mulLeft₀ lambda hlambda.ne' : ℝ → ℝ)) := by
    ext x
    simp only [normalizedDilationRaw, Function.mem_support, ne_eq,
      Function.comp_apply, Homeomorph.coe_mulLeft₀]
    simp [hsqrt]
  rw [tsupport, hsupport]
  exact tsupport_comp_eq_preimage g (Homeomorph.mulLeft₀ lambda hlambda.ne')

private theorem normalizedDilationRaw_tsupport_subset_pos
    (lambda : ℝ) (hlambda : 0 < lambda) (g : BombieriTest) :
    tsupport (normalizedDilationRaw lambda g) ⊆ Set.Ioi 0 := by
  rw [normalizedDilationRaw_tsupport lambda hlambda g]
  intro x hx
  have hproduct : 0 < lambda * x := by
    simpa [positiveHalfLine] using g.tsupport_subset hx
  exact pos_of_mul_pos_right hproduct hlambda.le

/-- The `L²(dx)`-normalized multiplicative dilation of a Bombieri test. -/
def normalizedDilation (lambda : ℝ) (hlambda : 0 < lambda)
    (g : BombieriTest) : BombieriTest :=
  TestFunction.mk
    (normalizedDilationRaw lambda g)
    (normalizedDilationRaw_contDiff lambda g)
    (normalizedDilationRaw_hasCompactSupport lambda hlambda g)
    (by simpa [positiveHalfLine] using
      normalizedDilationRaw_tsupport_subset_pos lambda hlambda g)

@[simp]
theorem normalizedDilation_apply
    (lambda : ℝ) (hlambda : 0 < lambda) (g : BombieriTest) (x : ℝ) :
    normalizedDilation lambda hlambda g x =
      ((Real.sqrt lambda : ℝ) : ℂ) * g (lambda * x) :=
  rfl

/-- Dilation pulls topological support back by multiplication by `lambda`. -/
theorem normalizedDilation_tsupport
    (lambda : ℝ) (hlambda : 0 < lambda) (g : BombieriTest) :
    tsupport (normalizedDilation lambda hlambda g) =
      (Homeomorph.mulLeft₀ lambda hlambda.ne') ⁻¹' tsupport g :=
  normalizedDilationRaw_tsupport lambda hlambda g

theorem normalizedDilation_tsupport_subset_Icc
    (lambda : ℝ) (hlambda : 0 < lambda) (g : BombieriTest)
    {a b : ℝ} (hs : tsupport g ⊆ Set.Icc a b) :
    tsupport (normalizedDilation lambda hlambda g) ⊆
      Set.Icc (a / lambda) (b / lambda) := by
  rw [normalizedDilation_tsupport lambda hlambda g]
  intro x hx
  have hx' := hs hx
  constructor
  · rw [div_le_iff₀ hlambda]
    simpa [mul_comm] using hx'.1
  · rw [le_div_iff₀ hlambda]
    simpa [mul_comm] using hx'.2

/-- Normalized dilation leaves multiplicative autocorrelation unchanged. -/
theorem autocorrelation_normalizedDilation
    (lambda : ℝ) (hlambda : 0 < lambda) (g : BombieriTest) (x : ℝ) :
    autocorrelation (normalizedDilation lambda hlambda g : ℝ → ℂ) x =
      autocorrelation (g : ℝ → ℂ) x := by
  unfold autocorrelation
  let F : ℝ → ℂ := fun y ↦
    g (x * y) * starRingEnd ℂ (g y)
  have hscale := integral_comp_mul_left_Ioi F 0 hlambda
  rw [mul_zero] at hscale
  have hscale' :
      (∫ y : ℝ in Ioi 0, F (lambda * y)) =
        (((lambda⁻¹ : ℝ) : ℂ) * ∫ y : ℝ in Ioi 0, F y) := by
    simpa only [Complex.real_smul] using hscale
  have hsqrt : (((Real.sqrt lambda : ℝ) : ℂ) ^ 2) = (lambda : ℂ) := by
    norm_cast
    exact Real.sq_sqrt hlambda.le
  calc
    (∫ y : ℝ in Ioi 0,
        normalizedDilation lambda hlambda g (x * y) *
          starRingEnd ℂ (normalizedDilation lambda hlambda g y)) =
        ∫ y : ℝ in Ioi 0, (lambda : ℂ) * F (lambda * y) := by
      apply integral_congr_ae
      filter_upwards with y
      simp only [normalizedDilation_apply, F, map_mul,
        Complex.conj_ofReal]
      rw [show lambda * (x * y) = x * (lambda * y) by ring]
      rw [← hsqrt]
      ring
    _ = (lambda : ℂ) * ∫ y : ℝ in Ioi 0, F (lambda * y) := by
      exact integral_const_mul (μ := volume.restrict (Ioi 0))
        (lambda : ℂ) (fun y : ℝ ↦ F (lambda * y))
    _ = (lambda : ℂ) *
        (((lambda⁻¹ : ℝ) : ℂ) * ∫ y : ℝ in Ioi 0, F y) := by
      rw [hscale']
    _ = ∫ y : ℝ in Ioi 0, F y := by
      rw [Complex.ofReal_inv]
      field_simp [hlambda.ne']

theorem bombieriQuadraticTest_normalizedDilation
    (lambda : ℝ) (hlambda : 0 < lambda) (g : BombieriTest) :
    bombieriQuadraticTest (normalizedDilation lambda hlambda g) =
      bombieriQuadraticTest g := by
  ext x
  rw [bombieriQuadraticTest_apply, bombieriQuadraticTest_apply,
    autocorrelation_normalizedDilation]

theorem bombieriFunctional_quadratic_normalizedDilation
    (lambda : ℝ) (hlambda : 0 < lambda) (g : BombieriTest) :
    bombieriFunctional
        (bombieriQuadraticTest (normalizedDilation lambda hlambda g)) =
      bombieriFunctional (bombieriQuadraticTest g) := by
  rw [bombieriQuadraticTest_normalizedDilation]

/-- At the critical exponent, normalized dilation is logarithmic translation. -/
theorem normalizedDilation_logarithmicPullbackSchwartz_critical
    (lambda : ℝ) (hlambda : 0 < lambda) (g : BombieriTest) (u : ℝ) :
    (normalizedDilation lambda hlambda g).logarithmicPullbackSchwartz
        (1 / 2) u =
      g.logarithmicPullbackSchwartz (1 / 2) (u - Real.log lambda) := by
  rw [BombieriTest.logarithmicPullbackSchwartz_apply,
    BombieriTest.logarithmicPullbackSchwartz_apply]
  unfold BombieriTest.logarithmicPullback
  rw [normalizedDilation_apply]
  have hsqrt :
      Real.sqrt lambda = Real.exp (Real.log lambda / 2) := by
    rw [← Real.exp_log (Real.sqrt_pos.2 hlambda),
      Real.log_sqrt hlambda.le]
  have hargument :
      lambda * Real.exp (-u) =
        Real.exp (-(u - Real.log lambda)) := by
    rw [show -(u - Real.log lambda) = Real.log lambda + -u by ring,
      Real.exp_add, Real.exp_log hlambda]
  have hweight :
      Real.exp (-(1 / 2) * u) * Real.sqrt lambda =
        Real.exp (-(1 / 2) * (u - Real.log lambda)) := by
    rw [hsqrt, ← Real.exp_add]
    congr 1
    ring
  rw [hargument, ← mul_assoc, ← Complex.ofReal_mul, hweight]

theorem normalizedDilation_eq_zero_iff
    (lambda : ℝ) (hlambda : 0 < lambda) (g : BombieriTest) :
    normalizedDilation lambda hlambda g = 0 ↔ g = 0 := by
  constructor
  · intro hdilation
    ext x
    have hx := congrArg
      (fun f : BombieriTest ↦ f (x / lambda)) hdilation
    change ((Real.sqrt lambda : ℝ) : ℂ) *
        g (lambda * (x / lambda)) = 0 at hx
    have hargument : lambda * (x / lambda) = x := by
      field_simp [hlambda.ne']
    rw [hargument] at hx
    exact (mul_eq_zero.mp hx).resolve_left
      (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 hlambda).ne')
  · intro hg
    subst g
    ext x
    simp

theorem normalizedDilation_ne_zero_iff
    (lambda : ℝ) (hlambda : 0 < lambda) (g : BombieriTest) :
    normalizedDilation lambda hlambda g ≠ 0 ↔ g ≠ 0 :=
  not_congr (normalizedDilation_eq_zero_iff lambda hlambda g)

/-- Geometric center expressed additively in logarithmic coordinates. -/
def logarithmicCenter (a b : ℝ) : ℝ :=
  Real.exp ((Real.log a + Real.log b) / 2)

/-- Half the logarithmic width of an interval. -/
def logarithmicHalfWidth (a b : ℝ) : ℝ :=
  (Real.log b - Real.log a) / 2

theorem logarithmicCenter_pos (a b : ℝ) :
    0 < logarithmicCenter a b := by
  exact Real.exp_pos _

theorem log_div_logarithmicCenter_left
    {a b : ℝ} (ha : 0 < a) :
    Real.log (a / logarithmicCenter a b) =
      -logarithmicHalfWidth a b := by
  rw [Real.log_div ha.ne' (logarithmicCenter_pos a b).ne']
  simp only [logarithmicCenter, Real.log_exp, logarithmicHalfWidth]
  ring

theorem log_div_logarithmicCenter_right
    {a b : ℝ} (hb : 0 < b) :
    Real.log (b / logarithmicCenter a b) =
      logarithmicHalfWidth a b := by
  rw [Real.log_div hb.ne' (logarithmicCenter_pos a b).ne']
  simp only [logarithmicCenter, Real.log_exp, logarithmicHalfWidth]
  ring

theorem logarithmicCenter_endpoint_reciprocal
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    a / logarithmicCenter a b =
      (b / logarithmicCenter a b)⁻¹ := by
  have hleft : 0 < a / logarithmicCenter a b :=
    div_pos ha (logarithmicCenter_pos a b)
  have hright : 0 < (b / logarithmicCenter a b)⁻¹ :=
    inv_pos.mpr (div_pos hb (logarithmicCenter_pos a b))
  rw [← Real.exp_log hleft, ← Real.exp_log hright]
  congr 1
  rw [log_div_logarithmicCenter_left ha, Real.log_inv,
    log_div_logarithmicCenter_right hb]

theorem logCenteredNormalizedDilation_tsupport_subset_Icc
    (g : BombieriTest) {a b : ℝ}
    (hs : tsupport g ⊆ Set.Icc a b) :
    tsupport (normalizedDilation (logarithmicCenter a b)
      (logarithmicCenter_pos a b) g) ⊆
        Set.Icc (a / logarithmicCenter a b)
          (b / logarithmicCenter a b) :=
  normalizedDilation_tsupport_subset_Icc
    (logarithmicCenter a b) (logarithmicCenter_pos a b) g hs

theorem logCenteredNormalizedDilation_logarithmicPullback_eq_zero_outside
    (g : BombieriTest) {a b u : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hs : tsupport g ⊆ Set.Icc a b)
    (hu : u ∉ Set.Icc (-logarithmicHalfWidth a b)
      (logarithmicHalfWidth a b)) :
    BombieriTest.logarithmicPullbackSchwartz
      (normalizedDilation (logarithmicCenter a b)
        (logarithmicCenter_pos a b) g) (1 / 2) u = 0 := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  refine logarithmicPullbackSchwartz_eq_zero_outside
    (normalizedDilation (logarithmicCenter a b)
      (logarithmicCenter_pos a b) g)
    (div_pos ha (logarithmicCenter_pos a b))
    (logCenteredNormalizedDilation_tsupport_subset_Icc g hs) ?_
  simpa only [log_div_logarithmicCenter_left ha,
    log_div_logarithmicCenter_right hb, neg_neg] using hu

end

end ArithmeticHodge.Analysis.MultiplicativeWeil

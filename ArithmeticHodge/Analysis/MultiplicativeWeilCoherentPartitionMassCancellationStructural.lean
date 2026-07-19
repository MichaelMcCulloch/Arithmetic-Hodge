import ArithmeticHodge.Analysis.MultiplicativeWeilCoherentFejerBoundaryDefectStructural

set_option autoImplicit false

open Complex MeasureTheory Real Set
open scoped ContDiff

namespace ArithmeticHodge.Analysis.MultiplicativeWeilCoherentPartitionMassCancellationStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilCoherentFejerBoundaryDefectStructural

/-- Ordinary mass of the first-slot cutoff derivative against a coherent
parent. -/
def coherentCutoffMass
    (parent : BombieriTest) (eta : ℝ → ℝ) : ℂ :=
  ∫ z : ℝ in Set.Ioi 0,
    ((deriv eta z : ℝ) : ℂ) * parent z

private theorem cutoffSource_integrableOn
    (parent : BombieriTest) (eta : ℝ → ℝ)
    (heta : ContDiff ℝ ∞ eta) :
    IntegrableOn (fun z : ℝ ↦
      ((deriv eta z : ℝ) : ℂ) * parent z) (Set.Ioi 0) := by
  have hderiv : Continuous (deriv eta) :=
    (contDiff_infty_iff_deriv.mp heta).2.continuous
  have hcontinuous : Continuous (fun z : ℝ ↦
      ((deriv eta z : ℝ) : ℂ) * parent z) := by
    fun_prop
  have hcompact : HasCompactSupport (fun z : ℝ ↦
      ((deriv eta z : ℝ) : ℂ) * parent z) := by
    simpa only [Pi.mul_apply] using parent.hasCompactSupport.mul_left
      (f := fun z : ℝ ↦ ((deriv eta z : ℝ) : ℂ))
  exact (hcontinuous.integrable_of_hasCompactSupport hcompact).integrableOn

private theorem weightDerivativeSource_integrableOn
    (parent : BombieriTest) (etas : List (ℝ → ℝ))
    (hsmooth : ∀ eta ∈ etas, ContDiff ℝ ∞ eta) :
    IntegrableOn (fun z : ℝ ↦
      ((weightDerivativeSum etas z : ℝ) : ℂ) * parent z)
      (Set.Ioi 0) := by
  have hweight : Continuous (weightDerivativeSum etas) := by
    induction etas with
    | nil =>
        simpa only [weightDerivativeSum] using
          (continuous_const : Continuous (fun _x : ℝ ↦ (0 : ℝ)))
    | cons eta tail ih =>
        have heta : Continuous (deriv eta) :=
          (contDiff_infty_iff_deriv.mp
            (hsmooth eta (by simp))).2.continuous
        have htail : ∀ theta ∈ tail, ContDiff ℝ ∞ theta := by
          intro theta htheta
          exact hsmooth theta (by simp [htheta])
        simpa only [weightDerivativeSum] using heta.add (ih htail)
  have hcontinuous : Continuous (fun z : ℝ ↦
      ((weightDerivativeSum etas z : ℝ) : ℂ) * parent z) := by
    fun_prop
  have hcompact : HasCompactSupport (fun z : ℝ ↦
      ((weightDerivativeSum etas z : ℝ) : ℂ) * parent z) := by
    simpa only [Pi.mul_apply] using parent.hasCompactSupport.mul_left
      (f := fun z : ℝ ↦ ((weightDerivativeSum etas z : ℝ) : ℂ))
  exact (hcontinuous.integrable_of_hasCompactSupport hcompact).integrableOn

private theorem sum_coherentCutoffMass_eq_integral
    (parent : BombieriTest) (etas : List (ℝ → ℝ))
    (hsmooth : ∀ eta ∈ etas, ContDiff ℝ ∞ eta) :
    (etas.map (coherentCutoffMass parent)).sum =
      ∫ z : ℝ in Set.Ioi 0,
        ((weightDerivativeSum etas z : ℝ) : ℂ) * parent z := by
  induction etas with
  | nil => simp [weightDerivativeSum]
  | cons eta tail ih =>
      have heta : ContDiff ℝ ∞ eta := hsmooth eta (by simp)
      have htail : ∀ theta ∈ tail, ContDiff ℝ ∞ theta := by
        intro theta htheta
        exact hsmooth theta (by simp [htheta])
      simp only [List.map_cons, List.sum_cons]
      rw [ih htail]
      unfold coherentCutoffMass
      rw [← integral_add (cutoffSource_integrableOn parent eta heta)
        (weightDerivativeSource_integrableOn parent tail htail)]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro z _hz
      simp only [weightDerivativeSum]
      push_cast
      ring

/-- Partition unity forces the sum of all ordinary cutoff-derivative masses
to vanish.  This is scalar cancellation only; it does not cancel masses after
they are attached to cell-dependent compensating bumps. -/
theorem sum_coherentCutoffMass_eq_zero
    (parent : BombieriTest) (etas : List (ℝ → ℝ))
    (hsmooth : ∀ eta ∈ etas, ContDiff ℝ ∞ eta)
    (hsum : ∀ z ∈ tsupport parent, weightValueSum etas z = 1) :
    (etas.map (coherentCutoffMass parent)).sum = 0 := by
  rw [sum_coherentCutoffMass_eq_integral parent etas hsmooth]
  apply integral_eq_zero_of_ae
  exact Filter.Eventually.of_forall (fun z ↦ by
    by_cases hp : parent z = 0
    · simp [hp]
    · have hzero := weightDerivativeSum_eq_zero_of_parent_ne_zero
        parent etas hsmooth hsum hp
      simp [hzero])

end

end ArithmeticHodge.Analysis.MultiplicativeWeilCoherentPartitionMassCancellationStructural

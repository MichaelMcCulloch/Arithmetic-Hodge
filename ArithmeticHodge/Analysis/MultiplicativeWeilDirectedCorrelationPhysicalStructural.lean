import ArithmeticHodge.Analysis.MultiplicativeWeilFarSupportSeparationStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilLiSmoothConvolution

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped ComplexConjugate Convolution FourierTransform SchwartzMap

namespace ArithmeticHodge.Analysis.MultiplicativeWeilDirectedCorrelationPhysicalStructural

noncomputable section

open MultiplicativeWeil
open YoshidaBombieriCrossDistribution
open YoshidaBombieriCrossMoments
open YoshidaCauchyPairing

/-!
# Physical realization of the critical logarithmic cross

The critical logarithmic cross-correlation is the conjugate of Bombieri's
directed multiplicative correlation at the exponential lag, with the exact
critical weight `exp (u / 2)`.  This identifies the arithmetic samples in a
far prime shell and the archimedean Cauchy tail as evaluations of one and the
same compactly supported physical function.
-/

/-- The critical logarithmic cross is the weighted physical directed cross.
The orientation is conjugate-linear in `f` and linear in `g`, exactly as on
the left-hand side. -/
theorem bombieriCriticalCrossCorrelation_eq_exp_mul_star_directedCorrelation
    (f g : BombieriTest) (u : ℝ) :
    bombieriCriticalCrossCorrelation f g u =
      ((Real.exp (u / 2) : ℝ) : ℂ) *
        starRingEnd ℂ
          (bombieriDirectedCorrelation f g (Real.exp u)) := by
  let J : ℝ → ℂ := fun y ↦
    (((Real.exp (u / 2) * y : ℝ) : ℂ) *
      starRingEnd ℂ (f (Real.exp u * y))) * g y
  let H : ℝ → ℂ := fun t ↦ J (Real.exp (-t))
  have hphysical :
      ((Real.exp (u / 2) : ℝ) : ℂ) *
          starRingEnd ℂ
            (bombieriDirectedCorrelation f g (Real.exp u)) =
        ∫ y : ℝ in Set.Ioi 0, J y / y := by
    unfold bombieriDirectedCorrelation
    rw [show starRingEnd ℂ
        (∫ y : ℝ in Set.Ioi 0,
          f (Real.exp u * y) * starRingEnd ℂ (g y)) =
        ∫ y : ℝ in Set.Ioi 0,
          starRingEnd ℂ
            (f (Real.exp u * y) * starRingEnd ℂ (g y)) by
      simpa only [RCLike.star_def] using
        (integral_conj (μ := volume.restrict (Set.Ioi 0))
          (f := fun y : ℝ ↦
            f (Real.exp u * y) * starRingEnd ℂ (g y))).symm]
    calc
      ((Real.exp (u / 2) : ℝ) : ℂ) *
          ∫ y : ℝ in Set.Ioi 0,
            starRingEnd ℂ
              (f (Real.exp u * y) * starRingEnd ℂ (g y)) =
          ∫ y : ℝ in Set.Ioi 0,
            ((Real.exp (u / 2) : ℝ) : ℂ) *
              starRingEnd ℂ
                (f (Real.exp u * y) * starRingEnd ℂ (g y)) := by
        exact (MeasureTheory.integral_const_mul
          (μ := volume.restrict (Set.Ioi 0)) _ _).symm
      _ = ∫ y : ℝ in Set.Ioi 0, J y / y := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro y hy
        dsimp only [J]
        rw [map_mul]
        simp only [starRingEnd_apply, star_star, Complex.ofReal_mul]
        change ((Real.exp (u / 2) : ℝ) : ℂ) *
            (starRingEnd ℂ (f (Real.exp u * y)) * g y) =
          ((((Real.exp (u / 2) : ℝ) : ℂ) * (y : ℂ)) *
            starRingEnd ℂ (f (Real.exp u * y)) * g y) / (y : ℂ)
        have hy0 : (y : ℂ) ≠ 0 :=
          Complex.ofReal_ne_zero.mpr (ne_of_gt hy)
        field_simp [hy0]
  rw [bombieriCriticalCrossCorrelation, crossCorrelation_apply]
  calc
    (∫ x : ℝ,
        starRingEnd ℂ
            (f.logarithmicPullbackSchwartz (1 / 2) x) *
          g.logarithmicPullbackSchwartz (1 / 2) (u + x)) =
        ∫ x : ℝ, H (x + u) := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [BombieriTest.logarithmicPullbackSchwartz_apply,
        BombieriTest.logarithmicPullback]
      dsimp only [H, J]
      rw [map_mul, Complex.conj_ofReal]
      have hargf : Real.exp u * Real.exp (-(x + u)) = Real.exp (-x) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hargf]
      have hweight :
          Real.exp (-(1 / 2) * x) *
              Real.exp (-(1 / 2) * (u + x)) =
            Real.exp (u / 2) * Real.exp (-(x + u)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      calc
        ((Real.exp (-(1 / 2) * x) : ℝ) : ℂ) *
              starRingEnd ℂ (f (Real.exp (-x))) *
            (((Real.exp (-(1 / 2) * (u + x)) : ℝ) : ℂ) *
              g (Real.exp (-(u + x)))) =
            ((((Real.exp (-(1 / 2) * x) : ℝ) : ℂ) *
                ((Real.exp (-(1 / 2) * (u + x)) : ℝ) : ℂ)) *
              starRingEnd ℂ (f (Real.exp (-x)))) *
                g (Real.exp (-(u + x))) := by ring
        _ = (((Real.exp (-(1 / 2) * x) *
              Real.exp (-(1 / 2) * (u + x)) : ℝ) : ℂ) *
              starRingEnd ℂ (f (Real.exp (-x)))) *
                g (Real.exp (-(u + x))) := by
            rw [Complex.ofReal_mul]
        _ = (((Real.exp (u / 2) * Real.exp (-(x + u)) : ℝ) : ℂ) *
              starRingEnd ℂ (f (Real.exp (-x)))) *
                g (Real.exp (-(x + u))) := by
            rw [hweight, add_comm u x]
        _ = _ := by ring
    _ = ∫ x : ℝ, H x := MeasureTheory.integral_add_right_eq_self H u
    _ = ∫ y : ℝ in Set.Ioi 0, J y / y := by
      exact (integral_div_eq_integral_comp_expNeg J).symm
    _ = ((Real.exp (u / 2) : ℝ) : ℂ) *
          starRingEnd ℂ
            (bombieriDirectedCorrelation f g (Real.exp u)) :=
      hphysical.symm

/-- With a normalized dilation in the second slot, the same physical cross
is sampled at the inverse-dilated exponential lag. -/
theorem bombieriCriticalCrossCorrelation_normalizedDilation_eq_exp_mul_star_directedCorrelation
    (f g : BombieriTest) (r : ℝ) (hr : 0 < r) (u : ℝ) :
    bombieriCriticalCrossCorrelation f (normalizedDilation r hr g) u =
      ((Real.exp ((u - Real.log r) / 2) : ℝ) : ℂ) *
        starRingEnd ℂ
          (bombieriDirectedCorrelation f g
            (Real.exp (u - Real.log r))) := by
  calc
    bombieriCriticalCrossCorrelation f (normalizedDilation r hr g) u =
        bombieriCriticalCrossCorrelation f g (u - Real.log r) := by
      rw [bombieriCriticalCrossCorrelation, bombieriCriticalCrossCorrelation,
        crossCorrelation_apply, crossCorrelation_apply]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [normalizedDilation_logarithmicPullbackSchwartz_critical]
      congr 2
      ring
    _ = _ :=
      bombieriCriticalCrossCorrelation_eq_exp_mul_star_directedCorrelation
        f g (u - Real.log r)

/-- A directed correlation between tests supported in positive boxes is
supported in the corresponding quotient box. -/
theorem bombieriDirectedCorrelation_eq_zero_outside_supportQuotient
    (f g : BombieriTest) {af bf ag bg x : ℝ}
    (haf : 0 < af) (hag : 0 < ag) (hbg : 0 < bg)
    (hf : tsupport f ⊆ Set.Icc af bf)
    (hg : tsupport g ⊆ Set.Icc ag bg)
    (hx : x ∉ Set.Icc (af / bg) (bf / ag)) :
    bombieriDirectedCorrelation f g x = 0 := by
  unfold bombieriDirectedCorrelation
  apply integral_eq_zero_of_ae
  filter_upwards [] with y
  by_cases hgy : g y = 0
  · rw [hgy, map_zero, mul_zero]
    simp
  by_cases hfy : f (x * y) = 0
  · rw [hfy, zero_mul]
    simp
  exfalso
  have hymem : y ∈ Set.Icc ag bg :=
    hg (subset_tsupport g (Function.mem_support.mpr hgy))
  have hxymem : x * y ∈ Set.Icc af bf :=
    hf (subset_tsupport f (Function.mem_support.mpr hfy))
  have hypos : 0 < y := hag.trans_le hymem.1
  have hxypos : 0 < x * y := haf.trans_le hxymem.1
  have hxpos : 0 < x := pos_of_mul_pos_left hxypos hypos.le
  apply hx
  constructor
  · rw [div_le_iff₀ hbg]
    exact hxymem.1.trans
      (mul_le_mul_of_nonneg_left hymem.2 hxpos.le)
  · rw [le_div_iff₀ hag]
    exact (mul_le_mul_of_nonneg_left hymem.1 hxpos.le).trans hxymem.2

/-- Conjugating the physical directed correlation does not alter its support
quotient. -/
theorem star_bombieriDirectedCorrelation_eq_zero_outside_supportQuotient
    (f g : BombieriTest) {af bf ag bg x : ℝ}
    (haf : 0 < af) (hag : 0 < ag) (hbg : 0 < bg)
    (hf : tsupport f ⊆ Set.Icc af bf)
    (hg : tsupport g ⊆ Set.Icc ag bg)
    (hx : x ∉ Set.Icc (af / bg) (bf / ag)) :
    starRingEnd ℂ (bombieriDirectedCorrelation f g x) = 0 := by
  rw [bombieriDirectedCorrelation_eq_zero_outside_supportQuotient
    f g haf hag hbg hf hg hx, map_zero]

/-- The conjugated physical directed correlation is integrable on the
positive half-line.  Compact quotient support supplies the global majorant;
continuity on that quotient follows from the logarithmic cross bridge. -/
theorem star_bombieriDirectedCorrelation_integrableOn_Ioi
    (f g : BombieriTest) {af bf ag bg : ℝ}
    (haf : 0 < af) (hag : 0 < ag) (hbg : 0 < bg)
    (hf : tsupport f ⊆ Set.Icc af bf)
    (hg : tsupport g ⊆ Set.Icc ag bg) :
    IntegrableOn
      (fun x : ℝ ↦ starRingEnd ℂ (bombieriDirectedCorrelation f g x))
      (Set.Ioi 0) := by
  let S : Set ℝ := Set.Icc (af / bg) (bf / ag)
  let P : ℝ → ℂ := fun x ↦
    (((Real.exp (Real.log x / 2) : ℝ) : ℂ)⁻¹) *
      bombieriCriticalCrossCorrelation f g (Real.log x)
  have hlower : 0 < af / bg := div_pos haf hbg
  have hPcont : ContinuousOn P S := by
    intro x hx
    have hxpos : 0 < x := hlower.trans_le hx.1
    have hlog : ContinuousAt Real.log x :=
      Real.continuousAt_log hxpos.ne'
    have hexp : ContinuousAt
        (fun y : ℝ ↦ ((Real.exp (Real.log y / 2) : ℝ) : ℂ)) x := by
      fun_prop
    have hcorr : ContinuousAt
        (fun y : ℝ ↦ bombieriCriticalCrossCorrelation f g (Real.log y)) x :=
      (bombieriCriticalCrossCorrelation_continuous f g).continuousAt.comp
        hlog
    exact (hexp.inv₀
      (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))).mul hcorr
      |>.continuousWithinAt
  have hphysicalEq : Set.EqOn
      (fun x : ℝ ↦ starRingEnd ℂ (bombieriDirectedCorrelation f g x))
      P S := by
    intro x hx
    have hxpos : 0 < x := hlower.trans_le hx.1
    have hbridge :=
      bombieriCriticalCrossCorrelation_eq_exp_mul_star_directedCorrelation
        f g (Real.log x)
    rw [Real.exp_log hxpos] at hbridge
    dsimp only [P]
    rw [hbridge]
    have hcoeff : ((Real.exp (Real.log x / 2) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
    field_simp [hcoeff]
  have hcontinuous : ContinuousOn
      (fun x : ℝ ↦ starRingEnd ℂ (bombieriDirectedCorrelation f g x)) S :=
    hPcont.congr hphysicalEq
  have hintegrableOn : IntegrableOn
      (fun x : ℝ ↦ starRingEnd ℂ (bombieriDirectedCorrelation f g x)) S :=
    hcontinuous.integrableOn_compact isCompact_Icc
  have hsupport : Function.support
      (fun x : ℝ ↦ starRingEnd ℂ (bombieriDirectedCorrelation f g x)) ⊆ S := by
    intro x hx
    by_contra hxS
    exact hx
      (star_bombieriDirectedCorrelation_eq_zero_outside_supportQuotient
        f g haf hag hbg hf hg (by simpa only [S] using hxS))
  have hintegrable : Integrable
      (fun x : ℝ ↦ starRingEnd ℂ (bombieriDirectedCorrelation f g x)) :=
    (integrableOn_iff_integrable_of_support_subset hsupport).mp hintegrableOn
  exact hintegrable.integrableOn

/-- Every real power moment of the conjugated directed correlation factors
as two critical logarithmic moments.  Compact support of the Bombieri tests
makes the identity valid for every real exponent `q`; no convergence strip
is required. -/
theorem integral_rpow_mul_star_bombieriDirectedCorrelation_eq_criticalMoments
    (f g : BombieriTest) (q : ℝ) :
    (∫ x : ℝ in Set.Ioi 0,
      ((x ^ q : ℝ) : ℂ) *
        starRingEnd ℂ (bombieriDirectedCorrelation f g x)) =
      starRingEnd ℂ
          (bombieriCriticalMoment f (-(q + 1 / 2))) *
        bombieriCriticalMoment g (q + 1 / 2) := by
  let P : ℝ → ℂ := fun x ↦
    starRingEnd ℂ (bombieriDirectedCorrelation f g x)
  let J : ℝ → ℂ := fun x ↦
    (((x * x ^ q : ℝ) : ℂ)) * P x
  let F : ℝ → ℂ := fun u ↦
    ((Real.exp ((q + 1 / 2) * u) : ℝ) : ℂ) *
      bombieriCriticalCrossCorrelation f g u
  have hphysicalChange :
      (∫ x : ℝ in Set.Ioi 0, ((x ^ q : ℝ) : ℂ) * P x) =
        ∫ u : ℝ, J (Real.exp (-u)) := by
    rw [← integral_div_eq_integral_comp_expNeg J]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only [J]
    have hx0 : (x : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt hx)
    change ((x ^ q : ℝ) : ℂ) * P x =
      (((x * x ^ q : ℝ) : ℂ) * P x) / (x : ℂ)
    rw [Complex.ofReal_mul]
    field_simp [hx0]
  have hlogPhysical (u : ℝ) : J (Real.exp (-u)) = F (-u) := by
    have hbridge :=
      bombieriCriticalCrossCorrelation_eq_exp_mul_star_directedCorrelation
        f g (-u)
    have hcoeff :
        Real.exp (-u) * Real.exp (-u) ^ q =
          Real.exp ((q + 1 / 2) * (-u)) * Real.exp ((-u) / 2) := by
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp,
        ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    dsimp only [J, F, P]
    rw [hbridge]
    calc
      (((Real.exp (-u) * Real.exp (-u) ^ q : ℝ) : ℂ) *
          starRingEnd ℂ
            (bombieriDirectedCorrelation f g (Real.exp (-u)))) =
          (((Real.exp ((q + 1 / 2) * (-u)) *
              Real.exp ((-u) / 2) : ℝ) : ℂ) *
            starRingEnd ℂ
              (bombieriDirectedCorrelation f g (Real.exp (-u)))) := by
            rw [hcoeff]
      _ = ((Real.exp ((q + 1 / 2) * (-u)) : ℝ) : ℂ) *
          (((Real.exp ((-u) / 2) : ℝ) : ℂ) *
            starRingEnd ℂ
              (bombieriDirectedCorrelation f g (Real.exp (-u)))) := by
            rw [Complex.ofReal_mul]
            ring
  calc
    (∫ x : ℝ in Set.Ioi 0,
        ((x ^ q : ℝ) : ℂ) *
          starRingEnd ℂ (bombieriDirectedCorrelation f g x)) =
        ∫ x : ℝ in Set.Ioi 0, ((x ^ q : ℝ) : ℂ) * P x := by rfl
    _ = ∫ u : ℝ, J (Real.exp (-u)) := hphysicalChange
    _ = ∫ u : ℝ, F (-u) := by
      apply integral_congr_ae
      filter_upwards [] with u
      exact hlogPhysical u
    _ = ∫ u : ℝ, F u := MeasureTheory.integral_neg_eq_self F volume
    _ = starRingEnd ℂ
          (bombieriCriticalMoment f (-(q + 1 / 2))) *
        bombieriCriticalMoment g (q + 1 / 2) := by
      exact integral_exp_mul_bombieriCriticalCrossCorrelation
        (q + 1 / 2) f g

/-- The continuous main term paired with the far Mangoldt shell is the
product of the two polar Mellin endpoints. -/
theorem integral_star_bombieriDirectedCorrelation_eq_mellin_endpoints
    (f g : BombieriTest) :
    (∫ x : ℝ in Set.Ioi 0,
      starRingEnd ℂ (bombieriDirectedCorrelation f g x)) =
      starRingEnd ℂ (mellin (f : ℝ → ℂ) 1) *
        mellin (g : ℝ → ℂ) 0 := by
  have h :=
    integral_rpow_mul_star_bombieriDirectedCorrelation_eq_criticalMoments
      f g 0
  simpa only [Real.rpow_zero, Complex.ofReal_one, one_mul, zero_add,
    bombieriCriticalMoment_neg_half_eq_mellin_one,
    bombieriCriticalMoment_half_eq_mellin_zero] using h

/-- The inverse odd-power moments occurring in the separated Cauchy tail are
the corresponding rank-one critical moments. -/
theorem integral_inverseOddPower_mul_star_bombieriDirectedCorrelation_eq_criticalMoments
    (f g : BombieriTest) (k : ℕ) :
    (∫ x : ℝ in Set.Ioi 0,
      ((x ^ (-(2 * (k : ℝ) + 3)) : ℝ) : ℂ) *
        starRingEnd ℂ (bombieriDirectedCorrelation f g x)) =
      starRingEnd ℂ
          (bombieriCriticalMoment f (2 * (k : ℝ) + 5 / 2)) *
        bombieriCriticalMoment g (-(2 * (k : ℝ) + 5 / 2)) := by
  have h :=
    integral_rpow_mul_star_bombieriDirectedCorrelation_eq_criticalMoments
      f g (-(2 * (k : ℝ) + 3))
  have hleft :
      -(-(2 * (k : ℝ) + 3) + 1 / 2) = 2 * (k : ℝ) + 5 / 2 := by
    ring
  have hright :
      -(2 * (k : ℝ) + 3) + 1 / 2 = -(2 * (k : ℝ) + 5 / 2) := by
    ring
  rw [hleft] at h
  simpa only [hright] using h

end

end ArithmeticHodge.Analysis.MultiplicativeWeilDirectedCorrelationPhysicalStructural

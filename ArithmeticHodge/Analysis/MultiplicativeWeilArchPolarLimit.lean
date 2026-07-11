import ArithmeticHodge.Analysis.MultiplicativeWeilHorizontalEdge
import ArithmeticHodge.Analysis.MultiplicativeWeilArchPolarGrowth
import ArithmeticHodge.Analysis.MultiplicativeWeilContourLimitAlgebra
import ArithmeticHodge.Analysis.MultiplicativeWeilVerticalBoundary

/-!
# The Bombieri archimedean-polar right-line limit

Finite residue rectangles move the paired archimedean-polar integral from a
right vertical line to the critical line.  Reflection collapses the latter to
the real digamma kernel, while rapid Mellin decay kills the horizontal sides.
This evaluates the last analytic boundary term needed by the unconditional
Bombieri explicit formula.
-/

set_option autoImplicit false

open Complex Filter MeasureTheory Real Set Topology
open scoped ContDiff Distributions Interval Real

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-- The polar terms cancel when the archimedean factor is reflected across
the critical line. -/
theorem bombieriArchPolar_critical_pair (v : ℝ) :
    bombieriArchPolar ((1 / 2 : ℝ) + v * I) +
        bombieriArchPolar (1 - ((1 / 2 : ℝ) + v * I)) =
      (((Complex.digamma ((1 / 4 : ℝ) + (v / 2) * I)).re -
        Real.log Real.pi : ℝ) : ℂ) := by
  let s : ℂ := (1 / 2 : ℝ) + v * I
  have hs0 : s ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [s] at hre
  have hs1 : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [s] at hre
  have hsm1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have h1ms : 1 - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  have hp : (1 / s + 1 / (s - 1)) +
      (1 / (1 - s) + 1 / ((1 - s) - 1)) = 0 := by
    field_simp [hs0, hsm1, h1ms]
    ring
  have hgamma := bombieri_digamma_critical_pair v
  change bombieriArchPolar s + bombieriArchPolar (1 - s) = _
  simp only [bombieriArchPolar]
  linear_combination hp + hgamma

private theorem bombieriArchPolar_vertical_continuous
    (a : ℝ) (ha0 : 0 < a) (ha1 : a ≠ 1) :
    Continuous (fun v : ℝ ↦
      bombieriArchPolar (a + v * I)) := by
  rw [continuous_iff_continuousAt]
  intro v
  have hspos : 0 < (((a : ℝ) : ℂ) + v * I).re := by simpa using ha0
  have hs1 : (((a : ℝ) : ℂ) + v * I) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      mul_zero, zero_mul, sub_self, add_zero, one_re] at hre
    exact ha1 hre
  exact (bombieriArchPolar_differentiableAt hspos hs1).continuousAt.comp'
    (f := fun u : ℝ ↦ ((a : ℝ) : ℂ) + u * I) (by fun_prop)

private theorem bombieriArchPolar_critical_continuous :
    Continuous (fun v : ℝ ↦
      bombieriArchPolar ((1 / 2 : ℝ) + v * I)) := by
  exact bombieriArchPolar_vertical_continuous (1 / 2)
    (by norm_num) (by norm_num)

/-- On every symmetric finite critical-line segment, the direct and
transpose archimedean/polar terms collapse to the real digamma kernel. -/
theorem bombieriCriticalArchPolarInterval_eq_gammaKernel
    (f : BombieriTest) (T : ℝ) :
    (∫ v : ℝ in -T..T,
      (mellin (f : ℝ → ℂ) ((1 / 2 : ℝ) + v * I) +
        mellin (transposeLinearMap f : ℝ → ℂ)
          ((1 / 2 : ℝ) + v * I)) *
        bombieriArchPolar ((1 / 2 : ℝ) + v * I)) =
      ∫ v : ℝ in -T..T,
        (((Complex.digamma ((1 / 4 : ℝ) + (v / 2) * I)).re -
          Real.log Real.pi : ℝ) : ℂ) *
            mellin (f : ℝ → ℂ) ((1 / 2 : ℝ) + v * I) := by
  let s : ℝ → ℂ := fun v ↦ ((1 / 2 : ℝ) : ℂ) + v * I
  let A : ℝ → ℂ := fun v ↦
    mellin (f : ℝ → ℂ) (s v) * bombieriArchPolar (s v)
  let B : ℝ → ℂ := fun v ↦
    mellin (transposeLinearMap f : ℝ → ℂ) (s v) *
      bombieriArchPolar (s v)
  let C : ℝ → ℂ := fun v ↦
    mellin (f : ℝ → ℂ) (s v) * bombieriArchPolar (1 - s v)
  have hscont : Continuous s := by
    dsimp only [s]
    fun_prop
  have hMcont : Continuous (fun v : ℝ ↦ mellin (f : ℝ → ℂ) (s v)) :=
    (bombieriMellin_differentiable f).continuous.comp hscont
  have hMtcont : Continuous (fun v : ℝ ↦
      mellin (transposeLinearMap f : ℝ → ℂ) (s v)) :=
    (bombieriMellin_differentiable (transposeLinearMap f)).continuous.comp hscont
  have hAPcont : Continuous (fun v : ℝ ↦ bombieriArchPolar (s v)) := by
    simpa only [s] using bombieriArchPolar_critical_continuous
  have hAPrefcont : Continuous (fun v : ℝ ↦ bombieriArchPolar (1 - s v)) := by
    have hreflect : (fun v : ℝ ↦ bombieriArchPolar (1 - s v)) =
        fun v : ℝ ↦ bombieriArchPolar (s (-v)) := by
      funext v
      congr 1
      dsimp only [s]
      push_cast
      ring
    rw [hreflect]
    exact hAPcont.comp continuous_neg
  have hAint : IntervalIntegrable A volume (-T) T :=
    (hMcont.mul hAPcont).intervalIntegrable _ _
  have hBint : IntervalIntegrable B volume (-T) T :=
    (hMtcont.mul hAPcont).intervalIntegrable _ _
  have hCint : IntervalIntegrable C volume (-T) T :=
    (hMcont.mul hAPrefcont).intervalIntegrable _ _
  have hBreflect : (∫ v : ℝ in -T..T, B v) =
      ∫ v : ℝ in -T..T, C v := by
    have hsymm : (∫ v : ℝ in -T..T, B v) =
        ∫ v : ℝ in -T..T, B (-v) := by
      have h := intervalIntegral.integral_comp_neg B (a := -T) (b := T)
      simpa only [neg_neg] using h.symm
    rw [hsymm]
    apply intervalIntegral.integral_congr
    intro v _
    have hfun : ((transposeLinearMap f : BombieriTest) : ℝ → ℂ) =
        transpose (f : ℝ → ℂ) := by
      funext x
      exact transposeLinearMap_apply f x
    have hreflect : 1 - s (-v) = s v := by
      dsimp only [s]
      push_cast
      ring
    dsimp only [B, C]
    rw [hfun, mellin_transpose, hreflect]
    congr 2
    dsimp only [s]
    push_cast
    ring
  calc
    (∫ v : ℝ in -T..T,
      (mellin (f : ℝ → ℂ) ((1 / 2 : ℝ) + v * I) +
        mellin (transposeLinearMap f : ℝ → ℂ)
          ((1 / 2 : ℝ) + v * I)) *
        bombieriArchPolar ((1 / 2 : ℝ) + v * I)) =
        ∫ v : ℝ in -T..T, A v + B v := by
          apply intervalIntegral.integral_congr
          intro v _
          simp only [A, B, s]
          ring
    _ = (∫ v : ℝ in -T..T, A v) +
          ∫ v : ℝ in -T..T, B v :=
      intervalIntegral.integral_add hAint hBint
    _ = (∫ v : ℝ in -T..T, A v) +
          ∫ v : ℝ in -T..T, C v := by rw [hBreflect]
    _ = ∫ v : ℝ in -T..T, A v + C v :=
      (intervalIntegral.integral_add hAint hCint).symm
    _ = ∫ v : ℝ in -T..T,
        (((Complex.digamma ((1 / 4 : ℝ) + (v / 2) * I)).re -
          Real.log Real.pi : ℝ) : ℂ) *
            mellin (f : ℝ → ℂ) ((1 / 2 : ℝ) + v * I) := by
      apply intervalIntegral.integral_congr
      intro v _
      dsimp only [A, C, s]
      rw [← mul_add]
      rw [bombieriArchPolar_critical_pair]
      ring

/-- The collapsed critical-line archimedean kernel is genuinely Bochner
integrable. -/
theorem bombieriCriticalArchKernel_integrable (f : BombieriTest) :
    Integrable (fun v : ℝ ↦
      (((Complex.digamma ((1 / 4 : ℝ) + (v / 2) * I)).re -
        Real.log Real.pi : ℝ) : ℂ) *
          mellin (f : ℝ → ℂ) ((1 / 2 : ℝ) + v * I)) := by
  let M : ℝ → ℂ := fun v ↦
    mellin (f : ℝ → ℂ) ((1 / 2 : ℝ) + v * I)
  let G : ℝ → ℂ := fun v ↦
    ((Complex.digamma ((1 / 4 : ℝ) + (v / 2) * I)).re : ℂ) * M v
  have hM : Integrable M := by
    simpa only [M] using f.mellin_verticalIntegrable (1 / 2)
  have hG : Integrable G := by
    simpa only [G, M] using
      digamma_quarter_vertical_re_mul_mellin_integrable f
  refine (hG.sub (hM.const_mul (Real.log Real.pi : ℂ))).congr ?_
  filter_upwards [] with v
  simp only [Pi.sub_apply, G, M]
  push_cast
  ring

/-- The normalized whole-line collapsed critical integral is exactly
Bombieri's real-space archimedean term. -/
theorem bombieriCriticalArchKernel_integral (f : BombieriTest) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ v : ℝ,
          (((Complex.digamma ((1 / 4 : ℝ) + (v / 2) * I)).re -
            Real.log Real.pi : ℝ) : ℂ) *
              mellin (f : ℝ → ℂ) ((1 / 2 : ℝ) + v * I) =
      bombieriArchTerm f := by
  let c : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  let M : ℝ → ℂ := fun v ↦
    mellin (f : ℝ → ℂ) ((1 / 2 : ℝ) + v * I)
  let G : ℝ → ℂ := fun v ↦
    ((Complex.digamma ((1 / 4 : ℝ) + (v / 2) * I)).re : ℂ) * M v
  let K : ℝ → ℂ := fun v ↦
    (((Complex.digamma ((1 / 4 : ℝ) + (v / 2) * I)).re -
      Real.log Real.pi : ℝ) : ℂ) * M v
  have hM : Integrable M := by
    simpa only [M] using f.mellin_verticalIntegrable (1 / 2)
  have hG : Integrable G := by
    simpa only [G, M] using
      digamma_quarter_vertical_re_mul_mellin_integrable f
  have hsplit : (∫ v : ℝ, K v) =
      (∫ v : ℝ, G v) -
        ∫ v : ℝ, (Real.log Real.pi : ℂ) * M v := by
    calc
      (∫ v : ℝ, K v) =
          ∫ v : ℝ, G v - (Real.log Real.pi : ℂ) * M v := by
        apply integral_congr_ae
        filter_upwards [] with v
        simp only [K, G]
        push_cast
        ring
      _ = (∫ v : ℝ, G v) -
          ∫ v : ℝ, (Real.log Real.pi : ℂ) * M v :=
        MeasureTheory.integral_sub hG
          (hM.const_mul (Real.log Real.pi : ℂ))
  have hconst : (∫ v : ℝ, (Real.log Real.pi : ℂ) * M v) =
      (Real.log Real.pi : ℂ) * ∫ v : ℝ, M v := by
    exact MeasureTheory.integral_const_mul (Real.log Real.pi : ℂ) M
  have hMnorm : c * (∫ v : ℝ, M v) = f 1 := by
    simpa only [c, M] using normalized_integral_mellin_eq_apply_one f
  have hgamma : c * (∫ v : ℝ, G v) -
      (Real.log Real.pi : ℂ) * f 1 = bombieriArchTerm f := by
    simpa only [c, G, M] using
      bombieri_digamma_integral_sub_log_pi_eq_archTerm f
  change c * (∫ v : ℝ, K v) = bombieriArchTerm f
  rw [hsplit, hconst]
  calc
    c * ((∫ v : ℝ, G v) -
        (Real.log Real.pi : ℂ) * ∫ v : ℝ, M v) =
        c * (∫ v : ℝ, G v) -
          (Real.log Real.pi : ℂ) * (c * ∫ v : ℝ, M v) := by ring
    _ = c * (∫ v : ℝ, G v) -
          (Real.log Real.pi : ℂ) * f 1 := by rw [hMnorm]
    _ = bombieriArchTerm f := hgamma

/-- Symmetric finite critical-line truncations converge to the evaluated
archimedean term. -/
theorem bombieriCriticalArchKernelInterval_tendsto
    (f : BombieriTest) (T : ℕ → ℝ) (hT : Tendsto T atTop atTop) :
    Tendsto
      (fun n ↦ ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ v : ℝ in -T n..T n,
          (((Complex.digamma ((1 / 4 : ℝ) + (v / 2) * I)).re -
            Real.log Real.pi : ℝ) : ℂ) *
              mellin (f : ℝ → ℂ) ((1 / 2 : ℝ) + v * I))
      atTop (nhds (bombieriArchTerm f)) := by
  let K : ℝ → ℂ := fun v ↦
    (((Complex.digamma ((1 / 4 : ℝ) + (v / 2) * I)).re -
      Real.log Real.pi : ℝ) : ℂ) *
        mellin (f : ℝ → ℂ) ((1 / 2 : ℝ) + v * I)
  have hK : Integrable K := by
    simpa only [K] using bombieriCriticalArchKernel_integrable f
  have hinterval : Tendsto (fun n ↦ ∫ v : ℝ in -T n..T n, K v)
      atTop (nhds (∫ v : ℝ, K v)) :=
    MeasureTheory.intervalIntegral_tendsto_integral hK
      (tendsto_neg_atTop_atBot.comp hT) hT
  have hscaled := hinterval.const_mul (((1 / (2 * Real.pi) : ℝ) : ℂ))
  have heval : (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ v : ℝ, K v) = bombieriArchTerm f := by
    simpa only [K] using bombieriCriticalArchKernel_integral f
  rw [heval] at hscaled
  simpa only [K] using hscaled

/-- The finite residue rectangle solves the normalized right archimedean
vertical integral in terms of its critical vertical integral and signed
horizontal remainder. -/
theorem bombieriArchPolarRightLine_eq_residue_critical_horizontal
    (f : BombieriTest) (sigma T : ℝ)
    (hsigma : 1 < sigma) (hT : 0 < T) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ v : ℝ in -T..T,
          mellin (f : ℝ → ℂ) (sigma + v * I) *
            bombieriArchPolar (sigma + v * I)) =
      mellin (f : ℝ → ℂ) 1 +
        ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ v : ℝ in -T..T,
            mellin (f : ℝ → ℂ) ((1 / 2 : ℝ) + v * I) *
              bombieriArchPolar ((1 / 2 : ℝ) + v * I)) +
        I * ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (bombieriHorizontalLower f bombieriArchPolar (1 / 2) sigma T -
            bombieriHorizontalUpper f bombieriArchPolar (1 / 2) sigma T) := by
  let H : ℂ :=
    bombieriHorizontalLower f bombieriArchPolar (1 / 2) sigma T -
      bombieriHorizontalUpper f bombieriArchPolar (1 / 2) sigma T
  let R : ℂ := ∫ v : ℝ in -T..T,
    mellin (f : ℝ → ℂ) (sigma + v * I) *
      bombieriArchPolar (sigma + v * I)
  let C : ℂ := ∫ v : ℝ in -T..T,
    mellin (f : ℝ → ℂ) ((1 / 2 : ℝ) + v * I) *
      bombieriArchPolar ((1 / 2 : ℝ) + v * I)
  let P : ℂ := mellin (f : ℝ → ℂ) 1
  have hdecomp := rectIntegral_bombieri_horizontal_decomposition
    f bombieriArchPolar (1 / 2) sigma T
  have hres := rectIntegral_bombieriMellin_mul_archPolar
    f sigma T hsigma hT
  have hmain : H + I * R - I * C = 2 * (Real.pi : ℂ) * I * P := by
    calc
      H + I * R - I * C =
          rectIntegral
            (fun s ↦ mellin (f : ℝ → ℂ) s * bombieriArchPolar s)
            (((1 / 2 : ℝ) : ℂ) - T * I)
            ((sigma : ℂ) + T * I) := by
        simpa only [H, R, C] using hdecomp.symm
      _ = 2 * (Real.pi : ℂ) * I * P := by
        simpa only [P] using hres
  have hiR : I * R =
      2 * (Real.pi : ℂ) * I * P + I * C - H := by
    linear_combination hmain
  have hsolve : R = 2 * (Real.pi : ℂ) * P + C + I * H := by
    calc
      R = (-I) * (I * R) := by rw [← mul_assoc]; simp
      _ = (-I) * (2 * (Real.pi : ℂ) * I * P + I * C - H) := by
        rw [hiR]
      _ = 2 * (Real.pi : ℂ) * P + C + I * H := by
        ring_nf
        simp
        ring
  change (((1 / (2 * Real.pi) : ℝ) : ℂ) * R) =
    (P + (((1 / (2 * Real.pi) : ℝ) : ℂ) * C)) +
      (I * ((1 / (2 * Real.pi) : ℝ) : ℂ)) * H
  rw [hsolve]
  push_cast
  field_simp [Real.pi_ne_zero]

/-- Adding the direct and transpose residue rectangles gives the exact
finite right-line formula with both polar Mellin values. -/
theorem bombieriArchPolarRightPair_eq_poles_critical_horizontal
    (f : BombieriTest) (sigma T : ℝ)
    (hsigma : 1 < sigma) (hT : 0 < T) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ v : ℝ in -T..T,
          (mellin (f : ℝ → ℂ) (sigma + v * I) +
            mellin (transposeLinearMap f : ℝ → ℂ) (sigma + v * I)) *
              bombieriArchPolar (sigma + v * I)) =
      mellin (f : ℝ → ℂ) 1 + mellin (f : ℝ → ℂ) 0 +
        ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ v : ℝ in -T..T,
            (mellin (f : ℝ → ℂ) ((1 / 2 : ℝ) + v * I) +
              mellin (transposeLinearMap f : ℝ → ℂ)
                ((1 / 2 : ℝ) + v * I)) *
                  bombieriArchPolar ((1 / 2 : ℝ) + v * I)) +
        (I * ((1 / (2 * Real.pi) : ℝ) : ℂ)) *
          ((bombieriHorizontalLower f bombieriArchPolar
              (1 / 2) sigma T -
            bombieriHorizontalUpper f bombieriArchPolar
              (1 / 2) sigma T) +
          (bombieriHorizontalLower (transposeLinearMap f)
              bombieriArchPolar (1 / 2) sigma T -
            bombieriHorizontalUpper (transposeLinearMap f)
              bombieriArchPolar (1 / 2) sigma T)) := by
  let c : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  let D : ℂ := ∫ v : ℝ in -T..T,
    mellin (f : ℝ → ℂ) (sigma + v * I) *
      bombieriArchPolar (sigma + v * I)
  let Dt : ℂ := ∫ v : ℝ in -T..T,
    mellin (transposeLinearMap f : ℝ → ℂ) (sigma + v * I) *
      bombieriArchPolar (sigma + v * I)
  let C : ℂ := ∫ v : ℝ in -T..T,
    mellin (f : ℝ → ℂ) ((1 / 2 : ℝ) + v * I) *
      bombieriArchPolar ((1 / 2 : ℝ) + v * I)
  let Ct : ℂ := ∫ v : ℝ in -T..T,
    mellin (transposeLinearMap f : ℝ → ℂ) ((1 / 2 : ℝ) + v * I) *
      bombieriArchPolar ((1 / 2 : ℝ) + v * I)
  let H : ℂ :=
    bombieriHorizontalLower f bombieriArchPolar (1 / 2) sigma T -
      bombieriHorizontalUpper f bombieriArchPolar (1 / 2) sigma T
  let Ht : ℂ :=
    bombieriHorizontalLower (transposeLinearMap f) bombieriArchPolar
        (1 / 2) sigma T -
      bombieriHorizontalUpper (transposeLinearMap f) bombieriArchPolar
        (1 / 2) sigma T
  have hdirect : c * D =
      mellin (f : ℝ → ℂ) 1 + c * C + (I * c) * H := by
    simpa only [c, D, C, H, mul_assoc] using
      bombieriArchPolarRightLine_eq_residue_critical_horizontal
        f sigma T hsigma hT
  have hfun : ((transposeLinearMap f : BombieriTest) : ℝ → ℂ) =
      transpose (f : ℝ → ℂ) := by
    funext x
    exact transposeLinearMap_apply f x
  have hMt1 : mellin (transposeLinearMap f : ℝ → ℂ) 1 =
      mellin (f : ℝ → ℂ) 0 := by
    rw [hfun, mellin_transpose]
    norm_num
  have htrans : c * Dt =
      mellin (f : ℝ → ℂ) 0 + c * Ct + (I * c) * Ht := by
    have h :=
      bombieriArchPolarRightLine_eq_residue_critical_horizontal
        (transposeLinearMap f) sigma T hsigma hT
    simpa only [c, Dt, Ct, Ht, hMt1, mul_assoc] using h
  have hlineSigma : Continuous (fun v : ℝ ↦ ((sigma : ℂ) + v * I)) := by
    fun_prop
  have hMdirectSigma : Continuous (fun v : ℝ ↦
      mellin (f : ℝ → ℂ) (sigma + v * I)) :=
    (bombieriMellin_differentiable f).continuous.comp hlineSigma
  have hMtransSigma : Continuous (fun v : ℝ ↦
      mellin (transposeLinearMap f : ℝ → ℂ) (sigma + v * I)) :=
    (bombieriMellin_differentiable (transposeLinearMap f)).continuous.comp
      hlineSigma
  have hAPSigma : Continuous (fun v : ℝ ↦
      bombieriArchPolar (sigma + v * I)) :=
    bombieriArchPolar_vertical_continuous sigma
      (by linarith) (ne_of_gt hsigma)
  have hDint : IntervalIntegrable
      (fun v : ℝ ↦ mellin (f : ℝ → ℂ) (sigma + v * I) *
        bombieriArchPolar (sigma + v * I)) volume (-T) T :=
    (hMdirectSigma.mul hAPSigma).intervalIntegrable _ _
  have hDtint : IntervalIntegrable
      (fun v : ℝ ↦ mellin (transposeLinearMap f : ℝ → ℂ)
          (sigma + v * I) * bombieriArchPolar (sigma + v * I))
      volume (-T) T :=
    (hMtransSigma.mul hAPSigma).intervalIntegrable _ _
  have hright : (∫ v : ℝ in -T..T,
      (mellin (f : ℝ → ℂ) (sigma + v * I) +
        mellin (transposeLinearMap f : ℝ → ℂ) (sigma + v * I)) *
          bombieriArchPolar (sigma + v * I)) = D + Dt := by
    calc
      (∫ v : ℝ in -T..T,
        (mellin (f : ℝ → ℂ) (sigma + v * I) +
          mellin (transposeLinearMap f : ℝ → ℂ) (sigma + v * I)) *
            bombieriArchPolar (sigma + v * I)) =
          ∫ v : ℝ in -T..T,
            mellin (f : ℝ → ℂ) (sigma + v * I) *
                bombieriArchPolar (sigma + v * I) +
              mellin (transposeLinearMap f : ℝ → ℂ) (sigma + v * I) *
                bombieriArchPolar (sigma + v * I) := by
        apply intervalIntegral.integral_congr
        intro v _
        ring
      _ = D + Dt := by
        simpa only [D, Dt] using
          intervalIntegral.integral_add hDint hDtint
  have hlineCritical : Continuous (fun v : ℝ ↦
      (((1 / 2 : ℝ) : ℂ) + v * I)) := by
    fun_prop
  have hMdirectCritical : Continuous (fun v : ℝ ↦
      mellin (f : ℝ → ℂ) ((1 / 2 : ℝ) + v * I)) :=
    (bombieriMellin_differentiable f).continuous.comp hlineCritical
  have hMtransCritical : Continuous (fun v : ℝ ↦
      mellin (transposeLinearMap f : ℝ → ℂ)
        ((1 / 2 : ℝ) + v * I)) :=
    (bombieriMellin_differentiable (transposeLinearMap f)).continuous.comp
      hlineCritical
  have hCint : IntervalIntegrable
      (fun v : ℝ ↦ mellin (f : ℝ → ℂ) ((1 / 2 : ℝ) + v * I) *
        bombieriArchPolar ((1 / 2 : ℝ) + v * I)) volume (-T) T :=
    (hMdirectCritical.mul bombieriArchPolar_critical_continuous)
      |>.intervalIntegrable _ _
  have hCtint : IntervalIntegrable
      (fun v : ℝ ↦ mellin (transposeLinearMap f : ℝ → ℂ)
          ((1 / 2 : ℝ) + v * I) *
        bombieriArchPolar ((1 / 2 : ℝ) + v * I)) volume (-T) T :=
    (hMtransCritical.mul bombieriArchPolar_critical_continuous)
      |>.intervalIntegrable _ _
  have hcritical : (∫ v : ℝ in -T..T,
      (mellin (f : ℝ → ℂ) ((1 / 2 : ℝ) + v * I) +
        mellin (transposeLinearMap f : ℝ → ℂ)
          ((1 / 2 : ℝ) + v * I)) *
            bombieriArchPolar ((1 / 2 : ℝ) + v * I)) = C + Ct := by
    calc
      (∫ v : ℝ in -T..T,
        (mellin (f : ℝ → ℂ) ((1 / 2 : ℝ) + v * I) +
          mellin (transposeLinearMap f : ℝ → ℂ)
            ((1 / 2 : ℝ) + v * I)) *
              bombieriArchPolar ((1 / 2 : ℝ) + v * I)) =
          ∫ v : ℝ in -T..T,
            mellin (f : ℝ → ℂ) ((1 / 2 : ℝ) + v * I) *
                bombieriArchPolar ((1 / 2 : ℝ) + v * I) +
              mellin (transposeLinearMap f : ℝ → ℂ)
                  ((1 / 2 : ℝ) + v * I) *
                bombieriArchPolar ((1 / 2 : ℝ) + v * I) := by
        apply intervalIntegral.integral_congr
        intro v _
        ring
      _ = C + Ct := by
        simpa only [C, Ct] using intervalIntegral.integral_add hCint hCtint
  change c * (∫ v : ℝ in -T..T,
      (mellin (f : ℝ → ℂ) (sigma + v * I) +
        mellin (transposeLinearMap f : ℝ → ℂ) (sigma + v * I)) *
          bombieriArchPolar (sigma + v * I)) =
    mellin (f : ℝ → ℂ) 1 + mellin (f : ℝ → ℂ) 0 +
      c * (∫ v : ℝ in -T..T,
        (mellin (f : ℝ → ℂ) ((1 / 2 : ℝ) + v * I) +
          mellin (transposeLinearMap f : ℝ → ℂ)
            ((1 / 2 : ℝ) + v * I)) *
              bombieriArchPolar ((1 / 2 : ℝ) + v * I)) +
      (I * c) * (H + Ht)
  rw [hright, hcritical, mul_add, hdirect, htrans]
  ring

/-- Sixth-order uniform Mellin decay absorbs the quartic archimedean/polar
growth on both horizontal sides. -/
theorem bombieriArchPolarHorizontalPair_tendsto_zero
    (f : BombieriTest) (sigma : ℝ) (T : ℕ → ℝ)
    (hsigma : 1 < sigma) (hT : Tendsto T atTop atTop)
    (hT4 : ∀ n, 4 ≤ T n) :
    Tendsto
        (fun n ↦ bombieriHorizontalUpper f bombieriArchPolar
          (1 / 2) sigma (T n)) atTop (nhds 0) ∧
      Tendsto
        (fun n ↦ bombieriHorizontalLower f bombieriArchPolar
          (1 / 2) sigma (T n)) atTop (nhds 0) := by
  obtain ⟨C, _hC, hbound⟩ :=
    bombieriArchPolar_quartic_bound sigma hsigma T hT4
  have hTabs : Tendsto (fun n ↦ |T n|) atTop atTop := by
    simpa only [Function.comp_apply] using
      (tendsto_abs_atTop_atTop.comp hT)
  exact bombieriHorizontalPair_tendsto_zero_of_growth_four
    f bombieriArchPolar (1 / 2) sigma C T (by linarith) hTabs hbound

/-- The normalized truncated direct-plus-transpose right-line
archimedean/polar integral converges to the two polar Mellin values plus
Bombieri's archimedean term. -/
theorem bombieriOuterArchPolarIntervalIntegral_tendsto
    (f : BombieriTest) (sigma : ℝ) (T : ℕ → ℝ)
    (hsigma : 1 < sigma) (hT : Tendsto T atTop atTop)
    (hT4 : ∀ n, 4 ≤ T n) :
    Tendsto
      (fun n ↦ ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ v : ℝ in -T n..T n,
          (mellin (f : ℝ → ℂ) (sigma + v * I) +
            mellin (transposeLinearMap f : ℝ → ℂ) (sigma + v * I)) *
              bombieriArchPolar (sigma + v * I))
      atTop
      (nhds (mellin (f : ℝ → ℂ) 1 + mellin (f : ℝ → ℂ) 0 +
        bombieriArchTerm f)) := by
  let c : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  let P : ℂ := mellin (f : ℝ → ℂ) 1 + mellin (f : ℝ → ℂ) 0
  let Right : ℕ → ℂ := fun n ↦ c *
    ∫ v : ℝ in -T n..T n,
      (mellin (f : ℝ → ℂ) (sigma + v * I) +
        mellin (transposeLinearMap f : ℝ → ℂ) (sigma + v * I)) *
          bombieriArchPolar (sigma + v * I)
  let Critical : ℕ → ℂ := fun n ↦ c *
    ∫ v : ℝ in -T n..T n,
      (mellin (f : ℝ → ℂ) ((1 / 2 : ℝ) + v * I) +
        mellin (transposeLinearMap f : ℝ → ℂ)
          ((1 / 2 : ℝ) + v * I)) *
            bombieriArchPolar ((1 / 2 : ℝ) + v * I)
  let H : ℕ → ℂ := fun n ↦
    (bombieriHorizontalLower f bombieriArchPolar
        (1 / 2) sigma (T n) -
      bombieriHorizontalUpper f bombieriArchPolar
        (1 / 2) sigma (T n)) +
    (bombieriHorizontalLower (transposeLinearMap f) bombieriArchPolar
        (1 / 2) sigma (T n) -
      bombieriHorizontalUpper (transposeLinearMap f) bombieriArchPolar
        (1 / 2) sigma (T n))
  have hfinite (n : ℕ) : Right n =
      P + Critical n + (I * c) * H n := by
    simpa only [Right, P, Critical, H, c] using
      bombieriArchPolarRightPair_eq_poles_critical_horizontal
        f sigma (T n) hsigma (by linarith [hT4 n])
  have hkernel :=
    bombieriCriticalArchKernelInterval_tendsto f T hT
  have hcritical : Tendsto Critical atTop (nhds (bombieriArchTerm f)) := by
    apply Filter.Tendsto.congr'
      (f₁ := fun n ↦ ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ v : ℝ in -T n..T n,
          (((Complex.digamma ((1 / 4 : ℝ) + (v / 2) * I)).re -
            Real.log Real.pi : ℝ) : ℂ) *
              mellin (f : ℝ → ℂ) ((1 / 2 : ℝ) + v * I))
      (f₂ := Critical)
    · filter_upwards [] with n
      dsimp only [Critical, c]
      apply congrArg (fun z : ℂ ↦
        ((1 / (2 * Real.pi) : ℝ) : ℂ) * z)
      exact (bombieriCriticalArchPolarInterval_eq_gammaKernel
        f (T n)).symm
    · exact hkernel
  obtain ⟨hfUpper, hfLower⟩ :=
    bombieriArchPolarHorizontalPair_tendsto_zero
      f sigma T hsigma hT hT4
  obtain ⟨htUpper, htLower⟩ :=
    bombieriArchPolarHorizontalPair_tendsto_zero
      (transposeLinearMap f) sigma T hsigma hT hT4
  have hH : Tendsto H atTop (nhds 0) := by
    have hfDiff := hfLower.sub hfUpper
    have htDiff := htLower.sub htUpper
    simpa only [H, sub_self, add_zero] using hfDiff.add htDiff
  have hHscaled : Tendsto (fun n ↦ (I * c) * H n)
      atTop (nhds 0) := by
    simpa only [mul_zero] using hH.const_mul (I * c)
  have hrhs : Tendsto (fun n ↦ P + Critical n + (I * c) * H n)
      atTop (nhds (P + bombieriArchTerm f)) := by
    have hP : Tendsto (fun _ : ℕ ↦ P) atTop (nhds P) :=
      tendsto_const_nhds
    have hsum := (hP.add hcritical).add hHscaled
    simpa only [Pi.add_apply, add_zero] using hsum
  change Tendsto Right atTop (nhds (P + bombieriArchTerm f))
  exact Filter.Tendsto.congr'
    (Eventually.of_forall fun n ↦ (hfinite n).symm) hrhs

/-- The unconditional archimedean/polar right-line limit required by the
contour-limit assembly. Small initial heights are removed by replacing the
sequence with `max 4 T`, which is eventually identical to `T`. -/
theorem bombieriArchPolarRightLineLimit :
    BombieriArchPolarRightLineLimit := by
  intro f sigma hsigma T hT
  let U : ℕ → ℝ := fun n ↦ max 4 (T n)
  have hUT : U =ᶠ[atTop] T := by
    filter_upwards [(tendsto_atTop.1 hT 4)] with n hn
    exact max_eq_right hn
  have hU : Tendsto U atTop atTop :=
    Filter.Tendsto.congr' hUT.symm hT
  have hU4 : ∀ n, 4 ≤ U n := by
    intro n
    exact le_max_left _ _
  have hlimitU := bombieriOuterArchPolarIntervalIntegral_tendsto
    f sigma U hsigma hU hU4
  have hboundaryU : Tendsto
      (fun n ↦ bombieriRightArchPolarBoundary f sigma (U n))
      atTop
      (nhds (mellin (f : ℝ → ℂ) 1 + mellin (f : ℝ → ℂ) 0 +
        bombieriArchTerm f)) := by
    simpa only [bombieriRightArchPolarBoundary] using hlimitU
  apply Filter.Tendsto.congr' (h := hboundaryU)
  exact hUT.mono fun n hn ↦ by
    change bombieriRightArchPolarBoundary f sigma (U n) =
      bombieriRightArchPolarBoundary f sigma (T n)
    rw [hn]

end


end ArithmeticHodge.Analysis.MultiplicativeWeil

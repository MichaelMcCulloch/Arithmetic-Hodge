import ArithmeticHodge.Analysis.YoshidaEndpointPositiveDistanceFold
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaPinnedHalfLogEnergyStructural

open UnitIntervalLogEnergyAffine
open YoshidaEndpointPositiveDistanceFold

noncomputable section

/-!
# Logarithmic energy forced by a pinned half-interval

If a profile vanishes on a measurable part `Z` of the centered interval,
then both oriented cross rectangles between `Z` and its complement occur in
the raw logarithmic energy.  On `[-1,1]` the distance is at most two, so each
rectangle controls one half of the squared profile times the volume of `Z`.
The two orientations therefore give the full coefficient `volume.real Z`.

The product-integrability of the singular difference kernel is stated as an
explicit hypothesis.  No truncation of the diagonal and no finite sampling is
used.
-/

private theorem centeredRawLogEnergy_eq_setIntegral
    (w : ℝ → ℝ)
    (henergy : IntegrableOn
      (fun p : ℝ × ℝ ↦ centeredLogDifferenceKernel w p.1 p.2)
      (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)
      ((volume : Measure ℝ).prod volume)) :
    centeredRawLogEnergy w =
      ∫ p : ℝ × ℝ in Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1,
        centeredLogDifferenceKernel w p.1 p.2
          ∂((volume : Measure ℝ).prod volume) := by
  unfold centeredRawLogEnergy centeredLogDifferenceKernel
  calc
    (∫ x : ℝ in -1..1, ∫ y : ℝ in -1..1,
        (w x - w y) ^ 2 / |x - y|) =
        ∫ x : ℝ in Icc (-1) 1,
          ∫ y : ℝ in Icc (-1) 1,
            (w x - w y) ^ 2 / |x - y| := by
      rw [intervalIntegral.integral_of_le (by norm_num),
        ← integral_Icc_eq_integral_Ioc]
      apply setIntegral_congr_fun measurableSet_Icc
      intro x _hx
      change (∫ y : ℝ in -1..1,
          (w x - w y) ^ 2 / |x - y|) =
        ∫ y : ℝ in Icc (-1) 1,
          (w x - w y) ^ 2 / |x - y|
      rw [intervalIntegral.integral_of_le (by norm_num),
        ← integral_Icc_eq_integral_Ioc]
    _ = ∫ p : ℝ × ℝ in Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1,
          (w p.1 - w p.2) ^ 2 / |p.1 - p.2| := by
      exact (setIntegral_prod _ henergy).symm

private theorem centeredLogDifferenceKernel_swap
    (w : ℝ → ℝ) (p : ℝ × ℝ) :
    centeredLogDifferenceKernel w p.swap.1 p.swap.2 =
      centeredLogDifferenceKernel w p.1 p.2 := by
  rcases p with ⟨x, y⟩
  unfold centeredLogDifferenceKernel
  simp only [Prod.swap_prod_mk]
  rw [abs_sub_comm]
  ring

/-- A zero set inside the centered interval contributes its full real volume
as an `L²` coercivity coefficient for the raw logarithmic energy.  The proof
uses only the two cross rectangles with the zero set and the diameter-two
bound on `[-1,1]`. -/
theorem volume_mul_integral_sq_le_centeredRawLogEnergy_of_zero_on
    (w : ℝ → ℝ) (Z : Set ℝ)
    (hZmeas : MeasurableSet Z)
    (hZsub : Z ⊆ Icc (-1 : ℝ) 1)
    (hzero : ∀ x ∈ Z, w x = 0)
    (hmass : IntegrableOn (fun x : ℝ ↦ w x ^ 2) (Icc (-1 : ℝ) 1))
    (henergy : IntegrableOn
      (fun p : ℝ × ℝ ↦ centeredLogDifferenceKernel w p.1 p.2)
      (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)
      ((volume : Measure ℝ).prod volume)) :
    volume.real Z * (∫ x : ℝ in -1..1, w x ^ 2) ≤
      centeredRawLogEnergy w := by
  let S : Set ℝ := Icc (-1 : ℝ) 1
  let B : Set ℝ := S \ Z
  let K : ℝ × ℝ → ℝ := fun p ↦
    centeredLogDifferenceKernel w p.1 p.2
  let L : ℝ × ℝ → ℝ := fun p ↦ (1 / 2 : ℝ) * w p.1 ^ 2
  let C : Set (ℝ × ℝ) := B ×ˢ Z
  let Cswap : Set (ℝ × ℝ) := Z ×ˢ B
  have hSmeas : MeasurableSet S := measurableSet_Icc
  have hBmeas : MeasurableSet B := hSmeas.diff hZmeas
  have hCmeas : MeasurableSet C := hBmeas.prod hZmeas
  have hCswapMeas : MeasurableSet Cswap := hZmeas.prod hBmeas
  have hZfinite : volume Z ≠ ⊤ := by
    exact ((measure_mono hZsub).trans_lt
      (measure_Icc_lt_top (a := (-1 : ℝ)) (b := 1))).ne
  have hZmass : (∫ x : ℝ in Z, w x ^ 2) = 0 := by
    calc
      (∫ x : ℝ in Z, w x ^ 2) = ∫ _x : ℝ in Z, (0 : ℝ) := by
        apply setIntegral_congr_fun hZmeas
        intro x hx
        change w x ^ 2 = 0
        rw [hzero x hx]
        norm_num
      _ = 0 := by simp
  have hBmass : (∫ x : ℝ in B, w x ^ 2) =
      ∫ x : ℝ in S, w x ^ 2 := by
    dsimp only [B]
    rw [setIntegral_diff hZmeas hmass hZsub, hZmass, sub_zero]
  have hmassB : IntegrableOn (fun x : ℝ ↦ w x ^ 2) B := by
    exact hmass.mono_set diff_subset
  have honeZ : IntegrableOn (fun _x : ℝ ↦ (1 : ℝ)) Z :=
    integrableOn_const hZfinite
  have hLcross : IntegrableOn L C
      ((volume : Measure ℝ).prod volume) := by
    rw [IntegrableOn, ← Measure.prod_restrict]
    simpa only [L, mul_one] using
      (hmassB.const_mul (1 / 2 : ℝ)).mul_prod honeZ
  have hCsub : C ⊆ S ×ˢ S := by
    intro p hp
    exact ⟨hp.1.1, hZsub hp.2⟩
  have hCswapSub : Cswap ⊆ S ×ˢ S := by
    intro p hp
    exact ⟨hZsub hp.1, hp.2.1⟩
  have hKcross : IntegrableOn K C
      ((volume : Measure ℝ).prod volume) := by
    exact henergy.mono_set hCsub
  have hKcrossSwap : IntegrableOn K Cswap
      ((volume : Measure ℝ).prod volume) := by
    exact henergy.mono_set hCswapSub
  have hpoint : ∀ p ∈ C, L p ≤ K p := by
    intro p hp
    have hxS : p.1 ∈ S := hp.1.1
    have hyZ : p.2 ∈ Z := hp.2
    have hyS : p.2 ∈ S := hZsub hyZ
    have hwy : w p.2 = 0 := hzero p.2 hyZ
    have hdist : |p.1 - p.2| ≤ 2 := by
      rw [abs_le]
      constructor <;> linarith [hxS.1, hxS.2, hyS.1, hyS.2]
    dsimp only [L, K]
    unfold centeredLogDifferenceKernel
    rw [hwy, sub_zero]
    by_cases hxy : |p.1 - p.2| = 0
    · have heq : p.1 = p.2 := sub_eq_zero.mp (abs_eq_zero.mp hxy)
      rw [heq, hwy]
      norm_num
    · have hxypos : 0 < |p.1 - p.2| :=
        lt_of_le_of_ne (abs_nonneg _) (Ne.symm hxy)
      rw [le_div_iff₀ hxypos]
      nlinarith [sq_nonneg (w p.1)]
  have hcrossLower :
      (1 / 2 : ℝ) * volume.real Z * (∫ x : ℝ in S, w x ^ 2) ≤
        ∫ p : ℝ × ℝ in C, K p
          ∂((volume : Measure ℝ).prod volume) := by
    have hmono :
        (∫ p : ℝ × ℝ in C, L p
          ∂((volume : Measure ℝ).prod volume)) ≤
        ∫ p : ℝ × ℝ in C, K p
          ∂((volume : Measure ℝ).prod volume) :=
      setIntegral_mono_on hLcross hKcross hCmeas hpoint
    have hLvalue :
        (∫ p : ℝ × ℝ in C, L p
          ∂((volume : Measure ℝ).prod volume)) =
        (1 / 2 : ℝ) * volume.real Z *
          (∫ x : ℝ in S, w x ^ 2) := by
      dsimp only [C, L]
      rw [show (fun p : ℝ × ℝ ↦ (1 / 2 : ℝ) * w p.1 ^ 2) =
          fun p ↦ ((1 / 2 : ℝ) * w p.1 ^ 2) * (1 : ℝ) by
        funext p
        ring]
      rw [setIntegral_prod_mul
        (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
        (fun x : ℝ ↦ (1 / 2 : ℝ) * w x ^ 2)
        (fun _x : ℝ ↦ (1 : ℝ)) B Z,
        integral_const_mul, hBmass, setIntegral_const]
      simp only [smul_eq_mul]
      ring
    rwa [hLvalue] at hmono
  have hcrossSwapEq :
      (∫ p : ℝ × ℝ in Cswap, K p
        ∂((volume : Measure ℝ).prod volume)) =
      ∫ p : ℝ × ℝ in C, K p
        ∂((volume : Measure ℝ).prod volume) := by
    have hswap := MeasureTheory.setIntegral_prod_swap
      (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)) B Z K
    calc
      (∫ p : ℝ × ℝ in Cswap, K p
          ∂((volume : Measure ℝ).prod volume)) =
          ∫ p : ℝ × ℝ in Z ×ˢ B, K p.swap
            ∂((volume : Measure ℝ).prod volume) := by
        dsimp only [Cswap]
        apply setIntegral_congr_fun (hZmeas.prod hBmeas)
        intro p _hp
        exact (centeredLogDifferenceKernel_swap w p).symm
      _ = ∫ p : ℝ × ℝ in B ×ˢ Z, K p
          ∂((volume : Measure ℝ).prod volume) := hswap
      _ = ∫ p : ℝ × ℝ in C, K p
          ∂((volume : Measure ℝ).prod volume) := by rfl
  have hCdisjoint : Disjoint C Cswap := by
    rw [Set.disjoint_left]
    intro p hpC hpSwap
    exact hpC.1.2 hpSwap.1
  have hunionSub : C ∪ Cswap ⊆ S ×ˢ S := by
    intro p hp
    rcases hp with hp | hp
    · exact hCsub hp
    · exact hCswapSub hp
  have hKnonneg : ∀ p : ℝ × ℝ, 0 ≤ K p := by
    intro p
    dsimp only [K]
    unfold centeredLogDifferenceKernel
    exact div_nonneg (sq_nonneg _) (abs_nonneg _)
  have hunionLe :
      (∫ p : ℝ × ℝ in C ∪ Cswap, K p
        ∂((volume : Measure ℝ).prod volume)) ≤
      ∫ p : ℝ × ℝ in S ×ˢ S, K p
        ∂((volume : Measure ℝ).prod volume) := by
    exact setIntegral_mono_set henergy
      (Filter.Eventually.of_forall hKnonneg)
      (Filter.Eventually.of_forall hunionSub)
  have hunionEq :
      (∫ p : ℝ × ℝ in C ∪ Cswap, K p
        ∂((volume : Measure ℝ).prod volume)) =
      2 * ∫ p : ℝ × ℝ in C, K p
        ∂((volume : Measure ℝ).prod volume) := by
    rw [setIntegral_union hCdisjoint hCswapMeas hKcross hKcrossSwap,
      hcrossSwapEq]
    ring
  have htwoCross : volume.real Z * (∫ x : ℝ in S, w x ^ 2) ≤
      ∫ p : ℝ × ℝ in C ∪ Cswap, K p
        ∂((volume : Measure ℝ).prod volume) := by
    rw [hunionEq]
    linarith
  rw [centeredRawLogEnergy_eq_setIntegral w henergy]
  rw [intervalIntegral.integral_of_le (by norm_num),
    ← integral_Icc_eq_integral_Ioc]
  dsimp only [S, K] at htwoCross hunionLe ⊢
  exact htwoCross.trans hunionLe

/-- Vanishing on the left one-sided interval of length `1/2` forces a
half-unit raw logarithmic-energy reserve. -/
theorem half_mul_integral_sq_le_centeredRawLogEnergy_of_zero_on_leftHalf
    (w : ℝ → ℝ)
    (hzero : ∀ x ∈ Icc (-1 : ℝ) (-1 / 2), w x = 0)
    (hmass : IntegrableOn (fun x : ℝ ↦ w x ^ 2) (Icc (-1 : ℝ) 1))
    (henergy : IntegrableOn
      (fun p : ℝ × ℝ ↦ centeredLogDifferenceKernel w p.1 p.2)
      (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)
      ((volume : Measure ℝ).prod volume)) :
    (1 / 2 : ℝ) * (∫ x : ℝ in -1..1, w x ^ 2) ≤
      centeredRawLogEnergy w := by
  have h := volume_mul_integral_sq_le_centeredRawLogEnergy_of_zero_on
    w (Icc (-1 : ℝ) (-1 / 2)) measurableSet_Icc (by
      intro x hx
      exact ⟨hx.1, by linarith [hx.2]⟩) hzero hmass henergy
  convert h using 1
  norm_num [Real.volume_real_Icc_of_le]

/-- The reflected right one-sided interval has the same half-unit reserve. -/
theorem half_mul_integral_sq_le_centeredRawLogEnergy_of_zero_on_rightHalf
    (w : ℝ → ℝ)
    (hzero : ∀ x ∈ Icc (1 / 2 : ℝ) 1, w x = 0)
    (hmass : IntegrableOn (fun x : ℝ ↦ w x ^ 2) (Icc (-1 : ℝ) 1))
    (henergy : IntegrableOn
      (fun p : ℝ × ℝ ↦ centeredLogDifferenceKernel w p.1 p.2)
      (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)
      ((volume : Measure ℝ).prod volume)) :
    (1 / 2 : ℝ) * (∫ x : ℝ in -1..1, w x ^ 2) ≤
      centeredRawLogEnergy w := by
  have h := volume_mul_integral_sq_le_centeredRawLogEnergy_of_zero_on
    w (Icc (1 / 2 : ℝ) 1) measurableSet_Icc (by
      intro x hx
      exact ⟨by linarith [hx.1], hx.2⟩) hzero hmass henergy
  convert h using 1
  norm_num [Real.volume_real_Icc_of_le]

end

end ArithmeticHodge.Analysis.YoshidaPinnedHalfLogEnergyStructural

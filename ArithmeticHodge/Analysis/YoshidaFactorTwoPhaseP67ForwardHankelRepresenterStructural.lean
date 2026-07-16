import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP67ResidualRegularDecompositionStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCoupledRankSquares

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP67ForwardHankelRepresenterStructural

open YoshidaEndpointTriangleInterchange
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoPhaseCoupledRankSquares
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
open YoshidaFactorTwoPhaseP67ResidualAnalyticSchurStructural
open YoshidaFactorTwoPhaseP67ResidualRegularDecompositionStructural

noncomputable section

/-!
# Forward-Hankel representers at the `P₆/P₇` border

The positive-lag triangle is disintegrated in both coordinate orders.  This
produces right and left half-representers without introducing a discontinuous
sign at the diagonal.  Their sum is the symmetric Stieltjes representer `K`;
their difference is the alternating representer `L`.
-/

/-! ## The two triangle Fubini orientations -/

/-- Integrate the centered upper triangle by fixing its first coordinate. -/
theorem setIntegral_centeredUpperTriangle_eq_iterated_left
    (F : ℝ × ℝ → ℝ) (hF : Continuous F) :
    (∫ p : ℝ × ℝ in centeredUpperTriangle, F p) =
      ∫ y : ℝ in -1..1, ∫ x : ℝ in -1..y, F (y, x) := by
  let U : Set (ℝ × ℝ) := centeredUpperTriangle
  have hUmeas : MeasurableSet U := by
    dsimp only [U]
    unfold centeredUpperTriangle
    measurability
  have hUsub : U ⊆ Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 := by
    intro p hp
    dsimp only [U] at hp
    unfold centeredUpperTriangle at hp
    exact ⟨⟨by linarith [hp.1, hp.2.1], hp.2.2⟩,
      ⟨hp.1, by linarith [hp.2.1, hp.2.2]⟩⟩
  have hFUpper : IntegrableOn F U :=
    (hF.continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)).mono_set hUsub
  have hFIndicator : Integrable (U.indicator F) :=
    hFUpper.integrable_indicator hUmeas
  calc
    (∫ p : ℝ × ℝ in centeredUpperTriangle, F p) =
        ∫ y : ℝ, ∫ x : ℝ, U.indicator F (y, x) := by
      change (∫ p : ℝ × ℝ in U, F p) = _
      rw [← integral_indicator hUmeas, Measure.volume_eq_prod ℝ ℝ,
        integral_prod _ hFIndicator]
    _ = ∫ y : ℝ in Icc (-1) 1,
        ∫ x : ℝ in Icc (-1) y, F (y, x) := by
      rw [← integral_indicator measurableSet_Icc]
      apply integral_congr_ae
      filter_upwards [] with y
      by_cases hy : y ∈ Icc (-1 : ℝ) 1
      · rw [Set.indicator_of_mem hy, ← integral_indicator measurableSet_Icc]
        apply integral_congr_ae
        filter_upwards [] with x
        have hmem : (y, x) ∈ U ↔ x ∈ Icc (-1 : ℝ) y := by
          dsimp only [U]
          unfold centeredUpperTriangle
          constructor
          · intro h
            exact ⟨h.1, h.2.1⟩
          · intro h
            exact ⟨h.1, h.2, hy.2⟩
        by_cases hx : x ∈ Icc (-1 : ℝ) y
        · rw [Set.indicator_of_mem hx,
            Set.indicator_of_mem (hmem.mpr hx)]
        · rw [Set.indicator_of_notMem hx,
            Set.indicator_of_notMem (mt hmem.mp hx)]
      · rw [Set.indicator_of_notMem hy]
        have hrow : (fun x : ℝ ↦ U.indicator F (y, x)) = 0 := by
          funext x
          have hnot : (y, x) ∉ U := by
            intro hp
            apply hy
            dsimp only [U] at hp
            unfold centeredUpperTriangle at hp
            exact ⟨by linarith [hp.1, hp.2.1], hp.2.2⟩
          rw [Set.indicator_of_notMem hnot]
          rfl
        rw [hrow]
        simp
    _ = ∫ y : ℝ in -1..1, ∫ x : ℝ in -1..y, F (y, x) := by
      symm
      rw [intervalIntegral.integral_of_le (by norm_num),
        ← integral_Icc_eq_integral_Ioc]
      apply setIntegral_congr_fun measurableSet_Icc
      intro y hy
      change (∫ x : ℝ in -1..y, F (y, x)) =
        ∫ x : ℝ in Icc (-1) y, F (y, x)
      rw [intervalIntegral.integral_of_le hy.1,
        ← integral_Icc_eq_integral_Ioc]

/-- Integrate the centered upper triangle by fixing its second coordinate. -/
theorem setIntegral_centeredUpperTriangle_eq_iterated_right
    (F : ℝ × ℝ → ℝ) (hF : Continuous F) :
    (∫ p : ℝ × ℝ in centeredUpperTriangle, F p) =
      ∫ x : ℝ in -1..1, ∫ y : ℝ in x..1, F (y, x) := by
  let U : Set (ℝ × ℝ) := centeredUpperTriangle
  let H : ℝ × ℝ → ℝ := fun p ↦ U.indicator F p.swap
  have hUmeas : MeasurableSet U := by
    dsimp only [U]
    unfold centeredUpperTriangle
    measurability
  have hUsub : U ⊆ Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 := by
    intro p hp
    dsimp only [U] at hp
    unfold centeredUpperTriangle at hp
    exact ⟨⟨by linarith [hp.1, hp.2.1], hp.2.2⟩,
      ⟨hp.1, by linarith [hp.2.1, hp.2.2]⟩⟩
  have hFUpper : IntegrableOn F U :=
    (hF.continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)).mono_set hUsub
  have hFIndicator : Integrable (U.indicator F) :=
    hFUpper.integrable_indicator hUmeas
  have hH : Integrable H := by
    simpa only [H] using hFIndicator.swap
  have hswap : (∫ p : ℝ × ℝ, H p) =
      ∫ p : ℝ × ℝ, U.indicator F p := by
    dsimp only [H]
    rw [Measure.volume_eq_prod ℝ ℝ]
    exact integral_prod_swap (U.indicator F)
  calc
    (∫ p : ℝ × ℝ in centeredUpperTriangle, F p) =
        ∫ p : ℝ × ℝ, U.indicator F p := by
      change (∫ p : ℝ × ℝ in U, F p) = _
      rw [← integral_indicator hUmeas]
    _ = ∫ x : ℝ, ∫ y : ℝ, H (x, y) := by
      rw [← hswap, Measure.volume_eq_prod ℝ ℝ,
        integral_prod _ hH]
    _ = ∫ x : ℝ in Icc (-1) 1,
        ∫ y : ℝ in Icc x 1, F (y, x) := by
      rw [← integral_indicator measurableSet_Icc]
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases hx : x ∈ Icc (-1 : ℝ) 1
      · rw [Set.indicator_of_mem hx, ← integral_indicator measurableSet_Icc]
        apply integral_congr_ae
        filter_upwards [] with y
        have hmem : (y, x) ∈ U ↔ y ∈ Icc x 1 := by
          dsimp only [U]
          unfold centeredUpperTriangle
          constructor
          · intro h
            exact ⟨h.2.1, h.2.2⟩
          · intro h
            exact ⟨hx.1, h.1, h.2⟩
        by_cases hy : y ∈ Icc x 1
        · rw [Set.indicator_of_mem hy,
            show H (x, y) = F (y, x) by
              dsimp only [H, Prod.swap_prod_mk]
              rw [Set.indicator_of_mem (hmem.mpr hy)]]
        · rw [Set.indicator_of_notMem hy,
            show H (x, y) = 0 by
              dsimp only [H, Prod.swap_prod_mk]
              rw [Set.indicator_of_notMem (mt hmem.mp hy)]]
      · rw [Set.indicator_of_notMem hx]
        have hrow : (fun y : ℝ ↦ H (x, y)) = 0 := by
          funext y
          have hnot : (y, x) ∉ U := by
            intro hp
            apply hx
            dsimp only [U] at hp
            unfold centeredUpperTriangle at hp
            exact ⟨hp.1, by linarith [hp.2.1, hp.2.2]⟩
          dsimp only [H, Prod.swap_prod_mk]
          rw [Set.indicator_of_notMem hnot]
          rfl
        rw [hrow]
        simp
    _ = ∫ x : ℝ in -1..1, ∫ y : ℝ in x..1, F (y, x) := by
      symm
      rw [intervalIntegral.integral_of_le (by norm_num),
        ← integral_Icc_eq_integral_Ioc]
      apply setIntegral_congr_fun measurableSet_Icc
      intro x hx
      change (∫ y : ℝ in x..1, F (y, x)) =
        ∫ y : ℝ in Icc x 1, F (y, x)
      rw [intervalIntegral.integral_of_le hx.2,
        ← integral_Icc_eq_integral_Ioc]

/-! ## Split forward-Hankel representers -/

/-- A globally continuous extension of the forward denominator. -/
def factorTwoForwardHankelLagWeight (t : ℝ) : ℝ :=
  1 / (2 + |t|)

theorem continuous_factorTwoForwardHankelLagWeight :
    Continuous factorTwoForwardHankelLagWeight := by
  unfold factorTwoForwardHankelLagWeight
  exact continuous_const.div (continuous_const.add continuous_abs) fun t ↦ by
    positivity

theorem factorTwoForwardHankelLagWeight_of_nonneg
    {t : ℝ} (ht : 0 ≤ t) :
    factorTwoForwardHankelLagWeight t = 1 / (2 + t) := by
  unfold factorTwoForwardHankelLagWeight
  rw [abs_of_nonneg ht]

/-- Contribution from low variables to the right of the residual variable. -/
def factorTwoForwardHankelRightRepresenter
    (p : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y : ℝ in x..1,
    factorTwoForwardHankelLagWeight (y - x) * p y

/-- Contribution from low variables to the left of the residual variable. -/
def factorTwoForwardHankelLeftRepresenter
    (p : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y : ℝ in -1..x,
    factorTwoForwardHankelLagWeight (x - y) * p y

/-- Symmetric forward-Hankel representer. -/
def factorTwoForwardHankelK (p : ℝ → ℝ) (x : ℝ) : ℝ :=
  factorTwoForwardHankelRightRepresenter p x +
    factorTwoForwardHankelLeftRepresenter p x

/-- Alternating forward-Hankel representer, with right-minus-left sign. -/
def factorTwoForwardHankelL (p : ℝ → ℝ) (x : ℝ) : ℝ :=
  factorTwoForwardHankelRightRepresenter p x -
    factorTwoForwardHankelLeftRepresenter p x

theorem factorTwoForwardHankelRightRepresenter_eq
    (p : ℝ → ℝ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    factorTwoForwardHankelRightRepresenter p x =
      ∫ y : ℝ in x..1, p y / (2 + y - x) := by
  unfold factorTwoForwardHankelRightRepresenter
  apply intervalIntegral.integral_congr
  intro y hy
  have hy' : y ∈ Icc x 1 := by
    simpa only [uIcc_of_le hx.2] using hy
  change factorTwoForwardHankelLagWeight (y - x) * p y =
    p y / (2 + y - x)
  rw [factorTwoForwardHankelLagWeight_of_nonneg (sub_nonneg.mpr hy'.1)]
  ring

theorem factorTwoForwardHankelLeftRepresenter_eq
    (p : ℝ → ℝ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    factorTwoForwardHankelLeftRepresenter p x =
      ∫ y : ℝ in -1..x, p y / (2 + x - y) := by
  unfold factorTwoForwardHankelLeftRepresenter
  apply intervalIntegral.integral_congr
  intro y hy
  have hy' : y ∈ Icc (-1 : ℝ) x := by
    simpa only [uIcc_of_le hx.1] using hy
  change factorTwoForwardHankelLagWeight (x - y) * p y =
    p y / (2 + x - y)
  rw [factorTwoForwardHankelLagWeight_of_nonneg (sub_nonneg.mpr hy'.2)]
  ring

theorem continuous_factorTwoForwardHankelRightRepresenter
    (p : ℝ → ℝ) (hp : Continuous p) :
    Continuous (factorTwoForwardHankelRightRepresenter p) := by
  let phi : ℝ → ℝ → ℝ := fun x s ↦
    factorTwoForwardHankelLagWeight ((1 - x) * s) *
      p ((1 - x) * s + x)
  let J : ℝ → ℝ := fun x ↦ ∫ s : ℝ in 0..1, phi x s
  have hphi : Continuous phi.uncurry := by
    dsimp only [phi, Function.uncurry]
    exact (continuous_factorTwoForwardHankelLagWeight.comp (by fun_prop)).mul
      (hp.comp (by fun_prop))
  have hJ : Continuous J := by
    have hset : Continuous (fun x : ℝ ↦
        ∫ s : ℝ in Icc (0 : ℝ) 1, phi x s) :=
      continuous_parametric_integral_of_continuous
        (μ := volume) hphi isCompact_Icc
    have heq : J = fun x : ℝ ↦
        ∫ s : ℝ in Icc (0 : ℝ) 1, phi x s := by
      funext x
      dsimp only [J]
      rw [intervalIntegral.integral_of_le (by norm_num),
        ← integral_Icc_eq_integral_Ioc]
    rw [heq]
    exact hset
  have htransport (x : ℝ) :
      factorTwoForwardHankelRightRepresenter p x = (1 - x) * J x := by
    let f : ℝ → ℝ := fun y ↦
      factorTwoForwardHankelLagWeight (y - x) * p y
    have hsubst := intervalIntegral.smul_integral_comp_mul_add
      (a := (0 : ℝ)) (b := 1) f (1 - x) x
    unfold factorTwoForwardHankelRightRepresenter
    change (∫ y : ℝ in x..1, f y) = (1 - x) * J x
    symm
    calc
      (1 - x) * J x =
          (1 - x) * ∫ s : ℝ in 0..1, f ((1 - x) * s + x) := by
        congr 1
        apply intervalIntegral.integral_congr
        intro s _hs
        dsimp only [J, phi, f]
        congr 2
        ring
      _ = ∫ y : ℝ in (1 - x) * 0 + x..(1 - x) * 1 + x, f y := by
        simpa only [smul_eq_mul] using hsubst
      _ = ∫ y : ℝ in x..1, f y := by
        congr 1 <;> ring
  rw [show factorTwoForwardHankelRightRepresenter p =
      fun x ↦ (1 - x) * J x by
    funext x
    exact htransport x]
  exact (continuous_const.sub continuous_id).mul hJ

theorem continuous_factorTwoForwardHankelLeftRepresenter
    (p : ℝ → ℝ) (hp : Continuous p) :
    Continuous (factorTwoForwardHankelLeftRepresenter p) := by
  let phi : ℝ → ℝ → ℝ := fun x s ↦
    factorTwoForwardHankelLagWeight ((x + 1) * (1 - s)) *
      p ((x + 1) * s - 1)
  let J : ℝ → ℝ := fun x ↦ ∫ s : ℝ in 0..1, phi x s
  have hphi : Continuous phi.uncurry := by
    dsimp only [phi, Function.uncurry]
    exact (continuous_factorTwoForwardHankelLagWeight.comp (by fun_prop)).mul
      (hp.comp (by fun_prop))
  have hJ : Continuous J := by
    have hset : Continuous (fun x : ℝ ↦
        ∫ s : ℝ in Icc (0 : ℝ) 1, phi x s) :=
      continuous_parametric_integral_of_continuous
        (μ := volume) hphi isCompact_Icc
    have heq : J = fun x : ℝ ↦
        ∫ s : ℝ in Icc (0 : ℝ) 1, phi x s := by
      funext x
      dsimp only [J]
      rw [intervalIntegral.integral_of_le (by norm_num),
        ← integral_Icc_eq_integral_Ioc]
    rw [heq]
    exact hset
  have htransport (x : ℝ) :
      factorTwoForwardHankelLeftRepresenter p x = (x + 1) * J x := by
    let f : ℝ → ℝ := fun y ↦
      factorTwoForwardHankelLagWeight (x - y) * p y
    have hsubst := intervalIntegral.smul_integral_comp_mul_add
      (a := (0 : ℝ)) (b := 1) f (x + 1) (-1)
    unfold factorTwoForwardHankelLeftRepresenter
    change (∫ y : ℝ in -1..x, f y) = (x + 1) * J x
    symm
    calc
      (x + 1) * J x =
          (x + 1) * ∫ s : ℝ in 0..1, f ((x + 1) * s + -1) := by
        congr 1
        apply intervalIntegral.integral_congr
        intro s _hs
        dsimp only [J, phi, f]
        congr 2
        ring
      _ = ∫ y : ℝ in (x + 1) * 0 + -1..(x + 1) * 1 + -1, f y := by
        simpa only [smul_eq_mul] using hsubst
      _ = ∫ y : ℝ in -1..x, f y := by
        congr 1 <;> ring
  rw [show factorTwoForwardHankelLeftRepresenter p =
      fun x ↦ (x + 1) * J x by
    funext x
    exact htransport x]
  exact (continuous_id.add continuous_const).mul hJ

theorem continuous_factorTwoForwardHankelK
    (p : ℝ → ℝ) (hp : Continuous p) :
    Continuous (factorTwoForwardHankelK p) :=
  (continuous_factorTwoForwardHankelRightRepresenter p hp).add
    (continuous_factorTwoForwardHankelLeftRepresenter p hp)

theorem continuous_factorTwoForwardHankelL
    (p : ℝ → ℝ) (hp : Continuous p) :
    Continuous (factorTwoForwardHankelL p) :=
  (continuous_factorTwoForwardHankelRightRepresenter p hp).sub
    (continuous_factorTwoForwardHankelLeftRepresenter p hp)

theorem factorTwoForwardHankelRightRepresenter_add
    (p r : ℝ → ℝ) (hp : Continuous p) (hr : Continuous r) (x : ℝ) :
    factorTwoForwardHankelRightRepresenter (p + r) x =
      factorTwoForwardHankelRightRepresenter p x +
        factorTwoForwardHankelRightRepresenter r x := by
  have hpI : IntervalIntegrable (fun y : ℝ ↦
      factorTwoForwardHankelLagWeight (y - x) * p y) volume x 1 :=
    ((continuous_factorTwoForwardHankelLagWeight.comp
      (continuous_id.sub continuous_const)).mul hp).intervalIntegrable x 1
  have hrI : IntervalIntegrable (fun y : ℝ ↦
      factorTwoForwardHankelLagWeight (y - x) * r y) volume x 1 :=
    ((continuous_factorTwoForwardHankelLagWeight.comp
      (continuous_id.sub continuous_const)).mul hr).intervalIntegrable x 1
  unfold factorTwoForwardHankelRightRepresenter
  rw [show (fun y : ℝ ↦
      factorTwoForwardHankelLagWeight (y - x) * (p + r) y) = fun y ↦
        factorTwoForwardHankelLagWeight (y - x) * p y +
          factorTwoForwardHankelLagWeight (y - x) * r y by
    funext y
    simp only [Pi.add_apply]
    ring,
    intervalIntegral.integral_add hpI hrI]

theorem factorTwoForwardHankelLeftRepresenter_add
    (p r : ℝ → ℝ) (hp : Continuous p) (hr : Continuous r) (x : ℝ) :
    factorTwoForwardHankelLeftRepresenter (p + r) x =
      factorTwoForwardHankelLeftRepresenter p x +
        factorTwoForwardHankelLeftRepresenter r x := by
  have hpI : IntervalIntegrable (fun y : ℝ ↦
      factorTwoForwardHankelLagWeight (x - y) * p y) volume (-1) x :=
    ((continuous_factorTwoForwardHankelLagWeight.comp
      (continuous_const.sub continuous_id)).mul hp).intervalIntegrable (-1) x
  have hrI : IntervalIntegrable (fun y : ℝ ↦
      factorTwoForwardHankelLagWeight (x - y) * r y) volume (-1) x :=
    ((continuous_factorTwoForwardHankelLagWeight.comp
      (continuous_const.sub continuous_id)).mul hr).intervalIntegrable (-1) x
  unfold factorTwoForwardHankelLeftRepresenter
  rw [show (fun y : ℝ ↦
      factorTwoForwardHankelLagWeight (x - y) * (p + r) y) = fun y ↦
        factorTwoForwardHankelLagWeight (x - y) * p y +
          factorTwoForwardHankelLagWeight (x - y) * r y by
    funext y
    simp only [Pi.add_apply]
    ring,
    intervalIntegral.integral_add hpI hrI]

theorem factorTwoForwardHankelRightRepresenter_smul
    (c : ℝ) (p : ℝ → ℝ) (x : ℝ) :
    factorTwoForwardHankelRightRepresenter (c • p) x =
      c * factorTwoForwardHankelRightRepresenter p x := by
  unfold factorTwoForwardHankelRightRepresenter
  rw [show (fun y : ℝ ↦
      factorTwoForwardHankelLagWeight (y - x) * (c • p) y) = fun y ↦
        c * (factorTwoForwardHankelLagWeight (y - x) * p y) by
    funext y
    simp only [Pi.smul_apply, smul_eq_mul]
    ring,
    intervalIntegral.integral_const_mul]

theorem factorTwoForwardHankelLeftRepresenter_smul
    (c : ℝ) (p : ℝ → ℝ) (x : ℝ) :
    factorTwoForwardHankelLeftRepresenter (c • p) x =
      c * factorTwoForwardHankelLeftRepresenter p x := by
  unfold factorTwoForwardHankelLeftRepresenter
  rw [show (fun y : ℝ ↦
      factorTwoForwardHankelLagWeight (x - y) * (c • p) y) = fun y ↦
        c * (factorTwoForwardHankelLagWeight (x - y) * p y) by
    funext y
    simp only [Pi.smul_apply, smul_eq_mul]
    ring,
    intervalIntegral.integral_const_mul]

theorem factorTwoForwardHankelK_add
    (p r : ℝ → ℝ) (hp : Continuous p) (hr : Continuous r) (x : ℝ) :
    factorTwoForwardHankelK (p + r) x =
      factorTwoForwardHankelK p x + factorTwoForwardHankelK r x := by
  unfold factorTwoForwardHankelK
  rw [factorTwoForwardHankelRightRepresenter_add p r hp hr,
    factorTwoForwardHankelLeftRepresenter_add p r hp hr]
  ring

theorem factorTwoForwardHankelL_add
    (p r : ℝ → ℝ) (hp : Continuous p) (hr : Continuous r) (x : ℝ) :
    factorTwoForwardHankelL (p + r) x =
      factorTwoForwardHankelL p x + factorTwoForwardHankelL r x := by
  unfold factorTwoForwardHankelL
  rw [factorTwoForwardHankelRightRepresenter_add p r hp hr,
    factorTwoForwardHankelLeftRepresenter_add p r hp hr]
  ring

theorem factorTwoForwardHankelK_smul
    (c : ℝ) (p : ℝ → ℝ) (x : ℝ) :
    factorTwoForwardHankelK (c • p) x = c * factorTwoForwardHankelK p x := by
  unfold factorTwoForwardHankelK
  rw [factorTwoForwardHankelRightRepresenter_smul,
    factorTwoForwardHankelLeftRepresenter_smul]
  ring

theorem factorTwoForwardHankelL_smul
    (c : ℝ) (p : ℝ → ℝ) (x : ℝ) :
    factorTwoForwardHankelL (c • p) x = c * factorTwoForwardHankelL p x := by
  unfold factorTwoForwardHankelL
  rw [factorTwoForwardHankelRightRepresenter_smul,
    factorTwoForwardHankelLeftRepresenter_smul]
  ring

/-! ## Ordered, symmetric, and alternating identities -/

private theorem integral_crossCorrelation_div_two_add_eq_weighted
    (u v : ℝ → ℝ) :
    (∫ t : ℝ in 0..2,
      factorTwoCenteredCrossCorrelation u v t / (2 + t)) =
      ∫ t : ℝ in 0..2,
        factorTwoForwardHankelLagWeight t *
          factorTwoCenteredCrossCorrelation u v t := by
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 2 := by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using ht
  change factorTwoCenteredCrossCorrelation u v t / (2 + t) =
    factorTwoForwardHankelLagWeight t *
      factorTwoCenteredCrossCorrelation u v t
  rw [factorTwoForwardHankelLagWeight_of_nonneg ht'.1]
  ring

theorem integral_crossCorrelation_div_two_add_eq_right
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    (∫ t : ℝ in 0..2,
      factorTwoCenteredCrossCorrelation u v t / (2 + t)) =
      ∫ x : ℝ in -1..1,
        v x * factorTwoForwardHankelRightRepresenter u x := by
  let q : ℝ → ℝ := factorTwoForwardHankelLagWeight
  let F : ℝ × ℝ → ℝ := fun p ↦
    q (p.1 - p.2) * u p.1 * v p.2
  have hq : Continuous q := continuous_factorTwoForwardHankelLagWeight
  have hF : Continuous F := by
    dsimp only [F, q]
    exact ((continuous_factorTwoForwardHankelLagWeight.comp (by fun_prop)).mul
      (hu.comp (by fun_prop))).mul (hv.comp (by fun_prop))
  rw [integral_crossCorrelation_div_two_add_eq_weighted u v,
    integral_weight_mul_crossCorrelation_eq_upperTriangle u v hu hv q hq,
    setIntegral_centeredUpperTriangle_eq_iterated_right F hF]
  apply intervalIntegral.integral_congr
  intro x _hx
  unfold factorTwoForwardHankelRightRepresenter
  change (∫ y : ℝ in x..1, F (y, x)) =
    v x * ∫ y : ℝ in x..1,
      factorTwoForwardHankelLagWeight (y - x) * u y
  rw [show (fun y : ℝ ↦ F (y, x)) = fun y ↦
      (factorTwoForwardHankelLagWeight (y - x) * u y) * v x by
    funext y
    dsimp only [F, q],
    intervalIntegral.integral_mul_const]
  ring

theorem integral_crossCorrelation_div_two_add_eq_left
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    (∫ t : ℝ in 0..2,
      factorTwoCenteredCrossCorrelation u v t / (2 + t)) =
      ∫ x : ℝ in -1..1,
        u x * factorTwoForwardHankelLeftRepresenter v x := by
  let q : ℝ → ℝ := factorTwoForwardHankelLagWeight
  let F : ℝ × ℝ → ℝ := fun p ↦
    q (p.1 - p.2) * u p.1 * v p.2
  have hq : Continuous q := continuous_factorTwoForwardHankelLagWeight
  have hF : Continuous F := by
    dsimp only [F, q]
    exact ((continuous_factorTwoForwardHankelLagWeight.comp (by fun_prop)).mul
      (hu.comp (by fun_prop))).mul (hv.comp (by fun_prop))
  rw [integral_crossCorrelation_div_two_add_eq_weighted u v,
    integral_weight_mul_crossCorrelation_eq_upperTriangle u v hu hv q hq,
    setIntegral_centeredUpperTriangle_eq_iterated_left F hF]
  apply intervalIntegral.integral_congr
  intro x _hx
  unfold factorTwoForwardHankelLeftRepresenter
  change (∫ y : ℝ in -1..x, F (x, y)) =
    u x * ∫ y : ℝ in -1..x,
      factorTwoForwardHankelLagWeight (x - y) * v y
  rw [show (fun y : ℝ ↦ F (x, y)) = fun y ↦
      u x * (factorTwoForwardHankelLagWeight (x - y) * v y) by
    funext y
    dsimp only [F, q]
    ring,
    intervalIntegral.integral_const_mul]

private theorem intervalIntegrable_crossCorrelation_div_two_add
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    IntervalIntegrable (fun t : ℝ ↦
      factorTwoCenteredCrossCorrelation u v t / (2 + t)) volume 0 2 := by
  apply ((continuous_factorTwoForwardHankelLagWeight.mul
    (continuous_factorTwoCenteredCrossCorrelation u v hu hv)).intervalIntegrable
      0 2).congr
  intro t ht
  have ht' : t ∈ Ioc (0 : ℝ) 2 := by
    simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using ht
  change factorTwoForwardHankelLagWeight t *
      factorTwoCenteredCrossCorrelation u v t =
    factorTwoCenteredCrossCorrelation u v t / (2 + t)
  rw [factorTwoForwardHankelLagWeight_of_nonneg ht'.1.le]
  ring

theorem integral_correlationBilinear_div_two_add_eq_K
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    (∫ t : ℝ in 0..2,
      factorTwoCenteredCorrelationBilinear u v t / (2 + t)) =
      (1 / 2 : ℝ) * ∫ x : ℝ in -1..1,
        v x * factorTwoForwardHankelK u x := by
  have huvI := intervalIntegrable_crossCorrelation_div_two_add u v hu hv
  have hvuI := intervalIntegrable_crossCorrelation_div_two_add v u hv hu
  have hrightI : IntervalIntegrable (fun x : ℝ ↦
      v x * factorTwoForwardHankelRightRepresenter u x) volume (-1) 1 :=
    (hv.mul (continuous_factorTwoForwardHankelRightRepresenter u hu))
      |>.intervalIntegrable (-1) 1
  have hleftI : IntervalIntegrable (fun x : ℝ ↦
      v x * factorTwoForwardHankelLeftRepresenter u x) volume (-1) 1 :=
    (hv.mul (continuous_factorTwoForwardHankelLeftRepresenter u hu))
      |>.intervalIntegrable (-1) 1
  rw [show (fun t : ℝ ↦
      factorTwoCenteredCorrelationBilinear u v t / (2 + t)) = fun t ↦
        (1 / 2 : ℝ) *
          (factorTwoCenteredCrossCorrelation u v t / (2 + t) +
            factorTwoCenteredCrossCorrelation v u t / (2 + t)) by
    funext t
    unfold factorTwoCenteredCorrelationBilinear
    ring,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add huvI hvuI,
    integral_crossCorrelation_div_two_add_eq_right u v hu hv,
    integral_crossCorrelation_div_two_add_eq_left v u hv hu,
    ← intervalIntegral.integral_add hrightI hleftI]
  congr 1
  apply intervalIntegral.integral_congr
  intro x _hx
  unfold factorTwoForwardHankelK
  ring

private theorem intervalIntegrable_alternatingCrossDifference_div_two_add
    (e o : ℝ → ℝ) (he : Continuous e) (ho : Continuous o) :
    IntervalIntegrable (fun t : ℝ ↦
      factorTwoP67ResidualAlternatingCrossDifference e o t / (2 + t))
      volume 0 2 := by
  unfold factorTwoP67ResidualAlternatingCrossDifference
  apply ((intervalIntegrable_crossCorrelation_div_two_add o e ho he).sub
    (intervalIntegrable_crossCorrelation_div_two_add e o he ho)).congr
  intro t _ht
  ring

theorem integral_alternatingCrossDifference_div_two_add_eq_L
    (e o : ℝ → ℝ) (he : Continuous e) (ho : Continuous o) :
    (∫ t : ℝ in 0..2,
      factorTwoP67ResidualAlternatingCrossDifference e o t / (2 + t)) =
      ∫ x : ℝ in -1..1, e x * factorTwoForwardHankelL o x := by
  have hoeI := intervalIntegrable_crossCorrelation_div_two_add o e ho he
  have heoI := intervalIntegrable_crossCorrelation_div_two_add e o he ho
  have hrightI : IntervalIntegrable (fun x : ℝ ↦
      e x * factorTwoForwardHankelRightRepresenter o x) volume (-1) 1 :=
    (he.mul (continuous_factorTwoForwardHankelRightRepresenter o ho))
      |>.intervalIntegrable (-1) 1
  have hleftI : IntervalIntegrable (fun x : ℝ ↦
      e x * factorTwoForwardHankelLeftRepresenter o x) volume (-1) 1 :=
    (he.mul (continuous_factorTwoForwardHankelLeftRepresenter o ho))
      |>.intervalIntegrable (-1) 1
  rw [show (fun t : ℝ ↦
      factorTwoP67ResidualAlternatingCrossDifference e o t / (2 + t)) =
      fun t ↦ factorTwoCenteredCrossCorrelation o e t / (2 + t) -
        factorTwoCenteredCrossCorrelation e o t / (2 + t) by
    funext t
    unfold factorTwoP67ResidualAlternatingCrossDifference
    ring,
    intervalIntegral.integral_sub hoeI heoI,
    integral_crossCorrelation_div_two_add_eq_right o e ho he,
    integral_crossCorrelation_div_two_add_eq_left e o he ho,
    ← intervalIntegral.integral_sub hrightI hleftI]
  apply intervalIntegral.integral_congr
  intro x _hx
  unfold factorTwoForwardHankelL
  ring

theorem integral_alternatingCrossDifference_div_two_add_eq_neg_L
    (e o : ℝ → ℝ) (he : Continuous e) (ho : Continuous o) :
    (∫ t : ℝ in 0..2,
      factorTwoP67ResidualAlternatingCrossDifference e o t / (2 + t)) =
      -(∫ x : ℝ in -1..1, o x * factorTwoForwardHankelL e x) := by
  have hoeI := intervalIntegrable_crossCorrelation_div_two_add o e ho he
  have heoI := intervalIntegrable_crossCorrelation_div_two_add e o he ho
  have hrightI : IntervalIntegrable (fun x : ℝ ↦
      o x * factorTwoForwardHankelRightRepresenter e x) volume (-1) 1 :=
    (ho.mul (continuous_factorTwoForwardHankelRightRepresenter e he))
      |>.intervalIntegrable (-1) 1
  have hleftI : IntervalIntegrable (fun x : ℝ ↦
      o x * factorTwoForwardHankelLeftRepresenter e x) volume (-1) 1 :=
    (ho.mul (continuous_factorTwoForwardHankelLeftRepresenter e he))
      |>.intervalIntegrable (-1) 1
  rw [show (fun t : ℝ ↦
      factorTwoP67ResidualAlternatingCrossDifference e o t / (2 + t)) =
      fun t ↦ factorTwoCenteredCrossCorrelation o e t / (2 + t) -
        factorTwoCenteredCrossCorrelation e o t / (2 + t) by
    funext t
    unfold factorTwoP67ResidualAlternatingCrossDifference
    ring,
    intervalIntegral.integral_sub hoeI heoI,
    integral_crossCorrelation_div_two_add_eq_left o e ho he,
    integral_crossCorrelation_div_two_add_eq_right e o he ho,
    ← intervalIntegral.integral_sub hleftI hrightI]
  rw [← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro x _hx
  unfold factorTwoForwardHankelL
  ring

/-! ## The four `P₆/P₇` rows -/

/-- The current forward-Hankel half-cross is exactly four representer
pairings.  The two alternating rows have opposite signs because the residual
is the second argument in the `P₆` row and the first argument in the `P₇`
row. -/
theorem factorTwoP67ResidualForwardHankelMixed_eq_pairings
    (p₆ p₇ eR oR : ℝ → ℝ)
    (hp₆ : Continuous p₆) (hp₇ : Continuous p₇)
    (heR : Continuous eR) (hoR : Continuous oR)
    (a b : ℝ) :
    factorTwoP67ResidualForwardHankelMixed p₆ p₇ eR oR a b =
      -(a / 4) * (∫ x : ℝ in -1..1,
        eR x * factorTwoForwardHankelK p₆ x) -
      (a / 4) * (∫ x : ℝ in -1..1,
        oR x * factorTwoForwardHankelK p₇ x) +
      (b / 4) * (∫ x : ℝ in -1..1,
        oR x * factorTwoForwardHankelL p₆ x) -
      (b / 4) * (∫ x : ℝ in -1..1,
        eR x * factorTwoForwardHankelL p₇ x) := by
  let B₆ : ℝ → ℝ := factorTwoCenteredCorrelationBilinear p₆ eR
  let B₇ : ℝ → ℝ := factorTwoCenteredCorrelationBilinear p₇ oR
  let D₆ : ℝ → ℝ := factorTwoP67ResidualAlternatingCrossDifference p₆ oR
  let D₇ : ℝ → ℝ := factorTwoP67ResidualAlternatingCrossDifference eR p₇
  have hB₆I : IntervalIntegrable (fun t : ℝ ↦ B₆ t / (2 + t)) volume 0 2 := by
    dsimp only [B₆, factorTwoCenteredCorrelationBilinear]
    exact ((intervalIntegrable_crossCorrelation_div_two_add p₆ eR hp₆ heR).add
      (intervalIntegrable_crossCorrelation_div_two_add eR p₆ heR hp₆)).const_mul
        (1 / 2 : ℝ) |>.congr (by
          intro t _ht
          ring)
  have hB₇I : IntervalIntegrable (fun t : ℝ ↦ B₇ t / (2 + t)) volume 0 2 := by
    dsimp only [B₇, factorTwoCenteredCorrelationBilinear]
    exact ((intervalIntegrable_crossCorrelation_div_two_add p₇ oR hp₇ hoR).add
      (intervalIntegrable_crossCorrelation_div_two_add oR p₇ hoR hp₇)).const_mul
        (1 / 2 : ℝ) |>.congr (by
          intro t _ht
          ring)
  have hD₆I : IntervalIntegrable (fun t : ℝ ↦ D₆ t / (2 + t)) volume 0 2 := by
    dsimp only [D₆]
    exact intervalIntegrable_alternatingCrossDifference_div_two_add p₆ oR hp₆ hoR
  have hD₇I : IntervalIntegrable (fun t : ℝ ↦ D₇ t / (2 + t)) volume 0 2 := by
    dsimp only [D₇]
    exact intervalIntegrable_alternatingCrossDifference_div_two_add eR p₇ heR hp₇
  have hSym :
      (∫ t : ℝ in 0..2,
        factorTwoP67ResidualSymmetricCrossSum p₆ p₇ eR oR t / (2 + t)) =
        (∫ t : ℝ in 0..2, B₆ t / (2 + t)) +
          ∫ t : ℝ in 0..2, B₇ t / (2 + t) := by
    rw [show (fun t : ℝ ↦
        factorTwoP67ResidualSymmetricCrossSum p₆ p₇ eR oR t / (2 + t)) =
      fun t ↦ B₆ t / (2 + t) + B₇ t / (2 + t) by
        funext t
        dsimp only [B₆, B₇]
        unfold factorTwoP67ResidualSymmetricCrossSum
        ring,
      intervalIntegral.integral_add hB₆I hB₇I]
  have hAlt :
      (∫ t : ℝ in 0..2,
        factorTwoP67ResidualAlternatingCrossSum p₆ p₇ eR oR t / (2 + t)) =
        (∫ t : ℝ in 0..2, D₆ t / (2 + t)) +
          ∫ t : ℝ in 0..2, D₇ t / (2 + t) := by
    rw [show (fun t : ℝ ↦
        factorTwoP67ResidualAlternatingCrossSum p₆ p₇ eR oR t / (2 + t)) =
      fun t ↦ D₆ t / (2 + t) + D₇ t / (2 + t) by
        funext t
        dsimp only [D₆, D₇]
        unfold factorTwoP67ResidualAlternatingCrossSum
        ring,
      intervalIntegral.integral_add hD₆I hD₇I]
  have hB₆ := integral_correlationBilinear_div_two_add_eq_K p₆ eR hp₆ heR
  have hB₇ := integral_correlationBilinear_div_two_add_eq_K p₇ oR hp₇ hoR
  have hD₆ := integral_alternatingCrossDifference_div_two_add_eq_neg_L p₆ oR hp₆ hoR
  have hD₇ := integral_alternatingCrossDifference_div_two_add_eq_L eR p₇ heR hp₇
  unfold factorTwoP67ResidualForwardHankelMixed
  rw [hSym, hAlt]
  rw [hB₆, hB₇, hD₆, hD₇]
  ring

/-- Canonical scaled `P₆/P₇` form of the four-pairing identity. -/
theorem factorTwoP67ResidualForwardHankelMixed_scaled_P67_eq_pairings
    (eR oR : ℝ → ℝ) (heR : Continuous eR) (hoR : Continuous oR)
    (c d a b : ℝ) :
    factorTwoP67ResidualForwardHankelMixed
        (c • factorTwoCenteredP6) (d • factorTwoCenteredP7)
        eR oR a b =
      -(a * c / 4) * (∫ x : ℝ in -1..1,
        eR x * factorTwoForwardHankelK factorTwoCenteredP6 x) -
      (a * d / 4) * (∫ x : ℝ in -1..1,
        oR x * factorTwoForwardHankelK factorTwoCenteredP7 x) +
      (b * c / 4) * (∫ x : ℝ in -1..1,
        oR x * factorTwoForwardHankelL factorTwoCenteredP6 x) -
      (b * d / 4) * (∫ x : ℝ in -1..1,
        eR x * factorTwoForwardHankelL factorTwoCenteredP7 x) := by
  rw [factorTwoP67ResidualForwardHankelMixed_eq_pairings
    (c • factorTwoCenteredP6) (d • factorTwoCenteredP7) eR oR
    (continuous_factorTwoCenteredP6.const_smul c)
    (continuous_factorTwoCenteredP7.const_smul d) heR hoR]
  simp_rw [factorTwoForwardHankelK_smul,
    factorTwoForwardHankelL_smul]
  repeat rw [show (fun x : ℝ ↦ eR x *
      (c * factorTwoForwardHankelK factorTwoCenteredP6 x)) = fun x ↦
        c * (eR x * factorTwoForwardHankelK factorTwoCenteredP6 x) by
    funext x
    ring,
    intervalIntegral.integral_const_mul]
  repeat rw [show (fun x : ℝ ↦ oR x *
      (d * factorTwoForwardHankelK factorTwoCenteredP7 x)) = fun x ↦
        d * (oR x * factorTwoForwardHankelK factorTwoCenteredP7 x) by
    funext x
    ring,
    intervalIntegral.integral_const_mul]
  repeat rw [show (fun x : ℝ ↦ oR x *
      (c * factorTwoForwardHankelL factorTwoCenteredP6 x)) = fun x ↦
        c * (oR x * factorTwoForwardHankelL factorTwoCenteredP6 x) by
    funext x
    ring,
    intervalIntegral.integral_const_mul]
  repeat rw [show (fun x : ℝ ↦ eR x *
      (d * factorTwoForwardHankelL factorTwoCenteredP7 x)) = fun x ↦
        d * (eR x * factorTwoForwardHankelL factorTwoCenteredP7 x) by
    funext x
    ring,
    intervalIntegral.integral_const_mul]
  ring

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP67ForwardHankelRepresenterStructural

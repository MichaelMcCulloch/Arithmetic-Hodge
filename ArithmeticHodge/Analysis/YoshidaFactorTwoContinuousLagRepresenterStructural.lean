import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP67ForwardHankelRepresenterStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoContinuousLagRepresenterStructural

open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoPhaseCoupledRankSquares
open YoshidaFactorTwoPhaseP67ForwardHankelRepresenterStructural
open YoshidaEndpointTriangleInterchange

noncomputable section

/-!
# Representers for a continuous lag kernel

A continuous lag weight on the positive-distance triangle defines two
one-variable transforms, according to whether the represented variable is
the right or left endpoint of the ordered pair.  Their sum represents the
symmetric correlation polarization and their difference represents the
alternating ordered cross-difference.
-/

/-! ## Integrable triangle disintegration -/

/-- Integrate an arbitrary integrable density on the centered upper triangle
by fixing its first coordinate.  Unlike the older continuous-density API,
this form also applies to the reflected endpoint pole. -/
theorem setIntegral_centeredUpperTriangle_eq_iterated_left_of_integrable
    (F : ℝ × ℝ → ℝ)
    (hFUpper : IntegrableOn F centeredUpperTriangle
      ((volume : Measure ℝ).prod volume)) :
    (∫ p : ℝ × ℝ in centeredUpperTriangle, F p) =
      ∫ y : ℝ in -1..1, ∫ x : ℝ in -1..y, F (y, x) := by
  let U : Set (ℝ × ℝ) := centeredUpperTriangle
  have hUmeas : MeasurableSet U := by
    dsimp only [U]
    unfold centeredUpperTriangle
    measurability
  have hFIndicator : Integrable (U.indicator F) := by
    exact (show IntegrableOn F U by simpa only [U] using hFUpper).integrable_indicator hUmeas
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

/-- Integrate an arbitrary integrable density on the centered upper triangle
by fixing its second coordinate. -/
theorem setIntegral_centeredUpperTriangle_eq_iterated_right_of_integrable
    (F : ℝ × ℝ → ℝ)
    (hFUpper : IntegrableOn F centeredUpperTriangle
      ((volume : Measure ℝ).prod volume)) :
    (∫ p : ℝ × ℝ in centeredUpperTriangle, F p) =
      ∫ x : ℝ in -1..1, ∫ y : ℝ in x..1, F (y, x) := by
  let U : Set (ℝ × ℝ) := centeredUpperTriangle
  let H : ℝ × ℝ → ℝ := fun p ↦ U.indicator F p.swap
  have hUmeas : MeasurableSet U := by
    dsimp only [U]
    unfold centeredUpperTriangle
    measurability
  have hFIndicator : Integrable (U.indicator F) := by
    exact (show IntegrableOn F U by simpa only [U] using hFUpper).integrable_indicator hUmeas
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

/-- Contribution from low variables to the right of the represented
variable for an arbitrary continuous lag kernel. -/
def factorTwoContinuousLagRightRepresenter
    (q p : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y : ℝ in x..1, q (y - x) * p y

/-- Contribution from low variables to the left of the represented
variable for an arbitrary continuous lag kernel. -/
def factorTwoContinuousLagLeftRepresenter
    (q p : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y : ℝ in -1..x, q (x - y) * p y

/-- Symmetric continuous-lag representer. -/
def factorTwoContinuousLagK
    (q p : ℝ → ℝ) (x : ℝ) : ℝ :=
  factorTwoContinuousLagRightRepresenter q p x +
    factorTwoContinuousLagLeftRepresenter q p x

/-- Alternating continuous-lag representer, with right-minus-left sign. -/
def factorTwoContinuousLagJ
    (q p : ℝ → ℝ) (x : ℝ) : ℝ :=
  factorTwoContinuousLagRightRepresenter q p x -
    factorTwoContinuousLagLeftRepresenter q p x

theorem continuous_factorTwoContinuousLagRightRepresenter
    (q p : ℝ → ℝ) (hq : Continuous q) (hp : Continuous p) :
    Continuous (factorTwoContinuousLagRightRepresenter q p) := by
  let phi : ℝ → ℝ → ℝ := fun x s ↦
    q ((1 - x) * s) * p ((1 - x) * s + x)
  let J : ℝ → ℝ := fun x ↦ ∫ s : ℝ in 0..1, phi x s
  have hphi : Continuous phi.uncurry := by
    dsimp only [phi, Function.uncurry]
    exact (hq.comp (by fun_prop)).mul (hp.comp (by fun_prop))
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
      factorTwoContinuousLagRightRepresenter q p x =
        (1 - x) * J x := by
    let f : ℝ → ℝ := fun y ↦ q (y - x) * p y
    have hsubst := intervalIntegral.smul_integral_comp_mul_add
      (a := (0 : ℝ)) (b := 1) f (1 - x) x
    unfold factorTwoContinuousLagRightRepresenter
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
  rw [show factorTwoContinuousLagRightRepresenter q p =
      fun x ↦ (1 - x) * J x by
    funext x
    exact htransport x]
  exact (continuous_const.sub continuous_id).mul hJ

theorem continuous_factorTwoContinuousLagLeftRepresenter
    (q p : ℝ → ℝ) (hq : Continuous q) (hp : Continuous p) :
    Continuous (factorTwoContinuousLagLeftRepresenter q p) := by
  let phi : ℝ → ℝ → ℝ := fun x s ↦
    q ((x + 1) * (1 - s)) * p ((x + 1) * s - 1)
  let J : ℝ → ℝ := fun x ↦ ∫ s : ℝ in 0..1, phi x s
  have hphi : Continuous phi.uncurry := by
    dsimp only [phi, Function.uncurry]
    exact (hq.comp (by fun_prop)).mul (hp.comp (by fun_prop))
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
      factorTwoContinuousLagLeftRepresenter q p x =
        (x + 1) * J x := by
    let f : ℝ → ℝ := fun y ↦ q (x - y) * p y
    have hsubst := intervalIntegral.smul_integral_comp_mul_add
      (a := (0 : ℝ)) (b := 1) f (x + 1) (-1)
    unfold factorTwoContinuousLagLeftRepresenter
    change (∫ y : ℝ in -1..x, f y) = (x + 1) * J x
    symm
    calc
      (x + 1) * J x =
          (x + 1) * ∫ s : ℝ in 0..1, f ((x + 1) * s - 1) := by
        congr 1
        apply intervalIntegral.integral_congr
        intro s _hs
        dsimp only [J, phi, f]
        congr 2
        ring
      _ = ∫ y : ℝ in (x + 1) * 0 + -1..(x + 1) * 1 + -1, f y := by
        simpa only [smul_eq_mul, sub_eq_add_neg] using hsubst
      _ = ∫ y : ℝ in -1..x, f y := by
        congr 1 <;> ring
  rw [show factorTwoContinuousLagLeftRepresenter q p =
      fun x ↦ (x + 1) * J x by
    funext x
    exact htransport x]
  exact (continuous_id.add continuous_const).mul hJ

theorem continuous_factorTwoContinuousLagK
    (q p : ℝ → ℝ) (hq : Continuous q) (hp : Continuous p) :
    Continuous (factorTwoContinuousLagK q p) :=
  (continuous_factorTwoContinuousLagRightRepresenter q p hq hp).add
    (continuous_factorTwoContinuousLagLeftRepresenter q p hq hp)

theorem continuous_factorTwoContinuousLagJ
    (q p : ℝ → ℝ) (hq : Continuous q) (hp : Continuous p) :
    Continuous (factorTwoContinuousLagJ q p) :=
  (continuous_factorTwoContinuousLagRightRepresenter q p hq hp).sub
    (continuous_factorTwoContinuousLagLeftRepresenter q p hq hp)

/-- Ordered correlation represented in the second, right-triangle
coordinate. -/
theorem integral_continuousLag_mul_crossCorrelation_eq_right
    (q u v : ℝ → ℝ)
    (hq : Continuous q) (hu : Continuous u) (hv : Continuous v) :
    (∫ t : ℝ in 0..2,
        q t * factorTwoCenteredCrossCorrelation u v t) =
      ∫ x : ℝ in -1..1,
        v x * factorTwoContinuousLagRightRepresenter q u x := by
  let F : ℝ × ℝ → ℝ := fun z ↦
    q (z.1 - z.2) * u z.1 * v z.2
  have hF : Continuous F := by
    dsimp only [F]
    exact ((hq.comp (by fun_prop)).mul (hu.comp (by fun_prop))).mul
      (hv.comp (by fun_prop))
  rw [integral_weight_mul_crossCorrelation_eq_upperTriangle
      u v hu hv q hq,
    setIntegral_centeredUpperTriangle_eq_iterated_right F hF]
  apply intervalIntegral.integral_congr
  intro x _hx
  unfold factorTwoContinuousLagRightRepresenter
  change (∫ y : ℝ in x..1, F (y, x)) =
    v x * ∫ y : ℝ in x..1, q (y - x) * u y
  rw [show (fun y : ℝ ↦ F (y, x)) = fun y ↦
      (q (y - x) * u y) * v x by
    funext y
    dsimp only [F],
    intervalIntegral.integral_mul_const]
  ring

/-- Ordered correlation represented in the first, left-triangle
coordinate. -/
theorem integral_continuousLag_mul_crossCorrelation_eq_left
    (q u v : ℝ → ℝ)
    (hq : Continuous q) (hu : Continuous u) (hv : Continuous v) :
    (∫ t : ℝ in 0..2,
        q t * factorTwoCenteredCrossCorrelation u v t) =
      ∫ x : ℝ in -1..1,
        u x * factorTwoContinuousLagLeftRepresenter q v x := by
  let F : ℝ × ℝ → ℝ := fun z ↦
    q (z.1 - z.2) * u z.1 * v z.2
  have hF : Continuous F := by
    dsimp only [F]
    exact ((hq.comp (by fun_prop)).mul (hu.comp (by fun_prop))).mul
      (hv.comp (by fun_prop))
  rw [integral_weight_mul_crossCorrelation_eq_upperTriangle
      u v hu hv q hq,
    setIntegral_centeredUpperTriangle_eq_iterated_left F hF]
  apply intervalIntegral.integral_congr
  intro x _hx
  unfold factorTwoContinuousLagLeftRepresenter
  change (∫ y : ℝ in -1..x, F (x, y)) =
    u x * ∫ y : ℝ in -1..x, q (x - y) * v y
  rw [show (fun y : ℝ ↦ F (x, y)) = fun y ↦
      u x * (q (x - y) * v y) by
    funext y
    dsimp only [F]
    ring,
    intervalIntegral.integral_const_mul]

/-- The sum of the right and left transforms represents the symmetric
correlation polarization. -/
theorem integral_continuousLag_mul_correlationBilinear_eq_K
    (q u v : ℝ → ℝ)
    (hq : Continuous q) (hu : Continuous u) (hv : Continuous v) :
    (∫ t : ℝ in 0..2,
        q t * factorTwoCenteredCorrelationBilinear u v t) =
      (1 / 2 : ℝ) * ∫ x : ℝ in -1..1,
        v x * factorTwoContinuousLagK q u x := by
  have huvI : IntervalIntegrable (fun t : ℝ ↦
      q t * factorTwoCenteredCrossCorrelation u v t) volume 0 2 :=
    (hq.mul (continuous_factorTwoCenteredCrossCorrelation u v hu hv))
      |>.intervalIntegrable 0 2
  have hvuI : IntervalIntegrable (fun t : ℝ ↦
      q t * factorTwoCenteredCrossCorrelation v u t) volume 0 2 :=
    (hq.mul (continuous_factorTwoCenteredCrossCorrelation v u hv hu))
      |>.intervalIntegrable 0 2
  have hrightI : IntervalIntegrable (fun x : ℝ ↦
      v x * factorTwoContinuousLagRightRepresenter q u x) volume (-1) 1 :=
    (hv.mul (continuous_factorTwoContinuousLagRightRepresenter q u hq hu))
      |>.intervalIntegrable (-1) 1
  have hleftI : IntervalIntegrable (fun x : ℝ ↦
      v x * factorTwoContinuousLagLeftRepresenter q u x) volume (-1) 1 :=
    (hv.mul (continuous_factorTwoContinuousLagLeftRepresenter q u hq hu))
      |>.intervalIntegrable (-1) 1
  rw [show (fun t : ℝ ↦
      q t * factorTwoCenteredCorrelationBilinear u v t) = fun t ↦
        (1 / 2 : ℝ) *
          (q t * factorTwoCenteredCrossCorrelation u v t +
            q t * factorTwoCenteredCrossCorrelation v u t) by
    funext t
    unfold factorTwoCenteredCorrelationBilinear
    ring,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add huvI hvuI,
    integral_continuousLag_mul_crossCorrelation_eq_right q u v hq hu hv,
    integral_continuousLag_mul_crossCorrelation_eq_left q v u hq hv hu,
    ← intervalIntegral.integral_add hrightI hleftI]
  congr 1
  apply intervalIntegral.integral_congr
  intro x _hx
  unfold factorTwoContinuousLagK
  ring

/-- The right-minus-left transform represents the alternating ordered
cross-difference with the represented function in the even slot. -/
theorem integral_continuousLag_mul_crossDifference_eq_J
    (q e o : ℝ → ℝ)
    (hq : Continuous q) (he : Continuous e) (ho : Continuous o) :
    (∫ t : ℝ in 0..2,
        q t * (factorTwoCenteredCrossCorrelation o e t -
          factorTwoCenteredCrossCorrelation e o t)) =
      ∫ x : ℝ in -1..1,
        e x * factorTwoContinuousLagJ q o x := by
  have hoeI : IntervalIntegrable (fun t : ℝ ↦
      q t * factorTwoCenteredCrossCorrelation o e t) volume 0 2 :=
    (hq.mul (continuous_factorTwoCenteredCrossCorrelation o e ho he))
      |>.intervalIntegrable 0 2
  have heoI : IntervalIntegrable (fun t : ℝ ↦
      q t * factorTwoCenteredCrossCorrelation e o t) volume 0 2 :=
    (hq.mul (continuous_factorTwoCenteredCrossCorrelation e o he ho))
      |>.intervalIntegrable 0 2
  have hrightI : IntervalIntegrable (fun x : ℝ ↦
      e x * factorTwoContinuousLagRightRepresenter q o x) volume (-1) 1 :=
    (he.mul (continuous_factorTwoContinuousLagRightRepresenter q o hq ho))
      |>.intervalIntegrable (-1) 1
  have hleftI : IntervalIntegrable (fun x : ℝ ↦
      e x * factorTwoContinuousLagLeftRepresenter q o x) volume (-1) 1 :=
    (he.mul (continuous_factorTwoContinuousLagLeftRepresenter q o hq ho))
      |>.intervalIntegrable (-1) 1
  rw [show (fun t : ℝ ↦
      q t * (factorTwoCenteredCrossCorrelation o e t -
        factorTwoCenteredCrossCorrelation e o t)) = fun t ↦
      q t * factorTwoCenteredCrossCorrelation o e t -
        q t * factorTwoCenteredCrossCorrelation e o t by
    funext t
    ring,
    intervalIntegral.integral_sub hoeI heoI,
    integral_continuousLag_mul_crossCorrelation_eq_right q o e hq ho he,
    integral_continuousLag_mul_crossCorrelation_eq_left q e o hq he ho,
    ← intervalIntegral.integral_sub hrightI hleftI]
  apply intervalIntegral.integral_congr
  intro x _hx
  unfold factorTwoContinuousLagJ
  ring

/-- Equivalent alternating representation with the represented function in
the odd slot. -/
theorem integral_continuousLag_mul_crossDifference_eq_neg_J
    (q e o : ℝ → ℝ)
    (hq : Continuous q) (he : Continuous e) (ho : Continuous o) :
    (∫ t : ℝ in 0..2,
        q t * (factorTwoCenteredCrossCorrelation o e t -
          factorTwoCenteredCrossCorrelation e o t)) =
      -(∫ x : ℝ in -1..1,
        o x * factorTwoContinuousLagJ q e x) := by
  have hswap := integral_continuousLag_mul_crossDifference_eq_J
    q o e hq ho he
  rw [show (fun t : ℝ ↦
      q t * (factorTwoCenteredCrossCorrelation e o t -
        factorTwoCenteredCrossCorrelation o e t)) = fun t ↦
      -(q t * (factorTwoCenteredCrossCorrelation o e t -
        factorTwoCenteredCrossCorrelation e o t)) by
    funext t
    ring,
    intervalIntegral.integral_neg] at hswap
  linarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoContinuousLagRepresenterStructural

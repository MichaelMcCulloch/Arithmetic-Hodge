import ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedRemainderEnvelopePolynomials

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedRemainderEnvelopeMoments

open YoshidaEndpointEvenProjectedRemainderEnvelopePolynomials
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointEvenProjectedRemainderEnvelopeKernel
open YoshidaEndpointHyperbolicBound

noncomputable section

/-- Explicit constant-basis regular representer obtained from the seven
elementary absolute-power moments. -/
def regularRepresenterPolynomial6_0_explicit (x : ℝ) : ℝ :=
  (1 / 2 : ℝ) - yoshidaEndpointA / 48 * (1 + x ^ 2) -
    yoshidaEndpointA ^ 2 / 32 * ((2 / 3 : ℝ) + 2 * x ^ 2) +
    7 * yoshidaEndpointA ^ 3 / 11520 *
      ((1 / 2 : ℝ) + 3 * x ^ 2 + x ^ 4 / 2) +
    5 * yoshidaEndpointA ^ 4 / 1536 *
      ((2 / 5 : ℝ) + 4 * x ^ 2 + 2 * x ^ 4) -
    31 * yoshidaEndpointA ^ 5 / 1935360 *
      ((1 / 3 : ℝ) + 5 * x ^ 2 + 5 * x ^ 4 + x ^ 6 / 3) -
    61 * yoshidaEndpointA ^ 6 / 184320 *
      ((2 / 7 : ℝ) + 6 * x ^ 2 + 10 * x ^ 4 + 2 * x ^ 6)

/-- Explicit degree-two-basis regular representer obtained from the weighted
absolute-power moments. -/
def regularRepresenterPolynomial6_2_explicit (x : ℝ) : ℝ :=
  -(yoshidaEndpointA / 48) * (1 - x ^ 2) ^ 2 / 4 -
    yoshidaEndpointA ^ 2 / 32 * (4 / 15 : ℝ) +
    7 * yoshidaEndpointA ^ 3 / 11520 *
      ((1 / 4 : ℝ) + 3 * x ^ 2 / 4 - x ^ 4 / 4 + x ^ 6 / 20) +
    5 * yoshidaEndpointA ^ 4 / 1536 *
      ((8 / 35 : ℝ) + 8 * x ^ 2 / 5) -
    31 * yoshidaEndpointA ^ 5 / 1935360 *
      ((5 / 24 : ℝ) + 5 * x ^ 2 / 2 + 5 * x ^ 4 / 4 -
        x ^ 6 / 6 + x ^ 8 / 56) -
    61 * yoshidaEndpointA ^ 6 / 184320 *
      ((4 / 21 : ℝ) + 24 * x ^ 2 / 7 + 4 * x ^ 4)

private theorem integral_abs_sub_pow
    (n : ℕ) {x : ℝ} (hx : x ∈ Icc (-1) 1) :
    (∫ y : ℝ in -1..1, |x - y| ^ n) =
      ((x + 1) ^ (n + 1) + (1 - x) ^ (n + 1)) / (n + 1) := by
  have hcont : Continuous (fun y : ℝ ↦ |x - y| ^ n) := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (-1) x) (hcont.intervalIntegrable x 1)]
  have hleft :
      (∫ y : ℝ in -1..x, |x - y| ^ n) =
        ∫ y : ℝ in -1..x, (x - y) ^ n := by
    apply intervalIntegral.integral_congr
    intro y hy
    change |x - y| ^ n = (x - y) ^ n
    have hy' : y ∈ Icc (-1) x := by
      simpa only [uIcc_of_le hx.1] using hy
    rw [abs_of_nonneg (sub_nonneg.mpr hy'.2)]
  have hright :
      (∫ y : ℝ in x..1, |x - y| ^ n) =
        ∫ y : ℝ in x..1, (y - x) ^ n := by
    apply intervalIntegral.integral_congr
    intro y hy
    change |x - y| ^ n = (y - x) ^ n
    have hy' : y ∈ Icc x 1 := by
      simpa only [uIcc_of_le hx.2] using hy
    rw [abs_of_nonpos (sub_nonpos.mpr hy'.1), neg_sub]
  rw [hleft, hright,
    intervalIntegral.integral_comp_sub_left (f := fun y : ℝ ↦ y ^ n),
    intervalIntegral.integral_comp_sub_right (f := fun y : ℝ ↦ y ^ n),
    integral_pow, integral_pow]
  norm_num
  ring

private theorem integral_abs_sub_pow_mul_centeredEvenP2
    (n : ℕ) {x : ℝ} (hx : x ∈ Icc (-1) 1) :
    (∫ y : ℝ in -1..1, |x - y| ^ n * centeredEvenP2 y) =
      ((3 * x ^ 2 - 1) / 2) *
          ((x + 1) ^ (n + 1) + (1 - x) ^ (n + 1)) / (n + 1) +
        3 * x * ((1 - x) ^ (n + 2) - (x + 1) ^ (n + 2)) / (n + 2) +
        (3 / 2 : ℝ) *
          ((x + 1) ^ (n + 3) + (1 - x) ^ (n + 3)) / (n + 3) := by
  let fL : ℝ → ℝ := fun s ↦ s ^ n * centeredEvenP2 (x - s)
  let fR : ℝ → ℝ := fun s ↦ s ^ n * centeredEvenP2 (x + s)
  have hcont : Continuous
      (fun y : ℝ ↦ |x - y| ^ n * centeredEvenP2 y) := by
    unfold centeredEvenP2
    fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (-1) x) (hcont.intervalIntegrable x 1)]
  have hleftAbs :
      (∫ y : ℝ in -1..x, |x - y| ^ n * centeredEvenP2 y) =
        ∫ y : ℝ in -1..x, (x - y) ^ n * centeredEvenP2 y := by
    apply intervalIntegral.integral_congr
    intro y hy
    change |x - y| ^ n * centeredEvenP2 y =
      (x - y) ^ n * centeredEvenP2 y
    have hy' : y ∈ Icc (-1) x := by
      simpa only [uIcc_of_le hx.1] using hy
    rw [abs_of_nonneg (sub_nonneg.mpr hy'.2)]
  have hrightAbs :
      (∫ y : ℝ in x..1, |x - y| ^ n * centeredEvenP2 y) =
        ∫ y : ℝ in x..1, (y - x) ^ n * centeredEvenP2 y := by
    apply intervalIntegral.integral_congr
    intro y hy
    change |x - y| ^ n * centeredEvenP2 y =
      (y - x) ^ n * centeredEvenP2 y
    have hy' : y ∈ Icc x 1 := by
      simpa only [uIcc_of_le hx.2] using hy
    rw [abs_of_nonpos (sub_nonpos.mpr hy'.1), neg_sub]
  rw [hleftAbs, hrightAbs]
  have hleftSub :
      (∫ y : ℝ in -1..x, (x - y) ^ n * centeredEvenP2 y) =
        ∫ s : ℝ in 0..x + 1, fL s := by
    calc
      _ = ∫ y : ℝ in -1..x, fL (x - y) := by
        apply intervalIntegral.integral_congr
        intro y _hy
        dsimp only [fL]
        congr 1
        unfold centeredEvenP2
        ring
      _ = _ := by
        simpa only [sub_self, sub_neg_eq_add] using
          (intervalIntegral.integral_comp_sub_left
            (f := fL) (a := (-1 : ℝ)) (b := x) x)
  have hrightSub :
      (∫ y : ℝ in x..1, (y - x) ^ n * centeredEvenP2 y) =
        ∫ s : ℝ in 0..1 - x, fR s := by
    calc
      _ = ∫ y : ℝ in x..1, fR (y - x) := by
        apply intervalIntegral.integral_congr
        intro y _hy
        dsimp only [fR]
        congr 1
        unfold centeredEvenP2
        ring
      _ = _ := by
        simpa only [sub_self] using
          (intervalIntegral.integral_comp_sub_right
            (f := fR) (a := x) (b := (1 : ℝ)) x)
  rw [hleftSub, hrightSub]
  have hfL : fL = fun s ↦
      ((3 * x ^ 2 - 1) / 2) * s ^ n -
        (3 * x) * s ^ (n + 1) + (3 / 2 : ℝ) * s ^ (n + 2) := by
    funext s
    dsimp only [fL]
    unfold centeredEvenP2
    simp only [pow_add]
    ring
  have hfR : fR = fun s ↦
      ((3 * x ^ 2 - 1) / 2) * s ^ n +
        (3 * x) * s ^ (n + 1) + (3 / 2 : ℝ) * s ^ (n + 2) := by
    funext s
    dsimp only [fR]
    unfold centeredEvenP2
    simp only [pow_add]
    ring
  rw [hfL, hfR]
  have hLn0 : IntervalIntegrable (fun s : ℝ ↦ s ^ n) volume 0 (x + 1) :=
    (continuous_id.pow n).intervalIntegrable 0 (x + 1)
  have hLn1 : IntervalIntegrable (fun s : ℝ ↦ s ^ (n + 1))
      volume 0 (x + 1) := (continuous_id.pow (n + 1)).intervalIntegrable 0 (x + 1)
  have hLn2 : IntervalIntegrable (fun s : ℝ ↦ s ^ (n + 2))
      volume 0 (x + 1) := (continuous_id.pow (n + 2)).intervalIntegrable 0 (x + 1)
  have hRn0 : IntervalIntegrable (fun s : ℝ ↦ s ^ n) volume 0 (1 - x) :=
    (continuous_id.pow n).intervalIntegrable 0 (1 - x)
  have hRn1 : IntervalIntegrable (fun s : ℝ ↦ s ^ (n + 1))
      volume 0 (1 - x) := (continuous_id.pow (n + 1)).intervalIntegrable 0 (1 - x)
  have hRn2 : IntervalIntegrable (fun s : ℝ ↦ s ^ (n + 2))
      volume 0 (1 - x) := (continuous_id.pow (n + 2)).intervalIntegrable 0 (1 - x)
  rw [intervalIntegral.integral_add
      ((hLn0.const_mul ((3 * x ^ 2 - 1) / 2)).sub
        (hLn1.const_mul (3 * x)))
      (hLn2.const_mul (3 / 2 : ℝ)),
    intervalIntegral.integral_sub
      (hLn0.const_mul ((3 * x ^ 2 - 1) / 2))
      (hLn1.const_mul (3 * x)),
    intervalIntegral.integral_add
      ((hRn0.const_mul ((3 * x ^ 2 - 1) / 2)).add
        (hRn1.const_mul (3 * x)))
      (hRn2.const_mul (3 / 2 : ℝ)),
    intervalIntegral.integral_add
      (hRn0.const_mul ((3 * x ^ 2 - 1) / 2))
      (hRn1.const_mul (3 * x)),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    integral_pow, integral_pow, integral_pow, integral_pow, integral_pow, integral_pow]
  push_cast
  ring

private theorem regularRepresenterPolynomial6_p0_eq_core
    {x : ℝ} (hx : x ∈ Icc (-1) 1) :
    yoshidaEndpointEvenRegularRepresenterPolynomial6 centeredEvenP0 x =
      regularRepresenterPolynomial6_0_explicit x := by
  let d : ℝ → ℝ := fun y ↦ |x - y|
  let g0 : ℝ → ℝ := fun y ↦ (1 / 4 : ℝ) * d y ^ 0
  let g1 : ℝ → ℝ := fun y ↦
    (yoshidaEndpointA / 48 : ℝ) * d y ^ 1
  let g2 : ℝ → ℝ := fun y ↦
    (yoshidaEndpointA ^ 2 / 32 : ℝ) * d y ^ 2
  let g3 : ℝ → ℝ := fun y ↦
    (7 * yoshidaEndpointA ^ 3 / 11520 : ℝ) * d y ^ 3
  let g4 : ℝ → ℝ := fun y ↦
    (5 * yoshidaEndpointA ^ 4 / 1536 : ℝ) * d y ^ 4
  let g5 : ℝ → ℝ := fun y ↦
    (31 * yoshidaEndpointA ^ 5 / 1935360 : ℝ) * d y ^ 5
  let g6 : ℝ → ℝ := fun y ↦
    (61 * yoshidaEndpointA ^ 6 / 184320 : ℝ) * d y ^ 6
  have hg0 : IntervalIntegrable g0 volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    dsimp only [g0, d]
    fun_prop
  have hg1 : IntervalIntegrable g1 volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    dsimp only [g1, d]
    fun_prop
  have hg2 : IntervalIntegrable g2 volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    dsimp only [g2, d]
    fun_prop
  have hg3 : IntervalIntegrable g3 volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    dsimp only [g3, d]
    fun_prop
  have hg4 : IntervalIntegrable g4 volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    dsimp only [g4, d]
    fun_prop
  have hg5 : IntervalIntegrable g5 volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    dsimp only [g5, d]
    fun_prop
  have hg6 : IntervalIntegrable g6 volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    dsimp only [g6, d]
    fun_prop
  unfold yoshidaEndpointEvenRegularRepresenterPolynomial6 centeredEvenP0
  rw [show (fun y : ℝ ↦
      yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * |x - y|) * 1) =
      fun y ↦ (((((g0 y - g1 y) - g2 y) + g3 y) + g4 y) - g5 y) - g6 y by
    funext y
    dsimp only [g0, g1, g2, g3, g4, g5, g6, d]
    unfold yoshidaRegularKernelPolynomial6
    ring]
  rw [intervalIntegral.integral_sub
      (((((hg0.sub hg1).sub hg2).add hg3).add hg4).sub hg5) hg6,
    intervalIntegral.integral_sub
      ((((hg0.sub hg1).sub hg2).add hg3).add hg4) hg5,
    intervalIntegral.integral_add
      (((hg0.sub hg1).sub hg2).add hg3) hg4,
    intervalIntegral.integral_add ((hg0.sub hg1).sub hg2) hg3,
    intervalIntegral.integral_sub (hg0.sub hg1) hg2,
    intervalIntegral.integral_sub hg0 hg1]
  dsimp only [g0, g1, g2, g3, g4, g5, g6, d]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    integral_abs_sub_pow 0 hx, integral_abs_sub_pow 1 hx,
    integral_abs_sub_pow 2 hx, integral_abs_sub_pow 3 hx,
    integral_abs_sub_pow 4 hx, integral_abs_sub_pow 5 hx,
    integral_abs_sub_pow 6 hx]
  unfold regularRepresenterPolynomial6_0_explicit
  norm_num
  ring

/-- The integral-defined constant representer envelope is the advertised
explicit even polynomial. -/
theorem regularRepresenterPolynomial6_p0_eq
    {x : ℝ} (hx : x ∈ Icc (-1) 1) :
    yoshidaEndpointEvenRegularRepresenterPolynomial6 centeredEvenP0 x =
      regularRepresenterPolynomial6_0_explicit x := by
  exact regularRepresenterPolynomial6_p0_eq_core hx

private theorem regularRepresenterPolynomial6_p2_eq_core
    {x : ℝ} (hx : x ∈ Icc (-1) 1) :
    yoshidaEndpointEvenRegularRepresenterPolynomial6 centeredEvenP2 x =
      regularRepresenterPolynomial6_2_explicit x := by
  let d : ℝ → ℝ := fun y ↦ |x - y|
  let g0 : ℝ → ℝ := fun y ↦
    (1 / 4 : ℝ) * (d y ^ 0 * centeredEvenP2 y)
  let g1 : ℝ → ℝ := fun y ↦
    (yoshidaEndpointA / 48 : ℝ) * (d y ^ 1 * centeredEvenP2 y)
  let g2 : ℝ → ℝ := fun y ↦
    (yoshidaEndpointA ^ 2 / 32 : ℝ) * (d y ^ 2 * centeredEvenP2 y)
  let g3 : ℝ → ℝ := fun y ↦
    (7 * yoshidaEndpointA ^ 3 / 11520 : ℝ) *
      (d y ^ 3 * centeredEvenP2 y)
  let g4 : ℝ → ℝ := fun y ↦
    (5 * yoshidaEndpointA ^ 4 / 1536 : ℝ) *
      (d y ^ 4 * centeredEvenP2 y)
  let g5 : ℝ → ℝ := fun y ↦
    (31 * yoshidaEndpointA ^ 5 / 1935360 : ℝ) *
      (d y ^ 5 * centeredEvenP2 y)
  let g6 : ℝ → ℝ := fun y ↦
    (61 * yoshidaEndpointA ^ 6 / 184320 : ℝ) *
      (d y ^ 6 * centeredEvenP2 y)
  have hg0 : IntervalIntegrable g0 volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    dsimp only [g0, d]
    unfold centeredEvenP2
    fun_prop
  have hg1 : IntervalIntegrable g1 volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    dsimp only [g1, d]
    unfold centeredEvenP2
    fun_prop
  have hg2 : IntervalIntegrable g2 volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    dsimp only [g2, d]
    unfold centeredEvenP2
    fun_prop
  have hg3 : IntervalIntegrable g3 volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    dsimp only [g3, d]
    unfold centeredEvenP2
    fun_prop
  have hg4 : IntervalIntegrable g4 volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    dsimp only [g4, d]
    unfold centeredEvenP2
    fun_prop
  have hg5 : IntervalIntegrable g5 volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    dsimp only [g5, d]
    unfold centeredEvenP2
    fun_prop
  have hg6 : IntervalIntegrable g6 volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    dsimp only [g6, d]
    unfold centeredEvenP2
    fun_prop
  unfold yoshidaEndpointEvenRegularRepresenterPolynomial6
  rw [show (fun y : ℝ ↦
      yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * |x - y|) *
        centeredEvenP2 y) =
      fun y ↦ (((((g0 y - g1 y) - g2 y) + g3 y) + g4 y) - g5 y) - g6 y by
    funext y
    dsimp only [g0, g1, g2, g3, g4, g5, g6, d]
    unfold yoshidaRegularKernelPolynomial6
    ring]
  rw [intervalIntegral.integral_sub
      (((((hg0.sub hg1).sub hg2).add hg3).add hg4).sub hg5) hg6,
    intervalIntegral.integral_sub
      ((((hg0.sub hg1).sub hg2).add hg3).add hg4) hg5,
    intervalIntegral.integral_add
      (((hg0.sub hg1).sub hg2).add hg3) hg4,
    intervalIntegral.integral_add ((hg0.sub hg1).sub hg2) hg3,
    intervalIntegral.integral_sub (hg0.sub hg1) hg2,
    intervalIntegral.integral_sub hg0 hg1]
  dsimp only [g0, g1, g2, g3, g4, g5, g6, d]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    integral_abs_sub_pow_mul_centeredEvenP2 0 hx,
    integral_abs_sub_pow_mul_centeredEvenP2 1 hx,
    integral_abs_sub_pow_mul_centeredEvenP2 2 hx,
    integral_abs_sub_pow_mul_centeredEvenP2 3 hx,
    integral_abs_sub_pow_mul_centeredEvenP2 4 hx,
    integral_abs_sub_pow_mul_centeredEvenP2 5 hx,
    integral_abs_sub_pow_mul_centeredEvenP2 6 hx]
  unfold regularRepresenterPolynomial6_2_explicit
  norm_num
  ring

/-- The integral-defined degree-two representer envelope is the advertised
explicit even polynomial. -/
theorem regularRepresenterPolynomial6_p2_eq
    {x : ℝ} (hx : x ∈ Icc (-1) 1) :
    yoshidaEndpointEvenRegularRepresenterPolynomial6 centeredEvenP2 x =
      regularRepresenterPolynomial6_2_explicit x := by
  exact regularRepresenterPolynomial6_p2_eq_core hx

end

end ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedRemainderEnvelopeMoments

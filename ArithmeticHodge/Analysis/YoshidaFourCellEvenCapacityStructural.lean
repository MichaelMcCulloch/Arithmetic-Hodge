import ArithmeticHodge.Analysis.YoshidaConstantBounds
import ArithmeticHodge.Analysis.YoshidaFourCellParityOperatorStructural
import ArithmeticHodge.Analysis.YoshidaFourCellRegularParityFoldStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellEvenCapacityStructural

noncomputable section

open YoshidaConstantBounds
open CenteredEndpointCorrelation
open YoshidaEndpointPotentialIntegrable
open YoshidaEndpointPotentialBound
open YoshidaFourCellParityHalfFoldStructural
open YoshidaFourCellEndpointVarianceStructural
open YoshidaFourCellParityOperatorStructural
open YoshidaFourCellRawParityFoldStructural
open YoshidaFourCellRegularKernelSquareStructural
open YoshidaFourCellRegularParityFoldStructural
open YoshidaGeneralEndpointPhysicalRealQuadraticStructural
open YoshidaRegularKernelBound

/-!
# Structural endpoint capacity in the even four-cell channel

The adverse even prime translation is paired with the endpoint potential
before either term is estimated.  On the strip `x + y = 8 / 5`, the product
of the two endpoint potentials has a uniform positive lower bound.  This
makes the corresponding two-by-two pointwise quadratic positive and leaves
all raw-log, regular-square, scalar, and cosh terms untouched.
-/

/-- The first five positive Taylor terms of the endpoint potential. -/
def fourCellEndpointPotentialTaylorFive (x : ℝ) : ℝ :=
  x ^ 2 / 2 + x ^ 4 / 4 + x ^ 6 / 6 + x ^ 8 / 8 + x ^ 10 / 10

/-- Five positive terms of `-log (1-x²)/2` remain below the exact endpoint
potential throughout the open interval. -/
theorem fourCellEndpointPotentialTaylorFive_le
    {x : ℝ} (hx : |x| < 1) :
    fourCellEndpointPotentialTaylorFive x ≤ yoshidaEndpointPotential x := by
  let R : ℝ → ℝ := fun u ↦
    -Real.log (1 - u) -
      (u + u ^ 2 / 2 + u ^ 3 / 3 + u ^ 4 / 4 + u ^ 5 / 5)
  have hu0 : 0 ≤ x ^ 2 := sq_nonneg x
  have hu1 : x ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one x).2 hx
  have hRderiv (u : ℝ) (hu : u < 1) :
      HasDerivAt R (u ^ 5 / (1 - u)) u := by
    have hinner : HasDerivAt (fun t : ℝ ↦ 1 - t) (-1) u := by
      convert (hasDerivAt_const u (1 : ℝ)).sub (hasDerivAt_id u) using 1
      ring
    have hne : 1 - u ≠ 0 := by linarith
    have hlog := (Real.hasDerivAt_log hne).comp u hinner
    have h2 := ((hasDerivAt_id u).pow 2).div_const (2 : ℝ)
    have h3 := ((hasDerivAt_id u).pow 3).div_const (3 : ℝ)
    have h4 := ((hasDerivAt_id u).pow 4).div_const (4 : ℝ)
    have h5 := ((hasDerivAt_id u).pow 5).div_const (5 : ℝ)
    dsimp only [R]
    convert (((((hlog.neg.sub (hasDerivAt_id u)).sub h2).sub h3).sub h4).sub h5) using 1
    · funext z
      simp only [Pi.sub_apply, Pi.neg_apply, Pi.pow_apply,
        Function.comp_apply, id_eq]
      ring
    · simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, mul_one]
      field_simp [hne]
      ring
  have hRcont : ContinuousOn R (Icc 0 (x ^ 2)) := by
    intro u hu
    exact (hRderiv u (lt_of_le_of_lt hu.2 hu1)).continuousAt.continuousWithinAt
  have hRmono : MonotoneOn R (Icc 0 (x ^ 2)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 (x ^ 2)) hRcont ?_ ?_
    · intro u hu
      exact (hRderiv u (lt_of_le_of_lt (interior_subset hu).2 hu1)).differentiableAt
        |>.differentiableWithinAt
    · intro u hu
      rw [(hRderiv u (lt_of_le_of_lt (interior_subset hu).2 hu1)).deriv]
      exact div_nonneg (pow_nonneg (interior_subset hu).1 5)
        (by linarith [(interior_subset hu).2])
  have hRnonneg : 0 ≤ R (x ^ 2) := by
    have hmono := hRmono (by exact ⟨le_rfl, hu0⟩)
      (by exact ⟨hu0, le_rfl⟩) hu0
    simpa [R] using hmono
  dsimp only [R] at hRnonneg
  unfold fourCellEndpointPotentialTaylorFive yoshidaEndpointPotential
  nlinarith [hRnonneg]

/-- The fifth-order lower potential has its smallest reflected product at
the midpoint `4/5` of the endpoint strip.  The proof is a centered polynomial
factorization with a manifestly positive residual on `|x-4/5| ≤ 1/5`. -/
theorem endpointPotentialTaylorFive_reflected_product_min
    {x : ℝ} (hx0 : (3 / 5 : ℝ) ≤ x) (hx1 : x ≤ 1) :
    fourCellEndpointPotentialTaylorFive (4 / 5) ^ 2 ≤
      fourCellEndpointPotentialTaylorFive x *
        fourCellEndpointPotentialTaylorFive (8 / 5 - x) := by
  let q : ℝ := (x - 4 / 5) ^ 2
  have hq0 : 0 ≤ q := by dsimp only [q]; positivity
  have hzlo : 0 ≤ (x - 4 / 5) + 1 / 5 := by linarith
  have hzhi : 0 ≤ 1 / 5 - (x - 4 / 5) := by linarith
  have hq : q ≤ 1 / 25 := by
    have hprod := mul_nonneg hzlo hzhi
    dsimp only [q]
    nlinarith
  have hq1 : q ≤ 1 := hq.trans (by norm_num)
  have hqSq : q ^ 2 ≤ (1 / 25 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hq0 hq 2
  have hq3 : q ^ 3 ≤ 1 := pow_le_one₀ hq0 hq1
  have hq5 : q ^ 5 ≤ 1 := pow_le_one₀ hq0 hq1
  have hbase :
      0 ≤
        (11642456881096 / 57220458984375 : ℝ) -
          (2627650627211 / 3051757812500 : ℝ) * q -
          (1972032295771 / 1098632812500 : ℝ) * q ^ 2 := by
    nlinarith
  have htailBracket :
      0 ≤
        (31648253613 / 19531250000 : ℝ) +
          (2575290071 / 1953125000 : ℝ) * q +
          (136096457 / 281250000 : ℝ) * q ^ 2 -
          (183949 / 1875000 : ℝ) * q ^ 3 +
          (72767 / 600000 : ℝ) * q ^ 4 -
          (39 / 1000 : ℝ) * q ^ 5 +
          (1 / 100 : ℝ) * q ^ 6 := by
    have hq2nonneg : 0 ≤ q ^ 2 := pow_nonneg hq0 2
    have hq4nonneg : 0 ≤ q ^ 4 := pow_nonneg hq0 4
    have hq6nonneg : 0 ≤ q ^ 6 := pow_nonneg hq0 6
    nlinarith
  have hfactor :
      fourCellEndpointPotentialTaylorFive x *
          fourCellEndpointPotentialTaylorFive (8 / 5 - x) -
          fourCellEndpointPotentialTaylorFive (4 / 5) ^ 2 =
        q *
          ((11642456881096 / 57220458984375 : ℝ) -
            (2627650627211 / 3051757812500 : ℝ) * q -
            (1972032295771 / 1098632812500 : ℝ) * q ^ 2 +
            q ^ 3 *
              ((31648253613 / 19531250000 : ℝ) +
                (2575290071 / 1953125000 : ℝ) * q +
                (136096457 / 281250000 : ℝ) * q ^ 2 -
                (183949 / 1875000 : ℝ) * q ^ 3 +
                (72767 / 600000 : ℝ) * q ^ 4 -
                (39 / 1000 : ℝ) * q ^ 5 +
                (1 / 100 : ℝ) * q ^ 6)) := by
    dsimp only [q]
    unfold fourCellEndpointPotentialTaylorFive
    ring
  apply sub_nonneg.mp
  rw [hfactor]
  exact mul_nonneg hq0
    (add_nonneg hbase (mul_nonneg (pow_nonneg hq0 3) htailBracket))

/-- The dyadic prime weight lies strictly inside the determinant furnished
by the reflected fifth-order endpoint potentials.  The factor `99/100`
leaves a genuine one-percent reserve of the exact strip potential. -/
theorem fourCell_dyadicWeight_sq_lt_reflectedTaylor_determinant :
    (Real.sqrt 2 * Real.log 2) ^ 2 <
      4 * (99 / 100 : ℝ) ^ 2 *
        fourCellEndpointPotentialTaylorFive (4 / 5) ^ 2 := by
  have hsqrt : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hlog := strict_log_two_bounds.2
  have hlog0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogSq : (Real.log 2) ^ 2 < (6932 / 10000 : ℝ) ^ 2 := by
    nlinarith
  rw [mul_pow, hsqrt]
  unfold fourCellEndpointPotentialTaylorFive
  norm_num at ⊢
  nlinarith

/-- Uniform determinant for the two endpoint potentials exchanged by the
four-cell prime involution. -/
theorem fourCell_reflected_endpointPotential_determinant
    {x : ℝ} (hx0 : (3 / 5 : ℝ) < x) (hx1 : x < 1) :
    (Real.sqrt 2 * Real.log 2) ^ 2 <
      4 * ((99 / 100 : ℝ) * yoshidaEndpointPotential x) *
        ((99 / 100 : ℝ) * yoshidaEndpointPotential (8 / 5 - x)) := by
  have hy0 : (3 / 5 : ℝ) < 8 / 5 - x := by linarith
  have hy1 : 8 / 5 - x < 1 := by linarith
  have hxabs : |x| < 1 := by rw [abs_lt]; constructor <;> linarith
  have hyabs : |8 / 5 - x| < 1 := by
    rw [abs_lt]
    constructor <;> linarith
  let Px := fourCellEndpointPotentialTaylorFive x
  let Py := fourCellEndpointPotentialTaylorFive (8 / 5 - x)
  let Vx := yoshidaEndpointPotential x
  let Vy := yoshidaEndpointPotential (8 / 5 - x)
  have hPx0 : 0 ≤ Px := by
    dsimp only [Px, fourCellEndpointPotentialTaylorFive]
    positivity
  have hPy0 : 0 ≤ Py := by
    dsimp only [Py, fourCellEndpointPotentialTaylorFive]
    positivity
  have hPxVx : Px ≤ Vx := by
    simpa only [Px, Vx] using fourCellEndpointPotentialTaylorFive_le hxabs
  have hPyVy : Py ≤ Vy := by
    simpa only [Py, Vy] using fourCellEndpointPotentialTaylorFive_le hyabs
  have hVx0 : 0 ≤ Vx := hPx0.trans hPxVx
  have hVy0 : 0 ≤ Vy := hPy0.trans hPyVy
  have hprod : Px * Py ≤ Vx * Vy :=
    mul_le_mul hPxVx hPyVy hPy0 hVx0
  have hmin := endpointPotentialTaylorFive_reflected_product_min
    hx0.le hx1.le
  change fourCellEndpointPotentialTaylorFive (4 / 5) ^ 2 ≤ Px * Py at hmin
  have hweight := fourCell_dyadicWeight_sq_lt_reflectedTaylor_determinant
  dsimp only [Vx, Vy] at hVx0 hVy0 ⊢
  dsimp only [Px, Py] at hprod hmin
  nlinarith

/-- Pointwise Schur absorption of the even dyadic translation by its two
reflected endpoint potentials.  One percent of each potential is retained. -/
theorem fourCell_dyadic_product_le_reflected_endpointPotentials
    {x : ℝ} (hx0 : (3 / 5 : ℝ) < x) (hx1 : x < 1)
    (u v : ℝ) :
    Real.sqrt 2 * Real.log 2 * u * v ≤
      (99 / 100 : ℝ) *
        (yoshidaEndpointPotential x * u ^ 2 +
          yoshidaEndpointPotential (8 / 5 - x) * v ^ 2) := by
  let beta := Real.sqrt 2 * Real.log 2
  let A := (99 / 100 : ℝ) * yoshidaEndpointPotential x
  let B := (99 / 100 : ℝ) * yoshidaEndpointPotential (8 / 5 - x)
  have hxabs : |x| < 1 := by rw [abs_lt]; constructor <;> linarith
  have hTaylorPos : 0 < fourCellEndpointPotentialTaylorFive x := by
    unfold fourCellEndpointPotentialTaylorFive
    have hxpos : 0 < x := by linarith
    have hxSq : 0 < x ^ 2 := sq_pos_of_pos hxpos
    positivity
  have hpotentialPos : 0 < yoshidaEndpointPotential x :=
    hTaylorPos.trans_le (fourCellEndpointPotentialTaylorFive_le hxabs)
  have hA : 0 < A := by dsimp only [A]; positivity
  have hdet : beta ^ 2 < 4 * A * B := by
    simpa only [beta, A, B, mul_assoc] using
      fourCell_reflected_endpointPotential_determinant hx0 hx1
  have hdet' : 0 ≤ 4 * A * B - beta ^ 2 := by linarith
  have hscaled :
      0 ≤ 4 * A * (A * u ^ 2 + B * v ^ 2 - beta * u * v) := by
    rw [show 4 * A * (A * u ^ 2 + B * v ^ 2 - beta * u * v) =
        (2 * A * u - beta * v) ^ 2 +
          (4 * A * B - beta ^ 2) * v ^ 2 by ring]
    exact add_nonneg (sq_nonneg _) (mul_nonneg hdet' (sq_nonneg v))
  have hcore : 0 ≤ A * u ^ 2 + B * v ^ 2 - beta * u * v :=
    nonneg_of_mul_nonneg_left
      (by simpa only [mul_comm] using hscaled) (by positivity : 0 < 4 * A)
  dsimp only [A, B, beta] at hcore ⊢
  linarith

/-- Integrated endpoint-capacity inequality in the actual ambient even
sector.  The adverse prime translation spends only `99/100` of each of the
two reflected strip potentials. -/
theorem fourCell_dyadicPairing_le_endpointStripPotential
    (w : ℝ → ℝ) (hw : Continuous w) (heven : Function.Even w) :
    Real.sqrt 2 * Real.log 2 * fourCellEndpointPairing w ≤
      (99 / 50 : ℝ) *
        (∫ x : ℝ in 3 / 5..1,
          yoshidaEndpointPotential x * w x ^ 2) := by
  let g : ℝ → ℝ := fun x ↦ yoshidaEndpointPotential x * w x ^ 2
  let reflectedProduct : ℝ → ℝ := fun x ↦ w x * w (8 / 5 - x)
  have hpotentialFull := intervalIntegrable_endpointPotential_mul_sq w hw
  have hsubset : uIcc (3 / 5 : ℝ) 1 ⊆ uIcc (-1 : ℝ) 1 := by
    intro x hx
    norm_num at hx ⊢
    constructor <;> linarith
  have hpotential : IntervalIntegrable g volume (3 / 5) 1 := by
    dsimp only [g]
    exact IntervalIntegrable.mono_set hpotentialFull hsubset
  have hreflectedPotential : IntervalIntegrable (fun x ↦ g (8 / 5 - x))
      volume (3 / 5) 1 := by
    convert (hpotential.comp_sub_left (8 / 5)).symm using 1 <;> norm_num
  have hleft : IntervalIntegrable
      (fun x ↦ Real.sqrt 2 * Real.log 2 * reflectedProduct x)
      volume (3 / 5) 1 := by
    apply Continuous.intervalIntegrable
    dsimp only [reflectedProduct]
    fun_prop
  have hright : IntervalIntegrable
      (fun x ↦ (99 / 100 : ℝ) * (g x + g (8 / 5 - x)))
      volume (3 / 5) 1 :=
    (hpotential.add hreflectedPotential).const_mul (99 / 100)
  have hmono :
      (∫ x : ℝ in 3 / 5..1,
          Real.sqrt 2 * Real.log 2 * reflectedProduct x) ≤
        ∫ x : ℝ in 3 / 5..1,
          (99 / 100 : ℝ) * (g x + g (8 / 5 - x)) := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo
      (by norm_num) hleft hright
    intro x hx
    dsimp only [reflectedProduct, g]
    simpa only [mul_assoc] using
      fourCell_dyadic_product_le_reflected_endpointPotentials
        hx.1 hx.2 (w x) (w (8 / 5 - x))
  have hreflect := intervalIntegral.integral_comp_sub_left
    (f := g) (a := (3 / 5 : ℝ)) (b := 1) (8 / 5)
  have hreflectEq :
      (∫ x : ℝ in 3 / 5..1, g (8 / 5 - x)) =
        ∫ x : ℝ in 3 / 5..1, g x := by
    convert hreflect using 1
    all_goals norm_num
  have hmono' :
      Real.sqrt 2 * Real.log 2 *
          (∫ x : ℝ in 3 / 5..1, reflectedProduct x) ≤
        (99 / 50 : ℝ) * ∫ x : ℝ in 3 / 5..1, g x := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add hpotential hreflectedPotential,
      hreflectEq] at hmono
    linarith
  have hpair : fourCellEndpointPairing w =
      ∫ x : ℝ in 3 / 5..1, reflectedProduct x := by
    unfold fourCellEndpointPairing
    apply intervalIntegral.integral_congr
    intro x _hx
    dsimp only [reflectedProduct]
    rw [show x - 8 / 5 = -(8 / 5 - x) by ring, heven]
  rw [hpair]
  simpa only [g] using hmono'

/-- The exact even operator after the adverse dyadic translation has been
paid by only `99/100` of each reflected strip potential.  Every raw term,
regular difference square, scalar term, and positive cosh rank is retained. -/
def fourCellEvenPostPrimeLowerOperator (w : ℝ → ℝ) : ℝ :=
  (1 / 2 : ℝ) *
      (fourCellPositiveHalfRawSameSignEnergy w +
        fourCellPositiveHalfRawReflectedEnergy w 1) +
    2 * (∫ x : ℝ in 0..1,
      yoshidaEndpointPotential x * w x ^ 2) -
    (99 / 50 : ℝ) * (∫ x : ℝ in 3 / 5..1,
      yoshidaEndpointPotential x * w x ^ 2) -
    2 * (Real.log (2 * fourCellOperatorHalfWidth) +
        Real.eulerMascheroniConstant + Real.log Real.pi) *
      (∫ x : ℝ in 0..1, w x ^ 2) +
    fourCellOperatorHalfWidth *
      (fourCellPositiveHalfRegularSameSignSquare w
          fourCellOperatorHalfWidth +
        fourCellPositiveHalfRegularReflectedSquare w
          fourCellOperatorHalfWidth 1) -
    2 * fourCellOperatorHalfWidth *
      fourCellPositiveHalfRegularRowMass w fourCellOperatorHalfWidth +
    8 * fourCellOperatorHalfWidth *
      fourCellPositiveCoshMoment w
        (fourCellOperatorHalfWidth / 2) ^ 2

private theorem fourCellOperatorHalfWidth_nonneg :
    0 ≤ fourCellOperatorHalfWidth := by
  unfold fourCellOperatorHalfWidth
  positivity

private theorem fourCellOperatorHalfWidth_le_log_three_div_two :
    fourCellOperatorHalfWidth ≤ Real.log 3 / 2 := by
  have h := five_mul_log_two_div_four_lt_log_three
  unfold fourCellOperatorHalfWidth
  linarith

private theorem even_regularFullSquare_eq_completion
    (w : ℝ → ℝ) (hw : Continuous w) (heven : Function.Even w) :
    -fourCellOperatorHalfWidth * fourCellRegularFullSquare w =
      fourCellOperatorHalfWidth *
          (fourCellPositiveHalfRegularSameSignSquare w
              fourCellOperatorHalfWidth +
            fourCellPositiveHalfRegularReflectedSquare w
              fourCellOperatorHalfWidth 1) -
        2 * fourCellOperatorHalfWidth *
          fourCellPositiveHalfRegularRowMass w fourCellOperatorHalfWidth := by
  let I : ℝ := ∫ t : ℝ in 0..2,
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
      centeredEndpointCorrelation w t
  have hfull :=
    two_mul_integral_yoshidaRegularKernel_mul_centeredCorrelation_eq_fullSquare
      w hw fourCellOperatorHalfWidth fourCellOperatorHalfWidth_nonneg
        fourCellOperatorHalfWidth_le_log_three_div_two
  change 2 * I = fourCellRegularFullSquare w at hfull
  have hcompletion :=
    neg_two_mul_regularCorrelation_eq_positiveHalfCompletion_even
      w hw heven fourCellOperatorHalfWidth
        fourCellOperatorHalfWidth_nonneg
        fourCellOperatorHalfWidth_le_log_three_div_two
  change -2 * fourCellOperatorHalfWidth * I = _ at hcompletion
  calc
    -fourCellOperatorHalfWidth * fourCellRegularFullSquare w =
        -2 * fourCellOperatorHalfWidth * I := by rw [← hfull]; ring
    _ = _ := hcompletion

private theorem evenParityOperator_eq_completedPrimePairing
    (w : ℝ → ℝ) (hw : Continuous w) (heven : Function.Even w) :
    fourCellEvenParityOperator w =
      (1 / 2 : ℝ) *
          (fourCellPositiveHalfRawSameSignEnergy w +
            fourCellPositiveHalfRawReflectedEnergy w 1) +
        2 * (∫ x : ℝ in 0..1,
          yoshidaEndpointPotential x * w x ^ 2) -
        2 * (Real.log (2 * fourCellOperatorHalfWidth) +
            Real.eulerMascheroniConstant + Real.log Real.pi) *
          (∫ x : ℝ in 0..1, w x ^ 2) +
        fourCellOperatorHalfWidth *
          (fourCellPositiveHalfRegularSameSignSquare w
              fourCellOperatorHalfWidth +
            fourCellPositiveHalfRegularReflectedSquare w
              fourCellOperatorHalfWidth 1) -
        2 * fourCellOperatorHalfWidth *
          fourCellPositiveHalfRegularRowMass w fourCellOperatorHalfWidth +
        8 * fourCellOperatorHalfWidth *
          fourCellPositiveCoshMoment w
            (fourCellOperatorHalfWidth / 2) ^ 2 -
        Real.sqrt 2 * Real.log 2 * fourCellEndpointPairing w := by
  have hregular := even_regularFullSquare_eq_completion w hw heven
  have hprime := neg_primePairing_eq_halfAntimatched_sub_mass_of_even
    w hw heven
  unfold fourCellEvenParityOperator
  linear_combination hregular - hprime

/-- The post-prime operator is a rigorous lower bound for the exact even
parity operator on its full continuous even form domain. -/
theorem fourCellEvenPostPrimeLowerOperator_le
    (w : ℝ → ℝ) (hw : Continuous w) (heven : Function.Even w) :
    fourCellEvenPostPrimeLowerOperator w ≤ fourCellEvenParityOperator w := by
  have hprime := fourCell_dyadicPairing_le_endpointStripPotential w hw heven
  rw [evenParityOperator_eq_completedPrimePairing w hw heven]
  unfold fourCellEvenPostPrimeLowerOperator
  linarith

/-- Nonnegativity of the explicit post-prime, regular-completed lower
operator is sufficient for the complete even four-cell bracket. -/
theorem fourCellBracket_nonnegative_of_evenPostPrimeLowerOperator
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w)
    (heven : Function.Even w)
    (hlower : 0 ≤ fourCellEvenPostPrimeLowerOperator w) :
    0 ≤ centeredClippedPhysicalQuadratic fourCellOperatorHalfWidth w -
      Real.sqrt 2 * Real.log 2 * fourCellEndpointPairing w := by
  rw [fourCellBracket_eq_evenParityOperator w hw hlocal heven]
  exact hlower.trans (fourCellEvenPostPrimeLowerOperator_le w hw heven)

end

end ArithmeticHodge.Analysis.YoshidaFourCellEvenCapacityStructural

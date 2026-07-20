import ArithmeticHodge.Analysis.YoshidaFourCellOddStripCapacityClosureStructural

set_option autoImplicit false

open Real

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddCoreGroundStatePiconeStructural

noncomputable section

open YoshidaFourCellParityOperatorStructural
open YoshidaFourCellOddStripCapacityClosureStructural
open YoshidaRegularKernelBound
open YoshidaConstantBounds

/-!
# Ground-state algebra for the complete odd four-cell core

This file isolates the exact pointwise algebra needed by a structural
ground-state proof.  It makes no positivity assumption about the unresolved
complete odd core.

There are two distinct facts.  First, both the same-sign and reflected raw
channels admit the same Picone remainder, so they can be transformed together
against one positive profile.  Second, the signed regular convolution has an
exact Dirichlet-minus-row decomposition.  The final lemmas record why a
*scalar* Stieltjes treatment of the complete kernel cannot simply absorb the
removed strip-odd raw energy: that term has a strictly positive reflected
off-diagonal polarization.
-/

/-! ## Pointwise two-channel Picone identities -/

/-- Picone's identity for a difference square, in the exact normalization
used by the same-sign raw channel. -/
theorem picone_sub_sq_identity
    {phiX phiY wX wY : ℝ} (hphiX : phiX ≠ 0) (hphiY : phiY ≠ 0) :
    (wX - wY) ^ 2 =
      phiX * phiY * (wX / phiX - wY / phiY) ^ 2 +
        (phiX - phiY) * (wX ^ 2 / phiX - wY ^ 2 / phiY) := by
  field_simp [hphiX, hphiY]
  ring

/-- The reflected (plus-square) raw channel has exactly the same Picone
remainder as the same-sign channel. -/
theorem picone_add_sq_identity
    {phiX phiY wX wY : ℝ} (hphiX : phiX ≠ 0) (hphiY : phiY ≠ 0) :
    (wX + wY) ^ 2 =
      phiX * phiY * (wX / phiX + wY / phiY) ^ 2 +
        (phiX - phiY) * (wX ^ 2 / phiX - wY ^ 2 / phiY) := by
  field_simp [hphiX, hphiY]
  ring

/-- Simultaneous Picone transform for arbitrary same-sign and reflected
kernel weights.  This is the pointwise identity whose symmetric integral
turns the last line into the ground-state row `L phi / phi`. -/
theorem picone_two_channel_identity
    {kSub kAdd phiX phiY wX wY : ℝ}
    (hphiX : phiX ≠ 0) (hphiY : phiY ≠ 0) :
    kSub * (wX - wY) ^ 2 + kAdd * (wX + wY) ^ 2 =
      phiX * phiY *
          (kSub * (wX / phiX - wY / phiY) ^ 2 +
            kAdd * (wX / phiX + wY / phiY) ^ 2) +
        (kSub + kAdd) * (phiX - phiY) *
          (wX ^ 2 / phiX - wY ^ 2 / phiY) := by
  rw [picone_sub_sq_identity hphiX hphiY,
    picone_add_sq_identity hphiX hphiY]
  ring

/-- Under the expected positive-profile and positive-kernel hypotheses, the
two quotient squares in the Picone transform are genuinely nonnegative. -/
theorem picone_two_channel_square_nonneg
    {kSub kAdd phiX phiY wX wY : ℝ}
    (hkSub : 0 ≤ kSub) (hkAdd : 0 ≤ kAdd)
    (hphiX : 0 ≤ phiX) (hphiY : 0 ≤ phiY) :
    0 ≤ phiX * phiY *
      (kSub * (wX / phiX - wY / phiY) ^ 2 +
        kAdd * (wX / phiX + wY / phiY) ^ 2) := by
  positivity

/-- Pointwise supersolution form of the two-channel Picone transform.  After
integration, its left-hand side is the raw ground-state row; proving that row
dominates the remaining local potential is the genuinely new analytic lemma
needed by this route. -/
theorem picone_two_channel_row_le
    {kSub kAdd phiX phiY wX wY : ℝ}
    (hkSub : 0 ≤ kSub) (hkAdd : 0 ≤ kAdd)
    (hphiX : 0 < phiX) (hphiY : 0 < phiY) :
    (kSub + kAdd) * (phiX - phiY) *
        (wX ^ 2 / phiX - wY ^ 2 / phiY) ≤
      kSub * (wX - wY) ^ 2 + kAdd * (wX + wY) ^ 2 := by
  rw [picone_two_channel_identity hphiX.ne' hphiY.ne']
  exact le_add_of_nonneg_left
    (picone_two_channel_square_nonneg hkSub hkAdd hphiX.le hphiY.le)

/-! ## The folded signed regular row -/

/-- Difference between the same-sign and reflected regular kernels after the
odd positive-half fold. -/
def fourCellOddFoldedRegularDifferenceKernel (x y : ℝ) : ℝ :=
  yoshidaRegularKernel (fourCellOperatorHalfWidth * |x - y|) -
    yoshidaRegularKernel (fourCellOperatorHalfWidth * (x + y))

private def regularAntitoneAux0 (t : ℝ) : ℝ :=
  t ^ 2 * (Real.exp (3 * t / 2) + 3 * Real.exp (-t / 2)) -
    (Real.exp (2 * t) - 2 + Real.exp (-2 * t))

private def regularAntitoneAux1 (t : ℝ) : ℝ :=
  (-3 * t ^ 2 / 2 + 6 * t) * Real.exp (-t / 2) +
    (3 * t ^ 2 / 2 + 2 * t) * Real.exp (3 * t / 2) -
    2 * Real.exp (2 * t) + 2 * Real.exp (-2 * t)

private def regularAntitoneAux2 (t : ℝ) : ℝ :=
  (3 * t ^ 2 / 4 - 6 * t + 6) * Real.exp (-t / 2) +
    (9 * t ^ 2 / 4 + 6 * t + 2) * Real.exp (3 * t / 2) -
    4 * Real.exp (2 * t) - 4 * Real.exp (-2 * t)

private def regularAntitoneAux3 (t : ℝ) : ℝ :=
  (-3 * t ^ 2 / 8 + 9 * t / 2 - 9) * Real.exp (-t / 2) +
    (27 * t ^ 2 / 8 + 27 * t / 2 + 9) * Real.exp (3 * t / 2) -
    8 * Real.exp (2 * t) + 8 * Real.exp (-2 * t)

private def regularAntitoneAux4 (t : ℝ) : ℝ :=
  (3 * t ^ 2 / 16 - 3 * t + 9) * Real.exp (-t / 2) +
    (81 * t ^ 2 / 16 + 27 * t + 27) * Real.exp (3 * t / 2) -
    16 * Real.exp (2 * t) - 16 * Real.exp (-2 * t)

private theorem hasDerivAt_exp_const_mul (c t : ℝ) :
    HasDerivAt (fun x : ℝ ↦ Real.exp (c * x))
      (c * Real.exp (c * t)) t := by
  convert ((hasDerivAt_id t).const_mul c).exp using 1
  all_goals (try simp only [id_eq])
  all_goals ring_nf

private theorem hasDerivAt_quadratic (a b c t : ℝ) :
    HasDerivAt (fun x : ℝ ↦ a * x ^ 2 + b * x + c) (2 * a * t + b) t := by
  convert ((((hasDerivAt_id t).pow 2).const_mul a).add
    ((hasDerivAt_id t).const_mul b)).add_const c using 1
  all_goals (try simp only [id_eq])
  all_goals ring_nf

private theorem regularAntitoneAux0_hasDerivAt (t : ℝ) :
    HasDerivAt regularAntitoneAux0 (regularAntitoneAux1 t) t := by
  unfold regularAntitoneAux0 regularAntitoneAux1
  have hT := hasDerivAt_quadratic 1 0 0 t
  have hS := (hasDerivAt_exp_const_mul (3 / 2) t).add
    ((hasDerivAt_exp_const_mul (-1 / 2) t).const_mul 3)
  have hR := ((hasDerivAt_exp_const_mul 2 t).sub_const 2).add
    (hasDerivAt_exp_const_mul (-2) t)
  convert (hT.mul hS).sub hR using 1
  all_goals (try funext z)
  all_goals (try simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply])
  all_goals ring_nf

private theorem regularAntitoneAux1_hasDerivAt (t : ℝ) :
    HasDerivAt regularAntitoneAux1 (regularAntitoneAux2 t) t := by
  unfold regularAntitoneAux1 regularAntitoneAux2
  have hA := hasDerivAt_quadratic (-3 / 2) 6 0 t
  have hB := hasDerivAt_quadratic (3 / 2) 2 0 t
  have hEneg := hasDerivAt_exp_const_mul (-1 / 2) t
  have hEpos := hasDerivAt_exp_const_mul (3 / 2) t
  have hE2 := (hasDerivAt_exp_const_mul 2 t).const_mul 2
  have hEneg2 := (hasDerivAt_exp_const_mul (-2) t).const_mul 2
  convert (((hA.mul hEneg).add (hB.mul hEpos)).sub hE2).add hEneg2 using 1
  all_goals (try funext z)
  all_goals (try simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply])
  all_goals ring_nf

private theorem regularAntitoneAux2_hasDerivAt (t : ℝ) :
    HasDerivAt regularAntitoneAux2 (regularAntitoneAux3 t) t := by
  unfold regularAntitoneAux2 regularAntitoneAux3
  have hA := hasDerivAt_quadratic (3 / 4) (-6) 6 t
  have hB := hasDerivAt_quadratic (9 / 4) 6 2 t
  have hEneg := hasDerivAt_exp_const_mul (-1 / 2) t
  have hEpos := hasDerivAt_exp_const_mul (3 / 2) t
  have hE2 := (hasDerivAt_exp_const_mul 2 t).const_mul 4
  have hEneg2 := (hasDerivAt_exp_const_mul (-2) t).const_mul 4
  convert (((hA.mul hEneg).add (hB.mul hEpos)).sub hE2).sub hEneg2 using 1
  all_goals (try funext z)
  all_goals (try simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply])
  all_goals ring_nf

private theorem regularAntitoneAux3_hasDerivAt (t : ℝ) :
    HasDerivAt regularAntitoneAux3 (regularAntitoneAux4 t) t := by
  unfold regularAntitoneAux3 regularAntitoneAux4
  have hA := hasDerivAt_quadratic (-3 / 8) (9 / 2) (-9) t
  have hB := hasDerivAt_quadratic (27 / 8) (27 / 2) 9 t
  have hEneg := hasDerivAt_exp_const_mul (-1 / 2) t
  have hEpos := hasDerivAt_exp_const_mul (3 / 2) t
  have hE2 := (hasDerivAt_exp_const_mul 2 t).const_mul 8
  have hEneg2 := (hasDerivAt_exp_const_mul (-2) t).const_mul 8
  convert (((hA.mul hEneg).add (hB.mul hEpos)).sub hE2).add hEneg2 using 1
  all_goals (try funext z)
  all_goals (try simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply])
  all_goals ring_nf

private theorem exp_half_le_eight_fifths
    {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 5 * Real.log 2 / 4) :
    Real.exp (t / 2) ≤ 8 / 5 := by
  let u : ℝ := t / 2
  have hu0 : 0 ≤ u := by
    dsimp only [u]
    linarith
  have hu7 : u ≤ 7 / 16 := by
    dsimp only [u]
    have hlog := strict_log_two_bounds.2
    linarith
  have hu1 : u ≤ 1 := hu7.trans (by norm_num)
  have hexp := Real.exp_bound' hu0 hu1 (n := 4) (by norm_num)
  norm_num [Finset.sum_range_succ] at hexp
  calc
    Real.exp (t / 2) = Real.exp u := by rfl
    _ ≤ 1 + u + u ^ 2 / 2 + u ^ 3 / 6 + 5 * u ^ 4 / 96 := by
      linarith
    _ ≤ 1 + (7 / 16 : ℝ) + (7 / 16 : ℝ) ^ 2 / 2 +
        (7 / 16 : ℝ) ^ 3 / 6 + 5 * (7 / 16 : ℝ) ^ 4 / 96 := by
      gcongr
    _ ≤ 8 / 5 := by norm_num

private theorem regularAntitoneBasePolynomial_nonneg
    {r : ℝ} (hr1 : 1 ≤ r) (hr8 : r ≤ 8 / 5) :
    0 ≤ 9 * r ^ 3 + 27 * r ^ 7 - 16 * r ^ 8 - 16 := by
  let u : ℝ := (5 / 3 : ℝ) * (r - 1)
  have hu0 : 0 ≤ u := by
    dsimp only [u]
    nlinarith
  have hu1 : u ≤ 1 := by
    dsimp only [u]
    linarith
  have hone : 0 ≤ 1 - u := sub_nonneg.mpr hu1
  rw [show 9 * r ^ 3 + 27 * r ^ 7 - 16 * r ^ 8 - 16 =
      4 * (1 - u) ^ 8 +
        (424 / 5 : ℝ) * u * (1 - u) ^ 7 +
        (13354 / 25 : ℝ) * u ^ 2 * (1 - u) ^ 6 +
        (207586 / 125 : ℝ) * u ^ 3 * (1 - u) ^ 5 +
        (73909 / 25 : ℝ) * u ^ 4 * (1 - u) ^ 4 +
        (9788053 / 3125 : ℝ) * u ^ 5 * (1 - u) ^ 3 +
        (29836984 / 15625 : ℝ) * u ^ 6 * (1 - u) ^ 2 +
        (45713728 / 78125 : ℝ) * u ^ 7 * (1 - u) +
        (22830064 / 390625 : ℝ) * u ^ 8 by
    dsimp only [u]
    ring]
  positivity

private theorem regularAntitoneAux4_nonneg
    {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 5 * Real.log 2 / 4) :
    0 ≤ regularAntitoneAux4 t := by
  let r : ℝ := Real.exp (t / 2)
  have hrpos : 0 < r := by
    dsimp only [r]
    positivity
  have hr1 : 1 ≤ r := by
    dsimp only [r]
    exact Real.one_le_exp (by linarith)
  have hr8 : r ≤ 8 / 5 := by
    dsimp only [r]
    exact exp_half_le_eight_fifths ht0 ht
  have hbase := regularAntitoneBasePolynomial_nonneg hr1 hr8
  have hr4 : 1 ≤ r ^ 4 := one_le_pow₀ hr1
  have hlinear : 0 ≤ -3 * r ^ 3 + 27 * r ^ 7 := by
    rw [show -3 * r ^ 3 + 27 * r ^ 7 =
      3 * r ^ 3 * (9 * r ^ 4 - 1) by ring]
    have hr3 : 0 ≤ r ^ 3 := pow_nonneg hrpos.le 3
    have hsecond : 0 ≤ 9 * r ^ 4 - 1 := by linarith
    positivity
  have hquadratic : 0 ≤ 3 * r ^ 3 / 16 + 81 * r ^ 7 / 16 := by
    positivity
  have hrpow (n : ℕ) : r ^ n = Real.exp (n * (t / 2)) := by
    dsimp only [r]
    rw [← Real.exp_nat_mul]
  have hnegHalf : Real.exp (-t / 2) * r ^ 4 = r ^ 3 := by
    rw [hrpow 4, hrpow 3, ← Real.exp_add]
    congr 1
    ring
  have hthreeHalf : Real.exp (3 * t / 2) * r ^ 4 = r ^ 7 := by
    rw [hrpow 4, hrpow 7, ← Real.exp_add]
    congr 1
    ring
  have htwo : Real.exp (2 * t) * r ^ 4 = r ^ 8 := by
    rw [hrpow 4, hrpow 8, ← Real.exp_add]
    congr 1
    ring
  have hnegTwo : Real.exp (-2 * t) * r ^ 4 = 1 := by
    rw [hrpow 4, ← Real.exp_add]
    convert Real.exp_zero using 1
    ring
  have hfactor : regularAntitoneAux4 t * r ^ 4 =
      (9 * r ^ 3 + 27 * r ^ 7 - 16 * r ^ 8 - 16) +
        t * (-3 * r ^ 3 + 27 * r ^ 7) +
        t ^ 2 * (3 * r ^ 3 / 16 + 81 * r ^ 7 / 16) := by
    calc
      regularAntitoneAux4 t * r ^ 4 =
          (3 * t ^ 2 / 16 - 3 * t + 9) *
              (Real.exp (-t / 2) * r ^ 4) +
            (81 * t ^ 2 / 16 + 27 * t + 27) *
              (Real.exp (3 * t / 2) * r ^ 4) -
            16 * (Real.exp (2 * t) * r ^ 4) -
            16 * (Real.exp (-2 * t) * r ^ 4) := by
        unfold regularAntitoneAux4
        ring
      _ = _ := by rw [hnegHalf, hthreeHalf, htwo, hnegTwo]; ring
  have hfactorNonneg : 0 ≤ regularAntitoneAux4 t * r ^ 4 := by
    rw [hfactor]
    positivity
  nlinarith [pow_pos hrpos 4]

private theorem value_nonneg_of_hasDerivAt_nonneg
    {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf0 : f 0 = 0) {t : ℝ} (ht : 0 ≤ t)
    (hf' : ∀ x, 0 ≤ x → x ≤ t → 0 ≤ f' x) : 0 ≤ f t := by
  have hcont : Continuous f := continuous_iff_continuousAt.mpr fun x ↦
    (hf x).continuousAt
  have hmono : MonotoneOn f (Set.Icc 0 t) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 t) hcont.continuousOn ?_ ?_
    · intro x _
      exact (hf x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(hf x).deriv]
      exact hf' x (interior_subset hx).1 (interior_subset hx).2
  have h := hmono ⟨le_rfl, ht⟩ ⟨ht, le_rfl⟩ ht
  simpa [hf0] using h

private theorem regularAntitoneAux0_nonneg
    {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 5 * Real.log 2 / 4) :
    0 ≤ regularAntitoneAux0 t := by
  have h3 : 0 ≤ regularAntitoneAux3 t := by
    apply value_nonneg_of_hasDerivAt_nonneg regularAntitoneAux3_hasDerivAt
    · norm_num [regularAntitoneAux3]
    · exact ht0
    · intro x hx0 hxt
      exact regularAntitoneAux4_nonneg hx0 (hxt.trans ht)
  have h2 : 0 ≤ regularAntitoneAux2 t := by
    apply value_nonneg_of_hasDerivAt_nonneg regularAntitoneAux2_hasDerivAt
    · norm_num [regularAntitoneAux2]
    · exact ht0
    · intro x hx0 hxt
      apply value_nonneg_of_hasDerivAt_nonneg regularAntitoneAux3_hasDerivAt
      · norm_num [regularAntitoneAux3]
      · exact hx0
      · intro y hy0 hyx
        exact regularAntitoneAux4_nonneg hy0 ((hyx.trans hxt).trans ht)
  have h1 : 0 ≤ regularAntitoneAux1 t := by
    apply value_nonneg_of_hasDerivAt_nonneg regularAntitoneAux1_hasDerivAt
    · norm_num [regularAntitoneAux1]
    · exact ht0
    · intro x hx0 hxt
      apply value_nonneg_of_hasDerivAt_nonneg regularAntitoneAux2_hasDerivAt
      · norm_num [regularAntitoneAux2]
      · exact hx0
      · intro y hy0 hyx
        apply value_nonneg_of_hasDerivAt_nonneg regularAntitoneAux3_hasDerivAt
        · norm_num [regularAntitoneAux3]
        · exact hy0
        · intro z hz0 hzy
          exact regularAntitoneAux4_nonneg hz0
            (((hzy.trans hyx).trans hxt).trans ht)
  apply value_nonneg_of_hasDerivAt_nonneg regularAntitoneAux0_hasDerivAt
  · norm_num [regularAntitoneAux0]
  · exact ht0
  · intro x hx0 hxt
    apply value_nonneg_of_hasDerivAt_nonneg regularAntitoneAux1_hasDerivAt
    · norm_num [regularAntitoneAux1]
    · exact hx0
    · intro y hy0 hyx
      apply value_nonneg_of_hasDerivAt_nonneg regularAntitoneAux2_hasDerivAt
      · norm_num [regularAntitoneAux2]
      · exact hy0
      · intro z hz0 hzy
        apply value_nonneg_of_hasDerivAt_nonneg regularAntitoneAux3_hasDerivAt
        · norm_num [regularAntitoneAux3]
        · exact hz0
        · intro q hq0 hqz
          exact regularAntitoneAux4_nonneg hq0
            ((((hqz.trans hzy).trans hyx).trans hxt).trans ht)

private theorem four_mul_sinh_sq_eq_exp_rows (t : ℝ) :
    4 * Real.sinh t ^ 2 =
      Real.exp (2 * t) - 2 + Real.exp (-2 * t) := by
  have hsq : Real.exp t ^ 2 = Real.exp (2 * t) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hsqneg : Real.exp (-t) ^ 2 = Real.exp (-2 * t) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hprod : Real.exp t * Real.exp (-t) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    ring
  rw [Real.sinh_eq]
  calc
    4 * ((Real.exp t - Real.exp (-t)) / 2) ^ 2 =
        Real.exp t ^ 2 - 2 * (Real.exp t * Real.exp (-t)) +
          Real.exp (-t) ^ 2 := by ring
    _ = _ := by rw [hsq, hsqneg, hprod]; ring

/-- The exact derivative numerator inequality for the Yoshida regular
kernel on the full four-cell folded range. -/
theorem four_mul_sinh_sq_le_regular_derivative_row
    {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 5 * Real.log 2 / 4) :
    4 * Real.sinh t ^ 2 ≤
      t ^ 2 * (Real.exp (3 * t / 2) + 3 * Real.exp (-t / 2)) := by
  have haux := regularAntitoneAux0_nonneg ht0 ht
  unfold regularAntitoneAux0 at haux
  rw [← four_mul_sinh_sq_eq_exp_rows] at haux
  linarith

private def yoshidaRegularKernelAwayZero (t : ℝ) : ℝ :=
  Real.exp (t / 2) / (2 * Real.sinh t) - 1 / (2 * t)

private def yoshidaRegularKernelAwayZeroDeriv (t : ℝ) : ℝ :=
  Real.exp (t / 2) * (Real.sinh t - 2 * Real.cosh t) /
      (4 * Real.sinh t ^ 2) +
    1 / (2 * t ^ 2)

private theorem yoshidaRegularKernelAwayZero_hasDerivAt
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt yoshidaRegularKernelAwayZero
      (yoshidaRegularKernelAwayZeroDeriv t) t := by
  have hnum : HasDerivAt (fun x : ℝ ↦ Real.exp (x / 2))
      (Real.exp (t / 2) / 2) t := by
    convert ((hasDerivAt_id t).div_const 2).exp using 1
    all_goals simp only [id_eq]
    all_goals ring_nf
  have hden : HasDerivAt (fun x : ℝ ↦ 2 * Real.sinh x)
      (2 * Real.cosh t) t := by
    simpa only using (Real.hasDerivAt_sinh t).const_mul 2
  have hdenne : 2 * Real.sinh t ≠ 0 := by
    have hsinh : 0 < Real.sinh t := Real.sinh_pos_iff.mpr ht
    positivity
  have hlin : HasDerivAt (fun x : ℝ ↦ 2 * x) 2 t := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id t).const_mul 2
  have hlinne : 2 * t ≠ 0 := by positivity
  have hone : HasDerivAt (fun _ : ℝ ↦ (1 : ℝ)) 0 t :=
    hasDerivAt_const t 1
  unfold yoshidaRegularKernelAwayZero yoshidaRegularKernelAwayZeroDeriv
  convert (hnum.div hden hdenne).sub (hone.div hlin hlinne) using 1
  all_goals field_simp [ht.ne', (Real.sinh_pos_iff.mpr ht).ne']
  all_goals ring_nf

private theorem exp_half_mul_two_cosh_sub_sinh (t : ℝ) :
    Real.exp (t / 2) * (2 * Real.cosh t - Real.sinh t) =
      (Real.exp (3 * t / 2) + 3 * Real.exp (-t / 2)) / 2 := by
  rw [Real.cosh_eq, Real.sinh_eq]
  have hpos : Real.exp (t / 2) * Real.exp t =
      Real.exp (3 * t / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hneg : Real.exp (t / 2) * Real.exp (-t) =
      Real.exp (-t / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [show Real.exp (t / 2) *
      (2 * ((Real.exp t + Real.exp (-t)) / 2) -
        (Real.exp t - Real.exp (-t)) / 2) =
      (Real.exp (t / 2) * Real.exp t +
        3 * (Real.exp (t / 2) * Real.exp (-t))) / 2 by ring,
    hpos, hneg]

private theorem yoshidaRegularKernelAwayZeroDeriv_nonpos
    {t : ℝ} (ht0 : 0 < t) (ht : t ≤ 5 * Real.log 2 / 4) :
    yoshidaRegularKernelAwayZeroDeriv t ≤ 0 := by
  have hsinh : 0 < Real.sinh t := Real.sinh_pos_iff.mpr ht0
  have hrow := four_mul_sinh_sq_le_regular_derivative_row ht0.le ht
  have hrewrite := exp_half_mul_two_cosh_sub_sinh t
  have hmain : 4 * Real.sinh t ^ 2 ≤
      2 * t ^ 2 * Real.exp (t / 2) *
        (2 * Real.cosh t - Real.sinh t) := by
    calc
      4 * Real.sinh t ^ 2 ≤
          t ^ 2 * (Real.exp (3 * t / 2) +
            3 * Real.exp (-t / 2)) := hrow
      _ = 2 * t ^ 2 *
          (Real.exp (t / 2) *
            (2 * Real.cosh t - Real.sinh t)) := by rw [hrewrite]; ring
      _ = _ := by ring
  unfold yoshidaRegularKernelAwayZeroDeriv
  have htne : t ≠ 0 := ht0.ne'
  have hsinhne : Real.sinh t ≠ 0 := hsinh.ne'
  field_simp [htne, hsinhne]
  nlinarith [sq_pos_of_pos ht0, sq_pos_of_pos hsinh]

/-- The Yoshida regular kernel is antitone throughout every argument reached
by the odd four-cell positive-half fold. -/
theorem yoshidaRegularKernel_antitone_fourCellRange
    {s t : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t)
    (ht : t ≤ 5 * Real.log 2 / 4) :
    yoshidaRegularKernel t ≤ yoshidaRegularKernel s := by
  by_cases hs : s = 0
  · subst s
    have ht0 : 0 ≤ t := by linarith
    simpa [yoshidaRegularKernel] using
      (yoshidaRegularKernel_le_quarter ht0)
  · have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
    have htpos : 0 < t := hspos.trans_le hst
    have hanti : AntitoneOn yoshidaRegularKernelAwayZero (Set.Icc s t) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc s t)
      · intro x hx
        exact (yoshidaRegularKernelAwayZero_hasDerivAt
          (hspos.trans_le hx.1)).continuousAt.continuousWithinAt
      · intro x hx
        have hx' := interior_subset hx
        exact (yoshidaRegularKernelAwayZero_hasDerivAt
          (by linarith [hspos, hx'.1])).differentiableAt.differentiableWithinAt
      · intro x hx
        have hx' := interior_subset hx
        have hxpos : 0 < x := by linarith [hspos, hx'.1]
        rw [(yoshidaRegularKernelAwayZero_hasDerivAt hxpos).deriv]
        exact yoshidaRegularKernelAwayZeroDeriv_nonpos hxpos
          (hx'.2.trans ht)
    have hpair := hanti ⟨le_rfl, hst⟩ ⟨hst, le_rfl⟩ hst
    simpa [yoshidaRegularKernel, yoshidaRegularKernelAwayZero,
      if_neg hs, if_neg htpos.ne'] using hpair

/-- The signed regular convolution does not break Stieltjes positivity: on
`[0,1]^2`, the same-sign kernel is at least its reflected counterpart. -/
theorem fourCellOddFoldedRegularDifferenceKernel_nonneg
    {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    0 ≤ fourCellOddFoldedRegularDifferenceKernel x y := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hwidth : 0 ≤ fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  have hdist0 : 0 ≤ fourCellOperatorHalfWidth * |x - y| :=
    mul_nonneg hwidth (abs_nonneg _)
  have hsum0 : 0 ≤ fourCellOperatorHalfWidth * (x + y) := by
    exact mul_nonneg hwidth (add_nonneg hx0 hy0)
  have habs : |x - y| ≤ x + y := by
    rw [abs_le]
    constructor <;> linarith
  have hargs : fourCellOperatorHalfWidth * |x - y| ≤
      fourCellOperatorHalfWidth * (x + y) :=
    mul_le_mul_of_nonneg_left habs hwidth
  have hsumle : x + y ≤ 2 := by linarith
  have hargUpper : fourCellOperatorHalfWidth * (x + y) ≤
      5 * Real.log 2 / 4 := by
    unfold fourCellOperatorHalfWidth
    nlinarith
  have hanti := yoshidaRegularKernel_antitone_fourCellRange
    hdist0 hargs hargUpper
  unfold fourCellOddFoldedRegularDifferenceKernel
  linarith

/-- The negative folded regular correlation is exactly a positive Dirichlet
square minus its two row masses.  Thus the regular term itself introduces no
positive off-diagonal coefficient whenever the folded difference kernel is
nonnegative. -/
theorem foldedRegularCorrelation_eq_dirichlet_sub_rows
    (x y wX wY : ℝ) :
    -2 * fourCellOperatorHalfWidth *
          fourCellOddFoldedRegularDifferenceKernel x y * wX * wY =
      fourCellOperatorHalfWidth *
          fourCellOddFoldedRegularDifferenceKernel x y * (wX - wY) ^ 2 -
        fourCellOperatorHalfWidth *
          fourCellOddFoldedRegularDifferenceKernel x y * wX ^ 2 -
        fourCellOperatorHalfWidth *
          fourCellOddFoldedRegularDifferenceKernel x y * wY ^ 2 := by
  ring

/-- Conditional sign statement separated from the still-needed analytic
monotonicity theorem for `yoshidaRegularKernel`. -/
theorem foldedRegularDirichletSquare_nonneg
    {x y wX wY : ℝ}
    (hkernel : 0 ≤ fourCellOddFoldedRegularDifferenceKernel x y) :
    0 ≤ fourCellOperatorHalfWidth *
      fourCellOddFoldedRegularDifferenceKernel x y * (wX - wY) ^ 2 := by
  have hwidth : 0 ≤ fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  positivity

/-! ## Fatal sign obstruction for a scalar Stieltjes fold -/

/-- One ordered-pair contribution of the adverse strip-odd raw energy.  The
four values are those at `x`, its strip reflection, `y`, and its strip
reflection. -/
def adverseStripOddPairQuadratic
    (distance wX wXRef wY wYRef : ℝ) : ℝ :=
  -(1 / 2 : ℝ) *
    (((wX - wXRef) / 2 - (wY - wYRef) / 2) ^ 2 / distance)

/-- Full algebraic expansion of one adverse strip-odd pair.  In particular,
the `wX*wXRef` and `wY*wYRef` coefficients have the opposite sign from a
scalar Stieltjes kernel. -/
theorem adverseStripOddPairQuadratic_expansion
    {distance wX wXRef wY wYRef : ℝ} (hdistance : distance ≠ 0) :
    adverseStripOddPairQuadratic distance wX wXRef wY wYRef =
      -(wX ^ 2 + wXRef ^ 2 + wY ^ 2 + wYRef ^ 2) /
          (8 * distance) +
        (wX * wXRef + wX * wY + wXRef * wYRef + wY * wYRef) /
          (4 * distance) -
        (wX * wYRef + wXRef * wY) / (4 * distance) := by
  unfold adverseStripOddPairQuadratic
  field_simp [hdistance]
  ring

/-- The polarized coefficient coupling a strip value to its own reflection
is exactly positive `1/(8 distance)`. -/
theorem adverseStripOddPair_reflection_polarization_eq
    {distance : ℝ} (hdistance : distance ≠ 0) :
    (adverseStripOddPairQuadratic distance 1 1 0 0 -
        adverseStripOddPairQuadratic distance 1 0 0 0 -
        adverseStripOddPairQuadratic distance 0 1 0 0) / 2 =
      1 / (8 * distance) := by
  unfold adverseStripOddPairQuadratic
  field_simp [hdistance]
  ring

/-- Hence every positive strip distance gives a strictly positive reflected
off-diagonal polarization.  A successful ground-state proof must retain the
strip parity block (or its already-proved positive reserve) rather than model
the complete core as one scalar Stieltjes kernel. -/
theorem adverseStripOddPair_reflection_polarization_pos
    {distance : ℝ} (hdistance : 0 < distance) :
    0 <
      (adverseStripOddPairQuadratic distance 1 1 0 0 -
          adverseStripOddPairQuadratic distance 1 0 0 0 -
          adverseStripOddPairQuadratic distance 0 1 0 0) / 2 := by
  rw [adverseStripOddPair_reflection_polarization_eq hdistance.ne']
  positivity

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddCoreGroundStatePiconeStructural

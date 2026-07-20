import ArithmeticHodge.Analysis.YoshidaFactorTwoPhasePerturbationOneSubCosEnclosures
import ArithmeticHodge.Analysis.YoshidaSineCheckpointedHead

set_option autoImplicit false
set_option maxRecDepth 100000

open Filter MeasureTheory Real Set intervalIntegral
open scoped BigOperators Topology

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhasePerturbationOneSubCosLowEnclosures

noncomputable section

open ArithmeticHodge.Analysis
open CorrectedTrapezoidRemainder
open DigammaTrapezoid
open RatInterval
open YoshidaDiagonalDigammaHighBound
open YoshidaDiagonalUniformIdentity
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoPhaseConcreteEvenPerturbationAdaptation
open YoshidaFactorTwoPhaseConcretePerturbationMoments
open YoshidaFactorTwoPhasePerturbationConstantEnclosures
open YoshidaFactorTwoPhasePerturbationMomentSeries
open YoshidaFactorTwoPhasePerturbationOneSubCosEnclosures
open YoshidaFactorTwoPhasePerturbationOneSubCosSeries
open YoshidaFactorTwoPrimeTrigEnclosures
open YoshidaPositiveLogEnclosures
open YoshidaSineCheckpointedHead
open YoshidaSineMomentEnclosures

/-!
# Complementary low enclosures for the factor-two `1 - cos` moment

The high-frequency enclosure loses precision below mode `18` only through
the vertical-digamma remainder.  Here the same slow rational series is
evaluated directly.  Its tail at `K = 2048` is enclosed by a shifted
first-corrected Euler--Maclaurin formula; the fifth-order geometric
corrections are reused unchanged from the high module.
-/

/-! ## A shifted Euler--Maclaurin formula for the slow rational tail -/

/-- Continuous version of the unweighted rational summand. -/
def factorTwoOneSubCosSlowProfile (y t : ℝ) : ℝ :=
  let u := t + 1 / 4
  y ^ 2 / (u * (u ^ 2 + y ^ 2))

def factorTwoOneSubCosSlowProfileDeriv (y t : ℝ) : ℝ :=
  let u := t + 1 / 4
  (-1) / u ^ 2 - diagonalHighProfileDeriv y t

def factorTwoOneSubCosSlowProfileSecondDeriv (y t : ℝ) : ℝ :=
  let u := t + 1 / 4
  2 / u ^ 3 - diagonalHighProfileSecondDeriv y t

def factorTwoOneSubCosSlowProfileThirdDeriv (y t : ℝ) : ℝ :=
  let u := t + 1 / 4
  (-6) / u ^ 4 - diagonalHighProfileThirdDeriv y t

/-- The positive tail integral from `t` to infinity. -/
def factorTwoOneSubCosSlowTailLog (y t : ℝ) : ℝ :=
  let u := t + 1 / 4
  Real.log (1 + y ^ 2 / u ^ 2) / 2

theorem factorTwoOneSubCosMainTerm_eq_slowProfile (n k : ℕ) :
    factorTwoOneSubCosMainTerm n k =
      factorTwoOneSubCosSlowProfile (factorTwoMomentY n) k := by
  unfold factorTwoOneSubCosMainTerm factorTwoOneSubCosSlowProfile
    factorTwoCauchyX
  rfl

private theorem hasDerivAt_factorTwoOneSubCosSlowProfile
    {y t : ℝ} (hu : t + 1 / 4 ≠ 0) (hy : y ≠ 0) :
    HasDerivAt (factorTwoOneSubCosSlowProfile y)
      (factorTwoOneSubCosSlowProfileDeriv y t) t := by
  have hrecip : HasDerivAt (fun s : ℝ ↦ 1 / (s + 1 / 4))
      (-1 / (t + 1 / 4) ^ 2) t := by
    convert (hasDerivAt_const t (1 : ℝ)).div
      ((hasDerivAt_id t).add_const (1 / 4)) hu using 1
    simp only [id_eq]
    field_simp [hu]
    ring
  have hbase : HasDerivAt (diagonalHighProfile y)
      (diagonalHighProfileDeriv y t) t := by
    have hinner : HasDerivAt (fun s : ℝ ↦ s + 1 / 4) 1 t := by
      simpa using (hasDerivAt_id t).add_const (1 / 4)
    have h := (hasDerivAt_reciprocalRealPart
      (y := y) (u := t + 1 / 4) hy).comp t hinner
    change HasDerivAt
      (reciprocalRealPart y ∘ fun s : ℝ ↦ s + 1 / 4)
      (reciprocalRealPartDeriv y (t + 1 / 4)) t
    simpa only [mul_one] using h
  have hdiff := hrecip.sub hbase
  have heq : (fun s : ℝ ↦ 1 / (s + 1 / 4)) - diagonalHighProfile y =
      factorTwoOneSubCosSlowProfile y := by
    funext s
    unfold factorTwoOneSubCosSlowProfile diagonalHighProfile reciprocalRealPart
    dsimp only
    change 1 / (s + 1 / 4) -
        (s + 1 / 4) / ((s + 1 / 4) ^ 2 + y ^ 2) =
      y ^ 2 / ((s + 1 / 4) * ((s + 1 / 4) ^ 2 + y ^ 2))
    by_cases hs : s + 1 / 4 = 0
    · rw [show s = -1 / 4 by linarith]
      norm_num
    · have hden : (s + 1 / 4) ^ 2 + y ^ 2 ≠ 0 := by
        positivity
      field_simp [hs, hden]
      ring
  rw [heq] at hdiff
  simpa [factorTwoOneSubCosSlowProfileDeriv] using hdiff

private theorem hasDerivAt_factorTwoOneSubCosSlowProfileDeriv
    {y t : ℝ} (hu : t + 1 / 4 ≠ 0) (hy : y ≠ 0) :
    HasDerivAt (factorTwoOneSubCosSlowProfileDeriv y)
      (factorTwoOneSubCosSlowProfileSecondDeriv y t) t := by
  have hinner : HasDerivAt (fun s : ℝ ↦ s + 1 / 4) 1 t := by
    simpa using (hasDerivAt_id t).add_const (1 / 4)
  have hpow := hinner.pow 2
  have hinv := (hasDerivAt_const t (-1 : ℝ)).div hpow
    (pow_ne_zero 2 hu)
  have hone : HasDerivAt (fun s : ℝ ↦ -1 / (s + 1 / 4) ^ 2)
      (2 / (t + 1 / 4) ^ 3) t := by
    have hu4 : t * 4 + 1 ≠ 0 := by
      intro h
      apply hu
      linarith
    convert hinv using 1
    simp only [Pi.pow_apply]
    field_simp [hu, hu4]
    ring
  have htwo :=
    hasDerivAt_diagonalHighProfileDeriv (y := y) (t := t) hy
  change HasDerivAt
    ((fun s : ℝ ↦ (-1) / (s + 1 / 4) ^ 2) -
      diagonalHighProfileDeriv y)
    (2 / (t + 1 / 4) ^ 3 - diagonalHighProfileSecondDeriv y t) t
  exact hone.sub htwo

private theorem hasDerivAt_factorTwoOneSubCosSlowProfileSecondDeriv
    {y t : ℝ} (hu : t + 1 / 4 ≠ 0) (hy : y ≠ 0) :
    HasDerivAt (factorTwoOneSubCosSlowProfileSecondDeriv y)
      (factorTwoOneSubCosSlowProfileThirdDeriv y t) t := by
  have hinner : HasDerivAt (fun s : ℝ ↦ s + 1 / 4) 1 t := by
    simpa using (hasDerivAt_id t).add_const (1 / 4)
  have hpow := hinner.pow 3
  have hinv := (hasDerivAt_const t (2 : ℝ)).div hpow
    (pow_ne_zero 3 hu)
  have hone : HasDerivAt (fun s : ℝ ↦ 2 / (s + 1 / 4) ^ 3)
      (-6 / (t + 1 / 4) ^ 4) t := by
    have hu4 : t * 4 + 1 ≠ 0 := by
      intro h
      apply hu
      linarith
    convert hinv using 1
    simp only [Pi.pow_apply]
    field_simp [hu, hu4]
    ring
  have hthree :=
    hasDerivAt_diagonalHighProfileSecondDeriv (y := y) (t := t) hy
  change HasDerivAt
    ((fun s : ℝ ↦ 2 / (s + 1 / 4) ^ 3) -
      diagonalHighProfileSecondDeriv y)
    ((-6) / (t + 1 / 4) ^ 4 - diagonalHighProfileThirdDeriv y t) t
  exact hone.sub hthree

private theorem hasDerivAt_factorTwoOneSubCosSlowTailLog
    {y t : ℝ} (hu : 0 < t + 1 / 4) :
    HasDerivAt (factorTwoOneSubCosSlowTailLog y)
      (-factorTwoOneSubCosSlowProfile y t) t := by
  let u : ℝ → ℝ := fun s ↦ s + 1 / 4
  have hu' : HasDerivAt u 1 t := by
    simpa [u] using (hasDerivAt_id t).add_const (1 / 4)
  have hden := hu'.pow 2
  have hfrac := (hasDerivAt_const t (y ^ 2)).div hden
    (pow_ne_zero 2 hu.ne')
  have hfrac' : HasDerivAt (fun s ↦ y ^ 2 / (u s) ^ 2)
      (-2 * y ^ 2 / (u t) ^ 3) t := by
    have hu4 : t * 4 + 1 ≠ 0 := by
      intro h
      apply hu.ne'
      linarith
    convert hfrac using 1
    simp only [Pi.pow_apply]
    dsimp only [u]
    field_simp [hu.ne', hu4]
    ring
  have hins := (hasDerivAt_const t (1 : ℝ)).add hfrac'
  have hinsPos : 0 < 1 + y ^ 2 / (u t) ^ 2 := by positivity
  have hlog := hins.log hinsPos.ne'
  have hhalf := hlog.div_const 2
  unfold factorTwoOneSubCosSlowTailLog factorTwoOneSubCosSlowProfile
  simp only [Pi.add_apply] at hhalf
  dsimp only [u] at hhalf ⊢
  convert hhalf using 1
  have hu4 : t * 4 + 1 ≠ 0 := by
    intro h
    apply hu.ne'
    linarith
  field_simp [hu.ne', hu4, hinsPos.ne']
  ring

private theorem integral_factorTwoOneSubCosSlowProfile
    {y a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫ t in a..b, factorTwoOneSubCosSlowProfile y t) =
      factorTwoOneSubCosSlowTailLog y a -
        factorTwoOneSubCosSlowTailLog y b := by
  have hderiv : ∀ t ∈ uIcc a b,
      HasDerivAt (fun s ↦ -factorTwoOneSubCosSlowTailLog y s)
        (factorTwoOneSubCosSlowProfile y t) t := by
    intro t ht
    have ht' : t ∈ Icc a b := by rwa [uIcc_of_le hab] at ht
    simpa only [Pi.neg_apply, neg_neg] using
      (hasDerivAt_factorTwoOneSubCosSlowTailLog (y := y) (t := t)
        (by linarith [ht'.1])).neg
  have hcont : ContinuousOn (factorTwoOneSubCosSlowProfile y) (Icc a b) := by
    intro t ht
    by_cases hy : y = 0
    · subst y
      have hzero : factorTwoOneSubCosSlowProfile 0 =
          (fun _ : ℝ ↦ (0 : ℝ)) := by
        funext s
        simp [factorTwoOneSubCosSlowProfile]
      rw [hzero]
      exact continuousAt_const.continuousWithinAt
    · exact (hasDerivAt_factorTwoOneSubCosSlowProfile
        (by linarith [ht.1]) hy).continuousAt.continuousWithinAt
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s ↦ -factorTwoOneSubCosSlowTailLog y s)
    hderiv (hcont.intervalIntegrable_of_Icc hab)
  convert hint using 1
  all_goals ring

private theorem factorTwoOneSubCosSlowThird_abs_le
    {y t : ℝ} (ht : 0 ≤ t) :
    |factorTwoOneSubCosSlowProfileThirdDeriv y t| ≤
      24 / (t + 1 / 4) ^ 4 := by
  let u : ℝ := t + 1 / 4
  let D : ℝ := u ^ 2 + y ^ 2
  let Q : ℝ := u ^ 4 - 6 * u ^ 2 * y ^ 2 + y ^ 4
  have hu : 0 < u := by dsimp [u]; linarith
  have hD : 0 < D := by dsimp [D]; positivity
  have hQ : |Q| ≤ 3 * D ^ 2 := by
    have hraw : |Q| ≤ u ^ 4 + 6 * u ^ 2 * y ^ 2 + y ^ 4 := by
      rw [abs_le]
      constructor <;> dsimp [Q] <;>
        nlinarith [sq_nonneg (u ^ 2), sq_nonneg (y ^ 2),
          mul_nonneg (sq_nonneg u) (sq_nonneg y)]
    have hexpand :
        3 * D ^ 2 = 3 * u ^ 4 + 6 * u ^ 2 * y ^ 2 + 3 * y ^ 4 := by
      dsimp [D]
      ring
    rw [hexpand]
    nlinarith [hraw, pow_nonneg hu.le 4, pow_nonneg (sq_nonneg y) 2]
  have hthird : |diagonalHighProfileThirdDeriv y t| ≤ 18 / u ^ 4 := by
    unfold diagonalHighProfileThirdDeriv
    dsimp only
    change |(-6 : ℝ) * Q / D ^ 4| ≤ 18 / u ^ 4
    rw [abs_div, abs_mul, abs_of_nonpos (by norm_num : (-6 : ℝ) ≤ 0),
      abs_of_pos (pow_pos hD 4)]
    norm_num only [neg_neg]
    calc
      6 * |Q| / D ^ 4 ≤ 6 * (3 * D ^ 2) / D ^ 4 := by gcongr
      _ = 18 / D ^ 2 := by field_simp [hD.ne']; ring
      _ ≤ 18 / u ^ 4 := by
        apply div_le_div_of_nonneg_left (by norm_num) (pow_pos hu 4)
        have hsq : u ^ 2 ≤ D := by dsimp [D]; nlinarith [sq_nonneg y]
        nlinarith [pow_le_pow_left₀ (sq_nonneg u) hsq 2]
  unfold factorTwoOneSubCosSlowProfileThirdDeriv
  dsimp only
  calc
    |-6 / u ^ 4 - diagonalHighProfileThirdDeriv y t| ≤
        |-6 / u ^ 4| + |diagonalHighProfileThirdDeriv y t| :=
      abs_sub _ _
    _ ≤ 6 / u ^ 4 + 18 / u ^ 4 := by
      gcongr
      rw [abs_div, abs_of_nonpos (by norm_num : (-6 : ℝ) ≤ 0),
        abs_of_pos (pow_pos hu 4)]
      norm_num
    _ = 24 / u ^ 4 := by ring

private def factorTwoOneSubCosSlowMajorant (t : ℝ) : ℝ :=
  2 / (t + 1 / 4) ^ 4

private def factorTwoOneSubCosSlowMajorantPrimitive (t : ℝ) : ℝ :=
  -2 / (3 * (t + 1 / 4) ^ 3)

private theorem hasDerivAt_factorTwoOneSubCosSlowMajorantPrimitive
    {t : ℝ} (hu : t + 1 / 4 ≠ 0) :
    HasDerivAt factorTwoOneSubCosSlowMajorantPrimitive
      (factorTwoOneSubCosSlowMajorant t) t := by
  have hinner : HasDerivAt (fun s : ℝ ↦ s + 1 / 4) 1 t := by
    simpa using (hasDerivAt_id t).add_const (1 / 4)
  have hden := (hinner.pow 3).const_mul 3
  unfold factorTwoOneSubCosSlowMajorantPrimitive
    factorTwoOneSubCosSlowMajorant
  convert (hasDerivAt_const t (-2 : ℝ)).div hden (by
    simp only [Pi.pow_apply]
    exact mul_ne_zero (by norm_num) (pow_ne_zero 3 hu)) using 1
  simp only [Pi.pow_apply]
  have hu4 : t * 4 + 1 ≠ 0 := by
    intro h
    apply hu
    linarith
  field_simp [hu, hu4]
  ring

private theorem integral_factorTwoOneSubCosSlowMajorant
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫ t in a..b, factorTwoOneSubCosSlowMajorant t) =
      factorTwoOneSubCosSlowMajorantPrimitive b -
        factorTwoOneSubCosSlowMajorantPrimitive a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t ht
    have ht' : t ∈ Icc a b := by rwa [uIcc_of_le hab] at ht
    exact hasDerivAt_factorTwoOneSubCosSlowMajorantPrimitive
      (by linarith [ht'.1])
  · have hcont : ContinuousOn factorTwoOneSubCosSlowMajorant (Icc a b) := by
      intro t ht
      have hu : t + 1 / 4 ≠ 0 := by linarith [ht.1]
      unfold factorTwoOneSubCosSlowMajorant
      exact (continuousAt_const.div
        ((continuousAt_id.add continuousAt_const).pow 4)
        (pow_ne_zero 4 hu)).continuousWithinAt
    exact hcont.intervalIntegrable_of_Icc hab

/-- Local form of the first-corrected trapezoid identity.  Unlike the generic
library statement, this only requests derivatives on the unit cell; that is
essential for the reciprocal profile, whose irrelevant pole lies outside all
production cells. -/
private theorem trapezoidal_error_one_sub_first_eq_integral_third_local
    {f f1 f2 f3 : ℝ → ℝ} {a : ℝ}
    (hf1 : ∀ t ∈ Icc a (a + 1), HasDerivAt f (f1 t) t)
    (hf2 : ∀ t ∈ Icc a (a + 1), HasDerivAt f1 (f2 t) t)
    (hf3 : ∀ t ∈ Icc a (a + 1), HasDerivAt f2 (f3 t) t)
    (hf3_int : IntervalIntegrable f3 volume a (a + 1)) :
    trapezoidal_error f 1 a (a + 1) -
          (f1 (a + 1) - f1 a) / 12 =
      -(∫ t in a..a + 1, correctedTrapezoidThirdKernel a t * f3 t) := by
  let W : ℝ → ℝ := fun t ↦ (t - a) * (a + 1 - t) / 2
  let W1 : ℝ → ℝ := fun t ↦ (2 * a + 1 - 2 * t) / 2
  let C2 : ℝ → ℝ := correctedTrapezoidThirdKernel a
  let C3 : ℝ → ℝ := fun t ↦
    -1 / 12 + (t - a) / 2 - (t - a) ^ 2 / 2
  have hW (t : ℝ) : HasDerivAt W (W1 t) t := by
    dsimp only [W, W1]
    have hx := (hasDerivAt_id t).sub_const a
    have hy := (hasDerivAt_const t (a + 1)).sub (hasDerivAt_id t)
    convert (hx.mul hy).div_const 2 using 1
    simp only [Pi.sub_apply, id_eq]
    ring
  have hW1 (t : ℝ) : HasDerivAt W1 (-1) t := by
    dsimp only [W1]
    convert ((hasDerivAt_const t (2 * a + 1)).sub
      ((hasDerivAt_id t).const_mul 2)).div_const 2 using 1
    ring
  have hC2 (t : ℝ) : HasDerivAt C2 (C3 t) t := by
    dsimp only [C2, C3]
    unfold correctedTrapezoidThirdKernel
    have hx := (hasDerivAt_id t).sub_const a
    convert (((hx.neg.div_const 12).add ((hx.pow 2).div_const 4)).sub
      ((hx.pow 3).div_const 6)) using 1
    simp only [id_eq]
    ring
  have hf_cont : ContinuousOn f (Icc a (a + 1)) :=
    fun t ht ↦ (hf1 t ht).continuousAt.continuousWithinAt
  have hf1_cont : ContinuousOn f1 (Icc a (a + 1)) :=
    fun t ht ↦ (hf2 t ht).continuousAt.continuousWithinAt
  have hf2_cont : ContinuousOn f2 (Icc a (a + 1)) :=
    fun t ht ↦ (hf3 t ht).continuousAt.continuousWithinAt
  have hf1_int : IntervalIntegrable f1 volume a (a + 1) :=
    hf1_cont.intervalIntegrable_of_Icc (by norm_num)
  have hf2_int : IntervalIntegrable f2 volume a (a + 1) :=
    hf2_cont.intervalIntegrable_of_Icc (by norm_num)
  have hW1_int : IntervalIntegrable W1 volume a (a + 1) := by
    have : Continuous W1 := by dsimp only [W1]; fun_prop
    exact this.intervalIntegrable _ _
  have hnegOne_int : IntervalIntegrable (fun _ : ℝ ↦ (-1 : ℝ))
      volume a (a + 1) := continuous_const.intervalIntegrable _ _
  have hC3_int : IntervalIntegrable C3 volume a (a + 1) := by
    have : Continuous C3 := by dsimp only [C3]; fun_prop
    exact this.intervalIntegrable _ _
  have hpartsW := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := W) (u' := W1) (v := f1) (v' := f2)
    (a := a) (b := a + 1)
    (fun t ht ↦ hW t) (fun t ht ↦ hf2 t (by
      simpa [uIcc_of_le (by norm_num : a ≤ a + 1)] using ht))
    hW1_int hf2_int
  have hpartsW1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := W1) (u' := fun _ ↦ (-1 : ℝ)) (v := f) (v' := f1)
    (a := a) (b := a + 1)
    (fun t ht ↦ hW1 t) (fun t ht ↦ hf1 t (by
      simpa [uIcc_of_le (by norm_num : a ≤ a + 1)] using ht))
    hnegOne_int hf1_int
  have hnegIntegral :
      (∫ t in a..a + 1, (-1 : ℝ) * f t) =
        -(∫ t in a..a + 1, f t) := by
    rw [intervalIntegral.integral_const_mul]
    ring
  have hWleft : W a = 0 := by simp [W]
  have hWright : W (a + 1) = 0 := by simp [W]
  have hW1left : W1 a = 1 / 2 := by dsimp [W1]; ring
  have hW1right : W1 (a + 1) = -1 / 2 := by dsimp [W1]; ring
  rw [hWleft, hWright, zero_mul, zero_mul, sub_zero] at hpartsW
  rw [hW1left, hW1right, hnegIntegral] at hpartsW1
  have hbase :
      trapezoidal_error f 1 a (a + 1) =
        ∫ t in a..a + 1, W t * f2 t := by
    rw [trapezoidal_error, trapezoidal_integral_one]
    linarith [hpartsW, hpartsW1]
  have hC3f2_int : IntervalIntegrable (fun t ↦ C3 t * f2 t)
      volume a (a + 1) :=
    hf2_int.continuousOn_mul (by dsimp only [C3]; fun_prop)
  have hconstf2_int : IntervalIntegrable (fun t ↦ (1 / 12 : ℝ) * f2 t)
      volume a (a + 1) := hf2_int.const_mul _
  have hderivIntegral :
      (∫ t in a..a + 1, f2 t) = f1 (a + 1) - f1 a := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht
      have ht' : t ∈ Icc a (a + 1) := by
        rwa [uIcc_of_le (by norm_num : a ≤ a + 1)] at ht
      exact hf2 t ht'
    · exact hf2_int
  have hdecomp :
      trapezoidal_error f 1 a (a + 1) =
        (f1 (a + 1) - f1 a) / 12 +
          ∫ t in a..a + 1, C3 t * f2 t := by
    rw [hbase]
    rw [show (fun t ↦ W t * f2 t) =
        fun t ↦ (1 / 12 : ℝ) * f2 t + C3 t * f2 t by
      funext t
      dsimp only [W, C3]
      ring]
    rw [intervalIntegral.integral_add hconstf2_int hC3f2_int,
      intervalIntegral.integral_const_mul, hderivIntegral]
    ring
  have hpartsC := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := C2) (u' := C3) (v := f2) (v' := f3)
    (a := a) (b := a + 1)
    (fun t ht ↦ hC2 t) (fun t ht ↦ hf3 t (by
      simpa [uIcc_of_le (by norm_num : a ≤ a + 1)] using ht))
    hC3_int hf3_int
  have hC2left : C2 a = 0 := by simp [C2, correctedTrapezoidThirdKernel]
  have hC2right : C2 (a + 1) = 0 := by
    simp [C2, correctedTrapezoidThirdKernel]
    ring
  rw [hC2left, hC2right, zero_mul, zero_mul, sub_zero, zero_sub] at hpartsC
  linarith [hdecomp, hpartsC]

private def factorTwoOneSubCosSlowCorrectedError
    (y : ℝ) (K k : ℕ) : ℝ :=
  trapezoidal_error (factorTwoOneSubCosSlowProfile y) 1
      (K + k) (K + k + 1) -
    (factorTwoOneSubCosSlowProfileDeriv y (K + k + 1) -
      factorTwoOneSubCosSlowProfileDeriv y (K + k)) / 12

private theorem continuousOn_factorTwoOneSubCosSlowProfileThirdDeriv
    {y a b : ℝ} (ha : 0 ≤ a) :
    ContinuousOn (factorTwoOneSubCosSlowProfileThirdDeriv y) (Icc a b) := by
  intro t ht
  have hu : t + 1 / 4 ≠ 0 := by linarith [ht.1]
  unfold factorTwoOneSubCosSlowProfileThirdDeriv
    diagonalHighProfileThirdDeriv
  dsimp only
  apply ContinuousAt.continuousWithinAt
  apply ContinuousAt.sub
  · exact continuousAt_const.div
      ((continuousAt_id.add continuousAt_const).pow 4)
      (pow_ne_zero 4 hu)
  · apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · have hden : 0 < (t + 1 / 4) ^ 2 + y ^ 2 := by
        nlinarith [sq_pos_of_ne_zero hu, sq_nonneg y]
      exact (pow_pos hden 4).ne'

private theorem factorTwoOneSubCosSlowCorrectedError_abs_le
    {y : ℝ} (hy : y ≠ 0) (K k : ℕ) :
    |factorTwoOneSubCosSlowCorrectedError y K k| ≤
      ∫ t in (K + k : ℕ)..(K + k + 1 : ℕ),
        factorTwoOneSubCosSlowMajorant t := by
  let a : ℝ := (K + k : ℕ)
  have hthirdInt : IntervalIntegrable
      (factorTwoOneSubCosSlowProfileThirdDeriv y) volume a (a + 1) := by
    exact (continuousOn_factorTwoOneSubCosSlowProfileThirdDeriv
      (y := y) (a := a) (b := a + 1) (by positivity)).intervalIntegrable_of_Icc
        (by norm_num)
  have hid := trapezoidal_error_one_sub_first_eq_integral_third_local
    (f := factorTwoOneSubCosSlowProfile y)
    (f1 := factorTwoOneSubCosSlowProfileDeriv y)
    (f2 := factorTwoOneSubCosSlowProfileSecondDeriv y)
    (f3 := factorTwoOneSubCosSlowProfileThirdDeriv y)
    (a := a)
    (fun t ht ↦ hasDerivAt_factorTwoOneSubCosSlowProfile
      (by dsimp [a] at ht; linarith [ht.1]) hy)
    (fun t ht ↦ hasDerivAt_factorTwoOneSubCosSlowProfileDeriv
      (by dsimp [a] at ht; linarith [ht.1]) hy)
    (fun t ht ↦ hasDerivAt_factorTwoOneSubCosSlowProfileSecondDeriv
      (by dsimp [a] at ht; linarith [ht.1]) hy)
    hthirdInt
  have hid' : factorTwoOneSubCosSlowCorrectedError y K k =
      -(∫ t in a..a + 1,
        correctedTrapezoidThirdKernel a t *
          factorTwoOneSubCosSlowProfileThirdDeriv y t) := by
    unfold factorTwoOneSubCosSlowCorrectedError
    dsimp only [a] at hid ⊢
    norm_num only [Nat.cast_add, Nat.cast_one] at hid ⊢
    convert hid using 1
  rw [hid', abs_neg]
  have hleftInt : IntervalIntegrable
      (fun t : ℝ ↦
        |correctedTrapezoidThirdKernel a t *
          factorTwoOneSubCosSlowProfileThirdDeriv y t|)
      volume a (a + 1) := by
    have hk : Continuous (correctedTrapezoidThirdKernel a) := by
      unfold correctedTrapezoidThirdKernel
      fun_prop
    have hthird := continuousOn_factorTwoOneSubCosSlowProfileThirdDeriv
      (y := y) (a := a) (b := a + 1) (by positivity)
    exact (hk.continuousOn.mul hthird).abs.intervalIntegrable_of_Icc
      (by norm_num)
  have hrightInt : IntervalIntegrable factorTwoOneSubCosSlowMajorant
      volume a (a + 1) := by
    have hcont : ContinuousOn factorTwoOneSubCosSlowMajorant (Icc a (a + 1)) := by
      intro t ht
      have hu : t + 1 / 4 ≠ 0 := by dsimp [a] at ht; linarith [ht.1]
      unfold factorTwoOneSubCosSlowMajorant
      exact (continuousAt_const.div
        ((continuousAt_id.add continuousAt_const).pow 4)
        (pow_ne_zero 4 hu)).continuousWithinAt
    exact hcont.intervalIntegrable_of_Icc (by norm_num)
  calc
    |∫ t in a..a + 1,
        correctedTrapezoidThirdKernel a t *
          factorTwoOneSubCosSlowProfileThirdDeriv y t| ≤
        ∫ t in a..a + 1,
          |correctedTrapezoidThirdKernel a t *
            factorTwoOneSubCosSlowProfileThirdDeriv y t| :=
      intervalIntegral.abs_integral_le_integral_abs (by norm_num)
    _ ≤ ∫ t in a..a + 1, factorTwoOneSubCosSlowMajorant t := by
      apply intervalIntegral.integral_mono_on (by norm_num) hleftInt hrightInt
      intro t ht
      rw [abs_mul]
      calc
        |correctedTrapezoidThirdKernel a t| *
            |factorTwoOneSubCosSlowProfileThirdDeriv y t| ≤
            (1 / 12 : ℝ) *
              |factorTwoOneSubCosSlowProfileThirdDeriv y t| :=
          mul_le_mul_of_nonneg_right
            (abs_correctedTrapezoidThirdKernel_le ht) (abs_nonneg _)
        _ ≤ factorTwoOneSubCosSlowMajorant t := by
          have hthird := factorTwoOneSubCosSlowThird_abs_le
            (y := y) (t := t) (by dsimp [a] at ht; linarith [ht.1])
          unfold factorTwoOneSubCosSlowMajorant
          calc
            (1 / 12 : ℝ) *
                |factorTwoOneSubCosSlowProfileThirdDeriv y t| ≤
                (1 / 12 : ℝ) * (24 / (t + 1 / 4) ^ 4) := by
              exact mul_le_mul_of_nonneg_left hthird (by norm_num)
            _ = 2 / (t + 1 / 4) ^ 4 := by ring
    _ = ∫ t in (K + k : ℕ)..(K + k + 1 : ℕ),
        factorTwoOneSubCosSlowMajorant t := by
      dsimp only [a]
      norm_num only [Nat.cast_add, Nat.cast_one]

/-- Exact uniform radius for the slow tail beginning at `K`. -/
def factorTwoOneSubCosSlowTailRadius (K : ℕ) : ℝ :=
  2 / (3 * ((K : ℝ) + 1 / 4) ^ 3)

private theorem factorTwoOneSubCosSlowCorrectedError_sum_abs_le
    {y : ℝ} (hy : y ≠ 0) (K M : ℕ) :
    |∑ k ∈ Finset.range M,
        factorTwoOneSubCosSlowCorrectedError y K k| ≤
      factorTwoOneSubCosSlowTailRadius K := by
  calc
    |∑ k ∈ Finset.range M,
        factorTwoOneSubCosSlowCorrectedError y K k| ≤
        ∑ k ∈ Finset.range M,
          |factorTwoOneSubCosSlowCorrectedError y K k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range M,
        ∫ t in (K + k : ℕ)..(K + k + 1 : ℕ),
          factorTwoOneSubCosSlowMajorant t := by
      exact Finset.sum_le_sum fun k _hk ↦
        factorTwoOneSubCosSlowCorrectedError_abs_le hy K k
    _ = ∑ k ∈ Finset.range M,
        (factorTwoOneSubCosSlowMajorantPrimitive (K + k + 1) -
          factorTwoOneSubCosSlowMajorantPrimitive (K + k)) := by
      apply Finset.sum_congr rfl
      intro k _hk
      convert integral_factorTwoOneSubCosSlowMajorant
        (a := ((K + k : ℕ) : ℝ))
        (b := ((K + k + 1 : ℕ) : ℝ)) (by positivity) (by norm_num) using 1
      all_goals norm_num only [Nat.cast_add, Nat.cast_one]
    _ = factorTwoOneSubCosSlowMajorantPrimitive (K + M) -
        factorTwoOneSubCosSlowMajorantPrimitive K := by
      convert (Finset.sum_range_sub
        (fun k : ℕ ↦ factorTwoOneSubCosSlowMajorantPrimitive (K + k)) M)
        using 1
      all_goals norm_num
      all_goals ring
    _ ≤ factorTwoOneSubCosSlowTailRadius K := by
      have hnonpos :
          factorTwoOneSubCosSlowMajorantPrimitive (K + M) ≤ 0 := by
        unfold factorTwoOneSubCosSlowMajorantPrimitive
        exact div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity)
      calc
        factorTwoOneSubCosSlowMajorantPrimitive (K + M) -
            factorTwoOneSubCosSlowMajorantPrimitive K ≤
            0 - factorTwoOneSubCosSlowMajorantPrimitive K :=
          sub_le_sub_right hnonpos _
        _ = factorTwoOneSubCosSlowTailRadius K := by
          unfold factorTwoOneSubCosSlowMajorantPrimitive
            factorTwoOneSubCosSlowTailRadius
          norm_num only [Nat.cast_add, Nat.cast_zero, zero_add]
          ring

private theorem factorTwoOneSubCosSlowProfile_nonneg
    {y t : ℝ} (ht : 0 ≤ t) :
    0 ≤ factorTwoOneSubCosSlowProfile y t := by
  unfold factorTwoOneSubCosSlowProfile
  dsimp only
  exact div_nonneg (sq_nonneg y)
    (mul_nonneg (by linarith) (add_nonneg (sq_nonneg _) (sq_nonneg y)))

private theorem factorTwoOneSubCosSlowProfile_abs_le_inv
    {y t : ℝ} (ht : 0 ≤ t) :
    |factorTwoOneSubCosSlowProfile y t| ≤ 1 / (t + 1 / 4) := by
  let u : ℝ := t + 1 / 4
  let D : ℝ := u ^ 2 + y ^ 2
  have hu : 0 < u := by dsimp [u]; linarith
  have hD : 0 < D := by dsimp [D]; positivity
  rw [abs_of_nonneg (factorTwoOneSubCosSlowProfile_nonneg ht)]
  unfold factorTwoOneSubCosSlowProfile
  dsimp only
  change y ^ 2 / (u * D) ≤ 1 / u
  rw [div_le_iff₀ (mul_pos hu hD)]
  field_simp [hu.ne']
  dsimp [D]
  nlinarith [sq_nonneg u]

private theorem diagonalHighProfileDeriv_abs_le_invSq
    {y t : ℝ} (ht : 0 ≤ t) :
    |diagonalHighProfileDeriv y t| ≤ 1 / (t + 1 / 4) ^ 2 := by
  let u : ℝ := t + 1 / 4
  let D : ℝ := u ^ 2 + y ^ 2
  have hu : 0 < u := by dsimp [u]; linarith
  have hD : 0 < D := by dsimp [D]; positivity
  have hnum : |y ^ 2 - u ^ 2| ≤ D := by
    rw [abs_le]
    dsimp [D]
    constructor <;> nlinarith [sq_nonneg y, sq_nonneg u]
  unfold diagonalHighProfileDeriv reciprocalRealPartDeriv
  change |(y ^ 2 - u ^ 2) / D ^ 2| ≤ 1 / u ^ 2
  rw [abs_div, abs_of_pos (pow_pos hD 2)]
  calc
    |y ^ 2 - u ^ 2| / D ^ 2 ≤ D / D ^ 2 := by gcongr
    _ = 1 / D := by field_simp [hD.ne']
    _ ≤ 1 / u ^ 2 := by
      apply one_div_le_one_div_of_le (sq_pos_of_pos hu)
      dsimp [D]
      nlinarith [sq_nonneg y]

private theorem factorTwoOneSubCosSlowProfileDeriv_abs_le
    {y t : ℝ} (ht : 0 ≤ t) :
    |factorTwoOneSubCosSlowProfileDeriv y t| ≤
      2 / (t + 1 / 4) ^ 2 := by
  let u : ℝ := t + 1 / 4
  have hu : 0 < u := by dsimp [u]; linarith
  unfold factorTwoOneSubCosSlowProfileDeriv
  dsimp only
  calc
    |-1 / u ^ 2 - diagonalHighProfileDeriv y t| ≤
        |-1 / u ^ 2| + |diagonalHighProfileDeriv y t| := abs_sub _ _
    _ ≤ 1 / u ^ 2 + 1 / u ^ 2 := by
      gcongr
      · rw [abs_div, abs_of_nonpos (by norm_num : (-1 : ℝ) ≤ 0),
          abs_of_pos (pow_pos hu 2)]
        norm_num
      · exact diagonalHighProfileDeriv_abs_le_invSq ht
    _ = 2 / u ^ 2 := by ring

private theorem tendsto_factorTwoOneSubCosSlowAbscissaInv
    (K : ℕ) :
    Tendsto (fun M : ℕ ↦
      (((K + M : ℕ) : ℝ) + 1 / 4)⁻¹) atTop (nhds 0) := by
  have hnat : Tendsto (fun M : ℕ ↦ ((K + M : ℕ) : ℝ))
      atTop atTop := by
    simpa only [Nat.add_comm] using
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat K)
  have htop : Tendsto (fun M : ℕ ↦
      ((K + M : ℕ) : ℝ) + 1 / 4) atTop atTop := by
    simpa using tendsto_atTop_add_const_right atTop (1 / 4 : ℝ) hnat
  exact tendsto_inv_atTop_zero.comp htop

private theorem tendsto_factorTwoOneSubCosSlowProfile
    (y : ℝ) (K : ℕ) :
    Tendsto (fun M : ℕ ↦
      factorTwoOneSubCosSlowProfile y (K + M)) atTop (nhds 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun M ↦ abs_nonneg _
  · exact Filter.Eventually.of_forall fun M ↦ by
      simpa only [Nat.cast_add] using
        factorTwoOneSubCosSlowProfile_abs_le_inv
          (y := y) (t := ((K + M : ℕ) : ℝ)) (by positivity)
  · simpa only [one_div, Nat.cast_add] using
      tendsto_factorTwoOneSubCosSlowAbscissaInv K

private theorem tendsto_factorTwoOneSubCosSlowProfileDeriv
    (y : ℝ) (K : ℕ) :
    Tendsto (fun M : ℕ ↦
      factorTwoOneSubCosSlowProfileDeriv y (K + M)) atTop (nhds 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun M ↦ abs_nonneg _
  · exact Filter.Eventually.of_forall fun M ↦ by
      simpa only [Nat.cast_add] using
        factorTwoOneSubCosSlowProfileDeriv_abs_le
          (y := y) (t := ((K + M : ℕ) : ℝ)) (by positivity)
  · have h := (tendsto_factorTwoOneSubCosSlowAbscissaInv K).pow 2
    have h' := (tendsto_const_nhds (x := (2 : ℝ))).mul h
    convert h' using 1 <;> norm_num [div_eq_mul_inv, inv_pow]

private theorem tendsto_factorTwoOneSubCosSlowTailLog
    (y : ℝ) (K : ℕ) :
    Tendsto (fun M : ℕ ↦
      factorTwoOneSubCosSlowTailLog y (K + M)) atTop (nhds 0) := by
  have hinv := tendsto_factorTwoOneSubCosSlowAbscissaInv K
  have hins : Tendsto (fun M : ℕ ↦
      1 + y ^ 2 * ((((K + M : ℕ) : ℝ) + 1 / 4)⁻¹) ^ 2)
      atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add
      (tendsto_const_nhds.mul (hinv.pow 2))
  have hlog : Tendsto (fun M : ℕ ↦ Real.log
      (1 + y ^ 2 * ((((K + M : ℕ) : ℝ) + 1 / 4)⁻¹) ^ 2))
      atTop (nhds 0) := by
    simpa using (Real.continuousAt_log
      (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hins
  have hhalf := hlog.div_const 2
  convert hhalf using 1
  · funext M
    unfold factorTwoOneSubCosSlowTailLog
    dsimp only
    norm_num only [Nat.cast_add]
    simp only [div_eq_mul_inv, inv_pow]
  · norm_num

private theorem sum_range_factorTwoOneSubCosSlowCorrectedError_eq
    {y : ℝ} (K M : ℕ) :
    (∑ k ∈ Finset.range M,
        factorTwoOneSubCosSlowCorrectedError y K k) =
      (∑ k ∈ Finset.range M,
          factorTwoOneSubCosSlowProfile y (K + k)) -
        factorTwoOneSubCosSlowProfile y K / 2 +
        factorTwoOneSubCosSlowProfile y (K + M) / 2 -
        (factorTwoOneSubCosSlowTailLog y K -
          factorTwoOneSubCosSlowTailLog y (K + M)) -
        (factorTwoOneSubCosSlowProfileDeriv y (K + M) -
          factorTwoOneSubCosSlowProfileDeriv y K) / 12 := by
  have hcell (k : ℕ) :
      trapezoidal_error (factorTwoOneSubCosSlowProfile y) 1
          (K + k) (K + k + 1) =
        (factorTwoOneSubCosSlowProfile y (K + k) +
            factorTwoOneSubCosSlowProfile y (K + k + 1)) / 2 -
          (factorTwoOneSubCosSlowTailLog y (K + k) -
            factorTwoOneSubCosSlowTailLog y (K + k + 1)) := by
    have hint := integral_factorTwoOneSubCosSlowProfile
      (y := y) (a := ((K + k : ℕ) : ℝ))
      (b := ((K + k + 1 : ℕ) : ℝ)) (by positivity) (by norm_num)
    rw [trapezoidal_error, trapezoidal_integral_one]
    norm_num only [Nat.cast_add, Nat.cast_one] at hint ⊢
    rw [hint]
    ring
  have hshift :
      (∑ k ∈ Finset.range M,
        factorTwoOneSubCosSlowProfile y (K + k + 1)) =
        (∑ k ∈ Finset.range M,
          factorTwoOneSubCosSlowProfile y (K + k)) -
          factorTwoOneSubCosSlowProfile y K +
          factorTwoOneSubCosSlowProfile y (K + M) := by
    have htel :
        (∑ k ∈ Finset.range M,
            factorTwoOneSubCosSlowProfile y (K + k + 1)) -
          (∑ k ∈ Finset.range M,
            factorTwoOneSubCosSlowProfile y (K + k)) =
          factorTwoOneSubCosSlowProfile y (K + M) -
            factorTwoOneSubCosSlowProfile y K := by
      have hraw := Finset.sum_range_sub
        (fun k : ℕ ↦ factorTwoOneSubCosSlowProfile y (K + k)) M
      rw [Finset.sum_sub_distrib] at hraw
      convert hraw using 1
      all_goals norm_num only [Nat.cast_add, Nat.cast_one,
        Nat.cast_zero, add_zero]
      all_goals ring
    linarith
  have havg :
      (∑ k ∈ Finset.range M,
        (factorTwoOneSubCosSlowProfile y (K + k) +
          factorTwoOneSubCosSlowProfile y (K + k + 1)) / 2) =
        (∑ k ∈ Finset.range M,
          factorTwoOneSubCosSlowProfile y (K + k)) -
          factorTwoOneSubCosSlowProfile y K / 2 +
          factorTwoOneSubCosSlowProfile y (K + M) / 2 := by
    rw [← Finset.sum_div, Finset.sum_add_distrib, hshift]
    ring
  have htelLog :
      (∑ k ∈ Finset.range M,
        (factorTwoOneSubCosSlowTailLog y (K + k) -
          factorTwoOneSubCosSlowTailLog y (K + k + 1))) =
        factorTwoOneSubCosSlowTailLog y K -
          factorTwoOneSubCosSlowTailLog y (K + M) := by
    convert (Finset.sum_range_sub'
      (fun k : ℕ ↦ factorTwoOneSubCosSlowTailLog y (K + k)) M) using 1
    all_goals norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero]
    all_goals ring
  have htrap :
      (∑ k ∈ Finset.range M,
        trapezoidal_error (factorTwoOneSubCosSlowProfile y) 1
          (K + k) (K + k + 1)) =
        (∑ k ∈ Finset.range M,
          factorTwoOneSubCosSlowProfile y (K + k)) -
          factorTwoOneSubCosSlowProfile y K / 2 +
          factorTwoOneSubCosSlowProfile y (K + M) / 2 -
          (factorTwoOneSubCosSlowTailLog y K -
            factorTwoOneSubCosSlowTailLog y (K + M)) := by
    calc
      _ = ∑ k ∈ Finset.range M,
          ((factorTwoOneSubCosSlowProfile y (K + k) +
              factorTwoOneSubCosSlowProfile y (K + k + 1)) / 2 -
            (factorTwoOneSubCosSlowTailLog y (K + k) -
              factorTwoOneSubCosSlowTailLog y (K + k + 1))) := by
        apply Finset.sum_congr rfl
        intro k _hk
        exact hcell k
      _ = _ := by rw [Finset.sum_sub_distrib, havg, htelLog]
  have htelDeriv :
      (∑ k ∈ Finset.range M,
        (factorTwoOneSubCosSlowProfileDeriv y (K + k + 1) -
          factorTwoOneSubCosSlowProfileDeriv y (K + k))) =
        factorTwoOneSubCosSlowProfileDeriv y (K + M) -
          factorTwoOneSubCosSlowProfileDeriv y K := by
    convert (Finset.sum_range_sub
      (fun k : ℕ ↦ factorTwoOneSubCosSlowProfileDeriv y (K + k)) M) using 1
    all_goals norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero]
    all_goals ring
  unfold factorTwoOneSubCosSlowCorrectedError
  rw [Finset.sum_sub_distrib, htrap, ← Finset.sum_div, htelDeriv]

private theorem factorTwoMomentY_pos_of_ne_zero
    {n : ℕ} (hn : n ≠ 0) : 0 < factorTwoMomentY n := by
  unfold factorTwoMomentY factorTwoNaturalFrequency
  exact div_pos (mul_pos Real.pi_pos (by exact_mod_cast Nat.pos_of_ne_zero hn))
    factorTwoMomentLength_pos

private theorem summable_factorTwoOneSubCosSlowProfile_tail
    (n K : ℕ) :
    Summable (fun j : ℕ ↦
      factorTwoOneSubCosSlowProfile (factorTwoMomentY n) (K + j)) := by
  have hshift := (summable_nat_add_iff K).2
    (summable_factorTwoOneSubCosMainTerm n)
  exact hshift.congr fun j ↦ by
    rw [factorTwoOneSubCosMainTerm_eq_slowProfile]
    norm_num only [Nat.cast_add]
    rw [add_comm]

/-- First-corrected Euler--Maclaurin main term for the slow tail. -/
def factorTwoOneSubCosSlowTailMain (n K : ℕ) : ℝ :=
  factorTwoOneSubCosSlowTailLog (factorTwoMomentY n) K +
    factorTwoOneSubCosSlowProfile (factorTwoMomentY n) K / 2 -
    factorTwoOneSubCosSlowProfileDeriv (factorTwoMomentY n) K / 12

private theorem tendsto_sum_factorTwoOneSubCosSlowCorrectedError
    (n K : ℕ) :
    Tendsto (fun M : ℕ ↦
      ∑ k ∈ Finset.range M,
        factorTwoOneSubCosSlowCorrectedError (factorTwoMomentY n) K k)
      atTop
      (nhds ((∑' j : ℕ,
          factorTwoOneSubCosSlowProfile (factorTwoMomentY n) (K + j)) -
        factorTwoOneSubCosSlowTailMain n K)) := by
  let y := factorTwoMomentY n
  have hsum := (summable_factorTwoOneSubCosSlowProfile_tail n K).hasSum.tendsto_sum_nat
  have hf := tendsto_factorTwoOneSubCosSlowProfile y K
  have hf1 := tendsto_factorTwoOneSubCosSlowProfileDeriv y K
  have hlog := tendsto_factorTwoOneSubCosSlowTailLog y K
  have hfStart : Tendsto (fun _ : ℕ ↦
      factorTwoOneSubCosSlowProfile y K) atTop
      (nhds (factorTwoOneSubCosSlowProfile y K)) := tendsto_const_nhds
  have hf1Start : Tendsto (fun _ : ℕ ↦
      factorTwoOneSubCosSlowProfileDeriv y K) atTop
      (nhds (factorTwoOneSubCosSlowProfileDeriv y K)) := tendsto_const_nhds
  have hlogStart : Tendsto (fun _ : ℕ ↦
      factorTwoOneSubCosSlowTailLog y K) atTop
      (nhds (factorTwoOneSubCosSlowTailLog y K)) := tendsto_const_nhds
  have hlim := ((((hsum.sub (hfStart.div_const 2)).add (hf.div_const 2)).sub
      (hlogStart.sub hlog)).sub ((hf1.sub hf1Start).div_const 12))
  convert hlim using 1
  · funext M
    rw [sum_range_factorTwoOneSubCosSlowCorrectedError_eq K M]
  · unfold factorTwoOneSubCosSlowTailMain
    dsimp only [y]
    ring

/-- The slow rational tail differs from its shifted Euler--Maclaurin main
term by the explicit rational radius. -/
theorem factorTwoOneSubCosSlowTail_sub_main_abs_le
    {n : ℕ} (hn : n ≠ 0) (K : ℕ) :
    |(∑' j : ℕ, factorTwoOneSubCosMainTerm n (K + j)) -
        factorTwoOneSubCosSlowTailMain n K| ≤
      factorTwoOneSubCosSlowTailRadius K := by
  have hlim := tendsto_sum_factorTwoOneSubCosSlowCorrectedError n K
  have hbound := le_of_tendsto' hlim.abs fun M ↦
    factorTwoOneSubCosSlowCorrectedError_sum_abs_le
      (factorTwoMomentY_pos_of_ne_zero hn).ne' K M
  convert hbound using 1
  apply congrArg fun x : ℝ ↦ |x - factorTwoOneSubCosSlowTailMain n K|
  apply tsum_congr
  intro j
  rw [factorTwoOneSubCosMainTerm_eq_slowProfile]
  norm_num only [Nat.cast_add]

/-! ## Exact rational enclosure of the shifted slow tail -/

def factorTwoOneSubCosLowCutoff : ℕ := 2048

private def factorTwoOneSubCosLowUQ (K : ℕ) : ℚ := K + 1 / 4

private def factorTwoOneSubCosLowYSqInterval (n : ℕ) : RatInterval :=
  nonnegSquare (factorTwoOneSubCosFineYInterval n)

private theorem factorTwoOneSubCosLowYInterval_lower_nonneg (n : ℕ) :
    0 ≤ (factorTwoOneSubCosFineYInterval n).lower := by
  unfold factorTwoOneSubCosFineYInterval piFineInterval
    factorTwoPrimeLogTwoInterval
  positivity

private theorem factorTwoOneSubCosLowYSqInterval_contains (n : ℕ) :
    (factorTwoOneSubCosLowYSqInterval n).Contains
      (factorTwoMomentY n ^ 2) :=
  contains_nonnegSquare (factorTwoOneSubCosLowYInterval_lower_nonneg n)
    (factorTwoOneSubCosFineYInterval_contains n)

private def factorTwoOneSubCosLowLogTInterval (n : ℕ) : RatInterval :=
  factorTwoOneSubCosLowYSqInterval n /
    pure (factorTwoOneSubCosLowUQ factorTwoOneSubCosLowCutoff ^ 2)

private def factorTwoOneSubCosLowLogInputInterval (n : ℕ) : RatInterval :=
  factorTwoOneSubCosLowLogTInterval n /
    (pure 2 + factorTwoOneSubCosLowLogTInterval n)

private theorem factorTwoOneSubCosLowLogInputInterval_bounds :
    ∀ n : FactorTwoCanonicalEvenIndex,
      1 ≤ n.1 → n.1 ≤ 17 →
      0 ≤ (factorTwoOneSubCosLowLogInputInterval n.1).lower ∧
      (factorTwoOneSubCosLowLogInputInterval n.1).upper < 1 ∧
      0 < (pure 2 + factorTwoOneSubCosLowLogTInterval n.1).lower := by
  set_option maxRecDepth 1000000 in
  set_option maxHeartbeats 0 in
    decide +kernel

private theorem factorTwoOneSubCosLowLogTInterval_contains (n : ℕ) :
    (factorTwoOneSubCosLowLogTInterval n).Contains
      (factorTwoMomentY n ^ 2 /
        (factorTwoOneSubCosLowUQ factorTwoOneSubCosLowCutoff : ℝ) ^ 2) := by
  have huSq :
      (pure (factorTwoOneSubCosLowUQ factorTwoOneSubCosLowCutoff ^ 2)).Contains
        ((factorTwoOneSubCosLowUQ factorTwoOneSubCosLowCutoff : ℝ) ^ 2) := by
    convert contains_pure
      (factorTwoOneSubCosLowUQ factorTwoOneSubCosLowCutoff ^ 2) using 1
    norm_num
  exact contains_div_of_pos (by
      change 0 < factorTwoOneSubCosLowUQ factorTwoOneSubCosLowCutoff ^ 2
      unfold factorTwoOneSubCosLowUQ factorTwoOneSubCosLowCutoff
      positivity)
    (factorTwoOneSubCosLowYSqInterval_contains n)
    huSq

private theorem factorTwoOneSubCosLowLogInputInterval_contains
    (n : FactorTwoCanonicalEvenIndex) (hn1 : 1 ≤ n.1) (hn17 : n.1 ≤ 17) :
    (factorTwoOneSubCosLowLogInputInterval n.1).Contains
      ((factorTwoMomentY n.1 ^ 2 /
          (factorTwoOneSubCosLowUQ factorTwoOneSubCosLowCutoff : ℝ) ^ 2) /
        (2 + factorTwoMomentY n.1 ^ 2 /
          (factorTwoOneSubCosLowUQ factorTwoOneSubCosLowCutoff : ℝ) ^ 2)) := by
  have ht := factorTwoOneSubCosLowLogTInterval_contains n.1
  have hbounds := factorTwoOneSubCosLowLogInputInterval_bounds n hn1 hn17
  exact contains_div_of_pos hbounds.2.2
    ht (contains_add (contains_pure 2) ht)

private def factorTwoOneSubCosLowTailLogInterval (n : ℕ) : RatInterval :=
  positiveLogRatioInterval (factorTwoOneSubCosLowLogInputInterval n) 12 /
    pure 2

private theorem factorTwoOneSubCosLowTailLogInterval_contains
    (n : FactorTwoCanonicalEvenIndex) (hn1 : 1 ≤ n.1) (hn17 : n.1 ≤ 17) :
    (factorTwoOneSubCosLowTailLogInterval n.1).Contains
      (factorTwoOneSubCosSlowTailLog (factorTwoMomentY n.1)
        factorTwoOneSubCosLowCutoff) := by
  let t : ℝ := factorTwoMomentY n.1 ^ 2 /
    (factorTwoOneSubCosLowUQ factorTwoOneSubCosLowCutoff : ℝ) ^ 2
  let x : ℝ := t / (2 + t)
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have htden : 0 < 2 + t := by linarith
  have hxI : (factorTwoOneSubCosLowLogInputInterval n.1).Contains x := by
    simpa only [x, t] using
      factorTwoOneSubCosLowLogInputInterval_contains n hn1 hn17
  have hbounds := factorTwoOneSubCosLowLogInputInterval_bounds n hn1 hn17
  have hlog := positiveLogRatioInterval_contains
    hbounds.1 hbounds.2.1 hxI 12
  have hhalf := contains_div_of_pos (by norm_num [RatInterval.pure])
    hlog (contains_pure 2)
  have hratio : (1 + x) / (1 - x) = 1 + t := by
    dsimp only [x]
    field_simp [htden.ne']
    ring
  unfold factorTwoOneSubCosLowTailLogInterval
    factorTwoOneSubCosSlowTailLog
  dsimp only
  convert hhalf using 1
  rw [hratio]
  dsimp only [t, factorTwoOneSubCosLowUQ]
  norm_num only [Nat.cast_add, Rat.cast_add, Rat.cast_natCast,
    Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]

private def factorTwoOneSubCosLowDenomInterval (n K : ℕ) : RatInterval :=
  pure (factorTwoOneSubCosLowUQ K ^ 2) +
    factorTwoOneSubCosLowYSqInterval n

private theorem factorTwoOneSubCosLowDenomInterval_contains (n K : ℕ) :
    (factorTwoOneSubCosLowDenomInterval n K).Contains
      (((K : ℝ) + 1 / 4) ^ 2 + factorTwoMomentY n ^ 2) := by
  exact contains_add (by
      convert contains_pure (factorTwoOneSubCosLowUQ K ^ 2) using 1
      unfold factorTwoOneSubCosLowUQ
      norm_num)
    (factorTwoOneSubCosLowYSqInterval_contains n)

private theorem factorTwoOneSubCosLowDenomInterval_lower_pos (n K : ℕ) :
    0 < (factorTwoOneSubCosLowDenomInterval n K).lower := by
  unfold factorTwoOneSubCosLowDenomInterval factorTwoOneSubCosLowYSqInterval
    RatInterval.instAdd RatInterval.add RatInterval.pure nonnegSquare
  change 0 < factorTwoOneSubCosLowUQ K ^ 2 +
    (factorTwoOneSubCosFineYInterval n).lower ^ 2
  have hu : 0 < factorTwoOneSubCosLowUQ K := by
    unfold factorTwoOneSubCosLowUQ
    positivity
  nlinarith [sq_pos_of_pos hu,
    sq_nonneg (factorTwoOneSubCosFineYInterval n).lower]

private theorem factorTwoOneSubCosLow_interval_mul_lower_pos
    {I J : RatInterval} (hI : 0 < I.lower) (hJ : 0 < J.lower)
    (hIv : I.Valid) (hJv : J.Valid) :
    0 < (I * J).lower := by
  have hIu : 0 < I.upper := hI.trans_le hIv
  have hJu : 0 < J.upper := hJ.trans_le hJv
  change 0 < min (min (I.lower * J.lower) (I.lower * J.upper))
    (min (I.upper * J.lower) (I.upper * J.upper))
  simp only [lt_min_iff]
  exact ⟨⟨mul_pos hI hJ, mul_pos hI hJu⟩,
    ⟨mul_pos hIu hJ, mul_pos hIu hJu⟩⟩

private def factorTwoOneSubCosLowProfileDerivInterval
    (n K : ℕ) : RatInterval :=
  let uSq := pure (factorTwoOneSubCosLowUQ K ^ 2)
  let D := factorTwoOneSubCosLowDenomInterval n K
  Neg.neg (pure 1 / uSq) -
    ((factorTwoOneSubCosLowYSqInterval n - uSq) / (D * D))

private theorem factorTwoOneSubCosLowProfileDerivInterval_contains
    (n K : ℕ) :
    (factorTwoOneSubCosLowProfileDerivInterval n K).Contains
      (factorTwoOneSubCosSlowProfileDeriv (factorTwoMomentY n) K) := by
  let uSq := pure (factorTwoOneSubCosLowUQ K ^ 2)
  let D := factorTwoOneSubCosLowDenomInterval n K
  have huSq : uSq.Contains ((((K : ℝ) + 1 / 4) ^ 2)) := by
    convert contains_pure (factorTwoOneSubCosLowUQ K ^ 2) using 1
    unfold factorTwoOneSubCosLowUQ
    norm_num
  have hD := factorTwoOneSubCosLowDenomInterval_contains n K
  have hD2 := contains_mul hD hD
  have hfrac := contains_div_of_pos (by
      exact factorTwoOneSubCosLow_interval_mul_lower_pos
        (factorTwoOneSubCosLowDenomInterval_lower_pos n K)
        (factorTwoOneSubCosLowDenomInterval_lower_pos n K)
        (valid_of_contains hD) (valid_of_contains hD))
    (contains_sub (factorTwoOneSubCosLowYSqInterval_contains n) huSq) hD2
  have hinv := contains_div_of_pos (by
      change 0 < factorTwoOneSubCosLowUQ K ^ 2
      unfold factorTwoOneSubCosLowUQ
      positivity)
    (contains_pure 1) huSq
  have h := contains_sub (contains_neg hinv) hfrac
  unfold factorTwoOneSubCosLowProfileDerivInterval
    factorTwoOneSubCosSlowProfileDeriv diagonalHighProfileDeriv
    reciprocalRealPartDeriv
  dsimp only [uSq, D]
  convert h using 1
  norm_num only [Nat.cast_add, Nat.cast_one]
  ring

private def factorTwoOneSubCosLowTailMainInterval (n : ℕ) : RatInterval :=
  factorTwoOneSubCosLowTailLogInterval n +
    factorTwoOneSubCosMainInterval n factorTwoOneSubCosLowCutoff / pure 2 -
    factorTwoOneSubCosLowProfileDerivInterval n
      factorTwoOneSubCosLowCutoff / pure 12

private theorem factorTwoOneSubCosLowTailMainInterval_contains
    (n : FactorTwoCanonicalEvenIndex) (hn1 : 1 ≤ n.1) (hn17 : n.1 ≤ 17) :
    (factorTwoOneSubCosLowTailMainInterval n.1).Contains
      (factorTwoOneSubCosSlowTailMain n.1
        factorTwoOneSubCosLowCutoff) := by
  have hlog := factorTwoOneSubCosLowTailLogInterval_contains n hn1 hn17
  have hmain := factorTwoOneSubCosMainInterval_contains n.1
    factorTwoOneSubCosLowCutoff
  rw [factorTwoOneSubCosMainTerm_eq_slowProfile] at hmain
  have hderiv := factorTwoOneSubCosLowProfileDerivInterval_contains n.1
    factorTwoOneSubCosLowCutoff
  have hhalf := contains_div_of_pos (by norm_num [RatInterval.pure])
    hmain (contains_pure 2)
  have htwelve := contains_div_of_pos (by norm_num [RatInterval.pure])
    hderiv (contains_pure 12)
  unfold factorTwoOneSubCosLowTailMainInterval
    factorTwoOneSubCosSlowTailMain
  exact contains_sub (contains_add hlog hhalf) htwelve

private def factorTwoOneSubCosLowTailRadiusQ : ℚ :=
  2 / (3 * factorTwoOneSubCosLowUQ factorTwoOneSubCosLowCutoff ^ 3)

private def factorTwoOneSubCosLowTailInterval (n : ℕ) : RatInterval :=
  ⟨(factorTwoOneSubCosLowTailMainInterval n).lower -
      factorTwoOneSubCosLowTailRadiusQ,
    (factorTwoOneSubCosLowTailMainInterval n).upper +
      factorTwoOneSubCosLowTailRadiusQ⟩

private theorem factorTwoOneSubCosLowTailInterval_contains
    (n : FactorTwoCanonicalEvenIndex) (hn1 : 1 ≤ n.1) (hn17 : n.1 ≤ 17) :
    (factorTwoOneSubCosLowTailInterval n.1).Contains
      (∑' j : ℕ, factorTwoOneSubCosMainTerm n.1
        (factorTwoOneSubCosLowCutoff + j)) := by
  have hmain := factorTwoOneSubCosLowTailMainInterval_contains n hn1 hn17
  have herr := factorTwoOneSubCosSlowTail_sub_main_abs_le
    (n := n.1) (by omega) factorTwoOneSubCosLowCutoff
  rw [abs_le] at herr
  unfold factorTwoOneSubCosLowTailInterval Contains
  norm_num only [Rat.cast_sub, Rat.cast_add]
  have hradius : ((factorTwoOneSubCosLowTailRadiusQ : ℚ) : ℝ) =
      factorTwoOneSubCosSlowTailRadius factorTwoOneSubCosLowCutoff := by
    unfold factorTwoOneSubCosLowTailRadiusQ
      factorTwoOneSubCosSlowTailRadius factorTwoOneSubCosLowUQ
    norm_num [factorTwoOneSubCosLowCutoff]
  rw [hradius]
  exact ⟨by linarith [hmain.1, herr.1], by linarith [hmain.2, herr.2]⟩

/-! ## Checkpointed finite head -/

private noncomputable def factorTwoOneSubCosLowHeadValueAux
    (n : ℕ) : ℕ → ℕ → ℝ
  | 0, _ => 0
  | fuel + 1, k => factorTwoOneSubCosMainTerm n k +
      factorTwoOneSubCosLowHeadValueAux n fuel (k + 1)

private def factorTwoOneSubCosLowHeadIntervalAux
    (n : ℕ) : ℕ → ℕ → RatInterval → RatInterval
  | 0, _, acc => acc
  | fuel + 1, k, acc =>
      factorTwoOneSubCosLowHeadIntervalAux n fuel (k + 1)
        (acc + factorTwoOneSubCosMainInterval n k)

private theorem factorTwoOneSubCosLowHeadIntervalAux_contains
    (n fuel k : ℕ) (acc : RatInterval) (x : ℝ) (hx : acc.Contains x) :
    (factorTwoOneSubCosLowHeadIntervalAux n fuel k acc).Contains
      (x + factorTwoOneSubCosLowHeadValueAux n fuel k) := by
  induction fuel generalizing k acc x with
  | zero => simpa [factorTwoOneSubCosLowHeadIntervalAux,
      factorTwoOneSubCosLowHeadValueAux] using hx
  | succ fuel ih =>
      rw [factorTwoOneSubCosLowHeadIntervalAux,
        factorTwoOneSubCosLowHeadValueAux]
      have hacc := contains_add hx (factorTwoOneSubCosMainInterval_contains n k)
      have hrec := ih (k + 1) (acc + factorTwoOneSubCosMainInterval n k)
        (x + factorTwoOneSubCosMainTerm n k) hacc
      convert hrec using 1
      ring

private theorem factorTwoOneSubCosLowHeadValueAux_eq_sum
    (n fuel k : ℕ) :
    factorTwoOneSubCosLowHeadValueAux n fuel k =
      ∑ j ∈ Finset.range fuel, factorTwoOneSubCosMainTerm n (k + j) := by
  induction fuel generalizing k with
  | zero => simp [factorTwoOneSubCosLowHeadValueAux]
  | succ fuel ih =>
      rw [factorTwoOneSubCosLowHeadValueAux, Finset.sum_range_succ']
      rw [ih]
      have hshift :
          (∑ j ∈ Finset.range fuel,
            factorTwoOneSubCosMainTerm n ((k + 1) + j)) =
          ∑ j ∈ Finset.range fuel,
            factorTwoOneSubCosMainTerm n (k + (j + 1)) := by
        apply Finset.sum_congr rfl
        intro j _
        congr 1
        omega
      rw [hshift]
      simp only [Nat.add_zero]
      ring

private def factorTwoOneSubCosLowChunkInterval (n i : ℕ) : RatInterval :=
  factorTwoOneSubCosLowHeadIntervalAux n 256 (256 * i) (pure 0)

private theorem factorTwoOneSubCosLowChunkInterval_contains (n i : ℕ) :
    (factorTwoOneSubCosLowChunkInterval n i).Contains
      (∑ j ∈ Finset.range 256,
        factorTwoOneSubCosMainTerm n (256 * i + j)) := by
  have h := factorTwoOneSubCosLowHeadIntervalAux_contains n 256 (256 * i)
    (pure 0) (0 : ℝ) (by norm_num [Contains, RatInterval.pure])
  rw [factorTwoOneSubCosLowHeadValueAux_eq_sum] at h
  simpa only [factorTwoOneSubCosLowChunkInterval, zero_add] using h

private def factorTwoOneSubCosLowRoundingScale : ℚ :=
  100000000000000000000

private def factorTwoOneSubCosLowRoundedChunk (n i : ℕ) : RatInterval :=
  YoshidaSineCheckpointedHead.outwardRoundedInterval
    factorTwoOneSubCosLowRoundingScale
    (factorTwoOneSubCosLowChunkInterval n i)

private theorem factorTwoOneSubCosLowRoundedChunk_contains (n i : ℕ) :
    (factorTwoOneSubCosLowRoundedChunk n i).Contains
      (∑ j ∈ Finset.range 256,
        factorTwoOneSubCosMainTerm n (256 * i + j)) := by
  exact contains_of_subinterval
    (outwardRoundedInterval_subinterval
      (by norm_num [factorTwoOneSubCosLowRoundingScale]) _)
    (factorTwoOneSubCosLowChunkInterval_contains n i)

private def factorTwoOneSubCosLowCoarseHead (n : ℕ) : ℕ → RatInterval
  | 0 => pure 0
  | blocks + 1 => factorTwoOneSubCosLowCoarseHead n blocks +
      factorTwoOneSubCosLowRoundedChunk n blocks

private theorem factorTwoOneSubCosLowCoarseHead_contains (n blocks : ℕ) :
    (factorTwoOneSubCosLowCoarseHead n blocks).Contains
      (∑ k ∈ Finset.range (256 * blocks),
        factorTwoOneSubCosMainTerm n k) := by
  induction blocks with
  | zero => norm_num [factorTwoOneSubCosLowCoarseHead, Contains,
      RatInterval.pure]
  | succ blocks ih =>
      rw [factorTwoOneSubCosLowCoarseHead]
      rw [show 256 * (blocks + 1) = 256 * blocks + 256 by omega]
      rw [Finset.sum_range_add]
      exact contains_add ih
        (factorTwoOneSubCosLowRoundedChunk_contains n blocks)

/-- Direct enclosure of the complete unweighted slow series. -/
def factorTwoOneSubCosLowSlowSeriesInterval (n : ℕ) : RatInterval :=
  factorTwoOneSubCosLowCoarseHead n 8 +
    factorTwoOneSubCosLowTailInterval n

theorem factorTwoOneSubCosLowSlowSeriesInterval_contains
    (n : FactorTwoCanonicalEvenIndex) (hn1 : 1 ≤ n.1) (hn17 : n.1 ≤ 17) :
    (factorTwoOneSubCosLowSlowSeriesInterval n.1).Contains
      (∑' k : ℕ, factorTwoOneSubCosMainTerm n.1 k) := by
  have hsplit := (summable_factorTwoOneSubCosMainTerm n.1).sum_add_tsum_nat_add
    factorTwoOneSubCosLowCutoff
  rw [← hsplit]
  unfold factorTwoOneSubCosLowSlowSeriesInterval
  have hhead := factorTwoOneSubCosLowCoarseHead_contains n.1 8
  have htail := factorTwoOneSubCosLowTailInterval_contains n hn1 hn17
  norm_num [factorTwoOneSubCosLowCutoff] at hhead ⊢
  exact contains_add hhead (by
    simpa [Nat.add_comm] using htail)

/-! ## Composed low-band target -/

theorem factorTwoAntisymmetricOneSubCosMoment_eq_slowSeriesCorrections
    (n : FactorTwoCanonicalEvenIndex) (hn : n.1 ≠ 0) :
    factorTwoAntisymmetricOneSubCosMoment n.1 =
      -factorTwoHeadDefect * factorTwoOneSubCosMainTerm n.1 0 -
        (((∑' k : ℕ, factorTwoOneSubCosMainTerm n.1 k) -
            factorTwoOneSubCosMainTerm n.1 0) -
          2 * ((∑' k : ℕ,
              factorTwoOneSubCosDyadicCorrection n.1 k) -
            factorTwoOneSubCosDyadicCorrection n.1 0) +
          ((∑' k : ℕ,
              factorTwoOneSubCosSecondDyadicCorrection n.1 k) -
            factorTwoOneSubCosSecondDyadicCorrection n.1 0)) +
      2 * (Real.log 3 / Real.sqrt 3) *
        (1 - Real.cos
          (2 * factorTwoMomentY n.1 * factorTwoPrimeShift)) := by
  rw [factorTwoAntisymmetricOneSubCosMoment_eq_digammaCorrections n hn]
  rw [← factorTwoOneSubCosMain_tsum_eq_digammaDifference]
  have hM := summable_factorTwoOneSubCosMainTerm n.1
  have hshift :
      (∑' m : ℕ, factorTwoOneSubCosMainTerm n.1 (m + 1)) =
        (∑' k : ℕ, factorTwoOneSubCosMainTerm n.1 k) -
          factorTwoOneSubCosMainTerm n.1 0 := by
    simpa only [Finset.sum_range_one] using
      ((hasSum_nat_add_iff' 1).2 hM.hasSum).tsum_eq
  rw [hshift]

/-- Direct low-mode target.  The slow series uses eight rounded 256-term
checkpoints and the two dyadic corrections retain cutoffs `20` and `10`. -/
def factorTwoAntisymmetricOneSubCosLowInterval
    (n : FactorTwoCanonicalEvenIndex) : RatInterval :=
  -(factorTwoHeadDefectInterval *
      factorTwoOneSubCosMainInterval n.1 0) -
    (((factorTwoOneSubCosLowSlowSeriesInterval n.1 -
          factorTwoOneSubCosMainInterval n.1 0) -
        pure 2 *
          (factorTwoOneSubCosDyadicCorrectionFullInterval n.1 20 -
            factorTwoOneSubCosDyadicCorrectionInterval n.1 0)) +
      (factorTwoOneSubCosSecondDyadicCorrectionFullInterval n.1 10 -
        factorTwoOneSubCosSecondDyadicCorrectionInterval n.1 0)) +
    pure 2 * factorTwoPrimeBetaInterval *
      (pure 1 - factorTwoPrimeCosInterval n)

theorem factorTwoAntisymmetricOneSubCosLowInterval_contains
    (n : FactorTwoCanonicalEvenIndex) (hn1 : 1 ≤ n.1) (hn17 : n.1 ≤ 17) :
    (factorTwoAntisymmetricOneSubCosLowInterval n).Contains
      (factorTwoAntisymmetricOneSubCosMoment n.1) := by
  rw [factorTwoAntisymmetricOneSubCosMoment_eq_slowSeriesCorrections n
    (by omega)]
  have hmain0 := factorTwoOneSubCosMainInterval_contains n.1 0
  have hhead := contains_neg
    (contains_mul factorTwoHeadDefectInterval_contains hmain0)
  have hhead' :
      (-(factorTwoHeadDefectInterval *
        factorTwoOneSubCosMainInterval n.1 0)).Contains
        (-factorTwoHeadDefect * factorTwoOneSubCosMainTerm n.1 0) := by
    convert hhead using 1
    ring
  have hslow := contains_sub
    (factorTwoOneSubCosLowSlowSeriesInterval_contains n hn1 hn17) hmain0
  have hfirst := contains_sub
    (factorTwoOneSubCosDyadicCorrectionFullInterval_contains n.1 20)
    (factorTwoOneSubCosDyadicCorrectionInterval_contains n.1 0)
  have hsecond := contains_sub
    (factorTwoOneSubCosSecondDyadicCorrectionFullInterval_contains n.1 10)
    (factorTwoOneSubCosSecondDyadicCorrectionInterval_contains n.1 0)
  have hcore := contains_add
    (contains_sub hslow (contains_mul (contains_pure 2) hfirst)) hsecond
  have hprime := contains_mul
    (contains_mul (contains_pure 2) factorTwoPrimeBetaInterval_contains)
    (contains_sub (contains_pure 1) (factorTwoPrimeCosInterval_contains n))
  have hprime' :
      (pure 2 * factorTwoPrimeBetaInterval *
        (pure 1 - factorTwoPrimeCosInterval n)).Contains
          (2 * (Real.log 3 / Real.sqrt 3) *
            (1 - Real.cos
              (2 * factorTwoMomentY n.1 * factorTwoPrimeShift))) := by
    convert hprime using 1
    norm_num
  exact contains_add (contains_sub hhead' hcore) hprime'

/-! ## Width and unified all-mode certificates -/

private theorem factorTwoAntisymmetricOneSubCosLowInterval_width_le_1_5 :
    ∀ n : FactorTwoCanonicalEvenIndex, 1 ≤ n.1 → n.1 ≤ 5 →
      width (factorTwoAntisymmetricOneSubCosLowInterval n) ≤
        (1 / 1000000000 : ℚ) := by
  set_option maxRecDepth 1000000 in
  set_option maxHeartbeats 0 in
    decide +kernel

private theorem factorTwoAntisymmetricOneSubCosLowInterval_width_le_6_10 :
    ∀ n : FactorTwoCanonicalEvenIndex, 6 ≤ n.1 → n.1 ≤ 10 →
      width (factorTwoAntisymmetricOneSubCosLowInterval n) ≤
        (1 / 1000000000 : ℚ) := by
  set_option maxRecDepth 1000000 in
  set_option maxHeartbeats 0 in
    decide +kernel

private theorem factorTwoAntisymmetricOneSubCosLowInterval_width_le_11_15 :
    ∀ n : FactorTwoCanonicalEvenIndex, 11 ≤ n.1 → n.1 ≤ 15 →
      width (factorTwoAntisymmetricOneSubCosLowInterval n) ≤
        (1 / 1000000000 : ℚ) := by
  set_option maxRecDepth 1000000 in
  set_option maxHeartbeats 0 in
    decide +kernel

private theorem factorTwoAntisymmetricOneSubCosLowInterval_width_le_16_17 :
    ∀ n : FactorTwoCanonicalEvenIndex, 16 ≤ n.1 → n.1 ≤ 17 →
      width (factorTwoAntisymmetricOneSubCosLowInterval n) ≤
        (1 / 1000000000 : ℚ) := by
  set_option maxRecDepth 1000000 in
  set_option maxHeartbeats 0 in
    decide +kernel

/-- Every complementary low mode has total composed width at most `10⁻⁹`. -/
theorem factorTwoAntisymmetricOneSubCosLowInterval_width_le :
    ∀ n : FactorTwoCanonicalEvenIndex, 1 ≤ n.1 → n.1 ≤ 17 →
      width (factorTwoAntisymmetricOneSubCosLowInterval n) ≤
        (1 / 1000000000 : ℚ) := by
  intro n hn1 hn17
  by_cases hn5 : n.1 ≤ 5
  · exact factorTwoAntisymmetricOneSubCosLowInterval_width_le_1_5 n hn1 hn5
  by_cases hn10 : n.1 ≤ 10
  · exact factorTwoAntisymmetricOneSubCosLowInterval_width_le_6_10 n
      (by omega) hn10
  by_cases hn15 : n.1 ≤ 15
  · exact factorTwoAntisymmetricOneSubCosLowInterval_width_le_11_15 n
      (by omega) hn15
  exact factorTwoAntisymmetricOneSubCosLowInterval_width_le_16_17 n
    (by omega) hn17

/-- Unified target selecting the checkpointed low certificate exactly on
`[1,17]` and the direct high/zero certificate elsewhere. -/
def factorTwoAntisymmetricOneSubCosCertifiedInterval
    (n : FactorTwoCanonicalEvenIndex) : RatInterval :=
  if 1 ≤ n.1 ∧ n.1 ≤ 17 then
    factorTwoAntisymmetricOneSubCosLowInterval n
  else
    factorTwoAntisymmetricOneSubCosMomentInterval n

theorem factorTwoAntisymmetricOneSubCosCertifiedInterval_contains
    (n : FactorTwoCanonicalEvenIndex) :
    (factorTwoAntisymmetricOneSubCosCertifiedInterval n).Contains
      (factorTwoAntisymmetricOneSubCosMoment n.1) := by
  by_cases hlow : 1 ≤ n.1 ∧ n.1 ≤ 17
  · rw [factorTwoAntisymmetricOneSubCosCertifiedInterval, if_pos hlow]
    exact factorTwoAntisymmetricOneSubCosLowInterval_contains n hlow.1 hlow.2
  · rw [factorTwoAntisymmetricOneSubCosCertifiedInterval, if_neg hlow]
    exact factorTwoAntisymmetricOneSubCosMomentInterval_contains n

/-- The low and high constructions compose to a width certificate on all
`201` canonical modes. -/
theorem factorTwoAntisymmetricOneSubCosCertifiedInterval_width_le
    (n : FactorTwoCanonicalEvenIndex) :
    width (factorTwoAntisymmetricOneSubCosCertifiedInterval n) ≤
      (1 / 1000000000 : ℚ) := by
  by_cases hlow : 1 ≤ n.1 ∧ n.1 ≤ 17
  · rw [factorTwoAntisymmetricOneSubCosCertifiedInterval, if_pos hlow]
    exact factorTwoAntisymmetricOneSubCosLowInterval_width_le n hlow.1 hlow.2
  · rw [factorTwoAntisymmetricOneSubCosCertifiedInterval, if_neg hlow]
    by_cases hzero : n.1 = 0
    · have hn : n = ⟨0, by omega⟩ := Fin.ext hzero
      rw [hn,
        factorTwoAntisymmetricOneSubCosMomentInterval_width_zero]
      norm_num
    · exact factorTwoAntisymmetricOneSubCosMomentInterval_width_le_high n
        (by omega)

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhasePerturbationOneSubCosLowEnclosures

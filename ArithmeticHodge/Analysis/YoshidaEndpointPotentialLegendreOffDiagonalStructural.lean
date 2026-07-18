import ArithmeticHodge.Analysis.UnitIntervalLogEnergyAffine
import ArithmeticHodge.Analysis.YoshidaEndpointPotentialLegendreGreenStructural

set_option autoImplicit false

open MeasureTheory Polynomial Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointPotentialLegendreOffDiagonalStructural

open ShiftedLegendreBasis
open ShiftedLegendreCenteredLowModes
open ShiftedLegendreJacobiSturmStructural
open ShiftedLegendreOrthogonality
open UnitIntervalLogEnergyAffine
open YoshidaEndpointPotentialBound
open YoshidaEndpointPotentialLegendreGreenStructural

noncomputable section

/-!
# All-degree off-diagonal endpoint-potential Gram entries

Centered Rodrigues orthogonality, one integration by parts, and the Green
commutator determine every off-diagonal shifted-Legendre entry at once.
No degree cutoff or list of modes occurs in the argument.
-/

/-- Centered shifted-Legendre degree `n` is orthogonal on `[-1,1]` to every
polynomial of degree strictly below `n`. -/
theorem integral_eval_mul_centeredShiftedLegendreReal_eq_zero
    (n : ℕ) (p : ℝ[X]) (hp : p.natDegree < n) :
    (∫ x : ℝ in -1..1,
      p.eval x * (centeredShiftedLegendreReal n).eval x) = 0 := by
  let A : ℝ[X] := C 2 * X - C 1
  have hA : A.natDegree ≤ 1 := by
    dsimp only [A]
    calc
      (C 2 * X - C 1 : ℝ[X]).natDegree ≤
          max (C 2 * X : ℝ[X]).natDegree (C 1 : ℝ[X]).natDegree :=
        natDegree_sub_le _ _
      _ ≤ 1 := by
        apply max_le
        · exact (natDegree_C_mul_le (2 : ℝ) X).trans (by simp)
        · simp
  have hdeg : (p.comp A).natDegree < n := by
    calc
      (p.comp A).natDegree ≤ p.natDegree * A.natDegree := natDegree_comp_le
      _ ≤ p.natDegree * 1 := Nat.mul_le_mul_left _ hA
      _ = p.natDegree := Nat.mul_one _
      _ < n := hp
  have hunit := integral_eval_mul_shiftedLegendreReal_eq_zero n (p.comp A) hdeg
  have htransport := integral_comp_two_mul_sub_one
    (fun x : ℝ ↦ p.eval x * (centeredShiftedLegendreReal n).eval x)
  have hpullback :
      (fun t : ℝ ↦
        p.eval (2 * t - 1) *
          (centeredShiftedLegendreReal n).eval (2 * t - 1)) =
      (fun t : ℝ ↦
        (p.comp A).eval t * (shiftedLegendreReal n).eval t) := by
    funext t
    simp only [A, Polynomial.eval_comp, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      eval_centeredShiftedLegendreReal]
    congr 2
    all_goals ring
  rw [hpullback, hunit] at htransport
  linarith

/-- Centering does not raise the shifted-Legendre degree. -/
theorem natDegree_centeredShiftedLegendreReal_le (n : ℕ) :
    (centeredShiftedLegendreReal n).natDegree ≤ n := by
  have haff : (((2 : ℝ)⁻¹ • (X + 1 : ℝ[X])).natDegree) ≤ 1 := by
    calc
      (((2 : ℝ)⁻¹ • (X + 1 : ℝ[X])).natDegree) ≤
          (X + 1 : ℝ[X]).natDegree := natDegree_smul_le _ _
      _ ≤ max X.natDegree (1 : ℝ[X]).natDegree := natDegree_add_le _ _
      _ ≤ 1 := by simp
  unfold centeredShiftedLegendreReal
  calc
    ((shiftedLegendreReal n).comp ((2 : ℝ)⁻¹ • (X + 1))).natDegree ≤
        (shiftedLegendreReal n).natDegree *
          (((2 : ℝ)⁻¹ • (X + 1 : ℝ[X])).natDegree) :=
      natDegree_comp_le
    _ ≤ n * 1 := by
      exact Nat.mul_le_mul (by simp) haff
    _ = n := Nat.mul_one n

/-- The shifted normalization equals one at the left unit endpoint. -/
theorem eval_shiftedLegendreReal_zero (n : ℕ) :
    (shiftedLegendreReal n).eval 0 = 1 := by
  rw [show (shiftedLegendreReal n).eval 0 =
      (shiftedLegendreReal n).coeff 0 by
    exact Polynomial.eval₂_at_zero (RingHom.id ℝ)]
  simp [coeff_shiftedLegendreReal]

/-- The centered normalization equals one at the left endpoint. -/
theorem eval_centeredShiftedLegendreReal_neg_one (n : ℕ) :
    (centeredShiftedLegendreReal n).eval (-1) = 1 := by
  rw [eval_centeredShiftedLegendreReal]
  norm_num [eval_shiftedLegendreReal_zero]

/-- The centered normalization has reflection sign at the right endpoint. -/
theorem eval_centeredShiftedLegendreReal_one (n : ℕ) :
    (centeredShiftedLegendreReal n).eval 1 = (-1 : ℝ) ^ n := by
  rw [eval_centeredShiftedLegendreReal]
  norm_num
  have hreflect :
      (shiftedLegendreReal n).eval 1 =
        (-1 : ℝ) ^ n * (shiftedLegendreReal n).eval 0 := by
    simp only [shiftedLegendreReal, Polynomial.eval_map]
    change Polynomial.aeval (1 : ℝ) (Polynomial.shiftedLegendre n) =
      (-1 : ℝ) ^ n *
        Polynomial.aeval (0 : ℝ) (Polynomial.shiftedLegendre n)
    simpa using Polynomial.shiftedLegendre_eval_symm n (1 : ℝ)
  rw [hreflect, eval_shiftedLegendreReal_zero, mul_one]

private theorem continuous_polynomialEval (p : ℝ[X]) :
    Continuous (fun x : ℝ ↦ p.eval x) := by
  rw [continuous_iff_continuousAt]
  intro x
  exact (p.hasDerivAt x).continuousAt

/-- The weighted Wronskian of two ordered centered Legendre modes is a pure
endpoint term.  Rodrigues orthogonality kills both interior terms after one
integration by parts. -/
theorem integral_x_mul_centeredShiftedLegendreReal_wronskian
    {m n : ℕ} (hmn : m < n) :
    (∫ x : ℝ in -1..1,
      x * ((centeredShiftedLegendreReal m).derivative.eval x *
          (centeredShiftedLegendreReal n).eval x -
        (centeredShiftedLegendreReal m).eval x *
          (centeredShiftedLegendreReal n).derivative.eval x)) =
      -(1 + (-1 : ℝ) ^ (m + n)) := by
  let qm : ℝ[X] := centeredShiftedLegendreReal m
  let qn : ℝ[X] := centeredShiftedLegendreReal n
  have hqmdeg : qm.natDegree ≤ m := by
    simpa only [qm] using natDegree_centeredShiftedLegendreReal_le m
  have hXqmdeg : (X * qm).natDegree ≤ m + 1 := by
    calc
      (X * qm).natDegree ≤ X.natDegree + qm.natDegree := natDegree_mul_le
      _ ≤ 1 + m := Nat.add_le_add (by simp) hqmdeg
      _ = m + 1 := by omega
  have hderivXqmdeg : (derivative (X * qm)).natDegree ≤ m := by
    calc
      (derivative (X * qm)).natDegree ≤ (X * qm).natDegree - 1 :=
        natDegree_derivative_le _
      _ ≤ (m + 1) - 1 := Nat.sub_le_sub_right hXqmdeg 1
      _ = m := by omega
  have hXderiv : X * derivative qm = derivative (X * qm) - qm := by
    simp only [derivative_mul, derivative_X, one_mul]
    ring
  have hXderivdeg : (X * derivative qm).natDegree ≤ m := by
    rw [hXderiv]
    exact (natDegree_sub_le _ _).trans (max_le hderivXqmdeg hqmdeg)
  have hfirst := integral_eval_mul_centeredShiftedLegendreReal_eq_zero
    n (X * derivative qm) (hXderivdeg.trans_lt hmn)
  have hsecond := integral_eval_mul_centeredShiftedLegendreReal_eq_zero
    n (derivative (X * qm)) (hderivXqmdeg.trans_lt hmn)
  have hfirst' :
      (∫ x : ℝ in -1..1,
        x * qm.derivative.eval x * qn.eval x) = 0 := by
    simpa only [Polynomial.eval_mul, Polynomial.eval_X, qm, qn] using hfirst
  have hsecond' :
      (∫ x : ℝ in -1..1,
        (derivative (X * qm)).eval x * qn.eval x) = 0 := by
    simpa only [qn] using hsecond
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun x : ℝ ↦ (X * qm).eval x)
    (u' := fun x : ℝ ↦ (derivative (X * qm)).eval x)
    (v := fun x : ℝ ↦ qn.eval x)
    (v' := fun x : ℝ ↦ qn.derivative.eval x)
    (fun x _hx ↦ (X * qm).hasDerivAt x)
    (fun x _hx ↦ qn.hasDerivAt x)
    ((continuous_polynomialEval (derivative (X * qm))).intervalIntegrable (-1) 1)
    ((continuous_polynomialEval qn.derivative).intervalIntegrable (-1) 1)
  rw [hsecond'] at hibp
  have hboundary :
      (X * qm).eval 1 * qn.eval 1 -
          (X * qm).eval (-1) * qn.eval (-1) =
        1 + (-1 : ℝ) ^ (m + n) := by
    dsimp only [qm, qn]
    simp only [Polynomial.eval_mul, Polynomial.eval_X,
      eval_centeredShiftedLegendreReal_one,
      eval_centeredShiftedLegendreReal_neg_one]
    rw [pow_add]
    ring
  have hthird :
      (∫ x : ℝ in -1..1,
        x * qm.eval x * qn.derivative.eval x) =
        1 + (-1 : ℝ) ^ (m + n) := by
    calc
      (∫ x : ℝ in -1..1,
          x * qm.eval x * qn.derivative.eval x) =
          ∫ x : ℝ in -1..1,
            (X * qm).eval x * qn.derivative.eval x := by
            apply intervalIntegral.integral_congr
            intro x _hx
            simp only [Polynomial.eval_mul, Polynomial.eval_X]
      _ = (X * qm).eval 1 * qn.eval 1 -
            (X * qm).eval (-1) * qn.eval (-1) := by
          linarith
      _ = 1 + (-1 : ℝ) ^ (m + n) := hboundary
  have hfirstInt : IntervalIntegrable
      (fun x : ℝ ↦ x * qm.derivative.eval x * qn.eval x)
      volume (-1) 1 :=
    ((continuous_id.mul (continuous_polynomialEval qm.derivative)).mul
      (continuous_polynomialEval qn)).intervalIntegrable (-1) 1
  have hthirdInt : IntervalIntegrable
      (fun x : ℝ ↦ x * qm.eval x * qn.derivative.eval x)
      volume (-1) 1 :=
    ((continuous_id.mul (continuous_polynomialEval qm)).mul
      (continuous_polynomialEval qn.derivative)).intervalIntegrable (-1) 1
  change (∫ x : ℝ in -1..1,
    x * (qm.derivative.eval x * qn.eval x -
      qm.eval x * qn.derivative.eval x)) = _
  rw [show (fun x : ℝ ↦
      x * (qm.derivative.eval x * qn.eval x -
        qm.eval x * qn.derivative.eval x)) =
      fun x : ℝ ↦
        x * qm.derivative.eval x * qn.eval x -
          x * qm.eval x * qn.derivative.eval x by
    funext x
    ring,
    intervalIntegral.integral_sub hfirstInt hthirdInt,
    hfirst', hthird]
  ring

/-- Closed all-degree formula for every ordered off-diagonal endpoint-
potential Gram entry. -/
theorem integral_endpointPotential_mul_centeredShiftedLegendreReal
    {m n : ℕ} (hmn : m < n) :
    (∫ x : ℝ in -1..1,
      yoshidaEndpointPotential x *
        (centeredShiftedLegendreReal m).eval x *
        (centeredShiftedLegendreReal n).eval x) =
      (1 + (-1 : ℝ) ^ (m + n)) /
        ((n : ℝ) * (n + 1 : ℝ) - (m : ℝ) * (m + 1 : ℝ)) := by
  let qm : ℝ[X] := centeredShiftedLegendreReal m
  let qn : ℝ[X] := centeredShiftedLegendreReal n
  let lm : ℝ := (m : ℝ) * (m + 1 : ℝ)
  let ln : ℝ := (n : ℝ) * (n + 1 : ℝ)
  have hSm : centeredLegendreSturm qm = lm • qm := by
    simpa only [qm, lm] using
      centeredLegendreSturm_centeredShiftedLegendreReal m
  have hSn : centeredLegendreSturm qn = ln • qn := by
    simpa only [qn, ln] using
      centeredLegendreSturm_centeredShiftedLegendreReal n
  have hgreen := integral_endpointPotential_sturm_commutator qm qn
  rw [hSm, hSn] at hgreen
  simp only [Polynomial.smul_eq_C_mul, Polynomial.eval_mul,
    Polynomial.eval_C] at hgreen
  have hw :
      (∫ x : ℝ in -1..1,
        x * (qm.derivative.eval x * qn.eval x -
          qm.eval x * qn.derivative.eval x)) =
        -(1 + (-1 : ℝ) ^ (m + n)) := by
    simpa only [qm, qn] using
      integral_x_mul_centeredShiftedLegendreReal_wronskian hmn
  rw [hw] at hgreen
  have hleft :
      (∫ x : ℝ in -1..1,
        yoshidaEndpointPotential x *
          (lm * qm.eval x * qn.eval x -
            qm.eval x * (ln * qn.eval x))) =
        (lm - ln) *
          ∫ x : ℝ in -1..1,
            yoshidaEndpointPotential x * qm.eval x * qn.eval x := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _hx
    ring
  rw [hleft] at hgreen
  have hmnR : (m : ℝ) < (n : ℝ) := by exact_mod_cast hmn
  have hgap : 0 < ln - lm := by
    dsimp only [ln, lm]
    rw [show (n : ℝ) * (n + 1 : ℝ) -
        (m : ℝ) * (m + 1 : ℝ) =
      ((n : ℝ) - m) * ((n : ℝ) + m + 1) by ring]
    exact mul_pos (sub_pos.mpr hmnR) (by positivity)
  change (∫ x : ℝ in -1..1,
    yoshidaEndpointPotential x * qm.eval x * qn.eval x) =
      (1 + (-1 : ℝ) ^ (m + n)) / (ln - lm)
  apply (eq_div_iff (ne_of_gt hgap)).2
  nlinarith

/-- Equal-parity off-diagonal entries have the positive spectral-gap
formula. -/
theorem integral_endpointPotential_mul_centeredShiftedLegendreReal_of_even
    {m n : ℕ} (hmn : m < n) (heven : Even (m + n)) :
    (∫ x : ℝ in -1..1,
      yoshidaEndpointPotential x *
        (centeredShiftedLegendreReal m).eval x *
        (centeredShiftedLegendreReal n).eval x) =
      2 / (((n : ℝ) - m) * ((n : ℝ) + m + 1)) := by
  rw [integral_endpointPotential_mul_centeredShiftedLegendreReal hmn,
    heven.neg_one_pow]
  have hden :
      (n : ℝ) * (n + 1 : ℝ) - (m : ℝ) * (m + 1 : ℝ) =
        ((n : ℝ) - m) * ((n : ℝ) + m + 1) := by
    ring
  rw [hden]
  norm_num

/-- Opposite-parity endpoint-potential entries vanish. -/
theorem integral_endpointPotential_mul_centeredShiftedLegendreReal_of_odd
    {m n : ℕ} (hmn : m < n) (hodd : Odd (m + n)) :
    (∫ x : ℝ in -1..1,
      yoshidaEndpointPotential x *
        (centeredShiftedLegendreReal m).eval x *
        (centeredShiftedLegendreReal n).eval x) = 0 := by
  rw [integral_endpointPotential_mul_centeredShiftedLegendreReal hmn,
    hodd.neg_one_pow]
  norm_num

end

end ArithmeticHodge.Analysis.YoshidaEndpointPotentialLegendreOffDiagonalStructural

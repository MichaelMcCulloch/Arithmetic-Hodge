import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseEvenSymmetricBound

set_option autoImplicit false

open Filter MeasureTheory Real Set Topology
open scoped BigOperators Interval

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseEvenSchur

noncomputable section

open YoshidaEndpointHyperbolicBound
open EndpointParityCarleman
open YoshidaFactorTwoPhaseAlternatingCoercivity
open YoshidaFactorTwoPhaseEvenSymmetricBound
open YoshidaFactorTwoPhaseRankLimit
open YoshidaFactorTwoPhaseSymmetricCoercivity
open YoshidaRenormalizedGeometricKernel

/-!
# Endpoint Schur kernel for the even factor-two rank tail

After even reflection, write a profile on the left half of the centered
interval as `p ↦ w (-1 + p)`, with `0 ≤ p ≤ 1`.  The complete negative
hyperbolic-rank tail then has a positive Hankel kernel.  This file sums that
kernel exactly and isolates its sole singularity in an exponentially damped
Carleman majorant.  No rank cutoff or numerical estimate enters the result.
-/

/-- One scalar geometric row of the even decaying-rank kernel. -/
def evenRankEndpointScalar (z : ℝ) : ℝ :=
  yoshidaEndpointA *
    Real.exp (-(5 / 2 : ℝ) * yoshidaEndpointA * z) /
      (1 - Real.exp (-2 * yoshidaEndpointA * z))

/-- Exact geometric summation of a scalar endpoint row.  The shift by one in
`oddRate` is the source of the exponent `5 / 2`. -/
theorem hasSum_evenRankEndpointScalar
    {z : ℝ} (hz : 0 < z) :
    HasSum
      (fun m : ℕ ↦
        yoshidaEndpointA *
          Real.exp
            (-yoshidaEndpointA * oddRate (m + 1) * z))
      (evenRankEndpointScalar z) := by
  let r : ℝ := Real.exp (-2 * yoshidaEndpointA * z)
  have hr0 : 0 ≤ r := by
    dsimp only [r]
    positivity
  have hr1 : r < 1 := by
    dsimp only [r]
    rw [Real.exp_lt_one_iff]
    nlinarith [yoshidaEndpointA_pos]
  have hgeom := (hasSum_geometric_of_lt_one hr0 hr1).mul_left
    (yoshidaEndpointA *
      Real.exp (-(5 / 2 : ℝ) * yoshidaEndpointA * z))
  have hterm :
      (fun m : ℕ ↦
        yoshidaEndpointA *
          Real.exp
            (-yoshidaEndpointA * oddRate (m + 1) * z)) =
        fun m : ℕ ↦
          (yoshidaEndpointA *
            Real.exp (-(5 / 2 : ℝ) * yoshidaEndpointA * z)) *
              r ^ m := by
    funext m
    dsimp only [r]
    rw [← Real.exp_nat_mul]
    rw [show
      yoshidaEndpointA *
          Real.exp (-(5 / 2 : ℝ) * yoshidaEndpointA * z) *
            Real.exp ((m : ℝ) * (-2 * yoshidaEndpointA * z)) =
        yoshidaEndpointA *
          (Real.exp (-(5 / 2 : ℝ) * yoshidaEndpointA * z) *
            Real.exp ((m : ℝ) * (-2 * yoshidaEndpointA * z))) by ring]
    apply congrArg (fun y : ℝ ↦ yoshidaEndpointA * y)
    rw [← Real.exp_add]
    unfold oddRate
    congr 1
    push_cast
    ring
  rw [hterm]
  simpa only [evenRankEndpointScalar, r, div_eq_mul_inv] using hgeom

/-- The geometric row has a sharp exponentially damped Carleman envelope.
The exponent `3 / 2` is not a convenience loss: it is the exact consequence
of `x ≤ sinh x` after the half-odd shift has been removed. -/
theorem evenRankEndpointScalar_le_dampedCarleman
    {z : ℝ} (hz : 0 < z) :
    evenRankEndpointScalar z ≤
      Real.exp (-(3 / 2 : ℝ) * yoshidaEndpointA * z) / (2 * z) := by
  let x : ℝ := yoshidaEndpointA * z
  have hx : 0 < x := by
    dsimp only [x]
    exact mul_pos yoshidaEndpointA_pos hz
  have hsinh : x ≤ Real.sinh x :=
    Real.self_le_sinh_iff.2 hx.le
  have hexpneg : 0 < Real.exp (-x) := Real.exp_pos _
  have hden :
      2 * x * Real.exp (-x) ≤ 1 - Real.exp (-2 * x) := by
    have htwoexp : 0 ≤ 2 * Real.exp (-x) :=
      mul_nonneg (by norm_num) hexpneg.le
    have hmul := mul_le_mul_of_nonneg_right hsinh
      htwoexp
    rw [Real.sinh_eq] at hmul
    have hposneg : Real.exp x * Real.exp (-x) = 1 := by
      rw [← Real.exp_add]
      simp
    have hnegneg : Real.exp (-x) * Real.exp (-x) =
        Real.exp (-2 * x) := by
      rw [← Real.exp_add]
      congr 1
      ring
    nlinarith
  have hdenpos : 0 < 1 - Real.exp (-2 * x) := by
    rw [sub_pos, Real.exp_lt_one_iff]
    linarith
  have hzpos : 0 < 2 * z := by positivity
  have hfactor :
      0 ≤ Real.exp (-(3 / 2 : ℝ) * x) / (2 * z) :=
    div_nonneg (Real.exp_pos _).le hzpos.le
  have hscaled :
      (Real.exp (-(3 / 2 : ℝ) * x) / (2 * z)) *
          (2 * x * Real.exp (-x)) ≤
        (Real.exp (-(3 / 2 : ℝ) * x) / (2 * z)) *
          (1 - Real.exp (-2 * x)) :=
    mul_le_mul_of_nonneg_left hden hfactor
  have hcore :
      yoshidaEndpointA * Real.exp (-(5 / 2 : ℝ) * x) ≤
        (Real.exp (-(3 / 2 : ℝ) * x) / (2 * z)) *
          (1 - Real.exp (-2 * x)) := by
    calc
      yoshidaEndpointA * Real.exp (-(5 / 2 : ℝ) * x) =
          (Real.exp (-(3 / 2 : ℝ) * x) / (2 * z)) *
            (2 * x * Real.exp (-x)) := by
        have hexp :
            Real.exp (-(3 / 2 : ℝ) * x) * Real.exp (-x) =
              Real.exp (-(5 / 2 : ℝ) * x) := by
          rw [← Real.exp_add]
          congr 1
          ring
        have hrearrange :
          (Real.exp (-(3 / 2 : ℝ) * x) / (2 * z)) *
              (2 * x * Real.exp (-x)) =
            (x / z) *
              (Real.exp (-(3 / 2 : ℝ) * x) * Real.exp (-x)) := by
          field_simp [hz.ne']
        have hxz : x / z = yoshidaEndpointA := by
          dsimp only [x]
          field_simp [hz.ne']
        rw [hrearrange, hexp, hxz]
      _ ≤ (Real.exp (-(3 / 2 : ℝ) * x) / (2 * z)) *
          (1 - Real.exp (-2 * x)) := hscaled
  unfold evenRankEndpointScalar
  have hdenpos' :
      0 < 1 - Real.exp (-2 * yoshidaEndpointA * z) := by
    convert hdenpos using 1
    dsimp only [x]
    ring
  rw [div_le_iff₀ hdenpos']
  convert hcore using 1 <;> (dsimp only [x]; ring)

/-- Forgetting the exponential damping leaves half of the scalar Carleman
kernel. -/
theorem evenRankEndpointScalar_le_half_carleman
    {z : ℝ} (hz : 0 < z) :
    evenRankEndpointScalar z ≤ 1 / (2 * z) := by
  have hdamped := evenRankEndpointScalar_le_dampedCarleman hz
  have hexp :
      Real.exp (-(3 / 2 : ℝ) * yoshidaEndpointA * z) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith [yoshidaEndpointA_pos]
  have hden : 0 ≤ 2 * z := by positivity
  calc
    evenRankEndpointScalar z ≤
        Real.exp (-(3 / 2 : ℝ) * yoshidaEndpointA * z) / (2 * z) :=
      hdamped
    _ ≤ 1 / (2 * z) := div_le_div_of_nonneg_right hexp hden

/-- The exact positive endpoint kernel generated by every decaying even
hyperbolic rank. -/
def evenRankEndpointKernel (p q : ℝ) : ℝ :=
  evenRankEndpointScalar (p + q) +
    evenRankEndpointScalar (2 + p - q) +
    evenRankEndpointScalar (2 - p + q) +
    evenRankEndpointScalar (4 - p - q)

/-- The four exponentially damped Carleman rows which dominate the complete
rank-tail kernel. -/
def evenRankEndpointSchurMajorant (p q : ℝ) : ℝ :=
  Real.exp (-(3 / 2 : ℝ) * yoshidaEndpointA * (p + q)) /
      (2 * (p + q)) +
    Real.exp (-(3 / 2 : ℝ) * yoshidaEndpointA * (2 + p - q)) /
      (2 * (2 + p - q)) +
    Real.exp (-(3 / 2 : ℝ) * yoshidaEndpointA * (2 - p + q)) /
      (2 * (2 - p + q)) +
    Real.exp (-(3 / 2 : ℝ) * yoshidaEndpointA * (4 - p - q)) /
      (2 * (4 - p - q))

/-- Exact summation of the full endpoint kernel.  The factor `4` is the
even-reflection factor in both variables. -/
theorem hasSum_evenRankEndpointKernel
    {p q : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hq0 : 0 < q) (hq1 : q ≤ 1) :
    HasSum
      (fun m : ℕ ↦
        4 * yoshidaEndpointA *
          Real.exp
            (-2 * yoshidaEndpointA * oddRate (m + 1)) *
          Real.cosh
            (yoshidaEndpointA * oddRate (m + 1) * (1 - p)) *
          Real.cosh
            (yoshidaEndpointA * oddRate (m + 1) * (1 - q)))
      (evenRankEndpointKernel p q) := by
  have hpq : 0 < p + q := by linarith
  have hpmq : 0 < 2 + p - q := by linarith
  have hmpq : 0 < 2 - p + q := by linarith
  have hmm : 0 < 4 - p - q := by linarith
  have h1 := hasSum_evenRankEndpointScalar hpq
  have h2 := hasSum_evenRankEndpointScalar hpmq
  have h3 := hasSum_evenRankEndpointScalar hmpq
  have h4 := hasSum_evenRankEndpointScalar hmm
  have hall := ((h1.add h2).add h3).add h4
  convert hall using 1
  · funext m
    let a : ℝ := yoshidaEndpointA * oddRate (m + 1)
    have hpp :
        Real.exp (-2 * a) * Real.exp (a * (1 - p)) *
            Real.exp (a * (1 - q)) =
          Real.exp (-a * (p + q)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    have hpn :
        Real.exp (-2 * a) * Real.exp (a * (1 - p)) *
            Real.exp (-(a * (1 - q))) =
          Real.exp (-a * (2 + p - q)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    have hnp :
        Real.exp (-2 * a) * Real.exp (-(a * (1 - p))) *
            Real.exp (a * (1 - q)) =
          Real.exp (-a * (2 - p + q)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    have hnn :
        Real.exp (-2 * a) * Real.exp (-(a * (1 - p))) *
            Real.exp (-(a * (1 - q))) =
          Real.exp (-a * (4 - p - q)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    rw [show -2 * yoshidaEndpointA * oddRate (m + 1) = -2 * a by
          dsimp only [a]
          ring,
      show yoshidaEndpointA * oddRate (m + 1) * (1 - p) =
          a * (1 - p) by rfl,
      show yoshidaEndpointA * oddRate (m + 1) * (1 - q) =
          a * (1 - q) by rfl,
      show -yoshidaEndpointA * oddRate (m + 1) * (p + q) =
          -a * (p + q) by
            dsimp only [a]
            ring,
      show -yoshidaEndpointA * oddRate (m + 1) * (2 + p - q) =
          -a * (2 + p - q) by
            dsimp only [a]
            ring,
      show -yoshidaEndpointA * oddRate (m + 1) * (2 - p + q) =
          -a * (2 - p + q) by
            dsimp only [a]
            ring,
      show -yoshidaEndpointA * oddRate (m + 1) * (4 - p - q) =
          -a * (4 - p - q) by
            dsimp only [a]
            ring]
    change 4 * yoshidaEndpointA * Real.exp (-2 * a) *
          Real.cosh (a * (1 - p)) * Real.cosh (a * (1 - q)) = _
    rw [Real.cosh_eq, Real.cosh_eq]
    rw [show 4 * yoshidaEndpointA * Real.exp (-2 * a) *
          ((Real.exp (a * (1 - p)) + Real.exp (-(a * (1 - p)))) / 2) *
          ((Real.exp (a * (1 - q)) + Real.exp (-(a * (1 - q)))) / 2) =
        yoshidaEndpointA *
          (Real.exp (-2 * a) * Real.exp (a * (1 - p)) *
              Real.exp (a * (1 - q)) +
            Real.exp (-2 * a) * Real.exp (a * (1 - p)) *
              Real.exp (-(a * (1 - q))) +
            Real.exp (-2 * a) * Real.exp (-(a * (1 - p))) *
              Real.exp (a * (1 - q)) +
            Real.exp (-2 * a) * Real.exp (-(a * (1 - p))) *
              Real.exp (-(a * (1 - q)))) by ring]
    rw [hpp, hpn, hnp, hnn]
    ring

/-- Pointwise Schur domination of the complete rank tail on the open unit
endpoint square.  Only the `p + q` row is singular at the endpoint corner;
the other three denominators stay uniformly positive. -/
theorem evenRankEndpointKernel_le_schurMajorant
    {p q : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hq0 : 0 < q) (hq1 : q ≤ 1) :
    evenRankEndpointKernel p q ≤
      evenRankEndpointSchurMajorant p q := by
  have hpq : 0 < p + q := by linarith
  have hpmq : 0 < 2 + p - q := by linarith
  have hmpq : 0 < 2 - p + q := by linarith
  have hmm : 0 < 4 - p - q := by linarith
  unfold evenRankEndpointKernel evenRankEndpointSchurMajorant
  exact add_le_add
    (add_le_add
      (add_le_add
        (evenRankEndpointScalar_le_dampedCarleman hpq)
        (evenRankEndpointScalar_le_dampedCarleman hpmq))
      (evenRankEndpointScalar_le_dampedCarleman hmpq))
    (evenRankEndpointScalar_le_dampedCarleman hmm)

/-- The complete rank kernel is dominated by the existing parity-unit Schur
kernel, up to the harmless constant row `1 / 4`.  The two nonsingular mixed
rows fit the `1 / (1 + p*q)` branch jointly; bounding them separately would
lose this useful cancellation in the row budget. -/
theorem evenRankEndpointKernel_le_parityUnit_add_quarter
    {p q : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hq0 : 0 < q) (hq1 : q ≤ 1) :
    evenRankEndpointKernel p q ≤
      parityUnitCarlemanKernel p q + (1 / 4 : ℝ) := by
  have hpq : 0 < p + q := by linarith
  have hplus : 0 < 2 + p - q := by linarith
  have hminus : 0 < 2 - p + q := by linarith
  have hfour : 0 < 4 - p - q := by linarith
  have h1 := evenRankEndpointScalar_le_half_carleman hpq
  have h2 := evenRankEndpointScalar_le_half_carleman hplus
  have h3 := evenRankEndpointScalar_le_half_carleman hminus
  have h4 := evenRankEndpointScalar_le_half_carleman hfour
  have hmiddle :
      1 / (2 * (2 + p - q)) + 1 / (2 * (2 - p + q)) ≤
        1 / (1 + p * q) := by
    have hp0' : 0 ≤ p := hp0.le
    have hq0' : 0 ≤ q := hq0.le
    have hpqden : 0 < 1 + p * q := by positivity
    field_simp [hpqden.ne', hplus.ne', hminus.ne']
    nlinarith [sq_nonneg (1 - p), sq_nonneg (1 - q)]
  have hlast : 1 / (2 * (4 - p - q)) ≤ (1 / 4 : ℝ) := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (4 - p - q))]
    nlinarith
  unfold evenRankEndpointKernel parityUnitCarlemanKernel
  calc
    evenRankEndpointScalar (p + q) +
          evenRankEndpointScalar (2 + p - q) +
          evenRankEndpointScalar (2 - p + q) +
          evenRankEndpointScalar (4 - p - q) ≤
        1 / (2 * (p + q)) +
          1 / (2 * (2 + p - q)) +
          1 / (2 * (2 - p + q)) +
          1 / (2 * (4 - p - q)) := by linarith
    _ ≤ 1 / (p + q) + 1 / (1 + p * q) + (1 / 4 : ℝ) := by
      have hfirst : 1 / (2 * (p + q)) ≤ 1 / (p + q) := by
        have hinv : 0 ≤ 1 / (p + q) := by positivity
        calc
          1 / (2 * (p + q)) = (1 / 2 : ℝ) * (1 / (p + q)) := by
            field_simp [hpq.ne']
          _ ≤ 1 * (1 / (p + q)) :=
            mul_le_mul_of_nonneg_right (by norm_num) hinv
          _ = 1 / (p + q) := one_mul _
      linarith

/-! ## Transport of even moments to the endpoint half interval -/

/-- Even reflection and the endpoint coordinate `p = 1 - x` turn every
centered cosh moment into twice a positive-unit-interval moment. -/
theorem centeredCoshMoment_eq_two_mul_endpointHalf
    (w : ℝ → ℝ) (hw : Continuous w) (heven : Function.Even w)
    (lambda : ℝ) :
    centeredCoshMoment w lambda =
      2 * (∫ p : ℝ in 0..1,
        Real.cosh (lambda * (1 - p)) * w (1 - p)) := by
  let g : ℝ → ℝ := fun x ↦ Real.cosh (lambda * x) * w x
  have hg : Continuous g := by
    dsimp only [g]
    fun_prop
  have hgeven : Function.Even g := by
    intro x
    dsimp only [g]
    rw [mul_neg, Real.cosh_neg, heven]
  have hleft :
      (∫ x : ℝ in -1..0, g x) = ∫ x : ℝ in 0..1, g x := by
    have hreflect := intervalIntegral.integral_comp_neg
      (f := g) (a := (-1 : ℝ)) (b := 0)
    rw [show (fun x : ℝ ↦ g (-x)) = g by
      funext x
      exact hgeven x] at hreflect
    simpa using hreflect
  have hsplit :
      (∫ x : ℝ in -1..1, g x) =
        (∫ x : ℝ in -1..0, g x) + ∫ x : ℝ in 0..1, g x := by
    exact (intervalIntegral.integral_add_adjacent_intervals
      (hg.intervalIntegrable (-1) 0) (hg.intervalIntegrable 0 1)).symm
  have hshift :
      (∫ p : ℝ in 0..1, g (1 - p)) = ∫ x : ℝ in 0..1, g x := by
    simpa only [sub_self, sub_zero] using
      intervalIntegral.integral_comp_sub_left
        (f := g) (a := (0 : ℝ)) (b := 1) 1
  unfold centeredCoshMoment
  change (∫ x : ℝ in -1..1, g x) = _
  rw [hsplit, hleft, ← hshift]
  dsimp only [g]
  ring

/-- Finite endpoint kernel associated with the first `N` decaying ranks. -/
def evenRankEndpointPartialKernel (N : ℕ) (p q : ℝ) : ℝ :=
  ∑ m ∈ Finset.range N,
    4 * yoshidaEndpointA *
      Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
      Real.cosh (yoshidaEndpointA * oddRate (m + 1) * (1 - p)) *
      Real.cosh (yoshidaEndpointA * oddRate (m + 1) * (1 - q))

/-- Every finite rank kernel already satisfies the complete parity-unit row
majorant.  Positivity of the geometric summands makes the passage from a
partial sum to the exact infinite kernel order-preserving. -/
theorem evenRankEndpointPartialKernel_le_parityUnit_add_quarter
    (N : ℕ) {p q : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hq0 : 0 < q) (hq1 : q ≤ 1) :
    evenRankEndpointPartialKernel N p q ≤
      parityUnitCarlemanKernel p q + (1 / 4 : ℝ) := by
  have hsum := hasSum_evenRankEndpointKernel hp0 hp1 hq0 hq1
  have hpartial : evenRankEndpointPartialKernel N p q ≤
      evenRankEndpointKernel p q := by
    unfold evenRankEndpointPartialKernel
    rw [← hsum.tsum_eq]
    exact hsum.summable.sum_le_tsum (Finset.range N)
      (fun m _hm ↦ by
        have hc1 : 0 ≤ Real.cosh
            (yoshidaEndpointA * oddRate (m + 1) * (1 - p)) :=
          (Real.cosh_pos _).le
        have hc2 : 0 ≤ Real.cosh
            (yoshidaEndpointA * oddRate (m + 1) * (1 - q)) :=
          (Real.cosh_pos _).le
        exact mul_nonneg
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg (by norm_num) yoshidaEndpointA_pos.le)
              (Real.exp_pos _).le)
            hc1)
          hc2)
  exact hpartial.trans
    (evenRankEndpointKernel_le_parityUnit_add_quarter hp0 hp1 hq0 hq1)

/-- A finite decaying-rank square sum is exactly the product-measure
quadratic form of the corresponding endpoint kernel. -/
theorem evenRankPartialSquares_eq_endpointKernel
    (w : ℝ → ℝ) (hw : Continuous w) (heven : Function.Even w)
    (N : ℕ) :
    yoshidaEndpointA *
        (∑ m ∈ Finset.range N,
          Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
            centeredCoshMoment w
              (yoshidaEndpointA * oddRate (m + 1)) ^ 2) =
      ∫ z : ℝ × ℝ,
        evenRankEndpointPartialKernel N z.1 z.2 *
          w (1 - z.1) * w (1 - z.2)
        ∂((volume.restrict (Ioc (0 : ℝ) 1)).prod
          (volume.restrict (Ioc (0 : ℝ) 1))) := by
  let mu : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)
  let f : ℝ → ℝ := fun p ↦ w (1 - p)
  let u : ℕ → ℝ → ℝ := fun m p ↦
    Real.cosh (yoshidaEndpointA * oddRate (m + 1) * (1 - p)) * f p
  have hf : Continuous f := by
    dsimp only [f]
    fun_prop
  have hu (m : ℕ) : Continuous (u m) := by
    dsimp only [u]
    fun_prop
  have hui (m : ℕ) : Integrable (u m) mu := by
    have hcompact : IntegrableOn (u m) (Icc (0 : ℝ) 1) :=
      (hu m).continuousOn.integrableOn_compact isCompact_Icc
    exact hcompact.mono_set Ioc_subset_Icc_self
  have hmoment (m : ℕ) :
      centeredCoshMoment w
          (yoshidaEndpointA * oddRate (m + 1)) =
        2 * ∫ p : ℝ, u m p ∂mu := by
    have h := centeredCoshMoment_eq_two_mul_endpointHalf
      w hw heven (yoshidaEndpointA * oddRate (m + 1))
    rw [intervalIntegral.integral_of_le (by norm_num)] at h
    simpa only [mu, u, f] using h
  let k : ℕ → ℝ × ℝ → ℝ := fun m z ↦
    4 * yoshidaEndpointA *
      Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
      Real.cosh (yoshidaEndpointA * oddRate (m + 1) * (1 - z.1)) *
      Real.cosh (yoshidaEndpointA * oddRate (m + 1) * (1 - z.2)) *
      f z.1 * f z.2
  have hk (m : ℕ) : Integrable (k m) (mu.prod mu) := by
    have hprod := (hui m).mul_prod (hui m)
    refine (hprod.const_mul
      (4 * yoshidaEndpointA *
        Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)))).congr ?_
    filter_upwards [] with z
    dsimp only [k, u]
    ring
  have hterm (m : ℕ) :
      yoshidaEndpointA *
          (Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
            centeredCoshMoment w
              (yoshidaEndpointA * oddRate (m + 1)) ^ 2) =
        ∫ z : ℝ × ℝ, k m z ∂mu.prod mu := by
    rw [show (fun z : ℝ × ℝ ↦ k m z) =
        fun z ↦
          (4 * yoshidaEndpointA *
            Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1))) *
              (u m z.1 * u m z.2) by
      funext z
      dsimp only [k, u]
      ring,
      MeasureTheory.integral_const_mul,
      integral_prod_mul, hmoment]
    ring
  calc
    yoshidaEndpointA *
        (∑ m ∈ Finset.range N,
          Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
            centeredCoshMoment w
              (yoshidaEndpointA * oddRate (m + 1)) ^ 2) =
        ∑ m ∈ Finset.range N,
          yoshidaEndpointA *
            (Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
              centeredCoshMoment w
                (yoshidaEndpointA * oddRate (m + 1)) ^ 2) := by
      rw [Finset.mul_sum]
    _ = ∑ m ∈ Finset.range N,
        ∫ z : ℝ × ℝ, k m z ∂mu.prod mu := by
      apply Finset.sum_congr rfl
      intro m _hm
      exact hterm m
    _ = ∫ z : ℝ × ℝ, ∑ m ∈ Finset.range N, k m z ∂mu.prod mu := by
      rw [MeasureTheory.integral_finset_sum]
      exact fun m _hm ↦ hk m
    _ = ∫ z : ℝ × ℝ,
        evenRankEndpointPartialKernel N z.1 z.2 *
          w (1 - z.1) * w (1 - z.2)
        ∂((volume.restrict (Ioc (0 : ℝ) 1)).prod
          (volume.restrict (Ioc (0 : ℝ) 1))) := by
      congr 1
      funext z
      dsimp only [mu, k, f, evenRankEndpointPartialKernel]
      simp only [Finset.sum_mul]


end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseEvenSchur

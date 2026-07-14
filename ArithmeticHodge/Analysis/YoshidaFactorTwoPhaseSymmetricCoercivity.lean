import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseEnvelope
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseTailCoercivity
import ArithmeticHodge.Analysis.EndpointParityCarleman
import ArithmeticHodge.Analysis.YoshidaEndpointTriangleInterchange

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseSymmetricCoercivity

noncomputable section

open CenteredEndpointCorrelation
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointSingularCorrelation
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoAdjacentKernel
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoPhaseEnvelope
open YoshidaFactorTwoPhaseTailCoercivity
open EndpointParityCarleman
open YoshidaRenormalizedGeometricKernel
open YoshidaEndpointTriangleInterchange

/-!
# The symmetric factor-two phase coordinate

This file isolates the actual one-profile quadratic coordinate.  In
particular, the reflected endpoint pole is kept with its sign; replacing it
by an absolute-value envelope would introduce the logarithmic endpoint
potential and lose the desired mass-only constant.
-/

/-- Exact signed normal form of the symmetric perturbation. -/
theorem symmetricPerturbation_eq_regular_sub_pole_sub_primes
    (w : ℝ → ℝ) (hw : Continuous w) :
    factorTwoCenteredSymmetricPerturbation w =
        yoshidaEndpointA *
            (∫ t : ℝ in 0..2,
              factorTwoCenteredForwardPhaseKernel w 0 1 0 t) +
          (∫ t : ℝ in 0..2,
            factorTwoCenteredReflectedDesingularizedPhaseKernel
              w 0 1 0 t) -
          (1 / 2 : ℝ) *
            (∫ t : ℝ in 0..2,
              factorTwoCenteredPhaseCorrelation w 0 1 0 t / (2 - t)) -
          (Real.log 2 / Real.sqrt 2) *
            (∫ x : ℝ in -1..1, w x ^ 2) -
          (Real.log 3 / Real.sqrt 3) *
            factorTwoCenteredPhaseCorrelation w 0 1 0
              (factorTwoPrimeShift / yoshidaEndpointA) := by
  have h :=
    phase_symmetric_add_alternating_eq_regular_sub_pole_sub_primes
      w 0 hw continuous_zero 1 0
  have hz : factorTwoCenteredSymmetricPerturbation (0 : ℝ → ℝ) = 0 := by
    simp [factorTwoCenteredSymmetricPerturbation,
      centeredEndpointCorrelation]
  simpa [hz] using h

/-- The retained `p = 3` self-correlation is a half-mass contraction.  This
is the one-profile specialization of the complete phase estimate; in
particular it does not discard the fact that the two translated pieces are
disjoint at this lag. -/
theorem two_mul_abs_primeCorrelation_le_energy
    (w : ℝ → ℝ) (hw : Continuous w) :
    2 * |centeredEndpointCorrelation w
        (factorTwoPrimeShift / yoshidaEndpointA)| ≤
      ∫ x : ℝ in -1..1, w x ^ 2 := by
  have h := two_mul_abs_phaseCorrelation_primeShift_le_mass
    w 0 hw continuous_zero 1 0 (by norm_num)
  simpa [factorTwoCenteredPhaseCorrelation,
    centeredEndpointCorrelation] using h

/-- With its exact arithmetic coefficient, the retained prime atom still
costs at most half of the endpoint energy. -/
theorem abs_weighted_primeCorrelation_le_half_energy
    (w : ℝ → ℝ) (hw : Continuous w) :
    |(Real.log 3 / Real.sqrt 3) *
        centeredEndpointCorrelation w
          (factorTwoPrimeShift / yoshidaEndpointA)| ≤
      (1 / 2 : ℝ) * ∫ x : ℝ in -1..1, w x ^ 2 := by
  let E : ℝ := ∫ x : ℝ in -1..1, w x ^ 2
  let C : ℝ := centeredEndpointCorrelation w
    (factorTwoPrimeShift / yoshidaEndpointA)
  have hE : 0 ≤ E := by
    dsimp only [E]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun x _hx ↦ sq_nonneg (w x))
  have hC := two_mul_abs_primeCorrelation_le_energy w hw
  have hcoeff0 : 0 ≤ Real.log 3 / Real.sqrt 3 := by positivity
  have hcoeff1 : Real.log 3 / Real.sqrt 3 < 1 :=
    factorTwoPrimeThreeWeight_lt_one
  change 2 * |C| ≤ E at hC
  rw [abs_mul, abs_of_nonneg hcoeff0]
  change (Real.log 3 / Real.sqrt 3) * |C| ≤ (1 / 2 : ℝ) * E
  nlinarith [abs_nonneg C]

/-- The sharp Carleman half-pole together with the dyadic mass atom uses
strictly less than `13/10` of the full endpoint energy.  Thus their apparent
endpoint singularity alone cannot violate the desired `3/2` bound; the
remaining issue is the joint (not separately normed) interaction with the
retained prime translation. -/
theorem carlemanHalfPole_add_dyadicMass_lt_thirteen_tenths :
    Real.pi / 4 + Real.log 2 / Real.sqrt 2 < (13 / 10 : ℝ) := by
  have hsqrtPos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrtSq : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hsqrtLower : (7 / 5 : ℝ) < Real.sqrt 2 := by
    nlinarith [Real.sqrt_nonneg 2]
  have hlogUpper : Real.log 2 < (7 / 10 : ℝ) :=
    Real.log_two_lt_d9.trans (by norm_num)
  have hdyadic : Real.log 2 / Real.sqrt 2 < (1 / 2 : ℝ) := by
    rw [div_lt_iff₀ hsqrtPos]
    nlinarith
  have hpi : Real.pi / 4 < (63 / 80 : ℝ) := by
    have := Real.pi_lt_d2
    nlinarith
  nlinarith

/-! ## Reflection fold of the endpoint pole -/

/-- The additive-convolution section seen from the left endpoint.  After
reflection parity, this is exactly the correlation at the opposite-endpoint
lag `2 - t`. -/
def endpointFoldedCorrelation (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ p : ℝ in 0..t, w (-1 + (t - p)) * w (-1 + p)

/-- Even reflection turns the opposite-endpoint correlation into the
positive-sign endpoint convolution. -/
theorem centeredCorrelation_two_sub_eq_endpointFolded_of_even
    {w : ℝ → ℝ} (heven : Function.Even w) (t : ℝ) :
    centeredEndpointCorrelation w (2 - t) =
      endpointFoldedCorrelation w t := by
  unfold centeredEndpointCorrelation endpointFoldedCorrelation
  rw [show 1 - (2 - t) = -1 + t by ring]
  calc
    (∫ x : ℝ in -1..-1 + t, w (2 - t + x) * w x) =
        ∫ p : ℝ in 0..t,
          w (2 - t + (-1 + p)) * w (-1 + p) := by
      convert (intervalIntegral.integral_comp_add_left
        (a := (0 : ℝ)) (b := t)
        (fun x : ℝ ↦ w (2 - t + x) * w x) (-1)).symm using 1;
        ring_nf
    _ = ∫ p : ℝ in 0..t,
          w (-1 + (t - p)) * w (-1 + p) := by
      apply intervalIntegral.integral_congr
      intro p _hp
      change w (2 - t + (-1 + p)) * w (-1 + p) =
        w (-1 + (t - p)) * w (-1 + p)
      rw [show 2 - t + (-1 + p) = -(-1 + (t - p)) by ring,
        heven]

/-- Odd reflection gives the same endpoint convolution with the opposite
sign. -/
theorem centeredCorrelation_two_sub_eq_neg_endpointFolded_of_odd
    {w : ℝ → ℝ} (hodd : Function.Odd w) (t : ℝ) :
    centeredEndpointCorrelation w (2 - t) =
      -endpointFoldedCorrelation w t := by
  unfold centeredEndpointCorrelation endpointFoldedCorrelation
  rw [show 1 - (2 - t) = -1 + t by ring]
  calc
    (∫ x : ℝ in -1..-1 + t, w (2 - t + x) * w x) =
        ∫ p : ℝ in 0..t,
          w (2 - t + (-1 + p)) * w (-1 + p) := by
      convert (intervalIntegral.integral_comp_add_left
        (a := (0 : ℝ)) (b := t)
        (fun x : ℝ ↦ w (2 - t + x) * w x) (-1)).symm using 1;
        ring_nf
    _ = ∫ p : ℝ in 0..t,
          -(w (-1 + (t - p)) * w (-1 + p)) := by
      apply intervalIntegral.integral_congr
      intro p _hp
      change w (2 - t + (-1 + p)) * w (-1 + p) =
        -(w (-1 + (t - p)) * w (-1 + p))
      rw [show 2 - t + (-1 + p) = -(-1 + (t - p)) by ring,
        hodd]
      ring
    _ = -(∫ p : ℝ in 0..t,
          w (-1 + (t - p)) * w (-1 + p)) := by
      rw [← intervalIntegral.integral_neg]

/-! ## The reflected pole and the retained prime as one quadratic block -/

/-- The complementary overlap length belonging to the retained `p = 3`
translation.  Writing the prime lag in this form puts its correlation on the
same endpoint convolution as the reflected Cauchy pole. -/
def factorTwoPrimeComplement : ℝ :=
  2 - factorTwoPrimeShift / yoshidaEndpointA

theorem two_sub_factorTwoPrimeComplement :
    2 - factorTwoPrimeComplement =
      factorTwoPrimeShift / yoshidaEndpointA := by
  unfold factorTwoPrimeComplement
  ring

/-- On an even profile the retained prime is the endpoint convolution at its
complementary overlap length. -/
theorem primeCorrelation_eq_endpointFolded_of_even
    {w : ℝ → ℝ} (heven : Function.Even w) :
    centeredEndpointCorrelation w
        (factorTwoPrimeShift / yoshidaEndpointA) =
      endpointFoldedCorrelation w factorTwoPrimeComplement := by
  rw [← two_sub_factorTwoPrimeComplement]
  exact centeredCorrelation_two_sub_eq_endpointFolded_of_even
    heven factorTwoPrimeComplement

/-- On an odd profile the same retained-prime endpoint convolution occurs
with the opposite reflection sign. -/
theorem primeCorrelation_eq_neg_endpointFolded_of_odd
    {w : ℝ → ℝ} (hodd : Function.Odd w) :
    centeredEndpointCorrelation w
        (factorTwoPrimeShift / yoshidaEndpointA) =
      -endpointFoldedCorrelation w factorTwoPrimeComplement := by
  rw [← two_sub_factorTwoPrimeComplement]
  exact centeredCorrelation_two_sub_eq_neg_endpointFolded_of_odd
    hodd factorTwoPrimeComplement

/-- The exact pole-plus-prime quadratic block.  It is deliberately a single
definition: bounding its two terms separately loses the target constant. -/
def factorTwoPolePrimeJoint (w : ℝ → ℝ) : ℝ :=
  (1 / 2 : ℝ) *
      (∫ t : ℝ in 0..2,
        centeredEndpointCorrelation w t / (2 - t)) +
    (Real.log 3 / Real.sqrt 3) *
      centeredEndpointCorrelation w
        (factorTwoPrimeShift / yoshidaEndpointA)

/-- Reflection parity transports both the pole and the retained prime to one
and the same endpoint-convolution functional. -/
theorem polePrimeJoint_eq_endpointFolded_of_even
    {w : ℝ → ℝ} (heven : Function.Even w) :
    factorTwoPolePrimeJoint w =
      (1 / 2 : ℝ) *
          (∫ t : ℝ in 0..2, endpointFoldedCorrelation w t / t) +
        (Real.log 3 / Real.sqrt 3) *
          endpointFoldedCorrelation w factorTwoPrimeComplement := by
  unfold factorTwoPolePrimeJoint
  rw [integral_centeredEndpointCorrelation_div_two_sub_eq_reflected,
    primeCorrelation_eq_endpointFolded_of_even heven]
  congr 2
  apply intervalIntegral.integral_congr
  intro t _ht
  change centeredEndpointCorrelation w (2 - t) / t =
    endpointFoldedCorrelation w t / t
  rw [centeredCorrelation_two_sub_eq_endpointFolded_of_even heven]

/-- The odd case is the negative of exactly the same folded joint
functional; in particular, taking its absolute value does not spend either
term separately. -/
theorem polePrimeJoint_eq_neg_endpointFolded_of_odd
    {w : ℝ → ℝ} (hodd : Function.Odd w) :
    factorTwoPolePrimeJoint w =
      -((1 / 2 : ℝ) *
          (∫ t : ℝ in 0..2, endpointFoldedCorrelation w t / t) +
        (Real.log 3 / Real.sqrt 3) *
          endpointFoldedCorrelation w factorTwoPrimeComplement) := by
  unfold factorTwoPolePrimeJoint
  rw [integral_centeredEndpointCorrelation_div_two_sub_eq_reflected,
    primeCorrelation_eq_neg_endpointFolded_of_odd hodd]
  have hfold :
      (∫ t : ℝ in 0..2,
          centeredEndpointCorrelation w (2 - t) / t) =
        -(∫ t : ℝ in 0..2, endpointFoldedCorrelation w t / t) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t _ht
    change centeredEndpointCorrelation w (2 - t) / t =
      -(endpointFoldedCorrelation w t / t)
    rw [centeredCorrelation_two_sub_eq_neg_endpointFolded_of_odd hodd]
    ring
  rw [hfold]
  ring

/-- Exact perturbation normal form with the reflected pole and `p = 3` atom
syntactically inseparable. -/
theorem symmetricPerturbation_eq_regular_sub_dyadic_sub_polePrimeJoint
    (w : ℝ → ℝ) (hw : Continuous w) :
    factorTwoCenteredSymmetricPerturbation w =
        yoshidaEndpointA *
            (∫ t : ℝ in 0..2,
              factorTwoCenteredForwardPhaseKernel w 0 1 0 t) +
          (∫ t : ℝ in 0..2,
            factorTwoCenteredReflectedDesingularizedPhaseKernel
              w 0 1 0 t) -
          (Real.log 2 / Real.sqrt 2) *
            (∫ x : ℝ in -1..1, w x ^ 2) -
          factorTwoPolePrimeJoint w := by
  rw [symmetricPerturbation_eq_regular_sub_pole_sub_primes w hw]
  unfold factorTwoPolePrimeJoint
  simp [factorTwoCenteredPhaseCorrelation, centeredEndpointCorrelation]
  ring

/-! ## The one-sided archimedean/prime split -/

/-- The complete archimedean adjacent-cell block before either retained prime
atom is subtracted. -/
def factorTwoCenteredArchBlock (w : ℝ → ℝ) : ℝ :=
  yoshidaEndpointA *
    ∫ t : ℝ in 0..2,
      factorTwoSymmetricWeight (yoshidaEndpointA * t) *
        centeredEndpointCorrelation w t

/-- The two retained prime atoms as one mass/translation quadratic block. -/
def factorTwoCenteredPrimeBlock (w : ℝ → ℝ) : ℝ :=
  (Real.log 2 / Real.sqrt 2) *
      (∫ x : ℝ in -1..1, w x ^ 2) +
    (Real.log 3 / Real.sqrt 3) *
      centeredEndpointCorrelation w
        (factorTwoPrimeShift / yoshidaEndpointA)

/-- In this normalization the symmetric perturbation is exactly the
archimedean adjacent-cell form minus the complete retained-prime block. -/
theorem symmetricPerturbation_eq_arch_sub_primeBlock (w : ℝ → ℝ) :
    factorTwoCenteredSymmetricPerturbation w =
      factorTwoCenteredArchBlock w - factorTwoCenteredPrimeBlock w := by
  unfold factorTwoCenteredSymmetricPerturbation factorTwoCenteredArchBlock
    factorTwoCenteredPrimeBlock
  rw [centeredEndpointCorrelation_zero]
  ring

/-- The `p = 3` weight is strictly smaller than twice the dyadic weight.
Consequently the complete retained-prime block has a strictly positive mass
floor even at the most adverse translated correlation. -/
theorem primeThreeWeight_lt_two_mul_dyadicWeight :
    Real.log 3 / Real.sqrt 3 <
      2 * (Real.log 2 / Real.sqrt 2) := by
  have hlog2pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hsqrt2pos : 0 < Real.sqrt (2 : ℝ) :=
    Real.sqrt_pos.2 (by norm_num)
  have hsqrt3pos : 0 < Real.sqrt (3 : ℝ) :=
    Real.sqrt_pos.2 (by norm_num)
  have hsqrt23 : Real.sqrt (2 : ℝ) < Real.sqrt (3 : ℝ) :=
    Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hlog3lt : Real.log (3 : ℝ) < 2 * Real.log (2 : ℝ) := by
    calc
      Real.log (3 : ℝ) < Real.log (4 : ℝ) :=
        Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)
      _ = Real.log ((2 : ℝ) * 2) := by norm_num
      _ = 2 * Real.log (2 : ℝ) := by
        rw [Real.log_mul (by norm_num) (by norm_num)]
        ring
  calc
    Real.log 3 / Real.sqrt 3 <
        (2 * Real.log 2) / Real.sqrt 2 := by
      rw [div_lt_div_iff₀ hsqrt3pos hsqrt2pos]
      calc
        Real.log 3 * Real.sqrt 2 <
            (2 * Real.log 2) * Real.sqrt 2 :=
          mul_lt_mul_of_pos_right hlog3lt hsqrt2pos
        _ < (2 * Real.log 2) * Real.sqrt 3 :=
          mul_lt_mul_of_pos_left hsqrt23
            (mul_pos (by norm_num) hlog2pos)
    _ = 2 * (Real.log 2 / Real.sqrt 2) := by ring

/-- Sharp mass interval for the complete retained-prime block.  The
translation atom is not bounded after being detached from the dyadic atom;
the result records their positive combined interval. -/
theorem primeBlock_mass_bounds
    (w : ℝ → ℝ) (hw : Continuous w) :
    let E := ∫ x : ℝ in -1..1, w x ^ 2
    (Real.log 2 / Real.sqrt 2 -
          (Real.log 3 / Real.sqrt 3) / 2) * E ≤
        factorTwoCenteredPrimeBlock w ∧
      factorTwoCenteredPrimeBlock w ≤
        (Real.log 2 / Real.sqrt 2 +
          (Real.log 3 / Real.sqrt 3) / 2) * E := by
  dsimp only
  let E : ℝ := ∫ x : ℝ in -1..1, w x ^ 2
  let C : ℝ := centeredEndpointCorrelation w
    (factorTwoPrimeShift / yoshidaEndpointA)
  let alpha : ℝ := Real.log 2 / Real.sqrt 2
  let beta : ℝ := Real.log 3 / Real.sqrt 3
  have hcorr := two_mul_abs_primeCorrelation_le_energy w hw
  change 2 * |C| ≤ E at hcorr
  have hClower : -(E / 2) ≤ C := by
    have := neg_abs_le C
    nlinarith [abs_nonneg C]
  have hCupper : C ≤ E / 2 := by
    have := le_abs_self C
    nlinarith [abs_nonneg C]
  have hbeta : 0 ≤ beta := by
    dsimp only [beta]
    positivity
  constructor
  · unfold factorTwoCenteredPrimeBlock
    dsimp only [E, C, alpha, beta] at hClower hbeta ⊢
    nlinarith
  · unfold factorTwoCenteredPrimeBlock
    dsimp only [E, C, alpha, beta] at hCupper hbeta ⊢
    nlinarith

/-- The upper prime-block coefficient is strictly below one. -/
theorem primeBlock_upperCoefficient_lt_one :
    Real.log 2 / Real.sqrt 2 +
        (Real.log 3 / Real.sqrt 3) / 2 < (1 : ℝ) := by
  have hsqrtPos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrtSq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrtLower : (7 / 5 : ℝ) < Real.sqrt 2 := by
    nlinarith [Real.sqrt_nonneg 2]
  have hlogUpper : Real.log 2 < (7 / 10 : ℝ) :=
    Real.log_two_lt_d9.trans (by norm_num)
  have hdyadic : Real.log 2 / Real.sqrt 2 < (1 / 2 : ℝ) := by
    rw [div_lt_iff₀ hsqrtPos]
    nlinarith
  have hthree := factorTwoPrimeThreeWeight_lt_one
  nlinarith

/-! ## Rank-one series of the archimedean block -/

/-- On the open overlap interval the complete symmetric adjacent kernel is a
single growing hyperbolic rank followed by the exact half-odd decaying rank
series.  This is the scalar identity needed before parity turns every
hyperbolic correlation integral into a signed square of a Laplace moment. -/
theorem factorTwoSymmetricWeight_eq_rankOneSeries
    {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t < 2) :
    factorTwoSymmetricWeight (yoshidaEndpointA * t) =
      2 * Real.exp yoshidaEndpointA *
          Real.cosh (yoshidaEndpointA * t / 2) -
        ∑' m : ℕ,
          2 * Real.exp
              (-2 * yoshidaEndpointA * oddRate (m + 1)) *
            Real.cosh
              (yoshidaEndpointA * oddRate (m + 1) * t) := by
  let zp : ℝ := yoshidaEndpointA * (2 + t)
  let zm : ℝ := yoshidaEndpointA * (2 - t)
  have hzp : 0 < zp := by
    dsimp only [zp]
    exact mul_pos yoshidaEndpointA_pos (by linarith)
  have hzm : 0 < zm := by
    dsimp only [zm]
    exact mul_pos yoshidaEndpointA_pos (by linarith)
  have hsummable (z : ℝ) (hz : 0 < z) :
      Summable (fun m : ℕ ↦ Real.exp (-oddRate (m + 1) * z)) := by
    have hfull : Summable
        (fun k : ℕ ↦ Real.exp (-oddRate k * z)) := by
      have hscaled := (hasSum_oddExponentials hz).summable.mul_left (1 / 2 : ℝ)
      convert hscaled using 1
      funext k
      ring
    simpa only [Nat.add_comm] using (summable_nat_add_iff 1).2 hfull
  have hsp := hsummable zp hzp
  have hsm := hsummable zm hzm
  have hhead :
      Real.exp (zp / 2) + Real.exp (zm / 2) =
        2 * Real.exp yoshidaEndpointA *
          Real.cosh (yoshidaEndpointA * t / 2) := by
    rw [Real.cosh_eq]
    dsimp only [zp, zm]
    rw [show yoshidaEndpointA * (2 + t) / 2 =
          yoshidaEndpointA + yoshidaEndpointA * t / 2 by ring,
      show yoshidaEndpointA * (2 - t) / 2 =
          yoshidaEndpointA + -(yoshidaEndpointA * t / 2) by ring,
      Real.exp_add, Real.exp_add]
    ring
  have hterm (m : ℕ) :
      Real.exp (-oddRate (m + 1) * zp) +
          Real.exp (-oddRate (m + 1) * zm) =
        2 * Real.exp
              (-2 * yoshidaEndpointA * oddRate (m + 1)) *
            Real.cosh
              (yoshidaEndpointA * oddRate (m + 1) * t) := by
    rw [Real.cosh_eq]
    dsimp only [zp, zm]
    rw [show -oddRate (m + 1) * (yoshidaEndpointA * (2 + t)) =
          -2 * yoshidaEndpointA * oddRate (m + 1) +
            -(yoshidaEndpointA * oddRate (m + 1) * t) by ring,
      show -oddRate (m + 1) * (yoshidaEndpointA * (2 - t)) =
          -2 * yoshidaEndpointA * oddRate (m + 1) +
            yoshidaEndpointA * oddRate (m + 1) * t by ring,
      Real.exp_add, Real.exp_add]
    ring
  have hsum :
      (∑' m : ℕ, Real.exp (-oddRate (m + 1) * zp)) +
          ∑' m : ℕ, Real.exp (-oddRate (m + 1) * zm) =
        ∑' m : ℕ,
          2 * Real.exp
              (-2 * yoshidaEndpointA * oddRate (m + 1)) *
            Real.cosh
              (yoshidaEndpointA * oddRate (m + 1) * t) := by
    rw [← hsp.tsum_add hsm]
    apply tsum_congr
    exact hterm
  unfold factorTwoSymmetricWeight
  rw [factorTwoLogLength_eq_two_mul_yoshidaEndpointA]
  rw [show 2 * yoshidaEndpointA + yoshidaEndpointA * t = zp by
      dsimp only [zp]; ring,
    show 2 * yoshidaEndpointA - yoshidaEndpointA * t = zm by
      dsimp only [zm]; ring,
    factorTwoAdjacentSmoothKernel_eq_exp_sub_tsum hzp,
    factorTwoAdjacentSmoothKernel_eq_exp_sub_tsum hzm]
  linear_combination hhead - hsum

/-! ## Hyperbolic correlation ranks -/

/-- The centered even Laplace moment at a real rate. -/
def centeredCoshMoment (w : ℝ → ℝ) (lambda : ℝ) : ℝ :=
  ∫ x : ℝ in -1..1, Real.cosh (lambda * x) * w x

/-- The centered odd Laplace moment at a real rate. -/
def centeredSinhMoment (w : ℝ → ℝ) (lambda : ℝ) : ℝ :=
  ∫ x : ℝ in -1..1, Real.sinh (lambda * x) * w x

/-- The hyperbolic difference kernel separates into one even and one odd
rank.  Recording the subtraction sign explicitly is what makes reflection
parity turn the correlation integral into a signed square. -/
theorem cosh_sub_eq_cosh_mul_cosh_sub_sinh_mul_sinh
    (lambda y x : ℝ) :
    Real.cosh (lambda * (y - x)) =
      Real.cosh (lambda * y) * Real.cosh (lambda * x) -
        Real.sinh (lambda * y) * Real.sinh (lambda * x) := by
  rw [mul_sub, Real.cosh_sub]

/-- A continuous lag weight transports the one-sided endpoint correlation to
the centered upper triangle.  This is the exact measure-theoretic bridge
between the scalar rank series and the corresponding quadratic ranks. -/
private theorem integral_weight_mul_centeredCorrelation_eq_upperTriangle
    (w : ℝ → ℝ) (hw : Continuous w)
    (q : ℝ → ℝ) (hq : Continuous q) :
    (∫ t : ℝ in 0..2, q t * centeredEndpointCorrelation w t) =
      ∫ p : ℝ × ℝ in centeredUpperTriangle,
        q (p.1 - p.2) * w p.1 * w p.2 := by
  let K : ℝ × ℝ → ℝ := fun p ↦
    q (p.1 - p.2) * w p.1 * w p.2
  let H : ℝ × ℝ → ℝ := fun p ↦ K (p.1 + p.2, p.2)
  have hTmeas : MeasurableSet positiveDistanceTriangle := by
    unfold positiveDistanceTriangle
    measurability
  have hKcont : Continuous K := by
    dsimp only [K]
    fun_prop
  have hHcont : Continuous H := by
    dsimp only [H]
    exact hKcont.comp (by fun_prop)
  have hHRectangle : IntegrableOn H
      (Icc (0 : ℝ) 2 ×ˢ Icc (-1 : ℝ) 1)
      ((volume : Measure ℝ).prod volume) :=
    hHcont.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hTsubset : positiveDistanceTriangle ⊆
      Icc (0 : ℝ) 2 ×ˢ Icc (-1 : ℝ) 1 := by
    intro p hp
    exact ⟨⟨hp.1, hp.2.1⟩, ⟨hp.2.2.1, by linarith [hp.2.2.2, hp.1]⟩⟩
  have hHTriangle : IntegrableOn H positiveDistanceTriangle
      ((volume : Measure ℝ).prod volume) :=
    hHRectangle.mono_set hTsubset
  have hHIndicator : Integrable
      (positiveDistanceTriangle.indicator H)
      ((volume : Measure ℝ).prod volume) :=
    hHTriangle.integrable_indicator hTmeas
  have hOuter :
      (∫ t : ℝ in 0..2, q t * centeredEndpointCorrelation w t) =
        ∫ t : ℝ in 0..2, ∫ x : ℝ in -1..1 - t, H (t, x) := by
    apply intervalIntegral.integral_congr
    intro t _ht
    unfold centeredEndpointCorrelation
    change q t * (∫ x : ℝ in -1..1 - t, w (t + x) * w x) =
      ∫ x : ℝ in -1..1 - t,
        q ((t + x) - x) * w (t + x) * w x
    rw [show (fun x : ℝ ↦
        q ((t + x) - x) * w (t + x) * w x) =
      fun x ↦ q t * (w (t + x) * w x) by
        funext x
        rw [show t + x - x = t by ring]
        ring,
      intervalIntegral.integral_const_mul]
  have hTriangleFold :
      (∫ t : ℝ in 0..2, ∫ x : ℝ in -1..1 - t, H (t, x)) =
        ∫ p : ℝ × ℝ in positiveDistanceTriangle, H p := by
    rw [← integral_indicator hTmeas,
      Measure.volume_eq_prod ℝ ℝ,
      integral_prod _ hHIndicator]
    rw [intervalIntegral.integral_of_le (by norm_num),
      ← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    filter_upwards [MeasureTheory.Measure.ae_ne volume (0 : ℝ)] with t ht0
    by_cases ht : t ∈ Ioc (0 : ℝ) 2
    · rw [Set.indicator_of_mem ht]
      calc
        (∫ x : ℝ in -1..1 - t, H (t, x)) =
            ∫ x : ℝ,
              (Icc (-1 : ℝ) (1 - t)).indicator (fun x ↦ H (t, x)) x := by
          rw [intervalIntegral.integral_of_le (by linarith [ht.2]),
            ← integral_Icc_eq_integral_Ioc,
            ← integral_indicator measurableSet_Icc]
        _ = ∫ x : ℝ,
            positiveDistanceTriangle.indicator H (t, x) := by
          apply integral_congr_ae
          filter_upwards [] with x
          by_cases hx : x ∈ Icc (-1 : ℝ) (1 - t)
          · have hp : (t, x) ∈ positiveDistanceTriangle :=
                ⟨ht.1.le, ht.2, hx.1, hx.2⟩
            rw [Set.indicator_of_mem hx, Set.indicator_of_mem hp]
          · have hp : (t, x) ∉ positiveDistanceTriangle := by
              intro hp
              exact hx ⟨hp.2.2.1, hp.2.2.2⟩
            rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hp]
    · rw [Set.indicator_of_notMem ht]
      have hrow : (fun x : ℝ ↦
          positiveDistanceTriangle.indicator H (t, x)) = 0 := by
        funext x
        by_cases hp : (t, x) ∈ positiveDistanceTriangle
        · exfalso
          apply ht
          exact ⟨lt_of_le_of_ne hp.1 (Ne.symm ht0), hp.2.1⟩
        · rw [Set.indicator_of_notMem hp]
          rfl
      rw [hrow]
      simp
  calc
    (∫ t : ℝ in 0..2, q t * centeredEndpointCorrelation w t) =
        ∫ t : ℝ in 0..2, ∫ x : ℝ in -1..1 - t, H (t, x) := hOuter
    _ = ∫ p : ℝ × ℝ in positiveDistanceTriangle, H p := hTriangleFold
    _ = ∫ p : ℝ × ℝ in centeredUpperTriangle, K p := by
      simpa only [H] using setIntegral_positiveDistanceTriangle_shear K
    _ = ∫ p : ℝ × ℝ in centeredUpperTriangle,
        q (p.1 - p.2) * w p.1 * w p.2 := by rfl

/-- An even lag weight fills the centered square twice.  The only overlap of
the two reflected triangles is the diagonal, which is null for planar
Lebesgue measure. -/
private theorem two_mul_integral_evenWeight_mul_centeredCorrelation
    (w : ℝ → ℝ) (hw : Continuous w)
    (q : ℝ → ℝ) (hq : Continuous q) (hqEven : Function.Even q) :
    2 * (∫ t : ℝ in 0..2, q t * centeredEndpointCorrelation w t) =
      ∫ y : ℝ in -1..1, ∫ x : ℝ in -1..1,
        q (y - x) * w y * w x := by
  let K : ℝ × ℝ → ℝ := fun p ↦
    q (p.1 - p.2) * w p.1 * w p.2
  let S : Set (ℝ × ℝ) := Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1
  let U : Set (ℝ × ℝ) := centeredUpperTriangle
  have hSmeas : MeasurableSet S := by
    dsimp only [S]
    exact measurableSet_Icc.prod measurableSet_Icc
  have hUmeas : MeasurableSet U := by
    dsimp only [U]
    unfold centeredUpperTriangle
    measurability
  have hKcont : Continuous K := by
    dsimp only [K]
    fun_prop
  have hKSquare : IntegrableOn K S
      ((volume : Measure ℝ).prod volume) := by
    apply hKcont.continuousOn.integrableOn_compact
    dsimp only [S]
    exact isCompact_Icc.prod isCompact_Icc
  have hUsub : U ⊆ S := by
    intro p hp
    dsimp only [U, S] at hp ⊢
    unfold centeredUpperTriangle at hp
    exact ⟨⟨by linarith [hp.1, hp.2.1], hp.2.2⟩,
      ⟨hp.1, by linarith [hp.2.1, hp.2.2]⟩⟩
  have hKUpper : IntegrableOn K U
      ((volume : Measure ℝ).prod volume) :=
    hKSquare.mono_set hUsub
  have hIU : Integrable (U.indicator K)
      ((volume : Measure ℝ).prod volume) :=
    hKUpper.integrable_indicator hUmeas
  have hKswap (p : ℝ × ℝ) : K p.swap = K p := by
    rcases p with ⟨y, x⟩
    dsimp only [K, Prod.swap_prod_mk]
    rw [show x - y = -(y - x) by ring, hqEven]
    ring
  have haeNe : ∀ᵐ p : ℝ × ℝ
      ∂((volume : Measure ℝ).prod volume), p.1 ≠ p.2 := by
    apply (MeasureTheory.Measure.ae_prod_iff_ae_ae (by measurability)).2
    filter_upwards [] with y
    filter_upwards [MeasureTheory.Measure.ae_ne volume y] with x hx
    exact Ne.symm hx
  have hIndicatorSplit : ∀ᵐ p : ℝ × ℝ
      ∂((volume : Measure ℝ).prod volume),
      S.indicator K p = U.indicator K p + U.indicator K p.swap := by
    filter_upwards [haeNe] with p hpne
    by_cases hpS : p ∈ S
    · rcases lt_or_gt_of_ne hpne with hlt | hgt
      · have hpU : p ∉ U := by
          intro hpU
          dsimp only [U] at hpU
          unfold centeredUpperTriangle at hpU
          linarith [hpU.2.1]
        have hswapU : p.swap ∈ U := by
          rcases p with ⟨y, x⟩
          dsimp only [S, U, Prod.swap_prod_mk] at hpS ⊢
          unfold centeredUpperTriangle
          exact ⟨hpS.1.1, hlt.le, hpS.2.2⟩
        rw [Set.indicator_of_mem hpS, Set.indicator_of_notMem hpU,
          Set.indicator_of_mem hswapU, hKswap]
        ring
      · have hpU : p ∈ U := by
          rcases p with ⟨y, x⟩
          dsimp only [S, U] at hpS ⊢
          unfold centeredUpperTriangle
          exact ⟨hpS.2.1, hgt.le, hpS.1.2⟩
        have hswapU : p.swap ∉ U := by
          intro hswapU
          rcases p with ⟨y, x⟩
          dsimp only [U, Prod.swap_prod_mk] at hswapU
          unfold centeredUpperTriangle at hswapU
          linarith [hswapU.2.1]
        rw [Set.indicator_of_mem hpS, Set.indicator_of_mem hpU,
          Set.indicator_of_notMem hswapU]
        ring
    · have hpU : p ∉ U := fun hpU ↦ hpS (hUsub hpU)
      have hswapU : p.swap ∉ U := by
        intro hswapU
        have hsS := hUsub hswapU
        apply hpS
        rcases p with ⟨y, x⟩
        dsimp only [S, Prod.swap_prod_mk] at hsS ⊢
        exact ⟨hsS.2, hsS.1⟩
      rw [Set.indicator_of_notMem hpS, Set.indicator_of_notMem hpU,
        Set.indicator_of_notMem hswapU]
      ring
  have hswapIntegral :
      (∫ p : ℝ × ℝ, U.indicator K p.swap) =
        ∫ p : ℝ × ℝ, U.indicator K p := by
    rw [Measure.volume_eq_prod ℝ ℝ]
    exact integral_prod_swap (U.indicator K)
  have hsplit :
      (∫ p : ℝ × ℝ in S, K p) =
        (∫ p : ℝ × ℝ in U, K p) +
          ∫ p : ℝ × ℝ in U, K p := by
    rw [← integral_indicator hSmeas,
      ← integral_indicator hUmeas]
    calc
      (∫ p : ℝ × ℝ, S.indicator K p) =
          ∫ p : ℝ × ℝ,
            (U.indicator K p + U.indicator K p.swap) :=
        integral_congr_ae hIndicatorSplit
      _ = (∫ p : ℝ × ℝ, U.indicator K p) +
          ∫ p : ℝ × ℝ, U.indicator K p.swap := by
        simpa only [Pi.add_apply, Function.comp_apply] using
          integral_add hIU hIU.swap
      _ = _ := by rw [hswapIntegral]
  have hSquareIterated :
      (∫ y : ℝ in -1..1, ∫ x : ℝ in -1..1, K (y, x)) =
        ∫ p : ℝ × ℝ in S, K p := by
    calc
      (∫ y : ℝ in -1..1, ∫ x : ℝ in -1..1, K (y, x)) =
          ∫ y : ℝ in Icc (-1) 1,
            ∫ x : ℝ in Icc (-1) 1, K (y, x) := by
        rw [intervalIntegral.integral_of_le (by norm_num),
          ← integral_Icc_eq_integral_Ioc]
        apply setIntegral_congr_fun measurableSet_Icc
        intro y _hy
        change (∫ x : ℝ in -1..1, K (y, x)) =
          ∫ x : ℝ in Icc (-1) 1, K (y, x)
        rw [intervalIntegral.integral_of_le (by norm_num),
          ← integral_Icc_eq_integral_Ioc]
      _ = ∫ p : ℝ × ℝ in S, K p := by
        dsimp only [S]
        exact (setIntegral_prod K hKSquare).symm
  have hUpper := integral_weight_mul_centeredCorrelation_eq_upperTriangle
    w hw q hq
  change 2 * (∫ t : ℝ in 0..2,
      q t * centeredEndpointCorrelation w t) =
    ∫ y : ℝ in -1..1, ∫ x : ℝ in -1..1, K (y, x)
  rw [hUpper]
  dsimp only [U] at hsplit
  rw [hSquareIterated]
  linarith

/-- Every hyperbolic correlation rank is exactly the difference of the
squares of its even and odd centered Laplace moments. -/
theorem two_mul_integral_cosh_mul_centeredCorrelation
    (w : ℝ → ℝ) (hw : Continuous w) (lambda : ℝ) :
    2 * (∫ t : ℝ in 0..2,
        Real.cosh (lambda * t) * centeredEndpointCorrelation w t) =
      centeredCoshMoment w lambda ^ 2 -
        centeredSinhMoment w lambda ^ 2 := by
  let ce : ℝ → ℝ := fun x ↦ Real.cosh (lambda * x) * w x
  let so : ℝ → ℝ := fun x ↦ Real.sinh (lambda * x) * w x
  have hce : Continuous ce := by
    dsimp only [ce]
    fun_prop
  have hso : Continuous so := by
    dsimp only [so]
    fun_prop
  have hinner (y : ℝ) :
      (∫ x : ℝ in -1..1,
        Real.cosh (lambda * (y - x)) * w y * w x) =
        (Real.cosh (lambda * y) * w y) * centeredCoshMoment w lambda -
          (Real.sinh (lambda * y) * w y) * centeredSinhMoment w lambda := by
    rw [show (fun x : ℝ ↦
        Real.cosh (lambda * (y - x)) * w y * w x) =
      fun x ↦ (Real.cosh (lambda * y) * w y) * ce x -
        (Real.sinh (lambda * y) * w y) * so x by
          funext x
          dsimp only [ce, so]
          rw [cosh_sub_eq_cosh_mul_cosh_sub_sinh_mul_sinh]
          ring]
    rw [intervalIntegral.integral_sub
        ((hce.const_mul _).intervalIntegrable (-1) 1)
        ((hso.const_mul _).intervalIntegrable (-1) 1),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    rfl
  have houter :
      (∫ y : ℝ in -1..1,
        ∫ x : ℝ in -1..1,
          Real.cosh (lambda * (y - x)) * w y * w x) =
        centeredCoshMoment w lambda ^ 2 -
          centeredSinhMoment w lambda ^ 2 := by
    rw [show (fun y : ℝ ↦
        ∫ x : ℝ in -1..1,
          Real.cosh (lambda * (y - x)) * w y * w x) =
      fun y ↦ ce y * centeredCoshMoment w lambda -
        so y * centeredSinhMoment w lambda by
          funext y
          exact hinner y]
    rw [intervalIntegral.integral_sub
        ((hce.mul_const _).intervalIntegrable (-1) 1)
        ((hso.mul_const _).intervalIntegrable (-1) 1),
      intervalIntegral.integral_mul_const,
      intervalIntegral.integral_mul_const]
    unfold centeredCoshMoment centeredSinhMoment
    dsimp only [ce, so]
    ring
  have hEven : Function.Even (fun t : ℝ ↦ Real.cosh (lambda * t)) := by
    intro t
    dsimp only
    rw [show lambda * -t = -(lambda * t) by ring, Real.cosh_neg]
  have hfill := two_mul_integral_evenWeight_mul_centeredCorrelation
    w hw (fun t : ℝ ↦ Real.cosh (lambda * t)) (by fun_prop) hEven
  rw [hfill]
  exact houter

private theorem centered_intervalIntegral_eq_zero_of_odd
    (f : ℝ → ℝ) (hf : Function.Odd f) :
    (∫ x : ℝ in -1..1, f x) = 0 := by
  have hreflect :
      (∫ x : ℝ in -1..1, f (-x)) = ∫ x : ℝ in -1..1, f x := by
    simpa only [neg_neg] using
      (intervalIntegral.integral_comp_neg
        (f := f) (a := (-1 : ℝ)) (b := 1))
  have hneg :
      (∫ x : ℝ in -1..1, f (-x)) = -(∫ x : ℝ in -1..1, f x) := by
    rw [show (fun x : ℝ ↦ f (-x)) = fun x ↦ -f x by
      funext x
      exact hf x]
    exact intervalIntegral.integral_neg
  rw [hneg] at hreflect
  exact CharZero.neg_eq_self_iff.mp hreflect

theorem centeredSinhMoment_eq_zero_of_even
    {w : ℝ → ℝ} (hw : Function.Even w) (lambda : ℝ) :
    centeredSinhMoment w lambda = 0 := by
  apply centered_intervalIntegral_eq_zero_of_odd
  intro x
  change Real.sinh (lambda * -x) * w (-x) =
    -(Real.sinh (lambda * x) * w x)
  rw [show lambda * -x = -(lambda * x) by ring,
    Real.sinh_neg, hw]
  ring

theorem centeredCoshMoment_eq_zero_of_odd
    {w : ℝ → ℝ} (hw : Function.Odd w) (lambda : ℝ) :
    centeredCoshMoment w lambda = 0 := by
  apply centered_intervalIntegral_eq_zero_of_odd
  intro x
  change Real.cosh (lambda * -x) * w (-x) =
    -(Real.cosh (lambda * x) * w x)
  rw [show lambda * -x = -(lambda * x) by ring,
    Real.cosh_neg, hw]
  ring

/-- On an even profile every hyperbolic correlation rank is a nonnegative
square. -/
theorem two_mul_integral_cosh_mul_centeredCorrelation_of_even
    (w : ℝ → ℝ) (hw : Continuous w) (heven : Function.Even w)
    (lambda : ℝ) :
    2 * (∫ t : ℝ in 0..2,
        Real.cosh (lambda * t) * centeredEndpointCorrelation w t) =
      centeredCoshMoment w lambda ^ 2 := by
  rw [two_mul_integral_cosh_mul_centeredCorrelation w hw,
    centeredSinhMoment_eq_zero_of_even heven]
  ring

/-- On an odd profile every hyperbolic correlation rank is the negative of a
square. -/
theorem two_mul_integral_cosh_mul_centeredCorrelation_of_odd
    (w : ℝ → ℝ) (hw : Continuous w) (hodd : Function.Odd w)
    (lambda : ℝ) :
    2 * (∫ t : ℝ in 0..2,
        Real.cosh (lambda * t) * centeredEndpointCorrelation w t) =
      -(centeredSinhMoment w lambda ^ 2) := by
  rw [two_mul_integral_cosh_mul_centeredCorrelation w hw,
    centeredCoshMoment_eq_zero_of_odd hodd]
  ring

/-! ## Exact finite-rank archimedean forms -/

/-- The first `N` decaying hyperbolic ranks of the symmetric adjacent-cell
kernel, together with its growing head rank.  Keeping this finite makes the
subsequent integral interchange purely algebraic; the analytic infinite
limit can then be taken in a downstream tail-closure theorem. -/
def factorTwoSymmetricRankPartialWeight (N : ℕ) (t : ℝ) : ℝ :=
  2 * Real.exp yoshidaEndpointA *
      Real.cosh (yoshidaEndpointA * t / 2) -
    ∑ m ∈ Finset.range N,
      2 * Real.exp
          (-2 * yoshidaEndpointA * oddRate (m + 1)) *
        Real.cosh
          (yoshidaEndpointA * oddRate (m + 1) * t)

/-- The centered quadratic form associated with the finite hyperbolic-rank
approximation. -/
def factorTwoCenteredArchRankPartialSum
    (w : ℝ → ℝ) (N : ℕ) : ℝ :=
  yoshidaEndpointA *
    ∫ t : ℝ in 0..2,
      factorTwoSymmetricRankPartialWeight N t *
        centeredEndpointCorrelation w t

private theorem intervalIntegrable_cosh_mul_centeredCorrelation
    (w : ℝ → ℝ) (hw : Continuous w) (lambda : ℝ) :
    IntervalIntegrable
      (fun t : ℝ ↦ Real.cosh (lambda * t) *
        centeredEndpointCorrelation w t) volume 0 2 := by
  exact ((by fun_prop : Continuous (fun t : ℝ ↦
      Real.cosh (lambda * t))).mul
    (continuous_centeredEndpointCorrelation_of_continuous w hw))
      |>.intervalIntegrable 0 2

/-- On an even profile, the finite archimedean approximation is exactly one
positive growing Laplace square minus the finite sum of positive decaying
Laplace squares. -/
theorem factorTwoCenteredArchRankPartialSum_eq_evenSquares
    (w : ℝ → ℝ) (hw : Continuous w) (heven : Function.Even w)
    (N : ℕ) :
    factorTwoCenteredArchRankPartialSum w N =
      yoshidaEndpointA *
        (Real.exp yoshidaEndpointA *
            centeredCoshMoment w (yoshidaEndpointA / 2) ^ 2 -
          ∑ m ∈ Finset.range N,
            Real.exp
                (-2 * yoshidaEndpointA * oddRate (m + 1)) *
              centeredCoshMoment w
                (yoshidaEndpointA * oddRate (m + 1)) ^ 2) := by
  have hhead :=
    two_mul_integral_cosh_mul_centeredCorrelation_of_even
      w hw heven (yoshidaEndpointA / 2)
  have htail (m : ℕ) :=
    two_mul_integral_cosh_mul_centeredCorrelation_of_even
      w hw heven (yoshidaEndpointA * oddRate (m + 1))
  have hheadScaled :
      (∫ t : ℝ in 0..2,
        2 * Real.exp yoshidaEndpointA *
          Real.cosh (yoshidaEndpointA * t / 2) *
            centeredEndpointCorrelation w t) =
        Real.exp yoshidaEndpointA *
          centeredCoshMoment w (yoshidaEndpointA / 2) ^ 2 := by
    rw [show (fun t : ℝ ↦
        2 * Real.exp yoshidaEndpointA *
          Real.cosh (yoshidaEndpointA * t / 2) *
            centeredEndpointCorrelation w t) =
      fun t : ℝ ↦
        (2 * Real.exp yoshidaEndpointA) *
          (Real.cosh ((yoshidaEndpointA / 2) * t) *
            centeredEndpointCorrelation w t) by
        funext t
        ring_nf]
    rw [intervalIntegral.integral_const_mul]
    linear_combination Real.exp yoshidaEndpointA * hhead
  have htailScaled (m : ℕ) :
      (∫ t : ℝ in 0..2,
        2 * Real.exp
            (-2 * yoshidaEndpointA * oddRate (m + 1)) *
          Real.cosh
              (yoshidaEndpointA * oddRate (m + 1) * t) *
            centeredEndpointCorrelation w t) =
        Real.exp
            (-2 * yoshidaEndpointA * oddRate (m + 1)) *
          centeredCoshMoment w
            (yoshidaEndpointA * oddRate (m + 1)) ^ 2 := by
    rw [show (fun t : ℝ ↦
        2 * Real.exp
            (-2 * yoshidaEndpointA * oddRate (m + 1)) *
          Real.cosh
              (yoshidaEndpointA * oddRate (m + 1) * t) *
            centeredEndpointCorrelation w t) =
      fun t : ℝ ↦
        (2 * Real.exp
            (-2 * yoshidaEndpointA * oddRate (m + 1))) *
          (Real.cosh
              (yoshidaEndpointA * oddRate (m + 1) * t) *
            centeredEndpointCorrelation w t) by
        funext t
        ring]
    rw [intervalIntegral.integral_const_mul]
    linear_combination
      Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) * htail m
  have hheadInt : IntervalIntegrable
      (fun t : ℝ ↦
        2 * Real.exp yoshidaEndpointA *
          Real.cosh (yoshidaEndpointA * t / 2) *
            centeredEndpointCorrelation w t) volume 0 2 := by
    apply Continuous.intervalIntegrable
    exact (by
      apply Continuous.mul
      · fun_prop
      · exact continuous_centeredEndpointCorrelation_of_continuous w hw)
  have htailInt (m : ℕ) : IntervalIntegrable
      (fun t : ℝ ↦
        2 * Real.exp
            (-2 * yoshidaEndpointA * oddRate (m + 1)) *
          Real.cosh
              (yoshidaEndpointA * oddRate (m + 1) * t) *
            centeredEndpointCorrelation w t) volume 0 2 := by
    apply Continuous.intervalIntegrable
    exact (by
      apply Continuous.mul
      · fun_prop
      · exact continuous_centeredEndpointCorrelation_of_continuous w hw)
  have htailSumInt : IntervalIntegrable
      (fun t : ℝ ↦
        ∑ m ∈ Finset.range N,
          2 * Real.exp
              (-2 * yoshidaEndpointA * oddRate (m + 1)) *
            Real.cosh
              (yoshidaEndpointA * oddRate (m + 1) * t) *
              centeredEndpointCorrelation w t) volume 0 2 := by
    rw [show (fun t : ℝ ↦
        ∑ m ∈ Finset.range N,
          2 * Real.exp
              (-2 * yoshidaEndpointA * oddRate (m + 1)) *
            Real.cosh
                (yoshidaEndpointA * oddRate (m + 1) * t) *
              centeredEndpointCorrelation w t) =
      ∑ m ∈ Finset.range N, fun t : ℝ ↦
        2 * Real.exp
            (-2 * yoshidaEndpointA * oddRate (m + 1)) *
          Real.cosh
              (yoshidaEndpointA * oddRate (m + 1) * t) *
            centeredEndpointCorrelation w t by
      funext t
      simp only [Finset.sum_apply]]
    exact IntervalIntegrable.sum (Finset.range N)
      (fun m _hm ↦ htailInt m)
  unfold factorTwoCenteredArchRankPartialSum
    factorTwoSymmetricRankPartialWeight
  rw [show (fun t : ℝ ↦
      (2 * Real.exp yoshidaEndpointA *
          Real.cosh (yoshidaEndpointA * t / 2) -
        ∑ m ∈ Finset.range N,
          2 * Real.exp
              (-2 * yoshidaEndpointA * oddRate (m + 1)) *
            Real.cosh
              (yoshidaEndpointA * oddRate (m + 1) * t)) *
        centeredEndpointCorrelation w t) =
      fun t : ℝ ↦
        2 * Real.exp yoshidaEndpointA *
            Real.cosh (yoshidaEndpointA * t / 2) *
              centeredEndpointCorrelation w t -
          ∑ m ∈ Finset.range N,
            (2 * Real.exp
                (-2 * yoshidaEndpointA * oddRate (m + 1)) *
              Real.cosh
                (yoshidaEndpointA * oddRate (m + 1) * t)) *
              centeredEndpointCorrelation w t by
        funext t
        simp only [sub_mul, Finset.sum_mul]]
  rw [intervalIntegral.integral_sub hheadInt htailSumInt,
    intervalIntegral.integral_finset_sum
      (fun m _hm ↦ htailInt m), hheadScaled]
  simp_rw [htailScaled]

/-- On an odd profile, the same finite archimedean approximation has the
opposite square signs: a negative growing sine square and positive decaying
sine squares. -/
theorem factorTwoCenteredArchRankPartialSum_eq_oddSquares
    (w : ℝ → ℝ) (hw : Continuous w) (hodd : Function.Odd w)
    (N : ℕ) :
    factorTwoCenteredArchRankPartialSum w N =
      yoshidaEndpointA *
        (-Real.exp yoshidaEndpointA *
            centeredSinhMoment w (yoshidaEndpointA / 2) ^ 2 +
          ∑ m ∈ Finset.range N,
            Real.exp
                (-2 * yoshidaEndpointA * oddRate (m + 1)) *
              centeredSinhMoment w
                (yoshidaEndpointA * oddRate (m + 1)) ^ 2) := by
  have hhead :=
    two_mul_integral_cosh_mul_centeredCorrelation_of_odd
      w hw hodd (yoshidaEndpointA / 2)
  have htail (m : ℕ) :=
    two_mul_integral_cosh_mul_centeredCorrelation_of_odd
      w hw hodd (yoshidaEndpointA * oddRate (m + 1))
  have hheadScaled :
      (∫ t : ℝ in 0..2,
        2 * Real.exp yoshidaEndpointA *
          Real.cosh (yoshidaEndpointA * t / 2) *
            centeredEndpointCorrelation w t) =
        -Real.exp yoshidaEndpointA *
          centeredSinhMoment w (yoshidaEndpointA / 2) ^ 2 := by
    rw [show (fun t : ℝ ↦
        2 * Real.exp yoshidaEndpointA *
          Real.cosh (yoshidaEndpointA * t / 2) *
            centeredEndpointCorrelation w t) =
      fun t : ℝ ↦
        (2 * Real.exp yoshidaEndpointA) *
          (Real.cosh ((yoshidaEndpointA / 2) * t) *
            centeredEndpointCorrelation w t) by
        funext t
        ring_nf]
    rw [intervalIntegral.integral_const_mul]
    linear_combination Real.exp yoshidaEndpointA * hhead
  have htailScaled (m : ℕ) :
      (∫ t : ℝ in 0..2,
        2 * Real.exp
            (-2 * yoshidaEndpointA * oddRate (m + 1)) *
          Real.cosh
              (yoshidaEndpointA * oddRate (m + 1) * t) *
            centeredEndpointCorrelation w t) =
        -Real.exp
            (-2 * yoshidaEndpointA * oddRate (m + 1)) *
          centeredSinhMoment w
            (yoshidaEndpointA * oddRate (m + 1)) ^ 2 := by
    rw [show (fun t : ℝ ↦
        2 * Real.exp
            (-2 * yoshidaEndpointA * oddRate (m + 1)) *
          Real.cosh
              (yoshidaEndpointA * oddRate (m + 1) * t) *
            centeredEndpointCorrelation w t) =
      fun t : ℝ ↦
        (2 * Real.exp
            (-2 * yoshidaEndpointA * oddRate (m + 1))) *
          (Real.cosh
              (yoshidaEndpointA * oddRate (m + 1) * t) *
            centeredEndpointCorrelation w t) by
        funext t
        ring]
    rw [intervalIntegral.integral_const_mul]
    linear_combination
      Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) * htail m
  have hheadInt : IntervalIntegrable
      (fun t : ℝ ↦
        2 * Real.exp yoshidaEndpointA *
          Real.cosh (yoshidaEndpointA * t / 2) *
            centeredEndpointCorrelation w t) volume 0 2 := by
    apply Continuous.intervalIntegrable
    exact (by
      apply Continuous.mul
      · fun_prop
      · exact continuous_centeredEndpointCorrelation_of_continuous w hw)
  have htailInt (m : ℕ) : IntervalIntegrable
      (fun t : ℝ ↦
        2 * Real.exp
            (-2 * yoshidaEndpointA * oddRate (m + 1)) *
          Real.cosh
              (yoshidaEndpointA * oddRate (m + 1) * t) *
            centeredEndpointCorrelation w t) volume 0 2 := by
    apply Continuous.intervalIntegrable
    exact (by
      apply Continuous.mul
      · fun_prop
      · exact continuous_centeredEndpointCorrelation_of_continuous w hw)
  have htailSumInt : IntervalIntegrable
      (fun t : ℝ ↦
        ∑ m ∈ Finset.range N,
          2 * Real.exp
              (-2 * yoshidaEndpointA * oddRate (m + 1)) *
            Real.cosh
              (yoshidaEndpointA * oddRate (m + 1) * t) *
              centeredEndpointCorrelation w t) volume 0 2 := by
    rw [show (fun t : ℝ ↦
        ∑ m ∈ Finset.range N,
          2 * Real.exp
              (-2 * yoshidaEndpointA * oddRate (m + 1)) *
            Real.cosh
                (yoshidaEndpointA * oddRate (m + 1) * t) *
              centeredEndpointCorrelation w t) =
      ∑ m ∈ Finset.range N, fun t : ℝ ↦
        2 * Real.exp
            (-2 * yoshidaEndpointA * oddRate (m + 1)) *
          Real.cosh
              (yoshidaEndpointA * oddRate (m + 1) * t) *
            centeredEndpointCorrelation w t by
      funext t
      simp only [Finset.sum_apply]]
    exact IntervalIntegrable.sum (Finset.range N)
      (fun m _hm ↦ htailInt m)
  unfold factorTwoCenteredArchRankPartialSum
    factorTwoSymmetricRankPartialWeight
  rw [show (fun t : ℝ ↦
      (2 * Real.exp yoshidaEndpointA *
          Real.cosh (yoshidaEndpointA * t / 2) -
        ∑ m ∈ Finset.range N,
          2 * Real.exp
              (-2 * yoshidaEndpointA * oddRate (m + 1)) *
            Real.cosh
              (yoshidaEndpointA * oddRate (m + 1) * t)) *
        centeredEndpointCorrelation w t) =
      fun t : ℝ ↦
        2 * Real.exp yoshidaEndpointA *
            Real.cosh (yoshidaEndpointA * t / 2) *
              centeredEndpointCorrelation w t -
          ∑ m ∈ Finset.range N,
            (2 * Real.exp
                (-2 * yoshidaEndpointA * oddRate (m + 1)) *
              Real.cosh
                (yoshidaEndpointA * oddRate (m + 1) * t)) *
              centeredEndpointCorrelation w t by
        funext t
        simp only [sub_mul, Finset.sum_mul]]
  rw [intervalIntegral.integral_sub hheadInt htailSumInt,
    intervalIntegral.integral_finset_sum
      (fun m _hm ↦ htailInt m), hheadScaled]
  simp_rw [htailScaled]
  simp_rw [neg_mul]
  rw [Finset.sum_neg_distrib]
  ring

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseSymmetricCoercivity

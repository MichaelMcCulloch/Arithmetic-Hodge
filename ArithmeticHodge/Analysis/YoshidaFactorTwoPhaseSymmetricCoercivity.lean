import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseEnvelope
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseTailCoercivity
import ArithmeticHodge.Analysis.EndpointParityCarleman

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

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseSymmetricCoercivity

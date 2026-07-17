import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP8ForwardKCertificateStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP8ForwardPotentialCertificateStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP8ForwardReducedRepresenterBridgeStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP67ResidualAnalyticSchurStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP67ResidualRegularDecompositionStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhasePotentialWeightedMomentGapStructural

set_option autoImplicit false

open MeasureTheory Polynomial Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP8ForwardSchurStructural

open YoshidaEndpointWeightedCauchy
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoPhaseIntrinsicHigherResidual
open YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationSharp
open YoshidaFactorTwoPhaseIntrinsicNineUnbalancedStaticDiskStructural
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFactorTwoPhaseP67ForwardHankelRepresenterStructural
open YoshidaFactorTwoPhaseP67ResidualAnalyticSchurStructural
open YoshidaFactorTwoPhaseP67ResidualPolynomialCancellationStructural
open YoshidaFactorTwoPhaseP67ResidualRegularDecompositionStructural
open YoshidaFactorTwoPhaseP8ForwardReducedRepresenterBridgeStructural
open YoshidaFactorTwoPhaseP8StructuralReserve

noncomputable section

/-!
# The three `P8` low--residual Schur cells

The symmetric analytic row and the symmetric forward-Hankel row use the
same even residual reserve, so they are combined before applying Schur.
The alternating analytic row uses ordinary odd energy.  The alternating
forward row retains its centered zero and is instead charged to endpoint
potential.  Thus adjoining `P8` creates three production cells, with
normalized weights

* `7 / 16896` for analytic plus symmetric forward against even energy;
* `1 / 132` for the alternating analytic row against odd energy;
* `17 / 528` for the alternating forward row against odd potential.

All forward-Hankel pairings below are reduced exactly.  Their degree-eight
or degree-seven polynomial parts disappear through the nine-moment gap;
no residual mode is enumerated.
-/

/-! ## Small scalar and integral helpers -/

private theorem factorTwoIntrinsicEnergy_smul_real
    (r : ℝ) (w : ℝ → ℝ) :
    factorTwoIntrinsicEnergy (r • w) =
      r ^ 2 * factorTwoIntrinsicEnergy w := by
  unfold factorTwoIntrinsicEnergy
  rw [show (fun x : ℝ ↦ (r • w) x ^ 2) =
      fun x ↦ r ^ 2 * w x ^ 2 by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul]
    ring,
    intervalIntegral.integral_const_mul]

private theorem mul_sq_le_mul_of_sq_le
    (q z Q R : ℝ) (hq : q ^ 2 ≤ Q) (hz : z ^ 2 ≤ R)
    (hQ : 0 ≤ Q) :
    (q * z) ^ 2 ≤ Q * R := by
  rw [mul_pow]
  exact mul_le_mul hq hz (sq_nonneg z) hQ

private theorem sq_intervalIntegral_mul_le
    (f g : ℝ → ℝ)
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1))
    (hg : ContinuousOn g (Icc (-1 : ℝ) 1)) :
    (∫ x : ℝ in -1..1, f x * g x) ^ 2 ≤
      (∫ x : ℝ in -1..1, f x ^ 2) *
        (∫ x : ℝ in -1..1, g x ^ 2) := by
  let μ : Measure ℝ := volume.restrict (Ioc (-1 : ℝ) 1)
  have hfMeas : AEStronglyMeasurable f μ :=
    (hf.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have hgMeas : AEStronglyMeasurable g μ :=
    (hg.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have hfLp : MemLp f 2 μ := by
    rw [memLp_two_iff_integrable_sq_norm hfMeas]
    have hcompact : IntegrableOn (fun x : ℝ ↦ ‖f x‖ ^ 2)
        (Icc (-1 : ℝ) 1) :=
      (hf.norm.pow 2).integrableOn_compact isCompact_Icc
    exact hcompact.mono_set Ioc_subset_Icc_self
  have hgLp : MemLp g 2 μ := by
    rw [memLp_two_iff_integrable_sq_norm hgMeas]
    have hcompact : IntegrableOn (fun x : ℝ ↦ ‖g x‖ ^ 2)
        (Icc (-1 : ℝ) 1) :=
      (hg.norm.pow 2).integrableOn_compact isCompact_Icc
    exact hcompact.mono_set Ioc_subset_Icc_self
  have h := sq_integral_mul_le_weighted μ (fun _ : ℝ ↦ 1) f g
    (by simp) (by simpa using hfLp) (by simpa using hgLp)
  repeat rw [intervalIntegral.integral_of_le (by norm_num)]
  simpa only [μ, div_one, one_mul] using h

/-! ## Compatibility of the independently certified reduced models -/

private abbrev factorTwoForwardKP8LowPolynomial : ℝ[X] :=
  YoshidaFactorTwoPhaseP8ForwardKCertificateStructural.factorTwoForwardKP8LowPolynomial

private abbrev factorTwoForwardKP8Certificate (x : ℝ) : ℝ :=
  YoshidaFactorTwoPhaseP8ForwardKCertificateStructural.factorTwoForwardKP8 x

private abbrev factorTwoForwardLP8PotentialCertificate (x : ℝ) : ℝ :=
  YoshidaFactorTwoPhaseP8ForwardPotentialCertificateStructural.factorTwoForwardLP8 x

private theorem factorTwoForwardKP8_eq_certificate (x : ℝ) :
    factorTwoForwardKP8 x = factorTwoForwardKP8Certificate x := by
  unfold factorTwoForwardKP8 factorTwoForwardKP8Certificate
  rw [factorTwoForwardCenteredP8_eq_factorTwoCenteredP8]
  rfl

private theorem factorTwoForwardLP8_eq_potentialCertificate (x : ℝ) :
    factorTwoForwardLP8 x = factorTwoForwardLP8PotentialCertificate x := by
  unfold factorTwoForwardLP8 factorTwoForwardLP8PotentialCertificate
  rw [factorTwoForwardCenteredP8_eq_factorTwoCenteredP8]
  rfl

/-! ## Exact reduced pairing bounds -/

/-- The actual symmetric `P8` forward-Hankel pairing has the certified
ordinary `L²` mass after its degree-eight part is canceled. -/
theorem sq_intervalIntegral_mul_factorTwoForwardHankelK_P8_le_energy
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlow : centeredLegendreMomentsVanishBelow w 9) :
    (∫ x : ℝ in -1..1,
      w x * factorTwoForwardHankelK factorTwoCenteredP8 x) ^ 2 ≤
      (1 / 4000000 : ℝ) * factorTwoIntrinsicEnergy w := by
  rw [integral_mul_factorTwoForwardHankelK_P8_eq_reduced w hw hlow]
  let R : ℝ → ℝ := fun x ↦
    factorTwoForwardKP8 x -
      factorTwoForwardKP8LowPolynomial.eval ((x + 1) / 2)
  have hRcont : ContinuousOn R (Icc (-1 : ℝ) 1) := by
    dsimp only [R]
    exact continuousOn_factorTwoForwardKP8.sub (by fun_prop)
  have hpoly :
      (∫ x : ℝ in -1..1,
        w x * factorTwoForwardKP8LowPolynomial.eval ((x + 1) / 2)) = 0 :=
    intervalIntegral_mul_shiftedPolynomial_eq_zero w hw hlow
      factorTwoForwardKP8LowPolynomial
      YoshidaFactorTwoPhaseP8ForwardKCertificateStructural.factorTwoForwardKP8LowPolynomial_natDegree_lt_nine
  have hwR : IntervalIntegrable (fun x : ℝ ↦ w x * R x)
      volume (-1) 1 :=
    (hw.continuousOn.mul hRcont).intervalIntegrable_of_Icc (by norm_num)
  have hwQ : IntervalIntegrable (fun x : ℝ ↦
      w x * factorTwoForwardKP8LowPolynomial.eval ((x + 1) / 2))
      volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hpair :
      (∫ x : ℝ in -1..1, w x * factorTwoForwardKP8 x) =
        ∫ x : ℝ in -1..1, w x * R x := by
    calc
      (∫ x : ℝ in -1..1, w x * factorTwoForwardKP8 x) =
          ∫ x : ℝ in -1..1,
            w x * R x +
              w x * factorTwoForwardKP8LowPolynomial.eval ((x + 1) / 2) := by
        apply intervalIntegral.integral_congr
        intro x _hx
        dsimp only [R]
        ring
      _ = (∫ x : ℝ in -1..1, w x * R x) +
          ∫ x : ℝ in -1..1,
            w x * factorTwoForwardKP8LowPolynomial.eval ((x + 1) / 2) := by
        rw [intervalIntegral.integral_add hwR hwQ]
      _ = _ := by rw [hpoly, add_zero]
  have hcauchy := sq_intervalIntegral_mul_le w R hw.continuousOn hRcont
  have hmass :
      (∫ x : ℝ in -1..1, R x ^ 2) ≤ (1 / 4000000 : ℝ) := by
    simpa only [R, factorTwoForwardKP8_eq_certificate] using
      YoshidaFactorTwoPhaseP8ForwardKCertificateStructural.integral_factorTwoForwardKP8_sub_lowPolynomial_sq_le
  have henergy := factorTwoIntrinsicEnergy_nonneg w
  rw [hpair]
  calc
    (∫ x : ℝ in -1..1, w x * R x) ^ 2 ≤
        factorTwoIntrinsicEnergy w *
          (∫ x : ℝ in -1..1, R x ^ 2) := by
      simpa only [factorTwoIntrinsicEnergy] using hcauchy
    _ ≤ factorTwoIntrinsicEnergy w * (1 / 4000000 : ℝ) :=
      mul_le_mul_of_nonneg_left hmass henergy
    _ = (1 / 4000000 : ℝ) * factorTwoIntrinsicEnergy w := by ring

/-- The actual alternating `P8` forward-Hankel pairing keeps the centered
factor from the reduced model and is charged to endpoint potential. -/
theorem sq_intervalIntegral_mul_factorTwoForwardHankelL_P8_le_potential
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlow : centeredLegendreMomentsVanishBelow w 9) :
    (∫ x : ℝ in -1..1,
      w x * factorTwoForwardHankelL factorTwoCenteredP8 x) ^ 2 ≤
      (1 / 100 : ℝ) * factorTwoIntrinsicPotentialEnergy w := by
  rw [integral_mul_factorTwoForwardHankelL_P8_eq_reduced w hw hlow]
  simpa only [factorTwoForwardLP8_eq_potentialCertificate] using
    YoshidaFactorTwoPhaseP8ForwardPotentialCertificateStructural.sq_intervalIntegral_mul_factorTwoForwardLP8_le_potential w hw hlow

/-! ## The three exact production cells -/

/-- Symmetric analytic and symmetric forward-Hankel contributions share
the even residual cell and must be combined before Schur. -/
def factorTwoP8ResidualEvenAnalyticKCell
    (eR : ℝ → ℝ) (c a : ℝ) : ℝ :=
  a * factorTwoP67ResidualSymmetricAnalyticBorder
      (c • factorTwoCenteredP8) eR -
    (a * c / 4) * (∫ x : ℝ in -1..1,
      eR x * factorTwoForwardHankelK factorTwoCenteredP8 x)

/-- Alternating analytic contribution against ordinary odd energy. -/
def factorTwoP8ResidualOddAnalyticCell
    (oR : ℝ → ℝ) (c b : ℝ) : ℝ :=
  (b / 2) * factorTwoP67ResidualAlternatingAnalyticBorder
    (c • factorTwoCenteredP8) oR

/-- Alternating forward-Hankel contribution against odd endpoint
potential. -/
def factorTwoP8ResidualOddForwardPotentialCell
    (oR : ℝ → ℝ) (c b : ℝ) : ℝ :=
  (b * c / 4) * (∫ x : ℝ in -1..1,
    oR x * factorTwoForwardHankelL factorTwoCenteredP8 x)

/-- The analytic plus forward-Hankel half-cross made by adjoining scaled
`P8` to the even low block. -/
def factorTwoP8ResidualCombinedForwardMixed
    (eR oR : ℝ → ℝ) (c a b : ℝ) : ℝ :=
  factorTwoP67ResidualAnalyticMixed
      (c • factorTwoCenteredP8) (0 : ℝ → ℝ) eR oR a b +
    factorTwoP67ResidualForwardHankelMixed
      (c • factorTwoCenteredP8) (0 : ℝ → ℝ) eR oR a b

@[simp] private theorem factorTwoP67ResidualSymmetricAnalyticBorder_zero_left
    (w : ℝ → ℝ) :
    factorTwoP67ResidualSymmetricAnalyticBorder (0 : ℝ → ℝ) w = 0 := by
  unfold factorTwoP67ResidualSymmetricAnalyticBorder poleFreeAnalyticError
    factorTwoCenteredCorrelationBilinear factorTwoCenteredCrossCorrelation
  simp

@[simp] private theorem factorTwoP67ResidualAlternatingAnalyticBorder_zero_right
    (w : ℝ → ℝ) :
    factorTwoP67ResidualAlternatingAnalyticBorder w (0 : ℝ → ℝ) = 0 := by
  unfold factorTwoP67ResidualAlternatingAnalyticBorder
    factorTwoP67ResidualAlternatingCrossDifference
    factorTwoCenteredCrossCorrelation
  simp

@[simp] private theorem factorTwoForwardHankelK_zero (x : ℝ) :
    factorTwoForwardHankelK (0 : ℝ → ℝ) x = 0 := by
  unfold factorTwoForwardHankelK factorTwoForwardHankelRightRepresenter
    factorTwoForwardHankelLeftRepresenter
  simp

@[simp] private theorem factorTwoForwardHankelL_zero (x : ℝ) :
    factorTwoForwardHankelL (0 : ℝ → ℝ) x = 0 := by
  unfold factorTwoForwardHankelL factorTwoForwardHankelRightRepresenter
    factorTwoForwardHankelLeftRepresenter
  simp

/-- Exact three-cell decomposition of the scaled `P8` low--residual
analytic and forward-Hankel half-cross. -/
theorem factorTwoP8ResidualCombinedForwardMixed_eq_threeCells
    (eR oR : ℝ → ℝ) (heRc : Continuous eR) (hoRc : Continuous oR)
    (c a b : ℝ) :
    factorTwoP8ResidualCombinedForwardMixed eR oR c a b =
      factorTwoP8ResidualEvenAnalyticKCell eR c a +
        factorTwoP8ResidualOddAnalyticCell oR c b +
        factorTwoP8ResidualOddForwardPotentialCell oR c b := by
  have hforward :=
    factorTwoP67ResidualForwardHankelMixed_eq_pairings
      (c • factorTwoCenteredP8) (0 : ℝ → ℝ) eR oR
      (continuous_factorTwoCenteredP8.const_smul c) (by fun_prop)
      heRc hoRc a b
  have hforwardScaled :
      factorTwoP67ResidualForwardHankelMixed
          (c • factorTwoCenteredP8) (0 : ℝ → ℝ) eR oR a b =
        -(a * c / 4) * (∫ x : ℝ in -1..1,
          eR x * factorTwoForwardHankelK factorTwoCenteredP8 x) +
        (b * c / 4) * (∫ x : ℝ in -1..1,
          oR x * factorTwoForwardHankelL factorTwoCenteredP8 x) := by
    rw [hforward]
    simp_rw [factorTwoForwardHankelK_smul,
      factorTwoForwardHankelL_smul]
    rw [show (fun x : ℝ ↦
        eR x * (c * factorTwoForwardHankelK factorTwoCenteredP8 x)) =
        fun x ↦ c *
          (eR x * factorTwoForwardHankelK factorTwoCenteredP8 x) by
      funext x
      ring,
      show (fun x : ℝ ↦
        oR x * (c * factorTwoForwardHankelL factorTwoCenteredP8 x)) =
        fun x ↦ c *
          (oR x * factorTwoForwardHankelL factorTwoCenteredP8 x) by
      funext x
      ring,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    simp
    ring
  unfold factorTwoP8ResidualCombinedForwardMixed
    factorTwoP8ResidualEvenAnalyticKCell
    factorTwoP8ResidualOddAnalyticCell
    factorTwoP8ResidualOddForwardPotentialCell
    factorTwoP67ResidualAnalyticMixed
  rw [hforwardScaled]
  simp
  ring

/-! ## Normalized cell bounds -/

/-- The symmetric analytic and `K` pieces fit together in the even-energy
cell with normalized weight `7 / 16896`. -/
theorem factorTwoP8ResidualEvenAnalyticKCell_sq_le
    (eR : ℝ → ℝ) (heRc : Continuous eR)
    (heLow : centeredLegendreMomentsVanishBelow eR 9)
    (c a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    factorTwoP8ResidualEvenAnalyticKCell eR c a ^ 2 ≤
      (7 / 16896 : ℝ) *
        ((33 / 100 : ℝ) *
          factorTwoIntrinsicEnergy factorTwoCenteredP8 * c ^ 2) *
        ((1 / 250 : ℝ) * factorTwoIntrinsicEnergy eR) := by
  let A : ℝ := a * factorTwoP67ResidualSymmetricAnalyticBorder
    (c • factorTwoCenteredP8) eR
  let F : ℝ := -(a * c / 4) * (∫ x : ℝ in -1..1,
    eR x * factorTwoForwardHankelK factorTwoCenteredP8 x)
  let E8 : ℝ := factorTwoIntrinsicEnergy factorTwoCenteredP8
  let Ee : ℝ := factorTwoIntrinsicEnergy eR
  have ha : a ^ 2 ≤ 1 := by nlinarith [sq_nonneg b]
  have hEe : 0 ≤ Ee := by
    dsimp only [Ee]
    exact factorTwoIntrinsicEnergy_nonneg eR
  have hscaledEnergy :
      factorTwoIntrinsicEnergy (c • factorTwoCenteredP8) = c ^ 2 * E8 := by
    simpa only [E8] using
      factorTwoIntrinsicEnergy_smul_real c factorTwoCenteredP8
  have hsym :=
    factorTwoP67ResidualSymmetricAnalyticBorder_sq_le_energy_mul
      (c • factorTwoCenteredP8) eR
      (continuous_factorTwoCenteredP8.const_smul c) heRc
  rw [hscaledEnergy] at hsym
  have hA : A ^ 2 ≤
      (9 / 64000000 : ℝ) * (c ^ 2 * E8) * Ee := by
    have hmul := mul_sq_le_mul_of_sq_le a
      (factorTwoP67ResidualSymmetricAnalyticBorder
        (c • factorTwoCenteredP8) eR)
      1 ((9 / 64000000 : ℝ) * (c ^ 2 * E8) * Ee)
      ha hsym (by norm_num)
    simpa only [A, Ee, one_mul] using hmul
  have hK := sq_intervalIntegral_mul_factorTwoForwardHankelK_P8_le_energy
    eR heRc heLow
  have hac : (-(a * c / 4)) ^ 2 ≤ (1 / 16 : ℝ) * c ^ 2 := by
    have h := mul_le_mul_of_nonneg_right ha (sq_nonneg c)
    calc
      (-(a * c / 4)) ^ 2 = (1 / 16 : ℝ) * (a ^ 2 * c ^ 2) := by ring
      _ ≤ (1 / 16 : ℝ) * (1 * c ^ 2) :=
        mul_le_mul_of_nonneg_left h (by norm_num)
      _ = (1 / 16 : ℝ) * c ^ 2 := by ring
  have hF : F ^ 2 ≤
      ((1 / 16 : ℝ) * c ^ 2) * ((1 / 4000000 : ℝ) * Ee) := by
    exact mul_sq_le_mul_of_sq_le _ _ _ _ hac (by simpa only [Ee] using hK)
      (by positivity)
  have hsum : (A + F) ^ 2 ≤ 2 * A ^ 2 + 2 * F ^ 2 := by
    nlinarith [sq_nonneg (A - F)]
  calc
    factorTwoP8ResidualEvenAnalyticKCell eR c a ^ 2 = (A + F) ^ 2 := by
      dsimp only [factorTwoP8ResidualEvenAnalyticKCell, A, F]
      ring
    _ ≤ 2 * A ^ 2 + 2 * F ^ 2 := hsum
    _ ≤ 2 * ((9 / 64000000 : ℝ) * (c ^ 2 * E8) * Ee) +
        2 * (((1 / 16 : ℝ) * c ^ 2) *
          ((1 / 4000000 : ℝ) * Ee)) := by nlinarith
    _ = (7 / 16896 : ℝ) *
        ((33 / 100 : ℝ) *
          factorTwoIntrinsicEnergy factorTwoCenteredP8 * c ^ 2) *
        ((1 / 250 : ℝ) * factorTwoIntrinsicEnergy eR) := by
      dsimp only [E8, Ee]
      rw [factorTwoCenteredP8_energy]
      ring

/-- The alternating analytic `P8` row has normalized weight `1 / 132`
against the ordinary odd-energy reserve. -/
theorem factorTwoP8ResidualOddAnalyticCell_sq_le
    (oR : ℝ → ℝ) (hoRc : Continuous oR) (hoRo : Function.Odd oR)
    (c a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    factorTwoP8ResidualOddAnalyticCell oR c b ^ 2 ≤
      (1 / 132 : ℝ) *
        ((33 / 100 : ℝ) *
          factorTwoIntrinsicEnergy factorTwoCenteredP8 * c ^ 2) *
        ((1 / 2500 : ℝ) * factorTwoIntrinsicEnergy oR) := by
  let E8 : ℝ := factorTwoIntrinsicEnergy factorTwoCenteredP8
  let Eo : ℝ := factorTwoIntrinsicEnergy oR
  have hb : b ^ 2 ≤ 1 := by nlinarith [sq_nonneg a]
  have hscaledEnergy :
      factorTwoIntrinsicEnergy (c • factorTwoCenteredP8) = c ^ 2 * E8 := by
    simpa only [E8] using
      factorTwoIntrinsicEnergy_smul_real c factorTwoCenteredP8
  have halt :=
    factorTwoP67ResidualAlternatingAnalyticBorder_sq_le_energy_mul
      (c • factorTwoCenteredP8) oR
      (continuous_factorTwoCenteredP8.const_smul c) hoRc
      (even_factorTwoCenteredP8.const_smul c) hoRo
  rw [hscaledEnergy] at halt
  have hbquarter : (b / 2) ^ 2 ≤ (1 / 4 : ℝ) := by nlinarith
  have hcell := mul_sq_le_mul_of_sq_le (b / 2)
    (factorTwoP67ResidualAlternatingAnalyticBorder
      (c • factorTwoCenteredP8) oR)
    (1 / 4 : ℝ) ((1 / 250000 : ℝ) * (c ^ 2 * E8) * Eo)
    hbquarter halt (by norm_num)
  calc
    factorTwoP8ResidualOddAnalyticCell oR c b ^ 2 ≤
        (1 / 4 : ℝ) *
          ((1 / 250000 : ℝ) * (c ^ 2 * E8) * Eo) := by
      simpa only [factorTwoP8ResidualOddAnalyticCell, Eo] using hcell
    _ = (1 / 132 : ℝ) *
        ((33 / 100 : ℝ) *
          factorTwoIntrinsicEnergy factorTwoCenteredP8 * c ^ 2) *
        ((1 / 2500 : ℝ) * factorTwoIntrinsicEnergy oR) := by
      dsimp only [E8, Eo]
      rw [factorTwoCenteredP8_energy]
      ring

/-- The alternating forward `P8` row has normalized weight `17 / 528`
against half the odd endpoint-potential energy. -/
theorem factorTwoP8ResidualOddForwardPotentialCell_sq_le
    (oR : ℝ → ℝ) (hoRc : Continuous oR)
    (hoLow : centeredLegendreMomentsVanishBelow oR 9)
    (c a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    factorTwoP8ResidualOddForwardPotentialCell oR c b ^ 2 ≤
      (17 / 528 : ℝ) *
        ((33 / 100 : ℝ) *
          factorTwoIntrinsicEnergy factorTwoCenteredP8 * c ^ 2) *
        ((1 / 2 : ℝ) * factorTwoIntrinsicPotentialEnergy oR) := by
  let E8 : ℝ := factorTwoIntrinsicEnergy factorTwoCenteredP8
  let Po : ℝ := factorTwoIntrinsicPotentialEnergy oR
  have hb : b ^ 2 ≤ 1 := by nlinarith [sq_nonneg a]
  have hL := sq_intervalIntegral_mul_factorTwoForwardHankelL_P8_le_potential
    oR hoRc hoLow
  have hbc : (b * c / 4) ^ 2 ≤ (1 / 16 : ℝ) * c ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hb (sq_nonneg c)
    calc
      (b * c / 4) ^ 2 = (1 / 16 : ℝ) * (b ^ 2 * c ^ 2) := by ring
      _ ≤ (1 / 16 : ℝ) * (1 * c ^ 2) :=
        mul_le_mul_of_nonneg_left h (by norm_num)
      _ = (1 / 16 : ℝ) * c ^ 2 := by ring
  have hcell := mul_sq_le_mul_of_sq_le (b * c / 4)
    (∫ x : ℝ in -1..1,
      oR x * factorTwoForwardHankelL factorTwoCenteredP8 x)
    ((1 / 16 : ℝ) * c ^ 2) ((1 / 100 : ℝ) * Po)
    hbc (by simpa only [Po] using hL) (by positivity)
  calc
    factorTwoP8ResidualOddForwardPotentialCell oR c b ^ 2 ≤
        ((1 / 16 : ℝ) * c ^ 2) * ((1 / 100 : ℝ) * Po) := by
      simpa only [factorTwoP8ResidualOddForwardPotentialCell] using hcell
    _ = (17 / 528 : ℝ) *
        ((33 / 100 : ℝ) *
          factorTwoIntrinsicEnergy factorTwoCenteredP8 * c ^ 2) *
        ((1 / 2 : ℝ) * factorTwoIntrinsicPotentialEnergy oR) := by
      dsimp only [Po]
      rw [factorTwoCenteredP8_energy]
      ring

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP8ForwardSchurStructural

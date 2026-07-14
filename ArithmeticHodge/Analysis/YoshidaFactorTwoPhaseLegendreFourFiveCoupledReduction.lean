import ArithmeticHodge.Analysis.YoshidaEndpointOddLowGramExpansion
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseArchRankDiskSchur
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCoupledCleanReduction
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseLegendreFourFiveStructural

set_option autoImplicit false

open MeasureTheory Real

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseLegendreFourFiveCoupledReduction

noncomputable section

open YoshidaEndpointOddLowGramExpansion
open YoshidaEndpointOddCleanPositive
open YoshidaFactorTwoEndpointChannelRadius
open YoshidaFactorTwoPhaseArchRankDiskSchur
open YoshidaFactorTwoPhaseCoupledCleanReduction
open YoshidaFactorTwoPhaseCoupledRankLimit
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseSymmetricCoercivity

/-!
# Coupled reduction for the first middle Legendre pair

The two scalar rank-energy estimates are the only analytic inputs left for
the `P₄/P₅` phase disk.  Homogeneity, the strict retained-prime mass bound,
and the clean diagonal reserves then give the complete coupled domination.
-/

/-- Scalar `3/20` rank bounds on `P₄` and `P₅` imply full phase positivity
for every independent rescaling of the pair. -/
theorem factorTwoEndpointChannelPhase_P4_P5_nonneg_of_rank_bounds
    (hRank4 : factorTwoEvenRankEnergy factorTwoCenteredP4 ≤
      (3 / 20 : ℝ) * factorTwoIntrinsicEnergy factorTwoCenteredP4)
    (hRank5 : factorTwoOddRankEnergy factorTwoCenteredP5 ≤
      (3 / 20 : ℝ) * factorTwoIntrinsicEnergy factorTwoCenteredP5)
    (c d a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    0 ≤ factorTwoEndpointChannelPhase
      (fun x ↦ c * factorTwoCenteredP4 x)
      (fun x ↦ d * factorTwoCenteredP5 x) a b := by
  let e : ℝ → ℝ := c • factorTwoCenteredP4
  let o : ℝ → ℝ := d • factorTwoCenteredP5
  have hec : Continuous e := by
    dsimp only [e]
    exact continuous_factorTwoCenteredP4.const_smul c
  have hoc : Continuous o := by
    dsimp only [o]
    exact continuous_factorTwoCenteredP5.const_smul d
  have heven : Function.Even e := by
    intro x
    dsimp only [e]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [even_factorTwoCenteredP4 x]
  have hodd : Function.Odd o := by
    intro x
    dsimp only [o]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [odd_factorTwoCenteredP5 x]
    ring
  have henergy_smul (r : ℝ) (w : ℝ → ℝ) :
      factorTwoIntrinsicEnergy (r • w) =
        r ^ 2 * factorTwoIntrinsicEnergy w := by
    unfold factorTwoIntrinsicEnergy
    rw [show (fun x : ℝ ↦ (r • w) x ^ 2) =
        fun x ↦ r ^ 2 * w x ^ 2 by
      funext x
      simp only [Pi.smul_apply, smul_eq_mul]
      ring,
      intervalIntegral.integral_const_mul]
  have hclean_smul (r : ℝ) (w : ℝ → ℝ) :
      yoshidaEndpointOddCleanQuadratic (r • w) =
        r ^ 2 * yoshidaEndpointOddCleanQuadratic w := by
    simpa only [Pi.smul_apply, smul_eq_mul] using
      yoshidaEndpointOddCleanQuadratic_const_mul w r
  have heEnergy := factorTwoIntrinsicEnergy_nonneg e
  have hoEnergy := factorTwoIntrinsicEnergy_nonneg o
  have hRankE : factorTwoEvenRankEnergy e ≤
      (3 / 20 : ℝ) * factorTwoIntrinsicEnergy e := by
    calc
      factorTwoEvenRankEnergy e =
          c ^ 2 * factorTwoEvenRankEnergy factorTwoCenteredP4 := by
        dsimp only [e]
        exact factorTwoEvenRankEnergy_smul c factorTwoCenteredP4
      _ ≤ c ^ 2 *
          ((3 / 20 : ℝ) * factorTwoIntrinsicEnergy factorTwoCenteredP4) :=
        mul_le_mul_of_nonneg_left hRank4 (sq_nonneg c)
      _ = (3 / 20 : ℝ) * factorTwoIntrinsicEnergy e := by
        dsimp only [e]
        rw [henergy_smul c factorTwoCenteredP4]
        ring
  have hRankO : factorTwoOddRankEnergy o ≤
      (3 / 20 : ℝ) * factorTwoIntrinsicEnergy o := by
    calc
      factorTwoOddRankEnergy o =
          d ^ 2 * factorTwoOddRankEnergy factorTwoCenteredP5 := by
        dsimp only [o]
        exact factorTwoOddRankEnergy_smul d factorTwoCenteredP5
      _ ≤ d ^ 2 *
          ((3 / 20 : ℝ) * factorTwoIntrinsicEnergy factorTwoCenteredP5) :=
        mul_le_mul_of_nonneg_left hRank5 (sq_nonneg d)
      _ = (3 / 20 : ℝ) * factorTwoIntrinsicEnergy o := by
        dsimp only [o]
        rw [henergy_smul d factorTwoCenteredP5]
        ring
  have hCleanE : (23 / 20 : ℝ) * factorTwoIntrinsicEnergy e ≤
      yoshidaEndpointOddCleanQuadratic e := by
    calc
      _ = c ^ 2 * ((23 / 20 : ℝ) *
          factorTwoIntrinsicEnergy factorTwoCenteredP4) := by
        dsimp only [e]
        rw [henergy_smul c factorTwoCenteredP4]
        ring
      _ ≤ c ^ 2 * yoshidaEndpointOddCleanQuadratic factorTwoCenteredP4 :=
        mul_le_mul_of_nonneg_left
          twenty_three_twentieths_energy_le_clean_P4 (sq_nonneg c)
      _ = _ := by
        dsimp only [e]
        rw [hclean_smul c factorTwoCenteredP4]
  have hCleanO : (4 / 3 : ℝ) * factorTwoIntrinsicEnergy o ≤
      yoshidaEndpointOddCleanQuadratic o := by
    calc
      _ = d ^ 2 * ((4 / 3 : ℝ) *
          factorTwoIntrinsicEnergy factorTwoCenteredP5) := by
        dsimp only [o]
        rw [henergy_smul d factorTwoCenteredP5]
        ring
      _ ≤ d ^ 2 * yoshidaEndpointOddCleanQuadratic factorTwoCenteredP5 :=
        mul_le_mul_of_nonneg_left four_thirds_energy_le_clean_P5 (sq_nonneg d)
      _ = _ := by
        dsimp only [o]
        rw [hclean_smul d factorTwoCenteredP5]
  have hCleanO' : (23 / 20 : ℝ) * factorTwoIntrinsicEnergy o ≤
      yoshidaEndpointOddCleanQuadratic o := by
    have hcoeff : (23 / 20 : ℝ) * factorTwoIntrinsicEnergy o ≤
        (4 / 3 : ℝ) * factorTwoIntrinsicEnergy o := by
      nlinarith
    exact hcoeff.trans hCleanO
  have hRank : factorTwoCoupledRankEnergy e o ≤
      (3 / 20 : ℝ) *
        (factorTwoIntrinsicEnergy e + factorTwoIntrinsicEnergy o) := by
    calc
      _ = factorTwoEvenRankEnergy e + factorTwoOddRankEnergy o :=
        factorTwoCoupledRankEnergy_eq_even_add_odd e o hec hoc heven hodd
      _ ≤ (3 / 20 : ℝ) * factorTwoIntrinsicEnergy e +
          (3 / 20 : ℝ) * factorTwoIntrinsicEnergy o :=
        add_le_add hRankE hRankO
      _ = _ := by ring
  have hBudget : factorTwoCoupledPrimeMassBudget e o ≤
      factorTwoIntrinsicEnergy e + factorTwoIntrinsicEnergy o := by
    have hmass : 0 ≤
        factorTwoIntrinsicEnergy e + factorTwoIntrinsicEnergy o :=
      add_nonneg heEnergy hoEnergy
    unfold factorTwoCoupledPrimeMassBudget factorTwoIntrinsicEnergy at hmass ⊢
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right primeBlock_upperCoefficient_lt_one.le hmass
  have hdom : factorTwoCoupledRankEnergy e o +
      factorTwoCoupledPrimeMassBudget e o ≤
        factorTwoEndpointChannelCleanSum e o := by
    calc
      _ ≤ (3 / 20 : ℝ) *
            (factorTwoIntrinsicEnergy e + factorTwoIntrinsicEnergy o) +
          (factorTwoIntrinsicEnergy e + factorTwoIntrinsicEnergy o) :=
        add_le_add hRank hBudget
      _ = (23 / 20 : ℝ) * factorTwoIntrinsicEnergy e +
          (23 / 20 : ℝ) * factorTwoIntrinsicEnergy o := by ring
      _ ≤ yoshidaEndpointOddCleanQuadratic e +
          yoshidaEndpointOddCleanQuadratic o :=
        add_le_add hCleanE hCleanO'
      _ = factorTwoEndpointChannelCleanSum e o := by rfl
  have hphase :=
    factorTwoEndpointChannelPhase_nonneg_of_coupledRank_domination
      e o hec hoc heven hodd hdom a b hab
  simpa only [e, o, Pi.smul_apply, smul_eq_mul] using hphase

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseLegendreFourFiveCoupledReduction

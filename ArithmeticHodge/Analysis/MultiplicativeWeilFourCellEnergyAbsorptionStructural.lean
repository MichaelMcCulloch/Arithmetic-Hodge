import ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneCellEnergyFrameStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneFourCellPrimeGeometryStructural
import ArithmeticHodge.Analysis.YoshidaCriticalLogCorrelation
import ArithmeticHodge.Analysis.YoshidaEndpointQuarticObstruction

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.MultiplicativeWeilFourCellEnergyAbsorptionStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilBelowThreePrimeReductionStructural
open MultiplicativeWeilMinimalNegativeBlockStructural
open MultiplicativeWeilMonotoneCellEnergyFrameStructural
open MultiplicativeWeilMonotoneFourCellPrimeGeometryStructural
open MultiplicativeWeilMonotoneLocalFullCoercivityStructural
open MultiplicativeWeilMonotoneQuarterPartitionStructural
open MultiplicativeWeilQuarterLogLatticePartitionStructural
open MultiplicativeWeilRealCutPhaseReductionStructural
open YoshidaCriticalLogCorrelation
open YoshidaEndpointQuarticObstruction

/-!
# Energy absorption for the four-cell prime-two term

The complementary endpoint mask localizes the sole prime term of four
consecutive monotone cells.  This module compares that term with the critical
logarithmic energies of the two ratio-two halves and records the exact
coercivity constant required for diagonal absorption.
-/

/-- The critical logarithmic norm is exactly ordinary physical `L²(dx)` on
the positive half-line. -/
theorem bombieriCriticalLogEnergy_eq_integral_Ioi_norm_sq
    (g : BombieriTest) :
    bombieriCriticalLogEnergy g =
      ∫ x : ℝ in Set.Ioi 0, ‖g x‖ ^ 2 := by
  have hchange := integral_Ioi_eq_integral_expNeg_mul
    (fun x : ℝ ↦ ((‖g x‖ ^ 2 : ℝ) : ℂ))
  have hleft :
      (∫ x : ℝ in Set.Ioi 0, ((‖g x‖ ^ 2 : ℝ) : ℂ)) =
        ((∫ x : ℝ in Set.Ioi 0, ‖g x‖ ^ 2 : ℝ) : ℂ) := by
    exact integral_complex_ofReal
  have hright :
      (∫ u : ℝ,
          ((Real.exp (-u) : ℝ) : ℂ) * ((‖g (Real.exp (-u))‖ ^ 2 : ℝ) : ℂ)) =
        ((∫ u : ℝ, Real.exp (-u) * ‖g (Real.exp (-u))‖ ^ 2 : ℝ) : ℂ) := by
    calc
      (∫ u : ℝ,
          ((Real.exp (-u) : ℝ) : ℂ) *
            ((‖g (Real.exp (-u))‖ ^ 2 : ℝ) : ℂ)) =
          ∫ u : ℝ,
            ((Real.exp (-u) * ‖g (Real.exp (-u))‖ ^ 2 : ℝ) : ℂ) := by
        apply integral_congr_ae
        filter_upwards [] with u
        rw [Complex.ofReal_mul]
      _ = _ := integral_complex_ofReal
  rw [hleft, hright] at hchange
  have hchangeReal :
      (∫ x : ℝ in Set.Ioi 0, ‖g x‖ ^ 2) =
        ∫ u : ℝ, Real.exp (-u) * ‖g (Real.exp (-u))‖ ^ 2 := by
    exact_mod_cast hchange
  unfold bombieriCriticalLogEnergy
  calc
    (∫ u : ℝ, ‖g.logarithmicPullbackSchwartz (1 / 2) u‖ ^ 2) =
        ∫ u : ℝ, Real.exp (-u) * ‖g (Real.exp (-u))‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [] with u
      simp only [BombieriTest.logarithmicPullbackSchwartz_apply,
        BombieriTest.logarithmicPullback, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      rw [mul_pow]
      rw [show Real.exp (-(1 / 2) * u) ^ 2 = Real.exp (-u) by
        rw [← Real.exp_nat_mul]; congr 1; ring]
    _ = ∫ x : ℝ in Set.Ioi 0, ‖g x‖ ^ 2 := hchangeReal.symm

theorem bombieriCriticalLogEnergy_nonnegative (g : BombieriTest) :
    0 ≤ bombieriCriticalLogEnergy g := by
  rw [bombieriCriticalLogEnergy_eq_integral_Ioi_norm_sq]
  exact integral_nonneg fun x ↦ sq_nonneg ‖g x‖

private theorem physicalNormSq_integrable (g : BombieriTest) :
    Integrable (fun x : ℝ ↦ ‖g x‖ ^ 2) := by
  have hcont : Continuous (fun x : ℝ ↦ ‖g x‖ ^ 2) := by fun_prop
  have hcompact : HasCompactSupport (fun x : ℝ ↦ ‖g x‖ ^ 2) := by
    simpa only [pow_two] using g.hasCompactSupport.norm.mul_left
      (f := fun x : ℝ ↦ ‖g x‖)
  exact hcont.integrable_of_hasCompactSupport hcompact

private theorem integral_Ioi_norm_sq_two_mul
    (g : BombieriTest) :
    (∫ x : ℝ in Set.Ioi 0, ‖g (2 * x)‖ ^ 2) =
      (1 / 2 : ℝ) * bombieriCriticalLogEnergy g := by
  have hscale := integral_comp_mul_left_Ioi
    (fun x : ℝ ↦ ‖g x‖ ^ 2) 0 (by norm_num : (0 : ℝ) < 2)
  rw [mul_zero] at hscale
  rw [bombieriCriticalLogEnergy_eq_integral_Ioi_norm_sq]
  simpa only [one_div, smul_eq_mul] using hscale

private theorem fourCellLeftHalf_eq_cutoff_sub
    (parent : BombieriTest) (k : ℤ) :
    monotoneQuarterFiniteBlock parent k 0 2 =
      monotoneQuarterCutoff parent k -
        monotoneQuarterCutoff parent (k + 2) := by
  simpa [monotoneQuarterFiniteBlock] using
    sum_range_monotoneQuarterCell_eq_cutoff_sub parent k 2

private theorem fourCellRightHalf_eq_cutoff_sub
    (parent : BombieriTest) (k : ℤ) :
    monotoneQuarterFiniteBlock parent k 2 2 =
      monotoneQuarterCutoff parent (k + 2) -
        monotoneQuarterCutoff parent (k + 4) := by
  simpa [monotoneQuarterFiniteBlock, Nat.cast_add, add_assoc] using
    sum_range_monotoneQuarterCell_eq_cutoff_sub parent (k + 2) 2

private theorem fourCellLeftHalf_apply_firstTransition
    (parent : BombieriTest) (k : ℤ) {x : ℝ}
    (hx : x ∈ Set.Icc (quarterLogLatticePoint k)
      (quarterLogLatticePoint (k + 1))) :
    monotoneQuarterFiniteBlock parent k 0 2 x =
      ((monotoneQuarterStep k x : ℝ) : ℂ) * parent x := by
  rw [fourCellLeftHalf_eq_cutoff_sub]
  simp only [TestFunction.coe_sub, Pi.sub_apply,
    monotoneQuarterCutoff_apply]
  rw [monotoneQuarterStep_eq_zero_of_le (k + 2)
    (hx.2.trans (quarterLogLatticePoint_mono (by omega)))]
  simp

private theorem fourCellRightHalf_apply_two_mul_firstTransition
    (parent : BombieriTest) (k : ℤ) {x : ℝ}
    (hx : x ∈ Set.Icc (quarterLogLatticePoint k)
      (quarterLogLatticePoint (k + 1))) :
    monotoneQuarterFiniteBlock parent k 2 2 (2 * x) =
      (((1 - monotoneQuarterStep k x : ℝ) : ℂ) * parent (2 * x)) := by
  rw [fourCellRightHalf_eq_cutoff_sub]
  simp only [TestFunction.coe_sub, Pi.sub_apply,
    monotoneQuarterCutoff_apply]
  rw [monotoneQuarterStep_eq_one_of_le (k + 2)]
  · rw [monotoneQuarterStep_add_four_two_mul]
    push_cast
    ring
  · calc
      quarterLogLatticePoint (k + 2 + 1) ≤
          quarterLogLatticePoint (k + 4) :=
        quarterLogLatticePoint_mono (by omega)
      _ = 2 * quarterLogLatticePoint k := by
        rw [quarterLogLatticePoint_add_four]
      _ ≤ 2 * x := mul_le_mul_of_nonneg_left hx.1 (by norm_num)

/-- The complementary-mask prime cross has the sharp energy bound obtained by
factor-two scaling and the optimally balanced Young inequality. -/
theorem norm_fourCell_halfCross_le_energySum
    (parent : BombieriTest) (k : ℤ) :
    ‖bombieriQuadraticCrossTest
        (monotoneQuarterFiniteBlock parent k 0 2)
        (monotoneQuarterFiniteBlock parent k 2 2) 2‖ ≤
      (Real.sqrt 2 / 4) *
        (bombieriCriticalLogEnergy
            (monotoneQuarterFiniteBlock parent k 0 2) +
          bombieriCriticalLogEnergy
            (monotoneQuarterFiniteBlock parent k 2 2)) := by
  let f : BombieriTest := monotoneQuarterFiniteBlock parent k 0 2
  let g : BombieriTest := monotoneQuarterFiniteBlock parent k 2 2
  let I : Set ℝ := Set.Icc (quarterLogLatticePoint k)
    (quarterLogLatticePoint (k + 1))
  have hsubset : I ⊆ Set.Ioi (0 : ℝ) := by
    intro x hx
    exact (quarterLogLatticePoint_pos k).trans_le hx.1
  have hcross :
      bombieriQuadraticCrossTest f g 2 =
        ∫ x : ℝ in I, g (2 * x) * starRingEnd ℂ (f x) := by
    rw [show bombieriQuadraticCrossTest f g 2 =
        ∫ x : ℝ in I,
          ((monotoneQuarterStep k x *
            (1 - monotoneQuarterStep k x) : ℝ) : ℂ) *
              parent (2 * x) * starRingEnd ℂ (parent x) by
      simpa only [f, g, I] using
        fourCell_halfCross_eq_complementaryMaskIntegral parent k]
    apply setIntegral_congr_fun measurableSet_Icc
    intro x hx
    dsimp only [f, g]
    rw [fourCellLeftHalf_apply_firstTransition parent k hx,
      fourCellRightHalf_apply_two_mul_firstTransition parent k hx]
    rw [map_mul (starRingEnd ℂ), Complex.conj_ofReal]
    push_cast
    ring
  have hproductInt : IntegrableOn
      (fun x : ℝ ↦ ‖g (2 * x)‖ * ‖f x‖) I := by
    exact (by fun_prop : Continuous
      (fun x : ℝ ↦ ‖g (2 * x)‖ * ‖f x‖)).continuousOn
        |>.integrableOn_compact isCompact_Icc
  have hmajorInt : IntegrableOn
      (fun x : ℝ ↦
        Real.sqrt 2 / 2 * ‖g (2 * x)‖ ^ 2 +
          Real.sqrt 2 / 4 * ‖f x‖ ^ 2) I := by
    exact (by fun_prop : Continuous
      (fun x : ℝ ↦
        Real.sqrt 2 / 2 * ‖g (2 * x)‖ ^ 2 +
          Real.sqrt 2 / 4 * ‖f x‖ ^ 2)).continuousOn
        |>.integrableOn_compact isCompact_Icc
  have hgSqInt : IntegrableOn (fun x : ℝ ↦ ‖g (2 * x)‖ ^ 2) I := by
    exact (by fun_prop : Continuous (fun x : ℝ ↦ ‖g (2 * x)‖ ^ 2)).continuousOn
      |>.integrableOn_compact isCompact_Icc
  have hfSqInt : IntegrableOn (fun x : ℝ ↦ ‖f x‖ ^ 2) I := by
    exact (by fun_prop : Continuous (fun x : ℝ ↦ ‖f x‖ ^ 2)).continuousOn
      |>.integrableOn_compact isCompact_Icc
  have hyoung (x : ℝ) :
      ‖g (2 * x)‖ * ‖f x‖ ≤
        Real.sqrt 2 / 2 * ‖g (2 * x)‖ ^ 2 +
          Real.sqrt 2 / 4 * ‖f x‖ ^ 2 := by
    have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hinv : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by
      apply (mul_left_cancel₀ hspos.ne')
      rw [mul_inv_cancel₀ hspos.ne']
      nlinarith
    have hy := two_mul_le_add_mul_sq
      (a := ‖g (2 * x)‖) (b := ‖f x‖) hspos
    rw [hinv] at hy
    nlinarith
  have hfLocal :
      (∫ x : ℝ in I, ‖f x‖ ^ 2) ≤ bombieriCriticalLogEnergy f := by
    rw [bombieriCriticalLogEnergy_eq_integral_Ioi_norm_sq]
    exact setIntegral_mono_set (physicalNormSq_integrable f).integrableOn
      (Filter.Eventually.of_forall fun x ↦ sq_nonneg ‖f x‖)
      (Filter.Eventually.of_forall fun x hx ↦ hsubset hx)
  have hgLocal :
      (∫ x : ℝ in I, ‖g (2 * x)‖ ^ 2) ≤
        (1 / 2 : ℝ) * bombieriCriticalLogEnergy g := by
    calc
      (∫ x : ℝ in I, ‖g (2 * x)‖ ^ 2) ≤
          ∫ x : ℝ in Set.Ioi 0, ‖g (2 * x)‖ ^ 2 := by
        exact setIntegral_mono_set
          ((physicalNormSq_integrable g).comp_mul_left' (by norm_num)).integrableOn
          (Filter.Eventually.of_forall fun x ↦ sq_nonneg ‖g (2 * x)‖)
          (Filter.Eventually.of_forall fun x hx ↦ hsubset hx)
      _ = (1 / 2 : ℝ) * bombieriCriticalLogEnergy g :=
        integral_Ioi_norm_sq_two_mul g
  rw [hcross]
  calc
    ‖∫ x : ℝ in I, g (2 * x) * starRingEnd ℂ (f x)‖ ≤
        ∫ x : ℝ in I, ‖g (2 * x) * starRingEnd ℂ (f x)‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ x : ℝ in I, ‖g (2 * x)‖ * ‖f x‖ := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [norm_mul, Complex.norm_conj]
    _ ≤ ∫ x : ℝ in I,
        (Real.sqrt 2 / 2 * ‖g (2 * x)‖ ^ 2 +
          Real.sqrt 2 / 4 * ‖f x‖ ^ 2) := by
      exact integral_mono_ae hproductInt hmajorInt
        (Filter.Eventually.of_forall hyoung)
    _ = Real.sqrt 2 / 2 * (∫ x : ℝ in I, ‖g (2 * x)‖ ^ 2) +
        Real.sqrt 2 / 4 * (∫ x : ℝ in I, ‖f x‖ ^ 2) := by
      rw [integral_add, integral_const_mul, integral_const_mul]
      · exact hgSqInt.const_mul _
      · exact hfSqInt.const_mul _
    _ ≤ Real.sqrt 2 / 2 *
          ((1 / 2 : ℝ) * bombieriCriticalLogEnergy g) +
        Real.sqrt 2 / 4 * bombieriCriticalLogEnergy f := by
      gcongr
    _ = (Real.sqrt 2 / 4) *
        (bombieriCriticalLogEnergy f + bombieriCriticalLogEnergy g) := by ring

/-- Exact energy coefficient paid by the unique four-cell prime-two term. -/
def fourCellPrimeEnergyCoefficient : ℝ :=
  Real.sqrt 2 * Real.log 2 / 2

theorem fourCellPrimeEnergyCoefficient_eq_log_two_div_sqrt_two :
    fourCellPrimeEnergyCoefficient = Real.log 2 / Real.sqrt 2 := by
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  unfold fourCellPrimeEnergyCoefficient
  field_simp [hspos.ne']
  nlinarith

/-- Quantitative coercivity transported from the endpoint crop to the local
critical diagonal of any conjugation-fixed ratio-two test. -/
theorem real_ratioTwo_localCriticalForm_re_ge_criticalLogEnergy
    (g : BombieriTest)
    (hcell : BombieriRatioTwoCell g)
    (hreal : bombieriConjugateTest g = g) :
    (1 / 12000 : ℝ) * bombieriCriticalLogEnergy g ≤
      (bombieriLocalCriticalForm g g).re := by
  obtain ⟨l, r, hl, hlr, hsupport, hratio⟩ := hcell
  have hcoercive :=
    bombieriFunctional_quadratic_re_ge_centeredCropEnergy_of_ratio_le_two
      g hl hlr hsupport hratio hreal
  rw [bombieriCenteredCropEnergy_eq_criticalLogEnergy_of_ratio_le_two
      g hl hlr hsupport hratio,
    bombieriFunctional_quadratic_eq_bombieriLocalCriticalForm_le_two
      g hl hlr hsupport hratio] at hcoercive
  exact hcoercive

/-- Both two-cell halves inherit the explicit `1 / 12000` local diagonal
coercivity from a real common parent. -/
theorem fourCellHalfLocalDiagonals_ge_criticalLogEnergy
    (parent : BombieriTest)
    (hreal : bombieriConjugateTest parent = parent)
    (k : ℤ) :
    (1 / 12000 : ℝ) * bombieriCriticalLogEnergy
          (monotoneQuarterFiniteBlock parent k 0 2) ≤
        (bombieriLocalCriticalForm
          (monotoneQuarterFiniteBlock parent k 0 2)
          (monotoneQuarterFiniteBlock parent k 0 2)).re ∧
      (1 / 12000 : ℝ) * bombieriCriticalLogEnergy
          (monotoneQuarterFiniteBlock parent k 2 2) ≤
        (bombieriLocalCriticalForm
          (monotoneQuarterFiniteBlock parent k 2 2)
          (monotoneQuarterFiniteBlock parent k 2 2)).re := by
  constructor
  · apply real_ratioTwo_localCriticalForm_re_ge_criticalLogEnergy
    · exact monotoneQuarterFiniteBlock_ratioTwo_of_le_three
        parent k 0 2 (by omega)
    · exact bombieriConjugateTest_monotoneQuarterFiniteBlock
        parent hreal k 0 2
  · apply real_ratioTwo_localCriticalForm_re_ge_criticalLogEnergy
    · exact monotoneQuarterFiniteBlock_ratioTwo_of_le_three
        parent k 2 2 (by omega)
    · exact bombieriConjugateTest_monotoneQuarterFiniteBlock
        parent hreal k 2 2

/-- Exact four-cell balance in terms of the two ratio-two diagonals, their
local critical cross, and the sole complementary-mask prime cross. -/
theorem bombieriFunctional_fourBlock_re_eq_halfEnergyBalance
    (parent : BombieriTest) (k : ℤ) :
    (bombieriFunctional
      (bombieriQuadraticTest (monotoneQuarterFourBlock parent k))).re =
      (bombieriLocalCriticalForm
        (monotoneQuarterFiniteBlock parent k 0 2)
        (monotoneQuarterFiniteBlock parent k 0 2)).re +
      (bombieriLocalCriticalForm
        (monotoneQuarterFiniteBlock parent k 2 2)
        (monotoneQuarterFiniteBlock parent k 2 2)).re +
      2 * (bombieriLocalCriticalForm
        (monotoneQuarterFiniteBlock parent k 0 2)
        (monotoneQuarterFiniteBlock parent k 2 2)).re -
      2 * Real.log 2 *
        (bombieriQuadraticCrossTest
          (monotoneQuarterFiniteBlock parent k 0 2)
          (monotoneQuarterFiniteBlock parent k 2 2) 2).re := by
  rw [monotoneQuarterFourBlock_eq_belowThreeFourCellBlock,
    bombieriFunctional_fourCell_re_eq_localCritical_sub_dilationCorrelation,
    criticalDilationCorrelation_fourCell_eq_sqrt_two_mul_halfCross,
    monotoneQuarterFourCellBlock_eq_twoHalves,
    bombieriLocalCriticalForm_add_self_re]
  simp only [Nat.zero_add, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [show Real.sqrt 2 * Real.log 2 *
      (Real.sqrt 2 *
        (bombieriQuadraticCrossTest
          (monotoneQuarterFiniteBlock parent k 0 2)
          (monotoneQuarterFiniteBlock parent k 2 2) 2).re) =
      2 * Real.log 2 *
        (bombieriQuadraticCrossTest
          (monotoneQuarterFiniteBlock parent k 0 2)
          (monotoneQuarterFiniteBlock parent k 2 2) 2).re by
    calc
      _ = (Real.sqrt 2 * Real.sqrt 2) * Real.log 2 *
          (bombieriQuadraticCrossTest
            (monotoneQuarterFiniteBlock parent k 0 2)
            (monotoneQuarterFiniteBlock parent k 2 2) 2).re := by ring
      _ = _ := by rw [hs2]]

/-- The direct worst-case energy condition on the *whole* local four-cell
quadratic.  The coefficient `log 2 / sqrt 2` is exactly the cost produced by
the sharp complementary-mask prime bound.  In particular, a bound on the two
diagonals alone is not enough unless the signed mixed local term is also
controlled. -/
theorem bombieriFunctional_fourBlock_re_nonnegative_of_totalLocalReserve
    (parent : BombieriTest) (k : ℤ)
    (hlocal :
      fourCellPrimeEnergyCoefficient *
          (bombieriCriticalLogEnergy
              (monotoneQuarterFiniteBlock parent k 0 2) +
            bombieriCriticalLogEnergy
              (monotoneQuarterFiniteBlock parent k 2 2)) ≤
        (bombieriLocalCriticalForm
          (monotoneQuarterFiniteBlock parent k 0 2)
          (monotoneQuarterFiniteBlock parent k 0 2)).re +
        (bombieriLocalCriticalForm
          (monotoneQuarterFiniteBlock parent k 2 2)
          (monotoneQuarterFiniteBlock parent k 2 2)).re +
        2 * (bombieriLocalCriticalForm
          (monotoneQuarterFiniteBlock parent k 0 2)
          (monotoneQuarterFiniteBlock parent k 2 2)).re) :
    0 ≤ (bombieriFunctional
      (bombieriQuadraticTest (monotoneQuarterFourBlock parent k))).re := by
  let f : BombieriTest := monotoneQuarterFiniteBlock parent k 0 2
  let g : BombieriTest := monotoneQuarterFiniteBlock parent k 2 2
  let E : ℝ := bombieriCriticalLogEnergy f + bombieriCriticalLogEnergy g
  let L : ℝ := (bombieriLocalCriticalForm f f).re +
    (bombieriLocalCriticalForm g g).re +
    2 * (bombieriLocalCriticalForm f g).re
  let P : ℝ := (bombieriQuadraticCrossTest f g 2).re
  have hP : P ≤ (Real.sqrt 2 / 4) * E := by
    exact (Complex.re_le_norm _).trans (by
      simpa only [P, E, f, g] using
        norm_fourCell_halfCross_le_energySum parent k)
  have hlog : 0 ≤ 2 * Real.log 2 := by positivity
  have hprime : 2 * Real.log 2 * P ≤
      fourCellPrimeEnergyCoefficient * E := by
    calc
      2 * Real.log 2 * P ≤
          2 * Real.log 2 * ((Real.sqrt 2 / 4) * E) :=
        mul_le_mul_of_nonneg_left hP hlog
      _ = fourCellPrimeEnergyCoefficient * E := by
        unfold fourCellPrimeEnergyCoefficient
        ring
  have hlocal' : fourCellPrimeEnergyCoefficient * E ≤ L := by
    simpa only [E, L, f, g] using hlocal
  rw [bombieriFunctional_fourBlock_re_eq_halfEnergyBalance]
  change 0 ≤ L - 2 * Real.log 2 * P
  linarith

/-- Exact sufficient inequality at an arbitrary diagonal coercivity constant
`kappa`.  The prime term consumes
`fourCellPrimeEnergyCoefficient = log 2 / sqrt 2` of the half-energy sum; any
remaining deficit must be supplied by the signed local half-cross. -/
theorem bombieriFunctional_fourBlock_re_nonnegative_of_energyCoercivity
    (parent : BombieriTest) (k : ℤ) (kappa : ℝ)
    (hleft : kappa * bombieriCriticalLogEnergy
          (monotoneQuarterFiniteBlock parent k 0 2) ≤
        (bombieriLocalCriticalForm
          (monotoneQuarterFiniteBlock parent k 0 2)
          (monotoneQuarterFiniteBlock parent k 0 2)).re)
    (hright : kappa * bombieriCriticalLogEnergy
          (monotoneQuarterFiniteBlock parent k 2 2) ≤
        (bombieriLocalCriticalForm
          (monotoneQuarterFiniteBlock parent k 2 2)
          (monotoneQuarterFiniteBlock parent k 2 2)).re)
    (hcross :
      ((fourCellPrimeEnergyCoefficient - kappa) / 2) *
          (bombieriCriticalLogEnergy
              (monotoneQuarterFiniteBlock parent k 0 2) +
            bombieriCriticalLogEnergy
              (monotoneQuarterFiniteBlock parent k 2 2)) ≤
        (bombieriLocalCriticalForm
          (monotoneQuarterFiniteBlock parent k 0 2)
          (monotoneQuarterFiniteBlock parent k 2 2)).re) :
    0 ≤ (bombieriFunctional
      (bombieriQuadraticTest (monotoneQuarterFourBlock parent k))).re := by
  let f : BombieriTest := monotoneQuarterFiniteBlock parent k 0 2
  let g : BombieriTest := monotoneQuarterFiniteBlock parent k 2 2
  let E : ℝ := bombieriCriticalLogEnergy f + bombieriCriticalLogEnergy g
  let D : ℝ := (bombieriLocalCriticalForm f f).re +
    (bombieriLocalCriticalForm g g).re
  let C : ℝ := (bombieriLocalCriticalForm f g).re
  let P : ℝ := (bombieriQuadraticCrossTest f g 2).re
  have hE : 0 ≤ E := by
    exact add_nonneg (bombieriCriticalLogEnergy_nonnegative f)
      (bombieriCriticalLogEnergy_nonnegative g)
  have hD : kappa * E ≤ D := by
    dsimp only [E, D, f, g]
    calc
      kappa *
          (bombieriCriticalLogEnergy
              (monotoneQuarterFiniteBlock parent k 0 2) +
            bombieriCriticalLogEnergy
              (monotoneQuarterFiniteBlock parent k 2 2)) =
          kappa * bombieriCriticalLogEnergy
              (monotoneQuarterFiniteBlock parent k 0 2) +
            kappa * bombieriCriticalLogEnergy
              (monotoneQuarterFiniteBlock parent k 2 2) := by ring
      _ ≤ _ := add_le_add hleft hright
  have hP : P ≤ (Real.sqrt 2 / 4) * E := by
    exact (Complex.re_le_norm _).trans (by
      simpa only [P, E, f, g] using
        norm_fourCell_halfCross_le_energySum parent k)
  have hlog : 0 ≤ 2 * Real.log 2 := by positivity
  have hprime : 2 * Real.log 2 * P ≤
      fourCellPrimeEnergyCoefficient * E := by
    calc
      2 * Real.log 2 * P ≤
          2 * Real.log 2 * ((Real.sqrt 2 / 4) * E) :=
        mul_le_mul_of_nonneg_left hP hlog
      _ = fourCellPrimeEnergyCoefficient * E := by
        unfold fourCellPrimeEnergyCoefficient
        ring
  have hcross' :
      ((fourCellPrimeEnergyCoefficient - kappa) / 2) * E ≤ C := by
    simpa only [E, C, f, g] using hcross
  have habsorb : fourCellPrimeEnergyCoefficient * E ≤ D + 2 * C := by
    nlinarith
  rw [bombieriFunctional_fourBlock_re_eq_halfEnergyBalance]
  change 0 ≤ D + 2 * C - 2 * Real.log 2 * P
  linarith

/-- The current `1 / 12000` diagonal reserve closes four cells only if the
local half-cross supplies the displayed positive energy deficit. -/
theorem bombieriFunctional_fourBlock_re_nonnegative_of_currentCoercivity
    (parent : BombieriTest)
    (hreal : bombieriConjugateTest parent = parent)
    (k : ℤ)
    (hcross :
      (Real.sqrt 2 * Real.log 2 / 4 - 1 / 24000) *
          (bombieriCriticalLogEnergy
              (monotoneQuarterFiniteBlock parent k 0 2) +
            bombieriCriticalLogEnergy
              (monotoneQuarterFiniteBlock parent k 2 2)) ≤
        (bombieriLocalCriticalForm
          (monotoneQuarterFiniteBlock parent k 0 2)
          (monotoneQuarterFiniteBlock parent k 2 2)).re) :
    0 ≤ (bombieriFunctional
      (bombieriQuadraticTest (monotoneQuarterFourBlock parent k))).re := by
  have hdiag := fourCellHalfLocalDiagonals_ge_criticalLogEnergy
    parent hreal k
  apply bombieriFunctional_fourBlock_re_nonnegative_of_energyCoercivity
    parent k (1 / 12000) hdiag.1 hdiag.2
  convert hcross using 1
  unfold fourCellPrimeEnergyCoefficient
  ring

/-- The generic endpoint constant is rigorously far below the exact prime
absorption threshold. -/
theorem current_coercivity_lt_fourCellPrimeEnergyCoefficient :
    (1 / 12000 : ℝ) < fourCellPrimeEnergyCoefficient := by
  have hs1 : 1 < Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      Real.sqrt_nonneg 2]
  have hlog : (1 / 2 : ℝ) < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hproduct : (1 / 2 : ℝ) < Real.sqrt 2 * Real.log 2 := by
    have hpositive := mul_pos (sub_pos.mpr hs1) (sub_pos.mpr hlog)
    nlinarith
  unfold fourCellPrimeEnergyCoefficient
  nlinarith

theorem current_fourCell_cross_deficit_positive :
    0 < Real.sqrt 2 * Real.log 2 / 4 - 1 / 24000 := by
  have h := current_coercivity_lt_fourCellPrimeEnergyCoefficient
  unfold fourCellPrimeEnergyCoefficient at h
  nlinarith

/-- A half-energy diagonal reserve exceeds the exact four-cell prime
coefficient.  This comparison concerns the prime cost only: total positivity
still requires control of the signed mixed local term. -/
theorem fourCellPrimeEnergyCoefficient_lt_one_half :
    fourCellPrimeEnergyCoefficient < (1 / 2 : ℝ) := by
  rw [fourCellPrimeEnergyCoefficient_eq_log_two_div_sqrt_two]
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  calc
    Real.log 2 / Real.sqrt 2 <
        (1 / Real.sqrt 2) / Real.sqrt 2 :=
      div_lt_div_of_pos_right log_two_lt_inv_sqrt_two hspos
    _ = (1 / 2 : ℝ) := by
      field_simp [hspos.ne']
      nlinarith

/-- Nonnegative local half-cross *together with* `1 / 2` coercivity on both
halves is sufficient for the complete four-cell Bombieri quadratic.  The
diagonal estimate by itself is deliberately not a hypothesis of this result. -/
theorem bombieriFunctional_fourBlock_re_nonnegative_of_halfCoercivity
    (parent : BombieriTest) (k : ℤ)
    (hleft : (1 / 2 : ℝ) * bombieriCriticalLogEnergy
          (monotoneQuarterFiniteBlock parent k 0 2) ≤
        (bombieriLocalCriticalForm
          (monotoneQuarterFiniteBlock parent k 0 2)
          (monotoneQuarterFiniteBlock parent k 0 2)).re)
    (hright : (1 / 2 : ℝ) * bombieriCriticalLogEnergy
          (monotoneQuarterFiniteBlock parent k 2 2) ≤
        (bombieriLocalCriticalForm
          (monotoneQuarterFiniteBlock parent k 2 2)
          (monotoneQuarterFiniteBlock parent k 2 2)).re)
    (hcross : 0 ≤ (bombieriLocalCriticalForm
      (monotoneQuarterFiniteBlock parent k 0 2)
      (monotoneQuarterFiniteBlock parent k 2 2)).re) :
    0 ≤ (bombieriFunctional
      (bombieriQuadraticTest (monotoneQuarterFourBlock parent k))).re := by
  apply bombieriFunctional_fourBlock_re_nonnegative_of_energyCoercivity
    parent k (1 / 2) hleft hright
  have hcoeff :
      (fourCellPrimeEnergyCoefficient - (1 / 2 : ℝ)) / 2 ≤ 0 := by
    linarith [fourCellPrimeEnergyCoefficient_lt_one_half]
  have henergy : 0 ≤
      bombieriCriticalLogEnergy
          (monotoneQuarterFiniteBlock parent k 0 2) +
        bombieriCriticalLogEnergy
          (monotoneQuarterFiniteBlock parent k 2 2) :=
    add_nonneg
      (bombieriCriticalLogEnergy_nonnegative _)
      (bombieriCriticalLogEnergy_nonnegative _)
  exact (mul_nonpos_of_nonpos_of_nonneg hcoeff henergy).trans hcross

end

end ArithmeticHodge.Analysis.MultiplicativeWeilFourCellEnergyAbsorptionStructural

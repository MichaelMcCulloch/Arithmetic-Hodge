import ArithmeticHodge.Analysis.MultiplicativeWeilMinimalBlockEndpointEliminationStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilFourCellEnergyAbsorptionStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneFourCellPrimeGeometryStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilRealMonotoneTailConeCriterionStructural

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.MultiplicativeWeilAllLengthEndpointReserveStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilBelowThreePrimeReductionStructural
open MultiplicativeWeilFourCellEnergyAbsorptionStructural
open MultiplicativeWeilMinimalNegativeBlockStructural
open MultiplicativeWeilMonotoneCellEnergyFrameStructural
open MultiplicativeWeilMonotoneFourCellPrimeGeometryStructural
open MultiplicativeWeilMonotoneQuarterPartitionStructural
open MultiplicativeWeilQuarterLogLatticePartitionStructural
open MultiplicativeWeilRealMonotoneTailConeCriterionStructural

/-!
# The first all-length endpoint remainder

The overlap recurrence first leaves the genuinely remote endpoint pair at
block length five.  The common-parent monotone masks do constrain that pair,
but they do not reduce it to the two adjacent four-cell prime masks.

At factor two, the two endpoint cells have the same canonical weight, so
their product carries the square `w_k^2`.  Meanwhile the two overlapping
four-cell blocks carry the complementary masks

`s_k (1-s_k)` and `s_(k+1) (1-s_(k+1))`.

Their exact inclusion-exclusion identity is

`w_k = s_k (1-s_k) + s_(k+1) (1-s_(k+1)) + w_k^2`.

Thus the first all-length step retains a positive square prime mask after
both adjacent four-cell masks have been used.  That square cannot be bounded
pointwise by any finite multiple of the two complementary masks: at their
shared lattice boundary it equals one while both complementary masks vanish.
Any successful endpoint-reserve argument must therefore use local/endpoint
energy at the same time as the prime term; iterating four-cell prime-mask
absorption alone cannot close the five-cell step.
-/

/-- Factor two transports a canonical cell weight four quarter-steps
forward exactly back to the original weight. -/
theorem monotoneQuarterWeight_add_four_two_mul
    (k : ℤ) (x : ℝ) :
    monotoneQuarterWeight (k + 4) (2 * x) =
      monotoneQuarterWeight k x := by
  unfold monotoneQuarterWeight
  rw [monotoneQuarterStep_add_four_two_mul k x]
  have hindex : k + 4 + 1 = (k + 1) + 4 := by ring
  rw [hindex, monotoneQuarterStep_add_four_two_mul (k + 1) x]

/-- Five consecutive cells, the first block length not covered by the two
overlapping four-cell windows. -/
def monotoneQuarterFiveBlock
    (parent : BombieriTest) (k : ℤ) : BombieriTest :=
  monotoneQuarterFiniteBlock parent k 0 5

/-- The five-cell block telescopes to boundary steps five quarter-steps
apart. -/
theorem monotoneQuarterFiveBlock_apply
    (parent : BombieriTest) (k : ℤ) (x : ℝ) :
    monotoneQuarterFiveBlock parent k x =
      (((monotoneQuarterStep k x -
        monotoneQuarterStep (k + 5) x : ℝ) : ℂ) * parent x) := by
  unfold monotoneQuarterFiveBlock monotoneQuarterFiniteBlock
  simp only [Nat.zero_add]
  rw [sum_range_monotoneQuarterCell_eq_cutoff_sub]
  simp only [TestFunction.coe_sub, Pi.sub_apply,
    monotoneQuarterCutoff_apply]
  push_cast
  ring

/-- The factor-two product of the remote endpoint cells in a five-cell block
has the exact square common-parent mask. -/
theorem fiveCell_remoteEndpoint_two_mul_product_eq_squareMask
    (parent : BombieriTest) (k : ℤ) (x : ℝ) :
    monotoneQuarterCell parent (k + 4) (2 * x) *
        starRingEnd ℂ (monotoneQuarterCell parent k x) =
      ((monotoneQuarterWeight k x ^ 2 : ℝ) : ℂ) *
        parent (2 * x) * starRingEnd ℂ (parent x) := by
  rw [monotoneQuarterCell_apply, monotoneQuarterCell_apply,
    monotoneQuarterWeight_add_four_two_mul,
    map_mul (starRingEnd ℂ), Complex.conj_ofReal]
  push_cast
  ring

/-- The complete factor-two mask of five consecutive cells, restricted to
the only possible base-cell interaction interval, is the full canonical
cell weight rather than a complementary four-cell mask. -/
theorem fiveCell_factorTwo_mask_eq_weight
    (k : ℤ) (x : ℝ) :
    monotoneQuarterStep k x *
        (1 - monotoneQuarterStep (k + 1) x) =
      monotoneQuarterWeight k x := by
  have hnested := monotoneQuarterStep_mul_later
    (k := k) (j := k + 1) (by omega) x
  unfold monotoneQuarterWeight
  nlinarith

/-- On the complete support of the first endpoint cell, the actual
five-cell factor-two product carries exactly the full cell weight. -/
theorem monotoneQuarterFiveBlock_two_mul_product_eq_weight
    (parent : BombieriTest) (k : ℤ) {x : ℝ}
    (hx : x ∈ Set.Icc (quarterLogLatticePoint k)
      (quarterLogLatticePoint (k + 2))) :
    monotoneQuarterFiveBlock parent k (2 * x) *
        starRingEnd ℂ (monotoneQuarterFiveBlock parent k x) =
      ((monotoneQuarterWeight k x : ℝ) : ℂ) *
        parent (2 * x) * starRingEnd ℂ (parent x) := by
  have hupperZero : monotoneQuarterStep (k + 5) x = 0 := by
    apply monotoneQuarterStep_eq_zero_of_le
    exact hx.2.trans (quarterLogLatticePoint_mono (by omega))
  have hlowerOne : monotoneQuarterStep k (2 * x) = 1 := by
    apply monotoneQuarterStep_eq_one_of_le
    calc
      quarterLogLatticePoint (k + 1) ≤
          quarterLogLatticePoint (k + 4) :=
        quarterLogLatticePoint_mono (by omega)
      _ = 2 * quarterLogLatticePoint k := by
        rw [quarterLogLatticePoint_add_four]
      _ ≤ 2 * x := mul_le_mul_of_nonneg_left hx.1 (by norm_num)
  have htransport : monotoneQuarterStep (k + 5) (2 * x) =
      monotoneQuarterStep (k + 1) x := by
    have hindex : k + 5 = (k + 1) + 4 := by ring
    rw [hindex, monotoneQuarterStep_add_four_two_mul]
  rw [monotoneQuarterFiveBlock_apply,
    monotoneQuarterFiveBlock_apply, hupperZero, hlowerOne, htransport,
    map_mul (starRingEnd ℂ), Complex.conj_ofReal]
  have hmask := fiveCell_factorTwo_mask_eq_weight k x
  calc
    ((1 - monotoneQuarterStep (k + 1) x : ℝ) : ℂ) * parent (2 * x) *
          (((monotoneQuarterStep k x - 0 : ℝ) : ℂ) *
            starRingEnd ℂ (parent x)) =
        ((monotoneQuarterStep k x *
          (1 - monotoneQuarterStep (k + 1) x) : ℝ) : ℂ) *
          parent (2 * x) * starRingEnd ℂ (parent x) := by
      push_cast
      ring
    _ = _ := by rw [hmask]

/-- Exact prime-mask inclusion-exclusion at the first all-length step.  The
last summand is precisely the remote endpoint square from the overlap
recurrence. -/
theorem fiveCell_factorTwo_mask_eq_adjacentFourCell_add_remoteSquare
    (k : ℤ) (x : ℝ) :
    monotoneQuarterWeight k x =
      monotoneQuarterStep k x * (1 - monotoneQuarterStep k x) +
        monotoneQuarterStep (k + 1) x *
          (1 - monotoneQuarterStep (k + 1) x) +
        monotoneQuarterWeight k x ^ 2 := by
  have hnested := monotoneQuarterStep_mul_later
    (k := k) (j := k + 1) (by omega) x
  unfold monotoneQuarterWeight
  nlinarith

/-- At the shared boundary of the two adjacent transition intervals, the
remote endpoint square is one while both four-cell complementary masks are
zero. -/
theorem fiveCell_remoteSquare_eq_one_adjacentMasks_eq_zero (k : ℤ) :
    monotoneQuarterWeight k (quarterLogLatticePoint (k + 1)) ^ 2 = 1 ∧
      monotoneQuarterStep k (quarterLogLatticePoint (k + 1)) *
          (1 - monotoneQuarterStep k (quarterLogLatticePoint (k + 1))) = 0 ∧
      monotoneQuarterStep (k + 1) (quarterLogLatticePoint (k + 1)) *
          (1 - monotoneQuarterStep (k + 1)
            (quarterLogLatticePoint (k + 1))) = 0 := by
  have hk : monotoneQuarterStep k (quarterLogLatticePoint (k + 1)) = 1 :=
    monotoneQuarterStep_eq_one_of_le k le_rfl
  have hk1 : monotoneQuarterStep (k + 1)
      (quarterLogLatticePoint (k + 1)) = 0 :=
    monotoneQuarterStep_eq_zero_of_le (k + 1) le_rfl
  rw [monotoneQuarterWeight, hk, hk1]
  norm_num

/-- No finite constant can pay the remote endpoint square using only the two
adjacent four-cell complementary prime masks.  This is an actual
common-parent-mask obstruction, stronger than the abstract equicorrelation
countermodel. -/
theorem no_constant_remoteSquare_bound_by_adjacentFourCellPrimeMasks
    (C : ℝ) (k : ℤ) :
    ¬ ∀ x : ℝ,
      monotoneQuarterWeight k x ^ 2 ≤
        C * (monotoneQuarterStep k x *
              (1 - monotoneQuarterStep k x) +
            monotoneQuarterStep (k + 1) x *
              (1 - monotoneQuarterStep (k + 1) x)) := by
  intro h
  have hboundary := h (quarterLogLatticePoint (k + 1))
  obtain ⟨hsquare, hleft, hright⟩ :=
    fiveCell_remoteSquare_eq_one_adjacentMasks_eq_zero k
  rw [hsquare, hleft, hright] at hboundary
  norm_num at hboundary

/-! ## Sharp endpoint-energy payment of the residual square -/

/-- In the reverse factor-two orientation the later endpoint cell and the
earlier endpoint cell cannot meet.  Thus the endpoint quadratic cross has
only the square-mask orientation displayed above. -/
theorem fiveCell_remoteEndpoint_reverse_two_mul_product_eq_zero
    (parent : BombieriTest) (k : ℤ) (x : ℝ) :
    monotoneQuarterCell parent k (2 * x) *
        starRingEnd ℂ (monotoneQuarterCell parent (k + 4) x) = 0 := by
  by_cases hx : x ≤ quarterLogLatticePoint (k + 4)
  · simp only [monotoneQuarterCell_apply, map_mul,
      Complex.conj_ofReal]
    rw [monotoneQuarterWeight_eq_zero_of_le (k + 4) hx]
    simp
  · have hx' : quarterLogLatticePoint (k + 4) ≤ x := le_of_not_ge hx
    have htwo : quarterLogLatticePoint (k + 2) ≤ 2 * x := by
      calc
        quarterLogLatticePoint (k + 2) ≤
            quarterLogLatticePoint (k + 8) :=
          quarterLogLatticePoint_mono (by omega)
        _ = 2 * quarterLogLatticePoint (k + 4) := by
          rw [show k + 8 = (k + 4) + 4 by ring,
            quarterLogLatticePoint_add_four]
        _ ≤ 2 * x := mul_le_mul_of_nonneg_left hx' (by norm_num)
    simp only [monotoneQuarterCell_apply, map_mul,
      Complex.conj_ofReal]
    rw [monotoneQuarterWeight_eq_zero_of_le_left k htwo]
    simp

/-- The mixed factor-two test of the remote endpoint cells has only its
forward directed orientation. -/
theorem fiveCell_remoteEndpointCross_eq_directedIntegral
    (parent : BombieriTest) (k : ℤ) :
    bombieriQuadraticCrossTest
        (monotoneQuarterCell parent k)
        (monotoneQuarterCell parent (k + 4)) 2 =
      ∫ x : ℝ in Set.Ioi 0,
        monotoneQuarterCell parent (k + 4) (2 * x) *
          starRingEnd ℂ (monotoneQuarterCell parent k x) := by
  rw [bombieriQuadraticCrossTest_apply]
  unfold bombieriDirectedCorrelation
  have hreverse :
      (∫ x : ℝ in Set.Ioi 0,
        monotoneQuarterCell parent k (2 * x) *
          starRingEnd ℂ (monotoneQuarterCell parent (k + 4) x)) = 0 := by
    have hfun :
        (fun x : ℝ ↦ monotoneQuarterCell parent k (2 * x) *
          starRingEnd ℂ (monotoneQuarterCell parent (k + 4) x)) = 0 := by
      funext x
      exact fiveCell_remoteEndpoint_reverse_two_mul_product_eq_zero parent k x
    rw [hfun]
    simp
  rw [hreverse, zero_add]

/-- The preceding directed integral is exactly the square-mask residual in
the five-cell overlap recurrence. -/
theorem fiveCell_remoteEndpointCross_eq_squareMaskIntegral
    (parent : BombieriTest) (k : ℤ) :
    bombieriQuadraticCrossTest
        (monotoneQuarterCell parent k)
        (monotoneQuarterCell parent (k + 4)) 2 =
      ∫ x : ℝ in Set.Ioi 0,
        ((monotoneQuarterWeight k x ^ 2 : ℝ) : ℂ) *
          parent (2 * x) * starRingEnd ℂ (parent x) := by
  rw [fiveCell_remoteEndpointCross_eq_directedIntegral]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x _hx
  exact fiveCell_remoteEndpoint_two_mul_product_eq_squareMask parent k x

private theorem physicalNormSq_integrable_endpointReserve
    (g : BombieriTest) :
    Integrable (fun x : ℝ ↦ ‖g x‖ ^ 2) := by
  have hcont : Continuous (fun x : ℝ ↦ ‖g x‖ ^ 2) := by fun_prop
  have hcompact : HasCompactSupport (fun x : ℝ ↦ ‖g x‖ ^ 2) := by
    simpa only [pow_two] using g.hasCompactSupport.norm.mul_left
      (f := fun x : ℝ ↦ ‖g x‖)
  exact hcont.integrable_of_hasCompactSupport hcompact

private theorem integral_Ioi_norm_sq_two_mul_endpointReserve
    (g : BombieriTest) :
    (∫ x : ℝ in Set.Ioi 0, ‖g (2 * x)‖ ^ 2) =
      (1 / 2 : ℝ) * bombieriCriticalLogEnergy g := by
  have hscale := integral_comp_mul_left_Ioi
    (fun x : ℝ ↦ ‖g x‖ ^ 2) 0 (by norm_num : (0 : ℝ) < 2)
  rw [mul_zero] at hscale
  rw [bombieriCriticalLogEnergy_eq_integral_Ioi_norm_sq]
  simpa only [one_div, smul_eq_mul] using hscale

private theorem normSq_integral_star_mul_le_endpointReserve
    {α : Type*} [MeasurableSpace α] (mu : Measure α)
    (F G : α → ℂ)
    (hFmeas : AEStronglyMeasurable F mu)
    (hGmeas : AEStronglyMeasurable G mu)
    (hFsq : Integrable (fun x ↦ ‖F x‖ ^ 2) mu)
    (hGsq : Integrable (fun x ↦ ‖G x‖ ^ 2) mu) :
    Complex.normSq (∫ x, starRingEnd ℂ (F x) * G x ∂mu) ≤
      (∫ x, ‖F x‖ ^ 2 ∂mu) * ∫ x, ‖G x‖ ^ 2 ∂mu := by
  have hFLp : MemLp F 2 mu :=
    (memLp_two_iff_integrable_sq_norm hFmeas).2 hFsq
  have hGLp : MemLp G 2 mu :=
    (memLp_two_iff_integrable_sq_norm hGmeas).2 hGsq
  have hholder := integral_mul_norm_le_Lp_mul_Lq
    (p := 2) (q := 2) (f := F) (g := G) (μ := mu)
    Real.HolderConjugate.two_two (by simpa using hFLp) (by simpa using hGLp)
  let A : ℝ := ∫ x, ‖F x‖ ^ 2 ∂mu
  let B : ℝ := ∫ x, ‖G x‖ ^ 2 ∂mu
  have hA0 : 0 ≤ A := integral_nonneg fun _ ↦ sq_nonneg _
  have hB0 : 0 ≤ B := integral_nonneg fun _ ↦ sq_nonneg _
  have hholder' :
      (∫ x, ‖F x‖ * ‖G x‖ ∂mu) ≤ Real.sqrt A * Real.sqrt B := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    simpa only [A, B, Real.rpow_two] using hholder
  have hnorm :
      ‖∫ x, starRingEnd ℂ (F x) * G x ∂mu‖ ≤
        ∫ x, ‖F x‖ * ‖G x‖ ∂mu := by
    calc
      ‖∫ x, starRingEnd ℂ (F x) * G x ∂mu‖ ≤
          ∫ x, ‖starRingEnd ℂ (F x) * G x‖ ∂mu :=
        norm_integral_le_integral_norm _
      _ = ∫ x, ‖F x‖ * ‖G x‖ ∂mu := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [norm_mul, Complex.norm_conj]
  have hbound := hnorm.trans hholder'
  rw [Complex.normSq_eq_norm_sq]
  calc
    ‖∫ x, starRingEnd ℂ (F x) * G x ∂mu‖ ^ 2 ≤
        (Real.sqrt A * Real.sqrt B) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hbound
    _ = A * B := by
      rw [mul_pow, Real.sq_sqrt hA0, Real.sq_sqrt hB0]
    _ = _ := rfl

/-- Determinant-scale form of the sharp endpoint estimate.  It is stronger
than the arithmetic-mean energy bound and vanishes when either endpoint
energy vanishes. -/
theorem normSq_fiveCell_remoteEndpointCross_le_energyProduct
    (parent : BombieriTest) (k : ℤ) :
    Complex.normSq (bombieriQuadraticCrossTest
        (monotoneQuarterCell parent k)
        (monotoneQuarterCell parent (k + 4)) 2) ≤
      (1 / 2 : ℝ) *
        bombieriCriticalLogEnergy (monotoneQuarterCell parent k) *
          bombieriCriticalLogEnergy
            (monotoneQuarterCell parent (k + 4)) := by
  let f : BombieriTest := monotoneQuarterCell parent k
  let g : BombieriTest := monotoneQuarterCell parent (k + 4)
  have hcross : bombieriQuadraticCrossTest f g 2 =
      ∫ x : ℝ in Set.Ioi 0, starRingEnd ℂ (f x) * g (2 * x) := by
    rw [show bombieriQuadraticCrossTest f g 2 =
        ∫ x : ℝ in Set.Ioi 0, g (2 * x) * starRingEnd ℂ (f x) by
      simpa only [f, g] using
        fiveCell_remoteEndpointCross_eq_directedIntegral parent k]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _hx
    ring
  have hsquare := normSq_integral_star_mul_le_endpointReserve
    (volume.restrict (Set.Ioi (0 : ℝ)))
    (fun x : ℝ ↦ f x) (fun x : ℝ ↦ g (2 * x))
    (by fun_prop)
    (by fun_prop)
    (physicalNormSq_integrable_endpointReserve f).integrableOn
    ((physicalNormSq_integrable_endpointReserve g).comp_mul_left'
      (by norm_num)).integrableOn
  rw [hcross]
  calc
    Complex.normSq (∫ x : ℝ in Set.Ioi 0,
        starRingEnd ℂ (f x) * g (2 * x)) ≤
        (∫ x : ℝ in Set.Ioi 0, ‖f x‖ ^ 2) *
          ∫ x : ℝ in Set.Ioi 0, ‖g (2 * x)‖ ^ 2 := hsquare
    _ = (1 / 2 : ℝ) * bombieriCriticalLogEnergy f *
          bombieriCriticalLogEnergy g := by
      rw [integral_Ioi_norm_sq_two_mul_endpointReserve,
        ← bombieriCriticalLogEnergy_eq_integral_Ioi_norm_sq f]
      ring

/-- Geometric-mean version of the sharp remote endpoint bound. -/
theorem norm_fiveCell_remoteEndpointCross_le_energyGeometricMean
    (parent : BombieriTest) (k : ℤ) :
    ‖bombieriQuadraticCrossTest
        (monotoneQuarterCell parent k)
        (monotoneQuarterCell parent (k + 4)) 2‖ ≤
      (Real.sqrt 2 / 2) * Real.sqrt
        (bombieriCriticalLogEnergy (monotoneQuarterCell parent k) *
          bombieriCriticalLogEnergy
            (monotoneQuarterCell parent (k + 4))) := by
  let f : BombieriTest := monotoneQuarterCell parent k
  let g : BombieriTest := monotoneQuarterCell parent (k + 4)
  let A : ℝ := bombieriCriticalLogEnergy f
  let B : ℝ := bombieriCriticalLogEnergy g
  have hA : 0 ≤ A := bombieriCriticalLogEnergy_nonnegative f
  have hB : 0 ≤ B := bombieriCriticalLogEnergy_nonnegative g
  have hAB : 0 ≤ A * B := mul_nonneg hA hB
  have hsquare :
      Complex.normSq (bombieriQuadraticCrossTest f g 2) ≤
        (1 / 2 : ℝ) * A * B := by
    simpa only [A, B, f, g] using
      normSq_fiveCell_remoteEndpointCross_le_energyProduct parent k
  have hrhs : 0 ≤ Real.sqrt 2 / 2 * Real.sqrt (A * B) := by positivity
  apply (sq_le_sq₀ (norm_nonneg _) hrhs).mp
  calc
    ‖bombieriQuadraticCrossTest f g 2‖ ^ 2 =
        Complex.normSq (bombieriQuadraticCrossTest f g 2) := by
      rw [Complex.normSq_eq_norm_sq]
    _ ≤ (1 / 2 : ℝ) * A * B := hsquare
    _ = (Real.sqrt 2 / 2 * Real.sqrt (A * B)) ^ 2 := by
      rw [mul_pow, div_pow,
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
        Real.sq_sqrt hAB]
      ring

/-- Sharp dilation-energy absorption of the five-cell residual square.  The
constant `sqrt 2 / 4` is the optimally balanced Young constant after the
factor-two Jacobian is taken into account. -/
theorem norm_fiveCell_remoteEndpointCross_le_energySum
    (parent : BombieriTest) (k : ℤ) :
    ‖bombieriQuadraticCrossTest
        (monotoneQuarterCell parent k)
        (monotoneQuarterCell parent (k + 4)) 2‖ ≤
      (Real.sqrt 2 / 4) *
        (bombieriCriticalLogEnergy (monotoneQuarterCell parent k) +
          bombieriCriticalLogEnergy
            (monotoneQuarterCell parent (k + 4))) := by
  let f : BombieriTest := monotoneQuarterCell parent k
  let g : BombieriTest := monotoneQuarterCell parent (k + 4)
  have hproductInt : IntegrableOn
      (fun x : ℝ ↦ ‖g (2 * x)‖ * ‖f x‖) (Set.Ioi 0) := by
    have hcont : Continuous (fun x : ℝ ↦ ‖g (2 * x)‖ * ‖f x‖) := by
      fun_prop
    have hcompact : HasCompactSupport
        (fun x : ℝ ↦ ‖g (2 * x)‖ * ‖f x‖) := by
      exact f.hasCompactSupport.norm.mul_left
        (f := fun x : ℝ ↦ ‖g (2 * x)‖)
    exact (hcont.integrable_of_hasCompactSupport hcompact).integrableOn
  have hmajorInt : IntegrableOn
      (fun x : ℝ ↦
        Real.sqrt 2 / 2 * ‖g (2 * x)‖ ^ 2 +
          Real.sqrt 2 / 4 * ‖f x‖ ^ 2) (Set.Ioi 0) := by
    exact (((physicalNormSq_integrable_endpointReserve g).comp_mul_left'
      (by norm_num)).const_mul _).add
        ((physicalNormSq_integrable_endpointReserve f).const_mul _)
      |>.integrableOn
  have hyoung (x : ℝ) :
      ‖g (2 * x)‖ * ‖f x‖ ≤
        Real.sqrt 2 / 2 * ‖g (2 * x)‖ ^ 2 +
          Real.sqrt 2 / 4 * ‖f x‖ ^ 2 := by
    have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    have hinv : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by
      apply (mul_left_cancel₀ hspos.ne')
      rw [mul_inv_cancel₀ hspos.ne']
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    have hy := two_mul_le_add_mul_sq
      (a := ‖g (2 * x)‖) (b := ‖f x‖) hspos
    rw [hinv] at hy
    nlinarith
  rw [show bombieriQuadraticCrossTest f g 2 =
      ∫ x : ℝ in Set.Ioi 0, g (2 * x) * starRingEnd ℂ (f x) by
    simpa only [f, g] using
      fiveCell_remoteEndpointCross_eq_directedIntegral parent k]
  calc
    ‖∫ x : ℝ in Set.Ioi 0, g (2 * x) * starRingEnd ℂ (f x)‖ ≤
        ∫ x : ℝ in Set.Ioi 0,
          ‖g (2 * x) * starRingEnd ℂ (f x)‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ x : ℝ in Set.Ioi 0, ‖g (2 * x)‖ * ‖f x‖ := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [norm_mul, Complex.norm_conj]
    _ ≤ ∫ x : ℝ in Set.Ioi 0,
        (Real.sqrt 2 / 2 * ‖g (2 * x)‖ ^ 2 +
          Real.sqrt 2 / 4 * ‖f x‖ ^ 2) := by
      exact integral_mono_ae hproductInt hmajorInt
        (Filter.Eventually.of_forall hyoung)
    _ = Real.sqrt 2 / 2 *
          (∫ x : ℝ in Set.Ioi 0, ‖g (2 * x)‖ ^ 2) +
        Real.sqrt 2 / 4 *
          (∫ x : ℝ in Set.Ioi 0, ‖f x‖ ^ 2) := by
      rw [integral_add, integral_const_mul, integral_const_mul]
      · exact ((physicalNormSq_integrable_endpointReserve g).comp_mul_left'
          (by norm_num)).integrableOn.const_mul _
      · exact (physicalNormSq_integrable_endpointReserve f).integrableOn.const_mul _
    _ = Real.sqrt 2 / 2 *
          ((1 / 2 : ℝ) * bombieriCriticalLogEnergy g) +
        Real.sqrt 2 / 4 * bombieriCriticalLogEnergy f := by
      rw [integral_Ioi_norm_sq_two_mul_endpointReserve,
        ← bombieriCriticalLogEnergy_eq_integral_Ioi_norm_sq f]
    _ = (Real.sqrt 2 / 4) *
        (bombieriCriticalLogEnergy f + bombieriCriticalLogEnergy g) := by ring

/-- After inserting the exact `2 log 2` mixed-prime coefficient, the residual
square consumes precisely the same endpoint-energy coefficient as the
four-cell complementary-mask prime. -/
theorem fiveCell_remoteEndpointPrimeCost_le_energySum
    (parent : BombieriTest) (k : ℤ) :
    2 * Real.log 2 *
        (bombieriQuadraticCrossTest
          (monotoneQuarterCell parent k)
          (monotoneQuarterCell parent (k + 4)) 2).re ≤
      fourCellPrimeEnergyCoefficient *
        (bombieriCriticalLogEnergy (monotoneQuarterCell parent k) +
          bombieriCriticalLogEnergy
            (monotoneQuarterCell parent (k + 4))) := by
  let f : BombieriTest := monotoneQuarterCell parent k
  let g : BombieriTest := monotoneQuarterCell parent (k + 4)
  let E : ℝ := bombieriCriticalLogEnergy f +
    bombieriCriticalLogEnergy g
  let P : ℝ := (bombieriQuadraticCrossTest f g 2).re
  have hP : P ≤ (Real.sqrt 2 / 4) * E := by
    exact (Complex.re_le_norm _).trans (by
      simpa only [P, E, f, g] using
        norm_fiveCell_remoteEndpointCross_le_energySum parent k)
  have hlog : 0 ≤ 2 * Real.log 2 := by positivity
  calc
    2 * Real.log 2 * P ≤
        2 * Real.log 2 * ((Real.sqrt 2 / 4) * E) :=
      mul_le_mul_of_nonneg_left hP hlog
    _ = fourCellPrimeEnergyCoefficient * E := by
      unfold fourCellPrimeEnergyCoefficient
      ring

/-- Sharp determinant-scale prime payment.  Compared with the energy-sum
version, this records the true geometric-mean cost of the square mask. -/
theorem fiveCell_remoteEndpointPrimeCost_le_energyGeometricMean
    (parent : BombieriTest) (k : ℤ) :
    2 * Real.log 2 *
        (bombieriQuadraticCrossTest
          (monotoneQuarterCell parent k)
          (monotoneQuarterCell parent (k + 4)) 2).re ≤
      2 * fourCellPrimeEnergyCoefficient * Real.sqrt
        (bombieriCriticalLogEnergy (monotoneQuarterCell parent k) *
          bombieriCriticalLogEnergy
            (monotoneQuarterCell parent (k + 4))) := by
  let f : BombieriTest := monotoneQuarterCell parent k
  let g : BombieriTest := monotoneQuarterCell parent (k + 4)
  let E : ℝ := bombieriCriticalLogEnergy f *
    bombieriCriticalLogEnergy g
  let P : ℝ := (bombieriQuadraticCrossTest f g 2).re
  have hP : P ≤ (Real.sqrt 2 / 2) * Real.sqrt E := by
    exact (Complex.re_le_norm _).trans (by
      simpa only [P, E, f, g] using
        norm_fiveCell_remoteEndpointCross_le_energyGeometricMean parent k)
  have hlog : 0 ≤ 2 * Real.log 2 := by positivity
  calc
    2 * Real.log 2 * P ≤
        2 * Real.log 2 * ((Real.sqrt 2 / 2) * Real.sqrt E) :=
      mul_le_mul_of_nonneg_left hP hlog
    _ = 2 * fourCellPrimeEnergyCoefficient * Real.sqrt E := by
      unfold fourCellPrimeEnergyCoefficient
      ring

private theorem quarterLogLatticePoint_two_lt_three_halves_endpointReserve :
    quarterLogLatticePoint 2 < (3 / 2 : ℝ) := by
  have hsq : quarterLogLatticePoint 2 ^ 2 = 2 := by
    calc
      quarterLogLatticePoint 2 ^ 2 =
          quarterLogLatticePoint 2 * quarterLogLatticePoint 2 := by ring
      _ = quarterLogLatticePoint (2 + 2) :=
        (quarterLogLatticePoint_add 2 2).symm
      _ = 2 := by norm_num [quarterLogLatticePoint_four]
  nlinarith [quarterLogLatticePoint_pos 2]

/-- The sparse pair of five-cell endpoints still has support ratio
`2 * sqrt 2 < 3`, so its entire prime functional is the single factor-two
atom just bounded above. -/
theorem fiveCell_remoteEndpointPair_tsupport_subset
    (parent : BombieriTest) (k : ℤ) :
    tsupport
        (monotoneQuarterCell parent k +
          monotoneQuarterCell parent (k + 4) : BombieriTest) ⊆
      Set.Icc (quarterLogLatticePoint k)
        (quarterLogLatticePoint (k + 6)) := by
  apply (tsupport_add
    (monotoneQuarterCell parent k : ℝ → ℂ)
    (monotoneQuarterCell parent (k + 4) : ℝ → ℂ)).trans
  apply union_subset
  · exact (monotoneQuarterCell_tsupport_subset parent k).trans
      (Set.Icc_subset_Icc le_rfl
        (quarterLogLatticePoint_mono (by omega)))
  · exact (monotoneQuarterCell_tsupport_subset parent (k + 4)).trans
      (Set.Icc_subset_Icc
        (quarterLogLatticePoint_mono (by omega)) (by
          rw [show k + 4 + 2 = k + 6 by ring]))

theorem fiveCell_remoteEndpointPair_ratio_lt_three (k : ℤ) :
    quarterLogLatticePoint (k + 6) / quarterLogLatticePoint k < 3 := by
  have hkpos := quarterLogLatticePoint_pos k
  calc
    quarterLogLatticePoint (k + 6) / quarterLogLatticePoint k =
        quarterLogLatticePoint 6 := by
      rw [quarterLogLatticePoint_add]
      field_simp [hkpos.ne']
    _ = 2 * quarterLogLatticePoint 2 := by
      rw [show (6 : ℤ) = 2 + 4 by norm_num,
        quarterLogLatticePoint_add, quarterLogLatticePoint_four]
    _ < 3 := by
      nlinarith [quarterLogLatticePoint_two_lt_three_halves_endpointReserve]

/-- Exact local/prime balance for the sparse pair of five-cell endpoints.
This is the production quadratic whose only prime term is the remote square
mask; no prime sum remains hidden in the statement. -/
theorem bombieriFunctional_remoteEndpointPair_re_eq_localEnergyBalance
    (parent : BombieriTest) (k : ℤ) :
    (bombieriFunctional (bombieriQuadraticTest
      (monotoneQuarterCell parent k +
        monotoneQuarterCell parent (k + 4)))).re =
      (bombieriLocalCriticalForm
        (monotoneQuarterCell parent k)
        (monotoneQuarterCell parent k)).re +
      (bombieriLocalCriticalForm
        (monotoneQuarterCell parent (k + 4))
        (monotoneQuarterCell parent (k + 4))).re +
      2 * (bombieriLocalCriticalForm
        (monotoneQuarterCell parent k)
        (monotoneQuarterCell parent (k + 4))).re -
      2 * Real.log 2 *
        (bombieriQuadraticCrossTest
          (monotoneQuarterCell parent k)
          (monotoneQuarterCell parent (k + 4)) 2).re := by
  let f : BombieriTest := monotoneQuarterCell parent k
  let g : BombieriTest := monotoneQuarterCell parent (k + 4)
  rw [bombieriFunctional_quadratic_re_eq_localCritical_sub_dilationCorrelation
    (f + g) (quarterLogLatticePoint_pos k)
    (quarterLogLatticePoint_mono (by omega))
    (by simpa only [f, g] using
      fiveCell_remoteEndpointPair_tsupport_subset parent k)
    (fiveCell_remoteEndpointPair_ratio_lt_three k),
    criticalDilationCorrelation_add_eq_sqrt_two_mul_quadraticCross
      f g (monotoneQuarterCell_ratioTwo parent k)
        (monotoneQuarterCell_ratioTwo parent (k + 4)),
    bombieriLocalCriticalForm_add_self_re]
  simp only [f, g, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [show Real.sqrt 2 * Real.log 2 *
      (Real.sqrt 2 *
        (bombieriQuadraticCrossTest
          (monotoneQuarterCell parent k)
          (monotoneQuarterCell parent (k + 4)) 2).re) =
      2 * Real.log 2 *
        (bombieriQuadraticCrossTest
          (monotoneQuarterCell parent k)
          (monotoneQuarterCell parent (k + 4)) 2).re by
    calc
      _ = (Real.sqrt 2 * Real.sqrt 2) * Real.log 2 *
          (bombieriQuadraticCrossTest
            (monotoneQuarterCell parent k)
            (monotoneQuarterCell parent (k + 4)) 2).re := by ring
      _ = _ := by rw [hs2]]

private theorem bombieriFunctional_monotoneQuarterCell_eq_localCritical
    (parent : BombieriTest) (k : ℤ) :
    bombieriFunctional
        (bombieriQuadraticTest (monotoneQuarterCell parent k)) =
      bombieriLocalCriticalForm
        (monotoneQuarterCell parent k)
        (monotoneQuarterCell parent k) := by
  obtain ⟨a, b, ha, hab, hsupport, hratio⟩ :=
    monotoneQuarterCell_ratioTwo parent k
  exact bombieriFunctional_quadratic_eq_bombieriLocalCriticalForm_le_two
    (monotoneQuarterCell parent k) ha hab hsupport hratio

/-- Exact mixed local-minus-prime formula for the remote endpoint corner.
Unlike the endpoint-pair quadratic, this identity contains no endpoint
diagonals, so it can be inserted into the five-cell overlap recurrence
without double-counting reserve. -/
theorem two_mul_fiveCell_remoteEndpointGlobalCross_re_eq_local_sub_prime
    (parent : BombieriTest) (k : ℤ) :
    2 * (bombieriTwoBlockGlobalCrossSymbol
      (monotoneQuarterCell parent k)
      (monotoneQuarterCell parent (k + 4))).re =
      2 * (bombieriLocalCriticalForm
        (monotoneQuarterCell parent k)
        (monotoneQuarterCell parent (k + 4))).re -
      2 * Real.log 2 *
        (bombieriQuadraticCrossTest
          (monotoneQuarterCell parent k)
          (monotoneQuarterCell parent (k + 4)) 2).re := by
  let f : BombieriTest := monotoneQuarterCell parent k
  let g : BombieriTest := monotoneQuarterCell parent (k + 4)
  have hpair :
      (bombieriFunctional (bombieriQuadraticTest (f + g))).re =
        (bombieriLocalCriticalForm f f).re +
        (bombieriLocalCriticalForm g g).re +
        2 * (bombieriLocalCriticalForm f g).re -
        2 * Real.log 2 * (bombieriQuadraticCrossTest f g 2).re := by
    simpa only [f, g] using
      bombieriFunctional_remoteEndpointPair_re_eq_localEnergyBalance parent k
  have htwo := bombieriFunctional_twoBlock_re f g (1 : ℂ)
  simp only [one_smul, Complex.normSq_one, one_mul] at htwo
  have hf := bombieriFunctional_monotoneQuarterCell_eq_localCritical parent k
  have hg := bombieriFunctional_monotoneQuarterCell_eq_localCritical
    parent (k + 4)
  have hfre := congrArg Complex.re hf
  have hgre := congrArg Complex.re hg
  rw [hpair, hfre, hgre] at htwo
  dsimp only [f, g] at htwo ⊢
  linarith

/-- Sharp coupled reserve for the actual five-cell remote corner.  Its local
critical endpoint cross pays the square-mask prime at the exact endpoint
energy cost `fourCellPrimeEnergyCoefficient / 2`; under this inequality the
remote global corner itself is nonnegative. -/
theorem fiveCell_remoteEndpointGlobalCross_nonnegative_of_localCrossEnergy
    (parent : BombieriTest) (k : ℤ)
    (hlocal :
      (fourCellPrimeEnergyCoefficient / 2) *
          (bombieriCriticalLogEnergy (monotoneQuarterCell parent k) +
            bombieriCriticalLogEnergy
              (monotoneQuarterCell parent (k + 4))) ≤
        (bombieriLocalCriticalForm
          (monotoneQuarterCell parent k)
          (monotoneQuarterCell parent (k + 4))).re) :
    0 ≤ (bombieriTwoBlockGlobalCrossSymbol
      (monotoneQuarterCell parent k)
      (monotoneQuarterCell parent (k + 4))).re := by
  have hprime := fiveCell_remoteEndpointPrimeCost_le_energySum parent k
  have hcross :=
    two_mul_fiveCell_remoteEndpointGlobalCross_re_eq_local_sub_prime parent k
  linarith

/-- Sharp geometric-energy version of the coupled five-cell endpoint
reserve.  This is the weakest direct `L²` target exposed by the exact
production geometry: the local endpoint cross need only dominate
`(log 2 / sqrt 2) * sqrt(E_left E_right)`. -/
theorem fiveCell_remoteEndpointGlobalCross_nonnegative_of_localCrossGeometricEnergy
    (parent : BombieriTest) (k : ℤ)
    (hlocal :
      fourCellPrimeEnergyCoefficient * Real.sqrt
          (bombieriCriticalLogEnergy (monotoneQuarterCell parent k) *
            bombieriCriticalLogEnergy
              (monotoneQuarterCell parent (k + 4))) ≤
        (bombieriLocalCriticalForm
          (monotoneQuarterCell parent k)
          (monotoneQuarterCell parent (k + 4))).re) :
    0 ≤ (bombieriTwoBlockGlobalCrossSymbol
      (monotoneQuarterCell parent k)
      (monotoneQuarterCell parent (k + 4))).re := by
  have hprime :=
    fiveCell_remoteEndpointPrimeCost_le_energyGeometricMean parent k
  have hcross :=
    two_mul_fiveCell_remoteEndpointGlobalCross_re_eq_local_sub_prime parent k
  linarith

/-- A genuinely coupled local/endpoint-energy inequality absorbs the
five-cell residual square.  The hypothesis contains only the local critical
quadratic of the two endpoints and their physical critical energies. -/
theorem bombieriFunctional_remoteEndpointPair_re_nonnegative_of_localEnergyReserve
    (parent : BombieriTest) (k : ℤ)
    (hlocal :
      fourCellPrimeEnergyCoefficient *
          (bombieriCriticalLogEnergy (monotoneQuarterCell parent k) +
            bombieriCriticalLogEnergy
              (monotoneQuarterCell parent (k + 4))) ≤
        (bombieriLocalCriticalForm
          (monotoneQuarterCell parent k)
          (monotoneQuarterCell parent k)).re +
        (bombieriLocalCriticalForm
          (monotoneQuarterCell parent (k + 4))
          (monotoneQuarterCell parent (k + 4))).re +
        2 * (bombieriLocalCriticalForm
          (monotoneQuarterCell parent k)
          (monotoneQuarterCell parent (k + 4))).re) :
    0 ≤ (bombieriFunctional (bombieriQuadraticTest
      (monotoneQuarterCell parent k +
        monotoneQuarterCell parent (k + 4)))).re := by
  rw [bombieriFunctional_remoteEndpointPair_re_eq_localEnergyBalance]
  have hprime := fiveCell_remoteEndpointPrimeCost_le_energySum parent k
  linarith

end

end ArithmeticHodge.Analysis.MultiplicativeWeilAllLengthEndpointReserveStructural

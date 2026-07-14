import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCoupledRankSquares
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhasePerturbationOneSubCosSeries

set_option autoImplicit false
set_option maxRecDepth 100000

open Filter MeasureTheory Real Set Topology
open scoped BigOperators Interval

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCoupledRankLimit

noncomputable section

open YoshidaEndpointHyperbolicBound
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoPhaseCoupledRankSquares
open YoshidaFactorTwoPhaseRankLimit
open YoshidaFactorTwoPhaseSymmetricCoercivity
open YoshidaRenormalizedGeometricKernel

private theorem coupledAlternatingRankPartialTail_le_tsum
    {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t < 2) (N : ℕ) :
    (∑ m ∈ Finset.range N,
      2 * Real.exp
          (-2 * yoshidaEndpointA * oddRate (m + 1)) *
        Real.sinh
          (yoshidaEndpointA * oddRate (m + 1) * t)) ≤
      ∑' m : ℕ,
        2 * Real.exp
            (-2 * yoshidaEndpointA * oddRate (m + 1)) *
          Real.sinh
            (yoshidaEndpointA * oddRate (m + 1) * t) := by
  have hs :=
    ArithmeticHodge.Analysis.YoshidaFactorTwoPhasePerturbationOneSubCosSeries.summable_factorTwoAntisymmetricRankTail
      ht0 ht2
  apply hs.sum_le_tsum (Finset.range N)
  intro m _hm
  exact mul_nonneg (by positivity)
    (Real.sinh_nonneg_iff.mpr <| mul_nonneg
      (mul_nonneg yoshidaEndpointA_pos.le (oddRate_pos _).le) ht0)

/-- Finite antisymmetric hyperbolic ranks converge to the genuine complete
alternating archimedean integral for every continuous profile pair. -/
theorem factorTwoCenteredAlternatingRankPartialSum_tendsto
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o) :
    Tendsto
      (fun N : ℕ ↦ factorTwoCenteredAlternatingRankPartialSum e o N)
      atTop
      (nhds (yoshidaEndpointA *
        ∫ t : ℝ in 0..2,
          factorTwoAntisymmetricWeight (yoshidaEndpointA * t) *
            (factorTwoCenteredCrossCorrelation o e t -
              factorTwoCenteredCrossCorrelation e o t))) := by
  let D : ℝ → ℝ := fun t ↦
    factorTwoCenteredCrossCorrelation o e t -
      factorTwoCenteredCrossCorrelation e o t
  let G : ℝ → ℝ := fun t ↦
    2 * Real.exp yoshidaEndpointA *
      Real.sinh (yoshidaEndpointA * t / 2)
  let W : ℝ → ℝ := fun t ↦
    factorTwoAntisymmetricWeight (yoshidaEndpointA * t)
  let F : ℕ → ℝ → ℝ := fun N t ↦
    factorTwoCoupledAlternatingRankPartialWeight N t * D t
  let B : ℝ → ℝ := fun t ↦ |W t * D t|
  have hD : Continuous D := by
    dsimp only [D]
    exact (continuous_factorTwoCenteredCrossCorrelation o e hoc hec).sub
      (continuous_factorTwoCenteredCrossCorrelation e o hec hoc)
  have hWeight : IntervalIntegrable (fun t : ℝ ↦ W t * D t)
      volume 0 2 := by
    simpa only [W, D] using
      intervalIntegrable_factorTwoCenteredAlternatingKernel e o hec hoc
  have hB : IntervalIntegrable B volume 0 2 := by
    simpa only [B] using hWeight.norm
  have hFmeas : ∀ᶠ N in atTop,
      AEStronglyMeasurable (F N) (volume.restrict (Ι (0 : ℝ) 2)) := by
    filter_upwards [] with N
    apply Continuous.aestronglyMeasurable
    dsimp only [F, factorTwoCoupledAlternatingRankPartialWeight]
    exact (by fun_prop)
  have hBound : ∀ᶠ N in atTop, ∀ᵐ t ∂volume,
      t ∈ Ι (0 : ℝ) 2 → ‖F N t‖ ≤ B t := by
    filter_upwards [] with N
    filter_upwards [MeasureTheory.Measure.ae_ne volume (2 : ℝ)] with t ht2
    intro ht
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 2)] at ht
    have ht0 : 0 ≤ t := ht.1.le
    have htlt2 : t < 2 := lt_of_le_of_ne ht.2 ht2
    let S : ℝ := ∑ m ∈ Finset.range N,
      2 * Real.exp
          (-2 * yoshidaEndpointA * oddRate (m + 1)) *
        Real.sinh
          (yoshidaEndpointA * oddRate (m + 1) * t)
    let T : ℝ := ∑' m : ℕ,
      2 * Real.exp
          (-2 * yoshidaEndpointA * oddRate (m + 1)) *
        Real.sinh
          (yoshidaEndpointA * oddRate (m + 1) * t)
    have hG0 : 0 ≤ G t := by
      dsimp only [G]
      exact mul_nonneg (by positivity)
        (Real.sinh_nonneg_iff.mpr <|
          div_nonneg (mul_nonneg yoshidaEndpointA_pos.le ht0) (by norm_num))
    have hS0 : 0 ≤ S := by
      dsimp only [S]
      apply Finset.sum_nonneg
      intro m _hm
      exact mul_nonneg (by positivity)
        (Real.sinh_nonneg_iff.mpr <| mul_nonneg
          (mul_nonneg yoshidaEndpointA_pos.le (oddRate_pos _).le) ht0)
    have hST : S ≤ T := by
      simpa only [S, T] using
        coupledAlternatingRankPartialTail_le_tsum ht0 htlt2 N
    have hT0 : 0 ≤ T := hS0.trans hST
    have hseries :=
      ArithmeticHodge.Analysis.YoshidaFactorTwoPhasePerturbationOneSubCosSeries.factorTwoAntisymmetricWeight_eq_rankOneSeries
        ht0 htlt2
    change W t = G t + T at hseries
    have hW0 : 0 ≤ W t := by
      rw [hseries]
      exact add_nonneg hG0 hT0
    have hpartial0 : 0 ≤ G t + S := add_nonneg hG0 hS0
    have hpartialW : G t + S ≤ W t := by
      rw [hseries]
      linarith
    have hWabs : |W t * D t| = W t * |D t| := by
      rw [abs_mul, abs_of_nonneg hW0]
    dsimp only [F, B, factorTwoCoupledAlternatingRankPartialWeight]
    change ‖(G t + S) * D t‖ ≤ |W t * D t|
    rw [Real.norm_eq_abs]
    calc
      |(G t + S) * D t| = (G t + S) * |D t| := by
        rw [abs_mul, abs_of_nonneg hpartial0]
      _ ≤ W t * |D t| :=
        mul_le_mul_of_nonneg_right hpartialW (abs_nonneg (D t))
      _ = |W t * D t| := hWabs.symm
  have hLim : ∀ᵐ t ∂volume, t ∈ Ι (0 : ℝ) 2 →
      Tendsto (fun N : ℕ ↦ F N t) atTop (nhds (W t * D t)) := by
    filter_upwards [MeasureTheory.Measure.ae_ne volume (2 : ℝ)] with t ht2
    intro ht
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 2)] at ht
    have htlt2 : t < 2 := lt_of_le_of_ne ht.2 ht2
    have hweight :=
      ArithmeticHodge.Analysis.YoshidaFactorTwoPhasePerturbationOneSubCosSeries.factorTwoAntisymmetricRankPartialWeight_tendsto
        ht.1.le htlt2
    have hweight' : Tendsto
        (fun N : ℕ ↦ factorTwoCoupledAlternatingRankPartialWeight N t)
        atTop (nhds (W t)) := by
      simpa only [factorTwoCoupledAlternatingRankPartialWeight,
        ArithmeticHodge.Analysis.YoshidaFactorTwoPhasePerturbationOneSubCosSeries.factorTwoAntisymmetricRankPartialWeight,
        W] using hweight
    exact hweight'.mul_const (D t)
  have hIntegral :
      Tendsto (fun N : ℕ ↦ ∫ t : ℝ in 0..2, F N t) atTop
        (nhds (∫ t : ℝ in 0..2, W t * D t)) := by
    exact intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      B hFmeas hBound hB hLim
  have hScaled := hIntegral.const_mul yoshidaEndpointA
  simpa only [factorTwoCenteredAlternatingRankPartialSum, F, W, D] using hScaled

/-- The decaying mixed-moment ranks are absolutely summable.  The proof is
the rankwise polarization bound `2 |CS| ≤ C² + S²`, majorized by the
already summable even and odd square families. -/
theorem summable_factorTwoCenteredAlternatingRankProducts
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o)
    (heven : Function.Even e) (hodd : Function.Odd o) :
    Summable (fun m : ℕ ↦
      2 * Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
        centeredCoshMoment e
          (yoshidaEndpointA * oddRate (m + 1)) *
        centeredSinhMoment o
          (yoshidaEndpointA * oddRate (m + 1))) := by
  have he :=
    (hasSum_factorTwoCenteredArch_evenRankSquares e hec heven).summable
  have ho :=
    (hasSum_factorTwoCenteredArch_oddRankSquares o hoc hodd).summable
  have hmajor := he.add ho
  apply hmajor.of_norm_bounded
  intro m
  let r : ℝ := Real.exp
    (-2 * yoshidaEndpointA * oddRate (m + 1))
  let C : ℝ := centeredCoshMoment e
    (yoshidaEndpointA * oddRate (m + 1))
  let S : ℝ := centeredSinhMoment o
    (yoshidaEndpointA * oddRate (m + 1))
  have hr : 0 ≤ r := by
    dsimp only [r]
    positivity
  have hpair := abs_coupledRank_phase_le_sq_add_sq
    0 1 C S (by norm_num)
  change ‖2 * r * C * S‖ ≤ r * C ^ 2 + r * S ^ 2
  rw [Real.norm_eq_abs]
  calc
    |2 * r * C * S| =
        r * |0 * (C ^ 2 - S ^ 2) + 2 * 1 * C * S| := by
      rw [show 2 * r * C * S = r * (2 * C * S) by ring,
        abs_mul, abs_of_nonneg hr]
      congr 1
      ring_nf
    _ ≤ r * (C ^ 2 + S ^ 2) :=
      mul_le_mul_of_nonneg_left hpair hr
    _ = r * C ^ 2 + r * S ^ 2 := by ring

/-- Infinite product expansion of the genuine alternating archimedean
channel.  This is the limit of the finite coupled-rank identity, not a
coefficient computation. -/
theorem factorTwoCenteredAlternatingArch_eq_rankProducts
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o)
    (heven : Function.Even e) (hodd : Function.Odd o) :
    yoshidaEndpointA *
        ∫ t : ℝ in 0..2,
          factorTwoAntisymmetricWeight (yoshidaEndpointA * t) *
            (factorTwoCenteredCrossCorrelation o e t -
              factorTwoCenteredCrossCorrelation e o t) =
      yoshidaEndpointA *
        (2 * Real.exp yoshidaEndpointA *
            centeredCoshMoment e (yoshidaEndpointA / 2) *
              centeredSinhMoment o (yoshidaEndpointA / 2) +
          ∑' m : ℕ,
            2 * Real.exp
                (-2 * yoshidaEndpointA * oddRate (m + 1)) *
              centeredCoshMoment e
                (yoshidaEndpointA * oddRate (m + 1)) *
              centeredSinhMoment o
                (yoshidaEndpointA * oddRate (m + 1))) := by
  let q : ℕ → ℝ := fun m ↦
    2 * Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
      centeredCoshMoment e
        (yoshidaEndpointA * oddRate (m + 1)) *
      centeredSinhMoment o
        (yoshidaEndpointA * oddRate (m + 1))
  let head : ℝ :=
    2 * Real.exp yoshidaEndpointA *
      centeredCoshMoment e (yoshidaEndpointA / 2) *
      centeredSinhMoment o (yoshidaEndpointA / 2)
  have hq : Summable q := by
    simpa only [q] using
      summable_factorTwoCenteredAlternatingRankProducts
        e o hec hoc heven hodd
  have hseries : Tendsto
      (fun N : ℕ ↦ yoshidaEndpointA *
        (head + ∑ m ∈ Finset.range N, q m))
      atTop
      (nhds (yoshidaEndpointA * (head + ∑' m : ℕ, q m))) := by
    exact (tendsto_const_nhds.add hq.hasSum.tendsto_sum_nat).const_mul
      yoshidaEndpointA
  have hproducts : Tendsto
      (fun N : ℕ ↦ factorTwoCenteredAlternatingRankPartialSum e o N)
      atTop
      (nhds (yoshidaEndpointA * (head + ∑' m : ℕ, q m))) := by
    refine hseries.congr' ?_
    filter_upwards [] with N
    rw [factorTwoCenteredAlternatingRankPartialSum_eq_products
      e o hec hoc heven hodd N]
  have hintegral :=
    factorTwoCenteredAlternatingRankPartialSum_tendsto e o hec hoc
  have hlimit := tendsto_nhds_unique hintegral hproducts
  simpa only [q, head] using hlimit

/-- The manifestly positive complete energy of the coupled even/odd rank
family. -/
def factorTwoCoupledRankEnergy (e o : ℝ → ℝ) : ℝ :=
  yoshidaEndpointA *
    (Real.exp yoshidaEndpointA *
        (centeredCoshMoment e (yoshidaEndpointA / 2) ^ 2 +
          centeredSinhMoment o (yoshidaEndpointA / 2) ^ 2) +
      ∑' m : ℕ,
        Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
          (centeredCoshMoment e
                (yoshidaEndpointA * oddRate (m + 1)) ^ 2 +
            centeredSinhMoment o
                (yoshidaEndpointA * oddRate (m + 1)) ^ 2))

/-- The positive tail defining the complete coupled-rank energy is summable. -/
theorem summable_factorTwoCoupledRankEnergyTail
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o)
    (heven : Function.Even e) (hodd : Function.Odd o) :
    Summable (fun m : ℕ ↦
      Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
        (centeredCoshMoment e
              (yoshidaEndpointA * oddRate (m + 1)) ^ 2 +
          centeredSinhMoment o
              (yoshidaEndpointA * oddRate (m + 1)) ^ 2)) := by
  have he :=
    (hasSum_factorTwoCenteredArch_evenRankSquares e hec heven).summable
  have ho :=
    (hasSum_factorTwoCenteredArch_oddRankSquares o hoc hodd).summable
  simpa only [mul_add] using he.add ho

/-- Finite positive coupled-rank energies converge to their full `tsum`.
This is obtained directly by adding the even and odd square `HasSum`
theorems. -/
theorem factorTwoCoupledRankEnergyPartialSum_tendsto
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o)
    (heven : Function.Even e) (hodd : Function.Odd o) :
    Tendsto (fun N : ℕ ↦ factorTwoCoupledRankEnergyPartialSum e o N)
      atTop (nhds (factorTwoCoupledRankEnergy e o)) := by
  let q : ℕ → ℝ := fun m ↦
    Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
      (centeredCoshMoment e
            (yoshidaEndpointA * oddRate (m + 1)) ^ 2 +
        centeredSinhMoment o
            (yoshidaEndpointA * oddRate (m + 1)) ^ 2)
  let head : ℝ := Real.exp yoshidaEndpointA *
    (centeredCoshMoment e (yoshidaEndpointA / 2) ^ 2 +
      centeredSinhMoment o (yoshidaEndpointA / 2) ^ 2)
  have hq : Summable q := by
    simpa only [q] using
      summable_factorTwoCoupledRankEnergyTail e o hec hoc heven hodd
  have hseries : Tendsto
      (fun N : ℕ ↦ yoshidaEndpointA *
        (head + ∑ m ∈ Finset.range N, q m))
      atTop
      (nhds (yoshidaEndpointA * (head + ∑' m : ℕ, q m))) := by
    exact (tendsto_const_nhds.add hq.hasSum.tendsto_sum_nat).const_mul
      yoshidaEndpointA
  simpa only [factorTwoCoupledRankEnergyPartialSum,
    factorTwoCoupledRankEnergy, q, head] using hseries

/-- The complete coupled-rank energy is nonnegative before any phase is
chosen. -/
theorem factorTwoCoupledRankEnergy_nonneg (e o : ℝ → ℝ) :
    0 ≤ factorTwoCoupledRankEnergy e o := by
  unfold factorTwoCoupledRankEnergy
  apply mul_nonneg yoshidaEndpointA_pos.le
  apply add_nonneg
  · exact mul_nonneg (by positivity)
      (add_nonneg (sq_nonneg _) (sq_nonneg _))
  · apply tsum_nonneg
    intro m
    exact mul_nonneg (by positivity)
      (add_nonneg (sq_nonneg _) (sq_nonneg _))

/-- Closed signed-block form of the same positive energy.  Positivity is
clearest in `factorTwoCoupledRankEnergy`; this identity records how that
radius sits relative to the two complete symmetric archimedean blocks. -/
theorem factorTwoCoupledRankEnergy_eq_archBlocks
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o)
    (heven : Function.Even e) (hodd : Function.Odd o) :
    factorTwoCoupledRankEnergy e o =
      2 * yoshidaEndpointA * Real.exp yoshidaEndpointA *
          (centeredCoshMoment e (yoshidaEndpointA / 2) ^ 2 +
            centeredSinhMoment o (yoshidaEndpointA / 2) ^ 2) +
        factorTwoCenteredArchBlock o - factorTwoCenteredArchBlock e := by
  have he := hasSum_factorTwoCenteredArch_evenRankSquares e hec heven
  have ho := hasSum_factorTwoCenteredArch_oddRankSquares o hoc hodd
  have htail :
      (∑' m : ℕ,
        Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
          (centeredCoshMoment e
                (yoshidaEndpointA * oddRate (m + 1)) ^ 2 +
            centeredSinhMoment o
                (yoshidaEndpointA * oddRate (m + 1)) ^ 2)) =
        (∑' m : ℕ,
          Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
            centeredCoshMoment e
              (yoshidaEndpointA * oddRate (m + 1)) ^ 2) +
        ∑' m : ℕ,
          Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
            centeredSinhMoment o
              (yoshidaEndpointA * oddRate (m + 1)) ^ 2 := by
    rw [show (fun m : ℕ ↦
        Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
          (centeredCoshMoment e
                (yoshidaEndpointA * oddRate (m + 1)) ^ 2 +
            centeredSinhMoment o
                (yoshidaEndpointA * oddRate (m + 1)) ^ 2)) =
      (fun m : ℕ ↦
        Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
          centeredCoshMoment e
            (yoshidaEndpointA * oddRate (m + 1)) ^ 2) +
      (fun m : ℕ ↦
        Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
          centeredSinhMoment o
            (yoshidaEndpointA * oddRate (m + 1)) ^ 2) by
        funext m
        simp only [Pi.add_apply]
        ring]
    exact he.summable.tsum_add ho.summable
  unfold factorTwoCoupledRankEnergy
  rw [htail, he.tsum_eq, ho.tsum_eq]
  field_simp [yoshidaEndpointA_pos.ne']
  ring

/-- Complete coupled-rank contraction.  The alternating coordinate is kept
as the genuine antisymmetric integral, so no prime term or finite-rank
surrogate is hidden in the statement. -/
theorem abs_factorTwoCoupledRankPhase_le_energy
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o)
    (heven : Function.Even e) (hodd : Function.Odd o)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    |a * (factorTwoCenteredArchBlock e +
            factorTwoCenteredArchBlock o) +
        b * (yoshidaEndpointA *
          ∫ t : ℝ in 0..2,
            factorTwoAntisymmetricWeight (yoshidaEndpointA * t) *
              (factorTwoCenteredCrossCorrelation o e t -
                factorTwoCenteredCrossCorrelation e o t))| ≤
      factorTwoCoupledRankEnergy e o := by
  have heLimit := factorTwoCenteredArchRankPartialSum_tendsto e hec
  have hoLimit := factorTwoCenteredArchRankPartialSum_tendsto o hoc
  have haltLimit :=
    factorTwoCenteredAlternatingRankPartialSum_tendsto e o hec hoc
  have hphase : Tendsto
      (fun N : ℕ ↦
        a * (factorTwoCenteredArchRankPartialSum e N +
            factorTwoCenteredArchRankPartialSum o N) +
          b * factorTwoCenteredAlternatingRankPartialSum e o N)
      atTop
      (nhds (a * (factorTwoCenteredArchBlock e +
            factorTwoCenteredArchBlock o) +
          b * (yoshidaEndpointA *
            ∫ t : ℝ in 0..2,
              factorTwoAntisymmetricWeight (yoshidaEndpointA * t) *
                (factorTwoCenteredCrossCorrelation o e t -
                  factorTwoCenteredCrossCorrelation e o t)))) := by
    exact ((heLimit.add hoLimit).const_mul a).add
      (haltLimit.const_mul b)
  have henergy := factorTwoCoupledRankEnergyPartialSum_tendsto
    e o hec hoc heven hodd
  exact le_of_tendsto_of_tendsto hphase.abs henergy
    (Filter.Eventually.of_forall fun N ↦
      abs_factorTwoCoupledRankPhasePartialSum_le_energy
        e o hec hoc heven hodd N a b hab)

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCoupledRankLimit

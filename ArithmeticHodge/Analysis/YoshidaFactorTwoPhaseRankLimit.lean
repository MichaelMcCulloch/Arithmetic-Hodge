import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseSymmetricCoercivity

set_option autoImplicit false

open Filter MeasureTheory Real Set Topology
open scoped BigOperators Interval

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseRankLimit

noncomputable section

open CenteredEndpointCorrelation
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoEndpointParityPencil
open YoshidaFactorTwoPhaseSymmetricCoercivity
open YoshidaEndpointHyperbolicBound
open YoshidaRenormalizedGeometricKernel

/-!
# Closure of the symmetric hyperbolic-rank expansion

The half-odd hyperbolic series is not uniformly convergent at the singular
endpoint `t = 2`.  The shrinking endpoint correlation supplies exactly the
missing cancellation.  We therefore first prove pointwise convergence on the
open overlap interval and then pass through the quadratic integral with a
dominating function made from the already-integrable complete kernel.
-/

/-- The decaying rank family is summable at every point of the open overlap
interval. -/
theorem summable_factorTwoSymmetricRankTail
    {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t < 2) :
    Summable (fun m : ℕ ↦
      2 * Real.exp
          (-2 * yoshidaEndpointA * oddRate (m + 1)) *
        Real.cosh
          (yoshidaEndpointA * oddRate (m + 1) * t)) := by
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
      have hscaled :=
        (hasSum_oddExponentials hz).summable.mul_left (1 / 2 : ℝ)
      convert hscaled using 1
      funext k
      ring
    simpa only [Nat.add_comm] using (summable_nat_add_iff 1).2 hfull
  have hsp := hsummable zp hzp
  have hsm := hsummable zm hzm
  apply (hsp.add hsm).congr
  intro m
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

/-- The finite hyperbolic-rank weights converge pointwise to the complete
symmetric weight throughout the open overlap interval. -/
theorem factorTwoSymmetricRankPartialWeight_tendsto
    {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t < 2) :
    Tendsto (fun N : ℕ ↦ factorTwoSymmetricRankPartialWeight N t)
      atTop
      (nhds (factorTwoSymmetricWeight (yoshidaEndpointA * t))) := by
  let a : ℕ → ℝ := fun m ↦
    2 * Real.exp
        (-2 * yoshidaEndpointA * oddRate (m + 1)) *
      Real.cosh
        (yoshidaEndpointA * oddRate (m + 1) * t)
  have ha : Summable a := by
    simpa only [a] using summable_factorTwoSymmetricRankTail ht0 ht2
  have hsum : Tendsto (fun N : ℕ ↦ ∑ m ∈ Finset.range N, a m)
      atTop (nhds (∑' m : ℕ, a m)) := ha.hasSum.tendsto_sum_nat
  have hhead : Tendsto
      (fun _ : ℕ ↦
        2 * Real.exp yoshidaEndpointA *
          Real.cosh (yoshidaEndpointA * t / 2))
      atTop
      (nhds (2 * Real.exp yoshidaEndpointA *
        Real.cosh (yoshidaEndpointA * t / 2))) := tendsto_const_nhds
  have hsub := hhead.sub hsum
  rw [factorTwoSymmetricWeight_eq_rankOneSeries ht0 ht2]
  simpa only [factorTwoSymmetricRankPartialWeight, a] using hsub

/-- The complete rank tail dominates every finite tail on the open overlap
interval.  This is the order estimate used in the endpoint majorant. -/
private theorem rankPartialTail_le_tsum
    {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t < 2) (N : ℕ) :
    (∑ m ∈ Finset.range N,
      2 * Real.exp
          (-2 * yoshidaEndpointA * oddRate (m + 1)) *
        Real.cosh
          (yoshidaEndpointA * oddRate (m + 1) * t)) ≤
      ∑' m : ℕ,
        2 * Real.exp
            (-2 * yoshidaEndpointA * oddRate (m + 1)) *
          Real.cosh
            (yoshidaEndpointA * oddRate (m + 1) * t) := by
  have hs := summable_factorTwoSymmetricRankTail ht0 ht2
  apply hs.sum_le_tsum (Finset.range N)
  intro m _hm
  positivity

/-- The finite-rank quadratic forms converge to the genuine complete
archimedean block.  No endpoint cutoff is introduced: dominated convergence
uses the complete singular kernel itself, whose product with the shrinking
correlation is already interval-integrable. -/
theorem factorTwoCenteredArchRankPartialSum_tendsto
    (w : ℝ → ℝ) (hw : Continuous w) :
    Tendsto (fun N : ℕ ↦ factorTwoCenteredArchRankPartialSum w N)
      atTop (nhds (factorTwoCenteredArchBlock w)) := by
  let C : ℝ → ℝ := centeredEndpointCorrelation w
  let H : ℝ → ℝ := fun t ↦
    2 * Real.exp yoshidaEndpointA *
      Real.cosh (yoshidaEndpointA * t / 2)
  let W : ℝ → ℝ := fun t ↦
    factorTwoSymmetricWeight (yoshidaEndpointA * t)
  let F : ℕ → ℝ → ℝ := fun N t ↦
    factorTwoSymmetricRankPartialWeight N t * C t
  let B : ℝ → ℝ := fun t ↦
    2 * |H t * C t| + |W t * C t|
  have hC : Continuous C := by
    exact continuous_centeredEndpointCorrelation_of_continuous w hw
  have hHead : IntervalIntegrable (fun t : ℝ ↦ H t * C t)
      volume 0 2 := by
    apply Continuous.intervalIntegrable
    dsimp only [H]
    exact (by fun_prop)
  have hWeight : IntervalIntegrable (fun t : ℝ ↦ W t * C t)
      volume 0 2 := by
    have h := intervalIntegrable_factorTwoCenteredSymmetricKernel
      w w hw hw
    simpa only [W, C, factorTwoCenteredCorrelationBilinear_self] using h
  have hB : IntervalIntegrable B volume 0 2 := by
    dsimp only [B]
    exact (hHead.norm.const_mul 2).add hWeight.norm
  have hFmeas : ∀ᶠ N in atTop,
      AEStronglyMeasurable (F N) (volume.restrict (Ι (0 : ℝ) 2)) := by
    filter_upwards [] with N
    apply Continuous.aestronglyMeasurable
    dsimp only [F, factorTwoSymmetricRankPartialWeight]
    fun_prop
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
        Real.cosh
          (yoshidaEndpointA * oddRate (m + 1) * t)
    let T : ℝ := ∑' m : ℕ,
      2 * Real.exp
          (-2 * yoshidaEndpointA * oddRate (m + 1)) *
        Real.cosh
          (yoshidaEndpointA * oddRate (m + 1) * t)
    have hS0 : 0 ≤ S := by
      dsimp only [S]
      positivity
    have hST : S ≤ T := by
      simpa only [S, T] using rankPartialTail_le_tsum ht0 htlt2 N
    have hT0 : 0 ≤ T := hS0.trans hST
    have hSC : |S * C t| ≤ |T * C t| := by
      rw [abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_right
        (by simpa only [abs_of_nonneg hS0, abs_of_nonneg hT0] using hST)
        (abs_nonneg (C t))
    have hseries := factorTwoSymmetricWeight_eq_rankOneSeries ht0 htlt2
    change W t = H t - T at hseries
    have hTC : |T * C t| ≤ |H t * C t| + |W t * C t| := by
      have htri := abs_sub (H t * C t) (W t * C t)
      rw [show H t * C t - W t * C t = T * C t by
        rw [hseries]
        ring] at htri
      exact htri
    dsimp only [F, B, factorTwoSymmetricRankPartialWeight]
    change ‖(H t - S) * C t‖ ≤ 2 * |H t * C t| + |W t * C t|
    rw [Real.norm_eq_abs, sub_mul]
    calc
      |H t * C t - S * C t| ≤
          |H t * C t| + |S * C t| := abs_sub _ _
      _ ≤ |H t * C t| + |T * C t| :=
        add_le_add (le_refl _) hSC
      _ ≤ 2 * |H t * C t| + |W t * C t| := by
        linarith
  have hLim : ∀ᵐ t ∂volume, t ∈ Ι (0 : ℝ) 2 →
      Tendsto (fun N : ℕ ↦ F N t) atTop (nhds (W t * C t)) := by
    filter_upwards [MeasureTheory.Measure.ae_ne volume (2 : ℝ)] with t ht2
    intro ht
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 2)] at ht
    have htlt2 : t < 2 := lt_of_le_of_ne ht.2 ht2
    have hweight := factorTwoSymmetricRankPartialWeight_tendsto ht.1.le htlt2
    exact hweight.mul_const (C t)
  have hIntegral :
      Tendsto (fun N : ℕ ↦ ∫ t : ℝ in 0..2, F N t) atTop
        (nhds (∫ t : ℝ in 0..2, W t * C t)) := by
    exact intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      B hFmeas hBound hB hLim
  have hScaled := hIntegral.const_mul yoshidaEndpointA
  simpa only [factorTwoCenteredArchRankPartialSum,
    factorTwoCenteredArchBlock, F, W, C] using hScaled

/-! ## Infinite signed-square forms -/

/-- On an even profile the positive decaying square family is summable, with
its sum identified by the complete archimedean block. -/
theorem hasSum_factorTwoCenteredArch_evenRankSquares
    (w : ℝ → ℝ) (hw : Continuous w) (heven : Function.Even w) :
    HasSum
      (fun m : ℕ ↦
        Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
          centeredCoshMoment w
            (yoshidaEndpointA * oddRate (m + 1)) ^ 2)
      (Real.exp yoshidaEndpointA *
          centeredCoshMoment w (yoshidaEndpointA / 2) ^ 2 -
        factorTwoCenteredArchBlock w / yoshidaEndpointA) := by
  let q : ℕ → ℝ := fun m ↦
    Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
      centeredCoshMoment w
        (yoshidaEndpointA * oddRate (m + 1)) ^ 2
  let head : ℝ := Real.exp yoshidaEndpointA *
    centeredCoshMoment w (yoshidaEndpointA / 2) ^ 2
  have harch := factorTwoCenteredArchRankPartialSum_tendsto w hw
  have hscaled := harch.const_mul (1 / yoshidaEndpointA)
  have hhead : Tendsto (fun _ : ℕ ↦ head) atTop (nhds head) :=
    tendsto_const_nhds
  have hpartial : Tendsto (fun N : ℕ ↦ ∑ m ∈ Finset.range N, q m)
      atTop
      (nhds (head - (1 / yoshidaEndpointA) *
        factorTwoCenteredArchBlock w)) := by
    refine (hhead.sub hscaled).congr' ?_
    filter_upwards [] with N
    rw [factorTwoCenteredArchRankPartialSum_eq_evenSquares
      w hw heven N]
    dsimp only [q, head]
    field_simp [yoshidaEndpointA_pos.ne']
    ring
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun m ↦ by
    positivity) _).2
  simpa only [q, head, div_eq_mul_inv, one_div, mul_comm, mul_one]
    using hpartial

/-- Infinite even signed-square representation of the complete archimedean
block: one growing square minus the full decaying square series. -/
theorem factorTwoCenteredArchBlock_eq_evenRankSquares
    (w : ℝ → ℝ) (hw : Continuous w) (heven : Function.Even w) :
    factorTwoCenteredArchBlock w =
      yoshidaEndpointA *
        (Real.exp yoshidaEndpointA *
            centeredCoshMoment w (yoshidaEndpointA / 2) ^ 2 -
          ∑' m : ℕ,
            Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
              centeredCoshMoment w
                (yoshidaEndpointA * oddRate (m + 1)) ^ 2) := by
  rw [(hasSum_factorTwoCenteredArch_evenRankSquares w hw heven).tsum_eq]
  field_simp [yoshidaEndpointA_pos.ne']
  ring

/-- On an odd profile the positive decaying sine-square family is summable,
again with its sum fixed by the complete archimedean block. -/
theorem hasSum_factorTwoCenteredArch_oddRankSquares
    (w : ℝ → ℝ) (hw : Continuous w) (hodd : Function.Odd w) :
    HasSum
      (fun m : ℕ ↦
        Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
          centeredSinhMoment w
            (yoshidaEndpointA * oddRate (m + 1)) ^ 2)
      (factorTwoCenteredArchBlock w / yoshidaEndpointA +
        Real.exp yoshidaEndpointA *
          centeredSinhMoment w (yoshidaEndpointA / 2) ^ 2) := by
  let q : ℕ → ℝ := fun m ↦
    Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
      centeredSinhMoment w
        (yoshidaEndpointA * oddRate (m + 1)) ^ 2
  let head : ℝ := Real.exp yoshidaEndpointA *
    centeredSinhMoment w (yoshidaEndpointA / 2) ^ 2
  have harch := factorTwoCenteredArchRankPartialSum_tendsto w hw
  have hscaled := harch.const_mul (1 / yoshidaEndpointA)
  have hhead : Tendsto (fun _ : ℕ ↦ head) atTop (nhds head) :=
    tendsto_const_nhds
  have hpartial : Tendsto (fun N : ℕ ↦ ∑ m ∈ Finset.range N, q m)
      atTop
      (nhds ((1 / yoshidaEndpointA) *
        factorTwoCenteredArchBlock w + head)) := by
    refine (hscaled.add hhead).congr' ?_
    filter_upwards [] with N
    rw [factorTwoCenteredArchRankPartialSum_eq_oddSquares
      w hw hodd N]
    dsimp only [q, head]
    field_simp [yoshidaEndpointA_pos.ne']
    ring
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun m ↦ by
    positivity) _).2
  simpa only [q, head, div_eq_mul_inv, one_div, mul_comm, mul_one]
    using hpartial

/-- Infinite odd signed-square representation of the complete archimedean
block: the growing sine square is negative and the full decaying square
series is positive. -/
theorem factorTwoCenteredArchBlock_eq_oddRankSquares
    (w : ℝ → ℝ) (hw : Continuous w) (hodd : Function.Odd w) :
    factorTwoCenteredArchBlock w =
      yoshidaEndpointA *
        (-Real.exp yoshidaEndpointA *
            centeredSinhMoment w (yoshidaEndpointA / 2) ^ 2 +
          ∑' m : ℕ,
            Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
              centeredSinhMoment w
                (yoshidaEndpointA * oddRate (m + 1)) ^ 2) := by
  rw [(hasSum_factorTwoCenteredArch_oddRankSquares w hw hodd).tsum_eq]
  field_simp [yoshidaEndpointA_pos.ne']
  ring

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseRankLimit

import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCoupledRankLimit

set_option autoImplicit false

open MeasureTheory Real
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseArchRankDiskSchur

noncomputable section

open CenteredEndpointCorrelation
open YoshidaEndpointHyperbolicBound
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoPhaseCoupledRankLimit
open YoshidaFactorTwoPhaseRankLimit
open YoshidaFactorTwoPhaseSymmetricCoercivity
open YoshidaRenormalizedGeometricKernel

/-!
# Archimedean rank disk--Schur inequality

The growing and decaying hyperbolic ranks are retained as genuine infinite
square families.  The even and odd diagonal energies use the same weights as
the alternating rank products, so the closed-disk determinant follows from
the rankwise numerical-radius contraction, without a mode truncation.
-/

/-- The positive even hyperbolic-rank energy: the growing cosh square and the
complete decaying cosh-square family. -/
def factorTwoEvenRankEnergy (e : ℝ → ℝ) : ℝ :=
  yoshidaEndpointA *
    (Real.exp yoshidaEndpointA *
        centeredCoshMoment e (yoshidaEndpointA / 2) ^ 2 +
      ∑' m : ℕ,
        Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
          centeredCoshMoment e
            (yoshidaEndpointA * oddRate (m + 1)) ^ 2)

/-- The positive odd hyperbolic-rank energy: the growing sinh square and the
complete decaying sinh-square family. -/
def factorTwoOddRankEnergy (o : ℝ → ℝ) : ℝ :=
  yoshidaEndpointA *
    (Real.exp yoshidaEndpointA *
        centeredSinhMoment o (yoshidaEndpointA / 2) ^ 2 +
      ∑' m : ℕ,
        Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
          centeredSinhMoment o
            (yoshidaEndpointA * oddRate (m + 1)) ^ 2)

/-- The archimedean alternating channel, before the retained `p = 3` atom is
subtracted. -/
def factorTwoCenteredAlternatingArch (e o : ℝ → ℝ) : ℝ :=
  yoshidaEndpointA *
    ∫ t : ℝ in 0..2,
      factorTwoAntisymmetricWeight (yoshidaEndpointA * t) *
        (factorTwoCenteredCrossCorrelation o e t -
          factorTwoCenteredCrossCorrelation e o t)

private theorem centeredCoshMoment_smul
    (c : ℝ) (w : ℝ → ℝ) (lambda : ℝ) :
    centeredCoshMoment (c • w) lambda = c * centeredCoshMoment w lambda := by
  unfold centeredCoshMoment
  rw [show (fun x : ℝ ↦ Real.cosh (lambda * x) * (c • w) x) =
      fun x ↦ c * (Real.cosh (lambda * x) * w x) by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul]
    ring,
    intervalIntegral.integral_const_mul]

private theorem centeredSinhMoment_smul
    (c : ℝ) (w : ℝ → ℝ) (lambda : ℝ) :
    centeredSinhMoment (c • w) lambda = c * centeredSinhMoment w lambda := by
  unfold centeredSinhMoment
  rw [show (fun x : ℝ ↦ Real.sinh (lambda * x) * (c • w) x) =
      fun x ↦ c * (Real.sinh (lambda * x) * w x) by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul]
    ring,
    intervalIntegral.integral_const_mul]

theorem factorTwoEvenRankEnergy_smul (c : ℝ) (e : ℝ → ℝ) :
    factorTwoEvenRankEnergy (c • e) = c ^ 2 * factorTwoEvenRankEnergy e := by
  unfold factorTwoEvenRankEnergy
  simp_rw [centeredCoshMoment_smul]
  rw [show (fun m : ℕ ↦
      Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
        (c * centeredCoshMoment e
          (yoshidaEndpointA * oddRate (m + 1))) ^ 2) =
      fun m ↦ c ^ 2 *
        (Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
          centeredCoshMoment e
            (yoshidaEndpointA * oddRate (m + 1)) ^ 2) by
    funext m
    ring,
    tsum_mul_left]
  ring

theorem factorTwoOddRankEnergy_smul (c : ℝ) (o : ℝ → ℝ) :
    factorTwoOddRankEnergy (c • o) = c ^ 2 * factorTwoOddRankEnergy o := by
  unfold factorTwoOddRankEnergy
  simp_rw [centeredSinhMoment_smul]
  rw [show (fun m : ℕ ↦
      Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
        (c * centeredSinhMoment o
          (yoshidaEndpointA * oddRate (m + 1))) ^ 2) =
      fun m ↦ c ^ 2 *
        (Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
          centeredSinhMoment o
            (yoshidaEndpointA * oddRate (m + 1)) ^ 2) by
    funext m
    ring,
    tsum_mul_left]
  ring

theorem factorTwoCenteredArchBlock_smul
    (c : ℝ) (w : ℝ → ℝ) :
    factorTwoCenteredArchBlock (c • w) =
      c ^ 2 * factorTwoCenteredArchBlock w := by
  have hcorr (t : ℝ) :
      centeredEndpointCorrelation (c • w) t =
        c ^ 2 * centeredEndpointCorrelation w t := by
    unfold centeredEndpointCorrelation
    rw [show (fun x : ℝ ↦ (c • w) (t + x) * (c • w) x) =
        fun x ↦ c ^ 2 * (w (t + x) * w x) by
      funext x
      simp only [Pi.smul_apply, smul_eq_mul]
      ring,
      intervalIntegral.integral_const_mul]
  unfold factorTwoCenteredArchBlock
  simp_rw [hcorr]
  rw [show (fun t : ℝ ↦ factorTwoSymmetricWeight (yoshidaEndpointA * t) *
      (c ^ 2 * centeredEndpointCorrelation w t)) =
      fun t ↦ c ^ 2 *
        (factorTwoSymmetricWeight (yoshidaEndpointA * t) *
          centeredEndpointCorrelation w t) by
    funext t
    ring,
    intervalIntegral.integral_const_mul]
  ring

theorem factorTwoCenteredAlternatingArch_smul_smul
    (c d : ℝ) (e o : ℝ → ℝ) :
    factorTwoCenteredAlternatingArch (c • e) (d • o) =
      c * d * factorTwoCenteredAlternatingArch e o := by
  have hcross (t : ℝ) :
      factorTwoCenteredCrossCorrelation (d • o) (c • e) t -
          factorTwoCenteredCrossCorrelation (c • e) (d • o) t =
        c * d *
          (factorTwoCenteredCrossCorrelation o e t -
            factorTwoCenteredCrossCorrelation e o t) := by
    rw [factorTwoCenteredCrossCorrelation_smul_left,
      factorTwoCenteredCrossCorrelation_smul_right,
      factorTwoCenteredCrossCorrelation_smul_left,
      factorTwoCenteredCrossCorrelation_smul_right]
    ring
  unfold factorTwoCenteredAlternatingArch
  simp_rw [hcross]
  rw [show (fun t : ℝ ↦
      factorTwoAntisymmetricWeight (yoshidaEndpointA * t) *
        (c * d *
          (factorTwoCenteredCrossCorrelation o e t -
            factorTwoCenteredCrossCorrelation e o t))) =
      fun t ↦ (c * d) *
        (factorTwoAntisymmetricWeight (yoshidaEndpointA * t) *
          (factorTwoCenteredCrossCorrelation o e t -
            factorTwoCenteredCrossCorrelation e o t)) by
    funext t
    ring,
    intervalIntegral.integral_const_mul]
  ring

theorem factorTwoCoupledRankEnergy_eq_even_add_odd
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o)
    (heven : Function.Even e) (hodd : Function.Odd o) :
    factorTwoCoupledRankEnergy e o =
      factorTwoEvenRankEnergy e + factorTwoOddRankEnergy o := by
  have he :=
    (hasSum_factorTwoCenteredArch_evenRankSquares e hec heven).summable
  have ho :=
    (hasSum_factorTwoCenteredArch_oddRankSquares o hoc hodd).summable
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
    exact he.tsum_add ho
  unfold factorTwoCoupledRankEnergy factorTwoEvenRankEnergy
    factorTwoOddRankEnergy
  rw [htail]
  ring

/-- The complete archimedean rank family is a nonnegative quadratic pencil
after independent rescaling of its even and odd inputs.  This is the infinite
rank analogue of summing positive `2 x 2` rank matrices. -/
theorem factorTwoArchRank_quadratic_nonneg
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o)
    (heven : Function.Even e) (hodd : Function.Odd o)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) (r s : ℝ) :
    0 ≤
      (factorTwoEvenRankEnergy e + a * factorTwoCenteredArchBlock e) * r ^ 2 +
        b * factorTwoCenteredAlternatingArch e o * r * s +
        (factorTwoOddRankEnergy o + a * factorTwoCenteredArchBlock o) * s ^ 2 := by
  have herc : Continuous (r • e) := hec.const_smul r
  have hosc : Continuous (s • o) := hoc.const_smul s
  have here : Function.Even (r • e) := by
    intro x
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [heven x]
  have hoso : Function.Odd (s • o) := by
    intro x
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hodd x]
    ring
  have hbound := abs_factorTwoCoupledRankPhase_le_energy
    (r • e) (s • o) herc hosc here hoso a b hab
  change
    |a * (factorTwoCenteredArchBlock (r • e) +
          factorTwoCenteredArchBlock (s • o)) +
        b * factorTwoCenteredAlternatingArch (r • e) (s • o)| ≤
      factorTwoCoupledRankEnergy (r • e) (s • o) at hbound
  rw [factorTwoCoupledRankEnergy_eq_even_add_odd
      (r • e) (s • o) herc hosc here hoso,
    factorTwoEvenRankEnergy_smul, factorTwoOddRankEnergy_smul,
    factorTwoCenteredArchBlock_smul, factorTwoCenteredArchBlock_smul,
    factorTwoCenteredAlternatingArch_smul_smul] at hbound
  have hlower := neg_abs_le
    (a * (r ^ 2 * factorTwoCenteredArchBlock e +
          s ^ 2 * factorTwoCenteredArchBlock o) +
      b * (r * s * factorTwoCenteredAlternatingArch e o))
  nlinarith

/-- Separate nonnegative diagonal pencils and their exact disk determinant.
The proof chooses the boundary phase `b = sqrt (1-a²)` and applies the
quadratic-pencil characterization after independently scaling `e` and `o`. -/
theorem factorTwoArchRank_disk_schur
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o)
    (heven : Function.Even e) (hodd : Function.Odd o)
    (a : ℝ) (ha : a ^ 2 ≤ 1) :
    let E := factorTwoEvenRankEnergy e + a * factorTwoCenteredArchBlock e
    let O := factorTwoOddRankEnergy o + a * factorTwoCenteredArchBlock o
    0 ≤ E ∧ 0 ≤ O ∧
      (1 - a ^ 2) * factorTwoCenteredAlternatingArch e o ^ 2 ≤
        4 * E * O := by
  let E : ℝ := factorTwoEvenRankEnergy e + a * factorTwoCenteredArchBlock e
  let O : ℝ := factorTwoOddRankEnergy o + a * factorTwoCenteredArchBlock o
  let J : ℝ := factorTwoCenteredAlternatingArch e o
  let b : ℝ := Real.sqrt (1 - a ^ 2)
  have hrad : 0 ≤ 1 - a ^ 2 := by linarith
  have hb_sq : b ^ 2 = 1 - a ^ 2 := by
    dsimp only [b]
    exact Real.sq_sqrt hrad
  have hab : a ^ 2 + b ^ 2 ≤ 1 := by linarith
  have hpencil : ∀ r s : ℝ,
      0 ≤ E * r ^ 2 + 2 * (b * J / 2) * r * s + O * s ^ 2 := by
    intro r s
    have h := factorTwoArchRank_quadratic_nonneg
      e o hec hoc heven hodd a b hab r s
    dsimp only [E, O, J]
    nlinarith
  have hcoeff :=
    (real_quadratic_pencil_nonneg_iff E O (b * J / 2)).1 hpencil
  refine ⟨hcoeff.1, hcoeff.2.1, ?_⟩
  calc
    (1 - a ^ 2) * factorTwoCenteredAlternatingArch e o ^ 2 =
        4 * (b * J / 2) ^ 2 := by
      dsimp only [J]
      rw [← hb_sq]
      ring
    _ ≤ 4 * (E * O) :=
      mul_le_mul_of_nonneg_left hcoeff.2.2 (by norm_num)
    _ = 4 * E * O := by ring

theorem factorTwoEvenRankArchPencil_nonneg
    (e : ℝ → ℝ) (hec : Continuous e) (heven : Function.Even e)
    (a : ℝ) (ha : a ^ 2 ≤ 1) :
    0 ≤ factorTwoEvenRankEnergy e + a * factorTwoCenteredArchBlock e := by
  have h := factorTwoArchRank_disk_schur
    e (0 : ℝ → ℝ) hec (by fun_prop) heven
      (by intro x; simp only [Pi.zero_apply, neg_zero]) a ha
  exact h.1

theorem factorTwoOddRankArchPencil_nonneg
    (o : ℝ → ℝ) (hoc : Continuous o) (hodd : Function.Odd o)
    (a : ℝ) (ha : a ^ 2 ≤ 1) :
    0 ≤ factorTwoOddRankEnergy o + a * factorTwoCenteredArchBlock o := by
  have h := factorTwoArchRank_disk_schur
    (0 : ℝ → ℝ) o (by fun_prop) hoc (by intro x; rfl) hodd a ha
  exact h.2.1

theorem factorTwoArchRank_determinant
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o)
    (heven : Function.Even e) (hodd : Function.Odd o)
    (a : ℝ) (ha : a ^ 2 ≤ 1) :
    (1 - a ^ 2) * factorTwoCenteredAlternatingArch e o ^ 2 ≤
      4 *
        (factorTwoEvenRankEnergy e + a * factorTwoCenteredArchBlock e) *
        (factorTwoOddRankEnergy o + a * factorTwoCenteredArchBlock o) := by
  exact (factorTwoArchRank_disk_schur
    e o hec hoc heven hodd a ha).2.2

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseArchRankDiskSchur

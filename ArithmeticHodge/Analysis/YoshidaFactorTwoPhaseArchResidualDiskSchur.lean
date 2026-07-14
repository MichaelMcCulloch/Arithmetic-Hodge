import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseArchRankDiskSchur
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCoupledRankDominationObstruction
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseDiskSchur

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseArchResidualDiskSchur

noncomputable section

open CenteredEndpointCorrelation
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoCenteredPhysical
open YoshidaEndpointEvenLowHyperbolic
open YoshidaFactorTwoPhaseArchRankDiskSchur
open YoshidaFactorTwoPhaseCoupledRankDominationObstruction
open YoshidaFactorTwoPhaseDiskSchur
open YoshidaFactorTwoPhaseEnvelope
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseSymmetricCoercivity
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointOddSharpMassLoss
open YoshidaRenormalizedGeometricKernel

/-!
# Archimedean rank block and prime-preserving residual

The complete phase pencil is split into two genuine analytic mechanisms.
The first is the infinite hyperbolic-rank block, whose disk--Schur inequality
is already structural.  The second keeps the clean quadratic together with
both retained prime atoms.  No absolute-value majorant or finite mode cutoff
is introduced by this split.
-/

/-- The even diagonal left after extracting the positive infinite
archimedean rank energy.  The complete retained-prime block remains signed. -/
def factorTwoEvenRankPrimeResidualDiagonal
    (e : ℝ → ℝ) (a : ℝ) : ℝ :=
  yoshidaEndpointOddCleanQuadratic e - factorTwoEvenRankEnergy e -
    a * factorTwoCenteredPrimeBlock e

/-- The odd diagonal left after extracting the positive infinite
archimedean rank energy. -/
def factorTwoOddRankPrimeResidualDiagonal
    (o : ℝ → ℝ) (a : ℝ) : ℝ :=
  yoshidaEndpointOddCleanQuadratic o - factorTwoOddRankEnergy o -
    a * factorTwoCenteredPrimeBlock o

/-- The retained `p = 3` alternating atom.  The dyadic atom has no
alternating component because its shift is zero. -/
def factorTwoCenteredAlternatingPrime
    (e o : ℝ → ℝ) : ℝ :=
  -(Real.log 3 / Real.sqrt 3) *
    (factorTwoCenteredCrossCorrelation o e
        (factorTwoPrimeShift / yoshidaEndpointA) -
      factorTwoCenteredCrossCorrelation e o
        (factorTwoPrimeShift / yoshidaEndpointA))

/-- Exact extraction of the even archimedean rank pencil from the complete
signed diagonal. -/
theorem factorTwoEndpointPhaseDiagonal_eq_evenArch_add_residual
    (e : ℝ → ℝ) (a : ℝ) :
    factorTwoEndpointPhaseDiagonal e a =
      (factorTwoEvenRankEnergy e + a * factorTwoCenteredArchBlock e) +
        factorTwoEvenRankPrimeResidualDiagonal e a := by
  unfold factorTwoEndpointPhaseDiagonal
    factorTwoEvenRankPrimeResidualDiagonal
  rw [symmetricPerturbation_eq_arch_sub_primeBlock]
  ring

/-- Exact extraction of the odd archimedean rank pencil from the complete
signed diagonal. -/
theorem factorTwoEndpointPhaseDiagonal_eq_oddArch_add_residual
    (o : ℝ → ℝ) (a : ℝ) :
    factorTwoEndpointPhaseDiagonal o a =
      (factorTwoOddRankEnergy o + a * factorTwoCenteredArchBlock o) +
        factorTwoOddRankPrimeResidualDiagonal o a := by
  unfold factorTwoEndpointPhaseDiagonal
    factorTwoOddRankPrimeResidualDiagonal
  rw [symmetricPerturbation_eq_arch_sub_primeBlock]
  ring

/-- The complete alternating coordinate is exactly its infinite
archimedean rank block plus the signed retained-prime atom. -/
theorem factorTwoCenteredAlternatingCoupling_eq_arch_add_prime
    (e o : ℝ → ℝ) :
    factorTwoCenteredAlternatingCoupling e o =
      factorTwoCenteredAlternatingArch e o +
        factorTwoCenteredAlternatingPrime e o := by
  unfold factorTwoCenteredAlternatingCoupling
    factorTwoCenteredAlternatingArch factorTwoCenteredAlternatingPrime
  ring

/-- Full phase closure from the structural infinite-rank theorem and one
prime-preserving residual disk--Schur estimate.  This is the exact remaining
analytic target after the archimedean ranks have been discharged. -/
theorem factorTwoEndpointChannelPhase_nonneg_of_rankPrimeResidual_disk_schur
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o)
    (heven : Function.Even e) (hodd : Function.Odd o)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1)
    (hEvenResidual :
      0 ≤ factorTwoEvenRankPrimeResidualDiagonal e a)
    (hOddResidual :
      0 ≤ factorTwoOddRankPrimeResidualDiagonal o a)
    (hResidualDet :
      (1 - a ^ 2) * factorTwoCenteredAlternatingPrime e o ^ 2 ≤
        4 * factorTwoEvenRankPrimeResidualDiagonal e a *
          factorTwoOddRankPrimeResidualDiagonal o a) :
    0 ≤ factorTwoEndpointChannelPhase e o a b := by
  have ha : a ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg b]
  exact factorTwoEndpointChannelPhase_nonneg_of_split_disk_schur
    e o a b hab
    (factorTwoEvenRankEnergy e + a * factorTwoCenteredArchBlock e)
    (factorTwoOddRankEnergy o + a * factorTwoCenteredArchBlock o)
    (factorTwoCenteredAlternatingArch e o)
    (factorTwoEvenRankPrimeResidualDiagonal e a)
    (factorTwoOddRankPrimeResidualDiagonal o a)
    (factorTwoCenteredAlternatingPrime e o)
    (factorTwoEndpointPhaseDiagonal_eq_evenArch_add_residual e a)
    (factorTwoEndpointPhaseDiagonal_eq_oddArch_add_residual o a)
    (factorTwoCenteredAlternatingCoupling_eq_arch_add_prime e o)
    (factorTwoEvenRankArchPencil_nonneg e hec heven a ha)
    (factorTwoOddRankArchPencil_nonneg o hoc hodd a ha)
    hEvenResidual hOddResidual
    (factorTwoArchRank_determinant e o hec hoc heven hodd a ha)
    hResidualDet

/-! ## Sharpness of the block split

The preceding composition theorem is exact, but demanding positivity of its
second block is too strong.  The constant even profile makes that residual
strictly negative at `a = 1`.  Thus the production proof must keep part of
the clean low-mode form coupled to the archimedean ranks, rather than treating
the two displayed blocks as independently positive.
-/

private theorem four_thirds_lt_factorTwoEvenRankEnergy_one :
    (4 / 3 : ℝ) < factorTwoEvenRankEnergy (fun _ : ℝ ↦ 1) := by
  let C : ℝ := centeredCoshMoment (fun _ : ℝ ↦ 1)
    (yoshidaEndpointA / 2)
  let tail : ℝ := ∑' m : ℕ,
    Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
      centeredCoshMoment (fun _ : ℝ ↦ 1)
        (yoshidaEndpointA * oddRate (m + 1)) ^ 2
  have htail : 0 ≤ tail := by
    dsimp only [tail]
    exact tsum_nonneg fun m ↦ mul_nonneg (by positivity) (sq_nonneg _)
  have hA : (1 / 3 : ℝ) < yoshidaEndpointA := by
    have hlog := six_hundred_ninety_three_div_thousand_lt_log_two
    unfold yoshidaEndpointA
    norm_num at hlog ⊢
    linarith
  have hC : (2 : ℝ) < C := by
    dsimp only [C, centeredCoshMoment]
    rw [show (fun x : ℝ ↦
        Real.cosh ((yoshidaEndpointA / 2) * x) * 1) =
        fun x ↦ Real.cosh (yoshidaEndpointA * x / 2) by
      funext x
      simp only [mul_one]
      congr 1
      ring]
    exact two_lt_integral_yoshidaEndpoint_cosh
  have hexp : 1 < Real.exp yoshidaEndpointA :=
    Real.one_lt_exp_iff.mpr yoshidaEndpointA_pos
  have hCsq : (4 : ℝ) < C ^ 2 := by nlinarith
  have hhead : (4 / 3 : ℝ) <
      yoshidaEndpointA * Real.exp yoshidaEndpointA * C ^ 2 := by
    calc
      (4 / 3 : ℝ) < yoshidaEndpointA * 1 * 4 := by nlinarith
      _ < yoshidaEndpointA * Real.exp yoshidaEndpointA * 4 := by
        gcongr
      _ < yoshidaEndpointA * Real.exp yoshidaEndpointA * C ^ 2 := by
        gcongr
  unfold factorTwoEvenRankEnergy
  dsimp only [C, tail] at htail hhead ⊢
  nlinarith [yoshidaEndpointA_pos]

private theorem eight_ninths_lt_factorTwoCenteredPrimeBlock_one :
    (8 / 9 : ℝ) < factorTwoCenteredPrimeBlock (fun _ : ℝ ↦ 1) := by
  have hsqrt : Real.sqrt 2 < (3 / 2 : ℝ) := by
    have hsqrtSq : Real.sqrt 2 ^ 2 = 2 :=
      Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg 2]
  have halpha : (4 / 9 : ℝ) < Real.log 2 / Real.sqrt 2 := by
    have hsqrtPos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    rw [lt_div_iff₀ hsqrtPos]
    have hlog := six_hundred_ninety_three_div_thousand_lt_log_two
    nlinarith
  have htau := factorTwoPrimeShift_div_endpointA_mem_one_two
  have hcorr : 0 ≤ centeredEndpointCorrelation (fun _ : ℝ ↦ 1)
      (factorTwoPrimeShift / yoshidaEndpointA) := by
    unfold centeredEndpointCorrelation
    apply intervalIntegral.integral_nonneg
    · linarith [htau.2]
    · intro x _hx
      norm_num
  have hbeta : 0 ≤ Real.log 3 / Real.sqrt 3 := by positivity
  have hmass : (∫ x : ℝ in -1..1, (1 : ℝ) ^ 2) = 2 := by
    norm_num
  unfold factorTwoCenteredPrimeBlock
  simp only [hmass]
  nlinarith

/-- The independent residual block in the preceding sufficient theorem is
not positive in general.  This is a structural constant-profile obstruction,
not a finite search. -/
theorem constant_even_rankPrimeResidualDiagonal_lt_zero :
    factorTwoEvenRankPrimeResidualDiagonal (fun _ : ℝ ↦ 1) 1 < 0 := by
  have hclean := constant_clean_lt_eight_fifths
  have hrank := four_thirds_lt_factorTwoEvenRankEnergy_one
  have hprime := eight_ninths_lt_factorTwoCenteredPrimeBlock_one
  unfold factorTwoEvenRankPrimeResidualDiagonal
  norm_num
  nlinarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseArchResidualDiskSchur

import ArithmeticHodge.Analysis.YoshidaEvenHomogeneousCoercivity
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseEnvelope
import ArithmeticHodge.Analysis.YoshidaFactorTwoEndpointParityPencil
import ArithmeticHodge.Analysis.YoshidaRegularKernelLowerBound

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseTailCoercivity

noncomputable section

open YoshidaEndpointOddCleanPositive
open YoshidaEndpointScaledCorrelation
open YoshidaEndpointHyperbolicBound
open CenteredEndpointCorrelation
open YoshidaEndpointSingularCorrelation
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointParityPencil
open YoshidaOddHomogeneousCoercivity
open YoshidaEvenHomogeneousCoercivity
open YoshidaFactorTwoAdjacentKernel
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoPhaseEnvelope
open YoshidaRegularKernelBound
open YoshidaRegularKernelLowerBound
open YoshidaRenormalizedGeometricKernel
open YoshidaSectionSixAnalytic

/-!
# Phase-uniform coercivity on the factor-two Fourier tails

The existing `102 / 25` even-tail and `38 / 25` odd-tail coercivities are
transported exactly to the centered endpoint clean quadratic.  An exact
two-by-two budget then reduces phase-uniform positivity to three complete
operator estimates: `3 / 2` for each symmetric tail perturbation and
`25 / 8` for the alternating even--odd cross channel.
-/

/-- Pointwise bounds for the two nonsingular scalar branches of the complete
phase kernel.  The forward adjacent branch lies in `[1, 2]`; after its pole is
added back, the reflected branch lies in `[7/4, 61/32]`.  Keeping the branches
together gives the sharper scaled sum `11/8`, while their scaled difference
is at most `203/640` in absolute value. -/
theorem factorTwo_regular_phase_scalar_bounds
    {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
    let F := factorTwoAdjacentSmoothKernel
      (yoshidaEndpointA * (2 + t))
    let R := factorTwoCenteredReflectedRegularKernel t
    (1 : ℝ) ≤ F ∧ F ≤ 2 ∧
      (7 / 4 : ℝ) ≤ R ∧ R ≤ (61 / 32 : ℝ) ∧
      yoshidaEndpointA * (F + R) ≤ (11 / 8 : ℝ) ∧
      yoshidaEndpointA * |F - R| ≤ (203 / 640 : ℝ) := by
  let zPlus : ℝ := yoshidaEndpointA * (2 + t)
  let zMinus : ℝ := yoshidaEndpointA * (2 - t)
  let F : ℝ := factorTwoAdjacentSmoothKernel zPlus
  let R : ℝ := factorTwoCenteredReflectedRegularKernel t
  have hlogPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogLower : (2 / 3 : ℝ) < Real.log 2 := by
    exact (by norm_num : (2 / 3 : ℝ) < 0.6931471803).trans
      Real.log_two_gt_d9
  have hlogUpper : Real.log 2 < (7 / 10 : ℝ) := by
    exact Real.log_two_lt_d9.trans (by norm_num)
  have hzPlusPos : 0 < zPlus := by
    dsimp only [zPlus, yoshidaEndpointA]
    exact mul_pos (div_pos hlogPos (by norm_num)) (by linarith)
  have hzPlusLower : Real.log 2 ≤ zPlus := by
    dsimp only [zPlus, yoshidaEndpointA]
    nlinarith
  have hzPlusUpper : zPlus ≤ 2 * Real.log 2 := by
    dsimp only [zPlus, yoshidaEndpointA]
    nlinarith
  have hzMinus0 : 0 ≤ zMinus := by
    dsimp only [zMinus]
    exact mul_nonneg yoshidaEndpointA_pos.le (by linarith)
  have hzMinusUpper : zMinus ≤ Real.log 2 := by
    dsimp only [zMinus, yoshidaEndpointA]
    nlinarith
  have hFLower : (1 : ℝ) ≤ F := by
    have hdecomp :=
      factorTwoAdjacentSmoothKernel_eq_cosh_sub_regular_sub_pole
        hzPlusPos.ne'
    have hregular := yoshidaRegularKernel_le_quarter hzPlusPos.le
    have hcosh := Real.one_le_cosh (zPlus / 2)
    have hpole : 1 / (2 * zPlus) ≤ (3 / 4 : ℝ) := by
      rw [div_le_iff₀ (mul_pos (by norm_num) hzPlusPos)]
      nlinarith
    dsimp only [F]
    rw [hdecomp]
    nlinarith
  have hFUpper : F ≤ (2 : ℝ) := by
    have hseries :=
      factorTwoAdjacentSmoothKernel_eq_exp_sub_tsum hzPlusPos
    have hsum : 0 ≤
        ∑' m : ℕ, Real.exp (-oddRate (m + 1) * zPlus) :=
      tsum_nonneg fun m ↦ (Real.exp_pos _).le
    have hexp : Real.exp (zPlus / 2) ≤ 2 := by
      calc
        Real.exp (zPlus / 2) ≤ Real.exp (Real.log 2) :=
          Real.exp_le_exp.mpr (by linarith)
        _ = 2 := Real.exp_log (by norm_num)
    dsimp only [F]
    rw [hseries]
    linarith
  have hRDef :
      R = 2 * Real.cosh (zMinus / 2) - yoshidaRegularKernel zMinus := by
    rfl
  have hregularMinusUpper : yoshidaRegularKernel zMinus ≤ (1 / 4 : ℝ) :=
    yoshidaRegularKernel_le_quarter hzMinus0
  have hRLower : (7 / 4 : ℝ) ≤ R := by
    have hcosh := Real.one_le_cosh (zMinus / 2)
    rw [hRDef]
    nlinarith
  have hregularMinusLower :
      (7 / 32 : ℝ) ≤ yoshidaRegularKernel zMinus :=
    seven_div_thirty_two_le_yoshidaRegularKernel hzMinus0 hzMinusUpper
  have hsqrtPos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrtSq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hexpHalf : Real.exp (Real.log 2 / 2) = Real.sqrt 2 := by
    rw [← Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    exact Real.exp_log hsqrtPos
  have hcoshEndpoint :
      2 * Real.cosh (Real.log 2 / 2) = 3 / Real.sqrt 2 := by
    rw [Real.cosh_eq, hexpHalf, Real.exp_neg, hexpHalf]
    field_simp [hsqrtPos.ne']
    nlinarith
  have hcoshMonotone :
      Real.cosh (zMinus / 2) ≤ Real.cosh (Real.log 2 / 2) := by
    rw [Real.cosh_le_cosh]
    rw [abs_of_nonneg (by positivity : 0 ≤ Real.log 2 / 2),
      abs_of_nonneg (by linarith : 0 ≤ zMinus / 2)]
    linarith
  have hsqrtLower : (24 / 17 : ℝ) < Real.sqrt 2 := by
    nlinarith
  have hhyperbolicUpper :
      2 * Real.cosh (zMinus / 2) ≤ (17 / 8 : ℝ) := by
    have hinv : 3 / Real.sqrt 2 < (17 / 8 : ℝ) := by
      rw [div_lt_iff₀ hsqrtPos]
      nlinarith
    rw [← hcoshEndpoint] at hinv
    nlinarith
  have hRUpper : R ≤ (61 / 32 : ℝ) := by
    rw [hRDef]
    nlinarith
  have hA0 : 0 ≤ yoshidaEndpointA := yoshidaEndpointA_pos.le
  have hAUpper : yoshidaEndpointA ≤ (7 / 20 : ℝ) := by
    unfold yoshidaEndpointA
    linarith
  have hsum0 : 0 ≤ F + R := by linarith
  have hsumUpper : F + R ≤ (125 / 32 : ℝ) := by linarith
  have hscaledSum :
      yoshidaEndpointA * (F + R) ≤ (11 / 8 : ℝ) := by
    calc
      yoshidaEndpointA * (F + R) ≤
          (7 / 20 : ℝ) * (F + R) :=
        mul_le_mul_of_nonneg_right hAUpper hsum0
      _ ≤ (7 / 20 : ℝ) * (125 / 32 : ℝ) :=
        mul_le_mul_of_nonneg_left hsumUpper (by norm_num)
      _ ≤ (11 / 8 : ℝ) := by norm_num
  have hdiff : |F - R| ≤ (29 / 32 : ℝ) := by
    rw [abs_le]
    constructor <;> linarith
  have hscaledDiff :
      yoshidaEndpointA * |F - R| ≤ (203 / 640 : ℝ) := by
    calc
      yoshidaEndpointA * |F - R| ≤
          (7 / 20 : ℝ) * |F - R| :=
        mul_le_mul_of_nonneg_right hAUpper (abs_nonneg _)
      _ ≤ (7 / 20 : ℝ) * (29 / 32 : ℝ) :=
        mul_le_mul_of_nonneg_left hdiff (by norm_num)
      _ = (203 / 640 : ℝ) := by norm_num
  exact ⟨hFLower, hFUpper, hRLower, hRUpper, hscaledSum, hscaledDiff⟩

/-- The adjacent smooth kernel is monotone on the positive half-line.  Its
rank-one series has an increasing exponential head and a decreasing positive
tail. -/
theorem factorTwoAdjacentSmoothKernel_mono_of_pos
    {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    factorTwoAdjacentSmoothKernel s ≤
      factorTwoAdjacentSmoothKernel t := by
  have ht : 0 < t := hs.trans_le hst
  have hsFull : Summable
      (fun k : ℕ ↦ Real.exp (-oddRate k * s)) := by
    have hscaled := (hasSum_oddExponentials hs).summable.mul_left (1 / 2 : ℝ)
    convert hscaled using 1
    funext k
    ring
  have htFull : Summable
      (fun k : ℕ ↦ Real.exp (-oddRate k * t)) := by
    have hscaled := (hasSum_oddExponentials ht).summable.mul_left (1 / 2 : ℝ)
    convert hscaled using 1
    funext k
    ring
  have hsTail : Summable
      (fun m : ℕ ↦ Real.exp (-oddRate (m + 1) * s)) := by
    simpa only [Nat.add_comm] using (summable_nat_add_iff 1).2 hsFull
  have htTail : Summable
      (fun m : ℕ ↦ Real.exp (-oddRate (m + 1) * t)) := by
    simpa only [Nat.add_comm] using (summable_nat_add_iff 1).2 htFull
  have hterm : ∀ m : ℕ,
      Real.exp (-oddRate (m + 1) * t) ≤
        Real.exp (-oddRate (m + 1) * s) := by
    intro m
    apply Real.exp_le_exp.mpr
    have hr := oddRate_pos (m + 1)
    nlinarith
  have htail := htTail.tsum_le_tsum hterm hsTail
  rw [factorTwoAdjacentSmoothKernel_eq_exp_sub_tsum hs,
    factorTwoAdjacentSmoothKernel_eq_exp_sub_tsum ht]
  have hhead : Real.exp (s / 2) ≤ Real.exp (t / 2) :=
    Real.exp_le_exp.mpr (by linarith)
  linarith

/-- The complete alternating scalar, with its Cauchy pole and regular
correction still recombined, is positive and is dominated by `27/40` times
the Carleman kernel.  This is the scalar estimate whose parity-folded
Carleman norm gives the required `25/8` cross-channel constant. -/
theorem factorTwo_complete_antisymmetric_scalar_bounds
    {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t < 2) :
    0 ≤ yoshidaEndpointA *
        factorTwoAntisymmetricWeight (yoshidaEndpointA * t) ∧
      yoshidaEndpointA *
          factorTwoAntisymmetricWeight (yoshidaEndpointA * t) ≤
        (27 / 40 : ℝ) / (2 - t) := by
  let zPlus : ℝ := yoshidaEndpointA * (2 + t)
  let zMinus : ℝ := yoshidaEndpointA * (2 - t)
  let F : ℝ := factorTwoAdjacentSmoothKernel zPlus
  let R : ℝ := factorTwoCenteredReflectedRegularKernel t
  have hzMinusPos : 0 < zMinus :=
    mul_pos yoshidaEndpointA_pos (by linarith)
  have hzOrder : zMinus ≤ zPlus := by
    dsimp only [zMinus, zPlus]
    nlinarith [yoshidaEndpointA_pos]
  have hmono : factorTwoAdjacentSmoothKernel zMinus ≤
      factorTwoAdjacentSmoothKernel zPlus :=
    factorTwoAdjacentSmoothKernel_mono_of_pos hzMinusPos hzOrder
  have hweightRaw :
      factorTwoAntisymmetricWeight (yoshidaEndpointA * t) =
        factorTwoAdjacentSmoothKernel zPlus -
          factorTwoAdjacentSmoothKernel zMinus := by
    unfold factorTwoAntisymmetricWeight
    rw [factorTwoLogLength_eq_two_mul_yoshidaEndpointA]
    dsimp only [zPlus, zMinus]
    congr 2 <;> ring
  have hnonneg : 0 ≤ yoshidaEndpointA *
      factorTwoAntisymmetricWeight (yoshidaEndpointA * t) := by
    rw [hweightRaw]
    exact mul_nonneg yoshidaEndpointA_pos.le (sub_nonneg.mpr hmono)
  have hminus :=
    factorTwoAdjacentSmoothKernel_eq_cosh_sub_regular_sub_pole
      hzMinusPos.ne'
  have hminusRegular :
      factorTwoAdjacentSmoothKernel zMinus = R - 1 / (2 * zMinus) := by
    rw [hminus]
    rfl
  have hcomplete :
      yoshidaEndpointA *
          factorTwoAntisymmetricWeight (yoshidaEndpointA * t) =
        yoshidaEndpointA * (F - R) + 1 / (2 * (2 - t)) := by
    rw [hweightRaw, hminusRegular]
    dsimp only [F]
    have hden : 2 - t ≠ 0 := by linarith
    dsimp only [zMinus]
    field_simp [yoshidaEndpointA_pos.ne', hden]
    ring
  have hb := factorTwo_regular_phase_scalar_bounds ht0 ht2.le
  change (1 : ℝ) ≤ F ∧ F ≤ 2 ∧
      (7 / 4 : ℝ) ≤ R ∧ R ≤ (61 / 32 : ℝ) ∧
      yoshidaEndpointA * (F + R) ≤ (11 / 8 : ℝ) ∧
      yoshidaEndpointA * |F - R| ≤ (203 / 640 : ℝ) at hb
  have hAUpper : yoshidaEndpointA ≤ (7 / 20 : ℝ) := by
    unfold yoshidaEndpointA
    nlinarith [Real.log_two_lt_d9]
  have hregularUpper :
      yoshidaEndpointA * (F - R) ≤ (7 / 80 : ℝ) := by
    rcases hb with ⟨_hF0, hFUpper, hRLower, _⟩
    have hdiffUpper : F - R ≤ (1 / 4 : ℝ) := by linarith
    by_cases hdiff0 : 0 ≤ F - R
    · calc
        yoshidaEndpointA * (F - R) ≤
            (7 / 20 : ℝ) * (F - R) :=
          mul_le_mul_of_nonneg_right hAUpper hdiff0
        _ ≤ (7 / 20 : ℝ) * (1 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_left hdiffUpper (by norm_num)
        _ = (7 / 80 : ℝ) := by norm_num
    · have hnegative : yoshidaEndpointA * (F - R) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos yoshidaEndpointA_pos.le
          (le_of_not_ge hdiff0)
      linarith
  have hdPos : 0 < 2 - t := by linarith
  have hupper : yoshidaEndpointA *
        factorTwoAntisymmetricWeight (yoshidaEndpointA * t) ≤
      (27 / 40 : ℝ) / (2 - t) := by
    rw [le_div_iff₀ hdPos]
    rw [hcomplete]
    have hpole : (1 / (2 * (2 - t))) * (2 - t) = (1 / 2 : ℝ) := by
      field_simp [hdPos.ne']
    rw [add_mul, hpole]
    have hscaled :=
      mul_le_mul_of_nonneg_right hregularUpper hdPos.le
    nlinarith
  exact ⟨hnonneg, hupper⟩

/-- The retained `p = 3` coefficient costs strictly less than one unit of
geometric-mean energy. -/
theorem factorTwoPrimeThreeWeight_lt_one :
    Real.log 3 / Real.sqrt 3 < (1 : ℝ) := by
  have hlog3 : Real.log 3 < 2 * Real.log 2 := by
    calc
      Real.log 3 < Real.log 4 :=
        Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)
      _ = Real.log ((2 : ℝ) * 2) := by norm_num
      _ = 2 * Real.log 2 := by
        rw [Real.log_mul (by norm_num) (by norm_num)]
        ring
  have hlog2 : Real.log 2 < (7 / 10 : ℝ) :=
    Real.log_two_lt_d9.trans (by norm_num)
  have hsqrtPos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hsqrtSq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsqrtLower : (17 / 10 : ℝ) < Real.sqrt 3 := by
    nlinarith
  rw [div_lt_one hsqrtPos]
  nlinarith

/-- The retained-prime alternating phase atom is a geometric-mean
contraction.  The proof polarizes the existing sharp two-profile mass bound
over arbitrary real rescalings and then applies the exact quadratic-pencil
criterion. -/
theorem factorTwo_primePhaseDifference_sq_le_energy_mul
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    let Eu := ∫ x : ℝ in -1..1, u x ^ 2
    let Ev := ∫ x : ℝ in -1..1, v x ^ 2
    let D := factorTwoCenteredCrossCorrelation v u
        (factorTwoPrimeShift / yoshidaEndpointA) -
      factorTwoCenteredCrossCorrelation u v
        (factorTwoPrimeShift / yoshidaEndpointA)
    D ^ 2 ≤ Eu * Ev := by
  let Eu : ℝ := ∫ x : ℝ in -1..1, u x ^ 2
  let Ev : ℝ := ∫ x : ℝ in -1..1, v x ^ 2
  let tau : ℝ := factorTwoPrimeShift / yoshidaEndpointA
  let D : ℝ := factorTwoCenteredCrossCorrelation v u tau -
    factorTwoCenteredCrossCorrelation u v tau
  have henergyU (r : ℝ) :
      (∫ x : ℝ in -1..1, (r • u) x ^ 2) = r ^ 2 * Eu := by
    calc
      (∫ x : ℝ in -1..1, (r • u) x ^ 2) =
          ∫ x : ℝ in -1..1, r ^ 2 * u x ^ 2 := by
        apply intervalIntegral.integral_congr
        intro x _hx
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      _ = r ^ 2 * (∫ x : ℝ in -1..1, u x ^ 2) := by
        rw [intervalIntegral.integral_const_mul]
      _ = r ^ 2 * Eu := by rfl
  have henergyV (s : ℝ) :
      (∫ x : ℝ in -1..1, (s • v) x ^ 2) = s ^ 2 * Ev := by
    calc
      (∫ x : ℝ in -1..1, (s • v) x ^ 2) =
          ∫ x : ℝ in -1..1, s ^ 2 * v x ^ 2 := by
        apply intervalIntegral.integral_congr
        intro x _hx
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      _ = s ^ 2 * (∫ x : ℝ in -1..1, v x ^ 2) := by
        rw [intervalIntegral.integral_const_mul]
      _ = s ^ 2 * Ev := by rfl
  have hscaled (r s : ℝ) :
      2 * |r * s * D| ≤ r ^ 2 * Eu + s ^ 2 * Ev := by
    have h := two_mul_abs_phaseCorrelation_primeShift_le_mass
      (r • u) (s • v) (hu.const_smul r) (hv.const_smul s)
      0 1 (by norm_num)
    simp only [factorTwoCenteredPhaseCorrelation, zero_mul, one_mul,
      zero_add, factorTwoCenteredCrossCorrelation_smul_left,
      factorTwoCenteredCrossCorrelation_smul_right] at h
    rw [henergyU r, henergyV s] at h
    change 2 * |r * s * D| ≤ r ^ 2 * Eu + s ^ 2 * Ev
    dsimp only [D, tau]
    convert h using 1
    all_goals ring_nf
  have hquad : ∀ r s : ℝ,
      0 ≤ Eu * r ^ 2 + 2 * (-D) * r * s + Ev * s ^ 2 := by
    intro r s
    have h := hscaled r s
    have habs := le_abs_self (r * s * D)
    nlinarith
  have hdet := (real_quadratic_pencil_nonneg_iff Eu Ev (-D)).1 hquad
  dsimp only [Eu, Ev, D, tau] at hdet ⊢
  simpa only [neg_sq] using hdet.2.2

/-- For an even/odd pair, the sign in the actual alternating-coupling prime
subtraction turns the cross difference into `+2` times the ordered
even--odd correlation. -/
theorem factorTwo_alternating_prime_of_even_odd
    {e o : ℝ → ℝ} (he : Function.Even e) (ho : Function.Odd o) :
    -(Real.log 3 / Real.sqrt 3) *
        (factorTwoCenteredCrossCorrelation o e
            (factorTwoPrimeShift / yoshidaEndpointA) -
          factorTwoCenteredCrossCorrelation e o
            (factorTwoPrimeShift / yoshidaEndpointA)) =
      2 * (Real.log 3 / Real.sqrt 3) *
        factorTwoCenteredCrossCorrelation e o
          (factorTwoPrimeShift / yoshidaEndpointA) := by
  rw [factorTwoCenteredCrossCorrelation_swap_of_even_odd he ho]
  ring

/-- The retained `p = 3` term in `factorTwoCenteredAlternatingCoupling` is
bounded by the geometric mean of the two endpoint energies, with its exact
coefficient and subtraction sign retained. -/
theorem abs_factorTwo_alternating_prime_le_sqrt_energy
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o)
    (_he : Function.Even e) (_ho : Function.Odd o) :
    let Ee := ∫ x : ℝ in -1..1, e x ^ 2
    let Eo := ∫ x : ℝ in -1..1, o x ^ 2
    |-(Real.log 3 / Real.sqrt 3) *
        (factorTwoCenteredCrossCorrelation o e
            (factorTwoPrimeShift / yoshidaEndpointA) -
          factorTwoCenteredCrossCorrelation e o
            (factorTwoPrimeShift / yoshidaEndpointA))| ≤
      Real.sqrt (Ee * Eo) := by
  let Ee : ℝ := ∫ x : ℝ in -1..1, e x ^ 2
  let Eo : ℝ := ∫ x : ℝ in -1..1, o x ^ 2
  let D : ℝ := factorTwoCenteredCrossCorrelation o e
      (factorTwoPrimeShift / yoshidaEndpointA) -
    factorTwoCenteredCrossCorrelation e o
      (factorTwoPrimeShift / yoshidaEndpointA)
  let beta : ℝ := Real.log 3 / Real.sqrt 3
  have hEe : 0 ≤ Ee := by
    dsimp only [Ee]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun x _hx ↦ sq_nonneg (e x))
  have hEo : 0 ≤ Eo := by
    dsimp only [Eo]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun x _hx ↦ sq_nonneg (o x))
  have hprod : 0 ≤ Ee * Eo := mul_nonneg hEe hEo
  have hD := factorTwo_primePhaseDifference_sq_le_energy_mul
    e o hec hoc
  change D ^ 2 ≤ Ee * Eo at hD
  have hbeta0 : 0 ≤ beta := by
    dsimp only [beta]
    positivity
  have hbeta1 : beta ≤ 1 := by
    dsimp only [beta]
    exact factorTwoPrimeThreeWeight_lt_one.le
  have hbetaSq : beta ^ 2 ≤ 1 := by nlinarith
  have hprimeSq : (-beta * D) ^ 2 ≤ Ee * Eo := by
    calc
      (-beta * D) ^ 2 = beta ^ 2 * D ^ 2 := by ring
      _ ≤ beta ^ 2 * (Ee * Eo) :=
        mul_le_mul_of_nonneg_left hD (sq_nonneg beta)
      _ ≤ 1 * (Ee * Eo) :=
        mul_le_mul_of_nonneg_right hbetaSq hprod
      _ = Ee * Eo := one_mul _
  dsimp only [Ee, Eo, D, beta] at hprod hprimeSq ⊢
  apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [sq_abs, Real.sq_sqrt hprod]
  exact hprimeSq

/-- The Carleman majorant `27/40`, together with the retained-prime unit
bound, fits strictly inside the target cross constant `25/8`. -/
theorem carleman_prime_budget_lt_cross_constant :
    (27 / 40 : ℝ) * Real.pi + 1 < (25 / 8 : ℝ) := by
  nlinarith [Real.pi_lt_d4]

/-- The two recombined regular coefficients stay in the radius-`11/8` disk
for every phase in the closed unit disk.  This is the pointwise PSD condition
that keeps the forward and reflected branches together before applying the
two-vector correlation inequality. -/
theorem factorTwo_regular_phase_coefficient_radius
    {t a b : ℝ} (ht0 : 0 ≤ t) (ht2 : t ≤ 2)
    (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    let F := factorTwoAdjacentSmoothKernel
      (yoshidaEndpointA * (2 + t))
    let R := factorTwoCenteredReflectedRegularKernel t
    (a * (yoshidaEndpointA * (F + R))) ^ 2 +
        (b * (yoshidaEndpointA * (F - R))) ^ 2 ≤
      (11 / 8 : ℝ) ^ 2 := by
  dsimp only
  let F : ℝ := factorTwoAdjacentSmoothKernel
    (yoshidaEndpointA * (2 + t))
  let R : ℝ := factorTwoCenteredReflectedRegularKernel t
  have hb := factorTwo_regular_phase_scalar_bounds ht0 ht2
  change (1 : ℝ) ≤ F ∧ F ≤ 2 ∧
      (7 / 4 : ℝ) ≤ R ∧ R ≤ (61 / 32 : ℝ) ∧
      yoshidaEndpointA * (F + R) ≤ (11 / 8 : ℝ) ∧
      yoshidaEndpointA * |F - R| ≤ (203 / 640 : ℝ) at hb
  rcases hb with ⟨hF0, _hFUpper, hR0, _hRUpper, hsum, hdiff⟩
  let S : ℝ := yoshidaEndpointA * (F + R)
  let D : ℝ := yoshidaEndpointA * (F - R)
  have hS0 : 0 ≤ S := by
    dsimp only [S]
    exact mul_nonneg yoshidaEndpointA_pos.le (by linarith)
  have hSUpper : S ≤ (11 / 8 : ℝ) := by
    simpa only [S] using hsum
  have hSsq : S ^ 2 ≤ (11 / 8 : ℝ) ^ 2 :=
    (sq_le_sq₀ hS0 (by norm_num)).2 hSUpper
  have hDabs : |D| ≤ (203 / 640 : ℝ) := by
    dsimp only [D]
    rw [abs_mul, abs_of_pos yoshidaEndpointA_pos]
    exact hdiff
  have hDabs' : |D| ≤ (11 / 8 : ℝ) :=
    hDabs.trans (by norm_num)
  have hDsq : D ^ 2 ≤ (11 / 8 : ℝ) ^ 2 := by
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg D) (by norm_num)).2 hDabs'
  have haScaled := mul_le_mul_of_nonneg_left hSsq (sq_nonneg a)
  have hbScaled := mul_le_mul_of_nonneg_left hDsq (sq_nonneg b)
  dsimp only [S, D] at haScaled hbScaled ⊢
  calc
    (a * (yoshidaEndpointA * (F + R))) ^ 2 +
          (b * (yoshidaEndpointA * (F - R))) ^ 2 =
        a ^ 2 * (yoshidaEndpointA * (F + R)) ^ 2 +
          b ^ 2 * (yoshidaEndpointA * (F - R)) ^ 2 := by ring
    _ ≤ a ^ 2 * (11 / 8 : ℝ) ^ 2 +
          b ^ 2 * (11 / 8 : ℝ) ^ 2 := add_le_add haScaled hbScaled
    _ = (11 / 8 : ℝ) ^ 2 * (a ^ 2 + b ^ 2) := by ring
    _ ≤ (11 / 8 : ℝ) ^ 2 := by nlinarith

/-- Away from the null endpoint, adding back the explicit half-pole turns
the reflected branch into its regular scalar kernel exactly. -/
theorem factorTwo_reflectedDesingularizedPhaseKernel_eq_regular
    (u v : ℝ → ℝ) (a b : ℝ) {t : ℝ} (ht2 : t < 2) :
    factorTwoCenteredReflectedDesingularizedPhaseKernel u v a b t =
      yoshidaEndpointA * factorTwoCenteredReflectedRegularKernel t *
        factorTwoCenteredPhaseCorrelation u v a (-b) t := by
  have hbranch := endpoint_mul_reflectedPhaseBranch_eq_regular_sub_half_pole
    u v a b ht2
  rw [factorTwoLogLength_eq_two_mul_yoshidaEndpointA] at hbranch
  rw [show 2 * yoshidaEndpointA - yoshidaEndpointA * t =
      yoshidaEndpointA * (2 - t) by ring] at hbranch
  unfold factorTwoCenteredReflectedDesingularizedPhaseKernel
  rw [hbranch]
  have hden : 2 - t ≠ 0 := by linarith
  field_simp [hden]
  ring

/-- Complete pointwise envelope for the nonsingular phase kernel.  The
forward and reflected branches are recombined before Cauchy--Schwarz, so the
alternating coefficient is their difference rather than the sum of their
absolute values. -/
theorem two_mul_abs_regular_phaseKernel_le_boundaryTail
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1) {t : ℝ}
    (ht0 : 0 ≤ t) (ht2 : t < 2) :
    2 * |yoshidaEndpointA *
          factorTwoCenteredForwardPhaseKernel u v a b t +
        factorTwoCenteredReflectedDesingularizedPhaseKernel u v a b t| ≤
      (11 / 8 : ℝ) *
        (centeredEndpointBoundaryTail u (2 - t) +
          centeredEndpointBoundaryTail v (2 - t)) := by
  let F : ℝ := factorTwoAdjacentSmoothKernel
    (yoshidaEndpointA * (2 + t))
  let R : ℝ := factorTwoCenteredReflectedRegularKernel t
  let S : ℝ := yoshidaEndpointA * (F + R)
  let D : ℝ := yoshidaEndpointA * (F - R)
  have hradius := factorTwo_regular_phase_coefficient_radius
    ht0 ht2.le hphase
  change (a * S) ^ 2 + (b * D) ^ 2 ≤ (11 / 8 : ℝ) ^ 2 at hradius
  let alpha : ℝ := (a * S) / (11 / 8 : ℝ)
  let beta : ℝ := (b * D) / (11 / 8 : ℝ)
  have hab : alpha ^ 2 + beta ^ 2 ≤ 1 := by
    dsimp only [alpha, beta]
    norm_num at hradius ⊢
    nlinarith
  have hreflected :=
    factorTwo_reflectedDesingularizedPhaseKernel_eq_regular
      u v a b ht2
  have hcombine :
      yoshidaEndpointA *
          factorTwoCenteredForwardPhaseKernel u v a b t +
        factorTwoCenteredReflectedDesingularizedPhaseKernel u v a b t =
      (a * S) *
          (centeredEndpointCorrelation u t +
            centeredEndpointCorrelation v t) +
        (b * D) *
          (factorTwoCenteredCrossCorrelation v u t -
            factorTwoCenteredCrossCorrelation u v t) := by
    rw [hreflected]
    unfold factorTwoCenteredForwardPhaseKernel
      factorTwoCenteredPhaseCorrelation
    dsimp only [F, R, S, D]
    ring
  have hnormalized :
      yoshidaEndpointA *
          factorTwoCenteredForwardPhaseKernel u v a b t +
        factorTwoCenteredReflectedDesingularizedPhaseKernel u v a b t =
      (11 / 8 : ℝ) *
        factorTwoCenteredPhaseCorrelation u v alpha beta t := by
    rw [hcombine]
    unfold factorTwoCenteredPhaseCorrelation
    dsimp only [alpha, beta]
    ring
  have htail :=
    two_mul_abs_phaseCorrelation_two_sub_le_boundaryTail
      u v hu hv alpha beta hab (t := 2 - t) (by linarith)
  rw [show 2 - (2 - t) = t by ring] at htail
  rw [hnormalized, abs_mul, abs_of_nonneg (by norm_num :
    (0 : ℝ) ≤ 11 / 8)]
  nlinarith

/-- A real clipped profile's interval energy acquires exactly one endpoint
scale under centered rescaling. -/
theorem centeredRescale_energy_eq
    (r : YoshidaClippedPeriodicCore yoshidaEndpointA)
    (hreal : ∀ x : ℝ,
      ((r : YoshidaClippedSmooth yoshidaEndpointA) x).im = 0) :
    clippedIntervalEnergy (r : YoshidaClippedSmooth yoshidaEndpointA) =
      yoshidaEndpointA *
        ∫ x : ℝ in -1..1,
          centeredRescale yoshidaEndpointA (fun y ↦
            ((r : YoshidaClippedSmooth yoshidaEndpointA) y).re) x ^ 2 := by
  let q : ℝ → ℝ := fun x ↦
    ((r : YoshidaClippedSmooth yoshidaEndpointA) x).re ^ 2
  have hsubst := intervalIntegral.smul_integral_comp_mul_add
    (a := (-1 : ℝ)) (b := 1) q yoshidaEndpointA 0
  have hscale :
      (∫ x : ℝ in -yoshidaEndpointA..yoshidaEndpointA, q x) =
        yoshidaEndpointA * ∫ x : ℝ in -1..1,
          q (yoshidaEndpointA * x) := by
    simpa only [smul_eq_mul, mul_neg, mul_one, add_zero, mul_zero,
      zero_add] using hsubst.symm
  rw [clippedIntervalEnergy]
  calc
    (∫ x : ℝ in -yoshidaEndpointA..yoshidaEndpointA,
        ‖((r : YoshidaClippedSmooth yoshidaEndpointA) : ℝ → ℂ) x‖ ^ 2) =
        ∫ x : ℝ in -yoshidaEndpointA..yoshidaEndpointA, q x := by
      apply intervalIntegral.integral_congr
      intro x _hx
      change ‖((r : YoshidaClippedSmooth yoshidaEndpointA) : ℝ → ℂ) x‖ ^ 2 =
        ((r : YoshidaClippedSmooth yoshidaEndpointA) x).re ^ 2
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      rw [hreal x]
      ring
    _ = yoshidaEndpointA * ∫ x : ℝ in -1..1,
          q (yoshidaEndpointA * x) := hscale
    _ = _ := by rfl

/-- The proved `102 / 25` even-tail coercivity in centered endpoint
coordinates. -/
theorem evenTail_endpoint_clean_coercive
    (r : YoshidaClippedPeriodicCore yoshidaEndpointA)
    (htail : r ∈ yoshidaPeriodicCoreEvenTailSubmodule
      yoshidaEndpointA_pos 199)
    (hreal : ∀ x : ℝ,
      ((r : YoshidaClippedSmooth yoshidaEndpointA) x).im = 0)
    (hneg : (r : YoshidaClippedSmooth yoshidaEndpointA)
      (-yoshidaEndpointA) = 0)
    (hpos : (r : YoshidaClippedSmooth yoshidaEndpointA)
      yoshidaEndpointA = 0) :
    let w := centeredRescale yoshidaEndpointA (fun x ↦
      ((r : YoshidaClippedSmooth yoshidaEndpointA) x).re)
    (102 / 25 : ℝ) * (∫ x : ℝ in -1..1, w x ^ 2) ≤
      yoshidaEndpointOddCleanQuadratic w := by
  dsimp only
  have hc := evenOneNinetyNineTail_clipped_form_value_coercive r htail
  change (102 / 25 : ℝ) * clippedIntervalEnergy
      (r : YoshidaClippedSmooth yoshidaEndpointA) ≤
    clippedCriticalFormValue yoshidaEndpointA yoshidaEndpointA_pos
      (r : YoshidaClippedSmooth yoshidaEndpointA) at hc
  have he := centeredRescale_energy_eq r hreal
  have hq :=
    clippedCriticalFormValue_eq_endpoint_mul_clean_of_real_endpoints_zero
      r hreal hneg hpos
  rw [he, hq] at hc
  nlinarith [yoshidaEndpointA_pos]

/-- The proved `38 / 25` odd-tail coercivity in centered endpoint
coordinates. -/
theorem oddTail_endpoint_clean_coercive
    (r : YoshidaClippedPeriodicCore yoshidaEndpointA)
    (htail : r ∈ yoshidaPeriodicCoreOddTailSubmodule
      yoshidaEndpointA_pos 10)
    (hreal : ∀ x : ℝ,
      ((r : YoshidaClippedSmooth yoshidaEndpointA) x).im = 0)
    (hneg : (r : YoshidaClippedSmooth yoshidaEndpointA)
      (-yoshidaEndpointA) = 0)
    (hpos : (r : YoshidaClippedSmooth yoshidaEndpointA)
      yoshidaEndpointA = 0) :
    let w := centeredRescale yoshidaEndpointA (fun x ↦
      ((r : YoshidaClippedSmooth yoshidaEndpointA) x).re)
    (38 / 25 : ℝ) * (∫ x : ℝ in -1..1, w x ^ 2) ≤
      yoshidaEndpointOddCleanQuadratic w := by
  dsimp only
  have hc := oddTenTail_clipped_form_value_coercive r htail
  change (38 / 25 : ℝ) * clippedIntervalEnergy
      (r : YoshidaClippedSmooth yoshidaEndpointA) ≤
    clippedCriticalFormValue yoshidaEndpointA yoshidaEndpointA_pos
      (r : YoshidaClippedSmooth yoshidaEndpointA) at hc
  have he := centeredRescale_energy_eq r hreal
  have hq :=
    clippedCriticalFormValue_eq_endpoint_mul_clean_of_real_endpoints_zero
      r hreal hneg hpos
  rw [he, hq] at hc
  nlinarith [yoshidaEndpointA_pos]

/-- The phase budget has a strictly positive exact reserve.  In particular,
the convenient cross constant `25 / 8` is not merely admissible at equality:
after paying the two `3 / 2` diagonal perturbations, the determinant retains
the uniform margin `24431 / 192160000`. -/
theorem phase_tail_budget_with_reserve
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    (625 / 256 : ℝ) * b ^ 2 + (24431 / 192160000 : ℝ) ≤
      ((102 / 25 : ℝ) - (3 / 2 : ℝ) * |a|) *
        ((38 / 25 : ℝ) - (3 / 2 : ℝ) * |a|) := by
  have hx_sq : |a| ^ 2 = a ^ 2 := sq_abs a
  have hb_sq : b ^ 2 ≤ 1 - |a| ^ 2 := by
    nlinarith
  nlinarith [sq_nonneg (6005 * |a| - 5376)]

/-- Exact phase-uniform tail budget.  `3 / 2` L2 bounds for the two diagonal
perturbations and a `25 / 8` geometric-mean bound for the alternating cross
channel fit inside the asymmetric `102 / 25`, `38 / 25` coercivity pair. -/
theorem phase_uniform_of_tail_operator_bounds
    (Ee Eo Qe Qo Pe Po J a b : ℝ)
    (hEe : 0 ≤ Ee) (hEo : 0 ≤ Eo)
    (hQe : (102 / 25 : ℝ) * Ee ≤ Qe)
    (hQo : (38 / 25 : ℝ) * Eo ≤ Qo)
    (hPe : |Pe| ≤ (3 / 2 : ℝ) * Ee)
    (hPo : |Po| ≤ (3 / 2 : ℝ) * Eo)
    (hJ : J ^ 2 ≤ (625 / 64 : ℝ) * Ee * Eo)
    (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    0 ≤ Qe + Qo + a * (Pe + Po) + b * J := by
  let x : ℝ := |a|
  let Re : ℝ := (102 / 25 : ℝ) - (3 / 2 : ℝ) * x
  let Ro : ℝ := (38 / 25 : ℝ) - (3 / 2 : ℝ) * x
  have hx0 : 0 ≤ x := abs_nonneg a
  have hx_sq : x ^ 2 = a ^ 2 := by
    dsimp only [x]
    exact sq_abs a
  have hx1 : x ≤ 1 := by
    nlinarith [sq_nonneg b]
  have hRe : 0 ≤ Re := by
    dsimp only [Re]
    nlinarith
  have hRo : 0 ≤ Ro := by
    dsimp only [Ro]
    nlinarith
  have hPeMul : -(3 / 2 : ℝ) * x * Ee ≤ a * Pe := by
    calc
      -(3 / 2 : ℝ) * x * Ee = -(x * ((3 / 2 : ℝ) * Ee)) := by ring
      _ ≤ -(x * |Pe|) := neg_le_neg
        (mul_le_mul_of_nonneg_left hPe hx0)
      _ = -|a * Pe| := by rw [abs_mul]
      _ ≤ a * Pe := neg_abs_le (a * Pe)
  have hPoMul : -(3 / 2 : ℝ) * x * Eo ≤ a * Po := by
    calc
      -(3 / 2 : ℝ) * x * Eo = -(x * ((3 / 2 : ℝ) * Eo)) := by ring
      _ ≤ -(x * |Po|) := neg_le_neg
        (mul_le_mul_of_nonneg_left hPo hx0)
      _ = -|a * Po| := by rw [abs_mul]
      _ ≤ a * Po := neg_abs_le (a * Po)
  have hdiagE : Re * Ee ≤ Qe + a * Pe := by
    dsimp only [Re]
    nlinarith
  have hdiagO : Ro * Eo ≤ Qo + a * Po := by
    dsimp only [Ro]
    nlinarith
  have hb_sq : b ^ 2 ≤ 1 - x ^ 2 := by
    nlinarith
  have hphaseBudget :
      (625 / 256 : ℝ) * b ^ 2 ≤ Re * Ro := by
    have hpoly :
        (625 / 256 : ℝ) * (1 - x ^ 2) ≤ Re * Ro := by
      dsimp only [Re, Ro]
      nlinarith [sq_nonneg (6005 * x - 5376)]
    exact (mul_le_mul_of_nonneg_left hb_sq (by norm_num)).trans hpoly
  let AE : ℝ := Re * Ee
  let AO : ℝ := Ro * Eo
  let C : ℝ := b * J / 2
  have hAE : 0 ≤ AE := mul_nonneg hRe hEe
  have hAO : 0 ≤ AO := mul_nonneg hRo hEo
  have hC : C ^ 2 ≤ AE * AO := by
    have hJscaled := mul_le_mul_of_nonneg_left hJ (sq_nonneg b)
    have hEprod : 0 ≤ Ee * Eo := mul_nonneg hEe hEo
    have hbudgetScaled := mul_le_mul_of_nonneg_right hphaseBudget hEprod
    dsimp only [C, AE, AO]
    calc
      (b * J / 2) ^ 2 = (b ^ 2 * J ^ 2) / 4 := by ring
      _ ≤ (b ^ 2 * ((625 / 64 : ℝ) * Ee * Eo)) / 4 := by
        nlinarith
      _ = ((625 / 256 : ℝ) * b ^ 2) * (Ee * Eo) := by ring
      _ ≤ (Re * Ro) * (Ee * Eo) := hbudgetScaled
      _ = (Re * Ee) * (Ro * Eo) := by ring
  have hbase : 0 ≤ AE + 2 * C + AO := by
    have hp := (real_quadratic_pencil_nonneg_iff AE AO C).2
      ⟨hAE, hAO, hC⟩ 1 1
    simpa only [one_pow, mul_one] using hp
  dsimp only [AE, AO, C] at hbase
  nlinarith

/-- After transporting the tail coercivities through the clean bridge, only
the three displayed complete operator estimates remain for phase-uniform
endpoint positivity. -/
theorem endpoint_tail_phase_uniform_of_complete_bounds
    (re ro : YoshidaClippedPeriodicCore yoshidaEndpointA)
    (heTail : re ∈ yoshidaPeriodicCoreEvenTailSubmodule
      yoshidaEndpointA_pos 199)
    (hoTail : ro ∈ yoshidaPeriodicCoreOddTailSubmodule
      yoshidaEndpointA_pos 10)
    (heReal : ∀ x : ℝ,
      ((re : YoshidaClippedSmooth yoshidaEndpointA) x).im = 0)
    (hoReal : ∀ x : ℝ,
      ((ro : YoshidaClippedSmooth yoshidaEndpointA) x).im = 0)
    (heNeg : (re : YoshidaClippedSmooth yoshidaEndpointA)
      (-yoshidaEndpointA) = 0)
    (hePos : (re : YoshidaClippedSmooth yoshidaEndpointA)
      yoshidaEndpointA = 0)
    (hoNeg : (ro : YoshidaClippedSmooth yoshidaEndpointA)
      (-yoshidaEndpointA) = 0)
    (hoPos : (ro : YoshidaClippedSmooth yoshidaEndpointA)
      yoshidaEndpointA = 0)
    (hPe :
      let e := centeredRescale yoshidaEndpointA (fun x ↦
        ((re : YoshidaClippedSmooth yoshidaEndpointA) x).re)
      |factorTwoCenteredSymmetricPerturbation e| ≤
        (3 / 2 : ℝ) * ∫ x : ℝ in -1..1, e x ^ 2)
    (hPo :
      let o := centeredRescale yoshidaEndpointA (fun x ↦
        ((ro : YoshidaClippedSmooth yoshidaEndpointA) x).re)
      |factorTwoCenteredSymmetricPerturbation o| ≤
        (3 / 2 : ℝ) * ∫ x : ℝ in -1..1, o x ^ 2)
    (hJ :
      let e := centeredRescale yoshidaEndpointA (fun x ↦
        ((re : YoshidaClippedSmooth yoshidaEndpointA) x).re)
      let o := centeredRescale yoshidaEndpointA (fun x ↦
        ((ro : YoshidaClippedSmooth yoshidaEndpointA) x).re)
      factorTwoCenteredAlternatingCoupling e o ^ 2 ≤
        (625 / 64 : ℝ) *
          (∫ x : ℝ in -1..1, e x ^ 2) *
          (∫ x : ℝ in -1..1, o x ^ 2))
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    let e := centeredRescale yoshidaEndpointA (fun x ↦
      ((re : YoshidaClippedSmooth yoshidaEndpointA) x).re)
    let o := centeredRescale yoshidaEndpointA (fun x ↦
      ((ro : YoshidaClippedSmooth yoshidaEndpointA) x).re)
    0 ≤ yoshidaEndpointOddCleanQuadratic e +
        yoshidaEndpointOddCleanQuadratic o +
      a * (factorTwoCenteredSymmetricPerturbation e +
        factorTwoCenteredSymmetricPerturbation o) +
      b * factorTwoCenteredAlternatingCoupling e o := by
  dsimp only at hPe hPo hJ ⊢
  let e : ℝ → ℝ := centeredRescale yoshidaEndpointA (fun x ↦
    ((re : YoshidaClippedSmooth yoshidaEndpointA) x).re)
  let o : ℝ → ℝ := centeredRescale yoshidaEndpointA (fun x ↦
    ((ro : YoshidaClippedSmooth yoshidaEndpointA) x).re)
  let Ee : ℝ := ∫ x : ℝ in -1..1, e x ^ 2
  let Eo : ℝ := ∫ x : ℝ in -1..1, o x ^ 2
  have hEe : 0 ≤ Ee := by
    dsimp only [Ee]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun x _hx ↦ sq_nonneg (e x))
  have hEo : 0 ≤ Eo := by
    dsimp only [Eo]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun x _hx ↦ sq_nonneg (o x))
  have hQe : (102 / 25 : ℝ) * Ee ≤
      yoshidaEndpointOddCleanQuadratic e := by
    simpa only [e, Ee] using evenTail_endpoint_clean_coercive
      re heTail heReal heNeg hePos
  have hQo : (38 / 25 : ℝ) * Eo ≤
      yoshidaEndpointOddCleanQuadratic o := by
    simpa only [o, Eo] using oddTail_endpoint_clean_coercive
      ro hoTail hoReal hoNeg hoPos
  apply phase_uniform_of_tail_operator_bounds
    Ee Eo
    (yoshidaEndpointOddCleanQuadratic e)
    (yoshidaEndpointOddCleanQuadratic o)
    (factorTwoCenteredSymmetricPerturbation e)
    (factorTwoCenteredSymmetricPerturbation o)
    (factorTwoCenteredAlternatingCoupling e o)
    a b hEe hEo hQe hQo
  · simpa only [e, Ee] using hPe
  · simpa only [o, Eo] using hPo
  · simpa only [e, o, Ee, Eo] using hJ
  · exact hphase

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseTailCoercivity

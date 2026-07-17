import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectSixSchurStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineStaticNestedSchurStructural

set_option autoImplicit false

open Matrix

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineStaticFinalThreePositiveStructural

noncomputable section

open ThreeByThreeRankOneSchur
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointOcticPotential
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointOddLowGramExpansion
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoPhaseDiskSchur
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseIntrinsicNineComplementSchurStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectMatrixStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectSixSchurStructural
open YoshidaFactorTwoPhaseIntrinsicNineStaticNestedSchurStructural
open YoshidaFactorTwoPhaseIntrinsicNineUnbalancedStaticDiskStructural
open YoshidaFactorTwoPhaseIntrinsicFourP45MixedExpansion
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicSixP4Schur
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticEvenPositiveStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedDiskStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticSchurReductionStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticSplitStructural
open YoshidaFactorTwoPhaseIntrinsicSixStaticPlusObstruction
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoPhaseNestedThreeSchurStructural
open YoshidaFactorTwoPhaseP8StructuralReserve
open YoshidaFactorTwoPhaseProfileStaticSquareAssemblyStructural

/-!
# A retuned static completion of the final cutoff-nine three-plane

The six-mode endpoint transfer was chosen before the modes `P₆/P₈/P₇`
were retained.  Freezing those first nine transfer entries makes the two
nine-mode static endpoint completions incompatible.  The transfer below is
instead selected simultaneously on the complete `5 × 4` parity rectangle.

Its coefficients are exact rationals.  The phase argument uses them only
through the two corrected static endpoints, where the opposite transfer
copies cancel identically.  The remaining analytic work is therefore two
fixed, phase-free `3 × 3` Sylvester certificates.
-/

/-! ## The exact simultaneous transfer -/

/-- The retuned bilinear transfer.  Rows are `(P₀,P₂,P₄,P₆,P₈)` and
columns are `(P₁,P₃,P₅,P₇)`.

The common denominator is kept visible so that every later Schur gate is a
proof-transparent rational perturbation of an analytic endpoint entry. -/
def factorTwoIntrinsicNineRetunedTransfer
    (c0 c2 c4 c6 c8 c1 c3 c5 c7 : ℝ) : ℝ :=
  (5661 / 100000 : ℝ) * c0 * c1 +
    (4903 / 100000 : ℝ) * c0 * c3 +
    (3436 / 100000 : ℝ) * c0 * c5 +
    (1895 / 100000 : ℝ) * c0 * c7 +
    (5437 / 100000 : ℝ) * c2 * c1 +
    (4994 / 100000 : ℝ) * c2 * c3 +
    (3908 / 100000 : ℝ) * c2 * c5 +
    (2079 / 100000 : ℝ) * c2 * c7 +
    (4254 / 100000 : ℝ) * c4 * c1 +
    (4927 / 100000 : ℝ) * c4 * c3 +
    (5003 / 100000 : ℝ) * c4 * c5 +
    (2065 / 100000 : ℝ) * c4 * c7 +
    (1926 / 100000 : ℝ) * c6 * c1 +
    (4211 / 100000 : ℝ) * c6 * c3 +
    (3649 / 100000 : ℝ) * c6 * c5 -
    (1320 / 100000 : ℝ) * c6 * c7 +
    (141 / 100000 : ℝ) * c8 * c1 +
    (457 / 100000 : ℝ) * c8 * c3 +
    (1484 / 100000 : ℝ) * c8 * c5 +
    (52 / 100000 : ℝ) * c8 * c7

def factorTwoIntrinsicNineRetunedStaticPlus
    (c0 c2 c4 c6 c8 c1 c3 c5 c7 : ℝ) : ℝ :=
  factorTwoProfileStaticBranchForm
      (factorTwoIntrinsicNineEvenProfile c0 c2 c4 c6 c8)
      (factorTwoIntrinsicNineOddProfile c1 c3 c5 c7) 1 -
    2 * factorTwoIntrinsicNineRetunedTransfer
      c0 c2 c4 c6 c8 c1 c3 c5 c7

def factorTwoIntrinsicNineRetunedStaticMinus
    (c0 c2 c4 c6 c8 c1 c3 c5 c7 : ℝ) : ℝ :=
  factorTwoProfileStaticBranchForm
      (factorTwoIntrinsicNineEvenProfile c0 c2 c4 c6 c8)
      (factorTwoIntrinsicNineOddProfile c1 c3 c5 c7) (-1) +
    2 * factorTwoIntrinsicNineRetunedTransfer
      c0 c2 c4 c6 c8 c1 c3 c5 c7

def FactorTwoIntrinsicNineRetunedStaticPlusReserve : Prop :=
  ∀ c0 c2 c4 c6 c8 c1 c3 c5 c7 : ℝ,
    factorTwoIntrinsicNineReserveQuadratic c6 c8 c7 ≤
      factorTwoIntrinsicNineRetunedStaticPlus
        c0 c2 c4 c6 c8 c1 c3 c5 c7

def FactorTwoIntrinsicNineRetunedStaticMinusReserve : Prop :=
  ∀ c0 c2 c4 c6 c8 c1 c3 c5 c7 : ℝ,
    factorTwoIntrinsicNineReserveQuadratic c6 c8 c7 ≤
      factorTwoIntrinsicNineRetunedStaticMinus
        c0 c2 c4 c6 c8 c1 c3 c5 c7

/-! ## Independent parity scaling -/

theorem factorTwoIntrinsicNineRetunedTransfer_scale
    (r s c0 c2 c4 c6 c8 c1 c3 c5 c7 : ℝ) :
    factorTwoIntrinsicNineRetunedTransfer
        (r * c0) (r * c2) (r * c4) (r * c6) (r * c8)
        (s * c1) (s * c3) (s * c5) (s * c7) =
      r * s * factorTwoIntrinsicNineRetunedTransfer
        c0 c2 c4 c6 c8 c1 c3 c5 c7 := by
  unfold factorTwoIntrinsicNineRetunedTransfer
  ring

private theorem factorTwoEndpointPhaseDiagonal_smul
    (w : ℝ → ℝ) (c a : ℝ) :
    factorTwoEndpointPhaseDiagonal (c • w) a =
      c ^ 2 * factorTwoEndpointPhaseDiagonal w a := by
  have hclean : yoshidaEndpointOddCleanQuadratic (c • w) =
      c ^ 2 * yoshidaEndpointOddCleanQuadratic w := by
    simpa only [Pi.smul_apply, smul_eq_mul] using
      yoshidaEndpointOddCleanQuadratic_const_mul w c
  unfold factorTwoEndpointPhaseDiagonal
  rw [hclean, factorTwoCenteredSymmetricPerturbation_smul]
  ring_nf

private theorem factorTwoProfileStaticBranchForm_smul_smul
    (e o : ℝ → ℝ) (r s sigma : ℝ) :
    factorTwoProfileStaticBranchForm (r • e) (s • o) sigma =
      r ^ 2 * factorTwoEndpointPhaseDiagonal e sigma +
        s ^ 2 * factorTwoEndpointPhaseDiagonal o (-sigma) +
        r * s * factorTwoCenteredAlternatingCoupling e o := by
  unfold factorTwoProfileStaticBranchForm
  rw [factorTwoEndpointPhaseDiagonal_smul,
    factorTwoEndpointPhaseDiagonal_smul,
    factorTwoCenteredAlternatingCoupling_smul_left,
    factorTwoCenteredAlternatingCoupling_smul_right]
  ring_nf

theorem factorTwoIntrinsicNineRetunedStaticPlus_scale
    (r s c0 c2 c4 c6 c8 c1 c3 c5 c7 : ℝ) :
    factorTwoIntrinsicNineRetunedStaticPlus
        (r * c0) (r * c2) (r * c4) (r * c6) (r * c8)
        (s * c1) (s * c3) (s * c5) (s * c7) =
      r ^ 2 * factorTwoEndpointPhaseDiagonal
          (factorTwoIntrinsicNineEvenProfile c0 c2 c4 c6 c8) 1 +
        s ^ 2 * factorTwoEndpointPhaseDiagonal
          (factorTwoIntrinsicNineOddProfile c1 c3 c5 c7) (-1) +
        r * s *
          (factorTwoCenteredAlternatingCoupling
              (factorTwoIntrinsicNineEvenProfile c0 c2 c4 c6 c8)
              (factorTwoIntrinsicNineOddProfile c1 c3 c5 c7) -
            2 * factorTwoIntrinsicNineRetunedTransfer
              c0 c2 c4 c6 c8 c1 c3 c5 c7) := by
  unfold factorTwoIntrinsicNineRetunedStaticPlus
  rw [factorTwoIntrinsicNineEvenProfile_scale,
    factorTwoIntrinsicNineOddProfile_scale,
    factorTwoProfileStaticBranchForm_smul_smul,
    factorTwoIntrinsicNineRetunedTransfer_scale]
  ring_nf

theorem factorTwoIntrinsicNineRetunedStaticMinus_scale
    (r s c0 c2 c4 c6 c8 c1 c3 c5 c7 : ℝ) :
    factorTwoIntrinsicNineRetunedStaticMinus
        (r * c0) (r * c2) (r * c4) (r * c6) (r * c8)
        (s * c1) (s * c3) (s * c5) (s * c7) =
      r ^ 2 * factorTwoEndpointPhaseDiagonal
          (factorTwoIntrinsicNineEvenProfile c0 c2 c4 c6 c8) (-1) +
        s ^ 2 * factorTwoEndpointPhaseDiagonal
          (factorTwoIntrinsicNineOddProfile c1 c3 c5 c7) 1 +
        r * s *
          (factorTwoCenteredAlternatingCoupling
              (factorTwoIntrinsicNineEvenProfile c0 c2 c4 c6 c8)
              (factorTwoIntrinsicNineOddProfile c1 c3 c5 c7) +
            2 * factorTwoIntrinsicNineRetunedTransfer
              c0 c2 c4 c6 c8 c1 c3 c5 c7) := by
  unfold factorTwoIntrinsicNineRetunedStaticMinus
  rw [factorTwoIntrinsicNineEvenProfile_scale,
    factorTwoIntrinsicNineOddProfile_scale,
    factorTwoProfileStaticBranchForm_smul_smul,
    factorTwoIntrinsicNineRetunedTransfer_scale]
  ring_nf

def factorTwoIntrinsicNineEvenReserve (c6 c8 : ℝ) : ℝ :=
  factorTwoIntrinsicNineReserve6 * c6 ^ 2 +
    factorTwoIntrinsicNineReserve8 * c8 ^ 2

def factorTwoIntrinsicNineOddReserve (c7 : ℝ) : ℝ :=
  factorTwoIntrinsicNineReserve7 * c7 ^ 2

theorem factorTwoIntrinsicNineReserveQuadratic_eq_parity
    (c6 c8 c7 : ℝ) :
    factorTwoIntrinsicNineReserveQuadratic c6 c8 c7 =
      factorTwoIntrinsicNineEvenReserve c6 c8 +
        factorTwoIntrinsicNineOddReserve c7 := by
  rfl

/-! ## Reserve-aware disk interpolation -/

/-- The unbalanced endpoint interpolation remains valid after subtracting
independent even and odd diagonal reserves. -/
theorem scalar_phase_reserve_le_of_unbalanced_static_splits
    (QE PE QO PO J H RE RO a b : ℝ)
    (hab : a ^ 2 + b ^ 2 ≤ 1)
    (hPlus : ∀ r s : ℝ,
      r ^ 2 * RE + s ^ 2 * RO ≤
        r ^ 2 * (QE + PE) + s ^ 2 * (QO - PO) +
          r * s * (J - 2 * H))
    (hMinus : ∀ r s : ℝ,
      r ^ 2 * RE + s ^ 2 * RO ≤
        r ^ 2 * (QE - PE) + s ^ 2 * (QO + PO) +
          r * s * (J + 2 * H)) :
    RE + RO ≤ QE + QO + a * (PE + PO) + b * J := by
  have h := scalar_phase_nonneg_of_unbalanced_static_splits
    (QE - RE) PE (QO - RO) PO J H a b hab
    (by
      intro r s
      have hrs := hPlus r s
      nlinarith)
    (by
      intro r s
      have hrs := hMinus r s
      nlinarith)
  nlinarith

/-- The two retuned static reserve certificates imply the full cutoff-nine
reserve uniformly on the phase disk. -/
theorem factorTwoIntrinsicNineReserveQuadratic_le_phase_of_retuned_static
    (hplus : FactorTwoIntrinsicNineRetunedStaticPlusReserve)
    (hminus : FactorTwoIntrinsicNineRetunedStaticMinusReserve)
    (c0 c2 c4 c6 c8 c1 c3 c5 c7 a b : ℝ)
    (hab : a ^ 2 + b ^ 2 ≤ 1) :
    factorTwoIntrinsicNineReserveQuadratic c6 c8 c7 ≤
      factorTwoEndpointChannelPhase
        (factorTwoIntrinsicNineEvenProfile c0 c2 c4 c6 c8)
        (factorTwoIntrinsicNineOddProfile c1 c3 c5 c7) a b := by
  let e := factorTwoIntrinsicNineEvenProfile c0 c2 c4 c6 c8
  let o := factorTwoIntrinsicNineOddProfile c1 c3 c5 c7
  let EPlus := factorTwoEndpointPhaseDiagonal e 1
  let EMinus := factorTwoEndpointPhaseDiagonal e (-1)
  let OMinus := factorTwoEndpointPhaseDiagonal o (-1)
  let OPlus := factorTwoEndpointPhaseDiagonal o 1
  let QE := (EPlus + EMinus) / 2
  let PE := (EPlus - EMinus) / 2
  let QO := (OMinus + OPlus) / 2
  let PO := (OPlus - OMinus) / 2
  let J := factorTwoCenteredAlternatingCoupling e o
  let H := factorTwoIntrinsicNineRetunedTransfer
    c0 c2 c4 c6 c8 c1 c3 c5 c7
  let RE := factorTwoIntrinsicNineEvenReserve c6 c8
  let RO := factorTwoIntrinsicNineOddReserve c7
  have hPlus : ∀ r s : ℝ,
      r ^ 2 * RE + s ^ 2 * RO ≤
        r ^ 2 * (QE + PE) + s ^ 2 * (QO - PO) +
          r * s * (J - 2 * H) := by
    intro r s
    have hs := hplus
      (r * c0) (r * c2) (r * c4) (r * c6) (r * c8)
      (s * c1) (s * c3) (s * c5) (s * c7)
    rw [factorTwoIntrinsicNineRetunedStaticPlus_scale] at hs
    dsimp only [RE, RO, factorTwoIntrinsicNineEvenReserve,
      factorTwoIntrinsicNineOddReserve,
      factorTwoIntrinsicNineReserveQuadratic] at hs ⊢
    dsimp only [QE, PE, QO, PO, J, H, EPlus, EMinus, OMinus, OPlus,
      e, o]
    nlinarith
  have hMinus : ∀ r s : ℝ,
      r ^ 2 * RE + s ^ 2 * RO ≤
        r ^ 2 * (QE - PE) + s ^ 2 * (QO + PO) +
          r * s * (J + 2 * H) := by
    intro r s
    have hs := hminus
      (r * c0) (r * c2) (r * c4) (r * c6) (r * c8)
      (s * c1) (s * c3) (s * c5) (s * c7)
    rw [factorTwoIntrinsicNineRetunedStaticMinus_scale] at hs
    dsimp only [RE, RO, factorTwoIntrinsicNineEvenReserve,
      factorTwoIntrinsicNineOddReserve,
      factorTwoIntrinsicNineReserveQuadratic] at hs ⊢
    dsimp only [QE, PE, QO, PO, J, H, EPlus, EMinus, OMinus, OPlus,
      e, o]
    nlinarith
  have hscalar := scalar_phase_reserve_le_of_unbalanced_static_splits
    QE PE QO PO J H RE RO a b hab hPlus hMinus
  have hEvenAffine : QE + a * PE = factorTwoEndpointPhaseDiagonal e a := by
    dsimp only [QE, PE, EPlus, EMinus]
    unfold factorTwoEndpointPhaseDiagonal
    ring
  have hOddAffine : QO + a * PO = factorTwoEndpointPhaseDiagonal o a := by
    dsimp only [QO, PO, OMinus, OPlus]
    unfold factorTwoEndpointPhaseDiagonal
    ring
  rw [factorTwoEndpointChannelPhase_eq_diagonals]
  rw [factorTwoIntrinsicNineReserveQuadratic_eq_parity]
  dsimp only [RE, RO] at hscalar ⊢
  dsimp only [QE, PE, QO, PO, J] at hscalar
  rw [show
      (EPlus + EMinus) / 2 + (OMinus + OPlus) / 2 +
          a * ((EPlus - EMinus) / 2 + (OPlus - OMinus) / 2) +
          b * factorTwoCenteredAlternatingCoupling e o =
        (QE + a * PE) + (QO + a * PO) + b * J by
      dsimp only [QE, PE, QO, PO, J]
      ring] at hscalar
  rw [hEvenAffine, hOddAffine] at hscalar
  simpa only [e, o, J] using hscalar

/-! ## Connection to the direct matrix -/

theorem factorTwoIntrinsicNineReserveQuadratic_eq_P678LowReserve
    (c6 c8 c7 : ℝ) :
    factorTwoIntrinsicNineReserveQuadratic c6 c8 c7 =
      factorTwoIntrinsicNineP678LowReserve c6 c7 c8 := by
  unfold factorTwoIntrinsicNineReserveQuadratic
    factorTwoIntrinsicNineReserve6 factorTwoIntrinsicNineReserve8
    factorTwoIntrinsicNineReserve7 factorTwoIntrinsicNineP678LowReserve
  rw [factorTwoCenteredP6_energy, factorTwoCenteredP7_energy,
    factorTwoCenteredP8_energy]
  ring

/-- Once the two fixed static endpoint gates are proved, the complete direct
cutoff-nine matrix is positive semidefinite on the entire disk. -/
theorem factorTwoIntrinsicNineDirectLowMatrix_posSemidef_of_retuned_static
    (hplus : FactorTwoIntrinsicNineRetunedStaticPlusReserve)
    (hminus : FactorTwoIntrinsicNineRetunedStaticMinusReserve)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    (factorTwoIntrinsicNineDirectLowMatrix a b).PosSemidef := by
  apply factorTwoIntrinsicNineDirectLowMatrix_posSemidef_of_nonneg
  intro x
  unfold factorTwoIntrinsicNineDirectCoordinateQuadratic
  rw [factorTwoIntrinsicNineDirectLowQuadratic_eq_phase_sub_reserve]
  have hfull :=
    factorTwoIntrinsicNineReserveQuadratic_le_phase_of_retuned_static
      hplus hminus
      (x 0) (x 1) (x 2) (x 6) (x 7) (x 3) (x 4) (x 5) (x 8)
      a b hab
  rw [factorTwoIntrinsicNineReserveQuadratic_eq_P678LowReserve] at hfull
  have hreserve := factorTwoIntrinsicNineP678LowReserve_nonneg
    (x 6) (x 8) (x 7)
  nlinarith

/-- Consequently the requested final `Fin 3` Schur matrix is positive
semidefinite at every point of the phase circle. -/
theorem factorTwoIntrinsicNineDirectFinalSchurMatrix_posSemidef_of_retuned_static
    (hplus : FactorTwoIntrinsicNineRetunedStaticPlusReserve)
    (hminus : FactorTwoIntrinsicNineRetunedStaticMinusReserve)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    (factorTwoIntrinsicNineDirectFinalSchurMatrix a b).PosSemidef := by
  exact (factorTwoIntrinsicNineDirectLowMatrix_posSemidef_iff_finalSchur
    a b hab.le).mp
      (factorTwoIntrinsicNineDirectLowMatrix_posSemidef_of_retuned_static
        hplus hminus a b hab.le)

/-! ## The two fixed fraction-free final three-planes -/

/-- Entry table of the exact rational transfer. -/
def factorTwoIntrinsicNineRetunedH (i : Fin 5) (j : Fin 4) : ℝ :=
  match i.1, j.1 with
  | 0, 0 => 5661 / 100000
  | 0, 1 => 4903 / 100000
  | 0, 2 => 3436 / 100000
  | 0, _ => 1895 / 100000
  | 1, 0 => 5437 / 100000
  | 1, 1 => 4994 / 100000
  | 1, 2 => 3908 / 100000
  | 1, _ => 2079 / 100000
  | 2, 0 => 4254 / 100000
  | 2, 1 => 4927 / 100000
  | 2, 2 => 5003 / 100000
  | 2, _ => 2065 / 100000
  | 3, 0 => 1926 / 100000
  | 3, 1 => 4211 / 100000
  | 3, 2 => 3649 / 100000
  | 3, _ => -1320 / 100000
  | _, 0 => 141 / 100000
  | _, 1 => 457 / 100000
  | _, 2 => 1484 / 100000
  | _, _ => 52 / 100000

def factorTwoIntrinsicNineRetunedEvenBasis : Fin 5 → (ℝ → ℝ) :=
  ![centeredEvenP0, centeredEvenP2, factorTwoCenteredP4,
    factorTwoCenteredP6, factorTwoCenteredP8]

def factorTwoIntrinsicNineRetunedOddBasis : Fin 4 → (ℝ → ℝ) :=
  ![centeredP1, centeredP3, factorTwoCenteredP5, factorTwoCenteredP7]

def factorTwoIntrinsicNineRetunedKPlus (i : Fin 5) (j : Fin 4) : ℝ :=
  factorTwoCenteredAlternatingCoupling
      (factorTwoIntrinsicNineRetunedEvenBasis i)
      (factorTwoIntrinsicNineRetunedOddBasis j) / 2 -
    factorTwoIntrinsicNineRetunedH i j

def factorTwoIntrinsicNineRetunedKMinus (i : Fin 5) (j : Fin 4) : ℝ :=
  factorTwoCenteredAlternatingCoupling
      (factorTwoIntrinsicNineRetunedEvenBasis i)
      (factorTwoIntrinsicNineRetunedOddBasis j) / 2 +
    factorTwoIntrinsicNineRetunedH i j

/-! The first block is the unchanged same-parity `(P₀,P₂,P₄)` block. -/

def factorTwoIntrinsicNineRetunedEPlus (i j : Fin 3) : ℝ :=
  match i.1, j.1 with
  | 0, 0 => factorTwoIntrinsicSixUnbalancedEPlus00
  | 0, 1 => factorTwoIntrinsicSixUnbalancedEPlus02
  | 1, 0 => factorTwoIntrinsicSixUnbalancedEPlus02
  | 0, _ => factorTwoIntrinsicSixUnbalancedEPlus04
  | _, 0 => factorTwoIntrinsicSixUnbalancedEPlus04
  | 1, 1 => factorTwoIntrinsicSixUnbalancedEPlus22
  | 1, _ => factorTwoIntrinsicSixUnbalancedEPlus24
  | _, 1 => factorTwoIntrinsicSixUnbalancedEPlus24
  | _, _ => factorTwoIntrinsicSixUnbalancedEPlus44

def factorTwoIntrinsicNineRetunedEMinus (i j : Fin 3) : ℝ :=
  match i.1, j.1 with
  | 0, 0 => factorTwoIntrinsicSixUnbalancedEMinus00
  | 0, 1 => factorTwoIntrinsicSixUnbalancedEMinus02
  | 1, 0 => factorTwoIntrinsicSixUnbalancedEMinus02
  | 0, _ => factorTwoIntrinsicSixUnbalancedEMinus04
  | _, 0 => factorTwoIntrinsicSixUnbalancedEMinus04
  | 1, 1 => factorTwoIntrinsicSixUnbalancedEMinus22
  | 1, _ => factorTwoIntrinsicSixUnbalancedEMinus24
  | _, 1 => factorTwoIntrinsicSixUnbalancedEMinus24
  | _, _ => factorTwoIntrinsicSixUnbalancedEMinus44

def factorTwoIntrinsicNineRetunedOPlus (i j : Fin 3) : ℝ :=
  match i.1, j.1 with
  | 0, 0 => factorTwoIntrinsicSixUnbalancedOMinus11
  | 0, 1 => factorTwoIntrinsicSixUnbalancedOMinus13
  | 1, 0 => factorTwoIntrinsicSixUnbalancedOMinus13
  | 0, _ => factorTwoIntrinsicSixUnbalancedOMinus15
  | _, 0 => factorTwoIntrinsicSixUnbalancedOMinus15
  | 1, 1 => factorTwoIntrinsicSixUnbalancedOMinus33
  | 1, _ => factorTwoIntrinsicSixUnbalancedOMinus35
  | _, 1 => factorTwoIntrinsicSixUnbalancedOMinus35
  | _, _ => factorTwoIntrinsicSixUnbalancedOMinus55

def factorTwoIntrinsicNineRetunedOMinus (i j : Fin 3) : ℝ :=
  match i.1, j.1 with
  | 0, 0 => factorTwoIntrinsicSixUnbalancedOPlus11
  | 0, 1 => factorTwoIntrinsicSixUnbalancedOPlus13
  | 1, 0 => factorTwoIntrinsicSixUnbalancedOPlus13
  | 0, _ => factorTwoIntrinsicSixUnbalancedOPlus15
  | _, 0 => factorTwoIntrinsicSixUnbalancedOPlus15
  | 1, 1 => factorTwoIntrinsicSixUnbalancedOPlus33
  | 1, _ => factorTwoIntrinsicSixUnbalancedOPlus35
  | _, 1 => factorTwoIntrinsicSixUnbalancedOPlus35
  | _, _ => factorTwoIntrinsicSixUnbalancedOPlus55

/-- Retuned cross block from `(P₀,P₂,P₄)` to `(P₁,P₃,P₅)`. -/
def factorTwoIntrinsicNineRetunedBPlus (i r : Fin 3) : ℝ :=
  factorTwoIntrinsicNineRetunedKPlus ⟨r, by omega⟩ ⟨i, by omega⟩

def factorTwoIntrinsicNineRetunedBMinus (i r : Fin 3) : ℝ :=
  factorTwoIntrinsicNineRetunedKMinus ⟨r, by omega⟩ ⟨i, by omega⟩

private theorem factorTwoIntrinsicNineRetunedTransfer_eq_core_add_tail
    (c0 c2 c4 c6 c8 c1 c3 c5 c7 : ℝ) :
    factorTwoIntrinsicNineRetunedTransfer c0 c2 c4 c6 c8 c1 c3 c5 c7 =
      factorTwoIntrinsicNineRetunedTransfer c0 c2 c4 0 0 c1 c3 c5 0 +
        (1895 / 100000 : ℝ) * c0 * c7 +
        (2079 / 100000 : ℝ) * c2 * c7 +
        (2065 / 100000 : ℝ) * c4 * c7 +
        (1926 / 100000 : ℝ) * c6 * c1 +
        (4211 / 100000 : ℝ) * c6 * c3 +
        (3649 / 100000 : ℝ) * c6 * c5 -
        (1320 / 100000 : ℝ) * c6 * c7 +
        (141 / 100000 : ℝ) * c8 * c1 +
        (457 / 100000 : ℝ) * c8 * c3 +
        (1484 / 100000 : ℝ) * c8 * c5 +
        (52 / 100000 : ℝ) * c8 * c7 := by
  unfold factorTwoIntrinsicNineRetunedTransfer
  ring

/-! The original six-mode endpoint identities are purely algebraic in the
cross-block transfer.  Replaying that algebra with the first `3 × 3`
rectangle of the retuned transfer isolates the only part changed from the
older completion. -/

private theorem factorTwoIntrinsicNineRetunedSixPlus_eq_block
    (c0 c2 c4 c1 c3 c5 : ℝ) :
    factorTwoIntrinsicSixStaticEven 1 c0 c2 c4 +
          factorTwoIntrinsicSixStaticOdd 1 c1 c3 c5 +
          (factorTwoIntrinsicSixStaticAlternating c0 c2 c4 c1 c3 c5 -
            2 * factorTwoIntrinsicNineRetunedTransfer
              c0 c2 c4 0 0 c1 c3 c5 0) =
      symmetricQuadratic
          factorTwoIntrinsicSixUnbalancedEPlus00
          factorTwoIntrinsicSixUnbalancedEPlus02
          factorTwoIntrinsicSixUnbalancedEPlus04
          factorTwoIntrinsicSixUnbalancedEPlus22
          factorTwoIntrinsicSixUnbalancedEPlus24
          factorTwoIntrinsicSixUnbalancedEPlus44 c0 c2 c4 +
        2 * (c0 *
            (factorTwoIntrinsicNineRetunedBPlus 0 0 * c1 +
              factorTwoIntrinsicNineRetunedBPlus 1 0 * c3 +
              factorTwoIntrinsicNineRetunedBPlus 2 0 * c5) +
          c2 *
            (factorTwoIntrinsicNineRetunedBPlus 0 1 * c1 +
              factorTwoIntrinsicNineRetunedBPlus 1 1 * c3 +
              factorTwoIntrinsicNineRetunedBPlus 2 1 * c5) +
          c4 *
            (factorTwoIntrinsicNineRetunedBPlus 0 2 * c1 +
              factorTwoIntrinsicNineRetunedBPlus 1 2 * c3 +
              factorTwoIntrinsicNineRetunedBPlus 2 2 * c5)) +
        symmetricQuadratic
          factorTwoIntrinsicSixUnbalancedOMinus11
          factorTwoIntrinsicSixUnbalancedOMinus13
          factorTwoIntrinsicSixUnbalancedOMinus15
          factorTwoIntrinsicSixUnbalancedOMinus33
          factorTwoIntrinsicSixUnbalancedOMinus35
          factorTwoIntrinsicSixUnbalancedOMinus55 c1 c3 c5 := by
  unfold factorTwoIntrinsicSixStaticEven
    factorTwoIntrinsicSixStaticOdd
    factorTwoIntrinsicSixStaticAlternating
    factorTwoIntrinsicOddPhaseQuadratic
    factorTwoIntrinsicNineRetunedTransfer
    factorTwoIntrinsicSixUnbalancedEPlus00
    factorTwoIntrinsicSixUnbalancedEPlus02
    factorTwoIntrinsicSixUnbalancedEPlus04
    factorTwoIntrinsicSixUnbalancedEPlus22
    factorTwoIntrinsicSixUnbalancedEPlus24
    factorTwoIntrinsicSixUnbalancedEPlus44
    factorTwoIntrinsicSixUnbalancedOMinus11
    factorTwoIntrinsicSixUnbalancedOMinus13
    factorTwoIntrinsicSixUnbalancedOMinus15
    factorTwoIntrinsicSixUnbalancedOMinus33
    factorTwoIntrinsicSixUnbalancedOMinus35
    factorTwoIntrinsicSixUnbalancedOMinus55
    symmetricQuadratic
  simp [factorTwoIntrinsicNineRetunedBPlus,
    factorTwoIntrinsicNineRetunedKPlus,
    factorTwoIntrinsicNineRetunedEvenBasis,
    factorTwoIntrinsicNineRetunedOddBasis,
    factorTwoIntrinsicNineRetunedH]
  unfold factorTwoIntrinsicAlternating01 factorTwoIntrinsicAlternating03
    factorTwoIntrinsicAlternating21 factorTwoIntrinsicAlternating23
    factorTwoIntrinsicFourP45Cross05 factorTwoIntrinsicFourP45Cross25
    factorTwoIntrinsicFourP45Cross41 factorTwoIntrinsicFourP45Cross43
    factorTwoIntrinsicP45Alternating
  ring

private theorem factorTwoIntrinsicNineRetunedSixMinus_eq_block
    (c0 c2 c4 c1 c3 c5 : ℝ) :
    factorTwoIntrinsicSixStaticEven (-1) c0 c2 c4 +
          factorTwoIntrinsicSixStaticOdd (-1) c1 c3 c5 +
          (factorTwoIntrinsicSixStaticAlternating c0 c2 c4 c1 c3 c5 +
            2 * factorTwoIntrinsicNineRetunedTransfer
              c0 c2 c4 0 0 c1 c3 c5 0) =
      symmetricQuadratic
          factorTwoIntrinsicSixUnbalancedEMinus00
          factorTwoIntrinsicSixUnbalancedEMinus02
          factorTwoIntrinsicSixUnbalancedEMinus04
          factorTwoIntrinsicSixUnbalancedEMinus22
          factorTwoIntrinsicSixUnbalancedEMinus24
          factorTwoIntrinsicSixUnbalancedEMinus44 c0 c2 c4 +
        2 * (c0 *
            (factorTwoIntrinsicNineRetunedBMinus 0 0 * c1 +
              factorTwoIntrinsicNineRetunedBMinus 1 0 * c3 +
              factorTwoIntrinsicNineRetunedBMinus 2 0 * c5) +
          c2 *
            (factorTwoIntrinsicNineRetunedBMinus 0 1 * c1 +
              factorTwoIntrinsicNineRetunedBMinus 1 1 * c3 +
              factorTwoIntrinsicNineRetunedBMinus 2 1 * c5) +
          c4 *
            (factorTwoIntrinsicNineRetunedBMinus 0 2 * c1 +
              factorTwoIntrinsicNineRetunedBMinus 1 2 * c3 +
              factorTwoIntrinsicNineRetunedBMinus 2 2 * c5)) +
        symmetricQuadratic
          factorTwoIntrinsicSixUnbalancedOPlus11
          factorTwoIntrinsicSixUnbalancedOPlus13
          factorTwoIntrinsicSixUnbalancedOPlus15
          factorTwoIntrinsicSixUnbalancedOPlus33
          factorTwoIntrinsicSixUnbalancedOPlus35
          factorTwoIntrinsicSixUnbalancedOPlus55 c1 c3 c5 := by
  unfold factorTwoIntrinsicSixStaticEven
    factorTwoIntrinsicSixStaticOdd
    factorTwoIntrinsicSixStaticAlternating
    factorTwoIntrinsicOddPhaseQuadratic
    factorTwoIntrinsicNineRetunedTransfer
    factorTwoIntrinsicSixUnbalancedEMinus00
    factorTwoIntrinsicSixUnbalancedEMinus02
    factorTwoIntrinsicSixUnbalancedEMinus04
    factorTwoIntrinsicSixUnbalancedEMinus22
    factorTwoIntrinsicSixUnbalancedEMinus24
    factorTwoIntrinsicSixUnbalancedEMinus44
    factorTwoIntrinsicSixUnbalancedOPlus11
    factorTwoIntrinsicSixUnbalancedOPlus13
    factorTwoIntrinsicSixUnbalancedOPlus15
    factorTwoIntrinsicSixUnbalancedOPlus33
    factorTwoIntrinsicSixUnbalancedOPlus35
    factorTwoIntrinsicSixUnbalancedOPlus55
    symmetricQuadratic
  simp [factorTwoIntrinsicNineRetunedBMinus,
    factorTwoIntrinsicNineRetunedKMinus,
    factorTwoIntrinsicNineRetunedEvenBasis,
    factorTwoIntrinsicNineRetunedOddBasis,
    factorTwoIntrinsicNineRetunedH]
  unfold factorTwoIntrinsicAlternating01 factorTwoIntrinsicAlternating03
    factorTwoIntrinsicAlternating21 factorTwoIntrinsicAlternating23
    factorTwoIntrinsicFourP45Cross05 factorTwoIntrinsicFourP45Cross25
    factorTwoIntrinsicFourP45Cross41 factorTwoIntrinsicFourP45Cross43
    factorTwoIntrinsicP45Alternating
  ring

/-- Cross block from the first even plane to `(P₆,P₈,P₇)`. -/
def factorTwoIntrinsicNineRetunedDPlus (n r : Fin 3) : ℝ :=
  match n.1, r.1 with
  | 0, 0 => factorTwoIntrinsicNineEPlus06
  | 0, 1 => factorTwoIntrinsicNineEPlus26
  | 0, _ => factorTwoIntrinsicNineEPlus46
  | 1, 0 => factorTwoIntrinsicNineEPlus08
  | 1, 1 => factorTwoIntrinsicNineEPlus28
  | 1, _ => factorTwoIntrinsicNineEPlus48
  | _, 0 => factorTwoIntrinsicNineRetunedKPlus 0 3
  | _, 1 => factorTwoIntrinsicNineRetunedKPlus 1 3
  | _, _ => factorTwoIntrinsicNineRetunedKPlus 2 3

def factorTwoIntrinsicNineRetunedDMinus (n r : Fin 3) : ℝ :=
  match n.1, r.1 with
  | 0, 0 => factorTwoIntrinsicNineEMinus06
  | 0, 1 => factorTwoIntrinsicNineEMinus26
  | 0, _ => factorTwoIntrinsicNineEMinus46
  | 1, 0 => factorTwoIntrinsicNineEMinus08
  | 1, 1 => factorTwoIntrinsicNineEMinus28
  | 1, _ => factorTwoIntrinsicNineEMinus48
  | _, 0 => factorTwoIntrinsicNineRetunedKMinus 0 3
  | _, 1 => factorTwoIntrinsicNineRetunedKMinus 1 3
  | _, _ => factorTwoIntrinsicNineRetunedKMinus 2 3

/-- Cross block from `(P₁,P₃,P₅)` to `(P₆,P₈,P₇)`. -/
def factorTwoIntrinsicNineRetunedFPlus (i n : Fin 3) : ℝ :=
  match i.1, n.1 with
  | 0, 0 => factorTwoIntrinsicNineRetunedKPlus 3 0
  | 1, 0 => factorTwoIntrinsicNineRetunedKPlus 3 1
  | _, 0 => factorTwoIntrinsicNineRetunedKPlus 3 2
  | 0, 1 => factorTwoIntrinsicNineRetunedKPlus 4 0
  | 1, 1 => factorTwoIntrinsicNineRetunedKPlus 4 1
  | _, 1 => factorTwoIntrinsicNineRetunedKPlus 4 2
  | 0, _ => factorTwoIntrinsicNineOMinus17
  | 1, _ => factorTwoIntrinsicNineOMinus37
  | _, _ => factorTwoIntrinsicNineOMinus57

def factorTwoIntrinsicNineRetunedFMinus (i n : Fin 3) : ℝ :=
  match i.1, n.1 with
  | 0, 0 => factorTwoIntrinsicNineRetunedKMinus 3 0
  | 1, 0 => factorTwoIntrinsicNineRetunedKMinus 3 1
  | _, 0 => factorTwoIntrinsicNineRetunedKMinus 3 2
  | 0, 1 => factorTwoIntrinsicNineRetunedKMinus 4 0
  | 1, 1 => factorTwoIntrinsicNineRetunedKMinus 4 1
  | _, 1 => factorTwoIntrinsicNineRetunedKMinus 4 2
  | 0, _ => factorTwoIntrinsicNineOPlus17
  | 1, _ => factorTwoIntrinsicNineOPlus37
  | _, _ => factorTwoIntrinsicNineOPlus57

/-- The survivor block after subtracting the full structural reserve. -/
def factorTwoIntrinsicNineRetunedGPlus (n m : Fin 3) : ℝ :=
  match n.1, m.1 with
  | 0, 0 => factorTwoIntrinsicNineEPlus66 - factorTwoIntrinsicNineReserve6
  | 0, 1 => factorTwoIntrinsicNineEPlus68
  | 1, 0 => factorTwoIntrinsicNineEPlus68
  | 0, _ => factorTwoIntrinsicNineRetunedKPlus 3 3
  | _, 0 => factorTwoIntrinsicNineRetunedKPlus 3 3
  | 1, 1 => factorTwoIntrinsicNineEPlus88 - factorTwoIntrinsicNineReserve8
  | 1, _ => factorTwoIntrinsicNineRetunedKPlus 4 3
  | _, 1 => factorTwoIntrinsicNineRetunedKPlus 4 3
  | _, _ => factorTwoIntrinsicNineOMinus77 - factorTwoIntrinsicNineReserve7

def factorTwoIntrinsicNineRetunedGMinus (n m : Fin 3) : ℝ :=
  match n.1, m.1 with
  | 0, 0 => factorTwoIntrinsicNineEMinus66 - factorTwoIntrinsicNineReserve6
  | 0, 1 => factorTwoIntrinsicNineEMinus68
  | 1, 0 => factorTwoIntrinsicNineEMinus68
  | 0, _ => factorTwoIntrinsicNineRetunedKMinus 3 3
  | _, 0 => factorTwoIntrinsicNineRetunedKMinus 3 3
  | 1, 1 => factorTwoIntrinsicNineEMinus88 - factorTwoIntrinsicNineReserve8
  | 1, _ => factorTwoIntrinsicNineRetunedKMinus 4 3
  | _, 1 => factorTwoIntrinsicNineRetunedKMinus 4 3
  | _, _ => factorTwoIntrinsicNineOPlus77 - factorTwoIntrinsicNineReserve7

/-! ## Two nested fraction-free Schur reductions -/

private def retunedTEntry
    (d a00 a01 a02 a11 a12 a22 o : ℝ)
    (b0 b1 b2 c0 c1 c2 : ℝ) : ℝ :=
  d * o - unbalancedThreeAdjugatePair
    a00 a01 a02 a11 a12 a22 b0 b1 b2 c0 c1 c2

def factorTwoIntrinsicNineRetunedTPlus (i j : Fin 3) : ℝ :=
  retunedTEntry factorTwoIntrinsicSixUnbalancedEPlusDet
    factorTwoIntrinsicSixUnbalancedEPlus00
    factorTwoIntrinsicSixUnbalancedEPlus02
    factorTwoIntrinsicSixUnbalancedEPlus04
    factorTwoIntrinsicSixUnbalancedEPlus22
    factorTwoIntrinsicSixUnbalancedEPlus24
    factorTwoIntrinsicSixUnbalancedEPlus44
    (factorTwoIntrinsicNineRetunedOPlus i j)
    (factorTwoIntrinsicNineRetunedBPlus i 0)
    (factorTwoIntrinsicNineRetunedBPlus i 1)
    (factorTwoIntrinsicNineRetunedBPlus i 2)
    (factorTwoIntrinsicNineRetunedBPlus j 0)
    (factorTwoIntrinsicNineRetunedBPlus j 1)
    (factorTwoIntrinsicNineRetunedBPlus j 2)

def factorTwoIntrinsicNineRetunedTMinus (i j : Fin 3) : ℝ :=
  retunedTEntry factorTwoIntrinsicSixUnbalancedEMinusDet
    factorTwoIntrinsicSixUnbalancedEMinus00
    factorTwoIntrinsicSixUnbalancedEMinus02
    factorTwoIntrinsicSixUnbalancedEMinus04
    factorTwoIntrinsicSixUnbalancedEMinus22
    factorTwoIntrinsicSixUnbalancedEMinus24
    factorTwoIntrinsicSixUnbalancedEMinus44
    (factorTwoIntrinsicNineRetunedOMinus i j)
    (factorTwoIntrinsicNineRetunedBMinus i 0)
    (factorTwoIntrinsicNineRetunedBMinus i 1)
    (factorTwoIntrinsicNineRetunedBMinus i 2)
    (factorTwoIntrinsicNineRetunedBMinus j 0)
    (factorTwoIntrinsicNineRetunedBMinus j 1)
    (factorTwoIntrinsicNineRetunedBMinus j 2)

def factorTwoIntrinsicNineRetunedRPlus (i n : Fin 3) : ℝ :=
  factorTwoIntrinsicNineRentry
    factorTwoIntrinsicSixUnbalancedEPlusDet
    factorTwoIntrinsicSixUnbalancedEPlus00
    factorTwoIntrinsicSixUnbalancedEPlus02
    factorTwoIntrinsicSixUnbalancedEPlus04
    factorTwoIntrinsicSixUnbalancedEPlus22
    factorTwoIntrinsicSixUnbalancedEPlus24
    factorTwoIntrinsicSixUnbalancedEPlus44
    (factorTwoIntrinsicNineRetunedFPlus i n)
    (factorTwoIntrinsicNineRetunedBPlus i 0)
    (factorTwoIntrinsicNineRetunedBPlus i 1)
    (factorTwoIntrinsicNineRetunedBPlus i 2)
    (factorTwoIntrinsicNineRetunedDPlus n 0)
    (factorTwoIntrinsicNineRetunedDPlus n 1)
    (factorTwoIntrinsicNineRetunedDPlus n 2)

def factorTwoIntrinsicNineRetunedRMinus (i n : Fin 3) : ℝ :=
  factorTwoIntrinsicNineRentry
    factorTwoIntrinsicSixUnbalancedEMinusDet
    factorTwoIntrinsicSixUnbalancedEMinus00
    factorTwoIntrinsicSixUnbalancedEMinus02
    factorTwoIntrinsicSixUnbalancedEMinus04
    factorTwoIntrinsicSixUnbalancedEMinus22
    factorTwoIntrinsicSixUnbalancedEMinus24
    factorTwoIntrinsicSixUnbalancedEMinus44
    (factorTwoIntrinsicNineRetunedFMinus i n)
    (factorTwoIntrinsicNineRetunedBMinus i 0)
    (factorTwoIntrinsicNineRetunedBMinus i 1)
    (factorTwoIntrinsicNineRetunedBMinus i 2)
    (factorTwoIntrinsicNineRetunedDMinus n 0)
    (factorTwoIntrinsicNineRetunedDMinus n 1)
    (factorTwoIntrinsicNineRetunedDMinus n 2)

def factorTwoIntrinsicNineRetunedUPlus (n m : Fin 3) : ℝ :=
  factorTwoIntrinsicNineUentry
    factorTwoIntrinsicSixUnbalancedEPlusDet
    factorTwoIntrinsicSixUnbalancedEPlus00
    factorTwoIntrinsicSixUnbalancedEPlus02
    factorTwoIntrinsicSixUnbalancedEPlus04
    factorTwoIntrinsicSixUnbalancedEPlus22
    factorTwoIntrinsicSixUnbalancedEPlus24
    factorTwoIntrinsicSixUnbalancedEPlus44
    (factorTwoIntrinsicNineRetunedGPlus n m)
    (factorTwoIntrinsicNineRetunedDPlus n 0)
    (factorTwoIntrinsicNineRetunedDPlus n 1)
    (factorTwoIntrinsicNineRetunedDPlus n 2)
    (factorTwoIntrinsicNineRetunedDPlus m 0)
    (factorTwoIntrinsicNineRetunedDPlus m 1)
    (factorTwoIntrinsicNineRetunedDPlus m 2)

def factorTwoIntrinsicNineRetunedUMinus (n m : Fin 3) : ℝ :=
  factorTwoIntrinsicNineUentry
    factorTwoIntrinsicSixUnbalancedEMinusDet
    factorTwoIntrinsicSixUnbalancedEMinus00
    factorTwoIntrinsicSixUnbalancedEMinus02
    factorTwoIntrinsicSixUnbalancedEMinus04
    factorTwoIntrinsicSixUnbalancedEMinus22
    factorTwoIntrinsicSixUnbalancedEMinus24
    factorTwoIntrinsicSixUnbalancedEMinus44
    (factorTwoIntrinsicNineRetunedGMinus n m)
    (factorTwoIntrinsicNineRetunedDMinus n 0)
    (factorTwoIntrinsicNineRetunedDMinus n 1)
    (factorTwoIntrinsicNineRetunedDMinus n 2)
    (factorTwoIntrinsicNineRetunedDMinus m 0)
    (factorTwoIntrinsicNineRetunedDMinus m 1)
    (factorTwoIntrinsicNineRetunedDMinus m 2)

def factorTwoIntrinsicNineRetunedWPlus (n m : Fin 3) : ℝ :=
  factorTwoIntrinsicNineWentry
    (factorTwoIntrinsicNineRetunedTPlus 0 0)
    (factorTwoIntrinsicNineRetunedTPlus 0 1)
    (factorTwoIntrinsicNineRetunedTPlus 0 2)
    (factorTwoIntrinsicNineRetunedTPlus 1 1)
    (factorTwoIntrinsicNineRetunedTPlus 1 2)
    (factorTwoIntrinsicNineRetunedTPlus 2 2)
    (factorTwoIntrinsicNineRetunedUPlus n m)
    (factorTwoIntrinsicNineRetunedRPlus 0 n)
    (factorTwoIntrinsicNineRetunedRPlus 1 n)
    (factorTwoIntrinsicNineRetunedRPlus 2 n)
    (factorTwoIntrinsicNineRetunedRPlus 0 m)
    (factorTwoIntrinsicNineRetunedRPlus 1 m)
    (factorTwoIntrinsicNineRetunedRPlus 2 m)

def factorTwoIntrinsicNineRetunedWMinus (n m : Fin 3) : ℝ :=
  factorTwoIntrinsicNineWentry
    (factorTwoIntrinsicNineRetunedTMinus 0 0)
    (factorTwoIntrinsicNineRetunedTMinus 0 1)
    (factorTwoIntrinsicNineRetunedTMinus 0 2)
    (factorTwoIntrinsicNineRetunedTMinus 1 1)
    (factorTwoIntrinsicNineRetunedTMinus 1 2)
    (factorTwoIntrinsicNineRetunedTMinus 2 2)
    (factorTwoIntrinsicNineRetunedUMinus n m)
    (factorTwoIntrinsicNineRetunedRMinus 0 n)
    (factorTwoIntrinsicNineRetunedRMinus 1 n)
    (factorTwoIntrinsicNineRetunedRMinus 2 n)
    (factorTwoIntrinsicNineRetunedRMinus 0 m)
    (factorTwoIntrinsicNineRetunedRMinus 1 m)
    (factorTwoIntrinsicNineRetunedRMinus 2 m)

/-- The six fixed strict Sylvester gates left by the retuned plus completion. -/
def FactorTwoIntrinsicNineRetunedPlusFinalThreeGates : Prop :=
  0 < factorTwoIntrinsicNineRetunedTPlus 0 0 ∧
  0 < leadingMinorTwo
    (factorTwoIntrinsicNineRetunedTPlus 0 0)
    (factorTwoIntrinsicNineRetunedTPlus 0 1)
    (factorTwoIntrinsicNineRetunedTPlus 1 1) ∧
  0 < symmetricDeterminant
    (factorTwoIntrinsicNineRetunedTPlus 0 0)
    (factorTwoIntrinsicNineRetunedTPlus 0 1)
    (factorTwoIntrinsicNineRetunedTPlus 0 2)
    (factorTwoIntrinsicNineRetunedTPlus 1 1)
    (factorTwoIntrinsicNineRetunedTPlus 1 2)
    (factorTwoIntrinsicNineRetunedTPlus 2 2) ∧
  0 < factorTwoIntrinsicNineRetunedWPlus 0 0 ∧
  0 < leadingMinorTwo
    (factorTwoIntrinsicNineRetunedWPlus 0 0)
    (factorTwoIntrinsicNineRetunedWPlus 0 1)
    (factorTwoIntrinsicNineRetunedWPlus 1 1) ∧
  0 < symmetricDeterminant
    (factorTwoIntrinsicNineRetunedWPlus 0 0)
    (factorTwoIntrinsicNineRetunedWPlus 0 1)
    (factorTwoIntrinsicNineRetunedWPlus 0 2)
    (factorTwoIntrinsicNineRetunedWPlus 1 1)
    (factorTwoIntrinsicNineRetunedWPlus 1 2)
    (factorTwoIntrinsicNineRetunedWPlus 2 2)

def FactorTwoIntrinsicNineRetunedMinusFinalThreeGates : Prop :=
  0 < factorTwoIntrinsicNineRetunedTMinus 0 0 ∧
  0 < leadingMinorTwo
    (factorTwoIntrinsicNineRetunedTMinus 0 0)
    (factorTwoIntrinsicNineRetunedTMinus 0 1)
    (factorTwoIntrinsicNineRetunedTMinus 1 1) ∧
  0 < symmetricDeterminant
    (factorTwoIntrinsicNineRetunedTMinus 0 0)
    (factorTwoIntrinsicNineRetunedTMinus 0 1)
    (factorTwoIntrinsicNineRetunedTMinus 0 2)
    (factorTwoIntrinsicNineRetunedTMinus 1 1)
    (factorTwoIntrinsicNineRetunedTMinus 1 2)
    (factorTwoIntrinsicNineRetunedTMinus 2 2) ∧
  0 < factorTwoIntrinsicNineRetunedWMinus 0 0 ∧
  0 < leadingMinorTwo
    (factorTwoIntrinsicNineRetunedWMinus 0 0)
    (factorTwoIntrinsicNineRetunedWMinus 0 1)
    (factorTwoIntrinsicNineRetunedWMinus 1 1) ∧
  0 < symmetricDeterminant
    (factorTwoIntrinsicNineRetunedWMinus 0 0)
    (factorTwoIntrinsicNineRetunedWMinus 0 1)
    (factorTwoIntrinsicNineRetunedWMinus 0 2)
    (factorTwoIntrinsicNineRetunedWMinus 1 1)
    (factorTwoIntrinsicNineRetunedWMinus 1 2)
    (factorTwoIntrinsicNineRetunedWMinus 2 2)

private def retunedEllPlus
    (r : Fin 3) (c1 c3 c5 c6 c8 c7 : ℝ) : ℝ :=
  factorTwoIntrinsicNineRetunedBPlus 0 r * c1 +
    factorTwoIntrinsicNineRetunedBPlus 1 r * c3 +
    factorTwoIntrinsicNineRetunedBPlus 2 r * c5 +
    factorTwoIntrinsicNineRetunedDPlus 0 r * c6 +
    factorTwoIntrinsicNineRetunedDPlus 1 r * c8 +
    factorTwoIntrinsicNineRetunedDPlus 2 r * c7

private def retunedEllMinus
    (r : Fin 3) (c1 c3 c5 c6 c8 c7 : ℝ) : ℝ :=
  factorTwoIntrinsicNineRetunedBMinus 0 r * c1 +
    factorTwoIntrinsicNineRetunedBMinus 1 r * c3 +
    factorTwoIntrinsicNineRetunedBMinus 2 r * c5 +
    factorTwoIntrinsicNineRetunedDMinus 0 r * c6 +
    factorTwoIntrinsicNineRetunedDMinus 1 r * c8 +
    factorTwoIntrinsicNineRetunedDMinus 2 r * c7

private def retunedLowerPlus
    (c1 c3 c5 c6 c8 c7 : ℝ) : ℝ :=
  symmetricQuadratic
      (factorTwoIntrinsicNineRetunedOPlus 0 0)
      (factorTwoIntrinsicNineRetunedOPlus 0 1)
      (factorTwoIntrinsicNineRetunedOPlus 0 2)
      (factorTwoIntrinsicNineRetunedOPlus 1 1)
      (factorTwoIntrinsicNineRetunedOPlus 1 2)
      (factorTwoIntrinsicNineRetunedOPlus 2 2) c1 c3 c5 +
    2 * (c1 * (factorTwoIntrinsicNineRetunedFPlus 0 0 * c6 +
          factorTwoIntrinsicNineRetunedFPlus 0 1 * c8 +
          factorTwoIntrinsicNineRetunedFPlus 0 2 * c7) +
      c3 * (factorTwoIntrinsicNineRetunedFPlus 1 0 * c6 +
          factorTwoIntrinsicNineRetunedFPlus 1 1 * c8 +
          factorTwoIntrinsicNineRetunedFPlus 1 2 * c7) +
      c5 * (factorTwoIntrinsicNineRetunedFPlus 2 0 * c6 +
          factorTwoIntrinsicNineRetunedFPlus 2 1 * c8 +
          factorTwoIntrinsicNineRetunedFPlus 2 2 * c7)) +
    symmetricQuadratic
      (factorTwoIntrinsicNineRetunedGPlus 0 0)
      (factorTwoIntrinsicNineRetunedGPlus 0 1)
      (factorTwoIntrinsicNineRetunedGPlus 0 2)
      (factorTwoIntrinsicNineRetunedGPlus 1 1)
      (factorTwoIntrinsicNineRetunedGPlus 1 2)
      (factorTwoIntrinsicNineRetunedGPlus 2 2) c6 c8 c7

private def retunedLowerMinus
    (c1 c3 c5 c6 c8 c7 : ℝ) : ℝ :=
  symmetricQuadratic
      (factorTwoIntrinsicNineRetunedOMinus 0 0)
      (factorTwoIntrinsicNineRetunedOMinus 0 1)
      (factorTwoIntrinsicNineRetunedOMinus 0 2)
      (factorTwoIntrinsicNineRetunedOMinus 1 1)
      (factorTwoIntrinsicNineRetunedOMinus 1 2)
      (factorTwoIntrinsicNineRetunedOMinus 2 2) c1 c3 c5 +
    2 * (c1 * (factorTwoIntrinsicNineRetunedFMinus 0 0 * c6 +
          factorTwoIntrinsicNineRetunedFMinus 0 1 * c8 +
          factorTwoIntrinsicNineRetunedFMinus 0 2 * c7) +
      c3 * (factorTwoIntrinsicNineRetunedFMinus 1 0 * c6 +
          factorTwoIntrinsicNineRetunedFMinus 1 1 * c8 +
          factorTwoIntrinsicNineRetunedFMinus 1 2 * c7) +
      c5 * (factorTwoIntrinsicNineRetunedFMinus 2 0 * c6 +
          factorTwoIntrinsicNineRetunedFMinus 2 1 * c8 +
          factorTwoIntrinsicNineRetunedFMinus 2 2 * c7)) +
    symmetricQuadratic
      (factorTwoIntrinsicNineRetunedGMinus 0 0)
      (factorTwoIntrinsicNineRetunedGMinus 0 1)
      (factorTwoIntrinsicNineRetunedGMinus 0 2)
      (factorTwoIntrinsicNineRetunedGMinus 1 1)
      (factorTwoIntrinsicNineRetunedGMinus 1 2)
      (factorTwoIntrinsicNineRetunedGMinus 2 2) c6 c8 c7

/-- Exact first fraction-free completion for the retuned plus endpoint. -/
theorem factorTwoIntrinsicNineRetunedPlus_firstSchur_eq
    (c1 c3 c5 c6 c8 c7 : ℝ) :
    factorTwoIntrinsicSixUnbalancedEPlusDet *
          retunedLowerPlus c1 c3 c5 c6 c8 c7 -
        adjugateQuadratic
          factorTwoIntrinsicSixUnbalancedEPlus00
          factorTwoIntrinsicSixUnbalancedEPlus02
          factorTwoIntrinsicSixUnbalancedEPlus04
          factorTwoIntrinsicSixUnbalancedEPlus22
          factorTwoIntrinsicSixUnbalancedEPlus24
          factorTwoIntrinsicSixUnbalancedEPlus44
          (retunedEllPlus 0 c1 c3 c5 c6 c8 c7)
          (retunedEllPlus 1 c1 c3 c5 c6 c8 c7)
          (retunedEllPlus 2 c1 c3 c5 c6 c8 c7) =
      symmetricQuadratic
          (factorTwoIntrinsicNineRetunedTPlus 0 0)
          (factorTwoIntrinsicNineRetunedTPlus 0 1)
          (factorTwoIntrinsicNineRetunedTPlus 0 2)
          (factorTwoIntrinsicNineRetunedTPlus 1 1)
          (factorTwoIntrinsicNineRetunedTPlus 1 2)
          (factorTwoIntrinsicNineRetunedTPlus 2 2) c1 c3 c5 +
        2 * (c1 * (factorTwoIntrinsicNineRetunedRPlus 0 0 * c6 +
              factorTwoIntrinsicNineRetunedRPlus 0 1 * c8 +
              factorTwoIntrinsicNineRetunedRPlus 0 2 * c7) +
          c3 * (factorTwoIntrinsicNineRetunedRPlus 1 0 * c6 +
              factorTwoIntrinsicNineRetunedRPlus 1 1 * c8 +
              factorTwoIntrinsicNineRetunedRPlus 1 2 * c7) +
          c5 * (factorTwoIntrinsicNineRetunedRPlus 2 0 * c6 +
              factorTwoIntrinsicNineRetunedRPlus 2 1 * c8 +
              factorTwoIntrinsicNineRetunedRPlus 2 2 * c7)) +
        symmetricQuadratic
          (factorTwoIntrinsicNineRetunedUPlus 0 0)
          (factorTwoIntrinsicNineRetunedUPlus 0 1)
          (factorTwoIntrinsicNineRetunedUPlus 0 2)
          (factorTwoIntrinsicNineRetunedUPlus 1 1)
          (factorTwoIntrinsicNineRetunedUPlus 1 2)
          (factorTwoIntrinsicNineRetunedUPlus 2 2) c6 c8 c7 := by
  unfold retunedLowerPlus retunedEllPlus
    factorTwoIntrinsicNineRetunedTPlus retunedTEntry
    factorTwoIntrinsicNineRetunedRPlus factorTwoIntrinsicNineRetunedUPlus
    factorTwoIntrinsicNineRentry factorTwoIntrinsicNineUentry
  simp only [factorTwoIntrinsicNineRetunedOPlus,
    factorTwoIntrinsicNineRetunedBPlus,
    factorTwoIntrinsicNineRetunedDPlus,
    factorTwoIntrinsicNineRetunedFPlus,
    factorTwoIntrinsicNineRetunedGPlus]
  unfold symmetricQuadratic unbalancedThreeAdjugatePair adjugateQuadratic
  ring

/-- The first retuned plus Schur identity specialized to the first two odd
coordinates.  Unlike the general identity, this public form contains no
private lower-block abbreviations. -/
theorem factorTwoIntrinsicNineRetunedTPlusTwoQuadratic_eq_fractionFree
    (y1 y3 : ℝ) :
    factorTwoIntrinsicSixUnbalancedEPlusDet *
          (factorTwoIntrinsicNineRetunedOPlus 0 0 * y1 ^ 2 +
            2 * factorTwoIntrinsicNineRetunedOPlus 0 1 * y1 * y3 +
            factorTwoIntrinsicNineRetunedOPlus 1 1 * y3 ^ 2) -
        adjugateQuadratic
          factorTwoIntrinsicSixUnbalancedEPlus00
          factorTwoIntrinsicSixUnbalancedEPlus02
          factorTwoIntrinsicSixUnbalancedEPlus04
          factorTwoIntrinsicSixUnbalancedEPlus22
          factorTwoIntrinsicSixUnbalancedEPlus24
          factorTwoIntrinsicSixUnbalancedEPlus44
          (factorTwoIntrinsicNineRetunedBPlus 0 0 * y1 +
            factorTwoIntrinsicNineRetunedBPlus 1 0 * y3)
          (factorTwoIntrinsicNineRetunedBPlus 0 1 * y1 +
            factorTwoIntrinsicNineRetunedBPlus 1 1 * y3)
          (factorTwoIntrinsicNineRetunedBPlus 0 2 * y1 +
            factorTwoIntrinsicNineRetunedBPlus 1 2 * y3) =
      factorTwoIntrinsicNineRetunedTPlus 0 0 * y1 ^ 2 +
        2 * factorTwoIntrinsicNineRetunedTPlus 0 1 * y1 * y3 +
        factorTwoIntrinsicNineRetunedTPlus 1 1 * y3 ^ 2 := by
  have h := factorTwoIntrinsicNineRetunedPlus_firstSchur_eq
    y1 y3 0 0 0 0
  unfold retunedLowerPlus retunedEllPlus at h
  simpa [symmetricQuadratic] using h

/-- Exact first fraction-free completion for the retuned minus endpoint. -/
theorem factorTwoIntrinsicNineRetunedMinus_firstSchur_eq
    (c1 c3 c5 c6 c8 c7 : ℝ) :
    factorTwoIntrinsicSixUnbalancedEMinusDet *
          retunedLowerMinus c1 c3 c5 c6 c8 c7 -
        adjugateQuadratic
          factorTwoIntrinsicSixUnbalancedEMinus00
          factorTwoIntrinsicSixUnbalancedEMinus02
          factorTwoIntrinsicSixUnbalancedEMinus04
          factorTwoIntrinsicSixUnbalancedEMinus22
          factorTwoIntrinsicSixUnbalancedEMinus24
          factorTwoIntrinsicSixUnbalancedEMinus44
          (retunedEllMinus 0 c1 c3 c5 c6 c8 c7)
          (retunedEllMinus 1 c1 c3 c5 c6 c8 c7)
          (retunedEllMinus 2 c1 c3 c5 c6 c8 c7) =
      symmetricQuadratic
          (factorTwoIntrinsicNineRetunedTMinus 0 0)
          (factorTwoIntrinsicNineRetunedTMinus 0 1)
          (factorTwoIntrinsicNineRetunedTMinus 0 2)
          (factorTwoIntrinsicNineRetunedTMinus 1 1)
          (factorTwoIntrinsicNineRetunedTMinus 1 2)
          (factorTwoIntrinsicNineRetunedTMinus 2 2) c1 c3 c5 +
        2 * (c1 * (factorTwoIntrinsicNineRetunedRMinus 0 0 * c6 +
              factorTwoIntrinsicNineRetunedRMinus 0 1 * c8 +
              factorTwoIntrinsicNineRetunedRMinus 0 2 * c7) +
          c3 * (factorTwoIntrinsicNineRetunedRMinus 1 0 * c6 +
              factorTwoIntrinsicNineRetunedRMinus 1 1 * c8 +
              factorTwoIntrinsicNineRetunedRMinus 1 2 * c7) +
          c5 * (factorTwoIntrinsicNineRetunedRMinus 2 0 * c6 +
              factorTwoIntrinsicNineRetunedRMinus 2 1 * c8 +
              factorTwoIntrinsicNineRetunedRMinus 2 2 * c7)) +
        symmetricQuadratic
          (factorTwoIntrinsicNineRetunedUMinus 0 0)
          (factorTwoIntrinsicNineRetunedUMinus 0 1)
          (factorTwoIntrinsicNineRetunedUMinus 0 2)
          (factorTwoIntrinsicNineRetunedUMinus 1 1)
          (factorTwoIntrinsicNineRetunedUMinus 1 2)
          (factorTwoIntrinsicNineRetunedUMinus 2 2) c6 c8 c7 := by
  unfold retunedLowerMinus retunedEllMinus
    factorTwoIntrinsicNineRetunedTMinus retunedTEntry
    factorTwoIntrinsicNineRetunedRMinus factorTwoIntrinsicNineRetunedUMinus
    factorTwoIntrinsicNineRentry factorTwoIntrinsicNineUentry
  simp only [factorTwoIntrinsicNineRetunedOMinus,
    factorTwoIntrinsicNineRetunedBMinus,
    factorTwoIntrinsicNineRetunedDMinus,
    factorTwoIntrinsicNineRetunedFMinus,
    factorTwoIntrinsicNineRetunedGMinus]
  unfold symmetricQuadratic unbalancedThreeAdjugatePair adjugateQuadratic
  ring

def factorTwoIntrinsicNineRetunedPlusBlock
    (c0 c2 c4 c1 c3 c5 c6 c8 c7 : ℝ) : ℝ :=
  symmetricQuadratic
      factorTwoIntrinsicSixUnbalancedEPlus00
      factorTwoIntrinsicSixUnbalancedEPlus02
      factorTwoIntrinsicSixUnbalancedEPlus04
      factorTwoIntrinsicSixUnbalancedEPlus22
      factorTwoIntrinsicSixUnbalancedEPlus24
      factorTwoIntrinsicSixUnbalancedEPlus44 c0 c2 c4 +
    2 * (c0 * retunedEllPlus 0 c1 c3 c5 c6 c8 c7 +
      c2 * retunedEllPlus 1 c1 c3 c5 c6 c8 c7 +
      c4 * retunedEllPlus 2 c1 c3 c5 c6 c8 c7) +
    retunedLowerPlus c1 c3 c5 c6 c8 c7

def factorTwoIntrinsicNineRetunedMinusBlock
    (c0 c2 c4 c1 c3 c5 c6 c8 c7 : ℝ) : ℝ :=
  symmetricQuadratic
      factorTwoIntrinsicSixUnbalancedEMinus00
      factorTwoIntrinsicSixUnbalancedEMinus02
      factorTwoIntrinsicSixUnbalancedEMinus04
      factorTwoIntrinsicSixUnbalancedEMinus22
      factorTwoIntrinsicSixUnbalancedEMinus24
      factorTwoIntrinsicSixUnbalancedEMinus44 c0 c2 c4 +
    2 * (c0 * retunedEllMinus 0 c1 c3 c5 c6 c8 c7 +
      c2 * retunedEllMinus 1 c1 c3 c5 c6 c8 c7 +
      c4 * retunedEllMinus 2 c1 c3 c5 c6 c8 c7) +
    retunedLowerMinus c1 c3 c5 c6 c8 c7

/-! ## Exact identification with the corrected endpoints -/

/-- Subtracting the full retained reserve from the retuned plus endpoint
gives exactly the displayed `3 + 3 + 3` block form. -/
theorem factorTwoIntrinsicNineRetunedStaticPlus_sub_reserve_eq_block
    (c0 c2 c4 c6 c8 c1 c3 c5 c7 : ℝ) :
    factorTwoIntrinsicNineRetunedStaticPlus
          c0 c2 c4 c6 c8 c1 c3 c5 c7 -
        factorTwoIntrinsicNineReserveQuadratic c6 c8 c7 =
      factorTwoIntrinsicNineRetunedPlusBlock
        c0 c2 c4 c1 c3 c5 c6 c8 c7 := by
  have hsix := factorTwoIntrinsicNineRetunedSixPlus_eq_block
    c0 c2 c4 c1 c3 c5
  unfold factorTwoIntrinsicNineRetunedStaticPlus
    factorTwoProfileStaticBranchForm
  rw [factorTwoEndpointPhaseDiagonal_intrinsicNineEven_eq,
    factorTwoEndpointPhaseDiagonal_intrinsicNineOdd_eq,
    factorTwoCenteredAlternatingCoupling_intrinsicNine_eq,
    factorTwoIntrinsicNineRetunedTransfer_eq_core_add_tail]
  unfold factorTwoIntrinsicNineRetunedPlusBlock
    retunedEllPlus retunedLowerPlus
    factorTwoIntrinsicNineReserveQuadratic
  simp only [factorTwoIntrinsicNineRetunedOPlus,
    factorTwoIntrinsicNineRetunedDPlus,
    factorTwoIntrinsicNineRetunedFPlus,
    factorTwoIntrinsicNineRetunedGPlus]
  unfold factorTwoIntrinsicNineEPlus06 factorTwoIntrinsicNineEPlus08
    factorTwoIntrinsicNineEPlus26 factorTwoIntrinsicNineEPlus28
    factorTwoIntrinsicNineEPlus46 factorTwoIntrinsicNineEPlus48
    factorTwoIntrinsicNineEPlus66 factorTwoIntrinsicNineEPlus68
    factorTwoIntrinsicNineEPlus88
    factorTwoIntrinsicNineOMinus17 factorTwoIntrinsicNineOMinus37
    factorTwoIntrinsicNineOMinus57 factorTwoIntrinsicNineOMinus77
    factorTwoIntrinsicNineEvenEntry factorTwoIntrinsicNineOddEntry
    factorTwoIntrinsicNineRetunedKPlus
    factorTwoIntrinsicNineReserve6 factorTwoIntrinsicNineReserve8
    factorTwoIntrinsicNineReserve7
  simp [factorTwoIntrinsicNineRetunedEvenBasis,
    factorTwoIntrinsicNineRetunedOddBasis,
    factorTwoIntrinsicNineRetunedH]
  unfold symmetricQuadratic at hsix ⊢
  linear_combination hsix

/-- Minus-endpoint counterpart of
`factorTwoIntrinsicNineRetunedStaticPlus_sub_reserve_eq_block`. -/
theorem factorTwoIntrinsicNineRetunedStaticMinus_sub_reserve_eq_block
    (c0 c2 c4 c6 c8 c1 c3 c5 c7 : ℝ) :
    factorTwoIntrinsicNineRetunedStaticMinus
          c0 c2 c4 c6 c8 c1 c3 c5 c7 -
        factorTwoIntrinsicNineReserveQuadratic c6 c8 c7 =
      factorTwoIntrinsicNineRetunedMinusBlock
        c0 c2 c4 c1 c3 c5 c6 c8 c7 := by
  have hsix := factorTwoIntrinsicNineRetunedSixMinus_eq_block
    c0 c2 c4 c1 c3 c5
  unfold factorTwoIntrinsicNineRetunedStaticMinus
    factorTwoProfileStaticBranchForm
  rw [factorTwoEndpointPhaseDiagonal_intrinsicNineEven_eq,
    factorTwoEndpointPhaseDiagonal_intrinsicNineOdd_eq,
    factorTwoCenteredAlternatingCoupling_intrinsicNine_eq,
    factorTwoIntrinsicNineRetunedTransfer_eq_core_add_tail]
  unfold factorTwoIntrinsicNineRetunedMinusBlock
    retunedEllMinus retunedLowerMinus
    factorTwoIntrinsicNineReserveQuadratic
  simp only [factorTwoIntrinsicNineRetunedOMinus,
    factorTwoIntrinsicNineRetunedDMinus,
    factorTwoIntrinsicNineRetunedFMinus,
    factorTwoIntrinsicNineRetunedGMinus]
  unfold factorTwoIntrinsicNineEMinus06 factorTwoIntrinsicNineEMinus08
    factorTwoIntrinsicNineEMinus26 factorTwoIntrinsicNineEMinus28
    factorTwoIntrinsicNineEMinus46 factorTwoIntrinsicNineEMinus48
    factorTwoIntrinsicNineEMinus66 factorTwoIntrinsicNineEMinus68
    factorTwoIntrinsicNineEMinus88
    factorTwoIntrinsicNineOPlus17 factorTwoIntrinsicNineOPlus37
    factorTwoIntrinsicNineOPlus57 factorTwoIntrinsicNineOPlus77
    factorTwoIntrinsicNineEvenEntry factorTwoIntrinsicNineOddEntry
    factorTwoIntrinsicNineRetunedKMinus
    factorTwoIntrinsicNineReserve6 factorTwoIntrinsicNineReserve8
    factorTwoIntrinsicNineReserve7
  simp [factorTwoIntrinsicNineRetunedEvenBasis,
    factorTwoIntrinsicNineRetunedOddBasis,
    factorTwoIntrinsicNineRetunedH]
  unfold symmetricQuadratic at hsix ⊢
  linear_combination hsix

/-- The twelve displayed scalar gates imply nonnegativity of the complete
retuned plus endpoint block. -/
theorem factorTwoIntrinsicNineRetunedPlusBlock_nonnegative_of_gates
    (hgates : FactorTwoIntrinsicNineRetunedPlusFinalThreeGates)
    (c0 c2 c4 c1 c3 c5 c6 c8 c7 : ℝ) :
    0 ≤ factorTwoIntrinsicNineRetunedPlusBlock
      c0 c2 c4 c1 c3 c5 c6 c8 c7 := by
  rcases hgates with
    ⟨hT00, hTMinor, hTDet, hW00, hWMinor, hWDet⟩
  rcases factorTwoIntrinsicSixUnbalancedEPlus_positive with
    ⟨hE00, hEMinor, hEDet⟩
  unfold factorTwoIntrinsicNineRetunedPlusBlock
  apply nineBlock_nonneg_of_nested_fractionFreeSchur
    factorTwoIntrinsicSixUnbalancedEPlus00
    factorTwoIntrinsicSixUnbalancedEPlus02
    factorTwoIntrinsicSixUnbalancedEPlus04
    factorTwoIntrinsicSixUnbalancedEPlus22
    factorTwoIntrinsicSixUnbalancedEPlus24
    factorTwoIntrinsicSixUnbalancedEPlus44
    (factorTwoIntrinsicNineRetunedTPlus 0 0)
    (factorTwoIntrinsicNineRetunedTPlus 0 1)
    (factorTwoIntrinsicNineRetunedTPlus 0 2)
    (factorTwoIntrinsicNineRetunedTPlus 1 1)
    (factorTwoIntrinsicNineRetunedTPlus 1 2)
    (factorTwoIntrinsicNineRetunedTPlus 2 2)
    (factorTwoIntrinsicNineRetunedRPlus 0 0)
    (factorTwoIntrinsicNineRetunedRPlus 0 1)
    (factorTwoIntrinsicNineRetunedRPlus 0 2)
    (factorTwoIntrinsicNineRetunedRPlus 1 0)
    (factorTwoIntrinsicNineRetunedRPlus 1 1)
    (factorTwoIntrinsicNineRetunedRPlus 1 2)
    (factorTwoIntrinsicNineRetunedRPlus 2 0)
    (factorTwoIntrinsicNineRetunedRPlus 2 1)
    (factorTwoIntrinsicNineRetunedRPlus 2 2)
    (factorTwoIntrinsicNineRetunedUPlus 0 0)
    (factorTwoIntrinsicNineRetunedUPlus 0 1)
    (factorTwoIntrinsicNineRetunedUPlus 0 2)
    (factorTwoIntrinsicNineRetunedUPlus 1 1)
    (factorTwoIntrinsicNineRetunedUPlus 1 2)
    (factorTwoIntrinsicNineRetunedUPlus 2 2)
  · exact hE00
  · exact hEMinor
  · simpa only [factorTwoIntrinsicSixUnbalancedEPlusDet] using hEDet
  · exact hT00
  · exact hTMinor
  · exact hTDet
  · intro z6 z8 z7
    exact symmetricQuadratic_nonneg
      (factorTwoIntrinsicNineRetunedWPlus 0 0)
      (factorTwoIntrinsicNineRetunedWPlus 0 1)
      (factorTwoIntrinsicNineRetunedWPlus 0 2)
      (factorTwoIntrinsicNineRetunedWPlus 1 1)
      (factorTwoIntrinsicNineRetunedWPlus 1 2)
      (factorTwoIntrinsicNineRetunedWPlus 2 2)
      hW00 hWMinor hWDet z6 z8 z7
  · exact factorTwoIntrinsicNineRetunedPlus_firstSchur_eq
      c1 c3 c5 c6 c8 c7

/-- Minus-endpoint counterpart of
`factorTwoIntrinsicNineRetunedPlusBlock_nonnegative_of_gates`. -/
theorem factorTwoIntrinsicNineRetunedMinusBlock_nonnegative_of_gates
    (hgates : FactorTwoIntrinsicNineRetunedMinusFinalThreeGates)
    (c0 c2 c4 c1 c3 c5 c6 c8 c7 : ℝ) :
    0 ≤ factorTwoIntrinsicNineRetunedMinusBlock
      c0 c2 c4 c1 c3 c5 c6 c8 c7 := by
  rcases hgates with
    ⟨hT00, hTMinor, hTDet, hW00, hWMinor, hWDet⟩
  rcases factorTwoIntrinsicSixUnbalancedEMinus_positive with
    ⟨hE00, hEMinor, hEDet⟩
  unfold factorTwoIntrinsicNineRetunedMinusBlock
  apply nineBlock_nonneg_of_nested_fractionFreeSchur
    factorTwoIntrinsicSixUnbalancedEMinus00
    factorTwoIntrinsicSixUnbalancedEMinus02
    factorTwoIntrinsicSixUnbalancedEMinus04
    factorTwoIntrinsicSixUnbalancedEMinus22
    factorTwoIntrinsicSixUnbalancedEMinus24
    factorTwoIntrinsicSixUnbalancedEMinus44
    (factorTwoIntrinsicNineRetunedTMinus 0 0)
    (factorTwoIntrinsicNineRetunedTMinus 0 1)
    (factorTwoIntrinsicNineRetunedTMinus 0 2)
    (factorTwoIntrinsicNineRetunedTMinus 1 1)
    (factorTwoIntrinsicNineRetunedTMinus 1 2)
    (factorTwoIntrinsicNineRetunedTMinus 2 2)
    (factorTwoIntrinsicNineRetunedRMinus 0 0)
    (factorTwoIntrinsicNineRetunedRMinus 0 1)
    (factorTwoIntrinsicNineRetunedRMinus 0 2)
    (factorTwoIntrinsicNineRetunedRMinus 1 0)
    (factorTwoIntrinsicNineRetunedRMinus 1 1)
    (factorTwoIntrinsicNineRetunedRMinus 1 2)
    (factorTwoIntrinsicNineRetunedRMinus 2 0)
    (factorTwoIntrinsicNineRetunedRMinus 2 1)
    (factorTwoIntrinsicNineRetunedRMinus 2 2)
    (factorTwoIntrinsicNineRetunedUMinus 0 0)
    (factorTwoIntrinsicNineRetunedUMinus 0 1)
    (factorTwoIntrinsicNineRetunedUMinus 0 2)
    (factorTwoIntrinsicNineRetunedUMinus 1 1)
    (factorTwoIntrinsicNineRetunedUMinus 1 2)
    (factorTwoIntrinsicNineRetunedUMinus 2 2)
  · exact hE00
  · exact hEMinor
  · simpa only [factorTwoIntrinsicSixUnbalancedEMinusDet] using hEDet
  · exact hT00
  · exact hTMinor
  · exact hTDet
  · intro z6 z8 z7
    exact symmetricQuadratic_nonneg
      (factorTwoIntrinsicNineRetunedWMinus 0 0)
      (factorTwoIntrinsicNineRetunedWMinus 0 1)
      (factorTwoIntrinsicNineRetunedWMinus 0 2)
      (factorTwoIntrinsicNineRetunedWMinus 1 1)
      (factorTwoIntrinsicNineRetunedWMinus 1 2)
      (factorTwoIntrinsicNineRetunedWMinus 2 2)
      hW00 hWMinor hWDet z6 z8 z7
  · exact factorTwoIntrinsicNineRetunedMinus_firstSchur_eq
      c1 c3 c5 c6 c8 c7

/-- The plus Sylvester gates discharge the complete plus static reserve
certificate. -/
theorem factorTwoIntrinsicNineRetunedStaticPlusReserve_of_gates
    (hgates : FactorTwoIntrinsicNineRetunedPlusFinalThreeGates) :
    FactorTwoIntrinsicNineRetunedStaticPlusReserve := by
  intro c0 c2 c4 c6 c8 c1 c3 c5 c7
  have hblock := factorTwoIntrinsicNineRetunedPlusBlock_nonnegative_of_gates
    hgates c0 c2 c4 c1 c3 c5 c6 c8 c7
  rw [← factorTwoIntrinsicNineRetunedStaticPlus_sub_reserve_eq_block] at hblock
  linarith

/-- The minus Sylvester gates discharge the complete minus static reserve
certificate. -/
theorem factorTwoIntrinsicNineRetunedStaticMinusReserve_of_gates
    (hgates : FactorTwoIntrinsicNineRetunedMinusFinalThreeGates) :
    FactorTwoIntrinsicNineRetunedStaticMinusReserve := by
  intro c0 c2 c4 c6 c8 c1 c3 c5 c7
  have hblock := factorTwoIntrinsicNineRetunedMinusBlock_nonnegative_of_gates
    hgates c0 c2 c4 c1 c3 c5 c6 c8 c7
  rw [← factorTwoIntrinsicNineRetunedStaticMinus_sub_reserve_eq_block] at hblock
  linarith

/-- Structural handoff from the twelve phase-free scalar gates to the
phase-native final `Fin 3` Schur matrix. -/
theorem factorTwoIntrinsicNineDirectFinalSchurMatrix_posSemidef_of_retuned_gates
    (hplus : FactorTwoIntrinsicNineRetunedPlusFinalThreeGates)
    (hminus : FactorTwoIntrinsicNineRetunedMinusFinalThreeGates)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    (factorTwoIntrinsicNineDirectFinalSchurMatrix a b).PosSemidef := by
  exact factorTwoIntrinsicNineDirectFinalSchurMatrix_posSemidef_of_retuned_static
    (factorTwoIntrinsicNineRetunedStaticPlusReserve_of_gates hplus)
    (factorTwoIntrinsicNineRetunedStaticMinusReserve_of_gates hminus)
    a b hab

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineStaticFinalThreePositiveStructural

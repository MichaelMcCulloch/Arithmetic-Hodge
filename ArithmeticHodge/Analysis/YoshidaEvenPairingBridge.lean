import ArithmeticHodge.Analysis.YoshidaClippedLowModes

set_option autoImplicit false

open Complex MeasureTheory
open scoped ComplexConjugate

namespace ArithmeticHodge.Analysis.YoshidaEvenPairingBridge

noncomputable section

open ArithmeticHodge.Analysis

/-!
# Exact clipped even-mode pairing formulas

This module exposes the strongest even-sector formula available before an
even analogue of the odd real-space admissible-distribution assembly is
proved.  The formulas are exact, all-mode, and removable-safe: every centered
Laplace sample is reduced to `yoshidaIntervalExpQuotient`, whose zero branch
records the removable resonance explicitly.

The canonical finite even block in the repository is `YoshidaEvenIndex =
Fin 200`, hence it consists of the zero mode and modes `1, ..., 199`; its first
tail mode is `200`.  Separate consequences below also expose zero and modes
`1, ..., 200` against modes `201 + k`, matching the alternative indexing often
used when stating the source cutoff.

No positivity, decay estimate, infinite interchange, or bounded extension of
the clipped form is asserted here.
-/

/-- The exact removable-safe centered Laplace value of a normalized clipped
exponential. -/
def yoshidaClippedExponentialLaplaceFormula
    (a : ℝ) (n : ℤ) (z : ℂ) : ℂ :=
  ((Real.sqrt (2 * a))⁻¹ : ℂ) *
    yoshidaIntervalExpQuotient a (yoshidaModeLaplaceExponent a n z)

/-- The exact centered Laplace value of a positive-frequency clipped even
mode. -/
def yoshidaClippedEvenModeLaplaceFormula
    (a : ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  ((Real.sqrt 2 : ℂ)⁻¹) *
    (yoshidaClippedExponentialLaplaceFormula a (n : ℤ) z +
      yoshidaClippedExponentialLaplaceFormula a (-(n : ℤ)) z)

/-- The exact centered Laplace value of the normalized clipped zero mode. -/
def yoshidaClippedEvenZeroLaplaceFormula (a : ℝ) (z : ℂ) : ℂ :=
  yoshidaClippedExponentialLaplaceFormula a 0 z

/-- Reconstruct a clipped local critical pairing from exact centered Laplace
formulas for its left and right arguments. -/
def yoshidaClippedPairingFromLaplaceFormula
    (left right : ℂ → ℂ) : ℂ :=
  star (left (1 / 2)) * right (-1 / 2) +
    star (left (-1 / 2)) * right (1 / 2) +
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ v : ℝ, MultiplicativeWeil.bombieriLocalCriticalKernel v *
        star (left (v * Complex.I)) * right (v * Complex.I))

/-- Exact all-mode clipped even/even pairing formula. -/
def yoshidaClippedEvenModePairingFormula
    (a : ℝ) (n m : ℕ) : ℂ :=
  yoshidaClippedPairingFromLaplaceFormula
    (yoshidaClippedEvenModeLaplaceFormula a n)
    (yoshidaClippedEvenModeLaplaceFormula a m)

/-- Exact zero/even pairing formula. -/
def yoshidaClippedEvenZeroModePairingFormula
    (a : ℝ) (m : ℕ) : ℂ :=
  yoshidaClippedPairingFromLaplaceFormula
    (yoshidaClippedEvenZeroLaplaceFormula a)
    (yoshidaClippedEvenModeLaplaceFormula a m)

/-- Exact even/zero pairing formula. -/
def yoshidaClippedEvenModeZeroPairingFormula
    (a : ℝ) (n : ℕ) : ℂ :=
  yoshidaClippedPairingFromLaplaceFormula
    (yoshidaClippedEvenModeLaplaceFormula a n)
    (yoshidaClippedEvenZeroLaplaceFormula a)

/-- Exact zero/zero pairing formula. -/
def yoshidaClippedEvenZeroZeroPairingFormula (a : ℝ) : ℂ :=
  yoshidaClippedPairingFromLaplaceFormula
    (yoshidaClippedEvenZeroLaplaceFormula a)
    (yoshidaClippedEvenZeroLaplaceFormula a)

/-- Exact low/even entry formula for the repository's canonical
`YoshidaEvenIndex`. -/
def yoshidaClippedEvenLowModePairingFormula
    (a : ℝ) (i : YoshidaEvenIndex) (m : ℕ) : ℂ :=
  if i.1 = 0 then yoshidaClippedEvenZeroModePairingFormula a m
  else yoshidaClippedEvenModePairingFormula a i.1 m

theorem yoshidaCenteredLaplace_clippedExponential_eq_formula
    {a : ℝ} (ha : 0 < a) (n : ℤ) (z : ℂ) :
    yoshidaCenteredLaplaceLinear a ha z
        (yoshidaClippedExponential a n) =
      yoshidaClippedExponentialLaplaceFormula a n z := by
  exact yoshidaCenteredLaplace_clippedExponential ha z n

theorem yoshidaCenteredLaplace_clippedEvenMode_eq_formula
    {a : ℝ} (ha : 0 < a) (n : ℕ) (z : ℂ) :
    yoshidaCenteredLaplaceLinear a ha z (yoshidaClippedEvenMode a n) =
      yoshidaClippedEvenModeLaplaceFormula a n z := by
  rw [yoshidaClippedEvenMode, map_smul, map_add]
  rw [yoshidaCenteredLaplace_clippedExponential_eq_formula ha,
    yoshidaCenteredLaplace_clippedExponential_eq_formula ha]
  rfl

theorem yoshidaCenteredLaplace_clippedEvenZeroMode_eq_formula
    {a : ℝ} (ha : 0 < a) (z : ℂ) :
    yoshidaCenteredLaplaceLinear a ha z (yoshidaClippedEvenZeroMode a) =
      yoshidaClippedEvenZeroLaplaceFormula a z := by
  exact yoshidaCenteredLaplace_clippedExponential_eq_formula ha 0 z

/-- Removable-safe critical-line formula for every clipped even mode. -/
theorem yoshidaCriticalSample_clippedEvenMode_eq_formula
    {a : ℝ} (ha : 0 < a) (v : ℝ) (n : ℕ) :
    yoshidaCriticalSampleLinear a ha v (yoshidaClippedEvenMode a n) =
      yoshidaClippedEvenModeLaplaceFormula a n (v * Complex.I) := by
  exact yoshidaCenteredLaplace_clippedEvenMode_eq_formula ha n
    (v * Complex.I)

/-- Removable-safe critical-line formula for the normalized clipped zero
mode. -/
theorem yoshidaCriticalSample_clippedEvenZeroMode_eq_formula
    {a : ℝ} (ha : 0 < a) (v : ℝ) :
    yoshidaCriticalSampleLinear a ha v (yoshidaClippedEvenZeroMode a) =
      yoshidaClippedEvenZeroLaplaceFormula a (v * Complex.I) := by
  exact yoshidaCenteredLaplace_clippedEvenZeroMode_eq_formula ha
    (v * Complex.I)

theorem yoshidaPositivePolar_clippedEvenMode_eq_formula
    {a : ℝ} (ha : 0 < a) (n : ℕ) :
    yoshidaPositivePolarLinear a ha (yoshidaClippedEvenMode a n) =
      yoshidaClippedEvenModeLaplaceFormula a n (1 / 2) := by
  exact yoshidaCenteredLaplace_clippedEvenMode_eq_formula ha n (1 / 2)

theorem yoshidaNegativePolar_clippedEvenMode_eq_formula
    {a : ℝ} (ha : 0 < a) (n : ℕ) :
    yoshidaNegativePolarLinear a ha (yoshidaClippedEvenMode a n) =
      yoshidaClippedEvenModeLaplaceFormula a n (-1 / 2) := by
  exact yoshidaCenteredLaplace_clippedEvenMode_eq_formula ha n (-1 / 2)

/-- A generic exact bridge: if two clipped functions have the supplied
centered Laplace formulas, their local critical pairing is exactly the
pairing reconstructed from those formulas. -/
theorem yoshidaClippedLocalCriticalPairing_eq_laplaceFormula
    {a : ℝ} (ha : 0 < a) (f g : YoshidaClippedSmooth a)
    (left right : ℂ → ℂ)
    (hleft : ∀ z, yoshidaCenteredLaplaceLinear a ha z f = left z)
    (hright : ∀ z, yoshidaCenteredLaplaceLinear a ha z g = right z) :
    yoshidaClippedLocalCriticalPairing a ha f g =
      yoshidaClippedPairingFromLaplaceFormula left right := by
  rw [yoshidaClippedLocalCriticalPairing]
  unfold yoshidaClippedPairingFromLaplaceFormula
  rw [show yoshidaPositivePolarLinear a ha f = left (1 / 2) by
        exact hleft (1 / 2),
    show yoshidaNegativePolarLinear a ha f = left (-1 / 2) by
        exact hleft (-1 / 2),
    show yoshidaPositivePolarLinear a ha g = right (1 / 2) by
        exact hright (1 / 2),
    show yoshidaNegativePolarLinear a ha g = right (-1 / 2) by
        exact hright (-1 / 2)]
  apply congrArg (fun value : ℂ ↦
    star (left (1 / 2)) * right (-1 / 2) +
      star (left (-1 / 2)) * right (1 / 2) +
      (((1 / (2 * Real.pi) : ℝ) : ℂ) * value))
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with v
  unfold yoshidaClippedCriticalCrossIntegrand yoshidaCriticalSampleLinear
  rw [hleft (v * Complex.I), hright (v * Complex.I)]

/-- Exact all-mode even/even bridge, including every low/high entry. -/
theorem yoshidaClippedLocalCriticalPairing_evenMode_eq_formula
    {a : ℝ} (ha : 0 < a) (n m : ℕ) :
    yoshidaClippedLocalCriticalPairing a ha
        (yoshidaClippedEvenMode a n) (yoshidaClippedEvenMode a m) =
      yoshidaClippedEvenModePairingFormula a n m := by
  exact yoshidaClippedLocalCriticalPairing_eq_laplaceFormula ha _ _ _ _
    (yoshidaCenteredLaplace_clippedEvenMode_eq_formula ha n)
    (yoshidaCenteredLaplace_clippedEvenMode_eq_formula ha m)

/-- Bundled-form version of the exact all-mode even/even bridge. -/
theorem yoshidaClippedLocalCriticalForm_evenMode_eq_formula
    {a : ℝ} (ha : 0 < a) (n m : ℕ) :
    yoshidaClippedLocalCriticalForm a ha
        (yoshidaClippedEvenMode a n) (yoshidaClippedEvenMode a m) =
      yoshidaClippedEvenModePairingFormula a n m := by
  exact yoshidaClippedLocalCriticalPairing_evenMode_eq_formula ha n m

theorem yoshidaClippedLocalCriticalPairing_evenZeroMode_evenMode_eq_formula
    {a : ℝ} (ha : 0 < a) (m : ℕ) :
    yoshidaClippedLocalCriticalPairing a ha
        (yoshidaClippedEvenZeroMode a) (yoshidaClippedEvenMode a m) =
      yoshidaClippedEvenZeroModePairingFormula a m := by
  exact yoshidaClippedLocalCriticalPairing_eq_laplaceFormula ha _ _ _ _
    (yoshidaCenteredLaplace_clippedEvenZeroMode_eq_formula ha)
    (yoshidaCenteredLaplace_clippedEvenMode_eq_formula ha m)

theorem yoshidaClippedLocalCriticalPairing_evenMode_evenZeroMode_eq_formula
    {a : ℝ} (ha : 0 < a) (n : ℕ) :
    yoshidaClippedLocalCriticalPairing a ha
        (yoshidaClippedEvenMode a n) (yoshidaClippedEvenZeroMode a) =
      yoshidaClippedEvenModeZeroPairingFormula a n := by
  exact yoshidaClippedLocalCriticalPairing_eq_laplaceFormula ha _ _ _ _
    (yoshidaCenteredLaplace_clippedEvenMode_eq_formula ha n)
    (yoshidaCenteredLaplace_clippedEvenZeroMode_eq_formula ha)

theorem yoshidaClippedLocalCriticalPairing_evenZeroMode_eq_formula
    {a : ℝ} (ha : 0 < a) :
    yoshidaClippedLocalCriticalPairing a ha
        (yoshidaClippedEvenZeroMode a) (yoshidaClippedEvenZeroMode a) =
      yoshidaClippedEvenZeroZeroPairingFormula a := by
  exact yoshidaClippedLocalCriticalPairing_eq_laplaceFormula ha _ _ _ _
    (yoshidaCenteredLaplace_clippedEvenZeroMode_eq_formula ha)
    (yoshidaCenteredLaplace_clippedEvenZeroMode_eq_formula ha)

/-- Exact formula for any canonical finite-block row paired with any even
mode. -/
theorem yoshidaClippedLocalCriticalPairing_evenLowMode_mode_eq_formula
    {a : ℝ} (ha : 0 < a) (i : YoshidaEvenIndex) (m : ℕ) :
    yoshidaClippedLocalCriticalPairing a ha
        (yoshidaClippedEvenLowMode a i) (yoshidaClippedEvenMode a m) =
      yoshidaClippedEvenLowModePairingFormula a i m := by
  by_cases hi : i.1 = 0
  · rw [yoshidaClippedEvenLowModePairingFormula,
      yoshidaClippedEvenLowMode, if_pos hi, if_pos hi]
    exact yoshidaClippedLocalCriticalPairing_evenZeroMode_evenMode_eq_formula
      ha m
  · rw [yoshidaClippedEvenLowModePairingFormula,
      yoshidaClippedEvenLowMode, if_neg hi, if_neg hi]
    exact yoshidaClippedLocalCriticalPairing_evenMode_eq_formula ha i.1 m

/-- Canonical `Fin 200` low block against its first and subsequent tail
modes.  The first such mode is `200`. -/
theorem yoshidaClippedLocalCriticalPairing_evenLowMode_tail_eq_formula
    {a : ℝ} (ha : 0 < a) (i : YoshidaEvenIndex) (k : ℕ) :
    yoshidaClippedLocalCriticalPairing a ha
        (yoshidaClippedEvenLowMode a i)
        (yoshidaClippedEvenMode a (200 + k)) =
      yoshidaClippedEvenLowModePairingFormula a i (200 + k) :=
  yoshidaClippedLocalCriticalPairing_evenLowMode_mode_eq_formula ha i (200 + k)

/-- Bundled-form version of the canonical `Fin 200` low/tail bridge. -/
theorem yoshidaClippedLocalCriticalForm_evenLowMode_tail_eq_formula
    {a : ℝ} (ha : 0 < a) (i : YoshidaEvenIndex) (k : ℕ) :
    yoshidaClippedLocalCriticalForm a ha
        (yoshidaClippedEvenLowMode a i)
        (yoshidaClippedEvenMode a (200 + k)) =
      yoshidaClippedEvenLowModePairingFormula a i (200 + k) := by
  exact yoshidaClippedLocalCriticalPairing_evenLowMode_tail_eq_formula ha i k

/-- Hermitian reverse orientation of the canonical low/high formula. -/
theorem yoshidaClippedLocalCriticalPairing_evenTail_lowMode_eq_formula
    {a : ℝ} (ha : 0 < a) (i : YoshidaEvenIndex) (k : ℕ) :
    yoshidaClippedLocalCriticalPairing a ha
        (yoshidaClippedEvenMode a (200 + k))
        (yoshidaClippedEvenLowMode a i) =
      star (yoshidaClippedEvenLowModePairingFormula a i (200 + k)) := by
  rw [← yoshidaClippedLocalCriticalPairing_evenLowMode_tail_eq_formula ha i k]
  exact (yoshidaClippedLocalCriticalPairing_conj ha _ _).symm

/-- The normalized zero mode against the alternative high range `201 + k`. -/
theorem yoshidaClippedLocalCriticalPairing_evenZero_high_eq_formula
    {a : ℝ} (ha : 0 < a) (k : ℕ) :
    yoshidaClippedLocalCriticalPairing a ha
        (yoshidaClippedEvenZeroMode a)
        (yoshidaClippedEvenMode a (201 + k)) =
      yoshidaClippedEvenZeroModePairingFormula a (201 + k) :=
  yoshidaClippedLocalCriticalPairing_evenZeroMode_evenMode_eq_formula ha (201 + k)

/-- Modes `1, ..., 200` against the alternative high range `201 + k`.
This is deliberately separate from `YoshidaEvenIndex`, whose nonzero modes
end at `199`. -/
theorem yoshidaClippedLocalCriticalPairing_evenOneToTwoHundred_high_eq_formula
    {a : ℝ} (ha : 0 < a) (i : Fin 200) (k : ℕ) :
    yoshidaClippedLocalCriticalPairing a ha
        (yoshidaClippedEvenMode a (i.1 + 1))
        (yoshidaClippedEvenMode a (201 + k)) =
      yoshidaClippedEvenModePairingFormula a (i.1 + 1) (201 + k) :=
  yoshidaClippedLocalCriticalPairing_evenMode_eq_formula ha _ _

end

end ArithmeticHodge.Analysis.YoshidaEvenPairingBridge

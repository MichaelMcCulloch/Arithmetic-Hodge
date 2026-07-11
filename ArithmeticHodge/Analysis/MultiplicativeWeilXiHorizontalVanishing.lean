import ArithmeticHodge.Analysis.MultiplicativeWeilHorizontalEdge
import ArithmeticHodge.Analysis.XiQuantitativeZeroFreeHeight

/-!
# Vanishing horizontal xi contours

Quantitative zero separation, the resulting quartic `xi'/xi` bound, and
sixth-order uniform Mellin decay combine into an exhausting paired sequence
whose two horizontal Bombieri contour terms vanish.
-/

set_option autoImplicit false

open Complex Filter Set Topology

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-- There is an exhausting sequence of paired zero-free xi contours on which
both horizontal Bombieri integrals vanish. -/
theorem exists_bombieri_xi_horizontal_vanishing_sequence
    (f : BombieriTest) (sigmaLower sigmaUpper : ℝ)
    (hsigma : sigmaLower < sigmaUpper) :
    ∃ T : ℕ → ℝ,
      Tendsto T atTop atTop ∧
      (∀ n : ℕ,
        0 < T n ∧
        (∀ sigma ∈ Set.Icc sigmaLower sigmaUpper,
          xiFunction ((sigma : ℂ) + T n * I) ≠ 0) ∧
        (∀ sigma ∈ Set.Icc sigmaLower sigmaUpper,
          xiFunction ((sigma : ℂ) - T n * I) ≠ 0)) ∧
      Tendsto
        (fun n ↦ bombieriHorizontalUpper f (logDeriv xiFunction)
          sigmaLower sigmaUpper (T n))
        atTop (nhds 0) ∧
      Tendsto
        (fun n ↦ bombieriHorizontalLower f (logDeriv xiFunction)
          sigmaLower sigmaUpper (T n))
        atTop (nhds 0) := by
  obtain ⟨K, N, T, hK, hT, hTbounds, hdata⟩ :=
    exists_xi_logDeriv_quartic_height_sequence
      sigmaLower sigmaUpper hsigma
  let U : ℕ → ℝ := fun n ↦ T (n + N)
  have hU_lower (n : ℕ) : (n : ℝ) ≤ U n := by
    have hbound := (hTbounds (n + N)).1
    dsimp only [U]
    exact (Nat.cast_le.mpr (Nat.le_add_right n N)).trans hbound.le
  have hU : Tendsto U atTop atTop :=
    tendsto_atTop_mono hU_lower (tendsto_natCast_atTop_atTop (R := ℝ))
  have hU_pos (n : ℕ) : 0 < U n := by
    dsimp only [U]
    exact (Nat.cast_nonneg (n + N)).trans_lt (hTbounds (n + N)).1
  have hUabs : Tendsto (fun n ↦ |U n|) atTop atTop := by
    convert hU using 1
    funext n
    exact abs_of_pos (hU_pos n)
  have hstrip (n : ℕ) (sigma : ℝ)
      (hsigmaMem : sigma ∈ Set.Icc sigmaLower sigmaUpper) :=
    hdata (n + N) (by omega) sigma hsigmaMem
  have hvanish := bombieriHorizontalPair_tendsto_zero_of_growth_four
    f (logDeriv xiFunction) sigmaLower sigmaUpper K U hsigma.le hUabs
    (fun n sigma hsigmaMem ↦
      ⟨(hstrip n sigma hsigmaMem).1.2,
        (hstrip n sigma hsigmaMem).2.2⟩)
  refine ⟨U, hU, ?_, hvanish.1, hvanish.2⟩
  intro n
  refine ⟨hU_pos n, ?_, ?_⟩
  · intro sigma hsigmaMem
    exact (hstrip n sigma hsigmaMem).1.1
  · intro sigma hsigmaMem
    exact (hstrip n sigma hsigmaMem).2.1

end

end ArithmeticHodge.Analysis.MultiplicativeWeil



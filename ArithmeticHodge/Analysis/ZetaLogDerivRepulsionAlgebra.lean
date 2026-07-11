import ArithmeticHodge.Analysis.ZetaLogDerivRealBound

/-!
# Order algebra for logarithmic zero repulsion

This isolates the final numerical step in the classical `3-4-1`
logarithmic-derivative proof.  Once the three analytic upper bounds are
available, the reciprocal gap estimate is pure ordered-field algebra.
-/

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

/-- The `3-4-1` inequality and three upper bounds imply a reciprocal lower
bound for the distance from the zero to the line of evaluation. -/
theorem gap_ge_of_logDeriv_341_bounds_scratch
    {x gap L Fzero Fone Ftwo Czero Cone Ctwo : ℝ}
    (hgap : 0 < gap)
    (h341 : 0 ≤ 3 * Fzero + 4 * Fone + Ftwo)
    (hzero : Fzero ≤ 1 / x + Czero * L)
    (hone : Fone ≤ Cone * L - 1 / gap)
    (htwo : Ftwo ≤ Ctwo * L)
    (hdenom : 0 < 3 / x + (3 * Czero + 4 * Cone + Ctwo) * L) :
    4 / (3 / x + (3 * Czero + 4 * Cone + Ctwo) * L) ≤ gap := by
  let D : ℝ := 3 / x + (3 * Czero + 4 * Cone + Ctwo) * L
  have hupper : 3 * Fzero + 4 * Fone + Ftwo ≤ D - 4 / gap := by
    calc
      3 * Fzero + 4 * Fone + Ftwo ≤
          3 * (1 / x + Czero * L) +
            4 * (Cone * L - 1 / gap) + Ctwo * L := by
        linarith
      _ = D - 4 / gap := by
        dsimp only [D]
        ring
  have hrecip : 4 / gap ≤ D := by linarith
  apply (div_le_iff₀ (show 0 < D by simpa only [D] using hdenom)).2
  have hmul : 4 ≤ D * gap := (div_le_iff₀ hgap).1 hrecip
  simpa only [mul_comm] using hmul

/-- Choosing the horizontal displacement `x = 1/L` turns the abstract
repulsion inequality into the desired constant multiple of `1/L`. -/
theorem gap_ge_inv_scale_of_logDeriv_341_bounds_scratch
    {gap L Fzero Fone Ftwo Czero Cone Ctwo : ℝ}
    (hgap : 0 < gap) (hL : 0 < L)
    (h341 : 0 ≤ 3 * Fzero + 4 * Fone + Ftwo)
    (hzero : Fzero ≤ L + Czero * L)
    (hone : Fone ≤ Cone * L - 1 / gap)
    (htwo : Ftwo ≤ Ctwo * L)
    (hconstant : 0 < 3 + 3 * Czero + 4 * Cone + Ctwo) :
    4 / ((3 + 3 * Czero + 4 * Cone + Ctwo) * L) ≤ gap := by
  have hinvInv : 1 / (1 / L) = L := by
    field_simp [hL.ne']
  have hdenom :
      0 < 3 / (1 / L) + (3 * Czero + 4 * Cone + Ctwo) * L := by
    rw [show 3 / (1 / L) = 3 * L by field_simp [hL.ne']]
    nlinarith [mul_pos hconstant hL]
  have h := gap_ge_of_logDeriv_341_bounds_scratch
    hgap h341 (by rw [hinvInv]; exact hzero)
      hone htwo hdenom
  convert h using 1
  all_goals
    field_simp [hL.ne']
    ring

end ArithmeticHodge.Analysis.MultiplicativeWeil


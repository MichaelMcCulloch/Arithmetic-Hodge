import Mathlib

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFourCellEvenEndpointSeedCoshBorderCompletionStructural

/-! # Exact scalar completion of the endpoint-cosh border -/

/-- The shared cosh selector in the finite/tail handoff is one exact bordered
square.  No sign or definiteness assumption is needed for the identity. -/
theorem coupled_scalar_cosh_border_completion
    (a W L P A B D s : ℝ)
    (hK : a * P ^ 2 + W * D ≠ 0) :
    a * (L - s * P) ^ 2 + W * (A - 2 * s * B + s ^ 2 * D) =
      a * L ^ 2 + W * A -
        (a * L * P + W * B) ^ 2 / (a * P ^ 2 + W * D) +
        (a * P ^ 2 + W * D) *
          (s - (a * L * P + W * B) /
            (a * P ^ 2 + W * D)) ^ 2 := by
  field_simp [hK]
  ring

/-- With a positive border diagonal, the completed value is minimized at the
exact scalar Schur selector. -/
theorem coupled_scalar_cosh_border_lower_bound
    (a W L P A B D s : ℝ)
    (hKpos : 0 < a * P ^ 2 + W * D) :
    a * L ^ 2 + W * A -
        (a * L * P + W * B) ^ 2 / (a * P ^ 2 + W * D) ≤
      a * (L - s * P) ^ 2 + W * (A - 2 * s * B + s ^ 2 * D) := by
  rw [coupled_scalar_cosh_border_completion a W L P A B D s hKpos.ne']
  exact le_add_of_nonneg_right
    (mul_nonneg hKpos.le (sq_nonneg
      (s - (a * L * P + W * B) / (a * P ^ 2 + W * D))))

end ArithmeticHodge.Analysis.YoshidaFourCellEvenEndpointSeedCoshBorderCompletionStructural

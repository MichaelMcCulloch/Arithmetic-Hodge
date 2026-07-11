import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Order

open Complex Real

theorem riemannZeta_dirichlet_uniform_bound (a : ℝ) (ha : 1 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, a ≤ s.re → ‖riemannZeta s‖ ≤ C := by
  have hmajor : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ a)⁻¹) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).2 (Real.summable_nat_rpow_inv.mpr ha)
  let C : ℝ := ∑' n : ℕ, (((n + 1 : ℕ) : ℝ) ^ a)⁻¹
  refine ⟨C + 1, ?_, fun s hs => ?_⟩
  · have hC_nonneg : 0 ≤ C := tsum_nonneg (fun n => by positivity)
    linarith
  · have hs_one : 1 < s.re := lt_of_lt_of_le ha hs
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs_one]
    have hsum : Summable (fun n : ℕ => 1 / (n + 1 : ℂ) ^ s) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (summable_nat_add_iff 1).2 (Complex.summable_one_div_nat_cpow.mpr hs_one)
    have hpoint : ∀ n : ℕ,
        ‖1 / (n + 1 : ℂ) ^ s‖ ≤ (((n + 1 : ℕ) : ℝ) ^ a)⁻¹ := by
      intro n
      rw [norm_div, norm_one]
      have hn_pos : (0 : ℝ) < (n + 1 : ℕ) := by positivity
      rw [show (n + 1 : ℂ) = ((n + 1 : ℕ) : ℂ) by push_cast; rfl]
      rw [show ‖((n + 1 : ℕ) : ℂ) ^ s‖ =
          (((n + 1 : ℕ) : ℝ) ^ s.re) by
        exact Complex.norm_natCast_cpow_of_pos (Nat.succ_pos n) s]
      rw [one_div]
      apply (inv_le_inv₀ (Real.rpow_pos_of_pos hn_pos s.re)
        (Real.rpow_pos_of_pos hn_pos a)).2
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hs
    calc
      ‖∑' n : ℕ, 1 / (n + 1 : ℂ) ^ s‖
          ≤ ∑' n : ℕ, ‖1 / (n + 1 : ℂ) ^ s‖ := norm_tsum_le_tsum_norm hsum.norm
      _ ≤ ∑' n : ℕ, (((n + 1 : ℕ) : ℝ) ^ a)⁻¹ :=
        hsum.norm.tsum_le_tsum hpoint hmajor
      _ ≤ C + 1 := by dsimp [C]; linarith

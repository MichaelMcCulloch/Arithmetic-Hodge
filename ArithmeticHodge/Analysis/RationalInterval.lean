import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace ArithmeticHodge.Analysis

/-!
# Exact rational interval arithmetic

The endpoints are rational and therefore kernel-computable.  `Contains`
interprets an interval over the reals, while the arithmetic theorems prove
that each computed enclosure contains the corresponding real operation.
Multiplication uses all four endpoint products, so it remains sound when
either input straddles zero.
-/

structure RatInterval where
  lower : ℚ
  upper : ℚ
deriving DecidableEq, Repr

namespace RatInterval

def Contains (I : RatInterval) (x : ℝ) : Prop :=
  (I.lower : ℝ) ≤ x ∧ x ≤ (I.upper : ℝ)

def Valid (I : RatInterval) : Prop := I.lower ≤ I.upper

theorem valid_of_contains {I : RatInterval} {x : ℝ} (hx : I.Contains x) :
    I.Valid :=
  (Rat.cast_le (K := ℝ)).1 (hx.1.trans hx.2)

def pure (q : ℚ) : RatInterval := ⟨q, q⟩

def neg (I : RatInterval) : RatInterval := ⟨-I.upper, -I.lower⟩

def add (I J : RatInterval) : RatInterval :=
  ⟨I.lower + J.lower, I.upper + J.upper⟩

def sub (I J : RatInterval) : RatInterval :=
  ⟨I.lower - J.upper, I.upper - J.lower⟩

private def min4 (a b c d : ℚ) : ℚ := min (min a b) (min c d)

private def max4 (a b c d : ℚ) : ℚ := max (max a b) (max c d)

def mul (I J : RatInterval) : RatInterval :=
  ⟨min4 (I.lower * J.lower) (I.lower * J.upper)
      (I.upper * J.lower) (I.upper * J.upper),
    max4 (I.lower * J.lower) (I.lower * J.upper)
      (I.upper * J.lower) (I.upper * J.upper)⟩

def inv (I : RatInterval) : RatInterval :=
  ⟨I.upper⁻¹, I.lower⁻¹⟩

def div (I J : RatInterval) : RatInterval := mul I (inv J)

instance instNeg : Neg RatInterval := ⟨neg⟩
instance instAdd : Add RatInterval := ⟨add⟩
instance instSub : Sub RatInterval := ⟨sub⟩
instance instMul : Mul RatInterval := ⟨mul⟩
instance instInv : Inv RatInterval := ⟨inv⟩
instance instDiv : Div RatInterval := ⟨div⟩

@[simp] theorem contains_pure (q : ℚ) : (pure q).Contains (q : ℝ) := by
  simp [Contains, pure]

theorem contains_neg {I : RatInterval} {x : ℝ} (hx : I.Contains x) :
    (-I).Contains (-x) := by
  change (neg I).Contains (-x)
  norm_num [Contains, neg] at hx ⊢
  exact ⟨hx.2, hx.1⟩

theorem contains_add {I J : RatInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) :
    (I + J).Contains (x + y) := by
  change (add I J).Contains (x + y)
  norm_num [Contains, add] at hx hy ⊢
  exact ⟨add_le_add hx.1 hy.1, add_le_add hx.2 hy.2⟩

theorem contains_sub {I J : RatInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) :
    (I - J).Contains (x - y) := by
  change (sub I J).Contains (x - y)
  norm_num [Contains, sub] at hx hy ⊢
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

private theorem const_mul_mem_corners
    {a c d z : ℝ} (hz : c ≤ z ∧ z ≤ d) :
    min (a * c) (a * d) ≤ a * z ∧
      a * z ≤ max (a * c) (a * d) := by
  by_cases ha : 0 ≤ a
  · constructor
    · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left hz.1 ha)
    · exact (mul_le_mul_of_nonneg_left hz.2 ha).trans (le_max_right _ _)
  · have ha' : a ≤ 0 := le_of_not_ge ha
    constructor
    · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_left hz.2 ha')
    · exact (mul_le_mul_of_nonpos_left hz.1 ha').trans (le_max_left _ _)

private theorem mul_mem_corners
    {a b c d x y : ℝ} (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d) :
    min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ x * y ∧
      x * y ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
  have ha := const_mul_mem_corners (a := a) hy
  have hb := const_mul_mem_corners (a := b) hy
  by_cases hy0 : 0 ≤ y
  · constructor
    · exact (min_le_left _ _).trans (ha.1.trans
        (mul_le_mul_of_nonneg_right hx.1 hy0))
    · exact (mul_le_mul_of_nonneg_right hx.2 hy0).trans
        (hb.2.trans (le_max_right _ _))
  · have hy0' : y ≤ 0 := le_of_not_ge hy0
    constructor
    · exact (min_le_right _ _).trans (hb.1.trans
        (mul_le_mul_of_nonpos_right hx.2 hy0'))
    · exact (mul_le_mul_of_nonpos_right hx.1 hy0').trans
        (ha.2.trans (le_max_left _ _))

theorem contains_mul {I J : RatInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) :
    (I * J).Contains (x * y) := by
  change (mul I J).Contains (x * y)
  simpa [Contains, mul, min4, max4] using mul_mem_corners hx hy

theorem contains_inv_of_pos {I : RatInterval} {x : ℝ}
    (hpos : 0 < I.lower) (hx : I.Contains x) :
    I⁻¹.Contains x⁻¹ := by
  have hl : (0 : ℝ) < (I.lower : ℝ) :=
    (Rat.cast_pos (K := ℝ)).2 hpos
  have hxpos : 0 < x := hl.trans_le hx.1
  have hu : 0 < (I.upper : ℝ) := hxpos.trans_le hx.2
  change (inv I).Contains x⁻¹
  norm_num [Contains, inv]
  exact ⟨by simpa [one_div] using one_div_le_one_div_of_le hxpos hx.2,
    by simpa [one_div] using one_div_le_one_div_of_le hl hx.1⟩

theorem contains_div_of_pos {I J : RatInterval} {x y : ℝ}
    (hypos : 0 < J.lower) (hx : I.Contains x) (hy : J.Contains y) :
    (I / J).Contains (x / y) := by
  change (mul I (inv J)).Contains (x * y⁻¹)
  exact contains_mul hx (contains_inv_of_pos hypos hy)

end RatInterval

end ArithmeticHodge.Analysis

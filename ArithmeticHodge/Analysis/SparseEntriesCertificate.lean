import ArithmeticHodge.Analysis.SparseCongruenceCertificate

set_option autoImplicit false

open scoped BigOperators

namespace ArithmeticHodge.Analysis.SparseEntriesCertificate

open SparseCongruenceCertificate

/-- A kernel-computable sparse row payload. Repeated indices are permitted and
their coefficients add when the payload is converted to a `Finsupp`. -/
abbrev SparseEntries (n : Type*) := List (n × ℚ)

/-- Value of a pair-list payload at one index, including repeated entries. -/
def entriesValue {n : Type*} [DecidableEq n] :
    SparseEntries n → n → ℚ
  | [], _ => 0
  | (j, q) :: xs, i => (if j = i then q else 0) + entriesValue xs i

private theorem mem_map_fst_of_entriesValue_ne_zero
    {n : Type*} [DecidableEq n] {xs : SparseEntries n} {i : n}
    (h : entriesValue xs i ≠ 0) :
    i ∈ xs.map Prod.fst := by
  induction xs with
  | nil => simp [entriesValue] at h
  | cons p xs ih =>
      rcases p with ⟨j, q⟩
      by_cases hji : j = i
      · simp [hji]
      · have htail : entriesValue xs i ≠ 0 := by
          simpa [entriesValue, hji] using h
        simp [ih htail]

/-- Convert a pair-list payload to the existing sparse-row representation.
The support is constructed with the supplied decidable equality rather than
through the noncomputable additive instance on `Finsupp`. -/
def rowOfEntries {n : Type*} [DecidableEq n]
    (xs : SparseEntries n) : SparseRow n where
  support := (xs.map Prod.fst).toFinset.filter fun i ↦ entriesValue xs i ≠ 0
  toFun := entriesValue xs
  mem_support_toFun i := by
    simp only [Finset.mem_filter, List.mem_toFinset]
    constructor
    · exact fun h ↦ h.2
    · exact fun h ↦ ⟨mem_map_fst_of_entriesValue_ne_zero h, h⟩

/-- The uncancelled coefficient `L¹` budget of a pair-list payload. -/
def entriesL1 {n : Type*} : SparseEntries n → ℚ
  | [] => 0
  | (_, q) :: xs => |q| + entriesL1 xs

/-- Exact pair-list evaluation of a congruence entry. Duplicate indices remain
separate here and are combined by linearity in the bridge theorem below. -/
def entriesCongruence {n : Type*} (xs ys : SparseEntries n)
    (C : Matrix n n ℚ) : ℚ :=
  (xs.map fun p ↦
    (ys.map fun q ↦ p.2 * C p.1 q.1 * q.2).sum).sum

@[simp] theorem rowOfEntries_apply
    {n : Type*} [DecidableEq n] (xs : SparseEntries n) (i : n) :
    rowOfEntries xs i = entriesValue xs i :=
  rfl

/-- A nonzero accumulated coefficient must have at least one source entry at
that index. The converse is intentionally false when duplicates cancel. -/
theorem mem_map_fst_of_rowOfEntries_apply_ne_zero
    {n : Type*} [DecidableEq n] {xs : SparseEntries n} {i : n}
    (h : rowOfEntries xs i ≠ 0) :
    i ∈ xs.map Prod.fst :=
  mem_map_fst_of_entriesValue_ne_zero h

private theorem entriesValue_dense_l1_le_entriesL1
    {n : Type*} [Fintype n] [DecidableEq n] (xs : SparseEntries n) :
    (∑ i, |entriesValue xs i|) ≤ entriesL1 xs := by
  induction xs with
  | nil => simp [entriesValue, entriesL1]
  | cons p xs ih =>
      rcases p with ⟨j, q⟩
      simp only [entriesValue, entriesL1]
      calc
        (∑ i, |(if j = i then q else 0) + entriesValue xs i|) ≤
            ∑ i, (|(if j = i then q else 0)| + |entriesValue xs i|) := by
          exact Finset.sum_le_sum fun i _hi ↦ abs_add_le _ _
        _ = (∑ i, |(if j = i then q else 0)|) +
              ∑ i, |entriesValue xs i| := Finset.sum_add_distrib
        _ = |q| + ∑ i, |entriesValue xs i| := by
          have hsingle : (∑ i, |(if j = i then q else 0)|) = |q| := by
            simp only [abs_ite, abs_zero, Fintype.sum_ite_eq]
          rw [hsingle]
        _ ≤ |q| + entriesL1 xs := add_le_add (le_refl |q|) ih

/-- The dense `L¹` norm of the accumulated row is bounded by the uncancelled
pair-list budget. This remains sound in the presence of duplicates. -/
theorem rowOfEntries_dense_l1_le_entriesL1
    {n : Type*} [Fintype n] [DecidableEq n] (xs : SparseEntries n) :
    (∑ i, |rowOfEntries xs i|) ≤ entriesL1 xs := by
  simpa only [rowOfEntries_apply] using
    entriesValue_dense_l1_le_entriesL1 xs

/-- `Finsupp.sum` form of `rowOfEntries_dense_l1_le_entriesL1`, matching the
row norm used by the sparse congruence certificate. -/
theorem rowOfEntries_l1_le_entriesL1
    {n : Type*} [Fintype n] [DecidableEq n] (xs : SparseEntries n) :
    (rowOfEntries xs).sum (fun _ q ↦ |q|) ≤ entriesL1 xs := by
  simpa [Finsupp.sum_fintype] using
    rowOfEntries_dense_l1_le_entriesL1 xs

private theorem entriesValue_sum_hom
    {n : Type*} [Fintype n] [DecidableEq n]
    (xs : SparseEntries n) (f : n → ℚ →+ ℚ) :
    (∑ i, f i (entriesValue xs i)) =
      (xs.map fun p ↦ f p.1 p.2).sum := by
  induction xs with
  | nil => simp [entriesValue]
  | cons p xs ih =>
      rcases p with ⟨j, q⟩
      simp only [entriesValue, map_add, Finset.sum_add_distrib,
        List.map_cons, List.sum_cons]
      rw [ih]
      congr 1
      simp only [apply_ite, map_zero, Fintype.sum_ite_eq]

private def congruenceInnerHom
    {n : Type*} (C : Matrix n n ℚ) (i : n) (pi : ℚ) (j : n) :
    ℚ →+ ℚ where
  toFun pj := pi * C i j * pj
  map_zero' := by ring
  map_add' := by intro a b; ring

private def congruenceOuterHom
    {n : Type*} [Fintype n] [DecidableEq n]
    (ys : SparseEntries n) (C : Matrix n n ℚ) (i : n) : ℚ →+ ℚ where
  toFun pi := ∑ j, pi * C i j * entriesValue ys j
  map_zero' := by simp
  map_add' := by
    intro a b
    simp only [add_mul, Finset.sum_add_distrib]

private theorem entriesValue_congruence_inner
    {n : Type*} [Fintype n] [DecidableEq n]
    (ys : SparseEntries n) (C : Matrix n n ℚ) (i : n) (pi : ℚ) :
    (∑ j, pi * C i j * entriesValue ys j) =
      (ys.map fun q ↦ pi * C i q.1 * q.2).sum := by
  exact entriesValue_sum_hom ys (congruenceInnerHom C i pi)

/-- Pair-list congruence evaluation agrees exactly with the existing Finsupp
evaluator, even when either list contains repeated indices. -/
theorem sparseCongruenceEntry_rowOfEntries
    {n : Type*} [Fintype n] [DecidableEq n]
    (entries : n → SparseEntries n) (C : Matrix n n ℚ) (i j : n) :
    sparseCongruenceEntry (fun k ↦ rowOfEntries (entries k)) C i j =
      entriesCongruence (entries i) (entries j) C := by
  calc
    sparseCongruenceEntry (fun k ↦ rowOfEntries (entries k)) C i j =
        ∑ k, ∑ l,
          rowOfEntries (entries i) k * C k l *
            rowOfEntries (entries j) l := by
      simp [sparseCongruenceEntry, Finsupp.sum_fintype]
    _ = ∑ k, congruenceOuterHom (entries j) C k
          (entriesValue (entries i) k) := by
      simp only [rowOfEntries_apply]
      rfl
    _ = entriesCongruence (entries i) (entries j) C := by
      rw [entriesValue_sum_hom]
      unfold entriesCongruence
      induction entries i with
      | nil => rfl
      | cons p xs ih =>
          simp only [List.map_cons, List.sum_cons]
          have hhead :
              (congruenceOuterHom (entries j) C p.1) p.2 =
                (List.map (fun q ↦ p.2 * C p.1 q.1 * q.2)
                  (entries j)).sum := by
            simpa only [congruenceOuterHom] using
              entriesValue_congruence_inner (entries j) C p.1 p.2
          rw [hhead, ih]

end ArithmeticHodge.Analysis.SparseEntriesCertificate

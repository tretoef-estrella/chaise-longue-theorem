module

public import RequestProject.Pfaffian.Basic

/-!
# Part A of `q_pfaffian.md`: (A1), the sum over perfect matchings

A perfect matching of `Fin m` is an involution `π` of `Fin m` without fixed points (given as a
function `π : Fin m → Fin m` with `π (π x) = x` and `π x ≠ x`; such a function is automatically
a bijection), and its number of crossings is `cr(π) = #{(x, y) : x < y < π(x) < π(y)}`.

Proof by induction on `m` with the definition, as in the file: a perfect matching `π` is the
pair `{0, j}` together with a perfect matching `π'` of the other indices; the pair `{0, j}`
crosses exactly the pairs of `π'` with one end among `1, …, j − 1`, and their number has the
parity of `j − 1`.
-/

@[expose] public section

namespace Pfaffian

open Finset

variable {R : Type*} [CommRing R]

/-- **(A1)** of Theorem A in `q_pfaffian.md`: a perfect matching of `Fin m`, i.e. an involution
of `Fin m` without fixed points. -/
def IsMatching {m : ℕ} (π : Fin m → Fin m) : Prop := (∀ x, π (π x) = x) ∧ ∀ x, π x ≠ x

/-- Decidability of being a perfect matching (**(A1)** of `q_pfaffian.md`). -/
instance {m : ℕ} : DecidablePred (IsMatching (m := m)) := fun π => by
  unfold IsMatching; infer_instance

/-- **(A1)** of Theorem A in `q_pfaffian.md`: the number of crossings
`cr(π) := #{(x, y) : x < y < π(x) < π(y)}` of a perfect matching. -/
def crossings {m : ℕ} (π : Fin m → Fin m) : ℕ :=
  (univ.filter (fun xy : Fin m × Fin m => xy.1 < xy.2 ∧ xy.2 < π xy.1 ∧ π xy.1 < π xy.2)).card

/-- Auxiliary for (A1) of `q_pfaffian.md`: decomposition of a product over `Fin (m+2)` into the indices `0`,
`j = j'+1` and the others. -/
theorem prod_decomp {M : Type*} [CommMonoid M] {m : ℕ} (j' : Fin (m + 1))
    (F : Fin (m + 2) → M) :
    ∏ x, F x = F 0 * F j'.succ * ∏ i : Fin m, F (j'.succAbove i).succ := by
  rw [Fin.prod_univ_succ, Fin.prod_univ_succAbove _ j', mul_assoc]

/-- Auxiliary for (A1) of `q_pfaffian.md`: `(−1)^{#{x ∈ s : P x}}` as a product. -/
theorem neg_one_pow_card_filter {α : Type*} (s : Finset α) (P : α → Prop) [DecidablePred P] :
    (-1 : R) ^ (s.filter P).card = ∏ x ∈ s, if P x then -1 else 1 := by
  rw [prod_ite, prod_const_one, mul_one, prod_const]

/-- Auxiliary for (A1) of `q_pfaffian.md`: the perfect matching of `Fin (m+2)` made of the pair `{0, j'+1}` and of
the perfect matching `π'` of the other indices. -/
def extM {m : ℕ} (j' : Fin (m + 1)) (π' : Fin m → Fin m) : Fin (m + 2) → Fin (m + 2) :=
  Fin.cons (α := fun _ => Fin (m + 2)) j'.succ
    (Fin.insertNth (α := fun _ => Fin (m + 2)) j' 0 (fun i => (j'.succAbove (π' i)).succ))

/-- Auxiliary for (A1) of `q_pfaffian.md`: `extM j' π'` sends `0` to `j = j' + 1`. -/
theorem extM_zero {m : ℕ} (j' : Fin (m + 1)) (π' : Fin m → Fin m) : extM j' π' 0 = j'.succ := by
  simp [extM]

/-- Auxiliary for (A1) of `q_pfaffian.md`: `extM j' π'` sends `j = j' + 1` to `0`. -/
theorem extM_j {m : ℕ} (j' : Fin (m + 1)) (π' : Fin m → Fin m) : extM j' π' j'.succ = 0 := by
  simp [extM]

/-- Auxiliary for (A1) of `q_pfaffian.md`: `extM j' π'` on the other indices is `π'`. -/
theorem extM_f {m : ℕ} (j' : Fin (m + 1)) (π' : Fin m → Fin m) (i : Fin m) :
    extM j' π' (j'.succAbove i).succ = (j'.succAbove (π' i)).succ := by
  simp [extM]

/-- Auxiliary for (A1) of `q_pfaffian.md`: the other indices are not `0`. -/
theorem f_ne_zero {m : ℕ} (j' : Fin (m + 1)) (i : Fin m) : (j'.succAbove i).succ ≠ 0 :=
  Fin.succ_ne_zero _

/-- Auxiliary for (A1) of `q_pfaffian.md`: the other indices are not `j = j' + 1`. -/
theorem f_ne_j {m : ℕ} (j' : Fin (m + 1)) (i : Fin m) : (j'.succAbove i).succ ≠ j'.succ :=
  fun h => Fin.succAbove_ne _ _ (Fin.succ_injective _ h)

/-- Auxiliary for (A1) of `q_pfaffian.md`: the enumeration of the other indices is injective. -/
theorem f_inj {m : ℕ} (j' : Fin (m + 1)) {i k : Fin m}
    (h : (j'.succAbove i).succ = (j'.succAbove k).succ) : i = k :=
  Fin.succAbove_right_injective (Fin.succ_injective _ h)

/-- Auxiliary for (A1) of `q_pfaffian.md`: the enumeration of the other indices is increasing. -/
theorem f_lt_iff {m : ℕ} (j' : Fin (m + 1)) (i k : Fin m) :
    (j'.succAbove i).succ < (j'.succAbove k).succ ↔ i < k := by
  rw [Fin.succ_lt_succ_iff, Fin.succAbove_lt_succAbove_iff]

/-- Auxiliary for (A1) of `q_pfaffian.md`: every index of `Fin (m+2)` is `0`, `j' + 1` or `(j'.succAbove i) + 1`. -/
theorem cases3 {m : ℕ} (j' : Fin (m + 1)) (y : Fin (m + 2)) :
    y = 0 ∨ y = j'.succ ∨ ∃ i, (j'.succAbove i).succ = y := by
  rcases Fin.eq_zero_or_eq_succ y with h | ⟨y1, rfl⟩
  · exact Or.inl h
  · by_cases h : y1 = j'
    · exact Or.inr (Or.inl (by rw [h]))
    · obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq h
      exact Or.inr (Or.inr ⟨i, rfl⟩)

/-- Auxiliary for (A1) of `q_pfaffian.md`: `extM j' π'` is a perfect matching. -/
theorem extM_isMatching {m : ℕ} (j' : Fin (m + 1)) {π' : Fin m → Fin m} (h : IsMatching π') :
    IsMatching (extM j' π') := by
  constructor
  · intro y
    rcases cases3 j' y with rfl | rfl | ⟨i, rfl⟩
    · rw [extM_zero, extM_j]
    · rw [extM_j, extM_zero]
    · rw [extM_f, extM_f, h.1]
  · intro y
    rcases cases3 j' y with rfl | rfl | ⟨i, rfl⟩
    · rw [extM_zero]; exact Fin.succ_ne_zero _
    · rw [extM_j]; exact (Fin.succ_ne_zero _).symm
    · rw [extM_f]; exact fun e => h.2 i (f_inj j' e)

/-- Auxiliary for (A1) of `q_pfaffian.md`: `#{k < t}` in `Fin m` is `t` for `t ≤ m`. -/
theorem card_filter_val_lt {m t : ℕ} (h : t ≤ m) :
    (univ.filter (fun k : Fin m => (k : ℕ) < t)).card = t := by
  have e : (univ.filter (fun k : Fin m => (k : ℕ) < t)).map Fin.valEmbedding = range t := by
    ext x
    simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_range]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact hy
    · intro hx; exact ⟨⟨x, by omega⟩, hx, rfl⟩
  rw [← card_map, e, card_range]

/-- Auxiliary for (A1) of `q_pfaffian.md`: `j'.succAbove k < j' ↔ k < j'`. -/
theorem succAbove_lt_iff_val {m : ℕ} (j' : Fin (m + 1)) (k : Fin m) :
    j'.succAbove k < j' ↔ (k : ℕ) < j' := by
  rcases lt_or_ge k.castSucc j' with h | h
  · rw [Fin.succAbove_of_castSucc_lt _ _ h]; simp only [Fin.lt_def, Fin.val_castSucc] at h ⊢
  · rw [Fin.succAbove_of_le_castSucc _ _ h]; simp [Fin.lt_def, Fin.le_def] at h ⊢; omega

/-- Auxiliary for (A1) of `q_pfaffian.md`: `j' < j'.succAbove k ↔ j' ≤ k`. -/
theorem lt_succAbove_iff_val {m : ℕ} (j' : Fin (m + 1)) (k : Fin m) :
    j' < j'.succAbove k ↔ (j' : ℕ) ≤ k := by
  constructor
  · intro h
    by_contra h'
    exact lt_asymm h ((succAbove_lt_iff_val j' k).2 (by omega))
  · intro h
    refine lt_of_le_of_ne (not_lt.1 fun h' => ?_) (Fin.succAbove_ne _ _).symm
    have := (succAbove_lt_iff_val j' k).1 h'
    omega

/-- Auxiliary for (A1) of `q_pfaffian.md`: the pair `{0, j}` crosses a number of pairs of `π'` of the parity of
`j − 1 = j'`. -/
theorem parity_lemma {m : ℕ} (j' : Fin (m + 1)) {π' : Fin m → Fin m} (h : IsMatching π') :
    ∏ k : Fin m, (if (j'.succAbove k).succ < j'.succ ∧ j'.succ < (j'.succAbove (π' k)).succ
      then (-1 : R) else 1) = (-1) ^ (j' : ℕ) := by
  simp only [Fin.succ_lt_succ_iff, succAbove_lt_iff_val, lt_succAbove_iff_val]
  have e1 : ∀ k : Fin m, (if (k : ℕ) < j' ∧ (j' : ℕ) ≤ π' k then (-1 : R) else 1) =
      if (k : ℕ) < j' then (if (j' : ℕ) ≤ π' k then -1 else 1) else 1 := by
    intro k; split_ifs <;> simp_all
  simp only [e1]
  rw [← prod_filter]
  have e2 : ∀ k ∈ univ.filter (fun k : Fin m => (k : ℕ) < j'),
      (if (j' : ℕ) ≤ π' k then (-1 : R) else 1) =
        (-1) * (if ((π' k : Fin m) : ℕ) < j' then -1 else 1) := by
    intro k _
    by_cases hk : (j' : ℕ) ≤ π' k
    · rw [if_pos hk, if_neg (not_lt.2 hk)]; ring
    · rw [if_neg hk, if_pos (not_le.1 hk)]; ring
  rw [prod_congr rfl e2, prod_mul_distrib, prod_const,
    card_filter_val_lt (Nat.lt_succ_iff.1 j'.2), ← prod_filter]
  have e3 : ∏ k ∈ (univ.filter (fun k : Fin m => (k : ℕ) < j')).filter
      (fun k => ((π' k : Fin m) : ℕ) < j'), (-1 : R) = 1 := by
    refine prod_involution (fun k _ => π' k) (fun k _ => by ring) (fun k _ _ => h.2 k)
      (fun k hk => ?_) (fun k _ => h.1 k)
    simp only [mem_filter, mem_univ, true_and] at hk ⊢
    exact ⟨hk.2, by rw [h.1]; exact hk.1⟩
  rw [e3, mul_one]

/-- Auxiliary for (A1) of `q_pfaffian.md`: the crossings of `extM j' π'`. -/
theorem extM_cross {m : ℕ} (j' : Fin (m + 1)) {π' : Fin m → Fin m} (h : IsMatching π') :
    (-1 : R) ^ (crossings (extM j' π')) = (-1) ^ (j' : ℕ) * (-1) ^ (crossings π') := by
  unfold crossings
  rw [neg_one_pow_card_filter, neg_one_pow_card_filter, ← univ_product_univ, prod_product,
    ← univ_product_univ, prod_product]
  simp only [prod_decomp j', extM_zero, extM_j, extM_f, f_lt_iff,
    Fin.not_lt_zero, false_and, and_false, if_false, mul_one, one_mul, prod_const_one,
    Fin.succ_pos, true_and]
  rw [parity_lemma j' h]

/-- Auxiliary for (A1) of `q_pfaffian.md`: the product of `extM j' π'`. -/
theorem extM_prod {m : ℕ} (A : Matrix (Fin (m + 2)) (Fin (m + 2)) R) (j' : Fin (m + 1))
    (π' : Fin m → Fin m) :
    ∏ x ∈ univ.filter (fun x => x < extM j' π' x), A x (extM j' π' x) =
      A 0 j'.succ * ∏ i ∈ univ.filter (fun i => i < π' i),
        (A.submatrix (fun i => (j'.succAbove i).succ) (fun i => (j'.succAbove i).succ)) i
          (π' i) := by
  rw [prod_filter, prod_filter, prod_decomp j']
  simp only [extM_zero, extM_j, extM_f, f_lt_iff, Fin.succ_pos, if_true, Fin.not_lt_zero,
    if_false, mul_one, Matrix.submatrix_apply]

/-- Auxiliary for (A1) of `q_pfaffian.md`: every perfect matching `π` of `Fin (m+2)` with `π 0 = j' + 1` is
`extM j' π'` for a perfect matching `π'` of `Fin m`. -/
theorem exists_extM {m : ℕ} (j' : Fin (m + 1)) {π : Fin (m + 2) → Fin (m + 2)}
    (hπ : IsMatching π) (h0 : π 0 = j'.succ) :
    ∃ π' : Fin m → Fin m, IsMatching π' ∧ extM j' π' = π := by
  have hex : ∀ i : Fin m, ∃ k, (j'.succAbove k).succ = π (j'.succAbove i).succ := by
    intro i
    rcases cases3 j' (π (j'.succAbove i).succ) with h | h | h
    · exfalso
      have := congrArg π h
      rw [hπ.1, h0] at this
      exact f_ne_j j' i this
    · exfalso
      rw [← h0] at h
      have := congrArg π h
      rw [hπ.1, hπ.1] at this
      exact f_ne_zero j' i this
    · exact h
  choose π' hπ' using hex
  have key : ∀ i, (j'.succAbove (π' i)).succ = π (j'.succAbove i).succ := hπ'
  refine ⟨π', ⟨fun i => f_inj j' ?_, fun i e => ?_⟩, ?_⟩
  · rw [key, key, hπ.1]
  · have := key i
    rw [e] at this
    exact hπ.2 _ this.symm
  · funext y
    rcases cases3 j' y with rfl | rfl | ⟨i, rfl⟩
    · rw [extM_zero, h0]
    · rw [extM_j, ← h0, hπ.1]
    · rw [extM_f, key]

/-- **(A1)** of Theorem A in `q_pfaffian.md` (the sum over perfect matchings; the definition
printed in the paper): `pf(A) = Σ_π (−1)^{cr(π)}·Π_{x : x < π(x)} A(x, π(x))`, the sum over all
perfect matchings `π` of `Fin m` (fixed-point-free involutions `π : Fin m → Fin m`), with
`cr(π) = #{(x, y) : x < y < π(x) < π(y)}`. This holds for every matrix `A` (alternating or not),
a slightly more general statement. -/
theorem pf_eq_sum_matchings : ∀ (m : ℕ) (A : Matrix (Fin m) (Fin m) R),
    pf m A = ∑ π ∈ univ.filter (fun π : Fin m → Fin m => IsMatching π),
      (-1) ^ (crossings π) * ∏ x ∈ univ.filter (fun x => x < π x), A x (π x)
  | 0, A => by
    rw [pf_zero]
    have : univ.filter (fun π : Fin 0 → Fin 0 => IsMatching π) = {fun x => x.elim0} := by
      ext π
      simp only [mem_filter, mem_univ, true_and, mem_singleton]
      constructor
      · intro _; funext x; exact x.elim0
      · intro _; exact ⟨fun x => x.elim0, fun x => x.elim0⟩
    rw [this, sum_singleton]
    simp [crossings]
  | 1, A => by
    rw [pf_one]; symm; apply sum_eq_zero; intro π hπ
    simp only [mem_filter, mem_univ, true_and] at hπ
    exact absurd (Subsingleton.elim (π 0) 0) (hπ.2 0)
  | m + 2, A => by
    rw [pf_succ_succ]
    conv_rhs => rw [← Finset.sum_fiberwise_of_maps_to
      (s := univ.filter (fun π : Fin (m + 2) → Fin (m + 2) => IsMatching π))
      (g := fun π => π 0) (t := univ) (fun _ _ => mem_univ _), Fin.sum_univ_succ]
    rw [sum_eq_zero (s := (univ.filter (fun π : Fin (m + 2) → Fin (m + 2) => IsMatching π)).filter
      (fun π => π 0 = 0)) (fun π hπ => by
      simp only [mem_filter, mem_univ, true_and] at hπ
      exact absurd hπ.2 (hπ.1.2 0)), zero_add]
    refine sum_congr rfl fun j' _ => ?_
    rw [pf_eq_sum_matchings m, mul_sum]
    refine Finset.sum_bij (fun π' _ => extM j' π') ?_ ?_ ?_ ?_
    · intro π' hπ'
      simp only [mem_filter, mem_univ, true_and] at hπ' ⊢
      exact ⟨extM_isMatching j' hπ', extM_zero j' π'⟩
    · intro π1 _ π2 _ h
      funext i
      have := congrFun h (j'.succAbove i).succ
      simp only at this
      rw [extM_f, extM_f] at this
      exact f_inj j' this
    · intro π hπ
      simp only [mem_filter, mem_univ, true_and] at hπ
      obtain ⟨π', hπ', rfl⟩ := exists_extM j' hπ.1 hπ.2
      exact ⟨π', by simpa using hπ', rfl⟩
    · intro π' hπ'
      simp only [mem_filter, mem_univ, true_and] at hπ'
      rw [extM_cross j' hπ', extM_prod]
      ring

end Pfaffian

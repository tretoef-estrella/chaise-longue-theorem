module

public import RequestProject.Pfaffian.ExpandVar

/-!
# Part B of `q_pfaffian.md`: (B5), the Laplace expansion

Proof of (B5) by induction on the number `s` of borders with (B2) (expansion along the last
border), as in the file: the subsets `S` of the right side that contain `b` correspond to the
subsets of the complement of `b`, and each determinant is expanded along its last column.

The sum over the `s`-subsets `S` of `Fin n` is written as a sum over the subtype
`{S : Finset (Fin n) // S.card = s}`; "the elements of `S` in increasing order" is
`S.orderEmbOfFin`.
-/

@[expose] public section

namespace Pfaffian

open Finset Equiv

variable {R : Type*} [CommRing R]

/-- Auxiliary for (B5) of `q_pfaffian.md` (via (A0)): a minor with an odd number of indices has Pfaffian `0`. -/
theorem pfS_odd {N k : ℕ} (A : Matrix (Fin N) (Fin N) R) (S : Finset (Fin N)) (hk : Odd k) :
    pfS k A S = 0 := by
  unfold pfS; split_ifs
  · exact pf_odd _ _ hk
  · rfl

/-- Auxiliary for (B5) of `q_pfaffian.md`: transport of `Finset.orderEmbOfFin` along an equality of sets. -/
theorem orderEmbOfFin_congr {α : Type*} [LinearOrder α] {s t : Finset α} (hst : s = t) {k : ℕ}
    (h : s.card = k) (i : Fin k) : s.orderEmbOfFin h i = t.orderEmbOfFin (hst ▸ h) i := by
  subst hst; rfl

/-- Auxiliary for (B5) of `q_pfaffian.md`: the position of the `p`-th element of `S` is the number of smaller elements. -/
theorem card_filter_lt_orderEmbOfFin {n m : ℕ} (S : Finset (Fin n)) (h : S.card = m)
    (p : Fin m) : (S.filter (· < S.orderEmbOfFin h p)).card = p := by
  have e : S.filter (· < S.orderEmbOfFin h p) =
      (Finset.Iio p).map (S.orderEmbOfFin h).toEmbedding := by
    ext y
    simp only [mem_filter, mem_map, mem_Iio, RelEmbedding.coe_toEmbedding]
    constructor
    · rintro ⟨hy, hlt⟩
      have : y ∈ Set.range (S.orderEmbOfFin h) := by
        rw [Finset.range_orderEmbOfFin]; exact hy
      obtain ⟨q, rfl⟩ := this
      exact ⟨q, (S.orderEmbOfFin h).lt_iff_lt.1 hlt, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨Finset.orderEmbOfFin_mem _ _ _, (S.orderEmbOfFin h).lt_iff_lt.2 hq⟩
  rw [e, card_map, Fin.card_Iio]

/-- Auxiliary for (B5) of `q_pfaffian.md`: `b.succAbove` as an embedding. -/
def sAbove {n : ℕ} (b : Fin (n + 1)) : Fin n ↪ Fin (n + 1) :=
  ⟨b.succAbove, Fin.succAbove_right_injective⟩

/-- Auxiliary for (B5) of `q_pfaffian.md`: `b` is not in `b.succAbove(T)`. -/
theorem not_mem_map_sAbove {n : ℕ} (b : Fin (n + 1)) (T : Finset (Fin n)) :
    b ∉ T.map (sAbove b) := by
  simp only [mem_map, not_exists, not_and]
  intro t _ h; exact Fin.succAbove_ne _ _ h

/-- Auxiliary for (B5) of `q_pfaffian.md`: `|{b} ∪ b.succAbove(T)| = |T| + 1`. -/
theorem card_insert_map {n : ℕ} (b : Fin (n + 1)) (T : Finset (Fin n)) :
    (insert b (T.map (sAbove b))).card = T.card + 1 := by
  rw [card_insert_of_notMem (not_mem_map_sAbove b T), card_map]

/-- Auxiliary for (B5) of `q_pfaffian.md`: the value of `b.succAbove t`. -/
theorem val_succAbove_eq {n : ℕ} (b : Fin (n + 1)) (t : Fin n) :
    ((b.succAbove t : Fin (n + 1)) : ℕ) = t + if t.castSucc < b then 0 else 1 := by
  split_ifs with h
  · rw [Fin.succAbove_of_castSucc_lt _ _ h]; simp
  · rw [Fin.succAbove_of_le_castSucc _ _ (not_lt.1 h)]; simp

/-- Auxiliary for (B5) of `q_pfaffian.md`: the sum of the elements of `{b} ∪ b.succAbove(T)`. -/
theorem sum_insert_map {n : ℕ} (b : Fin (n + 1)) (T : Finset (Fin n)) :
    ∑ x ∈ insert b (T.map (sAbove b)), (x : ℕ) =
      b + ∑ t ∈ T, (t : ℕ) + (T.filter (fun t => ¬ t.castSucc < b)).card := by
  rw [sum_insert (not_mem_map_sAbove b T), sum_map]
  simp only [sAbove, Function.Embedding.coeFn_mk, val_succAbove_eq, sum_add_distrib]
  rw [add_assoc]
  congr 2
  rw [sum_ite, sum_const_zero, zero_add, sum_const, smul_eq_mul, mul_one]

/-- Auxiliary for (B5) of `q_pfaffian.md`: the position of `b` in `{b} ∪ b.succAbove(T)`. -/
theorem filter_lt_insert_map {n : ℕ} (b : Fin (n + 1)) (T : Finset (Fin n)) :
    ((insert b (T.map (sAbove b))).filter (· < b)).card =
      (T.filter (fun t => t.castSucc < b)).card := by
  rw [filter_insert, if_neg (lt_irrefl b), filter_map, card_map]
  congr 1
  apply Finset.filter_congr
  intro t _
  simp only [Function.comp_apply, sAbove, Function.Embedding.coeFn_mk]
  constructor
  · intro h
    by_contra h'
    rw [Fin.succAbove_of_le_castSucc _ _ (not_lt.1 h')] at h
    exact h' (lt_trans Fin.castSucc_lt_succ h)
  · intro h; rw [Fin.succAbove_of_castSucc_lt _ _ h]; exact h

/-- Auxiliary for (B5) of `q_pfaffian.md`: the expansion of a determinant `det(c_k(e i))` along its last column. -/
theorem det_expand_last {n s : ℕ} (c : Fin (s + 1) → Fin n → R) (e : Fin (s + 1) → Fin n) :
    (Matrix.of fun i k => c k (e i)).det = ∑ p : Fin (s + 1), (-1) ^ ((p : ℕ) + s) *
      c (Fin.last s) (e p) * (Matrix.of fun i k => c k.castSucc (e (p.succAbove i))).det := by
  rw [Matrix.det_succ_column _ (Fin.last s)]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [Matrix.of_apply, Fin.val_last, Fin.succAbove_last]
  rfl

/-- Auxiliary for (B5) of `q_pfaffian.md`: the subset `{b} ∪ b.succAbove(T)` of `Fin (n+1)` together with the
position of `b` in it. -/
noncomputable def lapMap {n s : ℕ} (y : Fin (n + 1) × {T : Finset (Fin n) // T.card = s}) :
    {S : Finset (Fin (n + 1)) // S.card = s + 1} × Fin (s + 1) :=
  (⟨insert y.1 (y.2.1.map (sAbove y.1)), by rw [card_insert_map, y.2.2]⟩,
    ((insert y.1 (y.2.1.map (sAbove y.1))).orderIsoOfFin
      (by rw [card_insert_map, y.2.2])).symm ⟨y.1, mem_insert_self _ _⟩)

/-- Auxiliary for (B5) of `q_pfaffian.md`: the element of `lapMap y` at the recorded position is `b`. -/
theorem lapMap_emb {n s : ℕ} (y : Fin (n + 1) × {T : Finset (Fin n) // T.card = s}) :
    (lapMap y).1.1.orderEmbOfFin (lapMap y).1.2 (lapMap y).2 = y.1 := by
  simp only [lapMap]
  rw [← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]

/-- Auxiliary for (B5) of `q_pfaffian.md`: the pairs `(b, T)` correspond bijectively to the pairs `(S, position of b in S)`. -/
theorem lapMap_bijective {n s : ℕ} :
    Function.Bijective (lapMap (n := n) (s := s)) := by
  constructor
  · rintro ⟨b, T⟩ ⟨b', T'⟩ h
    have hb : b = b' := by
      have := congrArg (fun x : {S : Finset (Fin (n + 1)) // S.card = s + 1} × Fin (s + 1) =>
        x.1.1.orderEmbOfFin x.1.2 x.2) h
      simpa only [lapMap_emb] using this
    subst hb
    have h1 := congrArg (fun x => x.1.1) h
    simp only [lapMap] at h1
    have h2 := congrArg (fun X => Finset.erase X b) h1
    simp only [erase_insert (not_mem_map_sAbove b _)] at h2
    rw [Finset.map_inj] at h2
    rw [Subtype.ext h2]
  · rintro ⟨⟨S, hS⟩, p⟩
    set b := S.orderEmbOfFin hS p with hb
    have hbS : b ∈ S := Finset.orderEmbOfFin_mem _ _ _
    have hmap : (univ.filter (fun t => b.succAbove t ∈ S)).map (sAbove b) = S.erase b := by
      ext y
      simp only [mem_map, mem_filter, mem_univ, true_and, sAbove, Function.Embedding.coeFn_mk,
        mem_erase]
      constructor
      · rintro ⟨t, ht, rfl⟩; exact ⟨Fin.succAbove_ne _ _, ht⟩
      · rintro ⟨hy, hyS⟩
        obtain ⟨t, rfl⟩ := Fin.exists_succAbove_eq hy
        exact ⟨t, hyS, rfl⟩
    have hT : (univ.filter (fun t => b.succAbove t ∈ S)).card = s := by
      have := congrArg Finset.card hmap
      rw [card_map, card_erase_of_mem hbS, hS] at this
      simpa using this
    have hins : insert b ((univ.filter (fun t => b.succAbove t ∈ S)).map (sAbove b)) = S := by
      rw [hmap, insert_erase hbS]
    refine ⟨(b, ⟨_, hT⟩), Prod.ext (Subtype.ext hins) ?_⟩
    apply (Finset.orderEmbOfFin _ (lapMap (b, ⟨_, hT⟩)).1.2).injective
    rw [lapMap_emb]
    simp only [lapMap]
    rw [orderEmbOfFin_congr hins]

/-- Auxiliary for (B5) of `q_pfaffian.md`: the sign bookkeeping of the induction step. -/
theorem lap_sign {n s : ℕ} (hev : Even (n + 1 + (s + 1)))
    (y : Fin (n + 1) × {T : Finset (Fin n) // T.card = s}) :
    (-1 : R) ^ (n + 1 + (s + 1) + (y.1 : ℕ)) * (-1) ^ (∑ t ∈ y.2.1, (t : ℕ)) =
      (-1) ^ (∑ x ∈ (lapMap y).1.1, (x : ℕ)) * (-1) ^ (((lapMap y).2 : ℕ) + s) := by
  obtain ⟨b, T, hT⟩ := y
  have hpos : (((lapMap (b, ⟨T, hT⟩)).2 : Fin (s + 1)) : ℕ) =
      (T.filter (fun t => t.castSucc < b)).card := by
    rw [← card_filter_lt_orderEmbOfFin _ (lapMap (b, ⟨T, hT⟩)).1.2, lapMap_emb]
    exact filter_lt_insert_map b T
  have hsplit := Finset.card_filter_add_card_filter_not (s := T) (fun t => t.castSucc < b)
  rw [hpos]
  simp only [lapMap]
  rw [sum_insert_map, ← pow_add, ← pow_add, neg_one_pow_eq_pow_mod_two,
    neg_one_pow_eq_pow_mod_two (n := _ + _)]
  congr 1
  obtain ⟨k, hk⟩ := hev
  omega

/-- Auxiliary for (B5) of `q_pfaffian.md`: deleting the `p`-th element of `S` leaves `S ∖ {S_p}`. -/
theorem exists_orderEmbOfFin_succAbove_iff {n m : ℕ} (S : Finset (Fin n)) (h : S.card = m + 1)
    (p : Fin (m + 1)) (z : Fin n) :
    (∃ q, S.orderEmbOfFin h (p.succAbove q) = z) ↔ (z ∈ S ∧ z ≠ S.orderEmbOfFin h p) := by
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨Finset.orderEmbOfFin_mem _ _ _,
      fun e => Fin.succAbove_ne _ _ ((S.orderEmbOfFin h).injective e)⟩
  · rintro ⟨hz, hne⟩
    have : z ∈ Set.range (S.orderEmbOfFin h) := by rw [Finset.range_orderEmbOfFin]; exact hz
    obtain ⟨r, rfl⟩ := this
    have hr : r ≠ p := fun e => hne (by rw [e])
    obtain ⟨q, rfl⟩ := Fin.exists_succAbove_eq hr
    exact ⟨q, rfl⟩

/-- Auxiliary for (B5) of `q_pfaffian.md`: the rows of the minor of the determinant. -/
theorem lap_rows {n s : ℕ} (y : Fin (n + 1) × {T : Finset (Fin n) // T.card = s}) (i : Fin s) :
    (lapMap y).1.1.orderEmbOfFin (lapMap y).1.2 ((lapMap y).2.succAbove i) =
      y.1.succAbove (y.2.1.orderEmbOfFin y.2.2 i) := by
  revert i
  rw [← funext_iff]
  refine strictMono_eq_of_range
    ((Finset.orderEmbOfFin _ _).strictMono.comp (Fin.strictMono_succAbove _))
    ((Fin.strictMono_succAbove _).comp (Finset.orderEmbOfFin _ _).strictMono) fun z => ?_
  rw [exists_orderEmbOfFin_succAbove_iff, lapMap_emb]
  obtain ⟨b, T, hT⟩ := y
  simp only [lapMap, mem_insert, mem_map, sAbove, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨h1 | ⟨t, ht, rfl⟩, h2⟩
    · exact absurd h1 h2
    · have : t ∈ Set.range (T.orderEmbOfFin hT) := by rw [Finset.range_orderEmbOfFin]; exact ht
      obtain ⟨q, rfl⟩ := this
      exact ⟨q, rfl⟩
  · rintro ⟨q, rfl⟩
    exact ⟨Or.inr ⟨_, Finset.orderEmbOfFin_mem _ _ _, rfl⟩, Fin.succAbove_ne _ _⟩

/-- Auxiliary for (B5) of `q_pfaffian.md`: the minors of `a` on the complements. -/
theorem lap_pf {n s : ℕ} (a : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (y : Fin (n + 1) × {T : Finset (Fin n) // T.card = s}) :
    pfS (n - s) (a.submatrix y.1.succAbove y.1.succAbove) y.2.1ᶜ =
      pfS (n + 1 - (s + 1)) a (lapMap y).1.1ᶜ := by
  obtain ⟨b, T, hT⟩ := y
  have hc : Tᶜ.card = n - s := by rw [card_compl, Fintype.card_fin, hT]
  rw [Nat.add_sub_add_right, pfS_eq _ _ _ (Tᶜ.orderEmbOfFin hc).strictMono
    (fun z => ⟨fun hz => by
      have : z ∈ Set.range (Tᶜ.orderEmbOfFin hc) := by rw [Finset.range_orderEmbOfFin]; exact hz
      exact this, fun ⟨q, hq⟩ => hq ▸ Finset.orderEmbOfFin_mem _ _ _⟩)]
  rw [pfS_eq a _ (fun q => b.succAbove (Tᶜ.orderEmbOfFin hc q))
    ((Fin.strictMono_succAbove _).comp (Finset.orderEmbOfFin _ _).strictMono)]
  · rfl
  · intro z
    simp only [lapMap, mem_compl, mem_insert, mem_map, sAbove, Function.Embedding.coeFn_mk,
      not_or, not_exists, not_and]
    constructor
    · rintro ⟨hzb, hz⟩
      obtain ⟨t, rfl⟩ := Fin.exists_succAbove_eq hzb
      have ht : t ∈ Tᶜ := mem_compl.2 fun ht => hz t ht rfl
      have : t ∈ Set.range (Tᶜ.orderEmbOfFin hc) := by rw [Finset.range_orderEmbOfFin]; exact ht
      obtain ⟨q, rfl⟩ := this
      exact ⟨q, rfl⟩
    · rintro ⟨q, rfl⟩
      refine ⟨Fin.succAbove_ne _ _, fun t ht e => ?_⟩
      have := Fin.succAbove_right_injective e
      have hm := Finset.orderEmbOfFin_mem Tᶜ hc q
      rw [← this, mem_compl] at hm
      exact hm ht

/-- Auxiliary for (B5) of `q_pfaffian.md` (the core identity, with the sign `(−1)^{Σ_{i ∈ S} i}`):
`bpf(a; c) = Σ_{|S| = s} (−1)^{Σ_{i∈S} i}·det(c_k(i))_{i ∈ S, k < s}·pf(a|_{Fin n ∖ S})`. -/
theorem laplace_core : ∀ (s : ℕ) {n : ℕ} (a : Matrix (Fin n) (Fin n) R), IsAlt a →
    ∀ (c : Fin s → Fin n → R),
    bpf a c = ∑ S : {S : Finset (Fin n) // S.card = s},
      (-1) ^ (∑ i ∈ S.1, (i : ℕ)) * (Matrix.of fun i k => c k (S.1.orderEmbOfFin S.2 i)).det *
        pfS (n - s) a S.1ᶜ
  | 0, n, a, ha, c => by
    rw [Finset.sum_eq_single ⟨∅, card_empty⟩]
    · simp only [sum_empty, pow_zero, one_mul, Matrix.det_isEmpty, compl_empty, Nat.sub_zero]
      rw [pfS_eq a univ id strictMono_id (by simp)]
      unfold bpf
      congr 1
      ext p q
      induction p using Fin.addCases with
      | left i =>
        induction q using Fin.addCases with
        | left j => rw [bmat_cc]; rfl
        | right k => exact k.elim0
      | right k => exact k.elim0
    · intro S _ hS
      exfalso; apply hS; exact Subtype.ext (card_eq_zero.1 S.2)
    · intro h; exact absurd (mem_univ _) h
  | s + 1, 0, a, ha, c => by
    rw [bpf_eq_zero_of_lt a ha c (by omega)]
    symm; apply Finset.sum_eq_zero; intro S _
    exfalso; have := card_le_univ S.1; simp [S.2] at this
  | s + 1, n + 1, a, ha, c => by
    by_cases hpar : Odd (n + 1 + (s + 1))
    · rw [bpf_odd a c hpar]; symm; apply sum_eq_zero; intro S _
      have hle : s + 1 ≤ n + 1 := by have := card_le_univ S.1; simpa [S.2] using this
      rw [pfS_odd _ _ (by obtain ⟨k, hk⟩ := hpar; exact ⟨k - s - 1, by omega⟩), mul_zero]
    · have hev : Even (n + 1 + (s + 1)) := Nat.not_odd_iff_even.1 hpar
      rw [bpf_expand_last a ha c]
      have IH := fun b : Fin (n + 1) => laplace_core s (a.submatrix b.succAbove b.succAbove)
        (ha.submatrix _) (fun k i => c k.castSucc (b.succAbove i))
      simp only [IH, Finset.mul_sum]
      simp only [det_expand_last, Finset.mul_sum, Finset.sum_mul]
      rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
      refine Fintype.sum_bijective lapMap lapMap_bijective _ _ fun y => ?_
      rw [lap_pf, lapMap_emb]
      simp only [lap_rows]
      linear_combination c (Fin.last s) y.1 *
        (Matrix.of fun i k => c k.castSucc (y.1.succAbove (y.2.1.orderEmbOfFin y.2.2 i))).det *
        pfS (n + 1 - (s + 1)) a (lapMap y).1.1ᶜ * lap_sign (R := R) hev y

/-- Auxiliary for (B5) of `q_pfaffian.md`: `s(s−1)/2 ≤ Σ_{i ∈ S} i` for an `s`-subset `S` of `Fin n` (so the
natural subtraction in `sgn(S)` is the true one). -/
theorem tri_le_sum {n s : ℕ} (S : Finset (Fin n)) (h : S.card = s) :
    s * (s - 1) / 2 ≤ ∑ i ∈ S, (i : ℕ) := by
  conv_rhs => rw [← map_orderEmbOfFin_univ S h, sum_map]
  rw [← Finset.sum_range_id, ← Fin.sum_univ_eq_sum_range (fun i => i) s]
  refine Finset.sum_le_sum fun q _ => ?_
  simp only [RelEmbedding.coe_toEmbedding]
  calc (q : ℕ) = (S.filter (· < S.orderEmbOfFin h q)).card :=
        (card_filter_lt_orderEmbOfFin S h q).symm
    _ ≤ (Finset.Iio (S.orderEmbOfFin h q)).card := by
        apply card_le_card
        intro y hy
        simp only [mem_filter] at hy
        exact mem_Iio.2 hy.2
    _ = _ := Fin.card_Iio _

/-- **(B5)** of Theorem B in `q_pfaffian.md` (Laplace; (F7) of the paper):
`bpf(a; c) = (−1)^{s(s−1)/2}·Σ_{S ⊆ Fin n, |S| = s} sgn(S)·det(c_k(i))_{i ∈ S, k < s}·
pf(a|_{Fin n ∖ S})`, where the rows of the determinant are the elements of `S` in increasing
order (`S.orderEmbOfFin`), `a|_{Fin n ∖ S}` is `a` restricted to the complement of `S` in
increasing order, and `sgn(S) = (−1)^{Σ_{i ∈ S} i − s(s−1)/2}`.
The file assumes `n = s + 2κ`; the identity holds for all `n` and `s` (if `n + s` is odd both
sides are `0`, and if `s > n` the sum is empty), so it is stated without this hypothesis
(a more general statement). The sum over the `s`-subsets is a sum over the subtype
`{S : Finset (Fin n) // S.card = s}`. -/
theorem bpf_laplace {n s : ℕ} (a : Matrix (Fin n) (Fin n) R) (ha : IsAlt a)
    (c : Fin s → Fin n → R) :
    bpf a c = (-1) ^ (s * (s - 1) / 2) * ∑ S : {S : Finset (Fin n) // S.card = s},
      (-1) ^ ((∑ i ∈ S.1, (i : ℕ)) - s * (s - 1) / 2) *
        (Matrix.of fun i k => c k (S.1.orderEmbOfFin S.2 i)).det *
        pf (n - s) (a.submatrix
          (S.1ᶜ.orderEmbOfFin (by rw [Finset.card_compl, Fintype.card_fin, S.2]))
          (S.1ᶜ.orderEmbOfFin (by rw [Finset.card_compl, Fintype.card_fin, S.2]))) := by
  rw [laplace_core s a ha c, Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  have hc : S.1ᶜ.card = n - s := by rw [Finset.card_compl, Fintype.card_fin, S.2]
  have e : pfS (n - s) a S.1ᶜ = pf (n - s) (a.submatrix (S.1ᶜ.orderEmbOfFin hc)
      (S.1ᶜ.orderEmbOfFin hc)) := by
    unfold pfS; rw [dif_pos hc]
  rw [e]
  conv_lhs => rw [← Nat.add_sub_cancel' (tri_le_sum S.1 S.2), pow_add]
  ring

end Pfaffian

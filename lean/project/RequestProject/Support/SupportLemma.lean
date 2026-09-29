module

public import RequestProject.Support.Evaluation

/-!
# Lemma (support) of `q_support.md`

Formalization of the **Lemma (support)** of `q_support.md`: if the product of a tight pattern of
`λ` on `{1, …, m}` is non-zero at `M ∈ T^m`, then `λ(M) ≼ λ`.

The proof is the **Proof** ("Support") of `q_support.md`, with the intermediate partition `ν'`
unfolded: for `t ≥ 1`, `S_t(λ(M))` is a sum `Σ_{u ∈ U} (a_u − ā_u)` over at most `t` elements
`u ∈ T` (the majority elements of the `t` largest parts); each `a_u − ā_u` is at most the number
of indices outside the pairs where `M` takes the value `u` (step 2: a pair `{u, −u}` adds `1` to
both counts); and the number of indices outside the pairs with a value in `U` is at most
`Σ_c min(t, λ'_c) = S_t(λ)` (step 1: a value occurs at most once in each block `B_c`).
-/

@[expose] public section

open MvPolynomial

namespace Support

open ChainLemma ChainLemma.Partition Tight Fibres

set_option synthInstance.maxHeartbeats 200000

/-- **Proof** of the Lemma (support) of `q_support.md` (auxiliary): a sub-multiset of the image
`f(s)` of a finite set `s` is the image of a subset of `s`. -/
theorem exists_finset_of_le_map {α : Type*} [DecidableEq α] (f : α → ℕ) (s : Finset α) :
    ∀ s' : Multiset ℕ, s' ≤ s.val.map f → ∃ U ⊆ s, s' = U.val.map f := by
  induction s using Finset.induction_on with
  | empty =>
    intro s' h
    simp only [Finset.empty_val, Multiset.map_zero, nonpos_iff_eq_zero] at h
    exact ⟨∅, by simp, by simp [h]⟩
  | insert a s ha ih =>
    intro s' h
    rw [Finset.insert_val_of_notMem ha, Multiset.map_cons] at h
    by_cases hfa : f a ∈ s'
    · obtain ⟨U, hU, hUe⟩ := ih (s'.erase (f a)) (Multiset.erase_le_iff_le_cons.2 h)
      have haU : a ∉ U := fun h' => ha (hU h')
      refine ⟨insert a U, Finset.insert_subset_insert _ hU, ?_⟩
      rw [Finset.insert_val_of_notMem haU, Multiset.map_cons, ← hUe, Multiset.cons_erase hfa]
    · obtain ⟨U, hU, hUe⟩ := ih s' ((Multiset.le_cons_of_notMem hfa).1 h)
      exact ⟨U, hU.trans (Finset.subset_insert _ _), hUe⟩

/-- **Proof** of the Lemma (support) of `q_support.md`, step 1 (auxiliary): the `t` largest parts
of the partition with parts `{f(u) : u ∈ T}` are the values of `f` on at most `t` elements, so
`S_t ≤ Σ_{u ∈ U} f(u)` for some `U ⊆ T` with `|U| ≤ t`. -/
theorem exists_S_ofMultiset_le {α : Type*} [Fintype α] [DecidableEq α] (f : α → ℕ) (t : ℕ) :
    ∃ U : Finset α, U.card ≤ t ∧
      S t (ofMultiset (Finset.univ.val.map f)) ≤ ∑ u ∈ U, f u := by
  set μ := ofMultiset (Finset.univ.val.map f)
  have hle : ((μ.parts.take t : List ℕ) : Multiset ℕ) ≤ Finset.univ.val.map f := by
    refine le_trans ?_ (Multiset.filter_le (0 < ·) _)
    rw [← ofMultiset_parts]
    exact Multiset.coe_le.2 (List.take_sublist _ _).subperm
  obtain ⟨U, -, hU⟩ := exists_finset_of_le_map f _ _ hle
  refine ⟨U, ?_, ?_⟩
  · have hc := congrArg Multiset.card hU
    rw [Multiset.coe_card, Multiset.card_map, Finset.card_val] at hc
    rw [← hc]; exact List.length_take_le _ _
  · rw [S_eq_sum_take, ← Multiset.sum_coe, hU, Finset.sum_eq_multiset_sum]

/-- **Proof** of the Lemma (support) of `q_support.md`, step 2 (auxiliary): if the index set is
covered by the pairwise disjoint pairs of `P` and the set `B`, and every pair carries values
`{u, −u}`, then `#{i : M_i = u} − #{i : M_i = −u}` is at most the number of indices of `B` where
`M` takes the value `u` (each pair adds `1` to both counts of its class). -/
theorem cnt_sub_cnt_neg_le {T : Type*} [Fintype T] [DecidableEq T] {h : ℕ}
    (S : FibreSetting T h) {m : ℕ} (M : Fin m → T) (P : Finset (Finset (Fin m)))
    (B : Finset (Fin m)) (hcover : P.sup id ∪ B = Finset.univ)
    (hdisj : (P : Set (Finset (Fin m))).PairwiseDisjoint id) (hcard : ∀ e ∈ P, e.card = 2)
    (hneg : ∀ e ∈ P, ∀ a ∈ e, ∀ b ∈ e, a ≠ b → M b = S.neg (M a)) (u : T) :
    cnt M u - cnt M (S.neg u) ≤ (B.filter fun i => M i = u).card := by
  have hpair : ∀ v : T, ((P.sup id).filter fun i => M i = v).card =
      ∑ e ∈ P, (e.filter fun i => M i = v).card := by
    intro v
    rw [Finset.sup_eq_biUnion, Finset.filter_biUnion, Finset.card_biUnion]
    · rfl
    · intro e he e' he' hee'
      exact Finset.disjoint_filter_filter (hdisj he he' hee')
  have heq : ((P.sup id).filter fun i => M i = u).card =
      ((P.sup id).filter fun i => M i = S.neg u).card := by
    rw [hpair, hpair]
    refine Finset.sum_congr rfl fun e he => ?_
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 (hcard e he)
    have hb : M b = S.neg (M a) := hneg _ he a (by simp) b (by simp) hab
    rw [Finset.card_filter, Finset.card_filter, Finset.sum_pair hab, Finset.sum_pair hab, hb]
    have h1 : (M a = S.neg u) ↔ (S.neg (M a) = u) := by
      constructor
      · intro h'; rw [h', S.neg_neg]
      · intro h'; rw [← h', S.neg_neg]
    have h2 : (S.neg (M a) = S.neg u) ↔ (M a = u) := by
      constructor
      · intro h'; rw [← S.neg_neg (M a), h', S.neg_neg]
      · intro h'; rw [h']
    simp only [h1, h2]
    omega
  have hu : cnt M u ≤ ((P.sup id).filter fun i => M i = u).card +
      (B.filter fun i => M i = u).card := by
    unfold cnt
    rw [← hcover, Finset.filter_union]
    exact Finset.card_union_le _ _
  have hnu : ((P.sup id).filter fun i => M i = S.neg u).card ≤ cnt M (S.neg u) :=
    Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))
  omega

/-- **Proof** of the Lemma (support) of `q_support.md`, step 1 (auxiliary): if every block
`B_c` (`c = 1, …, λ_1`) carries pairwise distinct values and `|B_c| = λ'_c`, then at most
`Σ_c min(t, λ'_c)` indices of `B_1 ∪ ⋯ ∪ B_{λ_1}` take a value in a set `U` of at most `t`
values. -/
theorem card_filter_mem_le {T : Type*} [DecidableEq T] {m : ℕ} (M : Fin m → T)
    (lam : Partition) (blocks : ℕ → Finset (Fin m))
    (hblock : ∀ c ∈ Finset.Icc 1 (lam.row 1), (blocks c).card = colLen lam c)
    (hinj : ∀ c ∈ Finset.Icc 1 (lam.row 1), Set.InjOn M (blocks c))
    (U : Finset T) (t : ℕ) (hU : U.card ≤ t) :
    (((Finset.Icc 1 (lam.row 1)).sup blocks).filter fun i => M i ∈ U).card ≤
      ∑ c ∈ Finset.Icc 1 (lam.row 1), min t (colLen lam c) := by
  rw [Finset.sup_eq_biUnion, Finset.filter_biUnion]
  refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun c hc => ?_)
  refine le_min ?_ ?_
  · refine le_trans (Finset.card_le_card_of_injOn M ?_ ?_) hU
    · intro i hi; exact (Finset.mem_filter.1 hi).2
    · exact (hinj c hc).mono (fun i hi => (Finset.mem_filter.1 hi).1)
  · rw [← hblock c hc]; exact Finset.card_le_card (Finset.filter_subset _ _)

/-- **Proof** of the Lemma (support) of `q_support.md`, step 1 (auxiliary):
`Σ_{c=1}^{λ_1} min(t, λ'_c) = S_t(λ)`, the number of boxes of the Young diagram of `λ` in its
first `t` rows. -/
theorem sum_min_colLen (lam : Partition) (t : ℕ) :
    ∑ c ∈ Finset.Icc 1 (lam.row 1), min t (colLen lam c) = S t lam := by
  have hmax : ∀ x ∈ lam.parts, x ≤ lam.row 1 := by
    intro x hx
    have hs := lam.sorted
    unfold Partition.row
    cases hp : lam.parts with
    | nil => rw [hp] at hx; simp at hx
    | cons a l =>
      rw [hp] at hx hs
      rw [List.pairwise_cons] at hs
      simp only [Nat.sub_self, List.getD_cons_zero]
      rcases List.mem_cons.1 hx with rfl | hx
      · exact le_rfl
      · exact hs.1 x hx
  rw [S_eq_sum_take, sum_take_formula lam.parts lam.sorted (lam.row 1) ?_ t]
  · exact Finset.sum_congr rfl fun c _ => by rw [Lifts.colLen_eq_countP]
  · intro k hk
    rw [List.countP_eq_zero]
    intro x hx
    have := hmax x hx
    simp only [decide_eq_true_eq]
    omega

variable {F : Type*} [Field F]

/-- **Lemma (support)** of `q_support.md`: in the Setting (`q ≥ 3` odd, `T ⊆ F` with `|T| = q − 1`
and `Π_{u∈T}(y − u) = y^{q−1} − 1`, and `u ↦ −u` on `T`), if the product `G` of a tight pattern
of `λ` on `{1, …, m}` is non-zero at `M ∈ T^m`, then `λ(M) ≼ λ`. -/
theorem resPart_weakDom_of_eval_prodP_ne_zero [DecidableEq F] {q : ℕ} (hq : 3 ≤ q)
    (hodd : Odd q) (T : Finset F) (hT : T.card = q - 1)
    (hprod : ∏ u ∈ T, (Polynomial.X - Polynomial.C u) = Polynomial.X ^ (q - 1) - 1)
    {m : ℕ} {lam : Partition} (Tp : TightPattern lam (Finset.univ : Finset (Fin m)))
    (M : Fin m → T) (hM : eval (fun j => (M j : F)) (prodP F q Tp) ≠ 0) :
    (fibreSetting hq hodd T hT hprod).resPart M ≼ lam := by
  set S := fibreSetting hq hodd T hT hprod
  obtain ⟨hpairs, hblocks⟩ := (eval_prodP_ne_zero_iff hq hodd hprod Tp M).1 hM
  have hneg : ∀ e ∈ Tp.pairs, ∀ a ∈ e, ∀ b ∈ e, a ≠ b → M b = S.neg (M a) := by
    intro e he a ha b hb hab
    exact Subtype.ext (hpairs e he a ha b hb hab)
  have hinj : ∀ c ∈ Finset.Icc 1 (lam.row 1), Set.InjOn M (Tp.blocks c) := by
    intro c hc i hi j hj hij
    exact hblocks c hc hi hj (congrArg Subtype.val hij)
  intro t _
  set B := (Finset.Icc 1 (lam.row 1)).sup Tp.blocks
  obtain ⟨U, hU, hSU⟩ := exists_S_ofMultiset_le (fun u => cnt M u - cnt M (S.neg u)) t
  have h2 : ∑ u ∈ U, (cnt M u - cnt M (S.neg u)) ≤ ∑ u ∈ U, (B.filter fun i => M i = u).card :=
    Finset.sum_le_sum fun u _ =>
      cnt_sub_cnt_neg_le S M Tp.pairs B Tp.cover Tp.pairs_disjoint Tp.card_pair hneg u
  have h3 : ∑ u ∈ U, (B.filter fun i => M i = u).card = (B.filter fun i => M i ∈ U).card := by
    have hfib := Finset.card_eq_sum_card_fiberwise (s := B.filter fun i => M i ∈ U) (f := M)
      (t := U) (fun i hi => (Finset.mem_filter.1 hi).2)
    rw [hfib]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [Finset.filter_filter]
    congr 1
    ext i
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hi, rfl⟩; exact ⟨hi, hu, rfl⟩
    · rintro ⟨hi, -, rfl⟩; exact ⟨hi, rfl⟩
  have h4 := card_filter_mem_le M lam Tp.blocks Tp.card_block hinj U t hU
  rw [sum_min_colLen] at h4
  exact hSU.trans (h2.trans (h3.le.trans h4))

end Support

end

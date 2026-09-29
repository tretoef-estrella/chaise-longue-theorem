module

public import RequestProject.Lifts.Patterns

/-!
# The lifted tight patterns of the cases (α), (β), (γ) of `q_P3_lifts.md`

Given a tight pattern of `μ ∈ Λ_i` on `{2, …, m}` (i.e. on all variables of `C_{m−1}`), we build
the tight patterns of `λ ∈ Λ` on `{1, …, m}` used in Step 1 of the Proof of `q_P3_lifts.md`:
* cases (α) and (β): put the index `1` into the block `B_{c*}` (`exists_pattern_insert`);
* case (γ): for `b ∈ S = B_c`, add the pair `{1, b}` and remove `b` from `B_c`
  (`exists_pattern_pair`).
Throughout, `m = n + 1` and the index `i ∈ {2, …, m}` is `Fin.succ` of an index of `Fin n`.
-/

@[expose] public section

namespace Lifts

open Peel hiding C
open Tight ChainLemma

set_option synthInstance.maxHeartbeats 200000

variable {F : Type*} [Field F] {q : ℕ}

/-- Step 1 of the Proof in `q_P3_lifts.md`: the pairs of a tight pattern on `{2, …, m}`, viewed in
`{1, …, m}`. -/
def liftPairs {n : ℕ} (P : Finset (Finset (Fin n))) : Finset (Finset (Fin (n + 1))) :=
  P.map ⟨liftSet, liftSet_injective⟩

/-- Step 1 of the Proof in `q_P3_lifts.md`: membership in the lifted pairs. -/
lemma mem_liftPairs {n : ℕ} {P : Finset (Finset (Fin n))} {e : Finset (Fin (n + 1))} :
    e ∈ liftPairs P ↔ ∃ e' ∈ P, liftSet e' = e := by
  simp [liftPairs]

/-- Step 1 of the Proof in `q_P3_lifts.md`: lifted pairs are still 2-element sets. -/
lemma card_liftPairs {n : ℕ} {μ : Partition} {I : Finset (Fin n)} (T : TightPattern μ I) :
    ∀ e ∈ liftPairs T.pairs, e.card = 2 := by
  intro e he
  obtain ⟨e', he', rfl⟩ := mem_liftPairs.1 he
  simp [liftSet, T.card_pair e' he']

/-- Step 1 of the Proof in `q_P3_lifts.md`: lifted pairs are still pairwise disjoint. -/
lemma disjoint_liftPairs {n : ℕ} {μ : Partition} {I : Finset (Fin n)} (T : TightPattern μ I) :
    ((liftPairs T.pairs : Finset _) : Set (Finset (Fin (n + 1)))).PairwiseDisjoint id := by
  intro a ha b hb hab
  obtain ⟨a', ha', rfl⟩ := mem_liftPairs.1 ha
  obtain ⟨b', hb', rfl⟩ := mem_liftPairs.1 hb
  have hne : a' ≠ b' := fun h => hab (by rw [h])
  exact (Finset.disjoint_map _).2 (T.pairs_disjoint ha' hb' hne)

/-- Step 1 of the Proof in `q_P3_lifts.md`: the product of the lifted pairs is the image of the
product of the pairs under `C_{m−1} → C_m`. -/
lemma prod_liftPairs {n : ℕ} {μ : Partition} {I : Finset (Fin n)} (T : TightPattern μ I) :
    ∏ e ∈ liftPairs T.pairs, pairD F q e = incl F q n (∏ e ∈ T.pairs, pairD F q e) := by
  rw [liftPairs, Finset.prod_map, map_prod]
  exact Finset.prod_congr rfl (fun e he => (incl_pairD (T.card_pair e he)).symm)

/-- Step 1 of the Proof in `q_P3_lifts.md`: an index `i + 1 ∈ {2, …, m}` is covered by the lifted
pairs or by the lifted blocks `B_1, …, B_N` (`N ≥ μ_1`). -/
lemma succ_mem_cover {n : ℕ} {μ : Partition} (T : TightPattern μ (Finset.univ : Finset (Fin n)))
    {N : ℕ} (hN : μ.row 1 ≤ N) (i : Fin n) :
    (∃ e ∈ T.pairs, i ∈ e) ∨ (∃ c ∈ Finset.Icc 1 N, i ∈ cleanBlocks T c) := by
  have hi : i ∈ T.pairs.sup id ∪ (Finset.Icc 1 N).sup (cleanBlocks T) := by
    rw [cover_cleanBlocks T hN]; exact Finset.mem_univ i
  rcases Finset.mem_union.1 hi with h | h
  · left; obtain ⟨e, he, hie⟩ := Finset.mem_sup.1 h; exact ⟨e, he, hie⟩
  · right; exact Finset.mem_sup.1 h

/-- **Cases (α) and (β)** of the Proof in `q_P3_lifts.md`: let `T` be a tight pattern of `μ` on
`{2, …, m}` with product `G`, and let `λ` have the columns of `μ` except that column `c* ≥ 1` is
one longer.  Putting the index `1` into the block `B = B_{c*}` (`B = ∅` if `c* > μ_1`) gives a
tight pattern of `λ` on `{1, …, m}` (the number of pairs is unchanged), whose product is
`Δ(B ∪ {1}) · (other factors) = Π_{c ∈ B} (y_c − y_1) · G` (part (iii) of `q_P3_identities.md`,
first identity). -/
theorem exists_pattern_insert {n : ℕ} {μ lam : Partition}
    (T : TightPattern μ (Finset.univ : Finset (Fin n))) {cs : ℕ} (hcs : 1 ≤ cs)
    (hcol : ∀ c, 1 ≤ c → colLen lam c = colLen μ c + if c = cs then 1 else 0) :
    ∃ T' : TightPattern lam (Finset.univ : Finset (Fin (n + 1))),
      T'.prod F q = (∏ x ∈ cleanBlocks T cs, (y F q x.succ - y F q 0)) *
        incl F q n (T.prod F q) := by
  classical
  set N := lam.row 1 + μ.row 1 + cs with hNdef
  set P := liftPairs T.pairs with hPdef
  set B : ℕ → Finset (Fin (n + 1)) := fun c =>
    if c = cs then insert 0 (liftSet (cleanBlocks T c)) else liftSet (cleanBlocks T c) with hBdef
  have hB : ∀ c, 1 ≤ c → (B c).card = colLen lam c := by
    intro c hc
    rw [hcol c hc]
    by_cases h : c = cs
    · simp only [hBdef, if_pos h]
      rw [Finset.card_insert_of_notMem (zero_notMem_liftSet _), liftSet, Finset.card_map,
        card_cleanBlocks T hc]
    · simp only [hBdef, if_neg h, liftSet, Finset.card_map, card_cleanBlocks T hc, add_zero]
  have hBd : ∀ c, 1 ≤ c → ∀ c', 1 ≤ c' → c ≠ c' → Disjoint (B c) (B c') := by
    intro c _ c' _ hne
    have hd : Disjoint (liftSet (cleanBlocks T c)) (liftSet (cleanBlocks T c')) :=
      (Finset.disjoint_map _).2 (disjoint_cleanBlocks T hne)
    by_cases h : c = cs
    · have h' : c' ≠ cs := fun h' => hne (h.trans h'.symm)
      simp only [hBdef, if_pos h, if_neg h']
      exact Finset.disjoint_insert_left.2 ⟨zero_notMem_liftSet _, hd⟩
    · by_cases h' : c' = cs
      · simp only [hBdef, if_neg h, if_pos h']
        exact Finset.disjoint_insert_right.2 ⟨zero_notMem_liftSet _, hd⟩
      · simp only [hBdef, if_neg h, if_neg h']; exact hd
  have hPB : ∀ e ∈ P, ∀ c, 1 ≤ c → Disjoint e (B c) := by
    intro e he c _
    obtain ⟨e', he', rfl⟩ := mem_liftPairs.1 he
    have hd : Disjoint (liftSet e') (liftSet (cleanBlocks T c)) :=
      (Finset.disjoint_map _).2 (disjoint_pairs_cleanBlocks T he' c)
    by_cases h : c = cs
    · simp only [hBdef, if_pos h]
      exact Finset.disjoint_insert_right.2 ⟨zero_notMem_liftSet _, hd⟩
    · simp only [hBdef, if_neg h]; exact hd
  have hcov : P.sup id ∪ (Finset.Icc 1 N).sup B = Finset.univ := by
    refine Finset.eq_univ_of_forall (fun x => ?_)
    refine Fin.cases ?_ (fun i => ?_) x
    · refine Finset.mem_union_right _ (Finset.mem_sup.2 ⟨cs, Finset.mem_Icc.2 ⟨hcs, by omega⟩, ?_⟩)
      simp [hBdef]
    · rcases succ_mem_cover T (N := N) (by omega) i with ⟨e, he, hie⟩ | ⟨c, hc, hic⟩
      · refine Finset.mem_union_left _ (Finset.mem_sup.2 ⟨liftSet e, ?_, ?_⟩)
        · exact mem_liftPairs.2 ⟨e, he, rfl⟩
        · exact succ_mem_liftSet.2 hie
      · refine Finset.mem_union_right _ (Finset.mem_sup.2 ⟨c, hc, ?_⟩)
        by_cases h : c = cs
        · simp only [hBdef, if_pos h]; exact Finset.mem_insert_of_mem (succ_mem_liftSet.2 hic)
        · simp only [hBdef, if_neg h]; exact succ_mem_liftSet.2 hic
  refine ⟨mkPattern lam _ P B N (by omega) (card_liftPairs T) (disjoint_liftPairs T) hB hBd hPB
    hcov, ?_⟩
  have hcsN : cs ∈ Finset.Icc 1 N := Finset.mem_Icc.2 ⟨hcs, by omega⟩
  rw [prod_mkPattern, prod_cleanBlocks T (N := N) (by omega), hPdef, prod_liftPairs, map_mul,
    ← Finset.mul_prod_erase _ _ hcsN, ← Finset.mul_prod_erase _ _ hcsN, map_mul, map_prod]
  have e1 : B cs = insert 0 (liftSet (cleanBlocks T cs)) := by simp [hBdef]
  have e2 : ∏ c ∈ (Finset.Icc 1 N).erase cs, Delta F q (B c) =
      ∏ c ∈ (Finset.Icc 1 N).erase cs, incl F q n (Delta F q (cleanBlocks T c)) := by
    refine Finset.prod_congr rfl (fun c hc => ?_)
    rw [incl_Delta]; simp [hBdef, Finset.ne_of_mem_erase hc]
  have e3 : Delta F q (insert 0 (liftSet (cleanBlocks T cs))) =
      (∏ x ∈ cleanBlocks T cs, (y F q x.succ - y F q 0)) *
        incl F q n (Delta F q (cleanBlocks T cs)) := by
    rw [Delta_insert_of_lt _ _ (fun b hb => ?_), incl_Delta]
    · congr 1
      simp [liftSet, Finset.prod_map]
    · obtain ⟨b', _, rfl⟩ := Finset.mem_map.1 hb
      exact Fin.succ_pos b'
  rw [e1, e2, e3, map_prod]
  ring

/-- **Case (γ)** of the Proof in `q_P3_lifts.md`: let `T` be a tight pattern of `μ` on
`{2, …, m}`, let `λ` have the columns of `μ` except that column `c ≥ 1` is one shorter, let
`S = B_c` and write `G = Δ(S) · G'` with `G' = Π_{{a<b} ∈ P} D(y_a, y_b) · Π_{c' ≠ c} Δ(B_{c'})`
(for any `N ≥ λ_1, μ_1, c`, the product over `c' ∈ {1, …, N} ∖ {c}`).  For `b ∈ S`, the pairs
`P ∪ {{1, b}}` with the blocks `B_{c'}` (`c' ≠ c`) and `S ∖ {b}` form a tight pattern of `λ` on
`{1, …, m}` (the number of pairs has grown by one), with product
`Δ(S ∖ {b}) · D(y_1, y_b) · G'`. -/
theorem exists_pattern_pair {n : ℕ} {μ lam : Partition}
    (T : TightPattern μ (Finset.univ : Finset (Fin n))) {c0 : ℕ} (hc0 : 1 ≤ c0)
    (hcol : ∀ c, 1 ≤ c → colLen lam c + (if c = c0 then 1 else 0) = colLen μ c)
    {N : ℕ} (hN1 : lam.row 1 ≤ N) (hN2 : μ.row 1 ≤ N) (hN3 : c0 ≤ N)
    {b : Fin n} (hb : b ∈ cleanBlocks T c0) :
    ∃ T' : TightPattern lam (Finset.univ : Finset (Fin (n + 1))),
      T'.prod F q = D F q 0 b.succ * incl F q n (Delta F q ((cleanBlocks T c0).erase b) *
        ((∏ e ∈ T.pairs, pairD F q e) *
          ∏ c ∈ (Finset.Icc 1 N).erase c0, Delta F q (cleanBlocks T c))) := by
  classical
  set p0 : Finset (Fin (n + 1)) := {0, b.succ} with hp0
  have hp0L : ∀ e ∈ liftPairs T.pairs, Disjoint p0 e := by
    intro e he
    obtain ⟨e', he', rfl⟩ := mem_liftPairs.1 he
    rw [Finset.disjoint_left]
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact zero_notMem_liftSet _
    · rw [Finset.mem_singleton.1 hx, succ_mem_liftSet]
      exact Finset.disjoint_right.1 (disjoint_pairs_cleanBlocks T he' c0) hb
  have hp0notin : p0 ∉ liftPairs T.pairs := by
    intro h
    have := Finset.disjoint_left.1 (hp0L p0 h) (Finset.mem_insert_self 0 _)
    exact this (Finset.mem_insert_self 0 _)
  set P := insert p0 (liftPairs T.pairs) with hPdef
  set B : ℕ → Finset (Fin (n + 1)) := fun c =>
    if c = c0 then liftSet ((cleanBlocks T c).erase b) else liftSet (cleanBlocks T c) with hBdef
  have hP2 : ∀ e ∈ P, e.card = 2 := by
    intro e he
    rcases Finset.mem_insert.1 he with rfl | he
    · exact Finset.card_pair (Fin.succ_ne_zero b).symm
    · exact card_liftPairs T e he
  have hPd : (P : Set (Finset (Fin (n + 1)))).PairwiseDisjoint id := by
    rw [hPdef, Finset.coe_insert]
    exact (disjoint_liftPairs T).insert (fun e he _ => hp0L e he)
  have hsub : ∀ c, B c ⊆ liftSet (cleanBlocks T c) := by
    intro c
    by_cases h : c = c0
    · simp only [hBdef, if_pos h]
      exact Finset.map_subset_map.2 (Finset.erase_subset _ _)
    · simp only [hBdef, if_neg h]; exact Finset.Subset.refl _
  have hB : ∀ c, 1 ≤ c → (B c).card = colLen lam c := by
    intro c hc
    have := hcol c hc
    by_cases h : c = c0
    · subst h
      simp only [hBdef, if_true, liftSet, Finset.card_map,
        Finset.card_erase_of_mem hb, card_cleanBlocks T hc]
      simp at this; omega
    · simp only [hBdef, if_neg h, liftSet, Finset.card_map, card_cleanBlocks T hc]
      simp [h] at this; omega
  have hBd : ∀ c, 1 ≤ c → ∀ c', 1 ≤ c' → c ≠ c' → Disjoint (B c) (B c') := by
    intro c _ c' _ hne
    exact ((Finset.disjoint_map _).2 (disjoint_cleanBlocks T hne)).mono (hsub c) (hsub c')
  have hPB : ∀ e ∈ P, ∀ c, 1 ≤ c → Disjoint e (B c) := by
    intro e he c _
    rcases Finset.mem_insert.1 he with rfl | he
    · rw [Finset.disjoint_left]
      intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact fun h => zero_notMem_liftSet _ (hsub c h)
      · rw [Finset.mem_singleton.1 hx]
        by_cases h : c = c0
        · simp [hBdef, h, succ_mem_liftSet]
        · simp only [hBdef, if_neg h, succ_mem_liftSet]
          exact Finset.disjoint_left.1 (disjoint_cleanBlocks T (Ne.symm h)) hb
    · obtain ⟨e', he', rfl⟩ := mem_liftPairs.1 he
      exact ((Finset.disjoint_map _).2 (disjoint_pairs_cleanBlocks T he' c)).mono_right (hsub c)
  have hcov : P.sup id ∪ (Finset.Icc 1 N).sup B = Finset.univ := by
    refine Finset.eq_univ_of_forall (fun x => ?_)
    have hp0mem : ∀ x ∈ p0, x ∈ P.sup id ∪ (Finset.Icc 1 N).sup B := fun x hx =>
      Finset.mem_union_left _ (Finset.mem_sup.2 ⟨p0, Finset.mem_insert_self _ _, hx⟩)
    refine Fin.cases (hp0mem 0 (Finset.mem_insert_self _ _)) (fun i => ?_) x
    by_cases hib : i = b
    · subst hib; exact hp0mem _ (by simp [hp0])
    rcases succ_mem_cover T hN2 i with ⟨e, he, hie⟩ | ⟨c, hc, hic⟩
    · refine Finset.mem_union_left _ (Finset.mem_sup.2 ⟨liftSet e, ?_, ?_⟩)
      · exact Finset.mem_insert_of_mem (mem_liftPairs.2 ⟨e, he, rfl⟩)
      · exact succ_mem_liftSet.2 hie
    · refine Finset.mem_union_right _ (Finset.mem_sup.2 ⟨c, hc, ?_⟩)
      by_cases h : c = c0
      · simp only [hBdef, if_pos h, succ_mem_liftSet]
        subst h; exact Finset.mem_erase.2 ⟨hib, hic⟩
      · simp only [hBdef, if_neg h]; exact succ_mem_liftSet.2 hic
  refine ⟨mkPattern lam _ P B N hN1 hP2 hPd hB hBd hPB hcov, ?_⟩
  have hc0N : c0 ∈ Finset.Icc 1 N := Finset.mem_Icc.2 ⟨hc0, hN3⟩
  rw [prod_mkPattern, hPdef, Finset.prod_insert hp0notin, prod_liftPairs,
    ← Finset.mul_prod_erase _ _ hc0N, hp0, pairD_of_lt (Fin.succ_pos b)]
  have e1 : Delta F q (B c0) = incl F q n (Delta F q ((cleanBlocks T c0).erase b)) := by
    rw [incl_Delta]; simp [hBdef]
  have e2 : ∏ c ∈ (Finset.Icc 1 N).erase c0, Delta F q (B c) =
      incl F q n (∏ c ∈ (Finset.Icc 1 N).erase c0, Delta F q (cleanBlocks T c)) := by
    rw [map_prod]
    refine Finset.prod_congr rfl (fun c hc => ?_)
    rw [incl_Delta]; simp [hBdef, Finset.ne_of_mem_erase hc]
  rw [e1, e2, map_mul, map_mul]
  ring

end Lifts

end

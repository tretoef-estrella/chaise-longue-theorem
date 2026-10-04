module

public import RequestProject.OddLifts.Aux

/-!
# Marked patterns for the lifts of `q_oddbox_lifts_1.md`

* **(L2)** of `q_oddbox_lifts_1.md`: the clean blocks of a marked pattern (`cleanMBlocks`,
  `prod_cleanMBlocks`);
* a way to build a marked pattern from pairs, blocks and a marked block satisfying the covering
  conditions (`mkMPattern`);
* the lifted marked patterns used in the proofs of (T3) (`exists_mpattern_insert`) and (T4)
  (`exists_mpattern_pair`).

Throughout, `m = n + 1` and an index of `C_n` is lifted to `C_{n+1}` by `Fin.succ`
(`Lifts.liftSet`, `Lifts.liftPairs`).
-/

@[expose] public section

namespace OddLifts

open Peel hiding C
open Tight ChainLemma OddPatterns Lifts

set_option synthInstance.maxHeartbeats 200000

/-! ### Lifted pairs (for an arbitrary set of pairs) -/

/-- Auxiliary for (T3)–(T5) of `q_oddbox_lifts_1.md`: lifted pairs are still 2-element sets. -/
lemma card_liftPairs' {n : ℕ} {P : Finset (Finset (Fin n))} (hP2 : ∀ e ∈ P, e.card = 2) :
    ∀ e ∈ liftPairs P, e.card = 2 := by
  intro e he
  obtain ⟨e', he', rfl⟩ := mem_liftPairs.1 he
  simp [liftSet, hP2 e' he']

/-- Auxiliary for (T3)–(T5) of `q_oddbox_lifts_1.md`: lifted pairs are still pairwise disjoint. -/
lemma disjoint_liftPairs' {n : ℕ} {P : Finset (Finset (Fin n))}
    (hPd : (P : Set (Finset (Fin n))).PairwiseDisjoint id) :
    ((liftPairs P : Finset _) : Set (Finset (Fin (n + 1)))).PairwiseDisjoint id := by
  intro a ha b hb hab
  obtain ⟨a', ha', rfl⟩ := mem_liftPairs.1 ha
  obtain ⟨b', hb', rfl⟩ := mem_liftPairs.1 hb
  have hne : a' ≠ b' := fun h => hab (by rw [h])
  exact (Finset.disjoint_map _).2 (hPd ha' hb' hne)

/-- Auxiliary for (T3)–(T5) of `q_oddbox_lifts_1.md`: the product of the lifted pairs is the image
of the product of the pairs under `incl : C_n → C_{n+1}`. -/
lemma prod_liftPairs' {F : Type*} [Field F] {q n : ℕ} {P : Finset (Finset (Fin n))}
    (hP2 : ∀ e ∈ P, e.card = 2) :
    ∏ e ∈ liftPairs P, pairD F q e = incl F q n (∏ e ∈ P, pairD F q e) := by
  rw [liftPairs, Finset.prod_map, map_prod]
  exact Finset.prod_congr rfl (fun e he => (incl_pairD (hP2 e he)).symm)

/-! ### (L2): the clean blocks of a marked pattern -/

/-- **(L2)** of `q_oddbox_lifts_1.md` (clean blocks of a marked pattern): the blocks `B_c` of a
marked pattern of `μ`, with the convention `B_c = ∅` for `c ∉ [2, μ_1]`. -/
def cleanMBlocks {k : ℕ} {μ : Partition} {I : Finset (Fin k)} (T : MarkedPattern μ I) (c : ℕ) :
    Finset (Fin k) :=
  if c ∈ Finset.Icc 2 (μ.row 1) then T.blocks c else ∅

/-- **(L2)** of `q_oddbox_lifts_1.md`: `|B_c| = μ'_c` for every `c ≥ 2`. -/
lemma card_cleanMBlocks {k : ℕ} {μ : Partition} {I : Finset (Fin k)} (T : MarkedPattern μ I)
    {c : ℕ} (hc : 2 ≤ c) : (cleanMBlocks T c).card = colLen μ c := by
  unfold cleanMBlocks
  split_ifs with h
  · exact T.card_block c h
  · simp only [Finset.mem_Icc, not_and, not_le] at h
    rw [colLen_eq_zero μ (h hc)]; rfl

/-- **(L2)** of `q_oddbox_lifts_1.md`: the clean blocks are pairwise disjoint. -/
lemma disjoint_cleanMBlocks {k : ℕ} {μ : Partition} {I : Finset (Fin k)} (T : MarkedPattern μ I)
    {c c' : ℕ} (hne : c ≠ c') : Disjoint (cleanMBlocks T c) (cleanMBlocks T c') := by
  unfold cleanMBlocks
  split_ifs with h h'
  · exact T.blocks_disjoint h h' hne
  all_goals simp

/-- **(L2)** of `q_oddbox_lifts_1.md`: pairs and clean blocks are disjoint. -/
lemma disjoint_pairs_cleanMBlocks {k : ℕ} {μ : Partition} {I : Finset (Fin k)}
    (T : MarkedPattern μ I) {e : Finset (Fin k)} (he : e ∈ T.pairs) (c : ℕ) :
    Disjoint e (cleanMBlocks T c) := by
  unfold cleanMBlocks
  split_ifs with h
  · exact T.pairs_blocks_disjoint e he c h
  · simp

/-- **(L2)** of `q_oddbox_lifts_1.md`: clean blocks and the marked block are disjoint. -/
lemma disjoint_cleanMBlocks_marked {k : ℕ} {μ : Partition} {I : Finset (Fin k)}
    (T : MarkedPattern μ I) (c : ℕ) : Disjoint (cleanMBlocks T c) T.marked := by
  unfold cleanMBlocks
  split_ifs with h
  · exact T.blocks_marked_disjoint c h
  · simp

/-- Auxiliary for (L2) of `q_oddbox_lifts_1.md`: for blocks with `|B_c| = λ'_c` for all `c ≥ 2`,
the union over `c ∈ [2, N]` (`N ≥ λ_1`) is the union over `c ∈ [2, λ_1]`. -/
lemma sup_mblocks_eq {k : ℕ} {lam : Partition} {B : ℕ → Finset (Fin k)}
    (hB : ∀ c, 2 ≤ c → (B c).card = colLen lam c) {N : ℕ} (hN : lam.row 1 ≤ N) :
    (Finset.Icc 2 N).sup B = (Finset.Icc 2 (lam.row 1)).sup B := by
  refine le_antisymm (Finset.sup_le (fun c hc => ?_))
    (Finset.sup_mono (Finset.Icc_subset_Icc le_rfl hN))
  rw [Finset.mem_Icc] at hc
  by_cases h : c ≤ lam.row 1
  · exact Finset.le_sup (f := B) (Finset.mem_Icc.2 ⟨hc.1, h⟩)
  · have : B c = ∅ := by
      rw [← Finset.card_eq_zero, hB c hc.1, colLen_eq_zero lam (by omega)]
    rw [this]; exact bot_le

/-- **(L2)** of `q_oddbox_lifts_1.md`: the pairs, the clean blocks `B_2, …, B_N` (`N ≥ μ_1`) and
the marked block cover `I`. -/
lemma cover_cleanMBlocks {k : ℕ} {μ : Partition} {I : Finset (Fin k)} (T : MarkedPattern μ I)
    {N : ℕ} (hN : μ.row 1 ≤ N) :
    T.pairs.sup id ∪ (Finset.Icc 2 N).sup (cleanMBlocks T) ∪ T.marked = I := by
  rw [sup_mblocks_eq (fun c hc => card_cleanMBlocks T hc) hN]
  conv_rhs => rw [← T.cover]
  congr 2
  exact Finset.sup_congr rfl (fun c hc => by simp [cleanMBlocks, hc])

/-- **(L2)** of `q_oddbox_lifts_1.md`: with the clean blocks (`B_c = ∅` for `c ∉ [2, μ_1]`), the
product of a marked pattern is unchanged:
`G = Π_{{a<b} ∈ P} D(y_a, y_b) · Pf_{E_ℓ}(B_0) · Π_{c=2}^{N} Δ(B_c)` for every `N ≥ μ_1`. -/
theorem prod_cleanMBlocks {F : Type*} [Field F] {h k : ℕ} {μ : Partition} {I : Finset (Fin k)}
    (T : MarkedPattern μ I) {N : ℕ} (hN : μ.row 1 ≤ N) :
    T.prod F h = (∏ e ∈ T.pairs, pairD F (2 * h + 2) e) * markedPf F h μ.len T.marked *
      ∏ c ∈ Finset.Icc 2 N, Delta F (2 * h + 2) (cleanMBlocks T c) := by
  unfold MarkedPattern.prod
  congr 1
  rw [← Finset.prod_subset (Finset.Icc_subset_Icc le_rfl hN) (fun c hc hnc => ?_)]
  · exact Finset.prod_congr rfl (fun c hc => by simp [cleanMBlocks, hc])
  · simp only [Finset.mem_Icc, not_and, not_le] at hc hnc
    have : cleanMBlocks T c = ∅ := by simp [cleanMBlocks]; omega
    rw [this, Delta_empty]

/-! ### Building marked patterns -/

/-- Auxiliary for (T3)–(T5) of `q_oddbox_lifts_1.md`: a marked pattern of `λ` on `I` built from
pairs `P`, blocks `B_c` (`c ≥ 2`, with `|B_c| = λ'_c` for all `c ≥ 2`) and a marked block `M` with
`|M| = ℓ(λ) + 1 + 2t`, pairwise disjoint and covering `I`. -/
def mkMPattern {k : ℕ} (lam : Partition) (I : Finset (Fin k)) (P : Finset (Finset (Fin k)))
    (B : ℕ → Finset (Fin k)) (M : Finset (Fin k)) (N : ℕ) (hN : lam.row 1 ≤ N)
    (hP2 : ∀ e ∈ P, e.card = 2)
    (hPd : (P : Set (Finset (Fin k))).PairwiseDisjoint id)
    (hB : ∀ c, 2 ≤ c → (B c).card = colLen lam c)
    (hBd : ∀ c, 2 ≤ c → ∀ c', 2 ≤ c' → c ≠ c' → Disjoint (B c) (B c'))
    (hPB : ∀ e ∈ P, ∀ c, 2 ≤ c → Disjoint e (B c))
    (hPM : ∀ e ∈ P, Disjoint e M) (hBM : ∀ c, 2 ≤ c → Disjoint (B c) M)
    (hMc : ∃ t, M.card = lam.len + 1 + 2 * t)
    (hcov : P.sup id ∪ (Finset.Icc 2 N).sup B ∪ M = I) : MarkedPattern lam I where
  pairs := P
  blocks := B
  marked := M
  card_pair := hP2
  pairs_disjoint := hPd
  card_block := fun c hc => hB c (Finset.mem_Icc.1 hc).1
  blocks_disjoint := fun c hc c' hc' hne =>
    hBd c (Finset.mem_Icc.1 hc).1 c' (Finset.mem_Icc.1 hc').1 hne
  pairs_blocks_disjoint := fun e he c hc => hPB e he c (Finset.mem_Icc.1 hc).1
  pairs_marked_disjoint := hPM
  blocks_marked_disjoint := fun c hc => hBM c (Finset.mem_Icc.1 hc).1
  marked_card := hMc
  cover := by rw [← hcov, sup_mblocks_eq hB hN]

/-- Auxiliary for (T3)–(T5) of `q_oddbox_lifts_1.md`: the product of a marked pattern built with
`mkMPattern` is `Π_{e ∈ P} D_e · Pf_{E_ℓ}(M) · Π_{c=2}^{N} Δ(B_c)`. -/
theorem prod_mkMPattern {F : Type*} [Field F] {h k : ℕ} (lam : Partition) (I : Finset (Fin k))
    (P : Finset (Finset (Fin k))) (B : ℕ → Finset (Fin k)) (M : Finset (Fin k)) (N : ℕ)
    (hN : lam.row 1 ≤ N) (hP2 : ∀ e ∈ P, e.card = 2)
    (hPd : (P : Set (Finset (Fin k))).PairwiseDisjoint id)
    (hB : ∀ c, 2 ≤ c → (B c).card = colLen lam c)
    (hBd : ∀ c, 2 ≤ c → ∀ c', 2 ≤ c' → c ≠ c' → Disjoint (B c) (B c'))
    (hPB : ∀ e ∈ P, ∀ c, 2 ≤ c → Disjoint e (B c))
    (hPM : ∀ e ∈ P, Disjoint e M) (hBM : ∀ c, 2 ≤ c → Disjoint (B c) M)
    (hMc : ∃ t, M.card = lam.len + 1 + 2 * t)
    (hcov : P.sup id ∪ (Finset.Icc 2 N).sup B ∪ M = I) :
    (mkMPattern lam I P B M N hN hP2 hPd hB hBd hPB hPM hBM hMc hcov).prod F h =
      (∏ e ∈ P, pairD F (2 * h + 2) e) * markedPf F h lam.len M *
        ∏ c ∈ Finset.Icc 2 N, Delta F (2 * h + 2) (B c) := by
  unfold MarkedPattern.prod
  simp only [mkMPattern]
  congr 1
  refine Finset.prod_subset (Finset.Icc_subset_Icc le_rfl hN) (fun c hc hnc => ?_)
  simp only [Finset.mem_Icc, not_and, not_le] at hc hnc
  have : B c = ∅ := by
    rw [← Finset.card_eq_zero, hB c hc.1, colLen_eq_zero lam (hnc hc.1)]
  rw [this, Delta_empty]

/-- Auxiliary for (T3) and (T4) of `q_oddbox_lifts_1.md`: if `λ'_1 = μ'_1` then `ℓ(λ) = ℓ(μ)`. -/
lemma len_eq_of_colLen_one {lam μ : Partition} (h1 : colLen lam 1 = colLen μ 1) :
    lam.len = μ.len := by
  rw [← OddPatterns.colLen_one, ← OddPatterns.colLen_one, h1]

/-- Auxiliary for (T3) and (T4) of `q_oddbox_lifts_1.md`: an index `i + 1` of `C_{n+1}` is
covered by a lifted pair, a lifted clean block `B_c` (`c ∈ [2, N]`, `N ≥ μ_1`) or the lifted
marked block. -/
lemma succ_mem_mcover {n : ℕ} {μ : Partition}
    (T : MarkedPattern μ (Finset.univ : Finset (Fin n))) {N : ℕ} (hN : μ.row 1 ≤ N) (i : Fin n) :
    (∃ e ∈ T.pairs, i ∈ e) ∨ (∃ c ∈ Finset.Icc 2 N, i ∈ cleanMBlocks T c) ∨ i ∈ T.marked := by
  have hi : i ∈ T.pairs.sup id ∪ (Finset.Icc 2 N).sup (cleanMBlocks T) ∪ T.marked := by
    rw [cover_cleanMBlocks T hN]; exact Finset.mem_univ i
  rcases Finset.mem_union.1 hi with h | h
  · rcases Finset.mem_union.1 h with h | h
    · left; obtain ⟨e, he, hie⟩ := Finset.mem_sup.1 h; exact ⟨e, he, hie⟩
    · right; left; exact Finset.mem_sup.1 h
  · right; right; exact h

variable {F : Type*} [Field F] {h : ℕ}

/-- The lifted marked pattern of the proof of **(T3)** of `q_oddbox_lifts_1.md`: let `T` be a
marked pattern of `μ` on all the indices of `C_n`, and let `λ` have the columns of `μ` except that
column `c* ≥ 2` is one longer.  Putting the index `0` into the block `B_{c*}` (`B_{c*} = ∅` if
`c* > μ_1`), lifting the pairs, the other blocks and the marked block gives a marked pattern `T'`
of `λ` on `Fin (n+1)` with `T'.prod = Π_{x ∈ B_{c*}} (y_{x+1} − y_0) · incl(T.prod)`. -/
theorem exists_mpattern_insert {n : ℕ} {μ lam : Partition}
    (T : MarkedPattern μ (Finset.univ : Finset (Fin n))) {cs : ℕ} (hcs : 2 ≤ cs)
    (hcol : ∀ c, 1 ≤ c → colLen lam c = colLen μ c + if c = cs then 1 else 0) :
    ∃ T' : MarkedPattern lam (Finset.univ : Finset (Fin (n + 1))),
      T'.prod F h = (∏ x ∈ cleanMBlocks T cs, (y F (2 * h + 2) x.succ - y F (2 * h + 2) 0)) *
        incl F (2 * h + 2) n (T.prod F h) := by
  classical
  have hlen : lam.len = μ.len := len_eq_of_colLen_one (by
    have := hcol 1 le_rfl; rw [if_neg (by omega)] at this; omega)
  set N := lam.row 1 + μ.row 1 + cs with hNdef
  set P := liftPairs T.pairs with hPdef
  set M := liftSet T.marked with hMdef
  set B : ℕ → Finset (Fin (n + 1)) := fun c =>
    if c = cs then insert 0 (liftSet (cleanMBlocks T c)) else liftSet (cleanMBlocks T c)
    with hBdef
  have hB : ∀ c, 2 ≤ c → (B c).card = colLen lam c := by
    intro c hc
    rw [hcol c (by omega)]
    by_cases h : c = cs
    · simp only [hBdef, if_pos h]
      rw [Finset.card_insert_of_notMem (zero_notMem_liftSet _), liftSet, Finset.card_map,
        card_cleanMBlocks T hc]
    · simp only [hBdef, if_neg h, liftSet, Finset.card_map, card_cleanMBlocks T hc, add_zero]
  have hBd : ∀ c, 2 ≤ c → ∀ c', 2 ≤ c' → c ≠ c' → Disjoint (B c) (B c') := by
    intro c _ c' _ hne
    have hd : Disjoint (liftSet (cleanMBlocks T c)) (liftSet (cleanMBlocks T c')) :=
      (Finset.disjoint_map _).2 (disjoint_cleanMBlocks T hne)
    by_cases h : c = cs
    · have h' : c' ≠ cs := fun h' => hne (h.trans h'.symm)
      simp only [hBdef, if_pos h, if_neg h']
      exact Finset.disjoint_insert_left.2 ⟨zero_notMem_liftSet _, hd⟩
    · by_cases h' : c' = cs
      · simp only [hBdef, if_neg h, if_pos h']
        exact Finset.disjoint_insert_right.2 ⟨zero_notMem_liftSet _, hd⟩
      · simp only [hBdef, if_neg h, if_neg h']; exact hd
  have hPB : ∀ e ∈ P, ∀ c, 2 ≤ c → Disjoint e (B c) := by
    intro e he c _
    obtain ⟨e', he', rfl⟩ := mem_liftPairs.1 he
    have hd : Disjoint (liftSet e') (liftSet (cleanMBlocks T c)) :=
      (Finset.disjoint_map _).2 (disjoint_pairs_cleanMBlocks T he' c)
    by_cases h : c = cs
    · simp only [hBdef, if_pos h]
      exact Finset.disjoint_insert_right.2 ⟨zero_notMem_liftSet _, hd⟩
    · simp only [hBdef, if_neg h]; exact hd
  have hPM : ∀ e ∈ P, Disjoint e M := by
    intro e he
    obtain ⟨e', he', rfl⟩ := mem_liftPairs.1 he
    exact (Finset.disjoint_map _).2 (T.pairs_marked_disjoint e' he')
  have hBM : ∀ c, 2 ≤ c → Disjoint (B c) M := by
    intro c _
    have hd : Disjoint (liftSet (cleanMBlocks T c)) M :=
      (Finset.disjoint_map _).2 (disjoint_cleanMBlocks_marked T c)
    by_cases h : c = cs
    · simp only [hBdef, if_pos h]
      exact Finset.disjoint_insert_left.2 ⟨zero_notMem_liftSet _, hd⟩
    · simp only [hBdef, if_neg h]; exact hd
  have hMc : ∃ t, M.card = lam.len + 1 + 2 * t := by
    obtain ⟨t, ht⟩ := T.marked_card
    exact ⟨t, by rw [hMdef, liftSet, Finset.card_map, ht, hlen]⟩
  have hcov : P.sup id ∪ (Finset.Icc 2 N).sup B ∪ M = Finset.univ := by
    refine Finset.eq_univ_of_forall (fun x => ?_)
    refine Fin.cases ?_ (fun i => ?_) x
    · refine Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_sup.2 ⟨cs, Finset.mem_Icc.2 ⟨hcs, by omega⟩, ?_⟩))
      simp [hBdef]
    · rcases succ_mem_mcover T (N := N) (by omega) i with ⟨e, he, hie⟩ | ⟨c, hc, hic⟩ | hm
      · refine Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_sup.2 ⟨liftSet e, ?_, ?_⟩))
        · exact mem_liftPairs.2 ⟨e, he, rfl⟩
        · exact succ_mem_liftSet.2 hie
      · refine Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_sup.2 ⟨c, hc, ?_⟩))
        by_cases h : c = cs
        · simp only [hBdef, if_pos h]; exact Finset.mem_insert_of_mem (succ_mem_liftSet.2 hic)
        · simp only [hBdef, if_neg h]; exact succ_mem_liftSet.2 hic
      · exact Finset.mem_union_right _ (succ_mem_liftSet.2 hm)
  refine ⟨mkMPattern lam _ P B M N (by omega) (card_liftPairs' T.card_pair)
    (disjoint_liftPairs' T.pairs_disjoint) hB hBd hPB hPM hBM hMc hcov, ?_⟩
  have hcsN : cs ∈ Finset.Icc 2 N := Finset.mem_Icc.2 ⟨hcs, by omega⟩
  rw [prod_mkMPattern, prod_cleanMBlocks T (N := N) (by omega), hPdef,
    prod_liftPairs' T.card_pair, map_mul, map_mul,
    ← Finset.mul_prod_erase _ _ hcsN, ← Finset.mul_prod_erase _ _ hcsN, map_mul, map_prod,
    hMdef, hlen, ← L1]
  have e1 : B cs = insert 0 (liftSet (cleanMBlocks T cs)) := by simp [hBdef]
  have e2 : ∏ c ∈ (Finset.Icc 2 N).erase cs, Delta F (2 * h + 2) (B c) =
      ∏ c ∈ (Finset.Icc 2 N).erase cs,
        incl F (2 * h + 2) n (Delta F (2 * h + 2) (cleanMBlocks T c)) := by
    refine Finset.prod_congr rfl (fun c hc => ?_)
    rw [incl_Delta]; simp [hBdef, Finset.ne_of_mem_erase hc]
  have e3 : Delta F (2 * h + 2) (insert 0 (liftSet (cleanMBlocks T cs))) =
      (∏ x ∈ cleanMBlocks T cs, (y F (2 * h + 2) x.succ - y F (2 * h + 2) 0)) *
        incl F (2 * h + 2) n (Delta F (2 * h + 2) (cleanMBlocks T cs)) := by
    rw [Delta_insert_of_lt _ _ (fun b hb => ?_), incl_Delta]
    · congr 1
      simp [liftSet, Finset.prod_map]
    · obtain ⟨b', _, rfl⟩ := Finset.mem_map.1 hb
      exact Fin.succ_pos b'
  rw [e1, e2, e3]
  simp only [map_prod]
  ring

/-- The lifted marked patterns of the proof of **(T4)** of `q_oddbox_lifts_1.md`: let `T` be a
marked pattern of `μ` on all the indices of `C_n`, let `λ` have the columns of `μ` except that
column `c_0 ≥ 2` is one shorter, `S = B_{c_0}`.  For `b ∈ S`, the pairs
`liftPairs T.pairs ∪ {{0, b+1}}`, the lifted marked block and the lifted blocks `B_c^+`
(`c ≠ c_0`), `(S ∖ b)^+` form a marked pattern of `λ` on `Fin (n+1)` with product
`D(y_0, y_{b+1}) · incl(Δ(S ∖ b) · G')`,
`G' = D_P · Pf_{E_ℓ}(B_0) · Π_{c ∈ [2,N], c ≠ c_0} Δ(B_c)`. -/
theorem exists_mpattern_pair {n : ℕ} {μ lam : Partition}
    (T : MarkedPattern μ (Finset.univ : Finset (Fin n))) {c0 : ℕ} (hc0 : 2 ≤ c0)
    (hcol : ∀ c, 1 ≤ c → colLen lam c + (if c = c0 then 1 else 0) = colLen μ c)
    {N : ℕ} (hN1 : lam.row 1 ≤ N) (hN2 : μ.row 1 ≤ N) (hN3 : c0 ≤ N)
    {b : Fin n} (hb : b ∈ cleanMBlocks T c0) :
    ∃ T' : MarkedPattern lam (Finset.univ : Finset (Fin (n + 1))),
      T'.prod F h = D F (2 * h + 2) 0 b.succ *
        incl F (2 * h + 2) n (Delta F (2 * h + 2) ((cleanMBlocks T c0).erase b) *
          ((∏ e ∈ T.pairs, pairD F (2 * h + 2) e) * markedPf F h μ.len T.marked *
            ∏ c ∈ (Finset.Icc 2 N).erase c0, Delta F (2 * h + 2) (cleanMBlocks T c))) := by
  classical
  have hlen : lam.len = μ.len := len_eq_of_colLen_one (by
    have := hcol 1 le_rfl; rw [if_neg (by omega)] at this; omega)
  set p0 : Finset (Fin (n + 1)) := {0, b.succ} with hp0
  have hp0L : ∀ e ∈ liftPairs T.pairs, Disjoint p0 e := by
    intro e he
    obtain ⟨e', he', rfl⟩ := mem_liftPairs.1 he
    rw [Finset.disjoint_left]
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact zero_notMem_liftSet _
    · rw [Finset.mem_singleton.1 hx, succ_mem_liftSet]
      exact Finset.disjoint_right.1 (disjoint_pairs_cleanMBlocks T he' c0) hb
  have hp0notin : p0 ∉ liftPairs T.pairs := by
    intro h
    have := Finset.disjoint_left.1 (hp0L p0 h) (Finset.mem_insert_self 0 _)
    exact this (Finset.mem_insert_self 0 _)
  set P := insert p0 (liftPairs T.pairs) with hPdef
  set M := liftSet T.marked with hMdef
  set B : ℕ → Finset (Fin (n + 1)) := fun c =>
    if c = c0 then liftSet ((cleanMBlocks T c).erase b) else liftSet (cleanMBlocks T c)
    with hBdef
  have hP2 : ∀ e ∈ P, e.card = 2 := by
    intro e he
    rcases Finset.mem_insert.1 he with rfl | he
    · exact Finset.card_pair (Fin.succ_ne_zero b).symm
    · exact card_liftPairs' T.card_pair e he
  have hPd : (P : Set (Finset (Fin (n + 1)))).PairwiseDisjoint id := by
    rw [hPdef, Finset.coe_insert]
    exact (disjoint_liftPairs' T.pairs_disjoint).insert (fun e he _ => hp0L e he)
  have hsub : ∀ c, B c ⊆ liftSet (cleanMBlocks T c) := by
    intro c
    by_cases h : c = c0
    · simp only [hBdef, if_pos h]
      exact Finset.map_subset_map.2 (Finset.erase_subset _ _)
    · simp only [hBdef, if_neg h]; exact Finset.Subset.refl _
  have hB : ∀ c, 2 ≤ c → (B c).card = colLen lam c := by
    intro c hc
    have := hcol c (by omega)
    by_cases h : c = c0
    · subst h
      simp only [hBdef, if_true, liftSet, Finset.card_map,
        Finset.card_erase_of_mem hb, card_cleanMBlocks T hc]
      simp at this; omega
    · simp only [hBdef, if_neg h, liftSet, Finset.card_map, card_cleanMBlocks T hc]
      simp [h] at this; omega
  have hBd : ∀ c, 2 ≤ c → ∀ c', 2 ≤ c' → c ≠ c' → Disjoint (B c) (B c') := by
    intro c _ c' _ hne
    exact ((Finset.disjoint_map _).2 (disjoint_cleanMBlocks T hne)).mono (hsub c) (hsub c')
  have hbM : b.succ ∉ M := by
    rw [hMdef, succ_mem_liftSet]
    exact Finset.disjoint_left.1 (disjoint_cleanMBlocks_marked T c0) hb
  have hPB : ∀ e ∈ P, ∀ c, 2 ≤ c → Disjoint e (B c) := by
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
          exact Finset.disjoint_left.1 (disjoint_cleanMBlocks T (Ne.symm h)) hb
    · obtain ⟨e', he', rfl⟩ := mem_liftPairs.1 he
      exact ((Finset.disjoint_map _).2 (disjoint_pairs_cleanMBlocks T he' c)).mono_right (hsub c)
  have hPM : ∀ e ∈ P, Disjoint e M := by
    intro e he
    rcases Finset.mem_insert.1 he with rfl | he
    · rw [Finset.disjoint_left]
      intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact zero_notMem_liftSet _
      · rw [Finset.mem_singleton.1 hx]; exact hbM
    · obtain ⟨e', he', rfl⟩ := mem_liftPairs.1 he
      exact (Finset.disjoint_map _).2 (T.pairs_marked_disjoint e' he')
  have hBM : ∀ c, 2 ≤ c → Disjoint (B c) M := by
    intro c _
    exact ((Finset.disjoint_map _).2 (disjoint_cleanMBlocks_marked T c)).mono_left (hsub c)
  have hMc : ∃ t, M.card = lam.len + 1 + 2 * t := by
    obtain ⟨t, ht⟩ := T.marked_card
    exact ⟨t, by rw [hMdef, liftSet, Finset.card_map, ht, hlen]⟩
  have hcov : P.sup id ∪ (Finset.Icc 2 N).sup B ∪ M = Finset.univ := by
    refine Finset.eq_univ_of_forall (fun x => ?_)
    have hp0mem : ∀ x ∈ p0, x ∈ P.sup id ∪ (Finset.Icc 2 N).sup B ∪ M := fun x hx =>
      Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_sup.2 ⟨p0, Finset.mem_insert_self _ _, hx⟩))
    refine Fin.cases (hp0mem 0 (Finset.mem_insert_self _ _)) (fun i => ?_) x
    by_cases hib : i = b
    · subst hib; exact hp0mem _ (by simp [hp0])
    rcases succ_mem_mcover T hN2 i with ⟨e, he, hie⟩ | ⟨c, hc, hic⟩ | hm
    · refine Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_sup.2 ⟨liftSet e, ?_, ?_⟩))
      · exact Finset.mem_insert_of_mem (mem_liftPairs.2 ⟨e, he, rfl⟩)
      · exact succ_mem_liftSet.2 hie
    · refine Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_sup.2 ⟨c, hc, ?_⟩))
      by_cases h : c = c0
      · simp only [hBdef, if_pos h, succ_mem_liftSet]
        subst h; exact Finset.mem_erase.2 ⟨hib, hic⟩
      · simp only [hBdef, if_neg h]; exact succ_mem_liftSet.2 hic
    · exact Finset.mem_union_right _ (succ_mem_liftSet.2 hm)
  refine ⟨mkMPattern lam _ P B M N hN1 hP2 hPd hB hBd hPB hPM hBM hMc hcov, ?_⟩
  have hc0N : c0 ∈ Finset.Icc 2 N := Finset.mem_Icc.2 ⟨hc0, hN3⟩
  rw [prod_mkMPattern, hPdef, Finset.prod_insert hp0notin, prod_liftPairs' T.card_pair,
    ← Finset.mul_prod_erase _ _ hc0N, hp0, pairD_of_lt (Fin.succ_pos b), hMdef, hlen, ← L1]
  have e1 : Delta F (2 * h + 2) (B c0) =
      incl F (2 * h + 2) n (Delta F (2 * h + 2) ((cleanMBlocks T c0).erase b)) := by
    rw [incl_Delta]; simp [hBdef]
  have e2 : ∏ c ∈ (Finset.Icc 2 N).erase c0, Delta F (2 * h + 2) (B c) =
      incl F (2 * h + 2) n (∏ c ∈ (Finset.Icc 2 N).erase c0,
        Delta F (2 * h + 2) (cleanMBlocks T c)) := by
    rw [map_prod]
    refine Finset.prod_congr rfl (fun c hc => ?_)
    rw [incl_Delta]; simp [hBdef, Finset.ne_of_mem_erase hc]
  rw [e1, e2, map_mul, map_mul, map_mul]
  ring

end OddLifts

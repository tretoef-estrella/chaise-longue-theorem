module

public import RequestProject.OddLifts.Main

/-!
# Patterns for the lifts (T6)–(T8) of `q_oddbox_lifts_2.md`

* the tight pattern of `μ ⊔ 1` used in the proof of (T6) (`exists_tpattern_addOne`);
* the lifted marked patterns (marked block inside `{0} ∪ B_0^+`, possibly with new pairs through
  `0`) used in the proofs of (T7) and (T8) (`exists_mpattern_lift`);
* the lifted tight patterns of `μ` (first block inside `{0} ∪ B_0^+`, new pairs through `0`) used
  in the proof of (T7) when `t = 0` (`exists_tpattern_lift`).
-/

@[expose] public section

namespace OddLifts2

open Peel hiding C
open Tight ChainLemma OddPatterns Lifts OddLifts

set_option synthInstance.maxHeartbeats 200000

/-- Auxiliary for (T6) of `q_oddbox_lifts_2.md`: the columns of `μ ⊔ 1 = μ.addOne`:
`colLen μ c + [c = 1] = colLen (μ.addOne) c` for every `c ≥ 1`. -/
lemma colLen_addOne' (mu : Partition) {c : ℕ} (hc : 1 ≤ c) :
    colLen mu c + (if c = 1 then 1 else 0) = colLen mu.addOne c :=
  (Lifts.colLen_addOne mu hc).symm

/-- Auxiliary for (T6) of `q_oddbox_lifts_2.md`: elements of the pairs are in their union. -/
lemma subset_sup_of_mem {k : ℕ} {Q : Finset (Finset (Fin k))} {e : Finset (Fin k)} (he : e ∈ Q) :
    e ⊆ Q.sup id :=
  Finset.le_sup (f := id) he

variable {F : Type*} [Field F] {h : ℕ}

/-- The tight pattern of the proof of **(T6)** of `q_oddbox_lifts_2.md`: let `T` be a marked
pattern of `μ` on all the indices of `C_n` with marked block `B_0`, let `S ⊆ B_0` with
`|S| = ℓ + 1` and `Q` a set of pairs partitioning `B_0 ∖ S`.  Then the pairs `P ∪ Q`, the first
block `S` and the blocks `B_c` (`c ≥ 2`) form a tight pattern `T'` of `μ ⊔ 1 = μ.addOne`, with
product `Δ(S) · D_Q · (D_P · Π_{c=2}^{N} Δ(B_c))` (`N ≥ μ_1`, `N ≥ (μ ⊔ 1)_1`). -/
theorem exists_tpattern_addOne {n : ℕ} {mu : Partition}
    (T : MarkedPattern mu (Finset.univ : Finset (Fin n))) (S : Finset (Fin n))
    (Q : Finset (Finset (Fin n))) (hS : S ⊆ T.marked) (hScard : S.card = mu.len + 1)
    (hQ : Odd3.IsPairs Q) (hQs : Odd3.supp Q = T.marked \ S) {N : ℕ} (hN1 : mu.row 1 ≤ N)
    (hN2 : mu.addOne.row 1 ≤ N) (hN : 1 ≤ N) :
    ∃ T' : TightPattern mu.addOne (Finset.univ : Finset (Fin n)),
      T'.prod F (2 * h + 2) = Delta F (2 * h + 2) S * (∏ e ∈ Q, pairD F (2 * h + 2) e) *
        ((∏ e ∈ T.pairs, pairD F (2 * h + 2) e) *
          ∏ c ∈ Finset.Icc 2 N, Delta F (2 * h + 2) (cleanMBlocks T c)) := by
  classical
  have hQsub : ∀ e ∈ Q, e ⊆ T.marked \ S := fun e he => by
    rw [← hQs]; exact subset_sup_of_mem he
  have hQM : ∀ e ∈ Q, e ⊆ T.marked := fun e he =>
    (hQsub e he).trans Finset.sdiff_subset
  set P := T.pairs ∪ Q with hPdef
  set B : ℕ → Finset (Fin n) := fun c => if c = 1 then S else cleanMBlocks T c with hBdef
  have hB : ∀ c, 1 ≤ c → (B c).card = colLen mu.addOne c := by
    intro c hc
    rw [← colLen_addOne' mu hc]
    by_cases h1 : c = 1
    · subst h1
      simp only [hBdef, if_pos rfl, hScard, OddPatterns.colLen_one, if_true]
    · simp only [hBdef, if_neg h1, add_zero]
      exact card_cleanMBlocks T (by omega)
  have hBd : ∀ c, 1 ≤ c → ∀ c', 1 ≤ c' → c ≠ c' → Disjoint (B c) (B c') := by
    intro c _ c' _ hne
    by_cases h1 : c = 1
    · have h1' : c' ≠ 1 := fun h' => hne (h1.trans h'.symm)
      simp only [hBdef, if_pos h1, if_neg h1']
      exact Finset.disjoint_of_subset_left hS (disjoint_cleanMBlocks_marked T c').symm
    · by_cases h1' : c' = 1
      · simp only [hBdef, if_neg h1, if_pos h1']
        exact (Finset.disjoint_of_subset_left hS (disjoint_cleanMBlocks_marked T c).symm).symm
      · simp only [hBdef, if_neg h1, if_neg h1']
        exact disjoint_cleanMBlocks T hne
  have hPB : ∀ e ∈ P, ∀ c, 1 ≤ c → Disjoint e (B c) := by
    intro e he c _
    rcases Finset.mem_union.1 he with he | he
    · by_cases h1 : c = 1
      · simp only [hBdef, if_pos h1]
        exact Finset.disjoint_of_subset_right hS (T.pairs_marked_disjoint e he)
      · simp only [hBdef, if_neg h1]
        exact disjoint_pairs_cleanMBlocks T he c
    · by_cases h1 : c = 1
      · simp only [hBdef, if_pos h1]
        exact Finset.disjoint_of_subset_left (hQsub e he) Finset.sdiff_disjoint
      · simp only [hBdef, if_neg h1]
        exact Finset.disjoint_of_subset_left (hQM e he) (disjoint_cleanMBlocks_marked T c).symm
  have hP2 : ∀ e ∈ P, e.card = 2 := by
    intro e he
    rcases Finset.mem_union.1 he with he | he
    · exact T.card_pair e he
    · exact hQ.1 e he
  have hTQ : ∀ e ∈ T.pairs, ∀ e' ∈ Q, Disjoint e e' := fun e he e' he' =>
    Finset.disjoint_of_subset_right (hQM e' he') (T.pairs_marked_disjoint e he)
  have hPd : (P : Set (Finset (Fin n))).PairwiseDisjoint id := by
    rw [hPdef, Finset.coe_union, Set.pairwiseDisjoint_union]
    refine ⟨T.pairs_disjoint, hQ.2, fun e he e' he' _ => hTQ e he e' he'⟩
  have hcov : P.sup id ∪ (Finset.Icc 1 N).sup B = Finset.univ := by
    refine Finset.eq_univ_of_forall (fun x => ?_)
    rcases succ_mem_mcover T hN1 x with ⟨e, he, hxe⟩ | ⟨c, hc, hxc⟩ | hxm
    · exact Finset.mem_union_left _ (Finset.mem_sup.2 ⟨e, Finset.mem_union_left _ he, hxe⟩)
    · rw [Finset.mem_Icc] at hc
      refine Finset.mem_union_right _ (Finset.mem_sup.2 ⟨c, Finset.mem_Icc.2 ⟨by omega, hc.2⟩, ?_⟩)
      simp only [hBdef, if_neg (show c ≠ 1 by omega)]
      exact hxc
    · by_cases hxS : x ∈ S
      · refine Finset.mem_union_right _ (Finset.mem_sup.2 ⟨1, Finset.mem_Icc.2 ⟨le_rfl, hN⟩, ?_⟩)
        simp only [hBdef, if_pos rfl]
        exact hxS
      · have : x ∈ Odd3.supp Q := by rw [hQs]; exact Finset.mem_sdiff.2 ⟨hxm, hxS⟩
        obtain ⟨e, he, hxe⟩ := Finset.mem_sup.1 this
        exact Finset.mem_union_left _ (Finset.mem_sup.2 ⟨e, Finset.mem_union_right _ he, hxe⟩)
  refine ⟨mkPattern mu.addOne _ P B N hN2 hP2 hPd hB hBd hPB hcov, ?_⟩
  rw [prod_mkPattern, hPdef, Finset.prod_union (Finset.disjoint_left.2 (fun e he he' => by
    have h2 := T.card_pair e he
    have := Finset.disjoint_self_iff_empty e |>.1 (hTQ e he e he')
    rw [this] at h2; simp at h2)),
    ← Finset.mul_prod_erase _ _ (Finset.mem_Icc.2 ⟨le_rfl, hN⟩)]
  have e1 : (Finset.Icc 1 N).erase 1 = Finset.Icc 2 N := by
    ext c; simp only [Finset.mem_erase, Finset.mem_Icc]; omega
  have e2 : ∏ c ∈ Finset.Icc 2 N, Delta F (2 * h + 2) (B c) =
      ∏ c ∈ Finset.Icc 2 N, Delta F (2 * h + 2) (cleanMBlocks T c) :=
    Finset.prod_congr rfl (fun c hc => by
      rw [Finset.mem_Icc] at hc
      simp only [hBdef, if_neg (show c ≠ 1 by omega)])
  rw [e1, e2]
  simp only [hBdef, if_pos rfl]
  ring

/-- Auxiliary for (T7) and (T8) of `q_oddbox_lifts_2.md`: a lifted pair `e^+` is disjoint from
`{0} ∪ B_0^+`. -/
lemma disjoint_liftSet_pair_Z {n : ℕ} {mu : Partition}
    (T : MarkedPattern mu (Finset.univ : Finset (Fin n))) {e : Finset (Fin n)} (he : e ∈ T.pairs) :
    Disjoint (liftSet e) (insert 0 (liftSet T.marked)) :=
  Finset.disjoint_insert_right.2 ⟨zero_notMem_liftSet _,
    (Finset.disjoint_map _).2 (T.pairs_marked_disjoint e he)⟩

/-- Auxiliary for (T7) and (T8) of `q_oddbox_lifts_2.md`: a lifted clean block `B_c^+` is disjoint
from `{0} ∪ B_0^+`. -/
lemma disjoint_liftSet_block_Z {n : ℕ} {mu : Partition}
    (T : MarkedPattern mu (Finset.univ : Finset (Fin n))) (c : ℕ) :
    Disjoint (liftSet (cleanMBlocks T c)) (insert 0 (liftSet T.marked)) :=
  Finset.disjoint_insert_right.2 ⟨zero_notMem_liftSet _,
    (Finset.disjoint_map _).2 (disjoint_cleanMBlocks_marked T c)⟩

/-- Auxiliary for (T7) and (T8) of `q_oddbox_lifts_2.md`: every index of `C_{n+1}` is covered by a
lifted pair, a lifted clean block or `{0} ∪ B_0^+`. -/
lemma mem_cover_lift {n : ℕ} {mu : Partition}
    (T : MarkedPattern mu (Finset.univ : Finset (Fin n))) {N : ℕ} (hN : mu.row 1 ≤ N)
    (x : Fin (n + 1)) :
    (∃ e ∈ T.pairs, x ∈ liftSet e) ∨ (∃ c ∈ Finset.Icc 2 N, x ∈ liftSet (cleanMBlocks T c)) ∨
      x ∈ insert 0 (liftSet T.marked) := by
  refine Fin.cases (Or.inr (Or.inr (Finset.mem_insert_self _ _))) (fun i => ?_) x
  rcases succ_mem_mcover T hN i with ⟨e, he, hie⟩ | ⟨c, hc, hic⟩ | him
  · exact Or.inl ⟨e, he, succ_mem_liftSet.2 hie⟩
  · exact Or.inr (Or.inl ⟨c, hc, succ_mem_liftSet.2 hic⟩)
  · exact Or.inr (Or.inr (Finset.mem_insert_of_mem (succ_mem_liftSet.2 him)))

/-- The lifted marked patterns of the proofs of **(T7)** and **(T8)** of `q_oddbox_lifts_2.md`:
let `T` be a marked pattern of `μ` on all the indices of `C_n` (marked block `B_0`), let `λ` have
the columns `c ≥ 2` of `μ`, and let `X` (pairs) and `M` (marked block) partition
`{0} ∪ B_0^+` with `|M| = ℓ(λ) + 1 + 2t`.  The pairs `P^+ ∪ X`, the blocks `B_c^+` (`c ≥ 2`) and the
marked block `M` form a marked pattern `T'` of `λ` on `Fin (n+1)` with
`T'.prod = D_X · Pf_{E_{ℓ(λ)}}(M) · incl(D_P · Π_{c=2}^{N} Δ(B_c))`. -/
theorem exists_mpattern_lift {n : ℕ} {mu lam : Partition}
    (T : MarkedPattern mu (Finset.univ : Finset (Fin n)))
    (hcol : ∀ c, 2 ≤ c → colLen lam c = colLen mu c) {N : ℕ} (hN1 : mu.row 1 ≤ N)
    (hN2 : lam.row 1 ≤ N) (X : Finset (Finset (Fin (n + 1)))) (M : Finset (Fin (n + 1)))
    (hX2 : ∀ e ∈ X, e.card = 2) (hXd : (X : Set (Finset (Fin (n + 1)))).PairwiseDisjoint id)
    (hXM : ∀ e ∈ X, Disjoint e M) (hcovX : X.sup id ∪ M = insert 0 (liftSet T.marked))
    (hMc : ∃ t, M.card = lam.len + 1 + 2 * t) :
    ∃ T' : MarkedPattern lam (Finset.univ : Finset (Fin (n + 1))),
      T'.prod F h = (∏ e ∈ X, pairD F (2 * h + 2) e) * markedPf F h lam.len M *
        incl F (2 * h + 2) n ((∏ e ∈ T.pairs, pairD F (2 * h + 2) e) *
          ∏ c ∈ Finset.Icc 2 N, Delta F (2 * h + 2) (cleanMBlocks T c)) := by
  classical
  set Z := insert 0 (liftSet T.marked) with hZ
  have hXZ : ∀ e ∈ X, e ⊆ Z := fun e he => by
    rw [← hcovX]; exact (subset_sup_of_mem he).trans Finset.subset_union_left
  have hMZ : M ⊆ Z := by rw [← hcovX]; exact Finset.subset_union_right
  set P := liftPairs T.pairs ∪ X with hPdef
  set B : ℕ → Finset (Fin (n + 1)) := fun c => liftSet (cleanMBlocks T c) with hBdef
  have hLZ : ∀ e ∈ liftPairs T.pairs, Disjoint e Z := by
    intro e he
    obtain ⟨e', he', rfl⟩ := mem_liftPairs.1 he
    exact disjoint_liftSet_pair_Z T he'
  have hB : ∀ c, 2 ≤ c → (B c).card = colLen lam c := by
    intro c hc
    simp only [hBdef, liftSet, Finset.card_map, card_cleanMBlocks T hc, hcol c hc]
  have hBd : ∀ c, 2 ≤ c → ∀ c', 2 ≤ c' → c ≠ c' → Disjoint (B c) (B c') := fun c _ c' _ hne =>
    (Finset.disjoint_map _).2 (disjoint_cleanMBlocks T hne)
  have hPB : ∀ e ∈ P, ∀ c, 2 ≤ c → Disjoint e (B c) := by
    intro e he c _
    rcases Finset.mem_union.1 he with he | he
    · obtain ⟨e', he', rfl⟩ := mem_liftPairs.1 he
      exact (Finset.disjoint_map _).2 (disjoint_pairs_cleanMBlocks T he' c)
    · exact Finset.disjoint_of_subset_left (hXZ e he) (disjoint_liftSet_block_Z T c).symm
  have hPM : ∀ e ∈ P, Disjoint e M := by
    intro e he
    rcases Finset.mem_union.1 he with he | he
    · exact Finset.disjoint_of_subset_right hMZ (hLZ e he)
    · exact hXM e he
  have hBM : ∀ c, 2 ≤ c → Disjoint (B c) M := fun c _ =>
    Finset.disjoint_of_subset_right hMZ (disjoint_liftSet_block_Z T c)
  have hP2 : ∀ e ∈ P, e.card = 2 := by
    intro e he
    rcases Finset.mem_union.1 he with he | he
    · exact card_liftPairs' T.card_pair e he
    · exact hX2 e he
  have hLX : ∀ e ∈ liftPairs T.pairs, ∀ e' ∈ X, Disjoint e e' := fun e he e' he' =>
    Finset.disjoint_of_subset_right (hXZ e' he') (hLZ e he)
  have hPd : (P : Set (Finset (Fin (n + 1)))).PairwiseDisjoint id := by
    rw [hPdef, Finset.coe_union, Set.pairwiseDisjoint_union]
    exact ⟨disjoint_liftPairs' T.pairs_disjoint, hXd, fun e he e' he' _ => hLX e he e' he'⟩
  have hcov : P.sup id ∪ (Finset.Icc 2 N).sup B ∪ M = Finset.univ := by
    refine Finset.eq_univ_of_forall (fun x => ?_)
    rcases mem_cover_lift T hN1 x with ⟨e, he, hxe⟩ | ⟨c, hc, hxc⟩ | hxZ
    · refine Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_sup.2 ⟨liftSet e, Finset.mem_union_left _ (mem_liftPairs.2 ⟨e, he, rfl⟩), hxe⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_sup.2 ⟨c, hc, hxc⟩))
    · change x ∈ Z at hxZ
      rw [← hcovX] at hxZ
      rcases Finset.mem_union.1 hxZ with hx | hx
      · obtain ⟨e, he, hxe⟩ := Finset.mem_sup.1 hx
        exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_sup.2 ⟨e, Finset.mem_union_right _ he, hxe⟩))
      · exact Finset.mem_union_right _ hx
  refine ⟨mkMPattern lam _ P B M N hN2 hP2 hPd hB hBd hPB hPM hBM hMc hcov, ?_⟩
  rw [prod_mkMPattern, hPdef, Finset.prod_union (Finset.disjoint_left.2 (fun e he he' => by
    have h2 := hX2 e he'
    have := Finset.disjoint_self_iff_empty e |>.1 (hLX e he e he')
    rw [this] at h2; simp at h2)), prod_liftPairs' T.card_pair, map_mul, map_prod]
  have e2 : ∏ c ∈ Finset.Icc 2 N, Delta F (2 * h + 2) (B c) =
      ∏ c ∈ Finset.Icc 2 N, incl F (2 * h + 2) n (Delta F (2 * h + 2) (cleanMBlocks T c)) :=
    Finset.prod_congr rfl (fun c _ => (incl_Delta _).symm)
  rw [e2]
  simp only [map_prod]
  ring

/-- The lifted tight patterns of the proof of **(T7)** of `q_oddbox_lifts_2.md` (case `t = 0`):
let `T` be a marked pattern of `μ` on all the indices of `C_n` (marked block `B_0`), and let `X`
(pairs) and `S` (first block, `|S| = ℓ(μ)`) partition `{0} ∪ B_0^+`.  The pairs `P^+ ∪ X`, the
first block `S` and the blocks `B_c^+` (`c ≥ 2`) form a tight pattern `T'` of `μ` on `Fin (n+1)`
with `T'.prod = D_X · Δ(S) · incl(D_P · Π_{c=2}^{N} Δ(B_c))`. -/
theorem exists_tpattern_lift {n : ℕ} {mu : Partition}
    (T : MarkedPattern mu (Finset.univ : Finset (Fin n))) {N : ℕ} (hN1 : mu.row 1 ≤ N)
    (hN : 1 ≤ N) (X : Finset (Finset (Fin (n + 1)))) (S : Finset (Fin (n + 1)))
    (hX2 : ∀ e ∈ X, e.card = 2) (hXd : (X : Set (Finset (Fin (n + 1)))).PairwiseDisjoint id)
    (hXS : ∀ e ∈ X, Disjoint e S) (hcovX : X.sup id ∪ S = insert 0 (liftSet T.marked))
    (hS : S.card = mu.len) :
    ∃ T' : TightPattern mu (Finset.univ : Finset (Fin (n + 1))),
      T'.prod F (2 * h + 2) = (∏ e ∈ X, pairD F (2 * h + 2) e) * Delta F (2 * h + 2) S *
        incl F (2 * h + 2) n ((∏ e ∈ T.pairs, pairD F (2 * h + 2) e) *
          ∏ c ∈ Finset.Icc 2 N, Delta F (2 * h + 2) (cleanMBlocks T c)) := by
  classical
  set Z := insert 0 (liftSet T.marked) with hZ
  have hXZ : ∀ e ∈ X, e ⊆ Z := fun e he => by
    rw [← hcovX]; exact (subset_sup_of_mem he).trans Finset.subset_union_left
  have hSZ : S ⊆ Z := by rw [← hcovX]; exact Finset.subset_union_right
  set P := liftPairs T.pairs ∪ X with hPdef
  set B : ℕ → Finset (Fin (n + 1)) := fun c => if c = 1 then S else liftSet (cleanMBlocks T c)
    with hBdef
  have hLZ : ∀ e ∈ liftPairs T.pairs, Disjoint e Z := by
    intro e he
    obtain ⟨e', he', rfl⟩ := mem_liftPairs.1 he
    exact disjoint_liftSet_pair_Z T he'
  have hB : ∀ c, 1 ≤ c → (B c).card = colLen mu c := by
    intro c hc
    by_cases h1 : c = 1
    · subst h1
      simp only [hBdef, if_pos rfl, hS, OddPatterns.colLen_one]
    · simp only [hBdef, if_neg h1, liftSet, Finset.card_map]
      exact card_cleanMBlocks T (by omega)
  have hBd : ∀ c, 1 ≤ c → ∀ c', 1 ≤ c' → c ≠ c' → Disjoint (B c) (B c') := by
    intro c _ c' _ hne
    by_cases h1 : c = 1
    · have h1' : c' ≠ 1 := fun h' => hne (h1.trans h'.symm)
      simp only [hBdef, if_pos h1, if_neg h1']
      exact Finset.disjoint_of_subset_left hSZ (disjoint_liftSet_block_Z T c').symm
    · by_cases h1' : c' = 1
      · simp only [hBdef, if_neg h1, if_pos h1']
        exact (Finset.disjoint_of_subset_left hSZ (disjoint_liftSet_block_Z T c).symm).symm
      · simp only [hBdef, if_neg h1, if_neg h1']
        exact (Finset.disjoint_map _).2 (disjoint_cleanMBlocks T hne)
  have hPB : ∀ e ∈ P, ∀ c, 1 ≤ c → Disjoint e (B c) := by
    intro e he c _
    rcases Finset.mem_union.1 he with he | he
    · by_cases h1 : c = 1
      · simp only [hBdef, if_pos h1]
        exact Finset.disjoint_of_subset_right hSZ (hLZ e he)
      · simp only [hBdef, if_neg h1]
        obtain ⟨e', he', rfl⟩ := mem_liftPairs.1 he
        exact (Finset.disjoint_map _).2 (disjoint_pairs_cleanMBlocks T he' c)
    · by_cases h1 : c = 1
      · simp only [hBdef, if_pos h1]
        exact hXS e he
      · simp only [hBdef, if_neg h1]
        exact Finset.disjoint_of_subset_left (hXZ e he) (disjoint_liftSet_block_Z T c).symm
  have hP2 : ∀ e ∈ P, e.card = 2 := by
    intro e he
    rcases Finset.mem_union.1 he with he | he
    · exact card_liftPairs' T.card_pair e he
    · exact hX2 e he
  have hLX : ∀ e ∈ liftPairs T.pairs, ∀ e' ∈ X, Disjoint e e' := fun e he e' he' =>
    Finset.disjoint_of_subset_right (hXZ e' he') (hLZ e he)
  have hPd : (P : Set (Finset (Fin (n + 1)))).PairwiseDisjoint id := by
    rw [hPdef, Finset.coe_union, Set.pairwiseDisjoint_union]
    exact ⟨disjoint_liftPairs' T.pairs_disjoint, hXd, fun e he e' he' _ => hLX e he e' he'⟩
  have hcov : P.sup id ∪ (Finset.Icc 1 N).sup B = Finset.univ := by
    refine Finset.eq_univ_of_forall (fun x => ?_)
    rcases mem_cover_lift T hN1 x with ⟨e, he, hxe⟩ | ⟨c, hc, hxc⟩ | hxZ
    · exact Finset.mem_union_left _
        (Finset.mem_sup.2 ⟨liftSet e, Finset.mem_union_left _ (mem_liftPairs.2 ⟨e, he, rfl⟩), hxe⟩)
    · rw [Finset.mem_Icc] at hc
      refine Finset.mem_union_right _ (Finset.mem_sup.2 ⟨c, Finset.mem_Icc.2 ⟨by omega, hc.2⟩, ?_⟩)
      simp only [hBdef, if_neg (show c ≠ 1 by omega)]
      exact hxc
    · change x ∈ Z at hxZ
      rw [← hcovX] at hxZ
      rcases Finset.mem_union.1 hxZ with hx | hx
      · obtain ⟨e, he, hxe⟩ := Finset.mem_sup.1 hx
        exact Finset.mem_union_left _ (Finset.mem_sup.2 ⟨e, Finset.mem_union_right _ he, hxe⟩)
      · refine Finset.mem_union_right _ (Finset.mem_sup.2 ⟨1, Finset.mem_Icc.2 ⟨le_rfl, hN⟩, ?_⟩)
        simp only [hBdef, if_pos rfl]
        exact hx
  refine ⟨mkPattern mu _ P B N hN1 hP2 hPd hB hBd hPB hcov, ?_⟩
  rw [prod_mkPattern, hPdef, Finset.prod_union (Finset.disjoint_left.2 (fun e he he' => by
    have h2 := hX2 e he'
    have := Finset.disjoint_self_iff_empty e |>.1 (hLX e he e he')
    rw [this] at h2; simp at h2)), prod_liftPairs' T.card_pair, map_mul, map_prod,
    ← Finset.mul_prod_erase _ _ (Finset.mem_Icc.2 ⟨le_rfl, hN⟩)]
  have e1 : (Finset.Icc 1 N).erase 1 = Finset.Icc 2 N := by
    ext c; simp only [Finset.mem_erase, Finset.mem_Icc]; omega
  have e2 : ∏ c ∈ Finset.Icc 2 N, Delta F (2 * h + 2) (B c) =
      ∏ c ∈ Finset.Icc 2 N, incl F (2 * h + 2) n (Delta F (2 * h + 2) (cleanMBlocks T c)) :=
    Finset.prod_congr rfl (fun c hc => by
      rw [Finset.mem_Icc] at hc
      simp only [hBdef, if_neg (show c ≠ 1 by omega)]
      exact (incl_Delta _).symm)
  rw [e1, e2]
  simp only [hBdef, if_pos rfl, map_prod]
  ring

end OddLifts2

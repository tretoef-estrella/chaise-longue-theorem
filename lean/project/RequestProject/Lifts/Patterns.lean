module

public import RequestProject.Lifts.Algebra

/-!
# Tight patterns for the proof of `q_P3_lifts.md`

General facts about tight patterns (`q_P3_identities.md`) used in **Step 1** of the Proof of the
Proposition of `q_P3_lifts.md`:
* the index set `{2, …, m}` of `C_{m−1}` inside `{1, …, m}` (`liftSet`), and the fact that the
  inclusion `C_{m−1} → C_m` maps `D` and `Δ` on `{2, …, m}` to `D` and `Δ` (`incl_pairD`,
  `incl_Delta`);
* a way to build a tight pattern from pairs and blocks satisfying the covering conditions, where
  the number of pairs `(|I| − |λ|)/2` is automatic (`mkPattern`);
* the blocks `B_c` of a tight pattern of `μ`, taken to be empty for `c > μ_1` (`cleanBlocks`).
-/

@[expose] public section

namespace Lifts

open Peel hiding C
open Tight ChainLemma

set_option synthInstance.maxHeartbeats 200000

variable {F : Type*} [Field F] {q : ℕ}

/-- Step 1 of the Proof in `q_P3_lifts.md`: a subset of the index set `{2, …, m}` of `C_{m−1}`
(encoded as a subset of `Fin (m-1)`) viewed as a subset of `{1, …, m}` (`Fin m`), via
`i ↦ i + 1`. -/
def liftSet {n : ℕ} (s : Finset (Fin n)) : Finset (Fin (n + 1)) := s.map (Fin.succEmb n)

/-- Step 1 of the Proof in `q_P3_lifts.md`: the index `1` is not in `{2, …, m}`. -/
lemma zero_notMem_liftSet {n : ℕ} (s : Finset (Fin n)) : (0 : Fin (n + 1)) ∉ liftSet s := by
  simp [liftSet, Fin.succ_ne_zero]

/-- Step 1 of the Proof in `q_P3_lifts.md`: membership in a lifted index set. -/
lemma succ_mem_liftSet {n : ℕ} {s : Finset (Fin n)} {i : Fin n} :
    i.succ ∈ liftSet s ↔ i ∈ s := by
  simp [liftSet]

/-- Step 1 of the Proof in `q_P3_lifts.md`: lifting index sets is injective. -/
lemma liftSet_injective {n : ℕ} : Function.Injective (liftSet (n := n)) :=
  Finset.map_injective _

/-- Step 1 of the Proof in `q_P3_lifts.md`: a Vandermonde product over an order-preserving image
of an index set. -/
lemma vand_map_strictMono {ι κ R : Type*} [LinearOrder ι] [LinearOrder κ] [CommRing R]
    (x : κ → R) (f : ι ↪ κ) (hf : StrictMono f) (B : Finset ι) :
    vand x (B.map f) = vand (fun i => x (f i)) B := by
  classical
  unfold vand
  rw [Finset.prod_map]
  refine Finset.prod_congr rfl (fun c _ => ?_)
  rw [Finset.filter_map, Finset.prod_map]
  refine Finset.prod_congr ?_ (fun _ _ => rfl)
  ext c'
  simp [hf.lt_iff_lt]

/-- Step 1 of the Proof in `q_P3_lifts.md`: the inclusion `C_{m−1} → C_m` maps `Δ(B)` (for `B`
among the variables `y_2, …, y_m` of `C_{m−1}`) to `Δ(B)` in `C_m`. -/
theorem incl_Delta {n : ℕ} (B : Finset (Fin n)) :
    incl F q n (Delta F q B) = Delta F q (liftSet B) := by
  unfold Delta liftSet
  rw [map_vand, vand_map_strictMono _ _ (Fin.strictMono_succ) B]
  exact vand_congr (fun b _ => incl_y b)

/-- Step 1 of the Proof in `q_P3_lifts.md`: the inclusion `C_{m−1} → C_m` maps `D(y_a, y_b)`
to `D(y_{a+1}, y_{b+1})`. -/
theorem incl_D {n : ℕ} (a b : Fin n) : incl F q n (D F q a b) = D F q a.succ b.succ := by
  simp [D, map_sum, incl_y]

/-- Step 1 of the Proof in `q_P3_lifts.md`: the factor of a pair `{a < b}` is `D(y_a, y_b)`. -/
theorem pairD_of_lt {m : ℕ} {a b : Fin m} (hab : a < b) : pairD F q {a, b} = D F q a b := by
  unfold pairD
  rw [dif_pos ⟨a, by simp⟩]
  congr 1
  · simp [Finset.min'_insert, hab.le]
  · simp [Finset.max'_insert, hab.le]

/-- Step 1 of the Proof in `q_P3_lifts.md`: the inclusion `C_{m−1} → C_m` maps the factor of a
pair `{a, b}` of `{2, …, m}` to the factor of the same pair in `{1, …, m}`. -/
theorem incl_pairD {n : ℕ} {e : Finset (Fin n)} (he : e.card = 2) :
    incl F q n (pairD F q e) = pairD F q (liftSet e) := by
  obtain ⟨x, z, hxz, rfl⟩ := Finset.card_eq_two.1 he
  have key : ∀ a b : Fin n, a < b →
      incl F q n (pairD F q {a, b}) = pairD F q (liftSet {a, b}) := by
    intro a b hab
    have : liftSet ({a, b} : Finset (Fin n)) = {a.succ, b.succ} := by simp [liftSet]
    rw [this, pairD_of_lt hab, pairD_of_lt (Fin.succ_lt_succ_iff.2 hab), incl_D]
  rcases lt_or_gt_of_ne hxz with h | h
  · exact key x z h
  · rw [Finset.pair_comm]; exact key z x h

/-- `Δ(∅) = 1` (**Setting, "Vandermonde"** of `q_P3_identities.md`; used in Step 1 of the Proof
in `q_P3_lifts.md`). -/
lemma Delta_empty {m : ℕ} : Delta F q (∅ : Finset (Fin m)) = 1 := by
  simp [Delta, vand]

/-- Step 1 of the Proof in `q_P3_lifts.md` (counting): pairwise disjoint pairs cover
`2 · #pairs` indices. -/
lemma card_sup_pairs {k : ℕ} (P : Finset (Finset (Fin k))) (hP2 : ∀ e ∈ P, e.card = 2)
    (hPd : (P : Set (Finset (Fin k))).PairwiseDisjoint id) : (P.sup id).card = 2 * P.card := by
  rw [Finset.sup_eq_biUnion, Finset.card_biUnion hPd]
  simp only [id]
  rw [Finset.sum_congr rfl hP2]
  simp [mul_comm]

/-- Step 1 of the Proof in `q_P3_lifts.md`: `Σ_{c=1}^{N} λ'_c = |λ|` for `N ≥ λ_1` (the Setting
of `q_P3_identities.md`, padded with empty columns). -/
lemma sum_colLen_Icc (lam : Partition) {N : ℕ} (hN : lam.row 1 ≤ N) :
    ∑ c ∈ Finset.Icc 1 N, colLen lam c = lam.size := by
  rw [← sum_colLen]
  symm
  refine Finset.sum_subset (Finset.Icc_subset_Icc le_rfl hN) (fun c hc hnc => ?_)
  simp only [Finset.mem_Icc, not_and, not_le] at hc hnc
  exact colLen_eq_zero lam (hnc hc.1)

/-- Step 1 of the Proof in `q_P3_lifts.md`: blocks with `|B_c| = λ'_c` for all `c ≥ 1` vanish for
`c > λ_1`. -/
lemma block_eq_empty {k : ℕ} {lam : Partition} {B : ℕ → Finset (Fin k)}
    (hB : ∀ c, 1 ≤ c → (B c).card = colLen lam c) {c : ℕ} (hc : lam.row 1 < c) : B c = ∅ := by
  rw [← Finset.card_eq_zero, hB c (by omega), colLen_eq_zero lam hc]

/-- Step 1 of the Proof in `q_P3_lifts.md`: for blocks vanishing above `λ_1`, the union over
`c = 1, …, N` (`N ≥ λ_1`) is the union over `c = 1, …, λ_1`. -/
lemma sup_blocks_eq {k : ℕ} {lam : Partition} {B : ℕ → Finset (Fin k)}
    (hB : ∀ c, 1 ≤ c → (B c).card = colLen lam c) {N : ℕ} (hN : lam.row 1 ≤ N) :
    (Finset.Icc 1 N).sup B = (Finset.Icc 1 (lam.row 1)).sup B := by
  refine le_antisymm (Finset.sup_le (fun c hc => ?_))
    (Finset.sup_mono (Finset.Icc_subset_Icc le_rfl hN))
  rw [Finset.mem_Icc] at hc
  by_cases h : c ≤ lam.row 1
  · exact Finset.le_sup (f := B) (Finset.mem_Icc.2 ⟨hc.1, h⟩)
  · rw [block_eq_empty hB (by omega)]; exact bot_le

/-- Step 1 of the Proof in `q_P3_lifts.md`: a tight pattern of `λ` on `I` (`q_P3_identities.md`)
built from pairs `P` and blocks `B_c` (`c ≥ 1`, with `|B_c| = λ'_c` for all `c ≥ 1`, so
`B_c = ∅` for `c > λ_1`) that are pairwise disjoint and cover `I`.  The number of pairs
`(|I| − |λ|)/2` is then automatic ("the number of pairs … is unchanged / has grown by one" in the
cases of the Proof). -/
def mkPattern {k : ℕ} (lam : Partition) (I : Finset (Fin k)) (P : Finset (Finset (Fin k)))
    (B : ℕ → Finset (Fin k)) (N : ℕ) (hN : lam.row 1 ≤ N) (hP2 : ∀ e ∈ P, e.card = 2)
    (hPd : (P : Set (Finset (Fin k))).PairwiseDisjoint id)
    (hB : ∀ c, 1 ≤ c → (B c).card = colLen lam c)
    (hBd : ∀ c, 1 ≤ c → ∀ c', 1 ≤ c' → c ≠ c' → Disjoint (B c) (B c'))
    (hPB : ∀ e ∈ P, ∀ c, 1 ≤ c → Disjoint e (B c))
    (hcov : P.sup id ∪ (Finset.Icc 1 N).sup B = I) : TightPattern lam I :=
  have hcard : I.card = 2 * P.card + lam.size := by
    have hdisj : Disjoint (P.sup id) ((Finset.Icc 1 N).sup B) := by
      rw [Finset.disjoint_sup_left]
      intro e he
      rw [Finset.disjoint_sup_right]
      intro c hc
      exact hPB e he c (Finset.mem_Icc.1 hc).1
    have hBd' : ((Finset.Icc 1 N : Finset ℕ) : Set ℕ).PairwiseDisjoint B := by
      intro c hc c' hc' hne
      exact hBd c (Finset.mem_Icc.1 hc).1 c' (Finset.mem_Icc.1 hc').1 hne
    rw [← hcov, Finset.card_union_of_disjoint hdisj, card_sup_pairs P hP2 hPd,
      Finset.sup_eq_biUnion (Finset.Icc 1 N) B, Finset.card_biUnion hBd',
      Finset.sum_congr rfl (fun c hc => hB c (Finset.mem_Icc.1 hc).1), sum_colLen_Icc lam hN]
  { pairs := P
    blocks := B
    size_le := by omega
    even_sub := ⟨P.card, by omega⟩
    card_pairs := by omega
    card_pair := hP2
    pairs_disjoint := hPd
    card_block := fun c hc => hB c (Finset.mem_Icc.1 hc).1
    blocks_disjoint := fun c hc c' hc' hne =>
      hBd c (Finset.mem_Icc.1 hc).1 c' (Finset.mem_Icc.1 hc').1 hne
    pairs_blocks_disjoint := fun e he c hc => hPB e he c (Finset.mem_Icc.1 hc).1
    cover := by rw [← hcov, sup_blocks_eq hB hN] }

/-- Step 1 of the Proof in `q_P3_lifts.md`: the product of a pattern built with `mkPattern` is
`Π_{e ∈ P} D_e · Π_{c=1}^{N} Δ(B_c)`. -/
theorem prod_mkPattern {k : ℕ} (lam : Partition) (I : Finset (Fin k))
    (P : Finset (Finset (Fin k))) (B : ℕ → Finset (Fin k)) (N : ℕ) (hN : lam.row 1 ≤ N)
    (hP2 : ∀ e ∈ P, e.card = 2) (hPd : (P : Set (Finset (Fin k))).PairwiseDisjoint id)
    (hB : ∀ c, 1 ≤ c → (B c).card = colLen lam c)
    (hBd : ∀ c, 1 ≤ c → ∀ c', 1 ≤ c' → c ≠ c' → Disjoint (B c) (B c'))
    (hPB : ∀ e ∈ P, ∀ c, 1 ≤ c → Disjoint e (B c))
    (hcov : P.sup id ∪ (Finset.Icc 1 N).sup B = I) :
    (mkPattern lam I P B N hN hP2 hPd hB hBd hPB hcov).prod F q =
      (∏ e ∈ P, pairD F q e) * ∏ c ∈ Finset.Icc 1 N, Delta F q (B c) := by
  unfold TightPattern.prod
  simp only [mkPattern]
  congr 1
  refine Finset.prod_subset (Finset.Icc_subset_Icc le_rfl hN) (fun c hc hnc => ?_)
  simp only [Finset.mem_Icc, not_and, not_le] at hc hnc
  rw [block_eq_empty hB (hnc hc.1), Delta_empty]

/-- Step 1 of the Proof in `q_P3_lifts.md`: the blocks `B_c` of a tight pattern of `μ`, with the
convention `B_c = ∅` for `c ∉ {1, …, μ_1}` (the file's "`B = ∅` if `c* > μ_1`"). -/
def cleanBlocks {k : ℕ} {μ : Partition} {I : Finset (Fin k)} (T : TightPattern μ I) (c : ℕ) :
    Finset (Fin k) :=
  if c ∈ Finset.Icc 1 (μ.row 1) then T.blocks c else ∅

/-- Step 1 of the Proof in `q_P3_lifts.md`: `|B_c| = μ'_c` for every `c ≥ 1`. -/
lemma card_cleanBlocks {k : ℕ} {μ : Partition} {I : Finset (Fin k)} (T : TightPattern μ I)
    {c : ℕ} (hc : 1 ≤ c) : (cleanBlocks T c).card = colLen μ c := by
  unfold cleanBlocks
  split_ifs with h
  · exact T.card_block c h
  · simp only [Finset.mem_Icc, not_and, not_le] at h
    rw [colLen_eq_zero μ (h hc)]; rfl

/-- Step 1 of the Proof in `q_P3_lifts.md`: the blocks are pairwise disjoint. -/
lemma disjoint_cleanBlocks {k : ℕ} {μ : Partition} {I : Finset (Fin k)} (T : TightPattern μ I)
    {c c' : ℕ} (hne : c ≠ c') : Disjoint (cleanBlocks T c) (cleanBlocks T c') := by
  unfold cleanBlocks
  split_ifs with h h'
  · exact T.blocks_disjoint h h' hne
  all_goals simp

/-- Step 1 of the Proof in `q_P3_lifts.md`: pairs and blocks are disjoint. -/
lemma disjoint_pairs_cleanBlocks {k : ℕ} {μ : Partition} {I : Finset (Fin k)}
    (T : TightPattern μ I) {e : Finset (Fin k)} (he : e ∈ T.pairs) (c : ℕ) :
    Disjoint e (cleanBlocks T c) := by
  unfold cleanBlocks
  split_ifs with h
  · exact T.pairs_blocks_disjoint e he c h
  · simp

/-- Step 1 of the Proof in `q_P3_lifts.md`: the pairs and the blocks `B_1, …, B_N` (`N ≥ μ_1`)
cover `I`. -/
lemma cover_cleanBlocks {k : ℕ} {μ : Partition} {I : Finset (Fin k)} (T : TightPattern μ I)
    {N : ℕ} (hN : μ.row 1 ≤ N) :
    T.pairs.sup id ∪ (Finset.Icc 1 N).sup (cleanBlocks T) = I := by
  rw [sup_blocks_eq (fun c hc => card_cleanBlocks T hc) hN]
  conv_rhs => rw [← T.cover]
  congr 1
  exact Finset.sup_congr rfl (fun c hc => by simp [cleanBlocks, hc])

/-- Step 1 of the Proof in `q_P3_lifts.md`: `G = Π_{{a<b} ∈ P} D(y_a, y_b) · Π_{c=1}^{N} Δ(B_c)`
for every `N ≥ μ_1`. -/
lemma prod_cleanBlocks {k : ℕ} {μ : Partition} {I : Finset (Fin k)} (T : TightPattern μ I)
    {N : ℕ} (hN : μ.row 1 ≤ N) :
    T.prod F q = (∏ e ∈ T.pairs, pairD F q e) *
      ∏ c ∈ Finset.Icc 1 N, Delta F q (cleanBlocks T c) := by
  unfold TightPattern.prod
  congr 1
  rw [← Finset.prod_subset (Finset.Icc_subset_Icc le_rfl hN) (fun c hc hnc => ?_)]
  · exact Finset.prod_congr rfl (fun c hc => by simp [cleanBlocks, hc])
  · simp only [Finset.mem_Icc, not_and, not_le] at hc hnc
    have : cleanBlocks T c = ∅ := by simp [cleanBlocks]; omega
    rw [this, Delta_empty]

end Lifts

end

module

public import RequestProject.BipP3.Algebra

/-!
# The tight patterns of the cases (α), (β), (γ) of Proposition 7.5 (`q_bip_P3.md`)

Given a tight pattern `(P, (B^+_c), (B^−_c))` of `μ` on `([α − 1], [β])`, read inside `R_{α,β}`
on the indices `({2, …, α}, [β])` (**Setting** of `q_bip_P3.md`), we build the tight patterns of
`λ = opt_Φ(μ)` on `([α], [β])` used in the **Proof** of Proposition 7.5:
* cases (α) and (β): put the index `1` into a column block `B^+_{c*}` (`exists_pattern_insert`);
* case (γ): for `b ∈ S = B^−_{c_0}`, add the pair `(1, b)` and remove `b` from `S`
  (`exists_pattern_pair`).

General tools: building a tight pattern from pairs and blocks satisfying the covering conditions,
the number of pairs `α − |λ_+|` being automatic (`mkBPattern`), and the blocks of a tight pattern
taken to be empty outside `1, …, μ_{±,1}` (`cleanX`, `cleanZ`).
-/

@[expose] public section

namespace BipP3

open Bip ChainLemma Tight

set_option synthInstance.maxHeartbeats 200000

variable {F : Type*} [Field F] {q : ℕ}

/-! ### Building tight patterns -/

section Build

variable {α β : ℕ}

/-- Step 1 of the Proof of Proposition 7.5 in `q_bip_P3.md` (counting): blocks with
`|B_c| = λ'_c` (`c ≥ 1`) that are pairwise disjoint cover `|λ|` indices. -/
lemma card_sup_blocks {k : ℕ} {lam : Partition} {B : ℕ → Finset (Fin k)}
    (hB : ∀ c, 1 ≤ c → (B c).card = colLen lam c)
    (hBd : ∀ c, 1 ≤ c → ∀ c', 1 ≤ c' → c ≠ c' → Disjoint (B c) (B c')) {N : ℕ}
    (hN : lam.row 1 ≤ N) : ((Finset.Icc 1 N).sup B).card = lam.size := by
  have hBd' : ((Finset.Icc 1 N : Finset ℕ) : Set ℕ).PairwiseDisjoint B :=
    fun c hc c' hc' hne => hBd c (Finset.mem_Icc.1 hc).1 c' (Finset.mem_Icc.1 hc').1 hne
  rw [Finset.sup_eq_biUnion, Finset.card_biUnion hBd',
    Finset.sum_congr rfl (fun c hc => hB c (Finset.mem_Icc.1 hc).1), Lifts.sum_colLen_Icc lam hN]

/-- Step 1 of the Proof of Proposition 7.5 in `q_bip_P3.md`: a covering condition stated
elementwise. -/
lemma sup_eq_of_mem_iff {k N : ℕ} {B : ℕ → Finset (Fin k)} {s : Finset (Fin k)}
    (h : ∀ i, (∃ c ∈ Finset.Icc 1 N, i ∈ B c) ↔ i ∉ s) :
    (Finset.Icc 1 N).sup B = Finset.univ \ s := by
  ext i; rw [Finset.mem_sup, h]; simp

/-- Step 1 of the Proof of Proposition 7.5 in `q_bip_P3.md`: products of Vandermondes over blocks
vanishing above `λ_1` may be taken over `c = 1, …, N` for any `N ≥ λ_1`. -/
lemma prod_vand_extend {k : ℕ} {S : Type*} [CommRing S] (xx : Fin k → S) {lam : Partition}
    {B : ℕ → Finset (Fin k)} (hB : ∀ c, 1 ≤ c → (B c).card = colLen lam c) {N : ℕ}
    (hN : lam.row 1 ≤ N) :
    ∏ c ∈ Finset.Icc 1 (lam.row 1), vand xx (B c) = ∏ c ∈ Finset.Icc 1 N, vand xx (B c) := by
  refine Finset.prod_subset (Finset.Icc_subset_Icc le_rfl hN) (fun c hc hnc => ?_)
  simp only [Finset.mem_Icc, not_and, not_le] at hc hnc
  rw [Lifts.block_eq_empty hB (hnc hc.1)]
  simp [vand]

/-- Step 1 of the Proof of Proposition 7.5 in `q_bip_P3.md`: a tight pattern of
`λ = (λ_+, λ_−)` on `([α], [β])` (`q_bip_setting.md`) built from pairs `P` (first and second
indices pairwise distinct) and blocks `B^+_c`, `B^−_c` (`c ≥ 1`, with `|B^±_c| = (λ_±)'_c`, so
empty for `c > λ_{±,1}`), pairwise disjoint and covering the indices not used by `P`.  The number
of pairs `α − |λ_+|` is then automatic ("the number of pairs is unchanged / has grown by one" in
the cases of the Proof). -/
def mkBPattern (lam : Partition × Partition) (P : Finset (Fin α × Fin β))
    (BX : ℕ → Finset (Fin α)) (BZ : ℕ → Finset (Fin β)) (N : ℕ) (hN1 : lam.1.row 1 ≤ N)
    (hN2 : lam.2.row 1 ≤ N)
    (hfst : Set.InjOn Prod.fst (P : Set (Fin α × Fin β)))
    (hsnd : Set.InjOn Prod.snd (P : Set (Fin α × Fin β)))
    (hBX : ∀ c, 1 ≤ c → (BX c).card = colLen lam.1 c)
    (hBXd : ∀ c, 1 ≤ c → ∀ c', 1 ≤ c' → c ≠ c' → Disjoint (BX c) (BX c'))
    (hcovX : ∀ i, (∃ c ∈ Finset.Icc 1 N, i ∈ BX c) ↔ i ∉ P.image Prod.fst)
    (hBZ : ∀ c, 1 ≤ c → (BZ c).card = colLen lam.2 c)
    (hBZd : ∀ c, 1 ≤ c → ∀ c', 1 ≤ c' → c ≠ c' → Disjoint (BZ c) (BZ c'))
    (hcovZ : ∀ l, (∃ c ∈ Finset.Icc 1 N, l ∈ BZ c) ↔ l ∉ P.image Prod.snd) :
    BTightPattern lam α β where
  pairs := P
  card_pairs := by
    have h1 := card_sup_blocks hBX hBXd hN1
    rw [sup_eq_of_mem_iff hcovX, Finset.card_univ_diff, Fintype.card_fin,
      Finset.card_image_of_injOn hfst] at h1
    have h2 : P.card ≤ α := by
      rw [← Finset.card_image_of_injOn hfst]
      simpa using Finset.card_le_univ (P.image Prod.fst)
    omega
  inj_fst := hfst
  inj_snd := hsnd
  blocksX := BX
  card_blockX := fun c hc => hBX c (Finset.mem_Icc.1 hc).1
  blocksX_disjoint := fun c hc c' hc' hne =>
    hBXd c (Finset.mem_Icc.1 hc).1 c' (Finset.mem_Icc.1 hc').1 hne
  coverX := by rw [← Lifts.sup_blocks_eq hBX hN1]; exact sup_eq_of_mem_iff hcovX
  blocksZ := BZ
  card_blockZ := fun c hc => hBZ c (Finset.mem_Icc.1 hc).1
  blocksZ_disjoint := fun c hc c' hc' hne =>
    hBZd c (Finset.mem_Icc.1 hc).1 c' (Finset.mem_Icc.1 hc').1 hne
  coverZ := by rw [← Lifts.sup_blocks_eq hBZ hN2]; exact sup_eq_of_mem_iff hcovZ

/-- Step 1 of the Proof of Proposition 7.5 in `q_bip_P3.md`: the product of a pattern built with
`mkBPattern` is `Π_{(i,l) ∈ P} (x_i − z_l)^{q−1} · Π_{c=1}^{N} Δ(x_{B^+_c}) ·
Π_{c=1}^{N} Δ(z_{B^−_c})`. -/
theorem prod_mkBPattern (lam : Partition × Partition) (P : Finset (Fin α × Fin β))
    (BX : ℕ → Finset (Fin α)) (BZ : ℕ → Finset (Fin β)) (N : ℕ) (hN1 : lam.1.row 1 ≤ N)
    (hN2 : lam.2.row 1 ≤ N)
    (hfst : Set.InjOn Prod.fst (P : Set (Fin α × Fin β)))
    (hsnd : Set.InjOn Prod.snd (P : Set (Fin α × Fin β)))
    (hBX : ∀ c, 1 ≤ c → (BX c).card = colLen lam.1 c)
    (hBXd : ∀ c, 1 ≤ c → ∀ c', 1 ≤ c' → c ≠ c' → Disjoint (BX c) (BX c'))
    (hcovX : ∀ i, (∃ c ∈ Finset.Icc 1 N, i ∈ BX c) ↔ i ∉ P.image Prod.fst)
    (hBZ : ∀ c, 1 ≤ c → (BZ c).card = colLen lam.2 c)
    (hBZd : ∀ c, 1 ≤ c → ∀ c', 1 ≤ c' → c ≠ c' → Disjoint (BZ c) (BZ c'))
    (hcovZ : ∀ l, (∃ c ∈ Finset.Icc 1 N, l ∈ BZ c) ↔ l ∉ P.image Prod.snd) :
    (mkBPattern lam P BX BZ N hN1 hN2 hfst hsnd hBX hBXd hcovX hBZ hBZd hcovZ).prod F q =
      (∏ p ∈ P, (x F q p.1 - z F q p.2) ^ (q - 1)) *
        (∏ c ∈ Finset.Icc 1 N, vand (x F q) (BX c)) *
        ∏ c ∈ Finset.Icc 1 N, vand (z F q) (BZ c) := by
  unfold BTightPattern.prod
  simp only [mkBPattern]
  rw [prod_vand_extend _ hBX hN1, prod_vand_extend _ hBZ hN2]

end Build

/-! ### The blocks of a tight pattern -/

section Clean

variable {α β : ℕ} {μ : Partition × Partition}

/-- Step 1 of the Proof of Proposition 7.5 in `q_bip_P3.md`: the `x`-blocks `B^+_c` of a tight
pattern of `μ`, with the convention `B^+_c = ∅` for `c ∉ {1, …, μ_{+,1}}` (the file's "`S := ∅`
… when `c^*` is a new column"). -/
def cleanX (T : BTightPattern μ α β) (c : ℕ) : Finset (Fin α) :=
  if c ∈ Finset.Icc 1 (μ.1.row 1) then T.blocksX c else ∅

/-- Step 1 of the Proof of Proposition 7.5 in `q_bip_P3.md`: the `z`-blocks `B^−_c` of a tight
pattern of `μ`, with the convention `B^−_c = ∅` for `c ∉ {1, …, μ_{−,1}}`. -/
def cleanZ (T : BTightPattern μ α β) (c : ℕ) : Finset (Fin β) :=
  if c ∈ Finset.Icc 1 (μ.2.row 1) then T.blocksZ c else ∅

/-- Step 1 of the Proof of Proposition 7.5 in `q_bip_P3.md`: `|B^+_c| = (μ_+)'_c` for every `c ≥ 1`. -/
lemma card_cleanX (T : BTightPattern μ α β) {c : ℕ} (hc : 1 ≤ c) :
    (cleanX T c).card = colLen μ.1 c := by
  unfold cleanX
  split_ifs with h
  · exact T.card_blockX c h
  · simp only [Finset.mem_Icc, not_and, not_le] at h
    rw [Lifts.colLen_eq_zero μ.1 (h hc)]; rfl

/-- Step 1 of the Proof of Proposition 7.5 in `q_bip_P3.md`: `|B^−_c| = (μ_−)'_c` for every `c ≥ 1`. -/
lemma card_cleanZ (T : BTightPattern μ α β) {c : ℕ} (hc : 1 ≤ c) :
    (cleanZ T c).card = colLen μ.2 c := by
  unfold cleanZ
  split_ifs with h
  · exact T.card_blockZ c h
  · simp only [Finset.mem_Icc, not_and, not_le] at h
    rw [Lifts.colLen_eq_zero μ.2 (h hc)]; rfl

/-- Step 1 of the Proof of Proposition 7.5 in `q_bip_P3.md`: the `x`-blocks are pairwise disjoint. -/
lemma disjoint_cleanX (T : BTightPattern μ α β) {c c' : ℕ} (hne : c ≠ c') :
    Disjoint (cleanX T c) (cleanX T c') := by
  unfold cleanX
  split_ifs with h h'
  · exact T.blocksX_disjoint h h' hne
  all_goals simp

/-- Step 1 of the Proof of Proposition 7.5 in `q_bip_P3.md`: the `z`-blocks are pairwise disjoint. -/
lemma disjoint_cleanZ (T : BTightPattern μ α β) {c c' : ℕ} (hne : c ≠ c') :
    Disjoint (cleanZ T c) (cleanZ T c') := by
  unfold cleanZ
  split_ifs with h h'
  · exact T.blocksZ_disjoint h h' hne
  all_goals simp

/-- Step 1 of the Proof of Proposition 7.5 in `q_bip_P3.md`: the `x`-blocks `B^+_1, …, B^+_N` (`N ≥ μ_{+,1}`) cover exactly the first indices not used by the pairs. -/
lemma mem_cleanX_iff (T : BTightPattern μ α β) {N : ℕ} (hN : μ.1.row 1 ≤ N) (i : Fin α) :
    (∃ c ∈ Finset.Icc 1 N, i ∈ cleanX T c) ↔ i ∉ T.pairs.image Prod.fst := by
  have h : (Finset.Icc 1 N).sup (cleanX T) = Finset.univ \ T.pairs.image Prod.fst := by
    rw [Lifts.sup_blocks_eq (fun c hc => card_cleanX T hc) hN, ← T.coverX]
    exact Finset.sup_congr rfl (fun c hc => by simp [cleanX, hc])
  rw [← Finset.mem_sup, h]; simp

/-- Step 1 of the Proof of Proposition 7.5 in `q_bip_P3.md`: the `z`-blocks `B^−_1, …, B^−_N` (`N ≥ μ_{−,1}`) cover exactly the second indices not used by the pairs. -/
lemma mem_cleanZ_iff (T : BTightPattern μ α β) {N : ℕ} (hN : μ.2.row 1 ≤ N) (l : Fin β) :
    (∃ c ∈ Finset.Icc 1 N, l ∈ cleanZ T c) ↔ l ∉ T.pairs.image Prod.snd := by
  have h : (Finset.Icc 1 N).sup (cleanZ T) = Finset.univ \ T.pairs.image Prod.snd := by
    rw [Lifts.sup_blocks_eq (fun c hc => card_cleanZ T hc) hN, ← T.coverZ]
    exact Finset.sup_congr rfl (fun c hc => by simp [cleanZ, hc])
  rw [← Finset.mem_sup, h]; simp

/-- Step 1 of the Proof of Proposition 7.5 in `q_bip_P3.md`: the product `G` of a tight pattern of
`μ`, written with the blocks `B^±_1, …, B^±_N` for any `N ≥ μ_{+,1}, μ_{−,1}`. -/
lemma prod_clean (T : BTightPattern μ α β) {N : ℕ} (hN1 : μ.1.row 1 ≤ N) (hN2 : μ.2.row 1 ≤ N) :
    T.prod F q = (∏ p ∈ T.pairs, (x F q p.1 - z F q p.2) ^ (q - 1)) *
      (∏ c ∈ Finset.Icc 1 N, vand (x F q) (cleanX T c)) *
      ∏ c ∈ Finset.Icc 1 N, vand (z F q) (cleanZ T c) := by
  unfold BTightPattern.prod
  rw [← prod_vand_extend _ (fun c hc => card_cleanX T hc) hN1,
    ← prod_vand_extend _ (fun c hc => card_cleanZ T hc) hN2]
  have h1 : ∏ c ∈ Finset.Icc 1 (μ.1.row 1), vand (x F q (β := β)) (T.blocksX c) =
      ∏ c ∈ Finset.Icc 1 (μ.1.row 1), vand (x F q (β := β)) (cleanX T c) :=
    Finset.prod_congr rfl (fun c hc => by simp [cleanX, hc])
  have h2 : ∏ c ∈ Finset.Icc 1 (μ.2.row 1), vand (z F q (α := α)) (T.blocksZ c) =
      ∏ c ∈ Finset.Icc 1 (μ.2.row 1), vand (z F q (α := α)) (cleanZ T c) :=
    Finset.prod_congr rfl (fun c hc => by simp [cleanZ, hc])
  rw [h1, h2]

end Clean

/-! ### Lifting to `R_{α,β}` -/

section Lift

variable {α β : ℕ}

/-- **Setting** of `q_bip_P3.md`: the pairs of a tight pattern on `([α − 1], [β])`, read on the
indices `({2, …, α}, [β])`. -/
def liftP (P : Finset (Fin (α - 1) × Fin β)) : Finset (Fin α × Fin β) :=
  P.map (sh.prodMap (Function.Embedding.refl _))

/-- **Setting** of `q_bip_P3.md`: membership in the lifted pairs. -/
lemma mem_liftP {P : Finset (Fin (α - 1) × Fin β)} {p : Fin α × Fin β} :
    p ∈ liftP P ↔ ∃ p' ∈ P, (sh p'.1, p'.2) = p := by
  simp [liftP]

/-- **Setting** of `q_bip_P3.md`: an index of `[α]` is `1` or a shifted index `j + 1`, `j ∈ [α − 1]`. -/
lemma eq_zero_or_sh (hα : 1 ≤ α) (i : Fin α) : i = ⟨0, hα⟩ ∨ ∃ j : Fin (α - 1), i = sh j := by
  by_cases h : (i : ℕ) = 0
  · exact Or.inl (Fin.ext h)
  · exact Or.inr ⟨⟨i - 1, by omega⟩, Fin.ext (by simp [sh]; omega)⟩

/-- **Setting** of `q_bip_P3.md`: the lifted pairs do not involve the index `1` ("the new pair has a new first index `1`" in case (γ)). -/
lemma zero_notMem_image_fst_liftP (hα : 1 ≤ α) (P : Finset (Fin (α - 1) × Fin β)) :
    (⟨0, hα⟩ : Fin α) ∉ (liftP P).image Prod.fst := by
  simp only [Finset.mem_image, mem_liftP]
  rintro ⟨p, ⟨p', _, rfl⟩, h⟩
  exact sh_ne_zero hα _ h

/-- **Setting** of `q_bip_P3.md`: a shifted index is a first index of the lifted pairs iff the index is a first index of the pairs. -/
lemma sh_mem_image_fst_liftP (P : Finset (Fin (α - 1) × Fin β)) (j : Fin (α - 1)) :
    sh j ∈ (liftP P).image Prod.fst ↔ j ∈ P.image Prod.fst := by
  simp only [Finset.mem_image, mem_liftP]
  constructor
  · rintro ⟨p, ⟨p', hp', rfl⟩, h⟩; exact ⟨p', hp', sh.injective h⟩
  · rintro ⟨p', hp', rfl⟩; exact ⟨_, ⟨p', hp', rfl⟩, rfl⟩

/-- **Setting** of `q_bip_P3.md`: lifting the pairs does not change their second indices. -/
lemma image_snd_liftP (P : Finset (Fin (α - 1) × Fin β)) :
    (liftP P).image Prod.snd = P.image Prod.snd := by
  ext l; simp only [Finset.mem_image, mem_liftP]
  constructor
  · rintro ⟨p, ⟨p', hp', rfl⟩, h⟩; exact ⟨p', hp', h⟩
  · rintro ⟨p', hp', rfl⟩; exact ⟨_, ⟨p', hp', rfl⟩, rfl⟩

/-- **Setting** of `q_bip_P3.md`: the first indices of the lifted pairs are pairwise distinct. -/
lemma injOn_fst_liftP {μ : Partition × Partition} (T : BTightPattern μ (α - 1) β) :
    Set.InjOn Prod.fst (liftP T.pairs : Set (Fin α × Fin β)) := by
  intro a ha b hb h
  obtain ⟨a', ha', rfl⟩ := mem_liftP.1 ha
  obtain ⟨b', hb', rfl⟩ := mem_liftP.1 hb
  have := T.inj_fst ha' hb' (sh.injective h)
  rw [this]

/-- **Setting** of `q_bip_P3.md`: the second indices of the lifted pairs are pairwise distinct. -/
lemma injOn_snd_liftP {μ : Partition × Partition} (T : BTightPattern μ (α - 1) β) :
    Set.InjOn Prod.snd (liftP T.pairs : Set (Fin α × Fin β)) := by
  intro a ha b hb h
  obtain ⟨a', ha', rfl⟩ := mem_liftP.1 ha
  obtain ⟨b', hb', rfl⟩ := mem_liftP.1 hb
  have := T.inj_snd ha' hb' h
  rw [this]

/-- **Setting** of `q_bip_P3.md`: membership of a shifted index in a shifted block. -/
lemma mem_map_sh {B : Finset (Fin (α - 1))} (j : Fin (α - 1)) : sh j ∈ B.map sh ↔ j ∈ B :=
  Finset.mem_map' sh

/-- **Setting** of `q_bip_P3.md`: the index `1` is not in a shifted block. -/
lemma zero_notMem_map_sh (hα : 1 ≤ α) (B : Finset (Fin (α - 1))) :
    (⟨0, hα⟩ : Fin α) ∉ B.map sh := by
  simp only [Finset.mem_map]; rintro ⟨j, _, h⟩; exact sh_ne_zero hα j h

/-- **Setting** of `q_bip_P3.md`: `Δ(x_B)` of `R_{α−1,β}` read in `R_{α,β}` is `Δ(x_{B+1})`. -/
lemma liftR_vand_x (hα : 1 ≤ α) (B : Finset (Fin (α - 1))) :
    liftR (F := F) (q := q) α β hα (vand (x F q) B) = vand (x F q) (B.map sh) := by
  rw [map_vand, Lifts.vand_map_strictMono _ _ sh_strictMono]
  exact vand_congr (fun b _ => liftR_x hα b)

/-- **Setting** of `q_bip_P3.md`: `Δ(z_B)` of `R_{α−1,β}` read in `R_{α,β}` is `Δ(z_B)`. -/
lemma liftR_vand_z (hα : 1 ≤ α) (B : Finset (Fin β)) :
    liftR (F := F) (q := q) α β hα (vand (z F q) B) = vand (z F q) B := by
  rw [map_vand]
  exact vand_congr (fun b _ => liftR_z hα b)

/-- **Setting** of `q_bip_P3.md`: the pair factors of a tight pattern on `([α − 1], [β])` read in
`R_{α,β}` are the pair factors of the lifted pairs. -/
lemma liftR_prod_pairs (hα : 1 ≤ α) (P : Finset (Fin (α - 1) × Fin β)) :
    liftR (F := F) (q := q) α β hα (∏ p ∈ P, (x F q p.1 - z F q p.2) ^ (q - 1)) =
      ∏ p ∈ liftP P, (x F q p.1 - z F q p.2) ^ (q - 1) := by
  rw [map_prod, liftP, Finset.prod_map]
  refine Finset.prod_congr rfl (fun p _ => ?_)
  simp [liftR_x, liftR_z]

/-- **Cases (α) and (β)** of the Proof of Proposition 7.5 in `q_bip_P3.md`: let `T` be a tight
pattern of `μ` on `([α − 1], [β])` with product `G`, and let `λ_+` have the columns of `μ_+`
except that column `c* ≥ 1` is one longer.  Putting the index `1` into the block `S = B^+_{c*}`
(`S = ∅` if `c*` is a new column) gives a tight pattern of `λ = (λ_+, μ_−)` on `([α], [β])`
(the number of pairs is unchanged), whose product is
`Δ(x_{S ∪ {1}}) · (other factors) = Π_{s ∈ S} (x_s − w) · G` (part (iii) of
`q_P3_identities.md`, first identity; `G` read in `R_{α,β}`). -/
theorem exists_pattern_insert (hα : 1 ≤ α) {μ : Partition × Partition} {lam1 : Partition}
    (T : BTightPattern μ (α - 1) β) {cs : ℕ} (hcs : 1 ≤ cs)
    (hcol : ∀ c, 1 ≤ c → colLen lam1 c = colLen μ.1 c + if c = cs then 1 else 0) :
    ∃ T' : BTightPattern (lam1, μ.2) α β,
      T'.prod F q = (∏ s ∈ cleanX T cs, (x F q (sh s) - x F q ⟨0, hα⟩)) *
        liftR α β hα (T.prod F q) := by
  classical
  set x0 : Fin α := ⟨0, hα⟩ with hx0
  set N := lam1.row 1 + μ.1.row 1 + μ.2.row 1 + cs with hNdef
  set BX : ℕ → Finset (Fin α) := fun c =>
    if c = cs then insert x0 ((cleanX T c).map sh) else (cleanX T c).map sh with hBXdef
  have hBX : ∀ c, 1 ≤ c → (BX c).card = colLen (lam1, μ.2).1 c := by
    intro c hc
    show _ = colLen lam1 c
    rw [hcol c hc]
    by_cases h : c = cs
    · simp only [hBXdef, if_pos h]
      rw [Finset.card_insert_of_notMem (zero_notMem_map_sh hα _), Finset.card_map,
        card_cleanX T hc]
    · simp only [hBXdef, if_neg h, Finset.card_map, card_cleanX T hc, add_zero]
  have hBXd : ∀ c, 1 ≤ c → ∀ c', 1 ≤ c' → c ≠ c' → Disjoint (BX c) (BX c') := by
    intro c _ c' _ hne
    have hd : Disjoint ((cleanX T c).map sh) ((cleanX T c').map sh) :=
      (Finset.disjoint_map _).2 (disjoint_cleanX T hne)
    by_cases h : c = cs
    · have h' : c' ≠ cs := fun h' => hne (h.trans h'.symm)
      simp only [hBXdef, if_pos h, if_neg h']
      exact Finset.disjoint_insert_left.2 ⟨zero_notMem_map_sh hα _, hd⟩
    · by_cases h' : c' = cs
      · simp only [hBXdef, if_neg h, if_pos h']
        exact Finset.disjoint_insert_right.2 ⟨zero_notMem_map_sh hα _, hd⟩
      · simp only [hBXdef, if_neg h, if_neg h']; exact hd
  have hcovX : ∀ i, (∃ c ∈ Finset.Icc 1 N, i ∈ BX c) ↔ i ∉ (liftP T.pairs).image Prod.fst := by
    intro i
    rcases eq_zero_or_sh hα i with rfl | ⟨j, rfl⟩
    · refine iff_of_true ⟨cs, Finset.mem_Icc.2 ⟨hcs, by omega⟩, by
        simp only [hBXdef, if_true]; exact Finset.mem_insert_self _ _⟩
        (zero_notMem_image_fst_liftP hα _)
    · rw [sh_mem_image_fst_liftP, ← mem_cleanX_iff T (N := N) (by omega)]
      refine exists_congr (fun c => and_congr_right (fun _ => ?_))
      by_cases h : c = cs
      · simp only [hBXdef, if_pos h, Finset.mem_insert, mem_map_sh]
        exact or_iff_right (sh_ne_zero hα j)
      · simp only [hBXdef, if_neg h, mem_map_sh]
  have hcovZ : ∀ l, (∃ c ∈ Finset.Icc 1 N, l ∈ cleanZ T c) ↔
      l ∉ (liftP T.pairs).image Prod.snd := by
    intro l; rw [image_snd_liftP]; exact mem_cleanZ_iff T (by omega) l
  refine ⟨mkBPattern (lam1, μ.2) (liftP T.pairs) BX (cleanZ T) N (by simp; omega)
    (by simp; omega) (injOn_fst_liftP T) (injOn_snd_liftP T) hBX hBXd hcovX
    (fun c hc => card_cleanZ T hc) (fun c _ c' _ hne => disjoint_cleanZ T hne) hcovZ, ?_⟩
  have hcsN : cs ∈ Finset.Icc 1 N := Finset.mem_Icc.2 ⟨hcs, by omega⟩
  rw [prod_mkBPattern, prod_clean T (N := N) (by omega) (by omega), map_mul, map_mul,
    liftR_prod_pairs, map_prod, map_prod, ← Finset.mul_prod_erase _ _ hcsN,
    ← Finset.mul_prod_erase _ (fun c => liftR α β hα (vand (x F q) (cleanX T c))) hcsN]
  have e1 : BX cs = insert x0 ((cleanX T cs).map sh) := by simp [hBXdef]
  have e2 : ∏ c ∈ (Finset.Icc 1 N).erase cs, vand (x F q) (BX c) =
      ∏ c ∈ (Finset.Icc 1 N).erase cs, liftR α β hα (vand (x F q) (cleanX T c)) := by
    refine Finset.prod_congr rfl (fun c hc => ?_)
    rw [liftR_vand_x]; simp [hBXdef, Finset.ne_of_mem_erase hc]
  have e3 : vand (x F q) (insert x0 ((cleanX T cs).map sh)) =
      (∏ s ∈ cleanX T cs, (x F q (sh s) - x F q x0)) *
        liftR α β hα (vand (x F q) (cleanX T cs)) := by
    rw [vand_insert_of_lt _ _ _ (fun b hb => ?_), liftR_vand_x, Finset.prod_map]
    obtain ⟨b', _, rfl⟩ := Finset.mem_map.1 hb
    exact zero_lt_sh hα b'
  have e4 : ∏ c ∈ Finset.Icc 1 N, vand (z F q) (cleanZ T c) =
      ∏ c ∈ Finset.Icc 1 N, liftR α β hα (vand (z F q) (cleanZ T c)) :=
    Finset.prod_congr rfl (fun c _ => (liftR_vand_z hα _).symm)
  rw [e1, e2, e3, e4]
  ring

/-- **Case (γ)** of the Proof of Proposition 7.5 in `q_bip_P3.md`: let `T` be a tight pattern of
`μ` on `([α − 1], [β])`, let `λ_−` have the columns of `μ_−` except that column `c_0 ≥ 1` is one
shorter, let `S = B^−_{c_0}` and write `G = Δ(z_S) · G'` with
`G' = Π_{(i,l) ∈ P} (x_i − z_l)^{q−1} · Π_c Δ(x_{B^+_c}) · Π_{c ≠ c_0} Δ(z_{B^−_c})` (for any
`N ≥ λ_{−,1}, μ_{+,1}, μ_{−,1}, c_0`, the products over `c ∈ {1, …, N}`, resp. `{1, …, N} ∖ {c_0}`).
For `b ∈ S`, the pairs `P ∪ {(1, b)}`, the `x`-blocks `B^+_c`, the `z`-blocks `B^−_c` (`c ≠ c_0`)
and `S ∖ {b}` form a tight pattern of `λ = (μ_+, λ_−)` on `([α], [β])` (the number of pairs has
grown by one), with product `Δ(z_{S∖{b}}) · (w − z_b)^{q−1} · G'`. -/
theorem exists_pattern_pair (hα : 1 ≤ α) {μ : Partition × Partition} {lam2 : Partition}
    (T : BTightPattern μ (α - 1) β) {c0 : ℕ} (hc0 : 1 ≤ c0)
    (hcol : ∀ c, 1 ≤ c → colLen lam2 c + (if c = c0 then 1 else 0) = colLen μ.2 c)
    {N : ℕ} (hN1 : lam2.row 1 ≤ N) (hN2 : μ.1.row 1 ≤ N) (hN3 : μ.2.row 1 ≤ N) (hN4 : c0 ≤ N)
    {b : Fin β} (hb : b ∈ cleanZ T c0) :
    ∃ T' : BTightPattern (μ.1, lam2) α β,
      T'.prod F q = (x F q ⟨0, hα⟩ - z F q b) ^ (q - 1) *
        liftR α β hα (vand (z F q) ((cleanZ T c0).erase b) *
          ((∏ p ∈ T.pairs, (x F q p.1 - z F q p.2) ^ (q - 1)) *
            (∏ c ∈ Finset.Icc 1 N, vand (x F q) (cleanX T c)) *
            ∏ c ∈ (Finset.Icc 1 N).erase c0, vand (z F q) (cleanZ T c))) := by
  classical
  set x0 : Fin α := ⟨0, hα⟩ with hx0
  have hbP : b ∉ T.pairs.image Prod.snd :=
    (mem_cleanZ_iff T hN3 b).1 ⟨c0, Finset.mem_Icc.2 ⟨hc0, hN4⟩, hb⟩
  have hnotin : (x0, b) ∉ liftP T.pairs := fun h =>
    zero_notMem_image_fst_liftP hα T.pairs (Finset.mem_image.2 ⟨_, h, rfl⟩)
  set P := insert (x0, b) (liftP T.pairs) with hPdef
  have hfst : Set.InjOn Prod.fst (P : Set (Fin α × Fin β)) := by
    rw [hPdef, Finset.coe_insert, Set.injOn_insert (by exact_mod_cast hnotin)]
    refine ⟨injOn_fst_liftP T, ?_⟩
    rintro ⟨p, hp, hp'⟩
    exact zero_notMem_image_fst_liftP hα T.pairs (Finset.mem_image.2 ⟨p, hp, hp'⟩)
  have hsnd : Set.InjOn Prod.snd (P : Set (Fin α × Fin β)) := by
    rw [hPdef, Finset.coe_insert, Set.injOn_insert (by exact_mod_cast hnotin)]
    refine ⟨injOn_snd_liftP T, ?_⟩
    rintro ⟨p, hp, hp'⟩
    apply hbP
    rw [← image_snd_liftP]
    exact Finset.mem_image.2 ⟨p, hp, hp'⟩
  set BX : ℕ → Finset (Fin α) := fun c => (cleanX T c).map sh with hBXdef
  set BZ : ℕ → Finset (Fin β) := fun c =>
    if c = c0 then (cleanZ T c).erase b else cleanZ T c with hBZdef
  have hBZsub : ∀ c, BZ c ⊆ cleanZ T c := by
    intro c
    by_cases h : c = c0
    · simp only [hBZdef, if_pos h]; exact Finset.erase_subset _ _
    · simp only [hBZdef, if_neg h]; exact Finset.Subset.refl _
  have hBX : ∀ c, 1 ≤ c → (BX c).card = colLen (μ.1, lam2).1 c := by
    intro c hc
    simp only [hBXdef, Finset.card_map, card_cleanX T hc]
  have hBXd : ∀ c, 1 ≤ c → ∀ c', 1 ≤ c' → c ≠ c' → Disjoint (BX c) (BX c') :=
    fun c _ c' _ hne => (Finset.disjoint_map _).2 (disjoint_cleanX T hne)
  have hcovX : ∀ i, (∃ c ∈ Finset.Icc 1 N, i ∈ BX c) ↔ i ∉ P.image Prod.fst := by
    intro i
    rcases eq_zero_or_sh hα i with rfl | ⟨j, rfl⟩
    · refine iff_of_false ?_ (fun h => h (Finset.mem_image.2 ⟨(x0, b), by simp [hPdef], rfl⟩))
      rintro ⟨c, _, hc⟩
      exact zero_notMem_map_sh hα _ hc
    · have : sh j ∈ P.image Prod.fst ↔ sh j ∈ (liftP T.pairs).image Prod.fst := by
        rw [hPdef, Finset.image_insert, Finset.mem_insert]
        exact or_iff_right (sh_ne_zero hα j)
      rw [this, sh_mem_image_fst_liftP, ← mem_cleanX_iff T hN2]
      simp only [hBXdef, mem_map_sh]
  have hBZ : ∀ c, 1 ≤ c → (BZ c).card = colLen (μ.1, lam2).2 c := by
    intro c hc
    have := hcol c hc
    show _ = colLen lam2 c
    by_cases h : c = c0
    · subst h
      simp only [hBZdef, if_true, Finset.card_erase_of_mem hb, card_cleanZ T hc]
      simp at this; omega
    · simp only [hBZdef, if_neg h, card_cleanZ T hc]
      simp [h] at this; omega
  have hBZd : ∀ c, 1 ≤ c → ∀ c', 1 ≤ c' → c ≠ c' → Disjoint (BZ c) (BZ c') :=
    fun c _ c' _ hne => (disjoint_cleanZ T hne).mono (hBZsub c) (hBZsub c')
  have hcovZ : ∀ l, (∃ c ∈ Finset.Icc 1 N, l ∈ BZ c) ↔ l ∉ P.image Prod.snd := by
    intro l
    by_cases hl : l = b
    · subst hl
      refine iff_of_false ?_ (fun h => h (Finset.mem_image.2 ⟨(x0, l), by simp [hPdef], rfl⟩))
      rintro ⟨c, _, hc⟩
      by_cases h : c = c0
      · simp [hBZdef, h] at hc
      · simp only [hBZdef, if_neg h] at hc
        exact Finset.disjoint_left.1 (disjoint_cleanZ T h) hc hb
    · have : l ∈ P.image Prod.snd ↔ l ∈ T.pairs.image Prod.snd := by
        rw [hPdef, Finset.image_insert, Finset.mem_insert, image_snd_liftP]
        exact or_iff_right hl
      rw [this, ← mem_cleanZ_iff T hN3]
      refine exists_congr (fun c => and_congr_right (fun _ => ?_))
      by_cases h : c = c0
      · simp only [hBZdef, if_pos h, Finset.mem_erase]
        exact and_iff_right hl
      · simp only [hBZdef, if_neg h]
  refine ⟨mkBPattern (μ.1, lam2) P BX BZ N (by simp; omega) (by simp; omega) hfst hsnd hBX hBXd
    hcovX hBZ hBZd hcovZ, ?_⟩
  have hc0N : c0 ∈ Finset.Icc 1 N := Finset.mem_Icc.2 ⟨hc0, hN4⟩
  rw [prod_mkBPattern, hPdef, Finset.prod_insert hnotin,
    ← Finset.mul_prod_erase _ (fun c => vand (z F q) (BZ c)) hc0N]
  have e1 : vand (z F q) (BZ c0) = liftR α β hα (vand (z F q) ((cleanZ T c0).erase b)) := by
    rw [liftR_vand_z]; simp [hBZdef]
  have e2 : ∏ c ∈ (Finset.Icc 1 N).erase c0, vand (z F q) (BZ c) =
      liftR α β hα (∏ c ∈ (Finset.Icc 1 N).erase c0, vand (z F q) (cleanZ T c)) := by
    rw [map_prod]
    refine Finset.prod_congr rfl (fun c hc => ?_)
    rw [liftR_vand_z]; simp [hBZdef, Finset.ne_of_mem_erase hc]
  have e3 : ∏ c ∈ Finset.Icc 1 N, vand (x F q) (BX c) =
      liftR α β hα (∏ c ∈ Finset.Icc 1 N, vand (x F q) (cleanX T c)) := by
    rw [map_prod]
    exact Finset.prod_congr rfl (fun c _ => (liftR_vand_x hα _).symm)
  rw [e1, e2, e3, map_mul, map_mul, map_mul, liftR_prod_pairs]
  ring

end Lift

end BipP3

end

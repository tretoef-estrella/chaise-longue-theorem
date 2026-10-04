module

public import RequestProject.Odd3.Cases
public import RequestProject.Odd3.Count

/-!
# The Theorem of `q_odd3.md`, parts (ii), (iii), (iv) and (vi)

* (ii) `slices_pos`, `slice_zero`: the slice inclusions;
* (iii) `card_Z_le_finrank`: `dim_F I(m, J) ≥ |Z_J^{(m)}|`;
* (iv) `I_odd_one_eq_DIdeal`: `I(2k + 1, 1) = (D_J : J ∈ 𝒥)`;
* (vi) `O_ge_three`: `dim_F (D_J : J ∈ 𝒥) ≥ Q^e_k(4)`.

Part (i) is `card_Z_rec`, `card_Z_rec_zero` and part (v) is `card_Z_one_odd`
(`RequestProject/Odd3/Count.lean`).
-/

@[expose] public section

namespace Odd3

open Peel Tight

set_option synthInstance.maxHeartbeats 200000

variable {F : Type*} [Field F]

/-- **Theorem, part (ii)** of `q_odd3.md` (the slices), case `J ≥ 1`: for `m ≥ 1` and
`1 ≤ J ≤ m − 1`, with `W_j := W_j(I(m, J)) ⊆ C_{m−1}`:
`W_2 ⊇ I(m − 1, J + 1)`, `W_1 ⊇ I(m − 1, J)` and `W_0 ⊇ I(m − 1, J − 1)` (as sets in
`C_{m−1} = Peel.C F 4 (m − 1)`, whose variables `y_2, …, y_m` are those of the ideals
`I(m − 1, ·)`).  The proof is Cases I (`J ≡ m`) and II (`J ≢ m`) of the file. -/
theorem slices_pos {m : ℕ} (hm : 1 ≤ m) {J : ℕ} (hJ1 : 1 ≤ J) (hJ : J ≤ m - 1) :
    (I F (m - 1) (J + 1) : Set (C F 4 (m - 1))) ⊆ W hm (I F m J) 2 ∧
    (I F (m - 1) J : Set (C F 4 (m - 1))) ⊆ W hm (I F m J) 1 ∧
    (I F (m - 1) (J - 1) : Set (C F 4 (m - 1))) ⊆ W hm (I F m J) 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hJ' : J ≤ n := hJ
  by_cases hp : J % 2 = (n + 1) % 2
  · exact ⟨caseI_two hJ1 (by omega) hp, caseI_one hJ1 (by omega) hp,
      caseI_zero hJ1 (by omega) hp⟩
  · exact ⟨caseII_two hJ1 hJ' hp, caseII_one hJ1 hJ' hp, caseII_zero hJ1 hJ' hp⟩

/-- **Theorem, part (ii)** of `q_odd3.md` (the slices), case `J = 0`: for `m ≥ 1`,
`W_2(I(m, 0)) ⊇ I(m − 1, 1)`.  The proof is Case III of the file. -/
theorem slice_zero {m : ℕ} (hm : 1 ≤ m) :
    (I F (m - 1) 1 : Set (C F 4 (m - 1))) ⊆ W hm (I F m 0) 2 := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  exact caseIII n

/-- Proof of part (iii) of `q_odd3.md` (auxiliary): the inclusions of part (ii) for `J ≥ 1`, also
for `J ≥ m` (where `I(m, J) = C_m` and every slice is `C_{m−1}`), written with `m = n + 1`. -/
lemma slices_pos' (n : ℕ) {J : ℕ} (hJ1 : 1 ≤ J) :
    (I F n (J + 1) : Set (C F 4 n)) ⊆ Ws (I F (n + 1) J) 2 ∧
    (I F n J : Set (C F 4 n)) ⊆ Ws (I F (n + 1) J) 1 ∧
    (I F n (J - 1) : Set (C F 4 n)) ⊆ Ws (I F (n + 1) J) 0 := by
  by_cases hJ : J ≤ n
  · exact slices_pos (F := F) (m := n + 1) (by omega) hJ1 hJ
  · rw [I_top (m := n + 1) (by omega)]
    exact ⟨top_subset_W_top 2 le_rfl _, top_subset_W_top 1 (by norm_num) _,
      top_subset_W_top 0 (by norm_num) _⟩

/-- Proof of part (iii) of `q_odd3.md` (auxiliary): an inclusion of sets gives an inequality of
dimensions. -/
lemma finrank_le_of_subset {n : ℕ} (K : Ideal (C F 4 n)) (S : Submodule F (C F 4 n))
    (h : (K : Set (C F 4 n)) ⊆ S) :
    Module.finrank F (K.restrictScalars F) ≤ Module.finrank F S :=
  Submodule.finrank_mono (fun _ hx => h hx)

/-- **Theorem, part (iii)** of `q_odd3.md` (the dimension): for every field `F`, every `m ≥ 0`
and every `J ≥ 0`, `dim_F I(m, J) ≥ |Z_J^{(m)}|` (the dimension of the ideal `I(m, J)` regarded as
an `F`-subspace of `C_m`).  Induction on `m` by peeling: part (iii) of the peeling lemma
(`Peel.finrank_eq_sum`), part (ii) and part (i). -/
theorem card_Z_le_finrank (m J : ℕ) :
    (Z m J).card ≤ Module.finrank F ((I F m J).restrictScalars F) := by
  induction m generalizing J with
  | zero =>
    rw [I_top (Nat.zero_le J), Submodule.restrictScalars_top, finrank_top]
    haveI : Nontrivial (C F 4 0) := nontrivial_C (by norm_num)
    have h1 : (Z 0 J).card ≤ 1 := by
      have := Finset.card_le_univ (Z 0 J)
      simpa using this
    have h2 := Module.finrank_pos (R := F) (M := C F 4 0)
    omega
  | succ n ih =>
    rw [finrank_eq_sum (q := 4) (by norm_num) (m := n + 1) (by omega)]
    simp only [show 4 - 1 = 3 from rfl, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rcases Nat.eq_zero_or_pos J with rfl | hJ
    · rw [card_Z_succ_zero]
      have h2 := finrank_le_of_subset _ _ (caseIII (F := F) n)
      have := ih 1
      change _ ≤ Module.finrank F (Ws (I F (n + 1) 0) 0) +
        Module.finrank F (Ws (I F (n + 1) 0) 1) + Module.finrank F (Ws (I F (n + 1) 0) 2)
      omega
    · rw [card_Z_succ n J hJ]
      obtain ⟨s2, s1, s0⟩ := slices_pos' (F := F) n hJ
      have h2 := finrank_le_of_subset _ _ s2
      have h1 := finrank_le_of_subset _ _ s1
      have h0 := finrank_le_of_subset _ _ s0
      have := ih (J + 1)
      have := ih J
      have := ih (J - 1)
      change _ ≤ Module.finrank F (Ws (I F (n + 1) J) 0) +
        Module.finrank F (Ws (I F (n + 1) J) 1) + Module.finrank F (Ws (I F (n + 1) J) 2)
      omega

/-- Proof of part (iv) of `q_odd3.md` (auxiliary): a set `P` of `k` pairwise disjoint pairs of
`{1, …, 2k+1}` together with the free index `c` (as a block `{c}`) is a tight pattern of the
partition `(1)` in the sense of `q_P3_identities.md`; its product is `D_P`. -/
noncomputable def patternOfPairs {k : ℕ} (P : Finset (Finset (Fin (2 * k + 1)))) (hP : IsPairs P)
    (hc : P.card = k) (c : Fin (2 * k + 1)) (hcP : c ∉ supp P) :
    TightPattern TheoremB.one (Finset.univ : Finset (Fin (2 * k + 1))) where
  pairs := P
  blocks := fun _ => {c}
  size_le := by simp [TheoremB.size_one]
  even_sub := by simp only [Finset.card_univ, Fintype.card_fin, TheoremB.size_one]; exact ⟨k, by omega⟩
  card_pairs := by simp only [Finset.card_univ, Fintype.card_fin, TheoremB.size_one]; omega
  card_pair := hP.1
  pairs_disjoint := hP.2
  card_block := by
    intro c' hc'
    rw [TheoremB.one_row, Finset.Icc_self, Finset.mem_singleton] at hc'
    subst hc'
    simp [TheoremB.colLen_one]
  blocks_disjoint := by
    rw [TheoremB.one_row, Finset.Icc_self, Finset.coe_singleton]
    exact Set.pairwiseDisjoint_singleton _ _
  pairs_blocks_disjoint := by
    intro e he c' _
    rw [Finset.disjoint_singleton_right]
    exact fun h => hcP (mem_supp.2 ⟨e, he, h⟩)
  cover := by
    rw [TheoremB.one_row, Finset.Icc_self, Finset.sup_singleton]
    refine Finset.eq_univ_of_card _ ?_
    change (supp P ∪ {c}).card = _
    rw [Finset.card_union_of_disjoint (Finset.disjoint_singleton_right.2 hcP), card_supp hP,
      hc, Finset.card_singleton, Fintype.card_fin]

/-- **Theorem, part (iv)** of `q_odd3.md` (the ideal of the matchings): for `k ≥ 0`,
`I(2k + 1, 1) = (D_J : J ∈ 𝒥)·C_{2k+1}` (`TheoremB.DIdeal F 4 k`).  The generators `D_P`
(`|P| = k`) of `I(2k + 1, 1)` are the products of the tight patterns of `(1)` on `{1, …, 2k+1}`
(the free index forming the block), and these generate `(D_J : J ∈ 𝒥)` by part (i) of
`q_theorem_B_lower.md` (`TheoremB.VLamAll_one_eq_aux`, which holds for every `q`): this is the
correspondence `J ↦ P = J ∖ {{0, b}}` of the file. -/
theorem I_odd_one_eq_DIdeal (k : ℕ) : I F (2 * k + 1) 1 = TheoremB.DIdeal F 4 k := by
  rw [I_even' (by omega) (by omega), ← TheoremB.VLamAll_one_eq_aux]
  unfold VLamAll VLam
  congr 1
  ext g
  constructor
  · rintro ⟨P, hP, hc, rfl⟩
    have hc' : P.card = k := by rw [hc]; omega
    obtain ⟨c, hcP⟩ := exists_notMem (supp P) (by rw [card_supp hP]; omega)
    refine ⟨TheoremB.one, rfl, patternOfPairs P hP hc' c hcP, ?_⟩
    rw [TheoremB.prod_eq_prod_pairs]; rfl
  · rintro ⟨lam, hlam, T, rfl⟩
    rw [Set.mem_singleton_iff] at hlam
    subst hlam
    refine ⟨T.pairs, ⟨T.card_pair, T.pairs_disjoint⟩, ?_, ?_⟩
    · rw [T.card_pairs]; simp [TheoremB.size_one]
    · rw [TheoremB.prod_eq_prod_pairs]; rfl

/-- **Theorem, part (vi)** of `q_odd3.md` (Theorem O, `≥`, at `r = 3`): for every field `F` and
every `k ≥ 0`, `dim_F (D_J : J ∈ 𝒥)·C_{2k+1} ≥ Q^e_k(4)`, where the ideal is
`TheoremB.DIdeal F 4 k ⊆ C_{2k+1} = Peel.C F 4 (2k + 1)` regarded as an `F`-subspace.  By parts
(iv), (iii) with `(m, J) = (2k + 1, 1)`, and (v). -/
theorem O_ge_three (F : Type*) [Field F] (k : ℕ) :
    EvenCount.QkEven k 4 ≤ Module.finrank F ((TheoremB.DIdeal F 4 k).restrictScalars F) := by
  rw [← card_Z_one_odd, ← I_odd_one_eq_DIdeal]
  exact card_Z_le_finrank _ _

end Odd3

end

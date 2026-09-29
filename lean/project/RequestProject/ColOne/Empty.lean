module

public import RequestProject.ColOne.Transport

/-!
# The down-set `{∅}` of `Par_n` (`q_col_one.md`, proof of Lemma 6.6 (iii))

This file contains the combinatorial part of the **Proof** of Lemma 6.6 (iii) of `q_col_one.md`:
* `{∅}` is a down-set of `Par_n` for even `n` (`λ ≼ ∅` forces `λ = ∅`; `∅ ∈ Par_n`);
* a tight pattern of `∅` on `[n]` has `n/2` pairs and no blocks: it is a perfect matching `P`,
  with product `D_P`, so `V_{{∅}} = (D_P : P)·C_n`;
* `Z_{{∅}}` is the set of closed tuples.

The empty partition is `Bip.Partition'.empty` (`q_bip_setting.md`), tight patterns, `V_Λ`, `Par_n`,
down-sets, `Z_Λ` and closed tuples are those of `q_P3_identities.md`, `q_P3_lifts.md`,
`q_P1_fibres.md` and `q_theorem_B_lower.md`; perfect matchings of `[n]` are `ColComp.PerfMatch`.
-/

@[expose] public section

namespace ColOne

open ChainLemma Fibres Tight Lifts ColComp

open scoped Classical

/-- **Proof of Lemma 6.6 (iii)** of `q_col_one.md`: a partition of size `0` is the empty
partition. -/
theorem eq_empty_of_size_eq_zero (lam : Partition) (h : lam.size = 0) :
    lam = Bip.Partition'.empty := by
  ext1
  change lam.parts = []
  rcases hl : lam.parts with _ | ⟨x, l⟩
  · rfl
  · exfalso
    have hx := lam.pos x (by rw [hl]; exact List.mem_cons_self)
    have : lam.size = x + l.sum := by
      rw [Partition.size, hl, List.sum_cons]
    omega

/-- **Proof of Lemma 6.6 (iii)** of `q_col_one.md`: the set `{∅}` is a down-set of `Par_n` for even
`n` (`λ ≼ ∅` forces `λ = ∅`, and `∅ ∈ Par_n` as `n` is even). -/
theorem isDownSetPar_empty (h : ℕ) {n : ℕ} (hn : Even n) :
    IsDownSetPar h n {Bip.Partition'.empty} := by
  refine ⟨?_, ?_⟩
  · rintro _ rfl
    refine ⟨Nat.zero_le _, ?_, Nat.zero_le _⟩
    change 0 % 2 = n % 2
    rw [Nat.even_iff.1 hn]
  · rintro lam μ - hle rfl
    have h1 := hle (max 1 lam.len) (le_max_left _ _)
    rw [Partition.S_eq_size _ (le_max_right _ _),
      Partition.S_eq_size _ (by exact Nat.zero_le _)] at h1
    exact eq_empty_of_size_eq_zero lam (by
      have : Bip.Partition'.empty.size = 0 := rfl
      omega)

/-- **Proof of Lemma 6.6 (iii)** of `q_col_one.md`: `Z_{{∅}}` is the set of tuples in `T^n` whose
residue partition is empty, i.e. with `#{i : M_i = u} = #{i : M_i = −u}` for every `u`: the closed
tuples. -/
theorem ZLam_empty_eq {T : Type*} [Fintype T] [DecidableEq T] {h : ℕ} (S : FibreSetting T h)
    (n : ℕ) : S.ZLam n {Bip.Partition'.empty} = TheoremB.closedTuples S n := by
  ext M
  simp only [FibreSetting.ZLam, TheoremB.closedTuples, Finset.mem_filter, Finset.mem_univ,
    true_and, Set.mem_singleton_iff]
  constructor
  · intro hM u
    have h0 : (S.resPart M).size = 0 := by rw [hM]; rfl
    rw [TheoremB.size_resPart, Finset.sum_eq_zero_iff] at h0
    have h1 := h0 u (Finset.mem_univ _)
    have h2 := h0 (S.neg u) (Finset.mem_univ _)
    rw [S.neg_neg] at h2
    omega
  · intro hM
    apply eq_empty_of_size_eq_zero
    rw [TheoremB.size_resPart]
    exact Finset.sum_eq_zero fun u _ => by rw [hM u, Nat.sub_self]

/-! ### Tight patterns of `∅` are perfect matchings -/

variable (F : Type*) [Field F] (q : ℕ)

/-- **Proof of Lemma 6.6 (iii)** of `q_col_one.md`: `D_P = Π_{{a<b} ∈ P} D(y_a, y_b) ∈ C_n` for a
perfect matching `P` of `[n]` (pairs recorded by their smaller element). -/
noncomputable def DPn {n : ℕ} (P : PerfMatch (Fin n)) : Peel.C F q n :=
  ∏ a ∈ Finset.univ.filter (fun a => a < P.1 a), D F q a (P.1 a)

variable {F q}

section FromMatching

variable {n : ℕ} (P : PerfMatch (Fin n))

/-- **Proof of Lemma 6.6 (iii)** of `q_col_one.md`: the pair `{a, P(a)}` of a perfect matching. -/
def pairP (a : Fin n) : Finset (Fin n) := {a, P.1 a}

/-- **Proof of Lemma 6.6 (iii)** of `q_col_one.md`: two pairs `{a < P(a)}`, `{b < P(b)}` sharing an
element are equal. -/
theorem eq_of_mem_pairP {a b : Fin n} (ha : a < P.1 a) (hb : b < P.1 b) {x : Fin n}
    (hxa : x ∈ pairP P a) (hxb : x ∈ pairP P b) : a = b := by
  simp only [pairP, Finset.mem_insert, Finset.mem_singleton] at hxa hxb
  have hP := P.2
  rcases hxa with rfl | rfl <;> rcases hxb with h | h
  · exact h
  · have e : P.1 x = b := by rw [h, (hP b).2]
    rw [e] at ha
    rw [← h] at hb
    exact absurd (ha.trans hb) (lt_irrefl _)
  · have e : P.1 b = a := by rw [← h, (hP a).2]
    rw [h] at ha
    rw [e] at hb
    exact absurd (ha.trans hb) (lt_irrefl _)
  · rw [← (hP a).2, h, (hP b).2]

/-- **Proof of Lemma 6.6 (iii)** of `q_col_one.md`: `2·#{a : a < P(a)} = n` (the pairs of `P`
partition `[n]`). -/
theorem two_mul_card_filter : 2 * (Finset.univ.filter (fun a : Fin n => a < P.1 a)).card = n := by
  have hne : ∀ x, P.1 x ≠ x := fun x => (P.2 x).1
  have h1 : (Finset.univ.filter (fun a : Fin n => a < P.1 a)).card =
      (Finset.univ.filter (fun a : Fin n => ¬ a < P.1 a)).card := by
    refine Finset.card_nbij' P.1 P.1 ?_ ?_ ?_ ?_
    · intro x hx
      replace hx : x < P.1 x := by simpa using hx
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, (P.2 x).2]
      exact not_lt.2 hx.le
    · intro x hx
      replace hx : ¬ x < P.1 x := by simpa using hx
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, (P.2 x).2]
      exact lt_of_le_of_ne (not_lt.1 hx) (hne x)
    · intro x _; exact (P.2 x).2
    · intro x _; exact (P.2 x).2
  have h2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun a : Fin n => a < P.1 a)
  rw [Finset.card_univ, Fintype.card_fin] at h2
  omega

/-- **Proof of Lemma 6.6 (iii)** of `q_col_one.md`: the tight pattern of `∅` on `[n]` given by a
perfect matching `P` of `[n]` (its pairs, and no blocks). -/
noncomputable def patternOfPM : TightPattern Bip.Partition'.empty (Finset.univ : Finset (Fin n)) where
  pairs := (Finset.univ.filter (fun a => a < P.1 a)).image (pairP P)
  blocks := fun _ => ∅
  size_le := Nat.zero_le _
  even_sub := by
    simp only [Finset.card_univ, Fintype.card_fin]
    exact ⟨(Finset.univ.filter (fun a : Fin n => a < P.1 a)).card, by
      have := two_mul_card_filter P
      change n - 0 = _
      omega⟩
  card_pairs := by
    simp only [Finset.card_univ, Fintype.card_fin]
    rw [Finset.card_image_of_injOn (fun a ha b hb h => eq_of_mem_pairP P
      (by simpa using ha) (by simpa using hb) (x := a) (by simp [pairP])
      (by rw [← h]; simp [pairP]))]
    have := two_mul_card_filter P
    change _ = (n - 0) / 2
    omega
  card_pair := by
    intro e he
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 he
    exact Finset.card_pair (P.2 a).1.symm
  pairs_disjoint := by
    intro e he e' he' hne
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 he)
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 he')
    refine Finset.disjoint_left.2 fun x hx hx' => hne ?_
    rw [eq_of_mem_pairP P (by simpa using ha) (by simpa using hb) hx hx']
  card_block := by intro c hc; simp [show Bip.Partition'.empty.row 1 = 0 from rfl] at hc
  blocks_disjoint := by
    intro a ha
    simp [show Bip.Partition'.empty.row 1 = 0 from rfl] at ha
  pairs_blocks_disjoint := by intro e _ c _; exact Finset.disjoint_empty_right _
  cover := by
    ext x
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    left
    rw [Finset.mem_sup]
    rcases lt_or_gt_of_ne (P.2 x).1.symm with h | h
    · exact ⟨_, Finset.mem_image_of_mem _ (by simpa using h), by simp [pairP]⟩
    · refine ⟨pairP P (P.1 x), Finset.mem_image_of_mem _ (by simpa [(P.2 x).2] using h), ?_⟩
      simp [pairP, (P.2 x).2]

/-- **Proof of Lemma 6.6 (iii)** of `q_col_one.md`: the product of the tight pattern of `∅` given by
`P` is `D_P`. -/
theorem prod_patternOfPM : (patternOfPM P).prod F q = DPn F q P := by
  rw [TightPattern.prod, show Bip.Partition'.empty.row 1 = 0 from rfl]
  simp only [Finset.Icc_eq_empty_of_lt zero_lt_one, Finset.prod_empty, mul_one]
  show ∏ e ∈ (Finset.univ.filter (fun a => a < P.1 a)).image (pairP P), pairD F q e = _
  rw [Finset.prod_image (fun a ha b hb h => eq_of_mem_pairP P
      (by simpa using ha) (by simpa using hb) (x := a) (by simp [pairP])
      (by rw [← h]; simp [pairP]))]
  refine Finset.prod_congr rfl fun a ha => ?_
  exact TheoremB.pairD_of_lt F q (by simpa using ha)

end FromMatching

section FromPattern

variable {n : ℕ} (T : TightPattern Bip.Partition'.empty (Finset.univ : Finset (Fin n)))

/-- **Proof of Lemma 6.6 (iii)** of `q_col_one.md`: every index lies in a pair of a tight pattern of
`∅` (there are no blocks). -/
theorem exists_pair_mem_empty (x : Fin n) : ∃ e ∈ T.pairs, x ∈ e := by
  have hx : x ∈ T.pairs.sup id ∪ (Finset.Icc 1 (Bip.Partition'.empty.row 1)).sup T.blocks := by
    rw [T.cover]; exact Finset.mem_univ x
  rw [show Bip.Partition'.empty.row 1 = 0 from rfl, Finset.Icc_eq_empty_of_lt zero_lt_one,
    Finset.sup_empty, Finset.bot_eq_empty, Finset.union_empty] at hx
  obtain ⟨e, he, hxe⟩ := Finset.mem_sup.1 hx
  exact ⟨e, he, hxe⟩

/-- **Proof of Lemma 6.6 (iii)** of `q_col_one.md`: two pairs of the pattern sharing an index are
equal. -/
theorem eq_of_mem_pairs_empty {e1 e2 : Finset (Fin n)} (h1 : e1 ∈ T.pairs) (h2 : e2 ∈ T.pairs)
    {x : Fin n} (hx1 : x ∈ e1) (hx2 : x ∈ e2) : e1 = e2 :=
  T.pairs_disjoint.elim h1 h2 (fun hd => Finset.disjoint_left.1 hd hx1 hx2)

/-- **Proof of Lemma 6.6 (iii)** of `q_col_one.md`: the partner of an index in the pairs of a tight
pattern of `∅`. -/
noncomputable def partnerE (x : Fin n) : Fin n :=
  if h : ∃ y, y ≠ x ∧ ({x, y} : Finset (Fin n)) ∈ T.pairs then h.choose else x

/-- **Proof of Lemma 6.6 (iii)** of `q_col_one.md`: `{x, partner x}` is the pair containing `x`. -/
theorem partnerE_spec (x : Fin n) :
    partnerE T x ≠ x ∧ ({x, partnerE T x} : Finset (Fin n)) ∈ T.pairs := by
  have hex : ∃ y, y ≠ x ∧ ({x, y} : Finset (Fin n)) ∈ T.pairs := by
    obtain ⟨e, he, hxe⟩ := exists_pair_mem_empty T x
    obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.1 (T.card_pair e he)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxe
    rcases hxe with rfl | rfl
    · exact ⟨v, huv.symm, he⟩
    · exact ⟨u, huv, by rwa [Finset.pair_comm]⟩
  rw [partnerE, dif_pos hex]
  exact hex.choose_spec

/-- **Proof of Lemma 6.6 (iii)** of `q_col_one.md`: the partner is unique. -/
theorem eq_partnerE {x y : Fin n} (hxy : y ≠ x) (h : ({x, y} : Finset (Fin n)) ∈ T.pairs) :
    y = partnerE T x := by
  obtain ⟨_, h2⟩ := partnerE_spec T x
  have := eq_of_mem_pairs_empty T h h2 (x := x) (by simp) (by simp)
  have hy : y ∈ ({x, partnerE T x} : Finset (Fin n)) := this ▸ (by simp)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with h | h
  · exact absurd h hxy
  · exact h

/-- **Proof of Lemma 6.6 (iii)** of `q_col_one.md`: the perfect matching of `[n]` given by a tight
pattern of `∅` (`x ↦` its partner). -/
noncomputable def pmOfPattern : PerfMatch (Fin n) :=
  ⟨partnerE T, fun x => ⟨(partnerE_spec T x).1, by
    obtain ⟨h1, h2⟩ := partnerE_spec T x
    rw [Finset.pair_comm] at h2
    exact (eq_partnerE T h1.symm h2).symm⟩⟩

/-- **Proof of Lemma 6.6 (iii)** of `q_col_one.md`: the matching obtained from a tight pattern of `∅`
has `D_P` equal to the product of the pattern. -/
theorem DPn_pmOfPattern : DPn F q (pmOfPattern T) = T.prod F q := by
  rw [TightPattern.prod, show Bip.Partition'.empty.row 1 = 0 from rfl]
  simp only [Finset.Icc_eq_empty_of_lt zero_lt_one, Finset.prod_empty, mul_one]
  refine Finset.prod_nbij (pairP (pmOfPattern T)) ?_ ?_ ?_ ?_
  · intro a _
    exact (partnerE_spec T a).2
  · intro a ha b hb h
    exact eq_of_mem_pairP _ (by simpa using ha) (by simpa using hb) (x := a) (by simp [pairP])
      (by rw [← h]; simp [pairP])
  · intro e he
    obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.1 (T.card_pair e he)
    wlog hlt : u < v generalizing u v
    · have hvu : v < u := lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm huv)
      rw [Finset.pair_comm]
      exact this v u (Ne.symm huv) (by rwa [Finset.pair_comm]) hvu
    have hv : v = partnerE T u := eq_partnerE T (Ne.symm huv) he
    refine ⟨u, ?_, ?_⟩
    · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
      change u < partnerE T u
      rw [← hv]; exact hlt
    · simp only [pairP]
      change {u, partnerE T u} = _
      rw [← hv]
  · intro a ha
    exact (TheoremB.pairD_of_lt F q (by simpa using ha)).symm

end FromPattern

/-- **Proof of Lemma 6.6 (iii)** of `q_col_one.md`: `V_{{∅}} = (D_P : P a perfect matching of [n])`
in `C_n`, since the generators of the two ideals are the same set. -/
theorem VLamAll_empty_eq (n : ℕ) :
    VLamAll F q n {Bip.Partition'.empty} =
      Ideal.span (Set.range fun P : PerfMatch (Fin n) => DPn F q P) := by
  unfold VLamAll VLam
  congr 1
  ext g
  constructor
  · rintro ⟨lam, hlam, T, rfl⟩
    rw [Set.mem_singleton_iff] at hlam
    subst hlam
    exact ⟨pmOfPattern T, DPn_pmOfPattern T⟩
  · rintro ⟨P, rfl⟩
    exact ⟨_, rfl, patternOfPM P, prod_patternOfPM P⟩

end ColOne

end

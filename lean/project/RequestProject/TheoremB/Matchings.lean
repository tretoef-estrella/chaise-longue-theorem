module

public import RequestProject.TheoremB.Root

/-!
# Part (i) of the Theorem of `q_theorem_B_lower.md`: `V_{(1)} = (D_J : J ∈ 𝒥)`

Tight patterns of `(1)` on `{1, …, n'}` versus perfect matchings of `{0, 1, …, n'}`.
-/

@[expose] public section

namespace TheoremB

open ChainLemma Fibres Tight Lifts

set_option synthInstance.maxHeartbeats 200000

variable {k : ℕ}

/-- Proof of part (i) of `q_theorem_B_lower.md` (auxiliary): the element `a = x + 1` of the
ground set `{0, 1, …, n'}` corresponding to the index `x` of the variable `y_{x+1}`. -/
def sc (x : Fin (2 * k + 1)) : Fin (2 * k + 2) := ⟨x.val + 1, by omega⟩

/-- Proof of part (i) of `q_theorem_B_lower.md` (auxiliary): `idx (x + 1) = x`. -/
lemma idx_sc (x : Fin (2 * k + 1)) : idx (sc x) = x := by
  ext; simp [idx, sc]

/-- Proof of part (i) of `q_theorem_B_lower.md` (auxiliary): a nonzero element of the ground set has nonzero value. -/
lemma val_ne_zero_of_ne {a : Fin (2 * k + 2)} (ha : a ≠ 0) : a.val ≠ 0 :=
  fun h => ha (Fin.ext (by simpa using h))

/-- Proof of part (i) of `q_theorem_B_lower.md` (auxiliary): `(a − 1) + 1 = a` for `a ≠ 0`. -/
lemma sc_idx {a : Fin (2 * k + 2)} (ha : a ≠ 0) : sc (idx a) = a := by
  have := val_ne_zero_of_ne ha
  ext; simp [idx, sc]; omega

/-- Proof of part (i) of `q_theorem_B_lower.md` (auxiliary): `x + 1 ≠ 0`. -/
lemma sc_ne_zero (x : Fin (2 * k + 1)) : sc x ≠ 0 := by
  intro h
  have := congrArg Fin.val h
  simp [sc] at this

/-- Proof of part (i) of `q_theorem_B_lower.md` (auxiliary): `a ↦ a − 1` is injective on `{1, …, n'}`. -/
lemma idx_inj {a b : Fin (2 * k + 2)} (ha : a ≠ 0) (hb : b ≠ 0) (h : idx a = idx b) : a = b := by
  rw [← sc_idx ha, ← sc_idx hb, h]

/-- Proof of part (i) of `q_theorem_B_lower.md` (auxiliary): `a ↦ a − 1` is order preserving on `{1, …, n'}`. -/
lemma idx_lt_idx {a b : Fin (2 * k + 2)} (ha : a ≠ 0) (hb : b ≠ 0) : idx a < idx b ↔ a < b := by
  have := val_ne_zero_of_ne ha
  have := val_ne_zero_of_ne hb
  simp only [Fin.lt_def, idx]
  omega

/-- Proof of part (i) of `q_theorem_B_lower.md` (auxiliary): `x ↦ x + 1` is order preserving. -/
lemma sc_lt_sc {x y : Fin (2 * k + 1)} : sc x < sc y ↔ x < y := by
  rw [Fin.lt_def, Fin.lt_def]
  show x.val + 1 < y.val + 1 ↔ _
  omega

/-- Proof of part (i) of `q_theorem_B_lower.md` (auxiliary): the smaller elements `a` of the
pairs `{a < b}` of `J` avoiding `0` (the index set of the product `D_J`). -/
def pset (J : BallotBound.Matching k) : Finset (Fin (2 * k + 2)) :=
  Finset.univ.filter (fun a => a ≠ 0 ∧ J.1 a ≠ 0 ∧ a < J.1 a)

/-- Proof of part (i) of `q_theorem_B_lower.md` (auxiliary): the pair `{a, J a}` of `J`, as a
set of indices of variables. -/
def pairOf (J : BallotBound.Matching k) (a : Fin (2 * k + 2)) : Finset (Fin (2 * k + 1)) :=
  {idx a, idx (J.1 a)}

/-- Proof of part (i) of `q_theorem_B_lower.md` (auxiliary): membership in the index set of `D_J`. -/
lemma mem_pset {J : BallotBound.Matching k} {a : Fin (2 * k + 2)} :
    a ∈ pset J ↔ a ≠ 0 ∧ J.1 a ≠ 0 ∧ a < J.1 a := by
  simp [pset]

/-- Proof of part (i) of `q_theorem_B_lower.md` (auxiliary): distinct pairs of `J` are
disjoint. -/
lemma eq_of_mem_pairOf {J : BallotBound.Matching k} {a a' : Fin (2 * k + 2)} (ha : a ∈ pset J)
    (ha' : a' ∈ pset J) {x : Fin (2 * k + 1)} (hx : x ∈ pairOf J a) (hx' : x ∈ pairOf J a') :
    a = a' := by
  rw [mem_pset] at ha ha'
  simp only [pairOf, Finset.mem_insert, Finset.mem_singleton] at hx hx'
  have hJ := J.2
  rcases hx with rfl | rfl <;> rcases hx' with h | h
  · exact idx_inj ha.1 ha'.1 h
  · have e1 := idx_inj ha.1 ha'.2.1 h
    have e2 : J.1 a = a' := by rw [e1, (hJ a').2]
    have l1 := ha.2.2
    rw [e2] at l1
    have l2 := ha'.2.2
    rw [← e1] at l2
    exact absurd (lt_trans l1 l2) (lt_irrefl _)
  · have e1 := idx_inj ha.2.1 ha'.1 h
    have e2 : a = J.1 a' := by rw [← e1, (hJ a).2]
    have l1 := ha.2.2
    rw [e1] at l1
    have l2 := ha'.2.2
    rw [← e2] at l2
    exact absurd (lt_trans l1 l2) (lt_irrefl _)
  · have := idx_inj ha.2.1 ha'.2.1 h
    rw [← (hJ a).2, this, (hJ a').2]

/-- Proof of part (i) of `q_theorem_B_lower.md` (auxiliary): the two indices of a pair of `J` avoiding `0` are distinct. -/
lemma idx_ne_idx {J : BallotBound.Matching k} {a : Fin (2 * k + 2)} (ha : a ∈ pset J) :
    idx a ≠ idx (J.1 a) := by
  rw [mem_pset] at ha
  intro h
  exact (J.2 a).1 (idx_inj ha.2.1 ha.1 h.symm)

/-- Proof of part (i) of `q_theorem_B_lower.md` (auxiliary): `D(y_x, y_y)` is the factor of
the pair `{x < y}`. -/
lemma pairD_of_lt (F : Type*) [Field F] (q : ℕ) {m : ℕ} {x y : Fin m} (h : x < y) :
    pairD F q {x, y} = D F q x y := by
  have hne : ({x, y} : Finset (Fin m)).Nonempty := by simp
  have hmin : ({x, y} : Finset (Fin m)).min' hne = x :=
    le_antisymm (Finset.min'_le _ _ (by simp))
      (Finset.le_min' _ _ _ (by simp [h.le]))
  have hmax : ({x, y} : Finset (Fin m)).max' hne = y :=
    le_antisymm (Finset.max'_le _ _ _ (by simp [h.le])) (Finset.le_max' _ _ (by simp))
  rw [pairD, dif_pos hne, hmin, hmax]

/-- Proof of part (i) of `q_theorem_B_lower.md` (auxiliary): the first row of `(1)` is `1`. -/
lemma one_row : one.row 1 = 1 := rfl

/-- Proof of part (i) of `q_theorem_B_lower.md` (auxiliary): the first column of `(1)` has length `1`. -/
lemma colLen_one : colLen one 1 = 1 := rfl

/-- Proof of part (i) of `q_theorem_B_lower.md` (auxiliary): the Vandermonde of a one-element block is `1`. -/
lemma Delta_singleton (F : Type*) [Field F] (q : ℕ) {m : ℕ} (c : Fin m) :
    Delta F q {c} = 1 := by
  simp [Delta, vand, Finset.filter_singleton]

/-- Proof of part (i) of `q_theorem_B_lower.md` (auxiliary): `k` disjoint pairs covering all
indices but one, among `n` indices, satisfy `2k + 1 = n`. -/
lemma two_mul_card_add_one {n : ℕ} (P : Finset (Finset (Fin n))) (hcard : ∀ e ∈ P, e.card = 2)
    (hdisj : (P : Set (Finset (Fin n))).PairwiseDisjoint id) (c : Fin n)
    (hc : ∀ e ∈ P, c ∉ e) (hcov : ∀ x, x ≠ c → ∃ e ∈ P, x ∈ e) : 2 * P.card + 1 = n := by
  have hU : P.biUnion id = Finset.univ.erase c := by
    ext x
    simp only [Finset.mem_biUnion, id, Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · rintro ⟨e, he, hx⟩ rfl; exact hc e he hx
    · exact hcov x
  have h1 := Finset.card_biUnion (s := P) (t := id) (fun e he e' he' hne => hdisj he he' hne)
  rw [hU, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at h1
  have h2 : ∑ u ∈ P, (id u).card = ∑ u ∈ P, 2 := Finset.sum_congr rfl fun e he => hcard e he
  rw [h2, Finset.sum_const, smul_eq_mul] at h1
  have : 1 ≤ n := by have := c.2; omega
  omega

/-- Proof of part (i) of `q_theorem_B_lower.md` (auxiliary): a pair of `J` avoiding `0` has two indices. -/
lemma card_pairOf {J : BallotBound.Matching k} {a : Fin (2 * k + 2)} (ha : a ∈ pset J) :
    (pairOf J a).card = 2 :=
  Finset.card_pair (idx_ne_idx ha)

/-- Proof of part (i) of `q_theorem_B_lower.md` (auxiliary): the pairs of `J` avoiding `0` are pairwise disjoint. -/
lemma pairwiseDisjoint_pairOf (J : BallotBound.Matching k) :
    (((pset J).image (pairOf J) : Finset (Finset (Fin (2 * k + 1)))) :
      Set (Finset (Fin (2 * k + 1)))).PairwiseDisjoint id := by
  intro e he e' he' hne
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 he)
  obtain ⟨a', ha', rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 he')
  refine Finset.disjoint_left.2 fun x hx hx' => hne ?_
  rw [eq_of_mem_pairOf ha ha' hx hx']

/-- Proof of part (i) of `q_theorem_B_lower.md` (auxiliary): the partner `c` of `0` lies in no other pair of `J`. -/
lemma notMem_pairOf {J : BallotBound.Matching k} {a : Fin (2 * k + 2)} (ha : a ∈ pset J) :
    idx (J.1 0) ∉ pairOf J a := by
  have ha' := mem_pset.1 ha
  simp only [pairOf, Finset.mem_insert, Finset.mem_singleton, not_or]
  have hJ0 : J.1 0 ≠ 0 := (J.2 0).1
  constructor
  · intro h
    have := idx_inj ha'.1 hJ0 h.symm
    exact ha'.2.1 (by rw [this, (J.2 0).2])
  · intro h
    have := idx_inj ha'.2.1 hJ0 h.symm
    exact ha'.1 (by rw [← (J.2 a).2, this, (J.2 0).2])

/-- Proof of part (i) of `q_theorem_B_lower.md` (auxiliary): every index other than the partner `c` of `0` lies in a pair of `J` avoiding `0`. -/
lemma exists_mem_pairOf (J : BallotBound.Matching k) {x : Fin (2 * k + 1)}
    (hx : x ≠ idx (J.1 0)) : ∃ a ∈ pset J, x ∈ pairOf J a := by
  have hJ := J.2
  have hb : sc x ≠ 0 := sc_ne_zero x
  have hJb : J.1 (sc x) ≠ 0 := by
    intro h
    apply hx
    rw [← h, (hJ _).2, idx_sc]
  rcases lt_or_gt_of_ne (hJ (sc x)).1 with hlt | hlt
  · refine ⟨J.1 (sc x), mem_pset.2 ⟨hJb, by rw [(hJ _).2]; exact hb, by rw [(hJ _).2]; exact hlt⟩,
      ?_⟩
    simp [pairOf, (hJ _).2, idx_sc]
  · exact ⟨sc x, mem_pset.2 ⟨hb, hJb, hlt⟩, by simp [pairOf, idx_sc]⟩

/-- **Theorem, part (i)** of `q_theorem_B_lower.md`, second claim (every `J ∈ 𝒥` gives a tight
pattern): the tight pattern of `(1)` on `{1, …, n'}` obtained from a matching `J` by removing its
pair `{0, c}`, the other `k` pairs forming `P` and `{c}` being the block. -/
noncomputable def patternOf (J : BallotBound.Matching k) :
    TightPattern one (Finset.univ : Finset (Fin (2 * k + 1))) where
  pairs := (pset J).image (pairOf J)
  blocks := fun _ => {idx (J.1 0)}
  size_le := by simp [size_one]
  even_sub := by simp only [Finset.card_univ, Fintype.card_fin, size_one]; exact ⟨k, by omega⟩
  card_pairs := by
    simp only [Finset.card_univ, Fintype.card_fin, size_one]
    have := two_mul_card_add_one ((pset J).image (pairOf J))
      (fun e he => by obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 he; exact card_pairOf ha)
      (pairwiseDisjoint_pairOf J) (idx (J.1 0))
      (fun e he => by obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 he; exact notMem_pairOf ha)
      (fun x hx => by
        obtain ⟨a, ha, hxa⟩ := exists_mem_pairOf J hx
        exact ⟨_, Finset.mem_image_of_mem _ ha, hxa⟩)
    omega
  card_pair := by
    intro e he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 he
    exact card_pairOf ha
  pairs_disjoint := pairwiseDisjoint_pairOf J
  card_block := by
    intro c hc
    rw [one_row, Finset.Icc_self, Finset.mem_singleton] at hc
    subst hc
    simp [colLen_one]
  blocks_disjoint := by
    rw [one_row, Finset.Icc_self, Finset.coe_singleton]
    exact Set.pairwiseDisjoint_singleton _ _
  pairs_blocks_disjoint := by
    intro e he c _
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 he
    rw [Finset.disjoint_singleton_right]
    exact notMem_pairOf ha
  cover := by
    rw [one_row, Finset.Icc_self, Finset.sup_singleton]
    ext x
    simp only [Finset.mem_union, Finset.mem_univ, iff_true, Finset.mem_singleton]
    by_cases hx : x = idx (J.1 0)
    · exact Or.inr hx
    · obtain ⟨a, ha, hxa⟩ := exists_mem_pairOf J hx
      exact Or.inl (Finset.mem_sup.2 ⟨_, Finset.mem_image_of_mem _ ha, hxa⟩)

/-- Proof of part (i) of `q_theorem_B_lower.md` (auxiliary): the block of a tight pattern of
`(1)` is a single index `{c}`. -/
lemma exists_block (T : TightPattern one (Finset.univ : Finset (Fin (2 * k + 1)))) :
    ∃ c, T.blocks 1 = {c} :=
  Finset.card_eq_one.1 (by rw [T.card_block 1 (by simp [one_row]), colLen_one])

/-- Proof of part (i) of `q_theorem_B_lower.md` (auxiliary): the product of a tight pattern of
`(1)` is `D_P = Π_{{a<b}∈P} D(y_a, y_b)` (the Vandermonde of the one-element block is `1`). -/
lemma prod_eq_prod_pairs (F : Type*) [Field F] (q : ℕ)
    (T : TightPattern one (Finset.univ : Finset (Fin (2 * k + 1)))) :
    T.prod F q = ∏ e ∈ T.pairs, pairD F q e := by
  obtain ⟨c, hc⟩ := exists_block T
  rw [TightPattern.prod, one_row, Finset.Icc_self, Finset.prod_singleton, hc, Delta_singleton,
    mul_one]

/-- **Theorem, part (i)** of `q_theorem_B_lower.md`, second claim: the product of the tight
pattern obtained from `J` is `D_J`. -/
theorem prod_patternOf (F : Type*) [Field F] (q : ℕ) (J : BallotBound.Matching k) :
    (patternOf J).prod F q = DJ F q J := by
  rw [prod_eq_prod_pairs]
  show ∏ e ∈ (pset J).image (pairOf J), pairD F q e = _
  rw [Finset.prod_image (fun a ha a' ha' h => eq_of_mem_pairOf ha ha' (x := idx a)
    (by simp [pairOf]) (by rw [← h]; simp [pairOf]))]
  refine Finset.prod_congr rfl fun a ha => ?_
  have ha' := mem_pset.1 ha
  exact pairD_of_lt F q ((idx_lt_idx ha'.1 ha'.2.1).2 ha'.2.2)

section FromPattern

variable (T : TightPattern one (Finset.univ : Finset (Fin (2 * k + 1))))

/-- Proof of part (i) of `q_theorem_B_lower.md` (auxiliary): the index `c` of the block lies in no pair of `P`. -/
lemma notMem_pair {c : Fin (2 * k + 1)} (hc : T.blocks 1 = {c}) {e : Finset (Fin (2 * k + 1))}
    (he : e ∈ T.pairs) : c ∉ e := by
  have := T.pairs_blocks_disjoint e he 1 (by simp [one_row])
  rwa [hc, Finset.disjoint_singleton_right] at this

/-- Proof of part (i) of `q_theorem_B_lower.md` (auxiliary): every index other than `c` lies in a pair of `P`. -/
lemma exists_pair_mem {c : Fin (2 * k + 1)} (hc : T.blocks 1 = {c}) {x : Fin (2 * k + 1)}
    (hx : x ≠ c) : ∃ e ∈ T.pairs, x ∈ e := by
  have hx' : x ∈ T.pairs.sup id ∪ (Finset.Icc 1 (one.row 1)).sup T.blocks := by
    rw [T.cover]; exact Finset.mem_univ x
  rw [one_row, Finset.Icc_self, Finset.sup_singleton, hc, Finset.mem_union,
    Finset.mem_singleton] at hx'
  rcases hx' with h1 | h1
  · obtain ⟨e, he, hxe⟩ := Finset.mem_sup.1 h1
    exact ⟨e, he, hxe⟩
  · exact absurd h1 hx

/-- Proof of part (i) of `q_theorem_B_lower.md` (auxiliary): two pairs of `P` sharing an index are equal. -/
lemma eq_of_mem_pairs {e1 e2 : Finset (Fin (2 * k + 1))} (h1 : e1 ∈ T.pairs) (h2 : e2 ∈ T.pairs)
    {x : Fin (2 * k + 1)} (hx1 : x ∈ e1) (hx2 : x ∈ e2) : e1 = e2 :=
  T.pairs_disjoint.elim h1 h2 (fun hd => Finset.disjoint_left.1 hd hx1 hx2)

open Classical in
/-- **Theorem, part (i)** of `q_theorem_B_lower.md`, second claim (auxiliary): the partner of an
index `x ≠ c` in the pairs `P` of a tight pattern of `(1)` (and `x` itself for `x = c`). -/
noncomputable def partner (x : Fin (2 * k + 1)) : Fin (2 * k + 1) :=
  if h : ∃ y, y ≠ x ∧ ({x, y} : Finset (Fin (2 * k + 1))) ∈ T.pairs then h.choose else x

/-- Proof of part (i) of `q_theorem_B_lower.md` (auxiliary): `{x, partner x}` is the pair of `P` containing `x ≠ c`. -/
lemma partner_spec {c : Fin (2 * k + 1)} (hc : T.blocks 1 = {c}) {x : Fin (2 * k + 1)}
    (hx : x ≠ c) : partner T x ≠ x ∧ ({x, partner T x} : Finset (Fin (2 * k + 1))) ∈ T.pairs := by
  have hex : ∃ y, y ≠ x ∧ ({x, y} : Finset (Fin (2 * k + 1))) ∈ T.pairs := by
    obtain ⟨e, he, hxe⟩ := exists_pair_mem T hc hx
    obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.1 (T.card_pair e he)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxe
    rcases hxe with rfl | rfl
    · exact ⟨v, huv.symm, he⟩
    · exact ⟨u, huv, by rwa [Finset.pair_comm]⟩
  rw [partner, dif_pos hex]
  exact hex.choose_spec

/-- Proof of part (i) of `q_theorem_B_lower.md` (auxiliary): the partner is unique. -/
lemma eq_partner {c : Fin (2 * k + 1)} (hc : T.blocks 1 = {c}) {x y : Fin (2 * k + 1)}
    (hxy : y ≠ x) (h : ({x, y} : Finset (Fin (2 * k + 1))) ∈ T.pairs) : y = partner T x := by
  have hx : x ≠ c := fun hxc => notMem_pair T hc h (by simp [hxc])
  obtain ⟨_, h2⟩ := partner_spec T hc hx
  have := eq_of_mem_pairs T h h2 (x := x) (by simp) (by simp)
  have hy : y ∈ ({x, partner T x} : Finset (Fin (2 * k + 1))) := this ▸ (by simp)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with h | h
  · exact absurd h hxy
  · exact h

/-- Proof of part (i) of `q_theorem_B_lower.md` (auxiliary): the partner of `x ≠ c` is not `c`. -/
lemma partner_ne_c {c : Fin (2 * k + 1)} (hc : T.blocks 1 = {c}) {x : Fin (2 * k + 1)}
    (hx : x ≠ c) : partner T x ≠ c := by
  intro h
  exact notMem_pair T hc (partner_spec T hc hx).2 (by simp [h])

/-- Proof of part (i) of `q_theorem_B_lower.md` (auxiliary): the partner map is an involution off `c`. -/
lemma partner_partner {c : Fin (2 * k + 1)} (hc : T.blocks 1 = {c}) {x : Fin (2 * k + 1)}
    (hx : x ≠ c) : partner T (partner T x) = x := by
  obtain ⟨h1, h2⟩ := partner_spec T hc hx
  rw [Finset.pair_comm] at h2
  exact (eq_partner T hc h1.symm h2).symm

/-- **Theorem, part (i)** of `q_theorem_B_lower.md`, second claim: adding the pair `{0, c}` to the
pairs `P` of a tight pattern of `(1)` (whose block is `{c}`) gives a matching `J ∈ 𝒥`. -/
noncomputable def matchingOf {c : Fin (2 * k + 1)} (hc : T.blocks 1 = {c}) :
    BallotBound.Matching k :=
  ⟨fun a => if a = 0 then sc c else if idx a = c then 0 else sc (partner T (idx a)), by
    intro a
    by_cases ha : a = 0
    · subst ha
      simp only [if_true, sc_ne_zero, if_false, idx_sc]
      exact ⟨sc_ne_zero c, trivial⟩
    · by_cases hac : idx a = c
      · simp only [ha, hac, if_false, if_true]
        exact ⟨Ne.symm ha, by rw [← hac, sc_idx ha]⟩
      · simp only [ha, hac, if_false, sc_ne_zero, idx_sc, partner_ne_c T hc hac,
          partner_partner T hc hac, sc_idx ha, and_true]
        intro h
        apply (partner_spec T hc hac).1
        rw [← idx_sc (partner T (idx a)), h]⟩

/-- Proof of part (i) of `q_theorem_B_lower.md` (auxiliary): the values of the matching built from a tight pattern. -/
lemma matchingOf_apply {c : Fin (2 * k + 1)} (hc : T.blocks 1 = {c}) (a : Fin (2 * k + 2)) :
    (matchingOf T hc).1 a =
      if a = 0 then sc c else if idx a = c then 0 else sc (partner T (idx a)) := rfl

/-- **Theorem, part (i)** of `q_theorem_B_lower.md`, second claim: the matching `J` obtained
from a tight pattern of `(1)` has `D_J = D_P`, the product of the tight pattern. -/
theorem DJ_matchingOf (F : Type*) [Field F] (q : ℕ) {c : Fin (2 * k + 1)}
    (hc : T.blocks 1 = {c}) : DJ F q (matchingOf T hc) = T.prod F q := by
  rw [prod_eq_prod_pairs]
  show ∏ a ∈ pset (matchingOf T hc), _ = _
  set J := matchingOf T hc
  refine Finset.prod_nbij (pairOf J) ?_ ?_ ?_ ?_
  · intro a ha
    have ha' := mem_pset.1 ha
    have hac : idx a ≠ c := by
      intro h
      apply ha'.2.1
      rw [matchingOf_apply, if_neg ha'.1, if_pos h]
    have hJa : J.1 a = sc (partner T (idx a)) := by
      rw [matchingOf_apply, if_neg ha'.1, if_neg hac]
    rw [pairOf, hJa, idx_sc]
    exact (partner_spec T hc hac).2
  · intro a ha a' ha' h
    exact eq_of_mem_pairOf ha ha' (x := idx a) (by simp [pairOf]) (by rw [← h]; simp [pairOf])
  · intro e he
    obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.1 (T.card_pair e he)
    wlog hlt : u < v generalizing u v
    · have hvu : v < u := lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm huv)
      rw [Finset.pair_comm]
      exact this v u (Ne.symm huv) (by rwa [Finset.pair_comm]) hvu
    have huc : u ≠ c := fun h => notMem_pair T hc he (by simp [h])
    have hv : v = partner T u := eq_partner T hc (Ne.symm huv) he
    have hJ : J.1 (sc u) = sc v := by
      rw [matchingOf_apply, if_neg (sc_ne_zero u), idx_sc, if_neg huc, hv]
    refine ⟨sc u, mem_pset.2 ⟨sc_ne_zero u, ?_, ?_⟩, ?_⟩
    · rw [hJ]; exact sc_ne_zero v
    · rw [hJ]; exact sc_lt_sc.2 hlt
    · simp only [pairOf, hJ, idx_sc]
  · intro a ha
    have ha' := mem_pset.1 ha
    exact (pairD_of_lt F q ((idx_lt_idx ha'.1 ha'.2.1).2 ha'.2.2)).symm

end FromPattern

/-- **Theorem, part (i)**, second claim, of `q_theorem_B_lower.md`: `V_{(1)} = (D_J : J ∈ 𝒥)`,
since the generators of the two ideals are the same set. -/
theorem VLamAll_one_eq_aux (F : Type*) [Field F] (q k : ℕ) :
    VLamAll F q (2 * k + 1) {one} = DIdeal F q k := by
  unfold VLamAll VLam DIdeal
  congr 1
  ext g
  constructor
  · rintro ⟨lam, hlam, T, rfl⟩
    rw [Set.mem_singleton_iff] at hlam
    subst hlam
    obtain ⟨c, hc⟩ := exists_block T
    exact ⟨matchingOf T hc, DJ_matchingOf T F q hc⟩
  · rintro ⟨J, rfl⟩
    exact ⟨one, rfl, patternOf J, prod_patternOf F q J⟩

end TheoremB

end

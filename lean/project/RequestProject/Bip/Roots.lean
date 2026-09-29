module

public import RequestProject.Bip.Defs

/-!
# Down-sets and root ideals in Lemma 7.2 of `q_bip_setting.md`

The down-set statements and the identities `V_{{(∅,∅)}} = I^{bal}_a`, `V_{{((1),∅)}} = I^{ph}_a`
of parts (i) and (ii) of **Lemma 7.2** of `q_bip_setting.md`.
-/

@[expose] public section

namespace Bip

open ChainLemma Tight

set_option synthInstance.maxHeartbeats 200000

/-! ### Down-sets -/

/-- A partition `λ ≼ ∅` is empty (proof of **Lemma 7.2 (i), (ii)** of `q_bip_setting.md`:
`S_1(λ) ≤ 0` forces `λ = ∅`). -/
theorem eq_empty_of_weakDom_empty {lam : Partition} (h : lam ≼ Partition'.empty) :
    lam = Partition'.empty := by
  have h1 := h 1 le_rfl
  simp only [Partition.S, Finset.Icc_self, Finset.sum_singleton, Partition.row] at h1
  ext1
  change lam.parts = []
  rcases hl : lam.parts with _ | ⟨b, l⟩
  · rfl
  · have hb := lam.pos b (by rw [hl]; exact List.mem_cons_self)
    rw [hl] at h1
    simp [Partition'.empty] at h1
    omega

/-- A partition of size `1` is `(1)` (proof of **Lemma 7.2 (ii)** of `q_bip_setting.md`). -/
theorem eq_one_of_size_eq_one {lam : Partition} (h : lam.size = 1) : lam = Partition'.one := by
  ext1
  change lam.parts = [1]
  have hpos := lam.pos
  unfold Partition.size at h
  rcases hl : lam.parts with _ | ⟨b, l⟩
  · rw [hl] at h; simp at h
  · rw [hl] at h hpos
    have hb := hpos b List.mem_cons_self
    simp only [List.sum_cons] at h
    rcases l with _ | ⟨c, l'⟩
    · simp at h; rw [h]
    · have hc := hpos c (by simp)
      simp only [List.sum_cons] at h
      omega

/-- **Lemma 7.2 (i)** of `q_bip_setting.md`, down-set part: `{(∅, ∅)}` is a down-set of
`BPar_q(a, a)`. -/
theorem isDownSetB_empty (q a : ℕ) :
    IsDownSetB q a a {(Partition'.empty, Partition'.empty)} := by
  refine ⟨?_, ?_⟩
  · rintro p rfl
    refine ⟨?_, ?_, ?_⟩ <;> simp [Partition'.empty, Partition.size, Partition.len]
  · rintro lam μ - ⟨h1, h2⟩ rfl
    rw [Set.mem_singleton_iff]
    exact Prod.ext (eq_empty_of_weakDom_empty h1) (eq_empty_of_weakDom_empty h2)

/-- **Lemma 7.2 (ii)** of `q_bip_setting.md`, down-set part: `{((1), ∅)}` is a down-set of
`BPar_q(a + 1, a)`.  Only `1 ≤ q` (a consequence of the Setting's `q ≥ 3`) is needed. -/
theorem isDownSetB_one {q : ℕ} (hq : 1 ≤ q) (a : ℕ) :
    IsDownSetB q (a + 1) a {(Partition'.one, Partition'.empty)} := by
  refine ⟨?_, ?_⟩
  · rintro p rfl
    refine ⟨?_, ?_, ?_⟩
    · simp [Partition'.one, Partition'.empty, Partition.size]
    · simp [Partition'.one, Partition'.empty, Partition.size]; omega
    · simpa [Partition'.one, Partition'.empty, Partition.len] using hq
  · rintro lam μ hlam ⟨-, h2⟩ rfl
    have he := eq_empty_of_weakDom_empty h2
    have hs := hlam.1
    rw [he] at hs
    have h0 : Partition'.empty.size = 0 := rfl
    rw [h0] at hs
    push_cast at hs
    have h1 : lam.1.size = 1 := by omega
    rw [Set.mem_singleton_iff]
    exact Prod.ext (eq_one_of_size_eq_one h1) he

/-! ### Sets of pairs as bijections -/

/-- A set `P` of pairs `(i, l)` with the `i` pairwise distinct and the `l` pairwise distinct,
`|P| = a` pairs, whose first coordinates are exactly the values of an injective map `e : ι → [n]`,
is the graph of a bijection `σ : ι ≃ [a]` (proof of **Lemma 7.2 (i), (ii)** of
`q_bip_setting.md`). -/
theorem exists_equiv_of_pairs {n a : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι → Fin n) (he : Function.Injective e) (P : Finset (Fin n × Fin a))
    (hfst : Set.InjOn Prod.fst (P : Set (Fin n × Fin a)))
    (hsnd : Set.InjOn Prod.snd (P : Set (Fin n × Fin a))) (hcard : P.card = a)
    (hrange : ∀ j, j ∈ P.image Prod.fst ↔ ∃ i, e i = j) :
    ∃ σ : ι ≃ Fin a, P = Finset.univ.image fun i => (e i, σ i) := by
  have hex : ∀ i, ∃ p ∈ P, p.1 = e i := fun i => by
    simpa using (hrange (e i)).2 ⟨i, rfl⟩
  choose p hpP hp1 using hex
  have hinj : Function.Injective fun i => (p i).2 := by
    intro i j hij
    have := hsnd (hpP i) (hpP j) hij
    apply he
    rw [← hp1 i, ← hp1 j, this]
  have hι : Fintype.card ι = a := by
    rw [← hcard, ← Finset.card_image_of_injOn hfst, ← Finset.card_univ,
      ← Finset.card_image_of_injective _ he]
    congr 1
    ext j
    rw [hrange]
    simp
  refine ⟨Equiv.ofBijective _ ((Fintype.bijective_iff_injective_and_card _).2
    ⟨hinj, by simp [hι]⟩), ?_⟩
  symm
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro x hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Equiv.ofBijective_apply] at hx
    obtain ⟨i, rfl⟩ := hx
    have : (e i, (p i).2) = p i := Prod.ext (hp1 i).symm rfl
    rw [this]
    exact hpP i
  · rw [hcard, Finset.card_image_of_injective, Finset.card_univ, hι]
    intro i j hij
    exact he (congrArg Prod.fst hij)

/-- Basic properties of the graph `{(e(i), σ(i))}` of a bijection (proof of
**Lemma 7.2 (i), (ii)** of `q_bip_setting.md`). -/
theorem graph_props {n a : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι → Fin n) (he : Function.Injective e) (σ : ι ≃ Fin a) :
    let P := Finset.univ.image fun i => (e i, σ i)
    P.card = a ∧ Set.InjOn Prod.fst (P : Set (Fin n × Fin a)) ∧
      Set.InjOn Prod.snd (P : Set (Fin n × Fin a)) ∧ P.image Prod.snd = Finset.univ ∧
      ∀ j, j ∈ P.image Prod.fst ↔ ∃ i, e i = j := by
  intro P
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective, Finset.card_univ, Fintype.card_congr σ, Fintype.card_fin]
    intro i j hij
    exact he (congrArg Prod.fst hij)
  · rintro _ hx _ hy hxy
    simp only [P, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx hy
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨j, rfl⟩ := hy
    simp only at hxy
    rw [he hxy]
  · rintro _ hx _ hy hxy
    simp only [P, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx hy
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨j, rfl⟩ := hy
    simp only at hxy
    rw [σ.injective hxy]
  · ext l
    simp only [P, Finset.mem_image, Finset.mem_univ, true_and, iff_true]
    exact ⟨_, ⟨σ.symm l, rfl⟩, by simp⟩
  · intro j
    simp only [P, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩; exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩; exact ⟨_, ⟨i, rfl⟩, rfl⟩

variable (F : Type*) [Field F] (q : ℕ)

/-- The product of `(x_i − z_l)^{q−1}` over the graph of a bijection (proof of
**Lemma 7.2 (i), (ii)** of `q_bip_setting.md`). -/
theorem prod_graph {α β : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι → Fin α) (he : Function.Injective e) (σ : ι ≃ Fin β) :
    ∏ p ∈ Finset.univ.image (fun i => (e i, σ i)), (x F q p.1 - z F q p.2) ^ (q - 1) =
      ∏ i, (x F q (e i) - z F q (σ i)) ^ (q - 1) := by
  rw [Finset.prod_image]
  intro i _ j _ hij
  exact he (congrArg Prod.fst hij)

/-! ### The root ideals -/

/-- **Lemma 7.2 (i)** of `q_bip_setting.md`, ideal part: `V_{{(∅,∅)}} = I^{bal}_a` in `R_{a,a}`
(the generators of the two ideals are the same). -/
theorem VLamB_empty_eq_Ibal (a : ℕ) :
    VLamB F q a a {(Partition'.empty, Partition'.empty)} = Ibal F q a := by
  unfold VLamB Ibal
  congr 1
  ext g
  simp only [Set.mem_singleton_iff, exists_eq_left, Set.mem_setOf_eq, Set.mem_range]
  have hrow : Partition'.empty.row 1 = 0 := rfl
  constructor
  · rintro ⟨T, rfl⟩
    have hc : T.pairs.card = a := T.card_pairs
    have himg : T.pairs.image Prod.fst = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [Finset.card_image_of_injOn T.inj_fst, hc, Fintype.card_fin]
    obtain ⟨σ, hσ⟩ := exists_equiv_of_pairs (ι := Fin a) id Function.injective_id T.pairs
      T.inj_fst T.inj_snd hc (fun j => by simp [himg])
    refine ⟨σ, ?_⟩
    unfold BTightPattern.prod
    simp only [hrow, Finset.Icc_eq_empty_of_lt zero_lt_one, Finset.prod_empty, mul_one]
    rw [hσ, prod_graph F q id Function.injective_id σ]
    rfl
  · rintro ⟨σ, rfl⟩
    obtain ⟨hcard, hf, hs, himg2, hr⟩ := graph_props (ι := Fin a) id Function.injective_id σ
    simp only [id_eq] at hcard hf hs himg2 hr
    have himg1 : (Finset.univ.image fun i : Fin a => (i, σ i)).image Prod.fst =
        Finset.univ := by
      ext j; simp
    refine ⟨{ pairs := Finset.univ.image fun i : Fin a => (i, σ i)
              card_pairs := by rw [hcard]; rfl
              inj_fst := hf
              inj_snd := hs
              blocksX := fun _ => ∅
              card_blockX := by simp [hrow]
              blocksX_disjoint := by simp [hrow]
              coverX := by simp [hrow, himg1]
              blocksZ := fun _ => ∅
              card_blockZ := by simp [hrow]
              blocksZ_disjoint := by simp [hrow]
              coverZ := by simp [hrow, himg2] }, ?_⟩
    unfold BTightPattern.prod
    simp only [hrow, Finset.Icc_eq_empty_of_lt zero_lt_one, Finset.prod_empty, mul_one]
    exact prod_graph F q id Function.injective_id σ

/-- **Lemma 7.2 (ii)** of `q_bip_setting.md`, ideal part: `V_{{((1),∅)}} = I^{ph}_a` in
`R_{a+1,a}` (the products of the tight patterns of `((1), ∅)` are exactly the generators of
`I^{ph}_a`). -/
theorem VLamB_one_eq_Iph (a : ℕ) :
    VLamB F q (a + 1) a {(Partition'.one, Partition'.empty)} = Iph F q a := by
  unfold VLamB Iph
  congr 1
  ext g
  simp only [Set.mem_singleton_iff, exists_eq_left, Set.mem_setOf_eq]
  have hrow0 : Partition'.empty.row 1 = 0 := rfl
  have hrow1 : Partition'.one.row 1 = 1 := rfl
  have hcol : colLen Partition'.one 1 = 1 := rfl
  have hsize : Partition'.one.size = 1 := rfl
  constructor
  · rintro ⟨T, rfl⟩
    have hc : T.pairs.card = a := by rw [T.card_pairs, hsize]; rfl
    have hB : (T.blocksX 1).card = 1 := by
      rw [T.card_blockX 1 (by simp [hrow1]), hcol]
    obtain ⟨i₀, hi₀⟩ := Finset.card_eq_one.1 hB
    have hcov := T.coverX
    simp only [hrow1, Finset.Icc_self, Finset.sup_singleton, hi₀] at hcov
    have hmem : ∀ j, j ∈ T.pairs.image Prod.fst ↔ j ≠ i₀ := by
      intro j
      have := congrArg (j ∈ ·) hcov
      simp only [Finset.mem_singleton, Finset.mem_sdiff, Finset.mem_univ, true_and,
        eq_iff_iff] at this
      rw [Ne, this, not_not]
    obtain ⟨σ, hσ⟩ := exists_equiv_of_pairs (ι := {i // i ≠ i₀}) Subtype.val
      Subtype.val_injective T.pairs T.inj_fst T.inj_snd hc
      (fun j => by rw [hmem]; exact ⟨fun h => ⟨⟨j, h⟩, rfl⟩, by rintro ⟨i, rfl⟩; exact i.2⟩)
    refine ⟨i₀, σ, ?_⟩
    unfold BTightPattern.prod
    simp only [hrow0, hrow1, Finset.Icc_eq_empty_of_lt zero_lt_one, Finset.prod_empty, mul_one,
      Finset.Icc_self, Finset.prod_singleton, hi₀]
    rw [hσ, prod_graph F q Subtype.val Subtype.val_injective σ]
    simp [vand, Finset.filter_singleton]
  · rintro ⟨i₀, σ, rfl⟩
    obtain ⟨hcard, hf, hs, himg2, hr⟩ :=
      graph_props (ι := {i // i ≠ i₀}) Subtype.val Subtype.val_injective σ
    have himg1 : Finset.univ \
        (Finset.univ.image fun i : {i // i ≠ i₀} => (i.1, σ i)).image Prod.fst = {i₀} := by
      ext j
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, hr, Finset.mem_singleton]
      constructor
      · intro h; by_contra h'; exact h ⟨⟨j, h'⟩, rfl⟩
      · rintro rfl ⟨i, hi⟩; exact i.2 hi
    refine ⟨{ pairs := Finset.univ.image fun i : {i // i ≠ i₀} => (i.1, σ i)
              card_pairs := by rw [hcard, hsize]; rfl
              inj_fst := hf
              inj_snd := hs
              blocksX := fun _ => {i₀}
              card_blockX := by
                intro c hc
                simp only [hrow1, Finset.Icc_self, Finset.mem_singleton] at hc
                subst hc
                simp [hcol]
              blocksX_disjoint := by simp [hrow1]
              coverX := by simp [hrow1, himg1]
              blocksZ := fun _ => ∅
              card_blockZ := by simp [hrow0]
              blocksZ_disjoint := by simp [hrow0]
              coverZ := by simp [hrow0, himg2] }, ?_⟩
    unfold BTightPattern.prod
    simp only [hrow0, hrow1, Finset.Icc_eq_empty_of_lt zero_lt_one, Finset.prod_empty, mul_one,
      Finset.Icc_self, Finset.prod_singleton]
    rw [prod_graph F q Subtype.val Subtype.val_injective σ]
    simp [vand, Finset.filter_singleton]

end Bip

end

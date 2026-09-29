module

public import RequestProject.Bip.Defs

/-!
# Counting parts of Lemma 7.2 of `q_bip_setting.md`

Part (0) of **Lemma 7.2** (`λ(ξ, η) ∈ BPar_q(α, β)`), the shape characterizations and the counts
`|Z_Λ| = N_…(a, q)` of parts (i) and (ii), and part (iii) (`N_{ph}(a, q) = N_{bal}(a + 1, q)`).
-/

@[expose] public section

namespace Bip

open ChainLemma

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-! ### Auxiliary facts about counts and partitions -/

/-- `Σ_u X(u) = n` for a tuple `ξ ∈ Ω^n` (proofs of **Lemma 7.2** of `q_bip_setting.md`). -/
theorem sum_cnt {n : ℕ} (ξ : Fin n → Ω) : ∑ u, cnt ξ u = n := by
  unfold cnt
  rw [← Finset.card_eq_sum_card_fiberwise (f := ξ) (fun _ _ => Finset.mem_univ _),
    Finset.card_univ, Fintype.card_fin]

omit [Fintype Ω] in
/-- Counts of an appended tuple: `cnt (η, u) v = cnt η v + [u = v]` (proof of **Lemma 7.2 (iii)**
of `q_bip_setting.md`). -/
theorem cnt_snoc {n : ℕ} (η : Fin n → Ω) (u v : Ω) :
    cnt (Fin.snoc η u : Fin (n + 1) → Ω) v = cnt η v + if u = v then 1 else 0 := by
  unfold cnt
  simp only [Finset.card_filter]
  rw [Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

omit [Fintype Ω] in
/-- Transport of counts along a bijection `e : Ω ≃ Ω'` (auxiliary for **Lemma 7.2 (i), (ii)** of
`q_bip_setting.md`). -/
theorem cnt_comp {Ω' : Type*} [Fintype Ω'] [DecidableEq Ω'] (e : Ω ≃ Ω') {n : ℕ}
    (ξ : Fin n → Ω) (u : Ω') : cnt (e ∘ ξ) u = cnt ξ (e.symm u) := by
  unfold cnt
  congr 1
  ext i
  simp [Equiv.apply_eq_iff_eq_symm_apply]

/-- The number of points satisfying a condition `∀ u, r(X(u), Y(u))` depends only on `|Ω|`
(auxiliary for **Lemma 7.2 (i), (ii)** of `q_bip_setting.md`). -/
theorem card_filter_cnt_equiv {Ω' : Type*} [Fintype Ω'] [DecidableEq Ω'] (e : Ω ≃ Ω')
    (r : ℕ → ℕ → Prop) [DecidableRel r] (α β : ℕ) :
    (Finset.univ.filter fun p : (Fin α → Ω) × (Fin β → Ω) =>
        ∀ u, r (cnt p.1 u) (cnt p.2 u)).card =
      (Finset.univ.filter fun p : (Fin α → Ω') × (Fin β → Ω') =>
        ∀ u, r (cnt p.1 u) (cnt p.2 u)).card := by
  refine Finset.card_bij' (fun p _ => (e ∘ p.1, e ∘ p.2)) (fun p _ => (e.symm ∘ p.1, e.symm ∘ p.2))
    ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    intro u
    rw [cnt_comp, cnt_comp]
    exact hp _
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    intro u
    rw [cnt_comp, cnt_comp]
    simpa using hp (e u)
  · intro p _
    ext <;> simp
  · intro p _
    ext <;> simp

/-- If `Y ≤ X` pointwise and `Σ X = Σ Y + 1`, then `X = Y + δ_u` for some `u` (proofs of
**Lemma 7.2 (ii), (iii)** of `q_bip_setting.md`). -/
theorem exists_eq_add_single (X Y : Ω → ℕ) (hle : ∀ u, Y u ≤ X u)
    (hsum : ∑ u, X u = ∑ u, Y u + 1) : ∃ u, ∀ v, X v = Y v + if u = v then 1 else 0 := by
  have hD : ∑ u, (X u - Y u) = 1 := by
    rw [Finset.sum_tsub_distrib _ (fun u _ => hle u)]; omega
  obtain ⟨u, -, hu⟩ : ∃ u ∈ Finset.univ, X u - Y u ≠ 0 := by
    by_contra h
    push_neg at h
    rw [Finset.sum_eq_zero h] at hD
    exact zero_ne_one hD
  refine ⟨u, fun v => ?_⟩
  split_ifs with huv
  · subst huv
    have h1 : X u - Y u ≤ ∑ w, (X w - Y w) :=
      Finset.single_le_sum (f := fun u => X u - Y u) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ u)
    have := hle u
    omega
  · have h2 : ∑ w ∈ {u, v}, (X w - Y w) ≤ ∑ w, (X w - Y w) :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    rw [Finset.sum_pair huv] at h2
    have := hle v
    omega

/-- The size of `ofMultiset s` is the sum of `s` (proofs of **Lemma 7.2** of
`q_bip_setting.md`). -/
theorem ofMultiset_size (s : Multiset ℕ) : (Partition'.ofMultiset s).size = s.sum := by
  unfold Partition'.ofMultiset Partition.size
  simp only
  rw [← Multiset.sum_coe, Multiset.sort_eq]
  conv_rhs => rw [← Multiset.filter_add_not (0 < ·) s]
  have h0 : (Multiset.filter (fun a => ¬ 0 < a) s).sum = 0 :=
    Multiset.sum_eq_zero (by intro a ha; rw [Multiset.mem_filter] at ha; omega)
  rw [Multiset.sum_add, h0, add_zero]

/-- The length of `ofMultiset s` is at most the cardinality of `s` (proofs of **Lemma 7.2** of
`q_bip_setting.md`). -/
theorem ofMultiset_len_le (s : Multiset ℕ) : (Partition'.ofMultiset s).len ≤ Multiset.card s := by
  unfold Partition'.ofMultiset Partition.len
  simp only [Multiset.length_sort]
  exact Multiset.card_le_card (Multiset.filter_le _ _)

/-- `ofMultiset s` is the empty partition iff `s` has no positive element (proofs of
**Lemma 7.2 (i), (ii)** of `q_bip_setting.md`). -/
theorem ofMultiset_eq_empty_iff (s : Multiset ℕ) :
    Partition'.ofMultiset s = Partition'.empty ↔ ∀ a ∈ s, a = 0 := by
  constructor
  · intro h a ha
    have h1 := congrArg (·.parts) h
    simp only [Partition'.ofMultiset, Partition'.empty] at h1
    have h2 : Multiset.filter (0 < ·) s = 0 := by
      rw [← Multiset.sort_eq (Multiset.filter (0 < ·) s) (· ≥ ·), h1]; rfl
    by_contra hne
    have : a ∈ Multiset.filter (0 < ·) s := Multiset.mem_filter.2 ⟨ha, by omega⟩
    rw [h2] at this
    simp at this
  · intro h
    ext1
    simp only [Partition'.ofMultiset, Partition'.empty]
    rw [Multiset.filter_eq_nil.2 (fun a ha => by rw [h a ha]; omega), Multiset.sort_zero]

/-- `ofMultiset {1} = (1)` (proof of **Lemma 7.2 (ii)** of `q_bip_setting.md`). -/
theorem ofMultiset_one : Partition'.ofMultiset {1} = Partition'.one := by
  ext1
  simp only [Partition'.ofMultiset, Partition'.one]
  rw [Multiset.filter_singleton, if_pos (by norm_num), Multiset.sort_singleton]

/-- The size of `λ_+` (proofs of **Lemma 7.2** of `q_bip_setting.md`). -/
theorem shapePlus_size {α β : ℕ} (ξ : Fin α → Ω) (η : Fin β → Ω) :
    (shapePlus ξ η).size = ∑ u, if cnt η u < cnt ξ u then cnt ξ u - cnt η u else 0 := by
  rw [shapePlus, ofMultiset_size, ← Finset.sum_filter]
  rfl

/-- The size of `λ_−` (proofs of **Lemma 7.2** of `q_bip_setting.md`). -/
theorem shapeMinus_size {α β : ℕ} (ξ : Fin α → Ω) (η : Fin β → Ω) :
    (shapeMinus ξ η).size = ∑ u, if cnt ξ u < cnt η u then cnt η u - cnt ξ u else 0 := by
  rw [shapeMinus, ofMultiset_size, ← Finset.sum_filter]
  rfl

/-! ### Part (0) -/

/-- **Lemma 7.2 (0)** of `q_bip_setting.md`: for a finite set `Ω` with `|Ω| = q` and every point
`(ξ, η) ∈ Ω^α × Ω^β`, the shape `λ(ξ, η)` lies in `BPar_q(α, β)`.  (The Setting's hypotheses
`q ≥ 3` odd are not needed.) -/
theorem shape_mem_BPar {q α β : ℕ} (hΩ : Fintype.card Ω = q) (ξ : Fin α → Ω) (η : Fin β → Ω) :
    shape ξ η ∈ BPar q α β := by
  refine ⟨?_, ?_, ?_⟩
  · change ((shapePlus ξ η).size : ℤ) - (shapeMinus ξ η).size = α - β
    have h1 : ((∑ u, cnt ξ u : ℕ) : ℤ) = α := by rw [sum_cnt]
    have h2 : ((∑ u, cnt η u : ℕ) : ℤ) = β := by rw [sum_cnt]
    rw [shapePlus_size, shapeMinus_size, ← h1, ← h2]
    push_cast
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    split_ifs <;> push_cast <;> omega
  · change (shapePlus ξ η).size + (shapeMinus ξ η).size ≤ α + β
    have h1 := sum_cnt ξ
    have h2 := sum_cnt η
    rw [shapePlus_size, shapeMinus_size, ← Finset.sum_add_distrib]
    calc _ ≤ ∑ u, (cnt ξ u + cnt η u) := Finset.sum_le_sum fun u _ => by split_ifs <;> omega
      _ = α + β := by rw [Finset.sum_add_distrib, h1, h2]
  · change (shapePlus ξ η).len + (shapeMinus ξ η).len ≤ q
    refine le_trans (add_le_add (ofMultiset_len_le _) (ofMultiset_len_le _)) ?_
    simp only [Multiset.card_map, Finset.card_val]
    rw [← Finset.card_union_of_disjoint]
    · exact hΩ ▸ Finset.card_le_univ _
    · rw [Finset.disjoint_filter]
      intro u _ h1 h2
      omega

/-! ### Shape characterizations -/

/-- **Lemma 7.2 (i)** of `q_bip_setting.md` (proof): the shape of `(ξ, η)` is `(∅, ∅)` iff
`X(u) = Y(u)` for all `u`. -/
theorem shape_eq_empty_iff {α β : ℕ} (ξ : Fin α → Ω) (η : Fin β → Ω) :
    shape ξ η = (Partition'.empty, Partition'.empty) ↔ ∀ u, cnt ξ u = cnt η u := by
  simp only [shape, Prod.mk.injEq, shapePlus, shapeMinus, ofMultiset_eq_empty_iff,
    Multiset.mem_map, Finset.mem_val, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩ u
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have := h2 _ ⟨u, h, rfl⟩
      omega
    · have := h1 _ ⟨u, h, rfl⟩
      omega
  · intro h
    refine ⟨?_, ?_⟩ <;> rintro a ⟨u, hu, rfl⟩ <;> rw [h u] at hu ⊢ <;> omega

/-- **Lemma 7.2 (ii)** of `q_bip_setting.md` (proof): for `(ξ, η) ∈ Ω^{a+1} × Ω^a`, the shape is
`((1), ∅)` iff `Y(u) ≤ X(u)` for all `u`. -/
theorem shape_eq_one_iff {a : ℕ} (ξ : Fin (a + 1) → Ω) (η : Fin a → Ω) :
    shape ξ η = (Partition'.one, Partition'.empty) ↔ ∀ u, cnt η u ≤ cnt ξ u := by
  constructor
  · intro h u
    have h2 := congrArg Prod.snd h
    simp only [shape, shapeMinus, ofMultiset_eq_empty_iff, Multiset.mem_map, Finset.mem_val,
      Finset.mem_filter, Finset.mem_univ, true_and] at h2
    by_contra hlt
    push_neg at hlt
    have := h2 _ ⟨u, hlt, rfl⟩
    omega
  · intro hle
    obtain ⟨u, hu⟩ := exists_eq_add_single (cnt ξ) (cnt η) hle (by rw [sum_cnt, sum_cnt])
    have hfilt : (Finset.univ.filter fun v => cnt η v < cnt ξ v) = {u} := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      rw [hu v]
      split_ifs with h <;> [simp [h]; (constructor <;> intro h' <;> [omega; exact absurd h'.symm h])]
    refine Prod.ext ?_ ?_
    · change shapePlus ξ η = _
      rw [shapePlus, hfilt]
      simp only [Finset.singleton_val, Multiset.map_singleton]
      rw [hu u, if_pos rfl, show cnt η u + 1 - cnt η u = 1 by omega, ofMultiset_one]
    · change shapeMinus ξ η = _
      rw [shapeMinus, ofMultiset_eq_empty_iff]
      rintro b hb
      simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_filter, Finset.mem_univ,
        true_and] at hb
      obtain ⟨v, hv, -⟩ := hb
      have := hle v
      omega

/-! ### Counts -/

/-- **Lemma 7.2 (i)** of `q_bip_setting.md`, count: for a finite set `Ω` with `|Ω| = q`,
`|Z_{{(∅,∅)}}| = N_{bal}(a, q)` (the set `Z_{{(∅,∅)}}` taken in `Ω^a × Ω^a`). -/
theorem card_ZLam_empty {q : ℕ} (hΩ : Fintype.card Ω = q) (a : ℕ) :
    (ZLam Ω a a {(Partition'.empty, Partition'.empty)}).card = Nbal a q := by
  have e : Ω ≃ Fin q := Fintype.equivFinOfCardEq hΩ
  rw [Nbal]
  convert card_filter_cnt_equiv e (fun m n => m = n) a a using 2
  · ext p
    simp [ZLam, shape_eq_empty_iff]
  · ext p
    simp

/-- **Lemma 7.2 (ii)** of `q_bip_setting.md`, count: for a finite set `Ω` with `|Ω| = q`,
`|Z_{{((1),∅)}}| = N_{ph}(a, q)` (the set `Z_{{((1),∅)}}` taken in `Ω^{a+1} × Ω^a`). -/
theorem card_ZLam_one {q : ℕ} (hΩ : Fintype.card Ω = q) (a : ℕ) :
    (ZLam Ω (a + 1) a {(Partition'.one, Partition'.empty)}).card = Nph a q := by
  have e : Ω ≃ Fin q := Fintype.equivFinOfCardEq hΩ
  rw [Nph]
  convert card_filter_cnt_equiv e (fun m n => n ≤ m) (a + 1) a using 2
  · ext p
    simp [ZLam, shape_eq_one_iff]
  · ext p
    simp

/-- **Lemma 7.2 (iii)** of `q_bip_setting.md`: `N_{ph}(a, q) = N_{bal}(a + 1, q)`.  (The
Setting's hypotheses `q ≥ 3` odd are not needed.) -/
theorem Nph_eq_Nbal (a q : ℕ) : Nph a q = Nbal (a + 1) q := by
  symm
  unfold Nbal Nph
  refine Finset.card_bij (fun p _ => (p.1, Fin.init p.2)) ?_ ?_ ?_
  · rintro ⟨ξ, η'⟩ hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    intro u
    rw [hp u, ← Fin.snoc_init_self η', cnt_snoc, Fin.init_snoc]
    omega
  · rintro ⟨ξ, η₁⟩ h1 ⟨ξ', η₂⟩ h2 heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq] at h1 h2 heq
    obtain ⟨rfl, hinit⟩ := heq
    have hl : η₁ (Fin.last a) = η₂ (Fin.last a) := by
      have := h1 (η₁ (Fin.last a))
      rw [h2, ← Fin.snoc_init_self η₁, ← Fin.snoc_init_self η₂, cnt_snoc, cnt_snoc, hinit] at this
      simp only [Fin.snoc_last, if_true] at this
      by_contra hne
      rw [if_neg (Ne.symm hne)] at this
      omega
    refine Prod.ext rfl ?_
    rw [← Fin.snoc_init_self η₁, ← Fin.snoc_init_self η₂, hinit, hl]
  · rintro ⟨ξ, η⟩ hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨u, hu⟩ := exists_eq_add_single (cnt ξ) (cnt η) hp (by rw [sum_cnt, sum_cnt])
    refine ⟨(ξ, Fin.snoc η u), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro v
      rw [cnt_snoc, hu v]
    · simp [Fin.init_snoc]

end Bip

end

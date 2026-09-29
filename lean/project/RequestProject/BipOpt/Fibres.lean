module

public import RequestProject.BipOpt.Options

/-!
# Lemma 7.3 (ii) of `q_bip_options.md` (fibres)

For a tail `M'` with shape `μ`, the multiset `{λ(u, M') : u ∈ Ω}` equals the multiset
`{opt_p(μ) : p = 1, …, q}`, following the Proof of (ii) in `q_bip_options.md`: the values `u`
split into the `ℓ_−` values with `Y(u) > X(u)` (removals), the `ℓ_+` values with `X(u) > Y(u)`
(additions) and the `q − ℓ_+ − ℓ_−` values with `X(u) = Y(u)` (middle positions).
-/

@[expose] public section

namespace Bip

open ChainLemma ChainLemma.Partition

/-! ### Partitions as multisets -/

/-- Two partitions with the same multiset of parts are equal (proof of **Lemma 7.3 (ii)** of
`q_bip_options.md`: partitions are compared "after re-sorting"). -/
theorem eq_of_parts_coe {μ ν : Partition}
    (h : (μ.parts : Multiset ℕ) = (ν.parts : Multiset ℕ)) : μ = ν := by
  have hp : μ.parts.Perm ν.parts := Multiset.coe_eq_coe.1 h
  exact ChainLemma.Partition.ext (hp.eq_of_pairwise (fun a b _ _ h1 h2 => le_antisymm h2 h1)
    μ.sorted ν.sorted)

/-- The parts of `ofMultiset s` are the positive elements of `s` (proof of **Lemma 7.3 (ii)** of
`q_bip_options.md`). -/
theorem parts_ofMultiset (s : Multiset ℕ) :
    ((Partition'.ofMultiset s).parts : Multiset ℕ) = s.filter (0 < ·) := by
  simp only [Partition'.ofMultiset, Multiset.sort_eq]

/-- The parts of a partition, as a multiset, are positive (proof of **Lemma 7.3 (ii)** of
`q_bip_options.md`). -/
theorem filter_parts (μ : Partition) :
    (μ.parts : Multiset ℕ).filter (0 < ·) = μ.parts :=
  Multiset.filter_eq_self.2 fun a ha => μ.pos a ha

/-- Changing one entry of a list, as multisets (proof of **Lemma 7.3 (ii)** of
`q_bip_options.md`). -/
theorem coe_modify_add (L : List ℕ) (i : ℕ) (f : ℕ → ℕ) (h : i < L.length) :
    ((L.modify i f : List ℕ) : Multiset ℕ) + {L[i]} = (L : Multiset ℕ) + {f L[i]} := by
  induction L generalizing i with
  | nil => simp at h
  | cons a l ih =>
    cases i with
    | zero =>
      simp only [List.modify_zero_cons, List.getElem_cons_zero, ← Multiset.cons_coe,
        ← Multiset.singleton_add]
      abel
    | succ i =>
      simp only [List.modify_succ_cons, List.getElem_cons_succ, ← Multiset.cons_coe,
        Multiset.cons_add]
      rw [ih i (by simpa using h)]

/-- The partition `μ − e` at a part `k` of `μ`: remove one part `k` and add a part `k − 1`
(dropped if `0`), re-sorted (proof of **Lemma 7.3 (ii)** of `q_bip_options.md`). -/
def decP (μ : Partition) (k : ℕ) : Partition :=
  Partition'.ofMultiset ((μ.parts : Multiset ℕ).erase k + {k - 1})

/-- The partition `μ + e` at a part `k` of `μ`: remove one part `k` and add a part `k + 1`,
re-sorted (proof of **Lemma 7.3 (ii)** of `q_bip_options.md`). -/
def incP (μ : Partition) (k : ℕ) : Partition :=
  Partition'.ofMultiset ((μ.parts : Multiset ℕ).erase k + {k + 1})

/-- Characterization of `decP` (proof of **Lemma 7.3 (ii)** of `q_bip_options.md`). -/
theorem eq_decP {μ ν : Partition} {k : ℕ} (hk : k ∈ μ.parts)
    (h : (ν.parts : Multiset ℕ) + {k} = (μ.parts : Multiset ℕ) + ({k - 1} : Multiset ℕ).filter (0 < ·)) :
    ν = decP μ k := by
  apply eq_of_parts_coe
  rw [decP, parts_ofMultiset, Multiset.filter_add,
    Multiset.filter_eq_self.2 (fun a ha => μ.pos a (Multiset.mem_of_mem_erase ha))]
  rw [← Multiset.cons_erase (Multiset.mem_coe.2 hk), Multiset.cons_add,
    ← Multiset.singleton_add, add_comm] at h
  exact add_left_cancel h

/-- Characterization of `incP` (proof of **Lemma 7.3 (ii)** of `q_bip_options.md`). -/
theorem eq_incP {μ ν : Partition} {k : ℕ} (hk : k ∈ μ.parts)
    (h : (ν.parts : Multiset ℕ) + {k} = (μ.parts : Multiset ℕ) + {k + 1}) :
    ν = incP μ k := by
  apply eq_of_parts_coe
  rw [incP, parts_ofMultiset, Multiset.filter_add,
    Multiset.filter_eq_self.2 (fun a ha => μ.pos a (Multiset.mem_of_mem_erase ha)),
    Multiset.filter_singleton, if_pos (Nat.succ_pos k)]
  rw [← Multiset.cons_erase (Multiset.mem_coe.2 hk), Multiset.cons_add,
    ← Multiset.singleton_add, add_comm] at h
  exact add_left_cancel h

/-- `μ − e_j = decP μ μ_j` (proof of **Lemma 7.3 (ii)** of `q_bip_options.md`). -/
theorem subE_eq_decP (μ : Partition) {j : ℕ} (hj : 1 ≤ j) (hjl : j ≤ μ.len) :
    μ.subE j = decP μ (μ.row j) := by
  have hi : j - 1 < μ.parts.length := by unfold len at hjl; omega
  have hrow : μ.row j = μ.parts[j - 1] := row_eq_getElem μ j hi
  have hpos : 1 ≤ μ.row j := row_pos μ j hj hjl
  apply eq_decP (by rw [hrow]; exact List.getElem_mem hi)
  have hm := coe_modify_add μ.parts (j - 1) (· - 1) hi
  rw [← hrow] at hm
  simp only [subE, sortDesc]
  rw [Multiset.coe_eq_coe.2 (List.mergeSort_perm _ _), ← Multiset.filter_coe]
  calc _ = Multiset.filter (0 < ·) (↑(μ.parts.modify (j - 1) fun x => x - 1) + {μ.row j}) := by
        rw [Multiset.filter_add, Multiset.filter_singleton, if_pos (by omega)]
        congr 1
        exact Multiset.filter_congr (fun x _ => by omega)
    _ = _ := by rw [hm, Multiset.filter_add, filter_parts]

/-- `μ + e_j = incP μ μ_j` (proof of **Lemma 7.3 (ii)** of `q_bip_options.md`). -/
theorem addE_eq_incP (μ : Partition) {j : ℕ} (hj : 1 ≤ j) (hjl : j ≤ μ.len) :
    μ.addE j = incP μ (μ.row j) := by
  have hi : j - 1 < μ.parts.length := by unfold len at hjl; omega
  have hrow : μ.row j = μ.parts[j - 1] := row_eq_getElem μ j hi
  apply eq_incP (by rw [hrow]; exact List.getElem_mem hi)
  have hm := coe_modify_add μ.parts (j - 1) (· + 1) hi
  rw [← hrow] at hm
  simp only [addE, sortDesc]
  rw [Multiset.coe_eq_coe.2 (List.mergeSort_perm _ _)]
  exact hm

/-- Reindexing the rows `1, …, ℓ` of a partition (proof of **Lemma 7.3 (ii)** of
`q_bip_options.md`). -/
theorem map_Icc_row {γ : Type*} (μ : Partition) (f : ℕ → γ) :
    (Finset.Icc 1 μ.len).val.map (fun j => f (μ.row j)) = (μ.parts : Multiset ℕ).map f := by
  have himg : (Finset.univ.image (fun i : Fin μ.parts.length => (i : ℕ) + 1)) =
      Finset.Icc 1 μ.len := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_Icc, len]
    constructor
    · rintro ⟨i, rfl⟩; omega
    · intro h; exact ⟨⟨x - 1, by omega⟩, by simp; omega⟩
  rw [← himg, Finset.image_val_of_injOn (fun a _ b _ h => Fin.ext (by simpa using h)),
    Multiset.map_map]
  conv_rhs => rw [← List.ofFn_getElem μ.parts, ← Fin.univ_val_map, Multiset.map_map]
  refine Multiset.map_congr rfl fun i _ => ?_
  simp only [Function.comp_apply]
  rw [row_eq_getElem μ _ (by simp)]
  simp

/-! ### Shapes as functions of the counts -/

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- The partition with parts the positive values `g(u)`, `u ∈ Ω` (proof of **Lemma 7.3 (ii)** of
`q_bip_options.md`). -/
def ofFun (g : Ω → ℕ) : Partition := Partition'.ofMultiset (Finset.univ.val.map g)

/-- `λ_+ = ofFun (X − Y)` (proof of **Lemma 7.3 (ii)** of `q_bip_options.md`). -/
theorem shapePlus_eq_ofFun {α β : ℕ} (ξ : Fin α → Ω) (η : Fin β → Ω) :
    shapePlus ξ η = ofFun fun v => cnt ξ v - cnt η v := by
  apply eq_of_parts_coe
  rw [shapePlus, ofFun, parts_ofMultiset, parts_ofMultiset, Multiset.filter_map,
    Multiset.filter_map, Finset.filter_val, Multiset.filter_filter]
  congr 1
  exact Multiset.filter_congr fun x _ => by simp only [Function.comp_apply]; omega

/-- `λ_− = ofFun (Y − X)` (proof of **Lemma 7.3 (ii)** of `q_bip_options.md`). -/
theorem shapeMinus_eq_ofFun {α β : ℕ} (ξ : Fin α → Ω) (η : Fin β → Ω) :
    shapeMinus ξ η = ofFun fun v => cnt η v - cnt ξ v := by
  apply eq_of_parts_coe
  rw [shapeMinus, ofFun, parts_ofMultiset, parts_ofMultiset, Multiset.filter_map,
    Multiset.filter_map, Finset.filter_val, Multiset.filter_filter]
  congr 1
  exact Multiset.filter_congr fun x _ => by simp only [Function.comp_apply]; omega

/-- Changing one value of `g` (proof of **Lemma 7.3 (ii)** of `q_bip_options.md`). -/
theorem map_update_add (g : Ω → ℕ) (u : Ω) (c : ℕ) :
    Finset.univ.val.map (Function.update g u c) + {g u} = Finset.univ.val.map g + {c} := by
  rw [← Multiset.cons_erase (s := (Finset.univ : Finset Ω).val) (Finset.mem_univ u)]
  simp only [Multiset.map_cons, Function.update_self]
  have : (Finset.univ.val.erase u).map (Function.update g u c) =
      (Finset.univ.val.erase u).map g :=
    Multiset.map_congr rfl fun v hv =>
      Function.update_of_ne ((Multiset.Nodup.mem_erase_iff Finset.univ.nodup).1 hv).1 _ _
  rw [this, ← Multiset.singleton_add, ← Multiset.singleton_add]
  abel

omit [DecidableEq Ω] in
/-- The positive values of `g` are the parts of `ofFun g`, and they are the values of `g` on
`{g > 0}` (proof of **Lemma 7.3 (ii)** of `q_bip_options.md`). -/
theorem map_filter_pos (g : Ω → ℕ) :
    (Finset.univ.filter fun v => 0 < g v).val.map g = ((ofFun g).parts : Multiset ℕ) := by
  rw [ofFun, parts_ofMultiset, Multiset.filter_map, Finset.filter_val]
  rfl

omit [Fintype Ω] in
/-- The count of `ξ = (u, ξ')`: `X(v) = X'(v) + [v = u]` (proof of **Lemma 7.3 (ii)** of
`q_bip_options.md`: "adding `u` as the new first coordinate of `ξ` raises `X(u)` by one and leaves
the other counts unchanged"). -/
theorem cnt_consPt {α β : ℕ} (hα : 1 ≤ α) (u : Ω) (M' : (Fin (α - 1) → Ω) × (Fin β → Ω))
    (v : Ω) : cnt (consPt hα u M').1 v = cnt M'.1 v + if v = u then 1 else 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, α = n + 1 := ⟨α - 1, by omega⟩
  unfold cnt
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
  simp only [consPt, Fin.val_zero, Fin.val_succ, dite_true, Nat.add_one_ne_zero, dite_false]
  rw [add_comm]
  congr 1
  by_cases h : u = v
  · simp [h]
  · simp [h, Ne.symm h]

/-- Changing one value of `g` changes the parts of `ofFun g` accordingly (proof of
**Lemma 7.3 (ii)** of `q_bip_options.md`). -/
theorem parts_ofFun_update (g : Ω → ℕ) (u : Ω) (c : ℕ) :
    ((ofFun (Function.update g u c)).parts : Multiset ℕ) + ({g u} : Multiset ℕ).filter (0 < ·) =
      ((ofFun g).parts : Multiset ℕ) + ({c} : Multiset ℕ).filter (0 < ·) := by
  rw [ofFun, ofFun, parts_ofMultiset, parts_ofMultiset, ← Multiset.filter_add,
    ← Multiset.filter_add, map_update_add]

/-- The case `Y(u) > X(u)` (a value `v_j` of the rows of `μ_−`) of the Proof of
**Lemma 7.3 (ii)** of `q_bip_options.md`: `λ(u, M') = (μ_+, μ_− − e_j)`, where the removed box is
in a row of length `Y(u) − X(u)`. -/
theorem shape_consPt_of_lt {α β : ℕ} (hα : 1 ≤ α) (M' : (Fin (α - 1) → Ω) × (Fin β → Ω))
    {u : Ω} (hu : cnt M'.1 u < cnt M'.2 u) :
    shape (consPt hα u M').1 (consPt hα u M').2 =
      (shapePlus M'.1 M'.2, decP (shapeMinus M'.1 M'.2) (cnt M'.2 u - cnt M'.1 u)) := by
  have hc := cnt_consPt hα u M'
  simp only [shape, shapePlus_eq_ofFun, shapeMinus_eq_ofFun, Prod.mk.injEq]
  have h2 : (consPt hα u M').2 = M'.2 := rfl
  rw [h2]
  constructor
  · congr 1
    funext v
    rw [hc]
    split_ifs with h
    · subst h; omega
    · omega
  · have hfun : (fun v => cnt M'.2 v - cnt (consPt hα u M').1 v) =
        Function.update (fun v => cnt M'.2 v - cnt M'.1 v) u (cnt M'.2 u - cnt M'.1 u - 1) := by
      funext v
      rw [hc]
      by_cases h : v = u
      · subst h; simp; omega
      · simp [h]
    rw [hfun]
    refine eq_decP ?_ ?_
    · rw [← Multiset.mem_coe, ← map_filter_pos]
      exact Multiset.mem_map.2 ⟨u, by simp; omega, rfl⟩
    · have := parts_ofFun_update (fun v => cnt M'.2 v - cnt M'.1 v) u
        (cnt M'.2 u - cnt M'.1 u - 1)
      rwa [Multiset.filter_singleton, if_pos (by omega)] at this

/-- The case `X(u) > Y(u)` (a value `u_j` of the rows of `μ_+`) of the Proof of
**Lemma 7.3 (ii)** of `q_bip_options.md`: `λ(u, M') = (μ_+ + e_j, μ_−)`, where the added box is in
a row of length `X(u) − Y(u)`. -/
theorem shape_consPt_of_gt {α β : ℕ} (hα : 1 ≤ α) (M' : (Fin (α - 1) → Ω) × (Fin β → Ω))
    {u : Ω} (hu : cnt M'.2 u < cnt M'.1 u) :
    shape (consPt hα u M').1 (consPt hα u M').2 =
      (incP (shapePlus M'.1 M'.2) (cnt M'.1 u - cnt M'.2 u), shapeMinus M'.1 M'.2) := by
  have hc := cnt_consPt hα u M'
  simp only [shape, shapePlus_eq_ofFun, shapeMinus_eq_ofFun, Prod.mk.injEq]
  have h2 : (consPt hα u M').2 = M'.2 := rfl
  rw [h2]
  constructor
  · have hfun : (fun v => cnt (consPt hα u M').1 v - cnt M'.2 v) =
        Function.update (fun v => cnt M'.1 v - cnt M'.2 v) u (cnt M'.1 u - cnt M'.2 u + 1) := by
      funext v
      rw [hc]
      by_cases h : v = u
      · subst h; simp; omega
      · simp [h]
    rw [hfun]
    refine eq_incP ?_ ?_
    · rw [← Multiset.mem_coe, ← map_filter_pos]
      exact Multiset.mem_map.2 ⟨u, by simp; omega, rfl⟩
    · have := parts_ofFun_update (fun v => cnt M'.1 v - cnt M'.2 v) u
        (cnt M'.1 u - cnt M'.2 u + 1)
      rwa [Multiset.filter_singleton, Multiset.filter_singleton, if_pos (by omega),
        if_pos (by omega)] at this
  · congr 1
    funext v
    rw [hc]
    split_ifs with h
    · subst h; omega
    · omega

/-- The case `X(u) = Y(u)` of the Proof of **Lemma 7.3 (ii)** of `q_bip_options.md`: a new part
`1` appears in `λ_+`, `λ(u, M') = (μ_+ ⊔ 1, μ_−)`. -/
theorem shape_consPt_of_eq {α β : ℕ} (hα : 1 ≤ α) (M' : (Fin (α - 1) → Ω) × (Fin β → Ω))
    {u : Ω} (hu : cnt M'.1 u = cnt M'.2 u) :
    shape (consPt hα u M').1 (consPt hα u M').2 =
      ((shapePlus M'.1 M'.2).addOne, shapeMinus M'.1 M'.2) := by
  have hc := cnt_consPt hα u M'
  simp only [shape, shapePlus_eq_ofFun, shapeMinus_eq_ofFun, Prod.mk.injEq]
  have h2 : (consPt hα u M').2 = M'.2 := rfl
  rw [h2]
  constructor
  · have hfun : (fun v => cnt (consPt hα u M').1 v - cnt M'.2 v) =
        Function.update (fun v => cnt M'.1 v - cnt M'.2 v) u 1 := by
      funext v
      rw [hc]
      by_cases h : v = u
      · subst h; simp; omega
      · simp [h]
    rw [hfun]
    apply eq_of_parts_coe
    have := parts_ofFun_update (fun v => cnt M'.1 v - cnt M'.2 v) u 1
    rw [Multiset.filter_singleton, Multiset.filter_singleton, if_neg (by omega),
      if_pos (by omega), Multiset.empty_eq_zero, add_zero] at this
    rw [this]
    simp only [addOne]
    rw [← Multiset.coe_add, Multiset.coe_singleton]
  · congr 1
    funext v
    rw [hc]
    split_ifs with h
    · subst h; omega
    · omega

/-- **Lemma 7.3 (ii)** of `q_bip_options.md`, main statement: for `α ≥ 1`, a finite set `Ω` with
`|Ω| = q` and every tail `M' = (ξ', η)` with shape `μ`, the multiset `{λ(u, M') : u ∈ Ω}` equals
the multiset `{opt_p(μ) : p = 1, …, q}`. -/
theorem map_shape_consPt {q α β : ℕ} (hα : 1 ≤ α) (hΩ : Fintype.card Ω = q)
    (M' : (Fin (α - 1) → Ω) × (Fin β → Ω)) {μ : Partition × Partition}
    (hμ : shape M'.1 M'.2 = μ) :
    Finset.univ.val.map (fun u => shape (consPt hα u M').1 (consPt hα u M').2) =
      (Finset.Icc 1 q).val.map (bopt q μ) := by
  subst hμ
  have hB := lemma72_0 hΩ M'.1 M'.2
  set μp := shapePlus M'.1 M'.2 with hμp
  set μm := shapeMinus M'.1 M'.2 with hμm
  have hsh : shape M'.1 M'.2 = (μp, μm) := rfl
  have hl : μp.len + μm.len ≤ q := hB.2.2
  rw [hsh]
  set S := fun u => shape (consPt hα u M').1 (consPt hα u M').2 with hS
  set Am := Finset.univ.filter (fun u => cnt M'.1 u < cnt M'.2 u) with hAm
  set Ap := Finset.univ.filter (fun u => cnt M'.2 u < cnt M'.1 u) with hAp
  set A0 := Finset.univ.filter (fun u => cnt M'.1 u = cnt M'.2 u) with hA0
  -- the values with `Y(u) > X(u)` give the rows of `μ_−`
  have hmapm : Am.val.map (fun u => cnt M'.2 u - cnt M'.1 u) = (μm.parts : Multiset ℕ) := by
    have : Am = Finset.univ.filter (fun v => 0 < cnt M'.2 v - cnt M'.1 v) :=
      Finset.filter_congr (fun v _ => by omega)
    rw [this, hμm, shapeMinus_eq_ofFun, map_filter_pos]
  -- the values with `X(u) > Y(u)` give the rows of `μ_+`
  have hmapp : Ap.val.map (fun u => cnt M'.1 u - cnt M'.2 u) = (μp.parts : Multiset ℕ) := by
    have : Ap = Finset.univ.filter (fun v => 0 < cnt M'.1 v - cnt M'.2 v) :=
      Finset.filter_congr (fun v _ => by omega)
    rw [this, hμp, shapePlus_eq_ofFun, map_filter_pos]
  have hcardm : Am.card = μm.len := by
    have := congrArg Multiset.card hmapm
    rwa [Multiset.card_map, Multiset.coe_card] at this
  have hcardp : Ap.card = μp.len := by
    have := congrArg Multiset.card hmapp
    rwa [Multiset.card_map, Multiset.coe_card] at this
  -- the three groups of values
  have hd1 : Disjoint A0 Ap := Finset.disjoint_filter.2 (fun _ _ h1 h2 => by omega)
  have hd2 : Disjoint Am (A0.disjUnion Ap hd1) := by
    rw [Finset.disjoint_left]
    intro x h1 h2
    rw [Finset.mem_disjUnion] at h2
    have := (Finset.mem_filter.1 h1).2
    rcases h2 with h2 | h2 <;> have := (Finset.mem_filter.1 h2).2 <;> omega
  have huniv : (Finset.univ : Finset Ω) = Am.disjUnion (A0.disjUnion Ap hd1) hd2 := by
    ext x
    simp only [hAm, hA0, hAp, Finset.mem_disjUnion, Finset.mem_filter, Finset.mem_univ,
      true_and, true_iff]
    omega
  have hcard0 : A0.card = q - μp.len - μm.len := by
    have := congrArg Finset.card huniv
    rw [Finset.card_univ, hΩ, Finset.card_disjUnion, Finset.card_disjUnion] at this
    omega
  have hL : Finset.univ.val.map S = Am.val.map S + (A0.val.map S + Ap.val.map S) := by
    conv_lhs => rw [huniv]
    show Multiset.map S (Am.val + (A0.val + Ap.val)) = _
    rw [Multiset.map_add, Multiset.map_add]
  have h1 : Am.val.map S = (μm.parts : Multiset ℕ).map (fun k => (μp, decP μm k)) := by
    rw [← hmapm, Multiset.map_map]
    exact Multiset.map_congr rfl fun u hu =>
      shape_consPt_of_lt hα M' (Finset.mem_filter.1 hu).2
  have h2 : A0.val.map S = Multiset.replicate (q - μp.len - μm.len) (μp.addOne, μm) := by
    rw [Multiset.map_congr rfl fun u hu => shape_consPt_of_eq hα M' (Finset.mem_filter.1 hu).2,
      Multiset.map_const', Finset.card_val, hcard0]
  have h3 : Ap.val.map S = (μp.parts : Multiset ℕ).map (fun k => (incP μp k, μm)) := by
    rw [← hmapp, Multiset.map_map]
    exact Multiset.map_congr rfl fun u hu =>
      shape_consPt_of_gt hα M' (Finset.mem_filter.1 hu).2
  -- the three blocks of positions
  have hdI1 : Disjoint (Finset.Ioc μm.len (q - μp.len)) (Finset.Ioc (q - μp.len) q) := by
    rw [Finset.disjoint_left]
    intro x h1 h2
    simp only [Finset.mem_Ioc] at h1 h2
    omega
  have hdI2 : Disjoint (Finset.Icc 1 μm.len)
      ((Finset.Ioc μm.len (q - μp.len)).disjUnion (Finset.Ioc (q - μp.len) q) hdI1) := by
    rw [Finset.disjoint_left]
    intro x h1 h2
    simp only [Finset.mem_Icc, Finset.mem_disjUnion, Finset.mem_Ioc] at h1 h2
    omega
  have hIcc : Finset.Icc 1 q = (Finset.Icc 1 μm.len).disjUnion
      ((Finset.Ioc μm.len (q - μp.len)).disjUnion (Finset.Ioc (q - μp.len) q) hdI1) hdI2 := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_disjUnion, Finset.mem_Ioc]
    omega
  have hR1 : (Finset.Icc 1 μm.len).val.map (bopt q (μp, μm)) =
      (μm.parts : Multiset ℕ).map (fun k => (μp, decP μm k)) := by
    rw [← map_Icc_row μm (fun k => (μp, decP μm k))]
    refine Multiset.map_congr rfl fun j hj => ?_
    have := Finset.mem_Icc.1 hj
    unfold bopt
    dsimp only
    rw [if_pos this.2, subE_eq_decP μm this.1 this.2]
  have hR2 : (Finset.Ioc μm.len (q - μp.len)).val.map (bopt q (μp, μm)) =
      Multiset.replicate (q - μp.len - μm.len) (μp.addOne, μm) := by
    have : ∀ p ∈ (Finset.Ioc μm.len (q - μp.len)).val, bopt q (μp, μm) p = (μp.addOne, μm) := by
      intro p hp
      have := Finset.mem_Ioc.1 hp
      unfold bopt
      dsimp only
      rw [if_neg (by omega), if_pos this.2]
    rw [Multiset.map_congr rfl this, Multiset.map_const', Finset.card_val, Nat.card_Ioc]
  have hR3 : (Finset.Ioc (q - μp.len) q).val.map (bopt q (μp, μm)) =
      (μp.parts : Multiset ℕ).map (fun k => (incP μp k, μm)) := by
    rw [← map_Icc_row μp (fun k => (incP μp k, μm))]
    have himg : (Finset.Ioc (q - μp.len) q).image (fun p => q + 1 - p) = Finset.Icc 1 μp.len := by
      ext x
      simp only [Finset.mem_image, Finset.mem_Ioc, Finset.mem_Icc]
      constructor
      · rintro ⟨p, hp, rfl⟩; omega
      · intro h; exact ⟨q + 1 - x, by omega, by omega⟩
    rw [← himg, Finset.image_val_of_injOn (fun a ha b hb h => by
      simp only [Finset.coe_Ioc, Set.mem_Ioc] at ha hb
      omega), Multiset.map_map]
    refine Multiset.map_congr rfl fun p hp => ?_
    have := Finset.mem_Ioc.1 hp
    unfold bopt
    dsimp only
    rw [if_neg (by omega), if_neg (by omega), addE_eq_incP μp (by omega) (by omega)]
    rfl
  have hR : (Finset.Icc 1 q).val.map (bopt q (μp, μm)) =
      (Finset.Icc 1 μm.len).val.map (bopt q (μp, μm)) +
        ((Finset.Ioc μm.len (q - μp.len)).val.map (bopt q (μp, μm)) +
          (Finset.Ioc (q - μp.len) q).val.map (bopt q (μp, μm))) := by
    conv_lhs => rw [hIcc]
    show Multiset.map _ ((Finset.Icc 1 μm.len).val + ((Finset.Ioc μm.len (q - μp.len)).val +
      (Finset.Ioc (q - μp.len) q).val)) = _
    rw [Multiset.map_add, Multiset.map_add]
  rw [hL, hR, h1, h2, h3, hR1, hR2, hR3]

omit [Fintype Ω] [DecidableEq Ω] in
/-- The tuple of the point `(u, M')` is `(u, ξ'_1, …, ξ'_{α−1}, η_1, …, η_β)`, i.e. the tuple
`(u, M')` of `q_peeling_lemma.md` built on the tuple of the tail `M'` (proof of
**Lemma 7.3 (ii)** of `q_bip_options.md`, with Lemma 7.1 (iv) of `q_bip_setting.md`). -/
theorem toTuple_consPt {α β : ℕ} (hα : 1 ≤ α) (u : Ω) (M' : (Fin (α - 1) → Ω) × (Fin β → Ω)) :
    toTuple (consPt hα u M') = Peel.consTuple (m := α + β) u (tailToTuple M') := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun l => ?_) i
  · simp only [toTuple, Function.Embedding.coeFn_mk, Fin.append_left, consPt, Peel.consTuple,
      tailToTuple, Fin.val_castAdd]
    by_cases h : (i : ℕ) = 0
    · simp [h]
    · simp only [h, dite_false]
      rw [dif_pos (by omega)]
  · simp only [toTuple, Function.Embedding.coeFn_mk, Fin.append_right, consPt, Peel.consTuple,
      tailToTuple, Fin.val_natAdd]
    rw [dif_neg (by omega), dif_neg (by omega)]
    exact congrArg _ (Fin.ext (by simp only; omega))

omit [Fintype Ω] [DecidableEq Ω] in
/-- Every tuple of `Ω^{α+β−1}` is the tuple of exactly one tail `M' ∈ Ω^{α−1} × Ω^β` (proof of
**Lemma 7.3 (ii)** of `q_bip_options.md`, with Lemma 7.1 (iv) of `q_bip_setting.md`). -/
theorem tailToTuple_bijective {α β : ℕ} (hα : 1 ≤ α) :
    Function.Bijective (tailToTuple : (Fin (α - 1) → Ω) × (Fin β → Ω) → Fin (α + β - 1) → Ω) := by
  let g : (Fin (α + β - 1) → Ω) → (Fin (α - 1) → Ω) × (Fin β → Ω) := fun N =>
    (fun j => N ⟨j, by omega⟩, fun l => N ⟨α - 1 + l, by omega⟩)
  have hleft : Function.LeftInverse g tailToTuple := by
    intro M'
    ext j
    · simp [g, tailToTuple]
    · simp only [g, tailToTuple]
      rw [dif_neg (by simp)]
      exact congrArg _ (Fin.ext (by simp))
  have hright : Function.RightInverse g tailToTuple := by
    intro N
    funext i
    simp only [g, tailToTuple]
    split_ifs with h
    · rfl
    · exact congrArg _ (Fin.ext (by simp only; omega))
  exact ⟨hleft.injective, hright.surjective⟩

open Classical in
/-- **Lemma 7.3 (ii)** of `q_bip_options.md`, first consequence: for every tail `M'` with shape
`μ`, `|F(M')| = F_Λ(μ)`, where `F(M') = {u ∈ Ω : (u, M') ∈ Z_Λ}` is the fibre of Lemma 7.1 (iv)
of `q_bip_setting.md` (`Peel.fiber`, taken on the image of `Z_Λ` in `Ω^{α+β}` under `toTuple`,
over the tuple of `M'`).  (This holds for every set `Λ` of pairs of partitions, not only for the
down-sets of `BPar_q(α, β)` considered in the file.) -/
theorem card_fiber_eq_FLamB {q α β : ℕ} (hα : 1 ≤ α) (hΩ : Fintype.card Ω = q)
    (Λ : Set (Partition × Partition)) (M' : (Fin (α - 1) → Ω) × (Fin β → Ω))
    {μ : Partition × Partition} (hμ : shape M'.1 M'.2 = μ) :
    (Peel.fiber ((ZLam Ω α β Λ).map toTuple) (tailToTuple M')).card = FLamB q Λ μ := by
  have hmem : ∀ u, Peel.consTuple (m := α + β) u (tailToTuple M') ∈ (ZLam Ω α β Λ).map toTuple ↔
      shape (consPt hα u M').1 (consPt hα u M').2 ∈ Λ := by
    intro u
    rw [← toTuple_consPt hα, Finset.mem_map' toTuple]
    simp [ZLam]
  have key := congrArg (Multiset.countP (· ∈ Λ)) (map_shape_consPt hα hΩ M' hμ)
  rw [Multiset.countP_map, Multiset.countP_map] at key
  unfold Peel.fiber FLamB
  rw [Finset.filter_congr (fun u _ => hmem u)]
  exact key

open Classical in
/-- **Lemma 7.3 (ii)** of `q_bip_options.md`, second consequence: `Z_{>i} = Z_{Λ_i}` with
`Λ_i := {ν ∈ BPar_q(α − 1, β) : F_Λ(ν) > i}` (`LamLayer`).  Here `Z_{>i}` is the set of Lemma 7.1
(iv) of `q_bip_setting.md` (`Peel.Zgt`) for `Z = Z_Λ ⊆ Ω^α × Ω^β` (taken in `Ω^{α+β}` through
`toTuple`), and `Z_{Λ_i} ⊆ Ω^{α−1} × Ω^β` is read in `Ω^{α+β−1}` through the tuples of the tails
(`tailToTuple`).  The proof uses Lemma 7.2 (0) (`lemma72_0`) for the tails.  (This holds for every
set `Λ` of pairs of partitions.) -/
theorem Zgt_eq_ZLam_layer {q α β : ℕ} (hα : 1 ≤ α) (hΩ : Fintype.card Ω = q)
    (Λ : Set (Partition × Partition)) (i : ℕ) :
    Peel.Zgt ((ZLam Ω α β Λ).map toTuple) i =
      (ZLam Ω (α - 1) β (LamLayer q α β Λ i)).image tailToTuple := by
  ext N
  obtain ⟨M', rfl⟩ := (tailToTuple_bijective (Ω := Ω) (β := β) hα).2 N
  rw [(tailToTuple_bijective hα).1.mem_finset_image]
  simp only [Peel.Zgt, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [card_fiber_eq_FLamB hα hΩ Λ M' rfl]
  simp only [ZLam, LamLayer, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
  exact ⟨fun h => ⟨lemma72_0 hΩ M'.1 M'.2, h⟩, fun h => h.2⟩

end Bip

end

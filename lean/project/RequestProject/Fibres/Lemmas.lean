module

public import RequestProject.Fibres.Defs

/-!
# Auxiliary lemmas for `q_P1_fibres.md`

Helper lemmas for the proof of parts (i), (ii) and (iii) of the **Proposition** of
`q_P1_fibres.md`: describing partitions by their multisets of parts, the options
`μ − e_j`, `μ + e_j`, `μ ⊔ 1` in these terms, and the effect of prepending a value `t` to a tail.
-/

@[expose] public section

namespace Fibres

open ChainLemma ChainLemma.Partition Peel

/-- Helper for part (ii) of `q_P1_fibres.md`: the multiset of parts of `ofMultiset s` is the
multiset of positive elements of `s`. -/
lemma ofMultiset_parts (s : Multiset ℕ) :
    ((ofMultiset s).parts : Multiset ℕ) = s.filter (0 < ·) :=
  Multiset.sort_eq _ _

/-- Helper for part (ii) of `q_P1_fibres.md`: partitions with the same multiset of parts are
equal. -/
lemma Partition.eq_of_coe_parts {μ ν : Partition}
    (hμν : (μ.parts : Multiset ℕ) = (ν.parts : Multiset ℕ)) : μ = ν := by
  ext1
  refine List.Perm.eq_of_pairwise (le := (· ≥ ·)) ?_ μ.sorted ν.sorted (Multiset.coe_eq_coe.mp hμν)
  intro a b _ _ h1 h2
  exact le_antisymm h2 h1

/-- Helper for part (ii) of `q_P1_fibres.md`: every partition is `ofMultiset` of its parts. -/
lemma Partition.eq_ofMultiset (μ : Partition) : μ = ofMultiset (μ.parts : Multiset ℕ) := by
  apply Partition.eq_of_coe_parts
  rw [ofMultiset_parts, Multiset.filter_eq_self.mpr]
  intro a ha
  exact μ.pos a (by simpa using ha)

/-- Helper for part (ii) of `q_P1_fibres.md`. -/
lemma ofMultiset_congr {s s' : Multiset ℕ} (hss : s.filter (0 < ·) = s'.filter (0 < ·)) :
    ofMultiset s = ofMultiset s' :=
  Partition.eq_of_coe_parts (by rw [ofMultiset_parts, ofMultiset_parts, hss])

/-- Helper for part (ii): `l.modify i g` is a permutation of `g l[i] :: l.eraseIdx i`. -/
lemma coe_modify {l : List ℕ} {i : ℕ} (hi : i < l.length) (g : ℕ → ℕ) :
    ((l.modify i g : List ℕ) : Multiset ℕ) = g l[i] ::ₘ ((l : Multiset ℕ).erase l[i]) := by
  have h1 := List.getElem_cons_eraseIdx_perm (l := l.modify i g) (n := i) (by simpa using hi)
  have h2 := List.getElem_cons_eraseIdx_perm (l := l) hi
  rw [List.eraseIdx_modify_of_eq] at h1
  rw [← Multiset.coe_eq_coe.mpr h1, ← Multiset.coe_eq_coe.mpr h2]
  simp

/-- Helper for part (ii) of `q_P1_fibres.md`: `μ − e_j` in terms of multisets of parts. -/
lemma subE_eq (μ : Partition) {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ μ.len) :
    μ.subE j = ofMultiset ((μ.parts : Multiset ℕ).erase (μ.row j) + {μ.row j - 1}) := by
  have hi : j - 1 < μ.parts.length := by unfold Partition.len at hj; omega
  have hrow : μ.row j = μ.parts[j - 1] := by simp [Partition.row, List.getElem?_eq_getElem hi]
  apply Partition.eq_of_coe_parts
  rw [ofMultiset_parts]
  simp only [Partition.subE, sortDesc]
  rw [Multiset.coe_eq_coe.mpr (List.mergeSort_perm _ _), ← Multiset.filter_coe, coe_modify hi, hrow]
  ext a
  simp only [Multiset.count_filter, Multiset.count_cons, Multiset.count_add,
    Multiset.count_singleton]
  split_ifs <;> omega

/-- Helper for part (ii) of `q_P1_fibres.md`: `μ + e_j` in terms of multisets of parts. -/
lemma addE_eq (μ : Partition) {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ μ.len) :
    μ.addE j = ofMultiset ((μ.parts : Multiset ℕ).erase (μ.row j) + {μ.row j + 1}) := by
  have hi : j - 1 < μ.parts.length := by unfold Partition.len at hj; omega
  have hrow : μ.row j = μ.parts[j - 1] := by simp [Partition.row, List.getElem?_eq_getElem hi]
  apply Partition.eq_of_coe_parts
  rw [ofMultiset_parts]
  simp only [Partition.addE, sortDesc]
  rw [Multiset.coe_eq_coe.mpr (List.mergeSort_perm _ _), coe_modify hi, hrow, Multiset.filter_eq_self.mpr]
  · rw [add_comm _ {_}, Multiset.singleton_add]
  · intro a ha
    rw [Multiset.mem_add, Multiset.mem_singleton] at ha
    rcases ha with ha | rfl
    · exact μ.pos a (by simpa using Multiset.mem_of_mem_erase ha)
    · omega

/-- Helper for part (ii) of `q_P1_fibres.md`: `μ ⊔ 1` in terms of multisets of parts. -/
lemma addOne_eq (μ : Partition) : μ.addOne = ofMultiset ((μ.parts : Multiset ℕ) + {1}) := by
  apply Partition.eq_of_coe_parts
  rw [ofMultiset_parts, Multiset.filter_eq_self.mpr]
  · simp only [Partition.addOne]; rw [← Multiset.coe_add]; rfl
  · intro a ha
    rw [Multiset.mem_add, Multiset.mem_singleton] at ha
    rcases ha with ha | rfl
    · exact μ.pos a (by simpa using ha)
    · omega

/-- Helper for part (ii) of `q_P1_fibres.md`: the rows `μ_1, …, μ_ℓ` form the multiset of parts. -/
lemma map_row_Icc (μ : Partition) :
    (Finset.Icc 1 μ.len).val.map μ.row = (μ.parts : Multiset ℕ) := by
  have hI : Finset.Icc 1 μ.len = (Finset.range μ.len).map (addRightEmbedding 1) := by
    rw [Finset.range_eq_Ico, Finset.map_add_right_Ico]; ext; simp
  have hl : (List.range μ.parts.length).map (fun i => μ.parts.getD i 0) = μ.parts := by
    apply List.ext_getElem
    · simp
    · intro i _ h; simp [List.getElem?_eq_getElem h]
  rw [hI, Finset.map_val, Multiset.map_map]
  conv_rhs => rw [← hl]
  rfl

/-- Helper for part (ii) of `q_P1_fibres.md`: the partition with parts `μ` with one part `x`
replaced by `x − 1` (i.e. `μ − e_j` when `x = μ_j`). -/
def Gsub (μ : Partition) (x : ℕ) : Partition :=
  ofMultiset ((μ.parts : Multiset ℕ).erase x + {x - 1})

/-- Helper for part (ii) of `q_P1_fibres.md`: the partition with parts `μ` with one part `x`
replaced by `x + 1` (i.e. `μ + e_j` when `x = μ_j`). -/
def Gadd (μ : Partition) (x : ℕ) : Partition :=
  ofMultiset ((μ.parts : Multiset ℕ).erase x + {x + 1})

/-- Helper for part (ii) of `q_P1_fibres.md`: the multiset `{opt_p(μ) : p = 1, …, 2h}` is
`{μ − e_j}_{j ≤ ℓ} ∪ {μ ⊔ 1}^{×(2h − 2ℓ)} ∪ {μ + e_j}_{j ≤ ℓ}`. -/
lemma map_opt_eq (μ : Partition) {h : ℕ} (hℓ : μ.len ≤ h) :
    (Finset.Icc 1 (2 * h)).val.map (μ.opt (2 * h)) =
      (μ.parts : Multiset ℕ).map (Gsub μ) + Multiset.replicate (2 * h - 2 * μ.len) μ.addOne +
        (μ.parts : Multiset ℕ).map (Gadd μ) := by
  set ℓ := μ.len with hℓdef
  have e1 : (Finset.Icc 1 (2 * h)).val.filter (· ≤ ℓ) = (Finset.Icc 1 ℓ).val := by
    rw [← Finset.filter_val]; congr 1; ext; simp; omega
  have e2 : ((Finset.Icc 1 (2 * h)).val.filter (fun p => ¬ p ≤ ℓ)).filter (· ≤ 2 * h - ℓ) =
      (Finset.Icc (ℓ + 1) (2 * h - ℓ)).val := by
    rw [Multiset.filter_filter, ← Finset.filter_val]; congr 1; ext; simp; omega
  have e3 : ((Finset.Icc 1 (2 * h)).val.filter (fun p => ¬ p ≤ ℓ)).filter
      (fun p => ¬ p ≤ 2 * h - ℓ) = (Finset.Icc (2 * h - ℓ + 1) (2 * h)).val := by
    rw [Multiset.filter_filter, ← Finset.filter_val]; congr 1; ext; simp; omega
  rw [← Multiset.filter_add_not (· ≤ ℓ) (Finset.Icc 1 (2 * h)).val, e1,
    ← Multiset.filter_add_not (· ≤ 2 * h - ℓ)
      ((Finset.Icc 1 (2 * h)).val.filter (fun p => ¬ p ≤ ℓ)), e2, e3, Multiset.map_add, Multiset.map_add,
    add_assoc]
  congr 1
  · rw [Multiset.map_congr rfl (g := Gsub μ ∘ μ.row), ← Multiset.map_map, map_row_Icc]
    intro p hp
    rw [Finset.mem_val, Finset.mem_Icc] at hp
    simp only [Partition.opt, Function.comp, Gsub]
    rw [if_pos hp.2]
    exact subE_eq μ hp.1 hp.2
  congr 1
  · rw [Multiset.map_congr rfl (g := Function.const _ μ.addOne), Multiset.map_const]
    · simp; congr 1; omega
    intro p hp
    rw [Finset.mem_val, Finset.mem_Icc] at hp
    simp only [Partition.opt, Function.const]
    rw [if_neg (by omega), if_pos hp.2]
  · rw [Multiset.map_congr rfl (g := Gadd μ ∘ μ.row ∘ (fun p => 2 * h + 1 - p)),
      ← Multiset.map_map, ← Multiset.map_map]
    · have : (Finset.Icc (2 * h - ℓ + 1) (2 * h)).val.map (fun p => 2 * h + 1 - p) =
          (Finset.Icc 1 ℓ).val := by
        rw [← Finset.image_val_of_injOn]
        · congr 1; ext x; simp only [Finset.mem_image, Finset.mem_Icc]
          constructor
          · rintro ⟨p, hp, rfl⟩; omega
          · intro hx; exact ⟨2 * h + 1 - x, by omega, by omega⟩
        · intro a ha b hb hab; simp at ha hb hab; omega
      rw [this, map_row_Icc]
    intro p hp
    rw [Finset.mem_val, Finset.mem_Icc] at hp
    simp only [Partition.opt, Function.comp, Gadd]
    rw [if_neg (by omega), if_neg (by omega)]
    exact addE_eq μ (by omega) (by omega)

variable {T : Type*} [Fintype T] [DecidableEq T] {h : ℕ}

/-- Helper for parts (i)–(iii) of `q_P1_fibres.md`: the truncated difference
`#{M_i = u} − #{M_i = −u}`, positive exactly at the majority element of an unbalanced class. -/
def diff (S : FibreSetting T h) {m : ℕ} (M : Fin m → T) (u : T) : ℕ :=
  cnt M u - cnt M (S.neg u)

/-- Helper for parts (i)–(iii) of `q_P1_fibres.md`: the parts of `λ(M)`. -/
lemma resPart_parts (S : FibreSetting T h) {m : ℕ} (M : Fin m → T) :
    ((S.resPart M).parts : Multiset ℕ) = (Finset.univ.val.map (diff S M)).filter (0 < ·) :=
  ofMultiset_parts _

omit [Fintype T] in
/-- Helper for part (ii) of `q_P1_fibres.md`: prepending `t` to a tail of length `n`. -/
lemma cnt_consTuple_succ {n : ℕ} (t : T) (M' : Fin n → T) (u : T) :
    cnt (consTuple (m := n + 1) t M') u = cnt M' u + if t = u then 1 else 0 := by
  simp only [cnt, Finset.card_filter, Fin.sum_univ_succ]
  rw [add_comm]
  congr 1

omit [Fintype T] in
/-- Helper for part (ii) of `q_P1_fibres.md`: adding one value `t` changes only the count of `t`,
by one. -/
lemma cnt_consTuple {m : ℕ} (hm : 1 ≤ m) (t : T) (M' : Fin (m - 1) → T) (u : T) :
    cnt (consTuple (m := m) t M') u = cnt M' u + if t = u then 1 else 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  exact cnt_consTuple_succ t M' u

/-- Helper for part (ii) of `q_P1_fibres.md`: isolate the class `{t, −t}` in a map over `T`. -/
lemma univ_map_split (S : FibreSetting T h) (g : T → ℕ) (t : T) :
    Finset.univ.val.map g =
      g t ::ₘ g (S.neg t) ::ₘ ((Finset.univ.erase t).erase (S.neg t)).val.map g := by
  rw [← Multiset.map_cons, ← Multiset.map_cons, Finset.erase_val, Finset.erase_val,
    Multiset.cons_erase ((Multiset.mem_erase_of_ne (S.neg_ne t)).mpr (Finset.mem_univ_val _)),
    Multiset.cons_erase (Finset.mem_univ_val t)]

/-- Helper for part (ii) of `q_P1_fibres.md`: the three cases of the proof of (ii). If `t` is the
majority value `u_j` of an unbalanced class, `λ((t, M')) = μ + e_j`; if `t = −u_j`,
`λ((t, M')) = μ − e_j`; if `t` lies in a balanced class, `λ((t, M')) = μ ⊔ 1`. -/
lemma resPart_consTuple (S : FibreSetting T h) {m : ℕ} (hm : 1 ≤ m) (t : T)
    (M' : Fin (m - 1) → T) :
    S.resPart (consTuple (m := m) t M') =
      if 0 < diff S M' t then Gadd (S.resPart M') (diff S M' t)
      else if 0 < diff S M' (S.neg t) then Gsub (S.resPart M') (diff S M' (S.neg t))
      else (S.resPart M').addOne := by
  have hne : S.neg t ≠ t := S.neg_ne t
  set R := ((Finset.univ.erase t).erase (S.neg t)).val with hR
  have hRmap : R.map (diff S (consTuple (m := m) t M')) = R.map (diff S M') := by
    apply Multiset.map_congr rfl
    intro u hu
    rw [hR, Finset.mem_val, Finset.mem_erase, Finset.mem_erase] at hu
    have h1 : t ≠ u := fun e => hu.2.1 e.symm
    have h2 : t ≠ S.neg u := fun e => hu.1 (by rw [e, S.neg_neg])
    simp [diff, cnt_consTuple hm, h1, h2]
  have hP := resPart_parts S M'
  rw [univ_map_split S _ t] at hP
  have hc1 : cnt (consTuple (m := m) t M') t = cnt M' t + 1 := by
    simp [cnt_consTuple hm]
  have hc2 : cnt (consTuple (m := m) t M') (S.neg t) = cnt M' (S.neg t) := by
    simp [cnt_consTuple hm, hne.symm]
  have hd1 : diff S (consTuple (m := m) t M') t = cnt M' t + 1 - cnt M' (S.neg t) := by
    simp [diff, hc1, hc2]
  have hd2 : diff S (consTuple (m := m) t M') (S.neg t) = cnt M' (S.neg t) - (cnt M' t + 1) := by
    simp [diff, hc1, hc2, S.neg_neg]
  have he1 : diff S M' t = cnt M' t - cnt M' (S.neg t) := rfl
  have he2 : diff S M' (S.neg t) = cnt M' (S.neg t) - cnt M' t := by simp [diff, S.neg_neg]
  have hL : S.resPart (consTuple (m := m) t M') = ofMultiset
      ((cnt M' t + 1 - cnt M' (S.neg t)) ::ₘ (cnt M' (S.neg t) - (cnt M' t + 1)) ::ₘ
        R.map (diff S M')) := by
    rw [show S.resPart (consTuple (m := m) t M') =
      ofMultiset (Finset.univ.val.map (diff S (consTuple (m := m) t M'))) from rfl,
      univ_map_split S _ t, ← hR, hRmap, hd1, hd2]
  rw [hL, he1, he2]
  rw [he1, he2, ← hR] at hP
  set a := cnt M' t
  set b := cnt M' (S.neg t)
  split_ifs with hab hba
  · rw [Gadd, hP, Multiset.filter_cons_of_pos _ hab, Multiset.filter_cons_of_neg _ (by omega),
      Multiset.erase_cons_head]
    apply ofMultiset_congr
    ext x
    simp only [Multiset.count_filter, Multiset.count_cons, Multiset.count_add,
      Multiset.count_singleton]
    split_ifs <;> omega
  · rw [Gsub, hP, Multiset.filter_cons_of_neg _ hab, Multiset.filter_cons_of_pos _ hba,
      Multiset.erase_cons_head]
    apply ofMultiset_congr
    ext x
    simp only [Multiset.count_filter, Multiset.count_cons, Multiset.count_add,
      Multiset.count_singleton]
    split_ifs <;> omega
  · rw [addOne_eq, hP, Multiset.filter_cons_of_neg _ hab, Multiset.filter_cons_of_neg _ hba]
    apply ofMultiset_congr
    ext x
    simp only [Multiset.count_filter, Multiset.count_cons, Multiset.count_add,
      Multiset.count_singleton]
    split_ifs <;> omega

/-- Helper for parts (i)–(iii) of `q_P1_fibres.md`: at most one element of a class is a
majority element. -/
lemma diff_neg_eq_zero (S : FibreSetting T h) {m : ℕ} (M : Fin m → T) {u : T}
    (hu : 0 < diff S M u) : diff S M (S.neg u) = 0 := by
  unfold diff at *
  rw [S.neg_neg]
  omega

/-- Helper for parts (i)–(iii) of `q_P1_fibres.md`: the values of `diff` at the majority
elements are the parts of `λ(M)`. -/
lemma map_diff_filter (S : FibreSetting T h) {m : ℕ} (M : Fin m → T) :
    (Finset.univ.val.filter (fun u => 0 < diff S M u)).map (diff S M) =
      ((S.resPart M).parts : Multiset ℕ) := by
  rw [resPart_parts, Multiset.filter_map]
  rfl

/-- Helper for parts (i)–(iii) of `q_P1_fibres.md`: the same, indexed by the minority
elements `−u_j`. -/
lemma map_diff_neg_filter (S : FibreSetting T h) {m : ℕ} (M : Fin m → T) :
    (Finset.univ.val.filter (fun u => 0 < diff S M (S.neg u))).map (diff S M ∘ S.neg) =
      ((S.resPart M).parts : Multiset ℕ) := by
  let e : Equiv.Perm T := Function.Involutive.toPerm S.neg S.neg_neg
  rw [← map_diff_filter, ← Multiset.map_map]
  congr 1
  conv_rhs => rw [← Multiset.map_univ_val_equiv e]
  rw [Multiset.filter_map]
  rfl

/-- Helper for parts (i)–(iii) of `q_P1_fibres.md`: `T` splits into the majority elements, the
minority elements, and the elements of balanced classes. -/
lemma univ_split (S : FibreSetting T h) {m : ℕ} (M : Fin m → T) :
    (Finset.univ.val : Multiset T) =
      Finset.univ.val.filter (fun u => 0 < diff S M u) +
        (Finset.univ.val.filter (fun u => 0 < diff S M (S.neg u)) +
          Finset.univ.val.filter (fun u => ¬ 0 < diff S M u ∧ ¬ 0 < diff S M (S.neg u))) := by
  conv_lhs => rw [← Multiset.filter_add_not (fun u => 0 < diff S M u) Finset.univ.val]
  congr 1
  rw [← Multiset.filter_add_not (fun u => 0 < diff S M (S.neg u))
    (Finset.univ.val.filter (fun u => ¬ 0 < diff S M u)), Multiset.filter_filter,
    Multiset.filter_filter]
  congr 1
  · apply Multiset.filter_congr
    intro u _
    constructor
    · exact fun h => h.1
    · intro h
      refine ⟨h, ?_⟩
      have := diff_neg_eq_zero S M h
      rw [S.neg_neg] at this
      omega
  · apply Multiset.filter_congr
    intro u _
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-- Helper for parts (i) and (ii) of `q_P1_fibres.md`: `2ℓ(λ(M)) + #{balanced elements} = 2h`. -/
lemma two_len_add_card (S : FibreSetting T h) {m : ℕ} (M : Fin m → T) :
    2 * (S.resPart M).len +
      (Finset.univ.val.filter (fun u => ¬ 0 < diff S M u ∧ ¬ 0 < diff S M (S.neg u))).card =
      2 * h := by
  have h1 := congrArg Multiset.card (univ_split S M)
  have h2 := congrArg Multiset.card (map_diff_filter S M)
  have h3 := congrArg Multiset.card (map_diff_neg_filter S M)
  simp only [Multiset.card_add, Multiset.card_map, Multiset.coe_card] at h1 h2 h3
  rw [Finset.card_val, Finset.card_univ, S.card_eq] at h1
  unfold Partition.len
  omega

/-- Helper for part (ii) of `q_P1_fibres.md`: the multiset `{λ((t, M')) : t ∈ T}` equals
`{μ − e_j}_{j ≤ ℓ} ∪ {μ ⊔ 1}^{×(2h − 2ℓ)} ∪ {μ + e_j}_{j ≤ ℓ}` with `μ = λ(M')`. -/
lemma map_resPart_consTuple (S : FibreSetting T h) {m : ℕ} (hm : 1 ≤ m) (M' : Fin (m - 1) → T) :
    Finset.univ.val.map (fun t => S.resPart (consTuple (m := m) t M')) =
      ((S.resPart M').parts : Multiset ℕ).map (Gsub (S.resPart M')) +
        Multiset.replicate (2 * h - 2 * (S.resPart M').len) (S.resPart M').addOne +
          ((S.resPart M').parts : Multiset ℕ).map (Gadd (S.resPart M')) := by
  conv_lhs => rw [univ_split S M']
  rw [Multiset.map_add, Multiset.map_add]
  have hA : (Finset.univ.val.filter (fun u => 0 < diff S M' u)).map
      (fun t => S.resPart (consTuple (m := m) t M')) =
      ((S.resPart M').parts : Multiset ℕ).map (Gadd (S.resPart M')) := by
    rw [Multiset.map_congr rfl (g := Gadd (S.resPart M') ∘ diff S M'), ← Multiset.map_map,
      map_diff_filter]
    intro t ht
    rw [Multiset.mem_filter] at ht
    rw [resPart_consTuple S hm, if_pos ht.2]
    rfl
  have hB : (Finset.univ.val.filter (fun u => 0 < diff S M' (S.neg u))).map
      (fun t => S.resPart (consTuple (m := m) t M')) =
      ((S.resPart M').parts : Multiset ℕ).map (Gsub (S.resPart M')) := by
    rw [Multiset.map_congr rfl (g := Gsub (S.resPart M') ∘ (diff S M' ∘ S.neg)),
      ← Multiset.map_map, map_diff_neg_filter]
    intro t ht
    rw [Multiset.mem_filter] at ht
    have h0 : ¬ 0 < diff S M' t := by
      have := diff_neg_eq_zero S M' ht.2
      rw [S.neg_neg] at this
      omega
    rw [resPart_consTuple S hm, if_neg h0, if_pos ht.2]
    rfl
  have hC : (Finset.univ.val.filter
      (fun u => ¬ 0 < diff S M' u ∧ ¬ 0 < diff S M' (S.neg u))).map
      (fun t => S.resPart (consTuple (m := m) t M')) =
      Multiset.replicate (2 * h - 2 * (S.resPart M').len) (S.resPart M').addOne := by
    rw [Multiset.map_congr rfl (g := Function.const _ (S.resPart M').addOne),
      Multiset.map_const]
    · have := two_len_add_card S M'
      congr 1
      omega
    intro t ht
    rw [Multiset.mem_filter] at ht
    rw [resPart_consTuple S hm, if_neg ht.2.1, if_neg ht.2.2]
    rfl
  rw [hA, hB, hC]
  abel

/-- Helper for part (i) of `q_P1_fibres.md`: discarding zeros does not change a sum. -/
lemma sum_filter_pos (s : Multiset ℕ) : (s.filter (0 < ·)).sum = s.sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.filter_cons]
    split_ifs with ha
    · simp [ih]
    · simp [ih]; omega

/-- Helper for part (i) of `q_P1_fibres.md`: `|ofMultiset s| = Σ s`. -/
lemma size_ofMultiset (s : Multiset ℕ) : (ofMultiset s).size = s.sum := by
  rw [Partition.size, ← Multiset.sum_coe, ofMultiset_parts, sum_filter_pos]

/-- Helper for part (i) of `q_P1_fibres.md`: `|μ + e_j| = |μ| + 1`. -/
lemma size_Gadd (μ : Partition) {x : ℕ} (hx : x ∈ (μ.parts : Multiset ℕ)) :
    (Gadd μ x).size = μ.size + 1 := by
  rw [Gadd, size_ofMultiset, Partition.size, ← Multiset.sum_coe, ← Multiset.sum_erase hx,
    Multiset.sum_add, Multiset.sum_singleton]
  ring

/-- Helper for part (i) of `q_P1_fibres.md`: `|μ − e_j| + 1 = |μ|`. -/
lemma size_Gsub (μ : Partition) {x : ℕ} (hx : x ∈ (μ.parts : Multiset ℕ)) :
    (Gsub μ x).size + 1 = μ.size := by
  have hpos : 0 < x := μ.pos x (by simpa using hx)
  rw [Gsub, size_ofMultiset, Partition.size, ← Multiset.sum_coe, ← Multiset.sum_erase hx,
    Multiset.sum_add, Multiset.sum_singleton]
  omega

/-- Helper for part (i) of `q_P1_fibres.md`: `|μ ⊔ 1| = |μ| + 1`. -/
lemma size_addOne (μ : Partition) : μ.addOne.size = μ.size + 1 := by
  simp [Partition.size, Partition.addOne]

/-- Helper for part (i) of `q_P1_fibres.md`: `|λ(M)| ≡ m (mod 2)`, by induction on `m`, using
that adding one value changes `|λ|` by `± 1`. -/
lemma size_resPart_mod (S : FibreSetting T h) :
    ∀ (m : ℕ) (M : Fin m → T), (S.resPart M).size % 2 = m % 2
  | 0, M => by
    rw [FibreSetting.resPart, size_ofMultiset]
    simp [cnt]
  | n + 1, M => by
    have hM : M = consTuple (m := n + 1) (M 0) (fun i : Fin n => M i.succ) := by
      funext i
      cases i using Fin.cases with
      | zero => simp [consTuple]
      | succ i => simp [consTuple]
    have ih := size_resPart_mod S n (fun i : Fin n => M i.succ)
    rw [hM, resPart_consTuple S (m := n + 1) (by omega)]
    split_ifs with h1 h2
    · rw [size_Gadd]
      · omega
      · rw [← map_diff_filter]
        exact Multiset.mem_map_of_mem _ (Multiset.mem_filter.mpr ⟨Finset.mem_univ_val _, h1⟩)
    · have := size_Gsub (S.resPart (fun i : Fin n => M i.succ))
        (x := diff S (fun i : Fin n => M i.succ) (S.neg (M 0))) (by
          rw [← map_diff_neg_filter]
          exact Multiset.mem_map_of_mem (diff S (fun i : Fin n => M i.succ) ∘ S.neg)
            (Multiset.mem_filter.mpr ⟨Finset.mem_univ_val _, h2⟩))
      omega
    · rw [size_addOne]
      omega

end Fibres

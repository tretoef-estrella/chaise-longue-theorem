module

public import RequestProject.Odd3.Defs
public import RequestProject.Tight.Lemmas
public import RequestProject.TheoremB.Matchings

/-!
# Sets of pairwise disjoint pairs and the products `D_P` (`q_odd3.md`)

Auxiliary facts used in the proof of parts (ii) and (iv) of the Theorem of `q_odd3.md`: the
factor `D(a, b) = y_a^2 − y_a y_b + y_b^2`, the size of the support of a set of pairs, adding a
pair, and shifting the indices `{1, …, m − 1}` to `{2, …, m}` (the identification of `C_{m−1}`
with the ring in the variables `y_2, …, y_m`).
-/

@[expose] public section

namespace Odd3

open Peel Tight

set_option synthInstance.maxHeartbeats 200000

variable {F : Type*} [Field F]

/-- Setting of `q_odd3.md`: `D(a, b) = y_a^2 − y_a y_b + y_b^2` (for `q = 4`). -/
lemma D_eq {m : ℕ} (a b : Fin m) :
    D F 4 a b = y F 4 a ^ 2 - y F 4 a * y F 4 b + y F 4 b ^ 2 := by
  simp [D, Finset.sum_range_succ]
  ring

/-- Setting of `q_odd3.md`: `D(a, b)` is symmetric in `a, b`. -/
lemma D_comm {m : ℕ} (a b : Fin m) : D F 4 a b = D F 4 b a := by
  rw [D_eq, D_eq]; ring

/-- Setting of `q_odd3.md`: the factor of a pair `{a, b}` (`a ≠ b`, in either order) is
`D(a, b) = y_a^2 − y_a y_b + y_b^2`. -/
lemma pairD_eq {m : ℕ} {a b : Fin m} (h : a ≠ b) :
    pairD F 4 {a, b} = y F 4 a ^ 2 - y F 4 a * y F 4 b + y F 4 b ^ 2 := by
  rcases lt_or_gt_of_ne h with h | h
  · rw [TheoremB.pairD_of_lt F 4 h, D_eq]
  · rw [Finset.pair_comm, TheoremB.pairD_of_lt F 4 h, D_eq]; ring

/-- Proof of part (ii) of `q_odd3.md` (auxiliary): membership in the support of `P`. -/
lemma mem_supp {m : ℕ} {P : Finset (Finset (Fin m))} {x : Fin m} :
    x ∈ supp P ↔ ∃ e ∈ P, x ∈ e := by
  simp [supp, Finset.mem_sup]

/-- Proof of part (ii) of `q_odd3.md` (auxiliary): `k` disjoint pairs cover `2k` indices. -/
lemma card_supp {m : ℕ} {P : Finset (Finset (Fin m))} (hP : IsPairs P) :
    (supp P).card = 2 * P.card := by
  rw [supp, Finset.sup_eq_biUnion, Finset.card_biUnion (fun e he e' he' hne => hP.2 he he' hne)]
  have : ∑ u ∈ P, (id u).card = ∑ u ∈ P, 2 := Finset.sum_congr rfl (fun e he => hP.1 e he)
  rw [this, Finset.sum_const, smul_eq_mul, mul_comm]

/-- Proof of part (ii) of `q_odd3.md` (auxiliary): the empty set of pairs. -/
lemma isPairs_empty {m : ℕ} : IsPairs (∅ : Finset (Finset (Fin m))) :=
  ⟨by simp, by simp⟩

/-- Proof of part (ii) of `q_odd3.md` (auxiliary): `D_∅ = 1`. -/
@[simp] lemma DP_empty {m : ℕ} : DP F (∅ : Finset (Finset (Fin m))) = 1 := by
  simp [DP]

/-- Proof of part (ii) of `q_odd3.md` (auxiliary): the support of `P ∪ {{a, b}}`. -/
lemma supp_insert {m : ℕ} (e : Finset (Fin m)) (P : Finset (Finset (Fin m))) :
    supp (insert e P) = e ∪ supp P := by
  simp [supp]

/-- Proof of part (ii) of `q_odd3.md` (auxiliary): adding a pair `{a, b}` of free indices to `P`
gives a set of pairs. -/
lemma isPairs_insert {m : ℕ} {P : Finset (Finset (Fin m))} (hP : IsPairs P) {a b : Fin m}
    (hab : a ≠ b) (ha : a ∉ supp P) (hb : b ∉ supp P) : IsPairs (insert {a, b} P) := by
  refine ⟨fun e he => ?_, ?_⟩
  · rcases Finset.mem_insert.1 he with rfl | he
    · exact Finset.card_pair hab
    · exact hP.1 e he
  · rw [Finset.coe_insert]
    refine hP.2.insert fun e he _ => ?_
    refine Finset.disjoint_left.2 fun x hx hx' => ?_
    have hx2 : x = a ∨ x = b := by simpa using hx
    rcases hx2 with rfl | rfl
    · exact ha (mem_supp.2 ⟨e, he, hx'⟩)
    · exact hb (mem_supp.2 ⟨e, he, hx'⟩)

/-- Proof of part (ii) of `q_odd3.md` (auxiliary): a pair of free indices is not in `P`. -/
lemma pair_notMem {m : ℕ} {P : Finset (Finset (Fin m))} {a b : Fin m} (ha : a ∉ supp P) :
    ({a, b} : Finset (Fin m)) ∉ P :=
  fun h => ha (mem_supp.2 ⟨_, h, by simp⟩)

/-- Proof of part (ii) of `q_odd3.md` (auxiliary): `|P ∪ {{a, b}}| = |P| + 1`. -/
lemma card_insert_pair {m : ℕ} {P : Finset (Finset (Fin m))} {a b : Fin m} (ha : a ∉ supp P) :
    (insert {a, b} P).card = P.card + 1 :=
  Finset.card_insert_of_notMem (pair_notMem ha)

/-- Proof of part (ii) of `q_odd3.md` (auxiliary): `D_{P ∪ {{a,b}}} = D(a, b)·D_P`. -/
lemma DP_insert {m : ℕ} {P : Finset (Finset (Fin m))} {a b : Fin m} (hab : a ≠ b)
    (ha : a ∉ supp P) :
    DP F (insert {a, b} P) = (y F 4 a ^ 2 - y F 4 a * y F 4 b + y F 4 b ^ 2) * DP F P := by
  rw [DP, Finset.prod_insert (pair_notMem ha), pairD_eq hab]; rfl

/-- Proof of part (ii) of `q_odd3.md` (auxiliary): a free index exists when the pairs cover fewer
than all indices. -/
lemma exists_notMem {m : ℕ} (s : Finset (Fin m)) (h : s.card < m) : ∃ x, x ∉ s := by
  by_contra hc
  push_neg at hc
  have : s = Finset.univ := Finset.eq_univ_of_forall hc
  rw [this, Finset.card_univ, Fintype.card_fin] at h
  exact lt_irrefl _ h

/-- Proof of part (ii) of `q_odd3.md` (auxiliary): the embedding `Fin n ↪ Fin (n+1)`,
`i ↦ i + 1`, applied to a set of indices (the shift `{1, …, n} → {2, …, n + 1}`). -/
def liftE (n : ℕ) : Finset (Fin n) ↪ Finset (Fin (n + 1)) :=
  ⟨fun e => e.map (Fin.succEmb n), Finset.map_injective _⟩

/-- Proof of part (ii) of `q_odd3.md` (auxiliary): a set of pairs of `{1, …, n}` regarded as a set
of pairs of `{2, …, n + 1}`. -/
def liftP {n : ℕ} (P : Finset (Finset (Fin n))) : Finset (Finset (Fin (n + 1))) :=
  P.map (liftE n)

/-- Proof of part (ii) of `q_odd3.md` (auxiliary): shifting preserves the size. -/
lemma card_liftP {n : ℕ} (P : Finset (Finset (Fin n))) : (liftP P).card = P.card :=
  Finset.card_map _

/-- Proof of part (ii) of `q_odd3.md` (auxiliary): the support of the shifted set of pairs. -/
lemma mem_supp_liftP {n : ℕ} {P : Finset (Finset (Fin n))} {x : Fin (n + 1)} :
    x ∈ supp (liftP P) ↔ ∃ i ∈ supp P, x = i.succ := by
  simp only [mem_supp, liftP, liftE, Finset.mem_map, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨_, ⟨e, he, rfl⟩, hx⟩
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.1 hx
    exact ⟨i, ⟨e, he, hi⟩, rfl⟩
  · rintro ⟨i, ⟨e, he, hi⟩, rfl⟩
    exact ⟨_, ⟨e, he, rfl⟩, Finset.mem_map_of_mem _ hi⟩

/-- Proof of part (ii) of `q_odd3.md` (auxiliary): the new index `1` (here `0`) is free for a
shifted set of pairs. -/
lemma zero_notMem_supp_liftP {n : ℕ} (P : Finset (Finset (Fin n))) : (0 : Fin (n + 1)) ∉ supp (liftP P) := by
  rw [mem_supp_liftP]
  rintro ⟨i, -, h⟩
  exact Fin.succ_ne_zero i h.symm

/-- Proof of part (ii) of `q_odd3.md` (auxiliary): a shifted free index is free. -/
lemma succ_mem_supp_liftP {n : ℕ} {P : Finset (Finset (Fin n))} {i : Fin n} :
    i.succ ∈ supp (liftP P) ↔ i ∈ supp P := by
  rw [mem_supp_liftP]
  constructor
  · rintro ⟨j, hj, h⟩
    rwa [Fin.succ_inj.1 h]
  · exact fun h => ⟨i, h, rfl⟩

/-- Proof of part (ii) of `q_odd3.md` (auxiliary): shifting preserves "set of pairs". -/
lemma isPairs_liftP {n : ℕ} {P : Finset (Finset (Fin n))} (hP : IsPairs P) : IsPairs (liftP P) := by
  refine ⟨fun e he => ?_, ?_⟩
  · obtain ⟨e, he', rfl⟩ := Finset.mem_map.1 he
    simp [liftE, hP.1 e he']
  · intro e he e' he' hne
    obtain ⟨e, he1, rfl⟩ := Finset.mem_map.1 (Finset.mem_coe.1 he)
    obtain ⟨e', he1', rfl⟩ := Finset.mem_map.1 (Finset.mem_coe.1 he')
    have hne' : e ≠ e' := fun h => hne (by rw [h])
    exact (Finset.disjoint_map _).2 (hP.2 he1 he1' hne')

/-- Proof of part (ii) of `q_odd3.md` (auxiliary): the inclusion `C_{m−1} → C_m` sends the variable
`y_{i}` of `C_{m−1}` to `y_{i+1}` of `C_m`. -/
lemma incl_y (n : ℕ) (i : Fin n) : incl F 4 n (y F 4 i) = y F 4 i.succ := by
  simp [incl, Tight.y]

/-- Proof of part (ii) of `q_odd3.md` (auxiliary): the inclusion `C_{m−1} → C_m` sends `D_P` to
`D_{P'}`, `P'` the shifted set of pairs. -/
lemma incl_DP {n : ℕ} {P : Finset (Finset (Fin n))} (hP : IsPairs P) :
    incl F 4 n (DP F P) = DP F (liftP P) := by
  rw [DP, DP, map_prod, liftP, Finset.prod_map]
  refine Finset.prod_congr rfl fun e he => ?_
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 (hP.1 e he)
  have : (liftE n) {a, b} = {a.succ, b.succ} := by simp [liftE]
  rw [this, pairD_eq hab, pairD_eq (fun h => hab (Fin.succ_inj.1 h))]
  simp [incl_y]

end Odd3

end

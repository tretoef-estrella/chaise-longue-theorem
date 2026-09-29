module

public import RequestProject.TheoremB.Root

/-!
# Parts (ii) and (iii) of the Theorem of `q_theorem_B_lower.md`: auxiliary lemmas
-/

@[expose] public section

namespace TheoremB

open ChainLemma Fibres Tight Lifts

variable {T : Type*} [Fintype T] [DecidableEq T] {h : ℕ}

omit [Fintype T] in
/-- Proof of part (ii) of `q_theorem_B_lower.md` (auxiliary): prepending an entry `t` adds one
to the count of `t`. -/
lemma cnt_cons {n : ℕ} (t : T) (M : Fin n → T) (u : T) :
    cnt (Fin.cons t M : Fin (n + 1) → T) u = cnt M u + if t = u then 1 else 0 := by
  simp only [cnt, Finset.card_filter, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  rw [add_comm]

omit [Fintype T] in
/-- Proof of part (iii) of `q_theorem_B_lower.md` (auxiliary): appending a last entry `z` adds
one to the count of `z`. -/
lemma cnt_snoc {n : ℕ} (M : Fin n → T) (z : T) (u : T) :
    cnt (Fin.snoc M z : Fin (n + 1) → T) u = cnt M u + if z = u then 1 else 0 := by
  simp only [cnt, Finset.card_filter, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]

omit [Fintype T] in
/-- Proof of part (iii) of `q_theorem_B_lower.md` (auxiliary): counts of a tuple in terms of its
initial part and its last entry. -/
lemma cnt_eq_init {n : ℕ} (z : Fin (n + 1) → T) (u : T) :
    cnt z u = cnt (Fin.init z) u + if z (Fin.last n) = u then 1 else 0 := by
  conv_lhs => rw [← Fin.snoc_init_self z]
  exact cnt_snoc _ _ _

/-- **Theorem, part (iii)** of `q_theorem_B_lower.md`, "conversely": deleting the last entry `z`
of a closed `N`-tuple leaves a tuple in `T^{n'}` with `ν = k`. -/
lemma init_mem_Gamma' (S : FibreSetting T h) (k : ℕ) {z : Fin (2 * k + 2) → T}
    (hz : z ∈ closedTuples S (2 * k + 2)) : Fin.init z ∈ Gamma' S k := by
  simp only [closedTuples, Finset.mem_filter, Finset.mem_univ, true_and] at hz
  simp only [Gamma', Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← resPart_eq_one_iff_nu, resPart_eq_one_iff, size_resPart]
  obtain ⟨w, hw⟩ : ∃ w, z (Fin.last (2 * k + 1)) = w := ⟨_, rfl⟩
  have key : ∀ u, cnt (Fin.init z) u - cnt (Fin.init z) (S.neg u) =
      if u = S.neg w then 1 else 0 := by
    intro u
    have h1 := cnt_eq_init z u
    have h2 := cnt_eq_init z (S.neg u)
    rw [hw] at h1 h2
    have h3 := hz u
    have hne := S.neg_ne u
    by_cases hu : u = S.neg w
    · have this : w = S.neg u := by rw [hu, S.neg_neg]
      have hwu : w ≠ u := fun h => hne (this.symm.trans h)
      rw [if_pos hu]
      rw [if_neg hwu] at h1
      rw [if_pos this] at h2
      omega
    · rw [if_neg hu]
      have : w ≠ S.neg u := fun h => hu (by rw [h, S.neg_neg])
      rw [if_neg this] at h2
      split_ifs at h1 <;> omega
  rw [Finset.sum_congr rfl fun u _ => key u, Finset.sum_ite_eq']
  simp

/-- **Theorem, part (iii)** of `q_theorem_B_lower.md`: the bijection `Γ' → {closed tuples}`;
if `ν(M) = k`, exactly one class is unbalanced, by exactly one, with majority value `w`, and
appending `−w` gives a closed `N`-tuple (whose initial part is `M`). -/
lemma exists_closed_of_mem_Gamma' (S : FibreSetting T h) (k : ℕ) {M : Fin (2 * k + 1) → T}
    (hM : M ∈ Gamma' S k) : ∃ w, (Fin.snoc M (S.neg w) : Fin (2 * k + 2) → T) ∈
      closedTuples S (2 * k + 2) := by
  simp only [Gamma', Finset.mem_filter, Finset.mem_univ, true_and] at hM
  rw [← resPart_eq_one_iff_nu, resPart_eq_one_iff, size_resPart] at hM
  set d : T → ℕ := fun u => cnt M u - cnt M (S.neg u) with hd
  obtain ⟨w, hw⟩ : ∃ w, 1 ≤ d w := by
    by_contra hcon
    push_neg at hcon
    have : ∑ u, d u = 0 := Finset.sum_eq_zero fun u _ => by have := hcon u; omega
    change ∑ u, d u = 1 at hM
    omega
  have hsplit := Finset.add_sum_erase Finset.univ d (Finset.mem_univ w)
  change ∑ u, d u = 1 at hM
  have hrest : ∀ u, u ≠ w → d u = 0 := by
    intro u hu
    have := Finset.single_le_sum (f := d) (fun _ _ => Nat.zero_le _)
      (Finset.mem_erase.2 ⟨hu, Finset.mem_univ u⟩)
    omega
  have hdw : d w = 1 := by
    have := Finset.sum_eq_zero (s := Finset.univ.erase w) (f := d)
      fun u hu => hrest u (Finset.ne_of_mem_erase hu)
    omega
  refine ⟨w, ?_⟩
  simp only [closedTuples, Finset.mem_filter, Finset.mem_univ, true_and]
  intro u
  rw [cnt_snoc, cnt_snoc]
  have hne := S.neg_ne w
  by_cases huw : u = w
  · subst huw
    rw [if_neg hne, if_pos rfl]
    simp only [hd] at hdw
    omega
  by_cases hun : u = S.neg w
  · subst hun
    rw [if_pos rfl, S.neg_neg, if_neg hne]
    have := hrest (S.neg w) hne
    simp only [hd, S.neg_neg] at this hdw
    omega
  · rw [if_neg (Ne.symm hun), if_neg (fun h => huw (by rw [← S.neg_neg u, ← h, S.neg_neg]))]
    have h1 := hrest u huw
    have h2 := hrest (S.neg u) (fun h => hun (by rw [← h, S.neg_neg]))
    simp only [hd, S.neg_neg] at h1 h2
    omega

/-- **Theorem, part (iii)** of `q_theorem_B_lower.md`: `|Γ'| = #{closed tuples in T^N}`, by the
bijection "append `−w`" / "delete the last entry". -/
theorem card_Gamma'_eq_card_closedTuples (S : FibreSetting T h) (k : ℕ) :
    (Gamma' S k).card = (closedTuples S (2 * k + 2)).card := by
  symm
  refine Finset.card_nbij (fun z => Fin.init z) (fun z hz => init_mem_Gamma' S k hz) ?_ ?_
  · intro z1 hz1 z2 hz2 heq
    simp only [Finset.coe_filter, closedTuples, Finset.mem_univ, true_and,
      Set.mem_setOf_eq] at hz1 hz2
    have heq : Fin.init z1 = Fin.init z2 := heq
    have hlast : z1 (Fin.last _) = z2 (Fin.last _) := by
      by_contra hne
      set w1 := z1 (Fin.last (2 * k + 1))
      set w2 := z2 (Fin.last (2 * k + 1))
      have a1 := hz1 w1
      have a2 := hz2 w1
      rw [cnt_eq_init z1, cnt_eq_init z1 (S.neg w1)] at a1
      rw [cnt_eq_init z2, cnt_eq_init z2 (S.neg w1), ← heq] at a2
      have hn := S.neg_ne w1
      rw [if_pos rfl, if_neg (fun h => hn h.symm)] at a1
      rw [if_neg (Ne.symm hne)] at a2
      split_ifs at a2 <;> omega
    rw [← Fin.snoc_init_self z1, ← Fin.snoc_init_self z2, heq, hlast]
  · intro M hM
    obtain ⟨w, hw⟩ := exists_closed_of_mem_Gamma' S k hM
    exact ⟨_, hw, Fin.init_snoc _ _⟩

end TheoremB

end

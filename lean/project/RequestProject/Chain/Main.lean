module

public import RequestProject.Chain.Lemmas

/-!
# The chain lemma (`q_chain_lemma.md`)

This file proves parts (a), (b) and (c) of the **Lemma (chain)** of `q_chain_lemma.md`.
Partitions are encoded as weakly decreasing lists of positive naturals (see `ChainLemma.Partition`
in `RequestProject/Chain/Defs.lean`).
-/

@[expose] public section

namespace ChainLemma

namespace Partition

/-- **Lemma (chain), part (a)**, first identity, of `q_chain_lemma.md`: for every `t ≥ 1` and
`1 ≤ j ≤ ℓ`, `S_t(μ − e_j) = S_t(μ) − [t ≥ r̄_j]`.
(The subtraction is in `ℕ`; it never truncates, since `S_t(μ) ≥ 1` whenever `t ≥ r̄_j`.
The hypothesis `1 ≤ t` is kept as in the file; the identity also holds for `t = 0`.) -/
theorem S_subE (μ : Partition) (t j : ℕ) (ht : 1 ≤ t) (hj : 1 ≤ j) (hjl : j ≤ μ.len) :
    S t (μ.subE j) = S t μ - (if μ.rbar j ≤ t then 1 else 0) := by
  have key := sum_take_of_count μ.parts (μ.subE j).parts μ.sorted (μ.subE j).sorted
    (μ.row j) (μ.row_pos j hj hjl) (fun k hk => μ.countP_subE j hj hjl k hk) t
  rw [S_eq_sum_take, S_eq_sum_take, μ.rbar_eq j hj hjl]
  omega

/-- **Lemma (chain), part (a)**, second identity, of `q_chain_lemma.md`: for every `t ≥ 1` and
`1 ≤ j ≤ ℓ`, `S_t(μ + e_j) = S_t(μ) + [t ≥ r̲_j]`.
(The hypothesis `1 ≤ t` is kept as in the file; the identity also holds for `t = 0`.) -/
theorem S_addE (μ : Partition) (t j : ℕ) (ht : 1 ≤ t) (hj : 1 ≤ j) (hjl : j ≤ μ.len) :
    S t (μ.addE j) = S t μ + (if μ.rlow j ≤ t then 1 else 0) := by
  have key := sum_take_of_count (μ.addE j).parts μ.parts (μ.addE j).sorted μ.sorted
    (μ.row j + 1) (by omega) (fun k _ => μ.countP_addE j hj hjl k) t
  have hc := μ.countP_addE j hj hjl (μ.row j + 1)
  simp only [if_true] at hc
  rw [S_eq_sum_take, S_eq_sum_take, μ.rlow_eq j hj hjl]
  rw [← hc] at key
  omega

/-- **Lemma (chain), part (a)**, third identity, of `q_chain_lemma.md`: for every `t ≥ 1`,
`S_t(μ ⊔ 1) = S_t(μ) + [t > ℓ]`.
(The hypothesis `1 ≤ t` is kept as in the file; the identity also holds for `t = 0`.) -/
theorem S_addOne (μ : Partition) (t : ℕ) (ht : 1 ≤ t) :
    S t μ.addOne = S t μ + (if μ.len < t then 1 else 0) := by
  have key := sum_take_of_count μ.addOne.parts μ.parts μ.addOne.sorted μ.sorted
    1 le_rfl (fun k hk => μ.countP_addOne k hk) t
  have hc : μ.addOne.parts.countP (fun x => decide (1 ≤ x)) = μ.len + 1 := by
    rw [List.countP_eq_length.2]
    · simp [addOne, len]
    · intro x hx; simpa using μ.addOne.pos x hx
  rw [hc] at key
  rw [S_eq_sum_take, S_eq_sum_take]
  split_ifs at key ⊢ <;> omega

end Partition

open Partition

/-- Weak dominance is reflexive (**Setting, "Weak dominance"** of `q_chain_lemma.md`: it is a
partial order; used in the proof of part (b)). -/
theorem WeakDom.refl (μ : Partition) : μ ≼ μ := fun _ _ => le_rfl

/-- Weak dominance is transitive (**Setting, "Weak dominance"** of `q_chain_lemma.md`: it is a
partial order; used in the proof of part (b)). -/
theorem WeakDom.trans {a b c : Partition} (h1 : a ≼ b) (h2 : b ≼ c) : a ≼ c :=
  fun t ht => (h1 t ht).trans (h2 t ht)

namespace Partition

/-- Proof of part (b) of `q_chain_lemma.md` (a consecutive pair): `μ − e_j ≼ μ`. -/
lemma subE_le_self (μ : Partition) (j : ℕ) (hj : 1 ≤ j) (hjl : j ≤ μ.len) : μ.subE j ≼ μ := by
  intro t ht; rw [S_subE μ t j ht hj hjl]; omega

/-- Proof of part (b) of `q_chain_lemma.md` (a consecutive pair): `μ ≼ μ + e_j`. -/
lemma self_le_addE (μ : Partition) (j : ℕ) (hj : 1 ≤ j) (hjl : j ≤ μ.len) : μ ≼ μ.addE j := by
  intro t ht; rw [S_addE μ t j ht hj hjl]; omega

/-- Proof of part (b) of `q_chain_lemma.md` (a consecutive pair): `μ ≼ μ ⊔ 1`. -/
lemma self_le_addOne (μ : Partition) : μ ≼ μ.addOne := by
  intro t ht; rw [S_addOne μ t ht]; omega

/-- Proof of part (b) of `q_chain_lemma.md` (a consecutive pair): `μ − e_j ≼ μ − e_{j+1}` for `1 ≤ j < ℓ`. -/
lemma subE_mono (μ : Partition) (j : ℕ) (hj : 1 ≤ j) (hjl : j + 1 ≤ μ.len) :
    μ.subE j ≼ μ.subE (j + 1) := by
  intro t ht
  rw [S_subE μ t j ht hj (by omega), S_subE μ t (j + 1) ht (by omega) hjl,
    μ.rbar_eq j hj (by omega), μ.rbar_eq (j + 1) (by omega) hjl]
  have hr := μ.row_anti j (j + 1) hj (by omega) hjl
  have : μ.parts.countP (fun x => decide (μ.row j ≤ x)) ≤
      μ.parts.countP (fun x => decide (μ.row (j + 1) ≤ x)) :=
    List.countP_mono_left (fun x _ h => by simp at h ⊢; omega)
  split_ifs <;> omega

/-- Proof of part (b) of `q_chain_lemma.md` (a consecutive pair): `μ ⊔ 1 ≼ μ + e_ℓ` when `ℓ ≥ 1`. -/
lemma addOne_le_addE (μ : Partition) (j : ℕ) (hj : 1 ≤ j) (hjl : j = μ.len) :
    μ.addOne ≼ μ.addE j := by
  intro t ht
  rw [S_addOne μ t ht, S_addE μ t j ht hj hjl.le, μ.rlow_eq j hj hjl.le]
  have := μ.count_gt_le j hj hjl.le
  split_ifs <;> omega

/-- Proof of part (b) of `q_chain_lemma.md` (a consecutive pair): `μ + e_{j+1} ≼ μ + e_j` for `1 ≤ j < ℓ`. -/
lemma addE_mono (μ : Partition) (j : ℕ) (hj : 1 ≤ j) (hjl : j + 1 ≤ μ.len) :
    μ.addE (j + 1) ≼ μ.addE j := by
  intro t ht
  rw [S_addE μ t j ht hj (by omega), S_addE μ t (j + 1) ht (by omega) hjl,
    μ.rlow_eq j hj (by omega), μ.rlow_eq (j + 1) (by omega) hjl]
  have hr := μ.row_anti j (j + 1) hj (by omega) hjl
  have : μ.parts.countP (fun x => decide (μ.row j + 1 ≤ x)) ≤
      μ.parts.countP (fun x => decide (μ.row (j + 1) + 1 ≤ x)) :=
    List.countP_mono_left (fun x _ h => by simp at h ⊢; omega)
  split_ifs <;> omega

/-- **Lemma (chain), part (b)**, of `q_chain_lemma.md`: for `L ≥ 2ℓ`, the options are weakly
increasing, `opt_p(μ) ≼ opt_{p+1}(μ)` for every `1 ≤ p < L`. -/
theorem opt_le_opt_succ (μ : Partition) (L p : ℕ) (hL : 2 * μ.len ≤ L) (hp : 1 ≤ p)
    (hpL : p < L) : μ.opt L p ≼ μ.opt L (p + 1) := by
  unfold opt
  have e1 : L + 1 - (p + 1) = L - p := by omega
  rw [e1]
  by_cases h1 : p + 1 ≤ μ.len
  · rw [if_pos (by omega), if_pos h1]
    exact μ.subE_mono p hp h1
  by_cases h2 : p ≤ μ.len
  · rw [if_pos h2, if_neg h1]
    split_ifs with h3
    · exact (μ.subE_le_self p hp h2).trans μ.self_le_addOne
    · exact (μ.subE_le_self p hp h2).trans (μ.self_le_addE _ (by omega) (by omega))
  rw [if_neg h2, if_neg h1]
  by_cases h3 : p + 1 ≤ L - μ.len
  · rw [if_pos (by omega), if_pos h3]
    exact WeakDom.refl _
  rw [if_neg h3]
  by_cases h4 : p ≤ L - μ.len
  · rw [if_pos h4]
    exact μ.addOne_le_addE _ (by omega) (by omega)
  · rw [if_neg h4]
    have e2 : L + 1 - p = (L - p) + 1 := by omega
    rw [e2]
    exact μ.addE_mono _ (by omega) (by omega)

/-- **Lemma (chain), part (b)**, of `q_chain_lemma.md`, chain form: for `L ≥ 2ℓ`,
`opt_1(μ) ≼ opt_2(μ) ≼ ⋯ ≼ opt_L(μ)`, i.e. `opt_p(μ) ≼ opt_{p'}(μ)` whenever
`1 ≤ p ≤ p' ≤ L` (by transitivity of `≼`). -/
theorem opt_mono (μ : Partition) (L p p' : ℕ) (hL : 2 * μ.len ≤ L) (hp : 1 ≤ p)
    (hpp' : p ≤ p') (hp'L : p' ≤ L) : μ.opt L p ≼ μ.opt L p' := by
  induction p', hpp' using Nat.le_induction with
  | base => exact WeakDom.refl _
  | succ n hn ih =>
    exact (ih (by omega)).trans (μ.opt_le_opt_succ L n hL (by omega) (by omega))

open Classical in
/-- **Lemma (chain), part (c)**, of `q_chain_lemma.md`: for `L ≥ 2ℓ` and every down-set `Λ`, the
set `{p ∈ {1, …, L} : opt_p(μ) ∈ Λ}` is the initial segment `{1, …, F}` of `{1, …, L}` (possibly
empty), where `F := #{p ∈ {1, …, L} : opt_p(μ) ∈ Λ}`. -/
theorem opt_mem_initial_segment (μ : Partition) (L : ℕ) (hL : 2 * μ.len ≤ L)
    (Λ : Set Partition) (hΛ : IsDownSet Λ) :
    (Finset.Icc 1 L).filter (fun p => μ.opt L p ∈ Λ) =
      Finset.Icc 1 ((Finset.Icc 1 L).filter (fun p => μ.opt L p ∈ Λ)).card := by
  set A := (Finset.Icc 1 L).filter (fun p => μ.opt L p ∈ Λ) with hA
  have hdown : ∀ p ∈ A, ∀ p', 1 ≤ p' → p' ≤ p → p' ∈ A := by
    intro p hp p' hp' hp'p
    simp only [hA, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
    exact ⟨⟨hp', by omega⟩, hΛ _ _ (μ.opt_mono L p' p hL hp' hp'p hp.1.2) hp.2⟩
  have hsub : A ⊆ Finset.Icc 1 L := Finset.filter_subset _ _
  have hAeq : A = Finset.Icc 1 (A.sup id) := by
    ext p
    simp only [Finset.mem_Icc]
    constructor
    · intro hp
      exact ⟨(Finset.mem_Icc.1 (hsub hp)).1, Finset.le_sup (f := id) hp⟩
    · rintro ⟨hp1, hp2⟩
      rcases A.eq_empty_or_nonempty with hAe | hAne
      · simp [hAe] at hp2; omega
      · obtain ⟨m, hm, hmax⟩ := Finset.exists_mem_eq_sup A hAne id
        exact hdown m hm p hp1 (by simpa [hmax] using hp2)
  conv_rhs => rw [hAeq]
  rw [Nat.card_Icc, Nat.add_sub_cancel]
  exact hAeq

end Partition

end ChainLemma

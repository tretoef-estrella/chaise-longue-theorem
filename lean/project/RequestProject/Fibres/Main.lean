module

public import RequestProject.Fibres.Lemmas

/-!
# The fibres of a point set depend only on the residue partition (`q_P1_fibres.md`)

This file proves parts (i), (ii) and (iii) of the **Proposition** of `q_P1_fibres.md`.
The **Setting** (`T`, `u ↦ −u`, `|T| = 2h`, `h ≥ 1`) is bundled in `S : FibreSetting T h`,
`u ↦ −u` is `S.neg`, and the residue partition `λ(M)` is `S.resPart M`. Partitions, `ℓ(μ)`
(`len`), `|μ|` (`size`) and `opt_p(μ)` (`opt`, with `L = 2h`) are those of
`RequestProject/Chain/Defs.lean` and `RequestProject/Monotone/Defs.lean`; the tuple `(t, M')`,
the fibre `F(M')` and `Z_{>i}` are `consTuple`, `fiber` and `Zgt` of
`RequestProject/Peel/Defs.lean`. A tail `M' ∈ T^{m−1}` only makes sense for `m ≥ 1`, which is
the hypothesis `hm : 1 ≤ m` in (ii) and (iii) (the same convention as in `RequestProject/Peel/`).
-/

@[expose] public section

namespace Fibres

open ChainLemma ChainLemma.Partition Peel

variable {T : Type*} [Fintype T] [DecidableEq T] {h : ℕ}

/-- **Proposition, part (i)** of `q_P1_fibres.md`: for every `M ∈ T^m`, `ℓ(λ(M)) ≤ h` and
`|λ(M)| ≡ m (mod 2)`. (In particular `L = 2h ≥ 2ℓ(λ(M))`, so `opt_p(λ(M))` is defined.) -/
theorem resPart_len_le_and_size_mod (S : FibreSetting T h) {m : ℕ} (M : Fin m → T) :
    (S.resPart M).len ≤ h ∧ (S.resPart M).size % 2 = m % 2 := by
  refine ⟨?_, size_resPart_mod S m M⟩
  have := two_len_add_card S M
  omega

/-- **Proposition, part (ii)** of `q_P1_fibres.md`: for every tail `M' ∈ T^{m−1}` with
`μ := λ(M')`, the multiset `{λ((t, M')) : t ∈ T}` (one entry for each of the `2h` elements `t`)
equals the multiset `{opt_p(μ) : p = 1, …, 2h}` (with `L = 2h`). -/
theorem multiset_resPart_consTuple_eq_opt (S : FibreSetting T h) {m : ℕ} (hm : 1 ≤ m)
    (M' : Fin (m - 1) → T) :
    Finset.univ.val.map (fun t => S.resPart (consTuple (m := m) t M')) =
      (Finset.Icc 1 (2 * h)).val.map (fun p => (S.resPart M').opt (2 * h) p) := by
  rw [map_resPart_consTuple S hm, map_opt_eq _ (resPart_len_le_and_size_mod S M').1]

open Classical in
/-- **Proposition, part (iii)** of `q_P1_fibres.md`, first statement: for every set `Λ` of
partitions and every tail `M'`, `#{t ∈ T : λ((t, M')) ∈ Λ} = F_Λ(λ(M'))`. -/
theorem card_resPart_consTuple_mem (S : FibreSetting T h) {m : ℕ} (hm : 1 ≤ m)
    (Λ : Set Partition) (M' : Fin (m - 1) → T) :
    (Finset.univ.filter fun t => S.resPart (consTuple (m := m) t M') ∈ Λ).card =
      FLam h Λ (S.resPart M') := by
  have h2 := congrArg (fun s => (s.filter (· ∈ Λ)).card)
    (multiset_resPart_consTuple_eq_opt S hm M')
  simp only [Multiset.filter_map, Multiset.card_map] at h2
  exact h2

open Classical in
/-- **Proposition, part (iii)** of `q_P1_fibres.md`, second statement: in the notation of
`q_peeling_lemma.md`, with `Z = Z_Λ := {M ∈ T^m : λ(M) ∈ Λ}`, `|F(M')| = F_Λ(λ(M'))`. -/
theorem card_fiber_ZLam (S : FibreSetting T h) {m : ℕ} (hm : 1 ≤ m) (Λ : Set Partition)
    (M' : Fin (m - 1) → T) :
    (fiber (S.ZLam m Λ) M').card = FLam h Λ (S.resPart M') := by
  rw [← card_resPart_consTuple_mem S hm Λ M']
  congr 1
  ext t
  simp [fiber, FibreSetting.ZLam]

open Classical in
/-- **Proposition, part (iii)** of `q_P1_fibres.md`, third statement: with `Z = Z_Λ`,
`Z_{>i} = {M' ∈ T^{m−1} : F_Λ(λ(M')) > i}` for every `i ≥ 0`. -/
theorem Zgt_ZLam (S : FibreSetting T h) {m : ℕ} (hm : 1 ≤ m) (Λ : Set Partition) (i : ℕ) :
    Zgt (S.ZLam m Λ) i = Finset.univ.filter fun M' => i < FLam h Λ (S.resPart M') := by
  ext M'
  simp [Zgt, card_fiber_ZLam S hm Λ M']

end Fibres

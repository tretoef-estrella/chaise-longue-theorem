module

public import RequestProject.TheoremB.Defs

/-!
# Part (i) of the Theorem of `q_theorem_B_lower.md` (the root): auxiliary lemmas
-/

@[expose] public section

namespace TheoremB

open ChainLemma Fibres Tight Lifts

set_option synthInstance.maxHeartbeats 200000

/-- Proof of part (i) of `q_theorem_B_lower.md` (auxiliary): the only partition of size `1` is
`(1)`. -/
lemma eq_one_of_size_eq_one (lam : Partition) (h : lam.size = 1) : lam = one := by
  obtain ⟨l, hs, hp⟩ := lam
  simp only [Partition.size] at h
  apply ChainLemma.Partition.ext
  simp only [one]
  match l, hp, h with
  | [], _, h => simp at h
  | a :: l, hp, h =>
    have ha : 0 < a := hp a (by simp)
    have hl : ∀ x ∈ l, 0 < x := fun x hx => hp x (by simp [hx])
    simp only [List.sum_cons] at h
    have hl0 : l.sum = 0 := by omega
    have : l = [] := by
      rw [List.eq_nil_iff_forall_not_mem]
      intro x hx
      have := List.le_sum_of_mem hx
      have := hl x hx
      omega
    subst this
    simp at h
    simp [h]

/-- Proof of part (i) of `q_theorem_B_lower.md` (auxiliary): `|(1)| = 1`. -/
lemma size_one : one.size = 1 := rfl

/-- Proof of part (i) of `q_theorem_B_lower.md` (auxiliary): `ℓ((1)) = 1`. -/
lemma len_one : one.len = 1 := rfl

/-- **Theorem, part (i)**, first claim, of `q_theorem_B_lower.md`: in `Par_{n'}` (with
`h = (q − 1)/2 ≥ 1`), `{(1)}` is a down-set.  If `λ ∈ Par_{n'}` and `λ ≼ (1)`, then
`|λ| = S_t(λ) ≤ S_t((1)) = 1` for `t ≥ ℓ(λ)`, and `|λ| ≡ n'` is odd, so `λ = (1)`. -/
theorem isDownSetPar_one_aux {h : ℕ} (hh : 1 ≤ h) (k : ℕ) :
    IsDownSetPar h (2 * k + 1) {one} := by
  refine ⟨?_, ?_⟩
  · intro lam hlam
    rw [Set.mem_singleton_iff] at hlam
    subst hlam
    refine ⟨?_, ?_, ?_⟩ <;> simp only [size_one, len_one] <;> omega
  · intro lam μ hlam hle hμ
    rw [Set.mem_singleton_iff] at hμ ⊢
    subst hμ
    obtain ⟨_, hpar, _⟩ := hlam
    have h1 := hle (max 1 lam.len) (le_max_left _ _)
    rw [Partition.S_eq_size _ (le_max_right _ _),
      Partition.S_eq_size _ (by rw [len_one]; exact le_max_left _ _), size_one] at h1
    exact eq_one_of_size_eq_one lam (by omega)

variable {T : Type*} [Fintype T] [DecidableEq T] {h : ℕ}

/-- Proof of parts (i) and (iii) of `q_theorem_B_lower.md` (auxiliary): the counts
`#{M_i = u}` of a tuple `M ∈ T^m` add up to `m`. -/
lemma sum_cnt {m : ℕ} (M : Fin m → T) : ∑ u, cnt M u = m := by
  unfold cnt
  rw [← Finset.card_eq_sum_card_fiberwise (fun i _ => Finset.mem_univ (M i))]
  simp

/-- Proof of part (i) of `q_theorem_B_lower.md` (auxiliary): by the definition of `λ(M)` in
`q_P1_fibres.md`, `|λ(M)| = Σ_u (#{M_i = u} − #{M_i = −u})` (truncated differences). -/
lemma size_resPart (S : FibreSetting T h) {m : ℕ} (M : Fin m → T) :
    (S.resPart M).size = ∑ u, (cnt M u - cnt M (S.neg u)) := by
  rw [FibreSetting.resPart, size_ofMultiset]
  rfl

/-- Proof of part (i) of `q_theorem_B_lower.md` (auxiliary): the identity
`|λ(M)| + Σ_u min(a_u, a_{−u}) = m`, i.e. `|λ(M)| = n' − 2ν(M)` for `m = n'`. -/
lemma size_resPart_add_sum_min (S : FibreSetting T h) {m : ℕ} (M : Fin m → T) :
    (S.resPart M).size + ∑ u, min (cnt M u) (cnt M (S.neg u)) = m := by
  rw [size_resPart, ← Finset.sum_add_distrib]
  refine Eq.trans ?_ (sum_cnt M)
  refine Finset.sum_congr rfl fun u _ => ?_
  omega

/-- Proof of part (i) of `q_theorem_B_lower.md` (auxiliary): for `M ∈ T^{n'}`,
`λ(M) = (1)` iff `|λ(M)| = 1`. -/
lemma resPart_eq_one_iff (S : FibreSetting T h) {m : ℕ} (M : Fin m → T) :
    S.resPart M = one ↔ (S.resPart M).size = 1 :=
  ⟨fun h => h ▸ size_one, eq_one_of_size_eq_one _⟩

/-- **Theorem, part (i)**, third claim, of `q_theorem_B_lower.md` (membership form): for
`M ∈ T^{n'}`, `n' = 2k + 1`, `λ(M) = (1)` iff `ν(M) = k`, because `|λ(M)| = n' − 2ν(M)` is odd. -/
lemma resPart_eq_one_iff_nu (S : FibreSetting T h) (k : ℕ) (M : Fin (2 * k + 1) → T) :
    S.resPart M = one ↔ nu S M = k := by
  rw [resPart_eq_one_iff, nu]
  have h1 := size_resPart_add_sum_min S M
  have h2 := (resPart_len_le_and_size_mod S M).2
  constructor
  · intro h; omega
  · intro h
    have : (S.resPart M).size ≤ 1 := by omega
    omega

/-- **Theorem, part (i)**, third claim, of `q_theorem_B_lower.md`: `Z_{(1)} = Γ'`. -/
theorem ZLam_one_eq_aux (S : FibreSetting T h) (k : ℕ) :
    S.ZLam (2 * k + 1) {one} = Gamma' S k := by
  ext M
  simp only [FibreSetting.ZLam, Gamma', Finset.mem_filter, Finset.mem_univ, true_and,
    Set.mem_singleton_iff]
  exact resPart_eq_one_iff_nu S k M

end TheoremB

end

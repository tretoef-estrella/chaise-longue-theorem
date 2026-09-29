module

public import RequestProject.Fibres.Defs

/-!
# Part (0) of the Theorem of `q_every_field.md`: `|Z_Λ|` does not depend on `T`

Formalization of **part (0)** of the Theorem of `q_every_field.md`.  The point sets are the
`Fibres.FibreSetting`s of `q_P1_fibres.md` (a finite set `T` with a fixed-point-free involution
`u ↦ −u` and `|T| = 2h`); `λ(M)` is `resPart` and `Z_Λ` is `ZLam`.
-/

@[expose] public section

namespace EveryField

open ChainLemma Fibres

variable {T : Type*} [Fintype T] {h : ℕ}

/-- **Proof of part (0)** of `q_every_field.md` (auxiliary): the relation "`v = u` or `v = −u`",
whose classes are the orbits `{u, −u}` of the involution. -/
def orbitSetoid (S : FibreSetting T h) : Setoid T where
  r u v := v = u ∨ v = S.neg u
  iseqv := by
    refine ⟨fun u => Or.inl rfl, ?_, ?_⟩
    · rintro u v (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr (S.neg_neg u).symm
    · rintro u v w (rfl | rfl) (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact Or.inr rfl
      · exact Or.inl (S.neg_neg u)

/-- **Proof of part (0)** of `q_every_field.md` (the choice of one element in each orbit
`{u, −u}`): every point set is isomorphic to the standard one `{1, …, h} × {±1}`, i.e. there is a
bijection `e : T → Fin h × Bool` with `e(−u) = (e(u).1, ¬ e(u).2)`. -/
theorem exists_equiv_std (S : FibreSetting T h) :
    ∃ e : T ≃ Fin h × Bool, ∀ u, e (S.neg u) = ((e u).1, !(e u).2) := by
  classical
  let R := Quotient (orbitSetoid S)
  have hmem : ∀ u : T, (Quotient.mk (orbitSetoid S) u).out = u ∨
      (Quotient.mk (orbitSetoid S) u).out = S.neg u := by
    intro u
    rcases Quotient.mk_out (s := orbitSetoid S) u with h | h
    · exact Or.inl h.symm
    · refine Or.inr ?_
      have h' : S.neg u = (Quotient.mk (orbitSetoid S) u).out := by
        conv_lhs => rw [h]
        exact S.neg_neg _
      exact h'.symm
  let f : T → R × Bool := fun u =>
    (Quotient.mk _ u, decide (u = (Quotient.mk (orbitSetoid S) u).out))
  have hneg_mk : ∀ u, Quotient.mk (orbitSetoid S) (S.neg u) = Quotient.mk _ u := fun u =>
    Quotient.sound (Or.inr (S.neg_neg u).symm)
  have hf_neg : ∀ u, f (S.neg u) = ((f u).1, !(f u).2) := by
    intro u
    simp only [f, hneg_mk]
    refine Prod.ext rfl ?_
    rcases hmem u with h1 | h1 <;> rw [h1]
    · simp [S.neg_ne u]
    · simp [(S.neg_ne u).symm]
  have hbij : Function.Bijective f := by
    constructor
    · intro u v huv
      simp only [f, Prod.mk.injEq] at huv
      obtain ⟨h1, h2⟩ := huv
      have hr : v = u ∨ v = S.neg u := by
        rcases Quotient.exact h1 with h | h
        · exact Or.inl h
        · exact Or.inr h
      rcases hr with rfl | rfl
      · rfl
      · exfalso
        rw [hneg_mk] at h2
        rcases hmem u with h3 | h3 <;> rw [h3] at h2
        · simp [S.neg_ne u] at h2
        · simp [(S.neg_ne u).symm] at h2
    · rintro ⟨c, b⟩
      induction c using Quotient.inductionOn with
      | h w =>
      set o := (Quotient.mk (orbitSetoid S) w).out with ho
      have hco : Quotient.mk (orbitSetoid S) o = Quotient.mk _ w := Quotient.out_eq _
      cases b
      · refine ⟨S.neg o, ?_⟩
        simp only [f, hneg_mk, hco, ← ho]
        simp [S.neg_ne o]
      · refine ⟨o, ?_⟩
        simp only [f, hco, ← ho]
        simp
  let e1 : T ≃ R × Bool := Equiv.ofBijective f hbij
  have hcardR : Fintype.card R = h := by
    have := Fintype.card_congr e1
    rw [Fintype.card_prod, Fintype.card_bool, S.card_eq] at this
    omega
  let e2 : R ≃ Fin h := Fintype.equivFinOfCardEq hcardR
  refine ⟨e1.trans (Equiv.prodCongr e2 (Equiv.refl _)), fun u => ?_⟩
  simp only [Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map_apply, id_eq, e1,
    Equiv.ofBijective_apply, hf_neg]
  rfl

/-- **Part (0)** of the Theorem of `q_every_field.md` (first claim): if `T`, `T'` are two point
sets (finite sets with fixed-point-free involutions, `|T| = |T'| = 2h`), there is a bijection
`σ : T → T'` with `σ(−u) = −σ(u)`. -/
theorem exists_equiv_neg {T' : Type*} [Fintype T'] (S : FibreSetting T h)
    (S' : FibreSetting T' h) : ∃ σ : T ≃ T', ∀ u, σ (S.neg u) = S'.neg (σ u) := by
  obtain ⟨e, he⟩ := exists_equiv_std S
  obtain ⟨e', he'⟩ := exists_equiv_std S'
  refine ⟨e.trans e'.symm, fun u => ?_⟩
  apply e'.injective
  simp only [Equiv.trans_apply, Equiv.apply_symm_apply, he, he']

variable [DecidableEq T]

/-- **Part (0)** of the Theorem of `q_every_field.md` (second claim): for a bijection
`σ : T → T'` with `σ(−u) = −σ(u)`, `λ(σ ∘ M) = λ(M)` for every `M ∈ T^m`. -/
theorem resPart_comp {T' : Type*} [Fintype T'] [DecidableEq T'] (S : FibreSetting T h)
    (S' : FibreSetting T' h) (σ : T ≃ T') (hσ : ∀ u, σ (S.neg u) = S'.neg (σ u)) {m : ℕ}
    (M : Fin m → T) : S'.resPart (σ ∘ M) = S.resPart M := by
  have hcnt : ∀ u, cnt (σ ∘ M) (σ u) = cnt M u := by
    intro u
    simp only [cnt, Function.comp_apply, σ.apply_eq_iff_eq]
  unfold FibreSetting.resPart
  congr 1
  have huniv : (Finset.univ : Finset T').val = (Finset.univ : Finset T).val.map σ := by
    conv_lhs => rw [← Finset.univ_map_equiv_to_embedding σ]
    rfl
  rw [huniv, Multiset.map_map]
  refine Multiset.map_congr rfl fun u _ => ?_
  simp only [Function.comp_apply, ← hσ, hcnt]

/-- **Part (0)** of the Theorem of `q_every_field.md` (conclusion): `|Z_Λ(T)| = |Z_Λ(T')|` for
any two point sets `T`, `T'` (with fixed-point-free involutions and `|T| = |T'| = 2h`), every
`m` and every set `Λ` of partitions; `M ↦ σ ∘ M` is a bijection `Z_Λ(T) → Z_Λ(T')`. -/
theorem card_ZLam_eq {T' : Type*} [Fintype T'] [DecidableEq T'] (S : FibreSetting T h)
    (S' : FibreSetting T' h) (m : ℕ) (Λ : Set Partition) :
    (S.ZLam m Λ).card = (S'.ZLam m Λ).card := by
  obtain ⟨σ, hσ⟩ := exists_equiv_neg S S'
  refine Finset.card_nbij' (fun M => σ ∘ M) (fun M => σ.symm ∘ M) ?_ ?_ ?_ ?_
  · intro M hM
    simp only [FibreSetting.ZLam, Finset.coe_filter, Finset.mem_univ, true_and,
      Set.mem_setOf_eq] at hM ⊢
    rwa [resPart_comp S S' σ hσ]
  · intro M hM
    simp only [FibreSetting.ZLam, Finset.coe_filter, Finset.mem_univ, true_and,
      Set.mem_setOf_eq] at hM ⊢
    rwa [← resPart_comp S S' σ hσ, ← Function.comp_assoc, Equiv.self_comp_symm,
      Function.id_comp]
  · intro M _
    simp [← Function.comp_assoc]
  · intro M _
    simp [← Function.comp_assoc]

end EveryField

end

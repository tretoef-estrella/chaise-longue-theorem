module

public import RequestProject.ColPairs.Coord

/-!
# The pair blocks: Setting, Lemma 6.7 (i) and (ii) (`q_col_pairs.md`)

This file formalizes the **Setting** of `q_col_pairs.md` (the elements `x_i`, `z_l` of `B(W_ζ)`)
and parts **(i)** (the ring) and **(ii)** (the pair factor) of **Lemma 6.7**.

Conventions (reused unchanged from the earlier files):
* the data `F`, `p`, `q`, `r`, `μ` are bundled in `S : ColSplit.ColSetting F`;
* a colouring is `c : Fin (2 * k + 1) → S.μ`, extended by `c_0` to `ColSurv.cExt c` on
  `V = Fin (2 * k + 2)`; `A = 𝒞_ζ` is `ColComp.cls (ColSurv.cExt c) ζ` and `B = 𝒞_{ζ^{−1}}` is
  `ColComp.cls (ColSurv.cExt c) ζ⁻¹`; `A^* = A ∖ {0}` is `(cls (cExt c) ζ).erase 0`, and
  `α = |A^*|`, `β = |B^*|` are the cardinalities of these finsets;
* the box ring `B(W_ζ)` is `(ColDecomp.boxS S c).Box (ColDecomp.Wz S c ζ)`, and `t_a` (for
  `a ∈ V`) is `ColDecomp.tB S c (Wz S c ζ) a`;
* `R_{α,β}` is `Bip.R F S.q α β`, with variables `Bip.x F S.q i`, `Bip.z F S.q l`;
* `u^{−1}` for a unit `u` of a ring is `Ring.inverse u`.
-/

@[expose] public section

open MvPolynomial

namespace ColPairs

open ColSplit ColSurv ColComp ColTensor ColDecomp

open scoped Classical

variable {F : Type*} [Field F] (S : ColSetting F) {k : ℕ}

/-- **Setting** of `q_col_pairs.md`: for `i ∈ A^*`, `x_i := ζ^{−1} t_i − 1 ∈ B(W_ζ)`. -/
noncomputable def xW (c : Fin (2 * k + 1) → S.μ) (ζ : F) (i : Fin (2 * k + 2)) :
    (boxS S c).Box (Wz S c ζ) :=
  algebraMap F _ ζ⁻¹ * tB S c (Wz S c ζ) i - 1

/-- **Setting** of `q_col_pairs.md`: for `l ∈ B^*`, `z_l := (ζ t_l)^{−1} − 1 ∈ B(W_ζ)` (the inverse
of the unit `ζ t_l`, written `Ring.inverse`). -/
noncomputable def zW (c : Fin (2 * k + 1) → S.μ) (ζ : F) (l : Fin (2 * k + 2)) :
    (boxS S c).Box (Wz S c ζ) :=
  Ring.inverse (algebraMap F _ ζ * tB S c (Wz S c ζ) l) - 1

variable {S}

/-- **Setting** of `q_col_pairs.md`: `s ∈ W_ζ` iff `s ∈ A ∪ B` (for `s = j + 1 ≠ 0`). -/
theorem mem_Wz {c : Fin (2 * k + 1) → S.μ} {ζ : F} {j : Fin (2 * k + 1)} :
    j ∈ Wz S c ζ ↔ j.succ ∈ cls (cExt c) ζ ∪ cls (cExt c) ζ⁻¹ := by
  simp [Wz, varSet]

/-- **Setting** of `q_col_pairs.md`: `t_{j+1} = t_j` (the variable) for `j ∈ W_ζ`. -/
theorem tB_succ {c : Fin (2 * k + 1) → S.μ} {ζ : F} (j : Wz S c ζ) :
    tB S c (Wz S c ζ) j.1.succ = (boxS S c).t (Wz S c ζ) j := by
  simp [tB, j.2]

/-- **Setting** of `q_col_pairs.md`: the point of the box ring at `j ∈ W_ζ` is `c_{j+1}`. -/
theorem boxS_c (c : Fin (2 * k + 1) → S.μ) (j : Fin (2 * k + 1)) :
    (boxS S c).c j = cExt c j.succ := by
  simp [boxS, cExt]

/-- **Setting** of `q_col_pairs.md`: for `s ∈ W_ζ`, `c_s = ζ` if `s ∈ A^*` and `c_s = ζ^{−1}`
otherwise (i.e. if `s ∈ B^*`). -/
theorem boxS_c_Wz (c : Fin (2 * k + 1) → S.μ) (ζ : F) (j : Wz S c ζ) :
    (boxS S c).c j = if j.1.succ ∈ cls (cExt c) ζ then ζ else ζ⁻¹ := by
  have h := mem_Wz.1 j.2
  rw [boxS_c]
  split_ifs with hA
  · exact mem_cls.1 hA
  · exact mem_cls.1 ((Finset.mem_union.1 h).resolve_left hA)

/-- **Setting** of `q_col_pairs.md`: the generic new coordinates of `ColPairs.yC` are the `x_s`
(`s ∈ A^*`) and `z_s` (`s ∈ B^*`). -/
theorem yC_eq (c : Fin (2 * k + 1) → S.μ) (ζ : F) (j : Wz S c ζ) :
    yC (boxS S c) (Wz S c ζ) (fun j => j.succ ∈ cls (cExt c) ζ) ζ j =
      if j.1.succ ∈ cls (cExt c) ζ then xW S c ζ j.1.succ else zW S c ζ j.1.succ := by
  unfold yC xW zW
  rw [tB_succ]

/-! ### The enumeration of `W_ζ` -/

section Enum

variable {c : Fin (2 * k + 1) → S.μ} {ζ : F}

/-- **Setting** of `q_col_pairs.md`: `W_ζ = A^* ⊔ B^*`; the map `A^* ⊔ B^* → W_ζ`, `s ↦ s`
(a vertex `s = j + 1 ≠ 0` read as the variable index `j`). -/
def sumToW (c : Fin (2 * k + 1) → S.μ) (ζ : F) :
    ((cls (cExt c) ζ).erase 0) ⊕ ((cls (cExt c) ζ⁻¹).erase 0) → Wz S c ζ :=
  Sum.elim
    (fun a => ⟨a.1.pred (Finset.mem_erase.1 a.2).1, mem_Wz.2 (by
      rw [Fin.succ_pred _ (Finset.mem_erase.1 a.2).1]
      exact Finset.mem_union_left _ (Finset.mem_erase.1 a.2).2)⟩)
    (fun b => ⟨b.1.pred (Finset.mem_erase.1 b.2).1, mem_Wz.2 (by
      rw [Fin.succ_pred _ (Finset.mem_erase.1 b.2).1]
      exact Finset.mem_union_right _ (Finset.mem_erase.1 b.2).2)⟩)

/-- **Setting** of `q_col_pairs.md`: `sumToW` sends `s ∈ A^*` to `s`. -/
@[simp] theorem sumToW_inl (a : (cls (cExt c) ζ).erase 0) :
    (sumToW c ζ (Sum.inl a)).1.succ = a.1 := Fin.succ_pred _ (Finset.mem_erase.1 a.2).1

/-- **Setting** of `q_col_pairs.md`: `sumToW` sends `s ∈ B^*` to `s`. -/
@[simp] theorem sumToW_inr (b : (cls (cExt c) ζ⁻¹).erase 0) :
    (sumToW c ζ (Sum.inr b)).1.succ = b.1 := Fin.succ_pred _ (Finset.mem_erase.1 b.2).1

/-- **Setting** of `q_col_pairs.md`: `W_ζ = A^* ⊔ B^*` (`A`, `B` disjoint), i.e. `sumToW` is a
bijection. -/
theorem sumToW_bijective (hd : Disjoint (cls (cExt c) ζ) (cls (cExt c) ζ⁻¹)) :
    Function.Bijective (sumToW c ζ) := by
  constructor
  · have key : ∀ x y, (sumToW c ζ x).1 = (sumToW c ζ y).1 → x = y := by
      rintro (a | a) (b | b) h
      · have h' := congrArg Fin.succ h
        simp only [sumToW_inl] at h'
        exact congrArg Sum.inl (Subtype.ext h')
      · have h' := congrArg Fin.succ h
        simp only [sumToW_inl, sumToW_inr] at h'
        exact (Finset.disjoint_left.1 hd (Finset.mem_erase.1 a.2).2
          (by rw [h']; exact (Finset.mem_erase.1 b.2).2)).elim
      · have h' := congrArg Fin.succ h
        simp only [sumToW_inl, sumToW_inr] at h'
        exact (Finset.disjoint_left.1 hd (Finset.mem_erase.1 b.2).2
          (by rw [← h']; exact (Finset.mem_erase.1 a.2).2)).elim
      · have h' := congrArg Fin.succ h
        simp only [sumToW_inr] at h'
        exact congrArg Sum.inr (Subtype.ext h')
    exact fun x y h => key x y (congrArg Subtype.val h)
  · intro j
    have h := mem_Wz.1 j.2
    by_cases hA : j.1.succ ∈ cls (cExt c) ζ
    · refine ⟨Sum.inl ⟨j.1.succ, Finset.mem_erase.2 ⟨Fin.succ_ne_zero _, hA⟩⟩, ?_⟩
      exact Subtype.ext (Fin.succ_injective _ (by rw [sumToW_inl]))
    · refine ⟨Sum.inr ⟨j.1.succ, Finset.mem_erase.2 ⟨Fin.succ_ne_zero _,
        (Finset.mem_union.1 h).resolve_left hA⟩⟩, ?_⟩
      exact Subtype.ext (Fin.succ_injective _ (by rw [sumToW_inr]))

/-- **Setting** of `q_col_pairs.md` (**Enumerations**): from bijections `e_A : [α] → A^*` and
`e_B : [β] → B^*`, the enumeration `[α + β] → W_ζ` listing first `e_A` and then `e_B`. -/
noncomputable def enumAB (hd : Disjoint (cls (cExt c) ζ) (cls (cExt c) ζ⁻¹)) {n m : ℕ}
    (eA : Fin n ≃ (cls (cExt c) ζ).erase 0) (eB : Fin m ≃ (cls (cExt c) ζ⁻¹).erase 0) :
    Fin (n + m) ≃ Wz S c ζ :=
  finSumFinEquiv.symm.trans ((eA.sumCongr eB).trans (Equiv.ofBijective _ (sumToW_bijective hd)))

/-- **Setting** of `q_col_pairs.md` (**Enumerations**, names exchanged): the enumeration
`[β + α] → W_ζ` listing first `e_B` and then `e_A`. -/
noncomputable def enumBA (hd : Disjoint (cls (cExt c) ζ) (cls (cExt c) ζ⁻¹)) {n m : ℕ}
    (eA : Fin n ≃ (cls (cExt c) ζ).erase 0) (eB : Fin m ≃ (cls (cExt c) ζ⁻¹).erase 0) :
    Fin (m + n) ≃ Wz S c ζ :=
  finSumFinEquiv.symm.trans ((eB.sumCongr eA).trans
    ((Equiv.sumComm _ _).trans (Equiv.ofBijective _ (sumToW_bijective hd))))

end Enum

/-! ### Lemma 6.7 (i) -/

variable {R : Finset F}

/-- **Setting** of `q_col_pairs.md`: `ζ ∈ ℛ` is non-zero (it lies in `μ`). -/
theorem ne_zero_of_reps (hR : IsReps S R) {ζ : F} (hζ : ζ ∈ R) : ζ ≠ 0 :=
  Setting.ne_zero_of_mem_μ S (hR.mem hζ).1

/-- **Setting** of `q_col_pairs.md`: `A = 𝒞_ζ` and `B = 𝒞_{ζ^{−1}}` are disjoint. -/
theorem disjoint_AB (hR : IsReps S R) {ζ : F} (hζ : ζ ∈ R) (c : Fin (2 * k + 1) → S.μ) :
    Disjoint (cls (cExt c) ζ) (cls (cExt c) ζ⁻¹) :=
  (lemma63_i_disjoint hR hζ _).1

/-- **Lemma 6.7 (i)** of `q_col_pairs.md`: the `F`-algebra isomorphism `Φ : R_{α,β} → B(W_ζ)` with
`Φ(x_i) = x_{e_A(i)}` and `Φ(z_l) = z_{e_B(l)}`, for bijections `e_A : [n] → A^*`,
`e_B : [m] → B^*` (so `n = α`, `m = β`). -/
noncomputable def Phi (hR : IsReps S R) {ζ : F} (hζ : ζ ∈ R) (c : Fin (2 * k + 1) → S.μ)
    {n m : ℕ} (eA : Fin n ≃ (cls (cExt c) ζ).erase 0) (eB : Fin m ≃ (cls (cExt c) ζ⁻¹).erase 0) :
    Bip.R F S.q n m ≃ₐ[F] (boxS S c).Box (Wz S c ζ) :=
  coordEquiv (boxS S c) (Wz S c ζ) (fun j => j.succ ∈ cls (cExt c) ζ) ζ (ne_zero_of_reps hR hζ)
    (boxS_c_Wz c ζ) (enumAB (disjoint_AB hR hζ c) eA eB)

/-- **Lemma 6.7 (i)** of `q_col_pairs.md` (names exchanged): the `F`-algebra isomorphism
`Φ' : R_{β,α} → B(W_ζ)` with `Φ'(x_l) = z_{e_B(l)}` and `Φ'(z_i) = x_{e_A(i)}`. -/
noncomputable def Phi' (hR : IsReps S R) {ζ : F} (hζ : ζ ∈ R) (c : Fin (2 * k + 1) → S.μ)
    {n m : ℕ} (eA : Fin n ≃ (cls (cExt c) ζ).erase 0) (eB : Fin m ≃ (cls (cExt c) ζ⁻¹).erase 0) :
    Bip.R F S.q m n ≃ₐ[F] (boxS S c).Box (Wz S c ζ) :=
  coordEquiv (boxS S c) (Wz S c ζ) (fun j => j.succ ∈ cls (cExt c) ζ) ζ (ne_zero_of_reps hR hζ)
    (boxS_c_Wz c ζ) (enumBA (disjoint_AB hR hζ c) eA eB)

section values

variable (hR : IsReps S R) {ζ : F} (hζ : ζ ∈ R) (c : Fin (2 * k + 1) → S.μ) {n m : ℕ}
  (eA : Fin n ≃ (cls (cExt c) ζ).erase 0) (eB : Fin m ≃ (cls (cExt c) ζ⁻¹).erase 0)

include hR hζ

/-- **Lemma 6.7 (i)** of `q_col_pairs.md`: `Φ(x_i) = x_{e_A(i)}`. -/
theorem Phi_x (i : Fin n) : Phi hR hζ c eA eB (Bip.x F S.q i) = xW S c ζ (eA i) := by
  have hmem : ((eA i) : Fin (2 * k + 2)) ∈ cls (cExt c) ζ := (Finset.mem_erase.1 (eA i).2).2
  have h := coordEquiv_X (boxS S c) (Wz S c ζ) (fun j => j.succ ∈ cls (cExt c) ζ) ζ
    (ne_zero_of_reps hR hζ) (boxS_c_Wz c ζ) (enumAB (disjoint_AB hR hζ c) eA eB) (Fin.castAdd m i)
  have hs : (enumAB (disjoint_AB hR hζ c) eA eB (Fin.castAdd m i)).1.succ = eA i := by
    simp [enumAB]
  rw [yC_eq, hs, if_pos hmem] at h
  exact h

/-- **Lemma 6.7 (i)** of `q_col_pairs.md`: `Φ(z_l) = z_{e_B(l)}`. -/
theorem Phi_z (l : Fin m) : Phi hR hζ c eA eB (Bip.z F S.q l) = zW S c ζ (eB l) := by
  have hmem : ((eB l) : Fin (2 * k + 2)) ∉ cls (cExt c) ζ := fun h =>
    Finset.disjoint_left.1 (disjoint_AB hR hζ c) h (Finset.mem_erase.1 (eB l).2).2
  have h := coordEquiv_X (boxS S c) (Wz S c ζ) (fun j => j.succ ∈ cls (cExt c) ζ) ζ
    (ne_zero_of_reps hR hζ) (boxS_c_Wz c ζ) (enumAB (disjoint_AB hR hζ c) eA eB) (Fin.natAdd n l)
  have hs : (enumAB (disjoint_AB hR hζ c) eA eB (Fin.natAdd n l)).1.succ = eB l := by
    simp [enumAB]
  rw [yC_eq, hs, if_neg hmem] at h
  exact h

/-- **Lemma 6.7 (i)** of `q_col_pairs.md` (names exchanged): `Φ'(x_l) = z_{e_B(l)}`. -/
theorem Phi'_x (l : Fin m) : Phi' hR hζ c eA eB (Bip.x F S.q l) = zW S c ζ (eB l) := by
  have hmem : ((eB l) : Fin (2 * k + 2)) ∉ cls (cExt c) ζ := fun h =>
    Finset.disjoint_left.1 (disjoint_AB hR hζ c) h (Finset.mem_erase.1 (eB l).2).2
  have h := coordEquiv_X (boxS S c) (Wz S c ζ) (fun j => j.succ ∈ cls (cExt c) ζ) ζ
    (ne_zero_of_reps hR hζ) (boxS_c_Wz c ζ) (enumBA (disjoint_AB hR hζ c) eA eB) (Fin.castAdd n l)
  have hs : (enumBA (disjoint_AB hR hζ c) eA eB (Fin.castAdd n l)).1.succ = eB l := by
    simp [enumBA]
  rw [yC_eq, hs, if_neg hmem] at h
  exact h

/-- **Lemma 6.7 (i)** of `q_col_pairs.md` (names exchanged): `Φ'(z_i) = x_{e_A(i)}`. -/
theorem Phi'_z (i : Fin n) : Phi' hR hζ c eA eB (Bip.z F S.q i) = xW S c ζ (eA i) := by
  have hmem : ((eA i) : Fin (2 * k + 2)) ∈ cls (cExt c) ζ := (Finset.mem_erase.1 (eA i).2).2
  have h := coordEquiv_X (boxS S c) (Wz S c ζ) (fun j => j.succ ∈ cls (cExt c) ζ) ζ
    (ne_zero_of_reps hR hζ) (boxS_c_Wz c ζ) (enumBA (disjoint_AB hR hζ c) eA eB) (Fin.natAdd m i)
  have hs : (enumBA (disjoint_AB hR hζ c) eA eB (Fin.natAdd m i)).1.succ = eA i := by
    simp [enumBA]
  rw [yC_eq, hs, if_pos hmem] at h
  exact h

end values

/-- **Lemma 6.7 (i)** of `q_col_pairs.md` (the ring): for `c ∈ μ^d`, a set `ℛ` of representatives,
`ζ ∈ ℛ`, `A = 𝒞_ζ`, `B = 𝒞_{ζ^{−1}}`, `α = |A^*|`, `β = |B^*|` and any bijections
`e_A : [α] → A^*`, `e_B : [β] → B^*`, there is an `F`-algebra isomorphism
`Φ : R_{α,β} → B(W_ζ)` with `Φ(x_i) = x_{e_A(i)} = ζ^{−1} t_{e_A(i)} − 1` and
`Φ(z_l) = z_{e_B(l)} = (ζ t_{e_B(l)})^{−1} − 1`, and an `F`-algebra isomorphism
`Φ' : R_{β,α} → B(W_ζ)` with `Φ'(x_l) = z_{e_B(l)}` and `Φ'(z_i) = x_{e_A(i)}`.
(The explicit isomorphisms are `ColPairs.Phi` and `ColPairs.Phi'`, which are defined for
bijections from any `[n]`, `[m]`.) -/
theorem lemma67_i {R : Finset F} (hR : IsReps S R) {ζ : F} (hζ : ζ ∈ R)
    (c : Fin (2 * k + 1) → S.μ)
    (eA : Fin ((cls (cExt c) ζ).erase 0).card ≃ (cls (cExt c) ζ).erase 0)
    (eB : Fin ((cls (cExt c) ζ⁻¹).erase 0).card ≃ (cls (cExt c) ζ⁻¹).erase 0) :
    (∃ Φ : Bip.R F S.q ((cls (cExt c) ζ).erase 0).card ((cls (cExt c) ζ⁻¹).erase 0).card
        ≃ₐ[F] (boxS S c).Box (Wz S c ζ),
      (∀ i, Φ (Bip.x F S.q i) =
        algebraMap F _ ζ⁻¹ * tB S c (Wz S c ζ) (eA i) - 1) ∧
      (∀ l, Φ (Bip.z F S.q l) =
        Ring.inverse (algebraMap F _ ζ * tB S c (Wz S c ζ) (eB l)) - 1)) ∧
    (∃ Φ' : Bip.R F S.q ((cls (cExt c) ζ⁻¹).erase 0).card ((cls (cExt c) ζ).erase 0).card
        ≃ₐ[F] (boxS S c).Box (Wz S c ζ),
      (∀ l, Φ' (Bip.x F S.q l) =
        Ring.inverse (algebraMap F _ ζ * tB S c (Wz S c ζ) (eB l)) - 1) ∧
      (∀ i, Φ' (Bip.z F S.q i) =
        algebraMap F _ ζ⁻¹ * tB S c (Wz S c ζ) (eA i) - 1)) :=
  ⟨⟨Phi hR hζ c eA eB, Phi_x hR hζ c eA eB, Phi_z hR hζ c eA eB⟩,
    ⟨Phi' hR hζ c eA eB, Phi'_x hR hζ c eA eB, Phi'_z hR hζ c eA eB⟩⟩

/-! ### Lemma 6.7 (ii) -/

/-- **Proof** of Lemma 6.7 (ii) of `q_col_pairs.md`: a vertex `s ∈ (A ∪ B) ∖ {0}` is `j + 1` for a
`j ∈ W_ζ`. -/
theorem exists_Wz_of_mem {c : Fin (2 * k + 1) → S.μ} {ζ : F} {s : Fin (2 * k + 2)}
    (hs : s ∈ (cls (cExt c) ζ ∪ cls (cExt c) ζ⁻¹).erase 0) :
    ∃ j : Wz S c ζ, j.1.succ = s := by
  obtain ⟨hs0, hs⟩ := Finset.mem_erase.1 hs
  obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.2 hs0
  exact ⟨⟨j, mem_Wz.2 hs⟩, rfl⟩

/-- **Setting** of `q_col_pairs.md`: `t_l` (and `ζ t_l`) is a unit of `B(W_ζ)` for
`l ∈ (A ∪ B) ∖ {0}`. -/
theorem isUnit_smul_tB (hR : IsReps S R) {ζ : F} (hζ : ζ ∈ R) (c : Fin (2 * k + 1) → S.μ)
    {s : Fin (2 * k + 2)} (hs : s ∈ (cls (cExt c) ζ ∪ cls (cExt c) ζ⁻¹).erase 0) :
    IsUnit (algebraMap F _ ζ * tB S c (Wz S c ζ) s) := by
  obtain ⟨j, rfl⟩ := exists_Wz_of_mem hs
  rw [tB_succ]
  have h0 := ne_zero_of_reps hR hζ
  refine Box.isUnit_smul_t _ _ h0 ?_
  rw [boxS_c_Wz]
  split_ifs
  · exact h0
  · exact inv_ne_zero h0

/-- **Lemma 6.7 (ii)** of `q_col_pairs.md`, second claim: `t_s − 1` is a unit of `B(W_ζ)` for
every `s ∈ W_ζ = (A ∪ B) ∖ {0}` (as `c_s ∈ {ζ, ζ^{−1}}` and `c_s ≠ 1`). -/
theorem isUnit_tB_sub_one (hR : IsReps S R) {ζ : F} (hζ : ζ ∈ R) (c : Fin (2 * k + 1) → S.μ)
    {s : Fin (2 * k + 2)} (hs : s ∈ (cls (cExt c) ζ ∪ cls (cExt c) ζ⁻¹).erase 0) :
    IsUnit (tB S c (Wz S c ζ) s - 1) := by
  obtain ⟨j, rfl⟩ := exists_Wz_of_mem hs
  rw [tB_succ]
  have h1 := (hR.mem hζ).2.1
  have := Box.isUnit_t_sub (boxS S c) (Wz S c ζ) (i := j) (r := 1) (by
    rw [boxS_c_Wz]
    split_ifs
    · exact h1
    · exact fun h => h1 (inv_eq_one.1 h))
  simpa using this

/-- **Lemma 6.7 (ii)** of `q_col_pairs.md` (the pair factor): for `i ∈ A^*` and `l ∈ B^*`,
`t_i t_l − 1 = u·(x_i − z_l)` in `B(W_ζ)` with `u = (1 + z_l)^{−1}` a unit; and `t_s − 1` is a unit
for every `s ∈ W_ζ = (A ∪ B) ∖ {0}`. -/
theorem lemma67_ii {R : Finset F} (hR : IsReps S R) {ζ : F} (hζ : ζ ∈ R)
    (c : Fin (2 * k + 1) → S.μ) :
    (∀ i ∈ (cls (cExt c) ζ).erase 0, ∀ l ∈ (cls (cExt c) ζ⁻¹).erase 0,
      tB S c (Wz S c ζ) i * tB S c (Wz S c ζ) l - 1 =
        Ring.inverse (1 + zW S c ζ l) * (xW S c ζ i - zW S c ζ l) ∧
      IsUnit (Ring.inverse (1 + zW S c ζ l))) ∧
    (∀ s ∈ (cls (cExt c) ζ ∪ cls (cExt c) ζ⁻¹).erase 0, IsUnit (tB S c (Wz S c ζ) s - 1)) := by
  refine ⟨fun i _ l hl => ?_, fun s hs => isUnit_tB_sub_one hR hζ c hs⟩
  have hl' : l ∈ (cls (cExt c) ζ ∪ cls (cExt c) ζ⁻¹).erase 0 := by
    rw [Finset.mem_erase] at hl ⊢
    exact ⟨hl.1, Finset.mem_union_right _ hl.2⟩
  have hu := isUnit_smul_tB hR hζ c hl'
  have h1 : 1 + zW S c ζ l = Ring.inverse (algebraMap F _ ζ * tB S c (Wz S c ζ) l) := by
    rw [zW]; ring
  rw [h1, ringInverse_ringInverse hu]
  refine ⟨?_, hu⟩
  have h2 := Ring.inverse_mul_cancel _ hu
  have h3 : algebraMap F ((boxS S c).Box (Wz S c ζ)) ζ * algebraMap F _ ζ⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ (ne_zero_of_reps hR hζ), map_one]
  rw [zW, xW]
  linear_combination (-(tB S c (Wz S c ζ) i * tB S c (Wz S c ζ) l)) * h3 + h2

end ColPairs

end

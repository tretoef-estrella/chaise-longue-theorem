module

public import RequestProject.ColPairs.Main
public import RequestProject.EvenBlocks.Main

/-!
# Part P, (P1) of `q_even_block_minus.md`: Lemma 6.7 (i), (ii) without `IsReps`

The proofs of `ColPairs.lemma67_i`, `ColPairs.lemma67_ii` use the hypothesis `IsReps S R`, `ζ ∈ R`
only through three facts:
* `ζ ≠ 0` (to define the coordinates `x_s = ζ^{−1} t_s − 1`, `z_s = (ζ t_s)^{−1} − 1`),
* `ζ ≠ 1` (hence also `ζ^{−1} ≠ 1`: `t_s − 1` is a unit on `W_ζ`),
* the classes `𝒞_ζ`, `𝒞_{ζ^{−1}}` are disjoint.

This file re-proves them under exactly these three hypotheses (`hζ0`, `hζ1`, `hd`), and derives the
versions under `EvenBlocks.IsReps2 S R` and `ζ ∈ R` (from which the three facts follow:
`EvenMinus.IsReps2.ne_zero`, `EvenMinus.IsReps2.ne_one`, `EvenMinus.IsReps2.disjoint`). The
conventions are those of `RequestProject/ColPairs/Ring.lean`. The old statements do not apply
directly when `r` is even: then no `R` with `IsReps S R` exists (`−1 ≠ 1` is self-inverse).
-/

@[expose] public section

open MvPolynomial

namespace EvenMinus

open ColSplit ColSurv ColComp ColTensor ColDecomp ColPairs EvenBlocks

open scoped Classical

variable {F : Type*} [Field F] {S : ColSetting F} {k : ℕ}

/-! ### The three facts from `IsReps2` -/

/-- **Part P, (P1)** of `q_even_block_minus.md`: a representative `ζ ∈ R` (`IsReps2 S R`) is
non-zero (it lies in `μ`). -/
theorem IsReps2.ne_zero {R : Finset F} (hR : IsReps2 S R) {ζ : F} (hζ : ζ ∈ R) : ζ ≠ 0 :=
  Setting.ne_zero_of_mem_μ S (hR.mem hζ).1

/-- **Part P, (P1)** of `q_even_block_minus.md`: a representative `ζ ∈ R` (`IsReps2 S R`) is not
`1` (`1` is self-inverse). -/
theorem IsReps2.ne_one {R : Finset F} (hR : IsReps2 S R) {ζ : F} (hζ : ζ ∈ R) : ζ ≠ 1 :=
  fun h => (hR.mem hζ).2.1 (h ▸ one_mem_SInv)

/-- **Part P, (P1)** of `q_even_block_minus.md`: for a representative `ζ ∈ R` (`IsReps2 S R`),
the classes `𝒞_ζ` and `𝒞_{ζ^{−1}}` are disjoint (`ζ ≠ ζ^{−1}`). -/
theorem IsReps2.disjoint {R : Finset F} (hR : IsReps2 S R) {ζ : F} (hζ : ζ ∈ R)
    (c : Fin (2 * k + 1) → S.μ) : Disjoint (cls (cExt c) ζ) (cls (cExt c) ζ⁻¹) :=
  disjoint_cls _ (hR.mem hζ).2.2.2.2.symm

/-! ### Lemma 6.7 (i) under the general hypotheses -/

/-- **Part P, (P1)** of `q_even_block_minus.md` (Lemma 6.7 (i), model `ColPairs.Phi`): the
`F`-algebra isomorphism `Φ : R_{α,β} → B(W_ζ)` with `Φ(x_i) = x_{e_A(i)}`, `Φ(z_l) = z_{e_B(l)}`,
under the hypotheses `ζ ≠ 0` and `𝒞_ζ ∩ 𝒞_{ζ^{−1}} = ∅` only. -/
noncomputable def PhiG {ζ : F} (hζ0 : ζ ≠ 0) (c : Fin (2 * k + 1) → S.μ)
    (hd : Disjoint (cls (cExt c) ζ) (cls (cExt c) ζ⁻¹))
    {n m : ℕ} (eA : Fin n ≃ (cls (cExt c) ζ).erase 0) (eB : Fin m ≃ (cls (cExt c) ζ⁻¹).erase 0) :
    Bip.R F S.q n m ≃ₐ[F] (boxS S c).Box (Wz S c ζ) :=
  coordEquiv (boxS S c) (Wz S c ζ) (fun j => j.succ ∈ cls (cExt c) ζ) ζ hζ0
    (boxS_c_Wz c ζ) (enumAB hd eA eB)

/-- **Part P, (P1)** of `q_even_block_minus.md` (Lemma 6.7 (i), names exchanged, model
`ColPairs.Phi'`): `Φ' : R_{β,α} → B(W_ζ)` with `Φ'(x_l) = z_{e_B(l)}`, `Φ'(z_i) = x_{e_A(i)}`. -/
noncomputable def PhiG' {ζ : F} (hζ0 : ζ ≠ 0) (c : Fin (2 * k + 1) → S.μ)
    (hd : Disjoint (cls (cExt c) ζ) (cls (cExt c) ζ⁻¹))
    {n m : ℕ} (eA : Fin n ≃ (cls (cExt c) ζ).erase 0) (eB : Fin m ≃ (cls (cExt c) ζ⁻¹).erase 0) :
    Bip.R F S.q m n ≃ₐ[F] (boxS S c).Box (Wz S c ζ) :=
  coordEquiv (boxS S c) (Wz S c ζ) (fun j => j.succ ∈ cls (cExt c) ζ) ζ hζ0
    (boxS_c_Wz c ζ) (enumBA hd eA eB)

section values

variable {ζ : F} (hζ0 : ζ ≠ 0) (c : Fin (2 * k + 1) → S.μ)
  (hd : Disjoint (cls (cExt c) ζ) (cls (cExt c) ζ⁻¹)) {n m : ℕ}
  (eA : Fin n ≃ (cls (cExt c) ζ).erase 0) (eB : Fin m ≃ (cls (cExt c) ζ⁻¹).erase 0)

/-- **Part P, (P1)** of `q_even_block_minus.md` (Lemma 6.7 (i)): `Φ(x_i) = x_{e_A(i)}`. -/
theorem PhiG_x (i : Fin n) : PhiG hζ0 c hd eA eB (Bip.x F S.q i) = xW S c ζ (eA i) := by
  have hmem : ((eA i) : Fin (2 * k + 2)) ∈ cls (cExt c) ζ := (Finset.mem_erase.1 (eA i).2).2
  have h := coordEquiv_X (boxS S c) (Wz S c ζ) (fun j => j.succ ∈ cls (cExt c) ζ) ζ
    hζ0 (boxS_c_Wz c ζ) (enumAB hd eA eB) (Fin.castAdd m i)
  have hs : (enumAB hd eA eB (Fin.castAdd m i)).1.succ = eA i := by
    simp [enumAB]
  rw [yC_eq, hs, if_pos hmem] at h
  exact h

/-- **Part P, (P1)** of `q_even_block_minus.md` (Lemma 6.7 (i)): `Φ(z_l) = z_{e_B(l)}`. -/
theorem PhiG_z (l : Fin m) : PhiG hζ0 c hd eA eB (Bip.z F S.q l) = zW S c ζ (eB l) := by
  have hmem : ((eB l) : Fin (2 * k + 2)) ∉ cls (cExt c) ζ := fun h =>
    Finset.disjoint_left.1 hd h (Finset.mem_erase.1 (eB l).2).2
  have h := coordEquiv_X (boxS S c) (Wz S c ζ) (fun j => j.succ ∈ cls (cExt c) ζ) ζ
    hζ0 (boxS_c_Wz c ζ) (enumAB hd eA eB) (Fin.natAdd n l)
  have hs : (enumAB hd eA eB (Fin.natAdd n l)).1.succ = eB l := by
    simp [enumAB]
  rw [yC_eq, hs, if_neg hmem] at h
  exact h

/-- **Part P, (P1)** of `q_even_block_minus.md` (Lemma 6.7 (i), names exchanged):
`Φ'(x_l) = z_{e_B(l)}`. -/
theorem PhiG'_x (l : Fin m) : PhiG' hζ0 c hd eA eB (Bip.x F S.q l) = zW S c ζ (eB l) := by
  have hmem : ((eB l) : Fin (2 * k + 2)) ∉ cls (cExt c) ζ := fun h =>
    Finset.disjoint_left.1 hd h (Finset.mem_erase.1 (eB l).2).2
  have h := coordEquiv_X (boxS S c) (Wz S c ζ) (fun j => j.succ ∈ cls (cExt c) ζ) ζ
    hζ0 (boxS_c_Wz c ζ) (enumBA hd eA eB) (Fin.castAdd n l)
  have hs : (enumBA hd eA eB (Fin.castAdd n l)).1.succ = eB l := by
    simp [enumBA]
  rw [yC_eq, hs, if_neg hmem] at h
  exact h

/-- **Part P, (P1)** of `q_even_block_minus.md` (Lemma 6.7 (i), names exchanged):
`Φ'(z_i) = x_{e_A(i)}`. -/
theorem PhiG'_z (i : Fin n) : PhiG' hζ0 c hd eA eB (Bip.z F S.q i) = xW S c ζ (eA i) := by
  have hmem : ((eA i) : Fin (2 * k + 2)) ∈ cls (cExt c) ζ := (Finset.mem_erase.1 (eA i).2).2
  have h := coordEquiv_X (boxS S c) (Wz S c ζ) (fun j => j.succ ∈ cls (cExt c) ζ) ζ
    hζ0 (boxS_c_Wz c ζ) (enumBA hd eA eB) (Fin.natAdd m i)
  have hs : (enumBA hd eA eB (Fin.natAdd m i)).1.succ = eA i := by
    simp [enumBA]
  rw [yC_eq, hs, if_pos hmem] at h
  exact h

end values

/-- **Part P, (P1)** of `q_even_block_minus.md`: **Lemma 6.7 (i)** (`ColPairs.lemma67_i`) under
the hypotheses `ζ ≠ 0` and `𝒞_ζ ∩ 𝒞_{ζ^{−1}} = ∅` only (the hypothesis `ζ ≠ 1` is not needed for
(i)): there are `F`-algebra isomorphisms `Φ : R_{α,β} → B(W_ζ)` and `Φ' : R_{β,α} → B(W_ζ)` with
the values of Lemma 6.7 (i) on the variables. -/
theorem lemma67_i_gen {ζ : F} (hζ0 : ζ ≠ 0) (c : Fin (2 * k + 1) → S.μ)
    (hd : Disjoint (cls (cExt c) ζ) (cls (cExt c) ζ⁻¹))
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
  ⟨⟨PhiG hζ0 c hd eA eB, PhiG_x hζ0 c hd eA eB, PhiG_z hζ0 c hd eA eB⟩,
    ⟨PhiG' hζ0 c hd eA eB, PhiG'_x hζ0 c hd eA eB, PhiG'_z hζ0 c hd eA eB⟩⟩

/-- **Part P, (P1)** of `q_even_block_minus.md`: **Lemma 6.7 (i)** (`ColPairs.lemma67_i`) under
`IsReps2 S R` and `ζ ∈ R` in place of `IsReps S R`. -/
theorem lemma67_i_reps2 {R : Finset F} (hR : IsReps2 S R) {ζ : F} (hζ : ζ ∈ R)
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
  lemma67_i_gen (IsReps2.ne_zero hR hζ) c (IsReps2.disjoint hR hζ c) eA eB

/-! ### Lemma 6.7 (ii) under the general hypotheses -/

/-- **Part P, (P1)** of `q_even_block_minus.md` (proof of Lemma 6.7 (ii), model
`ColPairs.isUnit_smul_tB`): `ζ t_s` is a unit of `B(W_ζ)` for `s ∈ (A ∪ B) ∖ {0}` (needs only
`ζ ≠ 0`). -/
theorem isUnit_smul_tB_gen {ζ : F} (hζ0 : ζ ≠ 0) (c : Fin (2 * k + 1) → S.μ)
    {s : Fin (2 * k + 2)} (hs : s ∈ (cls (cExt c) ζ ∪ cls (cExt c) ζ⁻¹).erase 0) :
    IsUnit (algebraMap F _ ζ * tB S c (Wz S c ζ) s) := by
  obtain ⟨j, rfl⟩ := exists_Wz_of_mem hs
  rw [ColPairs.tB_succ]
  refine Box.isUnit_smul_t _ _ hζ0 ?_
  rw [boxS_c_Wz]
  split_ifs
  · exact hζ0
  · exact inv_ne_zero hζ0

/-- **Part P, (P1)** of `q_even_block_minus.md` (Lemma 6.7 (ii), second claim, model
`ColPairs.isUnit_tB_sub_one`): `t_s − 1` is a unit of `B(W_ζ)` for `s ∈ (A ∪ B) ∖ {0}` (needs only
`ζ ≠ 1`, hence `ζ^{−1} ≠ 1`). -/
theorem isUnit_tB_sub_one_gen {ζ : F} (hζ1 : ζ ≠ 1) (c : Fin (2 * k + 1) → S.μ)
    {s : Fin (2 * k + 2)} (hs : s ∈ (cls (cExt c) ζ ∪ cls (cExt c) ζ⁻¹).erase 0) :
    IsUnit (tB S c (Wz S c ζ) s - 1) := by
  obtain ⟨j, rfl⟩ := exists_Wz_of_mem hs
  rw [ColPairs.tB_succ]
  have := Box.isUnit_t_sub (boxS S c) (Wz S c ζ) (i := j) (r := 1) (by
    rw [boxS_c_Wz]
    split_ifs
    · exact hζ1
    · exact fun h => hζ1 (inv_eq_one.1 h))
  simpa using this

/-- **Part P, (P1)** of `q_even_block_minus.md`: **Lemma 6.7 (ii)** (`ColPairs.lemma67_ii`) under
the hypotheses `ζ ≠ 0` and `ζ ≠ 1` only (disjointness is not needed for (ii)): for `i ∈ A^*` and
`l ∈ B^*`, `t_i t_l − 1 = (1 + z_l)^{−1}·(x_i − z_l)` with `(1 + z_l)^{−1}` a unit, and `t_s − 1` is
a unit for `s ∈ W_ζ`. -/
theorem lemma67_ii_gen {ζ : F} (hζ0 : ζ ≠ 0) (hζ1 : ζ ≠ 1) (c : Fin (2 * k + 1) → S.μ) :
    (∀ i ∈ (cls (cExt c) ζ).erase 0, ∀ l ∈ (cls (cExt c) ζ⁻¹).erase 0,
      tB S c (Wz S c ζ) i * tB S c (Wz S c ζ) l - 1 =
        Ring.inverse (1 + zW S c ζ l) * (xW S c ζ i - zW S c ζ l) ∧
      IsUnit (Ring.inverse (1 + zW S c ζ l))) ∧
    (∀ s ∈ (cls (cExt c) ζ ∪ cls (cExt c) ζ⁻¹).erase 0, IsUnit (tB S c (Wz S c ζ) s - 1)) := by
  refine ⟨fun i _ l hl => ?_, fun s hs => isUnit_tB_sub_one_gen hζ1 c hs⟩
  have hl' : l ∈ (cls (cExt c) ζ ∪ cls (cExt c) ζ⁻¹).erase 0 := by
    rw [Finset.mem_erase] at hl ⊢
    exact ⟨hl.1, Finset.mem_union_right _ hl.2⟩
  have hu := isUnit_smul_tB_gen hζ0 c hl'
  have h1 : 1 + zW S c ζ l = Ring.inverse (algebraMap F _ ζ * tB S c (Wz S c ζ) l) := by
    rw [zW]; ring
  rw [h1, ringInverse_ringInverse hu]
  refine ⟨?_, hu⟩
  have h2 := Ring.inverse_mul_cancel _ hu
  have h3 : algebraMap F ((boxS S c).Box (Wz S c ζ)) ζ * algebraMap F _ ζ⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hζ0, map_one]
  rw [zW, xW]
  linear_combination (-(tB S c (Wz S c ζ) i * tB S c (Wz S c ζ) l)) * h3 + h2

/-- **Part P, (P1)** of `q_even_block_minus.md`: **Lemma 6.7 (ii)** (`ColPairs.lemma67_ii`) under
`IsReps2 S R` and `ζ ∈ R` in place of `IsReps S R`. -/
theorem lemma67_ii_reps2 {R : Finset F} (hR : IsReps2 S R) {ζ : F} (hζ : ζ ∈ R)
    (c : Fin (2 * k + 1) → S.μ) :
    (∀ i ∈ (cls (cExt c) ζ).erase 0, ∀ l ∈ (cls (cExt c) ζ⁻¹).erase 0,
      tB S c (Wz S c ζ) i * tB S c (Wz S c ζ) l - 1 =
        Ring.inverse (1 + zW S c ζ l) * (xW S c ζ i - zW S c ζ l) ∧
      IsUnit (Ring.inverse (1 + zW S c ζ l))) ∧
    (∀ s ∈ (cls (cExt c) ζ ∪ cls (cExt c) ζ⁻¹).erase 0, IsUnit (tB S c (Wz S c ζ) s - 1)) :=
  lemma67_ii_gen (IsReps2.ne_zero hR hζ) (IsReps2.ne_one hR hζ) c

end EvenMinus

end

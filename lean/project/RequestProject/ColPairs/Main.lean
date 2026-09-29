module

public import RequestProject.ColPairs.Ideal

/-!
# The pair blocks: Lemma 6.7 (iv), (v) and (vi) (`q_col_pairs.md`)

This file formalizes parts **(iv)** (dimensions), **(v)** (binomials) and **(vi)** (the bound) of
**Lemma 6.7** of `q_col_pairs.md`, with the conventions of `RequestProject/ColPairs/Ring.lean`.
Parts (i), (ii) are in `RequestProject/ColPairs/Ring.lean` (`ColPairs.lemma67_i`,
`ColPairs.lemma67_ii`) and part (iii) is in `RequestProject/ColPairs/Ideal.lean`
(`ColPairs.lemma67_iii_bal`, `ColPairs.lemma67_iii_ph`, `ColPairs.lemma67_iii_ph'`,
`ColPairs.lemma67_iii_ne`).

Dimensions are `Module.finrank F`; the ideals `I^{bal}_a`, `I^{ph}_a` of `q_bip_setting.md` are
regarded as `F`-subspaces via `Submodule.restrictScalars F`, as in Theorem C
(`Bip.theoremC`) of `q_bip_induction.md`.
-/

@[expose] public section

namespace ColPairs

open ColSplit ColSurv ColComp ColTensor ColDecomp

open scoped Classical

variable {F : Type*} [Field F] {S : ColSetting F} {k : ℕ}

/-- **Lemma 6.7 (iv)** of `q_col_pairs.md` (dimensions): in the three cases of (iii),
`dim_F I_{c,ζ}` equals `dim_F I^{bal}_a` (if `0 ∉ A ∪ B` and `α = β = a`), `dim_F I^{ph}_β`
(if `0 ∈ B` and `α = β + 1`), `dim_F I^{ph}_α` (if `0 ∈ A` and `β = α + 1`); and if `|A| ≠ |B|`
it is `0`. -/
theorem lemma67_iv {R : Finset F} (hR : IsReps S R) {ζ : F} (hζ : ζ ∈ R)
    (c : Fin (2 * k + 1) → S.μ) :
    (∀ a : ℕ, (0 : Fin (2 * k + 2)) ∉ cls (cExt c) ζ ∪ cls (cExt c) ζ⁻¹ →
      ((cls (cExt c) ζ).erase 0).card = a → ((cls (cExt c) ζ⁻¹).erase 0).card = a →
      Module.finrank F (Icz S c ζ) = Module.finrank F ((Bip.Ibal F S.q a).restrictScalars F)) ∧
    (∀ β : ℕ, (0 : Fin (2 * k + 2)) ∈ cls (cExt c) ζ⁻¹ →
      ((cls (cExt c) ζ).erase 0).card = β + 1 → ((cls (cExt c) ζ⁻¹).erase 0).card = β →
      Module.finrank F (Icz S c ζ) = Module.finrank F ((Bip.Iph F S.q β).restrictScalars F)) ∧
    (∀ α : ℕ, (0 : Fin (2 * k + 2)) ∈ cls (cExt c) ζ →
      ((cls (cExt c) ζ).erase 0).card = α → ((cls (cExt c) ζ⁻¹).erase 0).card = α + 1 →
      Module.finrank F (Icz S c ζ) = Module.finrank F ((Bip.Iph F S.q α).restrictScalars F)) ∧
    ((cls (cExt c) ζ).card ≠ (cls (cExt c) ζ⁻¹).card → Module.finrank F (Icz S c ζ) = 0) := by
  refine ⟨fun a h0 hα hβ => ?_, fun β h0 hα hβ => ?_, fun α h0 hα hβ => ?_, fun h => ?_⟩
  · set eA := (Finset.equivFinOfCardEq hα).symm
    set eB := (Finset.equivFinOfCardEq hβ).symm
    rw [← lemma67_iii_bal hR hζ c h0 eA eB (Phi hR hζ c eA eB) (Phi_x hR hζ c eA eB)
      (Phi_z hR hζ c eA eB), finrank_map_algEquiv]
  · set eA := (Finset.equivFinOfCardEq hα).symm
    set eB := (Finset.equivFinOfCardEq hβ).symm
    rw [← lemma67_iii_ph hR hζ c h0 eA eB (Phi hR hζ c eA eB) (Phi_x hR hζ c eA eB)
      (Phi_z hR hζ c eA eB), finrank_map_algEquiv]
  · set eA := (Finset.equivFinOfCardEq hα).symm
    set eB := (Finset.equivFinOfCardEq hβ).symm
    rw [← lemma67_iii_ph' hR hζ c h0 eA eB (Phi' hR hζ c eA eB) (Phi'_x hR hζ c eA eB)
      (Phi'_z hR hζ c eA eB), finrank_map_algEquiv]
  · rw [lemma67_iii_ne c h]
    exact Module.finrank_zero_of_subsingleton

/-- **Proof** of Lemma 6.7 (v) of `q_col_pairs.md`: in characteristic `p` with `q = p^v`,
`binom(q − 1, t) = (−1)^t` in `F` for `0 ≤ t ≤ q − 1` (here via Pascal's rule and
`p ∣ binom(q, t+1)` for `0 < t + 1 < q`, instead of the Frobenius identity of the source). -/
theorem choose_q_sub_one_eq (S : ColSetting F) :
    ∀ t, t ≤ S.q - 1 → (((S.q - 1).choose t : ℕ) : F) = (-1) ^ t := by
  haveI := S.charP
  have hq1 : 1 ≤ S.q := Setting.one_le_q S
  intro t
  induction t with
  | zero => intro _; simp
  | succ t ih =>
    intro ht
    have h1 := ih (by omega)
    have hdvd : S.p ∣ S.q.choose (t + 1) :=
      S.hp.dvd_choose_pow (Nat.succ_ne_zero t) (by rw [← ColSetting.q]; omega)
    have h2 : ((S.q.choose (t + 1) : ℕ) : F) = 0 := (CharP.cast_eq_zero_iff F S.p _).2 hdvd
    have e : S.q = (S.q - 1) + 1 := by omega
    rw [e, Nat.choose_succ_succ', Nat.cast_add, h1] at h2
    rw [pow_succ]
    linear_combination h2

/-- **Lemma 6.7 (v)** of `q_col_pairs.md` (binomials): if `F` has characteristic `p` and `q = p^v`,
then `binom(q − 1, t) ≠ 0` in `F` for every `0 ≤ t ≤ q − 1`. -/
theorem lemma67_v (S : ColSetting F) :
    ∀ t, t ≤ S.q - 1 → (((S.q - 1).choose t : ℕ) : F) ≠ 0 := by
  intro t ht
  rw [choose_q_sub_one_eq S t ht]
  exact pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)

/-- **Lemma 6.7 (vi)** of `q_col_pairs.md` (the bound): suppose moreover `p ≠ 2` and `|A| = |B|`.
Then `dim_F I_{c,ζ} ≥ N_ζ(c)`, where `N_ζ(c) = N_{bal}(α, q)` if `0 ∉ A ∪ B` and
`N_ζ(c) = N_{ph}(min(α, β), q)` otherwise. The proof combines (iv), (v) and Theorem C of
`q_bip_induction.md` (`Bip.theoremC`). -/
theorem lemma67_vi {R : Finset F} (hR : IsReps S R) {ζ : F} (hζ : ζ ∈ R)
    (c : Fin (2 * k + 1) → S.μ) (hp : S.p ≠ 2)
    (hAB : (cls (cExt c) ζ).card = (cls (cExt c) ζ⁻¹).card) :
    ((0 : Fin (2 * k + 2)) ∉ cls (cExt c) ζ ∪ cls (cExt c) ζ⁻¹ →
      Bip.Nbal ((cls (cExt c) ζ).erase 0).card S.q ≤ Module.finrank F (Icz S c ζ)) ∧
    ((0 : Fin (2 * k + 2)) ∈ cls (cExt c) ζ ∪ cls (cExt c) ζ⁻¹ →
      Bip.Nph (min ((cls (cExt c) ζ).erase 0).card ((cls (cExt c) ζ⁻¹).erase 0).card) S.q ≤
        Module.finrank F (Icz S c ζ)) := by
  have hodd_p : Odd S.p := S.hp.eq_two_or_odd'.resolve_left hp
  have hodd : Odd S.q := hodd_p.pow
  have hq3 : 3 ≤ S.q := by
    have h2 := S.hp.two_le
    have hp3 : 3 ≤ S.p := by omega
    exact hp3.trans (Nat.le_self_pow (by have := S.one_le_v; omega) S.p)
  have hC := Bip.theoremC F hq3 hodd (lemma67_v S)
  obtain ⟨ivb, ivp, ivp', -⟩ := lemma67_iv hR hζ c
  have hd := disjoint_AB hR hζ c
  refine ⟨fun h0 => ?_, fun h0 => ?_⟩
  · have h0A : (0 : Fin (2 * k + 2)) ∉ cls (cExt c) ζ := fun h => h0 (Finset.mem_union_left _ h)
    have h0B : (0 : Fin (2 * k + 2)) ∉ cls (cExt c) ζ⁻¹ :=
      fun h => h0 (Finset.mem_union_right _ h)
    rw [ivb _ h0 rfl (by rw [Finset.erase_eq_of_notMem h0A, Finset.erase_eq_of_notMem h0B, hAB])]
    exact (hC _).1
  · rcases Finset.mem_union.1 h0 with h0A | h0B
    · have h0B : (0 : Fin (2 * k + 2)) ∉ cls (cExt c) ζ⁻¹ :=
        fun h => Finset.disjoint_left.1 hd h0A h
      have hA := Finset.card_erase_of_mem h0A
      have hApos : 0 < (cls (cExt c) ζ).card := Finset.card_pos.2 ⟨0, h0A⟩
      have hB : ((cls (cExt c) ζ⁻¹).erase 0).card = ((cls (cExt c) ζ).erase 0).card + 1 := by
        rw [Finset.erase_eq_of_notMem h0B, hA, ← hAB]; omega
      rw [hB, min_eq_left (Nat.le_succ _), ivp' _ h0A rfl hB]
      exact (hC _).2.1
    · have h0A : (0 : Fin (2 * k + 2)) ∉ cls (cExt c) ζ :=
        fun h => Finset.disjoint_left.1 hd h h0B
      have hB := Finset.card_erase_of_mem h0B
      have hBpos : 0 < (cls (cExt c) ζ⁻¹).card := Finset.card_pos.2 ⟨0, h0B⟩
      have hA : ((cls (cExt c) ζ).erase 0).card = ((cls (cExt c) ζ⁻¹).erase 0).card + 1 := by
        rw [Finset.erase_eq_of_notMem h0A, hB, hAB]; omega
      rw [hA, min_eq_right (Nat.le_succ _), ivp _ h0B hA rfl]
      exact (hC _).2.1

end ColPairs

end

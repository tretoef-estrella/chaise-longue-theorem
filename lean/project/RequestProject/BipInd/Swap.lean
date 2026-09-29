module

public import RequestProject.Bip.Main
public import RequestProject.Tight.Main

/-!
# Lemma S of `q_bip_induction.md` (the symmetry)

Formalization of the **Setting, "The swap"** paragraph and of **Lemma S** (i), (ii), (iii) of
`q_bip_induction.md`, reusing unchanged the bipartite setting of `q_bip_setting.md`
(`RequestProject/Bip/`).

* `λ^⊤ = (λ_−, λ_+)` is `Prod.swap λ`, and `Λ^⊤ = {λ^⊤ : λ ∈ Λ}` is `swapSet Λ`.
* The renaming isomorphism `σ : R_{α,β} → R_{β,α}` is `swapR F q α β`; on the variable indices
  `Fin (α + β) ≃ Fin (β + α)` it is `finAddFlip`, which sends `x_i` (index `Fin.castAdd β i`) to
  `z_i` (index `Fin.natAdd β i`) and `z_l` (index `Fin.natAdd α l`) to `x_l`
  (index `Fin.castAdd α l`).
-/

@[expose] public section

open MvPolynomial

namespace Bip

open ChainLemma Tight

set_option synthInstance.maxHeartbeats 200000

/-! ### The swap of pairs of partitions -/

/-- **Setting, "The swap"** of `q_bip_induction.md`: for a set `Λ` of pairs of partitions,
`Λ^⊤ := {λ^⊤ : λ ∈ Λ}`, where `λ^⊤ = (λ_−, λ_+)` is `Prod.swap λ`. -/
def swapSet (Λ : Set (Partition × Partition)) : Set (Partition × Partition) := Prod.swap '' Λ

/-- Membership in `Λ^⊤` (**Setting, "The swap"** of `q_bip_induction.md`): `λ ∈ Λ^⊤` iff
`λ^⊤ ∈ Λ`. -/
theorem mem_swapSet {Λ : Set (Partition × Partition)} {lam : Partition × Partition} :
    lam ∈ swapSet Λ ↔ lam.swap ∈ Λ := by
  simp [swapSet, Set.image_swap_eq_preimage_swap]

/-- `(Λ^⊤)^⊤ = Λ` (**Setting, "The swap"** of `q_bip_induction.md`). -/
theorem swapSet_swapSet (Λ : Set (Partition × Partition)) : swapSet (swapSet Λ) = Λ := by
  ext lam; simp [mem_swapSet]

/-- **Lemma S (i)** of `q_bip_induction.md`, first statement (one direction):
`λ ∈ BPar_q(α, β)` implies `λ^⊤ ∈ BPar_q(β, α)`. -/
theorem swap_mem_BPar {q α β : ℕ} {lam : Partition × Partition} (h : lam ∈ BPar q α β) :
    lam.swap ∈ BPar q β α := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩ <;> simp only [Prod.fst_swap, Prod.snd_swap] <;> omega

/-- **Lemma S (i)** of `q_bip_induction.md`, third statement (one direction): if `Λ` is a
down-set of `BPar_q(α, β)`, then `Λ^⊤` is a down-set of `BPar_q(β, α)`. -/
theorem isDownSetB_swapSet {q α β : ℕ} {Λ : Set (Partition × Partition)}
    (h : IsDownSetB q α β Λ) : IsDownSetB q β α (swapSet Λ) := by
  refine ⟨fun lam hl => ?_, fun lam μ hlam hle hμ => ?_⟩
  · have := swap_mem_BPar (h.1 (mem_swapSet.1 hl))
    simpa using this
  · rw [mem_swapSet] at hμ ⊢
    exact h.2 _ μ.swap (swap_mem_BPar hlam) ⟨hle.2, hle.1⟩ hμ

/-- **Lemma S (i)** of `q_bip_induction.md`: `λ ∈ BPar_q(α, β)` iff `λ^⊤ ∈ BPar_q(β, α)`;
`λ ≼ μ` iff `λ^⊤ ≼ μ^⊤`; and `Λ` is a down-set of `BPar_q(α, β)` iff `Λ^⊤` is a down-set of
`BPar_q(β, α)`. -/
theorem lemmaS_i (q α β : ℕ) :
    (∀ lam : Partition × Partition, lam ∈ BPar q α β ↔ lam.swap ∈ BPar q β α) ∧
      (∀ lam μ : Partition × Partition, BWeakDom lam μ ↔ BWeakDom lam.swap μ.swap) ∧
      ∀ Λ : Set (Partition × Partition), IsDownSetB q α β Λ ↔ IsDownSetB q β α (swapSet Λ) := by
  refine ⟨fun lam => ⟨swap_mem_BPar, fun h => by simpa using swap_mem_BPar h⟩,
    fun lam μ => ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩,
    fun Λ => ⟨isDownSetB_swapSet, fun h => ?_⟩⟩
  simpa [swapSet_swapSet] using isDownSetB_swapSet h

/-! ### Shapes and `Z_Λ` under the swap -/

section Points

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- **Lemma S (ii)** of `q_bip_induction.md`, first statement: `λ(η, ξ) = λ(ξ, η)^⊤`. -/
theorem shape_swap {α β : ℕ} (ξ : Fin α → Ω) (η : Fin β → Ω) :
    shape η ξ = (shape ξ η).swap := rfl

/-- **Lemma S (ii)** of `q_bip_induction.md`: `λ(η, ξ) = λ(ξ, η)^⊤` for every point `(ξ, η)`;
the map `(ξ, η) ↦ (η, ξ)` sends `Z_Λ` onto `Z_{Λ^⊤}` (so it is a bijection
`Z_Λ → Z_{Λ^⊤}`, being injective); and `|Z_{Λ^⊤}| = |Z_Λ|` (the second set in `Ω^β × Ω^α`). -/
theorem lemmaS_ii (Ω : Type*) [Fintype Ω] [DecidableEq Ω] (α β : ℕ)
    (Λ : Set (Partition × Partition)) :
    (∀ (ξ : Fin α → Ω) (η : Fin β → Ω), shape η ξ = (shape ξ η).swap) ∧
      (ZLam Ω α β Λ).map (Equiv.prodComm _ _).toEmbedding = ZLam Ω β α (swapSet Λ) ∧
      (ZLam Ω β α (swapSet Λ)).card = (ZLam Ω α β Λ).card := by
  have hmap : (ZLam Ω α β Λ).map (Equiv.prodComm _ _).toEmbedding = ZLam Ω β α (swapSet Λ) := by
    ext p
    simp only [Finset.mem_map_equiv, ZLam, Finset.mem_filter, Finset.mem_univ, true_and,
      mem_swapSet]
    rfl
  refine ⟨fun ξ η => rfl, hmap, ?_⟩
  rw [← hmap, Finset.card_map]

end Points

/-! ### The renaming isomorphism -/

section Ring

variable (F : Type*) [Field F] (q : ℕ)

/-- The renaming of the variable indices `finAddFlip : Fin (m + n) ≃ Fin (n + m)` is an involution
(proof of **Lemma S (iii)** of `q_bip_induction.md`: `σ` is bijective). -/
theorem finAddFlip_finAddFlip {m n : ℕ} (i : Fin (m + n)) : finAddFlip (finAddFlip i) = i := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

/-- The renaming of the variables maps the box relations `x_i^q`, `z_l^q` of `R_{α,β}` onto those
of `R_{β,α}` (proof of **Lemma S (iii)** of `q_bip_induction.md`: `σ` is well defined). -/
theorem map_powIdeal_finAddFlip (α β : ℕ) :
    Peel.powIdeal F (q + 1) (β + α) =
      (Peel.powIdeal F (q + 1) (α + β)).map
        ((renameEquiv F (finAddFlip : Fin (α + β) ≃ Fin (β + α))) :
          MvPolynomial (Fin (α + β)) F →+* MvPolynomial (Fin (β + α)) F) := by
  unfold Peel.powIdeal
  rw [Ideal.map_span, ← Set.range_comp]
  congr 1
  ext g
  simp only [Set.mem_range, Function.comp_apply, RingHom.coe_coe, renameEquiv_apply, map_pow,
    rename_X]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨finAddFlip i, by rw [finAddFlip_finAddFlip]⟩
  · rintro ⟨i, rfl⟩
    exact ⟨_, rfl⟩

/-- **Lemma S (iii)** of `q_bip_induction.md`: the `F`-algebra isomorphism
`σ : R_{α,β} → R_{β,α}` renaming the variables, `σ(x_i) = z_i` (`i ∈ [α]`) and `σ(z_l) = x_l`
(`l ∈ [β]`) (see `swapR_x`, `swapR_z`).  It is induced by the renaming `finAddFlip` of the
polynomial variables, which maps the box relations onto the box relations. -/
noncomputable def swapR (α β : ℕ) : R F q α β ≃ₐ[F] R F q β α :=
  Ideal.quotientEquivAlg _ _ (renameEquiv F finAddFlip) (map_powIdeal_finAddFlip F q α β)

/-- **Lemma S (iii)** of `q_bip_induction.md`: `σ` on the class of a polynomial is the class of
its renamed polynomial. -/
theorem swapR_mk {α β : ℕ} (g : MvPolynomial (Fin (α + β)) F) :
    swapR F q α β (Ideal.Quotient.mk _ g) = Ideal.Quotient.mk _ (rename finAddFlip g) := rfl

/-- **Lemma S (iii)** of `q_bip_induction.md`: `σ(x_i) = z_i`. -/
theorem swapR_x {α β : ℕ} (i : Fin α) : swapR F q α β (x F q i) = z F q i := by
  simp only [x, z, swapR_mk, rename_X, finAddFlip_apply_castAdd]

/-- **Lemma S (iii)** of `q_bip_induction.md`: `σ(z_l) = x_l`. -/
theorem swapR_z {α β : ℕ} (l : Fin β) : swapR F q α β (z F q l) = x F q l := by
  simp only [x, z, swapR_mk, rename_X, finAddFlip_apply_natAdd]

/-- **Lemma S (iii)** of `q_bip_induction.md`: the renaming `R_{β,α} → R_{α,β}` is inverse to
`σ : R_{α,β} → R_{β,α}`. -/
theorem swapR_swapR {α β : ℕ} (g : R F q α β) : swapR F q β α (swapR F q α β g) = g := by
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective g
  rw [swapR_mk, swapR_mk, rename_rename]
  have : (finAddFlip ∘ finAddFlip : Fin (α + β) → Fin (α + β)) = id :=
    funext finAddFlip_finAddFlip
  rw [this, rename_id_apply]

end Ring

/-! ### Transposed tight patterns -/

/-- A ring map commutes with the Vandermonde products, `f(Δ(x_B)) = Δ((f ∘ x)_B)` (proof of
**Lemma S (iii)** of `q_bip_induction.md`: `σ(Δ(x_B)) = Δ(z_B)`, `σ(Δ(z_B)) = Δ(x_B)`). -/
theorem vand_map {ι R S : Type*} [LinearOrder ι] [CommRing R] [CommRing S] (f : R →+* S)
    (x : ι → R) (B : Finset ι) : f (vand x B) = vand (f ∘ x) B := by
  simp [vand, map_prod, map_sub]

/-- In a tight pattern of `λ` on `([α], [β])`, `|P| = β − |λ_−|` (the `z`-blocks partition
`[β] ∖ {l : (i, l) ∈ P}` and have sizes `(λ_−)'_c` summing to `|λ_−|`).  Used for the transposed
pattern in the proof of **Lemma S (iii)** of `q_bip_induction.md`. -/
theorem BTightPattern.card_pairs_snd {lam : Partition × Partition} {α β : ℕ}
    (T : BTightPattern lam α β) : T.pairs.card = β - lam.2.size := by
  classical
  have h1 : ((Finset.Icc 1 (lam.2.row 1)).sup T.blocksZ).card = lam.2.size := by
    rw [Finset.sup_eq_biUnion, Finset.card_biUnion T.blocksZ_disjoint, ← sum_colLen]
    exact Finset.sum_congr rfl T.card_blockZ
  have himg : (T.pairs.image Prod.snd).card = T.pairs.card :=
    Finset.card_image_of_injOn T.inj_snd
  have h2 : (Finset.univ \ T.pairs.image Prod.snd).card = β - T.pairs.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), himg, Finset.card_univ,
      Fintype.card_fin]
  have h3 : T.pairs.card ≤ β := by
    rw [← himg]
    simpa using Finset.card_le_univ (T.pairs.image Prod.snd)
  rw [T.coverZ] at h1
  omega

/-- **Lemma S (iii)** of `q_bip_induction.md`: the transposed pattern
`T^⊤ = ({(l, i) : (i, l) ∈ P}, (B^−_c), (B^+_c))` of a tight pattern `T = (P, (B^+_c), (B^−_c))`
of `λ` on `([α], [β])`, a tight pattern of `λ^⊤` on `([β], [α])`. -/
def BTightPattern.transpose {lam : Partition × Partition} {α β : ℕ}
    (T : BTightPattern lam α β) : BTightPattern lam.swap β α where
  pairs := T.pairs.map (Equiv.prodComm _ _).toEmbedding
  card_pairs := by rw [Finset.card_map]; exact T.card_pairs_snd
  inj_fst := by
    intro a ha b hb h
    simp only [Finset.coe_map, Equiv.coe_toEmbedding, Set.mem_image, Finset.mem_coe,
      Equiv.prodComm_apply] at ha hb
    obtain ⟨a, ha, rfl⟩ := ha
    obtain ⟨b, hb, rfl⟩ := hb
    have := T.inj_snd ha hb h
    rw [this]
  inj_snd := by
    intro a ha b hb h
    simp only [Finset.coe_map, Equiv.coe_toEmbedding, Set.mem_image, Finset.mem_coe,
      Equiv.prodComm_apply] at ha hb
    obtain ⟨a, ha, rfl⟩ := ha
    obtain ⟨b, hb, rfl⟩ := hb
    have := T.inj_fst ha hb h
    rw [this]
  blocksX := T.blocksZ
  card_blockX := T.card_blockZ
  blocksX_disjoint := T.blocksZ_disjoint
  coverX := T.coverZ.trans (by rw [Finset.map_eq_image, Finset.image_image]; rfl)
  blocksZ := T.blocksX
  card_blockZ := T.card_blockX
  blocksZ_disjoint := T.blocksX_disjoint
  coverZ := T.coverX.trans (by rw [Finset.map_eq_image, Finset.image_image]; rfl)

variable (F : Type*) [Field F] (q : ℕ)

/-- **Lemma S (iii)** of `q_bip_induction.md`: the products correspond, `σ(prod T) = prod T^⊤`,
using `σ((x_i − z_l)^{q−1}) = (z_i − x_l)^{q−1} = (x_l − z_i)^{q−1}` (as `q − 1` is even),
`σ(Δ(x_B)) = Δ(z_B)` and `σ(Δ(z_B)) = Δ(x_B)`. -/
theorem swapR_prod (hq : Even (q - 1)) {lam : Partition × Partition} {α β : ℕ}
    (T : BTightPattern lam α β) : swapR F q α β (T.prod F q) = T.transpose.prod F q := by
  have hx : (swapR F q α β : R F q α β →+* R F q β α) ∘ x F q = z F q :=
    funext fun i => swapR_x F q i
  have hz : (swapR F q α β : R F q α β →+* R F q β α) ∘ z F q = x F q :=
    funext fun i => swapR_z F q i
  have h1 : ∀ c, swapR F q α β (vand (x F q) (T.blocksX c)) = vand (z F q) (T.blocksX c) :=
    fun c => by rw [← hx]; exact vand_map (swapR F q α β : R F q α β →+* R F q β α) _ _
  have h2 : ∀ c, swapR F q α β (vand (z F q) (T.blocksZ c)) = vand (x F q) (T.blocksZ c) :=
    fun c => by rw [← hz]; exact vand_map (swapR F q α β : R F q α β →+* R F q β α) _ _
  have h3 : ∀ p : Fin α × Fin β, (z F q p.1 - x F q p.2) ^ (q - 1) =
      (x F q p.2 - z F q p.1) ^ (q - 1) := fun p => by
    rw [← neg_sub, hq.neg_pow]
  unfold BTightPattern.prod
  simp only [map_mul, map_prod, map_pow, map_sub, swapR_x, swapR_z, h1, h2]
  simp only [BTightPattern.transpose, Finset.prod_map, Equiv.coe_toEmbedding,
    Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, h3]
  ring

/-- `σ(V_Λ) ⊆ V_{Λ^⊤}` (one inclusion of **Lemma S (iii)** of `q_bip_induction.md`). -/
theorem map_VLamB_le (hq : Even (q - 1)) (α β : ℕ) (Λ : Set (Partition × Partition)) :
    (VLamB F q α β Λ).map (swapR F q α β) ≤ VLamB F q β α (swapSet Λ) := by
  unfold VLamB
  rw [Ideal.map_span]
  refine Ideal.span_mono ?_
  rintro _ ⟨_, ⟨lam, hlam, T, rfl⟩, rfl⟩
  exact ⟨lam.swap, mem_swapSet.2 (by simpa using hlam), T.transpose, (swapR_prod F q hq T).symm⟩

/-- **Lemma S (iii)** of `q_bip_induction.md`: for odd `q` (so that `q − 1` is even), the renaming
isomorphism `σ : R_{α,β} → R_{β,α}` (`σ(x_i) = z_i`, `σ(z_l) = x_l`) satisfies
`σ(V_Λ) = V_{Λ^⊤}`, and so `dim V_{Λ^⊤} = dim V_Λ` (dimensions of the ideals as `F`-subspaces). -/
theorem lemmaS_iii (hq : Odd q) (α β : ℕ) (Λ : Set (Partition × Partition)) :
    (VLamB F q α β Λ).map (swapR F q α β) = VLamB F q β α (swapSet Λ) ∧
      Module.finrank F ((VLamB F q β α (swapSet Λ)).restrictScalars F) =
        Module.finrank F ((VLamB F q α β Λ).restrictScalars F) := by
  have he : Even (q - 1) := by
    obtain ⟨k, rfl⟩ := hq
    exact ⟨k, by omega⟩
  have heq : (VLamB F q α β Λ).map (swapR F q α β) = VLamB F q β α (swapSet Λ) := by
    refine le_antisymm (map_VLamB_le F q he α β Λ) ?_
    have h1 := map_VLamB_le F q he β α (swapSet Λ)
    rw [swapSet_swapSet] at h1
    intro g hg
    rw [← swapR_swapR F q g]
    exact Ideal.mem_map_of_mem _ (h1 (Ideal.mem_map_of_mem _ hg))
  refine ⟨heq, ?_⟩
  have hsub : (VLamB F q β α (swapSet Λ)).restrictScalars F =
      ((VLamB F q α β Λ).restrictScalars F).map (swapR F q α β).toLinearMap := by
    rw [← heq]
    ext g
    simp only [Submodule.restrictScalars_mem, Submodule.mem_map, AlgEquiv.toLinearMap_apply]
    exact Ideal.mem_map_iff_of_surjective _ (swapR F q α β).surjective
  rw [hsub]
  exact (swapR F q α β).toLinearEquiv.finrank_map_eq _

end Bip

end

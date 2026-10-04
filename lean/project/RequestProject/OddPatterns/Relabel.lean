module

public import RequestProject.OddPatterns.Defs

/-!
# Lemma C of `q_oddbox_patterns.md`: stability under relabelling

A permutation `σ` of `Fin m` acts on `C_m` by `y_i ↦ y_{σ(i)}` (`Tight.relabel F (2h+2) σ`).
(C1) for the marked block, (C2) for marked patterns, (C3) for the ideals `V_Λ(I)`.
-/

@[expose] public section

namespace OddPatterns

open ChainLemma OddShapes

set_option synthInstance.maxHeartbeats 200000

variable {F : Type*} [Field F] {h : ℕ}

/-- Auxiliary for (C1) of `q_oddbox_patterns.md`: the sign of a permutation is `±1`. -/
theorem PM_sign_mul {R : Type*} [CommRing R] {n : ℕ} (τ : Equiv.Perm (Fin n)) (x : R) :
    Tight.PM (((Equiv.Perm.sign τ : ℤ) : R) * x) x := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h1 | h1
  · left; simp [h1]
  · right; simp [h1]

/-- **Lemma C, (C1)** of `q_oddbox_patterns.md`: for `B ⊆ Fin m` and `ℓ ≥ 0`,
`σ(Pf_{E_ℓ}(B)) = ± Pf_{E_ℓ}(σ(B))`. -/
theorem C1 {m : ℕ} (σ : Equiv.Perm (Fin m)) (l : ℕ) (B : Finset (Fin m)) :
    Tight.PM (Tight.relabel F (2 * h + 2) σ (markedPf F h l B))
      (markedPf F h l (B.map σ.toEmbedding)) := by
  set B' := B.map σ.toEmbedding with hB'
  have hc : B'.card = B.card := Finset.card_map _
  set ι := B.orderEmbOfFin rfl
  set ι' := B'.orderEmbOfFin rfl
  -- step 1: the relabelled marked block is `mPf_ℓ(y ∘ σ ∘ ι_B)`
  have h1 : Tight.relabel F (2 * h + 2) σ (markedPf F h l B) =
      mPf h l (fun i => Tight.y F (2 * h + 2) (σ (ι i))) := by
    unfold markedPf
    have := map_mPf ((Tight.relabel F (2 * h + 2) σ).toRingHom) h l
      (fun i => Tight.y F (2 * h + 2) (ι i))
    simpa [Tight.relabel_y] using this
  -- step 2: `σ ∘ ι_B = ι_{σ(B)} ∘ τ`
  have hmem : ∀ i, σ (ι i) ∈ B' := fun i =>
    Finset.mem_map_of_mem _ (Finset.orderEmbOfFin_mem B rfl i)
  let g : Fin B.card → Fin B.card := fun i =>
    Fin.cast hc ((B'.orderIsoOfFin rfl).symm ⟨σ (ι i), hmem i⟩)
  have hg : ∀ i, ι' (Fin.cast hc.symm (g i)) = σ (ι i) := by
    intro i
    simp only [g, Fin.cast_cast, Fin.cast_eq_self, ι']
    rw [← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]
  have ginj : Function.Injective g := by
    intro i j hij
    have := hg i
    rw [hij, hg j] at this
    exact ι.injective (σ.injective this.symm)
  let τ : Equiv.Perm (Fin B.card) := Equiv.ofBijective g (Finite.injective_iff_bijective.1 ginj)
  have h2 : mPf h l (fun i => Tight.y F (2 * h + 2) (σ (ι i))) =
      mPf h l (fun i => (fun j => Tight.y F (2 * h + 2) (ι' (Fin.cast hc.symm j))) (τ i)) := by
    congr 1
    funext i
    simp only [τ, Equiv.ofBijective_apply, hg]
  rw [h1, h2, A7 h l (fun j => Tight.y F (2 * h + 2) (ι' (Fin.cast hc.symm j))) τ]
  have h3 : mPf h l (fun j => Tight.y F (2 * h + 2) (ι' (Fin.cast hc.symm j))) =
      markedPf F h l B' := mPf_cast h l hc.symm (fun j => Tight.y F (2 * h + 2) (ι' j))
  rw [h3]
  exact PM_sign_mul τ _

/-- Auxiliary for (C2) of `q_oddbox_patterns.md`: the image `σ(T)` of a marked pattern `T` of `λ`
on `I` (pairs `σ(e)`, blocks `σ(B_c)`, marked block `σ(B_0)`) is a marked pattern of `λ` on
`σ(I)`. -/
def MarkedPattern.relabel {m : ℕ} (σ : Equiv.Perm (Fin m)) {lam : Partition}
    {I : Finset (Fin m)} (T : MarkedPattern lam I) : MarkedPattern lam (I.map σ.toEmbedding) where
  pairs := T.pairs.map ⟨Finset.map σ.toEmbedding, Finset.map_injective _⟩
  blocks c := (T.blocks c).map σ.toEmbedding
  marked := T.marked.map σ.toEmbedding
  card_pair := by
    intro e he
    obtain ⟨e0, he0, rfl⟩ := Finset.mem_map.1 he
    simp only [Function.Embedding.coeFn_mk, Finset.card_map]
    exact T.card_pair e0 he0
  pairs_disjoint := by
    intro e1 he1 e2 he2 hne
    obtain ⟨f1, hf1, rfl⟩ := Finset.mem_map.1 he1
    obtain ⟨f2, hf2, rfl⟩ := Finset.mem_map.1 he2
    have : f1 ≠ f2 := fun h => hne (h ▸ rfl)
    simp only [Function.onFun, id, Function.Embedding.coeFn_mk, Finset.disjoint_map]
    exact T.pairs_disjoint hf1 hf2 this
  card_block := by
    intro c hc
    rw [Finset.card_map]; exact T.card_block c hc
  blocks_disjoint := by
    intro c hc d hd hne
    simp only [Function.onFun, Finset.disjoint_map]
    exact T.blocks_disjoint hc hd hne
  pairs_blocks_disjoint := by
    intro e he c hc
    obtain ⟨f, hf, rfl⟩ := Finset.mem_map.1 he
    simp only [Function.Embedding.coeFn_mk, Finset.disjoint_map]
    exact T.pairs_blocks_disjoint f hf c hc
  pairs_marked_disjoint := by
    intro e he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_map.1 he
    simp only [Function.Embedding.coeFn_mk, Finset.disjoint_map]
    exact T.pairs_marked_disjoint f hf
  blocks_marked_disjoint := by
    intro c hc
    simp only [Finset.disjoint_map]
    exact T.blocks_marked_disjoint c hc
  marked_card := by
    obtain ⟨t, ht⟩ := T.marked_card
    exact ⟨t, by rw [Finset.card_map, ht]⟩
  cover := by
    have hc := congrArg (Finset.map σ.toEmbedding) T.cover
    rw [Finset.map_union, Finset.map_union, Tight.map_sup_eq, Tight.map_sup_eq] at hc
    rw [Finset.sup_map]
    exact hc

/-- Auxiliary for (C2) of `q_oddbox_patterns.md`: `σ(G(T)) = ±G(σ(T))`. -/
theorem relabel_markedProd_PM {m : ℕ} (σ : Equiv.Perm (Fin m)) {lam : Partition}
    {I : Finset (Fin m)} (T : MarkedPattern lam I) :
    Tight.PM (Tight.relabel F (2 * h + 2) σ (T.prod F h)) ((T.relabel σ).prod F h) := by
  unfold MarkedPattern.prod
  rw [map_mul, map_mul, map_prod, map_prod]
  simp only [MarkedPattern.relabel, Finset.prod_map, Function.Embedding.coeFn_mk]
  exact ((Tight.PM.prod _ (fun e he => Tight.relabel_pairD σ (T.card_pair e he))).mul
    (C1 σ lam.len T.marked)).mul
    (Tight.PM.prod _ (fun c _ => Tight.relabel_Delta σ (T.blocks c)))

/-- **Lemma C, (C2)** of `q_oddbox_patterns.md`: for a marked pattern `T` of `λ` on `I` there is
a marked pattern `T'` of `λ` on `σ(I)` with `σ(T.prod) = ± T'.prod`. -/
theorem C2 {m : ℕ} (σ : Equiv.Perm (Fin m)) {lam : Partition} {I : Finset (Fin m)}
    (T : MarkedPattern lam I) :
    ∃ T' : MarkedPattern lam (I.map σ.toEmbedding),
      Tight.relabel F (2 * h + 2) σ (T.prod F h) = T'.prod F h ∨
        Tight.relabel F (2 * h + 2) σ (T.prod F h) = -T'.prod F h :=
  ⟨T.relabel σ, relabel_markedProd_PM σ T⟩

/-- Auxiliary for (C3) of `q_oddbox_patterns.md`: transport of a marked pattern along an
equality of index sets. -/
theorem exists_marked_of_eq {m : ℕ} {lam : Partition} {I J : Finset (Fin m)} (hJ : J = I)
    (T : MarkedPattern lam J) : ∃ T0 : MarkedPattern lam I, T0.prod F h = T.prod F h := by
  subst hJ; exact ⟨T, rfl⟩

/-- Auxiliary for (C3) of `q_oddbox_patterns.md`: the image of the marked part of `V_Λ(I)`. -/
theorem map_relabel_marked {m : ℕ} (σ : Equiv.Perm (Fin m)) (Lam' : Set Partition)
    (I : Finset (Fin m)) :
    Ideal.map (Tight.relabel F (2 * h + 2) σ)
      (Ideal.span {g | ∃ lam ∈ Lam', ∃ T : MarkedPattern lam I, T.prod F h = g}) =
      Ideal.span {g | ∃ lam ∈ Lam', ∃ T : MarkedPattern lam (I.map σ.toEmbedding),
        T.prod F h = g} := by
  rw [Ideal.map_span]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨g, ⟨lam, hlam, T, rfl⟩, rfl⟩
    have hmem : (T.relabel σ).prod F h ∈
        Ideal.span {g | ∃ lam ∈ Lam', ∃ T : MarkedPattern lam (I.map σ.toEmbedding),
          T.prod F h = g} :=
      Ideal.subset_span ⟨lam, hlam, T.relabel σ, rfl⟩
    rcases relabel_markedProd_PM (F := F) (h := h) σ T with h | h
    · simp only [SetLike.mem_coe]; rw [h]; exact hmem
    · simp only [SetLike.mem_coe]; rw [h]; exact (Ideal.neg_mem_iff _).2 hmem
  · rw [Ideal.span_le]
    rintro _ ⟨lam, hlam, T, rfl⟩
    have hI : (I.map σ.toEmbedding).map σ.symm.toEmbedding = I := by
      rw [Finset.map_map]; simp
    obtain ⟨T0, hT0⟩ := exists_marked_of_eq (F := F) (h := h) hI (T.relabel σ.symm)
    have hmem : Tight.relabel F (2 * h + 2) σ (T0.prod F h) ∈
        Ideal.span ((Tight.relabel F (2 * h + 2) σ : Peel.C F (2 * h + 2) m →+*
          Peel.C F (2 * h + 2) m) ''
          {g | ∃ lam ∈ Lam', ∃ T : MarkedPattern lam I, T.prod F h = g}) :=
      Ideal.subset_span ⟨T0.prod F h, ⟨lam, hlam, T0, rfl⟩, rfl⟩
    have key : Tight.PM (T.prod F h) (Tight.relabel F (2 * h + 2) σ (T0.prod F h)) := by
      rw [hT0]
      have := (relabel_markedProd_PM (F := F) (h := h) σ.symm T).map
        (Tight.relabel F (2 * h + 2) σ).toRingHom
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Tight.relabel_relabel_symm] at this
      exact this
    rcases key with h | h
    · simp only [SetLike.mem_coe]; rw [h]; exact hmem
    · simp only [SetLike.mem_coe]; rw [h]; exact (Ideal.neg_mem_iff _).2 hmem

/-- **Lemma C, (C3)** of `q_oddbox_patterns.md`: `σ(V_Λ(I)) = V_Λ(σ(I))`, where `σ(V)` is the
image of the ideal `V` under the automorphism `y_i ↦ y_{σ(i)}` of `C_m`. -/
theorem C3 {m : ℕ} (σ : Equiv.Perm (Fin m)) (Lam : Set Shape) (I : Finset (Fin m)) :
    Ideal.map (Tight.relabel F (2 * h + 2) σ) (VS F h Lam I) =
      VS F h Lam (I.map σ.toEmbedding) := by
  unfold VS
  rw [Ideal.map_sup, Tight.map_relabel_VLam, map_relabel_marked]

/-- **Lemma C, (C3)** of `q_oddbox_patterns.md`, "In particular": `σ(V_Λ) = V_Λ`. -/
theorem C3_all {m : ℕ} (σ : Equiv.Perm (Fin m)) (Lam : Set Shape) :
    Ideal.map (Tight.relabel F (2 * h + 2) σ) (VSAll F h m Lam) = VSAll F h m Lam := by
  unfold VSAll
  rw [C3]
  congr 1
  exact Finset.map_univ_equiv σ

end OddPatterns

module

public import RequestProject.BipInd.Swap

/-!
# Item 6 of the Proofs of `q_any_bip.md`: Lemma S (iii) for every `q`

`q_any_bip.md`, **Proofs, "What the earlier proofs use", item 6** (*Lemma S, the swap*).  Parts
(i) and (ii) of Lemma S of `q_bip_induction.md` (`Bip.lemmaS_i`, `Bip.lemmaS_ii`) carry no
hypothesis on `q`.  Part (iii) (`Bip.lemmaS_iii`) was stated for odd `q`, through the sign
`(z_i − x_l)^{q−1} = (x_l − z_i)^{q−1}`.  Here, for every `q`,

`σ(prod T) = (−1)^{(q−1)·|P|} · prod T^⊤`

(`swapR_prod_sign`), and since `−1` is a unit, `σ(V_Λ) = V_{Λ^⊤}` and `dim V_{Λ^⊤} = dim V_Λ`
(`lemmaS_iii`), with no hypothesis on `q` at all.  The renaming isomorphism `σ` is `Bip.swapR`,
and the transposed pattern `T^⊤` is `Bip.BTightPattern.transpose`, both unchanged.
-/

@[expose] public section

open MvPolynomial

namespace BipAny

open Bip ChainLemma Tight

set_option synthInstance.maxHeartbeats 200000

variable (F : Type*) [Field F] (q : ℕ)

/-- `q_any_bip.md`, **Proofs, item 6** (the sign in Lemma S (iii), every `q`): for a tight pattern
`T` of `λ` on `([α], [β])` with pairs `P`,
`σ(Π_{(i,l)∈P}(x_i − z_l)^{q−1} · Π_c Δ(x_{B^+_c}) · Π_c Δ(z_{B^−_c}))
  = (−1)^{(q−1)·|P|} · Π_{(l,i)∈P^⊤}(x_l − z_i)^{q−1} · Π_c Δ(z_{B^+_c}) · Π_c Δ(x_{B^−_c})`,
i.e. `σ(prod T) = (−1)^{(q−1)·|P|} · prod T^⊤`, because
`(z_i − x_l)^{q−1} = (−1)^{q−1}(x_l − z_i)^{q−1}`.  (For odd `q` the sign is `+1`, which is
`Bip.swapR_prod`.) -/
theorem swapR_prod_sign {lam : Partition × Partition} {α β : ℕ} (T : BTightPattern lam α β) :
    swapR F q α β (T.prod F q) = (-1) ^ ((q - 1) * T.pairs.card) * T.transpose.prod F q := by
  have hx : (swapR F q α β : R F q α β →+* R F q β α) ∘ x F q = z F q :=
    funext fun i => swapR_x F q i
  have hz : (swapR F q α β : R F q α β →+* R F q β α) ∘ z F q = x F q :=
    funext fun i => swapR_z F q i
  have h1 : ∀ c, swapR F q α β (vand (x F q) (T.blocksX c)) = vand (z F q) (T.blocksX c) :=
    fun c => by rw [← hx]; exact vand_map (swapR F q α β : R F q α β →+* R F q β α) _ _
  have h2 : ∀ c, swapR F q α β (vand (z F q) (T.blocksZ c)) = vand (x F q) (T.blocksZ c) :=
    fun c => by rw [← hz]; exact vand_map (swapR F q α β : R F q α β →+* R F q β α) _ _
  have h3 : ∀ p : Fin α × Fin β, ((z F q p.1 : R F q β α) - x F q p.2) ^ (q - 1) =
      (-1) ^ (q - 1) * (x F q p.2 - z F q p.1) ^ (q - 1) := fun p => by
    rw [← neg_sub, neg_pow]
  have h4 : ∏ p ∈ T.pairs, ((z F q p.1 : R F q β α) - x F q p.2) ^ (q - 1) =
      (-1) ^ ((q - 1) * T.pairs.card) *
        ∏ p ∈ T.pairs, ((x F q p.2 : R F q β α) - z F q p.1) ^ (q - 1) := by
    rw [Finset.prod_congr rfl (fun p _ => h3 p), Finset.prod_mul_distrib, Finset.prod_const,
      pow_mul]
  unfold BTightPattern.prod
  simp only [map_mul, map_prod, map_pow, map_sub, swapR_x, swapR_z, h1, h2]
  rw [h4]
  simp only [BTightPattern.transpose, Finset.prod_map, Equiv.coe_toEmbedding,
    Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
  ring

/-- `q_any_bip.md`, **Proofs, item 6**: `σ(V_Λ) ⊆ V_{Λ^⊤}` for every `q` (the image of a generator
of `V_Λ` is `±` a generator of `V_{Λ^⊤}`). -/
theorem map_VLamB_le (α β : ℕ) (Λ : Set (Partition × Partition)) :
    (VLamB F q α β Λ).map (swapR F q α β) ≤ VLamB F q β α (swapSet Λ) := by
  unfold VLamB
  rw [Ideal.map_span]
  refine Ideal.span_le.2 ?_
  rintro _ ⟨_, ⟨lam, hlam, T, rfl⟩, rfl⟩
  rw [SetLike.mem_coe, swapR_prod_sign F q T]
  exact Ideal.mul_mem_left _ _
    (Ideal.subset_span ⟨lam.swap, mem_swapSet.2 (by simpa using hlam), T.transpose, rfl⟩)

/-- `q_any_bip.md`, **Proofs, item 6** (Lemma S (iii) of `q_bip_induction.md` for every `q`, odd
or even): the renaming isomorphism `σ : R_{α,β} → R_{β,α}` (`σ(x_i) = z_i`, `σ(z_l) = x_l`)
satisfies `σ(V_Λ) = V_{Λ^⊤}`, and so `dim V_{Λ^⊤} = dim V_Λ`.  Same statement as
`Bip.lemmaS_iii` without the hypothesis that `q` is odd (more general: no hypothesis on `q`). -/
theorem lemmaS_iii (α β : ℕ) (Λ : Set (Partition × Partition)) :
    (VLamB F q α β Λ).map (swapR F q α β) = VLamB F q β α (swapSet Λ) ∧
      Module.finrank F ((VLamB F q β α (swapSet Λ)).restrictScalars F) =
        Module.finrank F ((VLamB F q α β Λ).restrictScalars F) := by
  have heq : (VLamB F q α β Λ).map (swapR F q α β) = VLamB F q β α (swapSet Λ) := by
    refine le_antisymm (BipAny.map_VLamB_le F q α β Λ) ?_
    have h1 := BipAny.map_VLamB_le F q β α (swapSet Λ)
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

end BipAny

end

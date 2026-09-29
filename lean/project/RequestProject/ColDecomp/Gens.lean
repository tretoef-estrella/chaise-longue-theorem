module

public import RequestProject.ColDecomp.Pairs

/-!
# The generators `π_c(ψ_J)` in `B({1, …, d})` (`q_col_decomp.md`, Proof of Proposition 6.5)

* `piC_psi_eq_zero`: a matching `J` with `π_c(ψ_J) ≠ 0` is compatible;
* `piC_psi_eq_unit_mul`: for a compatible `J` corresponding to `(P, (σ_ζ))`,
  `π_c(ψ_J) = w_J · ι_{W_1}(g_P) · Π_ζ ι_{W_ζ}(g_{σ_ζ})` (read in `B({1, …, d})`) with `w_J` a unit.
-/

@[expose] public section

open MvPolynomial

namespace ColDecomp

open ColSplit ColSurv ColComp ColTensor

open scoped Classical

variable {F : Type*} [Field F] (S : ColSetting F) {k : ℕ}

/-- **Proof** of Proposition 6.5 in `q_col_decomp.md` (*a matching `J` with `π_c(ψ_J) ≠ 0` is
compatible*): by Lemma 6.2 (iii), `π_c(ψ_J) ≠ 0` forces `c_a c_{J(a)} = 1` for every pair with
`0 < a < J(a)`; since `c_0 c_1 ⋯ c_d = 1`, Lemma 6.3 (v) says that `J` is compatible. -/
theorem piC_psi_eq_zero (c : Fin (2 * k + 1) → S.μ) (J : BallotBound.Matching k)
    (hJ : ¬ Compatible (cExt c) J) : S.piC c (psi S k J) = 0 := by
  rw [lemma63_v (prod_cExt c)] at hJ
  push_neg at hJ
  obtain ⟨a, ha, hJa, hne⟩ := hJ
  refine (lemma62_iii S c J).1 ?_
  rcases lt_or_gt_of_ne (J.2 a).1.symm with hlt | hlt
  · exact ⟨a, Fin.pos_iff_ne_zero.2 ha, hlt, hne⟩
  · refine ⟨J.1 a, Fin.pos_iff_ne_zero.2 hJa, by rwa [(J.2 a).2], ?_⟩
    rwa [(J.2 a).2, mul_comm]

/-- The **Identification** `R_c = B({1, …, d})` of `q_col_decomp.md` sends `t_a ∈ R_c` to
`t_a ∈ B({1, …, d})` (for every `a ∈ V`, with the dummy value `0` at `a = 0` on both sides). -/
theorem rcEquiv_tR (c : Fin (2 * k + 1) → S.μ) (a : Fin (2 * k + 2)) :
    rcEquiv (boxS S c) (tR c a) = tB S c Finset.univ a := by
  cases a using Fin.cases with
  | zero => simp [tR, tB]
  | succ j =>
    simp only [tR, tB, Fin.cases_succ, dif_pos (Finset.mem_univ j)]
    exact rcEquiv_mk_X (boxS S c) j

/-- **Setting** of `q_col_decomp.md`: `ι_{W,{1,…,d}}(t_a) = t_a` for every `a ∈ V` whose variable
(if any) lies in `W`. -/
theorem iota_tB (c : Fin (2 * k + 1) → S.μ) (W : Finset (Fin (2 * k + 1))) (a : Fin (2 * k + 2))
    (ha : ∀ j : Fin (2 * k + 1), a = j.succ → j ∈ W) :
    (boxS S c).iota W Finset.univ (Finset.subset_univ W) (tB S c W a) = tB S c Finset.univ a := by
  cases a using Fin.cases with
  | zero => simp [tB]
  | succ j =>
    simp only [tB, Fin.cases_succ, dif_pos (ha j rfl), dif_pos (Finset.mem_univ j)]
    exact (boxS S c).iota_t W Finset.univ _ ⟨j, ha j rfl⟩

omit [Field F] in
/-- **Pair factors** of `q_col_decomp.md`: `f_{a,b}` is compatible with ring homomorphisms (it
only involves `t_a` and `t_b`). -/
theorem map_pairF {A B H : Type*} [CommRing A] [CommRing B] [FunLike H A B] [RingHomClass H A B]
    (f : H) (q : ℕ) (t : Fin (2 * k + 2) → A) (t' : Fin (2 * k + 2) → B) (a b : Fin (2 * k + 2))
    (ha : f (t a) = t' a) (hb : f (t b) = t' b) :
    f (pairF q t a b) = pairF q t' a b := by
  unfold pairF
  split_ifs <;> simp [map_mul, map_sub, map_pow, map_one, ha, hb]

/-- **Block generators** of `q_col_decomp.md`: `ι_{W_1}(g_P)` is the product of the `f_{a,b}`
over the pairs `{a < b}` of `P`, computed in `B({1, …, d})`. -/
theorem iota_gP (c : Fin (2 * k + 1) → S.μ) (P : PerfMatch (cls (cExt c) 1)) :
    (boxS S c).iota (W1 S c) Finset.univ (Finset.subset_univ _) (gP S c P) =
      ∏ x ∈ Finset.univ.filter (fun x => x.1 < (P.1 x).1),
        pairF S.q (tB S c Finset.univ) x.1 (P.1 x).1 := by
  rw [gP, map_prod]
  refine Finset.prod_congr rfl fun x _ => map_pairF _ _ _ _ _ _ ?_ ?_
  · exact iota_tB S c _ _ fun j hj => by
      simp only [W1, varSet, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← hj]; exact x.2
  · exact iota_tB S c _ _ fun j hj => by
      simp only [W1, varSet, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← hj]; exact (P.1 x).2

/-- **Block generators** of `q_col_decomp.md`: `ι_{W_ζ}(g_σ)` is the product of the
`f_{min(a,σ(a)), max(a,σ(a))}` over `a ∈ 𝒞_ζ`, computed in `B({1, …, d})`. -/
theorem iota_gσ (c : Fin (2 * k + 1) → S.μ) (ζ : F) (σ : cls (cExt c) ζ ≃ cls (cExt c) ζ⁻¹) :
    (boxS S c).iota (Wz S c ζ) Finset.univ (Finset.subset_univ _) (gσ S c ζ σ) =
      ∏ a : cls (cExt c) ζ, pairF S.q (tB S c Finset.univ) (min a.1 (σ a).1) (max a.1 (σ a).1) := by
  rw [gσ, map_prod]
  refine Finset.prod_congr rfl fun a _ => ?_
  have hmem : ∀ b, (b = a.1 ∨ b = (σ a).1) → ∀ j : Fin (2 * k + 1), b = j.succ → j ∈ Wz S c ζ := by
    rintro b hb j rfl
    simp only [Wz, varSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    rcases hb with hb | hb
    · exact Or.inl (hb ▸ a.2)
    · exact Or.inr (hb ▸ (σ a).2)
  refine map_pairF _ _ _ _ _ _ ?_ ?_
  · exact iota_tB S c _ _ (hmem _ (min_choice _ _))
  · exact iota_tB S c _ _ (hmem _ (max_choice _ _))

/-- **Proof** of Proposition 6.5 (ii) in `q_col_decomp.md` (*the product in (6.2) is exactly
`Π_{a<J(a)} f_{a,J(a)}`*): for a compatible `J`, `π_c(ψ_J)`, read in `B({1, …, d})`, is
`w_J · Π_{a<J(a)} f_{a,J(a)}` with `w_J` a unit (Lemma 6.2 (iii)). -/
theorem piC_psi_eq_unit_mul_prod (c : Fin (2 * k + 1) → S.μ) (J : BallotBound.Matching k)
    (hJ : Compatible (cExt c) J) :
    ∃ w : ((boxS S c).Box Finset.univ)ˣ,
      rcEquiv (boxS S c) (S.piC c (psi S k J)) =
        w * ∏ a ∈ Finset.univ.filter (fun a => a < J.1 a),
          pairF S.q (tB S c Finset.univ) a (J.1 a) := by
  obtain ⟨-, w, hw⟩ := (lemma62_iii S c J).2 fun a _ _ => hJ a
  refine ⟨(w.map (rcEquiv (boxS S c)).toMonoidHom), ?_⟩
  rw [hw, map_mul, map_mul, map_prod, map_prod, mul_assoc]
  congr 1
  simp only [map_sub, map_mul, map_pow, map_one, rcEquiv_tR]
  rw [show Finset.univ.filter (fun x => 0 < x ∧ x < J.1 x) =
      (Finset.univ.filter (fun x => x < J.1 x)).filter (fun x => 0 < x) by
    rw [Finset.filter_filter]; ext x; simp [and_comm], Finset.prod_filter (fun x => 0 < x),
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  unfold pairF
  by_cases ha : a = 0
  · simp [ha]
  · rw [if_pos (Fin.pos_iff_ne_zero.2 ha), if_neg ha]

/-- **Proof** of Proposition 6.5 (ii) in `q_col_decomp.md`: for a compatible `J` corresponding to
`(P, (σ_ζ))` by Lemma 6.3 (iii) (`P = J|_{𝒞_1}`, `σ_ζ = J|_{𝒞_ζ}`), `π_c(ψ_J)`, read in
`B({1, …, d})`, is `w_J · ι_{W_1}(g_P) · Π_{ζ∈ℛ} ι_{W_ζ}(g_{σ_ζ})` with `w_J` a unit. -/
theorem piC_psi_eq_unit_mul (c : Fin (2 * k + 1) → S.μ) {R : Finset F} (hR : IsReps S R)
    (J : CompMatching (cExt c)) :
    ∃ w : ((boxS S c).Box Finset.univ)ˣ,
      rcEquiv (boxS S c) (S.piC c (psi S k J.1)) =
        w * ((boxS S c).iota (W1 S c) Finset.univ (Finset.subset_univ _)
            (gP S c (restrict (cExt c) R J).1) *
          ∏ ζ : R, (boxS S c).iota (Wz S c ζ) Finset.univ (Finset.subset_univ _)
            (gσ S c ζ ((restrict (cExt c) R J).2 ζ))) := by
  obtain ⟨w, hw⟩ := piC_psi_eq_unit_mul_prod S c J.1 J.2
  refine ⟨w, ?_⟩
  rw [hw, prod_pairs_split hR (cExt_mem c) J (pairF S.q (tB S c Finset.univ)), iota_gP]
  simp_rw [iota_gσ]

end ColDecomp

end

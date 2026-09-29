module

public import RequestProject.ColCount.Blocks

/-!
# Lemma 6.8 (ii) and (iii) of `q_col_count.md`

* `ColCount.lemma68_i`: part (i) — `T_m` is a point set with a fixed-point-free involution and
  `|T_m| = m − 1 = 2H`; the point set itself is `ColCount.TmSetting`;
* `ColCount.lemma68_ii`: part (ii) — the number of closed tuples of `T_m^{2k+2}` with colour tuple
  `cExt c` is `[comp(c)]·N_1(c)·Π_{ζ∈ℛ} N_ζ(c)`;
* `ColCount.lemma68_iii`: part (iii) — `Σ_c [comp(c)]·N_1(c)·Π_{ζ∈ℛ} N_ζ(c) = Q_k(m)`.
-/

@[expose] public section

namespace ColCount

open ColSplit ColSurv ColComp Fibres TheoremB

open scoped Classical

variable {F : Type*} [Field F] {S : ColSetting F}

/-- **Lemma 6.8 (i)** of `q_col_count.md`: the involution `(w, ζ) ↦ (w̄, ζ^{−1})` of
`T_m = (Ω_q × μ) ∖ {(∗, 1)}` is an involution without fixed points, and
`|T_m| = m − 1 = 2H` with `H = (m − 1)/2 ≥ 1`. (The point set with these properties is
`TmSetting S hp hr`.) -/
theorem lemma68_i (hp : S.p ≠ 2) (hr : Odd S.r) :
    (∀ x : Tm S, negTm S (negTm S x) = x) ∧ (∀ x : Tm S, negTm S x ≠ x) ∧
      Fintype.card (Tm S) = S.m - 1 ∧ S.m - 1 = 2 * ((S.m - 1) / 2) ∧ 1 ≤ (S.m - 1) / 2 :=
  ⟨(TmSetting S hp hr).neg_neg, (TmSetting S hp hr).neg_ne, card_Tm S hp,
    by have h := (TmSetting S hp hr).card_eq; rwa [card_Tm S hp] at h, (TmSetting S hp hr).one_le⟩

/-- **Proof of Lemma 6.8 (ii)** of `q_col_count.md` (last paragraph): if
`|𝒞_ζ| = |𝒞_{ζ^{−1}}|`, then `N_{bal}(|𝒞_ζ|, q) = N_ζ(c)` (using Lemma 7.2 (iii) of
`q_bip_setting.md` when `0 ∈ 𝒞_ζ ∪ 𝒞_{ζ^{−1}}`). -/
theorem Nbal_eq_Nz {R : Finset F} (hR : IsReps S R) {k : ℕ} (c : Fin (2 * k + 1) → S.μ) {ζ : F}
    (hζ : ζ ∈ R) (h : (cls (cExt c) ζ).card = (cls (cExt c) ζ⁻¹).card) :
    Bip.Nbal (cls (cExt c) ζ).card S.q = Nz c ζ := by
  have hdisj := (lemma63_i_disjoint hR hζ (cExt c)).1
  unfold Nz
  split_ifs with h0
  · rcases Finset.mem_union.1 h0 with h0 | h0
    · have h0' : (0 : Fin (2 * k + 2)) ∉ cls (cExt c) ζ⁻¹ := Finset.disjoint_left.1 hdisj h0
      have hpos : 0 < (cls (cExt c) ζ).card := Finset.card_pos.2 ⟨_, h0⟩
      rw [Finset.card_erase_of_mem h0, Finset.erase_eq_of_notMem h0', ← h,
        min_eq_left (Nat.sub_le _ _), Bip.lemma72_iii, Nat.sub_add_cancel hpos]
    · have h0' : (0 : Fin (2 * k + 2)) ∉ cls (cExt c) ζ :=
        fun h' => Finset.disjoint_left.1 hdisj h' h0
      have hpos : 0 < (cls (cExt c) ζ⁻¹).card := Finset.card_pos.2 ⟨_, h0⟩
      rw [Finset.card_erase_of_mem h0, Finset.erase_eq_of_notMem h0', h,
        min_eq_right (Nat.sub_le _ _), Bip.lemma72_iii, Nat.sub_add_cancel hpos]
  · have h0' : (0 : Fin (2 * k + 2)) ∉ cls (cExt c) ζ := fun h' => h0 (Finset.mem_union_left _ h')
    rw [Finset.erase_eq_of_notMem h0']

/-- **Lemma 6.8 (ii)** of `q_col_count.md`: for every colouring `c ∈ μ^d`, the number of closed
tuples `g ∈ T_m^{2k+2}` whose colour tuple `(g_0.2, g_1.2, …, g_{2k+1}.2)` is the extended colouring
`(c_0, c_1, …, c_d)` equals `N_1(c)·Π_{ζ∈ℛ} N_ζ(c)` if some matching is compatible with `c`, and `0`
otherwise. -/
theorem lemma68_ii (hp : S.p ≠ 2) (hr : Odd S.r) {R : Finset F} (hR : IsReps S R) (k : ℕ)
    (c : Fin (2 * k + 1) → S.μ) :
    ((closedTuples (TmSetting S hp hr) (2 * k + 2)).filter
        fun g => ∀ i, ((g i).1.2 : F) = cExt c i).card =
      if ∃ J : BallotBound.Matching k, Compatible (cExt c) J then
        N1 hp c * ∏ ζ ∈ R, Nz c ζ
      else 0 := by
  have hκ : ∀ i, cExt c i ∈ S.μ := cExt_mem c
  split_ifs with hcomp
  · have hsz := ((lemma63_iv_exists hR hκ).1 hcomp).2
    rw [card_col_eq_card_good hp hr _ hκ]
    refine (card_good_eq_prod (X := Fin (2 * k + 2)) hR (cExt c)).trans ?_
    rw [Fintype.prod_option]
    congr 1
    · refine (card_good_one (X := {v // blk R (cExt c v) = none}) hp (fun j => cExt c j.1)
        (fun j => (blk_eq_none hR (hκ j.1)).1 j.2)).trans ?_
      have hset : (Finset.univ.filter fun v => blk R (cExt c v) = none) = cls (cExt c) 1 := by
        ext v
        simp [cls, blk_eq_none hR (hκ v)]
      rw [N1, Fintype.card_subtype, hset]
    · rw [← Finset.prod_coe_sort R (fun ζ => Nz c ζ)]
      refine Finset.prod_congr rfl fun ζ _ => ?_
      rw [← Nbal_eq_Nz hR c ζ.2 (hsz ζ ζ.2)]
      refine card_good_pair (X := {v // blk R (cExt c v) = some ζ}) hp (fun j => cExt c j.1)
        (hR.mem ζ.2).2.1 (hR.inv_ne ζ.2) ?_ ?_ ?_
      · intro j
        exact (blk_eq_some hR ζ _).1 j.2
      · refine (card_filter_subtype _ (fun v => cExt c v = ζ)).trans ?_
        congr 1
        ext v
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, blk_eq_some hR, cls]
        constructor
        · rintro ⟨_, h⟩; exact h
        · intro h; exact ⟨Or.inl h, h⟩
      · refine (card_filter_subtype _ (fun v => cExt c v = (ζ : F)⁻¹)).trans ?_
        rw [hsz ζ ζ.2]
        congr 1
        ext v
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, blk_eq_some hR, cls]
        constructor
        · rintro ⟨_, h⟩; exact h
        · intro h; exact ⟨Or.inr h, h⟩
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro g hg hcol
    apply hcomp
    obtain ⟨J, hJ⟩ := exists_compatible_col hp hr hR hg
    have : col g = cExt c := funext hcol
    exact ⟨J, this ▸ hJ⟩

/-- **Lemma 6.8 (iii)** of `q_col_count.md`:
`Σ_{c ∈ μ^d} [comp(c)]·N_1(c)·Π_{ζ∈ℛ} N_ζ(c) = Q_k(m)`, where `[comp(c)]·X` is `X` if some matching
is compatible with `c` and `0` otherwise.  Proved from (i), (ii) and Theorem (ii) of
`q_theorem_B_lower.md` (with `q := m`, `h := H = (m − 1)/2`). -/
theorem lemma68_iii (hp : S.p ≠ 2) (hr : Odd S.r) {R : Finset F} (hR : IsReps S R) (k : ℕ) :
    ∑ c : Fin (2 * k + 1) → S.μ,
        (if ∃ J : BallotBound.Matching k, Compatible (cExt c) J then
          N1 hp c * ∏ ζ ∈ R, Nz c ζ
        else 0) = Qk k S.m := by
  rw [← card_closedTuples (TmSetting S hp hr) k]
  simp_rw [← lemma68_ii hp hr hR k]
  symm
  rw [Finset.card_eq_sum_card_fiberwise (f := fun (g : Fin (2 * k + 2) → Tm S) (j : Fin (2 * k + 1)) => (g j.succ).1.2)
    (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  ext g
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hg, rfl⟩
    refine ⟨hg, fun i => ?_⟩
    exact congrFun (col_eq_cExt hp hr hR hg) i
  · rintro ⟨hg, h⟩
    refine ⟨hg, funext fun j => Subtype.ext ?_⟩
    simpa [cExt] using h j.succ

end ColCount

end

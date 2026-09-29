module

public import RequestProject.Tight.Lemmas

/-!
# The Lemma (three identities) of `q_P3_identities.md`

Parts (i), (ii), (iii) and (iv) of the **Lemma (three identities)** of `q_P3_identities.md`.
-/

@[expose] public section

open MvPolynomial

namespace Tight

open Peel ChainLemma

set_option synthInstance.maxHeartbeats 200000

variable {F : Type*} [Field F] {q : ℕ} {m : ℕ}

/-- **Setting, "Column lengths"** of `q_P3_identities.md`: `Σ_{c=1}^{λ_1} λ'_c = |λ|`. -/
theorem sum_colLen (lam : Partition) :
    ∑ c ∈ Finset.Icc 1 (lam.row 1), colLen lam c = lam.size := by
  unfold colLen Partition.size
  apply sum_filter_length_le
  intro x hx
  obtain ⟨parts, sorted, pos⟩ := lam
  cases parts with
  | nil => simp at hx
  | cons a l =>
    simp only [Partition.row]
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact le_rfl
    · exact (List.pairwise_cons.1 sorted).1 x hx

/-- **Lemma (i)** of `q_P3_identities.md`: for `a ≠ b` and `0 ≤ t ≤ q − 2`, the coefficient of
`y_a^{q−2−t}` in `D(y_a, y_b)` (as a polynomial in `y_a`) is `(−1)^{t+1} y_b^t`.
(Here `q ≥ 3` is odd, as in the Setting.) -/
theorem coeffY_D (hq : 3 ≤ q) (hodd : Odd q) {a b : Fin m} (hab : a ≠ b) {t : ℕ}
    (ht : t ≤ q - 2) :
    coeffY a (q - 2 - t) (D F q a b) = (-1) ^ (t + 1) * y F q b ^ t := by
  rw [D_eq_mk, coeffY_mk a (by omega)]
  have hba : b ≠ a := Ne.symm hab
  have h1 : polyIn F a (∑ i ∈ Finset.range (q - 1), (-1) ^ i * X a ^ i * X b ^ (q - 2 - i)) =
      ∑ i ∈ Finset.range (q - 1),
        Polynomial.C ((-1) ^ i * X ⟨b, hba⟩ ^ (q - 2 - i)) * Polynomial.X ^ i := by
    simp only [map_sum, map_mul, map_pow, map_neg, map_one, polyIn_X_self, polyIn_X_ne hba]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  simp only [pcoeff, h1, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.2 (by omega))]
  simp only [map_mul, map_pow, map_neg, map_one, rename_X]
  rw [show q - 2 - (q - 2 - t) = t by omega]
  simp only [y]
  congr 1
  rw [neg_one_pow_eq_pow_mod_two, neg_one_pow_eq_pow_mod_two (n := t + 1)]
  obtain ⟨k, rfl⟩ := hodd
  congr 1
  omega

/-- **Lemma (ii)** of `q_P3_identities.md`: let `S = {b_1 < ⋯ < b_r}` with `r ≥ 1` and put
`ε_{b_c} := (−1)^{r+c}` (the position `c` of `b ∈ S` is `#{x ∈ S : x < b} + 1`).  Then
`Σ_{b ∈ S} ε_b · Δ(S ∖ {b}) · y_b^t = 0` for `0 ≤ t ≤ r − 2` (written `t + 2 ≤ r`), and
`= Δ(S)` for `t = r − 1`.  (This holds for every `q`.) -/
theorem sum_eps_Delta (S : Finset (Fin m)) (hS : 1 ≤ S.card) :
    (∀ t : ℕ, t + 2 ≤ S.card →
      ∑ b ∈ S, (-1) ^ (S.card + ((S.filter (· < b)).card + 1)) * Delta F q (S.erase b) *
        y F q b ^ t = 0) ∧
    ∑ b ∈ S, (-1) ^ (S.card + ((S.filter (· < b)).card + 1)) * Delta F q (S.erase b) *
        y F q b ^ (S.card - 1) = Delta F q S := by
  refine ⟨fun t ht => ?_, ?_⟩
  · have := sum_eps_vand (y F q) S t (by omega)
    rw [if_neg (by omega), zero_mul] at this
    exact this
  · have := sum_eps_vand (y F q) S (S.card - 1) (by omega)
    rw [if_pos rfl, one_mul] at this
    exact this

/-- **Lemma (iii)**, first statement, of `q_P3_identities.md`: if `a < b` for all `b ∈ B` (so in
particular `a ∉ B`), then `Δ(B ∪ {a}) = Π_{c ∈ B} (y_c − y_a) · Δ(B)`.  (This holds for every
`q`; the hypothesis `a ∉ B` of the file follows from `a < b` for all `b ∈ B`.) -/
theorem Delta_insert_of_lt (B : Finset (Fin m)) (a : Fin m) (hlt : ∀ b ∈ B, a < b) :
    Delta F q (insert a B) = (∏ c ∈ B, (y F q c - y F q a)) * Delta F q B := by
  exact vand_insert_of_lt _ _ _ hlt

/-- **Lemma (iii)**, "Consequently", of `q_P3_identities.md`: if `a < b` for all `b ∈ B` and
`|B| ≤ q − 2`, then in `C_m` the element `Δ(B ∪ {a})` has degree exactly `|B|` in `y_a`, and its
coefficient of `y_a^{|B|}` is `(−1)^{|B|} Δ(B)`.  (Degree and coefficients in `y_a` are those of
the unique representative with all exponents of `y_a` at most `q − 2`, see `coeffY` and `degY`;
`q ≥ 3` as in the Setting.) -/
theorem degY_coeffY_Delta_insert (hq : 3 ≤ q) (B : Finset (Fin m)) (a : Fin m)
    (hlt : ∀ b ∈ B, a < b) (hB : B.card ≤ q - 2) :
    degY a (Delta F q (insert a B)) = B.card ∧
      coeffY a B.card (Delta F q (insert a B)) = (-1) ^ B.card * Delta F q B :=
  ⟨degY_Delta_insert hq B a hlt hB, coeffY_Delta_insert B a hlt hB⟩

/-- **Lemma (iv) (relabelling)**, first statement, of `q_P3_identities.md`: for a permutation
`σ` of `{1, …, m}` acting on `C_m` by `y_i ↦ y_{σ(i)}`, the image of a tight-pattern product of
`λ` on `I` is `±` a tight-pattern product of `λ` on `σ(I)`.  (This holds for every `q`.) -/
theorem relabel_prod (σ : Equiv.Perm (Fin m)) {lam : Partition} {I : Finset (Fin m)}
    (T : TightPattern lam I) :
    ∃ T' : TightPattern lam (I.map σ.toEmbedding),
      relabel F q σ (T.prod F q) = T'.prod F q ∨ relabel F q σ (T.prod F q) = -T'.prod F q :=
  ⟨T.relabel σ, relabel_prod_PM σ T⟩

/-- **Lemma (iv) (relabelling)**, "Hence", of `q_P3_identities.md`: `σ(V_Λ(I)) = V_Λ(σ(I))`,
where `σ(V)` is the image of the ideal `V` under the automorphism `y_i ↦ y_{σ(i)}` of `C_m`.
(This holds for every `q`.) -/
theorem map_relabel_VLam (σ : Equiv.Perm (Fin m)) (Λ : Set Partition) (I : Finset (Fin m)) :
    Ideal.map (relabel F q σ) (VLam F q Λ I) = VLam F q Λ (I.map σ.toEmbedding) := by
  unfold VLam
  rw [Ideal.map_span]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨g, ⟨lam, hlam, T, rfl⟩, rfl⟩
    have hmem : (T.relabel σ).prod F q ∈
        Ideal.span {g | ∃ lam ∈ Λ, ∃ T : TightPattern lam (I.map σ.toEmbedding), T.prod F q = g} :=
      Ideal.subset_span ⟨lam, hlam, T.relabel σ, rfl⟩
    rcases relabel_prod_PM (F := F) (q := q) σ T with h | h
    · simp only [SetLike.mem_coe]; rw [h]; exact hmem
    · simp only [SetLike.mem_coe]; rw [h]; exact (Ideal.neg_mem_iff _).2 hmem
  · rw [Ideal.span_le]
    rintro _ ⟨lam, hlam, T, rfl⟩
    have hI : (I.map σ.toEmbedding).map σ.symm.toEmbedding = I := by
      rw [Finset.map_map]; simp
    obtain ⟨T0, hT0⟩ := exists_pattern_of_eq (F := F) (q := q) hI (T.relabel σ.symm)
    have hmem : relabel F q σ (T0.prod F q) ∈
        Ideal.span ((relabel F q σ : C F q m →+* C F q m) ''
          {g | ∃ lam ∈ Λ, ∃ T : TightPattern lam I, T.prod F q = g}) :=
      Ideal.subset_span ⟨T0.prod F q, ⟨lam, hlam, T0, rfl⟩, rfl⟩
    have key : PM (T.prod F q) (relabel F q σ (T0.prod F q)) := by
      rw [hT0]
      have := (relabel_prod_PM (F := F) (q := q) σ.symm T).map (relabel F q σ).toRingHom
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, relabel_relabel_symm] at this
      exact this
    rcases key with h | h
    · rw [h]; exact hmem
    · rw [h]; exact (Ideal.neg_mem_iff _).2 hmem

end Tight

end

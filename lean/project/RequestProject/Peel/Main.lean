module

public import RequestProject.Peel.Expand

/-!
# The peeling lemma (`q_peeling_lemma.md`)

This file proves parts (i)–(iv) of the **Lemma (peeling)** of `q_peeling_lemma.md`, for every
field `F`, every `q ≥ 3` and every `m ≥ 1`.
-/

@[expose] public section

open Polynomial

namespace Peel

set_option synthInstance.maxHeartbeats 200000

variable {F : Type*} [Field F] {q : ℕ}

/-- The expansion of `f ∈ C_m` is the expansion of its image in `C_{m−1}[y_1]/(y_1^{q−1})`
(**Setting** of `q_peeling_lemma.md`).
Used in parts (i), (ii) and (iii) of the Lemma (peeling) of `q_peeling_lemma.md`. -/
theorem expand_apply {m : ℕ} (hm : 1 ≤ m) (f : C F q m) :
    expand hm f = expandGen F q (C F q (m - 1)) (peelEquiv F q m hm f) := rfl

/-- The coefficient `[y_1^j] f` is the `j`-th coefficient of the expansion (**Setting** of
`q_peeling_lemma.md`).
Used in parts (i), (ii) and (iii) of the Lemma (peeling) of `q_peeling_lemma.md`. -/
theorem coeffY1_apply {m : ℕ} (hm : 1 ≤ m) (j : ℕ) (f : C F q m) :
    coeffY1 hm j f = (expand hm f).coeff j := rfl

/-- Membership in `V_{≤j}` (**Setting** of `q_peeling_lemma.md`): `f ∈ V` and all coefficients
`[y_1^k] f` with `k > j` vanish, i.e. `deg_{y_1} f ≤ j`.
Used in parts (i), (ii) and (iii) of the Lemma (peeling) of `q_peeling_lemma.md`. -/
theorem mem_Vle {m : ℕ} (hm : 1 ≤ m) (V : Ideal (C F q m)) (j : ℕ) (f : C F q m) :
    f ∈ Vle hm V j ↔ f ∈ V ∧ ∀ k : ℕ, j < k → (expand hm f).coeff k = 0 := by
  simp only [Vle, degLE, Submodule.mem_inf, Submodule.restrictScalars_mem, Submodule.mem_comap,
    Polynomial.mem_degreeLE, degree_le_iff_coeff_zero, Nat.cast_lt]

/-- Membership in `V_{≤j}` in terms of `deg_{y_1}` (the literal definition
`V_{≤j} = {f ∈ V : deg_{y_1} f ≤ j}` of the **Setting** of `q_peeling_lemma.md`).
Used in parts (i), (ii) and (iii) of the Lemma (peeling) of `q_peeling_lemma.md`. -/
theorem mem_Vle_iff_degY1 {m : ℕ} (hm : 1 ≤ m) (V : Ideal (C F q m)) (j : ℕ) (f : C F q m) :
    f ∈ Vle hm V j ↔ f ∈ V ∧ degY1 hm f ≤ j := by
  simp only [Vle, degLE, Submodule.mem_inf, Submodule.restrictScalars_mem, Submodule.mem_comap,
    Polynomial.mem_degreeLE, degY1]

/-- Membership in `W_j(V)` (the literal definition `W_j(V) = {[y_1^j] f : f ∈ V_{≤j}}` of the
**Setting** of `q_peeling_lemma.md`).
Used in parts (i), (ii) and (iii) of the Lemma (peeling) of `q_peeling_lemma.md`. -/
theorem mem_W {m : ℕ} (hm : 1 ≤ m) (V : Ideal (C F q m)) (j : ℕ) (w : C F q (m - 1)) :
    w ∈ W hm V j ↔ ∃ f ∈ Vle hm V j, coeffY1 hm j f = w := Submodule.mem_map

/-- **Lemma (peeling), part (i)** of `q_peeling_lemma.md`: `W_j(V)` is an ideal of `C_{m−1}` for
every `0 ≤ j ≤ q−2`.  Encoding: `W_j(V)` is defined as a set (an `F`-subspace) of `C_{m−1}`, and
"is an ideal" means that there is an ideal of `C_{m−1}` whose underlying set is exactly `W_j(V)`.
The hypotheses `3 ≤ q` and `j ≤ q - 2` of the source are kept, although the proof does not
need them. -/
theorem W_isIdeal (hq : 3 ≤ q) {m : ℕ} (hm : 1 ≤ m) (V : Ideal (C F q m)) (j : ℕ)
    (hj : j ≤ q - 2) :
    ∃ I : Ideal (C F q (m - 1)), (I : Set (C F q (m - 1))) = W hm V j := by
  refine ⟨{ carrier := W hm V j
            add_mem' := (W hm V j).add_mem
            zero_mem' := (W hm V j).zero_mem
            smul_mem' := ?_ }, rfl⟩
  intro c w hw
  obtain ⟨f, hf, rfl⟩ := (mem_W hm V j w).1 hw
  set e := peelEquiv F q m hm
  have key : expand hm (e.symm (AdjoinRoot.of _ c) * f) = Polynomial.C c * expand hm f := by
    rw [expand_apply, expand_apply, map_mul, AlgEquiv.apply_symm_apply, expandGen_of_mul]
  rw [mem_Vle] at hf
  refine (mem_W hm V j _).2 ⟨e.symm (AdjoinRoot.of _ c) * f, (mem_Vle hm V j _).2
    ⟨V.mul_mem_left _ hf.1, fun k hk => ?_⟩, ?_⟩
  · rw [key, coeff_C_mul, hf.2 k hk, mul_zero]
  · rw [coeffY1_apply, coeffY1_apply, key, coeff_C_mul, smul_eq_mul]

/-- **Lemma (peeling), part (ii)** of `q_peeling_lemma.md`: `W_j(V) ⊆ W_{j+1}(V)` for
`0 ≤ j < q−2`.  The hypothesis `3 ≤ q` of the source is kept, although the proof does not
need it (it only ensures that such `j` exist). -/
theorem W_mono (hq : 3 ≤ q) {m : ℕ} (hm : 1 ≤ m) (V : Ideal (C F q m)) (j : ℕ)
    (hj : j < q - 2) : W hm V j ≤ W hm V (j + 1) := by
  intro w hw
  obtain ⟨f, hf, rfl⟩ := (mem_W hm V j w).1 hw
  set e := peelEquiv F q m hm
  have hdeg : (expand hm f).degree ≤ j := ((mem_Vle_iff_degY1 hm V j f).1 hf).2
  have key : expand hm (e.symm (AdjoinRoot.root _) * f) = Polynomial.X * expand hm f := by
    rw [expand_apply, expand_apply, map_mul, AlgEquiv.apply_symm_apply]
    exact expandGen_root_mul _ j hdeg hj
  refine (mem_W hm V (j + 1) _).2 ⟨e.symm (AdjoinRoot.root _) * f, (mem_Vle_iff_degY1 hm V _ _).2
    ⟨V.mul_mem_left _ ((mem_Vle hm V j f).1 hf).1, ?_⟩, ?_⟩
  · rw [degY1, key]
    exact degree_X_mul_le _ j hdeg
  · rw [coeffY1_apply, coeffY1_apply, key, coeff_X_mul]

/-- Each `C_m` is finite-dimensional over `F` (the remark "all rings here are finite-dimensional
over `F`" in part (iii) of `q_peeling_lemma.md`).
Used in part (iii) of the Lemma (peeling) of `q_peeling_lemma.md`. -/
instance finite_C (m : ℕ) : Module.Finite F (C F q m) := by
  induction m with
  | zero =>
    haveI : Module.Finite F (MvPolynomial (Fin 0) F) :=
      Module.Finite.equiv (MvPolynomial.isEmptyAlgEquiv F (Fin 0)).toLinearEquiv.symm
    exact Module.Finite.of_surjective (Ideal.Quotient.mkₐ F (powIdeal F q 0)).toLinearMap
      (Ideal.Quotient.mkₐ_surjective F _)
  | succ n ih =>
    haveI : Module.Finite (C F q n) (Peeled q (C F q n)) :=
      (AdjoinRoot.powerBasis' (monic_X_pow_q q (C F q n))).finite
    haveI : Module.Finite F (Peeled q (C F q n)) := Module.Finite.trans (C F q n) _
    exact Module.Finite.equiv (peelEquiv' F q n).symm.toLinearEquiv

/-- The dimension count behind part (iii) of `q_peeling_lemma.md`:
`dim V_{≤j} = Σ_{i=0}^{j} dim W_i(V)`, obtained by summing
`dim V_{≤i} = dim V_{≤i−1} + dim W_i(V)`.
Used in part (iii) of the Lemma (peeling) of `q_peeling_lemma.md`. -/
theorem finrank_Vle {m : ℕ} (hm : 1 ≤ m) (V : Ideal (C F q m)) (j : ℕ) :
    Module.finrank F (Vle hm V j) = ∑ i ∈ Finset.range (j + 1), Module.finrank F (W hm V i) := by
  have hrank : ∀ j, Module.finrank F (Vle hm V j) = Module.finrank F (W hm V j) +
      Module.finrank F (Vle hm V j ⊓ LinearMap.ker (coeffY1 hm j) : Submodule F (C F q m)) := by
    intro j
    have h := LinearMap.finrank_range_add_finrank_ker ((coeffY1 hm j).domRestrict (Vle hm V j))
    rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at h
    have e : Submodule.comap (Vle hm V j).subtype (LinearMap.ker (coeffY1 hm j)) =
        Submodule.comap (Vle hm V j).subtype (Vle hm V j ⊓ LinearMap.ker (coeffY1 hm j)) := by
      ext x; simp
    rw [e, (Submodule.comapSubtypeEquivOfLe inf_le_left).finrank_eq] at h
    rw [← h]; rfl
  have hker0 : (Vle hm V 0 ⊓ LinearMap.ker (coeffY1 hm 0) : Submodule F (C F q m)) = ⊥ := by
    rw [eq_bot_iff]
    intro f hf
    rw [Submodule.mem_inf, mem_Vle, LinearMap.mem_ker, coeffY1_apply] at hf
    have h0 : expand hm f = 0 := by
      ext k
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simpa using hf.2
      · simpa using hf.1.2 k hk
    rw [expand_apply] at h0
    have := mk_expandGen (F := F) (peelEquiv F q m hm f)
    rw [h0, map_zero, eq_comm, map_eq_zero_iff _ (peelEquiv F q m hm).injective] at this
    simp [this]
  have hkerS : ∀ j, (Vle hm V (j + 1) ⊓ LinearMap.ker (coeffY1 hm (j + 1)) :
      Submodule F (C F q m)) = Vle hm V j := by
    intro j
    ext f
    rw [Submodule.mem_inf, mem_Vle, mem_Vle, LinearMap.mem_ker, coeffY1_apply]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h1, fun k hk => ?_⟩
      rcases Nat.lt_or_ge (j + 1) k with h | h
      · exact h2 k h
      · rw [show k = j + 1 by omega]; exact h3
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, fun k hk => h2 k (by omega)⟩, h2 _ (by omega)⟩
  induction j with
  | zero => rw [hrank, hker0]; simp
  | succ j ih => rw [hrank, hkerS, ih, Finset.sum_range_succ _ (j + 1), add_comm]

/-- **Lemma (peeling), part (iii)** of `q_peeling_lemma.md`:
`dim_F V = Σ_{j=0}^{q−2} dim_F W_j(V)`.  Encoding: `dim_F V` is the `F`-dimension of the ideal
`V` regarded as an `F`-subspace of `C_m` (`V.restrictScalars F`), and the sum over
`j = 0, …, q−2` is over `Finset.range (q - 1)`. -/
theorem finrank_eq_sum (hq : 3 ≤ q) {m : ℕ} (hm : 1 ≤ m) (V : Ideal (C F q m)) :
    Module.finrank F (V.restrictScalars F) =
      ∑ j ∈ Finset.range (q - 1), Module.finrank F (W hm V j) := by
  have hV : Vle hm V (q - 2) = V.restrictScalars F := by
    ext f
    rw [mem_Vle_iff_degY1, Submodule.restrictScalars_mem]
    exact ⟨fun h => h.1, fun h => ⟨h, degree_expandGen_le (F := F) (by omega) _⟩⟩
  rw [← hV, finrank_Vle, show q - 2 + 1 = q - 1 by omega]

/-- The tail `M' = (t_2, …, t_m)` of a tuple `(t_1, …, t_m) ∈ T^m` (**Setting** of
`q_peeling_lemma.md`, counting part).
Used in part (iv) of the Lemma (peeling) of `q_peeling_lemma.md`. -/
def tailTuple {T : Type*} {m : ℕ} (M : Fin m → T) : Fin (m - 1) → T :=
  fun i => M ⟨i + 1, by omega⟩

/-- The tail of `(t, M')` is `M'` (part (iv) of the proof in `q_peeling_lemma.md`). -/
theorem tailTuple_consTuple {T : Type*} {m : ℕ} (t : T) (M' : Fin (m - 1) → T) :
    tailTuple (consTuple t M') = M' := by
  funext i
  simp [tailTuple, consTuple]

/-- The first coordinate of `(t, M')` is `t` (part (iv) of the proof in `q_peeling_lemma.md`). -/
theorem consTuple_zero {T : Type*} {m : ℕ} (hm : 1 ≤ m) (t : T) (M' : Fin (m - 1) → T) :
    consTuple t M' ⟨0, hm⟩ = t := by
  simp [consTuple]

/-- A tuple `M ∈ T^m` is `(t_1, M')` with `M'` its tail (part (iv) of the proof in
`q_peeling_lemma.md`). -/
theorem consTuple_tailTuple {T : Type*} {m : ℕ} (hm : 1 ≤ m) (M : Fin m → T) :
    consTuple (M ⟨0, hm⟩) (tailTuple M) = M := by
  funext i
  unfold consTuple tailTuple
  split_ifs with h
  · congr 1; ext; simp [h]
  · congr 1; ext; simp; omega

/-- The first identity in part (iv) of the proof in `q_peeling_lemma.md`:
`|Z| = Σ_{M' ∈ T^{m−1}} |F(M')|`.
Used in part (iv) of the Lemma (peeling) of `q_peeling_lemma.md`. -/
theorem card_eq_sum_fiber {m : ℕ} (hm : 1 ≤ m) {T : Type*} [Fintype T] [DecidableEq T]
    (Z : Finset (Fin m → T)) :
    Z.card = ∑ M' : Fin (m - 1) → T, (fiber Z M').card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := tailTuple) (t := Finset.univ)
    (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))]
  refine Finset.sum_congr rfl fun M' _ => ?_
  refine Finset.card_bij' (fun M _ => M ⟨0, hm⟩) (fun t _ => consTuple t M') ?_ ?_ ?_ ?_
  · intro M hM
    rw [Finset.mem_filter] at hM
    simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← hM.2, consTuple_tailTuple]
    exact hM.1
  · intro t ht
    simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and] at ht
    exact Finset.mem_filter.2 ⟨ht, tailTuple_consTuple t M'⟩
  · intro M hM
    have h2 := (Finset.mem_filter.1 hM).2
    change consTuple (M ⟨0, hm⟩) M' = M
    rw [← h2, consTuple_tailTuple]
  · intro t _
    exact consTuple_zero hm t M'

/-- **Lemma (peeling), part (iv)** of `q_peeling_lemma.md`: for a finite set `T` with
`|T| = q − 1` and every `Z ⊆ T^m`, `|Z| = Σ_{i=0}^{q−2} |Z_{>i}|`.  Encoding: `T` is a finite
type with `Fintype.card T = q - 1`, `Z` is a finset of tuples `Fin m → T`, and the sum over
`i = 0, …, q−2` is over `Finset.range (q - 1)`.  The hypothesis `3 ≤ q` of the source is kept,
although the proof does not need it. -/
theorem card_eq_sum_Zgt (hq : 3 ≤ q) {m : ℕ} (hm : 1 ≤ m) {T : Type*} [Fintype T]
    [DecidableEq T] (hT : Fintype.card T = q - 1) (Z : Finset (Fin m → T)) :
    Z.card = ∑ i ∈ Finset.range (q - 1), (Zgt Z i).card := by
  rw [card_eq_sum_fiber hm]
  simp only [Zgt, Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun M' _ => ?_
  rw [← Finset.card_filter]
  have hc : (fiber Z M').card ≤ q - 1 := hT ▸ Finset.card_le_univ _
  have : (Finset.range (q - 1)).filter (fun i => i < (fiber Z M').card) =
      Finset.range (fiber Z M').card := by
    ext i; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [this, Finset.card_range]

end Peel

end

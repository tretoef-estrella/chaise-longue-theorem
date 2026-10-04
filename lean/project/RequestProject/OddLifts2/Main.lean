module

public import RequestProject.OddLifts2.LemmaQp
public import RequestProject.OddLifts2.Patterns
public import RequestProject.OddLifts2.Border

/-!
# Part T of `q_oddbox_lifts_2.md`: the lifts (T6), (T7), (T8)

Throughout, `F` is a field, `h` a natural number, `r = 2h + 1`, `q = 2h + 2`, the rings are
`C_n = Peel.C F (2*h+2) n`, `y_i = Tight.y F (2*h+2) i`; the level is `m = n + 1`, the new
variable is `y_0` of `C_{n+1}` and the old variables are the images under `Peel.incl F (2*h+2) n`.
`Λ` is an arbitrary set of shapes, `V_Λ = OddPatterns.VSAll F h (n+1) Λ`, the marked patterns `T`
are on `Finset.univ : Finset (Fin n)`, and the conclusions are memberships in the slices
`W_d(V_Λ) = Peel.W (m := n+1) _ V_Λ d`.

This file also contains the entry point of the formalization of `q_oddbox_lifts_2.md`:
* Part Q (`LemmaQ.lean`, `LemmaQp.lean`): Lemma Q (Q1), (Q2) and Lemma Q′ (Q′1), (Q′2);
* the patterns used in Part T (`Patterns.lean`) and the second term of (T7) (`Border.lean`);
* Part T (this file): (T6), (T7), (T8).
-/

@[expose] public section

open Polynomial

namespace OddLifts2

open Peel hiding C
open Tight ChainLemma OddShapes OddPatterns Lifts OddLifts

set_option synthInstance.maxHeartbeats 200000

variable {F : Type*} [Field F] {h : ℕ}

/-- Auxiliary for (T6)–(T8) of `q_oddbox_lifts_2.md`: (L2) of `q_oddbox_lifts_1.md` in the form
`T.prod = Pf_{E_ℓ}(B_0) · G'` with `G' = D_P · Π_{c=2}^{N} Δ(B_c)` (`N ≥ μ_1`). -/
theorem prod_eq_markedPf_mul {n : ℕ} {mu : Partition}
    (T : MarkedPattern mu (Finset.univ : Finset (Fin n))) {N : ℕ} (hN : mu.row 1 ≤ N) :
    T.prod F h = markedPf F h mu.len T.marked *
      ((∏ e ∈ T.pairs, pairD F (2 * h + 2) e) *
        ∏ c ∈ Finset.Icc 2 N, Delta F (2 * h + 2) (cleanMBlocks T c)) := by
  rw [prod_cleanMBlocks T hN]
  ring

/-- **(T6)** of `q_oddbox_lifts_2.md` (the zero option of a marked shape; case (Z), `δ = 1`): let
`(μ, 0) ∈ Λ`, `1 ≤ h`, `ℓ(μ) ≤ h`, and `T` a marked pattern of `μ` on all the indices of `C_n`.
Then `T.prod ∈ W_{2h−ℓ(μ)}(V_Λ)`. -/
theorem T6 {n : ℕ} {Lam : Set Shape} {mu : Partition} (hmu : (mu, false) ∈ Lam) (hh : 1 ≤ h)
    (hlen : mu.len ≤ h) (T : MarkedPattern mu (Finset.univ : Finset (Fin n))) :
    T.prod F h ∈ W (m := n + 1) (by omega) (VSAll F h (n + 1) Lam) (2 * h - mu.len) := by
  classical
  set N := mu.row 1 + mu.addOne.row 1 + 1 with hNdef
  set G' : Peel.C F (2 * h + 2) n := (∏ e ∈ T.pairs, pairD F (2 * h + 2) e) *
    ∏ c ∈ Finset.Icc 2 N, Delta F (2 * h + 2) (cleanMBlocks T c) with hG'
  have hG : T.prod F h = markedPf F h mu.len T.marked * G' :=
    prod_eq_markedPf_mul T (by omega)
  obtain ⟨I, hI⟩ := Peel.W_isIdeal (F := F) (q := 2 * h + 2) (by omega) (m := n + 1) (by omega)
    (VSAll F h (n + 1) Lam) (2 * h - mu.len) (by omega)
  have hWI : ∀ x : Peel.C F (2 * h + 2) n,
      x ∈ W (m := n + 1) (by omega) (VSAll F h (n + 1) Lam) (2 * h - mu.len) ↔ x ∈ I :=
    fun x => by rw [← SetLike.mem_coe, ← hI]; rfl
  have key : ∀ g ∈ Membership.UB (2 * h + 1) (mu.len + 1) (y F (2 * h + 2)) T.marked,
      g * G' ∈ I := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨S, Q, hS, hScard, hQ, hQs, rfl⟩ := hx
      obtain ⟨T', hT'⟩ := exists_tpattern_addOne (F := F) (h := h) T S Q hS hScard hQ hQs
        (N := N) (by omega) (by omega) (by omega)
      have hc1 : colLen mu.addOne 1 = mu.len + 1 := by
        rw [← colLen_addOne' mu le_rfl, OddPatterns.colLen_one, if_pos rfl]
      have hmem := OddLifts.T2 (F := F) (h := h) hmu T' (c0 := 1) le_rfl
        (fun c hc => colLen_addOne' mu hc) (by omega) (by omega)
      rw [hc1, show 2 * h + 1 - (mu.len + 1) = 2 * h - mu.len by omega] at hmem
      have hmem' := (hWI _).1 hmem
      rw [hT'] at hmem'
      have e : vand (y F (2 * h + 2)) S * Membership.DPy (2 * h + 1) (y F (2 * h + 2)) Q * G' =
          Delta F (2 * h + 2) S * (∏ e ∈ Q, pairD F (2 * h + 2) e) * G' := rfl
      rw [e]
      exact hmem'
    | zero => rw [zero_mul]; exact I.zero_mem
    | add x z _ _ hx hz => rw [add_mul]; exact I.add_mem hx hz
    | smul a x _ hx => rw [smul_eq_mul, mul_assoc]; exact I.mul_mem_left a hx
  obtain ⟨t, ht⟩ := T.marked_card
  have hmem := key _ (D3 hh mu.len T.marked t ht)
  rw [← hG] at hmem
  exact (hWI _).2 hmem

/-- Auxiliary for (T8) of `q_oddbox_lifts_2.md`: if the last row of `μ` is `1`, then
`μ − e_ℓ = μ.subE μ.len` has the columns `c ≥ 2` of `μ`. -/
lemma colLen_subE_len_of_two_le (mu : Partition) (hl : 1 ≤ mu.len) (hrow : mu.row mu.len = 1)
    {c : ℕ} (hc : 2 ≤ c) : colLen (mu.subE mu.len) c = colLen mu c := by
  have := Lifts.colLen_subE mu hl le_rfl (by omega : 1 ≤ c)
  rw [hrow, if_neg (by omega), add_zero] at this
  exact this

/-- Auxiliary for (T8) of `q_oddbox_lifts_2.md`: if the last row of `μ` is `1`, then
`ℓ(μ − e_ℓ) + 1 = ℓ(μ)`. -/
lemma len_subE_len (mu : Partition) (hl : 1 ≤ mu.len) (hrow : mu.row mu.len = 1) :
    (mu.subE mu.len).len + 1 = mu.len := by
  have := Lifts.colLen_subE mu hl le_rfl le_rfl
  rw [hrow, if_pos rfl, OddPatterns.colLen_one, OddPatterns.colLen_one] at this
  exact this

/-- **(T8)** of `q_oddbox_lifts_2.md` (the removal that empties the first column of a marked shape;
case (R), `δ = 1`, `μ_ρ = 1`): let `(μ − e_ℓ, 1) = (μ.subE μ.len, true) ∈ Λ`, `1 ≤ ℓ(μ) ≤ h`,
`μ_ℓ = 1`, and `T` a marked pattern of `μ` on all the indices of `C_n`.  Then
`T.prod ∈ W_{2h+1−ℓ(μ)}(V_Λ)`. -/
theorem T8 {n : ℕ} {Lam : Set Shape} {mu : Partition} (hlam : (mu.subE mu.len, true) ∈ Lam)
    (hl1 : 1 ≤ mu.len) (hlh : mu.len ≤ h) (hrow : mu.row mu.len = 1)
    (T : MarkedPattern mu (Finset.univ : Finset (Fin n))) :
    T.prod F h ∈ W (m := n + 1) (by omega) (VSAll F h (n + 1) Lam) (2 * h + 1 - mu.len) := by
  classical
  haveI := nontrivial_C (F := F) (q := 2 * h + 2) (m := n) (by omega)
  have hll : (mu.subE mu.len).len + 1 = mu.len := len_subE_len mu hl1 hrow
  set N := mu.row 1 + (mu.subE mu.len).row 1 + 1 with hNdef
  set G' : Peel.C F (2 * h + 2) n := (∏ e ∈ T.pairs, pairD F (2 * h + 2) e) *
    ∏ c ∈ Finset.Icc 2 N, Delta F (2 * h + 2) (cleanMBlocks T c) with hG'
  have hG : T.prod F h = markedPf F h mu.len T.marked * G' :=
    prod_eq_markedPf_mul T (by omega)
  obtain ⟨t, ht⟩ := T.marked_card
  set M := insert 0 (liftSet T.marked) with hMdef
  have hMcard : M.card = T.marked.card + 1 := by
    rw [hMdef, Finset.card_insert_of_notMem (zero_notMem_liftSet _), liftSet, Finset.card_map]
  obtain ⟨T', hT'⟩ := exists_mpattern_lift (F := F) (h := h) T
    (fun c hc => colLen_subE_len_of_two_le mu hl1 hrow hc) (N := N) (by omega) (by omega)
    ∅ M (by simp) (by simp) (by simp) (by simp [hMdef]) ⟨t + 1, by omega⟩
  rw [Finset.prod_empty, one_mul] at hT'
  have hf : T'.prod F h ∈ VSAll F h (n + 1) Lam := B4_marked hlam T'
  set w : Fin T.marked.card → Peel.C F (2 * h + 2) n := fun j => y F (2 * h + 2) (T.marked.orderEmbOfFin rfl j)
    with hw
  set Qp : (Peel.C F (2 * h + 2) n)[X] := mPf h (mu.subE mu.len).len
    (Fin.cons X (fun j => Polynomial.C (w j)) : Fin (T.marked.card + 1) → (Peel.C F (2 * h + 2) n)[X])
    with hQp
  set Pol : (Peel.C F (2 * h + 2) n)[X] := Polynomial.C G' * Qp with hPol
  have hphi : peelEquiv' F (2 * h + 2) n (T'.prod F h) = AdjoinRoot.mk _ Pol := by
    rw [hT', map_mul, phi_markedPf_insert_zero F h (mu.subE mu.len).len T.marked rfl, phi_incl, hPol,
      map_mul (AdjoinRoot.mk _), AdjoinRoot.mk_C]
    exact mul_comm _ _
  have hcoeffP : ∀ k, Pol.coeff k = G' * Qp.coeff k := fun k => coeff_C_mul _
  have hn : T.marked.card = (mu.subE mu.len).len + 2 + 2 * t := by omega
  have hvan : ∀ k, 2 * h - (mu.subE mu.len).len < k → Pol.coeff k = 0 := by
    intro k hk
    rw [hcoeffP, hQp, Q1 h (mu.subE mu.len).len T.marked.card t hn (by omega) w k hk, mul_zero]
  have hmem := coeff_mem_W (by omega) _ hf Pol hphi (d := 2 * h - (mu.subE mu.len).len) (by omega) hvan
  rw [hcoeffP, hQp, Q2 h (mu.subE mu.len).len T.marked.card t hn (by omega) w, hll,
    show 2 * h - (mu.subE mu.len).len = 2 * h + 1 - mu.len by omega] at hmem
  have e : G' * ((-1) ^ (mu.subE mu.len).len * mPf h mu.len w) = (-1) ^ (mu.subE mu.len).len * T.prod F h := by
    rw [hG]
    change G' * ((-1) ^ (mu.subE mu.len).len * markedPf F h mu.len T.marked) = _
    ring
  rw [e] at hmem
  exact mem_of_neg_one_pow_mul_mem _ hmem

/-- **(T7)** of `q_oddbox_lifts_2.md` (the middle option of a marked shape; case (M), `δ = 1`): let
`(μ ⊔ 1, 1) = (μ.addOne, true) ∈ Λ`, `(μ, 0) ∈ Λ`, `ℓ(μ) < h`, and `T` a marked pattern of `μ` on
all the indices of `C_n`.  Then `T.prod ∈ W_{ℓ(μ)}(V_Λ)`. -/
theorem T7 {n : ℕ} {Lam : Set Shape} {mu : Partition} (hlam : (mu.addOne, true) ∈ Lam)
    (hmu : (mu, false) ∈ Lam) (hlen : mu.len < h)
    (T : MarkedPattern mu (Finset.univ : Finset (Fin n))) :
    T.prod F h ∈ W (m := n + 1) (by omega) (VSAll F h (n + 1) Lam) mu.len := by
  classical
  haveI := nontrivial_C (F := F) (q := 2 * h + 2) (m := n) (by omega)
  have hlenA : mu.addOne.len = mu.len + 1 := Lifts.len_addOne mu
  have hcolA : ∀ c, 2 ≤ c → colLen mu.addOne c = colLen mu c := fun c hc => by
    rw [Lifts.colLen_addOne mu (by omega), if_neg (by omega), add_zero]
  set N := mu.row 1 + mu.addOne.row 1 + 1 with hNdef
  set G' : Peel.C F (2 * h + 2) n := (∏ e ∈ T.pairs, pairD F (2 * h + 2) e) *
    ∏ c ∈ Finset.Icc 2 N, Delta F (2 * h + 2) (cleanMBlocks T c) with hG'
  have hG : T.prod F h = markedPf F h mu.len T.marked * G' :=
    prod_eq_markedPf_mul T (by omega)
  obtain ⟨t, ht⟩ := T.marked_card
  set M := insert 0 (liftSet T.marked) with hMdef
  have hMcard : M.card = T.marked.card + 1 := by
    rw [hMdef, Finset.card_insert_of_notMem (zero_notMem_liftSet _), liftSet, Finset.card_map]
  obtain ⟨T1, hT1⟩ := exists_mpattern_lift (F := F) (h := h) T hcolA (N := N) (by omega)
    (by omega) ∅ M (by simp) (by simp) (by simp) (by simp [hMdef]) ⟨t, by omega⟩
  rw [Finset.prod_empty, one_mul, hlenA] at hT1
  -- the terms of the expansion of the border `D(y_0, ·)` lie in `V_Λ`
  have hyp : ∀ x ∈ T.marked, D F (2 * h + 2) 0 x.succ *
      incl F (2 * h + 2) n (markedPf F h (mu.len + 1) (T.marked.erase x) * G') ∈
        VSAll F h (n + 1) Lam := by
    intro x hx
    have hcardE : (T.marked.erase x).card = mu.len + 2 * t := by
      rw [Finset.card_erase_of_mem hx]; omega
    have hne : (0 : Fin (n + 1)) ≠ x.succ := (Fin.succ_ne_zero x).symm
    have hpair : ∀ e ∈ ({{0, x.succ}} : Finset (Finset (Fin (n + 1)))), e.card = 2 := by
      intro e he
      rw [Finset.mem_singleton] at he
      rw [he]
      exact Finset.card_pair hne
    have hpd : (({{0, x.succ}} : Finset (Finset (Fin (n + 1)))) :
        Set (Finset (Fin (n + 1)))).PairwiseDisjoint id := by
      rw [Finset.coe_singleton]
      exact Set.pairwiseDisjoint_singleton _ _
    have hdisj : ∀ e ∈ ({{0, x.succ}} : Finset (Finset (Fin (n + 1)))),
        Disjoint e (liftSet (T.marked.erase x)) := by
      intro e he
      rw [Finset.mem_singleton] at he
      rw [he, Finset.disjoint_insert_left, Finset.disjoint_singleton_left]
      refine ⟨zero_notMem_liftSet _, fun h' => ?_⟩
      rw [succ_mem_liftSet] at h'
      simp at h'
    have hcov : ({{0, x.succ}} : Finset (Finset (Fin (n + 1)))).sup id ∪
        liftSet (T.marked.erase x) = insert 0 (liftSet T.marked) := by
      rw [Finset.sup_singleton, id]
      ext z
      refine Fin.cases ?_ (fun i => ?_) z
      · simp [zero_notMem_liftSet]
      · simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, succ_mem_liftSet,
          Finset.mem_erase, Fin.succ_ne_zero, false_or, Fin.succ_inj]
        constructor
        · rintro (rfl | ⟨_, h'⟩)
          · exact hx
          · exact h'
        · intro h'
          by_cases hix : i = x
          · exact Or.inl hix
          · exact Or.inr ⟨hix, h'⟩
    have hcardL : (liftSet (T.marked.erase x)).card = mu.len + 2 * t := by
      rw [liftSet, Finset.card_map, hcardE]
    rcases Nat.eq_zero_or_pos t with ht0 | ht1
    · -- `t = 0`: by (C5) the summand is `±` the product of a tight pattern of `μ`
      obtain ⟨T2, hT2⟩ := exists_tpattern_lift (F := F) (h := h) T (N := N) (by omega) (by omega)
        {{0, x.succ}} (liftSet (T.marked.erase x)) hpair hpd hdisj hcov (by omega)
      have hmem : T2.prod F (2 * h + 2) ∈ VSAll F h (n + 1) Lam := B4_tight hmu T2
      rw [hT2, Finset.prod_singleton] at hmem
      rw [markedPf_eq_Delta F h mu.len _ (by omega)]
      have e : D F (2 * h + 2) 0 x.succ * incl F (2 * h + 2) n
          ((-1) ^ (mu.len * (mu.len - 1) / 2) * Delta F (2 * h + 2) (T.marked.erase x) * G') =
          (-1) ^ (mu.len * (mu.len - 1) / 2) * (pairD F (2 * h + 2) {0, x.succ} *
            Delta F (2 * h + 2) (liftSet (T.marked.erase x)) * incl F (2 * h + 2) n G') := by
        rw [map_mul, map_mul, map_pow, map_neg, map_one, incl_Delta, pairD_of_lt (Fin.succ_pos x)]
        ring
      rw [e]
      exact Ideal.mul_mem_left _ _ hmem
    · -- `t ≥ 1`: the summand is the product of a marked pattern of `μ ⊔ 1`
      obtain ⟨T2, hT2⟩ := exists_mpattern_lift (F := F) (h := h) T hcolA (N := N) (by omega)
        (by omega) {{0, x.succ}} (liftSet (T.marked.erase x)) hpair hpd hdisj hcov
        ⟨t - 1, by omega⟩
      have hmem : T2.prod F h ∈ VSAll F h (n + 1) Lam := B4_marked hlam T2
      rw [hT2, Finset.prod_singleton, hlenA] at hmem
      have e : D F (2 * h + 2) 0 x.succ *
          incl F (2 * h + 2) n (markedPf F h (mu.len + 1) (T.marked.erase x) * G') =
          pairD F (2 * h + 2) {0, x.succ} *
            markedPf F h (mu.len + 1) (liftSet (T.marked.erase x)) * incl F (2 * h + 2) n G' := by
        rw [map_mul, L1, pairD_of_lt (Fin.succ_pos x)]
        ring
      rw [e]
      exact hmem
  have hPsi := Psi_mem F h mu.len T.marked rfl (by omega) (VSAll F h (n + 1) Lam) G' hyp
  set f : Peel.C F (2 * h + 2) (n + 1) := (y F (2 * h + 2) 0 * markedPf F h (mu.len + 1) M +
    Psi F h mu.len T.marked rfl) * incl F (2 * h + 2) n G' with hfdef
  have hf : f ∈ VSAll F h (n + 1) Lam := by
    rw [hfdef, add_mul, mul_assoc]
    refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ ?_) hPsi
    rw [← hT1]
    exact B4_marked hlam T1
  set w : Fin T.marked.card → Peel.C F (2 * h + 2) n :=
    fun j => y F (2 * h + 2) (T.marked.orderEmbOfFin rfl j) with hw
  set Pol : (Peel.C F (2 * h + 2) n)[X] := Phi h mu.len w * Polynomial.C G' with hPol
  have hphi : peelEquiv' F (2 * h + 2) n f = AdjoinRoot.mk _ Pol := by
    rw [hfdef, hPol, Phi, map_mul (peelEquiv' F (2 * h + 2) n), map_add, map_mul, phi_y0,
      phi_markedPf_insert_zero F h (mu.len + 1) T.marked rfl, phi_Psi, phi_incl]
    simp only [map_mul, map_add, AdjoinRoot.mk_X, AdjoinRoot.mk_C]
    rfl
  have hn : T.marked.card = mu.len + 1 + 2 * t := ht
  have hvan : ∀ k, mu.len < k → Pol.coeff k = 0 := by
    intro k hk
    rw [hPol, coeff_mul_C, Q'1 h mu.len _ t hn w k hk, zero_mul]
  have hmem := coeff_mem_W (by omega) _ hf Pol hphi (d := mu.len) (by omega) hvan
  rw [hPol, coeff_mul_C, Q'2 h mu.len _ t hn w] at hmem
  rw [hG]
  exact hmem

end OddLifts2

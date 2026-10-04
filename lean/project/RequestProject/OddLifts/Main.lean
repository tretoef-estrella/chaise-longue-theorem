module

public import RequestProject.OddLifts.Marked

/-!
# Part T of `q_oddbox_lifts_1.md`: the lifts (T1)–(T5)

Throughout, `F` is a field, `h` a natural number, `r = 2h + 1`, `q = 2h + 2`, the rings are
`C_n = Peel.C F (2*h+2) n`, `y_i = Tight.y F (2*h+2) i`; the level is `m = n + 1`, the new
variable is `y_0` of `C_{n+1}` and the old variables are the images under `Peel.incl F (2*h+2) n`.
`Λ` is an arbitrary set of shapes, `V_Λ = OddPatterns.VSAll F h (n+1) Λ`, the patterns `T` are on
`Finset.univ : Finset (Fin n)`, and the conclusions are memberships in the slices
`W_d(V_Λ) = Peel.W (m := n+1) _ V_Λ d`.

This file also contains the entry point of the formalization of `q_oddbox_lifts_1.md`:
* Part P (`LemmaP.lean`): Lemma P (P1)–(P3);
* Part L (`Aux.lean`, `Marked.lean`): (L0a), (L0b), (L1), (L2);
* Part T (this file): (T1)–(T5).
-/

@[expose] public section

open Polynomial

namespace OddLifts

open Peel hiding C
open Tight ChainLemma OddShapes OddPatterns Lifts

set_option synthInstance.maxHeartbeats 200000

variable {F : Type*} [Field F] {h : ℕ}

/-- **(T1)** of `q_oddbox_lifts_1.md` (insertion into a column, unmarked): let `(λ, 0) ∈ Λ`, `T` a
tight pattern of `μ` on all the indices of `C_n`, `c* ≥ 1`, with `λ'_c = μ'_c + [c = c*]` for every
`c ≥ 1` and `μ'_{c*} ≤ 2h`.  Then `T.prod ∈ W_{μ'_{c*}}(V_Λ)`. -/
theorem T1 {n : ℕ} {Lam : Set Shape} {mu lam : Partition} (hlam : (lam, false) ∈ Lam)
    (T : TightPattern mu (Finset.univ : Finset (Fin n))) {cs : ℕ} (hcs : 1 ≤ cs)
    (hcol : ∀ c, 1 ≤ c → colLen lam c = colLen mu c + if c = cs then 1 else 0)
    (hd : colLen mu cs ≤ 2 * h) :
    T.prod F (2 * h + 2) ∈
      W (m := n + 1) (by omega) (VSAll F h (n + 1) Lam) (colLen mu cs) :=
  L0a _ (L0b h (n + 1) Lam) _
    (mem_W_of_insert (F := F) (q := 2 * h + 2) (by omega) (Λ := comp Lam false) hlam T hcs hcol
      (by omega))

/-- **(T2)** of `q_oddbox_lifts_1.md` (removal from a column, unmarked): let `(λ, 0) ∈ Λ`, `T` a
tight pattern of `μ` on all the indices of `C_n`, `c_0 ≥ 1`, with `λ'_c + [c = c_0] = μ'_c` for
every `c ≥ 1` and `1 ≤ μ'_{c_0} ≤ 2h + 1`.  Then `T.prod ∈ W_{2h+1−μ'_{c_0}}(V_Λ)`. -/
theorem T2 {n : ℕ} {Lam : Set Shape} {mu lam : Partition} (hlam : (lam, false) ∈ Lam)
    (T : TightPattern mu (Finset.univ : Finset (Fin n))) {c0 : ℕ} (hc0 : 1 ≤ c0)
    (hcol : ∀ c, 1 ≤ c → colLen lam c + (if c = c0 then 1 else 0) = colLen mu c)
    (hr : 1 ≤ colLen mu c0) (hrq : colLen mu c0 ≤ 2 * h + 1) :
    T.prod F (2 * h + 2) ∈
      W (m := n + 1) (by omega) (VSAll F h (n + 1) Lam) (2 * h + 1 - colLen mu c0) := by
  have := mem_W_of_pair (F := F) (q := 2 * h + 2) (by omega) (Λ := comp Lam false) hlam T hc0
    hcol hr (by omega)
  rw [show 2 * h + 2 - 1 - colLen mu c0 = 2 * h + 1 - colLen mu c0 by omega] at this
  exact L0a _ (L0b h (n + 1) Lam) _ this

/-- **(T3)** of `q_oddbox_lifts_1.md` (insertion into a column `c* ≥ 2`, marked): let
`(λ, 1) ∈ Λ`, `T` a marked pattern of `μ` on all the indices of `C_n`, `c* ≥ 2`, with
`λ'_c = μ'_c + [c = c*]` for every `c ≥ 1` and `μ'_{c*} ≤ 2h`.  Then
`T.prod ∈ W_{μ'_{c*}}(V_Λ)`. -/
theorem T3 {n : ℕ} {Lam : Set Shape} {mu lam : Partition} (hlam : (lam, true) ∈ Lam)
    (T : MarkedPattern mu (Finset.univ : Finset (Fin n))) {cs : ℕ} (hcs : 2 ≤ cs)
    (hcol : ∀ c, 1 ≤ c → colLen lam c = colLen mu c + if c = cs then 1 else 0)
    (hd : colLen mu cs ≤ 2 * h) :
    T.prod F h ∈ W (m := n + 1) (by omega) (VSAll F h (n + 1) Lam) (colLen mu cs) := by
  haveI := nontrivial_C (F := F) (q := 2 * h + 2) (m := n) (by omega)
  obtain ⟨T', hT'⟩ := exists_mpattern_insert (F := F) (h := h) T hcs hcol
  have hf : T'.prod F h ∈ VSAll F h (n + 1) Lam := B4_marked hlam T'
  set B := cleanMBlocks T cs with hBdef
  have hcard : B.card = colLen mu cs := card_cleanMBlocks T hcs
  set Pol : (Peel.C F (2 * h + 2) n)[X] :=
    Polynomial.C (T.prod F h) * ∏ x ∈ B, (Polynomial.C (y F (2 * h + 2) x) - X) with hPol
  have hphi : peelEquiv' F (2 * h + 2) n (T'.prod F h) = AdjoinRoot.mk _ Pol := by
    have hs : ∀ x : Fin n, y F (2 * h + 2) x.succ = incl F (2 * h + 2) n (y F (2 * h + 2) x) :=
      fun x => (incl_y x).symm
    rw [hT', map_mul, map_prod, phi_incl, hPol, map_mul, map_prod]
    simp only [map_sub, hs, phi_incl, phi_y0, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
    ring
  obtain ⟨h1, h2⟩ := coeff_C_mul_prod B (fun x => y F (2 * h + 2) x) (T.prod F h)
  have hmem := coeff_mem_W (by omega) _ hf Pol hphi (d := B.card) (by omega) h1
  rw [h2, hcard] at hmem
  exact mem_of_neg_one_pow_mul_mem _ hmem

/-- **(T4)** of `q_oddbox_lifts_1.md` (removal from a column `c_0 ≥ 2`, marked): let
`(λ, 1) ∈ Λ`, `T` a marked pattern of `μ` on all the indices of `C_n`, `c_0 ≥ 2`, with
`λ'_c + [c = c_0] = μ'_c` for every `c ≥ 1` and `1 ≤ μ'_{c_0} ≤ 2h + 1`.  Then
`T.prod ∈ W_{2h+1−μ'_{c_0}}(V_Λ)`. -/
theorem T4 {n : ℕ} {Lam : Set Shape} {mu lam : Partition} (hlam : (lam, true) ∈ Lam)
    (T : MarkedPattern mu (Finset.univ : Finset (Fin n))) {c0 : ℕ} (hc0 : 2 ≤ c0)
    (hcol : ∀ c, 1 ≤ c → colLen lam c + (if c = c0 then 1 else 0) = colLen mu c)
    (hr : 1 ≤ colLen mu c0) (hrq : colLen mu c0 ≤ 2 * h + 1) :
    T.prod F h ∈
      W (m := n + 1) (by omega) (VSAll F h (n + 1) Lam) (2 * h + 1 - colLen mu c0) := by
  classical
  set q := 2 * h + 2 with hq
  set S := cleanMBlocks T c0 with hSdef
  have hcard : S.card = colLen mu c0 := card_cleanMBlocks T hc0
  set N := lam.row 1 + mu.row 1 + c0 with hNdef
  set G' : Peel.C F q n := (∏ e ∈ T.pairs, pairD F q e) * markedPf F h mu.len T.marked *
    ∏ c ∈ (Finset.Icc 2 N).erase c0, Delta F q (cleanMBlocks T c) with hG'
  have hG : T.prod F h = Delta F q S * G' := by
    rw [prod_cleanMBlocks T (N := N) (by omega),
      ← Finset.mul_prod_erase _ _ (Finset.mem_Icc.2 ⟨hc0, (by omega : c0 ≤ N)⟩), hG']
    ring
  have hex : ∀ b ∈ S, ∃ T' : MarkedPattern lam (Finset.univ : Finset (Fin (n + 1))),
      T'.prod F h = D F q 0 b.succ * incl F q n (Delta F q (S.erase b) * G') :=
    fun b hb => exists_mpattern_pair (F := F) (h := h) T hc0 hcol (N := N) (by omega) (by omega)
      (by omega) hb
  choose Tb hTb using hex
  set eps : Fin n → Peel.C F q n := fun b => (-1) ^ (S.card + ((S.filter (· < b)).card + 1))
    with heps
  set f : Peel.C F q (n + 1) :=
    ∑ b ∈ S.attach, incl F q n (eps b.1) * (Tb b.1 b.2).prod F h with hfdef
  have hf : f ∈ VSAll F h (n + 1) Lam :=
    Ideal.sum_mem _ (fun b _ => Ideal.mul_mem_left _ _ (B4_marked hlam _))
  set Pol : (Peel.C F q n)[X] :=
    ∑ b ∈ S.attach, Polynomial.C (eps b.1 * Delta F q (S.erase b.1) * G') * dpoly q (y F q b.1)
    with hPol
  have hphi : peelEquiv' F q n f = AdjoinRoot.mk _ Pol := by
    rw [hfdef, hPol, map_sum, map_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [hTb, map_mul, map_mul, phi_incl, phi_incl, phi_D]
    simp only [map_mul, AdjoinRoot.mk_C]
    ring
  have hcoeff : ∀ k, Pol.coeff k = if k < q - 1 then
      (-1) ^ k * G' * ∑ b ∈ S, eps b * Delta F q (S.erase b) * y F q b ^ (q - 2 - k) else 0 := by
    intro k
    rw [hPol, finset_sum_coeff]
    simp only [coeff_C_mul, coeff_dpoly]
    split_ifs with hk
    · rw [Finset.sum_attach S (fun b => eps b * Delta F q (S.erase b) * G' *
        ((-1) ^ k * y F q b ^ (q - 2 - k))), Finset.mul_sum]
      exact Finset.sum_congr rfl (fun b _ => by ring)
    · simp
  obtain ⟨hz, htop⟩ := sum_eps_Delta (F := F) (q := q) S (by omega)
  have hvan : ∀ k, q - 1 - colLen mu c0 < k → Pol.coeff k = 0 := by
    intro k hk
    rw [hcoeff k]
    split_ifs with hk'
    · rw [hz (q - 2 - k) (by omega), mul_zero]
    · rfl
  have hmem := coeff_mem_W (by omega) _ hf Pol hphi (d := q - 1 - colLen mu c0) (by omega) hvan
  rw [hcoeff, if_pos (by omega), show q - 2 - (q - 1 - colLen mu c0) = S.card - 1 by omega, htop,
    mul_assoc, mul_comm G', ← hG, show q - 1 - colLen mu c0 = 2 * h + 1 - colLen mu c0 by omega]
    at hmem
  exact mem_of_neg_one_pow_mul_mem _ hmem

/-- Auxiliary for (T5) of `q_oddbox_lifts_1.md`: the marked pattern `T'` of `μ` on `Fin (n+1)` built
from a tight pattern `T` of `μ` on `Fin n`: pairs `liftPairs T.pairs`, blocks `B_c^+` (`c ≥ 2`),
marked block `B_1^+ ∪ {0}` (of size `ℓ(μ) + 1`).  Its product is
`Pf_{E_ℓ}(B_1^+ ∪ {0}) · incl(G')` with `G' = D_P · Π_{c=2}^{N} Δ(B_c)`, `N = μ_1 + 1`. -/
theorem exists_mpattern_zero {n : ℕ} {mu : Partition}
    (T : TightPattern mu (Finset.univ : Finset (Fin n))) :
    ∃ T' : MarkedPattern mu (Finset.univ : Finset (Fin (n + 1))),
      T'.prod F h = markedPf F h mu.len (insert 0 (liftSet (cleanBlocks T 1))) *
        incl F (2 * h + 2) n ((∏ e ∈ T.pairs, pairD F (2 * h + 2) e) *
          ∏ c ∈ Finset.Icc 2 (mu.row 1 + 1), Delta F (2 * h + 2) (cleanBlocks T c)) := by
  classical
  set N := mu.row 1 + 1 with hNdef
  set P := liftPairs T.pairs with hPdef
  set M := insert 0 (liftSet (cleanBlocks T 1)) with hMdef
  set B : ℕ → Finset (Fin (n + 1)) := fun c => liftSet (cleanBlocks T c) with hBdef
  have hB : ∀ c, 2 ≤ c → (B c).card = colLen mu c := by
    intro c hc
    simp only [hBdef, liftSet, Finset.card_map, card_cleanBlocks T (by omega : 1 ≤ c)]
  have hBd : ∀ c, 2 ≤ c → ∀ c', 2 ≤ c' → c ≠ c' → Disjoint (B c) (B c') := fun c _ c' _ hne =>
    (Finset.disjoint_map _).2 (disjoint_cleanBlocks T hne)
  have hPB : ∀ e ∈ P, ∀ c, 2 ≤ c → Disjoint e (B c) := by
    intro e he c _
    obtain ⟨e', he', rfl⟩ := mem_liftPairs.1 he
    exact (Finset.disjoint_map _).2 (disjoint_pairs_cleanBlocks T he' c)
  have hPM : ∀ e ∈ P, Disjoint e M := by
    intro e he
    obtain ⟨e', he', rfl⟩ := mem_liftPairs.1 he
    exact Finset.disjoint_insert_right.2 ⟨zero_notMem_liftSet _,
      (Finset.disjoint_map _).2 (disjoint_pairs_cleanBlocks T he' 1)⟩
  have hBM : ∀ c, 2 ≤ c → Disjoint (B c) M := by
    intro c hc
    exact Finset.disjoint_insert_right.2 ⟨zero_notMem_liftSet _,
      (Finset.disjoint_map _).2 (disjoint_cleanBlocks T (by omega))⟩
  have hMc : ∃ t, M.card = mu.len + 1 + 2 * t := by
    refine ⟨0, ?_⟩
    rw [hMdef, Finset.card_insert_of_notMem (zero_notMem_liftSet _), liftSet, Finset.card_map,
      card_cleanBlocks T le_rfl, OddPatterns.colLen_one]
  have hcov : P.sup id ∪ (Finset.Icc 2 N).sup B ∪ M = Finset.univ := by
    refine Finset.eq_univ_of_forall (fun x => ?_)
    refine Fin.cases (Finset.mem_union_right _ (Finset.mem_insert_self _ _)) (fun i => ?_) x
    rcases succ_mem_cover T (N := N) (by omega) i with ⟨e, he, hie⟩ | ⟨c, hc, hic⟩
    · refine Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_sup.2 ⟨liftSet e, ?_, ?_⟩))
      · exact mem_liftPairs.2 ⟨e, he, rfl⟩
      · exact succ_mem_liftSet.2 hie
    · rw [Finset.mem_Icc] at hc
      by_cases h1 : c = 1
      · subst h1
        exact Finset.mem_union_right _ (Finset.mem_insert_of_mem (succ_mem_liftSet.2 hic))
      · refine Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_sup.2 ⟨c, Finset.mem_Icc.2 ⟨by omega, hc.2⟩, ?_⟩))
        exact succ_mem_liftSet.2 hic
  refine ⟨mkMPattern mu _ P B M N (by omega) (card_liftPairs T) (disjoint_liftPairs T) hB hBd hPB
    hPM hBM hMc hcov, ?_⟩
  rw [prod_mkMPattern, hPdef, prod_liftPairs T, map_mul, map_prod]
  have e2 : ∏ c ∈ Finset.Icc 2 N, Delta F (2 * h + 2) (B c) =
      ∏ c ∈ Finset.Icc 2 N, incl F (2 * h + 2) n (Delta F (2 * h + 2) (cleanBlocks T c)) :=
    Finset.prod_congr rfl (fun c _ => (incl_Delta _).symm)
  rw [e2, map_prod]
  ring

/-- Auxiliary for (T5) of `q_oddbox_lifts_1.md`: `T.prod = Δ(B_1) · G'` with
`G' = D_P · Π_{c=2}^{N} Δ(B_c)`, `N = μ_1 + 1`. -/
theorem prod_eq_Delta_one_mul {n : ℕ} {mu : Partition}
    (T : TightPattern mu (Finset.univ : Finset (Fin n))) :
    T.prod F (2 * h + 2) = Delta F (2 * h + 2) (cleanBlocks T 1) *
      ((∏ e ∈ T.pairs, pairD F (2 * h + 2) e) *
        ∏ c ∈ Finset.Icc 2 (mu.row 1 + 1), Delta F (2 * h + 2) (cleanBlocks T c)) := by
  rw [prod_cleanBlocks T (N := mu.row 1 + 1) (by omega),
    ← Finset.mul_prod_erase _ _ (Finset.mem_Icc.2 ⟨le_rfl, (by omega : 1 ≤ mu.row 1 + 1)⟩)]
  have : (Finset.Icc 1 (mu.row 1 + 1)).erase 1 = Finset.Icc 2 (mu.row 1 + 1) := by
    ext c; simp only [Finset.mem_erase, Finset.mem_Icc]; omega
  rw [this]
  ring

/-- Auxiliary for (T5) of `q_oddbox_lifts_1.md` ((P0) of the file, i.e. (A1)): for `ℓ = 0`,
`mPf_0(X) = X^{2h}`. -/
theorem mPf_cons_of_eq_zero {R : Type*} [CommRing R] (h l : ℕ) (hl : l = 0) (w : Fin l → R) :
    mPf h l (Fin.cons X (fun j => Polynomial.C (w j)) : Fin (l + 1) → R[X]) = X ^ (2 * h) := by
  subst hl
  rw [OddPatterns.A1]
  rfl

/-- **(T5)** of `q_oddbox_lifts_1.md` (the zero option of an unmarked shape): let `(μ, 1) ∈ Λ`,
`T` a tight pattern of `μ` on all the indices of `C_n`, and `ℓ(μ) ≤ h`.  Then
`T.prod ∈ W_{2h−ℓ(μ)}(V_Λ)`. -/
theorem T5 {n : ℕ} {Lam : Set Shape} {mu : Partition} (hmu : (mu, true) ∈ Lam)
    (T : TightPattern mu (Finset.univ : Finset (Fin n))) (hlen : mu.len ≤ h) :
    T.prod F (2 * h + 2) ∈
      W (m := n + 1) (by omega) (VSAll F h (n + 1) Lam) (2 * h - mu.len) := by
  set l := mu.len with hl
  set B1 := cleanBlocks T 1 with hB1def
  have hB1 : B1.card = l := by rw [hB1def, card_cleanBlocks T le_rfl, OddPatterns.colLen_one]
  set G' : Peel.C F (2 * h + 2) n := (∏ e ∈ T.pairs, pairD F (2 * h + 2) e) *
    ∏ c ∈ Finset.Icc 2 (mu.row 1 + 1), Delta F (2 * h + 2) (cleanBlocks T c) with hG'
  have hG : T.prod F (2 * h + 2) = Delta F (2 * h + 2) B1 * G' := prod_eq_Delta_one_mul T
  obtain ⟨T', hT'⟩ := exists_mpattern_zero (F := F) (h := h) T
  have hf : T'.prod F h ∈ VSAll F h (n + 1) Lam := B4_marked hmu T'
  set w : Fin l → Peel.C F (2 * h + 2) n := fun j => y F (2 * h + 2) (B1.orderEmbOfFin hB1 j)
    with hw
  set Q : (Peel.C F (2 * h + 2) n)[X] :=
    mPf h l (Fin.cons X (fun j => Polynomial.C (w j)) : Fin (l + 1) → (Peel.C F (2 * h + 2) n)[X])
    with hQ
  set Pol : (Peel.C F (2 * h + 2) n)[X] := Polynomial.C G' * Q with hPol
  have hphi : peelEquiv' F (2 * h + 2) n (T'.prod F h) = AdjoinRoot.mk _ Pol := by
    rw [hT', ← hG', map_mul, phi_markedPf_insert_zero F h l B1 hB1, phi_incl, hPol,
      map_mul (AdjoinRoot.mk _), AdjoinRoot.mk_C]
    exact mul_comm _ _
  have hcoeffP : ∀ k, Pol.coeff k = G' * Q.coeff k := fun k => coeff_C_mul _
  rcases Nat.eq_zero_or_pos l with hl0 | hl1
  · -- `ℓ(μ) = 0`: the marked block is `{0}` and `mPf_0(X) = X^{2h}` (A1)
    have hQ0 : Q = X ^ (2 * h) := by
      rw [hQ]
      exact mPf_cons_of_eq_zero h l hl0 w
    have hvan : ∀ k, 2 * h - l < k → Pol.coeff k = 0 := by
      intro k hk
      rw [hcoeffP, hQ0, coeff_X_pow, if_neg (by omega), mul_zero]
    have hmem := coeff_mem_W (by omega) _ hf Pol hphi (d := 2 * h - l) (by omega) hvan
    rw [hcoeffP, hQ0, coeff_X_pow, if_pos (by omega), mul_one] at hmem
    have hB10 : B1 = ∅ := Finset.card_eq_zero.1 (hB1.trans hl0)
    rw [hG, hB10, Delta_empty, one_mul]
    exact hmem
  · -- `ℓ(μ) ≥ 1`: Lemma P
    have hvan : ∀ k, 2 * h - l < k → Pol.coeff k = 0 := by
      intro k hk
      rw [hcoeffP, hQ, P3 h l hl1 w hlen k hk, mul_zero]
    have hmem := coeff_mem_W (by omega) _ hf Pol hphi (d := 2 * h - l) (by omega) hvan
    rw [hcoeffP, hQ, P2 h l hl1 w hlen] at hmem
    have hV : Delta F (2 * h + 2) B1 =
        ∏ i : Fin l, ∏ j ∈ Finset.Ioi i, (w j - w i) := Membership.V2 _ B1 hB1
    rw [← hV, mul_left_comm, mul_comm G', ← hG] at hmem
    exact mem_of_neg_one_pow_mul_mem _ hmem

end OddLifts

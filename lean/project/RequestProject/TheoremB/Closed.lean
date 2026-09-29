module

public import RequestProject.TheoremB.Count

/-!
# Part (ii) of the Theorem of `q_theorem_B_lower.md`: counting closed tuples
-/

@[expose] public section

namespace TheoremB

open ChainLemma Fibres Tight Lifts

/-- Proof of part (ii) of `q_theorem_B_lower.md` (auxiliary, "a multinomial coefficient"): the
number of tuples `M ∈ α^n` with prescribed counts `#{M_i = a} = c_a` (where `Σ_a c_a = n`),
multiplied by `Π_a c_a!`, is `n!`. -/
lemma card_cnt_eq_mul_prod {α : Type*} [Fintype α] [DecidableEq α] :
    ∀ (n : ℕ) (c : α → ℕ), ∑ a, c a = n →
      (Finset.univ.filter fun M : Fin n → α => ∀ a, cnt M a = c a).card *
        ∏ a, (c a).factorial = n.factorial
  | 0, c, hc => by
    have hc0 : ∀ a, c a = 0 := fun a => by
      have := Finset.single_le_sum (f := c) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
      omega
    have : (Finset.univ.filter fun M : Fin 0 → α => ∀ a, cnt M a = c a) = Finset.univ := by
      ext M; simp [cnt, hc0]
    rw [this]
    simp [hc0]
  | n + 1, c, hc => by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun M => M 0) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _), Finset.sum_mul]
    have step : ∀ a, ((Finset.univ.filter fun M : Fin (n + 1) → α => ∀ b, cnt M b = c b).filter
        fun M => M 0 = a).card * ∏ b, (c b).factorial = n.factorial * c a := by
      intro a
      rcases Nat.eq_zero_or_pos (c a) with h0 | hpos
      · have : ((Finset.univ.filter fun M : Fin (n + 1) → α => ∀ b, cnt M b = c b).filter
            fun M => M 0 = a) = ∅ := by
          ext M
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
            iff_false, not_and]
          intro hM hM0
          have h1 := hM a
          rw [← Fin.cons_self_tail M, cnt_cons, hM0, if_pos rfl, h0] at h1
          omega
        simp [this, h0]
      obtain ⟨c', hc'⟩ : ∃ c', c' = Function.update c a (c a - 1) := ⟨_, rfl⟩
      have hsum : ∑ b, c' b = n := by
        have h1 := Finset.add_sum_erase Finset.univ c (Finset.mem_univ a)
        have h2 := Finset.add_sum_erase Finset.univ c' (Finset.mem_univ a)
        have h3 : ∑ b ∈ Finset.univ.erase a, c' b = ∑ b ∈ Finset.univ.erase a, c b :=
          Finset.sum_congr rfl fun b hb => by
            rw [hc', Function.update_of_ne (Finset.ne_of_mem_erase hb)]
        have h4 : c' a = c a - 1 := by rw [hc', Function.update_self]
        omega
      have ih := card_cnt_eq_mul_prod n c' hsum
      have hprod : ∏ b, (c b).factorial = c a * ∏ b, (c' b).factorial := by
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a),
          ← Finset.mul_prod_erase Finset.univ (fun b => (c' b).factorial) (Finset.mem_univ a),
          hc', Function.update_self, ← mul_assoc, Nat.mul_factorial_pred (by omega)]
        congr 1
        exact Finset.prod_congr rfl fun b hb => by
          rw [Function.update_of_ne (Finset.ne_of_mem_erase hb)]
      have hcard : ((Finset.univ.filter fun M : Fin (n + 1) → α => ∀ b, cnt M b = c b).filter
          fun M => M 0 = a).card =
          (Finset.univ.filter fun M : Fin n → α => ∀ b, cnt M b = c' b).card := by
        refine Finset.card_nbij' (fun M => Fin.tail M) (fun M' => Fin.cons a M') ?_ ?_ ?_ ?_
        · intro M hM
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hM ⊢
          intro b
          have h1 := hM.1 b
          rw [← Fin.cons_self_tail M, cnt_cons, hM.2] at h1
          by_cases hab : a = b
          · subst hab; rw [hc', Function.update_self]; rw [if_pos rfl] at h1; omega
          · rw [hc', Function.update_of_ne (Ne.symm hab)]; rw [if_neg hab] at h1; omega
        · intro M' hM'
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hM' ⊢
          refine ⟨fun b => ?_, rfl⟩
          rw [cnt_cons, hM' b]
          by_cases hab : a = b
          · subst hab; rw [hc', Function.update_self, if_pos rfl]; omega
          · rw [hc', Function.update_of_ne (Ne.symm hab), if_neg hab]; rfl
        · intro M hM
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hM
          rw [← hM.2]
          exact Fin.cons_self_tail M
        · intro M' _
          simp
      rw [hcard, hprod, mul_left_comm, ih, mul_comm]
    rw [Finset.sum_congr rfl fun a _ => step a, ← Finset.mul_sum, hc, Nat.factorial_succ]
    ring

variable {T : Type*} [Fintype T] [DecidableEq T] {h : ℕ}

/-- Proof of part (ii) of `q_theorem_B_lower.md` (auxiliary): the number of closed tuples only
depends on the point set up to an isomorphism `e : T ≃ T'` compatible with the involutions. -/
lemma card_closedTuples_congr {T' : Type*} [Fintype T'] [DecidableEq T'] {h' : ℕ}
    (S : FibreSetting T h) (S' : FibreSetting T' h') (e : T ≃ T')
    (he : ∀ u, e (S.neg u) = S'.neg (e u)) (n : ℕ) :
    (closedTuples S n).card = (closedTuples S' n).card := by
  have hcnt : ∀ (M : Fin n → T) (u : T), cnt (e ∘ M) (e u) = cnt M u := by
    intro M u; simp [cnt]
  refine Finset.card_nbij' (fun M => e ∘ M) (fun M => e.symm ∘ M) ?_ ?_ ?_ ?_
  · intro M hM
    simp only [closedTuples, Finset.coe_filter, Finset.mem_univ, true_and,
      Set.mem_setOf_eq] at hM ⊢
    intro u'
    obtain ⟨u, rfl⟩ := e.surjective u'
    rw [← he, hcnt, hcnt, hM u]
  · intro M hM
    simp only [closedTuples, Finset.coe_filter, Finset.mem_univ, true_and,
      Set.mem_setOf_eq] at hM ⊢
    intro u
    have h1 := hM (e u)
    rw [← he] at h1
    have h2 : e.symm ∘ M = e.symm ∘ M := rfl
    rw [← hcnt (e.symm ∘ M) u, ← hcnt (e.symm ∘ M) (S.neg u)]
    simpa [Function.comp_def] using h1
  · intro M _; funext i; simp
  · intro M _; funext i; simp

omit [DecidableEq T] in
/-- Proof of part (ii) of `q_theorem_B_lower.md` (auxiliary): every point set `T` with a
fixed-point-free involution and `|T| = 2h` is isomorphic (compatibly with the involutions) to
the example `{1, …, h} × {±1}` of the **Setting**: choose one representative in each class. -/
lemma exists_equiv_std (S : FibreSetting T h) :
    ∃ e : T ≃ Fin h × Bool, ∀ u, e (S.neg u) = (stdSetting h S.one_le).neg (e u) := by
  let f := Fintype.equivFin T
  let R := {u : T // f u < f (S.neg u)}
  have hflip : ∀ u, ¬ f u < f (S.neg u) → f (S.neg u) < f (S.neg (S.neg u)) := by
    intro u hu
    rw [S.neg_neg]
    have : f u ≠ f (S.neg u) := fun h => S.neg_ne u (f.injective h).symm
    exact lt_of_le_of_ne (not_lt.1 hu) (Ne.symm this)
  let g : T → R × Bool := fun u =>
    if hu : f u < f (S.neg u) then (⟨u, hu⟩, true) else (⟨S.neg u, hflip u hu⟩, false)
  let g' : R × Bool → T := fun p => if p.2 then p.1.1 else S.neg p.1.1
  have hnot : ∀ r : R, ¬ f (S.neg r.1) < f (S.neg (S.neg r.1)) := by
    intro r; rw [S.neg_neg]; exact not_lt.2 r.2.le
  let eT : T ≃ R × Bool :=
    { toFun := g
      invFun := g'
      left_inv := by
        intro u
        by_cases hu : f u < f (S.neg u)
        · simp only [g, g', dif_pos hu, if_true]
        · simp only [g, g', dif_neg hu, Bool.false_eq_true, if_false, S.neg_neg]
      right_inv := by
        rintro ⟨r, b⟩
        cases b
        · simp only [g, g', Bool.false_eq_true, if_false]
          rw [dif_neg (hnot r)]
          simp [S.neg_neg]
        · simp only [g, g', if_true]
          rw [dif_pos r.2] }
  have hcardR : Fintype.card R = h := by
    have h1 := Fintype.card_congr eT
    have h2 := S.card_eq
    rw [Fintype.card_prod, Fintype.card_bool] at h1
    omega
  let eR : R ≃ Fin h := Fintype.equivFinOfCardEq hcardR
  refine ⟨eT.trans (eR.prodCongr (Equiv.refl Bool)), fun u => ?_⟩
  simp only [Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.coe_refl, stdSetting, eT,
    Equiv.coe_fn_mk, g]
  by_cases hu : f u < f (S.neg u)
  · rw [dif_neg (by rw [S.neg_neg]; exact not_lt.2 hu.le), dif_pos hu]
    simp [S.neg_neg]
  · rw [dif_pos (hflip u hu), dif_neg hu]
    simp

/-- Proof of part (ii) of `q_theorem_B_lower.md` (auxiliary): the counting argument for the
example `T = {1, …, h} × {±1}`.  A closed `N`-tuple is determined by the numbers `b_u` of entries
equal to `(u, +1)` (equal to the number equal to `(u, −1)`), with `Σ 2 b_u = N`, and then the
positions: `N! / Π_u (b_u!)^2` ways. -/
lemma card_closedTuples_std (hh : 1 ≤ h) (N : ℕ) :
    (closedTuples (stdSetting h hh) N).card =
      ∑ b ∈ (Fintype.piFinset fun _ : Fin h => Finset.range (N + 1)).filter
        (fun b => 2 * ∑ u, b u = N), N.factorial / ∏ u, (b u).factorial ^ 2 := by
  set B := (Fintype.piFinset fun _ : Fin h => Finset.range (N + 1)).filter
    (fun b => 2 * ∑ u, b u = N)
  let β : (Fin N → Fin h × Bool) → Fin h → ℕ := fun M u => cnt M (u, true)
  have hmaps : ∀ M ∈ closedTuples (stdSetting h hh) N, β M ∈ B := by
    intro M hM
    simp only [closedTuples, Finset.mem_filter, Finset.mem_univ, true_and] at hM
    simp only [B, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
    refine ⟨fun u => ?_, ?_⟩
    · have := Finset.card_filter_le (Finset.univ : Finset (Fin N)) (fun i => M i = (u, true))
      simp only [Finset.card_univ, Fintype.card_fin] at this
      simp only [β, cnt]
      omega
    · have hs := sum_cnt M
      rw [Fintype.sum_prod_type] at hs
      simp only [Fintype.sum_bool] at hs
      rw [← hs, Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      have := hM (u, true)
      simp only [stdSetting, Bool.not_true] at this
      simp only [β]
      omega
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_congr rfl fun b hb => ?_
  simp only [B, Finset.mem_filter] at hb
  have hfib : (closedTuples (stdSetting h hh) N).filter (fun M => β M = b) =
      Finset.univ.filter fun M : Fin N → Fin h × Bool => ∀ t, cnt M t = b t.1 := by
    ext M
    simp only [closedTuples, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hc, hβ⟩ ⟨u, ε⟩
      have h1 := congrFun hβ u
      simp only [β] at h1
      cases ε
      · have := hc (u, true)
        change cnt M (u, true) = cnt M (u, false) at this
        show cnt M (u, false) = b u
        omega
      · exact h1
    · intro hM
      refine ⟨fun t => ?_, funext fun u => hM (u, true)⟩
      rw [hM, hM]
      rfl
  have hsumc : ∑ t : Fin h × Bool, b t.1 = N := by
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool]
    rw [← hb.2, Finset.mul_sum]
    exact Finset.sum_congr rfl fun u _ => by ring
  have key := card_cnt_eq_mul_prod N (fun t : Fin h × Bool => b t.1) hsumc
  have hprod : ∏ t : Fin h × Bool, (b t.1).factorial = ∏ u, (b u).factorial ^ 2 := by
    rw [Fintype.prod_prod_type]
    simp only [Fintype.prod_bool]
    exact Finset.prod_congr rfl fun u _ => by ring
  rw [hprod] at key
  rw [hfib]
  have hpos : 0 < ∏ u, (b u).factorial ^ 2 :=
    Finset.prod_pos fun u _ => pow_pos (Nat.factorial_pos _) 2
  exact (Nat.div_eq_of_eq_mul_left hpos key.symm).symm

/-- **Theorem, part (ii)** of `q_theorem_B_lower.md` (proof): the number of closed tuples in
`T^N` is `Q_k(q)`. -/
theorem card_closedTuples_aux {q : ℕ} (S : FibreSetting T ((q - 1) / 2)) (k : ℕ) :
    (closedTuples S (2 * k + 2)).card = Qk k q := by
  obtain ⟨e, he⟩ := exists_equiv_std S
  rw [card_closedTuples_congr S _ e he, card_closedTuples_std]
  rfl

end TheoremB

end

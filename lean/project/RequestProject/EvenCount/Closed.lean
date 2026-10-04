module

public import RequestProject.EvenCount.Defs
public import RequestProject.ColUpper.Matching
public import RequestProject.TheoremB.Closed

/-!
# Parts (ii) and (iii) of the Theorem of `q_even_count.md`: closed tuples of a pointed point set

* `mem_closedPointed_iff` (Theorem (ii)): a tuple `g ∈ T^{2k+2}` is closed iff there is a
  matching `J` of `V` with `g_{J(x)} = −g_x` for every `x`;
* `card_closedPointed` (Theorem (iii)): the number of closed tuples in `T^{2k+2}` is
  `Q^e_k(2h + 2)`.
-/

@[expose] public section

namespace EvenCount

open Fibres TheoremB ColUpper

set_option synthInstance.maxHeartbeats 200000

variable {T : Type*} [Fintype T] [DecidableEq T] {h : ℕ}

/-! ### Part (ii) -/

/-- **Proof of (ii)** in `q_even_count.md` (auxiliary): the partner of a rank among the positions
with value `o` ("the first with the second, the third with the fourth, and so on"). -/
def flipRk (r : ℕ) : ℕ := if Even r then r + 1 else r - 1

/-- **Proof of (ii)** in `q_even_count.md` (auxiliary): pairing the ranks is an involution. -/
theorem flipRk_flipRk (r : ℕ) : flipRk (flipRk r) = r := by
  unfold flipRk
  rcases Nat.even_or_odd r with hr | hr
  · have : ¬ Even (r + 1) := by rw [Nat.not_even_iff_odd]; exact hr.add_one
    simp [hr, this]
  · have hr' : ¬ Even r := Nat.not_even_iff_odd.2 hr
    obtain ⟨t, rfl⟩ := hr
    have : Even (2 * t + 1 - 1) := ⟨t, by omega⟩
    simp only [hr', if_false, this, if_true]
    omega

/-- **Proof of (ii)** in `q_even_count.md` (auxiliary): pairing the ranks has no fixed point. -/
theorem flipRk_ne (r : ℕ) : flipRk r ≠ r := by
  unfold flipRk
  split_ifs with hr
  · omega
  · have : r ≠ 0 := by rintro rfl; exact hr ⟨0, rfl⟩
    omega

/-- **Proof of (ii)** in `q_even_count.md` (auxiliary): if `c` is even and `r < c`, the partner
rank is `< c`. -/
theorem flipRk_lt {r c : ℕ} (hc : Even c) (hr : r < c) : flipRk r < c := by
  unfold flipRk
  split_ifs with h
  · obtain ⟨a, rfl⟩ := hc
    obtain ⟨b, rfl⟩ := h
    omega
  · omega

/-- **Proof of (ii)** in `q_even_count.md` (*Only if*): for a closed tuple `g ∈ T^n` of a pointed
point set there is a fixed-point-free involution `J` of the positions with `g_{J(x)} = −g_x`. -/
theorem exists_invol_of_closedPointed (S : PointedSetting T h) {n : ℕ} {g : Fin n → T}
    (hg : g ∈ closedPointed S n) :
    ∃ J : Fin n → Fin n, ∀ x, J x ≠ x ∧ J (J x) = x ∧ g (J x) = S.neg (g x) := by
  simp only [closedPointed, Finset.mem_filter, Finset.mem_univ, true_and] at hg
  obtain ⟨hc, he⟩ := hg
  have hneg_ne : ∀ u, u ≠ S.o → S.neg u ≠ S.o := by
    intro u hu h
    apply hu
    rw [← S.neg_neg u, h, S.neg_o]
  let tr : Fin n → ℕ := fun x => if g x = S.o then flipRk (rk g x) else rk g x
  have hex : ∀ x, ∃ y, g y = S.neg (g x) ∧ rk g y = tr x := by
    intro x
    apply exists_rk_eq
    by_cases hx : g x = S.o
    · simp only [tr, hx, if_true, S.neg_o]
      have := rk_lt_cnt (M := g) x
      rw [hx] at this
      exact flipRk_lt he this
    · simp only [tr, hx, if_false]
      rw [← hc]
      exact rk_lt_cnt x
  choose J hJ1 hJ2 using hex
  refine ⟨J, fun x => ⟨fun hJx => ?_, ?_, hJ1 x⟩⟩
  · by_cases hx : g x = S.o
    · have := hJ2 x
      simp only [tr, hx, if_true, hJx] at this
      exact flipRk_ne _ this.symm
    · apply hx
      apply S.eq_o_of_neg_eq
      rw [← hJ1 x, hJx]
  · apply eq_of_rk_eq (M := g)
    · rw [hJ1, hJ1, S.neg_neg]
    · rw [hJ2]
      by_cases hx : g x = S.o
      · have hJo : g (J x) = S.o := by rw [hJ1, hx, S.neg_o]
        simp only [tr, hJo, if_true, hJ2, hx, flipRk_flipRk]
      · have hJo : g (J x) ≠ S.o := by rw [hJ1]; exact hneg_ne _ hx
        simp only [tr, hJo, if_false, hJ2, hx]

/-- **Proof of (ii)** in `q_even_count.md` (*If*, auxiliary): a fixed-point-free involution of a
finite set has an even number of elements. -/
theorem even_card_of_invol {α : Type*} (s : Finset α) (J : α → α) (hmem : ∀ x ∈ s, J x ∈ s)
    (hne : ∀ x ∈ s, J x ≠ x) (hJ : ∀ x ∈ s, J (J x) = x) : Even s.card := by
  have h1 : ∏ _x ∈ s, (-1 : ℤ) = 1 :=
    Finset.prod_involution (fun x _ => J x) (fun _ _ => by norm_num)
      (fun x hx _ => hne x hx) (fun x hx => hmem x hx) (fun x hx => hJ x hx)
  rw [Finset.prod_const] at h1
  exact (neg_one_pow_eq_one_iff_even (by norm_num)).1 h1

/-- **Theorem (ii)** of `q_even_count.md` (closed tuples and matchings): let `T` be a pointed
point set and `g ∈ T^{2k+2}`, indexed by `V = {0, …, 2k+1}`. Then `g` is closed if and only if
there is a matching `J` of `V` with `g_{J(x)} = −g_x` for every `x ∈ V`. -/
theorem mem_closedPointed_iff (S : PointedSetting T h) {k : ℕ} (g : Fin (2 * k + 2) → T) :
    g ∈ closedPointed S (2 * k + 2) ↔
      ∃ J : BallotBound.Matching k, ∀ x, g (J.1 x) = S.neg (g x) := by
  constructor
  · intro hg
    obtain ⟨J, hJ⟩ := exists_invol_of_closedPointed S hg
    exact ⟨⟨J, fun x => ⟨(hJ x).1, (hJ x).2.1⟩⟩, fun x => (hJ x).2.2⟩
  · rintro ⟨J, hJ⟩
    simp only [closedPointed, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun u => ?_, ?_⟩
    · refine Finset.card_bij' (fun x _ => J.1 x) (fun x _ => J.1 x) ?_ ?_ ?_ ?_
      · intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        rw [hJ, hx]
      · intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        rw [hJ, hx, S.neg_neg]
      · intro x _; exact (J.2 x).2
      · intro x _; exact (J.2 x).2
    · apply even_card_of_invol _ J.1
      · intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        rw [hJ, hx, S.neg_o]
      · intro x _; exact (J.2 x).1
      · intro x _; exact (J.2 x).2

/-! ### Part (iii) -/

/-- **Proof of (iii)** in `q_even_count.md` (auxiliary): the standard pointed point set
`T = {o} ∪ {1, …, h} × {±1}` (`Option (Fin h × Bool)`, with `o = none`), with
`(u, ε) ↦ (u, −ε)`. -/
def stdPointed (h : ℕ) : PointedSetting (Option (Fin h × Bool)) h where
  neg := Option.map fun p => (p.1, !p.2)
  neg_neg := by rintro (_ | ⟨u, ε⟩) <;> simp
  o := none
  neg_o := rfl
  eq_o_of_neg_eq := by
    rintro (_ | ⟨u, ε⟩) h
    · rfl
    · simp [Prod.ext_iff] at h
  card_eq := by simp [Fintype.card_option]; ring

/-- **Proof of (iii)** in `q_even_count.md` (auxiliary): the number of closed tuples only depends
on the pointed point set up to an isomorphism compatible with the maps `u ↦ −u`. -/
theorem card_closedPointed_congr {T' : Type*} [Fintype T'] [DecidableEq T'] {h' : ℕ}
    (S : PointedSetting T h) (S' : PointedSetting T' h') (e : T ≃ T')
    (he : ∀ u, e (S.neg u) = S'.neg (e u)) (n : ℕ) :
    (closedPointed S n).card = (closedPointed S' n).card := by
  have hcnt : ∀ (M : Fin n → T) (u : T), cnt (e ∘ M) (e u) = cnt M u := by
    intro M u; simp [cnt]
  have ho : e S.o = S'.o := S'.eq_o_of_neg_eq _ (by rw [← he, S.neg_o])
  refine Finset.card_nbij' (fun M => e ∘ M) (fun M => e.symm ∘ M) ?_ ?_ ?_ ?_
  · intro M hM
    simp only [closedPointed, Finset.coe_filter, Finset.mem_univ, true_and,
      Set.mem_setOf_eq] at hM ⊢
    refine ⟨fun u' => ?_, ?_⟩
    · obtain ⟨u, rfl⟩ := e.surjective u'
      rw [← he, hcnt, hcnt, hM.1 u]
    · rw [← ho, hcnt]; exact hM.2
  · intro M hM
    simp only [closedPointed, Finset.coe_filter, Finset.mem_univ, true_and,
      Set.mem_setOf_eq] at hM ⊢
    have hc' : ∀ u, cnt (e.symm ∘ M) u = cnt M (e u) := by
      intro u
      rw [← hcnt (e.symm ∘ M) u]
      simp [Function.comp_def]
    refine ⟨fun u => ?_, ?_⟩
    · rw [hc', hc', he]; exact hM.1 _
    · rw [hc', ho]; exact hM.2
  · intro M _; funext i; simp
  · intro M _; funext i; simp

omit [DecidableEq T] in
/-- **Proof of (iii)** in `q_even_count.md` (auxiliary): every pointed point set is isomorphic,
compatibly with `u ↦ −u`, to the standard one: `T' := T ∖ {o}` is a point set with a
fixed-point-free involution and `|T'| = 2h`, hence isomorphic to `{1, …, h} × {±1}`. -/
theorem exists_equiv_stdPointed (S : PointedSetting T h) :
    ∃ e : T ≃ Option (Fin h × Bool), ∀ u, e (S.neg u) = (stdPointed h).neg (e u) := by
  classical
  have hneg_ne : ∀ u, u ≠ S.o → S.neg u ≠ S.o := by
    intro u hu h
    apply hu
    rw [← S.neg_neg u, h, S.neg_o]
  let negT : {u // u ≠ S.o} → {u // u ≠ S.o} := fun u => ⟨S.neg u.1, hneg_ne u.1 u.2⟩
  have hcardT : Fintype.card {u // u ≠ S.o} = 2 * h := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, S.card_eq]; omega
  obtain ⟨e', he'⟩ : ∃ e' : {u // u ≠ S.o} ≃ Fin h × Bool,
      ∀ u, e' (negT u) = ((e' u).1, !(e' u).2) := by
    rcases Nat.eq_zero_or_pos h with h0 | hpos
    · subst h0
      have : IsEmpty {u // u ≠ S.o} := Fintype.card_eq_zero_iff.1 hcardT
      exact ⟨Fintype.equivOfCardEq (by rw [hcardT]; simp), fun u => isEmptyElim u⟩
    · let FS : FibreSetting {u // u ≠ S.o} h :=
        { neg := negT
          neg_neg := fun u => Subtype.ext (S.neg_neg u.1)
          neg_ne := fun u hu => u.2 (S.eq_o_of_neg_eq _ (congrArg Subtype.val hu))
          one_le := hpos
          card_eq := hcardT }
      obtain ⟨e', he'⟩ := exists_equiv_std FS
      exact ⟨e', he'⟩
  refine ⟨(Equiv.optionSubtypeNe S.o).symm.trans (Equiv.optionCongr e'), fun u => ?_⟩
  simp only [Equiv.trans_apply, Equiv.optionSubtypeNe_symm_apply, Equiv.optionCongr_apply]
  by_cases hu : u = S.o
  · subst hu
    simp [S.neg_o, stdPointed]
  · rw [dif_neg (hneg_ne u hu), dif_neg hu]
    simp only [Option.map_some, stdPointed]
    rw [← he' ⟨u, hu⟩]

/-- **Proof of (iii)** in `q_even_count.md` (auxiliary): the counting for the standard pointed
point set. A closed tuple is determined by `cnt(o) = 2c` and by the numbers `b_u` of entries
equal to `(u, +1)` (equal to the number equal to `(u, −1)`), and then the positions:
`N!/((2c)! Π_u (b_u!)^2)` ways. -/
theorem card_closedPointed_std (h k : ℕ) :
    (closedPointed (stdPointed h) (2 * k + 2)).card =
      ∑ c ∈ Finset.range (k + 2),
        ∑ b ∈ (Fintype.piFinset fun _ : Fin h => Finset.range (2 * k + 3)).filter
            (fun b => 2 * c + 2 * ∑ u, b u = 2 * k + 2),
          (2 * k + 2).factorial / ((2 * c).factorial * ∏ u, (b u).factorial ^ 2) := by
  set N := 2 * k + 2 with hN
  set B := (Finset.range (k + 2) ×ˢ
    (Fintype.piFinset fun _ : Fin h => Finset.range (2 * k + 3))).filter
      (fun p : ℕ × (Fin h → ℕ) => 2 * p.1 + 2 * ∑ u, p.2 u = N)
  let β : (Fin N → Option (Fin h × Bool)) → ℕ × (Fin h → ℕ) :=
    fun M => (cnt M none / 2, fun u => cnt M (some (u, true)))
  have hle : ∀ (M : Fin N → Option (Fin h × Bool)) t, cnt M t ≤ N := by
    intro M t
    have := Finset.card_filter_le (Finset.univ : Finset (Fin N)) (fun i => M i = t)
    simpa [cnt] using this
  have hsym : ∀ M ∈ closedPointed (stdPointed h) N, ∀ u : Fin h,
      cnt M (some (u, false)) = cnt M (some (u, true)) := by
    intro M hM u
    simp only [closedPointed, Finset.mem_filter, Finset.mem_univ, true_and] at hM
    have := hM.1 (some (u, true))
    simp only [stdPointed, Option.map_some, Bool.not_true] at this
    exact this.symm
  have hsum : ∀ M : Fin N → Option (Fin h × Bool),
      cnt M none + ∑ u : Fin h, (cnt M (some (u, true)) + cnt M (some (u, false))) = N := by
    intro M
    have hs := sum_cnt M
    rw [Fintype.sum_option, Fintype.sum_prod_type] at hs
    simpa only [Fintype.sum_bool] using hs
  have hmaps : ∀ M ∈ closedPointed (stdPointed h) N, β M ∈ B := by
    intro M hM
    have he : Even (cnt M none) := by
      simp only [closedPointed, Finset.mem_filter, Finset.mem_univ, true_and] at hM
      exact hM.2
    obtain ⟨a, ha⟩ := he
    simp only [B, β, Finset.mem_filter, Finset.mem_product, Fintype.mem_piFinset,
      Finset.mem_range]
    have h1 := hle M none
    refine ⟨⟨by omega, fun u => ?_⟩, ?_⟩
    · have := hle M (some (u, true)); omega
    · have hs := hsum M
      rw [Finset.sum_congr rfl fun u _ => by rw [hsym M hM u]] at hs
      have h2 : ∑ u : Fin h, (cnt M (some (u, true)) + cnt M (some (u, true))) =
          2 * ∑ u : Fin h, cnt M (some (u, true)) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun u _ => by ring
      omega
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  have hfib : ∀ p ∈ B, ((closedPointed (stdPointed h) N).filter fun M => β M = p).card =
      N.factorial / ((2 * p.1).factorial * ∏ u, (p.2 u).factorial ^ 2) := by
    rintro ⟨c, b⟩ hp
    simp only [B, Finset.mem_filter] at hp
    let cc : Option (Fin h × Bool) → ℕ := fun t => t.elim (2 * c) fun q => b q.1
    have hset : ((closedPointed (stdPointed h) N).filter fun M => β M = (c, b)) =
        Finset.univ.filter fun M : Fin N → Option (Fin h × Bool) => ∀ t, cnt M t = cc t := by
      ext M
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hM', hβ⟩
        have hM := hM'
        simp only [closedPointed, Finset.mem_filter, Finset.mem_univ, true_and] at hM
        simp only [β, Prod.mk.injEq] at hβ
        obtain ⟨hβ1, hβ2⟩ := hβ
        rintro (_ | ⟨u, ε⟩)
        · have ha : Even (cnt M none) := hM.2
          obtain ⟨a, ha⟩ := ha
          simp only [cc, Option.elim_none]
          change cnt M none = 2 * c
          omega
        · have h2 := congrFun hβ2 u
          simp only [cc, Option.elim_some]
          cases ε
          · rw [hsym M hM' u]; exact h2
          · exact h2
      · intro hM
        refine ⟨?_, ?_⟩
        · simp only [closedPointed, Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨fun t => ?_, ?_⟩
          · rcases t with _ | ⟨u, ε⟩
            · rfl
            · simp only [stdPointed, Option.map_some]
              rw [hM, hM]
              rfl
          · change Even (cnt M none)
            rw [hM]; exact ⟨c, by simp [cc]; ring⟩
        · simp only [β, Prod.mk.injEq]
          refine ⟨?_, funext fun u => hM _⟩
          rw [hM]; simp [cc]
    have hsumc : ∑ t, cc t = N := by
      rw [Fintype.sum_option, Fintype.sum_prod_type]
      simp only [cc, Option.elim_none, Option.elim_some, Fintype.sum_bool]
      rw [← hp.2, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun u _ => by ring
    have key := card_cnt_eq_mul_prod N cc hsumc
    have hprod : ∏ t, (cc t).factorial = (2 * c).factorial * ∏ u, (b u).factorial ^ 2 := by
      rw [Fintype.prod_option, Fintype.prod_prod_type]
      simp only [cc, Option.elim_none, Option.elim_some, Fintype.prod_bool]
      congr 1
      exact Finset.prod_congr rfl fun u _ => by ring
    rw [hprod] at key
    rw [hset]
    have hpos : 0 < (2 * c).factorial * ∏ u, (b u).factorial ^ 2 :=
      Nat.mul_pos (Nat.factorial_pos _)
        (Finset.prod_pos fun u _ => pow_pos (Nat.factorial_pos _) 2)
    exact (Nat.div_eq_of_eq_mul_left hpos key.symm).symm
  rw [Finset.sum_congr rfl hfib]
  simp only [B]
  rw [Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_filter]

/-- **Theorem (iii)** of `q_even_count.md` (the number of closed tuples): let `T` be a pointed
point set with `|T| = 2h + 1`. The number of closed tuples in `T^{2k+2}` is `Q^e_k(2h + 2)`.
(Proved directly by counting, through an isomorphism with the standard pointed point set,
rather than through `T ∖ {o}` and (i).) -/
theorem card_closedPointed (S : PointedSetting T h) (k : ℕ) :
    (closedPointed S (2 * k + 2)).card = QkEven k (2 * h + 2) := by
  obtain ⟨e, he⟩ := exists_equiv_stdPointed S
  rw [card_closedPointed_congr S (stdPointed h) e he, card_closedPointed_std]
  unfold QkEven
  rw [show (2 * h + 2 - 2) / 2 = h by omega]

end EvenCount

end

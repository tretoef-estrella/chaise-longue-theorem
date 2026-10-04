module

public import RequestProject.EvenColours.Defs

/-!
# (C0) of `q_even_count_colours.md`: the model point set

* (i) `EvenColours.negT_negT`: `negT` is an involution of `T2 S`;
* (ii) `EvenColours.card_T2`: `|T2 S| = m − 1`;
* (iii) `EvenColours.C0_iii_even`, `EvenColours.C0_iii_odd`: exactly one fixed point if `m` is
  even, none if `m` is odd;
* (iv) `EvenColours.C0_iv`: for even `m`, a pointed point set with `neg = negT`, and
  `|closedT negT (2k+2)| = Q^e_k(m)`;
* (v) `EvenColours.C0_v`: for odd `m`, a point set with `neg = negT`, and
  `|closedT negT (2k+2)| = Q_k(m)`.
-/

@[expose] public section

namespace EvenColours

open ColSplit ColSurv ColComp Fibres TheoremB EvenBlocks

open scoped Classical

variable {F : Type*} [Field F] (S : ColSetting F)

/-- **(C0)(i)** of `q_even_count_colours.md`: `negT` is an involution of `T2 S`. -/
@[simp] theorem negT_negT (x : T2 S) : negT S (negT S x) = x := by
  apply Subtype.ext
  simp [negT]

/-- **(C0)(ii)** of `q_even_count_colours.md`: `Fintype.card (T2 S) = S.m − 1`. -/
theorem card_T2 : Fintype.card (T2 S) = S.m - 1 := by
  rw [Fintype.card_subtype_compl, Fintype.card_prod, ZMod.card, Fintype.card_coe, S.card_μ,
    Fintype.card_unique]
  rfl

/-- **(C0)(iii)** of `q_even_count_colours.md` (proof): `(w, ζ)` is a fixed point of `negT` iff
`−w = w` and `ζ^{−1} = ζ`. -/
theorem negT_eq_iff (x : T2 S) : negT S x = x ↔ -x.1.1 = x.1.1 ∧ ((x.1.2 : F))⁻¹ = x.1.2 := by
  constructor
  · intro h
    have h' := congrArg Subtype.val h
    simp only [negT, Prod.ext_iff] at h'
    exact ⟨h'.1, congrArg Subtype.val h'.2⟩
  · rintro ⟨h1, h2⟩
    apply Subtype.ext
    exact Prod.ext h1 (Subtype.ext h2)

/-- **(C0)** of `q_even_count_colours.md` (proof): `m = q·r ≥ 2`. -/
theorem two_le_m : 2 ≤ S.m := by
  have h2 := two_le_q S
  have hr := S.one_le_r
  calc 2 ≤ S.q := h2
    _ ≤ S.q * S.r := Nat.le_mul_of_pos_right _ hr

variable {S} in
/-- **(C0)(iii)** of `q_even_count_colours.md` (proof): if `q` is odd, a fixed point `(w, ζ)` of
`negT` has `w = 0` and `ζ^{−1} = ζ`. -/
theorem fixed_of_odd_q (hq : Odd S.q) (x : T2 S) (hx : negT S x = x) :
    x.1.1 = 0 ∧ ((x.1.2 : F))⁻¹ = x.1.2 :=
  ⟨eq_zero_of_neg_eq_self hq ((negT_eq_iff S x).1 hx).1, ((negT_eq_iff S x).1 hx).2⟩

/-- **(C0)(iii)** of `q_even_count_colours.md`, even case: if `m` is even, `negT` has exactly one
fixed point (it is `(q/2, 1)` when `p = 2`, and `(0, −1)` when `r` is even). -/
theorem C0_iii_even (h : Even S.m) : ∃! x : T2 S, negT S x = x := by
  rcases (even_m_iff S).1 h with hp | hr
  · have hq := even_q_of_p_eq_two hp
    have hS := SInv_eq_singleton (S := S) (Or.inr hp)
    refine ⟨⟨(halfQ S, ColCount.oneμ S), fun h => halfQ_ne_zero S (Prod.mk.inj h).1⟩, ?_, ?_⟩
    · exact (negT_eq_iff S _).2 ⟨(neg_eq_self_iff_of_even hq _).2 (Or.inr rfl), by simp [ColCount.oneμ]⟩
    · intro y hy
      obtain ⟨h1, h2⟩ := (negT_eq_iff S y).1 hy
      have hmem : (y.1.2 : F) ∈ SInv S := Finset.mem_filter.2 ⟨y.1.2.2, h2⟩
      rw [hS, Finset.mem_singleton] at hmem
      have hζ : y.1.2 = ColCount.oneμ S := Subtype.ext hmem
      have hw : y.1.1 ≠ 0 := fun h0 => y.2 (Prod.ext h0 hζ)
      apply Subtype.ext
      exact Prod.ext (((neg_eq_self_iff_of_even hq _).1 h1).resolve_left hw) hζ
  · obtain ⟨hp, hne, hmem, hS⟩ := even_r_facts (S := S) hr
    have hq := ColOne.odd_q (S := S) hp
    refine ⟨⟨(0, ⟨-1, hmem⟩), fun h => hne (congrArg Subtype.val (Prod.mk.inj h).2)⟩, ?_, ?_⟩
    · exact (negT_eq_iff S _).2 ⟨neg_zero, by simp⟩
    · intro y hy
      obtain ⟨h1, h2⟩ := fixed_of_odd_q hq y hy
      have hmem' : (y.1.2 : F) ∈ SInv S := Finset.mem_filter.2 ⟨y.1.2.2, h2⟩
      rw [hS] at hmem'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem'
      rcases hmem' with h | h
      · exact absurd (Prod.ext h1 (Subtype.ext h)) y.2
      · apply Subtype.ext
        exact Prod.ext h1 (Subtype.ext h)

/-- **(C0)** of `q_even_count_colours.md` (proof): if `m` is odd, then `q` and `r` are odd. -/
theorem odd_q_r_of_odd_m (h : Odd S.m) : Odd S.q ∧ Odd S.r := by
  unfold ColSetting.m at h
  exact Nat.odd_mul.1 h

/-- **(C0)(iii)** of `q_even_count_colours.md`, odd case: if `m` is odd, `negT` has no fixed
point. -/
theorem C0_iii_odd (h : Odd S.m) : ∀ x : T2 S, negT S x ≠ x := by
  obtain ⟨hq, hr⟩ := odd_q_r_of_odd_m S h
  intro x hx
  obtain ⟨h1, h2⟩ := fixed_of_odd_q hq x hx
  exact x.2 (Prod.ext h1 (Subtype.ext (lemma63_i_self_inv hr x.1.2.2 h2)))

/-- **(C0)(iv)** of `q_even_count_colours.md`: for even `m`, `T2 S` with `negT` and its unique
fixed point is a pointed point set with `|T2 S| = 2·((m − 2)/2) + 1`. -/
noncomputable def pointedT2 (h : Even S.m) :
    EvenCount.PointedSetting (T2 S) ((S.m - 2) / 2) where
  neg := negT S
  neg_neg := negT_negT S
  o := Classical.choose (C0_iii_even S h)
  neg_o := (Classical.choose_spec (C0_iii_even S h)).1
  eq_o_of_neg_eq := fun u hu => (Classical.choose_spec (C0_iii_even S h)).2 u hu
  card_eq := by
    rw [card_T2]
    have := two_le_m S
    obtain ⟨t, ht⟩ := h
    omega

/-- **(C0)(iv)** of `q_even_count_colours.md` (proof): for even `m`, `closedT negT n` is the set of
closed tuples of the pointed point set `pointedT2`. -/
theorem closedT_eq_closedPointed (h : Even S.m) (n : ℕ) :
    closedT (negT S) n = EvenCount.closedPointed (pointedT2 S h) n := by
  ext g
  simp only [closedT, EvenCount.closedPointed, Finset.mem_filter, Finset.mem_univ, true_and]
  refine and_congr_right fun _ => ?_
  constructor
  · intro H
    exact H _ (pointedT2 S h).neg_o
  · intro H u hu
    rw [(pointedT2 S h).eq_o_of_neg_eq u hu]
    exact H

/-- **(C0)(iv)** of `q_even_count_colours.md`: if `m` is even, there is a pointed point set
`P : EvenCount.PointedSetting (T2 S) ((m − 2)/2)` with `P.neg = negT`, and for every `k`,
`|closedT negT (2k+2)| = Q^e_k(m)`. -/
theorem C0_iv (h : Even S.m) :
    (∃ P : EvenCount.PointedSetting (T2 S) ((S.m - 2) / 2), P.neg = negT S) ∧
      ∀ k, (closedT (negT S) (2 * k + 2)).card = EvenCount.QkEven k S.m := by
  refine ⟨⟨pointedT2 S h, rfl⟩, fun k => ?_⟩
  rw [closedT_eq_closedPointed S h, EvenCount.card_closedPointed]
  congr 1
  have := two_le_m S
  obtain ⟨t, ht⟩ := h
  omega

/-- **(C0)(v)** of `q_even_count_colours.md`: for odd `m`, `T2 S` with `negT` is a point set with
a fixed-point-free involution and `|T2 S| = 2·((m − 1)/2)`, `(m − 1)/2 ≥ 1`. -/
noncomputable def fibreT2 (h : Odd S.m) : FibreSetting (T2 S) ((S.m - 1) / 2) where
  neg := negT S
  neg_neg := negT_negT S
  neg_ne := C0_iii_odd S h
  one_le := by
    obtain ⟨hq, _⟩ := odd_q_r_of_odd_m S h
    have h2 := two_le_q S
    have hr := S.one_le_r
    have hq3 : 3 ≤ S.q := by obtain ⟨t, ht⟩ := hq; omega
    have : S.q ≤ S.m := Nat.le_mul_of_pos_right _ hr
    omega
  card_eq := by
    rw [card_T2]
    obtain ⟨t, ht⟩ := h
    omega

/-- **(C0)(v)** of `q_even_count_colours.md` (proof): for odd `m`, `closedT negT n` is the set of
closed tuples of the point set `fibreT2` (there is no fixed point). -/
theorem closedT_eq_closedTuples (h : Odd S.m) (n : ℕ) :
    closedT (negT S) n = closedTuples (fibreT2 S h) n := by
  ext g
  simp only [closedT, closedTuples, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · exact fun H => H.1
  · exact fun H => ⟨H, fun u hu => absurd hu (C0_iii_odd S h u)⟩

/-- **(C0)(v)** of `q_even_count_colours.md`: if `m` is odd, there is a point set
`Q : TheoremB.FibreSetting (T2 S) ((m − 1)/2)` with `Q.neg = negT`, and for every `k`,
`|closedT negT (2k+2)| = Q_k(m)`. -/
theorem C0_v (h : Odd S.m) :
    (∃ Q : FibreSetting (T2 S) ((S.m - 1) / 2), Q.neg = negT S) ∧
      ∀ k, (closedT (negT S) (2 * k + 2)).card = Qk k S.m := by
  refine ⟨⟨fibreT2 S h, rfl⟩, fun k => ?_⟩
  rw [closedT_eq_closedTuples S h]
  exact card_closedTuples (fibreT2 S h) k

end EvenColours

end

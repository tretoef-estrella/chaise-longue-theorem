module

public import RequestProject.EvenCount.Closed
public import RequestProject.ColUpper.Points

/-!
# Parts (iv) and (v) of the Theorem of `q_even_count.md`: the points `Γ`

`K` is a field containing a set `μ_m` of `m` distinct `m`-th roots of unity
(`X^m − 1 = Π_{ξ ∈ μ_m} (X − ξ)`), with `m ≠ 0` in `K`.

* `card_Gamma_eq_card_pairs` (Theorem (iv), every `m`): `|Γ|` is the number of tuples
  `g ∈ (μ_m ∖ {1})^{2k+2}` that split into inverse pairs along a matching;
* `card_Gamma_even` (Theorem (v)): for even `m`, `|Γ| = Q^e_k(m)`.
-/

@[expose] public section

namespace EvenCount

open ColSplit Fibres TheoremB ColUpper

set_option synthInstance.maxHeartbeats 200000

variable {K : Type*} [Field K] {m : ℕ}

/-- **Proof of (iv)** in `q_even_count.md` (*The product is `1`*): if a fixed-point-free
involution `J` of the positions pairs the entries of `u` into pairs with `u_x u_{J(x)} = 1`, then
`Π_x u_x = Π_{x < J(x)} u_x u_{J(x)} = 1`. (No parity hypothesis is needed.) -/
theorem prod_eq_one_of_matching {n : ℕ} (u : Fin n → K) (J : Fin n → Fin n)
    (hne : ∀ x, J x ≠ x) (hJ : ∀ x, J (J x) = x) (hpair : ∀ x, u x * u (J x) = 1) :
    ∏ x, u x = 1 :=
  Finset.prod_involution (fun x _ => J x) (fun x _ => hpair x) (fun x _ _ => hne x)
    (fun _ _ => Finset.mem_univ _) (fun x _ => hJ x)

section roots

open scoped Classical

variable {μm : Finset K}
  (hprod : (Polynomial.X ^ m - 1 : Polynomial K) = ∏ ξ ∈ μm, (Polynomial.X - Polynomial.C ξ))
include hprod

/-- **Proof of (iv)** in `q_even_count.md` (*Injective*): for a tuple `g ∈ P` the product of the
entries is `1`, so `g_0 = (g_1 ⋯ g_d)^{−1}`. -/
theorem head_eq_of_pairs {k : ℕ} {g : Fin (2 * k + 2) → Tpts μm} (J : BallotBound.Matching k)
    (hJ : ∀ x, (g (J.1 x) : K) = (g x : K)⁻¹) :
    (g 0 : K) = (∏ j : Fin (2 * k + 1), (g j.succ : K))⁻¹ := by
  have h1 : ∏ x, (g x : K) = 1 :=
    prod_eq_one_of_matching (fun x => (g x : K)) J.1 (fun x => (J.2 x).1) (fun x => (J.2 x).2)
      (fun x => by
        show (g x : K) * (g (J.1 x) : K) = 1
        rw [hJ x, mul_inv_cancel₀ (ne_zero_of_mem hprod (Finset.mem_of_mem_erase (g x).2))])
  rw [Fin.prod_univ_succ] at h1
  exact eq_inv_of_mul_eq_one_left h1

/-- **Theorem (iv)** of `q_even_count.md` (the points are the tuples that split into inverse
pairs; every `m`): let `K` contain a set `μ_m` of `m` distinct `m`-th roots of unity, with
`m ≠ 0` in `K` (`m` odd or even). Let `P` be the set of tuples
`g = (g_0, g_1, …, g_d) ∈ (μ_m ∖ {1})^{2k+2}` for which there is a matching `J` of `V` with
`g_{J(x)} = g_x^{−1}` for every `x ∈ V`. Then `g ↦ (g_1, …, g_d)` is a bijection from `P` onto
`Γ`; in particular `|Γ| = |P|`. (The hypothesis `|μ_m| = m` follows from the factorization and
is omitted.) -/
theorem card_Gamma_eq_card_pairs (hm : (m : K) ≠ 0) (k : ℕ) :
    (Gamma hprod k).card =
      (Finset.univ.filter fun g : Fin (2 * k + 2) → Tpts μm =>
        ∃ J : BallotBound.Matching k, ∀ x, (g (J.1 x) : K) = (g x : K)⁻¹).card := by
  symm
  apply Finset.card_bij (fun g _ => tailA g)
  · -- a tuple of `P` gives a point of `Γ`
    intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
    obtain ⟨J, hJK⟩ := hg
    simp only [Gamma, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨J, (evR_psiG_ne_zero_iff hprod hm _ J).2 ⟨?_, ?_⟩⟩
    · intro x hx
      rw [aExt_tailA g (ne_zero_of_lt hx)]
      exact Finset.ne_of_mem_erase (g _).2
    · intro x h0 hx
      rw [aExt_tailA g h0.ne', aExt_tailA g (ne_zero_of_lt hx), hJK,
        mul_inv_cancel₀ (ne_zero_of_mem hprod (Finset.mem_of_mem_erase (g x).2))]
  · -- injectivity
    intro g1 hg1 g2 hg2 h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg1 hg2
    obtain ⟨J1, hJ1⟩ := hg1
    obtain ⟨J2, hJ2⟩ := hg2
    have ht : ∀ j : Fin (2 * k + 1), (g1 j.succ : K) = (g2 j.succ : K) := fun j =>
      congrArg (fun y : μm => (y : K)) (congrFun h j)
    funext x
    cases x using Fin.cases with
    | zero =>
      apply Subtype.ext
      rw [head_eq_of_pairs hprod J1 hJ1, head_eq_of_pairs hprod J2 hJ2]
      simp only [ht]
    | succ j => exact Subtype.ext (ht j)
  · -- surjectivity
    intro a ha
    simp only [Gamma, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    obtain ⟨J, hJ⟩ := ha
    obtain ⟨h1, h2⟩ := (evR_psiG_ne_zero_iff hprod hm a J).1 hJ
    set b := J.1 0 with hbdef
    have hb0 : b ≠ 0 := (J.2 0).1
    have hab : aExt a b ≠ 0 := ne_zero_of_mem hprod (aExt_mem a hb0)
    let v : Fin (2 * k + 2) → K := fun x => if x = 0 then (aExt a b)⁻¹ else aExt a x
    have hvx : ∀ x, x ≠ 0 → v x = aExt a x := fun x hx => if_neg hx
    have hv0 : v 0 = (aExt a b)⁻¹ := if_pos rfl
    have hpair : ∀ x, v x * v (J.1 x) = 1 := by
      intro x
      by_cases hx : x = 0
      · subst hx
        rw [hv0, ← hbdef, hvx b hb0, inv_mul_cancel₀ hab]
      by_cases hJx : J.1 x = 0
      · have hxb : x = b := by rw [hbdef, ← hJx, (J.2 x).2]
        rw [hJx, hv0, hxb, hvx b hb0, mul_inv_cancel₀ hab]
      rw [hvx x hx, hvx _ hJx]
      rcases lt_or_gt_of_ne (J.2 x).1.symm with hlt | hlt
      · exact h2 x (Fin.pos_iff_ne_zero.2 hx) hlt
      · have := h2 (J.1 x) (Fin.pos_iff_ne_zero.2 hJx) (by rw [(J.2 x).2]; exact hlt)
        rw [(J.2 x).2, mul_comm] at this
        exact this
    have hvne : ∀ x, v x ≠ 1 := by
      intro x hvx1
      rcases lt_or_gt_of_ne (J.2 x).1.symm with hlt | hlt
      · have := hpair x
        rw [hvx1, one_mul, hvx _ (ne_zero_of_lt hlt)] at this
        exact h1 x hlt this
      · have hx0 : x ≠ 0 := ne_zero_of_lt hlt
        have := h1 (J.1 x) (by rw [(J.2 x).2]; exact hlt)
        rw [(J.2 x).2, ← hvx x hx0] at this
        exact this hvx1
    have hvmem : ∀ x, v x ∈ μm := by
      intro x
      by_cases hx : x = 0
      · rw [hx, hv0]; exact inv_mem_of_mem hprod (aExt_mem a hb0)
      · rw [hvx x hx]; exact aExt_mem a hx
    let g : Fin (2 * k + 2) → Tpts μm := fun x => ⟨v x, Finset.mem_erase.2 ⟨hvne x, hvmem x⟩⟩
    refine ⟨g, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨J, fun x => eq_inv_of_mul_eq_one_right (hpair x)⟩
    · funext j
      apply Subtype.ext
      show v j.succ = (a j : K)
      rw [hvx _ (Fin.succ_ne_zero j)]
      rfl

/-- **Proof of (v)** in `q_even_count.md`: for even `m` with `m ≠ 0` in `K`,
`T := μ_m ∖ {1}` with `u ↦ u^{−1}` is a pointed point set with `o = −1` and
`|T| = m − 1 = 2h + 1`, `h = (m − 2)/2`. -/
noncomputable def pointedSetting (hm : (m : K) ≠ 0) (heven : Even m) :
    PointedSetting (Tpts μm) ((m - 2) / 2) where
  neg u := ⟨(u : K)⁻¹, Finset.mem_erase.2 ⟨inv_ne_one.2 (Finset.ne_of_mem_erase u.2),
    inv_mem_of_mem hprod (Finset.mem_of_mem_erase u.2)⟩⟩
  neg_neg u := Subtype.ext (inv_inv _)
  o := ⟨-1, Finset.mem_erase.2 ⟨by
      intro h1
      apply hm
      obtain ⟨r, rfl⟩ := heven
      have h2 : (2 : K) = 0 := by
        have : (2 : K) = 1 - (-1) := by ring
        rw [this, h1, sub_self]
      push_cast
      rw [← two_mul, h2, zero_mul],
    (mem_iff_pow_eq_one hprod _).2 heven.neg_one_pow⟩⟩
  neg_o := Subtype.ext (by simp)
  eq_o_of_neg_eq u h := by
    apply Subtype.ext
    have h' : (u : K)⁻¹ = u := congrArg Subtype.val h
    have hne : (u : K) ≠ 0 := ne_zero_of_mem hprod (Finset.mem_of_mem_erase u.2)
    have h1 : (u : K) ≠ 1 := Finset.ne_of_mem_erase u.2
    have h2 : ((u : K) - 1) * ((u : K) + 1) = 0 := by
      have : (u : K) * (u : K) = 1 := by
        nth_rewrite 1 [← h']
        exact inv_mul_cancel₀ hne
      linear_combination this
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact absurd (sub_eq_zero.1 h3) h1
    · show (u : K) = -1
      linear_combination h3
  card_eq := by
    have hm0 : m ≠ 0 := by rintro rfl; exact hm Nat.cast_zero
    rw [Fintype.card_coe, Finset.card_erase_of_mem (one_mem_of_prod hprod), card_of_prod hprod]
    obtain ⟨r, rfl⟩ := heven
    omega

/-- **Theorem (v)** of `q_even_count.md` (the count for even `m`): if `K` contains a set `μ_m`
of `m` distinct `m`-th roots of unity, `m ≠ 0` in `K`, and `m` is even, then `|Γ| = Q^e_k(m)`.
(By (iv), (ii) and (iii) applied to `T = μ_m ∖ {1}` with `o = −1`. The hypothesis `|μ_m| = m`
follows from the factorization and is omitted.) -/
theorem card_Gamma_even (hm : (m : K) ≠ 0) (heven : Even m) (k : ℕ) :
    (Gamma hprod k).card = QkEven k m := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hm Nat.cast_zero
  rw [card_Gamma_eq_card_pairs hprod hm k]
  have hset : (Finset.univ.filter fun g : Fin (2 * k + 2) → Tpts μm =>
        ∃ J : BallotBound.Matching k, ∀ x, (g (J.1 x) : K) = (g x : K)⁻¹) =
      closedPointed (pointedSetting hprod hm heven) (2 * k + 2) := by
    ext g
    rw [mem_closedPointed_iff]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine exists_congr fun J => forall_congr' fun x => ?_
    constructor
    · intro h; exact Subtype.ext h
    · intro h; exact congrArg Subtype.val h
  rw [hset, card_closedPointed]
  congr 1
  obtain ⟨r, rfl⟩ := heven
  omega

end roots

end EvenCount

end

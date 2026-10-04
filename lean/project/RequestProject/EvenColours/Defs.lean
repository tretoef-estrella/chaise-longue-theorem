module

public import RequestProject.ColCount.Main
public import RequestProject.EvenBlocks.Product
public import RequestProject.EvenCount.Closed

/-!
# Definitions of `q_even_count_colours.md` (piece E17)

* `EvenColours.Om S := ZMod S.q`, the model of the `q`-th roots of unity (`0` plays `1`, negation
  plays inversion);
* `EvenColours.T2 S := {x : Om S × μ // x ≠ (0, 1)}` with the involution
  `EvenColours.negT S : (w, ζ) ↦ (−w, ζ^{−1})`;
* `EvenColours.closedT neg n`: the tuples in `X^n` that split into pairs `{u, neg u}`;
* `EvenColours.NS S ζ a`: the block counts of the self-inverse colours.

The settings and objects of the earlier files (`ColSplit.ColSetting`, `ColSurv.cExt`,
`ColComp.cls`, `ColComp.Compatible`, `EvenBlocks.SInv`, `EvenBlocks.IsReps2`, `Fibres.cnt`, …) are
reused unchanged.  No hypothesis on the parity of `p`, `q` or `r` is made in this file.
-/

@[expose] public section

namespace EvenColours

open ColSplit ColSurv ColComp Fibres TheoremB EvenBlocks

open scoped Classical

variable {F : Type*} [Field F] (S : ColSetting F)

/-- **Definitions** of `q_even_count_colours.md` (the remark `S.q ≥ 2` in the definition of
`Om S`): `q = p^v ≥ 2`, as `p ≥ 2` and `v ≥ 1`. -/
theorem two_le_q : 2 ≤ S.q := by
  unfold ColSetting.q
  calc 2 ≤ S.p := S.hp.two_le
    _ = S.p ^ 1 := (pow_one _).symm
    _ ≤ S.p ^ S.v := Nat.pow_le_pow_right S.hp.pos S.one_le_v

/-- **Definitions** of `q_even_count_colours.md`: `q ≠ 0` (so that `ZMod S.q` is finite). -/
instance qNeZero : NeZero S.q := ⟨by have := two_le_q S; omega⟩

/-- **Definitions** of `q_even_count_colours.md`: `Om S := ZMod S.q`, a model of the `q`-th roots
of unity (`0` plays `1`, negation plays inversion). -/
abbrev Om : Type := ZMod S.q

/-- **Definitions** of `q_even_count_colours.md`: the model point set
`T2 S := {x : Om S × μ // x ≠ (0, 1)}`. -/
abbrev T2 : Type _ := {x : Om S × S.μ // x ≠ (0, ColCount.oneμ S)}

/-- **Definitions** of `q_even_count_colours.md`: `negT (w, ζ) := (−w, ζ^{−1})`; it maps `T2 S` to
itself, since `(0, 1)` is its own image. -/
noncomputable def negT (x : T2 S) : T2 S :=
  ⟨(-x.1.1, ColCount.invμ S x.1.2), by
    intro h
    apply x.2
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    exact Prod.ext (neg_eq_zero.1 h1) ((ColCount.invμ_eq_one S _).1 h2)⟩

/-- **Definitions** of `q_even_count_colours.md`: for a finite type `X` with a map `neg : X → X`,
`closedT neg n` is the set of tuples `g ∈ X^n` with `cnt g u = cnt g (neg u)` for every `u` and
`cnt g u` even at every fixed point `u = neg u` (the tuples that split into pairs `{u, neg u}`). -/
def closedT {X : Type*} [Fintype X] [DecidableEq X] (neg : X → X) (n : ℕ) :
    Finset (Fin n → X) :=
  Finset.univ.filter fun g => (∀ u, cnt g u = cnt g (neg u)) ∧ ∀ u, neg u = u → Even (cnt g u)

/-- **Definitions** of `q_even_count_colours.md`: the negation `w ↦ −w` on
`{w : Om S // w ≠ 0}` (the point set of the class `𝒞_1`). -/
def negW (w : {w : Om S // w ≠ 0}) : {w : Om S // w ≠ 0} := ⟨-w.1, neg_ne_zero.2 w.2⟩

/-- **Definitions** of `q_even_count_colours.md`: for a colour `ζ : F` and `a : ℕ`,
`NS S ζ a` is the number of closed tuples in `{w : Om S // w ≠ 0}^a` if `ζ = 1`, and in
`(Om S)^a` otherwise (on `𝒞_1` the entries avoid the point `1`; on `𝒞_{−1}` they do not). -/
noncomputable def NS (ζ : F) (a : ℕ) : ℕ :=
  if ζ = 1 then (closedT (negW S) a).card else (closedT (fun w : Om S => -w) a).card

/-! ### General facts on `closedT` -/

section General

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- **Remarks for the proofs** of `q_even_count_colours.md` (auxiliary for (C2) and (C3)(d)): for
an involution `neg` and a set `s` stable under `neg`, the number of entries of a tuple of
`closedT neg n` lying in `s` is even. -/
theorem even_sum_cnt {neg : X → X} (hneg : ∀ u, neg (neg u) = u) {n : ℕ} {g : Fin n → X}
    (hg : g ∈ closedT neg n) (s : Finset X) (hs : ∀ u ∈ s, neg u ∈ s) :
    Even (∑ u ∈ s, cnt g u) := by
  have hcl := (Finset.mem_filter.1 hg).2
  rw [← ZMod.natCast_eq_zero_iff_even, Nat.cast_sum]
  refine Finset.sum_involution (fun u _ => neg u) ?_ ?_ ?_ ?_
  · intro u _
    rw [← hcl.1 u, ← two_mul]
    exact mul_eq_zero_of_left rfl _
  · intro u _ h hfix
    exact h ((ZMod.natCast_eq_zero_iff_even).2 (hcl.2 u hfix))
  · intro u hu
    exact hs u hu
  · intro u _
    exact hneg u

/-- **Remarks for the proofs** of `q_even_count_colours.md` (auxiliary): the length of a tuple is
the sum of its counts. -/
theorem sum_cnt_eq {n : ℕ} (g : Fin n → X) : ∑ u, cnt g u = n := by
  unfold cnt
  rw [← Finset.card_eq_sum_card_fiberwise (f := g) (s := Finset.univ) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  simp

/-- **(C3)(d)** of `q_even_count_colours.md` (general form): for an involution `neg`, a tuple of
`closedT neg n` has even length `n`. -/
theorem even_of_mem_closedT {neg : X → X} (hneg : ∀ u, neg (neg u) = u) {n : ℕ}
    {g : Fin n → X} (hg : g ∈ closedT neg n) : Even n := by
  have := even_sum_cnt hneg hg Finset.univ (fun u _ => Finset.mem_univ _)
  rwa [sum_cnt_eq] at this

/-- **(C3)(b), (C3)(c)** of `q_even_count_colours.md` (auxiliary): there is exactly one tuple of
length `0`, and it is closed. -/
theorem card_closedT_zero (neg : X → X) : (closedT neg 0).card = 1 := by
  have : closedT neg 0 = Finset.univ := by
    ext g
    simp [closedT, cnt]
  rw [this, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, pow_zero]

end General

/-! ### Negation in `Om S` -/

/-- **Remarks for the proofs** of `q_even_count_colours.md`: `w = −w` in `ZMod q` iff `w = 0` or
`2·w = q` (as natural numbers, with `w` read in `{0, …, q − 1}`). -/
theorem neg_eq_self_iff (w : Om S) : -w = w ↔ w = 0 ∨ 2 * w.val = S.q := by
  have hlt : w.val < S.q := ZMod.val_lt w
  have key : -w = w ↔ S.q ∣ 2 * w.val := by
    rw [← ZMod.natCast_eq_zero_iff, neg_eq_iff_add_eq_zero]
    push_cast
    rw [ZMod.natCast_zmod_val]
    constructor <;> intro h <;> linear_combination h
  rw [key, ← ZMod.val_eq_zero]
  constructor
  · rintro ⟨c, hc⟩
    have hc2 : c < 2 := by
      by_contra hc2
      push_neg at hc2
      have : S.q * 2 ≤ S.q * c := Nat.mul_le_mul_left _ hc2
      omega
    interval_cases c
    · left; omega
    · right; omega
  · rintro (h | h)
    · rw [h]; exact dvd_zero _
    · rw [h]

/-- **Remarks for the proofs** of `q_even_count_colours.md`: if `q` is odd, `w = −w` in `ZMod q`
only for `w = 0`. -/
theorem eq_zero_of_neg_eq_self {S : ColSetting F} (hq : Odd S.q) {w : Om S} (h : -w = w) :
    w = 0 := by
  rcases (neg_eq_self_iff S w).1 h with h | h
  · exact h
  · obtain ⟨t, ht⟩ := hq; omega

/-- **Remarks for the proofs** of `q_even_count_colours.md`: the element `q/2` of `ZMod q`. -/
def halfQ : Om S := ((S.q / 2 : ℕ) : Om S)

/-- **Remarks for the proofs** of `q_even_count_colours.md`: `q/2 ≠ 0` in `ZMod q` (as `q ≥ 2`). -/
theorem halfQ_ne_zero : halfQ S ≠ 0 := by
  have h2 := two_le_q S
  unfold halfQ
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro h
  have := Nat.le_of_dvd (by omega) h
  omega

/-- **Remarks for the proofs** of `q_even_count_colours.md`: if `q` is even, `w = −w` in `ZMod q`
iff `w = 0` or `w = q/2`. -/
theorem neg_eq_self_iff_of_even {S : ColSetting F} (hq : Even S.q) (w : Om S) :
    -w = w ↔ w = 0 ∨ w = halfQ S := by
  rw [neg_eq_self_iff]
  obtain ⟨t, ht⟩ := hq
  have hval : (halfQ S).val = S.q / 2 := by
    unfold halfQ
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by have := two_le_q S; omega)]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · right
      apply ZMod.val_injective
      rw [hval]; omega
  · rintro (h | h)
    · exact Or.inl h
    · right
      rw [h, hval]; omega

/-- **Remarks for the proofs** of `q_even_count_colours.md`: if `p = 2`, then `q = 2^v` is even. -/
theorem even_q_of_p_eq_two {S : ColSetting F} (hp : S.p = 2) : Even S.q := by
  unfold ColSetting.q
  rw [hp]
  exact (Nat.even_pow).2 ⟨even_two, by have := S.one_le_v; omega⟩

/-- **Remarks for the proofs** of `q_even_count_colours.md`: `Even S.m ↔ (S.p = 2 ∨ Even S.r)`. -/
theorem even_m_iff : Even S.m ↔ S.p = 2 ∨ Even S.r := by
  unfold ColSetting.m ColSetting.q
  rw [Nat.even_mul, Nat.even_pow, S.hp.even_iff]
  have := S.one_le_v
  constructor
  · rintro (⟨h, _⟩ | h)
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl ⟨h, by omega⟩
    · exact Or.inr h

end EvenColours

end

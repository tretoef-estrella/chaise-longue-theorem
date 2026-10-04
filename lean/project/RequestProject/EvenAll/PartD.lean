module

public import RequestProject.EvenAll.PartA

/-!
# Part D of `q_even_assembly.md`: Corollary 9.12 (i), every block has exactly the dimension of
its count

* **(D1)** `EvenAll.closedT_nonempty`, `EvenAll.D1_NS`, `EvenAll.D1_Nbal`: positivity of the
  counts `NS S ζ (2j)` and `Bip.Nbal a q`.
* **(D2)** `EvenAll.D2` (Corollary 9.12 (i)): for a compatible colouring, `finrank IcS = NS` and
  `finrank Icz = Nbal`.
-/

@[expose] public section

namespace EvenAll

open ColSplit ColSurv ColComp ColDecomp EvenBlocks Fibres Finset

open scoped Classical

set_option synthInstance.maxHeartbeats 200000

/-- **Part D, (D1)** of `q_even_assembly.md` (auxiliary; "a closed tuple exists: pair the
coordinates"): for an involution `neg` of a finite type `X` and any `x : X`, the tuple of length
`2j` whose first `j` entries are `x` and whose last `j` entries are `neg x` is closed, so
`closedT neg (2j)` is non-empty. -/
theorem closedT_nonempty {X : Type*} [Fintype X] [DecidableEq X] {neg : X → X}
    (hneg : ∀ u, neg (neg u) = u) (x : X) (j : ℕ) :
    (EvenColours.closedT neg (2 * j)).Nonempty := by
  let g : Fin (2 * j) → X := fun i => if i.val < j then x else neg x
  have hlt : (univ.filter fun i : Fin (2 * j) => i.val < j).card = j := by
    rw [Fin.card_filter_val_lt]; omega
  have hge : (univ.filter fun i : Fin (2 * j) => ¬ i.val < j).card = j := by
    have := card_filter_add_card_filter_not (s := (univ : Finset (Fin (2 * j))))
      (fun i : Fin (2 * j) => i.val < j)
    rw [card_univ, Fintype.card_fin, hlt] at this
    omega
  have key : ∀ u, cnt g u = (if x = u then j else 0) + (if neg x = u then j else 0) := by
    intro u
    unfold cnt
    by_cases hx : x = u <;> by_cases hn : neg x = u
    · have : (univ.filter fun i => g i = u) = univ := by
        ext i; simp only [g, mem_filter, mem_univ, true_and, iff_true]; split_ifs <;> assumption
      rw [this, card_univ, Fintype.card_fin, if_pos hx, if_pos hn]; ring
    · have : (univ.filter fun i => g i = u) = univ.filter fun i : Fin (2 * j) => i.val < j := by
        ext i; simp only [g, mem_filter, mem_univ, true_and]; split_ifs <;> simp_all
      rw [this, hlt, if_pos hx, if_neg hn]; omega
    · have : (univ.filter fun i => g i = u) = univ.filter fun i : Fin (2 * j) => ¬ i.val < j := by
        ext i; simp only [g, mem_filter, mem_univ, true_and]; split_ifs <;> simp_all
      rw [this, hge, if_neg hx, if_pos hn]; omega
    · have : (univ.filter fun i => g i = u) = ∅ := by
        ext i; simp only [g, mem_filter, mem_univ, true_and]; split_ifs <;> simp_all
      rw [this, card_empty, if_neg hx, if_neg hn]
  refine ⟨g, ?_⟩
  simp only [EvenColours.closedT, mem_filter, mem_univ, true_and]
  refine ⟨fun u => ?_, fun u hu => ?_⟩
  · rw [key, key]
    have e1 : (x = neg u) ↔ (neg x = u) := ⟨fun h => by rw [h, hneg], fun h => by rw [← h, hneg]⟩
    have e2 : (neg x = neg u) ↔ (x = u) :=
      ⟨fun h => by rw [← hneg x, h, hneg], fun h => by rw [h]⟩
    by_cases h1 : x = u <;> by_cases h2 : neg x = u <;> simp_all
  · rw [key]
    by_cases h1 : x = u
    · have h2 : neg x = u := by rw [h1, hu]
      rw [if_pos h1, if_pos h2]; exact ⟨j, rfl⟩
    · have h2 : ¬ neg x = u := fun h => h1 (by rw [← hneg x, h, hu])
      rw [if_neg h1, if_neg h2]; exact ⟨0, rfl⟩

variable {F : Type*} [Field F]

/-- **Part D, (D1)** of `q_even_assembly.md` (positivity of `NS`): for every `ColSetting S`,
`NS S ζ (2j) ≥ 1` for every `j`. **More general:** it holds for every colour `ζ : F`, not only for
`ζ ∈ SInv S` (pair the coordinates; the point set `{w ≠ 0}` is non-empty as `q ≥ 2`). -/
theorem D1_NS (S : ColSetting F) (ζ : F) (j : ℕ) : 1 ≤ EvenColours.NS S ζ (2 * j) := by
  unfold EvenColours.NS
  split_ifs
  · haveI : Fact (1 < S.q) := ⟨by have := EvenColours.two_le_q S; omega⟩
    have hw : (1 : EvenColours.Om S) ≠ 0 := one_ne_zero
    exact card_pos.2 (closedT_nonempty (fun w => Subtype.ext (neg_neg w.1)) ⟨1, hw⟩ j)
  · exact card_pos.2 (closedT_nonempty (fun w : EvenColours.Om S => neg_neg w) 0 j)

/-- **Part D, (D1)** of `q_even_assembly.md` (positivity of `Nbal`): `Bip.Nbal a q ≥ 1` for every
`a`, as soon as `q ≥ 1` (the pair `(ξ, ξ)` is balanced). In particular `Bip.Nbal a S.q ≥ 1` for
every `ColSetting S` (`D1_Nbal_S`). **More general:** stated for every `q ≥ 1`. -/
theorem D1_Nbal (a : ℕ) {q : ℕ} (hq : 1 ≤ q) : 1 ≤ Bip.Nbal a q := by
  unfold Bip.Nbal
  refine card_pos.2 ⟨(fun _ => ⟨0, hq⟩, fun _ => ⟨0, hq⟩), ?_⟩
  simp

/-- **Part D, (D1)** of `q_even_assembly.md`: `Bip.Nbal a S.q ≥ 1` for every `ColSetting S` and
every `a`. -/
theorem D1_Nbal_S (S : ColSetting F) (a : ℕ) : 1 ≤ Bip.Nbal a S.q :=
  D1_Nbal a (by have := EvenColours.two_le_q S; omega)

/-- **Part D, (D2)** of `q_even_assembly.md` (auxiliary, "a product of naturals that equals a
product of smaller-or-equal positive naturals forces each factor to be equal"). -/
theorem prod_eq_of_le_of_prod_eq {ι : Type*} {s : Finset ι} {f g : ι → ℕ}
    (hf : ∀ i ∈ s, 0 < f i) (hfg : ∀ i ∈ s, f i ≤ g i) (h : ∏ i ∈ s, f i = ∏ i ∈ s, g i) :
    ∀ i ∈ s, f i = g i := by
  by_contra hc
  push_neg at hc
  obtain ⟨i, hi, hne⟩ := hc
  have := Finset.prod_lt_prod hf hfg ⟨i, hi, lt_of_le_of_ne (hfg i hi) hne⟩
  omega

/-- **Part D, (D2)** of `q_even_assembly.md` (auxiliary, the two-factor case of the previous
lemma). -/
theorem mul_eq_of_le_of_mul_eq {a b c d : ℕ} (ha : 0 < a) (hb : 0 < b) (hac : a ≤ c)
    (hbd : b ≤ d) (h : a * b = c * d) : a = c ∧ b = d := by
  constructor
  · by_contra hne
    have : a * b < c * d := Nat.mul_lt_mul_of_lt_of_le (lt_of_le_of_ne hac hne) hbd (by omega)
    omega
  · by_contra hne
    have : a * b < c * d := Nat.mul_lt_mul_of_le_of_lt hac (lt_of_le_of_ne hbd hne) (by omega)
    omega

/-- **Part D, (D2)** of `q_even_assembly.md` (the sandwich, for every colouring): for every
`ColSetting S`, every `R` with `IsReps2 S R`, every `k` and every `c`, the term of
`EvenColours.C2` equals `finrank F ((idealI S k).map (S.piC c))`. (By `lemma61_ii`, (A2) and
`EvenColours.C4` the two sums over `c` agree, and each term is `≤` by `EvenOne.E2`.) -/
theorem term_eq_finrank (S : ColSetting F) {R : Finset F} (hR : IsReps2 S R) (k : ℕ)
    (c : Fin (2 * k + 1) → S.μ) :
    (if ∃ J : BallotBound.Matching k, Compatible (cExt c) J then
        (∏ ζ ∈ SInv S, EvenColours.NS S ζ (cls (cExt c) ζ).card) *
          ∏ ζ ∈ R, Bip.Nbal (cls (cExt c) ζ).card S.q
      else 0) = Module.finrank F ((idealI S k).map (S.piC c)) := by
  have hsum : (∑ c : Fin (2 * k + 1) → S.μ,
      (if ∃ J : BallotBound.Matching k, Compatible (cExt c) J then
        (∏ ζ ∈ SInv S, EvenColours.NS S ζ (cls (cExt c) ζ).card) *
          ∏ ζ ∈ R, Bip.Nbal (cls (cExt c) ζ).card S.q
      else 0)) = ∑ c : Fin (2 * k + 1) → S.μ,
        Module.finrank F ((idealI S k).map (S.piC c)) := by
    rw [EvenColours.C4 hR k, ← A2 S k]
    exact S.lemma61_ii (2 * k + 1) (idealI S k)
  exact (Finset.sum_eq_sum_iff_of_le (fun c _ => EvenOne.E2 S hR c)).1 hsum c (mem_univ c)

/-- **Part D, (D2)** of `q_even_assembly.md`: **Corollary 9.12 (i).** For every `ColSetting S`,
every `R` with `IsReps2 S R`, every `k` and every `c : Fin (2k+1) → S.μ` with a compatible
matching:
* `finrank F (IcS S c ζ) = NS S ζ |𝒞_ζ|` for every `ζ ∈ SInv S`, and
* `finrank F (Icz S c ζ) = Bip.Nbal |𝒞_ζ| S.q` for every `ζ ∈ R`.

(Sandwich: the term of `C2` equals `dim π_c(I)` (`term_eq_finrank`); `dim π_c(I)` is the product
of the block dimensions (`EvenBlocks.lemma95`), each count is `≤` its dimension
(`EvenOne.NS_le_finrank_IcS`, `EvenMinus.lemma97` with `existsA9`) and each count is `≥ 1`
(D1).) -/
theorem D2 (S : ColSetting F) {R : Finset F} (hR : IsReps2 S R) {k : ℕ}
    (c : Fin (2 * k + 1) → S.μ) (hcomp : ∃ J : BallotBound.Matching k, Compatible (cExt c) J) :
    (∀ ζ ∈ SInv S, Module.finrank F (IcS S c ζ) = EvenColours.NS S ζ (cls (cExt c) ζ).card) ∧
      ∀ ζ ∈ R, Module.finrank F (Icz S c ζ) = Bip.Nbal (cls (cExt c) ζ).card S.q := by
  have hA9 := (existsA9 hR (cExt_mem c)).1 hcomp
  have hNS : ∀ ζ ∈ SInv S, 0 < EvenColours.NS S ζ (cls (cExt c) ζ).card := by
    intro ζ hζ
    obtain ⟨j, hj⟩ := hA9.1 ζ hζ
    rw [hj, ← two_mul]
    exact D1_NS S ζ j
  have hNb : ∀ ζ ∈ R, 0 < Bip.Nbal (cls (cExt c) ζ).card S.q := fun ζ _ => D1_Nbal_S S _
  have hle1 : ∀ ζ ∈ SInv S, EvenColours.NS S ζ (cls (cExt c) ζ).card ≤
      Module.finrank F (IcS S c ζ) := fun ζ hζ => EvenOne.NS_le_finrank_IcS S c hζ
  have hle2 : ∀ ζ ∈ R, Bip.Nbal (cls (cExt c) ζ).card S.q ≤ Module.finrank F (Icz S c ζ) :=
    fun ζ hζ => EvenMinus.lemma97 hR hζ c (hA9.2 ζ hζ)
  have heq := term_eq_finrank S hR k c
  rw [if_pos hcomp, (lemma95 S c hR).1 hcomp] at heq
  obtain ⟨h1, h2⟩ := mul_eq_of_le_of_mul_eq (Finset.prod_pos hNS) (Finset.prod_pos hNb)
    (Finset.prod_le_prod (fun _ _ => Nat.zero_le _) hle1)
    (Finset.prod_le_prod (fun _ _ => Nat.zero_le _) hle2) heq
  exact ⟨fun ζ hζ => (prod_eq_of_le_of_prod_eq hNS hle1 h1 ζ hζ).symm,
    fun ζ hζ => (prod_eq_of_le_of_prod_eq hNb hle2 h2 ζ hζ).symm⟩

end EvenAll

end

module

public import Mathlib

/-!
# Combinatorics of ballot sets (steps (ii) and (iii) of `q3_ballot_lower_bound.md`)

Positions `1, …, n'` of the source are encoded here as natural numbers `0, …, n' - 1`.
-/

@[expose] public section

open Finset

namespace BallotBound

/-- The ballot condition defining `𝓤` in the **Proof** of `q3_ballot_lower_bound.md`:
reading the positions `0, …, n - 1` as up-steps (in `U`) and down-steps (not in `U`), the height
`h(i) = |U ∩ [i]| − |[i] ∖ U| = 2 |U ∩ [i]| − i` is `≥ −1` for every `i ≤ n`. -/
def IsBallot (n : ℕ) (U : Finset ℕ) : Prop := ∀ i ≤ n, i ≤ 2 * (U ∩ range i).card + 1

/-- The ballot condition of `𝓤` (**Proof** of `q3_ballot_lower_bound.md`) is decidable. -/
instance (n : ℕ) : DecidablePred (IsBallot n) := fun U => by unfold IsBallot; infer_instance

/-- The set `𝓤 = {U ⊆ [n] : h(i) ≥ −1 for all i}` of ballot sets from the **Proof** of
`q3_ballot_lower_bound.md` (with positions shifted to `0, …, n - 1`). -/
def ballotSets (n : ℕ) : Finset (Finset ℕ) := (range n).powerset.filter (IsBallot n)

/-- Unfolding the ballot condition of `𝓤` (**Proof**, *Ballot sets*, of `q3_ballot_lower_bound.md`) by one step. -/
lemma isBallot_succ (n : ℕ) (U : Finset ℕ) :
    IsBallot (n + 1) U ↔ IsBallot n U ∧ n + 1 ≤ 2 * (U ∩ range (n + 1)).card + 1 := by
  constructor
  · intro h
    exact ⟨fun i hi => h i (by omega), h (n + 1) le_rfl⟩
  · rintro ⟨h1, h2⟩ i hi
    rcases Nat.lt_or_ge i (n + 1) with h | h
    · exact h1 i (by omega)
    · obtain rfl : i = n + 1 := by omega
      exact h2

/-- Greedy matching of a ballot path (step (ii) of `q3_ballot_lower_bound.md`): the positions
`< n` split into a set `R ⊆ U` of unmatched up-steps, a set `D` (of size `≤ 1`) of unmatched
down-steps, and pairs `{x, p x}` whose smaller element is an up-step and larger a down-step. -/
theorem greedy_matching (U : Finset ℕ) : ∀ n, IsBallot n U → ∃ (p : ℕ → ℕ) (R D : Finset ℕ),
    R ⊆ U ∩ range n ∧ D ⊆ range n \ U ∧ D.card ≤ 1 ∧
    R.card + n = 2 * (U ∩ range n).card + D.card ∧
    (∀ x, (x ∈ R ∨ x ∈ D ∨ n ≤ x) → p x = x) ∧
    (∀ x < n, x ∉ R → x ∉ D → p x ≠ x ∧ p x < n ∧ p (p x) = x ∧ (x < p x → x ∈ U ∧ p x ∉ U)) := by
  intro n
  induction n with
  | zero =>
    intro _
    exact ⟨id, ∅, ∅, by simp, by simp, by simp, by simp, fun _ _ => rfl,
      fun x hx => absurd hx (Nat.not_lt_zero _)⟩
  | succ n ih =>
    intro hU
    have hU' : IsBallot n U := ((isBallot_succ n U).1 hU).1
    have hlast := ((isBallot_succ n U).1 hU).2
    obtain ⟨p, R, D, hR, hD, hD1, hcard, hfix, hpair⟩ := ih hU'
    have hRD : ∀ x, x ∈ R → x ∉ D := fun x hxR hxD => by
      have h1 := (mem_inter.1 (hR hxR)).1
      have h2 := (mem_sdiff.1 (hD hxD)).2
      exact h2 h1
    have hRlt : ∀ x ∈ R, x < n := fun x hx => mem_range.1 (mem_inter.1 (hR hx)).2
    have hDlt : ∀ x ∈ D, x < n := fun x hx => mem_range.1 (mem_sdiff.1 (hD hx)).1
    by_cases hn : n ∈ U
    · have hrs : U ∩ range (n + 1) = insert n (U ∩ range n) := by
        rw [range_add_one, inter_insert_of_mem hn]
      have hnR : n ∉ R := fun h => by have := hRlt n h; omega
      have hnU : n ∉ U ∩ range n := by simp
      refine ⟨p, insert n R, D, ?_, ?_, hD1, ?_, ?_, ?_⟩
      · rw [hrs]; exact insert_subset_insert _ hR
      · exact hD.trans (sdiff_subset_sdiff (range_mono (Nat.le_succ n)) (subset_refl U))
      · rw [hrs, card_insert_of_notMem hnR, card_insert_of_notMem hnU]; omega
      · intro x hx
        rcases hx with hx | hx | hx
        · rcases mem_insert.1 hx with rfl | hx
          · exact hfix _ (Or.inr (Or.inr le_rfl))
          · exact hfix _ (Or.inl hx)
        · exact hfix _ (Or.inr (Or.inl hx))
        · exact hfix _ (Or.inr (Or.inr (by omega)))
      · intro x hx hxR hxD
        have hxn : x ≠ n := fun h => hxR (h ▸ mem_insert_self _ _)
        have hxR' : x ∉ R := fun h => hxR (mem_insert_of_mem h)
        obtain ⟨h1, h2, h3, h4⟩ := hpair x (by omega) hxR' hxD
        exact ⟨h1, by omega, h3, h4⟩
    · have hrs : U ∩ range (n + 1) = U ∩ range n := by
        rw [range_add_one, inter_insert_of_notMem hn]
      by_cases hRe : R.Nonempty
      · obtain ⟨r, hr⟩ := hRe
        have hrn : r < n := hRlt r hr
        have hrU : r ∈ U := (mem_inter.1 (hR hr)).1
        have hpr : p r = r := hfix r (Or.inl hr)
        refine ⟨fun x => if x = r then n else if x = n then r else p x, R.erase r, D,
          ?_, ?_, hD1, ?_, ?_, ?_⟩
        · rw [hrs]; exact (erase_subset _ _).trans hR
        · exact hD.trans (sdiff_subset_sdiff (range_mono (Nat.le_succ n)) (subset_refl U))
        · rw [hrs, card_erase_of_mem hr]
          have : 0 < R.card := card_pos.2 ⟨r, hr⟩
          omega
        · intro x hx
          have hxr : x ≠ r := by
            rcases hx with hx | hx | hx
            · exact ne_of_mem_erase hx
            · exact fun h => hRD r hr (h ▸ hx)
            · omega
          have hxn : x ≠ n := by
            rcases hx with hx | hx | hx
            · have := hRlt x (mem_of_mem_erase hx); omega
            · have := hDlt x hx; omega
            · omega
          simp only [hxr, hxn, if_false]
          rcases hx with hx | hx | hx
          · exact hfix x (Or.inl (mem_of_mem_erase hx))
          · exact hfix x (Or.inr (Or.inl hx))
          · exact hfix x (Or.inr (Or.inr (by omega)))
        · intro x hx hxR hxD
          by_cases hxr : x = r
          · subst hxr
            simp only [if_true, show n ≠ x by omega, if_false]
            exact ⟨by omega, by omega, by simp, fun _ => ⟨hrU, hn⟩⟩
          by_cases hxn : x = n
          · subst hxn
            simp only [hxr, if_false, if_true]
            exact ⟨by omega, by omega, by simp, fun h => by omega⟩
          have hxR' : x ∉ R := fun h => hxR (mem_erase.2 ⟨hxr, h⟩)
          obtain ⟨h1, h2, h3, h4⟩ := hpair x (by omega) hxR' hxD
          have hpxr : p x ≠ r := fun h => by
            rw [h, hpr] at h3; exact hxr h3.symm
          have hpxn : p x ≠ n := by omega
          simp only [hxr, hxn, hpxr, hpxn, if_false]
          exact ⟨h1, by omega, h3, h4⟩
      · have hR0 : R = ∅ := not_nonempty_iff_eq_empty.1 hRe
        subst hR0
        rw [hrs] at hlast
        have hD0 : D = ∅ := by
          rw [← card_eq_zero]; simp at hcard; omega
        subst hD0
        refine ⟨p, ∅, {n}, by simp, ?_, by simp, ?_, ?_, ?_⟩
        · intro x hx
          rw [mem_singleton.1 hx]; simp [hn]
        · rw [hrs]; simp at hcard ⊢; omega
        · intro x hx
          simp only [notMem_empty, mem_singleton, false_or] at hx
          rcases hx with rfl | hx
          · exact hfix _ (Or.inr (Or.inr le_rfl))
          · exact hfix _ (Or.inr (Or.inr (by omega)))
        · intro x hx _ hxD
          have hxn : x ≠ n := fun h => hxD (mem_singleton.2 h)
          obtain ⟨h1, h2, h3, h4⟩ := hpair x (by omega) (notMem_empty x) (notMem_empty x)
          exact ⟨h1, by omega, h3, h4⟩

/-- Any finite set of even cardinality can be split into pairs. -/
theorem exists_pairing (S : Finset ℕ) (hS : Even S.card) : ∃ q : ℕ → ℕ,
    (∀ x ∈ S, q x ∈ S ∧ q x ≠ x ∧ q (q x) = x) ∧ (∀ x ∉ S, q x = x) := by
  obtain ⟨j, hj⟩ := hS
  induction j generalizing S with
  | zero =>
    have : S = ∅ := card_eq_zero.1 (by omega)
    subst this
    exact ⟨id, by simp, fun _ _ => rfl⟩
  | succ j ih =>
    have hpos : 0 < S.card := by omega
    obtain ⟨a, ha⟩ := card_pos.1 hpos
    have h1 : (S.erase a).card = 2 * j + 1 := by rw [card_erase_of_mem ha]; omega
    obtain ⟨b, hb⟩ := card_pos.1 (show 0 < (S.erase a).card by omega)
    have h2 : ((S.erase a).erase b).card = j + j := by rw [card_erase_of_mem hb]; omega
    obtain ⟨q, hq1, hq2⟩ := ih _ h2
    have hba : b ≠ a := ne_of_mem_erase hb
    have hbS : b ∈ S := mem_of_mem_erase hb
    refine ⟨fun x => if x = a then b else if x = b then a else q x, ?_, ?_⟩
    · intro x hx
      by_cases hxa : x = a
      · subst hxa; simp [hba, hbS]
      by_cases hxb : x = b
      · subst hxb; simp [hba, ha, Ne.symm hba]
      have hx2 : x ∈ (S.erase a).erase b := mem_erase.2 ⟨hxb, mem_erase.2 ⟨hxa, hx⟩⟩
      obtain ⟨hqa, hqb, hqc⟩ := hq1 x hx2
      have hqxa : q x ≠ a := fun h => by
        have := mem_erase.1 (mem_of_mem_erase hqa); exact this.1 h
      have hqxb : q x ≠ b := fun h => (mem_erase.1 hqa).1 h
      simp only [hxa, hxb, hqxa, hqxb, if_false]
      exact ⟨mem_of_mem_erase (mem_of_mem_erase hqa), hqb, hqc⟩
    · intro x hx
      have hxa : x ≠ a := fun h => hx (h ▸ ha)
      have hxb : x ≠ b := fun h => hx (h ▸ hbS)
      simp only [hxa, hxb, if_false]
      exact hq2 x (fun h => hx (mem_of_mem_erase (mem_of_mem_erase h)))

/-- Step (ii) of `q3_ballot_lower_bound.md`, combinatorial part: for a ballot set `U` of odd
length `n`, there is a special element `c` (the partner of `0`) and a pairing `π` of the
remaining positions `< n` such that the smaller element of each pair lies in `U`. -/
theorem exists_matching_of_isBallot (n : ℕ) (U : Finset ℕ) (hU : IsBallot n U) (hn : Odd n) :
    ∃ c < n, ∃ π : ℕ → ℕ, π c = c ∧
      ∀ x < n, x ≠ c → π x ≠ x ∧ π x < n ∧ π (π x) = x ∧ (x < π x → x ∈ U) := by
  obtain ⟨p, R, D, hR, hD, hD1, hcard, hfix, hpair⟩ := greedy_matching U n hU
  obtain ⟨k, rfl⟩ := hn
  have key : ∃ c, (c ∈ R ∨ c ∈ D) ∧ (∀ x ∈ D, x = c) ∧ Even (R.erase c).card := by
    by_cases hDe : D.Nonempty
    · obtain ⟨c, hc⟩ := hDe
      have hcR : c ∉ R := fun h => (mem_sdiff.1 (hD hc)).2 (mem_inter.1 (hR h)).1
      have hDc : D.card = 1 := by have := card_pos.2 ⟨c, hc⟩; omega
      refine ⟨c, Or.inr hc, fun x hx => ?_, ?_⟩
      · obtain ⟨z, hz⟩ := card_eq_one.1 hDc
        rw [hz] at hx hc; rw [mem_singleton.1 hx, mem_singleton.1 hc]
      · rw [erase_eq_of_notMem hcR]
        exact ⟨(U ∩ range (2 * k + 1)).card - k, by omega⟩
    · have hD0 : D = ∅ := not_nonempty_iff_eq_empty.1 hDe
      subst hD0
      simp only [card_empty] at hcard
      obtain ⟨c, hc⟩ := card_pos.1 (show 0 < R.card by omega)
      refine ⟨c, Or.inl hc, by simp, ?_⟩
      rw [card_erase_of_mem hc]
      exact ⟨(U ∩ range (2 * k + 1)).card - k - 1, by omega⟩
  obtain ⟨c, hc, hDc, hev⟩ := key
  obtain ⟨q, hq1, hq2⟩ := exists_pairing _ hev
  have hRlt : ∀ x ∈ R, x < 2 * k + 1 := fun x hx => mem_range.1 (mem_inter.1 (hR hx)).2
  have hRU : ∀ x ∈ R, x ∈ U := fun x hx => (mem_inter.1 (hR hx)).1
  have hclt : c < 2 * k + 1 := by
    rcases hc with hc | hc
    · exact hRlt c hc
    · exact mem_range.1 (mem_sdiff.1 (hD hc)).1
  refine ⟨c, hclt, fun x => if x ∈ R.erase c then q x else p x, ?_, ?_⟩
  · simp only [notMem_erase, if_false]
    exact hfix c (by tauto)
  · intro x hx hxc
    by_cases hxR : x ∈ R.erase c
    · obtain ⟨h1, h2, h3⟩ := hq1 x hxR
      simp only [hxR, h1, if_true]
      exact ⟨h2, hRlt _ (mem_of_mem_erase h1), h3, fun _ => hRU x (mem_of_mem_erase hxR)⟩
    · have hxR' : x ∉ R := fun h => hxR (mem_erase.2 ⟨hxc, h⟩)
      have hxD : x ∉ D := fun h => hxc (hDc x h)
      obtain ⟨h1, h2, h3, h4⟩ := hpair x hx hxR' hxD
      have hpR : p x ∉ R.erase c := fun h => by
        have := hfix (p x) (Or.inl (mem_of_mem_erase h))
        rw [h3] at this; exact h1 this.symm
      simp only [hxR, hpR, if_false]
      exact ⟨h1, h2, h3, fun h => (h4 h).1⟩

/-- The number of ballot sets of length `n` and size `u` (used in step (iii)). -/
def ballotCount (n u : ℕ) : ℕ := ((ballotSets n).filter (fun U => U.card = u)).card

/-- The count of step (iii) of `q3_ballot_lower_bound.md` written as a sum over all subsets. -/
lemma ballotCount_eq_sum (n u : ℕ) : ballotCount n u =
    ∑ U ∈ (range n).powerset, if IsBallot n U ∧ U.card = u then 1 else 0 := by
  unfold ballotCount ballotSets
  rw [filter_filter, card_filter]

/-- Step (iii) of `q3_ballot_lower_bound.md`: appending a down-step to a ballot path keeps it a ballot path iff the new height is `≥ −1`. -/
lemma isBallot_succ_of_subset {n : ℕ} {U : Finset ℕ} (hU : U ⊆ range n) :
    IsBallot (n + 1) U ↔ IsBallot n U ∧ n ≤ 2 * U.card := by
  rw [isBallot_succ, inter_eq_left.2 (hU.trans (range_mono (Nat.le_succ n)))]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩

/-- Step (iii) of `q3_ballot_lower_bound.md`: appending an up-step to a ballot path keeps it a ballot path. -/
lemma isBallot_insert {n : ℕ} {U : Finset ℕ} (hU : U ⊆ range n) :
    IsBallot (n + 1) (insert n U) ↔ IsBallot n U := by
  have hnU : n ∉ U := fun h => by simpa using hU h
  have hi' : ∀ i ≤ n, insert n U ∩ range i = U ∩ range i := by
    intro i hi
    rw [insert_inter_of_notMem (by simp; omega)]
  have hn : IsBallot n (insert n U) ↔ IsBallot n U := by
    constructor
    · intro h i hi; have := h i hi; rwa [hi' i hi] at this
    · intro h i hi; have := h i hi; rwa [hi' i hi]
  rw [isBallot_succ, hn]
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, ?_⟩
    have h1 := h n le_rfl
    rw [inter_eq_left.2 hU] at h1
    rw [inter_eq_left.2 (insert_subset (by simp) (hU.trans (range_mono (Nat.le_succ n)))),
      card_insert_of_notMem hnU]
    omega

/-- Step (iii) of `q3_ballot_lower_bound.md`: recursion for the number of ballot paths with `u` up-steps, obtained by splitting on the last step. -/
lemma ballotCount_succ (n u : ℕ) : ballotCount (n + 1) u =
    (if n ≤ 2 * u then ballotCount n u else 0) + (if u = 0 then 0 else ballotCount n (u - 1)) := by
  rw [ballotCount_eq_sum, range_add_one, sum_powerset_insert notMem_range_self]
  congr 1
  · split_ifs with h
    · rw [ballotCount_eq_sum]
      refine sum_congr rfl fun U hU => ?_
      simp only [isBallot_succ_of_subset (mem_powerset.1 hU)]
      refine if_congr ?_ rfl rfl
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨⟨h1, by omega⟩, h3⟩
    · refine sum_eq_zero fun U hU => ?_
      simp only [isBallot_succ_of_subset (mem_powerset.1 hU)]
      rw [if_neg]
      rintro ⟨⟨_, h2⟩, h3⟩; omega
  · have hnU : ∀ U ∈ (range n).powerset, n ∉ U := fun U hU h => by
      simpa using mem_powerset.1 hU h
    split_ifs with h
    · refine sum_eq_zero fun U hU => ?_
      rw [if_neg]
      rintro ⟨_, h3⟩
      rw [card_insert_of_notMem (hnU U hU)] at h3; omega
    · rw [ballotCount_eq_sum]
      refine sum_congr rfl fun U hU => ?_
      simp only [isBallot_insert (mem_powerset.1 hU), card_insert_of_notMem (hnU U hU)]
      refine if_congr ?_ rfl rfl
      constructor
      · rintro ⟨h1, h3⟩; exact ⟨h1, by omega⟩
      · rintro ⟨h1, h3⟩; exact ⟨h1, by omega⟩

/-- Step (iii) of `q3_ballot_lower_bound.md`, refined by size:
`#{U ∈ 𝓤 : |U| = u} = binomial(n, u) − binomial(n, u + 2)` if `2u + 1 ≥ n`, and `0` otherwise. -/
theorem ballotCount_formula (n u : ℕ) : (ballotCount n u : ℤ) =
    if n ≤ 2 * u + 1 then (n.choose u : ℤ) - n.choose (u + 2) else 0 := by
  induction n generalizing u with
  | zero =>
    have h0 : IsBallot 0 ∅ := fun i hi => by omega
    rw [ballotCount_eq_sum, range_zero, powerset_empty, sum_singleton]
    rcases u with _ | u
    · simp [h0]
    · simp
  | succ n ih =>
    rw [ballotCount_succ]
    rcases u with _ | u
    · simp only [Nat.cast_add, Nat.cast_ite, Nat.cast_zero]
      rcases n with _ | n
      · simp only [le_refl, if_true, ih]
        simp
      · simp
    · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, Nat.add_sub_cancel,
        Nat.cast_add, Nat.cast_ite, Nat.cast_zero, ih]
      have p1 := Nat.choose_succ_succ' n u
      have p2 := Nat.choose_succ_succ' n (u + 2)
      have e1 : (n + 1).choose (u + 1 + 2) = (n + 1).choose (u + 2 + 1) := rfl
      have e2 : n.choose (u + 1 + 2) = n.choose (u + 2 + 1) := rfl
      have hs : n = u + (u + 2) → n.choose u = n.choose (u + 2) := Nat.choose_symm_of_eq_add
      rw [e1, e2, p1, p2]
      push_cast
      split_ifs <;> omega

/-- Step (iii) of `q3_ballot_lower_bound.md`: the telescoping sum `∑_{u ≥ k} (binomial(n', u) − binomial(n', u + 2))`. -/
lemma sum_telescope_two (b : ℕ → ℤ) (k : ℕ) : ∀ j : ℕ,
    ∑ u ∈ range (k + j), (if k ≤ u then b u - b (u + 2) else 0) =
      b k + b (k + 1) - b (k + j) - b (k + j + 1) := by
  intro j
  induction j with
  | zero =>
    simp only [add_zero]
    rw [sum_eq_zero fun u hu => if_neg (by simp at hu; omega)]
    ring
  | succ j ih =>
    rw [← add_assoc, sum_range_succ, ih, if_pos (by omega)]
    ring_nf

/-- Step (iii) of `q3_ballot_lower_bound.md`: `|𝓤| = binomial(2k + 2, k + 1)`. -/
theorem card_ballotSets (k : ℕ) : (ballotSets (2 * k + 1)).card = (2 * k + 2).choose (k + 1) := by
  have hfib := card_eq_sum_card_fiberwise (f := Finset.card) (t := range (2 * k + 2))
    (s := ballotSets (2 * k + 1)) (fun U hU => by
      simp only [ballotSets, coe_filter, Set.mem_setOf_eq, mem_powerset] at hU
      have h1 := hU.1
      have h2 := card_le_card h1
      simp only [card_range] at h2
      exact mem_range.2 (by omega))
  have key : ((ballotSets (2 * k + 1)).card : ℤ) = ((2 * k + 2).choose (k + 1) : ℤ) := by
    rw [hfib]
    push_cast
    change ∑ u ∈ range (2 * k + 2), (ballotCount (2 * k + 1) u : ℤ) = _
    simp_rw [ballotCount_formula]
    rw [show 2 * k + 2 = k + (k + 2) by ring]
    rw [sum_congr rfl (g := fun u => if k ≤ u then (((2 * k + 1).choose u : ℕ) : ℤ) -
      ((2 * k + 1).choose (u + 2) : ℕ) else 0) (fun u _ => by
        simp only
        exact if_congr (by omega) rfl rfl)]
    rw [sum_telescope_two (fun u => (((2 * k + 1).choose u : ℕ) : ℤ)) k (k + 2)]
    rw [Nat.choose_eq_zero_of_lt (by omega : 2 * k + 1 < k + (k + 2)),
      Nat.choose_eq_zero_of_lt (by omega : 2 * k + 1 < k + (k + 2) + 1),
      show k + (k + 2) = (2 * k + 1) + 1 by ring, Nat.choose_succ_succ' (2 * k + 1) k]
    push_cast
    ring
  exact_mod_cast key

end BallotBound

end

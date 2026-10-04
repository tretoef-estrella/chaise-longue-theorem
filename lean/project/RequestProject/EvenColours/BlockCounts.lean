module

public import RequestProject.EvenColours.Blocks

/-!
# The block counts (`q_even_count_colours.md`, proof of (C2))

* `EvenColours.card_good_self`: on a class `𝒞_ζ` of a self-inverse colour `ζ`, the number of good
  tuples is `NS S ζ |𝒞_ζ|` (on `𝒞_1` the entries are `(w, 1)` with `w ≠ 0`; otherwise they are
  `(w, ζ)` with `w` arbitrary);
* `EvenColours.card_good_pair`: on `𝒞_ζ ∪ 𝒞_{ζ^{−1}}` (`ζ^{−1} ≠ ζ`, `|𝒞_ζ| = |𝒞_{ζ^{−1}}| = a`),
  the number of good tuples is `Bip.Nbal a q`.
-/

@[expose] public section

namespace EvenColours

open ColSplit ColSurv ColComp Fibres TheoremB EvenBlocks

open scoped Classical

variable {F : Type*} [Field F] {S : ColSetting F}

/-- **(C2)** of `q_even_count_colours.md` (proof, the class of a self-inverse colour `ζ ≠ 1`): on
an index set where all colours are `ζ`, with `ζ^{−1} = ζ` and `ζ ≠ 1`, good tuples are the
closed tuples of `(Om S, w ↦ −w)` (after an enumeration). -/
theorem card_good_self_ne_one {X : Type*} [Fintype X] [DecidableEq X] (κ : X → F) {ζ : F}
    (hκ : ∀ j, κ j = ζ) (hζ : ζ⁻¹ = ζ) (h1 : ζ ≠ 1) :
    (Finset.univ.filter (Good S κ)).card =
      (closedT (fun w : Om S => -w) (Fintype.card X)).card := by
  let e : X ≃ Fin (Fintype.card X) := Fintype.equivFin X
  have hne : ∀ (f : X → Om S) (w : Om S) (ζ' : F), ζ' ≠ ζ →
      (Finset.univ.filter fun j => f j = w ∧ κ j = ζ').card = 0 := by
    intro f w ζ' h
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro j _ hj
    exact h (hj.2.symm.trans (hκ j))
  have hcnt : ∀ (f : X → Om S) (w : Om S),
      (Finset.univ.filter fun j => f j = w ∧ κ j = ζ).card = cnt (fun i => f (e.symm i)) w := by
    intro f w
    unfold cnt
    refine Eq.trans ?_ (ColCount.card_filter_equiv e.symm (fun j => f j = w)).symm
    congr 1
    ext j
    simp [hκ j]
  have hgood : ∀ f : X → Om S,
      Good S κ f ↔ (fun i => f (e.symm i)) ∈ closedT (fun w : Om S => -w) (Fintype.card X) := by
    intro f
    simp only [closedT, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_, h2, h3⟩
      refine ⟨fun w => ?_, fun w hw => ?_⟩
      · have := h2 w ζ
        rw [hζ, hcnt, hcnt] at this
        exact this
      · have := h3 w ζ hw hζ
        rwa [hcnt] at this
    · rintro ⟨h2, h3⟩
      refine ⟨fun j hj => absurd ((hκ j).symm.trans hj) h1, fun w ζ' => ?_, fun w ζ' hw _ => ?_⟩
      · by_cases hz : ζ' = ζ
        · subst hz
          rw [hζ, hcnt, hcnt]
          exact h2 w
        · have hz' : ζ'⁻¹ ≠ ζ := by
            intro h
            have h' := congrArg Inv.inv h
            rw [inv_inv, hζ] at h'
            exact hz h'
          rw [hne _ _ _ hz, hne _ _ _ hz']
      · by_cases hz : ζ' = ζ
        · subst hz
          rw [hcnt]
          exact h3 w hw
        · rw [hne _ _ _ hz]
          exact Even.zero
  let E : (X → Om S) ≃ (Fin (Fintype.card X) → Om S) := e.arrowCongr (Equiv.refl _)
  have hE : ∀ f, E f = fun i => f (e.symm i) := fun f => rfl
  have hset : Finset.univ.filter (Good S κ) =
      Finset.univ.filter (fun f => E f ∈ closedT (fun w : Om S => -w) (Fintype.card X)) :=
    Finset.filter_congr (fun f _ => by rw [hE]; exact hgood f)
  rw [hset, ColCount.card_filter_equiv E (fun M => M ∈ closedT (fun w : Om S => -w) _),
    Finset.filter_mem_eq_inter, Finset.univ_inter]

/-- **(C2)** of `q_even_count_colours.md` (proof, the class `𝒞_1`): on an index set where all
colours are `1`, good tuples are the closed tuples of `({w : Om S // w ≠ 0}, w ↦ −w)` (after an
enumeration). -/
theorem card_good_self_one {X : Type*} [Fintype X] [DecidableEq X] (κ : X → F)
    (hκ : ∀ j, κ j = 1) :
    (Finset.univ.filter (Good S κ)).card = (closedT (negW S) (Fintype.card X)).card := by
  let e : X ≃ Fin (Fintype.card X) := Fintype.equivFin X
  have hne1 : ∀ (f : X → Om S) (w : Om S) (ζ : F), ζ ≠ 1 →
      (Finset.univ.filter fun j => f j = w ∧ κ j = ζ).card = 0 := by
    intro f w ζ hζ
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro j _ hj
    exact hζ (hj.2.symm.trans (hκ j))
  have hzero : ∀ (M : Fin (Fintype.card X) → {w : Om S // w ≠ 0}) (ζ : F),
      (Finset.univ.filter fun j => (M (e j)).1 = 0 ∧ κ j = ζ).card = 0 := by
    intro M ζ
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro j _ hj
    exact (M (e j)).2 hj.1
  have hsome : ∀ (M : Fin (Fintype.card X) → {w : Om S // w ≠ 0}) (u : {w : Om S // w ≠ 0}),
      (Finset.univ.filter fun j => (M (e j)).1 = u.1 ∧ κ j = 1).card = cnt M u := by
    intro M u
    unfold cnt
    refine Eq.trans ?_ (ColCount.card_filter_equiv e (fun i => M i = u))
    congr 1
    ext j
    simp [hκ j, Subtype.ext_iff]
  have hgood : ∀ M : Fin (Fintype.card X) → {w : Om S // w ≠ 0},
      Good S κ (fun j => (M (e j)).1) ↔ M ∈ closedT (negW S) (Fintype.card X) := by
    intro M
    simp only [closedT, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_, h2, h3⟩
      refine ⟨fun u => ?_, fun u hu => ?_⟩
      · have h := h2 u.1 1
        rw [inv_one] at h
        exact (hsome M u).symm.trans (h.trans (hsome M (negW S u)))
      · have h := h3 u.1 1 (congrArg Subtype.val hu) inv_one
        rwa [hsome] at h
    · rintro ⟨h2, h3⟩
      refine ⟨fun j _ => (M (e j)).2, fun w ζ => ?_, fun w ζ hw _ => ?_⟩
      · by_cases hζ : ζ = 1
        · subst hζ
          rw [inv_one]
          by_cases hw : w = 0
          · subst hw
            rw [neg_zero]
          · have a := hsome M ⟨w, hw⟩
            have b := hsome M (negW S ⟨w, hw⟩)
            exact a.trans ((h2 ⟨w, hw⟩).trans b.symm)
        · rw [hne1 _ _ _ hζ, hne1 _ _ _ (fun h' => hζ (inv_eq_one.1 h'))]
      · by_cases hζ : ζ = 1
        · subst hζ
          by_cases hw0 : w = 0
          · subst hw0
            rw [hzero]
            exact Even.zero
          · have a := hsome M ⟨w, hw0⟩
            rw [a]
            exact h3 ⟨w, hw0⟩ (Subtype.ext hw)
        · rw [hne1 _ _ _ hζ]
          exact Even.zero
  symm
  refine Finset.card_bij (fun M _ => fun j => (M (e j)).1) ?_ ?_ ?_
  · intro M hM
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, (hgood M).2 hM⟩
  · intro M1 _ M2 _ hM
    funext i
    have := congrFun hM (e.symm i)
    simp only [Equiv.apply_symm_apply] at this
    exact Subtype.ext this
  · intro f hf
    rw [Finset.mem_filter] at hf
    have hs : ∀ i, f (e.symm i) ≠ 0 := fun i => hf.2.1 _ (hκ _)
    let M : Fin (Fintype.card X) → {w : Om S // w ≠ 0} := fun i => ⟨f (e.symm i), hs i⟩
    have hfM : (fun j => (M (e j)).1) = f := by
      funext j
      simp [M]
    refine ⟨M, ?_, hfM⟩
    rw [← hgood, hfM]
    exact hf.2

/-- **(C2)** of `q_even_count_colours.md` (proof, the class `𝒞_ζ` of a self-inverse colour): on an
index set where all colours are `ζ`, with `ζ^{−1} = ζ`, the number of good tuples is
`NS S ζ |X|`. -/
theorem card_good_self {X : Type*} [Fintype X] [DecidableEq X] (κ : X → F) {ζ : F}
    (hκ : ∀ j, κ j = ζ) (hζ : ζ⁻¹ = ζ) :
    (Finset.univ.filter (Good S κ)).card = NS S ζ (Fintype.card X) := by
  unfold NS
  split_ifs with h1
  · subst h1
    exact card_good_self_one κ hκ
  · exact card_good_self_ne_one κ hκ hζ h1

/-- **(C2)** of `q_even_count_colours.md` (proof, the blocks `𝒞_ζ ∪ 𝒞_{ζ^{−1}}`): on an index set
coloured by `ζ` (`a` times) and `ζ^{−1}` (`a` times), with `ζ^{−1} ≠ ζ`, the number of good tuples
is `N_{bal}(a, q)` (the multiset of the `w` on `𝒞_ζ` equals the multiset of the `−w` on
`𝒞_{ζ^{−1}}`); model: `ColCount.card_good_pair`, without the hypothesis `p ≠ 2`. -/
theorem card_good_pair {X : Type*} [Fintype X] [DecidableEq X] (κ : X → F) {ζ : F} {a : ℕ}
    (hinv : ζ⁻¹ ≠ ζ) (hX : ∀ j, κ j = ζ ∨ κ j = ζ⁻¹)
    (ha : (Finset.univ.filter fun j => κ j = ζ).card = a)
    (hb : (Finset.univ.filter fun j => κ j = ζ⁻¹).card = a) :
    (Finset.univ.filter (Good S κ)).card = Bip.Nbal a S.q := by
  have h1 : ζ ≠ 1 := by
    rintro rfl
    exact hinv inv_one
  have hne : ζ⁻¹ ≠ 1 := fun h' => h1 (inv_eq_one.1 h')
  have hiff : ∀ f : X → Om S, Good S κ f ↔
      ∀ w, (Finset.univ.filter fun j => f j = w ∧ κ j = ζ).card =
        (Finset.univ.filter fun j => f j = -w ∧ κ j = ζ⁻¹).card := by
    intro f
    have hzero : ∀ (w : Om S) (ζ' : F), ζ' ≠ ζ → ζ' ≠ ζ⁻¹ →
        (Finset.univ.filter fun j => f j = w ∧ κ j = ζ').card = 0 := by
      intro w ζ' hz hz'
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro j _ hj
      rcases hX j with h | h
      · exact hz (hj.2.symm.trans h)
      · exact hz' (hj.2.symm.trans h)
    constructor
    · exact fun hf w => hf.2.1 w ζ
    · intro hf
      refine ⟨fun j hj => ?_, fun w ζ' => ?_, fun w ζ' _ hζ' => ?_⟩
      · rcases hX j with h | h
        · exact absurd (h.symm.trans hj) h1
        · exact absurd (h.symm.trans hj) hne
      · by_cases hz : ζ' = ζ
        · subst hz
          exact hf w
        · by_cases hz' : ζ' = ζ⁻¹
          · subst hz'
            rw [inv_inv]
            have := hf (-w)
            rw [neg_neg] at this
            exact this.symm
          · have hz2 : ζ'⁻¹ ≠ ζ := fun h => hz' (by rw [← h, inv_inv])
            have hz3 : ζ'⁻¹ ≠ ζ⁻¹ := fun h => hz (inv_injective h)
            rw [hzero w ζ' hz hz', hzero (-w) ζ'⁻¹ hz2 hz3]
      · have hz : ζ' ≠ ζ := by
          rintro rfl
          exact hinv hζ'
        have hz' : ζ' ≠ ζ⁻¹ := by
          rintro rfl
          rw [inv_inv] at hζ'
          exact hinv hζ'.symm
        rw [hzero w ζ' hz hz']
        exact Even.zero
  have hcardA : Fintype.card {j // κ j = ζ} = a := by rw [Fintype.card_subtype]; exact ha
  have hcardB : Fintype.card {j // κ j = ζ⁻¹} = a := by rw [Fintype.card_subtype]; exact hb
  let eA : {j // κ j = ζ} ≃ Fin a := Fintype.equivFinOfCardEq hcardA
  let eB : {j // κ j = ζ⁻¹} ≃ Fin a := Fintype.equivFinOfCardEq hcardB
  let eΩ : Om S ≃ Fin S.q := Fintype.equivFinOfCardEq (ZMod.card S.q)
  have hcnt1 : ∀ (f : X → Om S) (u : Om S), Bip.cnt (fun t => f (eA.symm t).1) u =
      (Finset.univ.filter fun j => f j = u ∧ κ j = ζ).card := by
    intro f u
    unfold Bip.cnt
    refine (ColCount.card_filter_equiv eA.symm (fun s => f s.1 = u)).trans ?_
    refine (ColCount.card_filter_subtype (fun j => κ j = ζ) (fun j => f j = u)).trans ?_
    congr 1
    ext j
    simp [and_comm]
  have hcnt2 : ∀ (f : X → Om S) (u : Om S), Bip.cnt (fun t => -(f (eB.symm t).1)) u =
      (Finset.univ.filter fun j => f j = -u ∧ κ j = ζ⁻¹).card := by
    intro f u
    unfold Bip.cnt
    refine (ColCount.card_filter_equiv eB.symm (fun s => -(f s.1) = u)).trans ?_
    refine (ColCount.card_filter_subtype (fun j => κ j = ζ⁻¹) (fun j => -(f j) = u)).trans ?_
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [neg_eq_iff_eq_neg, and_comm]
  let i : (X → Om S) → (Fin a → Om S) × (Fin a → Om S) := fun f =>
    (fun t => f (eA.symm t).1, fun t => -(f (eB.symm t).1))
  let jm : (Fin a → Om S) × (Fin a → Om S) → (X → Om S) := fun p x =>
    if hx : κ x = ζ then p.1 (eA ⟨x, hx⟩) else -(p.2 (eB ⟨x, (hX x).resolve_left hx⟩))
  have hkey : ∀ f, (∀ u, Bip.cnt (i f).1 u = Bip.cnt (i f).2 u) ↔ Good S κ f := by
    intro f
    rw [hiff f]
    exact forall_congr' fun u => by rw [← hcnt1 f u, ← hcnt2 f u]
  have hji : ∀ f, jm (i f) = f := by
    intro f
    funext x
    by_cases hx : κ x = ζ
    · simp [jm, i, hx]
    · simp [jm, i, hx]
  have hij : ∀ p, i (jm p) = p := by
    intro p
    refine Prod.ext (funext fun t => ?_) (funext fun t => ?_)
    · have : κ (eA.symm t).1 = ζ := (eA.symm t).2
      simp [i, jm, this]
    · have : ¬ κ (eB.symm t).1 = ζ := by rw [(eB.symm t).2]; exact hinv
      simp [i, jm, this]
  calc (Finset.univ.filter (Good S κ)).card =
      (Finset.univ.filter fun p : (Fin a → Om S) × (Fin a → Om S) =>
        ∀ u, Bip.cnt p.1 u = Bip.cnt p.2 u).card := by
        refine Finset.card_bij' (fun f _ => i f) (fun p _ => jm p) ?_ ?_ ?_ ?_
        · intro f hf
          rw [Finset.mem_filter] at hf ⊢
          exact ⟨Finset.mem_univ _, (hkey f).2 hf.2⟩
        · intro p hp
          rw [Finset.mem_filter] at hp ⊢
          refine ⟨Finset.mem_univ _, (hkey (jm p)).1 ?_⟩
          rw [hij p]
          exact hp.2
        · intro f _
          exact hji f
        · intro p _
          exact hij p
    _ = Bip.Nbal a S.q := by
        rw [Bip.Nbal]
        convert Bip.card_filter_cnt_equiv eΩ (fun m n => m = n) a a using 2
        ext p
        simp

end EvenColours

end

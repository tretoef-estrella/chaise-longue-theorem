module

public import RequestProject.ColCount.Colours

/-!
# The blocks of the count (`q_col_count.md`, Proof of Lemma 6.8 (ii), *The blocks*)

A tuple `g ∈ T_m^n` with a prescribed colour tuple `κ` is determined by `ω(g) = (g_i.1)_i ∈ Ω_q^n`;
closedness of `g` becomes a condition `Good κ ω` on `ω`, which splits along the partition of the
index set into `𝒞_1` and the sets `𝒞_ζ ∪ 𝒞_{ζ^{−1}}` (`ζ ∈ ℛ`) of Lemma 6.3 (i).
-/

@[expose] public section

namespace ColCount

open ColSplit ColSurv ColComp Fibres TheoremB

open scoped Classical

variable {F : Type*} [Field F] {S : ColSetting F}

variable (S) in
/-- **Proof of Lemma 6.8 (ii)** of `q_col_count.md` (*the blocks*): for a colour tuple `κ` on an
index set `X`, the condition on `ω ∈ Ω_q^X` for the tuple `(ω_i, κ_i)_i` to be a closed tuple of
`T_m`: `ω_i ≠ ∗` whenever `κ_i = 1`, and `cnt(g, (w, ζ)) = cnt(g, (w̄, ζ^{−1}))` for all `w`, `ζ`. -/
def Good {X : Type*} [Fintype X] (κ : X → F) (f : X → Om S) : Prop :=
  (∀ j, κ j = 1 → f j ≠ none) ∧
    ∀ (w : Om S) (ζ : F), (Finset.univ.filter fun j => f j = w ∧ κ j = ζ).card =
      (Finset.univ.filter fun j => f j = bar S w ∧ κ j = ζ⁻¹).card

/-- Counting in a subtype (auxiliary for the **Proof of Lemma 6.8 (ii)** of `q_col_count.md`). -/
theorem card_filter_subtype {X : Type*} [Fintype X] (p P : X → Prop) [DecidablePred p]
    [DecidablePred P] :
    (Finset.univ.filter fun j : {x // p x} => P j.1).card =
      (Finset.univ.filter fun x => p x ∧ P x).card := by
  refine Finset.card_bij (fun j _ => j.1) ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact ⟨j.2, hj⟩
  · intro a _ b _ h
    exact Subtype.ext h
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact ⟨⟨x, hx.1⟩, by simp [hx.2], rfl⟩

/-- **Proof of Lemma 6.8 (ii)** of `q_col_count.md`: in a tuple `g` with colour tuple `κ`,
`cnt(g, (w, ζ)) = #{i : ω(g)_i = w, κ_i = ζ}`. -/
theorem cnt_eq_of_col {n : ℕ} {g : Fin n → Tm S} {κ : Fin n → F}
    (hcol : ∀ j, ((g j).1.2 : F) = κ j) (u : Tm S) :
    cnt g u = (Finset.univ.filter fun j => (g j).1.1 = u.1.1 ∧ κ j = (u.1.2 : F)).card := by
  unfold cnt
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, ← hcol j]
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    exact Subtype.ext (Prod.ext h1 (Subtype.ext h2))

/-- **Proof of Lemma 6.8 (ii)** of `q_col_count.md` (*the blocks*): the number of closed tuples of
`T_m` with colour tuple `κ ∈ μ^n` equals the number of `ω ∈ Ω_q^n` with `Good κ ω` (a tuple `g`
with `κ(g) = κ` is determined by `ω(g)`). -/
theorem card_col_eq_card_good (hp : S.p ≠ 2) (hr : Odd S.r) {n : ℕ} (κ : Fin n → F)
    (hκ : ∀ i, κ i ∈ S.μ) :
    ((closedTuples (TmSetting S hp hr) n).filter fun g => ∀ i, ((g i).1.2 : F) = κ i).card =
      (Finset.univ.filter (Good S κ)).card := by
  symm
  refine Finset.card_bij (fun ω hω i => (⟨(ω i, ⟨κ i, hκ i⟩), fun h =>
      (Finset.mem_filter.1 hω).2.1 i (congrArg Subtype.val (Prod.mk.inj h).2)
        (Prod.mk.inj h).1⟩ : Tm S)) ?_ ?_ ?_
  · intro ω hω
    have hG := (Finset.mem_filter.1 hω).2
    simp only [closedTuples, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun u => ?_, fun _ => trivial⟩
    rw [cnt_eq_of_col (fun j => rfl) u, cnt_eq_of_col (fun j => rfl)]
    exact hG.2 u.1.1 u.1.2
  · intro ω1 _ ω2 _ h
    funext i
    exact congrArg (fun g : Fin n → Tm S => (g i).1.1) h
  · intro g hg
    simp only [closedTuples, Finset.mem_filter, Finset.mem_univ, true_and] at hg
    obtain ⟨hclosed, hcol⟩ := hg
    refine ⟨fun i => (g i).1.1, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, fun j hj hn => ?_, fun w ζ => ?_⟩
      · apply (g j).2
        exact Prod.ext hn (Subtype.ext ((hcol j).trans hj))
      · by_cases hζ : ζ ∈ S.μ
        · by_cases hw : (w, (⟨ζ, hζ⟩ : S.μ)) = (none, oneμ S)
          · obtain ⟨rfl, h2⟩ := Prod.mk.inj hw
            have : ζ = 1 := congrArg Subtype.val h2
            subst this
            simp [bar]
          · have h1 := cnt_eq_of_col hcol ⟨(w, ⟨ζ, hζ⟩), hw⟩
            have h2 := cnt_eq_of_col hcol (negTm S ⟨(w, ⟨ζ, hζ⟩), hw⟩)
            exact h1.symm.trans ((hclosed _).trans h2)
        · have hζ' : ζ⁻¹ ∉ S.μ := fun h => hζ (by simpa using Setting.inv_mem_μ S h)
          rw [Finset.card_eq_zero.2, Finset.card_eq_zero.2]
          · rw [Finset.filter_eq_empty_iff]
            intro j _ hj
            exact hζ' (hj.2 ▸ hκ j)
          · rw [Finset.filter_eq_empty_iff]
            intro j _ hj
            exact hζ (hj.2 ▸ hκ j)
    · funext i
      exact Subtype.ext (Prod.ext rfl (Subtype.ext (hcol i).symm))

/-- **Proof of Lemma 6.8 (ii)** of `q_col_count.md`: the block of a colour `x`: `none` for the class
`𝒞_1`, and `some ζ` (`ζ ∈ ℛ`) for the classes `𝒞_ζ`, `𝒞_{ζ^{−1}}` (Lemma 6.3 (i)). -/
noncomputable def blk (R : Finset F) (x : F) : Option R :=
  if h : x ∈ R then some ⟨x, h⟩ else if h' : x⁻¹ ∈ R then some ⟨x⁻¹, h'⟩ else none

/-- **Proof of Lemma 6.8 (ii)** of `q_col_count.md`: `ζ` and `ζ^{−1}` lie in the same block. -/
theorem blk_inv {R : Finset F} (hR : IsReps S R) (x : F) : blk R x⁻¹ = blk R x := by
  have key : ∀ y : F, y ∈ R → y⁻¹ ∉ R := fun y hy => (hR.mem hy).2.2
  unfold blk
  by_cases h1 : x ∈ R
  · have h2 : x⁻¹ ∉ R := key x h1
    simp [h1, h2]
  · by_cases h2 : x⁻¹ ∈ R
    · simp [h1, h2]
    · simp [h1, h2]

/-- **Proof of Lemma 6.8 (ii)** of `q_col_count.md`: for `x ∈ μ`, `x` is in the block `none` iff
`x = 1`. -/
theorem blk_eq_none {R : Finset F} (hR : IsReps S R) {x : F} (hx : x ∈ S.μ) :
    blk R x = none ↔ x = 1 := by
  unfold blk
  by_cases h1 : x = 1
  · subst h1
    have : (1 : F) ∉ R := fun h => (hR.mem h).2.1 rfl
    simp [this]
  · rcases hR.cases hx with h | h | h
    · exact absurd h h1
    · simp [h, h1]
    · have : x ∉ R := fun hx' => (hR.mem hx').2.2 h
      simp [h, h1, this]

/-- **Proof of Lemma 6.8 (ii)** of `q_col_count.md`: `x` is in the block `some ζ` iff
`x ∈ {ζ, ζ^{−1}}`. -/
theorem blk_eq_some {R : Finset F} (hR : IsReps S R) (ζ : R) (x : F) :
    blk R x = some ζ ↔ x = ζ ∨ x = (ζ : F)⁻¹ := by
  obtain ⟨z, hz⟩ := ζ
  have key : ∀ y : F, y ∈ R → y⁻¹ ∉ R := fun y hy => (hR.mem hy).2.2
  unfold blk
  by_cases h1 : x ∈ R
  · rw [dif_pos h1]
    simp only [Option.some.injEq, Subtype.mk.injEq]
    constructor
    · exact Or.inl
    · rintro (h | h)
      · exact h
      · exfalso
        subst h
        exact key z hz h1
  · rw [dif_neg h1]
    by_cases h2 : x⁻¹ ∈ R
    · rw [dif_pos h2]
      simp only [Option.some.injEq, Subtype.mk.injEq]
      constructor
      · intro h
        right
        rw [← h, inv_inv]
      · rintro (h | h)
        · exact absurd (h ▸ hz) h1
        · rw [h, inv_inv]
    · rw [dif_neg h2]
      simp only [reduceCtorEq, false_iff, not_or]
      refine ⟨fun h => h1 (h ▸ hz), fun h => h2 ?_⟩
      rw [h, inv_inv]
      exact hz

/-- **Proof of Lemma 6.8 (ii)** of `q_col_count.md` (*the blocks*): the conditions split into
independent conditions on the blocks: the number of good `ω` is the product over the blocks of the
numbers of good restrictions. -/
theorem card_good_eq_prod {X : Type*} [Fintype X] [DecidableEq X] {R : Finset F} (hR : IsReps S R)
    (κ : X → F) :
    (Finset.univ.filter (Good S κ)).card =
      ∏ b : Option R, (Finset.univ.filter
        (Good S (fun j : {v // blk R (κ v) = b} => κ j.1))).card := by
  have hcount : ∀ (f : X → Om S) (b : Option R) (w : Om S) (ζ : F),
      (Finset.univ.filter fun j : {v // blk R (κ v) = b} => f j.1 = w ∧ κ j.1 = ζ).card =
        if blk R ζ = b then (Finset.univ.filter fun x => f x = w ∧ κ x = ζ).card else 0 := by
    intro f b w ζ
    refine (card_filter_subtype (fun v => blk R (κ v) = b) (fun x => f x = w ∧ κ x = ζ)).trans ?_
    split_ifs with h
    · congr 1
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun h' => h'.2
      · intro h'
        exact ⟨h'.2 ▸ h, h'⟩
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro x - ⟨hb, -, hx⟩
      exact h (hx ▸ hb)
  have hiff : ∀ f : X → Om S, Good S κ f ↔
      ∀ b : Option R, Good S (fun j : {v // blk R (κ v) = b} => κ j.1) (fun j => f j.1) := by
    intro f
    constructor
    · rintro ⟨h1, h2⟩ b
      refine ⟨fun j hj => h1 j.1 hj, fun w ζ => ?_⟩
      rw [hcount f b w ζ, hcount f b (bar S w) ζ⁻¹, blk_inv hR]
      split_ifs
      · exact h2 w ζ
      · rfl
    · intro h
      refine ⟨fun x hx => (h (blk R (κ x))).1 ⟨x, rfl⟩ hx, fun w ζ => ?_⟩
      have := (h (blk R ζ)).2 w ζ
      rw [hcount f _ w ζ, hcount f _ (bar S w) ζ⁻¹, blk_inv hR, if_pos rfl, if_pos rfl] at this
      exact this
  have hfun : ∀ (G : ∀ b : Option R, {v // blk R (κ v) = b} → Om S) (b : Option R),
      (fun j : {v // blk R (κ v) = b} => G (blk R (κ j.1)) ⟨j.1, rfl⟩) = G b := by
    intro G b
    funext ⟨x, hx⟩
    subst hx
    rfl
  let e : {f : X → Om S // Good S κ f} ≃ ∀ b : Option R,
      {f : {v // blk R (κ v) = b} → Om S // Good S (fun j : {v // blk R (κ v) = b} => κ j.1) f} :=
    { toFun := fun f b => ⟨fun j => f.1 j.1, (hiff f.1).1 f.2 b⟩
      invFun := fun G => ⟨fun x => (G (blk R (κ x))).1 ⟨x, rfl⟩, (hiff _).2 fun b => by
        rw [hfun (fun b => (G b).1) b]
        exact (G b).2⟩
      left_inv := fun f => rfl
      right_inv := fun G => by
        funext b
        exact Subtype.ext (hfun (fun b => (G b).1) b) }
  calc (Finset.univ.filter (Good S κ)).card = Fintype.card {f // Good S κ f} :=
        (Fintype.card_subtype _).symm
    _ = Fintype.card (∀ b : Option R,
      {f : {v // blk R (κ v) = b} → Om S // Good S (fun j : {v // blk R (κ v) = b} => κ j.1) f}) :=
        Fintype.card_congr e
    _ = _ := by
        rw [Fintype.card_pi]
        exact Finset.prod_congr rfl fun b _ => Fintype.card_subtype _

/-- Reindexing a count along a bijection (auxiliary for the **Proof of Lemma 6.8 (ii)** of
`q_col_count.md`: "after an enumeration"). -/
theorem card_filter_equiv {X Y : Type*} [Fintype X] [Fintype Y] (e : X ≃ Y) (P : Y → Prop)
    [DecidablePred P] :
    (Finset.univ.filter fun x => P (e x)).card = (Finset.univ.filter P).card := by
  refine Finset.card_bij (fun x _ => e x) ?_ (fun a _ b _ h => e.injective h) ?_
  · intro x hx
    simpa using hx
  · intro y hy
    exact ⟨e.symm y, by simpa using hy, by simp⟩

/-- **Proof of Lemma 6.8 (ii)** of `q_col_count.md`: `v̄ = u` iff `v = ū`. -/
theorem bar_eq_iff (u v : Om S) : bar S v = u ↔ v = bar S u := by
  constructor
  · rintro rfl
    simp
  · rintro rfl
    simp

/-- **Proof of Lemma 6.8 (ii)** of `q_col_count.md` (*the block `𝒞_1`*): on an index set where all
colours are `1`, good tuples correspond to closed tuples of `T_h`. -/
theorem card_good_one (hp : S.p ≠ 2) {X : Type*} [Fintype X] [DecidableEq X] (κ : X → F) (hκ : ∀ j, κ j = 1) :
    (Finset.univ.filter (Good S κ)).card =
      (closedTuples (stdSetting ((S.q - 1) / 2) (ColOne.one_le_h hp)) (Fintype.card X)).card := by
  let e : X ≃ Fin (Fintype.card X) := Fintype.equivFin X
  have hne1 : ∀ (f : X → Om S) (w : Om S) (ζ : F), ζ ≠ 1 →
      (Finset.univ.filter fun j => f j = w ∧ κ j = ζ).card = 0 := by
    intro f w ζ hζ
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro j _ hj
    exact hζ (hj.2.symm.trans (hκ j))
  have hnone : ∀ (M : Fin (Fintype.card X) → Fin ((S.q - 1) / 2) × Bool) (ζ : F),
      (Finset.univ.filter fun j => some (M (e j)) = (none : Om S) ∧ κ j = ζ).card = 0 := by
    intro M ζ
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro j _ hj
    exact Option.some_ne_none _ hj.1
  have hsome : ∀ (M : Fin (Fintype.card X) → Fin ((S.q - 1) / 2) × Bool)
      (u : Fin ((S.q - 1) / 2) × Bool),
      (Finset.univ.filter fun j => some (M (e j)) = (some u : Om S) ∧ κ j = 1).card =
        cnt M u := by
    intro M u
    unfold cnt
    refine Eq.trans ?_ (card_filter_equiv e (fun i => M i = u))
    congr 1
    ext j
    simp [hκ j]
  have hgood : ∀ M : Fin (Fintype.card X) → Fin ((S.q - 1) / 2) × Bool,
      Good S κ (fun j => some (M (e j))) ↔
        M ∈ closedTuples (stdSetting ((S.q - 1) / 2) (ColOne.one_le_h hp)) (Fintype.card X) := by
    intro M
    simp only [closedTuples, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hM u
      have := hM.2 (some u) 1
      rw [inv_one, hsome, show bar S (some u) = some (u.1, !u.2) from rfl, hsome] at this
      exact this
    · intro hM
      refine ⟨fun j _ => Option.some_ne_none _, fun w ζ => ?_⟩
      by_cases hζ : ζ = 1
      · subst hζ
        rw [inv_one]
        cases w with
        | none => rw [show bar S none = none from rfl, hnone]
        | some u =>
          rw [hsome, show bar S (some u) = some (u.1, !u.2) from rfl, hsome]
          exact hM u
      · rw [hne1 _ _ _ hζ, hne1 _ _ _ (fun h' => hζ (inv_eq_one.1 h'))]
  symm
  refine Finset.card_bij (fun M _ => fun j => some (M (e j))) ?_ ?_ ?_
  · intro M hM
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, (hgood M).2 hM⟩
  · intro M1 _ M2 _ hM
    funext i
    have := congrFun hM (e.symm i)
    simpa using this
  · intro f hf
    rw [Finset.mem_filter] at hf
    have hs : ∀ i, (f (e.symm i)).isSome := fun i =>
      Option.isSome_iff_ne_none.2 (hf.2.1 _ (hκ _))
    let M : Fin (Fintype.card X) → Fin ((S.q - 1) / 2) × Bool := fun i => (f (e.symm i)).get (hs i)
    have hfM : (fun j => some (M (e j))) = f := by
      funext j
      simp [M]
    refine ⟨M, ?_, hfM⟩
    rw [← hgood, hfM]
    exact hf.2

/-- **Proof of Lemma 6.8 (ii)** of `q_col_count.md` (*the blocks `𝒞_ζ ∪ 𝒞_{ζ^{−1}}`*): on an index
set coloured by `ζ` (`a` times) and `ζ^{−1}` (`a` times), with `ζ ≠ ζ^{−1}` and `ζ ≠ 1`, the number
of good tuples is `N_{bal}(a, q)`. -/
theorem card_good_pair (hp : S.p ≠ 2) {X : Type*} [Fintype X] [DecidableEq X] (κ : X → F) {ζ : F} {a : ℕ}
    (h1 : ζ ≠ 1) (hinv : ζ⁻¹ ≠ ζ) (hX : ∀ j, κ j = ζ ∨ κ j = ζ⁻¹)
    (ha : (Finset.univ.filter fun j => κ j = ζ).card = a)
    (hb : (Finset.univ.filter fun j => κ j = ζ⁻¹).card = a) :
    (Finset.univ.filter (Good S κ)).card = Bip.Nbal a S.q := by
  have hne : ζ⁻¹ ≠ 1 := fun h' => h1 (inv_eq_one.1 h')
  have hiff : ∀ f : X → Om S, Good S κ f ↔
      ∀ w, (Finset.univ.filter fun j => f j = w ∧ κ j = ζ).card =
        (Finset.univ.filter fun j => f j = bar S w ∧ κ j = ζ⁻¹).card := by
    intro f
    constructor
    · exact fun hf w => hf.2 w ζ
    · intro hf
      refine ⟨fun j hj => ?_, fun w ζ' => ?_⟩
      · rcases hX j with h | h
        · exact absurd (h.symm.trans hj) h1
        · exact absurd (h.symm.trans hj) hne
      · by_cases hz : ζ' = ζ
        · subst hz
          exact hf w
        · by_cases hz' : ζ' = ζ⁻¹
          · subst hz'
            rw [inv_inv]
            have := hf (bar S w)
            rw [bar_bar] at this
            exact this.symm
          · have e1 : (Finset.univ.filter fun j => f j = w ∧ κ j = ζ').card = 0 := by
              rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
              intro j _ hj
              rcases hX j with h | h
              · exact hz (hj.2.symm.trans h)
              · exact hz' (hj.2.symm.trans h)
            have e2 : (Finset.univ.filter fun j => f j = bar S w ∧ κ j = ζ'⁻¹).card = 0 := by
              rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
              intro j _ hj
              rcases hX j with h | h
              · apply hz'
                have := congrArg Inv.inv (hj.2.symm.trans h)
                rwa [inv_inv] at this
              · exact hz (inv_injective (hj.2.symm.trans h))
            rw [e1, e2]
  have hcardA : Fintype.card {j // κ j = ζ} = a := by rw [Fintype.card_subtype]; exact ha
  have hcardB : Fintype.card {j // κ j = ζ⁻¹} = a := by rw [Fintype.card_subtype]; exact hb
  let eA : {j // κ j = ζ} ≃ Fin a := Fintype.equivFinOfCardEq hcardA
  let eB : {j // κ j = ζ⁻¹} ≃ Fin a := Fintype.equivFinOfCardEq hcardB
  let eΩ : Om S ≃ Fin S.q := Fintype.equivFinOfCardEq (card_Om S hp)
  have hcnt1 : ∀ (f : X → Om S) (u : Om S), Bip.cnt (fun t => f (eA.symm t).1) u =
      (Finset.univ.filter fun j => f j = u ∧ κ j = ζ).card := by
    intro f u
    unfold Bip.cnt
    refine (card_filter_equiv eA.symm (fun s => f s.1 = u)).trans ?_
    refine (card_filter_subtype (fun j => κ j = ζ) (fun j => f j = u)).trans ?_
    congr 1
    ext j
    simp [and_comm]
  have hcnt2 : ∀ (f : X → Om S) (u : Om S), Bip.cnt (fun t => bar S (f (eB.symm t).1)) u =
      (Finset.univ.filter fun j => f j = bar S u ∧ κ j = ζ⁻¹).card := by
    intro f u
    unfold Bip.cnt
    refine (card_filter_equiv eB.symm (fun s => bar S (f s.1) = u)).trans ?_
    refine (card_filter_subtype (fun j => κ j = ζ⁻¹) (fun j => bar S (f j) = u)).trans ?_
    congr 1
    ext j
    simp [and_comm, bar_eq_iff]
  let i : (X → Om S) → (Fin a → Om S) × (Fin a → Om S) := fun f =>
    (fun t => f (eA.symm t).1, fun t => bar S (f (eB.symm t).1))
  let jm : (Fin a → Om S) × (Fin a → Om S) → (X → Om S) := fun p x =>
    if hx : κ x = ζ then p.1 (eA ⟨x, hx⟩) else bar S (p.2 (eB ⟨x, (hX x).resolve_left hx⟩))
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

end ColCount

end

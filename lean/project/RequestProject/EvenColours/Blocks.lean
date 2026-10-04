module

public import RequestProject.EvenColours.Colours

/-!
# The blocks of the count (`q_even_count_colours.md`, proof of (C2))

A tuple `g ∈ (T2 S)^n` with a prescribed colour tuple `κ` is determined by `ω(g) = ((g i).1.1)_i`;
the condition `g ∈ closedT negT n` becomes a condition `Good S κ ω` on `ω`, which splits along any
partition of the colours into blocks closed under inversion (here: `SInv S ⊕ R`).  The block counts
are `NS S ζ |𝒞_ζ|` for a self-inverse colour `ζ`, and `Bip.Nbal |𝒞_ζ| q` for a pair
`𝒞_ζ ∪ 𝒞_{ζ^{−1}}` (the index `0` being an ordinary coordinate).
-/

@[expose] public section

namespace EvenColours

open ColSplit ColSurv ColComp Fibres TheoremB EvenBlocks

open scoped Classical

variable {F : Type*} [Field F] {S : ColSetting F}

variable (S) in
/-- **(C2)** of `q_even_count_colours.md` (proof): for a colour tuple `κ` on an index set `X`, the
condition on `ω ∈ (Om S)^X` for the tuple `(ω_i, κ_i)_i` to lie in `closedT negT`: `ω_i ≠ 0`
whenever `κ_i = 1`; `cnt (w, ζ) = cnt (−w, ζ^{−1})` for all `w`, `ζ`; and `cnt (w, ζ)` is even
when `−w = w` and `ζ^{−1} = ζ`. -/
def Good {X : Type*} [Fintype X] (κ : X → F) (f : X → Om S) : Prop :=
  (∀ j, κ j = 1 → f j ≠ 0) ∧
    (∀ (w : Om S) (ζ : F), (Finset.univ.filter fun j => f j = w ∧ κ j = ζ).card =
      (Finset.univ.filter fun j => f j = -w ∧ κ j = ζ⁻¹).card) ∧
    ∀ (w : Om S) (ζ : F), -w = w → ζ⁻¹ = ζ →
      Even (Finset.univ.filter fun j => f j = w ∧ κ j = ζ).card

/-- **(C2)** of `q_even_count_colours.md` (proof): in a tuple `g` with colour tuple `κ`,
`cnt g (w, ζ) = #{i : (g i).1.1 = w, κ_i = ζ}`. -/
theorem cnt_eq_of_col {n : ℕ} {g : Fin n → T2 S} {κ : Fin n → F}
    (hcol : ∀ j, ((g j).1.2 : F) = κ j) (u : T2 S) :
    cnt g u = (Finset.univ.filter fun j => (g j).1.1 = u.1.1 ∧ κ j = (u.1.2 : F)).card := by
  unfold cnt
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, ← hcol j]
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    exact Subtype.ext (Prod.ext h1 (Subtype.ext h2))

/-- **(C2)** of `q_even_count_colours.md` (proof): the number of tuples of `closedT negT n` with
colour tuple `κ ∈ μ^n` equals the number of `ω ∈ (Om S)^n` with `Good S κ ω`. -/
theorem card_col_eq_card_good {n : ℕ} (κ : Fin n → F) (hκ : ∀ i, κ i ∈ S.μ) :
    ((closedT (negT S) n).filter fun g => ∀ i, ((g i).1.2 : F) = κ i).card =
      (Finset.univ.filter (Good S κ)).card := by
  symm
  refine Finset.card_bij (fun ω hω i => (⟨(ω i, ⟨κ i, hκ i⟩), fun h =>
      (Finset.mem_filter.1 hω).2.1 i (congrArg Subtype.val (Prod.mk.inj h).2)
        (Prod.mk.inj h).1⟩ : T2 S)) ?_ ?_ ?_
  · intro ω hω
    have hG := (Finset.mem_filter.1 hω).2
    simp only [closedT, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨⟨fun u => ?_, fun u hu => ?_⟩, fun _ => trivial⟩
    · rw [cnt_eq_of_col (fun j => rfl) u, cnt_eq_of_col (fun j => rfl)]
      exact hG.2.1 u.1.1 u.1.2
    · rw [cnt_eq_of_col (fun j => rfl) u]
      obtain ⟨h1, h2⟩ := (negT_eq_iff S u).1 hu
      exact hG.2.2 u.1.1 u.1.2 h1 h2
  · intro ω1 _ ω2 _ h
    funext i
    exact congrArg (fun g : Fin n → T2 S => (g i).1.1) h
  · intro g hg
    simp only [closedT, Finset.mem_filter, Finset.mem_univ, true_and] at hg
    obtain ⟨⟨hclosed, hfix⟩, hcol⟩ := hg
    have hzero : ∀ ζ : F, ζ = 1 →
        (Finset.univ.filter fun j => (g j).1.1 = 0 ∧ κ j = ζ).card = 0 := by
      rintro ζ rfl
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro j _ hj
      exact (g j).2 (Prod.ext hj.1 (Subtype.ext ((hcol j).trans hj.2)))
    have hout : ∀ (w : Om S) (ζ : F), ζ ∉ S.μ →
        (Finset.univ.filter fun j => (g j).1.1 = w ∧ κ j = ζ).card = 0 := by
      intro w ζ hζ
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro j _ hj
      exact hζ (hj.2 ▸ hκ j)
    refine ⟨fun i => (g i).1.1, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, fun j hj hn => ?_, fun w ζ => ?_, fun w ζ hw hζ' => ?_⟩
      · apply (g j).2
        exact Prod.ext hn (Subtype.ext ((hcol j).trans hj))
      · by_cases hζ : ζ ∈ S.μ
        · by_cases hw : (w, (⟨ζ, hζ⟩ : S.μ)) = (0, ColCount.oneμ S)
          · obtain ⟨rfl, h2⟩ := Prod.mk.inj hw
            have : ζ = 1 := congrArg Subtype.val h2
            subst this
            simp
          · have h1 := cnt_eq_of_col hcol ⟨(w, ⟨ζ, hζ⟩), hw⟩
            have h2 := cnt_eq_of_col hcol (negT S ⟨(w, ⟨ζ, hζ⟩), hw⟩)
            exact h1.symm.trans ((hclosed _).trans h2)
        · have hζ' : ζ⁻¹ ∉ S.μ := fun h => hζ (by simpa using Setting.inv_mem_μ S h)
          exact (hout w ζ hζ).trans (hout (-w) ζ⁻¹ hζ').symm
      · by_cases hζ : ζ ∈ S.μ
        · by_cases hw' : (w, (⟨ζ, hζ⟩ : S.μ)) = (0, ColCount.oneμ S)
          · obtain ⟨rfl, h2⟩ := Prod.mk.inj hw'
            have : ζ = 1 := congrArg Subtype.val h2
            have h0 := hzero ζ this
            simp only at h0 ⊢
            rw [h0]
            exact Even.zero
          · have h1 : cnt g ⟨(w, ⟨ζ, hζ⟩), hw'⟩ =
                (Finset.univ.filter fun j => (g j).1.1 = w ∧ κ j = ζ).card :=
              cnt_eq_of_col hcol _
            have := hfix ⟨(w, ⟨ζ, hζ⟩), hw'⟩ ((negT_eq_iff S _).2 ⟨hw, hζ'⟩)
            rw [h1] at this
            exact this
        · have h0 := hout w ζ hζ
          simp only at h0 ⊢
          rw [h0]
          exact Even.zero
    · funext i
      exact Subtype.ext (Prod.ext rfl (Subtype.ext (hcol i).symm))

/-- **(C2)** of `q_even_count_colours.md` (proof): the conditions `Good` split into independent
conditions on blocks of colours closed under inversion: for any `blk : F → B` with
`blk ζ^{−1} = blk ζ`, the number of good `ω` is the product over the blocks of the numbers of good
restrictions (model: `ColCount.card_good_eq_prod`). -/
theorem card_good_eq_prod {X B : Type*} [Fintype X] [DecidableEq X] [Fintype B] [DecidableEq B]
    (blk : F → B) (hblk : ∀ x, blk x⁻¹ = blk x) (κ : X → F) :
    (Finset.univ.filter (Good S κ)).card =
      ∏ b : B, (Finset.univ.filter
        (Good S (fun j : {v // blk (κ v) = b} => κ j.1))).card := by
  have hcount : ∀ (f : X → Om S) (b : B) (w : Om S) (ζ : F),
      (Finset.univ.filter fun j : {v // blk (κ v) = b} => f j.1 = w ∧ κ j.1 = ζ).card =
        if blk ζ = b then (Finset.univ.filter fun x => f x = w ∧ κ x = ζ).card else 0 := by
    intro f b w ζ
    refine (ColCount.card_filter_subtype (fun v => blk (κ v) = b)
      (fun x => f x = w ∧ κ x = ζ)).trans ?_
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
      ∀ b : B, Good S (fun j : {v // blk (κ v) = b} => κ j.1) (fun j => f j.1) := by
    intro f
    constructor
    · rintro ⟨h1, h2, h3⟩ b
      refine ⟨fun j hj => h1 j.1 hj, fun w ζ => ?_, fun w ζ hw hζ => ?_⟩
      · rw [hcount f b w ζ, hcount f b (-w) ζ⁻¹, hblk]
        split_ifs
        · exact h2 w ζ
        · rfl
      · rw [hcount f b w ζ]
        split_ifs
        · exact h3 w ζ hw hζ
        · exact Even.zero
    · intro h
      refine ⟨fun x hx => (h (blk (κ x))).1 ⟨x, rfl⟩ hx, fun w ζ => ?_, fun w ζ hw hζ => ?_⟩
      · have := (h (blk ζ)).2.1 w ζ
        rw [hcount f _ w ζ, hcount f _ (-w) ζ⁻¹, hblk, if_pos rfl, if_pos rfl] at this
        exact this
      · have := (h (blk ζ)).2.2 w ζ hw hζ
        rw [hcount f _ w ζ, if_pos rfl] at this
        exact this
  have hfun : ∀ (G : ∀ b : B, {v // blk (κ v) = b} → Om S) (b : B),
      (fun j : {v // blk (κ v) = b} => G (blk (κ j.1)) ⟨j.1, rfl⟩) = G b := by
    intro G b
    funext ⟨x, hx⟩
    subst hx
    rfl
  let e : {f : X → Om S // Good S κ f} ≃ ∀ b : B,
      {f : {v // blk (κ v) = b} → Om S // Good S (fun j : {v // blk (κ v) = b} => κ j.1) f} :=
    { toFun := fun f b => ⟨fun j => f.1 j.1, (hiff f.1).1 f.2 b⟩
      invFun := fun G => ⟨fun x => (G (blk (κ x))).1 ⟨x, rfl⟩, (hiff _).2 fun b => by
        rw [hfun (fun b => (G b).1) b]
        exact (G b).2⟩
      left_inv := fun f => rfl
      right_inv := fun G => by
        funext b
        exact Subtype.ext (hfun (fun b => (G b).1) b) }
  calc (Finset.univ.filter (Good S κ)).card = Fintype.card {f // Good S κ f} :=
        (Fintype.card_subtype _).symm
    _ = Fintype.card (∀ b : B,
      {f : {v // blk (κ v) = b} → Om S // Good S (fun j : {v // blk (κ v) = b} => κ j.1) f}) :=
        Fintype.card_congr e
    _ = _ := by
        rw [Fintype.card_pi]
        exact Finset.prod_congr rfl fun b _ => Fintype.card_subtype _

end EvenColours

end

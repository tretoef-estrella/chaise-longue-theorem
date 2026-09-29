module

public import RequestProject.ColOne.Coord
public import RequestProject.ColComp.Main
public import RequestProject.Bip.Main

/-!
# The count factors in the same way: Setting and Lemma 6.8 (i) (`q_col_count.md`)

This file formalizes the **Setting** of `q_col_count.md` and part **(i)** of **Lemma 6.8**.

Conventions (reused unchanged from the earlier files):
* `S : ColSplit.ColSetting F` is the Setting of `q_col_splitting.md`; the extra hypotheses
  *"`p ≠ 2`"* and *"`r` is odd"* of the Setting of `q_col_count.md` are the hypotheses
  `hp : S.p ≠ 2` and `hr : Odd S.r`;
* colourings `c ∈ μ^d` (`d = 2k + 1`) are maps `c : Fin (2 * k + 1) → S.μ`, extended by `c_0` to
  `ColSurv.cExt c : Fin (2 * k + 2) → F` (`q_col_survivors.md`); the classes `𝒞_ζ` are
  `ColComp.cls (cExt c) ζ` and compatibility is `ColComp.Compatible` (`q_col_compatible.md`);
* the standard point set `T_h = {1, …, h} × {±1}` is `TheoremB.stdSetting h _`, on `Fin h × Bool`,
  and closed tuples are `TheoremB.closedTuples` (`q_theorem_B_lower.md`);
* `N_{bal}` and `N_{ph}` are `Bip.Nbal` and `Bip.Nph` (`q_bip_setting.md`).
-/

@[expose] public section

namespace ColCount

open ColSplit ColSurv ColComp Fibres TheoremB

open scoped Classical

variable {F : Type*} [Field F] (S : ColSetting F)

/-- **Lemma 6.8 (i)** of `q_col_count.md`: the set `Ω_q := T_h ⊔ {∗}`, with `h = (q − 1)/2` and
`T_h = {1, …, h} × {±1}` (here `Fin h × Bool`); the extra point `∗` is `none`. -/
abbrev Om : Type := Option (Fin ((S.q - 1) / 2) × Bool)

/-- **Lemma 6.8 (i)** of `q_col_count.md`: the involution `w ↦ w̄` of `Ω_q`, with `∗̄ := ∗` and
`w̄ := −w` for `w ∈ T_h` (the involution `(u, ε) ↦ (u, −ε)` of `T_h`). -/
def bar (w : Om S) : Om S := w.map fun u => (u.1, !u.2)

/-- The element `1 ∈ μ` (**Lemma 6.8 (i)** of `q_col_count.md`: the removed point is `(∗, 1)`). -/
def oneμ : S.μ := ⟨1, Setting.one_mem_μ S⟩

/-- The inverse `ζ ↦ ζ^{−1}` on `μ` (**Lemma 6.8 (i)** of `q_col_count.md`). -/
noncomputable def invμ (ζ : S.μ) : S.μ := ⟨(ζ : F)⁻¹, Setting.inv_mem_μ S ζ.2⟩

/-- **Lemma 6.8 (i)** of `q_col_count.md`: the point set `T_m := (Ω_q × μ) ∖ {(∗, 1)}`. -/
abbrev Tm : Type _ := {x : Om S × S.μ // x ≠ (none, oneμ S)}

/-- **Proof of Lemma 6.8 (i)** of `q_col_count.md`: `w̄̄ = w`. -/
@[simp] theorem bar_bar (w : Om S) : bar S (bar S w) = w := by
  cases w <;> simp [bar]

/-- **Proof of Lemma 6.8 (i)** of `q_col_count.md`: `w̄ = ∗` iff `w = ∗`. -/
@[simp] theorem bar_eq_none (w : Om S) : bar S w = none ↔ w = none := by
  simp [bar]

/-- **Proof of Lemma 6.8 (i)** of `q_col_count.md`: the involution of `T_h` has no fixed point, so
`w̄ = w` forces `w = ∗`. -/
theorem eq_none_of_bar_eq (w : Om S) (h : bar S w = w) : w = none := by
  cases w with
  | none => rfl
  | some u => simp [bar, Prod.ext_iff] at h

/-- **Proof of Lemma 6.8 (i)** of `q_col_count.md`: `ζ^{−1} = 1` iff `ζ = 1`. -/
@[simp] theorem invμ_eq_one (ζ : S.μ) : invμ S ζ = oneμ S ↔ ζ = oneμ S := by
  simp [invμ, oneμ, Subtype.ext_iff]

/-- **Proof of Lemma 6.8 (i)** of `q_col_count.md`: `(ζ^{−1})^{−1} = ζ`. -/
@[simp] theorem invμ_invμ (ζ : S.μ) : invμ S (invμ S ζ) = ζ := by
  simp [invμ]

/-- **Lemma 6.8 (i)** of `q_col_count.md`: the involution `(w, ζ) ↦ (w̄, ζ^{−1})` of `T_m` (it maps
`T_m` to itself since `(∗, 1)` is its own image). -/
noncomputable def negTm (x : Tm S) : Tm S :=
  ⟨(bar S x.1.1, invμ S x.1.2), by
    intro h
    apply x.2
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    exact Prod.ext ((bar_eq_none S _).1 h1) ((invμ_eq_one S _).1 h2)⟩

/-- **Proof of Lemma 6.8 (i)** of `q_col_count.md`: `|Ω_q| = q` (as `q` is odd, `q = 2h + 1`). -/
theorem card_Om (hp : S.p ≠ 2) : Fintype.card (Om S) = S.q := by
  have h1 := ColOne.odd_q (S := S) hp
  obtain ⟨t, ht⟩ := h1
  simp only [Fintype.card_option, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  omega

/-- **Proof of Lemma 6.8 (i)** of `q_col_count.md`: `m = q·r` is odd. -/
theorem odd_m (hp : S.p ≠ 2) (hr : Odd S.r) : Odd S.m :=
  (ColOne.odd_q (S := S) hp).mul hr

/-- **Proof of Lemma 6.8 (i)** of `q_col_count.md`: `|T_m| = q·r − 1 = m − 1`. -/
theorem card_Tm (hp : S.p ≠ 2) : Fintype.card (Tm S) = S.m - 1 := by
  rw [Fintype.card_subtype_compl, Fintype.card_prod, card_Om S hp, Fintype.card_coe, S.card_μ,
    Fintype.card_unique]
  rfl

/-- **Lemma 6.8 (i)** of `q_col_count.md`: `T_m`, with the involution `(w, ζ) ↦ (w̄, ζ^{−1})`, is a
point set with a fixed-point-free involution and `|T_m| = m − 1 = 2H`, `H = (m − 1)/2 ≥ 1`. -/
noncomputable def TmSetting (hp : S.p ≠ 2) (hr : Odd S.r) :
    FibreSetting (Tm S) ((S.m - 1) / 2) where
  neg := negTm S
  neg_neg := by
    intro x
    apply Subtype.ext
    simp [negTm]
  neg_ne := by
    intro x h
    apply x.2
    have h' := congrArg Subtype.val h
    simp only [negTm, Prod.ext_iff] at h'
    have hζ : x.1.2 = oneμ S := by
      apply Subtype.ext
      exact lemma63_i_self_inv hr x.1.2.2 (congrArg Subtype.val h'.2)
    exact Prod.ext (eq_none_of_bar_eq S _ h'.1) hζ
  one_le := by
    have h3 := ColOne.three_le_q (S := S) hp
    have hr1 := S.one_le_r
    have : 3 ≤ S.m := le_trans h3 (Nat.le_mul_of_pos_right _ hr1)
    omega
  card_eq := by
    rw [card_Tm S hp]
    obtain ⟨t, ht⟩ := odd_m S hp hr
    omega

variable {S}

/-- **Setting** of `q_col_count.md`: `N_1(c) := #{closed tuples in T_h^{|𝒞_1|}}`, with
`T_h = {1, …, h} × {±1}`, `h = (q − 1)/2`, and `𝒞_1` the class of `1` of the extended colouring. -/
noncomputable def N1 (hp : S.p ≠ 2) {k : ℕ} (c : Fin (2 * k + 1) → S.μ) : ℕ :=
  (closedTuples (stdSetting ((S.q - 1) / 2) (ColOne.one_le_h hp)) (cls (cExt c) 1).card).card

/-- **Setting** of `q_col_count.md`: for `ζ ∈ ℛ`, with `α := |𝒞_ζ ∖ {0}|` and
`β := |𝒞_{ζ^{−1}} ∖ {0}|`, `N_ζ(c) := N_{ph}(min(α, β), q)` if `0 ∈ 𝒞_ζ ∪ 𝒞_{ζ^{−1}}`, and
`N_ζ(c) := N_{bal}(α, q)` otherwise. -/
noncomputable def Nz {k : ℕ} (c : Fin (2 * k + 1) → S.μ) (ζ : F) : ℕ :=
  if (0 : Fin (2 * k + 2)) ∈ cls (cExt c) ζ ∪ cls (cExt c) ζ⁻¹ then
    Bip.Nph (min ((cls (cExt c) ζ).erase 0).card ((cls (cExt c) ζ⁻¹).erase 0).card) S.q
  else Bip.Nbal ((cls (cExt c) ζ).erase 0).card S.q

end ColCount

end

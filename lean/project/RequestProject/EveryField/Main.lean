module

public import RequestProject.EveryField.Invariance
public import RequestProject.EveryField.Integral
public import RequestProject.Support.Main
public import RequestProject.TheoremB.Main

/-!
# Parts (iii), (iv), (v) of the Theorem of `q_every_field.md`

Formalization of **parts (iii)** (characteristic `0`), **(iv)** (every field) and **(v)**
(Theorem B with equality) of the Theorem of `q_every_field.md`.

As in `q_induction.md` and `q_support.md`, `dim_F V_Λ(F)` is the `F`-dimension of the ideal
`V_Λ = Tight.VLamAll F q m Λ` of `C_m(F)` regarded as an `F`-subspace, `Z_Λ` is `S.ZLam m Λ` for a
point set `S : Fibres.FibreSetting T ((q - 1) / 2)` (any finite set with a fixed-point-free
involution and `|T| = 2h`, `h = (q − 1)/2`; by part (0) the choice does not matter), and "down-set
of `Par_m`" is `Lifts.IsDownSetPar ((q - 1) / 2) m Λ` of `q_P3_lifts.md`.  No hypothesis is made
on the characteristic of `F` in (iv) and (v).
-/

@[expose] public section

namespace EveryField

open ChainLemma Fibres Tight Lifts

set_option synthInstance.maxHeartbeats 200000

/-! ### The point set `T_K` of `(q−1)`-th roots of unity in `K = ℂ` -/

/-- **Proof of part (iii)** of `q_every_field.md`: `K := ℂ` contains the primitive `(q−1)`-th root
of unity `ζ = exp(2πi/(q−1))` (for `q ≥ 2`). -/
theorem isPrimitiveRoot_zeta {q : ℕ} (hq : 2 ≤ q) :
    IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / (q - 1 : ℕ))) (q - 1) :=
  Complex.isPrimitiveRoot_exp (q - 1) (by omega)

/-- **Proof of part (iii)** of `q_every_field.md`: the set `T_K = {ζ^j : 0 ≤ j < q − 1} ⊆ ℂ`, i.e.
the set of all `(q−1)`-th roots of unity in `ℂ`. -/
noncomputable def TK (q : ℕ) : Finset ℂ := Polynomial.nthRootsFinset (q - 1) (1 : ℂ)

/-- **Proof of part (iii)** of `q_every_field.md`: `T_K` has `q − 1` elements. -/
theorem card_TK {q : ℕ} (hq : 2 ≤ q) : (TK q).card = q - 1 :=
  (isPrimitiveRoot_zeta hq).card_nthRootsFinset

/-- **Proof of part (iii)** of `q_every_field.md`: `Π_{u∈T_K}(X − u) = X^{q−1} − 1`. -/
theorem prod_TK {q : ℕ} (hq : 2 ≤ q) :
    ∏ u ∈ TK q, (Polynomial.X - Polynomial.C u) = Polynomial.X ^ (q - 1) - 1 :=
  (Polynomial.X_pow_sub_one_eq_prod (by omega) (isPrimitiveRoot_zeta hq)).symm

/-- **Proof of part (iii)** of `q_every_field.md`: `T_K` with `u ↦ −u` is a point set (the Setting
of `q_support.md`, hence of `q_P1_fibres.md`, with `h = (q − 1)/2`). -/
noncomputable def settingTK {q : ℕ} (hq : 3 ≤ q) (hodd : Odd q) :
    FibreSetting (TK q) ((q - 1) / 2) :=
  Support.fibreSetting hq hodd (TK q) (card_TK (by omega)) (prod_TK (by omega))

/-- **Proof of part (iii)** of `q_every_field.md`: over `K = ℂ`, the Theorem of `q_support.md`
gives `dim_K V_Λ(K) = |Z_Λ(T_K)|` for every down-set `Λ` of `Par_m`. -/
theorem finrank_VLamAll_complex {q : ℕ} (hq : 3 ≤ q) (hodd : Odd q) [DecidableEq (TK q)]
    (m : ℕ) (Λ : Set Partition) (hΛ : IsDownSetPar ((q - 1) / 2) m Λ) :
    Module.finrank ℂ ((VLamAll ℂ q m Λ).restrictScalars ℂ) =
      ((settingTK hq hodd).ZLam m Λ).card := by
  rw [@Support.finrank_VLamAll_eq_card_ZLam ℂ _ (Classical.decEq ℂ) q hq hodd (TK q)
    (card_TK (by omega)) (prod_TK (by omega)) m Λ hΛ]
  convert rfl

variable {T : Type*} [Fintype T] [DecidableEq T]

/-- **Part (iii)** of the Theorem of `q_every_field.md` (characteristic `0`): if `char F = 0`,
then `dim_F V_Λ(F) = |Z_Λ|` for every `m` and every down-set `Λ` of `Par_m`.

Proof as in the file: `dim_F V_Λ(F) = rank_F(A) = rank_ℚ(A) = rank_K(A) = dim_K V_Λ(K)` by (i)
and (ii), with `K = ℂ`; `dim_K V_Λ(K) = |Z_Λ(T_K)|` by the Theorem of `q_support.md`, and
`|Z_Λ(T_K)| = |Z_Λ|` by (0). -/
theorem finrank_VLamAll_eq_card_ZLam_of_charZero (F : Type*) [Field F] [CharZero F] {q : ℕ}
    (hq : 3 ≤ q) (hodd : Odd q) (S : FibreSetting T ((q - 1) / 2)) (m : ℕ) (Λ : Set Partition)
    (hΛ : IsDownSetPar ((q - 1) / 2) m Λ) :
    Module.finrank F ((VLamAll F q m Λ).restrictScalars F) = (S.ZLam m Λ).card := by
  classical
  rw [finrank_VLamAll_eq_rankOver (by omega), rankOver_eq_rankOver_rat,
    ← rankOver_eq_rankOver_rat ℂ, ← finrank_VLamAll_eq_rankOver (by omega),
    finrank_VLamAll_complex hq hodd m Λ hΛ]
  exact card_ZLam_eq _ _ m Λ

/-- **Part (iv)** of the Theorem of `q_every_field.md` (every field): for every field `F` (of any
characteristic), every odd `q ≥ 3`, every `m ≥ 0` and every down-set `Λ` of `Par_m`:
`dim_F V_Λ(F) = |Z_Λ|`.

Proof as in the file: `dim_F V_Λ(F) = rank_F(A) ≤ rank_ℚ(A) = dim_ℚ V_Λ(ℚ) = |Z_Λ|` by (i),
(ii) and (iii) for `ℚ`; the reverse inequality is the Theorem of `q_induction.md`. -/
theorem finrank_VLamAll_eq_card_ZLam (F : Type*) [Field F] {q : ℕ} (hq : 3 ≤ q) (hodd : Odd q)
    (S : FibreSetting T ((q - 1) / 2)) (m : ℕ) (Λ : Set Partition)
    (hΛ : IsDownSetPar ((q - 1) / 2) m Λ) :
    Module.finrank F ((VLamAll F q m Λ).restrictScalars F) = (S.ZLam m Λ).card := by
  refine le_antisymm ?_ (Induction.finrank_VLamAll_ge_card_ZLam F hq hodd S m Λ hΛ)
  rw [finrank_VLamAll_eq_rankOver (by omega)]
  refine (rankOver_le_rankOver_rat F _).trans (le_of_eq ?_)
  rw [← finrank_VLamAll_eq_rankOver (by omega)]
  exact finrank_VLamAll_eq_card_ZLam_of_charZero ℚ hq hodd S m Λ hΛ

/-- **Part (v)** of the Theorem of `q_every_field.md` (Theorem B with equality): for every field
`F` (of any characteristic), every odd `q ≥ 3` and every `k ≥ 0`:
`dim_F (D_J : J ∈ 𝒥) = Q_k(q)`.

Proof as in the file: by part (i) of `q_theorem_B_lower.md`, `(D_J : J ∈ 𝒥) = V_{(1)}` with
`m = 2k + 1`, `{(1)}` is a down-set of `Par_{2k+1}` and `Z_{(1)} = Γ'`; by (iv),
`dim_F (D_J) = |Γ'|`, and `|Γ'| = Q_k(q)` by part (iii) of `q_theorem_B_lower.md` (with the point
set `T = {1, …, h} × {±1}`). -/
theorem finrank_DIdeal_eq (F : Type*) [Field F] {q : ℕ} (hq : 3 ≤ q) (hodd : Odd q) (k : ℕ) :
    Module.finrank F ((TheoremB.DIdeal F q k).restrictScalars F) = TheoremB.Qk k q := by
  have hh : 1 ≤ (q - 1) / 2 := by omega
  obtain ⟨hdown, hV, hZ⟩ := TheoremB.root hq F (TheoremB.stdSetting _ hh) k
  rw [← hV, ← TheoremB.card_Gamma' (TheoremB.stdSetting _ hh), ← hZ]
  exact finrank_VLamAll_eq_card_ZLam F hq hodd _ _ _ hdown

end EveryField

end

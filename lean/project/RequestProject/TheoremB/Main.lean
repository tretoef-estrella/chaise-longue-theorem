module

public import RequestProject.TheoremB.Closed
public import RequestProject.TheoremB.Matchings

/-!
# Theorem B, lower bound (`q_theorem_B_lower.md`)

Formalization of parts (i)–(iv) of the **Theorem** of `q_theorem_B_lower.md`.

**Setting** (`RequestProject/TheoremB/Defs.lean`): `F` is a field, `q ≥ 3` odd, `h = (q − 1)/2`,
`k ≥ 0`, `n' = 2k + 1`, `N = 2k + 2`, and `C = C_{n'}` is `Peel.C F q (2 * k + 1)`.
* `𝒥` is `BallotBound.Matching k` (fixed-point-free involutions of `Fin (2 * k + 2)`), `D_J` is
  `DJ F q J` and `(D_J : J ∈ 𝒥)` is `DIdeal F q k`;
* `Q_k(q)` is `Qk k q`;
* the point set `T` with its involution and `|T| = 2h` is `S : Fibres.FibreSetting T h`
  (`q_P1_fibres.md`); `ν(M)` is `nu S M`, the closed tuples in `T^n` are `closedTuples S n`, and
  `Γ'` is `Gamma' S k`;
* `(1)` is `one`, `Par_n` and down-sets of `Par_n` are `Lifts.Par`, `Lifts.IsDownSetPar`
  (`q_P3_lifts.md`), `V_Λ` is `Tight.VLamAll` (`q_P3_identities.md`) and `Z_Λ` is
  `FibreSetting.ZLam` (`q_P1_fibres.md`).

As in `q_peeling_lemma.md`, `dim_F` of an ideal of `C` is the `F`-dimension of the ideal regarded
as an `F`-subspace of `C` (`Submodule.restrictScalars F`).
-/

@[expose] public section

namespace TheoremB

open ChainLemma Fibres Tight Lifts

set_option synthInstance.maxHeartbeats 200000

variable {T : Type*} [Fintype T] [DecidableEq T]

/-- **Theorem, part (i)** of `q_theorem_B_lower.md` (first claim): in `Par_{n'}` (with
`h = (q − 1)/2`, `q ≥ 3`), `Λ := {(1)}` is a down-set. -/
theorem isDownSetPar_one {q : ℕ} (hq : 3 ≤ q) (k : ℕ) :
    IsDownSetPar ((q - 1) / 2) (2 * k + 1) {one} :=
  isDownSetPar_one_aux (by omega) k

/-- **Theorem, part (i)** of `q_theorem_B_lower.md` (second claim): `V_{(1)} = (D_J : J ∈ 𝒥)`
in `C = C_{n'}`. -/
theorem VLamAll_one_eq (F : Type*) [Field F] (q k : ℕ) :
    VLamAll F q (2 * k + 1) {one} = DIdeal F q k :=
  VLamAll_one_eq_aux F q k

/-- **Theorem, part (i)** of `q_theorem_B_lower.md` (third claim): `Z_{(1)} = Γ'`, for every
point set `T` with a fixed-point-free involution. -/
theorem ZLam_one_eq {h : ℕ} (S : FibreSetting T h) (k : ℕ) :
    S.ZLam (2 * k + 1) {one} = Gamma' S k :=
  ZLam_one_eq_aux S k

/-- **Theorem, part (i)** of `q_theorem_B_lower.md` (the root, Lemma 5.2 of the paper), all three
claims together: in `Par_{n'}`, `Λ := {(1)}` is a down-set; `V_{(1)} = (D_J : J ∈ 𝒥)`; and
`Z_{(1)} = Γ'`. -/
theorem root {q : ℕ} (hq : 3 ≤ q) (F : Type*) [Field F] (S : FibreSetting T ((q - 1) / 2))
    (k : ℕ) :
    IsDownSetPar ((q - 1) / 2) (2 * k + 1) {one} ∧
      VLamAll F q (2 * k + 1) {one} = DIdeal F q k ∧
      S.ZLam (2 * k + 1) {one} = Gamma' S k :=
  ⟨isDownSetPar_one hq k, VLamAll_one_eq F q k, ZLam_one_eq S k⟩

/-- **Theorem, part (ii)** of `q_theorem_B_lower.md` (Lemma 2.2): the number of closed tuples in
`T^N` is `Q_k(q)` (for `T` with a fixed-point-free involution and `|T| = 2h`, `h = (q − 1)/2`). -/
theorem card_closedTuples {q : ℕ} (S : FibreSetting T ((q - 1) / 2)) (k : ℕ) :
    (closedTuples S (2 * k + 2)).card = Qk k q :=
  card_closedTuples_aux S k

/-- **Theorem, part (iii)** of `q_theorem_B_lower.md` (Lemma 3.1): `|Γ'| = Q_k(q)`. -/
theorem card_Gamma' {q : ℕ} (S : FibreSetting T ((q - 1) / 2)) (k : ℕ) :
    (Gamma' S k).card = Qk k q := by
  rw [card_Gamma'_eq_card_closedTuples, card_closedTuples]

/-- **Theorem, part (iv)** of `q_theorem_B_lower.md` (Theorem B, lower bound): for every field
`F`, every odd `q ≥ 3` and every `k ≥ 0`, `dim_F (D_J : J ∈ 𝒥) ≥ Q_k(q)`.

No point set is assumed: the proof constructs `T = {1, …, h} × {±1}` (`stdSetting`) and combines
part (i), the Theorem of `q_induction.md` (`Induction.finrank_VLamAll_ge_card_ZLam`) with
`m = n'` and `Λ = {(1)}`, and part (iii):
`dim_F (D_J) = dim_F V_{(1)} ≥ |Z_{(1)}| = |Γ'| = Q_k(q)`. -/
theorem finrank_DIdeal_ge (F : Type*) [Field F] {q : ℕ} (hq : 3 ≤ q) (hodd : Odd q) (k : ℕ) :
    Module.finrank F ((DIdeal F q k).restrictScalars F) ≥ Qk k q := by
  have hh : 1 ≤ (q - 1) / 2 := by omega
  rw [← VLamAll_one_eq, ← card_Gamma' (stdSetting _ hh), ← ZLam_one_eq]
  exact Induction.finrank_VLamAll_ge_card_ZLam F hq hodd _ _ _ (isDownSetPar_one hq k)

end TheoremB

end

module

public import RequestProject.OddLayers.Exchange
public import RequestProject.Induction.Steps

/-!
# Theorem L of `q_oddbox_layers.md`: (L1), (L3), (L4), (L5)

(E) and (L2) are in `RequestProject/OddLayers/Exchange.lean`.
Step 1 of `q_induction.md` is `Induction.FLam_le_FLam`; part (iv) of `q_peeling_lemma.md` is
`Peel.card_eq_sum_Zgt`.
-/

@[expose] public section

namespace OddLayers

open ChainLemma ChainLemma.Partition Fibres OddShapes

/-- **Theorem L, (L1) (monotone)** of `q_oddbox_layers.md`: let `h ≥ 1`, `m ≥ 1` and let `Λ` be an
interlaced pair of level `m`. If `(μ, δ)` and `(μ̃, δ)` lie in `Sh_{m−1}` and `μ ≼ μ̃`, then
`F_Λ(μ̃, δ) ≤ F_Λ(μ, δ)`. -/
theorem FS_antitone {h m : ℕ} (hh : 1 ≤ h) (hm : 1 ≤ m) {Λ : Set Shape}
    (hΛ : IsInterlaced h m Λ) {μ μ' : Partition} {δ : Bool} (hμ : (μ, δ) ∈ Sh h (m - 1))
    (hμ' : (μ', δ) ∈ Sh h (m - 1)) (hle : μ ≼ μ') : FS h Λ (μ', δ) ≤ FS h Λ (μ, δ) := by
  obtain ⟨-, ⟨h0, h1⟩, -⟩ := hΛ
  unfold FS
  cases δ with
  | false =>
    rw [mem_Sh_false] at hμ hμ'
    have hA := Induction.FLam_le_FLam hh hm h0 hμ hμ' hle
    have hB : μ' ∈ comp Λ (!false) → μ ∈ comp Λ (!false) := fun h' => h1.2 μ μ' hμ hle h'
    simp only at hA hB ⊢
    split_ifs with c1 c2 <;> first | omega | exact absurd (hB c1) c2
  | true =>
    rw [mem_Sh_true] at hμ hμ'
    have hA := Induction.FLam_le_FLam (m := m - 1) hh hμ.1 h1 hμ.2 hμ'.2 hle
    have hpar : μ ∈ Lifts.Par h m := by
      obtain ⟨hs1, hs2, hs3⟩ := hμ.2
      exact ⟨by omega, by omega, hs3⟩
    have hB : μ' ∈ comp Λ (!true) → μ ∈ comp Λ (!true) := fun h' => h0.2 μ μ' hpar hle h'
    simp only at hA hB ⊢
    split_ifs with c1 c2 <;> first | omega | exact absurd (hB c1) c2

/-- **Theorem L, (L3), first part (Lemma 8.4 of the paper)** of `q_oddbox_layers.md`: if `h ≥ 1`,
`m ≥ 1` and `Λ` is an interlaced pair of level `m`, then for every `i ≥ 0` the layer `Λ_i` is an
interlaced pair of level `m − 1`. -/
theorem isInterlaced_layerS {h m : ℕ} (hh : 1 ≤ h) (hm : 1 ≤ m) {Λ : Set Shape}
    (hΛ : IsInterlaced h m Λ) (i : ℕ) : IsInterlaced h (m - 1) (layerS h m Λ i) := by
  refine ⟨fun s hs => hs.1, ⟨⟨fun x hx => (mem_Sh_false _ _ _).mp hx.1, ?_⟩,
    ⟨fun x hx => ((mem_Sh_true _ _ _).mp hx.1).2, ?_⟩⟩, ?_⟩
  · intro lam μ hlam hle hμ
    have hl : (lam, false) ∈ Sh h (m - 1) := (mem_Sh_false _ _ _).mpr hlam
    exact ⟨hl, lt_of_lt_of_le hμ.2 (FS_antitone hh hm hΛ hl hμ.1 hle)⟩
  · intro lam μ hlam hle hμ
    have hl : (lam, true) ∈ Sh h (m - 1) :=
      (mem_Sh_true _ _ _).mpr ⟨((mem_Sh_true _ _ _).mp hμ.1).1, hlam⟩
    exact ⟨hl, lt_of_lt_of_le hμ.2 (FS_antitone hh hm hΛ hl hμ.1 hle)⟩
  · intro ν δ hν j hj1 hj
    exact ⟨subE_mem_Sh hν.1 hj1 hj, lt_of_lt_of_le hν.2 (FS_le_FS_subE hm hΛ hν.1 hj1 hj)⟩

/-- **Theorem L, (L3), second part** of `q_oddbox_layers.md`: for every set `Λ` of shapes,
`Λ_{i+1} ⊆ Λ_i`. -/
theorem layerS_succ_subset (h m : ℕ) (Λ : Set Shape) (i : ℕ) :
    layerS h m Λ (i + 1) ⊆ layerS h m Λ i :=
  fun _ hs => ⟨hs.1, by have := hs.2; omega⟩

/-- **Theorem L, (L3), third part** of `q_oddbox_layers.md`: for every set `Λ` of shapes,
`Λ_i = ∅` for `i ≥ 2h + 1` (by (B5), `F_Λ(μ, δ) ≤ 2h + 1` whenever `ℓ(μ) ≤ h`). -/
theorem layerS_eq_empty (h m : ℕ) (Λ : Set Shape) {i : ℕ} (hi : 2 * h + 1 ≤ i) :
    layerS h m Λ i = ∅ := by
  classical
  ext ⟨μ, δ⟩
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hs, hlt⟩
  rw [FS_eq_card h Λ μ δ hs.1] at hlt
  have := Finset.card_le_card (Finset.filter_subset (fun p => optS h (μ, δ) p ∈ Λ)
    (Finset.Icc 1 (2 * h + 1)))
  rw [Nat.card_Icc] at this
  omega

variable {T : Type*} [Fintype T] [DecidableEq T] {h : ℕ}

/-- **Theorem L, (L4) (Lemma 8.4, second half)** of `q_oddbox_layers.md`: for every set `Λ` of
shapes, `m ≥ 1` and every `i ≥ 0`: `(Z_Λ)_{>i} = Z_{Λ_i}`, where `Z_Λ ⊆ T^m` and
`Z_{Λ_i} ⊆ T^{m−1}`. -/
theorem Zgt_ZS_eq_ZS_layerS (S : OddSetting T h) {m : ℕ} (hm : 1 ≤ m) (Λ : Set Shape)
    (i : ℕ) : Peel.Zgt (ZS S m Λ) i = ZS S (m - 1) (layerS h m Λ i) := by
  rw [Zgt_ZS S hm Λ i]
  ext M'
  simp [ZS, layerS, shape_mem_Sh S M']

/-- **Theorem L, (L5)** of `q_oddbox_layers.md`: for every set `Λ` of shapes and `m ≥ 1`:
`|Z_Λ| = Σ_{i=0}^{2h} |Z_{Λ_i}|`. -/
theorem card_ZS_eq_sum (S : OddSetting T h) {m : ℕ} (hm : 1 ≤ m) (Λ : Set Shape) :
    (ZS S m Λ).card =
      ∑ i ∈ Finset.range (2 * h + 1), (ZS S (m - 1) (layerS h m Λ i)).card := by
  have hh := S.one_le
  rw [Peel.card_eq_sum_Zgt (q := 2 * h + 2) (by omega) hm (by rw [S.card_eq]; omega),
    show 2 * h + 2 - 1 = 2 * h + 1 by omega]
  exact Finset.sum_congr rfl fun i _ => by rw [Zgt_ZS_eq_ZS_layerS S hm Λ i]

end OddLayers

module

public import RequestProject.BipP3.Main
public import RequestProject.BipAny.Peeling
public import RequestProject.BipAny.Layers

/-!
# Item 5 of the Proofs of `q_any_bip.md`: Proposition 7.5 for every `q ≥ 2`

`q_any_bip.md`, **Proofs, "What the earlier proofs use", item 5** (*Proposition 7.5, the three
lifts*): Proposition 7.5 of `q_bip_P3.md` (`BipP3.prop75`, stated there for `q ≥ 3` odd) holds for
every `q ≥ 2` such that `C(q − 1, t) ≠ 0` in `F` for `0 ≤ t ≤ q − 1`, without parity.  The proofs
are those of `RequestProject/BipP3/Main.lean`; the lifts of the cases (α), (β), (γ)
(`BipP3.mem_Wslice_of_insert`, `BipP3.mem_Wslice_of_pair`) are already stated there for `q ≥ 1`,
and the remaining uses of `q ≥ 3` go through Lemma 7.1 and Lemma 7.3, re-proved for `q ≥ 2` in
`RequestProject/BipAny/Peeling.lean` and `RequestProject/BipAny/Layers.lean`.
-/

@[expose] public section

namespace BipAny

open Bip ChainLemma Tight

set_option synthInstance.maxHeartbeats 200000

variable {F : Type*} [Field F] {q : ℕ}

/-- `q_any_bip.md`, **Proofs, items 1 and 5** (Step 1 of the Proof of Proposition 7.5 in
`q_bip_P3.md`, for every `q ≥ 2`): iterating Lemma 7.1 (ii), `W_d(V) ⊆ W_{d'}(V)` for
`d ≤ d' ≤ q − 1`.  Same statement as `BipP3.Wslice_mono_le`, with `q ≥ 2` instead of `q ≥ 3`. -/
theorem Wslice_mono_le (hq : 2 ≤ q) {α β : ℕ} (hα : 1 ≤ α) (V : Ideal (R F q α β)) {d d' : ℕ}
    (hdd' : d ≤ d') (hd' : d' ≤ q - 1) : Wslice F q hα V d ≤ Wslice F q hα V d' := by
  induction d', hdd' using Nat.le_induction with
  | base => exact le_rfl
  | succ k hk ih => exact (ih (by omega)).trans (BipAny.Wslice_mono (F := F) hq hα V k (by omega))

/-- `q_any_bip.md`, **Proofs, item 5** (Step 1 of the Proof of Proposition 7.5 in `q_bip_P3.md`,
for every `q ≥ 2`): for `μ ∈ Λ_i` and every tight pattern of `μ` on `([α − 1], [β])` with product
`G`, `G ∈ W_{q−1−i}(V_Λ)`.  Same statement as `BipP3.prod_mem_Wslice`, with `q ≥ 2` instead of
`q ≥ 3`; the case analysis (α), (β), (γ) is that of the original proof. -/
theorem prod_mem_Wslice (hq : 2 ≤ q)
    (hbin : ∀ t, t ≤ q - 1 → (((q - 1).choose t : ℕ) : F) ≠ 0) {α β : ℕ} (hα : 1 ≤ α)
    {Λ : Set (Partition × Partition)} (hΛ : IsDownSetB q α β Λ) {i : ℕ} (hi : i ≤ q - 1)
    {μ : Partition × Partition} (hμ : μ ∈ BPar q (α - 1) β) (hiΦ : i < FLamB q Λ μ)
    (T : BTightPattern μ (α - 1) β) :
    T.prod F q ∈ Wslice F q hα (VLamB F q α β Λ) (q - 1 - i) := by
  have hΦq := FLamB_le q Λ μ
  rcases BipAny.lemma73_v hq hα hμ hΛ (by omega) with ⟨hA, -, -⟩ | ⟨-, hB, -⟩ | ⟨-, -, hC⟩
  · -- case (α)
    obtain ⟨h1, hj, hjl, heq, hmem, hfirst⟩ := hA
    set j0 := q + 1 - FLamB q Λ μ with hj0
    have hcs := Lifts.colLen_row_succ μ.1 hj hjl (fun h2 => hfirst.resolve_left (by omega))
    rw [← heq] at hmem
    have h := BipP3.mem_Wslice_of_insert (F := F) (q := q) (by omega) hα hmem T
      (cs := μ.1.row j0 + 1) (by omega) (fun c _ => Lifts.colLen_addE μ.1 hj hjl c) (by omega)
    rw [hcs] at h
    exact BipAny.Wslice_mono_le hq hα _ (by omega) (by omega) h
  · -- case (β)
    obtain ⟨h1, h2, h3, h4, heq, hmem⟩ := hB
    rw [← heq] at hmem
    have h := BipP3.mem_Wslice_of_insert (F := F) (q := q) (by omega) hα hmem T (cs := 1) le_rfl
      (fun c hc => Lifts.colLen_addOne μ.1 hc) (by rw [Lifts.colLen_one]; omega)
    rw [Lifts.colLen_one] at h
    exact BipAny.Wslice_mono_le hq hα _ (by omega) (by omega) h
  · -- case (γ)
    obtain ⟨h1, h2, heq, hmem, hlast⟩ := hC
    rw [← heq] at hmem
    have hr := Lifts.colLen_row μ.2 h1 h2 (fun h => hlast.resolve_left (by omega))
    have h := BipP3.mem_Wslice_of_pair (F := F) (q := q) (by omega) hα hmem T
      (c0 := μ.2.row (FLamB q Λ μ)) (μ.2.row_pos _ h1 h2)
      (fun c hc => Lifts.colLen_subE μ.2 h1 h2 hc) (by omega) (by omega)
      (hbin _ (by omega))
    rw [hr] at h
    exact BipAny.Wslice_mono_le hq hα _ (by omega) (by omega) h

/-- `q_any_bip.md`, **Proofs, item 5** (Proposition 7.5 of `q_bip_P3.md` for every `q ≥ 2`, no
parity): let `F` be a field and `q ≥ 2` with `C(q−1, t) ≠ 0` in `F` for `0 ≤ t ≤ q − 1`; let
`α ≥ 1` and `Λ` a down-set of `BPar_q(α, β)`.  Then for every `i ∈ {0, …, q − 1}`,
`V_{Λ_i} ⊆ W_{q−1−i}(V_Λ)`.  Same statement as `BipP3.prop75`, with `q ≥ 2` instead of `q ≥ 3` and
without the hypothesis that `q` is odd. -/
theorem prop75 (hq : 2 ≤ q)
    (hbin : ∀ t, t ≤ q - 1 → (((q - 1).choose t : ℕ) : F) ≠ 0) {α β : ℕ} (hα : 1 ≤ α)
    (Λ : Set (Partition × Partition)) (hΛ : IsDownSetB q α β Λ) (i : ℕ) (hi : i ≤ q - 1) :
    (VLamB F q (α - 1) β (LamLayer q α β Λ i) : Set (R F q (α - 1) β)) ⊆
      Wslice F q hα (VLamB F q α β Λ) (q - 1 - i) := by
  obtain ⟨I, hI⟩ := BipAny.Wslice_isIdeal (F := F) hq hα (VLamB F q α β Λ) (q - 1 - i) (by omega)
  have hle : VLamB F q (α - 1) β (LamLayer q α β Λ i) ≤ I := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨μ, ⟨hμ, hiΦ⟩, T, rfl⟩
    rw [hI]
    exact BipAny.prod_mem_Wslice (F := F) hq hbin hα hΛ hi hμ hiΦ T
  intro g hg
  have := hle hg
  rw [← SetLike.mem_coe, hI] at this
  exact this

end BipAny

end

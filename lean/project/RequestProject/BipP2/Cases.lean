module

public import RequestProject.BipOpt.Main
public import RequestProject.Monotone.Main

/-!
# The nine cases of the proof of Proposition 7.4 (i) of `q_bip_P2.md`

The **Proof** of **Proposition 7.4 (i)** of `q_bip_P2.md` distinguishes, for a position `p`, the
type of `p` for `μ` and for `μ̃` (removal R, middle position M, addition A), giving the nine
cases RR, AA, MM, RM, RA, AM, MA, MR, AR.  This file proves one lemma per case (the partition-level
comparisons (a), (b), (c), (e2), (T), (5.2) are reused from `RequestProject/Monotone/`).
Throughout, `μ̃` of the file is written `ν`.
-/

@[expose] public section

namespace Bip

open ChainLemma ChainLemma.Partition

/-! ### Partition-level facts used in the cases MA, MR, AR -/

/-- Proof of **Proposition 7.4 (i)** of `q_bip_P2.md` (auxiliary): the partial sums `S_t` are
weakly increasing in `t`. -/
lemma p2_S_mono (μ : Partition) {m n : ℕ} (h : m ≤ n) : S m μ ≤ S n μ := by
  rw [S_add_Ioc μ h]; omega

/-- Proof of **Proposition 7.4 (i)** of `q_bip_P2.md` (auxiliary): `S_t(λ) ≤ |λ|` for every `t`. -/
lemma p2_S_le_size (μ : Partition) (t : ℕ) : S t μ ≤ μ.size := by
  rcases le_total t μ.len with h | h
  · rw [← S_eq_size μ le_rfl]; exact p2_S_mono μ h
  · rw [S_eq_size μ h]

/-- Proof of **Proposition 7.4 (i)** of `q_bip_P2.md`, case **MA** (and the size comparison used
there): `λ ≼ λ̃` gives `|λ| ≤ |λ̃|` ("by dominance at large `t`"). -/
lemma p2_size_le {μ ν : Partition} (hle : μ ≼ ν) : μ.size ≤ ν.size := by
  have := hle.le_all (max μ.len ν.len)
  rwa [S_eq_size μ (le_max_left _ _), S_eq_size ν (le_max_right _ _)] at this

/-- Proof of **Proposition 7.4 (i)** of `q_bip_P2.md`, case **MA**: for partitions `λ ≼ λ̃` and
`ℓ(λ) < j ≤ ℓ(λ̃)`, `λ ⊔ 1 ≼ λ̃ + e_j`.  (Following the file: dominance for `t ≤ ℓ(λ)`, (5.2) for
`ℓ(λ) < t ≤ ℓ(λ̃)`, and `|λ̃| + 1 ≥ |λ| + 1` for `t > ℓ(λ̃)`.) -/
lemma p2_addOne_le_addE {μ ν : Partition} (hle : μ ≼ ν) {j : ℕ} (hjμ : μ.len < j)
    (hjν : j ≤ ν.len) : μ.addOne ≼ ν.addE j := by
  intro t ht
  rw [S_addOne μ t ht, S_addE ν t j ht (by omega) hjν]
  have hA := hle t ht
  have hB : μ.len ≤ t → t ≤ ν.len → S t μ + (t - μ.len) ≤ S t ν := gap_estimate hle
  have hC1 : ν.len ≤ t → S t ν = ν.size := fun h => S_eq_size ν h
  have hC2 : μ.len ≤ t → S t μ = μ.size := fun h => S_eq_size μ h
  have hD := p2_size_le hle
  have hr := ν.rlow_le (by omega : 1 ≤ j) hjν
  split_ifs <;> omega

/-- Proof of **Proposition 7.4 (i)** of `q_bip_P2.md`, case **MR**, size estimate: if `λ ≼ λ̃`
and `ℓ(λ) < p ≤ ℓ(λ̃)`, then `|λ̃| ≥ |λ| + 1` (by (5.2) at `t = ℓ(λ̃)`). -/
lemma p2_size_succ_le {μ ν : Partition} (hle : μ ≼ ν) {p : ℕ} (hpμ : μ.len < p)
    (hpν : p ≤ ν.len) : μ.size + 1 ≤ ν.size := by
  have := gap_estimate hle (show μ.len ≤ ν.len by omega) le_rfl
  rw [S_eq_size μ (by omega), S_eq_size ν le_rfl] at this
  omega

/-- Proof of **Proposition 7.4 (i)** of `q_bip_P2.md`, case **MR**, first components: if
`λ ≼ λ̃` and `|λ̃| ≥ |λ| + 1`, then `λ ⊔ 1 ≼ λ̃` (dominance for `t ≤ ℓ(λ)`; for `t > ℓ(λ)`, (5.2)
if `t ≤ ℓ(λ̃)` and `|λ̃| ≥ |λ| + 1` if `t ≥ ℓ(λ̃)`). -/
lemma p2_addOne_le_of_size {μ ν : Partition} (hle : μ ≼ ν) (hs : μ.size + 1 ≤ ν.size) :
    μ.addOne ≼ ν := by
  intro t ht
  rw [S_addOne μ t ht]
  have hA := hle t ht
  have hB : μ.len ≤ t → t ≤ ν.len → S t μ + (t - μ.len) ≤ S t ν := gap_estimate hle
  have hC1 : ν.len ≤ t → S t ν = ν.size := fun h => S_eq_size ν h
  have hC2 : μ.len ≤ t → S t μ = μ.size := fun h => S_eq_size μ h
  split_ifs with h
  · rcases le_total t ν.len with h' | h'
    · have := hB h.le h'; omega
    · have := hC1 h'; have := hC2 h.le; omega
  · omega

/-- Proof of **Proposition 7.4 (i)** of `q_bip_P2.md`, case **MR**, second components (also used
in case **AR**, "it only used `ℓ_− < p ≤ ℓ̃_−`"): if `λ ≼ λ̃` and `ℓ(λ) < p ≤ ℓ(λ̃)`, then
`λ ≼ λ̃ − e_p`.  For `t < r̄_p(λ̃)` this is dominance; for `t ≥ r̄_p(λ̃) ≥ p > ℓ(λ)`,
`S_t(λ̃) ≥ S_{ℓ(λ)}(λ̃) + (p − ℓ(λ)) ≥ |λ| + 1`. -/
lemma p2_le_subE {μ ν : Partition} (hle : μ ≼ ν) {p : ℕ} (hpμ : μ.len < p) (hpν : p ≤ ν.len) :
    μ ≼ ν.subE p := by
  intro t ht
  rw [S_subE ν t p ht (by omega) hpν]
  have hA := hle t ht
  have hrb := ν.le_rbar (by omega : 1 ≤ p) hpν
  split_ifs with h
  · have h1 := ν.S_add_le_of_le_len (show μ.len ≤ p by omega) hpν
    have h2 := hle.le_all μ.len
    have h3 := S_eq_size μ (le_refl μ.len)
    have h4 := S_eq_size μ (show μ.len ≤ t by omega)
    have h5 := p2_S_mono ν (show p ≤ t by omega)
    omega
  · omega

/-- Proof of **Proposition 7.4 (i)** of `q_bip_P2.md`, case **AR**, first components: if
`λ ≼ λ̃`, `1 ≤ j ≤ ℓ(λ)`, `ℓ(λ̃) ≤ j − 1` and `|λ̃| ≥ |λ| + 1`, then `λ + e_j ≼ λ̃`.  We need
`S_t(λ) + [t ≥ r̲_j(λ)] ≤ S_t(λ̃)`: dominance for `t < r̲_j(λ)`, the size for `t ≥ ℓ(λ̃)`, and for
`r̲_j(λ) ≤ t < ℓ(λ̃)` a tight `t` is impossible (by (T), the rows of `λ̃` after the `t`-th are
`≤ λ_j`, and `λ̃_j = 0`, so `S_j(λ̃) < S_j(λ)`). -/
lemma p2_addE_le_of_size {μ ν : Partition} (hle : μ ≼ ν) {j : ℕ} (hj : 1 ≤ j)
    (hjμ : j ≤ μ.len) (hjν : ν.len < j) (hs : μ.size + 1 ≤ ν.size) : μ.addE j ≼ ν := by
  intro t ht
  rw [S_addE μ t j ht hj hjμ]
  have h0 := hle t ht
  have hC1 : ν.len ≤ t → S t ν = ν.size := fun h => S_eq_size ν h
  have hsz := p2_S_le_size μ t
  have key : μ.rlow j ≤ t → t < ν.len → S t μ < S t ν := by
    intro h1 h2
    by_contra hc
    have tight : S t μ = S t ν := by omega
    have hrow : ∀ s, t ≤ s → s ≤ j → μ.row s = μ.row j := fun s h1' h2' =>
      μ.row_eq_of_rlow_le hj hjμ (by omega) h2'
    have := μ.row_pos j hj hjμ
    have := row_eq_zero' ν hjν
    exact no_tight_drop hle ht tight (by omega) hrow (by omega)
  split_ifs with h
  · rcases lt_or_ge t ν.len with h' | h'
    · have := key h h'; omega
    · have := hC1 h'; omega
  · omega

/-! ### The nine cases -/

variable {μ ν : Partition × Partition}

/-- **Transfer of sizes** in the **Proof** of **Proposition 7.4** of `q_bip_P2.md`: for
`μ, μ̃ ∈ BPar_q(α − 1, β)`, `|μ_+| − |μ_−| = |μ̃_+| − |μ̃_−|`. -/
lemma p2_transfer {q α β : ℕ} (hμ : μ ∈ BPar q (α - 1) β) (hν : ν ∈ BPar q (α - 1) β) :
    (μ.1.size : ℤ) - μ.2.size = ν.1.size - ν.2.size := by
  rw [hμ.1, hν.1]

/-- Case **RR** of the Proof of **Proposition 7.4 (i)** of `q_bip_P2.md`
(`p ≤ min(ℓ_−, ℓ̃_−)`): `(μ_+, μ_− − e_p) ≼ (μ̃_+, μ̃_− − e_p)`, by (a). -/
lemma p2_case_RR (hle : BWeakDom μ ν) {p : ℕ} (hp : 1 ≤ p) (hpμ : p ≤ μ.2.len)
    (hpν : p ≤ ν.2.len) : BWeakDom (μ.1, μ.2.subE p) (ν.1, ν.2.subE p) :=
  ⟨hle.1, case_a hle.2 hp hpμ hpν⟩

/-- Case **AA** of the Proof of **Proposition 7.4 (i)** of `q_bip_P2.md`
(`j ≤ min(ℓ_+, ℓ̃_+)`): `(μ_+ + e_j, μ_−) ≼ (μ̃_+ + e_j, μ̃_−)`, by (b). -/
lemma p2_case_AA (hle : BWeakDom μ ν) {j : ℕ} (hj : 1 ≤ j) (hjμ : j ≤ μ.1.len)
    (hjν : j ≤ ν.1.len) : BWeakDom (μ.1.addE j, μ.2) (ν.1.addE j, ν.2) :=
  ⟨case_b hle.1 hj hjμ hjν, hle.2⟩

/-- Case **MM** of the Proof of **Proposition 7.4 (i)** of `q_bip_P2.md`:
`(μ_+ ⊔ 1, μ_−) ≼ (μ̃_+ ⊔ 1, μ̃_−)`, by (c). -/
lemma p2_case_MM (hle : BWeakDom μ ν) : BWeakDom (μ.1.addOne, μ.2) (ν.1.addOne, ν.2) :=
  ⟨case_c hle.1, hle.2⟩

/-- Case **RM** of the Proof of **Proposition 7.4 (i)** of `q_bip_P2.md`:
`opt_p(μ) = (μ_+, μ_− − e_p) ≼ μ ≼ μ̃ ≼ (μ̃_+ ⊔ 1, μ̃_−) = opt_p(μ̃)` (the chain of Lemma 7.3 (iii),
via part (a) of `q_chain_lemma.md`). -/
lemma p2_case_RM (hle : BWeakDom μ ν) {p : ℕ} (hp : 1 ≤ p) (hpμ : p ≤ μ.2.len) :
    BWeakDom (μ.1, μ.2.subE p) (ν.1.addOne, ν.2) :=
  ⟨hle.1.trans ν.1.self_le_addOne, (μ.2.subE_le_self p hp hpμ).trans hle.2⟩

/-- Case **RA** of the Proof of **Proposition 7.4 (i)** of `q_bip_P2.md`:
`opt_p(μ) = (μ_+, μ_− − e_p) ≼ μ ≼ μ̃ ≼ (μ̃_+ + e_j, μ̃_−) = opt_p(μ̃)` (the chain of
Lemma 7.3 (iii), via part (a) of `q_chain_lemma.md`). -/
lemma p2_case_RA (hle : BWeakDom μ ν) {p j : ℕ} (hp : 1 ≤ p) (hpμ : p ≤ μ.2.len) (hj : 1 ≤ j)
    (hjν : j ≤ ν.1.len) : BWeakDom (μ.1, μ.2.subE p) (ν.1.addE j, ν.2) :=
  ⟨hle.1.trans (ν.1.self_le_addE j hj hjν), (μ.2.subE_le_self p hp hpμ).trans hle.2⟩

/-- Case **AM** of the Proof of **Proposition 7.4 (i)** of `q_bip_P2.md` (`j ≤ ℓ_+` and
`ℓ̃_+ < j`): `(μ_+ + e_j, μ_−) ≼ (μ̃_+ ⊔ 1, μ̃_−)`, by (e2). -/
lemma p2_case_AM (hle : BWeakDom μ ν) {j : ℕ} (hjν : ν.1.len < j) (hjμ : j ≤ μ.1.len) :
    BWeakDom (μ.1.addE j, μ.2) (ν.1.addOne, ν.2) :=
  ⟨case_e2 hle.1 hjν hjμ, hle.2⟩

/-- Case **MA** of the Proof of **Proposition 7.4 (i)** of `q_bip_P2.md` (`j > ℓ_+`, `j ≤ ℓ̃_+`):
`(μ_+ ⊔ 1, μ_−) ≼ (μ̃_+ + e_j, μ̃_−)`. -/
lemma p2_case_MA (hle : BWeakDom μ ν) {j : ℕ} (hjμ : μ.1.len < j) (hjν : j ≤ ν.1.len) :
    BWeakDom (μ.1.addOne, μ.2) (ν.1.addE j, ν.2) :=
  ⟨p2_addOne_le_addE hle.1 hjμ hjν, hle.2⟩

/-- Case **MR** of the Proof of **Proposition 7.4 (i)** of `q_bip_P2.md` (`p > ℓ_−`,
`p ≤ ℓ̃_−`), for `μ, μ̃ ∈ BPar_q(α − 1, β)`: `(μ_+ ⊔ 1, μ_−) ≼ (μ̃_+, μ̃_− − e_p)`.  (Uses the
transfer of sizes: `|μ̃_−| ≥ |μ_−| + 1` gives `|μ̃_+| ≥ |μ_+| + 1`.) -/
lemma p2_case_MR {q α β : ℕ} (hμ : μ ∈ BPar q (α - 1) β) (hν : ν ∈ BPar q (α - 1) β)
    (hle : BWeakDom μ ν) {p : ℕ} (hpμ : μ.2.len < p) (hpν : p ≤ ν.2.len) :
    BWeakDom (μ.1.addOne, μ.2) (ν.1, ν.2.subE p) := by
  have h1 := p2_size_succ_le hle.2 hpμ hpν
  have h2 := p2_transfer hμ hν
  have h3 : μ.1.size + 1 ≤ ν.1.size := by omega
  exact ⟨p2_addOne_le_of_size hle.1 h3, p2_le_subE hle.2 hpμ hpν⟩

/-- Case **AR** of the Proof of **Proposition 7.4 (i)** of `q_bip_P2.md` (`j ≤ ℓ_+`,
`p ≤ ℓ̃_−`, with `j = q + 1 − p`), for `μ, μ̃ ∈ BPar_q(α − 1, β)`:
`(μ_+ + e_j, μ_−) ≼ (μ̃_+, μ̃_− − e_p)`.  (Here `ℓ_− < p` and `ℓ̃_+ ≤ j − 1` follow from
`ℓ_+ + ℓ_− ≤ q`, `ℓ̃_+ + ℓ̃_− ≤ q`.) -/
lemma p2_case_AR {q α β : ℕ} (hμ : μ ∈ BPar q (α - 1) β) (hν : ν ∈ BPar q (α - 1) β)
    (hle : BWeakDom μ ν) {p : ℕ} (hpq : p ≤ q) (hjμ : q + 1 - p ≤ μ.1.len)
    (hpν : p ≤ ν.2.len) : BWeakDom (μ.1.addE (q + 1 - p), μ.2) (ν.1, ν.2.subE p) := by
  have hlμ := hμ.2.2
  have hlν := hν.2.2
  have hpμ : μ.2.len < p := by omega
  have h1 := p2_size_succ_le hle.2 hpμ hpν
  have h2 := p2_transfer hμ hν
  have h3 : μ.1.size + 1 ≤ ν.1.size := by omega
  exact ⟨p2_addE_le_of_size hle.1 (by omega) hjμ (by omega) h3, p2_le_subE hle.2 hpμ hpν⟩

end Bip

end

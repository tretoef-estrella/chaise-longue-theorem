module

public import RequestProject.ColUpper.Main
public import RequestProject.ColCount.Main
public import RequestProject.ColOne.Main
public import RequestProject.ColPairs.Main
public import RequestProject.ColDecomp.Main

/-!
# Proposition 6.9 (the colour reduction) of `q_col_assembly.md`

For a field `F` with the Setting of `q_col_splitting.md` (bundled in `S : ColSplit.ColSetting F`),
with `p ≠ 2` and `r` odd, `dim_F I_F = Q_k(m)` (`ColAssembly.prop69`), where
`I_F = ColUpper.IK F S.m k` is the ideal `(ψ_J : J)` of `F[G]` of `q_col_upper.md`.

The proof follows the file: the lower bound sums the bounds of Lemmas 6.6 and 6.7 over the
colourings, using Lemma 6.1 (ii), Proposition 6.5 (iii), Lemma 6.3 (iv) and Lemma 6.8; the upper
bound is (iv) of `q_col_upper.md`.
-/

@[expose] public section

namespace ColAssembly

open ColSplit ColSurv ColComp ColDecomp ColCount ColUpper TheoremB

set_option synthInstance.maxHeartbeats 200000

open scoped Classical

variable {F : Type*} [Field F] (S : ColSetting F) {k : ℕ}

/-- **Proof of Proposition 6.9** in `q_col_assembly.md` (first sentence of the lower bound):
`I_F` is the ideal `I` of `q_col_decomp.md` (by the compatibility of the two `ψ_J`). -/
theorem IK_eq_idealI : IK F S.m k = idealI S k := rfl

/-- **Proof of Proposition 6.9** in `q_col_assembly.md` (the bound `dim I_{c,1} ≥ N_1(c)`): if
some matching is compatible with `c`, then `dim I_{c,1} ≥ N_1(c)` (via Lemma 6.3 (iv),
Lemma 6.6 (ii) with Theorem (ii) of `q_theorem_B_lower.md`, and Lemma 6.6 (iii)). -/
theorem N1_le (hp : S.p ≠ 2) (c : Fin (2 * k + 1) → S.μ) (heven : Even (cls (cExt c) 1).card) :
    N1 hp c ≤ Module.finrank F (Ic1 S c) := by
  obtain ⟨n, hn⟩ := heven
  by_cases h0 : (0 : Fin (2 * k + 2)) ∈ cls (cExt c) 1
  · have hpos : 0 < (cls (cExt c) 1).card := Finset.card_pos.2 ⟨_, h0⟩
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    have hs : (cls (cExt c) 1).card = 2 * j + 2 := by omega
    have h := (ColOne.lemma66_ii S hp c h0 hs).2
    unfold N1
    rw [hs, card_closedTuples]
    exact h
  · have hs : (cls (cExt c) 1).card = 2 * n := by omega
    have h := ColOne.lemma66_iii S hp c h0 hs
    unfold N1
    rw [hs]
    exact h

/-- **Proof of Proposition 6.9** in `q_col_assembly.md` (the bound `dim I_{c,ζ} ≥ N_ζ(c)`,
Lemma 6.7 (vi)). -/
theorem Nz_le (hp : S.p ≠ 2) {R : Finset F} (hR : IsReps S R) {ζ : F} (hζ : ζ ∈ R)
    (c : Fin (2 * k + 1) → S.μ) (hAB : (cls (cExt c) ζ).card = (cls (cExt c) ζ⁻¹).card) :
    Nz c ζ ≤ Module.finrank F (Icz S c ζ) := by
  have h := ColPairs.lemma67_vi hR hζ c hp hAB
  unfold Nz
  split_ifs with h0
  · exact h.2 h0
  · exact h.1 h0

/-- **Proof of Proposition 6.9** in `q_col_assembly.md` (the term for a fixed colouring `c`):
`dim_F π_c(I) ≥ N_1(c)·Π_{ζ∈ℛ} N_ζ(c)` if some matching is compatible with `c`, and `≥ 0`
otherwise. -/
theorem term_le (hp : S.p ≠ 2) {R : Finset F} (hR : IsReps S R) (c : Fin (2 * k + 1) → S.μ) :
    (if ∃ J : BallotBound.Matching k, Compatible (cExt c) J then N1 hp c * ∏ ζ ∈ R, Nz c ζ
      else 0) ≤ Module.finrank F (((idealI S k).map (S.piC c)).restrictScalars F) := by
  split_ifs with hJ
  · have h65 := (prop65_iii S c hR).1 hJ
    obtain ⟨heven, hcard⟩ := (lemma63_iv_exists hR (cExt_mem c)).1 hJ
    change _ ≤ Module.finrank F ((idealI S k).map (S.piC c))
    rw [h65]
    exact Nat.mul_le_mul (N1_le S hp c heven)
      (Finset.prod_le_prod' fun ζ hζ => Nz_le S hp hR hζ c (hcard ζ hζ))
  · exact Nat.zero_le _

/-- **Proposition 6.9** of `q_col_assembly.md`, lower bound: with the Setting of
`q_col_splitting.md`, `p ≠ 2` and `r` odd, `dim_F I_F ≥ Q_k(m)`. -/
theorem prop69_lower (hp : S.p ≠ 2) (hr : Odd S.r) :
    Qk k S.m ≤ Module.finrank F ((IK F S.m k).restrictScalars F) := by
  obtain ⟨R, hR⟩ := lemma63_i_exists_reps hr
  rw [IK_eq_idealI, S.lemma61_ii, ← lemma68_iii hp hr hR k]
  exact Finset.sum_le_sum fun c _ => term_le S hp hR c

/-- **Proof of Proposition 6.9** in `q_col_assembly.md` (upper bound): `m = q·r` is odd, since
`q` is a power of the odd prime `p` and `r` is odd. -/
theorem odd_m (hp : S.p ≠ 2) (hr : Odd S.r) : Odd S.m :=
  (Odd.pow (S.hp.odd_of_ne_two hp)).mul hr

/-- **Proposition 6.9** of `q_col_assembly.md` (the colour reduction): let `F` be a field with
the Setting of `q_col_splitting.md` (characteristic `p`, `q = p^v`, `r`, `μ`, `m = q·r`), with
`p ≠ 2` and `r` odd. Then `dim_F I_F = Q_k(m)`. -/
theorem prop69 (hp : S.p ≠ 2) (hr : Odd S.r) :
    Module.finrank F ((IK F S.m k).restrictScalars F) = Qk k S.m :=
  le_antisymm (finrank_IK_le F (odd_m S hp hr) k) (prop69_lower S hp hr)

end ColAssembly

end

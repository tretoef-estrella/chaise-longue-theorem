module

public import RequestProject.OddPatterns.Defs

/-!
# Lemma D of `q_oddbox_patterns.md`: Lemma 8.7 in the ring `C_m`

(D1) `y_i^{2h+1} = 0`, (D2) the generators of `Membership.UB` in `C_m`, (D3) the marked block
lies in `𝔘_{ℓ+1}(y; B)`.
-/

@[expose] public section

namespace OddPatterns

open Pfaffian

set_option synthInstance.maxHeartbeats 200000

variable {F : Type*} [Field F] {h : ℕ}

/-- **Lemma D, (D1)** of `q_oddbox_patterns.md`: `y_i^{2h+1} = 0` in `C_m` for every `i` (the
defining relations of `C_m`, `q − 1 = 2h + 1`). This holds for every `h`. -/
theorem D1 {m : ℕ} (i : Fin m) : Tight.y F (2 * h + 2) i ^ (2 * h + 1) = 0 := by
  unfold Tight.y
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span ⟨i, rfl⟩

/-- **Lemma D, (D2)** of `q_oddbox_patterns.md`, first part: for a set `P` of subsets of `Fin m`,
`Membership.DPy (2h+1) y P = Π_{e ∈ P} Tight.pairD F (2h+2) e`. This holds for every `h`. -/
theorem D2_DPy {m : ℕ} (P : Finset (Finset (Fin m))) :
    Membership.DPy (2 * h + 1) (Tight.y F (2 * h + 2)) P =
      ∏ e ∈ P, Tight.pairD F (2 * h + 2) e := rfl

/-- **Lemma D, (D2)** of `q_oddbox_patterns.md`, second part:
`Tight.vand y S = Tight.Delta F (2h+2) S`. This holds for every `h`. -/
theorem D2_vand {m : ℕ} (S : Finset (Fin m)) :
    Tight.vand (Tight.y F (2 * h + 2)) S = Tight.Delta F (2 * h + 2) S := rfl

/-- **Lemma D, (D3)** of `q_oddbox_patterns.md` (Lemma 8.7): let `h ≥ 1`. For `ℓ ≥ 0` and
`B ⊆ Fin m` with `|B| = ℓ + 1 + 2t`, `Pf_{E_ℓ}(B) ∈ 𝔘_{ℓ+1}(y; B)`, i.e.
`markedPf F h ℓ B ∈ Membership.UB (2h+1) (ℓ+1) y B`. -/
theorem D3 (hh : 1 ≤ h) {m : ℕ} (l : ℕ) (B : Finset (Fin m)) (t : ℕ)
    (hB : B.card = l + 1 + 2 * t) :
    markedPf F h l B ∈ Membership.UB (2 * h + 1) (l + 1) (Tight.y F (2 * h + 2)) B := by
  unfold markedPf mPf
  split_ifs with hl
  · subst hl
    have := Membership.M4b hh t (Tight.y F (2 * h + 2)) (fun i => D1 i) B rfl
      (s := 0) (by omega) Fin.elim0
    have e : (Fin.snoc (α := fun _ => Fin B.card → Peel.C F (2 * h + 2) m)
        (fun k i => Tight.y F (2 * h + 2) (B.orderEmbOfFin rfl i) ^ (Fin.elim0 k : ℕ))
        (fun i => Tight.y F (2 * h + 2) (B.orderEmbOfFin rfl i) ^ (2 * h)) :
          Fin 1 → Fin B.card → Peel.C F (2 * h + 2) m) =
        fun _ i => Tight.y F (2 * h + 2) (B.orderEmbOfFin rfl i) ^ (2 * h) := by
      funext k i
      rw [Fin.fin_one_eq_zero k]
      rfl
    rw [e] at this
    exact this
  · have := Membership.M4a hh t (Tight.y F (2 * h + 2)) (fun i => D1 i) B rfl
      (s := l - 1) (by omega) (fun k : Fin (l - 1) => (k : ℕ))
    rw [show l - 1 + 2 = l + 1 by omega] at this
    exact this

end OddPatterns

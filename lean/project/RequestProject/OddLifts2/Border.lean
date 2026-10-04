module

public import RequestProject.OddLifts2.LemmaQp
public import RequestProject.OddLifts2.Patterns

/-!
# The second term of (T7) of `q_oddbox_lifts_2.md`: the border `D(y_0, ·)`

For `B ⊆ Fin n` with increasing enumeration `b_1 < ⋯ < b_k`, the element
`Ψ_ℓ(B) := Pf(y_{B^+}; y_{B^+}^0, …, y_{B^+}^{ℓ−1}, D(y_0, ·)) ∈ C_{n+1}` (`Psi`) is the second
term of the element `f` of the proof of (T7).  This file proves
* `phi_Psi`: under `peelEquiv'`, `Ψ_ℓ(B)` is the class of the second term of `Φ` of Lemma Q′, with
  `w_j = y_{b_j}`;
* `Psi_mem`: the expansion of `Ψ_ℓ(B)` along its last border (`Pfaffian.bpf_expand_last`) into
  the terms `± D(y_0, y_{b+1}) · incl(Pf_{E_{ℓ+1}}(B ∖ b))`;
* `markedPf_eq_Delta`: for `|S| = ℓ`, `Pf_{E_{ℓ+1}}(S) = ±Δ(S)` (`Pfaffian.C5`).
-/

@[expose] public section

open Polynomial Pfaffian ColOne

namespace OddLifts2

open Peel hiding C
open Tight ChainLemma OddPatterns Lifts OddLifts

set_option synthInstance.maxHeartbeats 200000

/-- Auxiliary for (T7) of `q_oddbox_lifts_2.md`: the bordered Pfaffians `Pf(y; c)` commute with
ring homomorphisms. -/
theorem map_Pf {A A' : Type*} [CommRing A] [CommRing A'] (f : A →+* A') (r : ℕ) {n s : ℕ}
    (v : Fin n → A) (c : Fin s → Fin n → A) :
    f (Pf r v c) = Pf r (fun i => f (v i)) (fun k i => f (c k i)) := by
  unfold Pf bpf
  rw [OddPatterns.map_pf]
  congr 1
  funext p q
  induction p using Fin.addCases with
  | left i =>
    induction q using Fin.addCases with
    | left j => simp [ay, map_Dab]
    | right k => simp
  | right k =>
    induction q using Fin.addCases with
    | left j => simp
    | right k' => simp

/-- Auxiliary for (T7) of `q_oddbox_lifts_2.md`: the increasing enumeration of `B ∖ {b_j}` is the
increasing enumeration of `B` composed with `j.succAbove`. -/
theorem orderEmbOfFin_erase {n k : ℕ} (B : Finset (Fin n)) (hB : B.card = k + 1) (b : Fin (k + 1))
    (h' : (B.erase (B.orderEmbOfFin hB b)).card = k) (j : Fin k) :
    (B.erase (B.orderEmbOfFin hB b)).orderEmbOfFin h' j = B.orderEmbOfFin hB (b.succAbove j) := by
  have := Finset.orderEmbOfFin_unique h' (f := fun j => B.orderEmbOfFin hB (b.succAbove j))
    (fun j => Finset.mem_erase.2 ⟨fun he => Fin.succAbove_ne b j
      ((B.orderEmbOfFin hB).injective he), Finset.orderEmbOfFin_mem B hB _⟩)
    (fun a c hac => (B.orderEmbOfFin hB).strictMono (Fin.strictMono_succAbove b hac))
  exact (congrFun this j).symm

variable (F : Type*) [Field F] (h : ℕ)

/-- Auxiliary for (T7) of `q_oddbox_lifts_2.md`: the marked block `B ∖ {b_j}` is the marked
Pfaffian of `(y_{b_i})_{i ≠ j}`. -/
theorem markedPf_erase (L : ℕ) {n k : ℕ} (B : Finset (Fin n)) (hB : B.card = k + 1)
    (b : Fin (k + 1)) :
    markedPf F h L (B.erase (B.orderEmbOfFin hB b)) =
      mPf h L (fun j : Fin k => y F (2 * h + 2) (B.orderEmbOfFin hB (b.succAbove j))) := by
  have hc : (B.erase (B.orderEmbOfFin hB b)).card = k := by
    rw [Finset.card_erase_of_mem (Finset.orderEmbOfFin_mem B hB b), hB, Nat.add_sub_cancel]
  unfold markedPf
  rw [← mPf_cast h L hc.symm]
  congr 1
  funext i
  rw [← orderEmbOfFin_cast _ hc, orderEmbOfFin_erase B hB b hc]

/-- Auxiliary for (T7) of `q_oddbox_lifts_2.md` (case `t = 0`): for `|S| = ℓ`, the marked Pfaffian
`Pf_{E_{ℓ+1}}(S) = Pf_{(0, …, ℓ−1)}(y_S)` is `(−1)^{ℓ(ℓ−1)/2} Δ(S)` (`Pfaffian.C5` and
`Membership.V2`). -/
theorem markedPf_eq_Delta {m : ℕ} (l : ℕ) (S : Finset (Fin m)) (hS : S.card = l) :
    markedPf F h (l + 1) S = (-1) ^ (l * (l - 1) / 2) * Delta F (2 * h + 2) S := by
  unfold markedPf
  rw [← mPf_cast h (l + 1) hS.symm, mPf_succ_eq, C5 (OddPatterns.odd_two_mul_add_one h), Delta,
    Membership.V2 _ S hS]
  simp only [← orderEmbOfFin_cast S hS]

/-- The second term of the element `f` of the proof of **(T7)** of `q_oddbox_lifts_2.md`: for
`B ⊆ Fin n` with increasing enumeration `b_1 < ⋯ < b_k`,
`Ψ_ℓ(B) = Pf(y_{B^+}; y_{B^+}^0, …, y_{B^+}^{ℓ−1}, D(y_0, ·))` in `C_{n+1}`, where
`y_{B^+} = (y_{b_1+1}, …, y_{b_k+1})` and `D = ColOne.Dab (2h+2)`. -/
noncomputable def Psi (l : ℕ) {n k : ℕ} (B : Finset (Fin n)) (hB : B.card = k) :
    Peel.C F (2 * h + 2) (n + 1) :=
  Pf (2 * h + 1) (fun j : Fin k => y F (2 * h + 2) (B.orderEmbOfFin hB j).succ)
    (Fin.snoc (α := fun _ => Fin k → Peel.C F (2 * h + 2) (n + 1))
      (fun (i : Fin l) j => y F (2 * h + 2) (B.orderEmbOfFin hB j).succ ^ (i : ℕ))
      (fun j => Dab (2 * h + 2) (y F (2 * h + 2) 0) (y F (2 * h + 2) (B.orderEmbOfFin hB j).succ)))

/-- Auxiliary for (T7) of `q_oddbox_lifts_2.md`: under `φ = peelEquiv'`, `Ψ_ℓ(B)` is the class of
`Pf(C w; (C w)^0, …, (C w)^{ℓ−1}, D(X, ·))`, the second term of `Φ` of Lemma Q′, with
`w_j = y_{b_j}`. -/
theorem phi_Psi (l : ℕ) {n k : ℕ} (B : Finset (Fin n)) (hB : B.card = k) :
    peelEquiv' F (2 * h + 2) n (Psi F h l B hB) =
      AdjoinRoot.mk _ (Pf (2 * h + 1) (fun j => Polynomial.C (y F (2 * h + 2) (B.orderEmbOfFin hB j)))
        (Fin.snoc (α := fun _ => Fin k → (Peel.C F (2 * h + 2) n)[X])
          (fun (i : Fin l) j => (Polynomial.C (y F (2 * h + 2) (B.orderEmbOfFin hB j))) ^ (i : ℕ))
          (fun j => Dab (2 * h + 2) X (Polynomial.C (y F (2 * h + 2) (B.orderEmbOfFin hB j)))))) := by
  unfold Psi
  have h1 := map_Pf (peelEquiv' F (2 * h + 2) n).toRingEquiv.toRingHom (2 * h + 1)
    (fun j : Fin k => y F (2 * h + 2) (B.orderEmbOfFin hB j).succ)
    (Fin.snoc (α := fun _ => Fin k → Peel.C F (2 * h + 2) (n + 1))
      (fun (i : Fin l) j => y F (2 * h + 2) (B.orderEmbOfFin hB j).succ ^ (i : ℕ))
      (fun j => Dab (2 * h + 2) (y F (2 * h + 2) 0) (y F (2 * h + 2) (B.orderEmbOfFin hB j).succ)))
  have h2 := map_Pf (AdjoinRoot.mk (X ^ (2 * h + 2 - 1) : (Peel.C F (2 * h + 2) n)[X])) (2 * h + 1)
    (fun j => Polynomial.C (y F (2 * h + 2) (B.orderEmbOfFin hB j)))
    (Fin.snoc (α := fun _ => Fin k → (Peel.C F (2 * h + 2) n)[X])
      (fun (i : Fin l) j => (Polynomial.C (y F (2 * h + 2) (B.orderEmbOfFin hB j))) ^ (i : ℕ))
      (fun j => Dab (2 * h + 2) X (Polynomial.C (y F (2 * h + 2) (B.orderEmbOfFin hB j)))))
  refine h1.trans (Eq.trans ?_ h2.symm)
  have hs : ∀ j : Fin k, (peelEquiv' F (2 * h + 2) n).toRingEquiv.toRingHom
      (y F (2 * h + 2) (B.orderEmbOfFin hB j).succ) =
      AdjoinRoot.mk (X ^ (2 * h + 2 - 1) : (Peel.C F (2 * h + 2) n)[X])
        (Polynomial.C (y F (2 * h + 2) (B.orderEmbOfFin hB j))) := by
    intro j
    rw [AdjoinRoot.mk_C, ← Lifts.incl_y]
    exact Lifts.phi_incl _
  have h0 : (peelEquiv' F (2 * h + 2) n).toRingEquiv.toRingHom (y F (2 * h + 2) 0) =
      AdjoinRoot.mk (X ^ (2 * h + 2 - 1) : (Peel.C F (2 * h + 2) n)[X]) X := by
    rw [AdjoinRoot.mk_X]
    exact Lifts.phi_y0
  congr 1
  · funext j
    exact hs j
  · funext i j
    refine Fin.lastCases ?_ (fun i' => ?_) i
    · simp only [Fin.snoc_last, map_Dab, hs, h0]
    · simp only [Fin.snoc_castSucc, map_pow, hs]

/-- Auxiliary for (T7) of `q_oddbox_lifts_2.md`: the expansion of `Ψ_ℓ(B)` along its last border
`D(y_0, ·)` (`Pfaffian.bpf_expand_last`) is a signed sum of the terms
`D(y_0, y_{b+1}) · incl(Pf_{E_{ℓ+1}}(B ∖ b))`, `b ∈ B`; so if all the
`D(y_0, y_{b+1}) · incl(Pf_{E_{ℓ+1}}(B ∖ b) · G)` lie in an ideal `V`, so does `Ψ_ℓ(B) · incl(G)`. -/
theorem Psi_mem (l : ℕ) {n k : ℕ} (B : Finset (Fin n)) (hB : B.card = k) (hk : 1 ≤ k)
    (V : Ideal (Peel.C F (2 * h + 2) (n + 1))) (G : Peel.C F (2 * h + 2) n)
    (hyp : ∀ x ∈ B, D F (2 * h + 2) 0 x.succ *
      incl F (2 * h + 2) n (markedPf F h (l + 1) (B.erase x) * G) ∈ V) :
    Psi F h l B hB * incl F (2 * h + 2) n G ∈ V := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  unfold Psi Pf
  rw [bpf_expand_last _ (ay_isAlt (OddPatterns.odd_two_mul_add_one h) _), Finset.sum_mul]
  refine Ideal.sum_mem _ (fun b _ => ?_)
  have hsub : bpf ((ay (2 * h + 1) (fun j : Fin (k' + 1) =>
      y F (2 * h + 2) (B.orderEmbOfFin hB j).succ)).submatrix b.succAbove b.succAbove)
      (fun i j => (Fin.snoc (α := fun _ => Fin (k' + 1) → Peel.C F (2 * h + 2) (n + 1))
        (fun (i : Fin l) j => y F (2 * h + 2) (B.orderEmbOfFin hB j).succ ^ (i : ℕ))
        (fun j => Dab (2 * h + 2) (y F (2 * h + 2) 0)
          (y F (2 * h + 2) (B.orderEmbOfFin hB j).succ))) i.castSucc (b.succAbove j)) =
      incl F (2 * h + 2) n (markedPf F h (l + 1) (B.erase (B.orderEmbOfFin hB b))) := by
    rw [markedPf_erase, map_mPf, mPf_succ_eq]
    simp only [Fin.snoc_castSucc, Lifts.incl_y]
    rfl
  rw [hsub, Fin.snoc_last]
  have hm := hyp _ (Finset.orderEmbOfFin_mem B hB b)
  rw [map_mul] at hm
  have e : (-1) ^ (k' + 1 + (l + 1) + (b : ℕ)) * Dab (2 * h + 2) (y F (2 * h + 2) 0)
      (y F (2 * h + 2) (B.orderEmbOfFin hB b).succ) *
      incl F (2 * h + 2) n (markedPf F h (l + 1) (B.erase (B.orderEmbOfFin hB b))) *
      incl F (2 * h + 2) n G =
      (-1) ^ (k' + 1 + (l + 1) + (b : ℕ)) * (D F (2 * h + 2) 0 (B.orderEmbOfFin hB b).succ *
        (incl F (2 * h + 2) n (markedPf F h (l + 1) (B.erase (B.orderEmbOfFin hB b))) *
          incl F (2 * h + 2) n G)) := by
    rw [D_eq_Dab]
    ring
  rw [e]
  exact V.mul_mem_left _ hm

end OddLifts2

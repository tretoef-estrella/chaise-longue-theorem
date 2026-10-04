module

public import RequestProject.OddLifts.LemmaP
public import RequestProject.Lifts.Main

/-!
# Part L of `q_oddbox_lifts_1.md`: auxiliary facts (L0a), (L0b), (L1)

Throughout, `F` is a field, `h` a natural number, `r = 2h + 1`, `q = 2h + 2`, and the rings are
`C_n = Peel.C F (2*h+2) n` with `y_i = Tight.y F (2*h+2) i`.  The level is `m = n + 1`, the new
variable is `y_0` of `C_{n+1}` and the old variables are the images under `Peel.incl F (2*h+2) n`.
-/

@[expose] public section

open Polynomial

namespace OddLifts

open ChainLemma OddShapes

set_option synthInstance.maxHeartbeats 200000

section L0

variable {F : Type*} [Field F]

/-- **(L0a)** of `q_oddbox_lifts_1.md`: `W_d` is monotone in the ideal: if `V ≤ V'` are ideals of
`C_m` (`m ≥ 1`), then `W_d(V) ≤ W_d(V')` for every `d`.  (Stated for an arbitrary `q`.) -/
theorem L0a {q m : ℕ} (hm : 1 ≤ m) {V V' : Ideal (Peel.C F q m)} (hVV' : V ≤ V') (d : ℕ) :
    Peel.W hm V d ≤ Peel.W hm V' d := by
  unfold Peel.W Peel.Vle
  exact Submodule.map_mono (inf_le_inf_right _ (fun x hx => hVV' hx))

/-- **(L0b)** of `q_oddbox_lifts_1.md`:
`Tight.VLamAll F (2h+2) m (comp Λ false) ≤ VSAll F h m Λ` for every set `Λ` of shapes. -/
theorem L0b (h m : ℕ) (Lam : Set Shape) :
    Tight.VLamAll F (2 * h + 2) m (comp Lam false) ≤ OddPatterns.VSAll F h m Lam := by
  unfold OddPatterns.VSAll OddPatterns.VS Tight.VLamAll
  exact le_sup_left

end L0

/-- Auxiliary for (L1) and (T5) of `q_oddbox_lifts_1.md`: `Finset.orderEmbOfFin` does not depend
on the proof of the cardinality, up to `Fin.cast`. -/
theorem orderEmbOfFin_cast {α : Type*} [LinearOrder α] (s : Finset α) {k : ℕ} (hk : s.card = k)
    (i : Fin k) : s.orderEmbOfFin hk i = s.orderEmbOfFin rfl (Fin.cast hk.symm i) := by
  subst hk; rfl

/-- Auxiliary for (L1) of `q_oddbox_lifts_1.md`: the increasing enumeration of `B^+` is `Fin.succ`
composed with the increasing enumeration of `B`. -/
theorem orderEmbOfFin_liftSet {n k : ℕ} (B : Finset (Fin n)) (hB : B.card = k)
    (hB' : (Lifts.liftSet B).card = k) (i : Fin k) :
    (Lifts.liftSet B).orderEmbOfFin hB' i = (B.orderEmbOfFin hB i).succ := by
  have := Finset.orderEmbOfFin_unique hB' (f := fun i => (B.orderEmbOfFin hB i).succ)
    (fun i => Lifts.succ_mem_liftSet.2 (Finset.orderEmbOfFin_mem B hB i))
    (fun a b hab => Fin.succ_lt_succ_iff.2 ((B.orderEmbOfFin hB).strictMono hab))
  exact (congrFun this i).symm

/-- Auxiliary for (T5) of `q_oddbox_lifts_1.md`: the increasing enumeration of `B^+ ∪ {0}` is `0`
followed by the increasing enumeration of `B^+`. -/
theorem orderEmbOfFin_insert_zero {n k : ℕ} (B : Finset (Fin n)) (hB : B.card = k)
    (hB' : (insert 0 (Lifts.liftSet B)).card = k + 1) (i : Fin (k + 1)) :
    (insert 0 (Lifts.liftSet B)).orderEmbOfFin hB' i =
      (Fin.cons 0 (fun j => (B.orderEmbOfFin hB j).succ) : Fin (k + 1) → Fin (n + 1)) i := by
  have hmono : StrictMono
      (Fin.cons 0 (fun j => (B.orderEmbOfFin hB j).succ) : Fin (k + 1) → Fin (n + 1)) := by
    intro a b hab
    induction a using Fin.cases with
    | zero =>
      induction b using Fin.cases with
      | zero => exact absurd hab (lt_irrefl _)
      | succ b => simp
    | succ a =>
      induction b using Fin.cases with
      | zero => exact absurd hab (by simp [Fin.not_lt_zero])
      | succ b =>
        simp only [Fin.cons_succ]
        exact Fin.succ_lt_succ_iff.2 ((B.orderEmbOfFin hB).strictMono (Fin.succ_lt_succ_iff.1 hab))
  have hmem : ∀ j, (Fin.cons 0 (fun j => (B.orderEmbOfFin hB j).succ) :
      Fin (k + 1) → Fin (n + 1)) j ∈ insert 0 (Lifts.liftSet B) := by
    intro j
    induction j using Fin.cases with
    | zero => exact Finset.mem_insert_self _ _
    | succ j =>
      simp only [Fin.cons_succ]
      exact Finset.mem_insert_of_mem (Lifts.succ_mem_liftSet.2 (Finset.orderEmbOfFin_mem B hB j))
  exact (congrFun (Finset.orderEmbOfFin_unique hB' hmem hmono) i).symm

variable (F : Type*) [Field F] (h : ℕ)

/-- **(L1)** of `q_oddbox_lifts_1.md`: for `B ⊆ Fin n` and every `ℓ ≥ 0`,
`incl(Pf_{E_ℓ}(B)) = Pf_{E_ℓ}(B^+)`, i.e.
`Peel.incl F (2h+2) n (markedPf F h ℓ B) = markedPf F h ℓ (Lifts.liftSet B)`. -/
theorem L1 {n : ℕ} (l : ℕ) (B : Finset (Fin n)) :
    Peel.incl F (2 * h + 2) n (OddPatterns.markedPf F h l B) =
      OddPatterns.markedPf F h l (Lifts.liftSet B) := by
  have hc : (Lifts.liftSet B).card = B.card := by simp [Lifts.liftSet]
  unfold OddPatterns.markedPf
  rw [OddPatterns.map_mPf]
  simp only [Lifts.incl_y]
  rw [← OddPatterns.mPf_cast h l hc.symm]
  congr 1
  funext i
  rw [← orderEmbOfFin_cast _ hc, orderEmbOfFin_liftSet B rfl hc]

/-- Auxiliary for (T5) of `q_oddbox_lifts_1.md`: the marked block of `B^+ ∪ {0}` is the marked
Pfaffian of `(y_0, y_{b_1+1}, …, y_{b_k+1})`, `b_1 < ⋯ < b_k` the elements of `B`. -/
theorem markedPf_insert_zero {n k : ℕ} (l : ℕ) (B : Finset (Fin n)) (hB : B.card = k) :
    OddPatterns.markedPf F h l (insert 0 (Lifts.liftSet B)) =
      OddPatterns.mPf h l (Fin.cons (Tight.y F (2 * h + 2) 0)
        (fun j => Tight.y F (2 * h + 2) (B.orderEmbOfFin hB j).succ) :
          Fin (k + 1) → Peel.C F (2 * h + 2) (n + 1)) := by
  have hM : (insert 0 (Lifts.liftSet B)).card = k + 1 := by
    rw [Finset.card_insert_of_notMem (Lifts.zero_notMem_liftSet _)]
    simp [Lifts.liftSet, hB]
  unfold OddPatterns.markedPf
  rw [← OddPatterns.mPf_cast h l hM.symm]
  congr 1
  funext i
  rw [← orderEmbOfFin_cast _ hM, orderEmbOfFin_insert_zero B hB hM]
  induction i using Fin.cases with
  | zero => rfl
  | succ j => rfl

/-- Auxiliary for (T5) of `q_oddbox_lifts_1.md`: under `φ = Peel.peelEquiv'`, the marked block of
`B^+ ∪ {0}` is the class of the polynomial `P_ℓ(w) = mPf_ℓ(X, C w_1, …, C w_k)` of Lemma P, with
`w_j = y_{b_j}` (`b_1 < ⋯ < b_k` the elements of `B`). -/
theorem phi_markedPf_insert_zero {n k : ℕ} (l : ℕ) (B : Finset (Fin n)) (hB : B.card = k) :
    Peel.peelEquiv' F (2 * h + 2) n (OddPatterns.markedPf F h l (insert 0 (Lifts.liftSet B))) =
      AdjoinRoot.mk _ (OddPatterns.mPf h l (Fin.cons X
        (fun j => Polynomial.C (Tight.y F (2 * h + 2) (B.orderEmbOfFin hB j))) :
          Fin (k + 1) → (Peel.C F (2 * h + 2) n)[X])) := by
  rw [markedPf_insert_zero F h l B hB]
  have h1 := OddPatterns.map_mPf (Peel.peelEquiv' F (2 * h + 2) n).toRingEquiv.toRingHom h l
    (Fin.cons (Tight.y F (2 * h + 2) 0)
      (fun j => Tight.y F (2 * h + 2) (B.orderEmbOfFin hB j).succ) :
        Fin (k + 1) → Peel.C F (2 * h + 2) (n + 1))
  have h2 := OddPatterns.map_mPf (AdjoinRoot.mk (X ^ (2 * h + 2 - 1) : (Peel.C F (2 * h + 2) n)[X]))
    h l (Fin.cons X (fun j => Polynomial.C (Tight.y F (2 * h + 2) (B.orderEmbOfFin hB j))) :
          Fin (k + 1) → (Peel.C F (2 * h + 2) n)[X])
  refine h1.trans (Eq.trans ?_ h2.symm)
  congr 1
  funext i
  induction i using Fin.cases with
  | zero =>
    simp only [Fin.cons_zero, AdjoinRoot.mk_X]
    exact Lifts.phi_y0
  | succ j =>
    simp only [Fin.cons_succ, AdjoinRoot.mk_C]
    rw [← Lifts.incl_y]
    exact Lifts.phi_incl _

end OddLifts

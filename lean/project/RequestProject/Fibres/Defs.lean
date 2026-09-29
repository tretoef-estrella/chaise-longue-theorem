module

public import RequestProject.Monotone.Defs
public import RequestProject.Peel.Defs

/-!
# Definitions for `q_P1_fibres.md`

This file formalizes the **Setting** of `q_P1_fibres.md`. It reuses the partitions and the list
of options `opt_p(μ)` of `RequestProject/Chain/Defs.lean` (the **Setting** of
`q_chain_lemma.md`), the size `|μ|` of `RequestProject/Monotone/Defs.lean`, and the tuple
conventions `consTuple` (`(t, M')`), `fiber` (`F(M')`) and `Zgt` (`Z_{>i}`) of
`RequestProject/Peel/Defs.lean` (the notation of `q_peeling_lemma.md`, part (iv)).
All definitions here are used in parts (i), (ii) and (iii) of the **Proposition** of
`q_P1_fibres.md`.
-/

@[expose] public section

namespace Fibres

open ChainLemma ChainLemma.Partition Peel

/-- **Setting** of `q_P1_fibres.md`: an integer `h ≥ 1`, and a finite set `T` with `|T| = 2h`
together with a fixed-point-free involution `u ↦ −u` (so `−(−u) = u` and `−u ≠ u`).
Used in parts (i), (ii) and (iii) of the Proposition of `q_P1_fibres.md`. -/
structure FibreSetting (T : Type*) [Fintype T] (h : ℕ) where
  /-- The involution `u ↦ −u`. (Setting of `q_P1_fibres.md`; used in parts (i), (ii) and (iii).) -/
  neg : T → T
  /-- `−(−u) = u`. (Setting of `q_P1_fibres.md`; used in parts (i), (ii) and (iii).) -/
  neg_neg : ∀ u, neg (neg u) = u
  /-- `−u ≠ u` (no fixed points). (Setting of `q_P1_fibres.md`; used in parts (i), (ii) and (iii).) -/
  neg_ne : ∀ u, neg u ≠ u
  /-- `h ≥ 1`. (Setting of `q_P1_fibres.md`; used in parts (i), (ii) and (iii).) -/
  one_le : 1 ≤ h
  /-- `|T| = 2h`. (Setting of `q_P1_fibres.md`; used in parts (i), (ii) and (iii).) -/
  card_eq : Fintype.card T = 2 * h

/-- The partition whose parts are the positive elements of a multiset `s` of naturals, listed in
weakly decreasing order (zeros of `s` are discarded). Auxiliary for the **Setting**
("Residue partition") of `q_P1_fibres.md`; used in parts (i), (ii) and (iii). -/
def ofMultiset (s : Multiset ℕ) : Partition where
  parts := (s.filter (0 < ·)).sort (· ≥ ·)
  sorted := Multiset.pairwise_sort _ _
  pos := by
    intro x hx
    rw [Multiset.mem_sort, Multiset.mem_filter] at hx
    exact hx.2

/-- **Setting** ("Residue partition") of `q_P1_fibres.md`: for a tuple `M ∈ T^m` and `u ∈ T`, the
count `#{i : M_i = u}`. Used in parts (i), (ii) and (iii). -/
def cnt {T : Type*} [DecidableEq T] {m : ℕ} (M : Fin m → T) (u : T) : ℕ :=
  (Finset.univ.filter fun i => M i = u).card

variable {T : Type*} [Fintype T] [DecidableEq T] {h : ℕ}

/-- **Setting** ("Residue partition") of `q_P1_fibres.md`: the residue partition `λ(M)` of a
tuple `M ∈ T^m`, whose parts are the numbers `|a − ā|` over the classes `κ = {u, −u}` with
`a ≠ ā` (where `a = #{i : M_i = u}` and `ā = #{i : M_i = −u}`), in weakly decreasing order.

Formally, for every `u ∈ T` we take the truncated difference `a − ā = #{M_i = u} − #{M_i = −u}`
(in `ℕ`), and keep the positive values. Each class `κ` with `a ≠ ā` contributes exactly one
positive value `|a − ā|` (at its majority element), and a class with `a = ā` contributes none;
so this is exactly the multiset of parts of the file, and no choice of `u ∈ κ` is involved.
Used in parts (i), (ii) and (iii). -/
def FibreSetting.resPart (S : FibreSetting T h) {m : ℕ} (M : Fin m → T) : Partition :=
  ofMultiset (Finset.univ.val.map fun u => cnt M u - cnt M (S.neg u))

open Classical in
/-- **Setting** of `q_P1_fibres.md`: for a set `Λ` of partitions,
`F_Λ(μ) := #{p ∈ {1, …, 2h} : opt_p(μ) ∈ Λ}` (with `L = 2h`). Used in part (iii). -/
noncomputable def FLam (h : ℕ) (Λ : Set Partition) (μ : Partition) : ℕ :=
  ((Finset.Icc 1 (2 * h)).filter fun p => μ.opt (2 * h) p ∈ Λ).card

open Classical in
/-- Part (iii) of the Proposition of `q_P1_fibres.md`: the set
`Z_Λ := {M ∈ T^m : λ(M) ∈ Λ}`. -/
noncomputable def FibreSetting.ZLam (S : FibreSetting T h) (m : ℕ) (Λ : Set Partition) :
    Finset (Fin m → T) :=
  Finset.univ.filter fun M => S.resPart M ∈ Λ

end Fibres

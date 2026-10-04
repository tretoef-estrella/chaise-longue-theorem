module

public import RequestProject.TheoremB.Defs

/-!
# Setting of `q_even_count.md`

This file formalizes the **Setting** of `q_even_count.md` (the count for an even degree):

* `EvenCount.QkEven k m` is the number `Q^e_k(m)` (*The number*);
* `EvenCount.PointedSetting T h` is a pointed point set (*Pointed point sets*);
* `EvenCount.closedPointed S n` is the set of closed tuples of a pointed point set.

The counts `cnt_M(u)` are `Fibres.cnt` of `q_P1_fibres.md`, and `Q_j(q)` is `TheoremB.Qk` of
`q_theorem_B_lower.md`.
-/

@[expose] public section

namespace EvenCount

open Fibres

/-- **Setting, "The number"** of `q_even_count.md`: for `k ≥ 0` and an even `m ≥ 2`, with
`h = (m − 2)/2` and `N = 2k + 2`,
`Q^e_k(m) := Σ N! / ((2c)! · Π_{u=1}^{h} (b_u!)^2)`, the sum over all
`(c, b_1, …, b_h) ∈ ℕ^{1+h}` with `c + b_1 + ⋯ + b_h = k + 1` (written, as in `TheoremB.Qk`, as
`2c + 2(b_1 + ⋯ + b_h) = N`). The sum is written over finite sets: the bounds `c ≤ k + 1` and
`b_u ≤ N` imposed by `Finset.range` lose nothing. The division is the division of `ℕ`, which is
exact here. -/
def QkEven (k m : ℕ) : ℕ :=
  ∑ c ∈ Finset.range (k + 2),
    ∑ b ∈ (Fintype.piFinset fun _ : Fin ((m - 2) / 2) => Finset.range (2 * k + 3)).filter
        (fun b => 2 * c + 2 * ∑ u, b u = 2 * k + 2),
      (2 * k + 2).factorial / ((2 * c).factorial * ∏ u, (b u).factorial ^ 2)

/-- **Setting, "Pointed point sets"** of `q_even_count.md`: a finite set `T` with a map
`u ↦ −u` such that `−(−u) = u`, with exactly one fixed point `o` (`−o = o`, and `−u = u` only for
`u = o`), and `|T| = 2h + 1` for an integer `h ≥ 0`. -/
structure PointedSetting (T : Type*) [Fintype T] (h : ℕ) where
  /-- The map `u ↦ −u` (Setting, "Pointed point sets", of `q_even_count.md`). -/
  neg : T → T
  /-- `−(−u) = u` (Setting, "Pointed point sets", of `q_even_count.md`). -/
  neg_neg : ∀ u, neg (neg u) = u
  /-- The fixed point `o` (Setting, "Pointed point sets", of `q_even_count.md`). -/
  o : T
  /-- `−o = o` (Setting, "Pointed point sets", of `q_even_count.md`). -/
  neg_o : neg o = o
  /-- `−u = u` only for `u = o` (Setting, "Pointed point sets", of `q_even_count.md`). -/
  eq_o_of_neg_eq : ∀ u, neg u = u → u = o
  /-- `|T| = 2h + 1` (Setting, "Pointed point sets", of `q_even_count.md`). -/
  card_eq : Fintype.card T = 2 * h + 1

variable {T : Type*} [Fintype T] [DecidableEq T] {h : ℕ}

/-- **Setting, "Pointed point sets"** of `q_even_count.md`: the set of *closed* tuples
`M ∈ T^n`, i.e. those with `cnt_M(u) = cnt_M(−u)` for every `u ∈ T` and `cnt_M(o)` even. -/
def closedPointed (S : PointedSetting T h) (n : ℕ) : Finset (Fin n → T) :=
  Finset.univ.filter fun M => (∀ u, cnt M u = cnt M (S.neg u)) ∧ Even (cnt M S.o)

end EvenCount

end

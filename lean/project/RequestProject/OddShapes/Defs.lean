module

public import RequestProject.Fibres.Lemmas
public import RequestProject.Lifts.Defs

/-!
# Definitions for Parts B and C of `q_oddbox_shapes.md`

This file formalizes the **Setting** of Part B ("Shapes with a mark, and the options") of
`q_oddbox_shapes.md`, and the **Definition (interlaced pair)** of Part C.

Everything else is reused unchanged: partitions, `ℓ(μ)` (`len`), `μ − e_j` (`subE`),
`μ + e_j` (`addE`), `μ ⊔ 1` (`addOne`), `opt_p(μ)` (`opt`) and `≼` (`WeakDom`) of
`q_chain_lemma.md`; `|μ|` (`size`) of `q_P2_monotone_options.md`; `cnt`, `ofMultiset` and
`F_Λ(μ)` (`Fibres.FLam`) of `q_P1_fibres.md`; `Par_n` (`Lifts.Par`) and down-sets of `Par_n`
(`Lifts.IsDownSetPar`) of `q_P3_lifts.md`; the tuple `(t, M')` (`Peel.consTuple`), the fibre
`F(M')` (`Peel.fiber`) and `Z_{>i}` (`Peel.Zgt`) of `q_peeling_lemma.md`.
-/

@[expose] public section

namespace OddShapes

open ChainLemma ChainLemma.Partition Fibres

/-- **Part B, Setting** of `q_oddbox_shapes.md`: an integer `h ≥ 1` and a finite set `T` with
`|T| = r = 2h + 1`, together with an involution `u ↦ −u` (`−(−u) = u`) with exactly one fixed
point `0` (`−0 = 0`, and `−u ≠ u` for `u ≠ 0`). (In the style of `Fibres.FibreSetting`.) -/
structure OddSetting (T : Type*) [Fintype T] (h : ℕ) where
  /-- The involution `u ↦ −u` (Part B, Setting, of `q_oddbox_shapes.md`). -/
  neg : T → T
  /-- The fixed point `0` (Part B, Setting, of `q_oddbox_shapes.md`). -/
  zero : T
  /-- `−(−u) = u` (Part B, Setting, of `q_oddbox_shapes.md`). -/
  neg_neg : ∀ u, neg (neg u) = u
  /-- `−0 = 0` (Part B, Setting, of `q_oddbox_shapes.md`). -/
  neg_zero : neg zero = zero
  /-- `−u ≠ u` for `u ≠ 0` (Part B, Setting, of `q_oddbox_shapes.md`). -/
  neg_ne : ∀ u, u ≠ zero → neg u ≠ u
  /-- `h ≥ 1` (Part B, Setting, of `q_oddbox_shapes.md`). -/
  one_le : 1 ≤ h
  /-- `|T| = 2h + 1` (Part B, Setting, of `q_oddbox_shapes.md`). -/
  card_eq : Fintype.card T = 2 * h + 1

/-- **Part B, Setting** ("A *shape* in general") of `q_oddbox_shapes.md`: a pair `(λ, δ)` of a
partition and a mark `δ ∈ {0, 1}`, encoded as a Boolean (`true` = marked, i.e. `δ = 1`;
the other mark `1 − δ` is `!δ`). -/
abbrev Shape := Partition × Bool

variable {T : Type*} [Fintype T] [DecidableEq T] {h : ℕ}

namespace OddSetting

/-- **Part B, Setting** ("Shape", the residue partition `λ(M)`) of `q_oddbox_shapes.md`:
exactly as `Fibres.FibreSetting.resPart`, the partition whose parts are the positive values of
the truncated differences `cnt M u − cnt M (−u)` over all `u ∈ T` (the fixed point `0`
contributes `0`). -/
def resPart (S : OddSetting T h) {m : ℕ} (M : Fin m → T) : Partition :=
  ofMultiset (Finset.univ.val.map fun u => cnt M u - cnt M (S.neg u))

/-- **Part B, Setting** ("Shape", the mark `δ(M)`) of `q_oddbox_shapes.md`: the parity of
`#{i : M_i = 0}` (`true` iff it is odd). -/
def mark (S : OddSetting T h) {m : ℕ} (M : Fin m → T) : Bool :=
  decide (cnt M S.zero % 2 = 1)

/-- **Part B, Setting** ("Shape") of `q_oddbox_shapes.md`: the shape `(λ(M), δ(M))` of a tuple
`M ∈ T^m`. -/
def shape (S : OddSetting T h) {m : ℕ} (M : Fin m → T) : Shape :=
  (S.resPart M, S.mark M)

end OddSetting

/-- **Part B, Setting** ("The sets `Sh_m`", the equivalent description) of
`q_oddbox_shapes.md`: `(λ, δ) ∈ Sh_m` iff `ℓ(λ) ≤ h`, `|λ| + δ ≤ m` and `|λ| + δ ≡ m (mod 2)`.
The description as `{(λ, 0) : λ ∈ Par_m} ∪ {(λ, 1) : λ ∈ Par_{m−1}}` is the theorem
`OddShapes.Sh_eq`. -/
def Sh (h m : ℕ) : Set Shape :=
  {s | s.1.len ≤ h ∧ s.1.size + (if s.2 then 1 else 0) ≤ m ∧
    (s.1.size + (if s.2 then 1 else 0)) % 2 = m % 2}

/-- **Part B, Setting** ("The list of options of a shape") of `q_oddbox_shapes.md`: for a shape
`(μ, δ)` with `ℓ = ℓ(μ)` and `p = 1, …, 2h + 1`,
* `optS_p(μ, δ) = (μ − e_p, δ)` for `1 ≤ p ≤ ℓ`;
* `optS_p(μ, δ) = (μ, 1 − δ)` for `p = ℓ + 1`;
* `optS_p(μ, δ) = (μ ⊔ 1, δ)` for `ℓ + 1 < p ≤ 2h + 1 − ℓ`;
* `optS_p(μ, δ) = (μ + e_{2h+2−p}, δ)` for `2h + 1 − ℓ < p ≤ 2h + 1`.
(The values at `p = 0` and `p > 2h + 1` are irrelevant.) -/
def optS (h : ℕ) (s : Shape) (p : ℕ) : Shape :=
  if p ≤ s.1.len then (s.1.subE p, s.2)
  else if p = s.1.len + 1 then (s.1, !s.2)
  else if p ≤ 2 * h + 1 - s.1.len then (s.1.addOne, s.2)
  else (s.1.addE (2 * h + 2 - p), s.2)

/-- **Part B, Setting** ("The function `F_Λ` on shapes") of `q_oddbox_shapes.md`: the components
`Λ^0 = {λ : (λ, 0) ∈ Λ}` (`comp Λ false`) and `Λ^1 = {λ : (λ, 1) ∈ Λ}` (`comp Λ true`) of a set
`Λ` of shapes. -/
def comp (Λ : Set Shape) (δ : Bool) : Set Partition := {lam | (lam, δ) ∈ Λ}

open Classical in
/-- **Part B, Setting**, formula (8.5) of `q_oddbox_shapes.md`:
`F_Λ(μ, δ) := F_{Λ^δ}(μ) + [μ ∈ Λ^{1−δ}]`, with `F_{Λ^δ}` the function `Fibres.FLam h` of
`q_P1_fibres.md`. -/
noncomputable def FS (h : ℕ) (Λ : Set Shape) (s : Shape) : ℕ :=
  FLam h (comp Λ s.2) s.1 + if s.1 ∈ comp Λ (!s.2) then 1 else 0

open Classical in
/-- **Part B, Setting** of `q_oddbox_shapes.md`: `Z_Λ := {M ∈ T^m : the shape of M lies in Λ}`. -/
noncomputable def ZS (S : OddSetting T h) (m : ℕ) (Λ : Set Shape) : Finset (Fin m → T) :=
  Finset.univ.filter fun M => S.shape M ∈ Λ

/-- **Part C, Definition (interlaced pair; Definition 8.2 of the paper)** of
`q_oddbox_shapes.md`: a set `Λ` of shapes is an interlaced pair of level `m` if
* (D0) `Λ ⊆ Sh_m`;
* (D1) `Λ^0` is a down-set of `Par_m` and `Λ^1` is a down-set of `Par_{m−1}`;
* (D2) if `(ν, δ) ∈ Λ` and `1 ≤ j ≤ ℓ(ν)`, then `(ν − e_j, 1 − δ) ∈ Λ`. -/
def IsInterlaced (h m : ℕ) (Λ : Set Shape) : Prop :=
  Λ ⊆ Sh h m ∧
  (Lifts.IsDownSetPar h m (comp Λ false) ∧ Lifts.IsDownSetPar h (m - 1) (comp Λ true)) ∧
  ∀ ν δ, (ν, δ) ∈ Λ → ∀ j, 1 ≤ j → j ≤ ν.len → (ν.subE j, !δ) ∈ Λ

end OddShapes

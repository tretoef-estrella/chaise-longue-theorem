module

public import RequestProject.Induction.Main
public import RequestProject.Ballot.Defs

/-!
# Definitions for `q_theorem_B_lower.md` (Theorem B, lower bound)

This file formalizes the **Setting** of `q_theorem_B_lower.md`.  As in the file, everything is
assembled unchanged from the earlier parts of the project:
* `C_m` is `Peel.C F q m` (`q_peeling_lemma.md`), with `y_i = X (i - 1)`; here `m = n' = 2k + 1`;
* partitions and `≼` come from `RequestProject/Chain/` (`q_chain_lemma.md`);
* the involution on `T`, the counts `#{M_i = u}` (`Fibres.cnt`), `λ(M)` (`resPart`) and `Z_Λ`
  (`ZLam`) come from `RequestProject/Fibres/` (`q_P1_fibres.md`);
* `D`, tight patterns and `V_Λ` (`Tight.VLamAll`) come from `RequestProject/Tight/`
  (`q_P3_identities.md`);
* `Par_n` and down-sets of `Par_n` come from `RequestProject/Lifts/` (`q_P3_lifts.md`);
* perfect matchings of `{0, 1, …, 2k + 1}` are encoded as in `RequestProject/Ballot/`
  (`BallotBound.Matching`): fixed-point-free involutions of `Fin (2 * k + 2)`.
-/

@[expose] public section

namespace TheoremB

open ChainLemma Fibres Tight Lifts

set_option synthInstance.maxHeartbeats 200000

/-- **Setting, "Matchings"** of `q_theorem_B_lower.md`: the index of the variable `y_a` of
`C = C_{n'}` for `a ∈ {1, …, 2k + 1}` (an element of the ground set `{0, 1, …, 2k + 1}` of the
matchings, i.e. of `Fin (2 * k + 2)`).  With the convention `y_i = X (i - 1)` of
`q_peeling_lemma.md`, `y_a` is the variable of index `a - 1 : Fin (2 * k + 1)`.  (The value at
`a = 0` is never used.) -/
def idx {k : ℕ} (a : Fin (2 * k + 2)) : Fin (2 * k + 1) := ⟨a.val - 1, by omega⟩

variable (F : Type*) [Field F] (q : ℕ)

/-- **Setting, "Matchings"** of `q_theorem_B_lower.md`: for a perfect matching `J ∈ 𝒥` of
`{0, 1, …, 2k + 1}` (a fixed-point-free involution, `BallotBound.Matching k`),
`D_J := Π_{{a<b} ∈ J, a ≠ 0} D(y_a, y_b) ∈ C = C_{2k+1}`, the product over the `k` pairs of `J`
avoiding `0`.  A pair `{a < b}` of `J` is recorded by its smaller element `a` (so `b = J a`), and
it avoids `0` iff `a ≠ 0` and `J a ≠ 0`; the empty product is `1`.  Here `D` is the divided
difference of `q_P3_identities.md` and `y_a` is the variable of index `a - 1` (`idx a`). -/
noncomputable def DJ {k : ℕ} (J : BallotBound.Matching k) : Peel.C F q (2 * k + 1) :=
  ∏ a ∈ Finset.univ.filter (fun a => a ≠ 0 ∧ J.1 a ≠ 0 ∧ a < J.1 a),
    D F q (idx a) (idx (J.1 a))

/-- **Setting, "Matchings"** of `q_theorem_B_lower.md`: the ideal `(D_J : J ∈ 𝒥) ⊆ C` generated
by all the `D_J`. -/
noncomputable def DIdeal (k : ℕ) : Ideal (Peel.C F q (2 * k + 1)) :=
  Ideal.span (Set.range (DJ F q (k := k)))

/-- **Setting, "The number `Q_k(q)`"** of `q_theorem_B_lower.md`: with `h = (q − 1)/2` and
`N = 2k + 2`, `Q_k(q) := Σ N! / Π_{u=1}^{h} (b_u!)^2`, the sum over all `(b_1, …, b_h) ∈ ℕ^h` with
`2(b_1 + ⋯ + b_h) = N`.  (The `b_u` are indexed by `Fin h`.  The sum is written over a finite set:
the bound `b_u ≤ N` imposed by `piFinset` loses nothing, since `2 b_u ≤ N` anyway.  The division is
the division of `ℕ`, which is exact here, the quotient being a multinomial coefficient.) -/
def Qk (k q : ℕ) : ℕ :=
  ∑ b ∈ (Fintype.piFinset fun _ : Fin ((q - 1) / 2) => Finset.range (2 * k + 3)).filter
      (fun b => 2 * ∑ u, b u = 2 * k + 2),
    (2 * k + 2).factorial / ∏ u, (b u).factorial ^ 2

/-- **Theorem, part (i)** of `q_theorem_B_lower.md`: the one-box partition `(1)`, so that
`Λ := {(1)}`. -/
def one : Partition := ⟨[1], by simp, by simp⟩

/-- **Setting, "Point sets"** of `q_theorem_B_lower.md`: the example of a point set,
`T = {1, …, h} × {±1}` with `(u, ε) ↦ (u, −ε)` (here `Fin h × Bool`, with `ε` a boolean and
`−ε = !ε`); it has `|T| = 2h`.  This is the `T` constructed for part (iv). -/
def stdSetting (h : ℕ) (hh : 1 ≤ h) : FibreSetting (Fin h × Bool) h where
  neg := fun u => (u.1, !u.2)
  neg_neg := by simp
  neg_ne := by intro u; simp [Prod.ext_iff]
  one_le := hh
  card_eq := by simp [mul_comm]

variable {T : Type*} [Fintype T] [DecidableEq T] {h : ℕ}

/-- **Setting, "Point sets"** of `q_theorem_B_lower.md`:
`ν(M) := Σ_κ min(a_κ(M), ā_κ(M))`, the sum over the classes `κ = {u, −u}` of the minimum of the
numbers of entries of `M` equal to `u` and to `−u`.  Formally, the sum is taken over all `u ∈ T`
of `min(#{M_i = u}, #{M_i = −u})` and divided by `2`: every class `κ = {u, −u}` has exactly two
elements (`−u ≠ u`), which contribute the same value `min(a_κ, ā_κ)`, so this is exactly the sum
over the classes, and no choice of a representative of `κ` is needed. -/
def nu (S : FibreSetting T h) {m : ℕ} (M : Fin m → T) : ℕ :=
  (∑ u, min (cnt M u) (cnt M (S.neg u))) / 2

/-- **Setting, "Point sets"** of `q_theorem_B_lower.md`: the set of **closed** tuples in `T^n`,
i.e. those with `a_κ = ā_κ` for every class `κ = {u, −u}` (`#{M_i = u} = #{M_i = −u}` for all
`u ∈ T`). -/
def closedTuples (S : FibreSetting T h) (n : ℕ) : Finset (Fin n → T) :=
  Finset.univ.filter fun M => ∀ u, cnt M u = cnt M (S.neg u)

/-- **Setting, "Point sets"** of `q_theorem_B_lower.md`:
`Γ' := {M ∈ T^{n'} : ν(M) = k}`, with `n' = 2k + 1`. -/
def Gamma' (S : FibreSetting T h) (k : ℕ) : Finset (Fin (2 * k + 1) → T) :=
  Finset.univ.filter fun M => nu S M = k

end TheoremB

end

module

public import RequestProject.EvenCount.Defs
public import RequestProject.Tight.Defs

/-!
# Setting of `q_odd3.md` (the odd box `r = 3`)

This file formalizes the **Setting** of `q_odd3.md`, with the parameter `q := 4` of
`q_peeling_lemma.md`, `q_P3_identities.md` and `q_theorem_B_lower.md`:

* the ring `C_m = F[y_1, …, y_m]/(y_1^3, …, y_m^3)` is `Peel.C F 4 m`, with `y_i = X (i - 1)`, so
  the indices `1, …, m` are the elements `0, …, m - 1` of `Fin m` (order preserving);
* `y_a` is `Tight.y F 4 a`, `D(a, b) = y_a^2 − y_a y_b + y_b^2` is `Tight.D F 4 a b`, and the
  Vandermonde `Δ(y_a, y_b, y_c)` is `Tight.Delta F 4 {a, b, c}`;
* `T = {−1, 0, 1}` is modelled by `Fin 3` with the value map `v ↦ (v : ℤ) − 1` (`Odd3.val3`);
* a *set `P` of pairwise disjoint pairs of indices* is modelled by a finset of `2`-element finsets
  of indices which are pairwise disjoint (`Odd3.IsPairs`), and `D_P` is the product of the factors
  `D(a, b)` over its pairs `{a < b}` (`Odd3.DP`, using `Tight.pairD`).
-/

@[expose] public section

namespace Odd3

open Peel Tight

set_option synthInstance.maxHeartbeats 200000

/-- **Setting, "The point sets"** of `q_odd3.md`: the set `T = {−1, 0, 1}` is modelled by `Fin 3`,
the element `v : Fin 3` standing for the integer `(v : ℤ) − 1` (so `0, 1, 2 ↦ −1, 0, 1`). -/
def val3 (v : Fin 3) : ℤ := (v : ℤ) - 1

/-- **Setting, "The point sets"** of `q_odd3.md`:
`Z_J^{(m)} := {M ∈ T^m : |M_1 + ⋯ + M_m| ≤ J}`, the sum being taken in `ℤ` (with `T` modelled by
`Fin 3` and the values `val3`). -/
def Z (m J : ℕ) : Finset (Fin m → Fin 3) :=
  Finset.univ.filter fun M => |∑ i, val3 (M i)| ≤ (J : ℤ)

/-- **Setting** of `q_odd3.md`: "`P` is a set of pairwise disjoint pairs of indices of
`{1, …, m}`".  Model: `P` is a finset of subsets of the index set `Fin m`, each with exactly two
elements (a pair `{a, b}`, `a ≠ b`), and distinct members of `P` are disjoint.  Its size `|P|` is
`P.card`. -/
def IsPairs {m : ℕ} (P : Finset (Finset (Fin m))) : Prop :=
  (∀ e ∈ P, e.card = 2) ∧ (P : Set (Finset (Fin m))).PairwiseDisjoint id

/-- **Setting** of `q_odd3.md`: the set of indices covered by the pairs of `P` (the union of the
pairs).  An index is *outside the pairs of `P`* (or *free*) iff it is not in `supp P`; `P` is a
*perfect matching* of a set `S` of indices iff `IsPairs P` and `supp P = S`. -/
def supp {m : ℕ} (P : Finset (Finset (Fin m))) : Finset (Fin m) := P.sup id

variable (F : Type*) [Field F]

/-- **Setting** of `q_odd3.md`: `D_P := Π_{{a,b} ∈ P} D(a, b) ∈ C_m` (with `D_∅ = 1`), where for a
pair `e = {a < b}` the factor is `Tight.pairD F 4 e = D(y_a, y_b)` (`D` is symmetric for `q = 4`). -/
noncomputable def DP {m : ℕ} (P : Finset (Finset (Fin m))) : C F 4 m :=
  ∏ e ∈ P, pairD F 4 e

/-- **Setting, "The ideals"** of `q_odd3.md`, second line (`J < m`, `J ≡ m mod 2`): the
generators `D_P` with `|P| = (m − J)/2`. -/
def evenGens (m J : ℕ) : Set (C F 4 m) :=
  {g | ∃ P : Finset (Finset (Fin m)), IsPairs P ∧ P.card = (m - J) / 2 ∧ g = DP F P}

/-- **Setting, "The ideals"** of `q_odd3.md`, third line (`1 ≤ J < m`, `J ≢ m mod 2`): the
generators `(y_b − y_a)·D_P` with `|P| = (m − 1 − J)/2` and `a ≠ b` indices outside the pairs of
`P`, and `D_{P⁺}` with `|P⁺| = (m + 1 − J)/2`. -/
def oddGens (m J : ℕ) : Set (C F 4 m) :=
  {g | ∃ (P : Finset (Finset (Fin m))) (a b : Fin m), IsPairs P ∧ P.card = (m - 1 - J) / 2 ∧
      a ≠ b ∧ a ∉ supp P ∧ b ∉ supp P ∧ g = (y F 4 b - y F 4 a) * DP F P} ∪
  {g | ∃ P : Finset (Finset (Fin m)), IsPairs P ∧ P.card = (m + 1 - J) / 2 ∧ g = DP F P}

/-- **Setting, "The ideals"** of `q_odd3.md`, fourth line (`J = 0`, `m` odd): the generators
`y_c^2·D_P` (`c` an index, `P` a perfect matching of the other indices) and
`Δ(y_a, y_b, y_c)·D_{P'}` (`a < b < c`, `P'` a perfect matching of the other indices). -/
def zeroGens (m : ℕ) : Set (C F 4 m) :=
  {g | ∃ (c : Fin m) (P : Finset (Finset (Fin m))), IsPairs P ∧ supp P = Finset.univ.erase c ∧
      g = y F 4 c ^ 2 * DP F P} ∪
  {g | ∃ (a b c : Fin m) (P : Finset (Finset (Fin m))), a < b ∧ b < c ∧ IsPairs P ∧
      supp P = Finset.univ \ {a, b, c} ∧ g = Delta F 4 {a, b, c} * DP F P}

/-- **Setting, "The ideals"** of `q_odd3.md`: the ideal `I(m, J) ⊆ C_m`:
* `C_m` (the unit ideal) if `J ≥ m`;
* `(D_P : |P| = (m − J)/2)` if `J < m` and `J ≡ m (mod 2)`;
* `((y_b − y_a)·D_P : |P| = (m − 1 − J)/2, a ≠ b outside P;  D_{P⁺} : |P⁺| = (m + 1 − J)/2)` if
  `1 ≤ J < m` and `J ≢ m (mod 2)`;
* `(y_c^2·D_P;  Δ(y_a, y_b, y_c)·D_{P'})` if `J = 0` and `m` is odd (the remaining case). -/
noncomputable def I (m J : ℕ) : Ideal (C F 4 m) :=
  if m ≤ J then ⊤
  else if J % 2 = m % 2 then Ideal.span (evenGens F m J)
  else if 1 ≤ J then Ideal.span (oddGens F m J)
  else Ideal.span (zeroGens F m)

end Odd3

end

module

public import RequestProject.Peel.Main
public import RequestProject.Monotone.Defs

/-!
# Definitions for `q_P3_identities.md` (tight patterns and three polynomial identities)

This file formalizes the **Setting** section of `q_P3_identities.md`.

* The ring `C_m = F[y_1, …, y_m]/(y_1^{q−1}, …, y_m^{q−1})` is `Peel.C F q m` from
  `RequestProject/Peel/`, with `y_i = X (i - 1)`.  Indices `1, …, m` are therefore encoded as the
  elements `0, …, m - 1` of `Fin m` (the index `i` is `⟨i - 1, _⟩ : Fin m`); this encoding is
  order preserving, so "`a < b`", "`b_1 < ⋯ < b_r`" etc. are the order of `Fin m`.  A finite index
  set `I ⊆ {1, …, m}` is a `Finset (Fin m)`.
* Partitions `λ`, their rows `λ_i` and length are `ChainLemma.Partition`, `row`, `len` from
  `RequestProject/Chain/`, and `|λ|` is `ChainLemma.Partition.size` from
  `RequestProject/Monotone/`.
-/

@[expose] public section

open MvPolynomial

namespace Tight

open Peel ChainLemma

set_option synthInstance.maxHeartbeats 200000

variable (F : Type*) [Field F] (q : ℕ)

/-- **Setting** of `q_P3_identities.md`: the variable `y_i ∈ C_m`.  With the convention
`y_i = X (i - 1)` of `RequestProject/Peel/`, the index `i ∈ {1, …, m}` is encoded as
`⟨i - 1, _⟩ : Fin m`, so `y F q a` is the class of `X a` in `C_m`. -/
noncomputable def y {m : ℕ} (a : Fin m) : C F q m := Ideal.Quotient.mk _ (X a)

/-- **Setting, "Divided difference"** of `q_P3_identities.md`: for indices `a ≠ b`,
`D(y_a, y_b) := Σ_{i=0}^{q−2} (−1)^i y_a^i y_b^{q−2−i} ∈ C_m`.
(The sum over `i = 0, …, q − 2` is the sum over `Finset.range (q - 1)`.) -/
noncomputable def D {m : ℕ} (a b : Fin m) : C F q m :=
  ∑ i ∈ Finset.range (q - 1), (-1) ^ i * y F q a ^ i * y F q b ^ (q - 2 - i)

/-- **Setting, "Vandermonde"** of `q_P3_identities.md`, for arbitrary values `x_b` in a
commutative ring: for `B = {b_1 < ⋯ < b_r}`,
`Π_{1 ≤ c < c' ≤ r} (x_{b_{c'}} − x_{b_c})`, i.e. the product of `x_{c'} − x_c` over all pairs
`c < c'` of elements of `B`.  The empty product gives `Δ(∅) = Δ({b}) = 1`. -/
def vand {ι R : Type*} [LinearOrder ι] [CommRing R] (x : ι → R) (B : Finset ι) : R :=
  ∏ c ∈ B, ∏ c' ∈ B with c < c', (x c' - x c)

/-- **Setting, "Vandermonde"** of `q_P3_identities.md`: for a finite set of indices
`B = {b_1 < ⋯ < b_r}`, `Δ(B) := Π_{1 ≤ c < c' ≤ r} (y_{b_{c'}} − y_{b_c}) ∈ C_m`,
with `Δ(∅) = Δ({b}) = 1`. -/
noncomputable def Delta {m : ℕ} (B : Finset (Fin m)) : C F q m := vand (y F q) B

/-- **Setting, "Column lengths"** of `q_P3_identities.md`: `λ'_c := #{i : λ_i ≥ c}`, the number
of rows of `λ` that are `≥ c` (the length of the `c`-th column of the Young diagram; it is used
for `c = 1, …, λ_1`). -/
def colLen (lam : Partition) (c : ℕ) : ℕ := (lam.parts.filter (fun x => c ≤ x)).length

/-- **Setting, "Tight patterns"** of `q_P3_identities.md`: a tight pattern of the partition `λ`
on the finite index set `I` (with `|I| ≥ |λ|` and `|I| − |λ|` even) consists of
* a set `P` (`pairs`) of `p := (|I| − |λ|)/2` pairwise disjoint 2-element subsets of `I`, and
* pairwise disjoint subsets `B_1, …, B_{λ_1}` (`blocks c` for `c = 1, …, λ_1`; the values of
  `blocks` outside `1, …, λ_1` play no role) with `|B_c| = λ'_c`,

such that the pairs and the blocks together partition `I`: they are pairwise disjoint and their
union is `I` (in particular they are subsets of `I`). -/
structure TightPattern {m : ℕ} (lam : Partition) (I : Finset (Fin m)) where
  /-- The set `P` of pairs. -/
  pairs : Finset (Finset (Fin m))
  /-- The blocks `B_c` (`c = 1, …, λ_1`). -/
  blocks : ℕ → Finset (Fin m)
  /-- `|I| ≥ |λ|`. -/
  size_le : lam.size ≤ I.card
  /-- `|I| − |λ|` is even. -/
  even_sub : Even (I.card - lam.size)
  /-- There are `p = (|I| − |λ|)/2` pairs. -/
  card_pairs : pairs.card = (I.card - lam.size) / 2
  /-- Each pair is a 2-element set. -/
  card_pair : ∀ e ∈ pairs, e.card = 2
  /-- The pairs are pairwise disjoint. -/
  pairs_disjoint : (pairs : Set (Finset (Fin m))).PairwiseDisjoint id
  /-- `|B_c| = λ'_c` for `c = 1, …, λ_1`. -/
  card_block : ∀ c ∈ Finset.Icc 1 (lam.row 1), (blocks c).card = colLen lam c
  /-- The blocks are pairwise disjoint. -/
  blocks_disjoint : (↑(Finset.Icc 1 (lam.row 1)) : Set ℕ).PairwiseDisjoint blocks
  /-- Pairs and blocks are disjoint. -/
  pairs_blocks_disjoint : ∀ e ∈ pairs, ∀ c ∈ Finset.Icc 1 (lam.row 1), Disjoint e (blocks c)
  /-- The pairs and the blocks together cover `I` (and are contained in `I`). -/
  cover : pairs.sup id ∪ (Finset.Icc 1 (lam.row 1)).sup blocks = I

/-- **Setting, "Tight patterns"** of `q_P3_identities.md`: the factor `D(y_a, y_b)` of a pair
`{a < b}`, i.e. `D(y_{min e}, y_{max e})` for a 2-element set `e` (the value `1` for an empty `e`
is never used). -/
noncomputable def pairD {m : ℕ} (e : Finset (Fin m)) : C F q m :=
  if h : e.Nonempty then D F q (e.min' h) (e.max' h) else 1

/-- **Setting, "Tight patterns"** of `q_P3_identities.md`: the **product** of a tight pattern,
`G := Π_{{a<b} ∈ P} D(y_a, y_b) · Π_{c=1}^{λ_1} Δ(B_c) ∈ C_m`. -/
noncomputable def TightPattern.prod {m : ℕ} {lam : Partition} {I : Finset (Fin m)}
    (T : TightPattern lam I) : C F q m :=
  (∏ e ∈ T.pairs, pairD F q e) * ∏ c ∈ Finset.Icc 1 (lam.row 1), Delta F q (T.blocks c)

/-- **Setting, "The ideals `V_Λ`"** of `q_P3_identities.md`: for a set `Λ` of partitions and a
finite index set `I ⊆ {1, …, m}`, `V_Λ(I) ⊆ C_m` is the ideal generated by the products of all
tight patterns on `I` of all `λ ∈ Λ`. -/
noncomputable def VLam {m : ℕ} (Λ : Set Partition) (I : Finset (Fin m)) : Ideal (C F q m) :=
  Ideal.span {g | ∃ lam ∈ Λ, ∃ T : TightPattern lam I, T.prod F q = g}

/-- **Setting, "The ideals `V_Λ`"** of `q_P3_identities.md`: `V_Λ := V_Λ({1, …, m})`. -/
noncomputable def VLamAll (m : ℕ) (Λ : Set Partition) : Ideal (C F q m) :=
  VLam F q Λ (Finset.univ : Finset (Fin m))

/-- Auxiliary for the coefficients in `y_a` (**Lemma (iii)** of `q_P3_identities.md`): a
polynomial in `F[y_1, …, y_m]` viewed as a polynomial in the single variable `y_a` whose
coefficients are polynomials in the other variables `y_b`, `b ≠ a`. -/
noncomputable def polyIn {m : ℕ} (a : Fin m) :
    MvPolynomial (Fin m) F →ₐ[F] Polynomial (MvPolynomial {b // b ≠ a} F) :=
  (optionEquivLeft F {b // b ≠ a}).toAlgHom.comp (rename (Equiv.optionSubtypeNe a).symm)

/-- Auxiliary for the coefficients in `y_a` (**Lemma (iii)** of `q_P3_identities.md`): the
coefficient of `y_a^j` of a polynomial `p ∈ F[y_1, …, y_m]`, as a polynomial in the other
variables (regarded again as an element of `F[y_1, …, y_m]`). -/
noncomputable def pcoeff {m : ℕ} (a : Fin m) (j : ℕ) (p : MvPolynomial (Fin m) F) :
    MvPolynomial (Fin m) F :=
  rename Subtype.val ((polyIn F a p).coeff j)

variable {F q}

/-- **Lemma (iii)** of `q_P3_identities.md` (with the convention of `q_peeling_lemma.md`): the
coefficient of `y_a^j` of `f ∈ C_m`.  It is computed on the unique representative of `f` in which
every exponent of `y_a` is at most `q − 2`: for `j ≤ q − 2` it is the class in `C_m` of the
coefficient of `y_a^j` of an arbitrary lift `p` of `f` (this does not depend on the lift, see
`coeffY_mk`), and it is `0` for `j > q − 2`.  The coefficient is a polynomial in the variables
`y_b`, `b ≠ a`, regarded as an element of `C_m`. -/
noncomputable def coeffY {m : ℕ} (a : Fin m) (j : ℕ) (f : C F q m) : C F q m :=
  if j ≤ q - 2 then
    Ideal.Quotient.mk _ (pcoeff F a j (Ideal.Quotient.mk_surjective f).choose)
  else 0

/-- **Lemma (iii)** of `q_P3_identities.md` (with the convention of `q_peeling_lemma.md`): the
degree of `f ∈ C_m` in `y_a`, namely the largest `j ≤ q − 2` whose coefficient of `y_a^j` is
nonzero, with value `⊥` (i.e. `−∞`) for `f = 0`. -/
noncomputable def degY {m : ℕ} (a : Fin m) (f : C F q m) : WithBot ℕ :=
  open Classical in ((Finset.range (q - 1)).filter (fun j => coeffY a j f ≠ 0)).max

variable (F q)

/-- **Lemma (iv)** of `q_P3_identities.md`: a permutation `σ` of the indices `{1, …, m}` acting
on `C_m` by `y_i ↦ y_{σ(i)}` (an `F`-algebra automorphism; here as an `F`-algebra map). -/
noncomputable def relabel {m : ℕ} (σ : Equiv.Perm (Fin m)) : C F q m →ₐ[F] C F q m :=
  Ideal.quotientMapₐ (powIdeal F q m) (rename σ) (by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    simp only [SetLike.mem_coe, Ideal.mem_comap, map_pow, rename_X]
    exact Ideal.subset_span ⟨σ i, rfl⟩)

end Tight

end

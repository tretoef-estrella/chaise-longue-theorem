# The patterns of the odd box and the ideals `V_Λ`

Piece E11 of the plan for the even degrees. Source: paper v11, §8.4 (Definition 8.6, the ideals
`V_Λ`, stability under relabelling), with Lemma 8.7 put into the form in which §8.6 uses it.

Everything is stated for a field `F`, an integer `h ≥ 0`, the odd number `r = 2h + 1` and
`q = r + 1 = 2h + 2`. The ring is

`C_m = F[y_1, …, y_m]/(y_1^r, …, y_m^r)`,

which in the project is `Peel.C F (2*h+2) m`, with `y_i = Tight.y F (2*h+2) i`. Indices are the
elements of `Fin m` with their order.

## What is used unchanged

- Partitions, `ℓ(λ)` (`len`), `λ_1` (`row 1`), `|λ|` (`size`), the column lengths `λ'_c`
  (`Tight.colLen`).
- From `q_P3_identities.md` (`RequestProject/Tight/`): `Tight.y`, `Tight.D`, `Tight.pairD`,
  `Tight.Delta`, `Tight.vand`, `Tight.TightPattern`, `TightPattern.prod`, `Tight.VLam`,
  `Tight.relabel`, `Tight.PM` (equality up to sign), `relabel_prod`, `map_relabel_VLam`.
  All of them are defined for every `q`; here they are used with `q = 2h + 2`.
- `ColOne.Dab` and `ColOne.D_eq_Dab`: `Tight.D F q a b = Dab q (y_a) (y_b)`. With `q = r + 1`
  this is `D(y_a, y_b) = Σ_{u=0}^{r−1} (−1)^u y_a^u y_b^{r−1−u}`, and `D^−(a, b) := Dab r a b =
  Σ_{u=0}^{r−2} (−1)^u a^u b^{r−2−u}`.
- From `q_oddbox_shapes.md` (`RequestProject/OddShapes/`): `Shape = Partition × Bool`
  (`true` is the mark `δ = 1`), `OddShapes.comp Λ δ`.
- From `q_pfaffian.md` (`RequestProject/Pfaffian/`): `pf`, `bpf`, `Pfaffian.ay`, `Pf`, `Pfe`,
  (C6) `C6_e` (a permutation of the indices multiplies `Pf_e` by its sign).
- From `q_membership.md` (`RequestProject/Membership/`): `pairDy`, `DPy`, `UB`, (M4) `M4a`, `M4b`.
- `Odd3.IsPairs`, `Odd3.supp`.

## Part A. The marked Pfaffian

**Definition (A0).** For a commutative ring `A`, integers `h, ℓ ≥ 0`, and `z : Fin n → A` put

- `mPf_0(z) := Pf_{(2h)}(z)`: the bordered Pfaffian `Pfe (2h+1) z (fun _ : Fin 1 => 2*h)`, with
  the single border `i ↦ z_i^{2h}` (the paper's `E_0 = {r − 1}`);
- `mPf_ℓ(z) := Pf_{(0, 1, …, ℓ−2)}(z)` for `ℓ ≥ 1`: `Pfe (2h+1) z (fun k : Fin (ℓ−1) => k)`
  (the paper's `E_ℓ = {0, …, ℓ − 2}`; no border for `ℓ = 1`).

Suggested Lean form:
`mPf h ℓ z := if ℓ = 0 then Pfe (2*h+1) z (fun _ : Fin 1 => 2*h) else Pfe (2*h+1) z (fun k : Fin (ℓ-1) => (k : ℕ))`.

**Lemma A.** Over any commutative ring `A`, with `D^− = Dab (2h+1)`:

- (A1) for `z : Fin 1 → A`: `mPf_0(z) = z_0^{2h}`.
- (A2) for `z : Fin 2 → A`: `mPf_1(z) = D^−(z_0, z_1)`.
- (A3) for `z : Fin 3 → A`:
  `mPf_0(z) = z_2^{2h}·D^−(z_0, z_1) − z_1^{2h}·D^−(z_0, z_2) + z_0^{2h}·D^−(z_1, z_2)`.
- (A4) for `z : Fin 3 → A`: `mPf_2(z) = D^−(z_0, z_1) − D^−(z_0, z_2) + D^−(z_1, z_2)`.
- (A5) (parity) for `z : Fin n → A`: if `n + ℓ` is even, then `mPf_ℓ(z) = 0`. (The matrix of the
  bordered Pfaffian has `n + 1` indices for `ℓ = 0` and `n + ℓ − 1` for `ℓ ≥ 1`, an odd number.)
  So `mPf_ℓ(z)` can be non-zero only if `n = ℓ + 1 + 2t` for some `t` (for `ℓ ≥ 1` also
  `n = ℓ − 1 − 2t'` would have the right parity, but then `n < ℓ + 1`; see (A6)).
- (A6) for `ℓ ≥ 1` and `z : Fin n → A` with `n + 1 < ℓ`: `mPf_ℓ(z) = 0`. (More borders than
  indices: each term of the sum over matchings pairs two borders. This is not used later; if it
  is troublesome, leave it out and say so.)
- (A7) (relabelling) for a permutation `σ` of `Fin n`: `mPf_ℓ(z ∘ σ) = sgn(σ)·mPf_ℓ(z)`.
  (From (C6) `Pfaffian.C6_e`; `2h + 1` is odd.)

*Proof.* (A1)–(A4) by unfolding `Pfe`, `Pf`, `bpf`, `bmat` and the recursion of `pf` along the
index `0`: for a matrix with indices `0 < 1` it is the entry `(0, 1)`; for a matrix with indices
`0 < 1 < 2 < 3` it is `A_{01}A_{23} − A_{02}A_{13} + A_{03}A_{12}`. In (A1) the matrix has the
indices `0` (the point) and `1` (the border), and its entry `(0, 1)` is `z_0^{2h}`. In (A2) there
is no border. In (A3) and (A4) the index `3` is the border, `A_{i3} = z_i^{2h}` (resp. `1`) for
`i ≤ 2`, and `A_{ij} = D^−(z_i, z_j)` for `i < j ≤ 2`. (A5): `pf` of a matrix with an odd number
of indices is `0`. (A7): (C6). ∎

## Part B. Patterns with a marked block

**Definition (B0) (the marked block).** For a finite set `B ⊆ Fin m` with increasing enumeration
`ι_B : Fin |B| → Fin m` and `ℓ ≥ 0`,

`Pf_{E_ℓ}(B) := mPf_ℓ(y ∘ ι_B) ∈ C_m`.

Suggested Lean form: `markedPf F h ℓ B := mPf h ℓ (fun i : Fin B.card => Tight.y F (2*h+2) (B.orderEmbOfFin rfl i))`.

**Definition (B1) (marked pattern; Definition 8.6 of the paper, `δ = 1`).** Let `λ` be a
partition, `ℓ = ℓ(λ)`, and `I ⊆ Fin m`. A *marked pattern* of `λ` on `I` consists of

- a set `P` of pairwise disjoint 2-element subsets of `I` (the pairs);
- pairwise disjoint subsets `B_2, …, B_{λ_1}` of `I` with `|B_c| = λ'_c` (the blocks of the
  columns `c ≥ 2`; there is none if `λ_1 ≤ 1`);
- a subset `B_0` of `I`, the *marked block*, with `|B_0| = ℓ + 1 + 2t` for some `t ≥ 0`;

such that the pairs, the blocks and the marked block are pairwise disjoint and their union is `I`.
Its *product* is

`G := Π_{{a<b} ∈ P} D(y_a, y_b) · Pf_{E_ℓ}(B_0) · Π_{c=2}^{λ_1} Δ(B_c) ∈ C_m`.

Suggested Lean form, modelled on `Tight.TightPattern`: a structure `MarkedPattern lam I` with
fields `pairs : Finset (Finset (Fin m))`, `blocks : ℕ → Finset (Fin m)`,
`marked : Finset (Fin m)`, `card_pair`, `pairs_disjoint`,
`card_block : ∀ c ∈ Finset.Icc 2 (lam.row 1), (blocks c).card = Tight.colLen lam c`,
`blocks_disjoint` on `Finset.Icc 2 (lam.row 1)`, `pairs_blocks_disjoint`,
`pairs_marked_disjoint`, `blocks_marked_disjoint`,
`marked_card : ∃ t, marked.card = lam.len + 1 + 2 * t`, and
`cover : pairs.sup id ∪ (Finset.Icc 2 (lam.row 1)).sup blocks ∪ marked = I`; and
`MarkedPattern.prod F h T := (∏ e ∈ T.pairs, Tight.pairD F (2*h+2) e) * markedPf F h lam.len T.marked * ∏ c ∈ Finset.Icc 2 (lam.row 1), Tight.Delta F (2*h+2) (T.blocks c)`.

**Definition (B2) (the ideals `V_Λ`).** For a set `Λ` of shapes and `I ⊆ Fin m`, `V_Λ(I) ⊆ C_m`
is the ideal generated by

- the products of all tight patterns on `I` of all `λ` with `(λ, 0) ∈ Λ` (`Tight.TightPattern`,
  `TightPattern.prod`, with `q = 2h + 2`: these are the patterns of `δ = 0` of Definition 8.6), and
- the products of all marked patterns on `I` of all `λ` with `(λ, 1) ∈ Λ`.

`V_Λ := V_Λ(Fin m)`. Suggested Lean form:
`VS F h Λ I := Tight.VLam F (2*h+2) (OddShapes.comp Λ false) I ⊔ Ideal.span {g | ∃ lam ∈ OddShapes.comp Λ true, ∃ T : MarkedPattern lam I, T.prod F h = g}` and `VSAll F h m Λ := VS F h Λ Finset.univ`.

**Lemma B.**

- (B3) (sizes) For a marked pattern `T` of `λ` on `I` with `|B_0| = ℓ + 1 + 2t`:
  `|I| = 2|P| + 2t + |λ| + 1`. In particular `|λ| + 1 ≤ |I|`, `|I| − |λ| − 1` is even and
  `|P| + t = (|I| − 1 − |λ|)/2`.
- (B4) (membership) If `(λ, 0) ∈ Λ` and `T` is a tight pattern of `λ` on `I`, then
  `T.prod ∈ V_Λ(I)`; if `(λ, 1) ∈ Λ` and `T` is a marked pattern of `λ` on `I`, then
  `T.prod ∈ V_Λ(I)`.
- (B5) (monotone) If `Λ ⊆ Λ'` then `V_Λ(I) ⊆ V_{Λ'}(I)`. `V_∅(I) = 0`. If `Λ` has no marked
  shape (`comp Λ true = ∅`), then `V_Λ(I) = Tight.VLam F (2h+2) (comp Λ false) I`.
- (B6) (examples) In `C_1`: the marked patterns of the empty partition on `{1}` have the single
  product `y_1^{2h}`, so `V_{{(∅, 1)}} = (y_1^{2h})`. In `C_2`: the marked patterns of `(1)` on
  `{1, 2}` have the single product `D^−(y_1, y_2)`, so `V_{{((1), 1)}} = (D^−(y_1, y_2))`.
  (From (A1), (A2). If the equality of ideals is troublesome, prove that the element lies in
  the ideal and that every generator is that element.)

*Proof.* (B3): the sets partition `I`; `Σ_{c=2}^{λ_1} λ'_c = |λ| − λ'_1 = |λ| − ℓ`, so
`|I| = 2|P| + (|λ| − ℓ) + (ℓ + 1 + 2t)`. (B4), (B5): by definition. ∎

## Part C. Stability under relabelling

A permutation `σ` of `Fin m` acts on `C_m` by `y_i ↦ y_{σ(i)}` (`Tight.relabel F q σ`).

**Lemma C.**

- (C1) For `B ⊆ Fin m` and `ℓ ≥ 0`: `σ(Pf_{E_ℓ}(B)) = ± Pf_{E_ℓ}(σ(B))`.
- (C2) For a marked pattern `T` of `λ` on `I` there is a marked pattern `T'` of `λ` on `σ(I)` with
  `σ(T.prod) = ± T'.prod`.
- (C3) `σ(V_Λ(I)) = V_Λ(σ(I))`, where `σ(V)` is the image of the ideal `V` under the automorphism
  (`Ideal.map (Tight.relabel F q σ)`, `I.map σ.toEmbedding`). In particular `σ(V_Λ) = V_Λ`.

*Proof.* (C1) `σ(Pf_{E_ℓ}(B)) = mPf_ℓ(y ∘ σ ∘ ι_B)`, because `σ` is a ring homomorphism and
`mPf_ℓ(z)` is a polynomial expression with integer coefficients in the `z_i` (it commutes with
ring homomorphisms). The map `σ ∘ ι_B : Fin |B| → Fin m` is injective with image `σ(B)`, so
`σ ∘ ι_B = ι_{σ(B)} ∘ τ` for a unique permutation `τ` of `Fin |B|` (after identifying
`|σ(B)| = |B|`), and by (A7) `mPf_ℓ(y ∘ ι_{σ(B)} ∘ τ) = sgn(τ)·mPf_ℓ(y ∘ ι_{σ(B)})`.
(C2) `T'` has the pairs `σ(e)`, the blocks `σ(B_c)` and the marked block `σ(B_0)`; the factors
`D` and `Δ` change by signs (`relabel_pairD`, `relabel_Delta` of `q_P3_identities.md`) and the
marked factor by (C1). (C3) from (C2) and `map_relabel_VLam` for the unmarked part, applied to
`σ` and to `σ^{−1}` as in the proof of `map_relabel_VLam`. ∎

## Part D. Lemma 8.7 in the ring `C_m`

**Lemma D.** Let `h ≥ 1`.

- (D1) `y_i^{2h+1} = 0` in `C_m` for every `i`.
- (D2) For a set `P` of subsets of `Fin m`:
  `Membership.DPy (2h+1) y P = Π_{e ∈ P} Tight.pairD F (2h+2) e`; and
  `Tight.vand y S = Tight.Delta F (2h+2) S`. So the generators of the ideal
  `𝔘_p(y; B) = Membership.UB (2h+1) p y B` of `q_membership.md` are the elements
  `Δ(S)·Π_{e ∈ P} D_e` with `S ⊆ B`, `|S| = p`, and `P` a perfect matching of `B ∖ S`.
- (D3) (Lemma 8.7) For `ℓ ≥ 0` and `B ⊆ Fin m` with `|B| = ℓ + 1 + 2t`:
  `Pf_{E_ℓ}(B) ∈ 𝔘_{ℓ+1}(y; B)`, that is,
  `markedPf F h ℓ B ∈ Membership.UB (2*h+1) (ℓ+1) (Tight.y F (2*h+2)) B`.

*Proof.* (D1): the defining relations of `C_m` (`q − 1 = 2h + 1`). (D2): `ColOne.D_eq_Dab` and the
definitions. (D3): for `ℓ ≥ 1` it is (M4)(a) of `q_membership.md` with `s = ℓ − 1`, `n = |B| =
s + 2(t + 1)`, the exponents `e_k = k`, and the ideal `UB (2h+1) (s+2) y B`, `s + 2 = ℓ + 1`. For
`ℓ = 0` it is (M4)(b) with `s = 0`, `n = |B| = 1 + 2t`: the list of borders is the single border
`y^{2h}`, and the ideal is `UB (2h+1) 1 y B` (compare the proof of `Membership.M3_zero`). ∎

## What was checked before sending

In exact arithmetic (the script `chkE11.py`; the numbers are in the instruction):

1. (A1)–(A4) with the signs as stated, (A5), (A6), (A7), for `r = 3, 5, 7`.
2. The marked Pfaffian `Pf_{E_ℓ}(B)` in the convention of the project (`bmat`, `pf` along the
   index `0`) against the auditor's independent engine of the cold audit, which expands the
   Pfaffian of the paper directly: equal up to sign in every case tried.
3. (B3) on every marked pattern generated.
4. (C1), (C2) for random permutations.
5. (D3) by linear algebra modulo a prime.
6. `dim_F V_Λ = |Z_Λ|` for every interlaced pair `Λ` of the cells tried, with `V_Λ` built from
   the definitions above — the known count of the paper (Theorem 8.11 and Corollary 8.13) — so
   that the definition is tested against a number that it must reproduce.

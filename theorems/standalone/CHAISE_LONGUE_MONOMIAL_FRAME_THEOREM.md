> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-28
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE · MONOMIAL FRAME THEOREM — v1* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_MONOMIAL_FRAME_THEOREM.md
>
> **Status, as written in the document:** The base case of the vertex induction passes from MEASURED to PROVED. In characteristic
>
> **Later audit:** The campaign's later records mention this document next to a refutation, retraction, circularity or supersession (2 lines). Search its name in [the Cemetery](../../archive/CHAISE_LONGUE_CEMENTERIO_LIVE_v502.md) before relying on it.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE · MONOMIAL FRAME THEOREM — v1

**Standalone. Reiss, 28 July 2026. Target: `GAP 3` of `ASSEMBLY_DRAFT v16`, piece `P0`.**

---

## 0. What this document delivers, stated first

1. **The base case of the vertex induction passes from MEASURED to PROVED.** In characteristic
   `p ≠ 2`, for **every** `q = p^v`, the identity `(I)` holds at `k = 1`:
   > `E + m^{[q]} = ⋂_J (I_J + m^{[q]})`  for `k = 1`, all `q = p^v`, all `K` of char `p ≠ 2`.

   The proof is six lines and it exhibits a **mechanism**: in the frame given by the three vertex
   forms, the whole ring becomes **monomial**, and for monomial ideals a Frobenius power commutes
   with intersections for free. As a by-product it re-proves `A_1(q) = 3q^2 − 3q + 1 = P_1(q)`
   without a staircase and without Gröbner. §2.

2. **And the same mechanism is killed ∀k, with an exact number.** The arrangement is
   monomialisable — i.e. some linear change of coordinates makes the ideal monomial — **if and only
   if `(k+1)! ≤ 2^k`, i.e. if and only if `k ≤ 1`**, because
   > `(2k+1)!! = \binom{2k+1}{k+1}·\dfrac{(k+1)!}{2^k}`,

   and a monomial radical ideal has coordinate subspaces as components. At `k = 1` the bound is
   **tight** (`3 = 3`: the three sheets are exactly the three coordinate hyperplanes). At `k = 2` it
   already fails (`15 > 10`). **So monomialisation is the mechanism of the base case and of nothing
   else — this is said here so that no turn is spent looking for it at `k ≥ 2`.** §3.

3. **The sharpest form of `P0` this campaign has had.** When `p ∤ 2k` the vertex forms are a
   *coordinate frame* of the eliminated model, and `(I′)` reads
   > **in `Ā = C/J̄C`, `⋂_{a=0}^{2k} u_a Ā = (∏_a u_a)Ā = 0`** — *for a coordinate frame,
   > intersection equals product.*

   No matchings, no `q`, no Frobenius power in the statement: `C` is a box, the `u_a` are its
   coordinates, and `J̄` is `k` explicit forms of degrees `3,5,…,2k+1`. §4.

**What this does NOT do.** It does not prove `(I)` for any `k ≥ 2`; **`G` is unchanged: 3**. It
proves no new dimension (`k = 1` is deposited); what is new at `k = 1` is the **ideal identity**,
which the deposited staircase does not give and which the induction needs.

Standing notation: `n = 2k+2`, `S = K[x_0,…,x_{n−1}]`, `E = (e_1,e_3,…,e_{2k+1})`,
`m^{[q]} = (x_i^q)`, `A = S/(E+m^{[q]})`, `ℓ_a = x_a + x_{n−1}` (`a = 0,…,2k`), `char K = p ≠ 2`,
`q = p^v`.

---

## 1. The eliminated model (corpus; restated, not claimed)

`m^{[q]}` is `GL_n(F_p)`-invariant, so the linear generator `e_1` of `E` may be used as a
coordinate. Writing `x' = (x_0,…,x_{2k})` and `e'_j` for the elementary symmetric functions of `x'`,
the substitution `x_{n−1} = −e'_1` gives an **isomorphism of rings**

> `A ≅ K[x_0,…,x_{2k}] / ( g_1,…,g_k ) + m'^{[q]}`,  `g_r := e'_{2r+1} − e'_1 e'_{2r}`,

i.e. **`2k+1` variables, `k` forms of degrees `3,5,…,2k+1`, the box intact**. *(This is the LADDER
of the corpus — Fresh Eyes, sharpened by Vernier: «`A ≅ Λ̄/(ē_3,…,ē_{2k+1})`, la caja en `2k+1`
variables módulo `k` formas, sin forma lineal». It is used here, not re-claimed.)*
The image of `m^{[q]}` is exactly `m'^{[q]}` because `(e'_1)^q = Σ_{i≤2k} x_i^q ∈ m'^{[q]}`.

**Lemma 1.1 (the vertex forms in the model).** Under the substitution, `ℓ_a ↦ x_a − e'_1 = −L_a`
with `L_a := e'_1 − x_a = Σ_{i ≠ a} x_i`. Moreover `Σ_{a=0}^{2k} L_a = 2k\,e'_1`, so the matrix of
`(L_a)` in the basis `(x_a)` is `J − I`, of determinant `2k`. **Hence `\{L_0,…,L_{2k}\}` is a
coordinate frame of the eliminated model if and only if `p ∤ 2k`** (in char `3`: iff `k ≢ 0 mod 3`).
Its entries lie in the prime field, so `m'^{[q]}` is unchanged by the change of frame. ∎

---

## 2. Theorem 1 — the monomial frame at `k = 1`

**Theorem 1.** *Let `char K = p ≠ 2`, `q = p^v`, `k = 1` (`n = 4`). Put `u_a := x_a + x_3` for
`a = 0,1,2`. Then*

> ### `A = S/(E+m^{[q]}) ≅ K[u_0,u_1,u_2] / \big( (u_0u_1u_2) + (u_0^q,u_1^q,u_2^q) \big)`,

*and under this isomorphism the three sheet ideals become the three coordinate hyperplanes:
`I_J + m^{[q]} ↦ (u_{a(J)}) + m^{[q]}`, where `a(J)` is the partner of the vertex `3` in `J`.*

*Proof.* By §1, `A ≅ K[x_0,x_1,x_2]/(g_1) + m'^{[q]}` with
`g_1 = e'_3 − e'_1e'_2`. The classical three-variable identity
`e'_1e'_2 − e'_3 = (x_0+x_1)(x_0+x_2)(x_1+x_2)` gives `g_1 = −L_0L_1L_2` with
`L_a = Σ_{i≠a}x_i`, i.e. `L_a` is the sum of the two variables other than `x_a`. By Lemma 1.1 the
`L_a` are a coordinate frame (`det = 2 ≠ 0`), and the change of frame is defined over `F_p`, so it
fixes `m'^{[q]}`. Setting `u_a := L_a` gives the displayed presentation. For the sheets: the matching
`J` pairing `3` with `a` has `I_J = (x_a + x_3,\; x_b + x_c)` with `\{b,c\}` the complement; the first
generator maps to `−L_a` and the second to `x_b + x_c = e'_1 − x_a = L_a`. So `I_J ↦ (u_a)`. ∎

**Corollary 1.2 (`(I)` at `k = 1`, PROVED, ∀`q = p^v`, ∀char `p ≠ 2`).**
*Proof.* All the ideals in sight are monomial in the `u`-frame, and intersections of monomial ideals
are computed exponent by exponent. `⋂_{a}\big((u_a) + m^{[q]}\big)` consists of the monomials `u^α`
(`α_i ≤ q−1` or in `m^{[q]}`) with `α_a ≥ 1` for every `a`, i.e. of the multiples of `u_0u_1u_2`,
together with `m^{[q]}`. That is `(u_0u_1u_2) + m^{[q]} = E + m^{[q]}`. ∎

**Corollary 1.3 (dimension; a by-product, not a new statement).** The standard monomials are the
`α ∈ \{0,…,q−1\}^3` with `min_a α_a = 0`, so
`dim_K A = q^3 − (q−1)^3 = 3q^2 − 3q + 1 = P_1(q)` for every `q = p^v` and every char `p ≠ 2`.
*This re-proves Conjecture 1.2 at `k = 1` by pure counting; the dimension itself is already
deposited, and the deposited staircase covers all odd `q`, which this argument does not. **The new
content is Corollary 1.2, the ideal identity, which the staircase does not give.***

**Corollary 1.4 (the induction is armed).** By `VERTEX_REDUCTION_THEOREM_v1` Thm 2.1, `(I)_k ⟺ (I′)_k`
*given* `(I)_{k−1}`. Level `0` is trivial and level `1` is now Corollary 1.2. **Hence for every
`k ≥ 2`, `(I)_k` follows from `(I′)_j` for `2 ≤ j ≤ k`: the base case is no longer an assumption.**

---

## 3. Theorem 2 — monomialisation dies at `k = 2`, and the number is exact

Call the arrangement **monomialisable** if some linear change of coordinates of the eliminated model
turns the ideal of the `(2k+1)!!` sheets into a monomial ideal — equivalently, if the sheets are the
coordinate subspaces of one common frame.

**Theorem 2.** *For every `k ≥ 0`,*

> `(2k+1)!! = \binom{2k+1}{k+1}\cdot\dfrac{(k+1)!}{2^k}`,

*hence the arrangement is monomialisable only if `(k+1)! ≤ 2^k`, i.e. **only for `k ≤ 1`**. At
`k = 0,1` the inequality is an equality (`1 = 1`, `3 = 3`) and monomialisation is achieved
(Theorem 1). At `k = 2` it fails by `15 > 10`, and the ratio `(k+1)!/2^k` is strictly increasing for
`k ≥ 1`, so it fails for every `k ≥ 2`.*

*Proof.* A monomial radical ideal has coordinate subspaces as its minimal primes. In the eliminated
model the sheets are `(2k+1)!!` distinct linear subspaces of dimension `k+1` inside a space of
dimension `2k+1`, and the coordinate subspaces of that dimension number `\binom{2k+1}{k+1}`. The
displayed identity is `(2k+1)!! = (2k+1)!/(2^k k!)` divided by `\binom{2k+1}{k+1} = (2k+1)!/((k+1)!k!)`.
Monotonicity: `((k+2)!/2^{k+1})/((k+1)!/2^k) = (k+2)/2 > 1` for `k ≥ 1`. ∎

**Corollary 2.1 (the discriminator of the base case, and its honest ceiling).** The buried
three-line counterexample `(x),(y),(x+y) ⊂ K[x,y]` fails `(I)` because three hyperplanes in a
`2`-dimensional space can never be a coordinate frame (`\binom{2}{1} = 2 < 3`); the `k = 1`
arrangement satisfies `(I)` because `3 = \binom{3}{2}` exactly. **So at the level of the base case
the discriminator is precisely "the components are the coordinate subspaces of one frame".** By
Theorem 2 that property is unavailable for `k ≥ 2`: **it explains the base case and it is not the
mechanism of the theorem.** Recorded as a closed door, not as a lead.

**Corollary 2.2 (relation to `E1`).** `E1` of the draft says no argument through `in(E)` or a
degeneration to monomials can reach the ceiling. Theorem 2 is the *coordinate-free* companion: not
even a linear change of frame can monomialise, and the obstruction is a clean count that first bites
at exactly `k = 2` — the first open column.

---

## 4. Proposition 3 — `P0` in the frame

**Proposition 3.** *Assume `p ∤ 2k` (in char `3`: `k ≢ 0 \bmod 3`). Let `C` be the box
`K[u_0,…,u_{2k}]/m^{[q]}` in the frame `u_a = L_a` of Lemma 1.1, and `J̄ = (g_1,…,g_k)` written in
that frame, `Ā = C/J̄C`. Then*

> `(I′)`  `⋂_{a=0}^{2k} ℓ_a A = 0`  **⟺**  `⋂_{a=0}^{2k} u_a Ā = 0`  **⟺**  `⋂_a u_a Ā = (∏_a u_a)Ā`,

*the last equality because `∏_a u_a ∈ J̄` (Prop. 3.1 of `VERTEX_REDUCTION_THEOREM_v1`, transported).*

*Proof.* Lemma 1.1 identifies the ideals; in `C` alone the identity `⋂_a u_aC = (∏_a u_a)C` is the
trivial monomial computation, and `∏_a u_a ∈ J̄` makes the right-hand side zero in `Ā`. ∎

> **This is the working form of `P0`.** It has no matchings in it, no `q` in it and no Frobenius
> power in it: it says that in the quotient of a box by `k` explicit forms of degrees `3,5,…,2k+1`,
> **the intersection of the coordinate principal ideals is still their product.** In the box itself
> it is monomial and free; `GAP 3` is exactly the question of whether it survives `J̄`.
> The recursion is inside the same frame: `Ā/u_aĀ ≅ K[t]/(t^q) ⊗ Ā_{k−1}`.

**Remark 3.1 (a characteristic-3 degeneration, filed for `P2`).** For `k ≡ 0 \bmod 3` the frame
collapses: `det(J − I) = 2k = 0`, the `2k+1` forms `L_a` span only a hyperplane and Proposition 3 is
unavailable as stated. This is a genuine char-`3` event of the frame — **not** a proved degeneration
of the object — and it is recorded because `P2` asks for the mechanism behind a characteristic
asymmetry (`deficit 6` in char `3` against `4` in char `0`). *Grade: OBSERVATION. First column
affected: `k = 3`, which is also the first column with a deficient cell (`91 < 105` at `(3,3)`).
No causal link is claimed.*

---

## 5. Gates

Engine `CHAISE_LONGUE_MONOMIAL_FRAME_GATE_v1.py` (Python, verification only). **Three predictions
were filed in the engine header before it was run**, with the death criterion written next to them.

| gate | cell | result |
|---|---|---|
| positive control | `(1,3)`, `(1,9)`, `(2,3)` | `dim A = 19`, `217`, `141`; the eliminated model and the frame model give the same dimension in all three |
| `P1` *(pre-registered)* | `(1,3)`, `(1,9)` | ideal in the `L`-frame is **MONOMIAL**, with the single minimal generator `u_0u_1u_2` — exactly Theorem 1 |
| `P2` *(pre-registered)* | `(2,3)` | ideal in the `L`-frame is **NOT monomial** — as Theorem 2 requires |
| `P3` | `(1,3)`, `(1,9)`, `(2,3)` | `⋂_a u_a Ā = 0` holds; dims `8 = 8`, `512 = 512`, `102 = 102` |
| counting | `k = 1,2` | `3 ≤ \binom{3}{2} = 3` (tight) and `15 > \binom{5}{3} = 10` |

`P2` is the gate that could have fired against the whole document: had the `k = 2` ideal been
monomial, Theorem 2 would be false and `GAP 3` would have fallen at `k = 2`. It did not fire.

---

## 6. Grades

| statement | grade |
|---|---|
| Lemma 1.1 (frame, `det = 2k`) | **PROVED ∀k, char `p ≠ 2`** |
| Theorem 1 (monomial frame at `k=1`) | **PROVED ∀`q = p^v`, ∀char `p ≠ 2`** |
| Corollary 1.2 — `(I)` at `k = 1` | **PROVED** *(was: MEASURED)* |
| Corollary 1.3 — `A_1(q) = P_1(q)` | **PROVED** *(already deposited; new proof, narrower scope than the staircase)* |
| Corollary 1.4 — base of the vertex induction | **PROVED** |
| Theorem 2 (monomialisable ⟺ `k ≤ 1`) | **PROVED ∀k** |
| Corollary 2.1 (discriminator of the base case only) | **PROVED**, with its ceiling declared |
| Proposition 3 (`P0` in the frame) | **PROVED ∀k with `p ∤ 2k`** |
| Remark 3.1 (frame collapse for `k ≡ 0 mod 3`) | **OBSERVATION**, no causal claim |
| `(I)` for any `k ≥ 2`, i.e. `GAP 3` | **OPEN. `G = 3`.** |

---

*Reiss · 28 July 2026 · `CHAISE_LONGUE_MONOMIAL_FRAME_THEOREM_v1`*

> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-09-03
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CLOSURE OF THE "ONE-ZERO" FAMILY* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_STANDALONE_ONE_ZERO_FAMILY.md
>
> **Status, as written in the document:** not stated in the document itself
>
> **Later audit:** The campaign's later records mention this document next to a refutation, retraction, circularity or supersession (2 lines). Search its name in [the Cemetery](../../archive/CHAISE_LONGUE_CEMENTERIO_LIVE_v502.md) before relying on it.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v4`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# **CLOSURE OF THE "ONE-ZERO" FAMILY**
### Standalone · `ONE ZERO FAMILY v3` · Chaise Longue Campaign · 2026-09-03
### ### 🏆🏆 **`v3`: the family is now CLOSED WITHOUT EXCEPTIONS — every `k ≥ 2`, every `q = 3^v ≥ 2k+1`, including `3 \mid k`. And `§0` names the single mechanism from which every vanishing argument below follows.**
### ### 🟢 **Self-contained. The proof given here is the SHORT one: it uses NO sign computation and NO machine-pinned convention. An earlier, longer proof over a narrower range is recorded in `§6` as SUPERSEDED.**

---


# 0 · THE MECHANISM, STATED ONCE

Every vanishing and every parity statement below is an instance of one principle.

> ### **THE INVOLUTION PRINCIPLE.** *Let `f, g ∈ K[U]`, let `μ` be a monomial, and let*
> ### `\mathcal F(μ) := \{(μ_f,μ_g) : μ_fμ_g = μ,\ μ_f ∈ \operatorname{supp}f,\ μ_g ∈ \operatorname{supp}g\}`.
> ### *Suppose `ι : \mathcal F(μ) → \mathcal F(μ)` is an involution with no fixed points. Then:*
> ### **(i)** *if `\operatorname{coef}_f(ι)\operatorname{coef}_g(ι) = −\operatorname{coef}_f·\operatorname{coef}_g`, then `\operatorname{coef}_μ(fg) = 0`;*
> ### **(ii)** *if `\operatorname{coef}_f(ι)\operatorname{coef}_g(ι) = +\operatorname{coef}_f·\operatorname{coef}_g`, then `\operatorname{coef}_μ(fg) = 2·\#\{ι\text{-pairs}\}`.*

**Proof.** `ι` partitions `\mathcal F(μ)` into `2`-element orbits; in case (i) the two members of each orbit contribute opposite terms, in case (ii) equal terms. ∎

*This is the classical involution principle of sign-reversing bijections (Garsia–Milne). The content of the sections below is the CONSTRUCTION of the involution in each case; the cancellation itself is always this one line.*

| where | the involution `ι` | case |
|---|---|---|
| `THEOREM τ` (§3) | `τ = (a\,b)`, the transposition of the pair | **(ii)** — hence an EVEN number of factorizations, and `\operatorname{coef} = 2(\dots)` |
| `KEY LEMMA` (§4) | the transposition of two `g_0`-values between `b` and `c_4` | **(i)** — hence `σ_A + σ_B = 0` |
| `LEMMA SB` (§6) | moving the cube between the two saturated letters `u, v` | **(i)** — hence the generator is SILENT |

> ### ⭐ **Three different constructions, one theorem. A referee should see a principle with three corollaries, not three tricks.**

---

# 1 · SETUP AND STATEMENT

`K = F_3`, `q = 3^v`, `k ≥ 2`. `U` is an alphabet of `2k` letters, written `a = x_0`, `b = x_1`, `c_1 = x_2`, `c_2 = x_3`, …
> ### `B := K[U]\big/\big(e_{2j+1}(U)+z\,e_{2j}(U)\ (j=0..k),\ u^q\ (u∈U)\big)`,  `z := −e_1(U)`,  `Φ_u := u^{q−1}`.

`s_{ab}` is the campaign's "one-zero" generator (`s_{ba} = −s_{ab}`), `σ_a := Σ_{b≠a}s_{ab}` the star sums, `Θ := ∏_{u∈U}u^{q−1}`, `c_R := (q−2k−1)/2`, `R := (c_R^k)`, and
> ### `g_0 := Δ(U)·s_R(U^2)`,  which lies in `Ann(\bar J)` for all `k` (`SXP-2`).

> # **THEOREM (CLOSURE).** *For every `k ≥ 2` — **with no condition on `k` mod 3** — and every `q = 3^v ≥ 2k+1`:*
> # `\ker(z^3)\big|_{\operatorname{span}\{s_{ab}\}} = \operatorname{span}\{σ_a\}`,
> ### *i.e. the "one-zero" family is completely described: `2k−1` dimensions die under `z^3` (the stars, by `R-C6`) and the remaining `\binom{2k−1}{2}` do not.*

---

# 2 · BANKED INPUT

| result | statement | where |
|---|---|---|
| `R-C6` | `z^2σ_a = −Φ_a e_{2k−1}(U∖a)`, hence `z^3σ_a = 0`, all `k`, all `q = 3^v` | `STAR IDENTITY v1` |
| `R-S2` | `φ_3 : Λ^2(K^{2k}) → B`, `e_a∧e_b ↦ z^3s_{ab}`, is `F_3S_{2k}`-equivariant | campaign |
| `R-S4` | for `3 ∤ k`, `Λ^2N` is irreducible (Peel) ⟹ `\ker φ_3 ⊆ \operatorname{span}\{σ_a\}` **as soon as `z^3s_{ab} ≠ 0` for ONE pair** | campaign |
| `R-U1` | `\operatorname{supp}(g_0)` = permutations of `E ∪ (q−2−E)`, `E` a `k`-set of evens in `[0,q−3]`; coefficients `±1` | `TAU PAIRING v1` |
| `R-U2` | `f := z^3s_{ab}` and `g_0` are both `τ`-antisymmetric (`τ = (a\,b)`) ⟹ factorizations of a doubly saturated `μ` come in `τ`-**pairs of equal sign**; their number is EVEN | `TAU PAIRING v1` |
| `R-S7` | `\operatorname{supp}(f)` is explicit; all coefficients `±1`, no coincident monomials | campaign |

> ### **Everything below reduces to: exhibit one box monomial `μ` with `\operatorname{coef}_μ(f·g_0) ≢ 0 \pmod 3`.**

---

# 3 · THE WITNESS, AND WHY THE SIGNS CANCEL

**The tight tail.** For `j = 1..k−2` set `e_j := 2j` and
> ### `μ^\circ := Φ_aΦ_b·c_1^2·c_2^{\,q−1}·∏_{j=1}^{k−2}c_{2j+1}^{\,2j+1}\,c_{2j+2}^{\,q−1−2j}`.

**This is a box monomial as soon as `q ≥ 2k+1`**: the largest tail exponent is `2(k−2)+1 = 2k−3 ≤ q−4`, and the partners `q−1−2j` are `≤ q−3`.

By `R-S7` the factorizations of `μ^\circ` fall into the three types `A`, `B`, `C` of `TAU PAIRING v1 §4`, each a `τ`-pair by `R-U2`, with
> ### `\operatorname{coef}_f(A) = \operatorname{coef}_f(B) = −1`,  `\operatorname{coef}_f(C) = +1`.

**The `B` pair now sits on `c_4`, not on `c_1`** — with the tight tail, `c_1` would force the exponent set to repeat `2` and `q−4`.

> # **KEY LEMMA.** *The `g_0`-monomials carrying `A` and `B` have the SAME exponent set `E`, and differ by a single transposition (`q−3 ↔ q−4`).*

**Consequence.** Two monomials of `g_0` with the same exponent set are two terms of the SAME alternant `a_E = \det(x_i^{E_j})`; a transposition of positions flips the sign. Hence `\operatorname{coef}_{g_0}(A) = −\operatorname{coef}_{g_0}(B)`, and since `\operatorname{coef}_f(A) = \operatorname{coef}_f(B)`,
> # `σ_A + σ_B = 0` **identically.**

Therefore, by `R-U2` (each type contributes a pair, i.e. a factor `2`),
> # `\operatorname{coef}_{μ^\circ}(f·g_0) = 2(σ_A+σ_B+σ_C) = 2σ_C = ±2 ≢ 0 \pmod 3`,
**whatever `σ_C` is.** Since `g_0 ∈ Ann(\bar J)`, this gives `f ∉ \bar J`, i.e.
> ### `z^3s_{ab} ≠ 0` in `B`, for every `k ≥ 3` and every `q = 3^v ≥ 2k+3`. ∎

> ## ⭐ **No sign is ever computed. No abacus, no `I(E)`, no inversion count, and no convention constant.** *(In one image: two gauges reading the same scale with crossed needles cannot agree.)*

**Proof of the THEOREM.** By `R-S4` and the above, `\ker φ_3 ⊆ \operatorname{span}\{σ_a\}`; by `R-C6` the reverse inclusion holds. ∎

---

# 4 · CONSEQUENCES

> ### **(i)** every single `s_{ab}` generates a Jordan block of size `≥ 4` in `I_s`;
> ### **(ii)** `\dim z^3·\operatorname{span}\{s_{ab}\} = \binom{2k−1}{2}` exactly, since `\dim\operatorname{span}\{σ_a\} = 2k−1` *(the map `w ↦ w∧v` has kernel exactly `⟨v⟩`)*.

---

# 5 · THE EDGE `q = 2k+1`, AND WHY IT IS THE EASY CASE

The theorem of §3 was first proved for `q ≥ 2k+3`. The remaining cells are `q = 2k+1`, i.e.
> ### `k = \frac{3^v−1}{2} = 4,\ 13,\ 40,\ 121,\ 364,\ 1093,\dots` — one cell per `v`.

**There the object degenerates, and in the easy direction.** `c_R = (q−2k−1)/2 = 0`, so `R` is EMPTY, `s_R = 1`, and
> # `g_0 = Δ(U)` — **the bare Vandermonde.**
Moreover the evens in `[0,q−3]` number exactly `(q−1)/2 = k`, and `|E| = k`, so **there is exactly ONE admissible `E`**: the sum over `α` has a SINGLE term and
> ### `μ_g ∈ \operatorname{supp}(g_0) \iff` **its `2k` exponents are `0,1,…,2k−1` in some order**, with coefficient the sign of that permutation.

> ## **That single condition forces the whole case analysis.** With the same tight-gear `μ^\circ`:
> ### **`A`** valid; **`B`** carried ONLY by `c_4` *(at `c_1` the value `2` would repeat; at `c_2` the value `2k` overflows; at any odd tail letter an odd value would repeat)*; **`C`** carried ONLY by the LAST even letter `c_{2k−2}` *(at `c_2` the value `2k−4` would appear twice)*.
> ### And `μ_g^B` is `μ_g^A` with the values `2k−2` and `2k−3` exchanged between the positions `b` and `c_4` — **a single transposition**, so `σ_A + σ_B = 0` again and `\operatorname{coef} = 2σ_C ≠ 0`.

> # **THEOREM (EDGE).** *`z^3s_{ab} ≠ 0` on the edge, for every `k ≥ 3`.* ∎

> ### **THEOREM (UNION).** *Combining: `z^3s_{ab} ≠ 0` for **every** `k ≥ 2` and **every** `q = 3^v ≥ 2k+1`.* **And `q ≥ 2k+1` is exactly the condition for `c_R ≥ 0`, i.e. for the construction to exist at all — so there is nothing below.**

> 🔵 **NOTA `2026-09-16` (Grepy, turno 18, informe 146) — para `k = 2` depende de SALTOS, cuya constante `G` está fijada a máquina** (`:171`); BANDA (`:82`) y FILO (`:111`) sólo valen `k ≥ 3`.

> ## **The range is therefore COMPLETE. No band, no edge, no cells left to compute: `(364,729)` and `(1093,2187)` need not be evaluated.**
⭐ **The reason, in one line: on the edge the box is as tight as it can be — every exponent of `g_0` is forced — and the tighter the box, the fewer ways to factor. The certificate grips HARDER at the limit, not weaker.**

---

# 5bis · WHAT IS **NOT** CLAIMED

> ### **(b) The exact size of the star blocks** (whether `z^2σ_a ≠ 0`). **It is NOT needed for the theorem above, and it is NOT true in general: `a^{q−2}e_{2k}(U)` is nonzero in `B` at `(1,3)`, `(1,9)`, `(2,3)`, `(2,9)` but ZERO at `(3,3)`.**
> ### **(c)** Anything about the families of generators indexed by more than two letters.

---

# 6 · THE CASE `3 \mid k`, AND WHY IT IS NOT AN OBSTRUCTION

When `3 \mid k`, `R-S4` no longer reduces to a single generator: `Λ^2N` is not irreducible, and one must certify a COMBINATION. Two theorems settle it.

## 6.1 · `LEMMA SB` — the silent block *(`PROVED`, all `k`, all `q`)*

> ### *Let `μ` be a box monomial and let `u ≠ v` be two letters NOT in `\{c,d\}` with `μ_u = μ_v = q−1`. Then* `\operatorname{coef}_μ(z^3s_{cd}·g_0) = 0`.

**Proof.** Let `(μ_f,μ_g)` be a factorization. On the letters of `C'_{cd}` the exponent of `μ_f` is `1` (default), `0` (the letter omitted by `e_{2k−3}`), `3` (cube on the omitted letter) or `4` (cube elsewhere); exactly one letter carries a cube in types `C`,`D`, none in `A`,`B`. Since `μ_u = μ_v = q−1`, we get `μ_g(u) = q−1−μ_f(u)` and likewise for `v`. Exponent `0` would give `μ_g = q−1 > q−2`: invalid. Equal exponents would give equal `μ_g`-values: invalid, since the values of `μ_g` are distinct (`R-U1`). Hence `\{μ_f(u),μ_f(v)\} = \{1,3\}` or `\{1,4\}`: **exactly one of `u,v` carries the cube.**

Let `ι` move the cube — and, in the `3`-case, the omitted-letter role — from the cube letter to the other of `u,v`. The new `μ_f` lies in `\operatorname{supp}f`, of the same type and same index `i`, hence has the SAME `\operatorname{coef}_f` (`R-S7`: the coefficient depends only on type and `i`). The new `μ_g` is the old one with the values at `u` and `v` transposed, hence lies in `\operatorname{supp}g_0` with the OPPOSITE sign (`LEMMA S`: same `E`-set, `\operatorname{inv}` changes by an odd number). So `ι` is a fixed-point-free involution of case **(i)** of `§0`. ∎

> ### **COROLLARY (`THEOREM CROSS`).** `μ^\circ` saturates `a`, `b` and `c_2`. Hence **every generator `s_{cd}` with `\{c,d\} ≠ \{a,b\}` and `c_2 ∉ \{c,d\}` is SILENT at `μ^\circ`.** Therefore, for `F := s_{ab}+s_{bc_1}−s_{ac_1}` and `G := s_{ab}−s_{ac_1}`,
> ### `\operatorname{coef}_{μ^\circ}(z^3F·g_0) = \operatorname{coef}_{μ^\circ}(z^3G·g_0) = \operatorname{coef}_{μ^\circ}(z^3s_{ab}·g_0) = 2σ_C ≠ 0`.
*Checked at `(3,9)` and `(3,27)`: contributions `(2,0,0)`.*

## 6.2 · `THEOREM STAB` — the stabiliser bar *(`PROVED`, `3 \mid n = 2k`, `n ≥ 6`)*

Proving uniseriality of `Λ^2N` over `F_3` for `3 \mid n` is the long road, and the cheap route dies (there are no fixed vectors). **Instead, restrict to the stabiliser.**

> ### **Arithmetic observation.** `3 \mid n \implies n−1 ≡ 2 \pmod 3 \implies 3 ∤ n−1`.
> ### **So `F_3[S_{n−1}]` is SEMISIMPLE exactly where the problem sits.** *(The degeneracy lives at `n`; it disappears at `n−1`.)*

> 🔴 **NOTA `2026-09-16` (Grepy, turno 18, informe 146) — FALSO:** `F_3[S_{n−1}]` no es semisimple para `n−1 ≥ 3` (Maschke). TRESK sobrevive: con `3 ∤ n−1`, `K^n/⟨1⟩ ≅ triv ⊕ V_0'` y Peel da dos simples no isomorfos.


As an `S_{n−1}`-module, with `S_{n−1} = \operatorname{Stab}(a)` and `V_0'` the sum-zero vectors on the other `n−1` letters:
> ### `Λ^2N = (e_a ∧ V_0') ⊕ Λ^2D'`,  `\dim(e_a∧V_0') = n−2`,  `\dim Λ^2D' = \binom{n−2}{2}`,
both irreducible and non-isomorphic **by Peel's theorem**, valid since `p ∤ n−1`.

> ### 📚 **PEEL (1971).** *The hook Specht modules `S^{(m−r,\,1^r)}` of `S_m` are irreducible in odd characteristic `p` if and only if `p ∤ m`.* — M.H. Peel, «Hook representations of the symmetric groups», *Glasgow Math. J.* **12** (1971) 136–149.
> ### **Here `m = n−1` and `Λ^2V_0' ≅ S^{(m−2,1,1)}`, `e_a∧V_0' ≅ V_0' ≅ S^{(m−1,1)}`; both are hooks, and `p ∤ m` holds because `3 \mid n`.**
> ### ⚠️ **The identification `Λ^r(\text{standard}) ≅ S^{(m−r,1^r)}` requires `p ∤ m`, which is exactly the situation created by the restriction. It is not claimed outside that range.**
> ## ⭐ **Note for later use: the hook family is indexed by `r`, so Peel covers `Λ^r` for EVERY `r`, not only `r = 2`. The stabiliser bar therefore transports to the families of larger support by the same theorem.** **Hence the `S_{n−1}`-submodules of `Λ^2N` are exactly `0`, `e_a∧V_0'`, `Λ^2D'`, `Λ^2N`.** *(Dimensions and directness checked at `n = 6, 12`.)*

## 6.3 · `THEOREM TRESK` *(`PROVED`, `3 \mid k`, `k ≥ 3`, all `q = 3^v ≥ 2k+1`)*

`K := \ker(z^3)` on the generator span is `S_{n−1}`-stable, hence is one of the four submodules above. The certificate for `F` excludes `Λ^2D'` and `Λ^2N`; the SAME `μ^\circ` certifies `G = s_{ab}−s_{ac_1} ∈ e_a∧V_0'`, which excludes `e_a∧V_0'`. Therefore `K = 0`, i.e.
> ### `\ker(z^3)\big|_{\operatorname{span}\{s_{ab}\}} = \operatorname{span}\{σ_a\}` **also for `3 \mid k`.** ∎

> # **THEOREM (FAMILY).** *For every `k ≥ 2` and every `q = 3^v ≥ 2k+1`, with NO condition on `k` mod `3`: the family "one zero" is CLOSED — the `\binom{2k}{2}` generators give exactly `2k−1` star blocks killed by `z^3`, and a `\binom{2k−1}{2}`-dimensional complement injected by `z^3`.*

---

# 6 · A SUPERSEDED PROOF, RECORDED

An earlier argument established the same conclusion over the narrower range `q ≥ 8k−9`, using the spaced tail `e_j = 4j`. There `A` and `B` had **different** exponent sets, so the cancellation of §3 was unavailable and the three signs had to be computed individually, via
> ### `\operatorname{coef}_{x^π}(g_0) = G·(−1)^{I(E)}·(−1)^{\operatorname{inv}(π)}`  (`I(E) = \#\{(u,v) ∈ E_{\rm even}×E_{\rm odd} : u<v\}`),
a rule pinned against `144/144`, `1872/1872` and `2880/2880` monomials in three cells, **with a global convention constant `G` fixed by machine.** The parities `(I+\operatorname{inv})` came out `(0,1,0)`, constant in `k`, giving `(σ_A,σ_B,σ_C) = (−G,+G,+G)`.

> ### **That argument is correct and was verified symbolically for `k = 2..8`. It is recorded because it is the reason the sign rule was pinned at all — but it is SUPERSEDED: the range `q ≥ 2k+3` contains `q ≥ 8k−9` for every `k ≥ 2`, and the proof of §3 needs no sign rule and no convention constant.**

> 🔴 **NOTA `2026-09-16` (Grepy, turno 19, informe 147) — «BANDA contiene / sustituye a SALTOS» es FALSO en `k = 2`:** `THEOREM BANDA` sólo vale `k ≥ 3` (`corpus/CHAISE_LONGUE_STANDALONE_ONE_ZERO_FAMILY_v4.md:82`) y `THEOREM FILO` también (`:111`). En `k = 2`, UNIÓN descansa en SALTOS, con la constante `G` fijada a máquina (`:175-177`). La desigualdad `2k+3 ≤ 8k−9` es cierta pero no basta. No toca la conjetura: `k = 2` está probado `∀q` por el Sofá.

> ## ⭐ **The removal of `G` is a gain in rigour, not merely in range: the theorem no longer depends on any convention fixed by computation.**

---

# 7 · GRADES

| statement | grade |
|---|---|
| `KEY LEMMA` and `σ_A+σ_B = 0` | **PROVED**, all `k ≥ 3`, all `q = 3^v ≥ 2k+3` |
| **THE THEOREM** (closure of the family) | **PROVED**, all `k ≥ 3` with `3 ∤ k`, all `q = 3^v ≥ 2k+3` |
| Consequences (i), (ii) | **PROVED**, same range |
| `THE INVOLUTION PRINCIPLE` (§0) | **PROVED**, general — one line |
| **THEOREM (EDGE)** and **THEOREM (UNION)** | ### **PROVED**, all `k ≥ 2`, all `q = 3^v ≥ 2k+1`. **No machine computation is used or needed.** |

> 🔴 **NOTA `2026-09-16` (Grepy, turno 19, informe 147) — «BANDA contiene / sustituye a SALTOS» es FALSO en `k = 2`:** `THEOREM BANDA` sólo vale `k ≥ 3` (`corpus/CHAISE_LONGUE_STANDALONE_ONE_ZERO_FAMILY_v4.md:82`) y `THEOREM FILO` también (`:111`). En `k = 2`, UNIÓN descansa en SALTOS, con la constante `G` fijada a máquina (`:175-177`). La desigualdad `2k+3 ≤ 8k−9` es cierta pero no basta. No toca la conjetura: `k = 2` está probado `∀q` por el Sofá.

| The superseded proof of §6 | **PROVED** over `q ≥ 8k−9`, with a machine-pinned convention |
| Machine census | `117` cells with `k ≤ 100`, all certified, `6` factorizations each; validated against the exact censuses of `(2,9)`, `(3,9)`, `(2,27)` |

| **`LEMMA SB`** | **PROVED**, all `k`, all `q` — *an instance of `§0`(i)* |
| **`THEOREM STAB`** | **PROVED**, `3 \mid n`, `n ≥ 6`; cites Peel for `p ∤ n−1` |
| **`THEOREM TRESK`** and **`THEOREM (FAMILY)`** | ### **PROVED. The family is closed with NO exception.** |

⚠️ **What remains outside this document:** the families of generators indexed by more than two letters, and the exact size of the star blocks (`z^2σ_a ≠ 0`) — **the latter is NOT needed for anything above, and is FALSE in general: `a^{q−2}e_{2k}(U)` is zero in `B` at `(3,3)`.**

Nothing is claimed in characteristic `2`, nor for even `q`.

---
*Standalone `ONE ZERO FAMILY v3` · Chaise Longue Campaign. Companion to `SXP-BOUND v1`, `STAR IDENTITY v1` and `TAU PAIRING v1`.*

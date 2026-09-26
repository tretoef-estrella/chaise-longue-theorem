> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-26
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *THE DEFECT-TOR LOCALIZATION THEOREM* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_DEFECT_TOR_LOCALIZATION_THEOREM.md
>
> **Status, as written in the document:** not stated in the document itself
>
> **Later audit:** The campaign's later records mention this document next to a refutation, retraction, circularity or supersession (1 lines). Search its name in [the Cemetery](../../archive/CHAISE_LONGUE_CEMENTERIO_LIVE_v502.md) before relying on it.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# THE DEFECT-TOR LOCALIZATION THEOREM
## Chaise Longue campaign — standalone deposit v1
**Author:** Orfila (auditor) · **Constructor cross-check:** Lacassagne (missions #21, #22, #24) · **Architect:** Rafa · 26 Jul 2026

---

## ABSTRACT

Let `K` be a field of characteristic `3`, `n = 2k+2`, `S = K[x_1,…,x_n]`, and let `{L_J}` be the
`(2k+1)!!` matching sheets with (radical) ideals `I_J`, `E = ⋂_J I_J`. For `q = 3^v` put
`m^{[q]} = (x_1^q,…,x_n^q)` and `B = S/m^{[q]}`.

Condition **(I)** of `GAP 3` asks whether the Frobenius power commutes with the intersection:

> **(I)**  `E + m^{[q]} = ⋂_J ( I_J + m^{[q]} )`.

We identify the obstruction exactly. Let

> `C := coker( S/E ↪ ⊕_J S/I_J )`

be the **global defect module** of the arrangement (the inclusion is injective precisely because
`E = ⋂_J I_J`).

> ### **THEOREM.** For every `k` and every `q`:
> ### `⋂_J(I_J+m^{[q]}) / (E+m^{[q]}) ≅ im( Tor_1^S(C,B) → S/(E+m^{[q]}) ) = coker( Tor_1^S(⊕_J S/I_J, B) → Tor_1^S(C,B) )`.
> ### Consequently **(I) holds ⟺ `Tor_1^S(⊕_J S/I_J, B) ↠ Tor_1^S(C, B)`.**
> ### Moreover, since `x_1^q,…,x_n^q` is a **regular sequence**, `Tor_i^S(M,B) = H_i(x_1^q,…,x_n^q ; M)`,
> ### the Koszul homology of the Frobenius power on `M`.

The identification is a two-line consequence of the long exact sequence; it is **not** a measured
pattern. It is gated `4/4` byte-exact on cells where (I) holds **and** on cells where it fails.

---

## 1 · PROOF

Since `E = ⋂_J I_J`, the natural map `S/E → ⊕_J S/I_J` is injective, giving the short exact sequence
of graded `S`-modules

> `0 → S/E → ⊕_J S/I_J → C → 0.`   (∗)

Apply `− ⊗_S B`. The long exact sequence of `Tor` gives

> `Tor_1(⊕_J S/I_J, B) → Tor_1(C,B) →^∂ (S/E)⊗B → ⊕_J (S/I_J)⊗B.`   (∗∗)

Now `(S/E) ⊗_S B = S/(E + m^{[q]})` and `(S/I_J) ⊗_S B = S/(I_J + m^{[q]})`, and the right-hand map
of (∗∗) is the natural reduction. Its kernel is, by definition,

> `ker = ⋂_J (I_J + m^{[q]}) / (E + m^{[q]})` — **the deficit of (I)**.

By exactness of (∗∗) that kernel equals `im(∂) = im(Tor_1(C,B))`, and again by exactness
`im(∂) ≅ Tor_1(C,B) / im(Tor_1(⊕_J S/I_J,B)) = coker(Tor_1(⊕_J S/I_J,B) → Tor_1(C,B))`.
Hence (I) — the vanishing of the deficit — holds iff that cokernel vanishes, i.e. iff the map is
surjective. ∎

**Koszul form.** `m^{[q]} = (x_1^q,…,x_n^q)` is a regular sequence in `S`, so the Koszul complex
`K_•(x_1^q,…,x_n^q)` is a free resolution of `B`. Therefore for every `S`-module `M`,
`Tor_i^S(M,B) = H_i(x_1^q,…,x_n^q ; M)`. Condition (I) becomes a statement about **surjectivity of
first Koszul homology of the Frobenius power**, from the sheet side onto the defect side. ∎

---

## 2 · VERIFICATION (gate declared before reading)

Engine `tor_identify.py`, exact linear algebra over `F_3`, `k = 2` (`n = 6`), `q = 3`. In the range
`q ≤ d < 2q` the term `K_2` contributes nothing in degree `d`, so
`H_1(M)_d = ker( (M_{d−q})^n → M_d )`, `(m_i) ↦ Σ_i x_i^q m_i`, computed directly.

**Gate declared before running:** the cokernel must equal the independently measured deficit in
**both** regimes — where (I) fails and where it holds.

| cell | deficit (direct) | `dim H_1(C)_d` | `dim im H_1(⊕_J S/I_J)_d` | cokernel | verdict |
|---|---|---|---|---|---|
| circle triple, `d = 3` | 2 | 10 | 8 | **2** | ✓ |
| circle triple, `d = 4` | 2 | 20 | 18 | **2** | ✓ |
| all 15 sheets, `d = 3` | 0 | 44 | 44 | **0** | ✓ |
| all 15 sheets, `d = 4` | 0 | 130 | 130 | **0** | ✓ |

The circle triple is `J₁ = {01,23,45}`, `J₂ = {02,14,35}`, `J₃ = {05,13,24}` (mission #22).
**4/4, no exceptions, both regimes.**

---

## 3 · WHAT THIS BUYS

1. **It explains the non-heredity**, which was the central mystery of `GAP 3`. Measured (`k=2`,
   `q=3`): `3,4,5` sheets break; `6,7` commute; `8,9` break; `10` commutes; `11` breaks; `12–15`
   commute. This is not paradoxical: `C` is built from the **whole** collection, so enlarging the
   collection changes `C` and hence `Tor_1(C,B)`. The obstruction was never local — no local
   criterion could have seen it. This upgrades the tomb `NERVE-EXACTNESS-IS-NOT-LOCAL` from an
   observation to a consequence.

2. **The left-hand side is already closed by a deposited theorem.**
   `Tor_1(S/I_J,B) = H_1(x^{[q]}; S/I_J)`, and on `L_J` the sequence `x^{[q]}` restricts to
   `(u_p^q, −u_p^q)_p` — exactly the object of `FROBENIUS_KOSZUL_RECOGNITION_v2` (PROVED for all
   `k`, `q`, `e`: each Frobenius layer is a Koszul syzygy). Only the right-hand side is unknown.

3. **A structural hypothesis, stated as such and NOT claimed.** `MCM_REDUCTION_THEOREM_v2` is built
   on `0 → Γ → O(X)^m → C → 0`, a sequence of the **same shape** as (∗). Whether the letter's
   defect module and the arrangement's global `C` are the same object is **NOT established here**;
   asserting it would be `SCOPE-SPLICING`. Settling it either way is the next mission.

---

## 4 · SCOPE — WHAT THIS THEOREM DOES *NOT* CLAIM

1. **It does not prove (I), and it does not close `GAP 3`.** It converts (I) into an equivalent
   surjectivity statement. `G` remains `4`.
2. It does not compute `Tor_1(C,B)` for any `k` beyond the gated cells, and gives no closed form.
3. It does not identify the arrangement's `C` with the letter's defect module `C(B_m)` (§3.3).
4. `H_1 = 0` is **not** available as a shortcut: `dim C ≤ k+1 < n−1`, so the Frobenius sequence can
   never be regular on `C` and `Tor_1(C,B) ≠ 0` in general. **Surjectivity, not vanishing, is the
   target** — the gated cells show `dim H_1(C) = 44` and `130` with deficit `0`.
5. Nothing here touches `GAP 2`, `GAP 4`, `GAP 5`, nor condition (II).

---

## 5 · PROVENANCE

- The reformulation of `GAP 3` as (I)+(II): Lacassagne, mission #20 (`ASSEMBLY_DRAFT` Thm 8.6).
- The breaking triple and the non-heredity measurements: Lacassagne, missions #21–#22.
- The stratum classification that closed the local route with data, and the refutation of the
  stratum-freeness inference: Lacassagne, mission #24 (`STRATUM_CLASSIFICATION_THEOREM_v1`).
- Theorem, proof, Koszul form, engine and gate: Orfila, this deposit.
- Route: the theorem was reached by asking *which module owns the deficit* instead of asking which
  subsets break — after two successive local routes (nerve, strata) were each killed with data.
  The dead ends are what forced the question into its correct, global form.

---

**Every statement carries its grade inline. `GAP 3` remains open and the magic word is not spoken.**

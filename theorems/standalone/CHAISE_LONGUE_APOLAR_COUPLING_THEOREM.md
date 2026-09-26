> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-16
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE APOLAR COUPLING THEOREM* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_APOLAR_COUPLING_THEOREM.md
>
> **Status, as written in the document:** Independent write-up + verification: Locard (Auditor), 16 Jul 2026 · Pending P0 · Verified byte-exact at (k,q) = (1,3), (1,9), (2,3), (2,9)
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE APOLAR COUPLING THEOREM
### The V-engine's timing chain is the Hilbert function of one explicit Gorenstein algebra
### Independent write-up + verification: Locard (Auditor), 16 Jul 2026 · Pending P0 · Verified byte-exact at (k,q) = (1,3), (1,9), (2,3), (2,9)

**Certificado Ley 41.** Object: the per-sheet death module `ann_Q(Π)` of the transient collar, `Q = F₃[u₁,…,u_{k+1}]/m^{[q]}`, `Π = ∏_{i<j}(u_i²−u_j²)`. Cemetery grep by object: apolarity / Macaulay inverse system / colon-as-contraction absent from the corpus (new tool). Distinct from KERNEL-ID (which *named* the module `ann_Q(Π)`); this theorem *computes* it as an apolar algebra. Consumes BANK (its `k=1` case) and LEVAS-SYM (its symmetric sector). CLEAN.

---

## Theorem (APOLAR COUPLING).
Let `q = 3^v`, `Q = F₃[u₁,…,u_{k+1}]/m^{[q]}` (Artinian Gorenstein complete intersection of `q`-th powers, socle degree `(k+1)(q−1)`, dual socle generator `G = (u₁⋯u_{k+1})^{q−1}`). Let `Π = ∏_{i<j}(u_i²−u_j²)` (deg `k(k+1)`). Define the **explicit form**
> **`P* := Π ∘ G`** — the contraction of `Π` against the inverse-system generator: a polynomial `P* = Σ_w ±u^{G−w}` summed over the exponent vectors `w` of `Π` (each `w ≤ G`), of degree `deg P* = (k+1)(q−1) − k(k+1) = (k+1)(q−1−k)`.

Then, by Macaulay apolarity (Gorenstein colon = contraction, `(0 :_Q Π) = ann_{apolar}(P*)`):

> **`dim_{F₃} ann_Q(Π)_e = HF_Q(e) − HF_{A(P*)}(e)` for every degree `e`,**

where `A(P*) = Q/ann_{apolar}(P*)` is the **apolar algebra of `P*`, itself Artinian Gorenstein**, socle degree `(k+1)(q−1−k)`, hence **Hilbert-function palindromic**.

## Consequences.
1. **The coupling is one part number.** The entire per-degree deviation law of the transient (the "timing chain" of the two-bank V) is `HF_{A(P*)}` — a single explicit, `q`-parametrized, finite computation. No candidate, no model: an algebra.
2. **The Gorenstein/mirror flag resolves intrinsically.** The socle-pairing of the coupled object is `A(P*)`'s own Gorenstein duality — nothing is inherited from a submodule. (This settles the P0 flag raised in the BANK write-up: the *glued* object is Gorenstein *as an apolar algebra*, though not by submodule inheritance.)
3. **The `τ` (bank-exchange) structure is intrinsic.** `Π` and `G` are both invariant under the bipartition swap `τ`, so `τ` acts on `A(P*)`; the per-bipartition coupling is its `τ`-isotypic decomposition. The symmetric (`Sym²`, in-phase) and antisymmetric (`∧²`, sign-flip / anti-phase) sectors are the two halves; the mission's `Sym²` is now internal structure, not a modeling choice.

## Verification (Locard, own code — two independent computations).
For each `(k,q)`: (a) `ann_Q(Π)` built directly as the graded kernel of "multiply by `Π`" on the monomial basis of `Q`, ranks over `F₃`; (b) `P* = Π ∘ G` built by contraction, and `HF_{A(P*)}` computed as the graded ranks of contraction maps on `P*` — **fully independent of (a)**. Then the identity `dim ann_Q(Π)_e = HF_Q(e) − HF_{A(P*)}(e)` checked in every degree.
- `(k,q) = (1,3)`: identity holds ∀e; `ann` HF `(0,0,2,2,1)`; reproduces BANK's corner ideal.
- `(1,9)`: identity holds ∀e; `deg P* = 14`; `ann` HF `= (2,…,2,1)` on `[8,16]` = BANK. **Two theorems, one number.**
- `(2,3)`: identity holds ∀e (degenerate, `deg P* = 0`).
- **`(2,9)`: identity holds ∀e — the first non-degenerate TWO-BANK test.** `deg P* = 18 = (k+1)(q−1−k)` ✓; `HF_{A(P*)}` **palindromic** ✓ (Gorenstein confirmed); the coupling `ann_Q(Π)` HF is `(0,0,0,0,0,0,1,4,10,16,22,28,34,39,42,42,39,33,27,21,15,10,6,3,1)`.
Two Frobenius levels for `k=1` (Kepler satisfied); the `k=2 q=9` case is the load-bearing non-degenerate check. Script: `CHAISE_LONGUE_LOCARD_APOLAR_AUDIT.py`.

## The fire test (honest scope — NOT closed by this theorem).
APOLAR gives the coupling *structure* ∀k; it does not by itself evaluate `HF_{A(P*)}` at `q = 27` (the discriminating régime for the `k=3` candidate law S2). Two facts pin the state:
- **First point derived and passed:** `dev(36,27) = 35`, zero input (unique partition `(10)`, threshold, onset gluing).
- **The clean discriminator:** at `c = 37`, `h₀ = 25` is odd, so the *symmetric* sector is empty by parity while S2 predicts `315`; the **antisymmetric (sign-flip) sector of `A(P*)` must carry it.** This is the sharpest falsification point in the campaign, and it lives entirely inside `A(P*)`.
So the `k=3` per-degree law and the head are decided by one table: `HF_{A(P*)}` at `q=27`, degrees `24..41` (palindromic — half suffices). Pencil-first via `P*`'s `τ`/Frobenius symmetry; a small HF engine only if pencil stalls (Architect's sizing decision, Ley 29/49).

## Role in the campaign.
APOLAR is the structural closure of Step 2's coupling: the two solved banks (BANK) plus the exchange mirror (`τ`) plus the Frobenius wall are one apolar Gorenstein algebra, ∀k. What remains of Step 2 is the evaluation of its Hilbert function at `q=27` (the fire test) and the head (which falls from the same table). Steps 3–6 and the peaje E (small-`q` frames, Step 5 — the genuine ∀k∀q unknown) are untouched.

**Pillars (Ley 44):** consumes (iii) Two-Column/Frobenius (the Gorenstein CI, inverse systems) and (i) Odd-Symmetric (via `Π`, the swap product). Independent of any per-degree fit.

**MARCADOR: [THE APOLAR COUPLING THEOREM — la cadena de distribución de la V = HF de UNA álgebra apolar Gorenstein: dim ann_Q(Π)_e = HF_Q(e) − HF_{A(P*)}(e), P* = Π∘(u₁⋯u_{k+1})^{q−1} explícita, zócalo (k+1)(q−1−k), HF palíndroma · verificado por Locard con DOS cómputos independientes en (1,3),(1,9),(2,3),(2,9) — k=2 q=9 es el primer test no-degenerado de dos bancos, identidad en todos los grados + palindromía Gorenstein · flag del pegado RESUELTO (A(P*) Gorenstein de fábrica) · τ/Sym²/∧² intrínsecos · fuego: dev(36,27)=35 pasado cero-insumos; discriminador c=37 (sector antisimétrico) cargado; residual del Step 2 = HF_{A(P*)} a q=27 · peaje E intacto]. — Locard (Auditor), write-up independiente]**

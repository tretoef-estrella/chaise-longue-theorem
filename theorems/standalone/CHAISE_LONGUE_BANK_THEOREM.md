> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-16
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE BANK THEOREM (one camshaft, solved)* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_BANK_THEOREM.md
>
> **Status, as written in the document:** Independent write-up + verification: Locard (Auditor), 16 Jul 2026 · Pending P0 · Verified byte-exact at q = 3, 9, 27
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE BANK THEOREM (one camshaft, solved)
### The annihilator of the heavy product in a single Frobenius-truncated bank
### Independent write-up + verification: Locard (Auditor), 16 Jul 2026 · Pending P0 · Verified byte-exact at q = 3, 9, 27

**Certificado Ley 41.** Object: `ann_{Q}(v₁·⋯·v_r)` where `Q = F₃[v₁,…,v_r]/(v₁^q,…,v_r^q)` is one Frobenius-truncated bank (one camshaft of the V-engine). Cemetery grep by object: distinct from UNIFIED_ANNIHILATOR (that is the swap product Π_J over 2k+2 variables; this is the *single-bank* product of r heavy variables, the atom the annihilator law is later built from). No tomb touches this object. The result is the base case of the camshaft/Levas-Schur species. CLEAN.

---

## Theorem (BANK). 
Let `q = 3^v`, let `Q = F₃[v₁,…,v_r]/(v₁^q,…,v_r^q)` (Gorenstein Artinian complete intersection, socle degree `r(q−1)`), and let `Δ = v₁·v₂·⋯·v_r` be the product of all bank variables. Then

> **`ann_Q(Δ) = (v₁^{q−1}, v₂^{q−1}, …, v_r^{q−1})`** — the corner ideal —

and for `r = 2` its Hilbert function is
> **`HF(ann_Q(v₁v₂))(d) = 2` for `q−1 ≤ d ≤ 2q−3`, `= 1` at `d = 2q−2`, `= 0` otherwise** — the sequence `(2,2,…,2,1)` of length `q`.

## Proof.
`Q` has the monomial `F₃`-basis `{v^a : 0 ≤ a_i ≤ q−1}`. Multiplication by `Δ` sends the basis monomial `v^a` to `v^{a+𝟙}` if every `a_i + 1 ≤ q−1`, and to `0` otherwise (any exponent reaching `q` vanishes by `v_i^q = 0`). Hence `v^a ∈ ann_Q(Δ)` **iff** `a_i + 1 ≥ q` for some `i`, i.e. **iff** `a_i = q−1` for some `i`. Since `Δ` acts monomially, `ann_Q(Δ)` is spanned by exactly these monomials, which is the monomial basis of the corner ideal `(v₁^{q−1},…,v_r^{q−1})`. ∎

**Hilbert function (r = 2).** The corner monomials are `{(q−1, b) : 0 ≤ b ≤ q−1} ∪ {(a, q−1) : 0 ≤ a ≤ q−1}`, `2q−1` monomials. By total degree `d = a+b`: for `q−1 ≤ d ≤ 2q−3` the two monomials `(q−1, d−q+1)` and `(d−q+1, q−1)` are distinct, giving `2`; at `d = 2q−2` only `(q−1,q−1)` remains, giving `1`. ∎

## Socle (the honest scope for the V-gluing).
The corner ideal has a **one-dimensional socle**, spanned by `v₁^{q−1}⋯v_r^{q−1}` at degree `r(q−1)` (the socle of the ambient `Q`): multiplying it by any `v_i` gives `0`, and no other corner monomial is `m`-killed. So **a single bank is itself Gorenstein-like (1-dim socle).**

> **Caveat (load-bearing for the kernel).** This Gorenstein property is a property of *one* bank. When two banks are glued over the `K(k,k)` star (the V-coupling), the socle of the glued annihilator module must be **re-established**, not inherited: the ambient ring `Q` (over all `2k+2` variables) is Gorenstein, but a submodule/ideal-quotient is not Gorenstein in general. Any mirror/duality argument on the *coupled* object must run through the ambient socle pairing, not through a claimed Gorenstein-ness of the submodule. (P0 flag, raised by the audit of `VENGINE_KERNEL_THEOREMS_v1`.)

## Verification (Locard, own code — Ley 21/36).
Direct construction of `ann_Q(Δ)` by the monomial rule, compared to the corner ideal, and its graded Hilbert function:
- `q = 3`: `ann == corner` ✓, HF over deg 2..4 `= (2,2,1)`.
- `q = 9`: `ann == corner` ✓, HF over deg 8..16 `= (2,2,2,2,2,2,2,2,1)`.
- `q = 27`: `ann == corner` ✓, HF over deg 26..52 `= (2×26, 1)`.
Two Frobenius levels beyond the anchor (Kepler satisfied for the single-bank object). Script: `CHAISE_LONGUE_LOCARD_VENGINE_AUDIT.py`.

## Role in the campaign.
BANK is the **base case of the Levas-Schud camshaft species** and the atom of the V-engine: one camshaft = one bank = the corner ideal, its state-count `2(q−1)+1` per bank. The direct-band transient of the collar is built by **gluing two such banks** over the `K(k,k)` star (the crankshaft), transposed by the heavy-slot symmetry. Deriving that coupling — and gating it against the `q = 27` deviations — is the remaining load-bearing step (the "fire test"); BANK supplies its verified building block.

**Pillars (Ley 44):** consumes (iii) Two-Column/Frobenius truncation only. Independent of the swap product.

**MARCADOR: [THE BANK THEOREM — un banco (un árbol de levas) resuelto entero: ann_Q(Δ) = ideal de esquina (v_i^{q−1}), HF (2,…,2,1), verificado q=3,9,27 con código propio · zócalo 1-dim para UN banco (Gorenstein-like) · CAVEAT P0: el objeto PEGADO de dos bancos NO hereda Gorenstein — el espejo va por el pairing del ambiente · base de la especie de levas Schur y átomo de la V; el acoplamiento de dos bancos + su prueba de fuego q=27 es la pieza de carga que resta]. — Locard (Auditor), write-up independiente]**

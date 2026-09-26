> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-16
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE EQUIVARIANT MIRROR THEOREM* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_MIRROR_THEOREM.md
>
> **Status, as written in the document:** Independent write-up + verification: Locard (Auditor), 16 Jul 2026 · Pending P0 · Parity calibration and mutual gate verified byte-exact
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE EQUIVARIANT MIRROR THEOREM
### The Architect's "stop before the reverse spin" made exact: the coupling algebra's Gorenstein pairing is sign-equivariant
### Independent write-up + verification: Locard (Auditor), 16 Jul 2026 · Pending P0 · Parity calibration and mutual gate verified byte-exact

**Certificado Ley 41.** Object: the `S_{k+1}`-equivariant structure of the Gorenstein pairing on `A(P*)` (the apolar coupling algebra of APOLAR). Origin: the Architect's motor intuition — "the two camshafts, on swap, spin the reverse way, with a stop before the reversal." Cemetery grep: sign-equivariant Gorenstein duality / isotypic mirror absent from corpus (new). Consumes APOLAR (`A(P*)`, socle `s`). CLEAN.

---

## Theorem (EQUIVARIANT MIRROR).
Let `A = A(P*)` be the apolar coupling algebra (APOLAR), `s = (k+1)(q−1−k)` its socle degree, `G = (u₁⋯u_{k+1})^{q−1}` the socle generator, and let `S_{k+1}` act by permuting the sheet coordinates (`m^{[q]}` is permutation-invariant by Frobenius linearity).

Then:
1. **`σ·Π = sgn(σ)·Π` and `σ·P* = sgn(σ)·P*`** for every `σ ∈ S_{k+1}` — because `Π = ∏_{i<j}(u_i²−u_j²)` is the Vandermonde in the squares (alternating), and `G` is symmetric, so the contraction `P* = Π ∘ G` inherits the sign character.
2. **The Gorenstein pairing `⟨a,b⟩ := (coefficient of the top form P* in a·b)` is sign-equivariant:** `⟨σa, σb⟩ = sgn(σ)·⟨a,b⟩`.
3. **Hence, for every irreducible character `χ` of `S_{k+1}`,**
> **`HF_χ(A, e) = HF_{χ⊗sgn}(A, s − e)`** — each isotypic sector mirrors, at the complementary degree, into its **sign-twist**.

## Corollaries.
- **(i) Total palindromy.** Summing over `χ`: `HF_A(e) = HF_A(s−e)` — the Gorenstein palindrome (matches Locard's measured `k=2, q=9` table).
- **(ii) The Architect's mirror.** For an **odd** involution `τ` (a swap of the two *arms* of one camshaft), the `τ`-antisymmetric sector is the mirror of the `τ`-symmetric one: **`HF_{anti}(e) = HF_{sym}(s−e)`**. With palindromy this gives the measured shift `HF_{anti}(e) = HF_{sym}(e−1)`.
- **(iii) Self-dual modes.** Irreducibles with `χ ≅ χ⊗sgn` (at `k=3`: the 2-dimensional `[2,2]`) are self-palindromic.

## The atomic sign calibration (the nuance that makes it round).
There are **two distinct swaps** in the engine, of **opposite parity** — this is the sharp content:
- **Bank swap** `(u₁u₃)(u₂u₄)` (exchange the two whole camshafts): a product of two transpositions, **EVEN**. `P*` is bank-swap **symmetric** — the V's exchange `τ_bank` lives in the trivial-sign class, consistent with the `Sym²` coupling. *The V is serene: swapping the two trees changes nothing.*
- **Arm swap** `(u₁u₂)` (exchange the two arms `v₁,v₂` of one camshaft): a single transposition, **ODD**. This is the **true mirror** — the sign flip lives **inside one camshaft**, between its two arms, not between the two trees.

So the Architect's "reverse spin" is the **arm** involution, and the "stop before the reversal" is the crossover the mirror forces: **pure-symmetric at the floor** (`e=0`: `sym=1, anti=0`), **pure-antisymmetric at the ceiling** (`e=s`: `sym=0, anti=1`), the character sliding from one to the other as degree climbs.

## Verification (Locard, own code).
- **Parity calibration**, `k=3, q=9` (non-degenerate, `P*` has 24 terms): bank swap `(u₁u₃)(u₂u₄)` → `P*` EVEN ✓; arm swap `(u₁u₂)` → `P*` ODD ✓. (Matches `S₄` parities: `sgn(bank)=+1`, `sgn(arm)=−1`.)
- **Mutual gate** (reciprocal cross-check of the mirror against the earlier measurement): on the `k=2, q=9` split, `HF_{sym}(s−e) = HF_{sym}(e−1)` holds in **every** degree ✓ — the mirror and the measured shift are mutually consistent (either being wrong would break this).
- **Total palindromy** of `HF_A` verified at `k=2, q=9` (APOLAR audit).
Scripts: `CHAISE_LONGUE_LOCARD_MIRROR_THEOREM_AUDIT.py`, `CHAISE_LONGUE_LOCARD_APOLAR_AUDIT.py`.

## Scope and honest limit.
The mirror is `∀k∀q` structural (representation theory of the Gorenstein pairing; the only characteristic-sensitive point is the invertibility of `2` for the involution/Schur step, which holds in `F₃`). **It relates the antisymmetric sector to the symmetric one — it does not by itself compute either.** Closing the fire test still requires the symmetric sector's full isotypic content (the LEVAS-SYM completeness gap, an open P0 item) **and** the per-sheet→global gluing (the transient deviation `dev(c)` is a glued quantity; the per-sheet apolar HF, though `q`-invariant at low depth — measured `12,28,56` at both `q=9` and `q=27` — is not `dev` itself). The mirror is the reflection law of the motor, not the census of its parts.

## Role in the campaign.
Rafa's intuition, made a theorem: the two spin directions (symmetric / antisymmetric under an arm swap) are one palindrome read forwards and backwards, offset by one tooth (the degree-1 alternating factor). It halves the coupling table (only one sign-sector per complementary-degree pair is independent) and pins that the discriminator `c=37` (symmetric-empty by parity) is carried by the antisymmetric sector = the mirror of a symmetric degree. It is the reflection law that any closed-form `HF_A` must obey.

**Pillars (Ley 44):** consumes (iii) Two-Column/Frobenius (Gorenstein pairing) and (i) Odd-Symmetric (Π alternating). 

**MARCADOR: [THE EQUIVARIANT MIRROR THEOREM — el 'stop antes del giro inverso' del Architect hecho teorema: el pairing Gorenstein de A(P*) es sgn-equivariante ⟹ HF_χ(e) = HF_{χ⊗sgn}(s−e) ∀irreducible, ∀k∀q · calibración atómica VERIFICADA: swap de BANCOS PAR (P* banco-simétrica, la V serena), swap de BRAZOS IMPAR (el espejo verdadero, dentro de la leva) · corolarios: palindromía total, anti(e)=sym(s−e) para involución impar, [2,2] auto-dual · gate mutuo sym(s−e)=sym(e−1) PASADO (cross-check recíproco) · límite honesto: refleja un sector en otro, no los computa; el fuego necesita además la completitud de LEVAS-SYM y el pegado por-hoja→global (por-hoja q-invariante 12,28,56 medido ≠ dev global)]. — Locard (Auditor), write-up independiente; la idea es del Architect]**

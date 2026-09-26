> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Hodge–Fermat campaign* · 2026-06-06
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *THE LÉGOLAS THEOREM — v2: ONE FORMULA, ALL DEGREES* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/THE_LEGOLAS_THEOREM.md
>
> **Status, as written in the document:** not stated in the document itself
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v2`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# THE LÉGOLAS THEOREM — v2: ONE FORMULA, ALL DEGREES
### The Möbius spectrum of the Fermat fourfold rank, unified · 6 June 2026
### Rafael Amichis Luengo (Architect) · with the Constructor and the Auditor
### Supersedes v1 (whose hexad formulation is the odd-d, K≥3 specialization); v1 flags resolved here except the Nonvanishing citation (Auditor literature pass)

## 0. THE UNIFIED STATEMENT

For a subset S of the 15 plane families of the Fermat fourfold of degree d, let G_S be the
union graph of its matchings on the six coordinates, with components classified bipartite /
non-bipartite. Define
> **N_d(G) = ∏ over components: (d−1) if the component is bipartite; ε_d if not,**
> where ε_d = 1 for d even (the impostor's forced voice d/2) and 0 for d odd.

**Theorem.** ν(S) = (−1)^{|S|+1} · ( 1 + N_d(G_S) ) — for EVERY nonempty S, EVERY degree d ≥ 3,
prime or composite, odd or even. Telescoping over all 2¹⁵ subsets:
> rank V(4,d) = 15d³ − 90d² + 175d − 99 + δ·(15d − 39) = **DS₄(d) + 1**, δ = (d−1) mod 2,
both parity branches obtained SYMBOLICALLY from the formula (sympy identity in session record).

Everything earlier is a corollary: the flat law is K=1 (three disjoint edges: b=3 → (d−1)³);
the pair forms are K=2 (skew = one 6-cycle: d−1; pencil = edge + 4-cycle: (d−1)²); the
quantization ±1/±d at odd d is "N is 0 or d−1"; the hexads are exactly the K≥3 alliances with
connected bipartite footprint; resonance IS bipartiteness.

## 1. PROOF (support calculus, now in one line per leg)
(a) **Master formula:** rank V(S) = 1 + |∪_{F∈S} supp(F)| — the span of a family is
⟨h⟩ ⊕ span{v_a : a_x ≡ −a_y on every edge} (torus averaging + eigenbasis + Nonvanishing Lemma).
(b) **Möbius duality:** the Möbius transform of |∪| is (−1)^{|S|+1}|∩|, and of the constant 1
is (−1)^{|S|+1} — hence ν(S) = (−1)^{|S|+1}(1 + |∩ supp|).
(c) **Counting the common support:** a ∈ ∩supp ⟺ a alternates (x ↦ −x) along every edge of
G_S ⟺ per component, a is a 2-colouring value ±r: bipartite component → r ∈ Z/d∖{0}, d−1
choices; non-bipartite component → an odd walk forces 2r ≡ 0, so r = d/2, which exists (and is
a nonzero coordinate, and is Hodge) iff d is even. Multiply over components: N_d(G_S). ∎
(The Σa ≡ 0 condition is automatic: matched pairs cancel. Hodge condition: each value pair
(x, −x) contributes fractional sum 1 at every unit; three pairs give 3 — always Hodge.)

## 2. THE IMPOSTOR'S AUDITED DEBT — 15d − 39, céntimo a céntimo
The even-degree surcharge of DS is exactly Σ over S with ≥1 non-bipartite component of
(−1)^{|S|+1}(d−1)^{b(S)} — computed over the 156-type census:
- **The only d-scaling line: the 15 pencil triples** (shared-edge room, bipartite, pays d−1;
  plus a K₄ casino where only the impostor sings): **15(d−1)**.
- **The pure casinos** (b = 0, alliances whose footprint is entirely non-bipartite, K = 3..15):
  alternating ledger 240 − 1215 + 2943 − 4995 + 6435 − 6435 + 5005 − 3003 + 1365 − 455 + 105
  − 15 + 1 = **−24**.
- Total: 15(d−1) − 24 = **15d − 39 = DS's even surcharge, identically.** The impostor's debts:
  fifteen pencil parties at (d−1) a glass, minus the casinos' net balance of 24.

## 3. EVIDENCE LEDGER (every claim with its kingdoms)
- **Pointwise, complete ladders (all 156 types each): d = 3, 4, 5, 6** — every single ν equals
  the formula; measured telescopes 21, 142, 401, 1002 = DS₄+1 at all four. (d=4, d=6 measured
  THIS session, AFTER the formula was written — the even branch and the composite kingdom are
  blind-class confirmations; d=6 extends the theorem beyond prime degrees with data.)
- d = 7: all types K ≤ 5, 24/24 blind. d = 11: K ≤ 3 spot trial, 4/4 blind to the digit.
- The even-d corollary's first prediction (generic triple ν = +2) hit blind at d=4 before the
  general formula existed — independently reproduced by the Auditor.
- Symbolic: both telescope branches = DS₄(d)+1 as polynomial identities.

## 4. HONEST LEDGER
Proven modulo: (1) the Nonvanishing Lemma (classical Shioda-type; empirically enforced by
every measured dimension across six kingdoms; exact citation = Auditor's literature pass);
(2) the standard eigenbasis description of Fermat middle cohomology and the plane classes'
torus equivariance (textbook). The floors/discriminant profiles remain OUTSIDE — the next
theorem. The d=4 and d=6 ladder data enters the acta with this document. PMC.

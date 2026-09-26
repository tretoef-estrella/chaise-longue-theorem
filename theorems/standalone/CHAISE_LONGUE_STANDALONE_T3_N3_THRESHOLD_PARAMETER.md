> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-14
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *THE THRESHOLD BOUND AND THE PARAMETER LEMMA* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_STANDALONE_T3_N3_THRESHOLD_PARAMETER.md
>
> **Status, as written in the document:** Status and role. This closes, at theorem grade and uniformly in `k`, the boundedness half of the threshold question. The SHARP value is a separate matter: the filed data give `e₀(2) = 4` and `e₀(3) = 9` (the latter confirmed at four consecutive out-of-sample p…
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v0`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# THE THRESHOLD BOUND AND THE PARAMETER LEMMA
## `e₀(k) ≤ (2k+1)!!` for every dimension (the uniform census threshold, closed); and the parameter machinery at the deepest flat, with the falsified depth route on record

**Chaise Longue campaign — standalone theorem write-up (referee edition)** · R. Amichis Luengo · Claude (Anthropic) · 14 July 2026
*Source: campaign Tanda 1 (T3), Tanda 5 (N3), Tanda 6 (the autopsy), audited in snapshot v97 and CARDANO_TANDA5/6. Two short results that fence the census threshold and the deepest-flat question with complete precision — including one falsification whose documentation is itself load-bearing (it prevents the community from walking a dead street that looks open).*

---

## Part I — Theorem T3 (the uniform threshold bound)

> **Theorem T3.** For every `k`, the window census `σ_e(k)` agrees with its Hilbert polynomial for all `e > (2k+1)!!`; that is, the census threshold satisfies **`e₀(k) ≤ reg(M(k)) ≤ (2k+1)!!`**.
*Proof.* Two campaign theorems compose: Slap 1 exhibits `σ_e(k)` as the Hilbert function of a finitely generated graded module `M(k)`, hence polynomial for `e > reg(M(k))`; Slap 2 bounds `reg(M(k)) ≤ (2k+1)!!`. ∎
**Status and role.** This closes, at theorem grade and uniformly in `k`, the boundedness half of the threshold question. The SHARP value is a separate matter: the filed data give `e₀(2) = 4` and `e₀(3) = 9` (the latter confirmed at four consecutive out-of-sample points through `σ₁₂ = 14238`), matching the candidate `e₀(k) = k²` — which reduces, through the theorem-grade degree bookkeeping of the zone assembly (denominator `(1−t)^{k+1}`; pair-attachment preserves numerator degree; Leibniz adds letter degrees; the dominant word is the full zero letter `Z_{k+1}`), to the Sharp Regularity Law's `Z`-branch (`deg N_G(Z_m) = m(m−1)`). Under Ley 48 the sharp value stands as a two-dimension candidate with its reduction written; the BOUND above is what the Ledger consumes, and it suffices (Tanda 7, by construction).
**A candidate killed by the engine (on record).** An earlier plan candidate `e₀(k) = k+1` was falsified by data before entering any assembly (`Δ³σ` at `k = 3` non-constant through `e = 8`); its tombstone documents that the pre-stable head LENGTHENS with `k` — consistent with the Swap-Ramp scale `k(k+1)`, inconsistent with any linear candidate.

## Part II — Theorem N3 (the parameter lemma) and the autopsy

Setting: the defect complex of a letter, `E = ker(ob)/im(φ)` supported on the deepest flat `D` (the Künneth/induction standalone), `Gauge_J = O(V_J)^m`, `Q_g := (⊕_J Gauge_J)/Γ`.

> **Theorem N3.** (a) **Kernel identification:** gauge tuples pairwise compatible on the codim-1 flats are restrictions of global census elements: `ker(d⁰) = Γ` — the Gluing Theorem plus the containment lemma, applied componentwise. (b) **Parameter lemma:** for `f ∈ ker(ob)` and any `u ∈ I_D^N` (with `N` such that `I_D^N·E = 0`, which exists by the support statement), the flat-discrepancy cocycle satisfies `u·δ = d⁰(h_u)` EXPLICITLY: take `λ′` with `φ(λ′) = u·f` and set `h_u^J := u·μ^J − λ′|_{V_J}` for any per-sheet solutions `μ^J`. (c) **Sufficient criterion:** if `x^N, y^N` (generic in `I_D`) form a regular sequence on `Q_g`, then every such `δ` is a coboundary and `E = 0` for that letter (`m ≥ 3`; `m = 2` is closed exactly by the Local Splitting identifications).
*Proof of (c) given (a),(b).* `y^N h_{x^N} − x^N h_{y^N} ∈ ker(d⁰) = Γ` by (a); the regular-sequence hypothesis lets one correct `h_{x^N} = x^N g + γ`, `γ ∈ Γ`; then `x^N(δ − d⁰g) = 0`, and the flat coefficient modules `O(F)^{m−1}` are torsion-free for a generic `x` (which does not vanish on any flat `F ⊋ D`), forcing `δ = d⁰ g`. ∎

> **The autopsy (Ley 24/42 — the falsification, with its numbers).** The hypothesis of (c) is **FALSE**: the exact criterion `Γ ∩ (x·G + y·G) = xΓ + yΓ` was gated numerically BEFORE any proof was drafted and fails — `B₃`: `15 ≠ 11` (e = 2), `46 ≠ 40`, `95 ≠ 87`; `Z₃`: `70 ≠ 62` (e = 4). Hence **`depth Q_g = 1` exactly**: the lower bound `≥ 1` is theorem (the exact sequence `0 → Γ → ⊕Gauge → ⊕_F O(F)^{2m}` of (a) embeds `Q_g` in flat modules, so `Ass(Q_g) ⊆` flat primes and generic `x ∈ I_D` is regular); the upper bound is the gate. Cemetery: DEPTH-QG-ROUTE.
> **The forensic reading.** The discrepancy grows linearly (`+2` per degree at `B₃`) — a module supported exactly on `D`: the Koszul obstruction of `Q_g` lives precisely where `E` lives, yet `E ≡ 0` in every measurement — the actual cocycle classes AVOID the bad part of `Q_g`. The correct residual statement is therefore strictly finer than any depth condition: **(Lemma Ω)** the parameter classes of vanishing-obstruction cocycles lie in `xΓ + yΓ` — equivalently, the composite `E → H¹_{Koszul}(x,y; Q_g)` vanishes. Ω is exactly `E = 0` in the parameter machinery's coordinates, verified wherever computable, and — by the Ledger Experiment — NOT load-bearing for the Chaise Longue.

### Attack surface
(A) T3's composition (Slap 1's module presentation and Slap 2's regularity bound — the two citations to re-walk; nothing else enters). (B) N3(a)'s componentwise application of the Gluing Theorem (the gauge tuples ARE variable tuples pair-constant per sheet — check the identification both ways). (C) N3(b)'s explicit coboundary (a two-line computation; verify the degree bookkeeping of `h_u`). (D) The gate of the autopsy (rerun `B₃, e = 2`: build `Γ`, multiply, intersect, compare `15` with `11` — one afternoon of exact linear algebra, and the single most instructive computation in this circle of questions). (E) Ω's formulation (does the linear-growth support claim hold sharply? multiply discrepancy classes by a third `z ∈ I_D`).

**Anchors.** TANDA1 (T3) · TANDA5_GLUING_THEOREM_v1 (N3) · TANDA6_DEPTH_AUTOPSY_v1 (the gate, the killing numbers, P1) · SLAP1, SLAP2 (the two inputs of T3) · TANDA7 (non-load-bearing verdict) · CARDANO_TANDA5/6 audits · session logs. github.com/tretoef-estrella.

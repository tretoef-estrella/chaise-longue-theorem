> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-08-11
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE SELF-LINKAGE & DUALITY THEOREMS (M2, SL, ω, and the h-dictionary)* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_SELF_LINKAGE_DUALITY_THEOREM.md
>
> **Status, as written in the document:** Status: M2, SL (two proofs), ω-identification with exact twist: PROVED ∀k.
>
> **Later audit:** The campaign's later records mention this document next to a refutation, retraction, circularity or supersession (1 lines). Search its name in [the Cemetery](../../archive/CHAISE_LONGUE_CEMENTERIO_LIVE_v502.md) before relying on it.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE SELF-LINKAGE & DUALITY THEOREMS (M2, SL, ω, and the h-dictionary)
### 11 Aug 2026 · Constructor: FRESCALES14 · Serves: GAP 5 (mission v37, T1 Links 1–4)
### Inputs: GRADED_PINNING v1 (Theorems S, NZD, SYZ, GP), RESOLVENT_EXCESS v1 (V, R), Nash's 52/52.
### Status: M2, SL (two proofs), ω-identification with exact twist: PROVED ∀k.
### The h-dictionary: PROVED given CM of the arrangement ring; numerically exact at k = 2, 3
### with two blind pre-registered cells (570, 810) hit. CM (Link 3): OPEN, named.

**Setting.** `I := I(W₂)` (radical, by Theorem S = `√J`), `J = (f₃,…,f_{2k−1}, ū_k)` a CI ∀k
(Theorem S), `K := I/J`, `a := Σdeg − 2k = k²−1`, `g_α = (x_α+e₁)P̂(x_α)`.

---

## Theorem M2 (multiplicity two, ∀k — W15's measured law becomes a one-line theorem)

> Every component of `W₂` has multiplicity exactly 2 in `V(J)`.

*Proof.* `J` is a CI (Theorem S), so `deg(S/J) = 3·5⋯(2k−1)·2k = 2k·(2k−1)!!`, while
`#components = k(2k−1)·(2k−3)!! = k·(2k−1)!!` — ratio exactly 2. Components are linear
(degree 1) and exhaust `V(J)` (Theorem S), so the multiplicities sum to `2·#C`. `S_{2k}`
permutes the components transitively and fixes `J`, so all multiplicities are equal: each
is 2. ∎ (Bonus: `X = ∅` ∀k re-proved with zero Jacobians.)

## Theorem SL (self-linkage, ∀k) — Link 1, BANKED

> **(a)** `I(W₂)² ⊆ J`.  **(b)** `J : I(W₂) = I(W₂)` — `W₂` is self-linked via its CI.

*Proof (localization — stronger than the charted route: no generation needed).* `S/J` is CM
(Theorem S), hence unmixed: `Ass(S/J)` = the components' generic points `p_C`. By M2, the
local ring `A := (S/J)_{p_C}` is Artinian of length 2 over its residue field, so `m_A² = 0`
and (since `I` is the radical) `(I/J)_{p_C} = m_A`. **(a)** Membership in the primary
component at `p_C` is checked locally, and `(I²)_{p_C} ⊆ m_A² = 0 = J_{p_C}` there; running
over all components, `I² ⊆ ⋂ Q_C = J`. **(b)** `⊇` is (a). For `⊆`: `hI ⊆ J` localizes to
`h̄·m_A = 0`, and `ann_A(m_A) = m_A` (length 2), so `h̄ ∈ m_A`, i.e. `h ∈ I(C)_{p_C}`, i.e.
`h` vanishes on `C`; over all components, `h ∈ I`. ∎

## Theorem SL-explicit (the Bézoutian products, ∀k) — the constructive half, gated 31/31

> `g_α·g_β ∈ J_{4k−2}` for **all** α, β.

*Proof.* For `α = β`: `g_α² = [(x_α+e₁)²P̂(x_α)]·P̂(x_α) ∈ J` by Theorem SYZ. For `α ≠ β`:
let `χ(λ) = ∏_γ(λ+x_γ)` and `N(λ,μ) := χ(λ)P̂(μ) − χ(μ)P̂(λ)`, antisymmetric, hence
`N = (λ−μ)·B(λ,μ)` exactly in `S[λ,μ]`. Reducing N by Theorem V's factorization:
`N ≡ P̂(λ)P̂(μ)·[(λ−e₁)²−(μ−e₁)²] = (λ−μ)·P̂(λ)P̂(μ)(λ+μ+e₁) (mod J[λ,μ])` (char 3:
`−2e₁ = e₁`). Since `λ−μ` is monic in λ, it is a nonzerodivisor on `(S/J)[λ,μ]`, so
`B(λ,μ) ≡ P̂(λ)P̂(μ)(λ+μ+e₁) (mod J[λ,μ])`. Evaluate at `(λ,μ) = (−x_α,−x_β)`: from
`(λ−μ)B = N` and `χ(−x_γ) = 0`, `(x_β−x_α)·B(−x_α,−x_β) = 0` in the domain S, so
`B(−x_α,−x_β) = 0`; the congruence then gives (P̂ even):
> **SL0:** `(e₁ − s)·Q ∈ J`, where `s := x_α+x_β`, `Q := P̂(x_α)P̂(x_β)`.
Now close: SYZ (×P̂ of the other variable) gives `(x_α+e₁)²Q, (x_β+e₁)²Q ∈ J`; their sum is
`(x_α²+x_β² − e₁s − e₁²)Q = (s² + p − e₁s − e₁²)Q ∈ J` with `p := x_αx_β` (char 3:
`x_α²+x_β² = s²+p`). Adding `s·SL0 = (e₁s − s²)Q ∈ J` yields `(p − e₁²)Q ∈ J`; and
`−e₁·SL0 = (e₁s − e₁²)Q ∈ J`. Finally
`g_αg_β = (p + e₁s + e₁²)Q = (p−e₁²)Q + (e₁s−e₁²)Q ∈ J` (char 3: `−2e₁² = e₁²`). ∎
*(Gates: 10/10 at k=2, 21/21 at k=3, corrupted-product controls fire; Nash's 52/52
independently reproduced via his own T-gate, CTRL-OK at every degree. k=4's degree-14
echelon is out of sandbox reach — stated; the pencil covers all k.)*

## Theorem ω (the duality identification with exact twist, ∀k) — Link 2, BANKED

> ## `K ≅ ω_{S/I(W₂)}·(−(k²−1))` — the nilpotent-kernel IS the canonical module of the
> ## reduced arrangement ring, twisted by exactly `k²−1`.

*Proof.* `Hom_{S/J}(S/I, S/J) = (J:I)/J = I/J = K` by Theorem SL(b). For the CI,
`ω_{S/J} ≅ (S/J)(k²−1)` (Koszul duality: twist `Σdeg − 2k`). `S/I` is unmixed of the same
dimension, so its canonical module is `ω_{S/I} = Hom_{S/J}(S/I, ω_{S/J}) = K(k²−1)`. ∎
**Twist gates (each degree could fail):** `K_d = HF(ω)_{d−3}` at k=2 for d = 3..6
(3, 8, 14, 20 both sides) and `K_d = HF(ω)_{d−8}` at k=3 for d = 5..8 (5, 24, 69, 149
both sides): PASS 8/8, with `HF(ω)` computed from the reversed h-vector.

## The h-dictionary (Link 4's exact target; PROVED given CM of `S/I(W₂)`)

Write `HF_red(W₂)(t) = h(t)/(1−t)^k`, `h = (h₀,…,h_D)` the h-vector. If `S/I(W₂)` is CM,
the series duality `H_ω(t) = (−1)^k H(1/t)` turns Theorem ω into a dictionary:
> **`B(d)_k ⟺ D ≤ k(k−1)`** (the h-degree bound IS GAP 5), and then
> **(Rc)_k ⟺ h_D = 2k−1** and **(V)_k ⟺ h_{D−1} = k(2k−3)** (via `K_{2k} = k·h_D + h_{D−1}
> = 4k(k−1)`), with `D = k(k−1)` pinned.
**Gates (blind, pre-registered):** k=2: `h = (1,2,3)`: D = 2 = k(k−1), h₂ = 3, h₁ = 2 ✓.
k=3: predicted `h = (1,3,6,9,12,9,5)` forced `HF_red₇ = 570` and `HF_red₈ = 810` —
**both evaluation ranks returned exactly the pre-registered numbers**; h-vector exact,
`Σh = 45 = #C` ✓, `D = 6`, `h₆ = 5 = 2k−1` ✓, `h₅ = 9 = k(2k−3)` ✓. 6/6.

## Link 3 (CM of `S/I(W₂)`) — honest status: OPEN

Self-linkage makes the classical "linkage preserves CM" circular here (I is linked to
itself). What stands **without** CM: Theorems M2, SL, ω (the module identification is
unconditional); the numeric h-consistency at k = 2, 3 (h-vectors nonnegative O-sequences
summing to `deg = #C`) is a necessary condition for CM and passes. What NEEDS CM: reading
`HF(ω)` as the reversed h-vector (the dictionary's ⟺). Named routes: depth chase through
`0 → K → S/J → S/I → 0` with `depth K ≥ min(2,k)` (ω is S₂) — currently yields only
`depth ≥ 1`; lattice shellability of the arrangement; or the bounded local-cohomology
version of the dictionary.

## The residue of GAP 5 after this turn — final form

> **GAP 5 = [CM of the arrangement ring ∀k (Link 3)] + [the top of its h-vector:
> `D = k(k−1)`, `h_D = 2k−1`, `h_{D−1} = k(2k−3)` ∀k (Link 4's two cells)].**
Both are statements about a REDUCED subspace arrangement — no nilpotents anywhere; the
duality has moved the entire problem into the lattice-census domain (route β's machinery),
exactly as the auditor's chain predicted. Bonus banked: the k=4 sealed prediction
**`dim I(W₂^{(4)})₈ = 968` CONFIRMED by full evaluation rank (C++ engine, this turn)** —
generation of K by the resolvent family now machine-verified at k = 2, 3, 4.

**Grades.** M2, SL(a),(b), SL-explicit, ω + twist: PROVED ∀k. h-dictionary: PROVED given
CM; COMPUTED exactly at k = 2, 3 (blind pre-registrations hit). CM ∀k: OPEN. Link 4's two
cells ∀k: OPEN (lattice target named). B(d): unchanged in scope (k ≤ 4 mechanism-proved).

— FRESCALES14. Engines: `selflink_gate_v2.py` (Nash, re-run), `selflink_products_omega.py`,
`W2_K4_D8_RANK.cpp` (validated k=3: 87/222; k=4 run in sandbox: 968 PASS). Same turn.

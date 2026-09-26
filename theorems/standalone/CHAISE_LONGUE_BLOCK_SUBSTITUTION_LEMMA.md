> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-09-03
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *THE BLOCK SUBSTITUTION LEMMA* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_BLOCK_SUBSTITUTION_LEMMA.md
>
> **Status, as written in the document:** Scope. `K = F₃`, `q = 3^v`, `U` an alphabet with `u^q = 0` for every letter (the box `T_box`). `Φ_u := u^{q−1}`. The statement is an identity in `K[U]`; the box is used only in the corollary. It is uniform in `t`, in `k` and in `q`, and it is proved by pencil …
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# THE BLOCK SUBSTITUTION LEMMA
## The support-`2t` detector is the support-`2` detector with letters replaced by block monomials

*A standalone component of **The Chaise Longue Theorem**. Rafael Amichis Luengo (Madrid) and Claude (Anthropic), 2026-09-03. Auditor: Don Mister Grep 2.*

---

**Scope.** `K = F₃`, `q = 3^v`, `U` an alphabet with `u^q = 0` for every letter (the box `T_box`). `Φ_u := u^{q−1}`. The statement is an identity in `K[U]`; the box is used only in the corollary. It is uniform in `t`, in `k` and in `q`, and it is proved by pencil in three lines. It does **not** by itself rewrite `σ_a^{(2t)}`; it puts the outer `(s,r)` sum of that rewriting into closed factored form.

---

### 0. What it replaces

In `FR_TORRE_REPORT §3.3` the chain that closes the family `t = 1` breaks at **Step 2′**, where the sum over supports of size `2t−1` produces a monomial symmetric function in `2t−1` slots. The route proposed there — expand it in power sums via inclusion–exclusion over the partition lattice (Doubilet 1972) — **does not exist over `F₃`**:

> `e₃ = m_{(1,1,1)} = (p₁³ − 3p₁p₂ + 2p₃)/6`, denominator `6 = 2·3`.
> Over `F₃`, `p₃ = p₁³` identically, so the power sums generate a **proper** subring of `Λ`:
> `rank{p₁³, p₁p₂, p₃} = 2` in degree `3`, while `rank{p₁³, p₁p₂, p₃, e₃} = 3`.

Since Step 2′ involves `λ = (s^{t−1}, r^t)`, whose multiplicity reaches `3` at `t = 3`, that route is dead for all `t ≥ 3`. The cases `t = 1, 2` succeeded by arithmetic accident (denominators `1` and `2`, invertible mod `3`).

**The obstruction was a summation order, not a mathematical wall.** The outer sum `Σ_{s+r=q−2}(−1)^r a^s` does not commute with the product `Ψ = ∏_{v∈V}(1 + vy + αv^s + βv^r)` — but it does not need to. It is performed **first**, term by term.

---

### 1. The lemma

Let `A, B ⊆ U` be disjoint with `|A| = |B| = t`, and set

> `P := ∏_{u∈A} u`,  `Q := −∏_{v∈B} v`,  `h_{q−2}(P,Q) := Σ_{s+r=q−2} P^s Q^r`.

> **LEMMA (block substitution).** *For every `t ≥ 1`, every alphabet, and every `q = 3^v`:*
> **(i)** `Σ_{s+r=q−2} (−1)^r (∏_{A} u)^s (∏_{B} v)^r = h_{q−2}(P,Q)`;
> **(ii)** `(P − Q)·h_{q−2}(P,Q) = P^{q−1} − Q^{q−1}`;
> **(iii)** `P^{q−1} = ∏_{u∈A} Φ_u` and `Q^{q−1} = ∏_{v∈B} Φ_v`.
> *Hence*
> # `(∏_{u∈A} u + ∏_{v∈B} v)·h_{q−2}(P,Q) = ∏_{u∈A} Φ_u − ∏_{v∈B} Φ_v.`

*Proof.* (i) `(−1)^r (∏_A u)^s (∏_B v)^r = (∏_A u)^s (−∏_B v)^r = P^s Q^r`; the two sums are the same sum. (ii) Telescoping: `(P−Q)Σ_{s+r=q−2}P^sQ^r = P^{q−1} − Q^{q−1}`. (iii) The `(q−1)`-st power is multiplicative, and `(−1)^{q−1} = 1` since `q` is odd. For the displayed form, `P − Q = ∏_A u + ∏_B v`. ∎

---

### 2. Why it is the uniform mechanism

The campaign's proved identity `H3` reads `(a+b)·h_{ab} = Φ_a − Φ_b`, with `h_{ab} = Σ_{i=0}^{q−2} a^i(−b)^{q−2−i}` (gate `4/4`, `28` pairs; CATÁLOGO `v269`). **The lemma is exactly `H3` under the substitution `a ↦ ∏_{A} u`, `b ↦ ∏_{B} v`**, and `t = 1` is the case `|A| = |B| = 1`.

Consequently the step `t → t+1` adds **one letter to each block**, i.e. **one factor `Φ`** on each side, and each such factor is consumed by the same proved principle

> `Φ_u · f = Φ_u · f|_{u=0}` (valid because `u·Φ_u = u^q = 0`; `STAR IDENTITY v1`).

There is no `t`-dependent integer anywhere in the chain, no partition lattice and no Möbius inversion. The law lives **inside** the step, which is what a `∀t` statement requires (Law 12, Law 27).

---

### 3. Gates (over `GF(3)`, `collapse_gate.py`)

| cell | (i) reordering | (ii)+(iii) block identity |
|---|---|---|
| `t=1, q=3` | `0` | `0` |
| `t=1, q=9` | `0` | `0` |
| `t=2, q=3` | `0` | `0` |
| `t=2, q=9` | `0` | `0` |
| **`t=3, q=3`** | `0` | `0` |
| **`t=4, q=3`** | `0` | `0` |

**Negative control** (sign of `Q` flipped, `t=2`, `q=9`): residual `−y₀⁶y₁⁶y₂y₃ − y₀⁴y₁⁴y₂³y₃³ − y₀²y₁²y₂⁵y₃⁵ − y₂⁷y₃⁷` — **fires**. `empty-result-read-as-pass` excluded.

The gates support the pencil proof; they do not constitute it (Law 27a).

---

### 4. Honest limits

- The lemma closes the **outer sum**. The full rewriting of `σ_a^{(2t)}` additionally requires crossing it with `ε_{A∪B}` and summing over the splittings `(A|B)` of the support. That is open.
- The lemma says nothing about the exponent `α` in `σ_a^{(2t)} ∈ (z^α, e_{2k}, r)`. For `t = 1` that exponent is `q−3` (MEASURED, two cells; `FR_TORRE_REPORT §3.2`); no law in `t` is claimed.
- The definition of the campaign's detector `h_T` for `|T| = 2t` is taken from the mission glossary `§0.0`, not re-derived here. **If `h_T ≠ Σ_{(A|B)} h_{q−2}(P_A, Q_B)`, the block substitution does not apply to `h_T` and this lemma is a statement about a different object** — that check is the first step of the mission `FR-BLOQUE`.
- Not yet refereed by a human expert.

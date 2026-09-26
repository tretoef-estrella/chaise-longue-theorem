> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026 (date not stated in the document)
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — KEY LEMMA, DIRECTION ⟸ (INJECTIVITY) VIA THE MIRROR* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_KEYLEMMA_P1.md
>
> **Status, as written in the document:** not stated in the document itself
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — KEY LEMMA, DIRECTION `⟸` (INJECTIVITY) VIA THE MIRROR
### `CHAISE_LONGUE_KEYLEMMA_P1_v1`  ·  standalone

**Target.** Key Lemma: for `σ` standard and `S` valid, `σθ_S∈J'_{k−1} ⟺ S≠S^*(σ)` (lex-max valid).
This doc proves the direction **`[P1]` `S≠S^* ⟹ σθ_S∈J'`** — equivalently `σθ_S∉J' ⟹ S=S^*`,
which is exactly `ψ∘φ=id`, i.e. **`φ` is injective `∀k`** (mod one finite insertability lemma).

## Floor language
For a monomial `ν`, variable `v`: `α_ν(v):=⌈(v−ν_v)/2⌉` (min rank at which `v` can be a
`g`-generator element: `m`-gen with `v` at rank `i` divides `ν` iff `α_ν(v)≤i`). Ballot cap
`b(v)=⌊v/2⌋`. `S` valid `⟺ α_σ(s_i)≤i≤b(s_i)`. Since `μ:=σθ_S` has `μ_v=σ_v+2[v∈S]`,
**`α_μ(v)=α_σ(v)−[v∈S]`** (the square drops the floor by 1 exactly on `S`). A level gen `m(W)`
divides `μ` iff `α_μ(w_j)≤j−1` for all `j`.

## The mirror construction (balance point on `S∪{t}`) — PROVED `∀k`
**Insertable element.** Call `t∉S` *insertable* if `α_σ(t) ≤ #\{s∈S:s<t\}`.

**Lemma A.** If an insertable `t` exists, then `μ=σθ_S∈J'_{k−1}`.
*Proof.* Let `U'=S∪\{t\}` (`k` elements, `⊆\{2,…,2k−1\}`), sorted `u'_1<…<u'_k`. Then
`α_μ(u'_l)≤l−1` for every `l`:
- `u'_l∈S` at `S`-rank `r≤l`: `α_μ(u'_l)=α_σ(s_r)−1≤r−1≤l−1`.
- `u'_l=t`: `α_μ(t)=α_σ(t)≤#\{s∈S:s<t\}=l−1`.

Run the **balance point** of `U'` (as in the `(L)` lemma): `N(p)=#\{u'≤2p+1\}`, `g(p)=N(p)−p`;
`g(0)=0`, `g(k−1)=k−(k−1)=1`; let `p^*=min\{p:g(p)=1\}` (`≤k−1`). Then `c_{p^*}=2` (full pair
`\{2p^*,2p^*+1\}⊆U'`) and `W=\{p^*+1 smallest of U'\}` is an admissible level support (`g(j)≤0` for
`j<p^*` gives the ballot `w_i≥2i`). Finally `α_μ(w_j)=α_μ(u'_j)≤j−1`, so `m(W)|μ`. Hence
`μ∈J'_{k−1}`. ∎  *(Engine `P1_proof.py`: `0` failures, `k≤5`, 783 783 checks.)*

## Reduction of `[P1]` to insertability
**Lemma B (insertability `⟺` non-maximality).** For `S` valid: an insertable `t` exists `⟺ S≠S^*(σ)`.
*Proof of `⟸`, main case.* `S≠S^*` ⟹ `∃` valid `S'>_{lex}S`; at the first differing rank `i_0`,
`s'_{i_0}>s_{i_0}`, and `S'` valid gives `α_σ(s'_{i_0})≤i_0`. If `s'_{i_0}∉S`, then
`#\{s∈S:s<s'_{i_0}\}≥i_0≥α_σ(s'_{i_0})` (the `i_0` elements `s_1<…<s_{i_0}` all lie below), so
`t=s'_{i_0}` is insertable. *(The sub-case `s'_{i_0}∈S` — the raised value already occurs at a higher
`S`-rank — is verified `k≤5` (`0` failures) but its uniform pencil is not yet written.)* The `⟹`
direction (insertable `t ⟹` a lex-larger valid support, hence `S≠S^*`) is the swap that raises `S` at
`t`'s rank. ∎ *(verified `k≤5`, `0` failures.)*

## Consequence
Given Lemma A + Lemma B: `S≠S^* ⟹` insertable `t ⟹ μ∈J'`. Contrapositive:
**`σθ_S∉J', S` valid `⟹ S=S^*`**, i.e. `ψ∘φ=id` and **`φ` injective `∀k`** — modulo the one sub-case
of Lemma B.

| item | grade |
|---|---|
| Lemma A (insertable `t ⟹ μ∈J'`), balance-point mirror | **PROVED `∀k`** |
| Lemma B `⟹` and main sub-case of `⟸` | **PROVED `∀k`** |
| Lemma B remaining sub-case (`s'_{i_0}∈S`) | verified `k≤5`; pencil OPEN |
| `[P1]` / `φ` injective `∀k` | **PROVED `∀k` mod that sub-case** |
| `[P2]` `S=S^* ⟹ σθ_S∉J'` (surjectivity) | verified `k≤5`; pencil OPEN |

**Grade: injectivity direction of the Key Lemma reduced to a balance-point mirror (Lemma A PROVED
`∀k`) plus a finite insertability lemma (main case PROVED, one sub-case verified `k≤5`).** Surjectivity
`[P2]` still open. Hence the Key Lemma — and `(*)`, (BIJ) — are **not yet `∀k`**; (B), GAP 3 untouched.

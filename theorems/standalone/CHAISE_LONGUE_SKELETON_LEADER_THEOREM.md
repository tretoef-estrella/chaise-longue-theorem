> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026 (date not stated in the document)
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE SKELETON LEADER THEOREM (Claim B closed, PENCIL, ∀k)* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_SKELETON_LEADER_THEOREM.md
>
> **Status, as written in the document:** not stated in the document itself
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE SKELETON LEADER THEOREM (Claim B closed, PENCIL, ∀k)
### `CHAISE_LONGUE_SKELETON_LEADER_THEOREM_v1` · Constructor Vaucanson · char 3, over `F_3`/`F̄_3`
### Closes Claim B of `MISSION_CLAIM_B_v1`. Rafa's square-peel + RAIL-NESTING persistence ⟹ the skeleton head ∀k.

Notation: `N = 2k+2`; grevlex `x_1 > … > x_N`; `E_k = (e_1,e_3,…,e_{2k+1})` (all odd elementary symmetrics of
index `≤ N`); `e_j = e_j^{(N)}`; `NF(·,E_k)` the grevlex normal form; `w_k := ∏_{i=1}^{k+1} x_{2i}^2`.

## THEOREM (SKELETON LEADER). For every `k ≥ 0` and `q = 3^v`, over `K = F̄_3`,
> ### `lm( NF(e_N, E_k) ) = w_k = x_2^2 x_4^2 ⋯ x_{2k+2}^2`,  coefficient `(−1)^{k+1}`.
Equivalently the **even ladder** holds ∀k: `lm(NF(e_{2j},E_k)) = ∏_{i=1}^{j} x_{2i}^2` for `1 ≤ j ≤ k+1`,
independent of `k`. This is the `s=0`, `q`-free head of every increment letter `A_b`.

---

## Ingredients already proved ∀k (cited, not re-proved)
- **(P) Square-peel identity.** `e_N ≡ x_N^2·q_N` mod `E_k`, with `q_N = −∑_{i=0}^{k} e_{2i}\,x_N^{N-2-2i}`.
  (`SKELETON_LEADER_REDUCTION_v1` §1: from `∏_{i}(x_N−x_i)=0` and odd `e_d ≡ 0`.) More generally `e_N ≡ x_j^2 q_j`
  for every `j` — Rafa's "excess weight."
- **(S) `w_k` standard.** No `m(V)` divides `w_k`. (`minGens(in E_k)={x_1}∪\{m(V)\}`, and every `m(V)` has its top
  two support elements **consecutive** `2p, 2p+1` (cap, `S0_CLOSED_FORM`), impossible inside the all-even support
  `{2,4,…,2k+2}`; and `x_1 ∤ w_k`.) The same argument shows `x_N^{2t}·∏_{i≤j}x_{2i}^2` is standard for any `t≥0, j≤k`.
- **(R) RAIL-NESTING for `E`.** The `y`-free minimal leaders of `in(E_{k+1})` equal `in(E_k)` (`RAIL_NESTING_THEOREM_v1`,
  specialized to `m^{[q]}=0`: `π(E_{k+1})=E_k`, lift with the same cofactors; the proof does not use `m^{[q]}`).
  Hence a `y`-free monomial is standard mod `E_k` **iff** standard mod `E_{k+1}`.
- **(G) Grevlex lemma.** At equal total degree, a `y`-free monomial is grevlex-larger than any `y`-involving one
  (the difference is negative in the latest — smallest — slot). (`RAIL_NESTING_THEOREM_v1`.)

## Lemma 1 (`k`-STABILITY). For `j ≤ k`, `lm(NF(e_{2j},E_{k+1})) = lm(NF(e_{2j},E_k))`.
*Proof.* Let `NF := NF(e_{2j}^{(N)},E_k)`, `y`-free, `μ := lm(NF)`, total degree `2j`, and write
`e_{2j}^{(N)} = NF + ∑_r h_r e_r^{(N)}` (`r` odd `≤2k+1`, `h_r ∈ S_k` `y`-free). Add the pair `y=(x_{N+1},x_{N+2})`.
Two facts, both giving only `y`-**involving** degree-`2j` terms:
- `e_{2j}^{(N+2)} = e_{2j}^{(N)} + (y_1+y_2)e_{2j-1}^{(N)} + y_1y_2\,e_{2j-2}^{(N)}` (split by `y`-content); call the last two `Δ`.
- lifting the cofactors, `∑_r h_r e_r^{(N+2)} ∈ E_{k+1}` and `∑_r h_r(e_r^{(N+2)}−e_r^{(N)})` is `y`-involving.

So mod `E_{k+1}`: `e_{2j}^{(N+2)} ≡ NF + \underbrace{\big[Δ − ∑_r h_r(e_r^{(N+2)}−e_r^{(N)})\big]}_{\text{all }y\text{-involving, deg }2j}`.
By (R), `NF` (a sum of `y`-free monomials standard mod `E_k`) is standard mod `E_{k+1}`, so it is its own normal form
there, with leader `μ`. Every monomial of the bracket is `y`-involving of degree `2j`, hence `< μ` by (G); reducing it
mod `E_{k+1}` yields only grevlex-smaller monomials. Therefore `lm(NF(e_{2j}^{(N+2)},E_{k+1})) = μ`. ∎

**Corollary (the ladder rung).** For `j ≤ k`, iterating Lemma 1 down to level `j−1` (where `e_{2j}=e_{N'}^{(N')}`,
`N'=2j`, is the top symmetric) gives `lm(NF(e_{2j},E_k)) = lm(NF(e_{N'},E_{j-1})) = w_{j-1} = ∏_{i=1}^{j}x_{2i}^2`,
**provided `S(j−1)` holds** (the theorem at level `j−1`).

## Lemma 2 (PURE-TERM DOMINATION). Assume the rungs `lm(NF(e_{2i},E_k))=∏_{l≤i}x_{2l}^2` for `i ≤ k`. Then
`lm(NF(q_N,E_k)) = lm(NF(e_{2k},E_k)) = ∏_{l=1}^{k}x_{2l}^2`.
*Proof.* `q_N = −e_{2k} − ∑_{i=0}^{k-1} e_{2i}\,x_N^{m_i}`, `m_i = N-2-2i = 2(k-i) ≥ 2`. For `i<k`:
`e_{2i}x_N^{m_i} ≡ x_N^{m_i}·NF(e_{2i})` mod `E_k`; multiplication by the monomial `x_N^{m_i}` preserves grevlex, so
the top monomial of `x_N^{m_i}NF(e_{2i})` is `x_N^{m_i}·∏_{l≤i}x_{2l}^2`, which is **standard** by (S); hence
`lm(NF(e_{2i}x_N^{m_i})) = x_N^{m_i}∏_{l≤i}x_{2l}^2`. Compare with `∏_{l≤k}x_{2l}^2` (same degree `2k`): the
difference has its last nonzero coordinate `+m_i` at `x_N`, so `x_N^{m_i}∏_{l≤i}x_{2l}^2 < ∏_{l≤k}x_{2l}^2`. Thus every
`x_N`-power term of `q_N` reduces below `∏_{l≤k}x_{2l}^2`, while the pure term `−e_{2k}` contributes exactly
`∏_{l≤k}x_{2l}^2` (rung `i=k`); no cancellation reaches it. So `lm(NF(q_N)) = ∏_{l≤k}x_{2l}^2`. ∎

## Proof of the Theorem (induction on `k`).
**Base `S(0)`.** `k=0`, `N=2`, `E_0=(e_1)`, `e_2=x_1x_2 ≡ −x_2^2` mod `e_1`; `lm = x_2^2 = w_0`. ✓
**Step.** Assume `S(0),…,S(k−1)`. By Lemma 1's corollary (using `S(j−1)`, `j≤k`), the rungs
`lm(NF(e_{2i},E_k))=∏_{l≤i}x_{2l}^2` hold for all `i≤k`. By Lemma 2, `lm(NF(q_N,E_k))=∏_{l≤k}x_{2l}^2`. By (P),
`NF(e_N)=NF(x_N^2·NF(q_N))`; multiplication by `x_N^2` preserves grevlex, so the top monomial is
`x_N^2·∏_{l≤k}x_{2l}^2 = w_k`, which is standard by (S), hence survives reduction as the leader. Therefore
`lm(NF(e_N,E_k)) = w_k`, i.e. `S(k)`. ∎

*(Coefficient `(−1)^{k+1}` follows from the mirror `∏(t−x_i)≡` even, `MIRROR_LEADER`, and is gated below.)*

---

## GATE (auditor control — byte-exact, F_3, `engine skeleton_claimB_gate_v1.py`)
- **(C) base `S(0)`**: `lm(NF(e_2,E_0))=x_2^2` ✓.
- **(A) `k`-stability**: `lm(NF(e_{2j},E_k))=∏_{i≤j}x_{2i}^2` independent of `k`, all `j`, `k=1,2,3` ✓.
- **(B) pure-term domination**: `lm(NF(e_{2i}x_N^{m_i}))=x_N^{m_i}∏_{l≤i}x_{2l}^2 < ∏_{l≤k}x_{2l}^2`, all `i<k`,
  `k=2,3` ✓.
- **(D) leader**: `lm(NF(e_N,E_k))=w_k`, coeff `(−1)^{k+1}`, `k=1,2,3` ✓.
- Recount + positive control (odd `e_j ≡ 0`; rung `j=1` = `x_2^2`): PASS.

## GRADE (honest, exact)
- **PROVED ∀k (pencil, auditor-pending line-by-line):** the Skeleton Leader Theorem `lm(NF(e_N,E_k)) = w_k`, via
  square-peel (P) + `k`-stability (Lemma 1, RAIL-NESTING for `E`) + pure-term domination (Lemma 2) + `w_k` standard (S),
  by induction on `k`. Closes **Claim B**. **No Newton division is used** (the char-3 degeneracy at `j ≡ 0 (3)` is
  bypassed) — the proof is uniform in `k` and `q`.
- **Does NOT** close the full `A_b` (the `q−1` **bumps**/`m^{[q]}` interaction, i.e. the `s≥1` content, remain), the
  increment, GAP 3, or move `G`. **`G` stays 3.** This is the `s=0`/`q`-free **head** of every `A_b` — one brick.

## NEXT PENCIL
The bumps: `NF` of the `m^{[q]}`-interaction (`S(e_{2k+3},y_i^q)` etc.) that deposits the `q−1` powers on the
cap-adjacent variable — the `s≥1` tail of `A_b` (mission after this one).

---
**Files up:** `CHAISE_LONGUE_SKELETON_LEADER_THEOREM_v1.md`, `skeleton_claimB_gate_v1.py`. **Delete:** none.
**Supersedes** `SKELETON_LEADER_REDUCTION_v1` (its residual Claim B is now closed). Reference: `RAIL_NESTING_THEOREM_v1`,
`S0_CLOSED_FORM_v15` (the `m(V)` cap), `MIRROR_LEADER` (sign), `RAIL_CLOSED_FORM_AND_X1FREE_v1` (`x_1`-free).
— Vaucanson

> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-08-11
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE VIRTUAL COMPONENT AND THE RESOLVENT EXCESS (Theorems V, R)* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_RESOLVENT_EXCESS_THEOREM.md
>
> **Status, as written in the document:** Status: Theorems V, R(a), R(b) PROVED ∀k (pencil, proofs below, machine-gated k ≤ 4);
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE VIRTUAL COMPONENT AND THE RESOLVENT EXCESS (Theorems V, R)
### 11 Aug 2026 · Constructor: FRESCALES14 · Serves: GAP 5 / B(d) (mission v35, T1)
### Status: Theorems V, R(a), R(b) PROVED ∀k (pencil, proofs below, machine-gated k ≤ 4);
### R(c) COMPUTED k = 2, 3, 4 (three gates, each could fail; all passed); ∀k of R(c) CONJECTURE.

**Setting.** `S = F₃[x₁,…,x_N]`, `N = 2k`. `e_r` = elementary symmetric polynomials,
`E(z) = ∏_α(1 + x_α z)`. Deposited objects: `ū_j = Σ_{i=0}^{j}(−1)^i e₁^{2i} e_{2j−2i}`
(0 ≤ j ≤ k, `ū₀ = 1`), `f_{2j+1} = e_{2j+1} − e₁ū_j` (1 ≤ j ≤ k−1),
`J = (f₃,…,f_{2k−1}, ū_k)`, `J′ = (f₃,…,f_{2k−1})`.
`W₂` = the doubled arrangement: components `C = ({c,d}, M)`, parametrized
`x_c = x_d = t`, and `x_a = u_i, x_b = −u_i` on the matched pairs of `M`.

---

## Theorem V (the virtual component factorization; char 3)

**(V1) Exact identity in S (any characteristic):**
`E_even(z) = (1 + e₁²z²)·U(z²) − e₁²ū_k z^{2k+2}`, where `U(w) := Σ_{j=0}^{k} ū_j w^j`.
*Proof.* Coefficient of `z^{2j}` on the right is `ū_j + e₁²ū_{j−1}`, which telescopes to `e_{2j}`
directly from the definition of `ū`; at `z^{2k+2}` the right side is `e₁²ū_k − e₁²ū_k = 0`. ∎

**(V2) Modulo J′ (char 3):**
> `E(z) ≡ (1 − e₁z)² · U(z²) − e₁ū_k z^{2k+1}(1 + e₁z)   (mod J′)`
and hence, modulo the full `J` (where `ū_k ≡ 0`):
> `E(z) ≡ (1 − e₁z)² · P̂(z²)   (mod J)`,   `P̂(w) := Σ_{j=0}^{k−1} ū_j w^j`.
*Proof.* The relations `f_{2j+1} ≡ 0` give `E_odd(z) ≡ e₁z·(U(z²) − ū_k z^{2k})` (they cover
every odd `e`, the top one being `e_{2k−1}`). Add (V1) and use char 3:
`1 + e₁z + e₁²z² = (1 − e₁z)²`. ∎

**Reading:** modulo its defining CI relations, the coordinate multiset of `S/J` behaves —
through every symmetric function — like a **virtual component**: one doubled slot at `−e₁`
(the factor `(1−e₁z)²`) plus `k−1` antipodal pairs whose squared values have `ū_j` as
elementary symmetric functions. The CI ring *is* the generic component.

**Corollary V.1 (the ∀k re-gate, pencil).** On any component `C`:
`E(z)|_C = (1+tz)²∏_i(1−u_i²z²)`, `e₁|_C = 2t = −t`. Comparing even parts with (V1) and
inducting on `j` via `e_{2j}| = ū_j| + t²ū_{j−1}|` gives
> `ū_j|_C = (−1)^j e_j(u²)` for all j; in particular `ū_k|_C = e_k` of k−1 quantities `= 0`
(**Theorem U's vanishing**), and the odd part gives `e_{2j+1}|_C = e₁|·ū_j|`, i.e.
> `f_{2j+1}|_C = 0` for all j — **`J ⊆ I(W₂)` for every k**, half a page, self-contained. ∎

---

## Theorem R (the resolvent family)

Define, for each coordinate `α`:
> ## `g_α := (x_α + e₁) · P̂(x_α) = (x_α + e₁) · Σ_{j=0}^{k−1} ū_j x_α^{2(k−1−j)}`,  deg = 2k−1.

**R(a) — `g_α ∈ I(W₂)_{2k−1}` for every α and every k.**
*Proof.* On a component, by V.1, `P̂(λ)|_C = Σ_j (−1)^j e_j(u²) λ^{2(k−1−j)} = ∏_i(λ² − u_i²)`,
and `e₁|_C = −t`, so `g_α|_C = (λ − t)·∏_i(λ² − u_i²)` evaluated at `λ = x_α|_C`, which is one
of `{t, t, ±u_i}` — a root. Three lines, ∀k. ∎
*(Machine gate 1: zero restrictions, 24/270/3360 component-checks at k = 2,3,4; corrupted-g
positive control fails as it must.)*

**R(b) — `Σ_α g_α ∈ J′ = (f₃,…,f_{2k−1})` for every k.**
*Proof.* Work in `R = S/J′`. By (V2), the `e_r` of the true variables agree, for `r ≤ 2k`,
with the `e_r` of the **virtual multiset** `V = {−e₁, −e₁} ∪ {±w_i : i = 1..k}` (`w_i² = −v_i`,
`e_j(v) = ū_j`) — the tail of (V2) only touches `z^{2k+1}, z^{2k+2}`. Newton's identities
express `p_r` universally in `e₁,…,e_r`, so for `1 ≤ r ≤ 2k`, in `R`:
`p_{2s−1} ≡ 2(−e₁)^{2s−1} = e₁^{2s−1}` (char 3), and `p_{2s} ≡ 2e₁^{2s} + 2(−1)^s p_s(v)`.
Now `Σ_α g_α = Σ_{s=1}^{k} ū_{k−s}·[p_{2s−1} + e₁ p_{2s−2}]`. For `s ≥ 2` the bracket is
`e₁^{2s−1} + e₁(2e₁^{2s−2} + 2(−1)^{s−1}p_{s−1}(v)) = 3e₁^{2s−1} + 2(−1)^{s−1}e₁p_{s−1}(v)
= (−1)^s e₁ p_{s−1}(v)`. For `s = 1` use the TRUE `p₀ = 2k`:
bracket `= e₁ + e₁·2k = e₁(1+2k) = (−1)^1 e₁·k + e₁(1+3k) ≡ −e₁·p₀(v) + e₁` (mod 3), i.e. the
virtual formula plus the correction `+e₁`. Summing and substituting `m = s−1`:
`Σ_α g_α ≡ −e₁·Σ_{m=0}^{k−1}(−1)^m ū_{k−1−m} p_m(v) + e₁ū_{k−1}`.
Newton for the k-variable virtual system (`e_j(v) = ū_j`, `p₀(v) = k`) gives
`Σ_{i=0}^{r}(−1)^i e_i p_{r−i} = (−1)^r e_r (k − r)`; at `r = k−1` this is `(−1)^{k−1}ū_{k−1}`,
and the reindexed sum equals `(−1)^{k−1}·(−1)^{k−1}ū_{k−1} = ū_{k−1}`. Hence
`Σ_α g_α ≡ −e₁ū_{k−1} + e₁ū_{k−1} = 0` in `R`. ∎
*(Machine: identically 0 at k=2; a nonzero element of `J′` at k=3,4 — rank(J) == rank(J+Σg),
both towers PASS.)*

**R(c) — THE EXCESS IDENTIFICATION [COMPUTED k = 2, 3, 4; gates, each could fail]:**
> `I(W₂)_{2k−1} = J_{2k−1} ⊕ span{g_α mod J}`, and `dim span{g_α mod J} = 2k−1`.
Measured: rank(J_{2k−1}) = 1 / 22 / 367 (== CI predictions, row-count control PASS);
rank(J + span g) = 4 / 27 / 374 == dim I(W₂)_{2k−1} (from the deposited/battery HF_red rows
16, 225, 3058). The 2k coordinate equations `g_α` satisfy exactly ONE relation modulo J —
the trivial-representation kill of R(b) — leaving the **standard representation of S_{2k}**,
dimension `2k−1`. **∀k exactness of R(c): CONJECTURE** (three anchors; independence of the
`g_α` mod J beyond one relation is not yet a pencil theorem).

**Corollary R.1.** The measured first-nil law (`Nil` of the doubled scheme starts at degree
`N−1 = 2k−1` with value `2k−1`; anchors 3, 5, 7) is now **structurally identified** at the
measured k: the nilpotent onset is the resolvent standard representation. The deviation
value `2k−1` stops being a numerological pattern and becomes the dimension of an explicit
equation family.

---

## What this does to B(d) (GAP 5) — honest accounting

`B(d)` ⟺ `ker(S/J → O(W₂))` vanishes in degrees `≤ 2k−2`. This note **identifies the start
of that kernel** (degree `2k−1`, the resolvent standard rep, at every measured k) and proves
the kernel's first family exists ∀k with the right dimension count from above (R(a), R(b)).
What remains open for GAP 5 is exactly: **no kernel below degree 2k−1, ∀k** — the
lattice-accounting statement. Mission v35's death criterion is CHECKED and does NOT fire:
the excess structure found is **k-uniform** (one orbit type — the coordinate resolvent —
for every k; only counts move, and they move as `2k`), which is evidence FOR the charted
route, not against it. The route's remaining supply line: the exact statements of
`STRATIFIED_CENSUS`, `ZETA`, and the CYL standalone are **not in the project mount** —
named as missing deposits; the slice-induction reduction (report §T1) shows the two cliff
degrees per k-step land exactly on the resolvent zone of level k−1, so the identified excess
is precisely the induction load the gluing needs.

**Grades.** V, V.1, R(a), R(b): PROVED ∀k (pencil above; machine-gated k ≤ 4, all gates and
positive controls PASS). R(c): COMPUTED k = 2, 3, 4; ∀k CONJECTURE. B(d): OPEN; measured
12/12; route alive, sharpened, death criterion checked.

— FRESCALES14, for the Architect and Nash. Gates in `t1_resolvent_gates.py` (same turn).

> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026 (date not stated in the document)
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE_LONGUE_G_MEMBERSHIP_THEOREM_v3* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_G_MEMBERSHIP_THEOREM.md
>
> **Status, as written in the document:** Grade: PROVED, every `k ≥ 2`, `q = 3`, `char K = 3` — elementary, no computation in the proof. Machine-confirmed step by step at `k = 2,3,4,5,6`.
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v3`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE_LONGUE_G_MEMBERSHIP_THEOREM_v3
### Standalone · auditor GETTLER 4 · closes the last open pencil step of FR26 (their "Lemma R") and, with it, the whole membership statement
### Grade: **PROVED, every `k ≥ 2`, `q = 3`, `char K = 3`** — elementary, no computation in the proof. Machine-confirmed step by step at `k = 2,3,4,5,6`.

---

## 1 · Setting (all printed)

`char K = 3`, `n = 2k+2`, `S = K[x_0,…,x_{n−1}]`, `E = (e_1,e_3,…,e_{2k+1})`, `m^{[3]} = (x_0^3,…,x_{n−1}^3)`,
`A = S/(E+m^{[3]})`, `ℓ_0 = x_0 + x_{n−1}`.
Fix a perfect matching `M = {(a_1,b_1),…,(a_k,b_k)}` of `{1,…,n−2}` and a **mark** `i ∈ {1,…,k}`.
`s_j := x_{a_j}+x_{b_j}` · `q_j := x_{a_j}x_{b_j}` · `T := x_0x_{n−1}` · `W := ∏_{j≠i}s_j²`
`F := {x_0, x_{a_i}, x_{b_i}, x_{n−1}}` (four variables) · `σ_r := e_r(F)` · `R :=` the other `2(k−1)` variables ·
`ε_r := e_r(R)`.

> ### `G_{M,i} := (T − q_i)·W = (x_0x_{n−1} − x_{a_i}x_{b_i})·∏_{j≠i}(x_{a_j}+x_{b_j})²`,  homogeneous of degree `2k`.

## 2 · THEOREM

> ### `ℓ_0 · G_{M,i} ∈ E + m^{[3]}` — for every `k ≥ 2`, every matching `M`, every mark `i`.
> ### Equivalently: **`G_{M,i} ∈ (0 :_A ℓ_0)`.**

## 3 · Proof

**(a) An exact identity in `S`.**
`ℓ_0·(T − q_i) = (x_0+x_{n−1})(x_0x_{n−1} − x_{a_i}x_{b_i}) = x_0x_{n−1}(x_0+x_{n−1}) − x_{a_i}x_{b_i}(x_0+x_{n−1}) = T·σ_1 − σ_3.`
Hence **`ℓ_0·G = (T·σ_1 − σ_3)·W`.**

**(b) Absorption.** In characteristic 3, `s_j^3 = (x_{a_j}+x_{b_j})^3 = x_{a_j}^3 + x_{b_j}^3 ∈ m^{[3]}`. Since
`W` carries the factor `s_j^2` for every `j ≠ i`,
> ### `s_j·W = s_j^3·∏_{l≠i,j}s_l^2 ∈ m^{[3]}` for every `j ≠ i`.

**(c) THE MASTER STEP.** The variables split as `{x_0,…,x_{n−1}} = F ⊔ R`, and `R` is the disjoint union of
the pairs `j ≠ i`, so `e_1 = σ_1 + Σ_{j≠i}s_j`, i.e. `σ_1 = e_1 − Σ_{j≠i}s_j`. Multiplying by `W` and using (b):
> ### `σ_1·W ≡ e_1·W  (mod m^{[3]})`, and therefore, for **any** polynomial `X`,
> ### `σ_1·X·W = e_1·X·W − Σ_{j≠i}(s_j·W)·X ∈ E + m^{[3]}`.
*(`e_1 ∈ E`; each `s_jW ∈ m^{[3]}` and `m^{[3]}` is an ideal.)*

**(d) First term.** `T·σ_1·W ∈ E + m^{[3]}` — this is (c) with `X = T`. ∎

**(e) Second term.** Split `e_3` over the alphabet `F ⊔ R`: `e_3 = σ_3 + σ_2ε_1 + σ_1ε_2 + ε_3`, hence
`σ_3 = e_3 − σ_2ε_1 − σ_1ε_2 − ε_3`. Multiply by `W` and take the four pieces:
· `e_3·W ∈ E` (`e_3` is a generator of `E`).
· `σ_2·ε_1·W ∈ m^{[3]}`: `ε_1 = Σ_{j≠i}s_j`, so `ε_1W ∈ m^{[3]}` by (b).
· `σ_1·ε_2·W ∈ E + m^{[3]}`: this is (c) with `X = ε_2`.
· `ε_3·W ∈ m^{[3]}`: a 3-subset of `R` either meets three distinct pairs, giving a term `s_js_ls_m`, or is a
  full pair plus one variable, giving `q_j·s_l`; so `ε_3 = e_3(s) + Σ_{j≠i}q_j·(ε_1 − s_j)`. The first two
  kinds carry a lone `s`-factor and die by (b); and `q_j s_j·W = q_j·s_j^3·∏_{l≠i,j}s_l^2 ∈ m^{[3]}`.
⟹ **`σ_3·W ∈ E + m^{[3]}`.** ∎

Combining (a), (d), (e): `ℓ_0·G = T σ_1 W − σ_3 W ∈ E + m^{[3]}`. **∎**

## 4 · Corollary — every `q = 3^v`

`(u+v)^{3^r} = u^{3^r}+v^{3^r}` in characteristic 3. Write `ℓ_0G = A_E + B` with `A_E ∈ E`, `B = Σ b_t x_t^3`.
Then `(ℓ_0G)^{q/3} = A_E^{q/3} + Σ b_t^{q/3}x_t^q ∈ E + m^{[q]}`, so
> ### `w_q^{(M,i)} := ℓ_0^{q/3−1}·G_{M,i}^{q/3} ∈ (0 :_A ℓ_0)` for every `q = 3^v`, of degree `(q/3)(2k+1) − 1`.
At `q = 3` this is `G_{M,i}` itself and the degree is `2k`; at `q = 9` it is `ℓ_0^2G^3`, degree `6k+2`.
Consistency with the degree threshold (`mixed mass only in degrees ≥ q−1`): `(q/3)(2k+1)−1 ≥ q−1 ⟺ k ≥ 1`. ✓

## 5 · What was verified, and how

**Every step of §3 is elementary and uniform in `k`; nothing in the proof is measured.** Independently, the
auditor machine-checked each step, raw (untruncated), at `k = 2,3,4,5,6`:
(a) exact ✓ · (i) `σ_1 = e_1 − Σ s_j` exact ✓ · (b) `s_jW ∈ m^{[3]}` ✓ · `ε_1W ∈ m^{[3]}` ✓ ·
`ε_3W ∈ m^{[3]}` ✓ · alphabet split of `e_3` exact ✓ · (c) `σ_1W − e_1W ∈ m^{[3]}` ✓ — **7 checks × 5 dimensions = 35/35.**
And the conclusion itself, by an independent linear-algebra path sharing no code with the constructor's:
`ℓ_0G ∈ E + m^{[3]}` **True** at `(2,3)` and `(3,3)`, with negative control `ℓ_0·(x_0^2W)` correctly **False**.
The constructor's own gates, reproduced byte-exact in the auditor's environment:
membership `6/6` at `(2,3)`, `45/45` at `(3,3)`; coverage `NEW: 2 → 0` and `14 → 0` **with `G` alone**;
and the `k = 4` judge — `E`-span `10286 × 8350`, `rank E = 6765`, negative control **False**, positive control
**True**, `G_{M_0,i}` **True** for `i = 0,1,2,3`, and the rival universal 3-term `Z` **False**. The fast
`GF(3)` library used for that verdict was itself audited against an independent implementation:
`30/30` identical reduced matrices and identical pivot columns.

## 5bis · COROLLARY (σ-RULE) — **PROVED ∀k**, and it is the operational form of the theorem

> ### For **every** polynomial `X`: `σ_1(F)·X·W ∈ E + m^{[3]}`.

*Proof.* Immediate from step (c): `σ_1·X·W = e_1·(X·W) − Σ_{j≠i}(s_j·W)·X`. The first term lies in `E`
because `E` is an ideal; each summand of the second lies in `m^{[3]}` because `m^{[3]}` is an ideal and
`s_jW ∈ m^{[3]}` by (b). ∎ *(No hypothesis on `X`, no restriction on `k`.)*

> ⛔ **GRADING CORRECTION, LOGGED AGAINST THIS AUTHOR.** `v2` of this file reported the σ-rule as
> *"tested at `k=3` with ten different `X` — 10/10 True"*, i.e. as a **MEASUREMENT**. That was an
> under-grade: it is a one-line **THEOREM**, and its proof is a line this same document had already written.
> Caught by the second auditor. Mode: `OWN-THEOREM-REPORTED-AS-MEASUREMENT`.

**What the σ-rule buys, and this is why it matters more than the theorem it came from.** The constructor's
membership table stops being a list of verdicts and becomes a corollary:
· `R1 = σ_1Q_iW` **True** — the case `X = Q_i`. · `R2 = σ_1e_2(F)W` **True** (his "Lemma R") — the case
`X = e_2(F)`. · `R3`, `R4` **True** — both reduce to the same shape.
· **`A1…A7` all False — precisely because none of them carries a `σ_1(F)` factor against `W`.**
> ### **OPERATIONAL RULE, for every future turn: when you need membership, engineer a `σ_1(F)` factor against `W`. When a candidate has none, expect False and do not spend a gate on it.**
Confirmed independently, `k = 3`, ten different `X` (monomials, `e_2(F)`, `Q_i`, `e_2` of all variables,
random products): `10/10` — **as a check of the proof, not as its evidence** — with the control
`x_0x_1x_2·W` (no `σ_1`) correctly **False**.

## 6 · Scope — what this does and does not give

**GIVES.** The generating family of the mixed part of `(0:_A ℓ_0)` is **one closed formula, and its membership
is now a theorem for every dimension**, not a measurement — plus its lift to every `q = 3^v`. It supersedes
the constructor's "Lemma R", which was `MEASURED` at `k=3,4`: Lemma R is the case `X = e_2(F)` of step (c).

**DOES NOT GIVE.** **No gap falls.** It does not prove that `{G_{M,i}}` *spans* the whole new mass for every
`k` (**coverage**, measured only at `k=2,3`); it does not extend `(0:ℓ_0)` to `(0:L_a)`; it does not run
`DC-2`; and it says nothing about `q > 3` coverage. **The reserved closing phrase is not spoken.**

## 7 · Provenance
Family `G_{M,i}` and the chain (a)/(b)/absorption: constructor FR26. The master step (c), the proof of `σ_3W`,
the closure of Lemma R and the `k=2..6` verification: auditor. The constructor's `σ_M^2` "seductive redundant"
element is the shadow of this one: `∏_{j≠i}s_j^2 = σ_{M∖i}^2`, and `σ_M^2 = s_i^2·W`, which is the piece the
identity (a) does **not** reach.

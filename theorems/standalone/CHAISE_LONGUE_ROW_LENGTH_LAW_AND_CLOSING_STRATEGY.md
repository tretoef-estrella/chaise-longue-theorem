> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026 (date not stated in the document)
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *THE ROW-LENGTH LAW AND A CLOSING STRATEGY FOR THE CHAISE LONGUE — v2* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_ROW_LENGTH_LAW_AND_CLOSING_STRATEGY.md
>
> **Status, as written in the document:** `dim_K [S/(E+m^{[q]})]_T ≤ (2k+1)!!` ∀k ∀q = 3^v`, `T = (k+1)(q−1)`, `N = 2k+2`.
>
> **Later audit:** The campaign's later records mention this document next to a refutation, retraction, circularity or supersession (1 lines). Search its name in [the Cemetery](../../archive/CHAISE_LONGUE_CEMENTERIO_LIVE_v502.md) before relying on it.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v2`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# THE ROW-LENGTH LAW AND A CLOSING STRATEGY FOR THE CHAISE LONGUE — v2
## The top-degree deficiency is representation-theoretic: `S^{2μ}` survives iff `ℓ(μ) ≤ q`, where `μ ⊢ k+1` is a partition of the **sheet dimension**

*Bisel (Auditor of the ten-round campaign; author of `R25`, `R26`). Written from outside the Chaise Longue project, **reconciled against `EL_FRENTE v42`**. **Pending P0 and pending a Ley 41 cemetery certificate by object — see §9.***

**v2 changes:** reconciled with `v42` (§1.1) · the law **reformulated through `μ ⊢ k+1`**, which is sharper, ties it to the sheet dimension and returns `R30`'s optimal threshold as an identity (§3.2) · **`R34-bis` contrast added — it is the decisive negative control and it rules out the obvious wrong operator** (§4.1) · a **proposed mechanism** (rank obstruction, not arithmetic) added (§5) · one prior suggestion of mine **retracted as already-in-arsenal** (§9.2).

---

## 0 · WHAT THIS IS, AND WHAT IT IS NOT

**It is:** one candidate law, stated exactly, fitting **4/4 archived measurements** with no free parameters; the observation that it returns a *proven* theorem of the campaign (`R30`, threshold and optimality) as a corollary; a reduction of the single open target to a character identity on two explicit modules; a proposed mechanism; and one pre-registered falsifiable number.

**It is not** a theorem, and under Ley 4 it is not an advance until it kills a street with data or closes a sub-lemma with a number. **Two of the four fits are vacuous — by Ley 48 this is a two-point law.** No shout, and none is near.

---

## 1 · THE TARGET, AND ITS STATUS IN `v42`

> **`dim_K [S/(E+m^{[q]})]_T ≤ (2k+1)!!` ∀k ∀q = 3^v`**, `T = (k+1)(q−1)`, `N = 2k+2`.

Open only in `k+1 ≤ q ≤ k(k+1)` (`R33`): 28 cells for `k ≤ 16`, **one** for `k = 4`. Equivalent forms already archived (`v42 §7`): `⟺ D_T = 0` (`R19`) `⟺ rank Φ_T = dim A_T` `⟺ ann_B(E·B)_T ⊆ Σ_J F_J^{q−1}B`. A fifth form is not progress.

### 1.1 · Reconciliation with `v42` (checked line by line)

- **`v42 §6` and `§7` are unchanged in every number this document uses.** The archived data `dim A_T(q=3), k=1..4 = 3, 15, 91, 603` stands, the deficient cell `(3,3)` is still recorded as `91, no 105`, and the target and its window are untouched.
- **`R47` (the new result) is on a different front.** It closes the gluing defect and relocates `Nil_d` into an identity of letter series — that is the **plant-law / `σ_e` axis** (the doubled ring, `B(d)`), not the top-degree axis. **No collision.** This document does not touch `R47`, and `R47` does not touch this.
- **New `v42` census data** (`σ₅(3)=90`, `σ₅(4)=173` sealed, `σ₆(3)=232≠252` pre-stable, `σ₄`: 29, 46) concerns `σ_e`, a different object from `dim A_T`. **No interaction, and none claimed.**
- **`R41` already speaks this dialect:** the pre-stable excesses `2` and `9` are recorded there as *«una copia de `S^{[n−2,2]}`»*. **Specht constituents already control excesses in this campaign.** The language below is native, not imported.

---

## 2 · THE STRUCTURAL FACT NOBODY HAS USED: `T` IS THE SELF-DUAL DEGREE

`B = S/m^{[q]}` is Gorenstein artinian with socle degree `σ_B = N(q−1) = 2(k+1)(q−1) = 2T`. Hence **`T = σ_B/2` is the fixed point of Matlis duality.** Three consequences:

1. **This is *why* the window is hard, structurally.** The Zone Theorems kill `T_e` for `e < q`; the annihilator laws (`A8`) govern low `c`. Both relate a degree to its *distinct* dual. At `d = T` the two coincide, so **no duality-transport argument can reach `T` from either side.** Any plan that hopes to squeeze `T` between the two zones is dead before it starts — they meet exactly there and never overlap.
2. The Gorenstein pairing becomes a **form on a single space**, `⟨·,·⟩ : B_T × B_T → B_{2T} ≅ K`, and `V ↦ V^⊥` is an involution on subspaces of `B_T`.
3. Writing `Σ_T := (Σ_J F_J^{q−1}B)_T` — with `Σ ⊆ ann_B(E·B)` unconditional (`E ⊆ I_J`, `F_J^{q−1} ∈ ann(I_J·B)`; cf. `R23`) — and using `dim A_T = dim ann_B(E·B)_T = dim ((E·B)_T)^⊥`, the target reads:

> **`(E·B)_T = (Σ_T)^⊥`** — *the ideal and the Fedder span are exact perps of one another at the self-dual degree.*

The whole remaining conjecture, one line, no thresholds.

---

## 3 · THE ROW-LENGTH LAW

`S_N` permutes the `(2k+1)!!` matchings, hence the generators `F_J^{q−1}`; so `Σ_T` is an `S_N`-quotient of the matching module `M = K[\{J\}]`. Over `ℚ`, `(S_{2m}, H_m)` is a Gelfand pair and `M = ⊕_{λ even} S^λ`, **multiplicity one** — proven and character-certified in the boxing campaign (Round 3), verified `3 / 15 / 105`. Multiplicity-freeness forces every equivariant operator to act as a **single scalar** on each constituent, so **the deficiency must be a union of whole constituents.** That alone is falsifiable, and the data obeys it.

**Reparametrisation (this is the v2 sharpening).** Even partitions `λ ⊢ 2k+2` are in bijection with partitions `μ ⊢ k+1` via `λ = 2μ`, and `ℓ(λ) = ℓ(μ)`. **`k+1` is exactly the dimension of the sheets `L_J`** (`v42 §1`). So every constituent is indexed by a partition of the sheet dimension.

> ### ★ THE ROW-LENGTH LAW (candidate)
> **`S^{2μ}` survives (its eigenvalue is a unit mod 3) if and only if `ℓ(μ) ≤ q`,**
> where `μ ⊢ k+1` partitions the sheet dimension. Equivalently: a constituent dies exactly when it needs more rows than the tower level allows.

### 3.1 · The fit — `4/4`, no free parameters, `q = 3`

| `k` | `μ ⊢ k+1` surviving (`ℓ(μ) ≤ 3`), with `dim S^{2μ}` | **law** | **archived `dim A_T`** | dying `μ` |
|---|---|---|---|---|
| 1 | `[2]`=1, `[1,1]`=2 | **3** | **3** ✓ | — |
| 2 | `[3]`=1, `[2,1]`=9, `[1,1,1]`=5 | **15** | **15** ✓ | — |
| 3 | `[4]`=1, `[3,1]`=20, `[2,2]`=14, `[2,1,1]`=56 | **91** | **91** ✓ | `[1⁴]`=14 |
| 4 | `[5]`=1, `[4,1]`=35, `[3,2]`=90, `[3,1,1]`=225, `[2,2,1]`=252 | **603** | **603** ✓ | `[2,1,1,1]`=300, `[1⁵]`=42 |

Dimensions by hook length; each column sums to `(2k+1)!! = 3, 15, 105, 945`, as it must.

**Honest weighting (Ley 48).** `k = 1, 2` are **vacuous**: no `μ ⊢ 2` or `μ ⊢ 3` has four parts, so the law asserts nothing. The genuine content is two points:

- **`k=3`:** deficit `14`. Two constituents have dimension `14`: `λ=[4,4]` (`ℓ=2`) and `λ=[2⁴]` (`ℓ=4`). The law selects `[2⁴]`. **The campaign's independent three-integer-trace certificate (Round 3) also selected `[2⁴]`** — and it knew nothing of this law.
- **`k=4`:** deficit `342`. The row-length subset `\{[4,2,2,2], [2⁵]\}` sums to `300 + 42 = 342` **exactly**. (`[6,4] ⊕ [4,4,2] = 90 + 252 = 342` also works arithmetically, so the decomposition is not unique — the law forbids it, and that is a test, not a weakness.)

**Two genuine points is not a law. It is a candidate with a kill number (§6).**

### 3.2 · The law returns `R30` — threshold, optimality, and the first casualty

For `μ ⊢ k+1`, `ℓ(μ) ≤ k+1` with equality **only** for `μ = [1^{k+1}]`. Therefore:

> **every constituent survives `⟺ k+1 ≤ q`.**

That is **`R30` verbatim** — `rank Φ_T = (2k+1)!!` for `q ≥ k+1` — a theorem the campaign has **proven `∀k` with the threshold certified optimal**. The law was fitted only to `q = 3` data and was never shown `R30`. It returns:

- the threshold `q ≥ k+1`, exactly;
- **why it is optimal**: at `q = k`, the single constituent `μ = [1^{k+1}]` (i.e. `λ = [2^{k+1}]`) is the first and only one to drop out;
- and at `k=3, q=3` the first casualty is `[2⁴]` — **which is the constituent the character certificate actually found.**

Independent cross-check at a second tower level, from the boxing census `A(k=1, q=9) = [1,3,6,…,6,3]`: at `T = 16`, `dim A_T = 3 = (2k+1)!!`, no deficiency; and `ℓ(μ) ≤ 2 ≤ 9 = q`. Consistent.

### 3.3 · The characteristic-3 caveat, stated where it belongs

Over `F₃` the matching module need **not** be semisimple; `⊕_{λ even} S^λ` is a characteristic-zero decomposition. In char 3 one must speak of composition factors, filtration and radical — not summands. **The law as stated is therefore about ranks and Brauer characters, and its Specht labels are bookkeeping that must be earned over `F₃`, not assumed.** This is exactly the caveat `A5` already carries (*«necesario, no suficiente en característica modular»*), and it is why Round 3 used **integer** traces as its certificate. The correct formulation for a proof: *the operator lies in the Bose–Mesner algebra of the perfect-matching scheme over `F₃`, and its rank is the mod-3 reduction of the zonal spherical eigenvalues.*

---

## 4 · THE CLOSING STATEMENT

In the **entire open window** we have `q ≥ k+1`, so by the law — equivalently by `R30`, already proven — **every constituent survives and `Σ_T` is the full matching module**, `dim Σ_T = (2k+1)!!`. Since `Σ_T ⊆ ann_T` always, the target becomes exactly:

> ### ★ `ann_B(E·B)_T` has no constituent beyond the even-partition ones — as an `S_N`-module it is `≅ M`, multiplicity-free, only even-partition composition factors.

**A dimension inequality over an infinite family becomes a character identity.** Three reasons this is the right shape:

1. **No threshold.** Composition-factor statements carry no `q ≥ ·` hypothesis, so it is legal to state `∀k∀q` and to use `q = 3` as an induction base — exactly what `v42 §7` demands.
2. **Both modules are explicit.** `dim A_T = dim ann_T`; `B = S/m^{[q]}` is a monomial complete intersection with computable `S_N`-character; `E` is generated by the `S_N`-invariant odd elementaries. The only unknown is the character of `(E·B)_T`.
3. **FI finally pays where it should.** `A22` (FI-stability) gives eventual polynomiality in `k` for data at a *fixed* label. Aimed at the census it hit the growing-`e` wall. **Aimed at the constituent index `μ` it does not**: only `μ` of bounded size matter as `k` grows, so infinitely many `k` collapse to finitely many `μ`-families. This target has never been aimed at.

### 4.1 · ★ THE DECISIVE NEGATIVE CONTROL — `R34-bis` rules out the obvious wrong operator

`R34-bis` proves `∀k`: the **unsigned swap incidence has full rank `(2k+1)!!` in char ≠ 2**, verified `k=1..4` as `3 / 15 / 105 / 945`.

Char 3 **is** char ≠ 2. So on the swap incidence **no constituent dies** — `105`, not `91`; `945`, not `603`.

> **Therefore the Gram operator of `Φ_T` is NOT the swap incidence, nor any scalar multiple of it.** Anyone who reaches for the swap incidence as the operator will get `105` and conclude the law is wrong. It is a different element of the same algebra.

This is not a problem for the law — it is the sharpest thing in this document, and it says what kind of object we are hunting:

- the **swap incidence is `q`-free** and full rank;
- **`Φ_T`'s Gram is `q`-dependent** (through `F_J^{q−1}`) and its vanishing locus **moves with `q`**, dying on `ℓ(μ) > q` and on nothing else. As `q → ∞`, nothing dies — consistent with `R33`.

So the object is a **`q`-deformation** inside the Bose–Mesner algebra whose kernel grows as `q` shrinks. That is a much more specific hunt than "compute some eigenvalues", and `R34-bis` is the proof that eigenvalue computations of this type are tractable and provable `∀k` in this campaign.

---

## 5 · THE PROPOSED MECHANISM (conjectural — why an `iff` at exactly `q`)

An arithmetic vanishing (a coefficient divisible by 3) is the wrong shape: with `q = 3^v`, Lucas makes binomials `\binom{q}{j}` vanish mod 3 for *most* `j`, which would kill almost everything. The observed law kills a set that **shrinks as `q` grows** and is empty for `q ≥ k+1`. That is the signature of a **rank obstruction, not an arithmetic one**:

> **Conjectural mechanism.** The constituent `S^{2μ}` is reached only through an alternating (determinantal) expression of size `ℓ(μ)` in the data carried by `F_J^{q−1}`. That data has **rank at most `q`** — the generators are `(q−1)`-st powers, and Frobenius truncates the available alternating depth at `q`. A minor of size `ℓ(μ) > q` in a rank-`≤ q` object vanishes **identically**, not merely mod 3. Hence the `iff`, hence the threshold at exactly `q`, hence the first casualty `μ = [1^{k+1}]` (the fully alternating one), and hence `R30`'s optimality.

If this is the mechanism, the proof is a **rank/determinant argument at the sheet level**, not a character computation — cheaper, and of a species the campaign has closed before (`R30`'s colour budget, `R34-bis`'s incidence rank, `R45`'s Bézout pinning are all rank arguments).

---

## 6 · PRE-REGISTERED NUMBERS (write them down before measuring)

> ### ★ `dim A_T(k = 5, q = 3) = 4213`
> Surviving `μ ⊢ 6` with `ℓ(μ) ≤ 3`: `[6]`=1, `[5,1]`=54, `[4,2]`=275, `[4,1,1]`=616, `[3,3]`=132, `[3,2,1]`=2673, `[2,2,2]`=462. **Sum 4213.**
> Dying (`ℓ(μ) ≥ 4`): `[3,1,1,1]`=1925, `[2,2,1,1]`=2640, `[2,1,1,1,1]`=1485, `[1⁶]`=132. **Deficit 6182.** Total `10395 = 11!!` ✓

**Cheaper secondary test (do this first):** at `(k=4, q=3)` the deficient part is exactly `λ = [4,2,2,2] ⊕ [2⁵]`, by the Round-3 three-trace protocol. The law **forbids** the arithmetic alternative `[6,4] ⊕ [4,4,2]`.

**Tertiary:** at `q = 9`, no deficiency for any `k ≤ 8` (since `ℓ(μ) ≤ k+1 ≤ 9 = q`), i.e. `dim A_T = (2k+1)!!` exactly there.

---

## 7 · HOW TO KILL THIS WITH DATA

- **Any measured deficiency that is not a sum of even-partition Specht dimensions kills the multiplicity-free picture outright.** Nothing survives that.
- **`dim A_T(k=5, q=3) ≠ 4213` kills the Row-Length Law.**
- **A three-trace decomposition at `(k=4, q=3)` returning anything but `[4,2,2,2] ⊕ [2⁵]`** kills it — including `[6,4] ⊕ [4,4,2]`.
- If the Gram operator is **not** in the Bose–Mesner algebra, the eigenvalue reduction is unavailable and only numerology survives — not enough.

---

## 8 · WHAT THIS DOES **NOT** GIVE

- It does **not** prove the target. It restates it as a character identity and pins the shape of one of the two subspaces.
- It does **not** establish `Σ_T = ann_T`. That is the whole remaining content, now with a name.
- The step *«`rank Φ_T = rank G`»* needs the pairing non-degenerate on `Σ_T`; unproven here.
- §3.3 must be discharged before the Specht labels mean anything over `F₃`.
- **Two of four fits are vacuous. This is a two-point law.**
- §5 is a **conjectural mechanism**, offered because a named mechanism is testable and an unnamed one is decoration.

---

## 9 · MANDATORY BEFORE USE (Ley 41, Ley 43) — AND ONE RETRACTION

### 9.1 · Certificate required; I cannot run it

I am **outside** the Chaise Longue project and **cannot grep its cemetery**. Before a single turn is spent:

1. **Certificate by object, not by name.** Grep the live cemetery for: the perfect-matching association scheme · Bose–Mesner / zonal spherical functions · the Gram matrix of the `F_J^{q−1}` · any «Specht decomposition of the top degree» · any «eigenvalue mod 3» route · any prior explanation of the `91`/`603` deficiency. If a tomb touches the same **object**, this is a re-walk in new vocabulary and must be discarded (Ley 22).
2. **Failure-mode annex**, especially `ALIAS-CHAIN`: evaluate any proposed identity at the sealed anchors `3, 15, 91, 603` **before** proposing it. This document does exactly that and passes; anything built on top must too.
3. Load-bearing archive items quoted here from `v42` and from the ten-round campaign — `R30`, `R33`, `R34-bis`, `R23`, `R41`, `A5`, `A22`, and the Round-3 character certificate — should be **re-read in place**, not trusted from my quotation.

### 9.2 · Retraction of an earlier suggestion of mine

In an earlier turn I proposed, as «the Sofá's slap carried to `∀k`», the reduction of `S/E` to fixed matrices over a base ring by Auslander–Buchsbaum. **That is already in the arsenal as `R4`** (*«Libertad de rango: `S/E` LIBRE de rango `(2k+1)!!` sobre `C = K[θ_1..θ_{k+1}]`»*). It was not a new lever; it was a re-identification, which is precisely the failure pattern `v41 §7` diagnoses. **Retracted, and logged as my own instance of it.** The present document is offered in full awareness that it must clear §9.1 or share the same fate.

---

## 10 · ONE LINE

**The top-degree deficiency is not noise: at `q = 3` it is exactly the sum of the constituents indexed by partitions of the sheet dimension having more rows than the tower level allows — `4/4` on archived data — and this single law returns `R30`'s proven optimal threshold `q ≥ k+1`, its optimality, and the identity of the first casualty as corollaries. `R34-bis` proves the naive operator is the wrong one, which tells us the right one is a `q`-deformation whose kernel is a rank obstruction. If it survives `k = 5`, the remaining conjecture is a character identity on two explicit modules — finite, and of the species this campaign has tamed.**

*Not a theorem. Not measured by me. Pending P0, pending cemetery certificate. The word is not said.*

— **Bisel**

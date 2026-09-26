> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-08-18
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE BALANCED LIFTING THEOREM (v2)* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_BALANCED_LIFTING_THEOREM.md
>
> **Status, as written in the document:** |---|---|
>
> **Later audit:** The campaign's later records mention this document next to a refutation, retraction, circularity or supersession (3 lines). Search its name in [the Cemetery](../../archive/CHAISE_LONGUE_CEMENTERIO_LIVE_v502.md) before relying on it.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v2`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE BALANCED LIFTING THEOREM (v2)

### Author: **GETTLER** (auditor) · 18 August 2026 · Chaise Longue campaign
### **v2 opens with a retraction.** In v1 I graded Theorem 2 and the `λ`-identity as new. **They are not.** They are the `∀k` content of the **Recognition Theorem** and of the **T-block decomposition**, both deposited (Sofa Thm 2.1 / Thm 4.1; Hammock Thm 2.1, titled *"Recognition — campaign theorem, all dimensions"*). What survives is a different **proof**, a removed hypothesis, an unrestricted direction, and the measurements. Everything is re-graded below. No other statement is altered, and no number changes.

---

## 0. THE RETRACTION, IN FULL, BEFORE ANYTHING ELSE

**Hammock, Theorem 2.1, verbatim:**
> *"For `deg λ = e < q`: `Σλᵢxᵢ^q ∈ E ⟺ λ_a − λ_b ∈ I({a,b})` for all 28 edges; the window syzygy census `σ_e` is canonically independent of v. (Proof mechanism as in the Sofa: disjoint monomial supports of `u_k^q·m` for `e < q`.)"*

`I({a,b}) = I(V(p)) = ⋂_{J ∋ (a,b)} I_J`. **That is the "balanced" condition of v1 word for word**, and `e < q` is `d = e + q < 2q` — **the same threshold**. So:

| v1 claim | v2 grade |
|---|---|
| **T2** "every box-syzygy of degree `d < 2q` is balanced" — claimed **new** | **RETRACTED as new.** It is the `⟹` of Recognition, deposited in both papers, "all dimensions". |
| **T4** the `λ`-identity `c_p = Σ_{p'} λ^J_{pp'} t_{p'}^q`, `λ` antisymmetric, `deg λ = d−2q` | **RETRACTED as new.** It is the Sofa's **T-block decomposition** (Thm 4.1: `Δ_k = Δ_k^∅ + Σ_l u_l^q δ_{k,l}`, with (i) `Δ^∅=0`, (ii) `δ_{k,k}=0`, (iii) `δ_{l,k} = −δ_{k,l}`), which the Hammock §4 states is *"parametrized to every dimension"*. |
| **T3** finite window `d ≤ (2k+3)(q−1)` | **SUPERSEDED, weaker than filed.** Hammock Thm 1.6 (Confinement): `A_d = 0` for `d > (k+1)(q−1)`, verified exact at `q = 3, 9` in dimensions 2, 4, 6. That narrows the window to `2q ≤ d ≤ (k+2)(q−1)`. |

**What survives the retraction, and its honest grade:**

1. **A different proof of Recognition, char-free and hypothesis-free (`§3`).** Both deposited proofs run on *disjoint monomial supports of the heavy families* — a char-3 monomial argument whose load the Hammock had to shield by exhaustive verification (**H5**: the four heavy families pairwise disjoint for every `e < q`, *"collapse at `e = q` (union `74 < 80`, exactly the collar onset)"*, plus the shared-edge case checked by hand). **The proof below runs instead on the fact that `(t_1^q,…,t_{k+1}^q)` is a regular sequence in `K[t_1,…,t_{k+1}]`.** It is five lines, uniform in `k`, needs no `q ≥ 9`, no monomial trichotomy, and no shared-edge analysis. *Grade: PROOF SIMPLIFICATION of a deposited theorem, not a new theorem.*
2. **The `⟸` direction, unrestricted in degree, plus the lift (`§2`, Theorem 1).** The deposited statement is an `⟺` **only under `e < q`**. Theorem 1 below gives `⟸` in **every** degree, for **every odd exponent** simultaneously, and converts it into an uncorrected lift in the campaign's `ε`-deformation for **every** negation-closed `Λ_q`. *Grade: EXTENSION, PROVED ∀k ∀q odd char ≠ 2. This is the part that survives past the collar onset, which is exactly where the deposited `⟺` stops.*
3. **The two explicit families (`§2.1`, `§2.3`) and the collapse remark (`§2.2`).** *Grade: PROVED; the collapse remark is a scope saver.*
4. **The measurements (`§5`) and the localisation of the residual to the collar.** *Grade: MEASURED, two cells, `F_3`, own engine, with positive controls.*

**Nothing below is withdrawn on the numerical side. The engine and every gate stand unchanged.**

---

## 1. Setup, objects, inputs

`char K = p ≠ 2`; `p = 3`, `q` odd. `n = 2k+2`, `S = K[x_0,…,x_{n-1}]`, `m^{[q]} = (x_i^q)`, `B = S/m^{[q]}`,
`E = (e_1,e_3,…,e_{2k+1})`, `R = S/E`, `A = S/(E+m^{[q]})`.
Sheets `L_J` for perfect matchings `J`; adapted coordinates `x_{a_p} = t_p`, `x_{b_p} = -t_p`.
Every expression used is invariant under `t_p ↦ -t_p` together with swapping the pair, so the choice is immaterial.

Fix `d ≥ q`, `δ = d - q`.
`Z_d = { b ∈ (S_δ)^n : Σ_i b_i x_i^q ∈ E }` · `Triv_d = E·(S_δ)^n + Koszul` · `∂(b) = Σ_i b_i x_i` ·
`Λ := ∂ mod m^{[q]}`, well defined and `S`-linear of degree `-(q-1)` (two representations differ by a Koszul
syzygy of the regular sequence `(x_i^q)`, and `∂(x_j^q e_i - x_i^q e_j) = x_i x_j^q - x_j x_i^q ∈ m^{[q]}`).

> **Definition (BALANCED = the Recognition condition).** `b` is **balanced** if `(b_a - b_b)|_{L_J} = 0` for every
> sheet `J` and every pair `(a,b) ∈ J`; equivalently `b_a - b_b ∈ I(\{a,b\}) = ⋂_{J ∋ (a,b)} I_J` for every edge.

`Bal^+_d := { b ∈ Z_d : ∂(b) ∈ E }`.

**Inputs used as black boxes.** `E = ⋂_J I_J` complete intersection of degrees `1,3,…,2k+1`, **radical**
(`ODD_ELEMENTARY_CI_THEOREM`, PROVED ∀k char ≠ 2) · `p_m = 0` in `R` for odd `m`, all characteristics
(`SYMMETRIC_WRINKLE_LIFT`, Lemma 1) · `φ(T,ε) = ∏_{λ∈Λ_q}(T-λε)` is **odd in `T`**, `φ(T,0) = T^q`, `C` free over `K[ε]`
(`NEGATION_DEFORMATION_THEOREM`) · the conjecture ⟺ every syzygy over `W = S/m^{[q]}` lifts over `C`
(`SYZYGY_LIFTING_THEOREM` v64) · `A_d = 0` for `d > (k+1)(q-1)` (Hammock Thm 1.6).

---

## 2. Theorem 1 — BALANCED LIFTING (the surviving extension)

> ### **Theorem 1.** Let `b` be balanced. Then for **every odd** `m ≥ 1`, `Σ_i b_i x_i^m ∈ E`.
> ### In particular `b ∈ Z_d` (case `m = q`) and `∂(b) ∈ E` (case `m = 1`) — **in every degree, with no upper bound on `d`** — and
> ### `Σ_i b_i · φ(x_i,ε) = 0` in `R[ε]` for **every** negation-closed `Λ_q`: `b` lifts with no correction term.
> **PROVED ∀k, ∀q odd, char ≠ 2.**

**Proof.** On `L_J`, since `m` is odd, `x_{b_p}^m|_{L_J} = -t_p^m`, so
`(Σ_i b_i x_i^m)|_{L_J} = Σ_p t_p^m (b_{a_p} - b_{b_p})|_{L_J} = 0`.
True for every `J`, hence the polynomial vanishes on `⋃_J L_J = V(E)`, hence lies in `E` by radicality.
For the lift: `φ` odd in `T` gives `φ(T,ε) = Σ_j c_j(ε^2)T^{2j+1}`, so
`Σ_i b_i φ(x_i,ε) = Σ_j c_j(ε^2)(Σ_i b_i x_i^{2j+1}) = 0` in `R[ε]`. ∎

*Mechanism, one line: `q` is odd, so `x^q` and `x` have the same parity, and a balanced covector cannot tell them apart.*
*Why the degree restriction of the deposited `⟺` does not appear here: it belongs to the `⟹` direction, whose deposited proof needs the heavy families to be disjoint. The `⟸` direction needs nothing.*

### 2.1 Corollary A — the diagonal even family
`b_i = g(x_i)` with `g` **even** is balanced (`g(-t_p) = g(t_p)`). `g = 1` is `SYMMETRIC_WRINKLE_LIFT_THEOREM_v1`;
`g = T^{2j}` gives `Σ_i b_i x_i^q = p_{q+2j}`, `∂(b) = p_{2j+1}`, both `0` in `R`.
**Cross-check made here for the first time:** these are exactly the generators of `\bar E ∩ \mathfrak b` computed in
`CASING_IMPOSSIBILITY_THEOREM_v2` Lemmas 5.1–5.3 (`rel(0)=rel(1)=0`, `rel(2)=1`, generator `p_{q+2}`;
**declared domain: the reduced ring, `x_0` eliminated by `e_1`**). Hence `Λ(p_{q+2j}) = p_{2j+1} ∈ E` for every `j`, ∀k∀q.

### 2.2 Corollary A′ — the multi-index symmetric sector COLLAPSES
`b_i = Σ_{j_1…j_r} A(x_i,x_{j_1},…)` equals `x_i^{a_0} p_{a_1}⋯p_{a_r}` on monomials, and each `p_a` is `0` in `R`
(`a` odd) or a symmetric scalar (`a` even). Over `R` the whole multi-index sector lies in the `R`-span of Corollary A.
*A turn spent enlarging `r` is a wasted turn.*

### 2.3 Corollary B — the pair family
`b := c·(e_a + e_b)` with `c ∈ ⋂_{J : (a,b) ∉ J} I_J` is balanced. *(On a sheet through `(a,b)`: `c - c = 0`.
On a sheet missing it: `c|_{L_J} = 0`.)* Read off an explicit machine basis of a residual at `(k,q,d) = (1,3,5)`, then proved.

---

## 3. Recognition, reproved by regular sequence (the proof simplification)

> ### **Proposition 2 (= Recognition, `⟹` direction).** Every `b ∈ Z_d` with `d < 2q` is balanced.
> **PROVED ∀k, ∀q odd, char ≠ 2 — deposited result, new proof.**

**Proof.** Let `h = Σ_i b_i x_i^q ∈ E`. On `L_J`, with `c_p := (b_{a_p} - b_{b_p})|_{L_J}` of degree `d-q`,
`0 = h|_{L_J} = Σ_p t_p^q c_p`. Now `(t_1^q,…,t_{k+1}^q)` **is a regular sequence in `K[t_1,…,t_{k+1}]`**, so every
syzygy is Koszul:

  **(λ)** `c_p = Σ_{p'} λ^J_{pp'} t_{p'}^q`, `λ^J` antisymmetric, `deg λ^J = d - 2q`.

If `d < 2q` the degree is negative, so `λ^J = 0` and `c_p = 0`. ∎

**What this buys over the deposited proof.** No monomial trichotomy, no `q ≥ 9`, no shared-edge case, no
characteristic hypothesis beyond `≠ 2`, and the statement is uniform in `k` with no verification burden.
Identity **(λ)** is the Sofa's T-block (Thm 4.1) obtained without its hypotheses: `λ^J_{pp'} = δ_{k,l}^{(J)}`,
antisymmetry included, cofactor degree `d - 2q = f` matching the Sofa's *"cofactor degree ≤ 3"* at `k=2`, `f ≤ 3`.

**Consequences of (λ), unconditional, ∀k∀q:**
* `b` balanced ⟺ `λ^J ≡ 0` for every `J`;
* `∂(b)|_{L_J} = Σ_{p<p'} λ^J_{pp'}(t_p t_{p'}^q - t_{p'} t_p^q)`, so `b ∈ Bal^+` ⟺ this vanishes on every sheet;
* every term carries a factor `t_{p'}^q`, hence **`∂(b) ∈ ⋂_J (I_J B)` always**. *This is consistent with `D = 0` and is **not** a proof of it: the gap between `⋂_J I_J B` and `E·B` **is** GAP 3.*

---

## 4. The window, and the descent route

> **Proposition 3 (window).** Free bound: `2q ≤ d ≤ (2k+3)(q-1)`, from `top(B) = (2k+2)(q-1)`.
> **Filed and sharper (Hammock Thm 1.6, `A_d = 0` for `d > (k+1)(q-1)`):** `2q ≤ d ≤ (k+2)(q-1)`.

> ### ⚠️ **NOTA `2026-09-16` (Grepy, turno 9, informe 137) — «filed and sharper» hay que leerlo con su región:** el confinamiento `A_d = 0` para `d > (k+1)(q−1)` está probado para `q = 3` `∀k`, para `q > k(k+1)` `∀k` (`pending P0`) y para `k ≤ 3`; **en `k ≥ 4`, `9 ≤ q ≤ k(k+1)` está SIN MEDIR** (informe 132). Allí la ventana usable es la libre, `2q ≤ d ≤ (2k+3)(q−1)`.

> *Use the filed bound; quote its declared verification (`q = 3, 9`, dims 2, 4, 6).*

> **Proposition 4 (descent route).** Fix `Λ_q = F_q`, so `φ(T,ε) = T^q - ε^{q-1}T`.
> **If `Λ(E ∩ m^{[q]}) ⊆ E·B` in every degree, then every box-syzygy lifts and `A_k(q) = P_k(q)`.**
> *Proof.* `Σ_i b_iφ(x_i,ε) = -ε^{q-1}∂(b)`; write `∂(b) = e + Σ_i b'_i x_i^q`; then
> `Σ_i (b_i + ε^{q-1}b'_i)φ(x_i,ε) = -ε^{2(q-1)}∂(b')`. Each step lowers the degree by exactly `q-1`; after at most

> ### ⛔ **TACHADO `2026-09-16` (Grepy, turno 9, informe 137) — «Each step lowers the degree … after at most `⌈d/(q−1)⌉` steps … the lift is exact»: PASO NO JUSTIFICADO.** La hipótesis cubre `Λ` sobre `E ∩ m^{[q]}`, pero el segundo paso necesita `∂(b') ∈ E + m^{[q]}`, es decir `Λ(Σb'_ix_i^q) ∈ E·B`, con `Σb'_ix_i^q = ∂(b) − e`. **Ese elemento está en `E` sólo si `∂(b) ∈ E`**, y la tabla del `§5` de este fichero mide `∂(Z) mod E` NO NULO (`3,6,9` en `k=1`; `10,40` en `k=2`). Lo que está justificado es UN paso: el levantamiento módulo `ε^{2(q−1)}`. **No es una refutación: la implicación puede ser cierta con otra hipótesis más fuerte (p. ej. sobre todo `Λ(m^{[q]}) ∩ …`), pero no está escrita.** Está copiada como criterio en `VIVOS/EL_CATALOGO_MAESTRO` y en `VIVOS/THE_CHAISE_LONGUE_THEOREM_MASTER_ASSEMBLY`.

> `⌈d/(q-1)⌉` steps the degree falls below `q`, where `m^{[q]}` vanishes, and the lift is exact. ∎
> *Only `⟸` is claimed. Grade: corollary of `SYZYGY_LIFTING` with an explicit termination count.*

Because `Λ` is `S`-linear, the criterion needs checking **only on a generating set of `E ∩ m^{[q]}`**, whose bottom is
filed and already passes (§2.1).

---

## 5. Gates — own engine, `F_3`, `CHAISE_LONGUE_BALANCED_GATE_v1.py` (unchanged from v1)

**Positive controls, declared before the verdicts, all passed:** `#sheets = (2k+1)!!` (`3`, `15`) ·
`A_1(3) = 19`, `HF = 1,3,6,6,3` · `A_2(3) = 141`, `HF = 1,5,15,29,40,36,15` · `dim Z_q = 1` and the covector is
`(1,…,1)`, i.e. the engine independently rediscovers the invariant syzygy of `SYMMETRIC_WRINKLE_LIFT` ·
`Bal ⊆ Z` in every degree · `rank(Z ∪ Triv ∪ Bal^+) = rank Z = 511` at `(2,3,7)`.

**`k = 1, q = 3`** — residual vs `Triv+Bal` and vs `Triv+Bal^+`:

| `d` | `dim Z` | `dim Triv` | `H_1` | `dim Bal` | resid `Bal` | resid `Bal^+` | `∂(Z)` mod `(E+m^{[q]})` | `∂(Z)` mod `E` |
|---|---|---|---|---|---|---|---|---|
| 3 | 1 | 0 | 1 | 1 | 0 | 0 | 0 | 0 |
| 4 | 7 | 4 | 3 | 7 | 0 | 0 | 0 | 0 |
| 5 | 25 | 16 | 9 | 25 | 0 | 0 | 0 | 0 |
| 6 | 62 | 50 | 12 | 59 | 0 | 0 | 0 | 3 |
| 7 | 119 | 110 | 9 | 113 | 0 | 0 | 0 | 6 |
| 8 | 200 | 197 | 3 | 191 | 0 | 0 | 0 | 9 |

**`k = 2, q = 3`:**

| `d` | `dim Z` | `dim Triv` | `H_1` | `dim Bal` | resid `Bal` | resid `Bal^+` | `∂(Z)` mod `(E+m^{[q]})` | `∂(Z)` mod `E` |
|---|---|---|---|---|---|---|---|---|
| 3 | 1 | 0 | 1 | 1 | 0 | 0 | 0 | 0 |
| 4 | 11 | 6 | 5 | 11 | 0 | 0 | 0 | 0 |
| 5 | 52 | 36 | 16 | 52 | 0 | 0 | 0 | 0 |
| 6 | 181 | 147 | 34 | 171 | 0 | 0 | 0 | 10 |
| 7 | 511 | 441 | 70 | 456 | **5** | **1** | 0 | 40 |

**Readings, and only these:**
1. `dim Bal = dim Z` exactly for `d < 2q`, strictly less from `d = 2q` — Recognition confirmed on **both** sides,
   and the threshold reproduced by a second instrument (`∂(Z) mod E` = `0,0,0` then `3,6,9` / `10,40`).
   *This is the same collapse the Hammock measures at `k=3` as `74 < 80` at `e = q`.*
2. `∂(Z) ≡ 0 mod (E+m^{[q]})` in every measured degree — the hypothesis of Prop. 4 holds where measured.
   *Both cells already have `A = P`; this is a consistency check, not evidence for `∀k`.*
3. **The pre-registered death criterion fired.** *"If `dim Z_d - rank(Triv_d + Bal_d) > 0` in any degree, the
   hypothesis «the syzygy module is generated by balanced covectors» dies with that number."* **It died: `5` at
   `(2,3,7)`.** Enlarging to `Bal^+` shrinks it to **`1`**, reproduced with two elimination orders (`510` both ways).
4. **The residual sits inside the collar.** `d = 7 = 2q+1`, i.e. `f = 1`, and the collar is `2q ≤ d` (Sofa: four
   degrees at `k=2`; Hammock: **grows with `q`** at `k=3`). At `k=1` no residual appears through `d = 8`.
   *Measured `d ≤ 7` at `k=2`; `d = 8, 9` not measured, and no law is proposed for the residual dimension (Ley 12).*
5. `Z`, `Triv`, `Bal`, `Bal^+` are `S_n`-stable, so the residual line at `(2,3,7)` is a one-dimensional
   `S_n`-representation over `F_3`: **`S_n` acts by a linear character, trivial or sign.**

---

## 6. Scope

This closes nothing. It reproves a deposited theorem more cheaply, extends its `⟸` direction past the degree where
the deposited statement stops, supplies two explicit liftable families, and **locates the obstruction as the collar** —
the zone both deposited papers identify as the only one that resists, and for which both papers carry machinery
(Sofa: aggregate factoring + rank certificate `dim D_f = 10 + 45C(f+1,2)`, `rank A_f = 45,180,405,720`; Hammock:
crude Koszul ceiling minus a slack law assembled stratum by stratum). `G = 3`.

## 7. Provenance

Recognition and the T-block decomposition: Sofa Thms 2.1 / 4.1, Hammock Thm 2.1 (deposited, DOI 10.5281/zenodo.21382543).
Confinement: Hammock Thm 1.6. The `ε`-deformation and syzygy lifting: `NEGATION_DEFORMATION_THEOREM`,
`SYZYGY_LIFTING_THEOREM` v64 (Orfila). Theorem 1 and its corollaries, the regular-sequence proof of Proposition 2,
Propositions 3–4 and all measurements: this document. The v1 novelty grades on T2, T3 and T4 are retracted above.

— GETTLER, Chaise Longue campaign.

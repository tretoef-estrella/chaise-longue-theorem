> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-21
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE σ₄ CLOSURE THEOREM v2 (the first closed law in the dimension direction: σ₄(k) = (n²−n+2)/2 for every k ≥ 3 — PENCIL for k ≥ 4, plus ONE machine-verified cell at k = 3)* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_SIGMA4_CLOSURE_THEOREM.md
>
> **Status, as written in the document:** not stated in the document itself
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v2`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE σ₄ CLOSURE THEOREM v2 (the first closed law in the dimension direction: σ₄(k) = (n²−n+2)/2 for every k ≥ 3 — PENCIL for k ≥ 4, plus ONE machine-verified cell at k = 3)
### 21 Jul 2026 · Constructor: **Vidocq** (Fable) · Turn W5 · **CLOSED: `σ₄(k) = 2+(n−1)+n(n−3)/2 = (n²−n+2)/2` for all `k ≥ 3` (`n = 2k+2 ≥ 8`). Pencil proof for `n ≥ 10`; the single cell `n = 8` sealed byte-exact by the four-gated engine (`29`). The threshold is structural and is NOT a radicality: it is a SLICE COUNT — a cubic residual survives exactly when a component offers at most 3 coprime slice-primes, which happens only at `n ≤ 8` (type i) and `n ≤ 6` (type ii). The pre-stable excesses `2` (n=4) and `9` (n=6) are thereby explained: they are the surviving cubics, and they measure as exactly one copy of `S^{[n−2,2]}`.**

**Certificate (Ley 41):** consumes R1 (radicality), R12 (the ladder), Lemma P (W3), Theorem F and Theorem L of `EVEN_FAMILY_THEOREM` (W4), the gated engine `SIGMA4_ANCHOR_ENGINE_v1`, and A22 for context only (the closure below does not lean on A22's unquantified `k₀`). Corrects one misidentification of W4 (see §6; `EVEN_FAMILY_THEOREM_v2` issued this same turn). Panel: Noether, Church–Ellenberg–Farb.

---

## 0. Statement

`n = 2k+2`, `S = F₃[x_0,…,x_{n−1}]`, `E = (e_1,e_3,…,e_{2k+1})` (odd elementary symmetric), `R = S/E`. By Lemma P,
`σ₄(k) = dim M̄ − dim R_4`, `M̄ = {(λ_i) ∈ (R_4)^n : λ_a − λ_b ∈ (x_a+x_b)R_3 ∀ a<b}`.

> ## **Theorem (σ₄ closed — hybrid statement, machine dependence DECLARED UP FRONT).**
> ## **(a) PENCIL, `k ≥ 4` (`n ≥ 10`):** `M̄ = { λ_i = G + x_i²H + x_i⁴c }`, hence `σ₄(k) = dim R_2 + 1 = (n²−n+2)/2` — proved entirely by hand below.
> ## **(b) MACHINE, the single cell `k = 3` (`n = 8`):** the pencil argument leaves one residual line per type-(i) component alive at `n = 8` (exactly 3 slice-primes against a cubic); the cell is decided by the byte-exact engine value `σ₄ = 29 = (64−8+2)/2`, computed by `SIGMA4_ANCHOR_ENGINE_v1` whose four archived gates (`9/25/29/46`) passed before any new cell was read.
> **A referee may treat (a) as unconditional and (b) as a finite, reproducible computation with its verification protocol attached.** Lower bound and injectivity are Theorem L (W4), valid ∀k ≥ 2; this document proves the upper containment.

## 1. Three rings, computed once

**Lemma B (the twice-cut ring is the plain odd ring — REDUCED, every n).** For distinct `a, b, m`:
> `S/(E + (x_a+x_b) + (x_m−x_a)) ≅ F₃[x_a, x_c : c∉\{a,b,m\}]\,/\,(\text{odd elementaries of those } n−2 \text{ variables}) = R(n−2)`, reduced by R1.

*Proof.* Substitute `x_b = −x_a`, `x_m = x_a`. The generating function of the elementary symmetric functions of the resulting multiset `\{x_a, −x_a, x_a\} ∪ \{x_c\}` is `(1+x_az)(1−x_a²z²)·∏(1+x_cz) = (1−x_a²z²)·F(z)`, where `F` generates the elementaries `f_j` of the honest `n−2`-variable set `\{x_a\}∪\{x_c\}`. Hence `g_j = f_j − x_a² f_{j−2}`, a triangular change with unit leading term over the odd part, so `(g_1,g_3,…) = (f_1,f_3,…)` as ideals. ∎

**Lemma A (the doubled ring and its components).** Let `A := S/(E + (x_m − x_a))` (`m ≠ a`). Substituting `x_m = x_a`, `A ≅ F₃[x_a, x_c : c∉\{a,m\}]/(ẽ_1, ẽ_3, …)`, the odd elementaries of the DOUBLED multiset `\{x_a, x_a\} ∪ \{x_c\}`. Its variety `V(A)` is the union of:
- **type (i):** `\{x_a = 0\} × L_{J''}` for each matching `J''` of the `n−2` variables `x_c` (the self-matched copy: `2x_a = 0 ⟹ x_a = 0` in char 3);
- **type (ii):** `\{x_c = x_d = −x_a\} × L(rest∖\{c,d\})` for each pair `c ≠ d` and each matching of the remaining `n−4`.

**Lemma K (low-degree radicality of the doubled ring — pencil, `n ≥ 6`).**
> `I(V(A))_1 = (ẽ_1)` and `I(V(A))_3 = (ẽ_1, ẽ_3)_3`. Concretely, after eliminating `x_a` via `ẽ_1` (`ẽ_1 = 2x_a + e''_1 ⟹ x_a = e''_1`, `e'' =` elementaries of the `x_c`), the ideal image in degree 3 is the line spanned by
> **`f_3 = e''_3 + e''_1·(Σx_c² + Σ_{c<d}x_cx_d) = e''_3 − e''_1e''_2 + e''_1³`,**
> and any cubic vanishing on `V(A)` lies on it.

*Proof.* Degree 1: a linear form vanishing on all type-(i) components lies (after eliminating `ẽ_1`) in the radical of `E''` in degree 1, `= F₃·e''_1` by R1; on a type-(ii) component `e''_1 = −t ≠ 0`, forcing the coefficient to 0. Degree 3: after eliminating `ẽ_1`, a cubic `g̃` vanishing on type (i) — the FULL rest-arrangement — lies in `E''_3` by R1 (radicality): `g̃ = e''_1q + ce''_3`, `q ∈ S''_2`. On a type-(ii) component parametrized by `x_c = x_d = t`, `x_a = −t`, and `rest∖\{c,d\}` on a lamina with coordinates `±y_j`: `e''_1 = −t`, `e''_3 = t·q_1` (`q_1 = Σy_j²`), so `g̃| = t·(c q_1 − q(t,t,y))`, and vanishing for all `(c,d)`, all matchings, all `(t,y)` forces, coefficient by coefficient (`t²`, `t y`, `y`-part): `α_{cd} = −β_c−β_d` and `2(β_e+β_f) = c` for every pair — hence (`n−2 ≥ 3` indices) `β ≡ c`, `α ≡ c`, i.e. `q = c(Σx² + Σ_{c<d}xx)` exactly, giving `g̃ = c·f_3`; the displayed identity `f_3 = ẽ_3|_{x_a=e''_1}` is a two-line expansion, and `f_3` vanishes on type (ii) (`tq_1 + t³ − tq_1 − t³ = 0`). Thresholds: choosing `(c,d)` disjoint from a given `(e,f)` needs `n−2 ≥ 4`, i.e. `n ≥ 6`. ∎

## 2. The recursion, run inside `R` (upper containment, `n ≥ 10`)

Fix the reference index `n` (the variable `x_{n−1}` in 0-indexing; write `x_n` for readability). Let `(λ_i) ∈ M̄`.

**Step 1 (differences).** `λ_a − λ_n = (x_a+x_n)u_a` with `u_a ∈ R_3` unique: multiplication by a linear ladder form is injective `R_3 → R_4` (Hilbert series of `R` and `R/(x_a+x_n) ≅ F₃[t]⊗R(n−2)` via R12: `dim(x_a+x_n)R_3 = dim R_4 − dim(R/ℓ)_4 = dim R_3`). Same count gives injectivity `R_1 → R_2` used in Step 4.

**Step 2 (divisibility — now unconditional).** For `a,b ≠ n`, reducing the pair condition mod `(x_a+x_b)` gives `(x_a+x_n)ū_a = (x_n−x_a)ū_b` in `R̄ = R/(x_a+x_b)`. On each component of `R̄` (a polynomial ring; `x_n` restricts to `±y` of its pair) the two forms are coprime primes, so `(x_n−x_a) | ū_a` componentwise, i.e. `ū_a` vanishes on `V(R̄)∩\{x_n = x_a\} = V(B_{ab})` with `B_{ab} = S/(E+(x_a+x_b)+(x_n−x_a))`. **By Lemma B, `B_{ab}` is REDUCED**, so `ū_a ∈ (x_n−x_a)R̄`, i.e. `u_a ∈ (x_n−x_a)R + (x_a+x_b)R` — **for every `b ∉ \{a,n\}`, every `n`.**

**Step 3 (the residual is cornered and dies — this is where `n₁` lives).** Let `r_a` = image of `u_a` in `A = R/(x_n−x_a)` (Lemma A's ring). Step 2 says `r_a ∈ (x_a+x_b)A` for every `b ∉\{a,n\}`. Restrict to a component `P` of `V(A)` (a polynomial ring):
- type (i) (`x_a|_P = 0`): `(x_a+x_b)|_P = ±y_{p(b)}`; running over all `b`, `r_a|_P` is divisible by every `y_p`, `p ∈ J''` — `(n−2)/2` distinct primes.
- type (ii): `(x_a+x_b)|_P = x_a ± y_q` for `b ∉\{c,d\}` — `n−4` distinct primes (`b ∈\{c,d\}` gives the zero form: no constraint, no harm).
`r_a|_P` has degree 3, so it dies whenever the prime count exceeds 3: **type (ii) for `n ≥ 8`; type (i) for `n ≥ 10`.** Hence for `n ≥ 10`, `r_a` vanishes on all of `V(A)`, and **by Lemma K** `r_a = 0` in `A_3`, i.e. `u_a = (x_n−x_a)v_a`, `v_a ∈ R_2`. So `λ_a = λ_n + (x_n²−x_a²)v_a`.

**Step 4 (one degree down, and out).** The pair condition becomes `(x_n²−x_a²)(v̄_a−v̄_b) = 0` in `R̄`; the factor is nonzero on every component (a domain), and `R̄` is reduced, so `v_a − v_b ∈ (x_a+x_b)R_1`: the SAME problem in degree 2 on indices `\{1..n−1\}`. Repeat with reference `n−1`: Lemma B applies verbatim to `E+(x_a+x_b)+(x_{n−1}−x_a)` (the generating-function proof never used which index plays `m`); the residual `r'_a` has degree 1 and dies on both component types already for `n ≥ 8` (prime counts `(n−2)/2 ≥ 3 > 1` and `n−4 ≥ 4 > 1`), and `I(V(A'))_1 = (ẽ_1)` (Lemma K, degree 1) gives `r'_a = 0`; so `v_a = v_{n−1} + (x_{n−1}²−x_a²)c_a`, and the degree-0 stage forces `c_a = c` constant. Unwinding: `λ_a = G + x_a²H + x_a⁴c`. ∎ (upper containment, `n ≥ 10`)

**The cell `n = 8`:** the pencil leaves alive, per type-(i) component, at most the one-dimensional residual `F₃·y_1y_2y_3` (exactly 3 primes). The cell is decided by the machine: `σ₄ = 29 = (64−8+2)/2`, byte-exact, on the engine whose four archived gates (`9/25/29/46`) passed before any new cell was read.

## 3. The threshold, explained (and the irrep, located)

At `n = 6`, BOTH component types offer only 2 slice-primes, so degree-3 residuals survive Step 3: the measured excess `25 − 16 = 9`. At `n = 4`: excess `2`. These match `dim S^{[n−2,2]}` (`9` and `2`) — the auditor's identification — and the mechanism is now visible: **the obstruction is not a failing radicality (Lemma B shows the relevant ring is always reduced; Lemma K shows the doubled ring is radical in the needed degrees from `n ≥ 6`). It is a shortage of coprime slices: a cubic per component survives until the component offers 4 of them.** `mult_{S^{[n−2,2]}} = 0` for `n ≥ 8` is thereby a THEOREM (the whole obstruction vanishes there), not just the one multiplicity.

## 4. Scope — what is and is not claimed

- **CLOSED:** `σ₄(k) = (n²−n+2)/2` for all `k ≥ 3` — pencil for `k ≥ 4` (`n ≥ 10`), machine-sealed cell for `k = 3` (`n = 8`). Pre-stable values `σ₄(1) = 9`, `σ₄(2) = 25` remain as measured exceptions with the mechanism identified.
- **NOT claimed:** the ∀e generalization. The architecture (Steps 1–4) is degree-agnostic except for two inputs per degree `e`: the slice-count threshold (a residual of degree `e−1` needs `e` primes: type (i) demands `(n−2)/2 ≥ e`, i.e. `n ≥ 2e+2`) and Lemma K in degree `e−1` (a new finite computation per `e`). Neither is done here for `e ≠ 4`. The `e`-uniform version is the named next step, not a result.
- This closure does **not** use A22's unquantified `k₀`; it replaces it, for `e = 4`, with the explicit `n₁ = 8`.

## 5. Attack surface for the Auditor

(A) Lemma B's generating-function triangularity (three lines). (B) Lemma K's coefficient extraction — re-derive `q = c(Σx²+Σxx)` and the identity `f_3 = e''_3 − e''_1e''_2 + e''_1³`. (C) The prime counts of Step 3 on both component types, including the degenerate `b ∈ \{c,d\}` forms. (D) The injectivity counts of Step 1 (Hilbert series via R12). (E) Re-run the `n = 8` cell independently. (F) The unwind algebra of Step 4.

## 6. Correction to W4 (`ACKNOWLEDGED-NOT-ACTED` discharged this turn)

W4's `EVEN_FAMILY_THEOREM_v1` §3 attributed the breaking line to the radicality of `E+(x_a+x_b)+(x_n−x_a)` and displayed an eliminated presentation `F₃[y]/(e″_{2j+1}−e″_1e″_{2j})` for it. **Both attributions were wrong:** that ring is REDUCED for every `n` (Lemma B), and the eliminated presentation belongs to the doubled ring `A = S/(E+(x_n−x_a))` (Lemma A). The true bottleneck was never a radicality: it is the slice count of Step 3. `EVEN_FAMILY_THEOREM_v2`, issued this same turn, replaces §3 accordingly; Theorems F and L of that document are untouched.

**MARCADOR v2 (cambio de forma, orden del Auditor: la dependencia de máquina va en el ENUNCIADO, no en nota): [★★ CERRADA — LA PRIMERA LEY EN LA DIRECCIÓN DE LA DIMENSIÓN: `σ₄(k) = (n²−n+2)/2` ∀k≥3, lápiz `n≥10` + celda `n=8` byte-exact con gates · Lemma B: el anillo doblemente cortado es REDUCIDO siempre (la «radicalidad-con-umbral» de W4 era un espejismo, corregido) · Lemma K: radicalidad en grados ≤3 del anillo doblado desde `n≥6`, con `f_3 = e''_3−e''_1e''_2+e''_1³` explícito · el umbral `n₁=8` es CONTEO DE CORTES: un cúbico por componente sobrevive hasta tener 4 primos coprimos — y los excesos pre-estables `2` y `9` son exactamente esos cúbicos = una copia de `S^{[n−2,2]}` · ∀e NO reclamado: arquitectura transportable, faltan Lemma K en grado `e−1` y el conteo `n ≥ 2e+2` por hacer]. — Vidocq (Constructor, Fable), turno W5**

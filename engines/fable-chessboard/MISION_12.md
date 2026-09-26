# MISSION 12 — THE SECOND FAMILIES. THE CASILLA BROKE AT n = 7, AND THE BREAK HAS A NAME.
*(Grepy el Lector, auditor, 2026-09-23.)*

**You are a NEW Fable. This file is SELF-CONTAINED: read it whole before anything else; you need nothing else.** The reports `INFORME.md` … `INFORME_11.md` in this folder are audited and APPROVED. Open them only to quote a proof summarised here. Their scripts may be reused (`m11lib.m2`, `r6.m2`, `r9.m2`, `r10.m2`, `fibre.py`, …). **Four engines of the auditor are here for you** (§1.6):
- `grepy_casilla_verdadera.py`: the TRUE casilla, certified, in seconds;
- `grepy_filas_verdaderas.m2`: the TRUE rows of a TRUE parent;
- `grepy_polys.py` and `grepy_tres_letras.py`: exact polynomial identities over `ZZ`;
- `grepy_vigia.sh`: the watchdog you MUST use.

> **OBJECTIVE of the campaign: the complete closure of Conjecture 1.2 of Degtyarev–Shimada, for all `k` and all `q = 3^v`.**
>
> **Where we stand — every item verified by the auditor, by a second route:**
> - The conjecture is ONE induction on the number of variables over explicit ideals («casillas») `K_μ(n)`, indexed by an imbalance profile `μ`. Only **row inclusions** are needed (§2).
> - **Last mission proved, with letters** (§3.1):
>   - value-0 and new-class for every `(1^ℓ)`;
>   - value-0, new-class, all lower rows and the large raise for every hook `(m,1^{ℓ−1})`;
>   - every leaf row of every profile, in any characteristic;
>   - 22 of the 26 kinds of row inclusions of row `k = 4` that INFORME_11 listed (but see §4 PART C (iv): two rows it took as proved are not).
> - **But those theorems are about the UNIFORM casilla, and the auditor has now found that THE UNIFORM CASILLA IS FALSE** at `(1,1)`, `n = 7` and `n = 8`, and at `(2,2)`, `n = 7` (`q = 9`). It is too small: its colength exceeds the fibre (§3.2). The row lemmas cannot all hold there, and they don't: rows 0 and 7 of `(1,1)` at 7 fail, and so do rows 0, 2 and 7 of `(2,2)` at 7.
> - **And the break has a name. Each failure is repaired, EXACTLY, by ONE explicit family** (the certified true casilla is the uniform one plus it):
>   - `(1,1)`: **`F2_{ab;cd} := (y_ay_b)^{q−2}·e_{f−1}(y∖{y_c,y_d})`** — two heavy letters;
>   - `(2,2)`: **`H_{j;k;l} := y_j^{q−2}·y_k²·e_{f−1}(y∖{y_k,y_l})`** — a squared letter.
>   One of them is visibly the source of what the last Fable could not prove: **the raise row of `(1,1)` gets its missing monomials `T_{b;cd}` from the lowest `z`-term of `F2_{zb;cd}`** (§3.3).
> - ⟹ **The object of the four row lemmas is the CORRECTED casilla, `K_μ(n) = (uniform) + (second families)`, and nobody knows its general law yet.**
>
> **This mission: find the law of the second families, prove they belong, and close row `k = 4` with the corrected casilla.**
>
> **Prize ladder:**
> - **MINIMUM:** the LAW of the second families for `ℓ = 2` written with `n`, `q` as letters (§3.3bis gives a candidate), gated AS IDEALS by the certifier on every cell it reaches — including at least one cell predicted BEFORE measuring — plus a proof with letters that `(y_c², y_a^{q−2})·D_{j;cd} ⊆ gr I(W)` for `(1,1)` and every `n`, `q`.
> - **GOOD:** **ROW `k = 4` CLOSED FOR ALL q WITH THE CORRECTED CASILLA** — every row inclusion that `A_4(q) = P_4(q)` needs, including `(1,1)` at `n = 7` and `n = 8` and the NEW obligations the second families create (§4 PART C), each PROVED with `q` a letter. **It is the first new row of the conjecture since `k = 3`.**
> - **EXCELLENT:** the corrected casilla and all four row lemmas for every two-part profile, every `q`.
> - **FULL:** **every profile ⟹ CONJECTURE 1.2 CLOSED FOR ALL `k` AND ALL `q`.** If you get there, say it in your FIRST LINE, in capitals, with the full chain.
>
> **This is a hunt with the prey in sight.** You have two members of the unknown family, written down and certified, a certifier that answers in seconds, and a proof method that worked twice in two turns (Lemma G, §3.1). The last Fable located the gap exactly; the auditor found what fills it at two cells. **Find why it is there, and where else it must be. Bite and do not let go.**

---
## 0 · RULES OF THE TURN (mandatory)
1. **BEFORE THINKING:** create `INFORME_12.md` with these empty sections: `## FIRST LINE` · `## STEP 0 — DESIGN AND SEALED BETS` · `## STEP 1` · `## STEP 2` · `## STEP 3` · `## STEP 4` · `## STEP 5 — VERDICT` · `## WHAT I FOUND BEAUTIFUL` · `## FOR MISSION 13`.
2. **Save to disk after every step.** What is not written does not exist. If your session is cut, what is on disk IS your delivery.
3. **Header per step:** `STATE: CLOSED | EXHAUSTED | NOT CONCLUDED` and `NEXT:`.
4. **Timing:** work in order, no going back, no retries. Write the budget before each step. After 10 minutes without progress: stop, write, declare. Keep the last 20 % of each budget for writing.
5. **At most one literature search per step**, in the original source.
6. **Do not recompute anything listed here as proved or measured** (§3). Re-gating a CLOSED FORM of yours on a measured cell is allowed and expected.
7. **A negative dimension, or one larger than the box, is a bug:** stop.
8. **«This route dies, for this reason» is a result.** A falsified sealed bet is worth more than a safe hit.
9. **Write ONLY in `~/Desktop/FABLE_TABLERO/`. Do not open anything in `~/Desktop/ARBOLYAML/`.**
10. **Machine and guardrail — EVERY engine runs inside the watchdog:** `zsh grepy_vigia.sh LOGFILE 'the whole command'` (the LOG is the FIRST argument). It kills at **1.2 GB of RSS (whole process tree) or 600 s**; the last line of the log says how it ended. `wd.sh` (time only) is retired.
    - **Write the estimate in the report BEFORE each run, engine by engine.** (Last turn five runs started without one: do not repeat it.)
    - You MAY run TWO engines at once if their estimates add up to less than 1.2 GB. **Any run estimated above 30 s runs ALONE.**
    - After any kill, check with `pgrep` that it is gone and write that you checked. When you finish, check that nothing of yours runs.
    - M2 reserved names abort scripts (`check`, `top`, `info`, `run`, `hh`, `degree` as a variable, …): prefix your own names (`cl…`). Building `R/I` REBINDS variable names: re-`use` the ring you mean.
    - **Allowed (Gröbner, M2 or Singular):** `n ≤ 10` variables at `q = 3`; `n ≤ 7` at `q = 9`; `n ≤ 5` at `q = 27`; `n ≤ 4` at `q = 81`. The certifier counts `t` as a variable, so `n ≤ 7` at `q = 9` means `(y_1..y_7, t)`: allowed. **Pure-Python polynomial identities (no Gröbner) are allowed at any size that fits the caps.**
    - **Forbidden:** any Gröbner run with `n ≥ 8` at `q = 9`, or `n ≥ 6` at `q = 27`. (The auditor tried `(1,1)` at `n = 8`: the certifier was killed at 601 s and `K + F2` hit the memory cap. At `n = 8` you work with letters.)
    - **Known costs (q = 9):**
      - certifier (standard basis only / with the family tests): `(1,1)` n = 7: 18–24 s / 30 s; `(2,2)` n = 7: 40 s / 110 s; `(1,1,1)` n = 7: 50 s / 72 s;
      - full Gröbner basis of a uniform casilla at `n = 7` in M2 over `ZZ/3`: 0.5–40 s;
      - `quotient(K, z^a)` at `n = 7`: 1–130 s per row;
      - M2 on the INHOMOGENEOUS fibre ideal with `DegreeLimit`: useless for certification (truncation is unsafe; 580 s without result).
11. **In characteristic 3, never average over a group whose order is divisible by 3.** Make a certificate canonical by REDUCTION, not by averaging. Read certificates from a SMALL ANSATZ, never from a raw syzygy normal form.
12. **Re-read the disk before the verdict.**
13. **Double check:** every PROVED claim carries its proof in the report; every number its cell and its log; every identity used in a proof is checked exactly (symbolically, or on ALL points of the set it is claimed on); **every casilla is gated AS AN IDEAL against the certified true one.**

**FIRST LINE** (answer first, in this order):
- (a) The LAW of the second families: what are they, for which `(μ, n, q)` are they needed, and on how many cells is the law gated as an ideal?
- (b) Is `F2 ⊆ gr I(W_{(1,1)}(n))` PROVED with letters? And `H ⊆ gr I(W_{(2,2)}(n))`? One sentence each: the vanishing function whose top form it is.
- (c) Row `k = 4` with the corrected casilla: how many row inclusions remain OPEN, of how many kinds?
- (d) Does anything close row `k = 4` or the conjecture? YES or NO, with the reason in one line.

---
## 1 · THE OBJECTS
### 1.1 Basics
`q = 3^v`, `h := (q−1)/2`, `S_n := F_q[x_1..x_n]`. `e_r` is the elementary symmetric polynomial (`e_0 = 1`; `e_r = 0` for `r < 0` or `r >` the number of variables). `box := (x_1^q, …, x_n^q)`. **`I^{(n)} := (e_1, e_3, e_5, …) + box`.** `x_C := Π_{i∈C}x_i`; `x_A^{q−1} := Π_{i∈A}x_i^{q−1}`. `gr I(X)` is the ideal of top forms of the polynomials vanishing on `X ⊆ F_q^n`; **for a finite set, `dim S_n/gr I(X) = |X|`.**

### 1.2 Profiles and fibres
A multiset `S ⊂ F_q` (the **anchor**) constrains `y ∈ F_q^n` by «`y ∪ S` is closed under negation». Its **profile** `μ = (μ_1 ≥ … ≥ μ_ℓ)` has one positive part per non-zero class `{s,−s}`: how many more copies of `−s_i` than of `s_i` the point `y` must carry. `|μ| := Σμ_i`, `ℓ := ℓ(μ)`, **`f := n − |μ|`**.
- **`W_μ(n) := {y ∈ F_q^n : y ∪ S closed}`**, up to bijection a function of `μ`; empty iff `|μ| > n` or `ℓ > h`.
- **Fibre sizes** (`fibre.py`): with `I_m(t) := Σ_{b≥0} t^{2b+m}/(b!(b+m)!)`, `|W_μ(n)| = n!·[t^n] E(t)·Π_iI_{μ_i}(t)·I_0(t)^{h−ℓ}`, `E = cosh` if `f` even, `sinh` if `f` odd. Re-counted by the auditor by multinomials over count vectors (no EGF).
- **Gates at `q = 9`, `n = 0..9`:**

| `μ` | `n = 0 … 9` |
|---|---|
| `∅` | 1, 1, 9, 25, 217, 921, 7761, 41889, 345465, 2162617 |
| `(1)` | 0, 1, 2, 24, 88, 855, 4266, 37947, 227144, 1930329 |
| `(2)` | 0, 0, 1, 3, 46, 210, 2340, 13496, 130984, 868680 |
| `(1,1)` | 0, 0, 2, 6, 84, 380, 3930, **22302**, **204456**, 1329624 |
| `(2,1)` | 0, 0, 0, 3, 12, 200, 1080, 12390, 79408, 779436 |
| `(3,1)` | 0, 0, 0, 0, 4, 20, 390, 2450, 31248, 223776 |
| `(2,2)` | 0, 0, 0, 0, 6, 30, 570, **3570**, 44380, 315756 |
| `(3,2)` | 0, 0, 0, 0, 0, 10, 60, 1295, 9240, 125496 |
| `(1,1,1)` | 0, 0, 0, 6, 24, 360, 1920, 20370, 128016, 1189944 |
| `(2,1,1)` | 0, 0, 0, 0, 12, 60, 1020, 6300, 72240, 502992 |
| `(2,2,1)` | 0, 0, 0, 0, 0, 30, 180, 3360, 23520, 286020 |
| `(1,1,1,1)` | 0, 0, 0, 0, 24, 120, 1800, 10920, 115920, 789264 |
| `(2,1,1,1)` | 0, 0, 0, 0, 0, 60, 360, 5880, 40320, 453600 |

- **Fibre recursion (last coordinate `v`):** `|W_μ(n)| = Σ_{v∈F_q}|W_{μ+v}(n−1)|`: `v = 0` keeps `μ`; `v = −s_i` LOWERS `μ_i`; `v = +s_i` RAISES `μ_i`; `v` in an unused class APPENDS a part `1`.
- **The fibre ideal (PROVED):** with `R_j := Σ_{r=0}^{|μ|}e_r(S)·e_{j−r}(y)`, **`I(W_μ(n)) = (R_j : j odd, 1 ≤ j ≤ n+|μ|) + (x_i^q − x_i)`**.

### 1.3 Rows
For `K ⊆ S_n` with `z := x_n` and `z^q ∈ K`: **row `a`** is `R_a(K) := π_z(K : z^a) ⊆ S_{n−1}` (`π_z` sets `z = 0`); equivalently, **`f ∈ R_a(K)` ⟺ `z^a·f ∈ K + (z^{a+1})`**. Rows increase with `a`, and **`dim S_n/K = Σ_{a=0}^{q−1} dim S_{n−1}/R_a(K)`**.

### 1.4 The conjecture
`A_k(q) := dim S_{2k+2}/I^{(2k+2)}`, `P_k(q) := |W_∅(2k+2)|`. **Conjecture 1.2: `A_k(q) = P_k(q)`.** The floor `A ≥ P` is PROVED, so **the conjecture ⟺ `A_k(q) ≤ P_k(q)`**. Proved: `q = 3` for every `k`; `k ≤ 3` for every `q`. **Open: `k ≥ 4` and `q ≥ 9`.**

### 1.5 The uniform casilla (the object of INFORME_11)
**`K^{unif}_μ(n) := Q_μ(n) + box + N_{μ_1−1}(n) + F_μ(n)`**, where:
- **`Q_μ(n) := (e_j([n]) : j odd or j ≥ f+1) + (e_r(x_S) : S ⊊ [n], r > |S| − d_{|S|}(λ))`**, `λ := μ ∪ (1^f)`, `d_k(λ) := λ'_n + … + λ'_{n−k+1}` (`λ'` the conjugate, padded to length `n`).
- **Layer:** `N_w(n)` is generated by the monomials `x_A^{q−1}x_C` over all splittings `A ⊔ B ⊔ C = [n]` with `|B| − |A| ≤ w` and `|B| ≥ 1` (so `B` is the set of ABSENT variables). Minimal generators: `|B| = |A| + w`. **For `(1^ℓ)`, `ℓ ≥ 2`, the layer `N_0` is OMITTED** (it is not needed at the cells where the uniform casilla is true, and at `(1,1)`, `n = 7` adding it changes nothing: §3.2).
- **Family:** `F_μ(n) := (φ^{(ℓ)}_{jl} : j ≠ l)`, **`φ^{(ℓ)}_{jl} := y_j^{q−ℓ}·Σ_{i=0}^{ℓ−1}y_j^i·e_{f+ℓ−2−i}(y∖{y_j,y_l})`**. Degree `q+f−2`. For `ℓ = 2` it is `y_j^{q−2}e_f(y∖y_l)`. `m11lib.m2` builds all of this (`clK`).
- **Leaves** (`f ≤ 1`): `K_leaf := I_λ + box` (the Tanisaki ideal).

### 1.6 The auditor's engines in this folder
- **`grepy_casilla_verdadera.py`** — THE CERTIFIER (Singular). Usage: `python3 grepy_casilla_verdadera.py 1,1 7 2:0 > c.sing`, then `zsh grepy_vigia.sh c.log 'Singular -q c.sing'`.
  - **Method:** homogenize the fibre ideal with `t` (last, `dp`); compute a standard basis with `degBound 40`; divide each element by its largest power of `t`; set `t = 0`.
  - **The forms obtained are in `gr I(W)`.** If `vdim(tops alone) = |W|`, they GENERATE `gr I(W)`: **certified**.
  - It prints `vdim(uniform K)`, `vdim(tops alone)`, whether `K ⊆ tops`, the new generators beyond `K` (normal forms, NOT canonical: read them, then write a canonical candidate), and tests the family `(y_ay_b)^{q−E}e_{f−1+D}(y∖{c,d})` for each `E:D` you pass.
  - Anchors `a^i` (`a` generates `GF(9)^*`; one class per part, `i = 0..3`). **Edit it for your own candidate families.**
- `grepy_filas_verdaderas.m2` (M2): the TRUE rows `π(G : z^a)` of a true parent, compared with the true casillas of the children.
- `grepy_polys.py` (Python, exact over `ZZ`, no Gröbner) and `grepy_tres_letras.py` (the identities of §3.3, `264/264`).
- `grepy_vigia.sh`: the watchdog of rule 10.

## 2 · THE FRAMEWORK: THE PARTITION INDUCTION (sound; re-checked by the auditor)
**`T(n)`:** for every profile `μ` there is an EXPLICIT ideal `K_μ(n) ⊆ S_n` with `z^q ∈ K_μ(n)`, `K_∅(n) = I^{(n)}`, `K_μ(n) = (1)` when `W_μ(n) = ∅`, and **`dim S_n/K_μ(n) ≤ |W_μ(n)|`**.
**Inductive step:** `T(n−1)` ⟹ `T(n)` at `μ` as soon as, under a bijection rows ↔ values of `z`, **`R_a(K_μ(n)) ⊇ K_{μ+v}(n−1)`** for every `a`. Within a block of rows with the same child only the FIRST row needs proof. **Base:** `n = 0`. ⟹ `T(2k+2)` at `μ = ∅` is the conjecture.
**The induction never needs `K_μ ⊆ gr I(W_μ)`**; but if `K_μ ⊆ gr I(W_μ)` and `dim S/K_μ > |W_μ|` at some cell (a casilla TOO SMALL), then **some row inclusion out of `K_μ`, or `T` at some child, must fail**. At `(1,1)`, `n = 7` every child casilla is true, so row inclusions fail: this is what happens to the uniform casilla (§3.2). **So the casilla must be CORRECT before its row lemmas can be.**
**The row dictionary (a parent with `ℓ` parts):**
- **LOWER**, rows `0 … ℓ−1`: each lowers one part (largest first); the child's `f` is unchanged.
- **VALUE-0**, row `ℓ`: the child is the same `μ`, with `f−1`.
- **NEW-CLASS**, rows `ℓ+1 … q−ℓ−1`: the child is `μ ∪ (1)`, with `f−2`.
- **RAISE**, the last `ℓ` rows: each raises one part (smallest first); the child has `f−2`.

Example, `(1,1)` at `n+1`: rows 0, 1 → `(1)`; row 2 → `(1,1)`; rows `3..q−3` → `(1,1,1)`; rows `q−2, q−1` → `(2,1)`.
**Every row of the TRUE casilla IS the true casilla of its child** (the auditor, 99/99 rows in 11 parents at `n ≤ 6`, plus 81/81 leaf rows): the dictionary is right on the true objects.

## 3 · WHAT IS PROVED OR MEASURED (use it; do not re-prove it)
### 3.1 PROVED last turn (INFORME_11; re-derived by hand and re-checked by the auditor by a second route)
Notation: `a := y_j`, `b := y_l`, `P := y∖{a,b}`, `h_D(−a,b) := Σ_{i=0}^D(−a)^ib^{D−i}`, **`S^a_M := Σ_{p≥0}a^{M−p}e_p(P)`**, `S^b_M` likewise; «≡» is modulo the box.
- **LEMMA G, general form (auditor; identity over `ZZ`, every `M ≥ 0`, `196/196`):**
  - (I) `Σ_{k odd}e_k(y)h_{M−k}(−a,b) = S^b_M − (−1)^MS^a_M − [M odd]·e_M(P)`;
  - (II) `Σ_{k even}e_k(y)h_{M−k}(−a,b) = S^b_M + (−1)^MS^a_M − [M even]·e_M(P)`.
  - Proof: `E(t)H(t) = E_P(t)(1+bt)/(1−bt)` and `E(−t)H(t) = E_P(−t)(1−at)/(1+at)` with `H = 1/((1+at)(1−bt))`; the ½ cancels.
  - For `M ≥ n−1` the correction vanishes.
- **LEMMA F:** `φ^{(ℓ)}_{jl} ≡ S^a_{q+f−2} − Σ_{p=f+ℓ−1}^{n−2}a^{q+f−2−p}e_p(P)`.
- **Theorem A (VALUE-0, every `(1^ℓ)`, all `n`, `q`):** `φ_{jl}(n+1) ≡ (z+a)·φ_{jl}(n)`, hence `z^ℓφ_{jl}(n) = [Σ_{i<ℓ}z^{ℓ−1−i}(−a)^i]·φ_{jl}(n+1) + box`.
- **Theorem B (NEW-CLASS, every `(1^ℓ)`, `ℓ+1 ≤ h`):** `z^ℓ·Σ_{k odd}h_{N+1−k}(−a,b)·e_k(y,z) ∈ K`, `N := q+n−ℓ−3`; Lemma G splits it into value-0 families plus `z·`(new-class families), and (I) makes the other half an `e_odd`-combination. Holds in every odd characteristic.
- **Theorem C (LOWER row 0 for `μ_1 > μ_2` and for `(1^ℓ)`, `ℓ ≥ 3`):** row 0 is the substitution `z = 0`.
- **Theorem D (Tanisaki row lemma, characteristic-free):** `R_a(I_λ(n+1)) ⊇ I_{λ^{(a)}}(n)` for `a < ℓ(λ)` (`λ^{(a)}`: lower `λ_{a+1}` by one), and **`z^{ℓ(λ)} ∈ I_λ`** with coefficients `±1`. ⟹ **every leaf row of every profile.** The proper-subset part applies to the Tanisaki part of any `Q_μ`.
- **Theorem E (hooks `(m,1^{ℓ−1})`, `m ≥ 2`, `q ≥ |μ|+2`):** VALUE-0, NEW-CLASS, all LOWER rows, and the LARGE RAISE (row `q−1`); all corrections are layer monomials.
- **Leaf-child rows:** a row whose child is a leaf needs only q-free generators; the auditor re-proved the 10 such raise rows of row `k = 4` q-FREE (`20/20` over `QQ` and `F_3`).
- ⚠️ **These theorems are about `K^{unif}`.** They stay true as statements. Wherever the uniform casilla is also the true one (every cell at `n ≤ 6`, and 10 of 12 profiles at `n = 7`), they are row lemmas of the true casilla.

### 3.2 THE UNIFORM CASILLA IS FALSE AT THREE CELLS (auditor; re-counted twice, two fields)
| cell (`q = 9`) | `f` | colength of `K^{unif}` | `|W|` | status |
|---|---|---|---|---|
| `(1,1)`, `n = 7` | 5 | **22 337** | 22 302 | too small by 35 |
| `(2,2)`, `n = 7` | 3 | **3 675** | 3 570 | too small by 105 |
| `(1,1)`, `n = 8` | 6 | **204 820** | 204 456 | too small by 364 |
| the other 10 multi-part profiles at `n = 7` | 2–4 | = `|W|` | | the uniform casilla is true |

**Where the rows fail** (row colength vs the child's fibre; the child generators missing from the row):
- **`(1,1)`, `n = 7`:**
  - row 0 (→ `(1)`): 4 271 vs 4 266; missing the child's layer monomials `(ab)^{q−1}x_{cd}` (`|A| = 2`), 90 of them, degree 18;
  - row 7 (→ `(2,1)`): 1 110 vs 1 080; missing **`T_{a;bc} := a^{q−1}x_{[6]∖{a,b,c}}`**, 60 of them, degree 11;
  - every other row is exact.
- **`(2,2)`, `n = 7`:**
  - row 0: missing the same 60 `T`;
  - row 2 (value 0): 615 vs 570; missing the family of `(2,2)` at 6;
  - row 7 (raise → the leaf `(3,2)`): 90 vs 60; missing 15 squarefree degree-4 monomials;
  - every other row is exact.

**Dead repairs:** adding `N_0(7)` changes nothing (22 337). Adding all monomials `(y_iy_j)^{q−1}x_C`, `|C| = 2`, OVERSHOOTS (22 085 < 22 302), so they are not all in `gr I`.

### 3.3 THE TWO SECOND FAMILIES (auditor; CERTIFIED)
**Certified true casillas.** With the certifier:
- `(1,1)` at 7: tops alone 22 302 = `|W|`; `K^{unif} ⊆` tops; 21 new independent generators, ALL of degree 18.
- `(2,2)` at 7: tops alone 3 570; `K^{unif} ⊆` tops; 35 new generators, ALL of degree 11.

**The families, read and certified:**
| profile | the second family | members in `gr I` | `K^{unif} + family` |
|---|---|---|---|
| `(1,1)` (`ℓ = 2`) | **`F2_{ab;cd} := (y_ay_b)^{q−2}·e_{f−1}(y∖{y_c,y_d})`**, `{a,b} ∩ {c,d} = ∅`; degree `2q+f−5` | at `n = 7`: 210/210; at `n = 6`: 90/90 (there redundant) | **`= gr I(W)` exactly at `n = 7`** |
| `(2,2)` | **`H_{j;k;l} := y_j^{q−2}·y_k²·e_{f−1}(y∖{y_k,y_l})`**, `j, k, l` distinct; degree `q+f−1` | at `n = 7`: 210/210 | **`= gr I(W)` exactly at `n = 7`** |
| `(1,1,1)` | `(y_ay_b)^{q−3}e_{f−1}(y∖{c,d})`: **0/210** in `gr I` at `n = 7` | — | the `ℓ = 3` analogue is NOT this; at `n = 7` none is needed |

**How they feed the rows (read this twice: it is the scent).**
- `F2_{zb;cd}` has lowest `z`-term `z^{q−2}·y_b^{q−2}·e_{f−1}(y∖{c,d})`. Here `y∖{c,d}` (the `y`-variables without `c, d`) has exactly `f−1` variables, so its `e_{f−1}` is their PRODUCT. **Raise row `q−2` receives `y_b^{q−1}x_{[n]∖{b,c,d}} = T_{b;cd}`.** This is exactly the piece the last Fable could not prove.
- `F2_{ab;cz}` is `z`-free and feeds row 0 (the child `(1)`'s `|A| = 2` layer).
- `H_{j;z;l}` has lowest `z`-term `z²·y_j^{q−2}e_{f−1}(y∖y_l)`. **Row 2 (value 0) receives the `(2,2)` family** — the non-hook family INFORME_11 §3.5 could not reach.

**Three-letter structure behind `T`** (auditor, `264/264` over `ZZ` modulo the box, `q = 9, 27, 81`, `ℓ ≤ 4`, `n ≤ 9`; `grepy_tres_letras.py`). Take the parent `(1^ℓ)` at `n+1`, `P'' := y∖{a,b,c}` and `U := a^{q−ℓ}Σ_{i<ℓ}a^ie_{n−3−i}(P'')` (`≡ S^a_{q+f_c−2}(P'')`, `f_c = n−ℓ−1`). Then:
- `φ_{ab} ≡ (a+c)(a+z)·U`, `φ_{ac} ≡ (a+b)(a+z)·U`, `φ_{az} ≡ (a+b)(a+c)·U` (the last is `z`-free);
- `T_{a;bc} ≡ a^{ℓ−1}·U`.
The first family kills `U` only on the three lines `{(a+b)(a+c) = (a+b)(a+z) = (a+c)(a+z) = 0}`, and gives nothing on the line `b = c = −a`: one letter against two copies of its negative, **an imbalance-2 class**. That is the class a raise creates. **For `ℓ = 2` the second family `F2` is what lives there.** For `ℓ ≥ 3` nothing was needed up to `n = 7`.

### 3.3bis THE UNIFYING SCENT — both second families are multiples of ONE divided difference (auditor, verified)
For `ℓ = 2` the family is `φ_{jl} = y_j^{q−2}e_f(y∖y_l)` exactly. Expanding `e_f` over `Y := y∖{c,d}`:
- **`φ_{jc} − φ_{jd} = (y_d − y_c)·D_{j;cd}`, with `D_{j;cd} := y_j^{q−2}·e_{f−1}(y∖{y_c,y_d})`**: an exact identity over `ZZ`, 162/162, `q = 9, 27, 81`, `n ≤ 9`, every `f`. So `D` is the divided difference of the first family.
- **`F2_{ab;cd} = y_a^{q−2}·D_{b;cd}`** and **`H_{j;k;l} = y_k²·D_{j;kl}`**: the two second families are the SAME divided difference times two different multipliers.
- **At BOTH failing cells** (`(1,1)` and `(2,2)`, `n = 7`):
  - `y_c²·D` and `y_a^{q−2}·D` (`a ∉ {j,c,d}`) are in `gr I`, 210/210 each;
  - `y_c·D` is NOT (0/210 at `(1,1)`);
  - `H` alone does not repair `(1,1)` (22 337), and `F2` alone does not repair `(2,2)` (3 675);
  - **but `K^{unif} + (y_c², y_a^{q−2})·D` is the true casilla at both.** ⟹ **Candidate law for `ℓ = 2`: the second family is `M_{cd}·D_{j;cd}`, where `M_{cd} := {m : m·D_{j;cd} ∈ gr I(W)}` (the multiplier ideal) contains `(y_d − y_c)` trivially, and — measured — `y_c²`, `y_d²`, `y_a^{q−2}`.** Why these multipliers, and no smaller ones, is the question.
- **For `ℓ = 3` it does NOT transfer as is.** At `(1,1,1)`, `n = 7` (`f = 4`, where nothing is needed), `D3_{j;cd} := y_j^{q−3}Σ_{i<3}y_j^ie_{t−1−i}(y∖{j,c,d})` (the divided difference of `φ^{(3)}`) gives `y_c²D3`, `y_a^{q−3}D3` and `y_cD3`, and **none of them is in `gr I` (0/105 each)**. The `ℓ = 3` law is different, or starts at larger `f`.
- **For ROW `k = 4` you need the corrected casilla ONLY for `(1,1)` at `n = 7` and `n = 8`: `ℓ = 2`.** The `ℓ = 2` law is enough for the GOOD prize.

### 3.4 Also measured (auditor, `q = 9`)
- **At `f = 2`, the layer is REDUNDANT** in the child's own `Q + box + F`: `(2,1)` at 5, 0/160; `(2,1,1)` at 6, 0/497; `(2,2)` at 6, 0/497.
- **At `f = 3` it is not:** `(2,1)` at 6: 60/497 missing, exactly the `T_{a;bc}`.

## 4 · THE TARGETS
### PART A — THE LAW OF THE SECOND FAMILIES (the must; ~40 %)
**A1 — Read (budget 30 min).**
- Run the certifier on the cells it reaches that nobody has measured: `q = 27`, every multi-part profile with `n ≤ 5` (6 variables with `t`); and `q = 9`, the one-part `(1)` and `(2)` at `n = 7` as controls (INFORME_8 showed their casilla is the true one there: the certifier must find nothing new).
- **Before running, write a PREDICTION** of which cells need a second family, and of its degree.
- For the two known cells, read the 21 and the 35 normal forms and make sure the canonical families (`F2`, `H`) explain all of them. **Is there a common form**, e.g. one family `y_{a_1}^{q−ℓ}⋯y_{a_r}^{q−ℓ}·y_{k_1}^2⋯·e_{…}(y∖{…})` with `r` heavy letters and some squared ones, of which the first family (`r = 1`), `F2` (`r = 2`) and `H` (`r = 1`, one square) are cases?

**A2 — The law (budget 45 min).**
- State, with `μ`, `n`, `q` as letters, the corrected casilla `K_μ(n) = K^{unif}_μ(n) + (second families)`.
- Explain WHEN each family is needed. Data: `F2` is in `gr I` at `(1,1)`, `n = 6` (redundant) and needed at `n = 7`; `H` is needed at `(2,2)`, `f = 3`; nothing is needed at `(1,1,1)`, `f = 4`, or at the other 10 profiles at `n = 7`.
- **Start from §3.3bis:** is the second family always `M_{cd}·D_{j;cd}`, the multiplier ideal of the divided differences of the first family? Find `M_{cd}` with letters for `ℓ = 2`; then find what replaces it for `ℓ ≥ 3` (the naive `D3` fails). A degree check that helps: `F2` has degree `2q+f−5`, which is exactly the degree of what rows 0 and `q−2` of `(1,1)` demand (`(ab)^{q−1}x_{cd}` in row 0, `z^{q−2}T` in row `q−2`).
- Gate the law AS IDEALS with the certifier on every cell it reaches, and on `(1,1)` at `n = 8` with letters only.

**A3 — Prove they belong (budget 30 min).** Prove with letters:
- **`F2_{ab;cd} ∈ gr I(W_{(1,1)}(n))`** for every `n`, `q` (equivalently `y_a^{q−2} ∈ M_{cd}`): exhibit a polynomial vanishing on `W` whose top form it is. Natural start: take vanishing lifts `Φ_{jc}, Φ_{jd}` of the first family (polynomials vanishing on `W` with top forms `φ_{jc}, φ_{jd}`; that `φ ∈ gr I` is MEASURED at every gated cell, and proving it is part of this step); their difference vanishes on `W` and has top form `(y_d−y_c)D`. On `W`, `y^{q−1} = [y ≠ 0]`: find why multiplying by `y_a^{q−2}` or `y_c²` lets you DIVIDE by `y_d − y_c` on the points of `W`. Hints: on `W`, `y^{q−1} = [y ≠ 0]` and `y^q = y`; the anchors of `(1,1)` sit in two classes; Lemma G and its generating functions; the three-letter identities.
- **`H_{j;k;l} ∈ gr I(W_{(2,2)}(n))`**. Gate every vanishing identity on ALL points of `W` (Python, `q = 9`, `n ≤ 7`).

### PART B — THE f = 2 LEMMA (~10 %)
**Prove with letters:** at `f = 2` the layer of the casillas above is redundant in `Q + box + F`, for every `q`. With the proved pieces of INFORME_11, it closes these row-`k = 4` inclusions:
- `(1,1)` at 6 → `(2,1)` at 5;
- `(2,2)` at 6, row 0 → `(2,1)` at 5;
- `(1,1,1)` at 7 → `(2,1,1)` at 6.

INFORME_11 observed an identity for it (not re-verified by the auditor): `x_a^{q−1}x_C ≡ Σ_{i=1,2}h_{L−2}(a,−b_{3−i})·φ_{ab_i}` modulo `(e_k) + (x_{[n]∖b}) + box`, where `L := |μ|`, `C = [n]∖{a,b_1,b_2}`, and `φ` is the child's family.

### PART C — ROW `k = 4` WITH THE CORRECTED CASILLA (the prize; ~35 %)
`A_4(q) = P_4(q)` for all `q` is `T(10)` at `∅`. It needs every `(μ, n)` with `|μ| ≤ min(n, 10−n)`, `n ≤ 9`. The non-leaf parents are: `∅`, the one-part profiles, `(1,1)` at `n = 4..8`, `(2,1)` at `5..7`, `(3,1)`, `(2,2)`, `(2,1,1)`, `(1^4)` at 6, and `(1,1,1)` at `5..7`.

**The ledger after this audit (parent in `n` variables):**
- **PROVED for all `q`** (INFORME_11 plus the auditor's q-free re-proof of the leaf-child rows):
  - every row of `∅` and of `(1)…(4)`; every leaf row;
  - rows 0–2 of `(2,1)` and `(3,1)`; the new-class rows of `(1,1)`, `(2,1)`, `(3,1)`, `(1^3)`, `(1^4)`, `(2,1,1)`;
  - the value-0 rows of `(1,1)` (at `n ≤ 7`: its child is true there), `(1^3)`, `(1^4)`, `(2,1,1)`; every lower row of `(1^3)`, `(1^4)`, `(2,1,1)`;
  - the large raise of `(2,1)`, `(3,1)`, `(2,1,1)`; the leaf-child raises (`(1,1)` at 4, 5; `(2,1)` at 5, 6; `(3,1)`; `(2,2)`; `(1^3)` at 5, 6; `(2,1,1)`; `(1^4)`);
  - the value-0 and new-class rows of `(2,2)` at 6 (leaf children).
- **Where the uniform casilla is TRUE** (every parent here except `(1,1)` at 7 and 8), these are row lemmas of the true casilla.
- **OPEN:**
  - **(i) the f = 2 lemma (PART B):** `(1,1)` at 6 raise; `(2,2)` at 6 row 0; `(1^3)` at 7 raise;
  - **(ii)** `(2,1)` at 7, raise row `q−2` → `(2,2)` at 6: the `(2,2)` family in the row. Here the child's layer is redundant (0/497), so this is not a layer problem; and the uniform `(2,1)` at 7 IS the true casilla, so by the dictionary the row is expected true (parents with 7 variables were never row-checked);
  - **(iii) `(1,1)` at `n = 7` and `n = 8`, EVERY row, with the corrected casilla** `K^{unif} + F2` (+ whatever the law of PART A adds at `n = 8`);
  - **(iv) `(1,1)`, rows 0 and 1 (→ `(1)`), at EVERY `n = 4..8`: NOT proved.** INFORME_11 took them from `MISION_11` §3.1, which took them from INFORME_8 §2.2; that argument produces the child's layer `N_{m−2}`, EMPTY for `m = 1`, while the child `(1)` has `N_0`. (Row 1's argument also needs `N_0 ⊆ K_{(1,1)}`, only measured.) Measured TRUE at `n ≤ 6`, and row 1 at `n = 7`; row 0 at `n = 7` needs `F2`. This is the auditor's error, not the Fable's.
  - **(v) NEW OBLIGATIONS created by `F2`.** `(1,1)` at 7 and 8 are CHILDREN of `(1)` at 8, 9 (new-class rows `2..q−2`) and of `(1,1)` at 8 (value-0, row 2). So **`F2(n) ⊆ R_2(K_{(1)}(n+1))`** and **`F2(n) ⊆ R_2(K_{(1,1)}(n+1))`** must now be proved. (The one-part row lemmas are proved; if the dictionary holds, row 2 of the true `(1)` casilla IS the true `(1,1)` casilla, so the obligation is TRUE — it needs a proof.)
- **Give every row a status:** PROVED (by which lemma) or OPEN (what is missing, smallest cell). **If none is OPEN: write «ROW k = 4 CLOSED FOR ALL q» and the full chain.**

### PART D — LEMMA G BEYOND `q ≥ |μ|+2` (~5 %, pencil)
Theorems B and E need `q ≥ |μ|+2`. For DS 1.2 at `q = 9` the induction visits, when `k ≥ 7`, hooks with `|μ|` up to `k+1 > q−2`. With the general Lemma G (the correction `e_M(P)` has squarefree monomials, layer for hooks), extend them to every `|μ|`, or say what breaks.

## 5 · PROCESS
- **STEP 0 — Design and sealed bets (15 min, no runs).** Plan, with an estimate for every run. **Seal at least FIVE predictions before running anything, at least THREE risky**, for example:
  - «the square in `H` is the part size: a profile with a part 3 carries a cube `y_k^3`»;
  - «for `(1,1)` and every `n ≥ 6`, `M_{cd} = (y_d − y_c, y_c², y_a^{q−2} : a ∉ {j,c,d})` exactly»;
  - «at `q = 27` no cell with `n ≤ 5` needs a second family»;
  - «`(1,1)` at `n = 8` needs a THIRD family `(y_ay_by_c)^{q−2}e_{f−2}(y∖{d,e,g})`».
  Score them at the end, hits and falsified printed the same size.
- **STEP 1 — PART A1 (30 min). STEP 2 — PART A2 + A3 (75 min). STEP 3 — PARTS B and D (30 min). STEP 4 — PART C (45 min). STEP 5 — Verdict (10 min)**, after re-reading the disk.
- **WHAT I FOUND BEAUTIFUL:** one paragraph.
- **FOR MISSION 13:** the law, what is proved, the smallest open cell of each type, and your estimate of what the full conjecture still takes.

## 6 · DEAD ROUTES (do not retry)
- **«The uniform casilla is the true one»:** false at `(1,1)` `n = 7, 8` and `(2,2)` `n = 7`.
- The layer `N_0` as the repair of `(1^ℓ)`. The degree-`2q` monomials `(y_iy_j)^{q−1}x_C` as a repair (overshoot).
- **«Rows 0, 1 of `K_{(m,1)}` are proved for all `m`»:** the row-0 argument yields the child's layer `N_{m−2}`, which is EMPTY for `m = 1`, while the child `(1)` has `N_0`. Row 0 of `(1,1)` at 7 FAILS for the uniform casilla.
- M2 `DegreeLimit` Gröbner bases of the inhomogeneous fibre ideal as a certificate. Use the certifier.
- Counting lemmas for rows (the counts ARE the induction); «rows ⊆ fibres» as a formal consequence; the sum of colons alone for generic rows.
- Reading certificates from a raw syzygy normal form; single-variable descents; the lift lemma (inert).
- Any ascent in `q` (a tower elevator): dead, with proof. Measuring cells as a substitute for a mechanism: cells are gates.
- The truncated Lucas certificate `H_D = h_D − (pure powers)`: it hides a division by `ℓ` (fails at `ℓ = 3`); keep the full `h_D`.

## 7 · SUCCESS
- **Minimum:** the law of the second families for `ℓ = 2` with letters, gated as ideals by the certifier, with a prediction made before measuring; and `(y_c², y_a^{q−2})·D_{j;cd} ⊆ gr I(W_{(1,1)}(n))` proved with letters for every `n`, `q`.
- **Good:** **ROW `k = 4` CLOSED FOR ALL q** with the corrected casilla.
- **Excellent:** corrected casilla plus all four row lemmas for every two-part profile.
- **Full:** **every profile ⟹ CONJECTURE 1.2 CLOSED FOR ALL `k` AND ALL `q`.**

*Last word from the auditor.* Two turns ago one lemma resisted two missions and turned out to be a single line in two letters. Last turn a whole list of rows fell to one generating function. This turn the ground moved under the proofs: the casilla everybody used was wrong exactly where nobody had looked. Then the same turn found the families that make it right, and one of them hands over, in its lowest term, the monomials that had resisted. The prey is not hidden any more. It has a scent, two tracks and a certifier. Follow it.

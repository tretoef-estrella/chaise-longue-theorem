# MISSION 11 — THE FOUR ROW LEMMAS. ONE ENGINE, FOUR DOORS, AND THE CONJECTURE BEHIND THEM.
*(Grepy el Lector, auditor, 2026-09-23.)*

**You are a NEW Fable. This file is SELF-CONTAINED: read it whole before anything else; you need nothing else.** The reports `INFORME.md` … `INFORME_10.md` in this folder are audited and APPROVED. Open them only to quote a proof summarised here. Their scripts may be reused (`fibre.py`, `wd.sh`, `m10cas.m2`, `m10unif.m2`, `m10alg.m2`, `a1sym.m2`, `m10cert.m2`, …), and two engines of the auditor are here for you: **`grepy_filas_verdaderas.m2`** (are the rows of a TRUE parent casilla the TRUE casillas of its children?) and **`grepy_gate_uniforme.m2`** (is the uniform casilla the true one, as an ideal?).

> **OBJECTIVE of the campaign: the complete closure of Conjecture 1.2 of Degtyarev–Shimada, for all `k` and all `q = 3^v`.**
>
> **Where we stand — every item verified by the auditor, most of them twice, by two engines:**
> - The conjecture is ONE induction on the number of variables over explicit ideals («casillas») `K_μ(n)`, indexed by an imbalance profile `μ`. Only **row inclusions** are needed, never counts (§2).
> - **Last mission proved (G1) with letters** — every `m`, every `n`, every `q ≥ 9` — with a FIRST-ORDER certificate in TWO letters: a Lucas divided difference of `(−y_j, y_l)` (§3.2). ⟹ **every row of every one-part casilla is PROVED for all `q`.**
> - **ONE uniform casilla for every profile**, `K_μ(n) = Q_μ(n) + box + N_{μ_1−1}(n) + F_μ(n)`, equal AS AN IDEAL to the true casilla in **53 cells** (40 by the last Fable, 13 again by the auditor with a differently written family), and failing when perturbed (§3.3).
> - **New this turn (auditor): every row is TRUE.** In the 11 multi-part parents that row `k = 4` needs up to `n = 6`, **99/99 rows** of the true parent casilla ARE, as ideals, the true casillas of the children the dictionary names. **And the leaves are inside the induction:** in 9 leaves, **81/81 rows**, the rows with an empty child being the unit ideal. So there is NO separate «Tanisaki in characteristic 3» step (§2.4).
> - ⟹ **THE CONJECTURE, FOR EVERY `k` AND EVERY `q`, FOLLOWS FROM FOUR ROW LEMMAS — LOWER, VALUE-0, NEW-CLASS, RAISE — FOR THE UNIFORM CASILLA, FOR EVERY PROFILE `μ`.** One of them is proved in its first cases. The other rows are true wherever measured (180 of 180). **What is missing is proofs, not truth.**
>
> **This mission: prove the four lemmas.** The recipe exists and worked last turn: machine-find the certificate in a SMALL ansatz in the two letters the target distinguishes, read it, prove it with letters by the three tools of the campaign (generating identity, Frobenius, Lucas).
>
> **Prize ladder:**
> - **MINIMUM:** ONE whole row type proved with letters for a NEW infinite family of profiles. Examples: the value-0 row for every `(1^ℓ)`; the new-class row out of every `(m,1)`; the raise rows of every `(m,1)`. The certificates written down explicitly.
> - **GOOD:** **ROW `k = 4` CLOSED FOR ALL q** — every row inclusion that `A_4(q) = P_4(q)` needs (the 26 kinds of §4 PART D plus the leaf rows), each PROVED with `q` a letter. **It is the first new row of the conjecture since `k = 3`.**
> - **EXCELLENT:** all four row types for EVERY two-part profile and every `q`, plus the value-0 row for every `ℓ`.
> - **FULL:** **all four row lemmas for every profile ⟹ CONJECTURE 1.2 CLOSED FOR ALL `k` AND ALL `q`.** If you get there, say it in your FIRST LINE, in capitals, with the full chain.
>
> **This is not a small mission, and it is not meant to be.** The last Fable proved in one turn a lemma that four certificates had hidden for two missions. You have its proof as a model, the true casillas computable in seconds, every row known to be true, and a list of exactly what is missing. **Bite and do not let go.**

---
## 0 · RULES OF THE TURN (mandatory)
1. **BEFORE THINKING:** create `INFORME_11.md` with these empty sections: `## FIRST LINE` · `## STEP 0 — DESIGN AND SEALED BETS` · `## STEP 1` · `## STEP 2` · `## STEP 3` · `## STEP 4` · `## STEP 5 — VERDICT` · `## WHAT I FOUND BEAUTIFUL` · `## FOR MISSION 12`.
2. **Save to disk after every step.** What is not written does not exist. If your session is cut, what is on disk IS your delivery.
3. **Header per step:** `STATE: CLOSED | EXHAUSTED | NOT CONCLUDED` and `NEXT:`.
4. **Timing:** work in order, no going back, no retries. Write the budget before each step. After 10 minutes without progress: stop, write, declare. Keep the last 20 % of each budget for writing.
5. **At most one literature search per step**, in the original source.
6. **Do not recompute anything listed here as proved or measured.**
7. **A negative dimension, or one larger than the box, is a bug:** stop.
8. **«This route dies, for this reason» is a result.** A falsified sealed bet is worth more than a safe hit.
9. **Write ONLY in `~/Desktop/FABLE_TABLERO/`. Do not open anything in `~/Desktop/ARBOLYAML/`.**
10. **Machine:** `/opt/homebrew/bin/M2` (and `Singular` if you prefer it for memberships). This Mac has no `timeout`: use the folder's `wd.sh script.m2 logfile` (570 s watchdog).
    - **Caps per run, do not move:** `< 1.2 GB` and `< 10 min`. **Write the estimate BEFORE each run, engine by engine** (last turn one run started before its estimate: do not repeat it).
    - You MAY run TWO engines at once if their estimates add up to less than 1.2 GB. **Any Gröbner basis in 7 variables runs ALONE.**
    - After any kill, check with `pgrep` that it is gone, and write that you checked. When you finish, check that nothing of yours runs.
    - M2 reserved names (`check`, `top`, `info`, `degree` as a variable, …) abort scripts: prefix your own names (`cl…`). Building `R/I` REBINDS variable names: re-`use` the ring you mean. Never pass thousands of generators at once: reduce first.
    - **Allowed:** explicit ideals in `n ≤ 10` variables at `q = 3`, `n ≤ 7` at `q = 9`, `n ≤ 5` at `q = 27`, `n ≤ 4` at `q = 81`: colengths, colons by a power of one variable, memberships, lifts, minimal generators; the fibre ideals of §3.4 at the same sizes; Python evaluation on all points of a fibre at `q ≤ 27`.
    - **Forbidden:** any M2 run with `n ≥ 8` at `q ≥ 9`, `n ≥ 6` at `q = 27`, `n ≥ 5` at `q = 81`; point ideals over `GF(27)`; point enumeration in M2.
    - **Known costs:** the true casilla of `(1,1,1)` at `n = 7` (DegreeLimit 17): 51 s, 300 MB. Any base containing the layer `N_w(7)`: ~ 424 s. A colon in 6 variables at `q = 9` on a true casilla: seconds (the auditor ran 99 rows in 13 s). A colon in 7 variables at `q = 9`: killed at 570 s once.
11. **In characteristic 3, never average over a group whose order is divisible by 3.** Make a certificate canonical by REDUCTION, not by averaging. **And do not read certificates from the syzygy normal form of a raw lift:** last turn that gave 225 unreadable terms; the readable certificate came from a SMALL ANSATZ (§3.2).
12. **Re-read the disk before the verdict.**
13. **Double check:** every PROVED claim carries its proof in the report; every number its cell and its log; every identity used in a proof is checked exactly (symbolically, or on ALL points of the set it is claimed on); every casilla is gated AS AN IDEAL against the true one.

**FIRST LINE** (answer first, in this order):
- (a) Which of the four row types are PROVED, and for exactly which families of profiles (with the hypotheses on `n`, `q`)?
- (b) The certificate of each proved type, in one sentence with letters.
- (c) The leaves: is `z^{ℓ(λ)} ∈ K_leaf` proved with letters? Are the leaf rows covered by your lemmas?
- (d) Row `k = 4`: how many row inclusions remain OPEN, of how many kinds?
- (e) Does anything close row `k = 4` or the conjecture? YES or NO, with the reason in one line.

---
## 1 · THE OBJECTS
**Basics.** `q = 3^v`, `h := (q−1)/2`, `S_n := F_q[x_1..x_n]`. `e_r` is the elementary symmetric polynomial (`e_0 = 1`; `e_r = 0` for `r < 0` or `r >` the number of variables). `box := (x_1^q, …, x_n^q)`. **`I^{(n)} := (e_1, e_3, e_5, …) + box`.** `x_C := Π_{i∈C}x_i`; `x_A^{q−1} := Π_{i∈A}x_i^{q−1}`. `gr I(X)` is the ideal of top forms of the functions vanishing on `X`.

**Profiles and fibres.** A multiset `S ⊂ F_q` (the **anchor**) constrains `y ∈ F_q^n` by «`y ∪ S` is closed under negation». Its **profile** `μ = (μ_1 ≥ … ≥ μ_ℓ)` has one positive part per non-zero class `{s,−s}`: how many more copies of `−s_i` than of `s_i` the point `y` must carry. `|μ| := Σμ_i`, `ℓ := ℓ(μ)`, **`f := n − |μ|`**.
- **`W_μ(n) := {y ∈ F_q^n : y ∪ S closed}`**, up to bijection a function of `μ`; empty iff `|μ| > n` or `ℓ > h`.
- **Fibre sizes:** with `I_m(t) := Σ_{b≥0} t^{2b+m}/(b!(b+m)!)`, **`|W_μ(n)| = n!·[t^n] E(t)·Π_iI_{μ_i}(t)·I_0(t)^{h−ℓ}`**, `E = cosh` if `f` even, `sinh` if `f` odd (`fibre.py`).
- **Gates** (`q = 9`, `n = 0..9` | `q = 27`, `n = 0..7`):

| `μ` | `q = 9` | `q = 27` |
|---|---|---|
| `∅` | 1, 1, 9, 25, 217, 921, 7761, 41889, 345465, 2162617 | 1, 1, 27, 79, 2107, 10011, 263901, 1708617 |
| `(1)` | 0, 1, 2, 24, 88, 855, 4266, 37947, 227144, 1930329 | 0, 1, 2, 78, 304, 9765, 55566, 1647597 |
| `(2)` | 0, 0, 1, 3, 46, 210, 2340, 13496, 130984, 868680 | 0, 0, 1, 3, 154, 750, 28530, 189266 |
| `(3)` | 0, 0, 0, 1, 4, 75, 410, 5201, 34104, 362670 | 0, 0, 0, 1, 4, 255, 1490, 65681 |
| `(4)` | 0, 0, 0, 0, 1, 5, 111, 707, 10094, 74214 | 0, 0, 0, 0, 1, 5, 381, 2597 |
| `(1,1)` | 0, 0, 2, 6, 84, 380, 3930, 22302, 204456, 1329624 | 0, 0, 2, 6, 300, 1460, 54150, 358722 |
| `(2,1)` | 0, 0, 0, 3, 12, 200, 1080, 12390, 79408, 779436 | 0, 0, 0, 3, 12, 740, 4320, 184380 |
| `(3,1)` | 0, 0, 0, 0, 4, 20, 390, 2450, 31248, 223776 | 0, 0, 0, 0, 4, 20, 1470, 10010 |
| `(4,1)` | 0, 0, 0, 0, 0, 5, 30, 672, 4816, 67914 | 0, 0, 0, 0, 0, 5, 30, 2562 |
| `(2,2)` | 0, 0, 0, 0, 6, 30, 570, 3570, 44380, 315756 | 0, 0, 0, 0, 6, 30, 2190, 14910 |
| `(3,2)` | 0, 0, 0, 0, 0, 10, 60, 1295, 9240, 125496 | 0, 0, 0, 0, 0, 10, 60, 5075 |
| `(1,1,1)` | 0, 0, 0, 6, 24, 360, 1920, 20370, 128016, 1189944 | 0, 0, 0, 6, 24, 1440, 8400, 349230 |
| `(2,1,1)` | 0, 0, 0, 0, 12, 60, 1020, 6300, 72240, 502992 | 0, 0, 0, 0, 12, 60, 4260, 28980 |
| `(3,1,1)` | 0, 0, 0, 0, 0, 20, 120, 2310, 16240, 203112 | 0, 0, 0, 0, 0, 20, 120, 9870 |
| `(2,2,1)` | 0, 0, 0, 0, 0, 30, 180, 3360, 23520, 286020 | 0, 0, 0, 0, 0, 30, 180, 14700 |
| `(1,1,1,1)` | 0, 0, 0, 0, 24, 120, 1800, 10920, 115920, 789264 | 0, 0, 0, 0, 24, 120, 8280, 56280 |
| `(2,1,1,1)` | 0, 0, 0, 0, 0, 60, 360, 5880, 40320, 453600 | 0, 0, 0, 0, 0, 60, 360, 28560 |
| `(1,1,1,1,1)` | all 0 (`ℓ = 5 > h`) | 0, 0, 0, 0, 0, 120, 720, 55440 |

- **Fibre recursion (last coordinate `v`):** `|W_μ(n)| = Σ_{v∈F_q}|W_{μ+v}(n−1)|`: `v = 0` gives `μ`; `v = −s_i` LOWERS `μ_i`; `v = +s_i` RAISES `μ_i`; `v` in an unused class APPENDS a part `1`.

**Rows.** For `K ⊆ S_n` with `z := x_n` and `z^q ∈ K`: **row `a`** is `R_a(K) := π_z(K : z^a) ⊆ S_{n−1}` (`π_z` sets `z = 0`). Rows increase with `a`, and **`dim S_n/K = Σ_{a=0}^{q−1} dim S_{n−1}/R_a(K)`**.

**The conjecture.** `A_k(q) := dim S_{2k+2}/I^{(2k+2)}`, `P_k(q) := |W_∅(2k+2)|`. **Conjecture 1.2: `A_k(q) = P_k(q)`.** The floor `A ≥ P` is PROVED, so **the conjecture ⟺ `A_k(q) ≤ P_k(q)`**.

## 2 · THE FRAMEWORK: THE PARTITION INDUCTION
### 2.1 The statement
**`T(n)`:** for every profile `μ` there is an EXPLICIT ideal `K_μ(n) ⊆ S_n` with `z^q ∈ K_μ(n)`, `K_∅(n) = I^{(n)}`, `K_μ(n) = (1)` when `W_μ(n) = ∅`, and **`dim S_n/K_μ(n) ≤ |W_μ(n)|`**.
**Inductive step:** `T(n−1)` ⟹ `T(n)` at `μ` as soon as there is a bijection `a ↔ v` (rows ↔ values) with **`R_a(K_μ(n)) ⊇ K_{μ+v}(n−1)`** for every `a`. Rows increase with `a`, so give the LARGE fibres to the SMALL `a`; within a block of rows of the same child type, only the first row needs proof. **Base:** `n = 0`. ⟹ `T(n)` for all `n` ⟹ the conjecture (at `μ = ∅`, `n = 2k+2`).

### 2.2 The row dictionary (a parent with `ℓ` parts), and the FOUR ROW TYPES
- **LOWER** — rows `0 … ℓ−1`: each lowers one part (the largest part first). Child `f` unchanged.
- **VALUE-0** — row `ℓ`: child of the same type `μ`, `f−1`.
- **NEW-CLASS** — rows `ℓ+1 … q−ℓ−1` (there are `q−1−2ℓ` of them): child `μ ∪ (1)`, `f−2`.
- **RAISE** — the last `ℓ` rows: each raises one part (the smallest part first). Child `f−2`.
Example, `μ = (m,1)` in `n+1` variables: row 0 → `(m−1,1)`; row 1 → `(m)`; row 2 → `(m,1)`; rows `3..q−3` → `(m,1,1)`; row `q−2` → `(m,2)`; row `q−1` → `(m+1,1)`.
**`f` never increases along rows.**

### 2.3 Every row is TRUE where measured (auditor, this turn; do not re-measure)
With the TRUE casillas `G := gr I(W_S(n))` (§3.4), the auditor computed every row `R_a(G) = π(G : z^a)` and compared it AS AN IDEAL with the true casillas of the children `W_{S∪{v}}(n−1)`, at `q = 9` (`grepy_filas_verdaderas.m2`):

| parent `(μ,n)` | row colengths (rows `0..8`) | rows = a child's true casilla |
|---|---|---|
| `(1,1)` n = 4 / 5 / 6 | 24,24,6,6,6,6,6,3,3 / 88,88,84,24,24,24,24,12,12 / 855,855,380,360,360,360,360,200,200 | 27/27 |
| `(2,1)` n = 5 / 6 | 84,46,12,12,12,12,12,6,4 / 380,210,200,60,60,60,60,30,20 | 18/18 |
| `(3,1)` n = 6 | 200,75,20,20,20,20,20,10,5 | 9/9 |
| `(2,2)` n = 6 | 200,200,30,30,30,30,30,10,10 | 9/9 |
| `(1,1,1)` n = 5 / 6 | 84,84,84,24,24,24,12,12,12 / 380,380,380,360,120,120,60,60,60 | 18/18 |
| `(2,1,1)` n = 6 | 360,200,200,60,60,60,30,30,20 | 9/9 |
| `(1^4)` n = 6 | 360,360,360,360,120,60,60,60,60 | 9/9 |

**99/99**, with the dictionary's children and colengths. The row inclusions you must prove are TRUE statements.

### 2.4 The leaves are inside the induction (auditor, this turn)
For `f ≤ 1` the children have `f ≤ 1` (lower, value-0) or `f < 0` (new-class, raise) — and **`f < 0` means an EMPTY child, whose casilla is `(1)`**. So a leaf needs: its LOWER rows, its VALUE-0 row (if `f = 1`), and **`z^{ℓ+f} ∈ K_leaf`** (all remaining rows are the unit ideal). Measured at 9 leaves (`(1,1)` n = 2, 3; `(1,1,1)` n = 4; `(2,1)` n = 4; `(1^4)` n = 5; `(2,1,1)` n = 5; `(2,2)` n = 5; `(1)` n = 2; `(3)` n = 4): **exactly `ℓ+f` nonzero rows, each the true casilla of its child; every other row the unit ideal. 81/81.**
- At a leaf the casilla is the Tanisaki ideal plus the box: `K_leaf = I_λ + box` with `λ := μ ∪ (1^f)`, `ℓ(λ) = ℓ+f`, `I_λ := (e_r(x_S) : S ⊆ [n], r > |S| − d_{|S|}(λ))`, `d_k(λ) := λ'_n + … + λ'_{n−k+1}` (`λ'` the conjugate, padded with zeros to length `n`).
- ⟹ **No separate «Tanisaki colength in characteristic 3» is needed.** T at the leaves follows from the lower and value-0 lemmas at `f ≤ 1` plus **`z^{ℓ(λ)} ∈ I_λ`**, which is (to the auditor's knowledge) the top-power fact of Garsia–Procesi rings, **not yet proved here**.

### 2.5 Proving the rows proves the casilla
The induction never needs `K_μ(n) ⊆ gr I(W_μ(n))`. Once every row inclusion holds, `dim S/K_μ(n) ≤ |W_μ(n)|`; with the easy inclusion `K ⊆ gr I` it gives `K = gr I`. **So the four row lemmas for the uniform casilla prove the conjecture AND the uniform casilla at the same time.** Conversely, **the reduction is strictly stronger than DS 1.2** (it forces `gr I(W_μ(n))` explicit for every `μ`): it is a real reduction, not a restatement, and it could fail while the conjecture holds. It failed nowhere in 180 rows.

## 3 · WHAT IS PROVED OR MEASURED (use it; do not re-prove it)
### 3.1 Earlier theorems (PROVED)
The floor · the Plus Lemma (`(−2)^j = 1` in `F_3`) · the casilla theorems (rows `a ≥ 1` of `I^{(n)}` contain `K_(1)(n−1)`) · `(P_k)` for all `k, q` · `A_k = P_k` for `k ≤ 3`, all `q` · `A_k(3) = P_k(3)` for all `k` · rows 0, 1, `q−1` of the one-part line `K_(m)(n) := (e_odd) + box + (e_n, if n even and m ≥ 1) + N_{m−1}(n)` · rows 0, 1 of `K_{(m,1)}` · the row formula; iterated rows are lex-staircase colons · the engine (§3.5) · the symmetric core `e_{2i}(y) ∈ R_2(K_(m)(n+1))` for `n−m ≤ 2i ≤ n−1` · the fibre ideal (§3.4).
**Layer.** `N_w(n)` is the ideal of the monomials `x_C·x_A^{q−1}` over all splittings `A ⊔ B ⊔ C = [n]` with `|B|−|A| ≤ w` and `|B| ≥ 1`.

### 3.2 THE MODEL — Theorem 2.1 of INFORME_10: (G1) for all `m ≥ 1`, `n`, `q ≥ 9` (PROVED; re-derived by the auditor and re-checked in Singular, 15 cells, `q` up to 243)
**Statement.** For `c := n−m−1 ≥ 1` and `j ≠ l`: **`s_{jl} := y_j^{q−2}e_c(y∖y_l) ∈ R_2(K_(m)(n+1))`.** Hence `R_2(K_(m)(n+1)) ⊇ K_{(m,1)}(n)` and, with rows 0, 1, `q−1`, **every row of every one-part casilla is PROVED for all `q`**; and row 2 (value-0) of every `K_{(m,1)}` is PROVED.
**Notation.** `a := y_j`, `b := y_l`, `u := −a`, `P := y∖{a,b}`, `N := q+c−2`, `D_r := N−2r`, `R := ⌊c/2⌋`, `H_D := Σ_{i=1}^{D−1}u^ib^{D−i}` (= `h_D(u,b) − u^D − b^D`). `J := Ñ_{m−1}(n) + box + (e_n)` (a MONOMIAL ideal); `B := (e_k : k odd or k ≥ n−m) + box + N_{m−1}(n)` (already inside `R_2`).
**The certificate:** **`A_r := (−1)^c·H_{D_r}` for `0 ≤ r ≤ R`, zero beyond.** Only `y_j`, `y_l`: no `e_k`, no layer, no `z³`, no point of `W`.
**Proof skeleton (the recipe to imitate):**
1. **First-order lemma:** if `(T) Σ_rA_re_{2r+1}(y) ∈ J` and `(Sh) Σ_rA_re_{2r}(y) ≡ s mod B`, then `s ∈ R_2`. (Because `z·Σ_rA_re_{2r+1}(y,z) ∈ I^{(n+1)}`, `e_{2r+1}(y,z) = e_{2r+1}(y) + z·e_{2r}(y)`, and `z·J ⊆ K_(m)(n+1)`.)
2. **(T) by two telescopes:** with `e_k(y) = e_k(P) + (b−u)e_{k−1}(P) − ub·e_{k−2}(P)`, the coefficient of `e_p(P)` is `ub^{q+c−2−p} ± u^{q+c−2−p}b` for `p ≤ c−1` (box for `p ≤ c−2`, a layer monomial for `p = c−1`), and has support `≥ c+2` for `p ≥ c`. Telescopes: `ub·H_{D−2} = H_D − ub^{D−1} − u^{D−1}b`, `(b−u)H_D = ub^D − u^Db`.
3. **(Sh) by a generating function:** `Σ_{k even}e_kh_{N−k} = −[t^N](E(t)H(t) + E(−t)H(t))` with `E(t) = Π(1+y_it)`, `H(t) = 1/((1−ut)(1−bt))`, `1/2 = −1`; then `E(t)H(t) = E_P(t)(1+bt)/(1−bt) = E_P(t)(1 − Σ_{k≥1}b^kt^k)`. Result: `Σ_rA_re_{2r} ≡ −s_{jl} + (−1)^c[s_{lj} − (b^{D_R}+u^{D_R})e_{2R}(y)]`.
4. **Three facts in `B`, each a descending telescope finished by the box:** (F) `y_i^{q−2}e_c(y) ∈ B` (and `y_i^{q−1}e_{c−1}(y) ∈ B` for `c` odd); (Sym) `s_{jl}+s_{lj} ∈ B` for `c` even; (Anti) `s_{jl}−s_{lj} ∈ B` for `c` odd — the box kills `a^qb²`, `a^qb` at each step; the Lucas quotients `(a^{q−2}+b^{q−2})/(a+b)`, `(a^{q−1}−b^{q−1})/(a+b)` appear.
5. **Conclusion:** `Σ_rA_re_{2r} ≡ −2s_{jl} = s_{jl}`. ∎
**How it was found (do the same):** the raw M2 lift, even reduced by syzygies, gave 225 unreadable terms; single-variable descents never solved; the ansatz **`A_r ∈ span{y_j^αy_l^β·e_k(y)}`** solved in 0.03 s at 5 variables and its greedy-minimal solution used NO `e_k` (scripts `m10alg.m2`, `a1sym.m2`).

### 3.3 The uniform casilla (MEASURED 53/53 as ideals; not needed separately, see 2.5)
**`K_μ(n) := Q_μ(n) + box + N_{μ_1−1}(n) + F_μ(n)`**, `F_μ(n) := (φ^{(ℓ)}_{jl} : j ≠ l)`,
- **boson form:** `φ^{(ℓ)}_{jl} := y_j^{q−ℓ}·Σ_{i=0}^{ℓ−1} y_j^i·e_{f+ℓ−2−i}(y∖{y_j,y_l})`;
- **fermion form (auditor, equal modulo the box, also gated 13/13):** `φ^{(ℓ)}_{jl} ≡ y_j^{q−ℓ}·Σ_{k≥0} y_j^{2k}·e_{f+ℓ−2−2k}(y∖y_l)`, i.e. `y_j^{q−ℓ}[u^{f+ℓ−2}] E_{y∖y_l}(u)/(1−y_j²u²)`.
- For `ℓ = 2` it is the (G1) family `y_j^{q−2}e_f(y∖y_l)`; for `ℓ = 3`, `y_j^{q−3}(e_{f+1}(y∖y_l) + y_j²e_{f−1}(y∖y_l))`. **Degree `q+f−2` for every `μ`.** The first-factor exponent is a THRESHOLD: every `y_j^{q−ℓ+i}` with `i ≥ ℓ` is in the box.
- **`Q_μ(n) := (e_j([n]) : j odd or j ≥ n−|μ|+1) + (e_r(x_S) : S ⊊ [n], r > |S| − d_{|S|}(λ))`**, `λ := μ ∪ (1^f)`.
- **The layer `N_{μ_1−1}`** is redundant for `(1^ℓ)`, `ℓ ≥ 2` (proved: its smallest generator has degree `q+n−3 > q+f−2`), and NOT redundant for `(m)`, `(m,1)`.
- **Gates:** q = 9: all twelve multi-part profiles, `n ≤ 6` (35 cells incl. 24 leaves), and `(1,1,1)` at `n = 7` (DegreeLimit 17, colength 20370); q = 27: `(1,1)` n = 4, 5; `(2,1)` n = 5; `(1,1,1)` n = 5. **Controls fail as they must** (exponent `q−ℓ+1`, or no family: colength 1110 ≠ 1080, 1980 / 2100 ≠ 1920). **First ungated cell: `(2,1)` at `n = 7`.**

### 3.4 THE CASILLA IS COMPUTABLE (PROVED)
With `S` the anchor multiset of `μ` and **`R_j := Σ_{r=0}^{|μ|} e_r(S)·e_{j−r}(y)`**: **`I(W_μ(n)) = (R_j : j odd, 1 ≤ j ≤ n+|μ|) + (x_i^q − x_i)`**, every `μ`, every odd `q`. *(Proof: `Π_i(T+y_i)·Π_{s∈S}(T+s)` has root multiset closed under negation iff its wrong-parity coefficients vanish.)* **`gr I(W_μ(n))` = the top forms of a degrevlex Gröbner basis** (0.0004–3 s for `n ≤ 6`; `DegreeLimit` + a colength certificate at `n = 7`). The casilla does not depend on the anchor (35/35 + 5/5). One box generator is always redundant (`y_n^q = −Σ_{i<n}y_i^q` modulo `e_1`).

### 3.5 THE ENGINE (PROVED)
- **Row formula.** For `K = (e_odd) + box + M ⊆ S_{n+1}`, `M` generated by `z^i·g(y)`, `M^{[i]} := {g : z^ig ∈ M}`: `f ∈ R_a(K)` iff there are `c^0,…,c^{a−1}` (vectors indexed by odd degrees) with `Σ_rc_r^0e_{2r+1}(y) ∈ box + M^{[0]}`; `Σ_rc_r^ie_{2r+1}(y) + Σ_rc_r^{i−1}e_{2r}(y) ∈ box + M^{[i]}` for `1 ≤ i ≤ a−1`; `f ≡ Σ_rc_r^{a−1}e_{2r}(y)` mod `(e_odd) + box + M^{[a]}`.
- **General form (verified in 11 cells last-but-one turn):** every row inclusion `f ∈ R_a(K)` of every casilla `K = I^{(n+1)} + M` is the membership **`z^{a−1}f ∈ (I^{(n+1)} : z) + (M : z) + (z^a)`**. For multi-part parents `M` contains generators that mix `z` and `y` (the `e_r(x_S)` with `z ∈ S`, and the family with `j` or `l` equal to the last variable): write them out.
- **Lemma H (one-part line):** the slice `{z = w} ∩ W_∅(n+1)` is `w·W_(1)(n)`; if `F ∈ I(W_(1)(n))` has top form in `Ñ_{m−1}(n)`, then `F_{d−1} ∈ R_2(K_(m)(n+1))`. On `W_(1)(n)`, `e_{2i+1}(y) = −e_{2i}(y)`.
- **In general the slice of a parent is its child:** `{x_n = v} ∩ W_μ(n) = W_{μ+v}(n−1)`.

## 4 · THE TARGETS
### PART A — THE VALUE-0 AND NEW-CLASS LEMMAS FOR EVERY ℓ (the must; ~45 %)
**The claim to prove.** For a parent `K_μ(n+1)` with `ℓ` parts:
- **(VZ_ℓ)** `R_ℓ(K_μ(n+1)) ⊇ K_μ(n)` (value-0), and
- **(NC_ℓ)** `R_{ℓ+1}(K_μ(n+1)) ⊇ K_{μ∪(1)}(n)` (the first new-class row).

Everything in `K_μ(n)` except the family is expected to follow from the proved symmetric parts (say so if not). **The heart is the family:** `φ^{(ℓ)}_{jl}(n) ∈ R_ℓ(K_μ(n+1))` and `φ^{(ℓ+1)}_{jl}(n) ∈ R_{ℓ+1}(K_μ(n+1))`. Theorem 2.1 is exactly **(NC_1)** and **(VZ_2)** for `μ = (m,1)`.

**A1 — Extract (budget 30 min).** ⚠️ **Watch the child's `f`:** when the child has `f ≤ 1` it is a LEAF and its family is redundant (the child casilla is `I_λ + box`), so the row is easier and tells you little about the family. The genuine family enters only when the child has `f ≥ 2`. Cells at `q = 9`:
- **(VZ_3) at `(1,1,1)`, `n+1 = 6`** (row 3 → `(1,1,1)` at `n = 5`, `f = 2`, family `y_j^{q−3}(e_3(y∖{j,l}) + y_je_2(y∖{j,l}) + y_j²e_1(y∖{j,l}))`); warm-up at `n+1 = 5` (leaf child).
- **(NC_2) at `(1,1)`, `n+1 = 6`** (row 3 → `(1,1,1)` at `n = 5`, `f = 2`); warm-up at `n+1 = 5` (leaf child).
- (NC_2) at `(2,1)` and (VZ_2) at `(2,2)`, (VZ_4) at `(1^4)`: at `n+1 = 6` the child is a leaf; the genuine family needs `n+1 = 7` (7 variables, one run ALONE, estimate first; a colon in 7 variables was once killed at 570 s — use the membership form of §3.5, not a full colon) or `q = 27` with `n+1 ≤ 5`.
- The auditor's `grepy_filas_verdaderas.m2` gives you, in seconds for `n ≤ 6`, the TRUE rows to aim at.
For rows `a ≥ 3` the row formula has `c^0, …, c^{a−1}`: expect `a−1` layers of the same object. **Use the small ansatz first** — multipliers in `span{y_j^αy_l^β·e_k(y)}` (add a third distinguished letter only if two do not solve, and say so). Also extract at `q = 27` where `n ≤ 5` allows it, to see which exponents carry `q`.
**A2 — Read and prove (budget 60 min).** Closed form with `ℓ`, `μ`, `n`, `q` as letters; then PROVE it: the first-order lemma, telescopes for the top part, the generating function `E(t)/((1−ut)(1−bt))` (or its ℓ-analogue) for the shadow, descending telescopes in the already-proved part. Gate every closed form on the cells of A1 exactly (symbolic normal forms), then on at least two cells you did NOT extract from.
**Prediction from the auditor, sealed:** the family has only two distinguished letters for every `ℓ`, so the certificates of (VZ_ℓ) and (NC_ℓ) are again Lucas objects in `(y_j, y_l)`, with first exponent `q−ℓ`. **Falsify it if you can.**

### PART B — THE RAISE AND LOWER ROWS (~20 %)
- **Raise:** the last `ℓ` rows, `R_{q−ℓ+i}(K_μ(n+1)) ⊇ K_{μ+ε_i}(n)` (`ε_i` raises part `i`). The raise child has `f−2`, so in small cells it is often a leaf: prefer parents with `f ≥ 4` where they fit. Smallest cells: `(1,1)` at `n+1 = 4` (rows `q−2, q−1` → `(2,1)`), `(2,1)` at `n+1 = 5` (row `q−1` → `(3,1)`) and `n+1 = 6` (row `q−2` → `(2,2)`). INFORME_9 saw that raise row `q−2` is a «family shadow»: the child's family should come out of the parent's family by the same certificate type.
- **Lower:** the first `ℓ` rows, `R_{i}(K_μ(n+1)) ⊇ K_{μ−ε}(n)`. Rows 0, 1 of `(m,1)` are PROVED; do `(1,1,1)` at `n+1 = 5` (rows 0..2 → `(1,1)`) and `(2,2)` at `n+1 = 6` (rows 0, 1 → `(2,1)`). The lower rows are the smallest rows, so the child casilla is the biggest ideal: this may be the easy type.
- Prove at least one of the two types with letters for a family of profiles.

### PART C — THE LEAVES WITH LETTERS (~10 %)
- **Prove `z^{ℓ(λ)} ∈ I_λ + box`** for every `λ` (it is the only extra input the leaves need, §2.4). Tools: Tanisaki's generators `e_r(x_S)` and the identity `Σ_r(−1)^re_r(x_S)z^{s−r} = Π_{i∈S}(z−x_i)`; or a citation you read in the original (Garsia–Procesi, Adv. Math. 94 (1992) 82–138, or Griffin, Trans. AMS 374 (2021) 2609–2660) — **then say whether its argument is characteristic-free.**
- Check that your PART A/B lemmas cover the leaf rows (`f ≤ 1`), or state what is missing for them.

### PART D — ROW `k = 4`: THE LEDGER TO ZERO (~15 %)
`A_4(q) = P_4(q)` for all `q` is `T(10)` at `∅`. It needs `T(n)` at every `(μ, n)` with `|μ| ≤ min(n, 10−n)`, `n ≤ 9`; non-leaves are exactly `|μ| ≤ 4`, `|μ|+2 ≤ n ≤ 10−|μ|`. Already PROVED: every row of `∅` and of the one-part profiles `(1)…(4)`; rows 0, 1, 2 of `(1,1)`, `(2,1)`, `(3,1)`. **The open kinds (INFORME_10 §4.2), parent in `n` variables, children in `n−1`:**

| # | parent | rows → child | type | `n` needed |
|---|---|---|---|---|
| 1 | `(1,1)` | `3..q−3` → `(1,1,1)` | new class | 4..8 |
| 2 | `(1,1)` | `q−2, q−1` → `(2,1)` | raise | 4..8 |
| 3 | `(2,1)` | `3..q−3` → `(2,1,1)` | new class | 5..7 |
| 4 | `(2,1)` | `q−2` → `(2,2)` | raise small | 5..7 |
| 5 | `(2,1)` | `q−1` → `(3,1)` | raise large | 5..7 |
| 6–8 | `(3,1)` | new class → `(3,1,1)`; `q−2` → `(3,2)`; `q−1` → `(4,1)` | as 3–5 | 6 |
| 9 | `(2,2)` | 0, 1 → `(2,1)` | lower | 6 |
| 10 | `(2,2)` | 2 → `(2,2)` | value 0 | 6 |
| 11 | `(2,2)` | `3..q−3` → `(2,2,1)` | new class | 6 |
| 12 | `(2,2)` | `q−2, q−1` → `(3,2)` | raise | 6 |
| 13 | `(1,1,1)` | 0..2 → `(1,1)` | lower | 5..7 |
| 14 | `(1,1,1)` | 3 → `(1,1,1)` | value 0 | 5..7 |
| 15 | `(1,1,1)` | `4..q−4` → `(1^4)` | new class | 5..7 |
| 16 | `(1,1,1)` | `q−3..q−1` → `(2,1,1)` | raise | 5..7 |
| 17–22 | `(2,1,1)` | lower → `(1,1,1)`, `(2,1)`; value 0; new class → `(2,1,1,1)`; raise → `(2,2,1)`, `(3,1,1)` | | 6 |
| 23–26 | `(1^4)` | lower → `(1^3)`; value 0; new class → `(1^5)` (only `q ≥ 27`); raise → `(2,1,1,1)` | | 6 |

**Plus the leaf rows** (lower and value-0 at `f ≤ 1`, and `z^{ℓ(λ)} ∈ K_leaf`) for every leaf with `|μ| ≤ min(n,10−n)`. Give every row a status: **PROVED** (by which lemma) / **OPEN** (what is missing, smallest cell). **If none is OPEN: write «ROW k = 4 CLOSED FOR ALL q» and the full chain.**

## 5 · PROCESS
- **STEP 0 — Design and sealed bets (15 min, no runs).** Plan, with an estimate for every run. **Seal at least FIVE predictions before running anything, at least TWO risky.** Examples: «the (VZ_3) certificate lives in `(y_j,y_l)` alone»; «the raise certificate is the (G1) certificate with `q−2 → q−ℓ`»; «(NC_2) needs a third letter»; «`z^{ℓ(λ)} ∈ I_λ` holds with coefficients `±1`». Score them at the end, hits and falsified printed the same size.
- **STEP 1 — PART A, A1 (30 min).** **STEP 2 — PART A, A2 (60 min).** **STEP 3 — PART B (45 min).** **STEP 4 — PARTS C and D (40 min).** **STEP 5 — Verdict (10 min)**, after re-reading the disk.
- **WHAT I FOUND BEAUTIFUL:** one paragraph.
- **FOR MISSION 12:** the lemmas proved, the smallest open cell of each type, and your estimate of what closing all four types for every `μ` still takes.

## 6 · DEAD ROUTES (do not retry)
- Counting lemmas for rows (the counts ARE the induction) · «rows ⊆ fibres» as a formal consequence (false in general, three points) · the sum of colons alone for generic rows.
- Reading certificates from the syzygy normal form of a raw lift (canonical for the order, not for the mathematics) · single-variable descents · the first-order single-multiplier ansatz · the lift lemma and monotonicity for (G1) (inert).
- Guessing interaction families and gating them by colength: the casilla is COMPUTABLE (§3.4); read it.
- The uniform second factors `e_{f+ℓ−2}(y∖y_l)`, `h_{f+ℓ−2}(y∖y_l)`, `p_{f+ℓ−2}(y∖y_l)` for every `μ`; any `S_n`-orbit of a two-variable monomial for `(1,1,1)` at `n = 7`.
- The printed sign of (O′) in INFORME_9 (the correct second term is `+u^{q−1}(1−y_l^{q−1})e_{n−3}(P)`); antisymmetrising (O′). (INFORME_10 closed the odd case without it.)
- Any ascent in `q` (a tower elevator): dead, with proof.
- Measuring cells as a substitute for a mechanism: cells are gates only.
- A separate characteristic-3 Tanisaki colength theorem for the leaves: NOT needed (§2.4).

## 7 · SUCCESS
- **Minimum:** one whole row type proved with letters for a new infinite family, plus its certificates written down.
- **Good:** **ROW `k = 4` CLOSED FOR ALL q.**
- **Excellent:** all four types for every two-part profile, plus (VZ_ℓ) for every `ℓ`.
- **Full:** **the four row lemmas for every profile ⟹ CONJECTURE 1.2 CLOSED FOR ALL `k` AND ALL `q`.**

*Last word from the auditor.* Last turn a lemma that had resisted two missions turned out to be one line in two letters. Every row you are asked to prove is already known to be true, in every cell that fits in this machine. The wall is not infinite any more: it is four doors, and one of them is already open. Open the next.

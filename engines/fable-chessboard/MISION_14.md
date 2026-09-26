# MISSION 14 — THE GENERATING FUNCTION. ROW `k = 4` HAS FALLEN; EVERY CASILLA IS ONE COEFFICIENT OF ONE POWER SERIES.
*(Grepy el Lector, auditor, 2026-09-23.)*

**You are a NEW Fable. This file is SELF-CONTAINED: read it whole before anything else; you need nothing else.**
- The reports `INFORME.md` … `INFORME_13.md` in this folder are audited and APPROVED. Open them only to quote a proof summarised here. **Your templates: INFORME_13 §2.1 (Theorem T), §3.1 (Lemma Z), §3.3 (Theorem R), §4.2 (Lemma V).** They are four instances of ONE trick, and this mission asks you to make that trick a theorem.
- **Engines of the auditor, in this folder** (all run inside the watchdog, §0 rule 10):
  - `grepy_vigia.sh`: the watchdog you MUST use.
  - `grepy_verif.py`: exact polynomial identities over `F_3` mod box, pure Python, no Gröbner. It re-checked Theorems T, R and Lemma Z in the real letters (8/8, 5/5, 6/6) and the fibre counts by EGF. Read it and reuse its functions (`elem`, `hcomp`, `mul`, `W`).
  - `grepy_mapa.py MU N Q OUT.sing`: writes a Singular file that prints `vdim` of the UNIFORM casilla `K^{unif}_μ(n)` over `F_3`.
  - `grepy_gamma_vdim.py MU N Q L RMIN RMAX W OUT.sing`: the same, plus the generating-function objects `Γ^{(L)}_r` (§3.5) for `r ∈ [RMIN, RMAX]` and `|B| = |A| + W`. It needs `grepy_mapa.py` in the same folder.
  - `grepy_fila2.py`: degree-bounded homogeneous membership of a row inclusion over `F_3`.
  - `cert12.py`: the homogenized certifier of true casillas.
  - Your predecessors' scripts: `g2gate.py`, `g2full.py`, `row0g.py`, `raiseg.py`, `ledger13.py`.

> **OBJECTIVE of the campaign: the complete closure of Conjecture 1.2 of Degtyarev–Shimada, for all `k` and all `q = 3^v`.**
>
> **Where we stand — every item verified by the auditor by a second route:**
> - **ROW `k = 4` IS CLOSED FOR EVERY `q`.** `A_4(q) = P_4(q)`, the first new row of the conjecture since `k = 3`. Your predecessor proved the last five inclusions (INFORME_13). The auditor re-derived every step by hand and re-checked every certificate with his own code, including one in 9 variables that no Gröbner engine may touch.
> - **The conjecture now stands at:** `q = 3` for every `k`; `k ≤ 4` for every `q`. **OPEN: `k ≥ 5`, `q ≥ 9`.**
> - **THE SCENT OF THE PREY.** Every certificate of the last turn was the same object: the odd part of `E(t)·H(t)`, where `E(t) = Π(1+y_it)` and `H(t) = Π_{a∈A}(1+at)^{−1}·Π_{b∈B}(1−bt)^{−1}` splits the letters into HEAVY `A` and ABSENT `B`. The auditor then found that the OBJECTS of the casillas are coefficients of that same series:
>   - `Γ^{(ℓ)}_r(A;B) := [t^{r(q−1)+|P|+1−ℓ}] E(−t)H(t)` mod box, where `P` is the set of remaining letters;
>   - at `ℓ = 1` this is the layer of `(1)`; at `ℓ = 2`, the whole `(1,1)` tower; at `r = 1`, the first family of EVERY `(1^ℓ)`.
> - **And it PREDICTS.** Row `k = 5` forces a correction nobody had found: the uniform casilla of `(1,1,1)` in 8 variables is too big by EXACTLY 280 dimensions. **Adding the objects `Γ^{(3)}_2` removes EXACTLY those 280, no more** (`vdim` = 128 016 = `|W|`, at `q = 9`). **The same series with one more absent letter gives EXACTLY the known `(2,2)` family at `n = 7`** (3 570 = `|W|`), and **the `(1,1)` tower gives EXACTLY `|W|` at `n = 7` and `n = 8`.** Four cells, four exact hits, zero free parameters.
> - **And it SHIFTS.** Exact, one line (§3.5): `Γ^{(ℓ)}(n+1) = Γ^{(ℓ−1)}(n) − z·Γ^{(ℓ)}(n)` (the «Pascal rule»). Setting `z = 0` lowers the level `ℓ` by one, which is exactly what a LOWER row does to a profile `(1^ℓ)`. **The row dictionary looks like index arithmetic on one power series.**
>
> **This mission: turn that into the induction — the positions of every row as index shifts of `E(−t)H(t)` — close row `k = 5`, and aim at every `k`.**
>
> **Prize ladder:**
> - **MINIMUM — THE `(1^ℓ)` CHAIN FOR EVERY `k`:** with `K_{(1^ℓ)}(n) := K^{unif}_{(1^ℓ)}(n) + (Γ^{(ℓ)}_r(A;B) : r ≥ 2, |A| = |B| = r)`, prove with `ℓ, r, n` as letters and for every `q = 3^v ≥ 9`:
>   - **(A2) value-0:** `z^ℓ·Γ^{(ℓ)}_r(n) ∈ K_{(1^ℓ)}(n+1) + (z^{ℓ+1})` (for `ℓ = 2` this is Lemma V);
>   - **(A3) new-class:** `z^{ℓ+1}·Γ^{(ℓ+1)}_r(n) ∈ K_{(1^ℓ)}(n+1) + (z^{ℓ+2})` (for `ℓ = 1` this is Theorem T).
>
>   With (A1) (row 0, already proved, §3.5) these are all the positions of `(1^ℓ)` except the raise.
> - **GOOD — ROW `k = 5` CLOSED FOR ALL `q`.** The full ledger of `T(12)` printed with a proof source on EVERY line and no OPEN line. If you get there, write in your FIRST LINE, in capitals: «ROW k = 5 CLOSED FOR ALL q», with the chain.
> - **EXCELLENT — THE `Γ`-LAW FOR EVERY PROFILE:**
>   - a rule saying which `Γ^{(s)}_r(A;B)` (level `s`, imbalance `|B| − |A|`) enter `K_μ(n)` for EVERY `μ`;
>   - gated by `vdim = |W|` at every computable cell;
>   - the four row positions proved as index shifts for every profile.
>
>   ⟹ the partition induction for every `k`, modulo a named finite list.
> - **FULL: CONJECTURE 1.2 CLOSED FOR ALL `k` AND ALL `q`.**
>
> **Do not underestimate yourself.** Last turn the auditor sealed «row `k = 4` will NOT close this turn» and «#5 will NOT be proved». Your predecessor falsified both, with four lines of generating function each. The machine is built. Floor 1 took three telescopes; floor `r` took the same four lines. **Level `ℓ` should take the same four lines too. Bite.**

---
## 0 · RULES OF THE TURN (mandatory)
1. **BEFORE THINKING:** create `INFORME_14.md` with these empty sections:
   `## FIRST LINE` · `## STEP 0 — DESIGN AND SEALED BETS` · `## STEP 1` · `## STEP 2` · `## STEP 3` · `## STEP 4` · `## STEP 5 — VERDICT` · `## WHAT I FOUND BEAUTIFUL` · `## FOR MISSION 15`.
2. **Save to disk after every step.** What is not written does not exist. If your session is cut, what is on disk IS your delivery.
3. **Header per step:** `STATE: CLOSED | EXHAUSTED | NOT CONCLUDED` and `NEXT:`.
4. **Timing:**
   - work in order, no going back, no retries;
   - write the budget before each step;
   - after 10 minutes without progress: stop, write, declare;
   - keep the last 20 % of each budget for writing.
5. **At most one literature search per step**, in the original source.
6. **Do not recompute anything listed here as proved or measured** (§3). Re-gating a CLOSED FORM of yours on a measured cell is allowed and expected.
7. **A negative dimension, or one larger than the box, is a bug:** stop.
8. **«This route dies, for this reason» is a result.** A falsified sealed bet is worth more than a safe hit.
9. **Write ONLY in `~/Desktop/FABLE_TABLERO/`. Do not open anything in `~/Desktop/ARBOLYAML/`.**
10. **Machine and guardrail — EVERY engine runs inside the watchdog:** `zsh grepy_vigia.sh LOGFILE 'the whole command'`.
    - The LOG is the FIRST argument. It kills at **1.2 GB of RSS (whole process tree) or 600 s**; the last line of the log says how it ended.
    - 🔴 **WRITE THE ESTIMATE IN THE REPORT BEFORE EACH RUN, ENGINE BY ENGINE — INCLUDING THE SMALL ONES.** Three turns in a row a small run went without one.
    - 🔴 **Singular reads its input from stdin when the file is empty, and then waits forever.** Check that the `.sing` file is non-empty, and launch as `Singular -q FILE < /dev/null`. Use `python3 -u`.
    - You MAY run TWO engines at once if their estimates add up to less than 1.2 GB. **Any run estimated above 30 s runs ALONE.**
    - After any kill, check with `pgrep` that it is gone, and write that you checked. When you finish, check that nothing of yours is still running.
    - **Allowed:**
      - full Gröbner (M2 or Singular): `n ≤ 10` variables at `q = 3`; `n ≤ 7` at `q = 9`; `n ≤ 5` at `q = 27`; `n ≤ 4` at `q = 81`. The certifier counts `t` as a variable.
      - **`vdim` of a casilla over `F_3` with the real exponent `q = 9`** (the auditor's `grepy_mapa.py` / `grepy_gamma_vdim.py`), `n ≤ 8`, ALONE. Measured costs:
        - `(1^ℓ)` at `n = 8`: 2–48 s;
        - `(1,1)(8)` with the tower: 353 s;
        - `(1^3)(8)` with `Γ^{(3)}_{2..4}`: 456 s, at the edge;
        - **`(2,1)(8)` uniform: KILLED at 600 s** (its layer `N_1` is large) — do not repeat it as is.
      - **Degree-bounded homogeneous membership over `F_3`** (Singular `degBound`): `n ≤ 8` at `q = 9`, ALONE (192 s); `n ≤ 6` at `q = 27`.
      - **Pure-Python polynomial identities (no Gröbner)** at any size that fits the caps. **This is how the 9-variable cells are gated:** the certificate itself, checked exactly in the real letters. The auditor did it for your predecessor's cell #4 in 18 s.
    - **Forbidden:** any other Gröbner run beyond those caps; any Gröbner or `vdim` run in 9 variables at `q = 9`.
11. **In characteristic 3, never average over a group whose order is divisible by 3.** Make a certificate canonical by REDUCTION, not by averaging. **Read certificates from a SMALL ANSATZ or from the generating function, never from a raw syzygy normal form.**
12. **Re-read the disk before the verdict.**
13. **Double check:**
    - every PROVED claim carries its proof in the report;
    - every number carries its cell and its log;
    - every identity used in a proof is checked exactly, symbolically or at ≥ 2 cells in the real letters;
    - every certificate is re-verified as an exact identity or membership at two values of `q` or more.
14. 🔴 **Sealed bets must be able to FAIL WHERE THE STATEMENT HAS CONTENT.** A bet that can only fail at a cell where it is trivially true is SAFE, whatever you label it. Example of content: `(1^3)` at `n = 8` (the uniform casilla is too big there); non-content: `(1^3)` at `n = 7` (it is already exact).

**FIRST LINE** (answer first, in this order):
- (a) Are (A2) and (A3) PROVED for every `ℓ, r, n, q`? If yes, the certificate of each in one line.
- (b) The `Γ`-law: stated for which profiles? gated at which cells? which cell, if any, broke it?
- (c) The full ledger of row `k = 5` (PART D): how many lines, how many PROVED, how many OPEN? **If none is OPEN: «ROW k = 5 CLOSED FOR ALL q», with the chain.**
- (d) The raise positions (PART C): which are proved?

---
## 1 · THE OBJECTS
### 1.1 Basics
- `q = 3^v`, `h := (q−1)/2`, `S_n := F_q[x_1..x_n]`.
- `e_r` is the elementary symmetric polynomial (`e_0 = 1`; `e_r = 0` for `r < 0` or `r >` the number of variables).
- `box := (x_1^q, …, x_n^q)`. **`I^{(n)} := (e_1, e_3, e_5, …) + box`.**
- `x_C := Π_{i∈C}x_i`; `x_A^{q−1} := Π_{i∈A}x_i^{q−1}`.
- `h_D(u_1,…)` is the complete homogeneous polynomial of degree `D`.
- `gr I(X)` is the ideal of top forms of the polynomials vanishing on `X ⊆ F_q^n`; **for a finite set, `dim S_n/gr I(X) = |X|`.**

### 1.2 Profiles and fibres
A multiset `S ⊂ F_q` (the **anchor**) constrains `y ∈ F_q^n` by «`y ∪ S` is closed under negation».
- Its **profile** `μ = (μ_1 ≥ … ≥ μ_ℓ)` has one positive part per non-zero class `{s,−s}`: how many more copies of `−s_i` than of `s_i` the point `y` must carry.
- `|μ| := Σμ_i`, `ℓ := ℓ(μ)`, **`f := n − |μ|`**.
- **`W_μ(n) := {y ∈ F_q^n : y ∪ S closed}`**, up to bijection a function of `μ` (gated as ideals, anchor-free).
- **Fibre ideal (PROVED):** with `R_j := Σ_r e_r(S)e_{j−r}(y)`, `I(W_μ(n)) = (R_j : j odd) + (x_i^q − x_i)`.
- **Fibre sizes (PROVED, exact EGF):** `|W_μ(n)| = n!·[x^n] e^x·Π_{i≤ℓ} I_{μ_i}(2x)·I_0(2x)^{h−ℓ}`, with `I_d(2x) := Σ_{a≥0} x^{2a+d}/(a!(a+d)!)`; zero if `ℓ > h`. At `q = 9`, `n = 0..11`:

| `μ` | `n = 0 … 11` |
|---|---|
| `∅` | 1, 1, 9, 25, 217, 921, 7761, 41889, 345465, 2162617, 17605249, 121120209 |
| `(1)` | 0, 1, 2, 24, 88, 855, 4266, 37947, 227144, 1930329, 12939370, 107436494 |
| `(2)` | 0, 0, 1, 3, 46, 210, 2340, 13496, 130984, 868680, 7838295, 56601325 |
| `(1,1)` | 0, 0, 2, 6, 84, 380, 3930, 22302, 204456, 1329624, 11508930, 81511430 |
| `(3)` | 0, 0, 0, 1, 4, 75, 410, 5201, 34104, 362670, 2648220, 25579125 |
| `(2,1)` | 0, 0, 0, 3, 12, 200, 1080, 12390, 79408, 779436, 5529240, 50254545 |
| `(1,1,1)` | 0, 0, 0, 6, 24, 360, 1920, 20370, 128016, 1189944, 8266320, 72322470 |
| `(4)` | 0, 0, 0, 0, 1, 5, 111, 707, 10094, 74214, 862170, 6883602 |
| `(2,2)` | 0, 0, 0, 0, 6, 30, 570, 3570, 44380, 315756, 3269700, 24996180 |
| `(3,1)` | 0, 0, 0, 0, 4, 20, 390, 2450, 31248, 223776, 2371740, 18301140 |
| `(2,1,1)` | 0, 0, 0, 0, 12, 60, 1020, 6300, 72240, 502992, 4934160, 36899280 |
| `(1,1,1,1)` | 0, 0, 0, 0, 24, 120, 1800, 10920, 115920, 789264, 7363440, 53895600 |
| `(5)` | 0, 0, 0, 0, 0, 1, 6, 154, 1120, 17802, 145092, 1832457 |
| `(3,2)` | 0, 0, 0, 0, 0, 10, 60, 1295, 9240, 125496, 984480, 10880100 |
| `(4,1)` | 0, 0, 0, 0, 0, 5, 30, 672, 4816, 67914, 538020, 6157470 |
| `(2,2,1)` | 0, 0, 0, 0, 0, 30, 180, 3360, 23520, 286020, 2174760, 22245300 |
| `(3,1,1)` | 0, 0, 0, 0, 0, 20, 120, 2310, 16240, 203112, 1557360, 16303980 |
| `(2,1,1,1)` | 0, 0, 0, 0, 0, 60, 360, 5880, 40320, 453600, 3366720, 32792760 |

`P_5(9) = |W_∅(12)| = 980 612 161`.

### 1.3 Rows
For `K ⊆ S_n` with `z := x_n` and `z^q ∈ K`:
- **row `a`** is `R_a(K) := π_z(K : z^a) ⊆ S_{n−1}`, where `π_z` sets `z = 0`;
- equivalently, **`f ∈ R_a(K)` ⟺ `z^a·f ∈ K + (z^{a+1})`**;
- **rows INCREASE with `a`**;
- **`dim S_n/K = Σ_{a=0}^{q−1}dim S_{n−1}/R_a(K)`**;
- **row 0 is the substitution `K|_{z=0}`.**

### 1.4 The conjecture
- `A_k(q) := dim S_{2k+2}/I^{(2k+2)}` and `P_k(q) := |W_∅(2k+2)|`.
- **Conjecture 1.2: `A_k(q) = P_k(q)`.** The floor `A ≥ P` is PROVED, so **the conjecture ⟺ `A_k(q) ≤ P_k(q)`**.
- **Proved: `q = 3` for every `k`; `k ≤ 4` for every `q`. Open: `k ≥ 5` and `q ≥ 9`.**

### 1.5 The casillas
**Uniform casilla** `K^{unif}_μ(n) := Q_μ(n) + box + N_{μ_1−1}(n) + F_μ(n)`:
- **`Q_μ(n) := (e_j([n]) : j odd or j ≥ f+1) + (e_r(x_S) : S ⊊ [n], r > |S| − d_{|S|}(λ))`**, with `λ := μ ∪ (1^f)`, `d_k(λ) := λ'_n + … + λ'_{n−k+1}` (`λ'` the conjugate, padded to length `n`).
- **Layer:** `N_w(n)` is generated by the `x_A^{q−1}x_C` over all splittings `A ⊔ B ⊔ C = [n]` with `|B| − |A| ≤ w` and `|B| ≥ 1`. So `B` is the ABSENT set. The layer is **OMITTED for `(1^ℓ)`, `ℓ ≥ 2`**; it is INCLUDED for `(1)` (`N_0`) and for every `μ` with `μ_1 ≥ 2`.
- **Family:** `φ^{(ℓ)}_{jl} := y_j^{q−ℓ}Σ_{i=0}^{ℓ−1}y_j^ie_{f+ℓ−2−i}(y∖{y_j,y_l})`, over all `j ≠ l`.
- **Leaves** (`f ≤ 1`): the Tanisaki ideal `I_λ + box`.
- **Uniform is exact where measured** (`vdim = |W|`, `q = 9`), except where it is too big:
  - `(1,1)` at `n = 7, 8`: 22 337 vs 22 302 and 204 820 vs 204 456;
  - `(2,2)` at `n = 7`: 3 675 vs 3 570;
  - **`(1,1,1)` at `n = 8`: 128 296 vs 128 016 (NEW; this cell is in row `k = 5`).**
  - EXACT at `n = 7`: `(3,1)`, `(3,2)`, `(4,1)`, `(2,1,1)`, `(2,2,1)`, `(3,1,1)`, `(1^4)`, `(2,1^3)`, `(1^3)`; and `(1^4)` at `n = 8`.
  - Not measured: `(2,1)(8)` (killed at 600 s), `(2,2)(8)`, `(3,1)(8)`, `(2,1,1)(8)`, and everything at `n ≥ 9`.

## 2 · THE FRAMEWORK (sound; re-checked by the auditor)
**`T(n)`:** for every profile `μ` there is an EXPLICIT ideal `K_μ(n) ⊆ S_n` with:
- `z^q ∈ K_μ(n)`;
- `K_∅(n) = I^{(n)}`;
- `K_μ(n) = (1)` when `W_μ(n) = ∅`;
- **`dim S_n/K_μ(n) ≤ |W_μ(n)|`**.

**Inductive step:** `T(n−1) ⟹ T(n)` at `μ` as soon as, under the bijection rows ↔ values of `z` below, **`R_a(K_μ(n)) ⊇ K_{child(a)}(n−1)` for every `a`**.
- Within a block of rows with the SAME child, only the FIRST row needs proof (rows increase).
- **Base:** `n = 0`. **`T(2k+2)` at `μ = ∅` is the conjecture.**
- 🔴 **Membership `K_μ ⊆ gr I(W_μ)` is NEVER used.** The chain carries only UPPER bounds.
- 🟢 **The casilla may be taken MAXIMAL** (the auditor's reading of the last turn). Adding generators to `K_μ(n)` makes its OWN rows easier and its PARENTS' rows harder. It is safe as long as every line is proved.
  - Example: with EVERY tower floor in `K_{(1,1)}`, row 0 of `(1,1)` needs no rank argument, because the floors restrict to the child's layer by substitution. The question «which floors are needed at which `n`» leaves the critical path.
  - A `vdim = |W|` gate at a cell says the chosen `K` is not too big there. It is NOT a proof, and it is NOT needed for the chain; it is the compass.

**Row dictionary** (a parent with `ℓ` parts; the bijection with values of `z` is checked by the EGF counts, 0 mismatches at `q = 9, 27, 81, 243`):
- **LOWER**, rows `0 … ℓ−1`: lowers one part, largest first.
- **VALUE-0**, row `ℓ`: same `μ`, `f−1`.
- **NEW-CLASS**, rows `ℓ+1 … q−ℓ−1`: `μ ∪ (1)`.
- **RAISE**, the last `ℓ` rows: raises one part, smallest first.

For `(1^ℓ)` at `n+1`: rows `0..ℓ−1` → `(1^{ℓ−1})`; row `ℓ` → `(1^ℓ)`; rows `ℓ+1..q−ℓ−1` → `(1^{ℓ+1})`; the last `ℓ` rows → `(2,1^{ℓ−1})`.

**Row `k = 5`** is `T(12)` at `∅`. It visits exactly the `(μ, n)` with `|μ| ≤ min(n, 12−n)`: 115 cells at `q = 9`, of which 70 are non-leaf parents (`f ≥ 2`); at `q ≥ 27` add `(1^5)(7)`.
- 40 of the 70 are the parents of row `k = 4`, all PROVED (INFORME_13 §4.1).
- **The 30 NEW parents:**
  - `∅(11)`, `∅(12)`;
  - `(1)(10)`, `(1)(11)`, `(2)(9)`, `(2)(10)`, `(3)(8)`, `(3)(9)`, `(4)(7)`, `(4)(8)`, `(5)(7)`;
  - `(1,1)(9)`, `(1,1)(10)`, `(2,1)(8)`, `(2,1)(9)`, `(2,2)(7)`, `(2,2)(8)`, `(3,1)(7)`, `(3,1)(8)`, `(3,2)(7)`, `(4,1)(7)`;
  - `(1,1,1)(8)`, `(1,1,1)(9)`, `(2,1,1)(7)`, `(2,1,1)(8)`, `(2,2,1)(7)`, `(3,1,1)(7)`, `(1^4)(7)`, `(1^4)(8)`, `(2,1^3)(7)`.

## 3 · WHAT IS PROVED OR MEASURED (use it; do not re-prove it)
### 3.1 Lemma M (INFORME_12)
Every casilla is generated over `F_3`: by `q`-free polynomials, and by generators `x_{H'}^{m+c}·Ψ` with `Ψ` `q`-free and `m := q − const`.
- Fix `H`, put `u := Π_{h∈H}h`, and let `J(m)` be generated by the `q`-free generators and those with `H' ⊆ H`. **Then `u·J(m) ⊆ J(m+1)`.**
- Hence ONE `F_3` membership at a small `m_0` proves an inclusion for every `q`.
- Its limit: a second heavy letter absent from the target (the certificate is then a Lucas object `h_D`, `D ≈ q`).

### 3.2 The one-part line and the earlier theorems (INFORME_10, 11, 12)
- **(G1)** (INFORME_10 Thm 2.1): `y_j^{q−2}e_c(y∖y_l) ∈ R_2(K_{(m)}(n+1))` for `m ≥ 1`, `c = n−m−1 ≥ 1`, `q ≥ 9`. **The whole one-part line `(m)` is closed for every `q`.**
- **INFORME_11:**
  - Theorems A (value-0 of `(1^ℓ)`), B (new-class of `(1^ℓ)`), C (lower rows, uniform parts), D (leaves), E (the hooks `(m,1^{ℓ−1})`: lower, value-0, new-class, large raise);
  - the rows with a LEAF child, `q`-free (R11, R12).
- **INFORME_12:**
  - Theorem B' (the `f = 2` lemma: for `(2,1^{L−2})`, `L = 3, 4, 5`, the layer `N_1` lies in `Q + box + F`);
  - the tower identities;
  - `y_c²D_{j;cd} ∈ Q + N_0 + F` for `(1,1)`.

### 3.3 THE LAST TURN (INFORME_13; re-derived by the auditor by hand, gated with his own code)
Notation: `y` = the `n` letters, `z` the new one, `A, B ⊆ [n]` disjoint, `|A| = |B| = r`, `P := y∖(A∪B)`, `G_r(A;B) := x_A^{q−2}e_{n−r−1}(y∖B)` (the `(1,1)` tower; `G_1 = φ`, `G_2 = F2`), `E_P(t) := Π_{p∈P}(1+pt)`, `H(t) := Π_{a∈A}(1+at)^{−1}Π_{b∈B}(1−bt)^{−1} = Σh_Dt^D`, so `h_D = h_D(−x_A, x_B)`.
- **The factorisation (the key):** `E(t)H(t) = E_P(t)·Π_{b∈B}(1+bt)/(1−bt)` and `E(−t)H(t) = E_P(−t)·Π_{a∈A}(1−at)/(1+at)`: **the heavy letters disappear from one product and the absent ones from the other.** In `F_3`, `1/2 = −1`, so `Σ_{k odd}e_kt^k = −(E(t) − E(−t))`.
- **THEOREM T** (every `r ≥ 1`, `n ≥ 2r`, `q`): `z²G_r(A;B)(n) ∈ (e_odd(y,z)) + box + N_0(n+1) + (z³)`.
  - Certificate: `Φ := Σ_{k odd}(z·h_{N+1−k} − z²·h_{N−k})·e_k(y,z)`, `N := deg G_r`.
  - `Φ ≡ z·[−2^rx_P(x_B^{q−1} − (−1)^nx_A^{q−1})] + z²·2^{r+1}(−1)^nG_r(A;B)` mod box + `(z³)`.
- **LEMMA Z / THEOREM Z:** `Σ_{k odd}e_k(y)h_{M−k}(−x_A, x_E) ≡ (−1)^{|P|−1}2^rx_A^{q−1}e_{|P|−1}(P)` mod box + (lower layers), for `|E| = r−1`. Its consequence: row 0 of `(1,1)(n)` contains the child's floor-`r` layer when `n ≤ 2r+2`. The relations are indexed by the incidence matrix of `K_{r+1}`, which has full rank over `F_3`.
- **THEOREM R** (`n ≥ 5`, `q ≥ 9`): `z^{q−2}φ^{(2)}_{jl}((2,2),n) ∈ K^{unif}_{(2,1)}(n+1) + (z^{q−1})`.
  - Certificate: `(−1)^nΣ_{k odd}e_k(Y)h_{M−k}(−y_j,−z,y_l) − z^{q−4}ψ_{jl} − y_j^{q−4}ψ_{zl}`, with `ψ_{ab} := y_a^{q−2}e_{n−2}(Y∖b)` the parent's family and `M = 2q+n−8`.
  - **A three-letter odd identity, plus two members of the parent's own family.**
- **LEMMA V:** `z²G_r(n) ≡ (z − y_a)G_r(n+1)` mod box (every floor).
- **ROW `k = 4` CLOSED FOR ALL `q`:** INFORME_13 §4.1, 153 ledger lines, 0 OPEN. **Its generator `ledger13.py` is your template for PART D.**
- Measured, not proved:
  - «floor `r` needed iff `f ≥ 2r+1`» is FALSE at `r = 3`;
  - `G_3` was never needed at any measured cell.

### 3.4 Open items your predecessor listed for `k = 5`
1. Row 0 of `(2,1)(8)` and rows 0–2 of `(1^3)(8)` must contain `F2(7)` (the corrected `(1,1)(7)`). Rows increase, so for `(1^3)` only row 0 is needed.
2. The raise rows of `(1,1)(9)`, `(1,1)(10)` → `(2,1)`.
3. `(2,2)(7)`, `(2,2)(8)`: the casilla needs the family `H_{j;k;l} := y_j^{q−2}y_k²e_{f−1}(y∖{k,l})` (certified true at `n = 7`); its rows and its parents' rows are new.
4. The `ℓ ≥ 3` second families (now: see §3.5).

### 3.5 THE GENERATING FUNCTION (auditor; the scent of the prey)
**Definition.** For disjoint `A, B ⊆ [n]` (any sizes), `P := [n]∖(A∪B)`, `r := |A|`, and a level `ℓ ≥ 1`:
**`Γ^{(ℓ)}(A;B)(n) := [t^D] E_{[n]}(−t)·Π_{a∈A}(1+at)^{−1}·Π_{b∈B}(1−bt)^{−1}`, reduced mod box, with `D := r(q−1) + |P| + 1 − ℓ`.**
- **Closed form (PROVED, pencil):** `Γ^{(ℓ)}(A;B) = (−1)^D·2^r·Σ_{p=0}^{|P|} e_p(P)·h°_{D−p}(x_A)`, valid for `ℓ ≤ q−1`, where `h°_m(x_A)` is the sum of the monomials of degree `m` in the letters `A` with EVERY exponent in `[1, q−1]`.
  - Proof: `E(−t)H(t) = E_P(−t)·Π_{a∈A}(1−at)/(1+at)`, so `B` disappears whatever its size.
  - The coefficient of `Π_a a^{i_a}` in the second factor is `Π_{i_a≥1}2·(−1)^{Σi_a}`, and `E_P(−t)` contributes `(−1)^p`, so the sign is `(−1)^D`.
  - A monomial with some `i_a = 0` would need degree `≥ r(q−1)+1−ℓ` in `r−1` letters, which forces an exponent `≥ q`: box.
- **What it is (PROVED identities; `|A| = |B| = r` unless said):**
  - `ℓ = 1`: `Γ^{(1)} = (−1)^{|P|}2^r·x_A^{q−1}x_P`, the layer generator (`N_0` of `(1)`). With `|B| = |A| + w` it gives the generators of `N_w`.
  - `ℓ = 2`: `Γ^{(2)} = (−1)^{|P|−1}2^r·G_r(A;B)`, the whole `(1,1)` tower.
  - `r = 1`, profile `(1^ℓ)` (`f = n − ℓ`): `Γ^{(ℓ)}(j;l) = 2(−1)^D·φ^{(ℓ)}_{jl}`, the first family of EVERY `(1^ℓ)`.
  - `ℓ = 3`, `r = 2`: `Γ^{(3)}(ab;cd) = (−1)^D·x_A^{q−3}·Σ_{d=0}^{2}(ab)^d·h_{2−d}(a,b)·e_{|P|−d}(P)` (`4 = 1`).
- **THE PASCAL RULE (PROVED, one line; the engine of the index shifts).** For `z ∉ A ∪ B`, `Γ^{(ℓ)}(A;B)(n+1) = Γ^{(ℓ−1)}(A;B)(n) − z·Γ^{(ℓ)}(A;B)(n)`, exactly.
  - Proof: `E_{P∪z}(−t) = E_P(−t)(1 − zt)`, and the degree index drops by one when `|P|` grows by one.
  - **At `z = 0`: `Γ^{(ℓ)}(n+1)|_{z=0} = Γ^{(ℓ−1)}(n)`. Substitution lowers the level by one.**
- **(A1) LOWER ROW OF `(1^ℓ)` (PROVED by the Pascal rule).** With `K_{(1^ℓ)}(n) := K^{unif}_{(1^ℓ)}(n) + (Γ^{(ℓ)}_r(A;B) : r ≥ 2, |A| = |B| = r)` for `ℓ ≥ 2`, and `K_{(1)} := K^{unif}_{(1)}`:
  - row 0 of `K_{(1^ℓ)}(n+1)` contains every `Γ^{(ℓ−1)}_r(A;B)(n)` (take `A, B ⊆ [n]`);
  - with INFORME_11 Theorem C for the uniform part, it contains `K_{(1^{ℓ−1})}(n)`.
  - (For `ℓ = 2` the `Γ^{(1)}` are the layer `N_0` of `(1)`; the unbalanced layer generators `|B| < |A|` are multiples of balanced ones of a lower floor.)
- **THE GATES (`vdim` over `F_3` at `q = 9`, full std; logs of the auditor):**

| cell | uniform | + `Γ` objects | `|W|` |
|---|---|---|---|
| `(1,1)(7)` | 22 337 | + `Γ^{(2)}_2`: **22 302** | 22 302 |
| `(1,1)(8)` | 204 820 | + `Γ^{(2)}_{2,3}`: **204 456** (353 s) | 204 456 |
| **`(1,1,1)(8)`** | **128 296** | + `Γ^{(3)}_2`: **128 016** (48 s); + `Γ^{(3)}_{2..4}`: **128 016** (456 s) | **128 016** |
| **`(2,2)(7)`** | 3 675 | + `Γ^{(2)}(j;kl)`, `|A| = 1`, `|B| = 2`: **3 570** (8 s) | 3 570 |

  - Also: `Γ^{(3)}_2(7) ∈ K^{unif}_{(1^3)}(7)`, where the uniform casilla is already exact; `Γ^{(3)}_2(8) ∉ K^{unif}_{(1^3)}(8)` (degree-bounded membership). So the `ℓ = 3` objects enter exactly where they are needed.
  - **Not certified:** that `Γ^{(3)}_2(8) ∈ gr I(W_{(1^3)}(8))`. A certifier truncated at degree 18 did not find it; that is inconclusive, and it is not needed for the chain.
- **Reading (not proved).** The casilla of a profile looks like «the uniform part + the `Γ`-objects of the right levels and imbalances»:
  - `(1^ℓ)`: level `ℓ`, imbalance 0, every `r`;
  - `(2,2)`: level 2, imbalance 1 (which is also where its layer `N_1` sits at level 1).
  - The layer `N_{μ_1−1}` is level 1, imbalance `≤ μ_1−1`.
  - **The natural guess — level `s ≤ ℓ(μ)` with imbalance `≤ μ_s − 1` — is YOURS to state precisely, gate and prove or kill.** Careful: for hooks `(m,1^{ℓ−1})` the uniform family `φ^{(ℓ)}` is NOT a `Γ^{(s)}_1` with `|B| = 1` (the index `f+ℓ−2 = n−2−(m−1)` is shifted).

## 4 · THE TARGETS
### PART A — THE `(1^ℓ)` CHAIN (the must; ~40 %)
With `K_{(1^ℓ)}` as in §3.5 (A1):
- **(A2) value-0, row `ℓ`:** `z^ℓ·Γ^{(ℓ)}_r(A;B)(n) ∈ K_{(1^ℓ)}(n+1) + (z^{ℓ+1})`, every `ℓ ≥ 2`, `r ≥ 2`, `n`, `q ≥ 9`. The uniform part is INFORME_11 Theorem A.
  - Scent: the Pascal rule gives `z·Γ^{(ℓ)}(n) = Γ^{(ℓ−1)}(n) − Γ^{(ℓ)}(n+1)`, so `z^ℓΓ^{(ℓ)}(n) ≡ z^{ℓ−1}Γ^{(ℓ−1)}(n)` modulo the casilla.
  - For `ℓ = 2` Lemma V closes it with the extra identity `y_aG_r(n) ≡ x_A^{q−1}x_P`. Find the level-`ℓ` analogue: which multiple of `Γ^{(ℓ−1)}(n)` by `z^{ℓ−1}` is reachable?
- **(A3) new-class, row `ℓ+1`:** `z^{ℓ+1}·Γ^{(ℓ+1)}_r(A;B)(n) ∈ K_{(1^ℓ)}(n+1) + (z^{ℓ+2})`, same quantifiers; also for `ℓ = 1` (Theorem T is its `ℓ = 1` case). The uniform part is INFORME_11 Theorem B.
  - Scent: Theorem T's certificate is `Σ_{k odd}(z·h_{N+1−k} − z²h_{N−k})e_k(y,z)`, and its `z`- and `z²`-coefficients are `[t^{N+1}]` and `[t^N]` of the odd/even parts of `E(±t)H(t)`.
  - The natural level-`ℓ` certificate is `Σ_{k odd}Σ_{s=1}^{ℓ+1}(±z^s)h_{N+ℓ+1−s−k}e_k(y,z)`. Its `z^s`-coefficients are `Γ^{(s)}`-objects. You must show the ones with `s ≤ ℓ` lie in `K_{(1^ℓ)}(n+1)` and the one with `s = ℓ+1` is a unit times `Γ^{(ℓ+1)}`.
- **If (A2) or (A3) is FALSE as stated** (the truth of (A3) at its content cell, parent `(1,1)(9)`, is NOT measured: 9 variables), the casilla is yours to enlarge.
  - State the enlarged `K_{(1^ℓ)}`, re-gate its size with `grepy_gamma_vdim.py` (`vdim` must not drop below `|W|`), and prove the rows for it.
  - A clean «(A3) fails, and this object repairs it» is a result.
- **Gates:**
  - every certificate checked EXACTLY in the real letters by pure Python (`grepy_verif.py` pattern) at `≥ 2` cells, including one with content (`(1^3)` at `n = 8`, i.e. parent `(1,1)(9)` for (A3), `ℓ = 2`), at two values of `q`;
  - where the parent has `≤ 8` variables, also as a Singular membership.

### PART B — THE `Γ`-LAW (~25 %)
- State a rule `K_μ(n) := Q_μ(n) + box + (Γ^{(s)}(A;B) : (s, |B| − |A|) ∈ Λ(μ))` + the families you need, for EVERY profile `μ`.
- Gate it by `vdim = |W|` at EVERY cell you can afford: all of row `k = 5` at `n ≤ 7`; `(1^ℓ)`, `(2,2)`, `(2,1)`, `(3,1)`, `(2,1,1)` at `n = 8`, `q = 9`; some cells at `q = 27`, `n ≤ 6`.
  - `(2,1)(8)` uniform timed out: build a cheaper `vdim` (fewer layer generators: only the minimal ones, `|B| = |A| + w`), estimate before running, and run it ALONE.
- **A cell where the law is too SMALL (`vdim < |W|`) KILLS that law** (its objects cannot all be true tops). A cell where it is too BIG says an object is missing.
- Check: is `H_{j;k;l}` of `(2,2)` in `K^{unif}_{(2,2)}(7) + (Γ^{(2)}(j;kl))`, and conversely? (the auditor measured only the size).

### PART C — THE RAISE POSITIONS (~15 %)
- The last `ℓ` rows of `(1^ℓ)(n+1)` must contain `K_{(2,1^{ℓ−1})}(n)`; the raise rows of hooks and of `(2,2)` likewise.
- Template: Theorem R (an odd identity with the new letter `z` HEAVY, minus parent-family members), and the tower identity «the lowest `z`-term of `G_r` with `z ∈ A` is the `(2,1)`-child's layer».
- In `Γ`-language: `z ∈ A` puts `z` in the denominator. Find the `Γ`-statement of «the raise».

### PART D — THE LEDGER OF ROW `k = 5` (~15 %; mandatory whatever else happens)
- Generate it like `ledger13.py`: closure of `(∅, 12)` under the dictionary, one line per (parent, row type, distinct child), casilla of each cell stated.
- For each line: its proof source (INFORME_10–13, or this turn), or OPEN. Print the full table, count PROVED / OPEN, and list the OPEN lines grouped by kind.
- **If none is OPEN: «ROW k = 5 CLOSED FOR ALL q».** The chain: `A_5(q) = dim S_{12}/I^{(12)} ≤ Σ_{leaves}|W_leaf| = P_5(q)`.

### PART E — WHAT THE LAW MUST DO AT 9 AND 10 VARIABLES (~5 %)
`(1,1)(9)`, `(1,1)(10)`, `(1,1,1)(9)`, `(2,1)(9)`, `∅(11)`, `∅(12)`, `(1)(10)`, `(1)(11)`, `(2)(9)`, `(2)(10)`, `(3)(9)` are beyond every Gröbner cap. They can be closed ONLY by letters, with certificates gated as exact identities in pure Python. **Say which of them your theorems cover, line by line.**

## 5 · PROCESS
- **STEP 0 — Design and sealed bets (15 min, no runs).** Plan, with an estimate for EVERY run. **Seal at least SIX predictions before running anything, at least THREE risky in the sense of rule 14.** Examples:
  - «(A3) is ONE generating-function identity with `ℓ+1` powers of `z`»;
  - «(A2) needs a second family member, as Theorem R did»;
  - «the `Γ`-law is `s ≤ ℓ(μ)`, imbalance `≤ μ_s − 1`, and it gives `vdim = |W|` at `(2,1)(8)`»;
  - «`H` and `Γ^{(2)}(j;kl)` generate the same ideal modulo `K^{unif}_{(2,2)}(7)`»;
  - «row `k = 5` closes this turn».

  Score them at the end, hits and falsified printed the same size.
- **STEP 1:** PART A — (A3) first, since it generalises the proof you know; then (A2). 50 min.
- **STEP 2:** PART B — the law and its gates. 40 min.
- **STEP 3:** PART C — the raises. 35 min.
- **STEP 4:** PART D (the ledger), then PART E. 40 min.
- **STEP 5:** Verdict (10 min), after re-reading the disk.
- **WHAT I FOUND BEAUTIFUL:** one paragraph.
- **FOR MISSION 15:** what is proved, the smallest open line of the `k = 5` ledger, and your estimate of what the full conjecture still takes.

## 6 · DEAD ROUTES (do not retry)
- **Membership in `gr I` as a step of the chain:** it is never used.
- **Finding the MINIMAL casilla** (which floors are needed at which `n`): off the critical path. Take the casilla maximal and prove the rows.
- **«Floor `r` needed iff `f ≥ 2r+1`»:** false at `r = 3`.
- **The uniform casilla** at `(1,1)` `n = 7, 8`, `(2,2)` `n = 7`, `(1,1,1)` `n = 8`: too big.
- **The naive `ℓ = 3` divided differences** (`y_c²D3`, `y_a^{q−3}D3`, `(y_ay_b)^{q−3}e_{f−1}(y∖{c,d})`): not in `gr I` at `(1^3)(7)`.
- **Restricted Lemma M across a second heavy letter:** no certificate for `m ≤ 7`.
- **Certificates read from a raw syzygy normal form; averaging over groups of order divisible by 3.**
- **M2 `DegreeLimit` on the inhomogeneous fibre ideal.** Use the certifier, or homogeneous `degBound`.
- **Any ascent in `q` (a tower elevator):** dead, with proof. **Measuring cells as a substitute for a mechanism:** cells are gates.
- **Gröbner or `vdim` in 9 variables at `q = 9`:** forbidden; gate by exact identities instead.

## 7 · SUCCESS
- **Minimum:** (A2) and (A3) PROVED with letters for every `ℓ, r, n` and `q ≥ 9` ⟹ the `(1^ℓ)` chain for every `k`, except its raise rows.
- **Good:** **ROW `k = 5` CLOSED FOR ALL `q`** — the full ledger with no OPEN line.
- **Excellent:** the `Γ`-law for every profile, gated, with the four positions proved as index shifts.
- **Full:** **CONJECTURE 1.2 CLOSED FOR ALL `k` AND ALL `q`.**

*Last word from the auditor.* Your predecessor found that every certificate is the odd part of one product with the letters split into heavy and absent. The auditor then found that every OBJECT of the casillas is a coefficient of the same product: the layer, the families, the tower, and the correction that row `k = 5` forces and nobody had seen. It was predicted to the last dimension, 280 out of 128 296, with nothing fitted. And a lower row is just «level minus one». The four positions of a row look like four index shifts of `E(−t)H(t)`. If they are, the induction runs by itself, for every profile and every `k`. That is the whole conjecture, and the scent is strong. Hunt.

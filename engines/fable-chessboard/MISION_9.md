# MISSION 9 — THE ENGINE TEST. CLOSE THE ONE-PART LINE, AND TASTE THE REST.
*(Grepy el Cartógrafo, auditor, 2026-09-22.)*

**You are a NEW Fable. This file is SELF-CONTAINED: read it whole before anything else; you need nothing else.** The reports `INFORME.md` … `INFORME_8.md` in this folder are audited and APPROVED. `INFORME_8.md` holds the full proofs of the results quoted in §3.3; open it only if you want them. Its scripts (`t111f.m2`, `g1e.m2`, `rows2_body.m2`, `fibre.py`, `wd.sh`) are in this folder and may be reused.

> **OBJECTIVE of the campaign: the complete closure of Conjecture 1.2 of Degtyarev–Shimada, for all `k` and all `q = 3^v`.**
>
> **Where we stand (every item below is verified by the auditor):**
> - The conjecture is ONE induction on the number of variables, over explicit ideals («casillas») `K_μ(n)` indexed by an imbalance profile `μ` (§2). Only inclusions of rows are needed, never counts.
> - The one-part line `μ = (m)` is closed at every `q` EXCEPT one family of elements in its generic rows: the «interaction family» of (G1) (§4, PART A). Everything else about (G1) is proved, including the explicit target ideal.
> - The casillas with at most one free coordinate are Tanisaki ideals: they are the LEAVES of the induction (§3.3).
> - What remains for the full conjecture is three things: **(A)** the interaction identity of (G1); **(B)** the rows of the two-part casillas; **(C)** the casillas with two or more free coordinates.
>
> **This mission:**
> - **PART A (the must, 60 % of your time):** prove (A) with `m`, `n`, `q` as letters ⟹ **«ONE-PART LINE CLOSED FOR ALL q»**. Then the FIRE TEST: does the same engine produce the three-part family of `(1,1,1)`?
> - **PART B (a bite, 20 %):** the rows of the two-part casillas whose child is a leaf.
> - **PART C (a bite, 20 %):** write down the first two casillas with two free coordinates, `(2,2)` and `(1,1,1,1)` at `n = 6`, and gate them.
> - **For B and C the goal is to TASTE, not to finish:** write what the difficulty is, which engine works, and whether a uniform pattern shows. That tasting is what missions 10 and 11 will be built on.
>
> **Prize ladder:** MINIMUM = PART A for `m ≥ 2` (all `n`, `q`). GOOD = PART A complete (also `m = 1`, `n` odd) + the fire test. EXCELLENT = + PART B proved for leaf children. FULL = a uniform `K_μ` with row inclusions for every `μ` ⟹ **CONJECTURE 1.2 CLOSED**.

---
## 0 · RULES OF THE TURN (mandatory)
1. **BEFORE THINKING:** create `INFORME_9.md` with the empty sections `## FIRST LINE` · `## STEP 0` · `## STEP 1` · `## STEP 2` · `## STEP 3` · `## STEP 4` · `## STEP 5 — VERDICT` · `## FOR MISSIONS 10 AND 11`.
2. **Save to disk after every step.** What is not written does not exist.
3. **Header per step:** `STATE: CLOSED | EXHAUSTED | NOT CONCLUDED` and `NEXT:`.
4. **In order, no going back, no retries.** Write the budget before each step. 10 min without progress ⟹ stop, write, declare. Keep the last 20 % of each budget for writing.
5. **At most one literature search per step**, in the original source.
6. **Do not recompute anything listed here as proved or measured.**
7. **A negative dimension, or one larger than the box, is a bug:** stop.
8. **«This route dies, for this reason» is a result.**
9. **Write ONLY in `~/Desktop/FABLE_TABLERO/`. Do not open anything in `~/Desktop/ARBOLYAML/`.**
10. **Machine:** `/opt/homebrew/bin/M2`. This Mac has no `timeout`; use the folder's `wd.sh script.m2 logfile` (570 s watchdog).
    - Each run **< 1.2 GB and < 10 min**. Write an estimate BEFORE each run, for its most expensive case, engine by engine.
    - After any kill, check with `pgrep` that it is gone, and write that you checked.
    - M2 reserved names (`check`, `top`, `info`, …) abort scripts: prefix your own names.
    - Never pass thousands of generators at once: reduce modulo a Gröbner basis first.
    - **Allowed:** explicit ideals in `n` variables with `n ≤ 10` at `q = 3`, `n ≤ 7` at `q = 9`, `n ≤ 5` at `q = 27`, `n ≤ 4` at `q = 81`: colengths, colons by a power of one variable, memberships, minimal generators. Python evaluation of a function on all points of a fibre at `q ≤ 27`, and linear algebra on those values.
    - **Forbidden:** any M2 run with `n ≥ 8` at `q ≥ 9`, `n ≥ 6` at `q = 27`, `n ≥ 5` at `q = 81`; point ideals over `GF(27)`; point enumeration in M2.
    - **A colon in 7 variables at `q = 9` was killed at 570 s last turn.** In 7 variables use MEMBERSHIP gates (Gröbner basis of `K + (z^{a+1})`, then test `z^a·g`), which took 26–72 s.
11. **Re-read the disk before the verdict.**
12. **Double check:** every PROVED claim carries its proof in the report; every number carries its cell and its log; every identity used in a proof is checked exactly (symbolically, or on ALL points of the set it is claimed on); every new casilla passes its colength gate against §1 BEFORE you build on it.

**FIRST LINE** (answer first, in this order):
- (a) Is the interaction identity of (G1) proved for all `m, n, q`? For which `(m, n-parity)` exactly?
- (b) Does the engine produce the `(1,1,1)` family? YES / NO / PARTLY, with the cell.
- (c) PART B and PART C: what did each taste like, in one line each?
- (d) Does anything close the row `k = 4` or the conjecture? YES or NO, with the reason in one line.

---
## 1 · THE OBJECTS
**Basics.** `q = 3^v`, `h := (q−1)/2`. `S_n := F_q[x_1..x_n]`; `e_r` := elementary symmetric polynomial of degree `r` (`e_0 = 1`, `e_r = 0` for `r < 0` or `r >` number of variables); `box := (x_1^q, …, x_n^q)`. **`I^{(n)} := (e_1, e_3, e_5, …) + box`.** `x_C := Π_{i∈C}x_i`; `x_A^{q−1} := Π_{i∈A}x_i^{q−1}`. For a polynomial `F`, `F_d` is its homogeneous component of degree `d`; `gr I(X)` is the ideal of top forms of the functions vanishing on `X`.

**Profiles and fibres.**
- A multiset `S ⊂ F_q` constrains `y ∈ F_q^n` by «`y ∪ S` is closed under negation». Only the unpaired part of `S` matters. Its **profile** is `μ = (μ_1 ≥ … ≥ μ_ℓ)`: one positive integer per non-zero class `{s,−s}`, where `μ_i` = how many more copies of `−s_i` than of `s_i` the point `y` must carry. Zeros impose nothing. Write `|μ| := Σμ_i`, `ℓ := ℓ(μ)`, **`f := n − |μ|`** (the number of «free» coordinates).
- **`W_μ(n) := {y ∈ F_q^n : y ∪ S closed}`.** Up to bijection it depends only on `μ`. Empty iff `|μ| > n` or `ℓ > h`.
- **Fibre sizes, exact:** with `I_m(t) := Σ_{b≥0} t^{2b+m}/(b!(b+m)!)`, **`|W_μ(n)| = n!·[t^n] E(t)·Π_i I_{μ_i}(t)·I_0(t)^{h−ℓ}`**, `E = cosh` if `f` is even and `sinh` if `f` is odd. (`fibre.py` in this folder implements it.)
- **Gates (auditor, independent code), `n = 0..7`:**

| `μ` | `q = 9` | `q = 27` |
|---|---|---|
| `∅` | 1, 1, 9, 25, 217, 921, 7761, 41889 | 1, 1, 27, 79, 2107, 10011, 263901, 1708617 |
| `(1)` | 0, 1, 2, 24, 88, 855, 4266, 37947 | 0, 1, 2, 78, 304, 9765, 55566, 1647597 |
| `(2)` | 0, 0, 1, 3, 46, 210, 2340, 13496 | 0, 0, 1, 3, 154, 750, 28530, 189266 |
| `(1,1)` | 0, 0, 2, 6, 84, 380, 3930, 22302 | 0, 0, 2, 6, 300, 1460, 54150, 358722 |
| `(2,1)` | 0, 0, 0, 3, 12, 200, 1080, 12390 | 0, 0, 0, 3, 12, 740, 4320, 184380 |
| `(3,1)` | 0, 0, 0, 0, 4, 20, 390, 2450 | 0, 0, 0, 0, 4, 20, 1470, 10010 |
| `(2,2)` | 0, 0, 0, 0, 6, 30, 570, 3570 | 0, 0, 0, 0, 6, 30, 2190, 14910 |
| `(1,1,1)` | 0, 0, 0, 6, 24, 360, 1920, 20370 | 0, 0, 0, 6, 24, 1440, 8400, 349230 |
| `(2,1,1)` | 0, 0, 0, 0, 12, 60, 1020, 6300 | 0, 0, 0, 0, 12, 60, 4260, 28980 |
| `(1,1,1,1)` | 0, 0, 0, 0, 24, 120, 1800, 10920 | 0, 0, 0, 0, 24, 120, 8280, 56280 |

- **Fibre recursion (last coordinate `v`):** `|W_μ(n)| = Σ_{v∈F_q}|W_{μ+v}(n−1)|`, where `μ+v` is the profile of `S ∪ {v}`: `v = 0` gives `μ`; `v = −s_i` LOWERS `μ_i` by one; `v = +s_i` RAISES `μ_i` by one; `v` in an unused class APPENDS a part `1`.

**Rows.** For `K ⊆ S_n` with `z := x_n` and `z^q ∈ K`, **row `a`** is `R_a(K) := π_z(K : z^a) ⊆ S_{n−1}` (`π_z` sets `z = 0`). **Rows increase with `a`**, and **`dim S_n/K = Σ_{a=0}^{q−1} dim S_{n−1}/R_a(K)`**.

**The conjecture.** `A_k(q) := dim S_{2k+2}/I^{(2k+2)}`, `P_k(q) := |W_∅(2k+2)|`. **Conjecture 1.2: `A_k(q) = P_k(q)`.** The floor `A ≥ P` is PROVED, so **the conjecture ⟺ `A_k(q) ≤ P_k(q)`.**

## 2 · THE FRAMEWORK: THE PARTITION INDUCTION
**Statement `T(n)`:** for every profile `μ` there is an EXPLICIT ideal `K_μ(n) ⊆ S_n`, with `z^q ∈ K_μ(n)`, `K_∅(n) = I^{(n)}`, `K_μ(n) = (1)` when `W_μ(n) = ∅`, and `dim S_n/K_μ(n) ≤ |W_μ(n)|`.
- **Inductive step:** `T(n−1)` implies `T(n)` at `μ` as soon as there is a bijection `a ↔ v` (rows `0..q−1` ↔ values `v ∈ F_q`) with **`R_a(K_μ(n)) ⊇ K_{μ+v}(n−1)`** for every `a`. Rows increase with `a`: give the LARGE fibres to the SMALL `a`; within a block of rows of the same type, only the first row of the block needs proof.
- **Base:** `n = 0`. ⟹ `T(n)` for all `n`, in particular the conjecture.
- **Row dictionary for a profile with `ℓ` parts (measured 126/126 rows last turn):** rows `0 … ℓ−1` LOWER a part (larger fibre first = lower the largest part first); row `ℓ` is the value `0` (same type `μ`); rows `ℓ+1 … q−ℓ−1` are the `q−1−2ℓ` NEW-CLASS rows (type `μ ∪ (1)`); the last `ℓ` rows RAISE a part (larger fibre first = raise the smallest part first). For `μ = (m,1)` in `n+1` variables: row 0 → `(m−1,1)`, row 1 → `(m)`, row 2 → `(m,1)`, rows `3..q−3` → `(m,1,1)`, row `q−2` → `(m,2)`, row `q−1` → `(m+1,1)` (for `m = 1`, rows 0 and 1 are both `(1)`).
- **`f` never increases along rows** (lowering keeps `f`, value `0` lowers it by 1, new class and raising lower it by 2). So the casillas with `f ≤ 1` form a world closed under rows.
- **Tools in induction order:** at level `n`, once `T(n)` holds at `∅` (it comes first), the floor gives **`gr I(W_∅(n)) = I^{(n)}`**; likewise at `(1)`: `gr I(W_(1)(n)) = K_(1)(n)`. For `(m)`, `m ≥ 2`, the floor `K_(m) ⊆ gr I(W_(m))` is NOT automatic. If your engine needs `gr I` of some set, say which, and show it is available before it is used (the induction order is: level `n−1` entirely, then level `n` profile by profile).

## 3 · WHAT IS PROVED OR MEASURED (use it; do not re-prove it)
### 3.1 Earlier theorems (PROVED)
The floor; the Plus Lemma (`(−2)^j = 1` in `F_3`); the casilla theorems (rows `a ≥ 1` of `I^{(n)}` contain `K_(1)(n−1)`); `(P_k)` for all `k, q`; `A_k = P_k` for `k ≤ 3`, all `q`; `A_k(3) = P_k(3)` for all `k` (Steinberg bridge; reproved by this framework, since at `q = 3` there are no new-class rows).

### 3.2 The one-part line
**`K_(m)(n) := (e_odd) + box + (e_n, if n even and m ≥ 1) + N_{m−1}(n)`**, where **`N_w(n)`** := the ideal of the monomials `x_C·x_A^{q−1}` over all splittings `A ⊔ B ⊔ C = [n]` with `|B| − |A| ≤ w` and `|B| ≥ 1` (auditor check: `≤ w` and `= w` give the same ideal `K_(m)(n)` in 6/6 cells, `q = 9`, `n ≤ 6`, `m ≤ 3`). Colength `= |W_(m)(n)|` measured 25/25; rows equal the family as ideals. **Rows 0, 1, `q−1` PROVED for all `q`** (to `K_(m−1)`, `K_(m)`, `K_(m+1)`). All generic rows `a = 2..q−2` carry type `(m,1)`, and only `R_2 ⊇ K_{(m,1)}(n−1)` is needed.

### 3.3 From INFORME_8 (audited; full proofs there)
1. **Row formula (PROVED).** For `K = (e_odd) + box + M ⊆ S_{n+1}` with `M` generated by elements `z^i·g(y)`, and `M^{[i]} := {g : z^i g ∈ M}`: `f ∈ R_a(K)` iff there are `c^0,…,c^{a−1}` (vectors indexed by odd degrees) with `Σ_r c_r^0e_{2r+1}(y) ∈ box + M^{[0]}`, `Σ_r c_r^i e_{2r+1}(y) + Σ_r c_r^{i−1}e_{2r}(y) ∈ box + M^{[i]}` (`1 ≤ i ≤ a−1`), and `f ≡ Σ_r c_r^{a−1}e_{2r}(y)` mod `(e_odd) + box + M^{[a]}`. For the one-part line, `M^{[0]} = N_{m−2}(n)`, `M^{[i]} = Ñ_{m−1}(n)` for `1 ≤ i ≤ q−2` (`Ñ := N + (e_n(y))` when `n+1` is even and `m ≥ 1`), `M^{[q−1]} = N_m(n)`. Equivalently **`R_2(K_(m)(n+1)) = π_z((I^{(n+1)} + N_{m−2}(n) + z·Ñ_{m−1}(n) + (z³)) : z²)`**.
2. **Iterated rows are lex-staircase colons (PROVED);** on the one-part line `K_(m)(n) = π(I^{(n+m)} : (z_1⋯z_m)^{q−1})`, path-independent.
3. **THE ENGINE (Lemma H for every `m`, PROVED).** The slice `{z = w} ∩ W_∅(n+1)` equals `w·W_(1)(n)` for every `w ≠ 0` and every `n`. Hence: **if `F ∈ I(W_(1)(n))` has top form `F_d ∈ Ñ_{m−1}(n)`, then `F_{d−1} ∈ R_2(K_(m)(n+1))`.** (Homogenize `G := Σ_i z^{d+1−i}F_i`; it vanishes on `W_∅(n+1)`, so `G ∈ I^{(n+1)}`; and `z·Ñ_{m−1}(n) ⊆ K_(m)(n+1)`.) On `W_(1)(n)`: `E_y(T) = (T−1)·Ev(T)` with `Ev` even, so **`e_{2i+1}(y) = −e_{2i}(y)` on `W_(1)(n)`** for all `i` (`e_1 = −1`).
4. **Symmetric core (PROVED by the engine):** `e_{2i}(y) ∈ R_2(K_(m)(n+1))` for `n−m ≤ 2i ≤ n−1`.
5. **THE (G1) CASILLA (explicit; exact as an ideal in 12/12 colon cells: `q = 9`, `n+1 ≤ 7`; `q = 27`, `n+1 ≤ 5`; plus membership gates at `(n+1,m) = (7,1), (7,2)`):**
   **`K_{(m,1)}(n) := (e_j : j odd, or j ≥ n−m) + box + N_{m−1}(n) + F_m(n)`, `F_m(n) := (s^{(m)}_{jl} : j ≠ l)`, `s^{(m)}_{jl} := y_j^{q−2}·e_{n−m−1}(y∖y_l)`.**
   The family is redundant when `n−m−1 ≤ 1`. PROVED: `K_(m)(n) ⊆ R_2`, the symmetric part, and **the family for `m = 1`, `n` even** (by the identity (D_k), §3.4). **NOT proved: the family for `m ≥ 2`, and for `m = 1`, `n` odd. That is PART A.**
6. **Rows 0, 1 of `K_{(m,1)}(n)` PROVED; row 2 PROVED given (G1).**
7. **Leaves (MEASURED 16 cells; geometric side classical):** for `f ≤ 1`, `W_μ(n)` is one `S_n`-orbit and its casilla is **the Tanisaki ideal `I_λ + box`**, `λ := μ ∪ (1^f)`: `I_λ := (e_r(x_S) : S ⊆ [n], r > |S| − d_{|S|}(λ))`, `d_k(λ) := λ'_n + … + λ'_{n−k+1}` (`λ'` = conjugate partition, padded with zeros to length `n`); colength `n!/Π_i λ_i!`.
8. **The `q`-free part of every measured casilla (16/16)** is `Q_μ(n) := (e_j([n]) : j odd or j ≥ n−|μ|+1) + (e_r(x_S) : S ⊊ [n], r > |S| − d_{|S|}(λ))`.
9. **`(1,1,1)` (MEASURED, n = 4, 5, 6; q = 27 gate at n = 5):** `K_{(1,1,1)}(n) = (e_j : j odd or j ≥ n−2) + box + N_0(n) + (y_j^{q−3}·y_l^{n−2} : j ≠ l)`, colengths 24, 360, 1920 (q = 9) and 1440 at n = 5 (q = 27). At `n = 5, 6` the form `y_j^{q−3}·p_{n−2}(y∖y_l)` (power sum) gives the same ideal. It is **row 3 of `K_{(1,1)}(n+1)`** (the first new-class row). At `n = 6` the nine rows of `K_{(1,1,1)}(6)` are exactly the dictionary casillas (9/9).
10. **Two-part rows measured (81 rows, `q = 9`, `n+1 ≤ 6`):** the new-class rows `(m,1,1)` and the raising row `(m,2)` of `K_{(m,1)}(n+1)` equal the Tanisaki casilla when `f ≤ 1`. For `μ_2 ≥ 2` the monomial layer has weight `|μ| − ℓ − 1` (NOT `|μ| − ℓ`: that is too big — `(2,2)` n = 4: colength 4 < 6; n = 5: 20 < 30; `(3,2)` n = 5: 5 < 10).
11. **Cells closed:** `T(7)` at `(1)` and at `(2)`, `q = 9` (rows sum `37947` and `13496` = fibres).
12. **Uniform degree (auditor):** every measured interaction family lives in degree **`q + n − |μ| − 2 = q + f − 2`**, first factor `y_j^{q−ℓ}`: `(m)`: `x_j^{q−1}`·(degree `f−1`); `(m,1)`: `y_j^{q−2}e_f(y∖y_l)`; `(1,1,1)`: `y_j^{q−3}y_l^{f+1}`.

### 3.4 The model to imitate: `m = 1`, `n = 2k` even (PROVED for all `k`, `q`)
Setting: `K_(1)(2k+1)`, `y := (x_1..x_{2k})`, `z := x_{2k+1}`, `W_0 := W_(1)(2k)`. Fix `j ≠ l`, `P := y∖{y_j, y_l}`, `τ := y_j^{q−1}·Π_P` (so `z·τ` is a monomial of the layer), and **`s_0 := y_j^{q−2}·e_{2k−2}(y∖y_l)`** (this is `s^{(1)}_{jl}`).
- **Identity (D_k), exact on every point of `W_0`, PROVED by cases:**
  `s_0 + τ = E' + u + D − Σ(P) − [y_j+y_l=0]R'_j + [y_j=y_l](1−y_j)R'_j − Σ_{a=±1}([y_j=a]y_l + [y_l=a]y_j)D`,
  where `F(s) := Σ_{m<k} e_{2m}(y)s^{k−1−m}`; `D := F[y_j², y_l²]` (divided difference); `R'_j := F'(y_j²)`; `u := Π_P`, `E' := e_{2k−3}(P)`, `Σ(P) := Π_{p∈P}(1+y_p)`; `[x=a] := 1 − (x−a)^{q−1}`. Auditor check: exact at `(k,q) = (2,9), (3,9), (4,9), (5,9), (6,9), (2,27), (3,27), (4,3)`.
- **(B_k) — the model proof of this campaign; imitate it.** The degree-`(q+2k−4)` remainder (the degree of `s_0`) must lie in `R_2`:
  `X := (y_j−y_l)^{q−1}y_jR'_j − y_j^{q−1}y_lD − y_l^{q−1}y_jD`. Write `X_1` for its first term.
  1. **Degree:** the casilla's monomials have degree `≥ q+2k−3`, so only **`J := (e_odd, e_{2k}) + box`** can contain `X`.
  2. **Relations in `J`:** `Π(T+y_i) ≡ T²F(T²)`, so `a²F(a²) ∈ J` and `(a+b)(F(a²) + b²D) ∈ J`, with `a = y_j`, `b = y_l`.
  3. **Frobenius:** `(a−b)^q ≡ 0`, so `(a−b)^{q−1}` kills multiples of `a−b`, and `X_1 ≡ −(a−b)^{q−1}(a+b)D`.
  4. **Lucas:** `(a−b)^{q−1} = h_{q−1}(a,b)`, so `X ≡ a²b²h_{q−4}(a,b)D`, with `h_{q−4}(a,b) = (a+b)h_{(q−5)/2}(a²,b²)`.
  5. Hence `X ≡ −(a+b)h·a²F(a²) ∈ J ⊆ R_2`. ∎
- **The odd parity `n = 2k−1`** (target `y_j^{q−2}e_{2k−3}(y∖y_l)` in `R_2(K_(1)(2k))`): a descent identity exists at `(2,9)`, `(3,9)`; its closed form has NOT been extracted.

## 4 · THE TARGETS
### PART A — the (G1) interaction identity (the must)
**Target A1.** For `m ≥ 2` and all `n` with `n−m−1 ≥ 2`, and for `m = 1` with `n` odd: **`s^{(m)}_{jl} ∈ R_2(K_(m)(n+1))`**, with `m, n, q` as letters.
**Reduction (by the engine 3.3.3):** it suffices to find **`F ∈ I(W_(1)(n))`** of degree `d = q+n−m−2` with **top form `F_d ∈ Ñ_{m−1}(n)`** and next form **`F_{d−1} ≡ s^{(m)}_{jl}` modulo `K_(m)(n) + (e_{2i} : n−m ≤ 2i ≤ n−1)`** (both already in `R_2`). Lower components are free. Equivalently: an identity of FUNCTIONS on `W_(1)(n)`: `s^{(m)}_{jl} + τ = r + κ` with `τ ∈ (Ñ_{m−1}(n))_d`, `κ` in the ideal above (degree `d−1`), `deg r ≤ d−2`.
**Room you have for `m ≥ 2` that `m = 1` did not have:** `Ñ_{m−1}` contains the `q`-free monomials `x_C` with `|C| ≥ n−m+1` (times anything of the right degree), and the second-order terms `N_{m−2}(n)` enter through the row formula 3.3.1.
**The model to imitate** is `m = 1`, `n` even (§3.4). **How to find the identity:** at the smallest cells, evaluate candidate `τ`, `κ` on ALL points of `W_(1)(n)` (Python, `q = 9`) and solve the linear system for `r`; read off the closed form; then prove it by cases on the points, as (D_k) was proved. Smallest cells: `m = 2`: `n = 5` (`|W_(1)(5)| = 855` at `q = 9`), `n = 6` (4266); `m = 3`: `n = 6`; `m = 1` odd: `n = 5` (855), `n = 7` (37947). Check every identity exactly on all points at `q = 9` and at `q = 27` where the fibre fits (`n ≤ 5` at `q = 27`: 9765 points).
**Dead for PART A (measured last turn, do not retry):** the lift lemma `x_{Y'}^{q−1}K_(1)(V∪z) ⊆ K_(m)(n+1)` is correct but INERT (its elements add nothing to `K_(m)(n) + core`, 3 cells); monotonicity `K_(1) ⊆ K_(m)` adds nothing; a Lemma H on `W_∅(n+m+1)` is out of the induction order; the tautological induction on simultaneous colons is false at `N = 2`.

**Target A2 — THE FIRE TEST.** Does the engine produce the `(1,1,1)` family `y_j^{q−3}y_l^{n−2}` inside **row 3 of `K_{(1,1)}(n+1)`**? The obstacle to name first: the slices of `W_(1)(n+1)` over a new-class value `w` are two-class sets whose class ratio changes with `w`, so they are NOT scalings of one set, and the homogenization of 3.3.3 does not apply as is. Candidates: (i) a scale-invariant union (all classes at once); (ii) a two-step descent through `W_∅` (only if it stays in induction order); (iii) the row formula 3.3.1 with the explicit `(1,1)` casilla. Decide at `n = 4, 5` (`q = 9`). **If the engine works here, the method scales with the number of parts; if not, say why exactly: that decides missions 10 and 11.**

### PART B — a bite: two-part rows with a LEAF child
For `K_{(m,1)}(n+1)`, the new-class rows (type `(m,1,1)`) and the row `q−2` (type `(m,2)`) whose child has `f ≤ 1` must contain the Tanisaki casilla `I_λ + box` of the child. Those generators are `q`-free (degree `< q`). **Question:** do they follow from the `q`-free part of the parent by the row formula 3.3.1, i.e. by a `q`-free certificate `z^a·g ∈ K + (z^{a+1})` without exponents `q−1`? Try the smallest case `K_{(1,1)}(5)` rows 3 (type `(1,1,1)`, child `n = 4`, `f = 1`) and `K_{(2,1)}(6)` row `q−2` (type `(2,2)`, child `n = 5`, `f = 1`). If a pattern appears, state it with `μ` as a letter; if it does not, say which generator resists.

### PART C — a bite: the first casillas with two free coordinates
**First gate the parents, which are NOT yet gated at `n = 7`:** the (G1) casilla `K_{(2,1)}(7)` of 3.3.5 must have colength **12390** and the `(1,1,1)` guess `K_{(1,1,1)}(7)` of 3.3.9 must have colength **20370** (7 variables, `q = 9`, allowed; estimate first). If a parent fails its gate, stop PART C there and report it — that is itself a result. Then write explicit candidates for **`K_{(2,2)}(6)`** (target colength **570** at `q = 9`) and **`K_{(1,1,1,1)}(6)`** (target **1800**), gate their colength in 6 variables (cheap), and then gate them as rows by MEMBERSHIP: `(2,2)` is row `q−2` of `K_{(2,1)}(7)`; `(1,1,1,1)` is a new-class row of `K_{(1,1,1)}(7)`. Ingredients to try, in this order: `Q_μ(n)` (3.3.8) + box + monomial layer of weight `|μ| − ℓ − 1` for `(2,2)` (3.3.10) and `N_0` for `(1,1,1,1)` + an interaction family in degree `q + f − 2 = q` with first factor `y_j^{q−ℓ}` (3.3.12). If the colength is right, test at `q = 27` in 5 variables only if the profile has non-empty fibre there with `n ≤ 5` (it does not for these two at `f = 2`; then say so). **Write what the interaction family looks like for `ℓ = 2` with `μ_2 = 2`, and for `ℓ = 4`.**

## 5 · PROCESS
- **STEP 0 — Design (15 min, no runs).** Plan the identity search for A1 (unknowns, cells, how you will prove it), name the obstacle of A2, and the plan for B and C.
- **STEP 1 — A1 for `m ≥ 2` (70 min).** Find, then prove. If proved: write **«(G1) FOR m ≥ 2, ALL n, q»**.
- **STEP 2 — A1 for `m = 1`, `n` odd, and A2 (50 min).** If A1 is complete: **«ONE-PART LINE CLOSED FOR ALL q»**.
- **STEP 3 — PART B (25 min).**
- **STEP 4 — PART C (25 min).**
- **STEP 5 — Verdict (10 min)**, after re-reading the disk.
- **FOR MISSIONS 10 AND 11:** for each of A2, B, C: the engine that works (or the reason none does), the smallest open cell, and your estimate of what it takes.

## 6 · DEAD ROUTES (do not retry)
- Separate counting lemmas for rows (the counts ARE the induction).
- The odd casilla with `j ≤ min(2, k−1)` (wrong from `k = 5`).
- «rows ⊆ fibres» as a formal consequence (false; three points).
- The sum of colons alone for generic rows (too small; shadows come from mixed certificates).
- The lift lemma and monotonicity for (G1) (inert).
- The uniform second factor `e_{f+ℓ−2}(y∖y_l)`, `h_{f+ℓ−2}(y∖y_l)`, `p_{f+ℓ−2}(y∖y_l)` for all `μ` (the first two wrong in every tested cell; `p` wrong at `(1,1)`, `n = 6`: 2985 < 3930).
- Any ascent in `q` (tower elevator): dead, with proof.
- Measuring cells as a substitute for a mechanism: cells are gates only.

## 7 · SUCCESS
- **Minimum:** A1 for `m ≥ 2`, all `n, q`.
- **Good:** A1 complete ⟹ **ONE-PART LINE CLOSED FOR ALL q**, plus a clear verdict on the fire test.
- **Excellent:** + PART B proved for all leaf children.
- **Full:** a uniform `K_μ` with row inclusions for every `μ` ⟹ **CONJECTURE 1.2 CLOSED.**

# MISSION 10 — THE ONE LEMMA. READ THE CERTIFICATES, AND THE LINE IS YOURS.
*(Grepy el Cartógrafo, auditor, 2026-09-23.)*

**You are a NEW Fable. This file is SELF-CONTAINED: read it whole before anything else, and you need nothing else.** The reports `INFORME.md` … `INFORME_9.md` in this folder are audited and APPROVED. Open them only if you want a proof quoted here. Their scripts (`fibre.py`, `wd.sh`, `rows2_body.m2`, `fire.m2`, `eng1.m2`, `eng7.m2`, `odd5.py`, `span5.py`, `t111f.m2`, `g1e.m2`) are in this folder and may be reused.

> **OBJECTIVE of the campaign: the complete closure of Conjecture 1.2 of Degtyarev–Shimada, for all `k` and all `q = 3^v`.**
>
> **Where we stand (every item is verified by the auditor):**
> - The conjecture is ONE induction on the number of variables, over explicit ideals («casillas») `K_μ(n)` indexed by an imbalance profile `μ` (§2). Only inclusions of rows are needed, never counts.
> - Every row inclusion of every casilla is the SAME kind of statement: one identity of functions on the same finite set `W_(1)(n)`. The engine that turns such identities into row inclusions is PROVED. It works in every cell measured: 11 cells last turn, and the «fire test» on a three-part profile was POSITIVE.
> - **What is missing everywhere is ONE lemma: the second-order certificates.** These are the syzygies of `(e_1, e_3, e_5, …)` modulo the box, written with letters. The last Fable found them by machine in four cells and did not read them.
> - **New since the last mission, and it changes how you work:** the true casilla of every profile is **COMPUTABLE in seconds** from closed-form generators (§3.4). You do not have to guess any interaction family again. You can READ it.
>
> **This mission — three parts, one prize.**
> - **PART A (the must, about 50 % of your time): THE ONE LEMMA.**
>   1. Extract the certificates of (G1) at the cells where they exist.
>   2. Read their shape with `m`, `n`, `q` as letters.
>   3. Prove it.
>
>   ⟹ **«ONE-PART LINE CLOSED FOR ALL q»**.
> - **PART B (about 30 %): THE CASILLA MACHINE.** Compute the true casillas of the twelve multi-part profiles that row `k = 4` needs. Read ONE uniform formula from them. Resolve `(1,1,1)` at `n = 7`, which beat two missions of guessing.
> - **PART C (about 15 %): THE LEDGER OF ROW `k = 4`.** List every row inclusion that `A_4(q) = P_4(q)` for all `q` needs, with its status. If the list is empty, **ROW `k = 4` IS CLOSED**. That would be the first new row of the conjecture since `k = 3`.
>
> **Prize ladder:**
> - **MINIMUM:** ONE new infinite family PROVED with letters. Any one of: (G1) for `m ≥ 2`; (G1) for `m = 1`, `n` odd; the uniform casilla of one multi-part line with its row inclusions. The certificates of §4 PART A must also be written down explicitly.
> - **GOOD:** **ONE-PART LINE CLOSED FOR ALL q.**
> - **EXCELLENT:** GOOD, plus the uniform `K_μ` for the twelve profiles as IDEALS (equal to the true casilla in every allowed cell), plus the ledger of row `k = 4` reduced to identities of the one engine.
> - **FULL:** **ROW `k = 4` CLOSED FOR ALL q**, or a uniform `K_μ` with all its row inclusions ⟹ **CONJECTURE 1.2 CLOSED.**

---
## 0 · RULES OF THE TURN (mandatory)
1. **BEFORE THINKING:** create `INFORME_10.md` with these empty sections: `## FIRST LINE` · `## STEP 0 — DESIGN AND SEALED BETS` · `## STEP 1` · `## STEP 2` · `## STEP 3` · `## STEP 4` · `## STEP 5 — VERDICT` · `## WHAT I FOUND BEAUTIFUL` · `## FOR MISSION 11`.
2. **Save to disk after every step.** What is not written does not exist. If your session is cut, what is on disk IS your delivery.
3. **Header per step:** `STATE: CLOSED | EXHAUSTED | NOT CONCLUDED` and `NEXT:`.
4. **Timing:**
   - Work in order, with no going back and no retries.
   - Write the budget before each step.
   - After 10 minutes without progress: stop, write, declare.
   - Keep the last 20 % of each budget for writing.
5. **At most one literature search per step**, in the original source.
6. **Do not recompute anything listed here as proved or measured.**
7. **A negative dimension, or one larger than the box, is a bug:** stop.
8. **«This route dies, for this reason» is a result.** A falsified sealed bet is worth more than a safe hit.
9. **Write ONLY in `~/Desktop/FABLE_TABLERO/`. Do not open anything in `~/Desktop/ARBOLYAML/`.**
10. **Machine:** `/opt/homebrew/bin/M2`. This Mac has no `timeout`: use the folder's `wd.sh script.m2 logfile` (570 s watchdog).
    - **Caps per run:** `< 1.2 GB` and `< 10 min`. Write an estimate BEFORE each run, for its most expensive case, engine by engine.
    - **The machine is idle (about 20 % CPU).** You MAY run TWO engines at once, provided their estimates add up to less than 1.2 GB. Any Gröbner basis in 7 variables always runs ALONE. The per-run caps do not move.
    - After any kill, check with `pgrep` that it is gone, and write that you checked. When you finish, check that nothing of yours is still running.
    - M2 reserved names (`check`, `top`, `info`, `degree` as a variable, …) abort scripts: prefix your own names (e.g. `cl`).
    - In M2, building a quotient ring `R/I` REBINDS the variable names; re-`use` the ring you mean before every quotient in a loop.
    - Never pass thousands of generators at once: reduce modulo a Gröbner basis first.
    - **Allowed:**
      - explicit ideals in `n` variables with `n ≤ 10` at `q = 3`, `n ≤ 7` at `q = 9`, `n ≤ 5` at `q = 27`, `n ≤ 4` at `q = 81`: colengths, colons by a power of one variable, memberships, liftings (certificates), minimal generators;
      - the fibre ideals of §3.4 at the same sizes;
      - Python evaluation of a function on all points of a fibre at `q ≤ 27`, and linear algebra on those values.
    - **Forbidden:** any M2 run with `n ≥ 8` at `q ≥ 9`, `n ≥ 6` at `q = 27`, `n ≥ 5` at `q = 81`; point ideals over `GF(27)`; point enumeration in M2.
    - **Known costs:**
      - A colon in 7 variables at `q = 9` was killed at 570 s. Memberships in 7 variables took 26–72 s.
      - The base `Q + box + N_0(7)` took 424 s. The same colength WITHOUT the layer `N_0` took 3 s (§3.4).
      - The true casilla of `(1,1,1)` at `n = 7` by a FULL Gröbner basis of `I(W)` was killed at 601 s. Use `DegreeLimit` (§4 PART B).
11. **In characteristic 3, never average over a group whose order is divisible by 3** (`1/3`, `1/6` do not exist). A certificate is not unique. Make it canonical by REDUCTION (a normal form modulo the syzygies), not by averaging.
12. **Re-read the disk before the verdict.**
13. **Double check:**
    - Every PROVED claim carries its proof in the report.
    - Every number carries its cell and its log.
    - Every identity used in a proof is checked exactly: symbolically, or on ALL points of the set it is claimed on.
    - Every casilla is gated AS AN IDEAL against the true casilla of §3.4 wherever that fits, and by colength against §1 elsewhere.

**FIRST LINE** (answer first, in this order):
- (a) Is (G1) proved for all `m, n, q`? For exactly which `(m, n-parity)`?
- (b) What do the second-order certificates look like, in one sentence with letters?
- (c) PART B: is there ONE uniform `K_μ` for the twelve profiles? YES / NO / PARTLY, with the first cell where it fails.
- (d) PART C: how many row identities remain for row `k = 4`, and of how many kinds?
- (e) Does anything close row `k = 4` or the conjecture? YES or NO, with the reason in one line.

---
## 1 · THE OBJECTS
**Basics.**
- `q = 3^v`, `h := (q−1)/2`. `S_n := F_q[x_1..x_n]`.
- `e_r` is the elementary symmetric polynomial of degree `r` (`e_0 = 1`; `e_r = 0` for `r < 0` or `r >` the number of variables).
- `box := (x_1^q, …, x_n^q)`. **`I^{(n)} := (e_1, e_3, e_5, …) + box`.**
- `x_C := Π_{i∈C}x_i`; `x_A^{q−1} := Π_{i∈A}x_i^{q−1}`.
- For a polynomial `F`, `F_d` is its homogeneous component of degree `d`. `gr I(X)` is the ideal of top forms of the functions vanishing on `X`.

**Profiles and fibres.**
- A multiset `S ⊂ F_q` (the **anchor**) constrains `y ∈ F_q^n` by the condition «`y ∪ S` is closed under negation».
- Only the unpaired part of `S` matters. Its **profile** is `μ = (μ_1 ≥ … ≥ μ_ℓ)`: one positive integer per non-zero class `{s,−s}`, where `μ_i` is how many more copies of `−s_i` than of `s_i` the point `y` must carry. Zeros impose nothing.
- Write `|μ| := Σμ_i`, `ℓ := ℓ(μ)`, **`f := n − |μ|`** (the number of «free» coordinates).
- **`W_μ(n) := {y ∈ F_q^n : y ∪ S closed}`.** Up to bijection it depends only on `μ`. It is empty iff `|μ| > n` or `ℓ > h`.
- **Fibre sizes, exact.** With `I_m(t) := Σ_{b≥0} t^{2b+m}/(b!(b+m)!)`:
  **`|W_μ(n)| = n!·[t^n] E(t)·Π_i I_{μ_i}(t)·I_0(t)^{h−ℓ}`**, with `E = cosh` if `f` is even and `sinh` if `f` is odd. `fibre.py` implements it.
- **Gates** (auditor, two independent codes; brute force agrees wherever it was run). Every profile that row `k = 4` needs, `n = 0..9` at `q = 9`, `n = 0..7` at `q = 27`:

| `μ` | `q = 9`, `n = 0..9` | `q = 27`, `n = 0..7` |
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
| `(1,1,1,1,1)` | all 0 (`ℓ = 5 > h = 4`) | 0, 0, 0, 0, 0, 120, 720, 55440 |

  Check: `|W_∅(10)| = 17605249 = |W_∅(9)| + 8·|W_(1)(9)|` at `q = 9`. This is `P_4(9)`.
- **Fibre recursion (last coordinate `v`):** `|W_μ(n)| = Σ_{v∈F_q}|W_{μ+v}(n−1)|`, where `μ+v` is the profile of `S ∪ {v}`:
  - `v = 0` gives `μ`;
  - `v = −s_i` LOWERS `μ_i` by one;
  - `v = +s_i` RAISES `μ_i` by one;
  - `v` in an unused class APPENDS a part `1`.

**Rows.** Take `K ⊆ S_n` with `z := x_n` and `z^q ∈ K`.
- **Row `a`** is `R_a(K) := π_z(K : z^a) ⊆ S_{n−1}`, where `π_z` sets `z = 0`.
- **Rows increase with `a`**, and **`dim S_n/K = Σ_{a=0}^{q−1} dim S_{n−1}/R_a(K)`**.

**The conjecture.**
- `A_k(q) := dim S_{2k+2}/I^{(2k+2)}` and `P_k(q) := |W_∅(2k+2)|`. **Conjecture 1.2: `A_k(q) = P_k(q)`.**
- The floor `A ≥ P` is PROVED, so **the conjecture ⟺ `A_k(q) ≤ P_k(q)`.**

## 2 · THE FRAMEWORK: THE PARTITION INDUCTION
**Statement `T(n)`:** for every profile `μ` there is an EXPLICIT ideal `K_μ(n) ⊆ S_n` with:
- `z^q ∈ K_μ(n)`;
- `K_∅(n) = I^{(n)}`;
- `K_μ(n) = (1)` when `W_μ(n) = ∅`;
- `dim S_n/K_μ(n) ≤ |W_μ(n)|`.

**Inductive step.** `T(n−1)` implies `T(n)` at `μ` as soon as there is a bijection `a ↔ v` (rows `0..q−1` ↔ values `v ∈ F_q`) with **`R_a(K_μ(n)) ⊇ K_{μ+v}(n−1)`** for every `a`.
- Rows increase with `a`: give the LARGE fibres to the SMALL `a`.
- Within a block of rows of the same type, only the first row of the block needs proof.

**Base:** `n = 0`. ⟹ `T(n)` for all `n`, in particular the conjecture.

**Row dictionary for a profile with `ℓ` parts** (measured 126/126 rows, then 11 more cells last turn):
- rows `0 … ℓ−1` LOWER a part (larger fibre first, i.e. lower the largest part first);
- row `ℓ` is the value `0` (same type `μ`);
- rows `ℓ+1 … q−ℓ−1` are the `q−1−2ℓ` NEW-CLASS rows (type `μ ∪ (1)`);
- the last `ℓ` rows RAISE a part (larger fibre first, i.e. raise the smallest part first).

For `μ = (m,1)` in `n+1` variables: row 0 → `(m−1,1)`; row 1 → `(m)`; row 2 → `(m,1)`; rows `3..q−3` → `(m,1,1)`; row `q−2` → `(m,2)`; row `q−1` → `(m+1,1)`.

**`f` never increases along rows.** Lowering keeps `f`; the value `0` lowers it by 1; a new class and a raise lower it by 2. So the casillas with `f ≤ 1` form a world closed under rows.

**Leaves.** For `f ≤ 1`, `W_μ(n)` is one `S_n`-orbit. Its casilla is the Tanisaki ideal (§3.3.7), whose colength is the orbit size. So `T(n)` holds there by the count; only the parents' rows must contain it.

**Induction order.** Level `n−1` entirely, then level `n` profile by profile, `∅` first.
- Once `T(n)` holds at `∅`, the floor gives **`gr I(W_∅(n)) = I^{(n)}`**.
- Once `T(n)` holds at `μ` with an explicit `K_μ(n) ⊆ gr I(W_μ(n))`, equality of colengths gives **`K_μ(n) = gr I(W_μ(n))`**.
- **Consequence you must keep in mind:** every correct casilla IS the true casilla `gr I(W_μ(n))`. There is exactly one right answer per cell, and §3.4 lets you compute it.

## 3 · WHAT IS PROVED OR MEASURED (use it; do not re-prove it)
### 3.1 Earlier theorems (PROVED)
- The floor.
- The Plus Lemma (`(−2)^j = 1` in `F_3`).
- The casilla theorems: rows `a ≥ 1` of `I^{(n)}` contain `K_(1)(n−1)`.
- `(P_k)` for all `k, q`.
- `A_k = P_k` for `k ≤ 3`, all `q`.
- `A_k(3) = P_k(3)` for all `k` (Steinberg bridge; also reproved by this framework, since at `q = 3` there are no new-class rows).

### 3.2 The one-part line
**`K_(m)(n) := (e_odd) + box + (e_n, if n even and m ≥ 1) + N_{m−1}(n)`**, where **`N_w(n)`** is the ideal of the monomials `x_C·x_A^{q−1}` over all splittings `A ⊔ B ⊔ C = [n]` with `|B| − |A| ≤ w` and `|B| ≥ 1`.
- Colength `= |W_(m)(n)|`, measured 25/25. The rows equal the family as ideals.
- **Rows 0, 1, `q−1` are PROVED for all `q`** (they go to `K_(m−1)`, `K_(m)`, `K_(m+1)`).
- All generic rows `a = 2..q−2` carry type `(m,1)`, and only `R_2 ⊇ K_{(m,1)}(n−1)` needs proof.

### 3.3 From INFORME_8 and INFORME_9 (audited; the proofs are there)
1. **Row formula (PROVED).** Let `K = (e_odd) + box + M ⊆ S_{n+1}`, with `M` generated by elements `z^i·g(y)`, and let `M^{[i]} := {g : z^i g ∈ M}`.
   - Then `f ∈ R_a(K)` iff there are `c^0,…,c^{a−1}` (vectors indexed by odd degrees) with:
     - `Σ_r c_r^0e_{2r+1}(y) ∈ box + M^{[0]}`;
     - `Σ_r c_r^i e_{2r+1}(y) + Σ_r c_r^{i−1}e_{2r}(y) ∈ box + M^{[i]}` for `1 ≤ i ≤ a−1`;
     - `f ≡ Σ_r c_r^{a−1}e_{2r}(y)` mod `(e_odd) + box + M^{[a]}`.
   - On the one-part line: `M^{[0]} = N_{m−2}(n)`; `M^{[i]} = Ñ_{m−1}(n)` for `1 ≤ i ≤ q−2`, where `Ñ := N + (e_n(y))` when `n+1` is even and `m ≥ 1`; and `M^{[q−1]} = N_m(n)`.
   - Equivalently, **`R_2(K_(m)(n+1)) = π_z((I^{(n+1)} + N_{m−2}(n) + z·Ñ_{m−1}(n) + (z³)) : z²)`**.
2. **Iterated rows are lex-staircase colons (PROVED).** On the one-part line, `K_(m)(n) = π(I^{(n+m)} : (z_1⋯z_m)^{q−1})`, independent of the path.
3. **THE ENGINE (Lemma H for every `m`, PROVED).**
   - The slice `{z = w} ∩ W_∅(n+1)` equals `w·W_(1)(n)` for every `w ≠ 0` and every `n`.
   - Hence: **if `F ∈ I(W_(1)(n))` has top form `F_d ∈ Ñ_{m−1}(n)`, then `F_{d−1} ∈ R_2(K_(m)(n+1))`.** (Homogenize `G := Σ_i z^{d+1−i}F_i`. It vanishes on `W_∅(n+1)`, so `G ∈ I^{(n+1)}`. And `z·Ñ_{m−1}(n) ⊆ K_(m)(n+1)`.)
   - **General form (INFORME_9, verified in 11 cells):** every row inclusion `f ∈ R_a(K)` of every casilla `K = I^{(n+1)} + M` is the membership **`z^{a−1}f ∈ (I^{(n+1)} : z) + (M : z) + (z^a)`**. In every cell measured, its row EQUALS the true row. The `z^0`-room (`N_{m−2}`, `c^0 ≠ 0`) was never needed.
   - On `W_(1)(n)`: `E_y(T) = (T−1)·Ev(T)` with `Ev` even, so **`e_{2i+1}(y) = −e_{2i}(y)` on `W_(1)(n)`** for all `i` (`e_1 = −1`).
4. **Symmetric core (PROVED by the engine):** `e_{2i}(y) ∈ R_2(K_(m)(n+1))` for `n−m ≤ 2i ≤ n−1`.
5. **THE (G1) CASILLA** (explicit; exact as an ideal in 12/12 colon cells, plus membership gates at `(n+1,m) = (7,1), (7,2)`):
   **`K_{(m,1)}(n) := (e_j : j odd, or j ≥ n−m) + box + N_{m−1}(n) + F_m(n)`**, with `F_m(n) := (s^{(m)}_{jl} : j ≠ l)` and **`s^{(m)}_{jl} := y_j^{q−2}·e_{n−m−1}(y∖y_l)`**.
   - The family is redundant when `n−m−1 ≤ 1`.
   - PROVED: `K_(m)(n) ⊆ R_2`, the symmetric part, and **the family for `m = 1`, `n` even** (§3.5).
   - **NOT proved: the family for `m ≥ 2`, and for `m = 1`, `n` odd.**
   - **(G1) is the membership `z²·s^{(m)}_{jl} ∈ I^{(n+1)} + z·Ñ_{m−1}(n) + (z³)`.** It is MEASURED TRUE at `(n+1, m) = (6,2), (7,2), (7,3), (6,1)`. The certificate there is **second order**: it uses several `(q−1)`-monomials of the layer with different `A`, plus `q`-free squarefree terms. **Its coefficients were never read.**
6. **Rows 0, 1 of `K_{(m,1)}(n)` are PROVED; row 2 is PROVED given (G1).**
7. **Leaves** (MEASURED in 16 cells; the geometric side is classical in characteristic 0). For `f ≤ 1`, the casilla is **the Tanisaki ideal `I_λ + box`**, with `λ := μ ∪ (1^f)`:
   - `I_λ := (e_r(x_S) : S ⊆ [n], r > |S| − d_{|S|}(λ))`, where `d_k(λ) := λ'_n + … + λ'_{n−k+1}` (`λ'` is the conjugate partition, padded with zeros to length `n`);
   - its colength is `n!/Π_i λ_i!`.
8. **The `q`-free part of every casilla** is `Q_μ(n) := (e_j([n]) : j odd or j ≥ n−|μ|+1) + (e_r(x_S) : S ⊊ [n], r > |S| − d_{|S|}(λ))`. This is verified against the TRUE casilla in 6/6 cells, including the first cell with `f = 4`. `e_4 ∉ gr I(W_{(1,1,1)}(7))` is PROVED by a rank test; `e_6 ∈` it is PROVED by a certificate checked on all 20370 points.
9. **Measured interaction families** (all in the uniform degree **`q + f − 2`**):

   | `μ` | second factor | first factor |
   |---|---|---|
   | `(m)` | degree `f−1` | `x_j^{q−1}` |
   | `(m,1)` | `e_f(y∖y_l)` | `y_j^{q−2}` |
   | `(2,2)` at `n = 6` | `e_f(y∖y_l)` (the same shape: for two parts the family does not see `μ_2`) | `y_j^{q−2}` |
   | `(1,1,1)` at `n = 4, 5, 6` | `y_l^{f+1}` | `y_j^{q−3}` |
   | `(1^4)` at `n = 5, 6` | `y_l^{f+2}` | `y_j^{q−4}` |

   - **The first-factor exponent is a THRESHOLD, not an identity:** every `a ≤ q−ℓ` gives the SAME ideal, and every `a > q−ℓ` gives a strictly bigger one (measured at `(1,1,1)`, `n = 5, 6`; `(1^4)`, `n = 6`).
   - **At `(1,1,1)`, `n = 7` (target 20370) the family is UNKNOWN.** No `S_n`-orbit of a two-variable monomial `y_j^ay_l^b` works in ANY degree: `D = 10, 11, 12, 13` give at best 16450, 17185, 19040, 20146, all too strong, and the colength is monotone in `D` and steps over the target between `D = 13` and `D = 14`. `y_j^ae_b(y∖y_l)` (`a = 5..8`) and the antisymmetric `y_j^3y_l^8 − y_l^3y_j^8` are also too strong.
10. **Two-part layer weight.** For `μ_2 ≥ 2` the monomial layer has weight `|μ| − ℓ − 1`.
11. **Cells closed:** `T(7)` at `(1)` and at `(2)`, `q = 9` (the rows sum to 37947 and 13496).

### 3.4 THE CASILLA IS COMPUTABLE (PROVED; new since the last mission — this is your main tool)
- **Fibre ideal, every profile.** With `S` the anchor multiset of `μ` and **`R_j := Σ_{r=0}^{|μ|} e_r(S)·e_{j−r}(y)`**:
  **`I(W_μ(n)) = (R_j : j odd, 1 ≤ j ≤ n+|μ|) + (x_i^q − x_i : i ≤ n)`**, for EVERY profile `μ` and every odd `q`.
  - *Proof.* `P(T) := Π_i(T+y_i)·Π_{s∈S}(T+s) = Σ_j R_j·T^{n+|μ|−j}`. The multiset `{−y_i}∪{−s}` is closed under negation iff `P(−T) = ±P(T)`, iff the coefficients of the wrong parity vanish, and those are exactly the odd `j` in both parities of `n+|μ|`. The ideal is radical because it contains `x_i^q − x_i`, and its zero set is `W_μ(n)`. ∎
  - **Consequences:** `e_j(y) ∈ gr I(W_μ(n))` for every odd `j ≤ n` (the top form of `R_j`). And `e_n(y) ∈ gr I` as soon as some `i ≡ n+1 (mod 2)` in `[1,|μ|]` has `e_i(S) ≠ 0`.
- **THE CASILLA IS THE TOP FORMS OF A DEGREVLEX GRÖBNER BASIS of that ideal:** `gr I(W_μ(n)) = (top form of g : g ∈ gb(I(W_μ(n))))`, for any degree-compatible order.
  - Measured at `q = 9`: colength = fibre EXACTLY at `(1,1,1)` for `n = 4, 5, 6`, `(2,1)` at `n = 5`, and `(1^4)` at `n = 6`. The cpu time is 0.0004 s to 3 s.
  - The low-degree minimal generators are exactly `Q_μ(n)`. Degree `q` is the box, with ONE generator always redundant: `y_n^q = −Σ_{i<n}y_i^q` modulo `e_1`, because Frobenius is additive. Degree `q+f−2` is the family.
- **THE CASILLA DOES NOT SEE THE ANCHOR** (measured today; auditor, `q = 9`, 5/5 cells): different anchor multisets of the same profile give the SAME ideal `gr I(W)`. The cells are `(1,1)` with 4 anchors at `n = 5` and 3 at `n = 6`; `(2,1)` with 3 anchors at `n = 5` and at `n = 6`; `(1,1,1)` with 3 anchors at `n = 5`. This is forced by the framework wherever `T(n)` holds. A pencil proof of it in general is a bonus.
- **The layer `N_w` is REDUNDANT for `(1^ℓ)`, `ℓ ≥ 2`** (PROVED reason, measured 4/4). The smallest layer generator has degree `q+n−3`, which is strictly above the family degree `q+n−ℓ−2`. **Dropping it makes the `n = 7` base 140 times cheaper** (424 s → 3 s). For `(m)` and `(m,1)` the layer is NOT redundant.
- **How to compute at `n = 7`.** A full Gröbner basis of `I(W_{(1,1,1)}(7))` was killed at 601 s. Instead:
  - compute `gb(I(W), DegreeLimit => q+f)` (or build the homogenization and truncate);
  - take the top forms `J`;
  - **certify by colength:** `J ⊆ gr I(W)` always, so `dim S/J = |W_μ(n)|` ⟹ `J = gr I(W)` exactly.
  - If `dim S/J` is larger, raise the limit by one and retry. Estimate first.

### 3.5 The model to imitate: `m = 1`, `n = 2k` even (PROVED for all `k`, `q`)
**Setting and notation.**
- `K_(1)(2k+1)`, `y := (x_1..x_{2k})`, `z := x_{2k+1}`, `W_0 := W_(1)(2k)`.
- Fix `j ≠ l` and put `P := y∖{y_j, y_l}` and `τ := y_j^{q−1}·Π_P` (so `z·τ` is a monomial of the layer).
- **`s_0 := y_j^{q−2}·e_{2k−2}(y∖y_l)`**.

**Identity (D_k)**, exact on every point of `W_0`, PROVED by cases:
`s_0 + τ = E' + u + D − Σ(P) − [y_j+y_l=0]R'_j + [y_j=y_l](1−y_j)R'_j − Σ_{a=±1}([y_j=a]y_l + [y_l=a]y_j)D`, where:
- `F(s) := Σ_{m<k} e_{2m}(y)s^{k−1−m}`;
- `D := F[y_j², y_l²]` (divided difference) and `R'_j := F'(y_j²)`;
- `u := Π_P`, `E' := e_{2k−3}(P)`, `Σ(P) := Π_{p∈P}(1+y_p)`;
- `[x=a] := 1 − (x−a)^{q−1}`.

**(B_k) — the model proof of this campaign.** The degree-`(q+2k−4)` remainder must lie in `R_2`: `X := (y_j−y_l)^{q−1}y_jR'_j − y_j^{q−1}y_lD − y_l^{q−1}y_jD`. Put `a := y_j`, `b := y_l`.
1. **Degree.** Only `J := (e_odd, e_{2k}) + box` can contain `X`.
2. **Relations.** `Π(T+y_i) ≡ T²F(T²)`, so `a²F(a²) ∈ J` and `(a+b)(F(a²) + b²D) ∈ J`.
3. **Frobenius.** `(a−b)^q ≡ 0`, and `X_1 ≡ −(a−b)^{q−1}(a+b)D`.
4. **Lucas.** `(a−b)^{q−1} = h_{q−1}(a,b)`, so `X ≡ a²b²h_{q−4}(a,b)D` with `h_{q−4}(a,b) = (a+b)h_{(q−5)/2}(a²,b²)`.
5. Hence `X ≡ −(a+b)h·a²F(a²) ∈ J`. ∎

### 3.6 The odd case `m = 1`, `n` odd — the skeleton is PROVED, one step is missing
- Target: `s := y_j^{q−2}e_{n−2}(y∖y_l) ∈ R_2(K_(1)(n+1))`, with `n` odd. Put `u := y_j`, `P := y∖{y_j,y_l}`, `τ := y_j^{q−1}Π_P`.
- **(R1) and (O) are PROVED:** on `W_(1)(n)`, `n` odd, every `q`,
  **`s + τ = −u^{q−1}y_l^{q−2}Π_P + u^{q−1}(1−y_l^{q−1})e_{n−3}(P)`** (O),
  **`s + τ = −y_l^{q−2}Π_P + u^{q−1}(1−y_l^{q−1})e_{n−3}(P)`** (O′).
- ⚠️ **TRAP:** INFORME_9 PRINTS (O′) with a MINUS in front of the second term. **That is wrong.** The sign is `+`. The printed version fails at 1260 of the 17100 checks at `n = 5`; the report's own script `odd5.py` uses `+`. Somebody already built a false identity on the printed sign. Do not be the second.
- A low-degree form of the right-hand side EXISTS at `n = 5` (linear algebra on the 855 points). **What is missing is the joint lowering of the two terms** `y_l^{q−2}Π_P` and `[u≠0][y_l=0]e_{n−3}(P)`, i.e. a case analysis on the partners of `y_l`.
- **Antisymmetrising in `j ↔ l` is EMPTY** (it collapses to a triviality about the parity of the number of zeros). The work has to be done on the symmetric part.

## 4 · THE TARGETS
### PART A — THE ONE LEMMA (the must)
**The idea.** (G1) is an ideal membership that the machine confirms. It holds as `z²·s = Σ_g A_g·g` over the generators `g` of `I^{(n+1)} + z·Ñ_{m−1}(n) + (z³)`. **Nobody has looked at the coefficients `A_g`.** The last Fable wrote that everything else (the odd `m = 1` case, the layer shadows of PART B of last mission, the three-part fire test) «becomes bookkeeping» once these certificates are known with letters. Your job is to make that sentence true.

**A0 — Learn to read, where the answer is known (budget 25 min).**
- Cell `(n+1, m) = (5,1)`: `n = 4` is even, so (D_4)/(B_2) of §3.5 is the known answer.
- Extract a certificate. In M2, if `clf ∈ clJ` then `(matrix{{clf}}) // (gens clJ)` returns `c` with `gens clJ * c == clf`.
- Then REDUCE it: subtract syzygies of `gens clJ` until the support is smallest (count terms), and split it by `z`-degree `A^0 + z A^1 + z² A^2`.
- Match it with (D_k)/(B_k): which `A_g` is the `(a+b)(F(a²)+b²D)` of step 2, which is the Lucas step?
- Write the dictionary «certificate term ↔ proof step».

**A1 — Extract where the answer is NOT known (budget 30 min).**
- Cells: `(6,2)`, `(6,1)` (this is `m = 1`, `n = 5` odd), `(7,2)`, `(7,3)`, all at `q = 9`.
- To see which coefficients carry `q`: extract `(5,1)` also at `q = 27` (5 variables, allowed). **Six variables at `q = 27` are forbidden**, and at `n+1 = 5` the family for `m = 2` is redundant (`n−m−1 = 1`). So the `q`-dependence of the unknown cells must be READ from the `q = 9` certificates plus the `(5,1)` comparison `q = 9` vs `q = 27`, not measured.
- **In 7 variables compute memberships and lifts one at a time, alone** (§0.10). If a lift does not fit, extract only the `z²`-part by working modulo `(z³)` in a smaller presentation, and say what you did.
- For each cell, list the certificate by TYPES of generator: `e_{2i+1}` with coefficient `A^0`; layer monomials `z·x_C x_A^{q−1}` grouped by `(|A|,|B|,|C|)`; `e_n`; box.
- Say how many layer monomials with different `A` enter, and which `q`-free squarefree terms appear.

**A2 — Read with letters and prove (budget 40 min).**
- Find the closed form of `A^0, A^1, A^2` with `m`, `n`, `q` as letters. Hints from the measured shapes:
  - the family degree `q+f−2`;
  - the threshold `a ≤ q−ℓ` of §3.3.9 (it says only the MULTIPLICITY `q−2 ≥ …` matters, which smells like Lucas);
  - the (B_k) proof, which used exactly three tools: the generating identity `Π(T+y_i) ≡ T²F(T²)`, Frobenius `(a−b)^q ≡ 0`, and Lucas `(a−b)^{q−1} = h_{q−1}(a,b)`.
- Then PROVE it with letters: either the membership directly, or through the engine §3.3.3 as a function identity on `W_(1)(n)` checked on all points.
- If it closes for `m ≥ 2`: write **«(G1) FOR m ≥ 2, ALL n, q»**.
- If A1's `(6,1)` certificate also closes the odd case, or §3.6 closes by the case analysis: **«ONE-PART LINE CLOSED FOR ALL q»**.

**Dead for PART A (measured; do not retry):**
- the first-order ansatz «certificate with a single `u = y_i` multiplier»;
- the lift lemma `x_{Y'}^{q−1}K_(1)(V∪z) ⊆ K_(m)(n+1)` (correct but INERT);
- monotonicity `K_(1) ⊆ K_(m)`;
- a Lemma H on `W_∅(n+m+1)` (out of the induction order);
- the tautological induction on simultaneous colons (false at `N = 2`);
- antisymmetrising (O′).

### PART B — THE CASILLA MACHINE
**B1 — Compute the truth (budget 25 min).**
- With §3.4, compute `G_μ(n) := gr I(W_μ(n))` for the twelve multi-part profiles that are non-empty at `q = 9`: `(1,1), (2,1), (3,1), (4,1), (2,2), (3,2), (1,1,1), (2,1,1), (3,1,1), (2,2,1), (1,1,1,1), (2,1,1,1)`.
- Cover every allowed `n` (at most 7 at `q = 9`). At `q = 27` use `n ≤ 5`, where the fibre is non-empty.
- Start from the small fibres. Use `DegreeLimit` plus the colength certificate for the big ones. Estimate each; skip what does not fit, and say so.
- **Include `(1,1,1)` at `n = 7`** (target 20370), with `DegreeLimit => q+f` (so 13 at `q = 9`, `f = 4`), certified by colength.
- For each cell record the minimal generators by degree. Then record the top-degree non-symmetric generators as an `S_n`-module: orbit type and number, and whether they are monomials, orbits of monomials, or genuinely mixed.

**B2 — Read ONE formula (budget 20 min).**
- Propose a uniform `K_μ(n) = Q_μ(n) + box + [layer N_w, only when needed, with w as a function of μ] + F_μ(n)`, with `F_μ` a function of `μ`, `n`, `q`.
- Gate it AS AN IDEAL against `G_μ(n)` in EVERY cell of B1 (not by colength: by equality of ideals).
- The `(1,1,1)` family at `n = 7` must come OUT of B1, not be guessed.
- If one formula does not fit all twelve, give the smallest set of formulas that does, and say where each breaks.

**B3 — The two questions B answers for A (budget 5 min).**
- Is the interaction family of every multi-part `μ` in the uniform degree `q+f−2`? Say YES/NO with the first exception.
- Is the anchor-independence of §3.4 still true in every cell you computed (test at least two anchors per profile)?

### PART C — THE LEDGER OF ROW `k = 4` (budget 25 min)
**The goal.** `A_4(q) = P_4(q)` for all `q` is `T(10)` at `∅`. It needs `T(n)` at every profile `μ` with `|μ| ≤ min(n, 10−n)`, for `n ≤ 9`. These are the five one-part profiles `(1)…(5)` and the thirteen multi-part profiles of §1 (at `q = 9` the profile `(1^5)` is empty).

**The ledger.**
- For every such `(μ, n)` that is NOT a leaf, list its rows by the dictionary, with the child each row must contain.
- Give each row one of these statuses:
  - **PROVED** (say by what);
  - **ENGINE** (it is an engine membership whose certificate is of the type of PART A, and you say which);
  - **OPEN** (say what is missing).
- Count them; rows of the same type and block count once.

**The payoff.**
- **If after PART A every row is PROVED or reduced to the lemma you proved:** write **«ROW k = 4 CLOSED FOR ALL q»** and give the full chain.
- If not: the exact list of the remaining identities, each with its smallest test cell. That list is mission 11.

## 5 · PROCESS
- **STEP 0 — Design and sealed bets (15 min, no runs).**
  - Plan A0–A2 and B1–B2, with the estimate of every run you intend.
  - **Seal at least FIVE predictions before running anything**, each with the number or shape you expect. At least TWO of them must be risky (you are not sure). Examples:
    - «the certificate at `(6,2)` uses exactly … layer monomials»;
    - «`A^1` is `q`-free»;
    - «the `(1,1,1)` family at `n = 7` lives in degree 11»;
    - «the `(2,2,1)` family has the `(m,1)` shape».
  - At the end, score them: hits and falsified, both printed the same size.
- **STEP 1 — PART A, A0 + A1 (55 min).**
- **STEP 2 — PART A, A2 (40 min).**
- **STEP 3 — PART B (50 min).** If you have two light engines, B1 may run while you read A1's certificates.
- **STEP 4 — PART C (25 min).**
- **STEP 5 — Verdict (10 min)**, after re-reading the disk. Score the sealed bets.
- **WHAT I FOUND BEAUTIFUL:** one paragraph. What surprised you, what you liked, and what you would do next if this were your own problem.
- **FOR MISSION 11:** the engine that works (or the reason none does); the smallest open cell of each kind; and your estimate of what closing row `k = 4` still takes.

## 6 · DEAD ROUTES (do not retry)
- Separate counting lemmas for rows (the counts ARE the induction).
- The odd casilla with `j ≤ min(2, k−1)` (wrong from `k = 5`).
- «Rows ⊆ fibres» as a formal consequence (false; three points).
- The sum of colons alone for generic rows (too small; the shadows come from mixed certificates).
- The lift lemma and monotonicity for (G1) (inert).
- The first-order single-multiplier certificate for (G1).
- **Guessing interaction families and gating them by colength.** That loop ran two missions. The casilla is COMPUTABLE (§3.4): read it.
- The uniform second factors `e_{f+ℓ−2}(y∖y_l)`, `h_{f+ℓ−2}(y∖y_l)`, `p_{f+ℓ−2}(y∖y_l)` for every `μ`.
- Any `S_n`-orbit of a two-variable monomial for `(1,1,1)` at `n = 7`, in any degree.
- The printed sign of (O′); antisymmetrising (O′).
- Any ascent in `q` (a tower elevator): dead, with proof.
- Measuring cells as a substitute for a mechanism: cells are gates only.

## 7 · SUCCESS
- **Minimum:** one new infinite family PROVED with letters, plus the certificates of PART A written down explicitly.
- **Good:** **ONE-PART LINE CLOSED FOR ALL q.**
- **Excellent:** GOOD, plus the uniform `K_μ` for the twelve profiles, equal as ideals to the true casilla in every allowed cell, plus the ledger of row `k = 4` reduced to engine identities of the type you proved.
- **Full:** **ROW `k = 4` CLOSED FOR ALL q** (`A_4(q) = P_4(q)` for every `q = 3^v`), or a uniform `K_μ` with all row inclusions ⟹ **CONJECTURE 1.2 CLOSED.**

*Last word from the auditor.* The last three Fables built the whole machine: the induction, the engine, the casillas, the fire test. You hold the first tool that turns guessing into reading. The single lemma that is missing is written, in coefficients, inside four Gröbner certificates that nobody has opened. Open them.

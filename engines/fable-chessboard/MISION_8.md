# MISSION 8 — THE PARTITION INDUCTION. CLOSE CONJECTURE 1.2.
*(Grepy el Cartógrafo, auditor, 2026-09-22.)*

**You are a NEW Fable. This file is SELF-CONTAINED: read it whole before anything else; you need nothing else.** The reports `INFORME.md` … `INFORME_7.md` in this folder are audited and APPROVED. Open `INFORME_7.md` §1 only if you want the full text of the descent (§3.4 below states everything you need).

> **OBJECTIVE: the complete closure of Conjecture 1.2 of Degtyarev–Shimada, for all `k` and all `q = 3^v`.**
>
> **Where we stand (every item below is verified):**
> - The conjecture is now ONE induction on the number of variables, over explicit ideals («casillas») indexed by an IMBALANCE PROFILE `μ` (§2). No count is ever needed: only inclusions of rows.
> - The whole one-part line `μ = (m)` is DONE for every `q`, by pencil (§3.2). At `q = 3` it already proves `A_k(3) = P_k(3)` for all `k` by this new route, so the framework is validated.
> - **What is left is the casillas of the profiles with two or more parts, and their row inclusions.**
>   - Their anatomy is MEASURED: lower neighbour + `q`-free core + interaction family (§3.5).
>   - Their row dictionary is MEASURED (§3.6).
>   - Each is squeezed between two explicit neighbours (§3.5).
>   - The first one, `(1,1)`, already has its interaction family PROVED for all `k`, `q` (§3.4).
> - **For «D(4) FOR ALL q» the work list is 13 explicit profiles (§4).**
>
> **Prize ladder:**
> - **MINIMUM:** (G1) — the generic row of the whole one-part line, for all `m, n, q`.
> - **ROW:** the 13 profiles ⟹ **D(4) FOR ALL q**, the first new row of the conjecture.
> - **FULL:** one construction `K_μ(n)` uniform in `μ` ⟹ **CONJECTURE 1.2 CLOSED.**
>
> **Aim at FULL from the first minute. Every piece of the machine exists; you are asked to assemble it.**

---
## 0 · RULES OF THE TURN (mandatory)
1. **BEFORE THINKING:** create `INFORME_8.md` with the empty sections `## FIRST LINE` · `## STEP 0` · `## STEP 1` · `## STEP 2` · `## STEP 3` · `## STEP 4 — VERDICT`.
2. **Save to disk after every step.** What is not written does not exist.
3. **Header per step:** `STATE: CLOSED | EXHAUSTED | NOT CONCLUDED` and `NEXT:`.
4. **In order, no going back, no step 5, no retries.**
   - Write the budget before each step.
   - 10 min without progress ⟹ stop, write, declare.
   - Keep the last 20 % of each budget for writing.
5. **At most one literature search per step**, in the original source.
6. **Do not recompute anything listed here as proved or measured.**
7. **A negative dimension, or one larger than the box, is a bug:** stop.
8. **«This route dies, for this reason» is a result.**
9. **Write ONLY in `~/Desktop/FABLE_TABLERO/`. Do not open anything in `~/Desktop/ARBOLYAML/`.**
10. **Machine:** `/opt/homebrew/bin/M2`. This Mac has no `timeout`; use the folder's `wd.sh` wrapper (570 s).
    - Each run must stay **< 1.2 GB and < 10 min**.
    - Write an estimate BEFORE each run, for its most expensive case. Estimate each engine separately, never «the turn».
    - After any kill, check with `ps`/`pgrep` that it is gone, and write that you checked.
    - M2 reserved names (`check`, `top`, `info`, …) abort scripts: prefix your own names.
    - Never pass thousands of generators at once. Reduce them modulo a Gröbner basis and add only the non-zero normal forms.
    - **Allowed:** explicit ideals in `n` variables with `n ≤ 10` at `q = 3`, `n ≤ 7` at `q = 9`, `n ≤ 5` at `q = 27`, `n ≤ 4` at `q = 81`.
      - Colengths, colons by a power of one variable, memberships, minimal generators.
      - Python evaluation of a function on all points of a fibre at `q ≤ 27`.
    - **Forbidden:** any M2 run with `n ≥ 8` at `q ≥ 9`, or `n ≥ 6` at `q = 27`, or `n ≥ 5` at `q = 81`; point ideals over `GF(27)`; point enumeration in M2.
11. **Re-read the disk before the verdict.**
12. **Double check:**
    - every PROVED claim carries its proof in the report;
    - every number carries its cell and its log;
    - every identity used in a proof is checked exactly — symbolically, or on all points of the set it is claimed on;
    - every new casilla passes its colength gate against §1 BEFORE you build on it.

**FIRST LINE** (answer first, in this order):
- (a) Which profiles `μ` now have an explicit casilla with PROVED row inclusions, for all `n` and all `q`?
- (b) What exactly is still missing, and in which cell was it checked?
- (c) Does it close the conjecture, or the row `k = 4` for all `q`? YES or NO, with the reason in one line.

---
## 1 · THE OBJECTS
**Basics.**
- `q = 3^v`, `h := (q−1)/2`.
- `S_n := F_q[x_1..x_n]`; `e_r` := elementary symmetric polynomial of degree `r`; `box := (x_1^q, …, x_n^q)`.
- **`I^{(n)} := (e_1, e_3, e_5, …) + box`.**
- `x_C := Π_{i∈C} x_i`; `x_A^{q−1} := Π_{i∈A} x_i^{q−1}`.

**Profiles and fibres.**
- A finite multiset `S ⊂ F_q` («fixed values») constrains `y ∈ F_q^n` by: «the multiset `y ∪ S` is closed under negation».
- Only the unpaired part of `S` matters. Its **profile** is `μ = (μ_1 ≥ … ≥ μ_ℓ)`: one positive integer per non-zero class `{s,−s}`, where `μ_i` = how many more copies of `−s_i` than of `s_i` the point `y` must carry. Zeros impose nothing.
- **`W_μ(n) := {y ∈ F_q^n : y ∪ S closed}`.** Up to a bijection it depends only on `μ`. It is empty iff `|μ| > n` or `ℓ(μ) > h`.
- **Fibre sizes, exact:** with `I_m(t) := Σ_{b≥0} t^{2b+m}/(b!(b+m)!)`,
  **`|W_μ(n)| = n!·[t^n] E(t)·Π_i I_{μ_i}(t)·I_0(t)^{h−ℓ(μ)}`**, where `E = cosh` if `n − |μ|` is even and `sinh` if it is odd.
  - Gates at `q = 9`: `|W_∅(4)| = 217`, `|W_(1)(5)| = 855`, `|W_(1,1)(4)| = 84`, `|W_(2)(4)| = 46`, `|W_(1)(4)| = 88`, `|W_(1)(8)| = 227144`, `|W_(1)(9)| = 1930329`, `|W_(1,1)(8)| = 204456`, `|W_(2)(8)| = 130984`.
- **Fibre recursion (last coordinate `v`):** `|W_μ(n)| = Σ_{v∈F_q} |W_{μ+v}(n−1)|`. Here `μ+v` is the profile of `S ∪ {v}`:
  - `v = 0` gives `μ`;
  - `v = −s_i` LOWERS `μ_i` by one (the part disappears at 0);
  - `v = +s_i` RAISES `μ_i` by one;
  - `v` in an unused class APPENDS a part `1`.

**Rows.**
- For an ideal `K ⊆ S_n` with `z := x_n` and `z^q ∈ K`, **row `a`** is `R_a(K) := π_z(K : z^a) ⊆ S_{n−1}`, where `π_z` sets `z = 0`.
- **Rows increase with `a`**, and **`dim S_n/K = Σ_{a=0}^{q−1} dim S_{n−1}/R_a(K)`**.

**The conjecture.**
- `A_k(q) := dim S_{2k+2}/I^{(2k+2)}`, `P_k(q) := |W_∅(2k+2)|`. **Conjecture 1.2: `A_k(q) = P_k(q)`.**
- The floor `A ≥ P` is PROVED (`I^{(n)} ⊆ gr I(W_∅(n))`, where `gr` is the ideal of top forms). So **the conjecture ⟺ `A_k(q) ≤ P_k(q)`.**

## 2 · THE FRAMEWORK: THE PARTITION INDUCTION
**Statement `T(n)`:** for every profile `μ` there is an EXPLICIT ideal `K_μ(n) ⊆ S_n`, with `z^q ∈ K_μ(n)` and `K_∅(n) = I^{(n)}`, such that `dim S_n/K_μ(n) ≤ |W_μ(n)|`.
- **Empty fibre convention:** if `W_μ(n) = ∅` you need `K_μ(n) = (1)`.

**Inductive step.**
- Compare the row and fibre recursions. `T(n−1)` implies `T(n)` for the profile `μ` as soon as there is a bijection `a ↔ v` between the rows `0..q−1` and the values `v ∈ F_q` with **`R_a(K_μ(n)) ⊇ K_{μ+v}(n−1)`** for every `a`.
- Rows increase with `a`, so give the LARGE fibres to the SMALL `a`. For a block of rows carrying the same type, it suffices to prove the inclusion for the first row of the block.
- **Base:** `n = 0`, with `K_∅(0) = 0` and `K_μ(0) = (1)` for `μ ≠ ∅`.
- ⟹ `T(n)` for all `n`, in particular `A_k(q) ≤ P_k(q)`: **the conjecture.**
- **FR20:151 test (passed):** `T(n)` for `μ ≠ ∅` is STRICTLY stronger than the conjecture and falsifiable cell by cell. It is not a restatement.

**Tools available in induction order.**
- At step `n`, `T(n−1)` together with the floor gives `gr I(W_∅(n−1)) = I^{(n−1)}`.
- More generally it gives `gr I(W_ν(n−1)) = K_ν(n−1)` for every `ν` whose casilla satisfies the floor `K_ν ⊆ gr I(W_ν)`. This is PROVED for `ν = ∅` and `ν = (1)`, and is NOT automatic for `ν = (m)` with `m ≥ 2`: `e_n` does not vanish on `W_(2)(n)`, which has points without zeros.
- If your engine needs the floor for a profile, prove it or avoid it, and say which.

## 3 · WHAT IS PROVED OR MEASURED (use it; do not re-prove it)
**1. Earlier theorems (all PROVED; do not re-prove):**
- the floor;
- `(P_k)`: the identities `x_{2k}·x_C(x_A^{q−1} + x_B^{q−1}) ∈ I^{(2k+1)}` for `|A| = |B| = j`, `2 ≤ j ≤ k−1` — all `k`, all `q`;
- the **Plus Lemma** (`(−2)^j = 1` in `F_3`, so the parity product has top form exactly `x_C(x_A^{q−1} + x_B^{q−1})`);
- **the casilla theorems:** row `a ≥ 1` of `I^{(n)}` contains `K_(1)(n−1)`, given `T(n−1)` at `μ = ∅` (the even one via the Plus Lemma, the odd one via `(P_k)` and the anchor `x_n·e_{n−1} = e_n` for `n` odd);
- `A_k = P_k` for `k ≤ 3`, all `q` (external: Sofá, Hamaca);
- `A_k(3) = P_k(3)` for all `k` (Steinberg bridge).

**2. THE ONE-PART LINE, CLOSED FOR ALL `q`.** For `m ≥ 0`:
**`K_(m)(n) := (e_odd) + box + (e_n, if n even and m ≥ 1) + (x_C·x_A^{q−1} : A ⊔ B ⊔ C = [n], |B| − |A| = m − 1, |B| ≥ 1)`.**
- For `m = 0` the monomial layer is redundant and `K_(0)(n) = I^{(n)}`.
- Old names: `K_(1)(2k+1)` = even casilla; `K_(1)(2k)` = odd casilla with `|A| = |B| ≤ k−1`; `K_(2)(2k)`, `K_(2)(2k−1)` = the `+1`-row ideals.
  - ⚠️ Earlier missions wrote the odd casilla with `j ≤ min(2,k−1)`: that is WRONG from `k = 5` (8602 instead of 8350 at `(n,q) = (10,3)`).
- **Measured.**
  - Colength = `|W_(m)(n)|` in 25/25 cells (`q = 3` with `n ≤ 8`, `m ≤ 4`; `q = 9` with `n ≤ 6`).
  - Rows equal the family AS IDEALS, 11/11.
- **Row inclusions, PROVED by pencil for all `q`.** For `m ≥ 1`, with dictionary `a = 0 ↔ v = −1`, `a = 1 ↔ v = 0`, `a = q−1 ↔ v = +1`, generic `a ↔` new class:
  - **`R_{q−1} ⊇ K_(m+1)(n−1)`:**
    - monomials from the layer with `z ∈ A`;
    - `z^{q−1}e_{2r+1}(y) = z^{q−1}e_{2r+1}(y,z) − z^q e_{2r}(y)`;
    - for `n` odd, `z^{q−1}e_{n−1}(y) = z^{q−2}·e_n(y,z)`.
  - **`R_1 ⊇ K_(m)(n−1)`:**
    - monomials with `z ∈ C`;
    - `e_{2r+1}(y) = π_z(e_{2r+1}(y,z) − z·e_{2r}(y))`, and `z·(that) ∈ K`;
    - for `n` odd, `z·e_{n−1}(y) = e_n(y,z)`.
  - **`R_0 ⊇ K_(m−1)(n−1)`:**
    - monomials with `z ∈ B`;
    - `e_odd` and box by setting `z = 0`;
    - `e_{n−1}(y)` (needed when `n` is odd and `m ≥ 2`) equals `Π y`, a multiple of the monomial `x_C` with `A = ∅`, `z ∈ B`, `|B| = m−1`, `C ⊂ y` — trivial.
  - `m = 0`: rows `a ≥ 1` are the casilla theorems; row 0 is trivial.
- **Consequence, PROVED:** at `q = 3` there are no generic rows, so `T(n)` holds along the whole line. **The partition induction proves `A_k(3) = P_k(3)` for all `k` by a new route.** At `q ≥ 9`, the ONLY missing rows of the one-part line are its generic rows, whose type is `(m,1)`.

**3. Generic rows are all equal to the first.** `R_2 ⊆ R_3 ⊆ … ⊆ R_{q−2}`, and all carry the same type, so only `R_2 ⊇ K_{(m,1)}(n−1)` is needed. (Measured `R_2 = R_3` in every cell.)

**4. Type `(1,1)`, interaction family, PROVED for all `k`, `q`.** Setting: `K_(1)(2k+1)`, `y := (x_1..x_{2k})`, `z := x_{2k+1}`, `W_0 := W_(1)(2k)`. Fix `j ≠ l`, `P := y∖{y_j, y_l}`, `τ := y_j^{q−1}·Π_P` (so `z·τ` is a monomial of the layer), and **`s_0 := y_j^{q−2}·e_{2k−2}(y∖y_l)`**.
- **Lemma H.** If `f ∈ I(W_0)` has top form `t` (degree `d`) and next form `s` (degree `d−1`), then `z·t + z²·s ∈ gr I(W_∅(2k+1)) + (z³)`. The reason: the slice of `W_∅(2k+1)` over `z = w ≠ 0` is `w·W_0`, and `z^{d}f(y/z)` vanishes on it.
- **Descent.** If moreover `z·t ∈ K`, then `s ∈ R_2(K)`.
- **Identity (D_k), exact on every point of `W_0`, PROVED by cases:**
  `s_0 + τ = E' + u + D − Σ(P) − [y_j+y_l=0]R'_j + [y_j=y_l](1−y_j)R'_j − Σ_{a=±1}([y_j=a]y_l + [y_l=a]y_j)D`,
  where:
  - `F(s) := Σ_{m<k} e_{2m}(y)s^{k−1−m}`;
  - `D := F[y_j², y_l²]` (divided difference);
  - `R'_j := F'(y_j²)`;
  - `u := Π_P`, `E' := e_{2k−3}(P)`, `Σ(P) := Π_{p∈P}(1+y_p)`;
  - `[x=a] := 1 − (x−a)^{q−1}`.
  - Auditor check: exact at `(k,q) = (2,9), (3,9), (4,9), (5,9), (6,9), (2,27), (3,27), (4,3)`.
- **(B_k) — the model proof of this campaign; imitate it.** The degree-`(q+2k−4)` remainder `X := (y_j−y_l)^{q−1}y_jR'_j − y_j^{q−1}y_lD − y_l^{q−1}y_jD` must lie in `R_2`.
  1. **Degree:** the casilla's monomials have degree `≥ q+2k−3`, so only **`J := (e_odd, e_{2k}) + box`** can contain `X`.
  2. **Relations in `J`:** `Π(T+y_i) ≡ T²F(T²)`, so `a²F(a²) ∈ J` and `(a+b)(F(a²) + b²D) ∈ J`, with `a = y_j`, `b = y_l`.
  3. **Frobenius:** `(a−b)^q ≡ 0`, so `(a−b)^{q−1}` kills multiples of `a−b`, and `X_1 ≡ −(a−b)^{q−1}(a+b)D`.
  4. **Lucas:** `(a−b)^{q−1} = h_{q−1}(a,b)`, so `X ≡ a²b²h_{q−4}(a,b)D`, with `h_{q−4}(a,b) = (a+b)h_{(q−5)/2}(a²,b²)`.
  5. Hence `X ≡ −(a+b)h·a²F(a²) ∈ J`, and `J ⊆ R_2`. ∎
  - Result: **`s_0 ∈ R_2(K_(1)(2k+1))` for all `k`, `q`.**
- **The odd parity of `(1,1)`** (`K_(1)(2k)`, target `s'_0 := y_j^{q−2}e_{2k−3}(y∖y_l)`):
  - the descent identity exists in the full space at `(2,9)`, `(3,9)`;
  - its closed form (D'_k) has NOT been extracted;
  - at `(3,9)` the row is exactly the odd sum of colons `+ (s'_0 family) +` two `q`-free elements of degrees 4, 5 (INFORME_7 §2.4).

**5. ANATOMY of the generic casillas (MEASURED) and the SANDWICH (PROVED).**
- **Sandwich.** Rows increase, so **`K_(m)(n−1) = R_1 ⊆ R_2 ⊆ R_{q−1} = K_(m+1)(n−1)`**.
  - The generic casilla is the lower neighbour plus `|W_(m)(n−1)| − |W_{(m,1)}(n−1)|` independent elements chosen inside the upper neighbour.
  - The same holds for every profile: rows sit between their lowering and raising neighbours.
- **Anatomy** — minimal generators of `R_2(K_(m)(n))` beyond `(e_odd) + box`:

| `(n,m)` | `dim S/R_2` | generator degrees | identical at `q = 27`? |
|---|---|---|---|
| `(4,1)` | 6 | 2, 3 | yes |
| `(4,2)` | 3 | 2 (×3, monomials) | yes |
| `(5,2)` | 12 | 2, 3 (×4) | yes |
| `(5,3)` | 4 | 2 (×6, monomials) | yes |
| `(6,3)` | 20 | 2, 3 (×10) | — |
| `(5,1)` | 84 | 4, **9 (×3) = q** | — |
| `(6,2)` | 200 | 4 (×5), **9 (×6) = q** | — |
| `(6,1)` | 380 | 4, 5, **10 (×5) = q+1** | — |

- **Reading:**
  - there is a **`q`-free core** of degree `≤ 5`;
  - there is an **interaction family** of degree `≈ q` (type `y^{q−2}·(…)`, like `s_0`), which appears only when `n − 1 − m ≥ 3`.
  - Examples of the core, with the first variable eliminated by `e_1`: at `(5,2)`, the complete homogeneous `h_2(w_1,w_2,w_3)` and `w_2w_3(w_2+w_3)`; at `(4,2)`, the monomials `w_1², w_1w_2, w_2²`.

**6. ROW DICTIONARY of a two-part casilla (MEASURED, 3/3, `q = 9`).** For `G := R_2(K_(m)(n))` (type `(m,1)` in `n−1` variables), the colengths of its rows `a = 0..8` are:
- `G` from `K_(1)(5)`: `24, 24, 6, 6, 6, 6, 6, 3, 3` — the types `(1),(1)`, then `(1,1)` and `(1,1,1)`×4, then `(2,1),(2,1)`.
- `G` from `K_(1)(6)`: `88, 88, 84, 24, 24, 24, 24, 12, 12`.
- `G` from `K_(2)(6)`: `84, 46, 12, 12, 12, 12, 12, 6, 4` — the types `(1,1)`, `(2)`, then `(2,1)` and `(2,1,1)`×4, then `(2,2)`, `(3,1)`.

Each sum equals the colength of `G`, and **row 1 of `G` equals `K_(m)(n−2)` AS AN IDEAL in all three.**

**RULE (measured):** for a profile with `ℓ` parts,
- the first `ℓ` rows are the LOWERING values, larger fibre first;
- then come `q − 2ℓ` middle rows: the value `0` and the new classes;
- the last `ℓ` rows are the RAISING values.

The lowering row of the new class returns EXACTLY to the one-part casilla.

## 4 · THE TARGET, EXACTLY
**(G1) — the generic row of the one-part line, all `m, n, q`.** Define explicitly **`K_{(m,1)}(n) := K_(m)(n) + C_m(n) + F_m(n)`**, where:
- `C_m(n)` is the `q`-free core (§3.5);
- `F_m(n)` is the interaction family, present when `n − m ≥ 3`.

Then:
- **gate:** its colength is `|W_{(m,1)}(n)|` (`q = 9`, `n ≤ 6`; `q = 27`, `n ≤ 4`);
- **prove `R_2(K_(m)(n+1)) ⊇ K_{(m,1)}(n)`:**
  - the core by a `q`-free certificate, i.e. membership of `z²·c` in `K_(m)(n+1) + (z³)`, handling the exponents `q−1` with Frobenius and Lucas as in (B_k);
  - the interaction by the descent.
- For `m ≥ 2` the Lemma H of §3.4 does not apply directly (the slices of `W_(m)` are not scalings of one set). Candidate engines:
  - (i) a Lemma H on the weighted cone `{(y,z) : y ∪ {z}^m closed}`;
  - (ii) since `K_(m)` is reached from `I^{(n+m)}` by `m` successive `+1` rows, lift the needed identity to `W_∅`, where §3.4 holds, and descend `m` times;
  - (iii) use the sandwich: the elements you need are inside `K_(m+1)`, whose membership is explicit.

**(G2) — the rows of every two-part (and longer) casilla, by the dictionary of §3.6.**
- Lowering rows go to known casillas: row 1 → `K_(m)`, measured equal.
- Raising rows: expect them free, as on the one-part line (check generator by generator).
- The middle block: value `0` (same type) and new classes (one more part). The new-class rows are the only ones expected to need interaction elements.

**THE WORK LIST for «D(4) FOR ALL q».** The profiles with `≥ 2` parts reachable from `(∅, n = 10)` along rows with non-empty fibre are exactly these 13, the same list for every `q ≥ 27` (`q = 9` lacks the last one):
**`(1,1)`, `(2,1)`, `(3,1)`, `(4,1)`, `(2,2)`, `(3,2)`, `(1,1,1)`, `(2,1,1)`, `(3,1,1)`, `(2,2,1)`, `(1,1,1,1)`, `(2,1,1,1)`, `(1,1,1,1,1)`.**

**THE UNIFORM CONSTRUCTION (the FULL prize).**
- Look for ONE formula `K_μ(n)` from the start, and test it on the 13 profiles at `q = 9`, `n ≤ 7`, against `|W_μ(n)|` (§1).
- Hints:
  - (a) `x^{q−1}` only sees «non-zero», so monomial layers cannot tell classes apart: the class structure lives in the cores and in the interaction elements;
  - (b) the sandwich bounds every casilla between explicit neighbours;
  - (c) scaling `y ↦ λy` fixes every homogeneous ideal, so `K_μ` must be symmetric in the classes.
- Prove the formula once, with `μ` as a letter: that is the closure.

## 5 · PROCESS
- **STEP 0 — Design (20 min, no M2 runs).** Write:
  - the dictionary for a general profile, with fibre sizes from §1;
  - your plan for the core certificate, for the engine of (G1) (i/ii/iii), and a first GUESS of a uniform `K_μ`.
- **STEP 1 — (G1) for all `m, n, q` (90 min).**
  - Extract the cores `C_m(n)` at `q = 9`, `n ≤ 7`, and check them at `q = 27`, `n ≤ 5`. Find their form in `m, n`. Prove the `q`-free certificate.
  - Interaction: the engine, then `F_m(n)`, including the odd parity of `(1,1)`.
  - If it closes: **«ONE-PART LINE CLOSED FOR ALL q»**.
- **STEP 2 — (G2) and the 13 profiles (90 min).** Data at `q = 9`, `n ≤ 7`.
  - If the 13 close: **«D(4) FOR ALL q»**.
- **STEP 3 — Uniform `K_μ` (45 min).**
  - If it is proved for all `μ`: **«CONJECTURE 1.2 CLOSED»**.
- **STEP 4 — Verdict (15 min).**

## 6 · DEAD ROUTES (do not retry)
- Separate counting lemmas for rows. The counts ARE the induction: include, do not count.
- The odd casilla with `j ≤ min(2,k−1)` (wrong from `k = 5`).
- «rows ⊆ fibres» as a formal consequence (false; three points).
- The sum of colons alone for generic rows (too small).
- Vanishing arguments that reach only `gr I`, not the casilla.
- Any ascent in `q` (a tower elevator): dead, with proof.
- Measuring cells as a substitute for a mechanism: cells are gates only.

## 7 · SUCCESS
- **Full:** a uniform `K_μ` with row inclusions for all reachable `μ` ⟹ **CONJECTURE 1.2 CLOSED.**
- **Row:** the 13 profiles ⟹ **D(4) FOR ALL q.**
- **Minimum:** (G1) for all `m, n, q` ⟹ the one-part line closed at every `q`.
- **Partial, declared as such:** the `q`-free cores in closed form; the engine for `m ≥ 2`; (D'_k) extracted.

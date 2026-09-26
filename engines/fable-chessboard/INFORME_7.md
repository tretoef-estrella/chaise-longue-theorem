# INFORME 7 — (L2): the last lemma
*(Fable, 2026-09-22. Mission: MISION_7.md.)*

## FIRST LINE
**(a)** **(L2) is NOT proved for all k.** Of the four row inclusions per level, for all q: **O-1 (row 1 of `K'_k`) is PROVED for k = 2, 3** (§0.2) and, for k ≥ 4, reduced to one monomial lemma (O1_k) (true at (4,3)); **E-+1 and O-+1 (the two `+1` rows) are PROVED to contain explicit ideals `Q_k`, `Q'_k` for all k** (§2.2), so they are reduced to two pure counting lemmas whose counts are EXACT at (2,9), (2,27), (3,9); **E-gen (the even generic row, i.e. (G-a_k)) is PROVED for all k to follow from ONE function identity on `W_0`**, the boundary lemma (B_k) (§1.6), via a new one-step descent (§1.1) and an exact closed-form identity (D_k) proved with k as a letter (§1.4–1.5), (B_k) being true at (2,9), (2,27), (2,81), (3,9); **O-gen** has the same descent (ideal gate and full-space function test true at (2,9), (2,27)/(3,9)) plus a q-free part, not closed. Nothing is proved for k ≥ 3 with q as a letter beyond these reductions.
**(b)** Missing, exactly: (B_k): «`N = [y_j=0]y_lR_l + [y_l=0]y_jR_j + [y_j=y_l=−1]R'_j` is a function of degree ≤ q+2k−5 on `W_0`» (equivalently `X_1−X_2−X_3 ∈ K'_k`, §1.6) — cell (3,9) true, (2,81) true; the counts `dim S_{2k}/Q_k ≤ |W_{+1}|`, `dim S_{2k−1}/Q'_k ≤ |W'_{+1}|` (§2.2) — exact at three cells; the even generic count `L + (s_0 family)` (INFORME_5 §2.7, exact at (3,9)); the odd identity (D'_k) and the k-general q-free part of the odd generic row (§2.4, exact at (3,9)); (O1_k) for k ≥ 4 (§2.1, true at (4,3)).
**(c)** **NO.** Neither the conjecture nor row k = 4 closes: every one of (DE_4), (DO_4) still depends on at least one of the lemmas in (b), none proved with q as a letter (§STEP 3).

## STEP 0
**STATE: CLOSED** (design written; no runs). **NEXT:** STEP 1, budget 60 min (start 11:28, writing from 12:15).
Budget written: 15 min (11:05–11:27; machine clock 11:27 at close). Read: MISION_7 (all), INFORME_6 §2 (all), INFORME_5 §2.7–2.13, INFORME_3 §2.1/§3.2 (rows), INFORME_2 §2.1–2.5 (Q^gen, odd rows, the «+» identity).

### 0.1 The four row inclusions at level k, exactly (what (L2) asks)
Even casilla `K_k = I^{(2k+1)} + M_k ⊂ S_{2k+1}`, `z = x_{2k}`, `x' = (x_0..x_{2k−1})`; odd casilla `K'_k = I^{(2k)} + (e_{2k}(x')) + M'_k ⊂ S_{2k}`, `z' = x_{2k−1}`. Rows `R_a := π_z(K_k : z^a)`, `R'_a := π_{z'}(K'_k : z'^a)`.
| # | inclusion | target colength | status before this turn |
|---|---|---|---|
| E-gen | `dim S_{2k}/R_2 ≤ |W_gen|` | `(2k)!·[t^{2k}] cosh·I_1²·I_0^{h−2}` | k = 1, 2 all q; (3,9) |
| E-+1 | `dim S_{2k}/R_{q−1} ≤ |W_{+1}|` | `(2k)!·[t^{2k}] cosh·I_2·I_0^{h−1}` | k = 1, 2 all q; (3,9) |
| O-1 | `dim S_{2k−1}/R'_1 ≤ N_{k−1}` | `|W'_0|` | k ≤ 3 all q (see 0.2) |
| O-gen | `dim S_{2k−1}/R'_2 ≤ |W'_gen|` | `(2k−1)!·[t^{2k−1}] sinh·I_1²·I_0^{h−2}` | k = 1, 2 all q; (3,9) |
| O-+1 | `dim S_{2k−1}/R'_{q−1} ≤ |W'_{+1}|` | `(2k−1)!·[t^{2k−1}] sinh·I_2·I_0^{h−1}` | k = 1, 2 all q; (3,9) |

### 0.2 Row 1 of the odd side is free for k ≤ 3 and reduces to one monomial family for k ≥ 4 — PROVED (no run)
`R'_1 ⊇ R'_0 = I^{(2k−1)}` (mission §2.6) and `R'_1 ∋ x_Cx_A^{q−1}` whenever `z'·x_Cx_A^{q−1} ∈ M'_k`, i.e. `x_{C∪{2k−1}}x_A^{q−1} ∈ M^{(j)}({0..2k−1})` with `j = |A| ≤ min(2, k−1)`. Hence **`R'_1 ⊇ I^{(2k−1)} + Σ_{j ≤ min(2,k−1)} M^{(j)}({0..2k−2})`**, which for `k ≤ 3` is exactly `K_{k−1}` (`M_{k−1} = Σ_{j ≤ k−1} M^{(j)}`), of colength `≤ N_{k−1}` by `(DE_{k−1})` (k−1 ≤ 2: mission §2.9 / INFORME_6 §2.6, all q). **So O-1 is PROVED for k = 2, 3 and all q.** For `k ≥ 4` the same argument gives `R'_1 ⊇ K_{k−1}` as soon as `z'·x_c·x_A^{q−1} ∈ K'_k` for `|A| = j ≥ 3` (the `M^{(j)}` monomials that `M'_k` omits); this is the only gap of O-1 at k ≥ 4 (checked at k = 4 only through `q = 3` cells, where it is vacuous). Recorded as **lemma (O1_k)**: `x_{C}x_A^{q−1} ∈ K'_k` for `2k−1 ∈ C`, `|A| = |B| = j ≥ 3`.

### 0.3 The engine, restated in the form I will use (Lemma H as a «descent»)
Let `Row_1^+ := {t ∈ S_{2k} : z·t ∈ K_k + (z³)}` (z-free elements). Then `Row_1^+ ⊆ R_1`, and `Row_1^+ ⊇ φ(K_k) + (e_{2k}(x')) + (x_Cx_A^{q−1} : 2k ∈ C)` where `φ: z ↦ −e_1(x')` (elimination, INFORME_6 §2.1), so `φ(K_k) = (P'_3, P'_5, …, x'^q, e_1(x')^q) + φ(M_k)`, `P'_j := e_j(x') − e_1(x')e_{j−1}(x')`.
> **Descent form of Lemma H (even side, needs D'(k)).** If `f ∈ I(W_0) ⊂ F_q[x']`, `f = t + s + r` (`t` top, degree d; `s` degree d−1; `deg r ≤ d−2`) and **`t ∈ Row_1^+`**, then **`s ∈ R_2`** (the generic row). Proof: `z t + z² s ∈ I^{(2k+1)} + (z³)` (Lemma H), `z t ∈ K_k + (z³)`, so `z² s ∈ K_k + (z³)`, i.e. `s ∈ π_z(K_k : z²)`. ∎
So an element `s_0` is put into the generic row by ONE function identity on `W_0` of the form `s_0 = −t − r` with `t ∈ Row_1^+` of degree `deg s_0 + 1`. At k = 2 the proof of G-a (INFORME_6 §2.5) is a chain of such descents (via the colon certificate). **Plan: find the k-general descent directly for the target `s_0 = x_l²x_j^{q−2}e_{2k−4}(x'∖x_l)` — or for the equivalent `x_j^{q−2}e_{2k−2}(x'∖x_l)` (INFORME_5 §2.8) — using the structure of `W_0`.**

### 0.4 Structure of W_0 and of the identities, uniform in k
`W_0 = ⋃_{i≠j'} {y_i = −1, y_{j'} = 0} × Z_{2k−2}(rest)`. On each piece the generating polynomial is `E(T) = Π(T + y_m) = (T−1)·T·Ev(T)` with `Ev` even of degree `2k−2`; hence on `W_0`: **`e_{2m+1}(y) = −e_{2m}(y)` for all m, `e_{2k}(y) = 0`**, and for a subset `V = y∖{y_l}`: `E_V(T) = E(T)/(T + y_l)`. For a fixed coordinate `y_j`, `y_j^{q−2}` is `0, −1, 1/c` on the pieces `y_j = 0, −1, c` (c in the closed rest). A function identity on `W_0` that is symmetric in the «passive» coordinates `P = x'∖{x_l, x_j}` reduces to finitely many k-INDEPENDENT cases (which of the values `−1, 0` fall in P) in the coefficients of `Ev` — this is the uniformity in k that mission §3 asks for. The target `e_{2k−4}(V)` is the coefficient of `T²` in `E_V`, a TOP coefficient; the relations `e_1 = −1`, `e_3 = −e_2` are BOTTOM coefficients. For `k ≥ 4` top and bottom coefficients are independent; k = 2, 3 are degenerate (`ε_2` is both). So the k-general certificate must be read off with this in mind; the (3,9) cell is the last degenerate one.

### 0.5 Plan of STEP 1 (even generic row, all k)
1. Verify the descent form at k = 2 against INFORME_6 (no run) and write the target as a function on `W_0` piece by piece.
2. Find the k-general descent `f ∈ I(W_0)` for `s_0 = x_j^{q−2}e_{2k−2}(V)` (V = x'∖x_l, j ∈ V) — candidates come from the identities `e_{2k−1}(V) = 0`-type relations on the pieces (since `V` misses one coordinate). Gate each candidate on all points of `W_0` at (2,9), (3,9) (python, allowed) and as memberships in M2 at (2,9), (2,27), (3,9).
3. If (G-a_k) falls: the count of `K'_k + π_z(M_k : z²) + (G-a_k family)` — by rows one level down (the tablero repeats), or via `Q^gen` (INFORME_2 §2.1: `gr I(W_gen) ⊆ Q^gen`, and `Q^gen = R_2` measured).
Runs planned: python point checks (seconds); M2 memberships at (2,9), (2,27), (3,9) in ≤ 7 variables, each estimated < 2 min, < 300 MB (like `ga7.m2`: 71 s).

## STEP 1
**STATE: NOT CONCLUDED** — (G-a_k), hence the even generic row, is reduced for ALL k and q to ONE explicit function identity on `W_0` (the «boundary lemma» (B_k) of 1.6), which is PROVED exact on all points at (2,9), (2,27), (3,9) but not yet with k as a letter. **NEXT:** STEP 2, budget 60 min (12:16–13:16; writing from 13:04).
Budget written: 60 min (11:28–12:28; writing from 12:15; closed 12:16 by the machine clock). Runs: `ga8.m2` (75 s, 250 MB, EXIT 0: the 14 low generators of the (3,9) colon and the certificate; not used further), `gateH.m2` (1 s), `excess.m2` (5 s), python `fq.py`, `desc2*.py`, `desc3*.py`, `blocks.py`, `resid*.py`, `formula*.py`, `nterm.py` (all ≤ 10 s). No kills; `pgrep` after each M2 run: none running.

### 1.1 The one-step descent for the even generic row — the k-general shape (PROVED given the function identity of 1.3)
Notation: `x' = (y_0..y_{2k−1})`, `W_0 = {y : y ∪ {0,1} closed}`, `Z = Z(y)` the set of zero coordinates (`|Z|` odd). Fix `l ≠ j`, `V := x'∖{y_l}`, `P := x'∖{y_j, y_l}` (2k−2 «passive» coordinates), `u := Π_P = e_{2k−2}(P)`, `E' := e_{2k−3}(P)`, and the **row-1 monomials `τ_{bb'} := y_b^{q−1}·x_{x'∖{b,b'}}`** (`z·τ_{bb'} ∈ M_k`: `C = x'∖{b,b'} ∪ {z}`, `A = {b}`, `B = {b'}`; so `τ_{bb'} ∈ Row_1^+`).
Target (INFORME_5 §2.8 form): **`s_0 := y_j^{q−2}·e_{2k−2}(V)`**, degree `q+2k−4`.
> **Descent lemma.** If, as functions on `W_0`, **`s_0 + τ_{jl} = r` with `deg r ≤ q+2k−5`** (identity (D_k)), then `f := τ_{jl} + s_0 − r ∈ I(W_0)` has top form `τ_{jl}`, second form `s_0`, and Lemma H (mission §2.11, even side, given `D'(k)`) gives `z·τ_{jl} + z²·s_0 ∈ I^{(2k+1)} + (z³)`; since `z·τ_{jl} ∈ M_k`, **`z²·s_0 ∈ K_k + (z³)`, i.e. `s_0 ∈ R_2`**, which is (IL_k) and hence (G-a_k) (INFORME_5 §2.8). ∎
So (G-a_k) for all k, q reduces to ONE function identity (D_k) on `W_0`.

### 1.2 Values of the two sides on `W_0` — PROVED (case analysis, all k)
`s_0 ≠ 0` needs `y_j ≠ 0` and `|Z ∩ V| ≤ 1`; `τ_{jl} = [Z = {l}]·u`. Cases: **`Z = {l}`:** `e_{2k−2}(V) = [T^1]((T−1)·Ev(T)) = Π_rest = −Π_V`, so `s_0 = −Π_V/y_j = −u = −τ_{jl}`; **`Z = {m}`, `m ∈ P`:** `s_0 = Π_{V∖m}/y_j = Π_{P∖m}`, `τ_{jl} = 0`; otherwise both vanish. Hence
> **`g := s_0 + τ_{jl} = Σ_{m∈P} [Z = {m}]·Π_{P∖m} = e_{2k−3}(P)·y_j^{q−1}y_l^{q−1}`** (exact on `W_0`).
(Here `Ev(T) = Π_{c∈rest}(T + c)` is the even polynomial of the closed multiset `rest := y ∖ {−1, 0}`, so on `W_0`: `e_{2r}(y) = ε_{2r}(rest)`, `e_{2r+1}(y) = −e_{2r}(y)`.)

### 1.3 Identity (D_k) — MEASURED at (2,9), (2,27), (3,9); closed form in progress
- `desc2.py`: at (2,9), (2,27), `s_0 ≡ −τ_{jl}` mod functions of degree `≤ q−1` on `W_0` (i.e. (D_2) holds; the other `τ_{jb}` do not work alone). `desc3n.py`: at (3,9), `g` lies in the span of {polynomials in `y_j, y_l, e_λ(P)` of degree ≤ 2k−1} ∪ {`J_a(ℓ)·(degree ≤ 2k−3)`, `ℓ ∈ {y_j, y_l, y_j±y_l}`, `a = ±1`}, where **`J_a(x) := Σ_{i=0}^{q−2}(x/a)^i = [x=0] − [x=a]`** (degree `q−2`); no `τ_{bb'}` other than `τ_{jl}` is needed. So **(D_3) holds at q = 9**, with `r` of the form (indicator of degree q−2) × (degree ≤ 2k−3) + (degree ≤ 2k−1).
- At k = 2 the identity is the same at q = 9 and q = 27 (`desc3.py`): `g = (1+y_j+y_l)(1 + J_1(y_j+y_l)) − J_1(y_j)(1+y_j) − J_1(y_l)(1+y_l) − J_{−1}(y_j)y_l − J_{−1}(y_l)y_j`.
- **Ideal-side gate (`gateH.m2`, (2,9), (2,27), (3,9)):** `z·τ_{jl} + z²·s_0 ∈ I^{(2k+1)} + (z³)` is TRUE in all three cells, while `z²s_0` and `z·τ_{jl}` alone are NOT: exactly Lemma H's conclusion for (D_k).
- `blocks.py`: the natural pieces of `g` (`[y_j=0]E'`, `[Z={l}]R_j`, the three-zero piece `h`, …) are individually NOT of low degree at (2,9), (3,9); only their combination is. Reduction (PROVED, all k, on `W_0`): with `Σ(P) := Π_{m∈P}(1+y_m)`, `R_b := Σ_{i=1}^{k−1} y_b^{2i−2}e_{2k−2−2i}(y)` (so that `e_{2k−2}(y) = Ω_b − y_b²R_b`, `Ω_b := Σ_r e_{2r}(y)y_b^{2k−2−2r} = Ev(y_b)`), `h := [Z={j,l,m}]Π_{P∖m}`: **`g = E' + u + (y_j^{q−2} + y_l^{q−2})u − h`** and `[Z={l}]·u/y_j = [Z={l}](R_j − Σ(P))`. (D_k) is therefore equivalent to a low-degree representative of `φ − h := [Z={l}](R_j − Σ(P)) + [Z={j}](R_l − Σ(P)) − [Z={j,l,m}]E'`.

### 1.4 The identity (D_k) in closed form — PROVED EXACT on all points of W_0 at (2,9), (3,9) (`formula2.py`: 0 failures); proof by cases in 1.5
Notation (all polynomials in `y`, homogeneous of the stated degree): `ε_{2r} := e_{2r}(y)`; on `W_0`, `ε_{2r} = e_{2r}(rest)` where `rest := y∖{−1,0}` is closed of size `2k−2`, `Ev(T) := Π_{c∈rest}(T+c) = Σ_r ε_{2k−2−2r}T^{2r}`, `ev(s) := Ev(√s)`.
- `R_b := Σ_{i=1}^{k−1} y_b^{2i−2}ε_{2k−2−2i} = ev[0, y_b²]` (divided difference; degree 2k−4), so `ε_{2k−2} = Ev(y_b) − y_b²R_b`;
- `R'_b := Σ_{i=1}^{k−1} i·y_b^{2i−2}ε_{2k−2−2i} = ev'(y_b²)` (degree 2k−4);
- `D := ev[y_j², y_l²] = Σ_{i≥1} ε_{2k−2−2i}·h_{i−1}(y_j², y_l²)` (complete homogeneous; degree 2k−4);
- `Σ(P) := Π_{m∈P}(1+y_m) = Σ_r e_r(P)` (degree 2k−2), `u = e_{2k−2}(P)`, `E' = e_{2k−3}(P)`.
> **(D_k), exact on `W_0`:**
> `g = s_0 + τ_{jl} = E' + u + D − Σ(P) − [y_j+y_l=0]·R'_j + [y_j=y_l]·(1−y_j)·R'_j − Σ_{a=±1} ( [y_j=a]·y_l + [y_l=a]·y_j )·D`,
> where `[·]` are the true indicator functions.
Structure of the proof (1.5): `g = Σ_{m∈P}[Z={m}]Π_{P∖m}`; on `Z={m}` one has `Π_{P∖m} = −ε_{2k−2}/(y_jy_l) = D − Ω_j/(y_jy_l) + y_j(Ω_{jl} − D)/y_l`-type expansions, and the polynomial identity `R_j + R_l − ε_{2k−4} + y_j²y_l²·ev[0,0,y_j²,y_l²] = ev[y_j², y_l²] = D` (Newton's divided differences) collapses the generic value to `D − Σ(P)`; the remaining terms are exactly the coincidences `y_j = −1` (designated), `y_l = −1`, `y_l = −y_j`, `y_j = y_l = −1`, `(y_j,y_l) = (±1,∓1)`, each with the value computed from `Ev` (e.g. on `y_l = −y_j = −c`: `D = ev'(c²) = R'_j`; on `y_j = −1, y_l = c`: `D − Σ(P) = ω/(1−c²) − ω/(1+c) = −c·D`, `ω := Ev(1)`).
`resid.py` / `formula.py` document the successive residuals: the main term `D − Σ(P)` is exact off the coincidence pieces; the residual table at (3,9) is exactly the list of coincidence pieces.

### 1.5 Proof of (D_k) — case analysis (PROVED with k as a letter, given the values of 1.2)
Fix a point of `W_0`; write `y∖{y_m}` or `y∖{y_l}`, … as `{−1} ∪ rest` with `rest` closed of size 2k−2 and `Ev(T) = Π_{c∈rest}(T+c) = ev(T²)`, so `ε_{2r} = e_{2r}(y) = [T^{2k−2−2r}]Ev` (mission §1 fibres; INFORME_6 §2.4 style). Then `R_b = ev[0,y_b²]`, `R'_b = ev'(y_b²)`, `D = ev[y_j²,y_l²]`, `Ω_b := Ev(y_b) = ε_{2k−2} + y_b²R_b`, and `Ω_b = 0 ⟺ −y_b ∈ rest`.
**(i) Pieces `Z ⊂ P`** (`y_j,y_l ≠ 0`; `|Z| = 1` or ≥ 3): `g = [|Z|=1]·Π_{P∖m}`, `E' = [|Z|=1]Π_{P∖m}` too (|Z∩P| ≤ 1 needed), `u = 0`, and `Π_{P∖m} = −ε_{2k−2}/(y_jy_l)`. Newton's identities give the polynomial identity `R_j + R_l − ε_{2k−4} + y_j²y_l²·ev[0,0,y_j²,y_l²] = ev[y_j²,y_l²] = D`; hence the claim on these pieces is `D − Σ(P) = (indicator terms)`, i.e. the values: generic (`y_j,y_l ∈ rest`, `y_l ≠ ±y_j`): `Ω_j = Ω_l = 0 ⇒ D = 0`, `Σ(P) = 0` (the −1 lies in P) ✓; `y_l = −y_j = −c`: `D = ev'(c²) = R'_j`, `Σ(P) = 0` ⇒ the term `−[y_j+y_l=0]R'_j` ✓; `y_j = −1` designated, `y_l = c ∉ {0,±1}`: `D = ω/(1−c²)`, `Σ(P) = ω/(1+c)` (`ω = Ev(1)`), difference `= −c·D` ⇒ the term `−[y_j=−1]y_lD` ✓ (and symmetrically); `y_j = y_l = −1`: `D = ev'(1)`, `Σ(P) = Π_{rest∖{−1}}(1+c) = −ev'(1)` ⇒ `D − Σ(P) = −ev'(1)`, matched by `[y_j=y_l](1−y_j)R'_j + 2·D = (2−2)…`: explicitly `−ev'(1)·(−1)·… ` — the sum of the three active terms `[y_j=y_l](1+1)R'_j − (−1)D − (−1)D = −R'_j + 2D = R'_j = ev'(1)` and `D − Σ(P) + (that) = −ev'(1) + ev'(1) = 0 = g` ✓; `(y_j,y_l) = (−1,1)`: `D = ev'(1)`, `Σ(P) = 0`, active terms `−R'_j − (1)D − (−1)·…`: `−[y_j+y_l=0]R'_j − [y_j=−1]·y_l·D − [y_l=1]·y_j·D = −R'_j − D + D = −R'_j`, total `D − R'_j = 0` ✓ (symmetric for `(1,−1)`); `y_j = y_l = c` (double pair): `ev'(c²) = 0` (double root), `D = 0`, all terms vanish ✓; `y_j = 1` alone or `y_l = 1` alone: `D = 0 = Σ(P)`, and `[y_j=1]y_lD = 0` ✓.
**(ii) `Z = {l}`:** `g = 0`, `E' = −(1+y_j)R_j`, `u = y_jR_j + Σ(P)`, `D = ev[y_j²,0] = R_j`, so `E' + u + D − Σ(P) = 0`; the indicator terms vanish (`y_l = 0` kills `[y_j+y_l=0]`, `[y_j=y_l]`, `[y_j=a]y_l`, and `[y_l=a]` is off) ✓. **`Z = {j}`** symmetric ✓.
**(iii) `Z ⊇ {j,l}`:** `E' = [Z={j,l,m}]Π_{P∖m} = −[Z={j,l,m}]ε_{2k−4}`, `u = 0`, `D = ε_{2k−4}`, `Σ(P) = 0`, `−[+]R'_j + [=](1−0)R'_j = 0`; on `Z = {j,l,m}`: `−ε_{2k−4} + ε_{2k−4} = 0` ✓; on 5 or more zeros `ε_{2k−4} = 0` ✓.
**(iv) `Z ∋ j`, `l ∉ Z`, `|Z| ≥ 3`** (and symmetric): `E' = 0`, `u = 0`, `D = R_l = Ω_l/y_l²` (`ε_{2k−2} = 0`), `Σ(P) = [y_l=−1]·Ev(1)`; `Ω_l ≠ 0` iff `y_l = −1` designated, where `D = Ev(1) = Σ(P)`; indicator terms: `[y_j=y_l]` off, `[y_j+y_l=0]` off, `[y_l=−1]y_jD = 0`, `[y_j=a]` off ⇒ total `0` ✓.
Every piece type of `W_0` is one of (i)–(iv); the exhaustive machine check at (2,9), (3,9) (`formula2.py`, 0 failures) confirms the bookkeeping. ∎

### 1.6 From (D_k) to the row: the polynomial realisation and the ONE remaining lemma
Realise the indicators by `[x=a] := 1 − (x−a)^{q−1}` (degree q−1). Then `f := τ_{jl} + s_0 − r_poly ∈ I(W_0)`, top form `τ_{jl} ∈ Row_1^+`, and its degree-`(q+2k−4)` form is `s_0 − (X_1 − X_2 − X_3)` with (using `(y_j−y_l)^{q−1} = h_{q−1}(y_j,y_l)` in char 3, Lucas)
> `X_1 := h_{q−1}(y_j,y_l)·y_j·R'_j`, `X_2 := y_j^{q−1}·y_l·D`, `X_3 := y_l^{q−1}·y_j·D`.
Lemma H ⇒ `s_0 − (X_1−X_2−X_3) ∈ R_2`. Hence **(G-a_k) ⟸ `X_1 − X_2 − X_3 ∈ R_2`**. MEASURED (`excess.m2`, (2,9), (2,27), (3,9)): `X_1, X_2, X_3` are individually NOT in `R_2`, but **`X_1 − X_2 − X_3 ∈ L = K'_k + π_z(M_k : z²)` (the sum of colons, ⊆ R_2 for all k)** in all three cells. Equivalently (1.3, `nterm.py`), as functions on `W_0`, `X_1 − X_2 − X_3 ≡ N + y_jR'_j − (y_j+y_l)D` with the boundary function
> **`N := [y_j=0]·y_lR_l + [y_l=0]·y_jR_j + [y_j=y_l=−1]·R'_j`**,
> and **(B_k): `N` has a representative of degree `≤ q+2k−5` on `W_0`** (equivalently `X_1−X_2−X_3 ∈ gr I(W_0) = K'_k`). MEASURED at (2,9), (2,27), (3,9) (`nterm.py`: `N` lies in the span of {polys of degree ≤ 2k−1 in `y_j,y_l,e(P)`} ∪ {`J_a(ℓ)`·(degree ≤ 2k−3)}, the k = 2 representative being `N ≡ −(y_j+y_l)(1 + J_{−1}(y_j) + J_{−1}(y_l) − J_{−1}(y_j+y_l))`, identical at q = 9, 27).
**Exact remaining lemma for the even generic row, all k:** (B_k), or the ideal form `X_1 − X_2 − X_3 ∈ L`. Cell to check it: (3,27) is not allowed in full; (2,81) in 4 variables is allowed (membership in ≤ 5 variables) — not run (time).
**What is PROVED with k as a letter in STEP 1:** the descent lemma (1.1); the values (1.2); the identity (D_k) (1.4–1.5); the reduction (G-a_k) ⟸ (B_k) (1.6). What is NOT: (B_k); and the count (colength of `L + (s_0 family) ≤ |W_gen|`), not attempted (rule 4: budget).

## STEP 2
**STATE: NOT CONCLUDED** — the four remaining row inclusions are each reduced, for all k, to explicit lemmas (2.5), none proved with k as a letter; (L2) is NOT proved for all k, so the conjecture is NOT closed. **NEXT:** STEP 3 (row k = 4, specialisation only; 30 min, 12:26–12:56).
Budget written: 60 min (12:16–13:16; writing from 13:04; closed 12:26 by the machine clock — all runs of this step took ≤ 3 s). Runs: `o1k4.m2` ((4,3), 1 s), `gateHodd.m2` (1 s), `plus1.m2` (1 s), `q81.m2` (3 s), `oddrow.m2` (1 s), `oddrow2.m2` (1 s), python `odddesc*.py`, `oddfull.py`; no kills; `pgrep` after each: none running.

### 2.1 Odd row 1 — PROVED for k ≤ 3, and its only gap for k ≥ 4 is TRUE at (4,3)
§0.2: `R'_1 ⊇ I^{(2k−1)} + Σ_{j≤min(2,k−1)}M^{(j)}({0..2k−2})`, which equals `K_{k−1}` for k ≤ 3, so **O-1 holds for k = 2, 3 and all q** (colength ≤ N_{k−1} by INFORME_6 §2.6 / mission §2.9). For k ≥ 4 the gap is lemma **(O1_k): `x_{C∪{z'}}·x_A^{q−1} ∈ K'_k` for `|A| = |B| = j ≥ 3`**. `o1k4.m2` (cell (4,3), allowed; `K'_4` has 490 generators, colength 1016): **all 140 monomials `z'·x_C·x_A²` with `|A| = |B| = 3` lie in `K'_4`** (they are not in `M'_4`, so they come from `I^{(8)} + (e_8) + M'_4` by identities). Evidence, not a proof with k as a letter.

### 2.2 THE TWO `+1` ROWS REDUCE TO A COUNT — inclusion PROVED for all k, count EXACT at (2,9), (2,27), (3,9)
Even side: `z^{q−1}·x_C·x_{A'}^{q−1} ∈ M_k` (take `A = A' ∪ {z}`, `|A| = |B| = j`, `|C| = 2k+1−2j`), `z·e_{2k}(x') = e_{2k+1} ∈ I^{(2k+1)}`, so for all k, q:
> **`Q_k := (e_1, e_3, …)(x') + box_q + (e_{2k}(x')) + (x_C·x_{A'}^{q−1} : A' ⊔ B ⊔ C = x', |A'| = j−1, |B| = j, 1 ≤ j ≤ k) ⊆ R_{q−1}`.**
Odd side (`M'_k` has `j ≤ min(2,k−1)`; `z'·e_{2k−1}(x') = e_{2k}(x',z') ∈ K'_k`):
> **`Q'_k := (e_1, e_3, …)(x') + box_q + (e_{2k−1}(x')) + (x_C·x_{A'}^{q−1} : |A'| = j−1, |B| = j, 1 ≤ j ≤ min(2,k−1)) ⊆ R'_{q−1}`.**
MEASURED (`plus1.m2`): `dim S_{2k}/Q_k = 46, 154, 2340` and `dim S_{2k−1}/Q'_k = 3, 3, 210` at (2,9), (2,27), (3,9) — **exactly `|W_{+1}|` and `|W'_{+1}|`** (fibre formula of mission §1, recomputed: 46, 154, 2340; 3, 3, 210). Hence **E-+1 and O-+1 for all k are equivalent to the counting lemmas `dim S_{2k}/Q_k ≤ |W_{+1}|`, `dim S_{2k−1}/Q'_k ≤ |W'_{+1}|`** (no interaction element is needed in the `+1` rows: they are «free» in the sense of INFORME_3 §3.2, on both sides). The count is not proved with k as a letter this turn (a row-by-row count of `Q_k` along `y_{2k−1}` produces fibres of new type `{y : y ∪ {v,1,1} closed}`, i.e. the tablero of the multiset `S = {v,1,1}`, one level down).

### 2.3 Odd generic row — the descent exists on the ideal side; the function identity is not yet located
Odd Lemma H (`W'_0 = V_1^{(k−1)}`, uses `D(k−1)`) and `τ'_{jl} := y_j^{q−1}·x_{x'∖{j,l}} ∈ Row'^+_1` (`z'·τ'_{jl} ∈ M^{(1)}({0..2k−1}) ⊆ M'_k`). Target `s'_0 := y_j^{q−2}·e_{2k−3}(x'∖y_l)` (at (3,9) these are the interaction generators `y_4^{q−2}e_3(y_1..y_4)`, `y_3^{q−2}e_3(y_1..y_4)` of INFORME_5 §2.12). **`gateHodd.m2`: `z'·τ'_{jl} + z'²·s'_0 ∈ I^{(2k)} + (z'³)` at (2,9), (2,27), (3,9), neither term alone** — the odd analogue of 1.3. But the function `s'_0 + τ'_{jl}` is NOT of degree `≤ q+2k−6` on `W'_0` in the ansatz of STEP 1 (`odddesc.py`, `odddesc2.py`, even with all `τ'_{bb'}` and full indicators): on the odd side `W'_0` has no forced zero, `Π_{x'} = e_{2k−1}(x') ∈ Row'^+_1` does not vanish on `W'_0`, and the descent must use it (tested next).

**Full-space test (`oddfull.py`, all monomials of degree ≤ q+2k−6 on `W'_0`):** `s'_0 + τ'_{jl} ∈ F_{q+2k−6}(W'_0)` at **(2,9)** (dim 21 of 24) **and (3,9)** (dim 436 of 855), while `s'_0` alone is not. So the **odd descent identity (D'_k) exists** at both cells (the structured ansatz of STEP 1 was too small on the odd side); by the odd Lemma H and `z'·τ'_{jl} ∈ M'_k`, **`s'_0 ∈ R'_2`** follows at those cells — consistent with `gateHodd.m2`. Its closed form is not extracted this turn.
**q = 81 gates (`q81.m2`, ≤ 5 variables, allowed):** at (2,81) `X_1 − X_2 − X_3 ∈ L` (`dim S_4/L = 952 = N'_2(81)`) and `z·τ_{jl} + z²·s_0 ∈ I^{(5)} + (z³)`: the remaining lemma (B_k)/its ideal form and the descent are q-uniform at k = 2 through q = 81.

### 2.4 Odd generic row at (3,9) and (2,q): EXACT decomposition — MEASURED
`oddrow.m2`, `oddrow2.m2`: with `L' := π_{z'}(I^{(2k)} : z') + π_{z'}(M'_k : z'^2)` (the odd sum of colons) and the **odd descent family `fam' := (y_j^{q−2}·e_{2k−3}(x'∖y_l) : j ≠ l)`**:
| cell | `R'_2` | `L'` | `L' + fam'` | `L' + fam' + (q-free part)` |
|---|---|---|---|---|
| (2,9) | 6 | 24 | 21 | 6 |
| (2,27) | 6 | 78 | 75 | 6 |
| (3,9) | **380** | 855 | 690 | **380** |
where the **q-free part** is: k = 2: `h_2(y_1,y_2) = y_1²+y_1y_2+y_2²`, `y_2³` (INFORME_2 §2.2, proved for all q from the q-free colon `(P'_3, ε_1ε_3, ε_1³) : ε_1²`); k = 3: the quartic `y_1²y_3² + y_1y_2y_3² + y_2²y_3² + y_1³y_3 + y_2³y_3 + y_1²y_3y_4 + y_1y_2y_3y_4 + y_2²y_3y_4 − y_1y_3²y_4 − y_2y_3²y_4 + y_3³y_4 + y_1²y_4² + y_1y_2y_4² + y_2²y_4² − y_1y_3y_4² − y_2y_3y_4² − y_3²y_4² + y_1y_4³ + y_2y_4³ + y_3y_4³` and the quintic `y_4³·(h_2(y_1,y_2,y_3) + y_4·e_1(y_1,y_2,y_3))` (INFORME_5 §2.12). **So at (3,9): `R'_2 = L' + fam' + (quartic, quintic)` exactly**; the other degree-(q+1) generators of INFORME_5 §2.12 (`y_b³y_j^{q−2}`, `y_j^{q−2}[y_by_c(y_b+y_c) + y_jh_2(y_b,y_c)]`) lie in this sum. Pattern for general k: `fam'` (from the odd descent), plus a q-free part of degrees `2k−2, 2k−1` coming from the q-free colon `(J̄'_1 : ε_1²)` of INFORME_3's odd Lemma E (q-free ⇒ valid for all q once computed at level k, as INFORME_2 §2.2 did for k = 2), plus the count.

### 2.5 Summary of STEP 2: what each row inclusion of (L2) now rests on, for all k
| row | reduced to | status of the reduction | cells |
|---|---|---|---|
| E-gen | (B_k) [boundary lemma, 1.6] + count `dim S_{2k}/(L + s_0-family) ≤ |W_gen|` | descent + identity (D_k) PROVED all k; (B_k) measured; count measured (INFORME_5 §2.7) | (2,9),(2,27),(2,81)(B only),(3,9) |
| E-+1 | count `dim S_{2k}/Q_k ≤ |W_{+1}|` | `Q_k ⊆ R_{q−1}` PROVED all k; count measured EXACT | (2,9),(2,27),(3,9) |
| O-1 | (O1_k) for k ≥ 4 | PROVED for k ≤ 3; (O1_4) true at q = 3 | (4,3) |
| O-gen | odd identity (D'_k) + q-free part + count | descent exists (full space) at (2,9),(3,9); q-free part k-general form unknown | (2,9),(2,27),(3,9) |
| O-+1 | count `dim S_{2k−1}/Q'_k ≤ |W'_{+1}|` | `Q'_k ⊆ R'_{q−1}` PROVED all k; count measured EXACT | (2,9),(2,27),(3,9) |
**(L2) for all k: NOT PROVED. CONJECTURE 1.2: NOT CLOSED.**

## STEP 3
**STATE: EXHAUSTED** (specialisation only; no run is allowed at k = 4, q ≥ 9). **NEXT:** STEP 4.
Budget written: 30 min (12:26–12:56); used 5 min (no runs). Specialising 2.5 to k = 4 (chain: `D'(4)` needs `(DO_4)`; `D(4)` needs `D'(4) + (DE_4)`; `(P_4)` is proved, mission §2.5):
- **(DE_4)** ⟸ [E-gen(4): (B_4) + `dim S_8/(L + (y_j^{q−2}e_6(x'∖y_l)))_{k=4} ≤ |W_gen|` (204456 at q = 9)] ∧ [E-+1(4): `dim S_8/Q_4 ≤ |W_{+1}|` (130984 at q = 9)]. Row 0 and row 1 are free (mission §2.6–2.7, given `D(3)`, `(DO_4)`).
- **(DO_4)** ⟸ [O-1(4): lemma (O1_4), i.e. `z'·x_C·x_A^{q−1} ∈ K'_4` for `|A| = |B| = 3` — TRUE at q = 3 (2.1), open for q ≥ 9] ∧ [O-gen(4): odd descent family + q-free part + count `≤ 22302` at q = 9] ∧ [O-+1(4): `dim S_7/Q'_4 ≤ |W'_{+1}|` (13496 at q = 9)]; row 1 target 37947 = `N_3`.
None of these is proved for all q; none can be measured within the rules (k = 4 with q ≥ 9 is forbidden). **«D(4) FOR ALL q»: NOT reached.** The exact missing pieces at k = 4 are the five lemmas above; the two `+1` counts and the two generic counts are pure counts of explicit ideals in 8 and 7 variables; (B_4) is a function identity on `W_0 ⊂ F_q^8`; (O1_4) is a membership in `K'_4`.

## STEP 4 — VERDICT
**STATE: CLOSED** (verdict written; disk re-read before writing: the sections above are as saved).
Applying the chain (mission §2.3, §2.5) to what is proved: nothing new is added to the list of proved levels (`D(1), D'(1), D'(2), D(2), D(3)` all q; all k at q = 3). (L2) is not proved for any k ≥ 3; `D(3)` is known externally (the Hamaca), but `D'(4)` and `D(4)` are not: **row k = 4 is not closed; the conjecture is not closed.**
What this turn PROVED with k and q as letters (all with proofs in this report): (i) the descent lemma (1.1): a function identity on the row-1 fibre `W_0` of the form `t + s + r ∈ I(W_0)` with `t` a row-1 monomial `τ_{bb'}` puts `s` in the generic row; (ii) the exact identity (D_k) for the even target (1.4–1.5), which reduces (G-a_k) — the whole even generic row's interaction family — to the single boundary lemma (B_k); (iii) both `+1` rows contain the explicit ideals `Q_k`, `Q'_k` (2.2), so E-+1 and O-+1 are pure counting lemmas; (iv) O-1 for k ≤ 3 (0.2). MEASURED: the counts of `Q_k`, `Q'_k` are exactly the fibre sizes at (2,9), (2,27), (3,9); (B_k) at (2,9), (2,27), (2,81), (3,9); the odd descent at (2,9), (3,9); the exact decomposition of the odd generic row at (3,9); (O1_4) at (4,3).
**Answer to the mission's minimum («D(4) for all q»): NO.**

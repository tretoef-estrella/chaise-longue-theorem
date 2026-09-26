# INFORME_5 — MISSION 5 «TWO LEMMAS»
*(Fable, 2026-09-22. Folder: ~/Desktop/FABLE_TABLERO. Machine: /opt/homebrew/bin/M2.)*

## FIRST LINE

**(a)** (L1) is NOT proved for all q (still q ∈ {3, 9, 27}); (L2) is NOT proved for all k (still k ≤ 2 odd, k ≤ 1 even, all q). Proved this turn, with k as a letter: the reduction of the even generic row's interaction element to the **G-a family** `z²·x_l²·x_j^{q−2}·e_{2k−4}(x'∖x_l) ∈ K_k + (z³)` (its k = 2 member is G-a) — STEP 2 §2.8; and three exact reformulations of (L1), the last one a single congruence modulo a monomial ideal for G-invariant unknowns (equivalent to (L1) at q = 9) — STEP 1 §1.1. Measured: rows of the explicit casillas = top-form ideals of the fibres, every row at (2,9), generic rows at (3,9) both sides; (DO_3) at q = 9; the exact generic row `K'_k + π_z(M_k : z²) + (x_j^{q−2}e_{2k−2}(V))` at (2,9), (2,27), (3,9).
**(b)** Missing, exact: (L1'): «∃ G-invariant γ_0 (deg 2q−6), γ_1 (deg 2q−4) with `x_2x_3x_4·γ_0 + (x_2+x_3+x_4)·γ_1 ≡ L_1` mod `(x_1^{q−1}, (x_1+x_2)^{q−1}, (x_1+x_3)^{q−1}, (x_1+x_4)^{q−1})`» together with (C) ⟹ (L1) for that q (cell: 4 variables, q = 27 next, unrun); (L2): the G-a family **(G-a_k)** for all k, q (cells (2,9), (2,27), (2,81) for G-a; (3,9) for k = 3) and the count of the `+1` rows, plus the odd generic/`+1` rows of `K'_k` (cell (3,9): 7 interaction generators of degrees 4, 5, q+1).
**(c)** **NO**: neither the conjecture nor the row k = 4 closes — (P_4) for q ≥ 81 needs (L1), and (DE_4), (DO_4) need (G-a_4) and the odd interaction lemma, none proved with k as a letter.

## STEP 0

**STATE: CLOSED.** **NEXT:** STEP 1, (L1) for every q, budget 40 min (last 8 min for writing).
Budget of this step: 10 min, no runs. Started 07:26.

### 0.1 Which way for (L2), and why

I take the **row way (Way C, organised by the tablero)**, with Way B's pieces only to describe the fibres. Statement of the mechanism (all inclusions are in `S_{2k} = F_3[x_0..x_{2k−1}]`, `z := x_{2k}`, `π_z : z ↦ 0`):

> **Row reduction.** `dim S/K_k = Σ_{a=0}^{q−1} dim S_{2k}/π_z(K_k : z^a)` (standard filtration by powers of `z`; rows `a ≥ q` are empty because `z^q ∈ K_k`). Write `W_v := {y ∈ F_q^{2k} : (y, v, 1) ∈ Z_{2k+2}}` for the fibre of `V_1` over `y_{2k} = v`, so `N_k = Σ_v |W_v|`. Hence
> **(DE_k) ⟸ for every `a`: `π_z(K_k : z^a) ⊇ gr I(W_{v(a)})`** with the tablero dictionary `a=0 ↔ v=−1`, `a=1 ↔ v=0`, `2 ≤ a ≤ q−2 ↔ v generic`, `a=q−1 ↔ v=+1`.

Two rows are already free:
- **Row 0** (`v = −1`, `W_{−1} = Z_{2k}`): `π_z(K_k) ⊇ I^{(2k)} = gr I(Z_{2k})` by `D(k−1)`. Colength `≤ P_{k−1}`.
- **Row 1** (`v = 0`, `W_0 = V'_1`): `π_z(K_k : z) ⊇ K'_k`, because `z·x_0⋯x_{2k−1} = e_{2k+1} ∈ I^{(2k+1)}` (2k+1 is odd) and `z·x_Cx_A^{q−1} ∈ M_k` for every generator of `M'_k` (add `z` to `C`). With `(DO_k)` (`gr I(V'_1) = K'_k`) the colength is `≤ N'_k`.

So **(DE_k) is reduced, given `D(k−1)` and `(DO_k)`, to the generic rows and the `+1` row**: `gr I(W_v) ⊆ π_z(K_k : z^a)` for `v ∉ {0, −1}`. These are fibre statements in `2k` variables about the two-fold slices `W_v = ⋃_{i≠j} {y_i = −v, y_j = −1} × Z_{2k−2}` (generic) and `W_{+1} = ⋃_{i<j} {y_i = y_j = −1} × Z_{2k−2}`; G-a is exactly the generic row at `k = 2`.

Why not Way A: it needs `gr Fun(Z_{2k+1})` structurally, and `D'(k)` is only available as a number; every argument through it collapses back to `dim S/K_k ≤ N_k`. Why not Way B alone: `gr` of a union is not the intersection of the `gr`'s (the mission's warning), and the incidences are exactly the fibres over `y_{2k}`, which is what the row way isolates.

The same reduction, one parity down, applies to `(DO_k)` with `z = x_{2k−1}` and the fibres of `V'_1`.

### 0.2 (L1): what I will do
The system is `E_o(w)·(γ_1 + Uw) ≡ ε_1γ_1·E_e(w)` mod `box_q` as polynomials in `w`, with `E_e = 1 + ε_2w + ε_4w²`, `E_o = ε_1 + ε_3w`, `U = T − ε_4γ_0` (check: the `w¹` and `w²` coefficients are (I) and (II)). Necessary conditions (adjugate): `Π·γ_1 ∈ box_q` and `Π·γ_0 ∈ box_{q−1}`, `Π = ∏_{i<j}(x_i + x_j) = det Mat` (note `Π·T ∈ box_q` automatically since `β_1 r_1^{q−1} ∈ box_q`). Plan: look for the general-`q` shape of the `q = 9` solution through these annihilators, gate at `q = 9, 27`.

### 0.3 Reading check of MISION_5.md
- §2.5 `(P_k)`: `|C| = 2k−3` with `x_{2k}`, `a, a', b, b'` and `C` in `S_{2k+1}` uses `2k+2` letters; the audited statement (INFORME_3 §1.1) has `x_{2k} ∈ C`-free form with `|C| = 2k−4`... I will take the statement from INFORME_3 §1.1 if I need it; nothing in this turn depends on `|C|`.
- No other inconsistency found.

## STEP 1

**STATE: NOT CONCLUDED** ((L1) not closed for all q; 23 of the 40 min used, see 1.5). **NEXT:** STEP 2, (L2) by the row way, budget 100 min (last 20 min for writing).
Budget written: 40 min (07:36–08:16). Runs: `adj.m2`, `evalsys.m2`, `c1.m2` (all 4 variables, q ≤ 9, no colon; each < 15 s, < 450 MB; estimates written in the shell before each run).

### 1.1 Three exact reformulations of (L1) — PROVED (coefficient comparison, written here)
Notation: `R := F_3[x_1..x_4]/box_q`, `U := T − ε_4γ_0`, `m(s) := s² + ε_2 s + ε_4`, `α(s) := ε_3 + ε_1 s`, `E*(u) := ∏(u + x_i) = m(u²) + u·α(u²)` (even/odd parts of the reciprocal quartic).

- **(R1) Quadratic-extension form.** `R' := R[s]/(m(s))` (free of rank 2 over R). Then
  **(L1) ⟺ ∃ ζ = U + γ_1 s ∈ R' with α·ζ = 0 in R' and ζ ≡ T mod sR'.**
  Proof: `α(s)(U + γ_1s) = ε_3U + (ε_3γ_1 + ε_1U)s + ε_1γ_1s²`, and `s² = −ε_2s − ε_4`; the `s⁰`, `s¹` coefficients of `α·ζ − ε_1γ_1·m(s)` are exactly (II) and (I). `sR' = {U + γ_1s : U ∈ ε_4R}`, so `ζ ≡ T mod sR' ⟺ U ≡ T mod ε_4`. Equivalently **(L1) ⟺ α·T ∈ α·s·R'**.
  Norm: `α·ᾱ = −Π` with `ᾱ = (ε_3 − ε_1ε_2) − ε_1 s`, `Π = ∏_{i<j}(x_i+x_j) = ε_1ε_2ε_3 − ε_1²ε_4 − ε_3² = det Mat`. Hence the necessary conditions `Π·γ_1 ∈ box_q`, `Π·γ_0 ∈ box_{q−1}` (`Π·T ∈ box_q` automatically, since `β_1 r_1^{q−1} ∈ box_q`).
- **(R2) Root form.** With `F̃(u) := U + ε_1γ_1u + γ_1u² = u²F(1/u)`:
  **(L1) ⟺ α(u²)·F̃(u) = 0 in R[u]/(E*(u)).** Proof: `α(u²)F̃(u) = α(s)ζ(s) + ε_1γ_1·uα(s)` with `s = u²`, and `uα(u²) ≡ −m(u²)` mod `E*`; so `α(u²)F̃ ≡ αζ − ε_1γ_1 m`, an even polynomial of degree ≤ 2 in `u` (the `u⁴` coefficient cancels), which is 0 mod the monic quartic `E*` iff it is 0.
- **(R3) Evaluation system.** Evaluating (R2) at `u = −x_i` (`E*(−x_i) = 0`, `α(x_i²) = ∏_{j≠i}(x_i+x_j) =: P_i`):
  **(L1) ⟹ (C):  P_i · (U − γ_1 x_i(ε_1 − x_i)) ∈ box_q for i = 1..4.**
  In the coordinates `x := x_i`, `y_j := x_i + x_j` (j ≠ i) one has `box_q = (x^q, y_j^q)` (Frobenius, char 3) and `P_i = y_jy_ky_l` is a monomial, so `(box_q : P_i) = 𝔟_i := (x_i^q, (x_i+x_j)^{q−1} : j ≠ i)` and **(C_i) ⟺ U − γ_1x_i(ε_1 − x_i) ∈ 𝔟_i**. Moreover `r_i-pair^{q−1} ∈ 𝔟_i`, and `T ≡ r_{other pair}^{q−1} mod 𝔟_i` is divisible by `x_i²` after reduction, so dividing by `x_i` (𝔟_i is monomial in the adapted coordinates):
  **(C_i) ⟺ σ_3^{(i)}·γ_0 + σ_1^{(i)}·γ_1 ≡ L_i mod 𝔠_i := (x_i^{q−1}, (x_i+x_j)^{q−1} : j≠i)**, where `σ^{(i)}` are the elementary symmetric polynomials of the other three variables and `L_i := x_i^{−1}·(T mod 𝔟_i)`; explicitly for i = 1: `L_1 = Σ_{m,m' ≤ q−2, m+m' ≥ q−1} y_3^m y_4^{m'} x^{2q−3−m−m'}`.
- **Symmetry.** `T`, `ε_j` are invariant under `G = ⟨a↔a', b↔b', (a,a')↔(b,b')⟩` (order 8) and `G` permutes the `(C_i)`. So for **G-invariant `(γ_0, γ_1)` (as in l1b), (C) ⟺ (C_1)**: a single congruence modulo a monomial ideal.

### 1.2 Measured (logs in this folder)
| claim | cell | result | log |
|---|---|---|---|
| adjugate ansatz `ζ = ᾱ·c` (`γ_1 = −ε_1c`, `U = (ε_3−ε_1ε_2)c`, `Πc ∈ box_q`) | q = 3, 9 | **unsolvable** (unknowns 4 / 560) | `adj.log` |
| (C) ⟺ (L1) as linear systems in (γ_0, γ_1), all monomials | q = 9 | **same row space**: rank(L1) = rank(C) = rank(L1∪C) = 645; unknowns 1135; (L1) affine kernel dim 490 | `evalsys.log` |
| same | q = 3 | (L1) ⟹ (C) but rank(C) = 10 < 11 = rank(L1); both solvable ((L1) unique) | `evalsys.log` |
| single congruence (C_1) with G-invariant unknowns, degrees (2q−6, 2q−4) | q = 9 | solvable (unknowns 72+104, rows 336, kernel 74); the solution satisfies (I), (II) and all four (C_i) | `c1.log` |

So at `q = 9` **(L1) ⟺ (C_1) for G-invariant unknowns**, a congruence modulo the monomial ideal `(x^{q−1}, y_2^{q−1}, y_3^{q−1}, y_4^{q−1})`. At `q = 3` (C) is strictly weaker than (L1) (small-q effect: the kernel of evaluation `R[u]/(E*) → R⁴` meets the relevant elements). Gate q = 27 not run: the G-invariant (C_1) system at q = 27 has ≈ 5 800 unknowns × 11 700 rows and building the columns (products of degree ≈ 50 in 4 variables) extrapolates from q = 9 to ≈ 15 min > 10 min; not launched.

### 1.3 Dead this step
- Adjugate ansatz `ζ ∈ ᾱ·Ann_{R'}(Π)` (would have given a closed formula): dead at q = 3 and q = 9 (`adj.log`). Reason: `Ann_{R'}(α) ⊋ ᾱ·Ann_{R'}(Π)`; the solutions live outside the adjugate image. (The `c_1` component of `c` never enters the constraint `ζ ≡ T mod s`, so this kills the whole adjugate family.)

### 1.4 What is missing for (L1), exactly
> **Missing lemma (L1'):** for every `q = 3^v ≥ 9` there are G-invariant `γ_0` (degree 2q−6), `γ_1` (degree 2q−4) with
> `x_2x_3x_4·γ_0 + (x_2+x_3+x_4)·γ_1 ≡ L_1 mod (x_1^{q−1}, (x_1+x_2)^{q−1}, (x_1+x_3)^{q−1}, (x_1+x_4)^{q−1})`,
> together with the implication (C) ⟹ (L1) for that `q` (measured at q = 9, false at q = 3).
> Cell where it is checked: 4 variables, q = 9 (`c1.log`); q = 27 is the next gate (estimated 15 min, over budget as written; feasible with the columns built inside the quotient ring).

**(P_k) for all k and all q: NOT PROVED.** Status of (P_k) unchanged: all k at q ∈ {3, 9, 27}.

### 1.5 Addendum (still inside the STEP 1 budget, 07:48–07:59): gate q = 27 launched and killed
`c1_27.m2`: the G-invariant single congruence (C_1) at q = 27 with caps (q−3, q−1) (unknowns 1427 + 1687, rows 11 700), columns built inside the quotient ring. Estimate written before launch: ≈ 37 M entries, ≈ 300 MB, solve time uncertain, **watchdog set to 570 s**. Result: still building the columns at 570 s (RSS 670 MB), **killed by the watchdog** (`c1_27.log`: WATCHDOG-KILLED, exit 143). **Checked with `ps -p` and `pgrep -fl "M2.*c1_27"` at 07:58: the process is gone.** Nothing from this run is used. The gate q = 27 for (C) ⟺ (L1) remains unrun (needs a sparse/structured solver, not dense linear algebra).
Time actually used by STEP 1: 07:36–07:59 (23 min of 40).

## STEP 2

**STATE: NOT CONCLUDED** ((L2) not proved for any k ≥ 3 with k as a letter; new structure proved and measured, see the summary at the end of the step). **NEXT:** STEP 3, row k = 4, budget 30 min (last 6 min for writing).
Budget written: 100 min (07:59–09:39; writing from 09:19); actually used 07:59–08:27 (stopped by rule 4: after the reduction to the G-a family no further progress on it). Runs (all with a 570 s watchdog after the first two; estimates written in the shell before each launch): `rows.m2`, `rows_odd.m2` (2,9); `rows27.m2` (2,27, killed); `int39.m2`, `int39b.m2` (killed), `int39c.m2`, `int39d.m2`, `dim39.m2` (second half killed), `proved.m2`, `red.m2`, `ga3k.m2`, `odd39.m2` (3,9); `guess2.m2`, `guessgen2.m2`, `proved.m2` (2,9), (2,27); `gaf.m2` (q = 9 done, q = 27 killed). Every kill was verified with `ps`/`pgrep` and is recorded in its subsection.

### 2.1 The rows of the explicit casillas ARE the top-form ideals of the fibres — MEASURED at (2,9), both parities
Rows along the last variable `z`: `R^K_a := π_z(K_k : z^a)`, `R'^K_a := π_z(K'_k : z^a)`; fibres `W_v := {y ∈ F_q^{2k} : y ∪ {v,1} closed}` (even), `W'_v := {y ∈ F_q^{2k−1} : y ∪ {v,1} closed}` (odd).
| cell | side | v = −1 (a = 0) | v = 0 (a = 1) | v generic (a = 2) | v = +1 (a = q−1) | log |
|---|---|---|---|---|---|---|
| (2,9) | even, `K_2` | 217 = 217, **equal** | 88 = 88, **equal** | 84 = 84, **equal** (rows 2..7 all equal) | 46 = 46, **equal** | `rows.log` |
| (2,9) | odd, `K'_2` | 25 = 25, **equal** | 24 = 24, **equal** | 6 = 6, **equal** | 3 = 3, **equal** | `rows_odd.log` |
(entries: `|W_v| = colength gr I(W_v)`, and `gr I(W_v) = R^K_a` as ideals over GF(9); sums 855 = N_2, 88 = N'_2.)
So in the cell the identity **`R^K_a = gr I(W_{v(a)})`** holds exactly, for every row, on both sides. This is the precise content of the row way of STEP 0: (DE_k) and (DO_k) are the statements that the explicit ideal's rows are (contain) the top-form ideals of the fibres.

**PROVED for all k (elementary, from §2 of the mission):** `gr I(W_v) ⊇ I^{(2k)}` for every `v` (top forms of `e_j(y,v,1) = 0`, j odd); `gr I(W_v) ∋ e_{2k}` for `v ≠ −1` (from `(v+1)e_{2k}(y) + v·e_{2k−1}(y) = 0` on `W_v`); rows 0 and 1 of `K_k` contain `gr I(W_{−1}) = I^{(2k)}` (by `D(k−1)`) and `gr I(W_0) = K'_k` (by `(DO_k)`), as in STEP 0. Hence
> **(DE_k) ⟺ `gr I(W_v) ⊆ π_z(K_k : z²)` (v generic, one inclusion since the generic rows coincide) and `gr I(W_{+1}) ⊆ π_z(K_k : z^{q−1})`**, given `D(k−1)`, `D'(k)`, `(DO_k)`; and symmetrically for (DO_k).

### 2.2 The generic-row interaction elements at k = 3 are NOT «G-a times a variable» — MEASURED at (3,9)
`int39.m2` (`int39.log`): in `S_7`, `z = x_6`, `K_3 + (z³)`:
- `z²·x_0·x_1²·x_2^{q−2}` ∉ `K_3 + (z³)`; `z²·x_0x_3·x_1²x_2^{q−2}` ∉; `z²·x_0·x_1³x_2^{q−3}` ∉; the pure shape `z²x_1²x_2^{q−2}` ∉;
- `z²·x_0·x_1²x_2^{q−2}·x_3^{q−1}` ∈ (a `j = 2` monomial of `M_3 : z²`); `z·e_6` ∈ (`e_7`).
So the naive lift of G-a (multiplying by `x_C`, `|C| = 2k−4`) is **dead**: the interaction elements of the generic row at `k = 3` have another shape (see 2.2d for what `int39c` finds).

### 2.2b Gate (2,27) for the rows = fibres identity: launched and killed
`rows27.m2` (cell (2,27): `K_2` in 5 variables, 4 colons, point ideals of ≤ 700 points over GF(27)); estimate written before launch: < 8 min, < 1 GB, watchdog 570 s. It printed `dim S5/K2 = 9765` (= N_2(27), consistent with `slice27.log`) and was still computing the first point ideal at 570 s: **killed by the watchdog** (`rows27.log`: WATCHDOG-KILLED, exit 143); **checked with `pgrep -fl M2-binary` at 08:09: no M2 process of this run remains.** Nothing from it is used. The identity of 2.1 is therefore measured at (2,9) only.

### 2.2c Run `int39b.m2` (cell (3,9), the colon `K_3 : z²` in 7 variables): launched and killed
Estimate written before launch: < 6 min, < 1 GB (extrapolated from `int39.m2`, whose Gröbner basis of `K_3 + (z³)` took < 2 min), watchdog 570 s. The colon `K_3 : z²` was still running at 570 s (RSS 256 MB): **killed by the watchdog** (`int39b.log`: WATCHDOG-KILLED, exit 143); **checked with `pgrep -fl M2-binary` at 08:12: no M2 process remains.** Nothing from it is used. Relaunched as `int39c.m2` through the cheaper colon `(K_3 + (z³)) : z²`, which has the same z-free part (if `z²g = k + z³s` then `z²(g − zs) ∈ K_3`).


### 2.2d The generic row of K_3 at (3,9): exact colength and the shape of its interaction elements — MEASURED (`int39c.log`, 90 s, < 300 MB; python count of the fibres)
Row `R_2 := π_z(K_3 : z²)` (`z = x_6`, computed as the z-free part of `(K_3 + (z³)) : z²`), `L := K'_3 + π_z(M_3 : z²)` (the «sum of colons»):
| object | colength at (3,9) | fibre count (python, `F_9 = F_3[i]`) |
|---|---|---|
| `L = K'_3 + π_z(M_3 : z²)` | 4266 | `|W_0| = N'_3 = 4266` |
| generic row `R_2` | **3930** | **`|W_gen| = 3930`** |
| (for the record) | | `|W_{−1}| = 7761`, `|W_{+1}| = 2340`, so `N_3(9) = 37947` |
So at (3,9) **the generic row of the explicit casilla has exactly the colength of the generic fibre**, and the sum of colons adds nothing to `K'_3` (4266 = N'_3), exactly as INFORME_3 §2.1 predicted: the 336 missing dimensions are cut by **10 interaction elements**, all minimal generators of `R_2` of degree `q+2 = 11` (`mingens`, reduced modulo `L`). Two of them have a closed form (read off the log, exact):
- `y_5^{q−2}·e_4(y_1, y_2, y_3, y_4, y_5)` and `y_4^{q−2}·e_4(y_1, y_2, y_3, y_4, y_5)` (`e_4` of FIVE of the six variables, times `y_j^{q−2}` with `j` inside the five);
- the others are of the form `y_j^{q−2}·(cubic or `y_i²·quadratic`) in five variables, e.g. `y_4²y_5^{q−2}·[h_2(y_1,y_2,y_3) + (y_1+y_2+y_3)(y_4+y_5) + y_4y_5] + y_4³y_5^{q−1}` and `y_5^{q−2}·[σ_1σ_3 + y_5(σ_1σ_2 − σ_3)]` with `σ_i = e_i(y_2,y_3,y_4)`.
**Consequence (structural, not yet a proof):** the interaction elements of the generic row at `k = 3` are *not* `x_C·(G-a)`; they are `y_j^{q−2}` times a form of degree 4 in five variables (G-a itself is `y_i²·y_j^{q−2}`, i.e. `y_j^{q−2}` times a form of degree 2 in four variables). The natural k-general guess is **«`y_j^{q−2}·Φ_{2k−2}` with `Φ` a form of degree `2k−2` in `2k−1` of the `2k` variables, `e_{2k−2}` among them»**; it reproduces both cells (k = 2: degree 2, k = 3: degree 4). This is the candidate statement for the interaction lemma; it is not proved here for any k ≥ 3 (cell (3,9) shows the generators exist; a k-general membership proof of `z²·y_j^{q−2}·e_{2k−2}(…) ∈ K_k + (z³)` is the next lemma to attempt, with `y_j^{q−2}e_4 ∈ R_2` at (3,9) as its first gate — passed by construction).

### 2.2e Gate k = 2 of the k-general guess, and (DO_3) at (3,9) — MEASURED
`guess2.log` (cell (2,9) and (2,27), `K_2 + (z³)` in 5 variables, < 1 min each): **`z²·x_1^{q−2}·e_2(x_0,x_1,x_2) ∈ K_2 + (z³)` at q = 9 and q = 27** (also with `j` outside: `z²x_1^{q−2}e_2(x_0,x_2,x_3)` ∈), while the pieces `z²x_0x_2x_1^{q−2}`, `z²(x_0+x_2)x_1^{q−1}`, `z²x_1^{q−2}h_2(x_0,x_2)` are NOT in. So the guess of 2.2d, «`y_j^{q−2}·e_{2k−2}(2k−1 variables)` lies in the generic row», passes its k = 2 gate at two values of q, and it is an interaction element there too (its monomials are not in the row separately); G-a (`z²x_0²x_1^{q−2}`) is confirmed at 9, 27 as in INFORME_3.
`dim39.log`: **`dim S_6/K'_3 = 4266 = N'_3` at (3,9)** (the second part of that run, `dim S_7/K_3`, was still computing at 570 s and was **killed by the watchdog**; checked with `pgrep -fl M2-binary` at 08:25: no M2 process remains; nothing from it is used), hence **(DO_3) holds at q = 9** (with `K'_3 ⊆ J'_1 ⊆ gr I(V'_1)` of colength N'_3, the three ideals coincide). New cell for (L2) odd side: k = 3, q = 9.

### 2.6 A k-general interaction element of the generic rows — PROVED for all k ≥ 1 and all q ≥ 3
> **Lemma (even generic row).** In `S_{2k+1}` with `z = x_{2k}`, `x' = (x_0..x_{2k−1})`, for every `j ≤ 2k−1`:
> `z²·x_j^{q−2}·e_{2k−2}(x') ∈ K_k = I^{(2k+1)} + M_k`, hence **`x_j^{q−2}·e_{2k−2}(x_0..x_{2k−1}) ∈ π_z(K_k : z²)`** (the generic row).
Proof. (i) `e_{2k−1}(x') = x_j·e_{2k−2}(x'∖x_j) + ∏_{i≠j} x_i`. Then `z·x_j^{q−1}·e_{2k−2}(x'∖x_j)` is a sum of monomials `x_{C∪{z}}·x_j^{q−1}` with `C ⊆ x'∖x_j`, `|C| = 2k−2`: each is a generator of `M^{(1)}([2k+1])` (partition `A = {j}`, `B = {the one variable of x' left out}`, `C ∪ {z}` of size `2k−1`). And `z·x_j^{q−2}·∏_{i≠j}x_i = x_j^{q−3}·e_{2k+1}(x_0..x_{2k}) ∈ I^{(2k+1)}` (`q ≥ 3`). So `z·x_j^{q−2}·e_{2k−1}(x') ∈ K_k`.
(ii) `e_{2k−1}(x_0..x_{2k}) = e_{2k−1}(x') + z·e_{2k−2}(x') ∈ I^{(2k+1)}` (`2k−1` odd). Multiply by `z·x_j^{q−2}` and subtract (i): `z²·x_j^{q−2}·e_{2k−2}(x') ∈ K_k`. ∎
> **Lemma (odd generic row).** In `S_{2k}` with `z = x_{2k−1}`, `x'' = (x_0..x_{2k−2})`: `z²·x_j^{q−2}·e_{2k−2}(x'') ∈ K'_k`, hence `x_j^{q−2}·e_{2k−2}(x'') ∈ π_z(K'_k : z²)`.
Proof. `e_{2k−1}(x_0..x_{2k−1}) = ∏x'' + z·e_{2k−2}(x'') ∈ I^{(2k)}`; multiply by `z·x_j^{q−2}`: `z·x_j^{q−2}·∏x'' = x_j^{q−3}·e_{2k}(x_0..x_{2k−1}) ∈ K'_k`. ∎
Relation with the cells: modulo `L` and `e_1`, at k = 2 the even element is `x_j^{q−2}·Σ_{i≠j}x_i²`, the **symmetric sum of the three G-a elements `x_i²x_j^{q−2}` with the same `j`** (from `e_2(x'∖x_j) ≡ p_2(x'∖x_j) − x_j²` mod `(e_1)`); it is the first interaction element of the generic row proved with `k` as a letter. It does **not** give G-a itself (the 12 elements `x_i²x_j^{q−2}` span more than the 4 sums). **Measured (`proved.log`, cells (2,9), (2,27), (3,9)): the elements `x_j^{q−2}e_{2k−2}(x')` all lie in `L = K'_k + π_z(M_k : z²)`, and `L + (them)` has the colength of `L` (88, 304, 4266).** So this lemma is PROVED but gives nothing beyond the sum of colons; its value is only as the first step of the reduction in 2.8. Same method, one more variable: `z²·x_ix_j^{q−2}·e_{2k−2}(x') ≡ −z·x_i²x_j^{q−1}·e_{2k−3}(x'∖{x_i,x_j})` mod `K_k`, and `x_i²x_j^{q−1}e_{2k−3}(x'∖{x_i,x_j}) ∈ K'_k` for all k (multiply `e_{2k−1}(x') ∈ I^{(2k)}` by `x_ix_j^{q−2}`; the other two terms are multiples of `e_{2k}(x')`; checked in `red.log` at (2,9), (2,27), (3,9)). But `z·K'_k ⊄ K_k` (`z·e_{2k−1}(x') ≡ −z²e_{2k−2}(x')`), so this congruence is **circular** (it is the same identity read backwards) and gives nothing new: **corrected, an earlier draft of this paragraph claimed a reduction to a row-1 membership; that claim is withdrawn.**

### 2.7 The generic row of K_3 at (3,9) is EXACTLY «sum of colons + the guess» — MEASURED (`int39d.log`, < 3 min)
With `L = K'_3 + π_z(M_3 : z²)` and `Γ := (y_j^{q−2}·e_4(V) : V ⊂ {0..5}, |V| = 5, j ∈ V)` (30 elements):
**all 30 lie in `R_2`, and `L + Γ = R_2` as ideals, colength 3930 = |W_gen|.** Adding the `j`-outside elements `y_j^{q−2}e_4(V)`, `j ∉ V` (also in `R_2`) changes nothing.
So at (3,9) the even generic row is completely described: `π_z(K_3 : z²) = K'_3 + π_z(M_3 : z²) + (y_j^{q−2}e_4(V))`. Together with 2.2e (k = 2 membership at q = 9, 27) this fixes the **candidate interaction lemma for all k**:
> **(IL_k), even generic row:** `z²·x_j^{q−2}·e_{2k−2}(V) ∈ K_k + (z³)` for every `V ⊂ {0..2k−1}` with `|V| = 2k−1` and `j ∈ V`; and **(GR_k):** `π_z(K_k : z²) = K'_k + π_z(M_k : z²) + (x_j^{q−2}e_{2k−2}(V))`.
> Status: (IL_2) at q = 9, 27 (`guess2.log`); (IL_3) and (GR_3) at q = 9 (`int39d.log`); (GR_2) at q = 9, 27: see `guessgen2.log` (2.8). With `k` as a letter: the weaker element `x_j^{q−2}e_{2k−2}(x')` (all 2k variables) is PROVED (2.6), but at k = 2 it lies in `L` (`proved.log`: colength of `L` unchanged at (2,9), (2,27)), so it is not the interaction element; (IL_k) itself is **not proved** for any k with k as a letter.

### 2.8 (GR_2) at q = 9, 27 — MEASURED; and (IL_k) ⟺ a G-a family — PROVED with k as a letter
`guessgen2.log`: at (2,9) and (2,27), `L + (x_j^{q−2}e_2(V)) = R_2 = L + (x_i²x_j^{q−2})`, colengths 84 = 12·7 and 300 = 12·25. So **(GR_k) holds at (2,9), (2,27), (3,9)** and the two descriptions (by `x_j^{q−2}e_{2k−2}(V)` or by the G-a family below) coincide at k = 2.
> **Lemma (reduction of the interaction element, all k ≥ 2, all q ≥ 3).** For `V = x'∖{x_l}`, `j ∈ V`:
> `z²·x_j^{q−2}·e_{2k−2}(V) ∈ K_k + (z³)  ⟺  z²·x_l²·x_j^{q−2}·e_{2k−4}(V) ∈ K_k + (z³)`.
Proof. By 2.6, `z²x_j^{q−2}e_{2k−2}(x') ∈ K_k`, and `e_{2k−2}(x') = e_{2k−2}(V) + x_l e_{2k−3}(V)`; so the left side is equivalent to `z²x_lx_j^{q−2}e_{2k−3}(V) ∈ K_k + (z³)`. Next `e_{2k−3}(x_0..x_{2k}) = e_{2k−3}(x') + z·e_{2k−4}(x') ∈ I^{(2k+1)}` (odd), so `z²x_lx_j^{q−2}e_{2k−3}(x') ∈ K_k + (z³)`; with `e_{2k−3}(x') = e_{2k−3}(V) + x_le_{2k−4}(V)` this gives `z²x_lx_j^{q−2}e_{2k−3}(V) ≡ −z²x_l²x_j^{q−2}e_{2k−4}(V)` mod `K_k + (z³)`. ∎
At k = 2 (`e_0 = 1`) the right side is **G-a**. So the candidate interaction lemma (IL_k) is, for every k, the **G-a family**
> **(G-a_k): `z²·x_l²·x_j^{q−2}·e_{2k−4}(x'∖x_l) ∈ I^{(2k+1)} + M_k + (z³)`** (`l ≠ j`),
and (GR_k) reads `π_z(K_k : z²) = K'_k + π_z(M_k : z²) + (x_l²x_j^{q−2}e_{2k−4}(x'∖x_l))`. (G-a_2) = G-a is true at q = 9, 27, 81 and open in general; (G-a_3) is true at q = 9 (`int39d.log` through the lemma; **direct check `ga3k.log`: `z²x_0²x_1^{q−2}e_2(x_1..x_5) ∈ K_3 + (z³)` true, while the pieces `z²x_0²x_1^{q−2}x_2x_3` and the `j`-outside form `z²x_0²x_1^{q−2}e_2(x_2..x_5)` are not**: the algebra of the reduction is confirmed in the cell). **The whole even generic row for all k now rests on the G-a family, which contains G-a: nothing with k as a letter is proved beyond the equivalence.** The colength statement (GR_k) ⟹ «row colength = |W_gen|» additionally needs the count, which at (2,q) is the mission-1 count `12(q−2)` and at (3,9) is measured.

### 2.9 Geometric side of G-a on the fibre points — MEASURED at q = 9; q = 27 killed
`gaf.m2`: on `W_v = perm(−v,−1,c,−c) ⊂ F_q^4` (84 points at q = 9), **`y_0²y_1^{q−2}` is a function of degree ≤ q−1** (evaluation matrix, rank 78: the polynomials of degree ≤ q−1 span 78 of the 84 dimensions of `Fun(W_v)`; the last 6 need degree q). This is the geometric content of G-a at k = 2 (`x_0²x_1^{q−2} ∈ gr I(W_v)`), consistent with 2.1. At q = 27 the evaluation matrix (300 × 27 405 over GF(27)) was still being built at 570 s: **killed by the watchdog** (`gaf.log`); **checked with `pgrep -fl M2-binary` at 08:23: no `gaf` process remains.** Nothing from the q = 27 part is used.

### 2.12 Odd side at (3,9): the odd generic row is exact and its interaction elements — MEASURED (`odd39.log`, < 1 min; fibre counts by python)
Rows of `K'_3` along `z = x_5` (5 remaining variables), fibres of `V'_1` over `y_5 = v`: `|W'_{−1}| = 921 = P'_2`, `|W'_0| = 855 = N_2`, `|W'_gen| = 380`, `|W'_{+1}| = 210` (sum 4266 = N'_3).
| row of `K'_3` | colength | fibre |
|---|---|---|
| row 1 | 855 | `|W'_0| = 855` |
| generic row `R'_2` | **380** | **`|W'_gen| = 380`** |
| sum of colons `L' = π_z(I^{(6)} : z) + π_z(M'_3 : z²) + (e_5)` | 855 | (adds nothing to row 1, as INFORME_3 §3.2 predicted) |
The 7 interaction generators of `R'_2` beyond `L'` have degrees 4, 5, 10, 10, 10, 10, 10 (`q+1 = 10`). Closed forms read off the log: the quintic `y_4³·[h_2(y_1,y_2,y_3) + y_4·e_1(y_1,y_2,y_3)]`, the quartic (a form in `y_1..y_4`, the k = 3 analogue of the `(y_1−y_2)²` of INFORME_3 §3.1), the **monomial `y_3³y_4^{q−2}`**, `y_4^{q−2}·e_3(y_1,y_2,y_3,y_4)` (and `y_3^{q−2}e_3(y_1,y_2,y_3,y_4)`; same pattern as the even side: `y_j^{q−2}·e_{2k−3}` of `2k−2` variables), and `y_4^{q−2}·[y_2y_3(y_2+y_3) + y_4·h_2(y_2,y_3)]`.
So **rows = fibres holds at (3,9) on both sides for the generic row** (even 3930, odd 380), and `(DO_3)` at q = 9 is confirmed twice (`dim39.log` and the row sum). The odd interaction elements mix a q-free part (degrees 4, 5) with a `q`-part (`y_j^{q−2}·`cubic, and the pure monomial `y_l³y_j^{q−2}`), unlike the even side where all are of degree `q+2`.

### 2.10 What can and cannot be done with the fibres — PROVED / DEAD
- **Multi-fibre lemma (PROVED, all k, both parities).** Let `X ⊆ F_q^{n}` be finite, `X_v` its fibre over `x_{n−1} = v`, and `T ⊆ F_q` a set of values. If `f` vanishes on `⋃_{v∈T} X_v`, then `f·∏_{w∉T}(x_{n−1} − w) ∈ I(X)`, so `f_top ∈ π(gr I(X) : x_{n−1}^{q−|T|})`. In particular **`gr I(W_v) ⊆ π_z(gr I(V_1) : z^{q−1})` for every single value `v`**: the vanishing argument reaches only the `+1` row (`a = q−1`), for any `v`. Proof of the limitation: an element `H ∈ I(Z_{2k+2})` with top form `t·z^a·f_top(y)` restricted to the fibre `z = wt`, `t ≠ 0`, is `w^a f(y) + (lower)`, and to vanish on the fibres `w ≠ v` it needs a factor with `q−1` roots unless the lower-order terms interact. **So the generic rows (`2 ≤ a ≤ q−2`) cannot be reached by vanishing alone; they are «interaction» rows, as INFORME_3 §2.1 already said from the algebraic side.** This is the geometric reason why the generic rows are the whole difficulty: they are the only rows whose fibre identity `R^K_a = gr I(W_v)` is not a consequence of a vanishing construction.
- **The generic rows all coincide (measured (2,9): `R^K_2 = … = R^K_{q−2}`), while the generic fibres `W_v` are pairwise different sets** (`W_v ≠ W_{v'}`) with the same `gr I`. So `gr I(W_v)` is independent of the generic value `v`: the top-form ideal only sees the combinatorial type of the union of pieces `⋃_{i≠j}{y_i = −v, y_j = −1} × Z_{2k−2}`, not the values. Same for the odd side. (Measured; not proved for general k.)
- **The row chain is a chain of fibres (measured (2,9)):** `gr I(Z_{2k}) ⊆ gr I(V'_1) ⊆ gr I(W_gen) ⊆ gr I(W_{+1})`, although the sets are not nested. Each step is «replace a value `0` in the pieces by a non-zero value»: `V'_1 = ⋃{y_i = −1, y_j = 0} × Z_{2k−2}` versus `W_gen = ⋃{y_i = −1, y_j = −v} × Z_{2k−2}`, exactly the Way-B picture of MISION_5 §4 one level down. **The mechanism that makes `gr I` grow when a `0` is moved to a generic value is the interaction; it is the same mechanism at every level, and G-a is its smallest instance (k = 2, one level).**

### 2.11 Exact missing lemma for (L2), in fibre form
> **(L2-fibre), for every `k` and every `q`:**
> **even generic:** `gr I(W_v) ⊆ π_z(K_k : z²)` for one generic `v` (with `K_k = I^{(2k+1)} + M_k`, `z = x_{2k}`);
> **even +1:** `gr I(W_{+1}) ⊆ π_z(K_k : z^{q−1})`;
> **odd generic / odd +1:** the same with `K'_k`, `z = x_{2k−1}`, and the fibres `W'_v`, `W'_{+1}` of `V'_1`.
> Given `D(k−1)`, `D'(k)`, `(DO_k)` (even side) and `D(k−1)`, `(P_k)` (odd side), these four inclusions are equivalent to (DE_k) and (DO_k) (2.1). The reverse inclusions `π_z(K_k : z^a) ⊆ gr I(W_{v(a)})` hold whenever `K_k ⊆ gr I(V_1)` (multi-fibre lemma read backwards on the true casilla; PROVED given the PLUS lemma).
> Cells: (2,9) both sides equal (`rows.log`, `rows_odd.log`); (3,9) is the first cell with a generic row at `k = 3`.
The k = 2 even generic instance is G-a; **G-a for all q remains open** (nothing new this turn: the fibre form shows it is equivalent to «`y_0²y_1^{q−2}` has degree ≤ q−1 as a function on the 12(q−2) points `perm(−v, −1, c, −c)`» together with `gr I(W_v) ⊆ R^K_2`, and I found no polynomial of degree ≤ q−1 realising `y_0²/y_1` on those points for general q).

### 2.13 Summary of STEP 2
PROVED (k as a letter): the multi-fibre lemma and the limitation of vanishing arguments to the `+1` row (2.10); the elements `x_j^{q−2}e_{2k−2}(x')` in the generic rows of both parities (2.6; they lie in the sum of colons in all cells); **the reduction lemma (2.8): the candidate generic-row element `x_j^{q−2}e_{2k−2}(V)` is in the row iff the G-a-family element `x_l²x_j^{q−2}e_{2k−4}(x'∖x_l)` is** — so the even generic row of every `K_k` is governed by the family (G-a_k) whose first member is G-a.
MEASURED: rows = fibres for every row at (2,9) both sides (2.1); generic rows at (3,9) both sides (even 3930, odd 380) (2.2d, 2.12); (DO_3) at q = 9 (2.2e); the exact description `π_z(K_k : z²) = K'_k + π_z(M_k : z²) + (x_j^{q−2}e_{2k−2}(V))` at (2,9), (2,27), (3,9) (2.7, 2.8); (G-a_3) at q = 9; the odd interaction elements at (3,9) (degrees 4, 5, q+1) (2.12); the geometric side of G-a at q = 9 (2.9).
DEAD: «G-a times a variable» as the k = 3 interaction element (2.2); `x_j^{q−2}e_{2k−2}` of all 2k variables as a new element (in `L`); the withdrawn «reduction to row 1» (2.6).
**(L2) for all k: NOT PROVED. CONJECTURE 1.2: NOT CLOSED.** Nothing beyond k = 2 (odd) and k = 1 (even) is proved for all q; new cells: (DO_3) at q = 9, and the generic rows of both casillas at (3,9) have exactly the fibre colengths.

## STEP 3

**STATE: NOT CONCLUDED.** **NEXT:** STEP 4, verdict, 15 min.
Budget written: 30 min (08:27–08:57; writing from 08:51); used 08:27–08:29. No new runs: the only allowed cell for k = 4 is (4,3), already sealed (`J_1 = K_4`, `J'_1 = K'_4`, and D(4) at q = 3 by Steinberg), and it has no generic rows (q = 3 has rows 0, 1, q−1 only), so it cannot gate (P_4), (DO_4) or (DE_4) at general q.

Row k = 4 for all q needs exactly (P_4), (DO_4), (DE_4) (MISION_5 §2). Status after STEPs 1–2:
- **(P_4)**: holds at q ∈ {3, 9, 27} (INFORME_3, k-free). For q ≥ 81 it is (L1) at that q, not proved (STEP 1: reduced to the single congruence (C_1) with G-invariant unknowns, gate q = 27 unrun).
- **(DE_4)** (given D(3), D'(4), (DO_4)): by the row way, ⟺ generic row `π_z(K_4 : z²) ⊇ gr I(W_gen)` and `+1` row `⊇ gr I(W_{+1})`. Candidate description (GR_4): `K'_4 + π_z(M_4 : z²) + (x_j^{q−2}e_6(V))`, equivalent by the reduction lemma (2.8) to the family **(G-a_4): `z²x_l²x_j^{q−2}e_4(x'∖x_l) ∈ K_4 + (z³)`**. Not proved; first cell would be (4,9), not allowed (and beyond the machine).
- **(DO_4)** (given D(3), (P_4)): odd generic and `+1` rows of `K'_4`; the (3,9) data (2.12) show the odd interaction elements are of mixed type (q-free forms of low degree plus `y_j^{q−2}·`cubic and `y_l³y_j^{q−2}`); no k-general statement proved.
**«D(4) FOR ALL q»: NOT REACHED.** Exact missing pieces for the row: (L1) at q ≥ 81; (G-a_4) for all q plus the count of the even `+1` row of `K_4`; the odd generic and `+1` rows of `K'_4` for all q.

## STEP 4 — VERDICT

**STATE: CLOSED** (verdict written after re-reading the whole file from disk). Budget written: 15 min (08:29–08:44); the file was re-read from disk in full at 08:27 before writing this verdict, and the header times of STEPs 1–3 were corrected to the real ones.

Applying the chain of MISION_5 §2 to what is proved:
- (L1): proved for q ≤ 27 (unchanged); this turn: three exact reformulations (quadratic-extension form `α·ζ = 0` in `R[s]/(s² + ε_2s + ε_4)`, root form in `R[u]/∏(u+x_i)`, evaluation system (C) ⟺ four memberships in the monomial ideals `𝔟_i` of the adapted coordinates), (C) ⟺ (L1) at q = 9, and for G-invariant unknowns (L1) ⟺ one congruence modulo `(x^{q−1}, y_2^{q−1}, y_3^{q−1}, y_4^{q−1})` (verified q = 9). The adjugate ansatz is dead. **No solution for general q.**
- (L2): rows 0, 1 exact for all k (INFORME_3 + STEP 0); this turn the target is made geometric (rows = fibres; the generic rows are the only «interaction» rows) and, with k as a letter, the even generic row is reduced to the family (G-a_k) ⊇ {G-a} (2.8). **No k ≥ 3 proved for all q; G-a still open.** New cells: (DO_3) at q = 9; exact generic rows at (3,9) both sides.
- Hence: **CONJECTURE 1.2: NOT CLOSED. Row k = 4 for all q: NOT CLOSED.** What is closed for all q remains: D(1), D'(1), D'(2), D(2), D(3) (external), (DO_2); (P_k) for all k at q ≤ 27.

Rule-10 incidents (all declared in their subsections, each verified gone with `ps`/`pgrep`): `c1_27.m2` (STEP 1), `rows27.m2`, `int39b.m2`, `gaf.m2` (q = 27 part), `dim39.m2` (second half) — killed by the 570 s watchdog; nothing from them is used. All other runs < 3 min and < 700 MB.
Errors found in MISION_5.md: none of substance. One precision: §2.5 states `(P_k)` with `|C| = 2k−3` and `2k+2` letters in `S_{2k+1}`; the audited form is INFORME_3 §1.1's; nothing here depends on it. §4 «Way A» was not used; its targets were not needed.
Double check: every PROVED claim above carries its proof in the step where it is stated (STEP 1 §1.1; STEP 2 §2.6, §2.8, §2.10); every number carries its cell and log.

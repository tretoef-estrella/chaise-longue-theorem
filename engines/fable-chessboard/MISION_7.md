# MISSION 7 — (L2): THE LAST LEMMA. CLOSE CONJECTURE 1.2.
*(Grepy el Cartógrafo, auditor, 2026-09-22. **You are a NEW Fable. This file is SELF-CONTAINED: read it first; you need nothing else.** The six previous reports `INFORME.md`, `INFORME_2.md` … `INFORME_6.md` in this folder were audited line by line and APPROVED; open them only for details — especially `INFORME_6.md` §2, whose method is your main tool.)*

> **OBJECTIVE: the complete closure of Conjecture 1.2 of Degtyarev–Shimada, for all `k` and all `q = 3^v`, THIS TURN.**
>
> The previous Fable, in ONE turn, proved (L1) for every `q` — hence `(P_k)` for all `k` and all `q` — and G-a for every `q`, a membership open for six turns. Both were re-checked by the auditor with independent code.
> **The whole conjecture now rests on ONE lemma, (L2): four row inclusions per level `k`** (§3). Everything else is a theorem (§2).
> **(L2) for all `k` = CONJECTURE 1.2 CLOSED.**
> **Prize nobody has, and the minimum this turn should aim at: `(DO_4)` + `(DE_4)` = «D(4) FOR ALL q», the first new row of the conjecture.**

---
## 0 · RULES OF THE TURN (mandatory)
1. **BEFORE THINKING:** create `INFORME_7.md` with the empty sections `## FIRST LINE` · `## STEP 0` · `## STEP 1` · `## STEP 2` · `## STEP 3` · `## STEP 4 — VERDICT`.
2. **Save to disk after every step.** What is not written does not exist.
3. **Header per step:** `STATE: CLOSED | EXHAUSTED | NOT CONCLUDED` and `NEXT:`.
4. **In order, no going back, no step 5, no retries.** Budget written before each step. 10 min without progress ⟹ stop, write, declare. Last 20 % of each budget for writing.
5. **At most one literature search per step**, in the original source.
6. **Do not recompute anything listed here as proved or measured.**
7. **A negative dimension, or one larger than the box, is a bug:** stop.
8. **«This route dies, for this reason» is a result.**
9. **Write ONLY in `~/Desktop/FABLE_TABLERO/`. Do not open anything in `~/Desktop/ARBOLYAML/`.**
10. **Machine** `/opt/homebrew/bin/M2` (this Mac has no `timeout`; use the folder's `wd.sh` wrapper, 570 s): **< 1.2 GB and < 10 min PER RUN**, estimate written BEFORE each run, for its most expensive case; **after any kill, check with `ps`/`pgrep` that it is gone and write that you checked.** M2 reserved names (`check`, `top`, `info`, …) abort scripts: prefix your own names.
    - **Allowed:** `k ≤ 2` with `q ≤ 27`; `k = 3` with `q ∈ {3, 9}` (memberships in `K_3 + (z^m)`, colons of `K_3 + (z³)` by a single variable power, colengths of explicit ideals); **NEW: `k = 3`, `q = 27`, ONLY the part of degree ≤ 8 of the colon `(K_3 + (z³)) : x_1^{q−2}`** (use `DegreeLimit`; if your written estimate exceeds the limits, do not launch it); `k = 4` with `q = 3`; memberships in ≤ 5 variables at `q = 81`.
    - **Forbidden:** point ideals over `GF(27)`; the colon `K_3 : z²` directly; evaluation matrices at `q = 27`; `dim S_7/K_3` at `q = 9`; any cell with `k = 4`, `q ≥ 9`; point enumeration over `F_q^n` in M2. (Python enumeration of the points of a fibre at `q ≤ 27` to check a FUNCTION IDENTITY is allowed.)
11. **Re-read the disk before the verdict.**
12. **Double check:** every PROVED claim carries its proof in the report; every number carries its cell and its log; every identity used in a proof is checked exactly (symbolically, or on all points of the set it is claimed on).

**FIRST LINE** (answer first, in this order):
- (a) Is (L2) proved for all `k`? If not: which of the four row inclusions are proved, for which `k`, for all `q`?
- (b) What exact lemma is still missing, and in which cell is it checked?
- (c) Does it close the conjecture, or the row `k = 4` for all `q`? YES or NO, reason in one line.

---
## 1 · THE OBJECTS
- `q = 3^v`; `S_N := F_3[x_0..x_{N−1}]`; `e_j` = elementary symmetric of degree `j`.
- **`I^{(N)} := (e_1, e_3, e_5, …) + (x_0^q, …, x_{N−1}^q)`**; `A(N) := dim S_N/I^{(N)}`; `A_k := A(2k+2)`, `A'_k := A(2k+1)`.
- **`Z_N := {x ∈ F_q^N : the multiset {x_i} is closed under negation}`**; `P_k := |Z_{2k+2}|`, `P'_k := |Z_{2k+1}|`.
- **`D(k)`: `A_k = P_k`**; **`D'(k)`: `A'_k = P'_k`**. The conjecture is `D(k)` for all `k`, `q`.
- **Slices.** `V_1 := {y ∈ F_q^{2k+1} : (y,1) ∈ Z_{2k+2}}`, `N_k := |V_1|`; `V'_1 := {y ∈ F_q^{2k} : (y,1) ∈ Z_{2k+1}}`, `N'_k := |V'_1|`.
- **`gr 𝔞`** = ideal of top forms. For finite `X`, `I(X)` = vanishing ideal over `F_q`; `gr I(X)` has colength `|X|`.
- **Monomial ideals.** `M^{(j)}(V) := (x_C·x_A^{q−1} : A, B, C a partition of V, |A| = |B| = j)` (`B` does not appear; it fixes `|C|`). `M_k := Σ_{j=1}^{k} M^{(j)}({0..2k})` in `S_{2k+1}`; `M'_k := Σ_{j=1}^{min(2,k−1)} M^{(j)}({0..2k−1})` in `S_{2k}`.
- **The casillas.** **`K_k := I^{(2k+1)} + M_k`** (in `S_{2k+1}`, even side) and **`K'_k := I^{(2k)} + (x_0x_1⋯x_{2k−1}) + M'_k`** (in `S_{2k}`, odd side).
- **Rows.** `z` := last variable (`x_{2k}` for `K_k`, `x_{2k−1}` for `K'_k`), `π_z : z ↦ 0`, `S'` the ring without `z`. **Row `a`** of `K` is `π_z(K : z^a)`; rows increase with `a`, and `dim S/K = Σ_{a<q} dim S'/π_z(K : z^a)` (because `z^q ∈ K`).
- **Fibres.** Even: `W_v := {y ∈ F_q^{2k} : y ∪ {v, 1} closed under negation}`; `V_1 = ⨆_v W_v × {v}`. Odd: `W'_v := {y ∈ F_q^{2k−1} : y ∪ {v, 1} closed}`; `V'_1 = ⨆_v W'_v × {v}`. Dictionary: row `a = 0 ↔ v = −1`, `a = 1 ↔ v = 0`, `2 ≤ a ≤ q−2 ↔ v` generic (`∉ {0, ±1}`), `a = q−1 ↔ v = +1`.
  - Identifications: **`W_{−1} = Z_{2k}`, `W_0 = V'_1`; `W'_{−1} = Z_{2k−1}`, `W'_0 = V_1^{(k−1)}`** (the even slice one level down).
  - **Fibre sizes (auditor, exact, gated):** with `h = (q−1)/2`, `I_m(2t) := Σ_a t^{2a+m}/(a!(a+m)!)`, `n` = number of coordinates (`2k` even side, `2k−1` odd side), and `E(t) = cosh t` if `n` is even, `sinh t` if odd, `Ē` the other one:
    `|W_gen| = n!·[t^n] E·I_1²·I_0^{h−2}`, `|W_0| = n!·[t^n] Ē·I_1·I_0^{h−1}`, `|W_{+1}| = n!·[t^n] E·I_2·I_0^{h−1}`, `|W_{−1}| = n!·[t^n] E·I_0^h`.
    Gates: even `(2,9)`: `217, 88, 84, 46` (sum with `(q−3)×` generic: `855 = N_2`); `(3,9)`: `7761, 4266, 3930, 2340`; `(4,9)`: `345465, 227144, 204456, 130984` (`N_4 = 1 930 329`). Odd `(3,9)`: `921, 855, 380, 210`; `(4,9)`: `41889, 37947, 22302, 13496` (`N'_4 = 227 144`).

## 2 · WHAT IS PROVED (theorems; use them, do not re-prove them)
1. **Floor:** `I^{(N)} ⊆ gr I(Z_N)`; `A(N) ≥ |Z_N|`.
2. **Points:** `P_k = P'_k + (q−1)N_k`, `P'_k = P_{k−1} + (q−1)N'_k`.
3. **Chain.** Odd step: `D(k−1) + (P_k) + (DO_k) ⟹ D'(k)`; even step: `D'(k) + (DE_k) ⟹ D(k)`, where **`(DO_k)`: `dim S_{2k}/K'_k ≤ N'_k`** and **`(DE_k)`: `dim S_{2k+1}/K_k ≤ N_k`** (equivalently `gr I(V'_1) ⊆ K'_k`, `gr I(V_1) ⊆ K_k`).
4. **Known levels, all `q`:** `D(1)`, `D'(1)`, `D'(2)`, `D(2)`, `D(3)` (the last two: external theorems, the Sofá and the Hamaca); `D(k)` for all `k` at `q = 3`; `(DO_2)`.
5. **`(P_k)` FOR ALL `k` AND ALL `q`** (INFORME_6 STEP 1, explicit certificate, auditor-verified at `q = 3, 9, 27, 81`). **So the chain at level `k` needs ONLY `(DO_k)` and `(DE_k)`. Row `k = 4` needs exactly `(DO_4)` and `(DE_4)`.**
6. **Row 0 is free:** row 0 of `K_k` equals `I^{(2k)} = gr I(Z_{2k})`, colength `|W_{−1}|` (given `D(k−1)`); row 0 of `K'_k` equals `I^{(2k−1)}`, colength `|W'_{−1}|` (given `D'(k−1)`).
7. **Row 1, even side:** row 1 of `K_k` contains `K'_k` (`z·x_0⋯x_{2k−1} = e_{2k+1}`), so given `(DO_k)` its colength is `≤ N'_k = |W_0|`.
8. **What `(DE_k)`, `(DO_k)` reduce to (counting):** `(DE_k)` ⟺ `Σ_a dim S'/row_a(K_k) ≤ Σ_v |W_v|`. With rows 0, 1 settled, **`(DE_k)` ⟸ [generic row of `K_k` has colength `≤ |W_gen|`] ∧ [row `q−1` of `K_k` has colength `≤ |W_{+1}|`]** (all generic rows are equal in every cell measured; since rows increase with `a`, it suffices to bound row 2). Odd side the same with `K'_k`, `W'` — plus row 1 of `K'_k`, which must reach `|W'_0| = N_{k−1}`.
   **To bound a row, EXHIBIT an explicit ideal `R` inside it and COUNT `dim S'/R`.** There is no free reverse inclusion (INFORME_6 STEP 0.3: rows ⊄ fibres in general, three-point counterexample).
9. **G-a FOR ALL `q`** (INFORME_6 §2.5): `x_4²x_0²x_1^{q−2} ∈ K_2 + (x_4³)`; with INFORME_1's count, **every row of `K_2` is exact for all `q`**; generic row `= (e_1, e_3, e_4) + box_q + (x_i²x_j^{q−2})`, colength `12(q−2)`.
10. **Reduction lemma (INFORME_5 §2.8), all `k`, `q`:** the even generic row's candidate elements are governed by **(G-a_k): `z²·x_l²·x_j^{q−2}·e_{2k−4}(x'∖x_l) ∈ K_k + (z³)`** (`x'` = the `2k` non-`z` variables, `l ≠ j`); first member = G-a.
11. **Lemma H (INFORME_6 §2.3), at every level, in chain order.** If `f ∈ I(W_0)` has degree `d` and `f = t + s + r` (`t` homogeneous of degree `d`, `s` of degree `d−1`, `deg r ≤ d−2`), then **`z·t + z²·s ∈ gr I(Z_N) + (z³)`**, because the fibre of `Z_N` over `z = w ≠ 0` is `w·W_0` and `z·f^h` is homogeneous and vanishes on `Z_N`.
    - Even side (`N = 2k+1`, `W_0 = V'_1^{(k)}`): uses `D'(k)`, available when `(DE_k)` is needed.
    - Odd side (`N = 2k`, `W'_0 = V_1^{(k−1)}`): uses `D(k−1)`, available when `(DO_k)` is needed.
    **This is the engine: function identities of low degree on the row-1 fibre become elements of row 2.**
12. **Elimination (INFORME_6 §2.1):** on `V_1`, `z = −1 − e_1(y)`; `gr I(V_1) = (e_1(y,z)) + gr I(U)`, `U = ⨆ W_v`; the fibres are level sets of `e_1`.
13. **Measured, all audited:**
    - generic rows at `(3,9)`: even colength `3930 = |W_gen|`, odd `380 = |W'_gen|`; `(DO_3)` at `q = 9`;
    - even generic row `= K'_k + π_z(M_k : z²) + (G-a_k family)` at `(2,9)`, `(2,27)`, `(3,9)`; the sum of colons alone gives only `N'_k`;
    - odd row 1 of `K'_3` at `(3,9)`: equals the sum of colons `π_z(I^{(6)} : z) + π_z(M'_3 : z²) + (e_5)` (on `x_0..x_4`), colength `855 = |W'_0| = N_2` — row 1 of the odd side may be free in general: check it first;
    - odd generic row of `K'_3` at `(3,9)`: 7 generators beyond the sum of colons, degrees `4, 5, q+1` (×5): the quintic `y_4³(h_2(y_1,y_2,y_3) + y_4e_1(y_1,y_2,y_3))`, a quartic in `y_1..y_4`, the monomial `y_3³y_4^{q−2}`, `y_4^{q−2}e_3(y_1..y_4)`, `y_3^{q−2}e_3(y_1..y_4)`, `y_4^{q−2}(y_2y_3(y_2+y_3) + y_4h_2(y_2,y_3))`;
    - **the G-a mechanism at `(3,9)`:** `(K_3 + (z³)) : x_1^{q−2}` has minimal generators of degrees `1, 2, 3, 3, 5, 5, 6 (×8)`, then `9, 11, 12`; the (G-a_3) target `z²x_0²e_2(x_1..x_5)` lies in the ideal of the 14 generators of degree `≤ 8` alone.

## 3 · (L2), exactly — THE TARGET
**Only `q ≥ 9` matters:** `D(k)` is known for all `k` at `q = 3`, and at `q = 3` there are no generic rows. Every statement below is for `q = 3^v ≥ 9`, with `q` as a letter.

> **(L2) at level `k`:** the generic and `+1` rows of `K_k` and of `K'_k` have colength at most the corresponding fibre size, and row 1 of `K'_k` has colength at most `N_{k−1}`.

**THE G-a METHOD (INFORME_6 §2.2–2.5), which is how G-a fell after six turns — generalise it:**
1. **Colon with a `q`-free core.** For the target element `z²·x_l²·x_j^{q−2}·Φ` (or any row element with a factor `x_j^{q−2}`), work in the colon `(K + (z³)) : x_j^{q−2}`. Its low-degree part is `q`-free (same at `q = 9, 27` at `k = 2`). Write the target as a `q`-free combination of a few low-degree generators.
2. **Each generator times `x_j^{q−2}` is in `K + (z³)`** by one of: an identity in `(e_1, e_3, …)`; a monomial of `M_k`; or **Lemma H** applied to an `f ∈ I(W_0)`.
3. **The needed `f` are FUNCTION IDENTITIES on the row-1 fibre `W_0`, of degree `≤ q−1`**, in which `x^{q−2}` acts as `1/x` on nonzero values. At `k = 2` there were three, `(F3)`–`(F5)` (INFORME_6 §2.4), each proved by splitting into the cases of the coordinate values.
   **At level `k`, `W_0` is a union of pieces `{y_i = −1, y_j = 0} × Z_{2k−2}`**, so the case split is uniform in `k`: the other `2k−2` coordinates only enter through `Z_{2k−2}`, whose functions are controlled by `D(k−2)`.

**Where to look for the `k`-general form.**
- The certificates are `q`-free and the pieces are uniform in `k` ⟹ **aim for ONE certificate with `k` as a letter**, whose ingredients are the elementary symmetric functions of the `2k−2` «passive» coordinates.
- G-a at `k = 2` has `e_0 = 1` where (G-a_k) has `e_{2k−4}`: the passive coordinates enter through `e_{2k−4}`, which is a function on `Z_{2k−2}`.
- The counts are EXACT and in closed form (§1).
- Counting an explicit row ideal `R` can itself go by rows along the next variable. The tablero repeats one level down: measured 12/12 at `(2,3)`, `(2,9)`.

## 4 · PROCESS
- **STEP 0 — Reading and design (15 min, no runs).** Read `INFORME_6.md` §2 in full. Write the `k`-general version of the three ingredients as a PLAN: the target elements for each of the four rows at level `k`, the candidate `q`-free core, and the shape of the function identities on `W_0`.
- **STEP 1 — Even generic row for every `k` (60 min).**
  - (G-a_k) by the G-a method with `k` as a letter.
  - Then the count: the colength of `K'_k + π_z(M_k : z²) + (G-a_k family)` is `≤ |W_gen|`, or any other explicit ideal inside the row that reaches `|W_gen|`.
  - Gates: `(2,9)`, `(2,27)`, `(3,9)`; the new `(3,27)` degree-≤ 8 core, to test `q`-independence at `k = 3`.
- **STEP 2 — The `+1` rows and the odd side for every `k` (60 min).**
  - Even `+1` row: find its interaction elements at `(2,9)` and `(3,9)` — at `k = 2` it has colength 46 — then the `k`-general form.
  - Odd rows 1, generic and `+1` of `K'_k`: the same method with odd Lemma H (`W'_0 = V_1^{(k−1)}`, uses `D(k−1)`). The `(3,9)` generators of §2.13 are your gate.
  - If STEP 1 and STEP 2 close, write in large letters **«CONJECTURE 1.2 CLOSED»**.
- **STEP 3 — Row `k = 4` (30 min, only if STEP 2 did not close for all `k`).**
  - Specialise the proved statements to `k = 4`; prove `(DO_4)` and `(DE_4)`.
  - Numeric targets at `q = 9`: generic `204456`, `+1` `130984` (even); generic `22302`, `+1` `13496`, row 1 `37947` (odd). These are targets for the COUNT, not cells to compute.
  - If they close: **«D(4) FOR ALL q»**.
- **Sanity check before any count:** `|W_{−1}| + |W_0| + (q−3)|W_gen| + |W_{+1}| = N_k` (and the same odd, `= N'_k`); the gates in §1 satisfy it.
- **STEP 4 — Verdict (15 min).** Apply the chain to what is proved.

## 5 · DEAD ROUTES (do not retry)
- «rows ⊆ fibres» as a formal consequence of `K ⊆ gr I(V_1)` (false, three points).
- Vanishing arguments for the generic rows: they reach only the `+1` row of `gr I(V_1)`, not of `K`.
- The sum of colons for the generic rows (gives only `N'_k`).
- «G-a times a variable» as the `k = 3` element.
- `x_j^{q−2}e_{2k−2}` of all `2k` variables (lies in the sum of colons).
- The circular «reduction to row 1» (`z·K'_k ⊄ K_k`).
- The naive lifting `x_ax_b·I^{(m)} ⊆ I^{(m+2)}`; the shear lever; the transfer argument for G-a.
- The naive colon guess `(x_1², g_3, g_5, ε_1³, x_1β_{ii'}x_ix_{i'})` for G-a (coprimality).
- Measuring cells as a substitute for a mechanism: cells are gates only.

## 6 · SUCCESS
- **Full:** (L2) for all `k` ⟹ **CONJECTURE 1.2 CLOSED** (with §2.5, the chain runs at every level).
- **Row:** `(DO_4)` + `(DE_4)` for all `q` ⟹ **D(4) FOR ALL q**, the first new row of the conjecture.
- **Partial, declared as such:** (G-a_k) for all `k`; the even generic row for all `k`; any row inclusion for all `k`; (G-a_3) for all `q`.

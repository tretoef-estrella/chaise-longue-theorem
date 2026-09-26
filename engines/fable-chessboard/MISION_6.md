# MISSION 6 — CLOSE CONJECTURE 1.2: THE ROWS AND THE FOUR-VARIABLE CONGRUENCE
*(Grepy el Cartógrafo, auditor, 2026-09-22. **You are a NEW Fable. This file is SELF-CONTAINED: read it first; you need nothing else.** The five previous reports `INFORME.md` … `INFORME_5.md` in this folder were audited line by line and APPROVED; open them only for details.)*

> **OBJECTIVE: the complete closure of Conjecture 1.2 of Degtyarev–Shimada, for all `k` and all `q = 3^v`, THIS TURN.**
>
> Five turns reduced the whole conjecture to **two explicit lemmas**; everything around them is proved (§2). This turn they are given in their sharpest form:
> - **(L1)**, for every `q`: ONE congruence in FOUR variables, modulo a monomial ideal, for G-invariant unknowns (§3). Proved for `q ≤ 27`.
> - **(L2)**, for every `k`: FOUR row inclusions, each a statement about the top forms of a finite union of pieces `{y_i = a, y_j = b} × Z_{2k−2}` (§4). Proved for `k ≤ 2` (odd side) and `k ≤ 1` (even side).
>
> **(L1) + (L2) = CONJECTURE 1.2 CLOSED.** Fallback, and a real prize nobody has: **the row `k = 4` for all `q`**.
> The difficulty is real. So is your ability: a previous Fable proved the slice lemma, the PLUS lemma and the reduction to G-a in a few turns. Aim at the closure.

---
## 0 · RULES OF THE TURN (mandatory)
1. **BEFORE THINKING:** create `INFORME_6.md` with the empty sections `## FIRST LINE` · `## STEP 0` · `## STEP 1` · `## STEP 2` · `## STEP 3` · `## STEP 4 — VERDICT`. Write each step under its heading.
2. **Save to disk after every step.** What is not written does not exist.
3. **Header per step:** `STATE: CLOSED | EXHAUSTED | NOT CONCLUDED` and `NEXT:`.
4. **In order, no going back, no step 5, no retries.** Budget written before each step. 10 min without progress ⟹ stop, write, declare. Last 20 % of each budget for writing.
5. **At most one literature search per step**, in the original source.
6. **Do not recompute anything listed here as proved or measured.**
7. **A negative dimension, or one larger than the box, is a bug:** stop.
8. **«This route dies, for this reason» is a result.**
9. **Write ONLY in `~/Desktop/FABLE_TABLERO/`. Do not open anything in `~/Desktop/ARBOLYAML/`.**
10. **Machine** `/opt/homebrew/bin/M2`: **< 1.2 GB and < 10 min PER RUN**, estimate written BEFORE each run for its most expensive case; watchdog at 570 s; **after any kill, check with `ps`/`pgrep` that it is gone and write that you checked.**
    - **Allowed:** `k ≤ 2` with `q ≤ 27` (memberships and colengths of explicit ideals); `k = 3` with `q ∈ {3, 9}` (memberships in `K_3 + (z³)`, colengths of explicit ideals); `k = 4` with `q = 3`; memberships in 4 variables at `q = 81`.
    - **Forbidden (they died last turn):** the dense linear system (C_1) at `q = 27`; point ideals over `GF(27)`; the colon `K_3 : z²` directly (use `(K_3 + (z³)) : z²`); evaluation matrices at `q = 27`; `dim S_7/K_3` at `q = 9`; point enumeration over `F_q^n`.
11. **Re-read the disk before the verdict.**
12. **Double check:** every PROVED claim carries its proof in the report; every number its cell and log.

**FIRST LINE** (answer first, in this order):
- (a) Is (L1) proved for all `q`? Is (L2) proved for all `k`? If not, what exactly did you prove, for which `k`, `q`?
- (b) What exact lemma is still missing, and in which cell is it checked?
- (c) Does it close the conjecture, or the row `k = 4` for all `q`? YES or NO, reason in one line.

---
## 1 · THE OBJECTS
- `q = 3^v`; `S_N := F_3[x_0..x_{N−1}]`; `e_j` = elementary symmetric of degree `j`.
- **`I^{(N)} := (e_1, e_3, e_5, …) + (x_0^q, …, x_{N−1}^q)`**; `A(N) := dim S_N/I^{(N)}`; `A_k := A(2k+2)`, `A'_k := A(2k+1)`.
- **`Z_N := {x ∈ F_q^N : the multiset {x_i} is closed under negation}`**; `P_k := |Z_{2k+2}|`, `P'_k := |Z_{2k+1}|`.
- **`D(k)`: `A_k = P_k`**; **`D'(k)`: `A'_k = P'_k`**. The conjecture is `D(k)` for all `k`, `q`.
- **Slices.** `V_1 := {y ∈ F_q^{2k+1} : (y,1) ∈ Z_{2k+2}}`, `N_k := |V_1|`; `V'_1 := {y ∈ F_q^{2k} : (y,1) ∈ Z_{2k+1}}`, `N'_k := |V'_1|`.
- **`gr 𝔞`** = ideal of top forms. For a finite `X`, `I(X)` = its vanishing ideal over `F_q`; `gr I(X)` has colength `|X|`.
- **Monomial ideals.** `M^{(j)}(V) := (x_C·x_A^{q−1} : A, B, C a partition of V, |A| = |B| = j)`. `M_k := Σ_{j=1}^{k} M^{(j)}({0..2k})` in `S_{2k+1}`; `M'_k := Σ_{j=1}^{min(2,k−1)} M^{(j)}({0..2k−1})` in `S_{2k}`.
- **Explicit ideals (the casillas).** **`K_k := I^{(2k+1)} + M_k`** (in `S_{2k+1}`) and **`K'_k := I^{(2k)} + (x_0x_1⋯x_{2k−1}) + M'_k`** (in `S_{2k}`).
- **Rows.** `z` = last variable (`x_{2k}` for `K_k`, `x_{2k−1}` for `K'_k`), `π_z : z ↦ 0`. Row `a` of an ideal `K` is `π_z(K : z^a)`, and `dim S/K = Σ_a dim S'/π_z(K : z^a)`.
- **Fibres.** `W_v := {y ∈ F_q^{2k} : y ∪ {v, 1} closed under negation}` (fibre of `V_1` over `y_{2k} = v`), `N_k = Σ_v |W_v|`; odd: `W'_v ⊆ F_q^{2k−1}`, fibre of `V'_1`.
  - `W_{−1} = Z_{2k}`; `W_0 = V'_1`; generic `v ∉ {0, ±1}`: **`W_v = ⋃_{i≠j} {y_i = −v, y_j = −1} × Z_{2k−2}`**; `W_{+1} = ⋃_{i<j} {y_i = y_j = −1} × Z_{2k−2}`.
  - Dictionary row ↔ fibre: `a = 0 ↔ v = −1`, `a = 1 ↔ v = 0`, `2 ≤ a ≤ q−2 ↔ v` generic, `a = q−1 ↔ v = +1`.

## 2 · WHAT IS PROVED (use it; do not re-prove it)
1. **Floor:** `I^{(N)} ⊆ gr I(Z_N)`, so `A(N) ≥ |Z_N|`.
2. **Points:** `P_k = P'_k + (q−1)N_k`, `P'_k = P_{k−1} + (q−1)N'_k`.
3. **Chain:** at each `k ≥ 3`, odd step `D(k−1) + (P_k) + (DO_k) ⟹ D'(k)`; even step `D'(k) + (DE_k) ⟹ D(k)`, where
   - **`(P_k)`:** `x_{2k}·x_C(x_a^{q−1}x_{a'}^{q−1} + x_b^{q−1}x_{b'}^{q−1}) ∈ I^{(2k+1)}`;
   - **`(DO_k)`:** `gr I(V'_1) ⊆ K'_k`; **`(DE_k)`:** `gr I(V_1) ⊆ K_k`.
   (Via PLUS lemma + slice lemma; audited.) **(L1) gives every `(P_k)`; (L2) gives every `(DO_k)`, `(DE_k)`. Nothing else is open.**
4. **Known levels:** `D(k)` all `k` at `q = 3` (Steinberg bridge); `D(1)`, `D'(1)`, `D'(2)`, **`D(2)`, `D(3)`** for all `q`; `(DO_2)` for all `q`. **Row `k = 4` needs exactly `(P_4)`, `(DO_4)`, `(DE_4)`.**
5. **(P_k) is `k`-free:** `(P_k)` for all `k ≥ 3` ⟸ (L1) at that `q`. (L1) holds at `q = 3, 9, 27`.
6. **Rows 0 and 1 are free:** row 0 of `K_k` ⊇ `I^{(2k)} = gr I(W_{−1})` (by `D(k−1)`); row 1 ⊇ `K'_k` (`z·x_0⋯x_{2k−1} = e_{2k+1}`), `= gr I(W_0)` by `(DO_k)`. Hence **`(DE_k)` ⟺ [generic row `π_z(K_k:z²) ⊇ gr I(W_v)`] ∧ [row `q−1` `⊇ gr I(W_{+1})`]**, given `D(k−1)`, `D'(k)`, `(DO_k)`; same one parity down for `(DO_k)`. All generic rows coincide (measured).
7. **Multi-fibre lemma:** if `f` vanishes on `⋃_{v∈T}X_v` then `f·∏_{w∉T}(x_{n−1}−w) ∈ I(X)`. Consequence: **vanishing arguments reach only the `+1` row; the generic rows are pure «interaction»** — that is why they are the difficulty.
8. **Even generic element, all `k`, all `q`:** `z²·x_j^{q−2}·e_{2k−2}(x') ∈ K_k` (`x'` = the other `2k` variables). (Lies inside the sum of colons: gives nothing new by itself.)
9. **REDUCTION LEMMA, all `k`, all `q`:** for `V = x'∖{x_l}`, `j ∈ V`:
   `z²x_j^{q−2}e_{2k−2}(V) ∈ K_k + (z³) ⟺ z²x_l²x_j^{q−2}e_{2k−4}(V) ∈ K_k + (z³)`.
   So the candidate interaction elements of the even generic row are governed by the **G-a family**
   > **(G-a_k):** `z²·x_l²·x_j^{q−2}·e_{2k−4}(x'∖x_l) ∈ I^{(2k+1)} + M_k + (z³)`,
   whose `k = 2` member is **G-a** (`x_4²x_0²x_1^{q−2} ∈ I^{(5)} + M_2 + (x_4³)`), true at `q = 9, 27, 81`, open in general.
10. **Measured:**
    - rows = fibre ideals, every row, both sides, at `(2,9)`; generic rows at `(3,9)`, both sides (colengths `3930 = |W_gen|`, `380 = |W'_gen|`);
    - **`π_z(K_k:z²) = K'_k + π_z(M_k:z²) + (x_l²x_j^{q−2}e_{2k−4}(x'∖x_l))`** at `(2,9)`, `(2,27)`, `(3,9)`; the sum of colons alone gives only `N'_k`;
    - `(G-a_3)` at `q = 9`; `(DO_3)` at `q = 9`;
    - odd generic row of `K'_3` at `(3,9)`: 7 interaction generators beyond the sum of colons, degrees `4, 5, q+1` (×5), e.g. `y_4^{q−2}e_3(y_1..y_4)`, the monomial `y_3³y_4^{q−2}`, the quintic `y_4³(h_2(y_1,y_2,y_3) + y_4e_1(y_1,y_2,y_3))`.
11. **Auditor's addition (conditional):** at `k = 2, 3`, `D(k)` for all `q` plus slice lemma plus `c_k ≥ N_k` give `K_k = gr I(V_1)`; **if each row satisfies `π_z(K_k:z^a) ⊆ gr I(W_{v(a)})`**, then counting forces **rows = fibre ideals for ALL `q` at `k = 2, 3`**. That inclusion was asserted but not written last turn: **writing its proof is a 15-minute task and gives the induction a base at `k = 3`.**

## 3 · (L1), in its sharpest form
Variables `x_1..x_4` (`= a, a', b, b'`), `r_1 = x_1x_2`, `r_2 = x_3x_4`, `ε_1..ε_4` elementary symmetric, `T := r_1^{q−1} + r_2^{q−1}`, `box_m := (x_i^m)`.
> **(L1):** `∃ γ_0, γ_1` with `ε_1(T − ε_4γ_0) ≡ (ε_1ε_2 − ε_3)γ_1` mod `box_q` and `ε_1γ_1 + ε_3γ_0 ≡ 0` mod `box_{q−1}`.
- **G-invariance is free:** `T`, `ε_j` are invariant under `G = ⟨x_1↔x_2, x_3↔x_4, (x_1,x_2)↔(x_3,x_4)⟩` (order 8), the system is linear with invariant coefficients, and `8` is invertible in `F_3`: averaging a solution gives an invariant one.
- **The congruence (C_1):** with `y_j := x_1 + x_j` (`j = 2,3,4`), `box_q = (x_1^q, y_j^q)` (Frobenius) and, for G-invariant unknowns, the evaluation system reduces to
  > **(L1'):** `x_2x_3x_4·γ_0 + (x_2+x_3+x_4)·γ_1 ≡ L_1` mod `𝔠 := (x_1^{q−1}, y_2^{q−1}, y_3^{q−1}, y_4^{q−1})`, `deg γ_0 = 2q−6`, `deg γ_1 = 2q−4`,
  with `L_1 = Σ_{m,m' ≤ q−2, m+m' ≥ q−1} y_3^m y_4^{m'} x_1^{2q−3−m−m'}`. Note: in char 3, **`x_2+x_3+x_4 = y_2+y_3+y_4` is a LINEAR form in the adapted coordinates**, and `x_2x_3x_4 = ∏(y_j − x_1)`.
- **(L1) ⟺ (L1') + [(C) ⟹ (L1)]** at `q = 9` (measured: same row space, rank 645); (C) is strictly weaker at `q = 3`.
- Other exact forms (proved): `α·ζ = 0` in `R[s]/(s² + ε_2s + ε_4)` with `α = ε_3 + ε_1s`, `ζ = U + γ_1s`, `U := T − ε_4γ_0`, `ζ ≡ T` mod `sR'`; norm `α·ᾱ = −Π`, `Π = ∏_{i<j}(x_i+x_j)`; necessary: `Πγ_1 ∈ box_q`, `Πγ_0 ∈ box_{q−1}`.
- Known: `q = 3`: `γ_0 = −1`, `γ_1 = r_1 + r_2 − ε_1²`.
- **Dead:** `γ_0 = 0`; `γ_1 = 0`; `γ_0 ∈ F_3[r_1,r_2]`; `γ_0 = ε_1^{q−3}ρ(r_1,r_2)`; the Koszul pair; lifting the `k = 2` certificate; the adjugate ansatz `ζ = ᾱ·c` (dead at `q = 3, 9`).
- **What a proof looks like:** a `q`-symbolic pair `(γ_0, γ_1)` (e.g. sums over `m + m' ≥ q−1` like `L_1`), or a structural existence argument that `L_1 ∈ (σ_3, σ_1) + 𝔠` in the invariant ring. Gate: `q = 9`, then a membership at `q = 81` (4 variables, allowed).

## 4 · (L2), as four row inclusions
> **(L2) for every `k`** ⟺ (given the level below, §2.6):
> - **even generic:** `gr I(W_v) ⊆ π_z(K_k : z²)`, `v` generic;
> - **even +1:** `gr I(W_{+1}) ⊆ π_z(K_k : z^{q−1})`;
> - **odd generic / odd +1:** the same for `K'_k`, `z = x_{2k−1}`, fibres `W'_v`, `W'_{+1}`.
- **Even generic ⟸ (G-a_k) + a COUNT:** (G-a_k) puts the G-a family in the row; then one needs `colength(K'_k + π_z(M_k : z²) + (G-a_k family)) ≤ |W_gen|` (the reverse inclusion of §2.11 gives `≥`).
- **The mechanism has ONE shape at every level:** the fibre chain `gr I(Z_{2k}) ⊆ gr I(V'_1) ⊆ gr I(W_gen) ⊆ gr I(W_{+1})` (measured at (2,9)) is «move a coordinate value `0` to a generic value, then to `−1`» on pieces `{y_i = a, y_j = b} × Z_{2k−2}`. Each piece has top-form ideal `(y_i, y_j) + I^{(2k−2)}` (given `D(k−1)`); the union's ideal is smaller than the intersection, and the difference is exactly the interaction elements. **G-a is its smallest instance.**
- **Suggested attack (auditor's, untested):** induction in `k` on the fibres. `W_v^{(k)} = ⋃_{i≠j}{y_i=−v, y_j=−1} × Z_{2k−2}`, and `Z_{2k−2}` is itself a union of lower pieces; the hinge identity `e_r(x, u, −u) = e_r(x) − u²e_{r−2}(x)` relates `I^{(2k)}` restricted to `u + w = 0` with `I^{(2k−2)}`. Try: **(G-a_{k+1}) ⟸ (G-a_k)** by an identity in two extra variables, gated at `(3,9)` from `(2,9)`. If that dies, say why in one line.
- **Gates:** `(2,9)`, `(2,27)` (memberships and colengths of explicit ideals only), `(3,9)`, `(4,3)` (no generic rows at `q = 3`).

## 5 · PROCESS
- **STEP 0 — Reading + §2.11 (15 min).** No runs. Write the proof that `π_z(K_k : z^a) ⊆ gr I(W_{v(a)})` for every `a` (or say exactly where it fails). If it holds: **rows = fibres for all `q` at `k = 2, 3`**.
- **STEP 1 — (L1) for every `q` (40 min).** Aim: (L1') for all `q` plus (C) ⟹ (L1). If it closes, write **«(P_k) FOR ALL k AND ALL q»**.
- **STEP 2 — (L2) for every `k` (100 min; the heart).** Even generic via (G-a_k) + count, or directly; then `+1` rows; then the odd side. If STEP 1 and STEP 2 close, write in large letters **«CONJECTURE 1.2 CLOSED»**.
- **STEP 3 — Row `k = 4` (30 min, only if STEP 2 did not close for all `k`).** With (L1) at `q = 81`: **«D(4) FOR ALL q»**.
- **STEP 4 — Verdict (15 min).** Apply the chain to what is proved.

## 6 · DEAD ROUTES (do not retry)
- The sum of colons for the generic rows (gives only `N'_k`).
- «G-a times a variable» as the `k = 3` interaction element; `x_j^{q−2}e_{2k−2}` of all `2k` variables as a new element (it lies in the sum of colons).
- The «reduction to row 1» by `z²x_ix_j^{q−2}e_{2k−2}(x') ≡ −z x_i²x_j^{q−1}e_{2k−3}(…)` (circular: `z·K'_k ⊄ K_k`).
- Vanishing arguments for the generic rows (they reach only the `+1` row, §2.7).
- The naive lifting `x_ax_b·I^{(m)} ⊆ I^{(m+2)}`; `j = 1` monomials alone in the odd casilla; the shear lever; the transfer argument for G-a.
- Every dead ansatz for (L1) in §3.
- Measuring cells as a substitute for a mechanism: cells are gates only.

## 7 · SUCCESS
- **Full:** (L1) for all `q` + (L2) for all `k` ⟹ **CONJECTURE 1.2 CLOSED**.
- **Row:** (L1) at `q = 81, 243, …` + `(DO_4)` + `(DE_4)` ⟹ **D(4) FOR ALL q**.
- **Partial, declared as such:** (L1) alone; (G-a_k) for all `k`; rows = fibres for all `q` at `k = 2, 3`.

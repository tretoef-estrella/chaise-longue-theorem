# MISSION 5 «TWO LEMMAS» — CLOSE CONJECTURE 1.2 FOR ALL k AND ALL q
*(Grepy el Cartógrafo, auditor, 2026-09-22. **SELF-CONTAINED: read this file first; you need nothing else.** Your INFORME_2, INFORME_3 and INFORME_4 are in this folder and were audited line by line and APPROVED; open them only for details.)*

> **OBJECTIVE: the complete closure of Conjecture 1.2 of Degtyarev–Shimada for all `k` and all `q = 3^v`, THIS TURN.**
>
> After your four turns, **the whole conjecture stands on exactly TWO explicit lemmas**, and everything around them is proved (§2):
> - **(L1)**, for every `q = 3^v`: a system in FOUR variables (§3). It is proved for `q ≤ 27`.
> - **(L2)**, for every `k`: every top form of a polynomial vanishing on the slice lies in an explicit ideal (§4). It is proved for `k ≤ 2` (odd side) and `k ≤ 1` (even side).
>
> **(L1) + (L2) = CONJECTURE 1.2 CLOSED.**
> **Fallback, and it is a real prize:** (L1) at `q ≥ 81` + (L2) at `k = 4` = **the row `k = 4` for all `q`**, which nobody has.

---
## 0 · RULES OF THE TURN (mandatory)
1. **BEFORE THINKING:** create `INFORME_5.md` with the empty sections `## FIRST LINE` · `## STEP 0` · `## STEP 1` · `## STEP 2` · `## STEP 3` · `## STEP 4 — VERDICT`. Write each step under its heading.
2. **Save to disk after every step.** What is not written does not exist. If the session is cut, what is on disk is the delivery.
3. **Header per step:** `STATE: CLOSED | EXHAUSTED | NOT CONCLUDED` and `NEXT:`.
4. **In order, no going back, no step 5, no retries.** Write a budget before each step. 10 min without real progress ⟹ stop, write, declare. The last 20 % of each budget is for writing.
5. **At most one literature search per step**, in the original source.
6. **Do not recompute anything listed here as proved or measured.**
7. **A negative dimension, or one larger than the box, is a bug:** stop.
8. **«This route dies, for this reason» is a result.**
9. **Write ONLY in `~/Desktop/FABLE_TABLERO/`. Do not open anything in `~/Desktop/ARBOLYAML/`.**
10. **Machine** `/opt/homebrew/bin/M2`: **< 1.2 GB and < 10 min PER RUN, estimate written BEFORE each run, for the most expensive case in the run.**
    - **After killing a run, check with `ps` that it is gone, and write that you checked.** (Last turn `z5.m2` was declared killed and was still running 20 minutes later; the auditor stopped it.)
    - No point-by-point enumeration loops over `F_q^n` in M2.
    - Allowed cells: `k ≤ 2` with `q ≤ 27`; `k = 3` with `q ∈ {3, 9}`; `k = 4` with `q = 3`; memberships in `≤ 5` variables at `q = 81` (no colon). Anything else: do not run it.
11. **Re-read the disk before the verdict.**
12. **Double check:** every claim promoted to PROVED carries its proof in the report; every number carries its cell and its log.

**FIRST LINE** (answer first, in this order):
- (a) Is (L1) proved for all `q`? Is (L2) proved for all `k`? If not, what did you prove, for which `k` and `q`?
- (b) What exact lemma is missing, and in which cell is it checked?
- (c) Does it close the conjecture, or the row `k = 4` for all `q`? YES or NO, with the reason in one line.

---
## 1 · THE OBJECTS
- `q = 3^v`; `S_N := F_3[x_0..x_{N−1}]`; `e_j` = elementary symmetric polynomial of degree `j`.
- **`I^{(N)} := (e_1, e_3, e_5, …) + (x_0^q, …, x_{N−1}^q)`**; `A(N) := dim S_N/I^{(N)}`; `A_k := A(2k+2)`, `A'_k := A(2k+1)`.
- **`Z_N := {x ∈ F_q^N : the multiset {x_i} is closed under negation}`**; `P_k := |Z_{2k+2}|`, `P'_k := |Z_{2k+1}|`.
- **`D(k)`: `A_k = P_k`.** **`D'(k)`: `A'_k = P'_k`.** The conjecture is `D(k)` for all `k`, `q`.
- **Slices.** `V_1 := {y ∈ F_q^{2k+1} : (y,1) ∈ Z_{2k+2}}`, `N_k := |V_1|`; `V'_1 := {y ∈ F_q^{2k} : (y,1) ∈ Z_{2k+1}}`, `N'_k := |V'_1|`.
- **Casillas.** `π : x_{N−1} ↦ 0`. `J_1 := π(I^{(2k+2)} : x_{2k+1})`, `c_k := dim S_{2k+1}/J_1`; `J'_1 := π(I^{(2k+1)} : x_{2k})`, `c'_k := dim S_{2k}/J'_1`.
- **`gr 𝔞`** = ideal of top forms. For a finite set `X`, `I(X)` = its vanishing ideal over `F_q`; `gr I(X)` has colength `|X|`.
- **Monomial ideals.** `M^{(j)}(V) := (x_C·x_A^{q−1} : A, B, C a partition of V, |A| = |B| = j)` (`B` does not appear; it fixes `|C|`).
  - `M_k := Σ_{j=1}^{k} M^{(j)}({0..2k})` in `S_{2k+1}`;
  - `M'_k := Σ_{j=1}^{min(2,k−1)} M^{(j)}({0..2k−1})` in `S_{2k}`.
- **Explicit ideals.** **`K_k := I^{(2k+1)} + M_k`** and **`K'_k := I^{(2k)} + (x_0x_1⋯x_{2k−1}) + M'_k`**.

## 2 · WHAT IS PROVED (use it; do not re-prove it)
1. **Floor:** `I^{(N)} ⊆ gr I(Z_N)`, so `A(N) ≥ |Z_N|`.
2. **Points:** `P_k = P'_k + (q−1)N_k`, `P'_k = P_{k−1} + (q−1)N'_k`.
3. **Ladder:** `A_k ≤ A'_k + (q−1)c_k`, `A'_k ≤ A_{k−1} + (q−1)c'_k`. So `D'(k) ⟸ D(k−1) + [c'_k ≤ N'_k]` and `D(k) ⟸ D'(k) + [c_k ≤ N_k]`.
4. **Known levels:**
   - `D(k)` for all `k` at `q = 3` (Steinberg bridge);
   - `D(1)`, `D'(1)` for all `q` (your mission 1);
   - `D'(2)` for all `q` (your mission 2);
   - **`D(2)` and `D(3)` for all `q`** (external theorems, the Sofá and the Hamaca).
5. **PLUS LEMMA + Lemma Φ:** given `D'(k)`, `M_k ⊆ J_1`, so **`K_k ⊆ J_1`**. Given `D(k−1)` and `(P_k)`, **`K'_k ⊆ J'_1`**, where
   **`(P_k)`: `x_{2k}·x_C(x_a^{q−1}x_{a'}^{q−1} + x_b^{q−1}x_{b'}^{q−1}) ∈ I^{(2k+1)}`** (`|C| = 2k−3`).
6. **`(P_k)` has no `k` (your INFORME_3 §1.1):** `(P_k)` for ALL `k ≥ 3` ⟸ **(L1)** at that `q`. (L1) is true at `q = 3, 9, 27` ⟹ `(P_k)` holds for every `k` at `q = 9, 27` (the auditor reproduced `q = 9` with independent code).
7. **SLICE LEMMA (your INFORME_4 §2.1; audited):** if `X` is closed under scaling, `gr I(X_1) ⊆ π(gr I(X) : x_{n−1})`. Hence `D(k) ⟹ c_k ≤ N_k` and `D'(k) ⟹ c'_k ≤ N'_k`. In particular `c_2 ≤ N_2` and `c_3 ≤ N_3` for all `q`, and the chain has no hidden hypothesis left.
8. **The two dimension statements as inclusions (INFORME_4 §2.2; audited):**
   - given `D(k−1)` + `(P_k)`: `K'_k ⊆ J'_1 ⊆ gr I(V'_1)`, so **`(DO_k)`: `dim S/K'_k ≤ N'_k` ⟺ `gr I(V'_1) ⊆ K'_k`**;
   - given `D'(k)`: **`(DE_k)`: `dim S/K_k ≤ N_k` ⟺ `gr I(V_1) ⊆ K_k`**.
   - `(DO_k)` ⟹ `D'(k)`; `(DE_k)` ⟹ `D(k)`.
9. **Proved instances:** `(DO_2)` for all `q` (INFORME_3 §3.1); `k = 1` both sides. **G-a** (`x_4²x_0²x_1^{q−2} ∈ I^{(5)} + M_2 + (x_4³)`) is the even `k = 2` generic-row instance of (L2), true at `q = 9, 27, 81`.
10. **Measured:** `J_1 = K_k` in `(1,3)`, `(1,9)`, `(2,3)`, `(2,9)`, `(3,3)`, `(2,27)`, `(4,3)` (sealed); `J'_1 = K'_k` in `(2,3)`, `(2,9)`, `(3,3)`, `(2,27)`, `(4,3)` (sealed).

**THE CHAIN, as it stands.** At each level `k ≥ 3`: odd step `D(k−1)` + `(P_k)` + `(DO_k)` ⟹ `D'(k)`; even step `D'(k)` + `(DE_k)` ⟹ `D(k)`. **(L1) gives every `(P_k)`; (L2) gives every `(DO_k)` and `(DE_k)`. Nothing else is open.**
**Row `k = 4`:** `D(3)` is known, so it needs exactly **`(P_4)`, `(DO_4)`, `(DE_4)`** — NOT `(P_3)` or `(DO_3)`.

---
## 3 · (L1), exactly
Variables `a, a', b, b'`; `r_1 = aa'`, `r_2 = bb'`, `β_1 = a+a'`, `β_2 = b+b'`; `ε_1..ε_4` = elementary symmetric in the four; `T := r_1^{q−1} + r_2^{q−1}`; `box_m := (a^m, a'^m, b^m, b'^m)`.
> **(L1):** `∃ γ_0, γ_1 ∈ F_3[a,a',b,b']` with **`ε_1(T − ε_4γ_0) ≡ (ε_1ε_2 − ε_3)γ_1` mod `box_q`** and **`ε_1γ_1 + ε_3γ_0 ≡ 0` mod `box_{q−1}`**.

Equivalent form (yours): with `E(u) := ∏(1+x_iu)`, **`[γ_1(1+ε_1u) + (T − ε_4γ_0)u²]·E(u)^{q−1}` is EVEN in `u` mod `box_q`**.

Known data:
- `q = 3`: `γ_0 = −1`, `γ_1 = r_1 + r_2 − ε_1²`.
- Degrees: `γ_0` has degree `2(q−3)`, `γ_1` degree `2(q−2)`.
- In the pair-symmetric ring the minimal `β`-degrees are exactly `(q−3, q−1)` at `q = 3, 9`.
- Dead: `γ_0 = 0`; `γ_1 = 0`; `γ_0 ∈ F_3[r_1, r_2]`; `γ_0 = ε_1^{q−3}ρ(r_1, r_2)`; the Koszul pair `γ_0 = ε_1δ`, `γ_1 = −ε_3δ`; lifting the `k = 2` certificate.

## 4 · (L2), exactly, and three ways in
> **(L2):** for every `k`: **`gr I(V_1) ⊆ I^{(2k+1)} + M_k`** (even) and **`gr I(V'_1) ⊆ I^{(2k)} + (x_0⋯x_{2k−1}) + M'_k`** (odd).

- **Way A — the free side (exhibit independents).**
  - Given `D'(k)`, `S/I^{(2k+1)} = A'_k = gr Fun(Z_{2k+1})`, of dimension `P'_k`. So (DE_k) ⟺ **the image of `M_k` in `gr Fun(Z_{2k+1})` has dimension `≥ P'_k − N_k`.**
  - A monomial `x_Cx_A^{q−1}` is the function `y_C·[y_A all nonzero]`.
  - The targets are SMALL: `P'_k − N_k` = `1, 6, 36, 232` at `q = 3` (`k = 1..4`) and `66` at `(2,9)`.
  - Odd side, given `D(k−1)`: (DO_k) ⟺ the image of `(x_0⋯x_{2k−1}) + M'_k` in `A_{k−1} = gr Fun(Z_{2k})` has dimension `≥ P_{k−1} − N'_k` (`3` at `(2,3)`, `129` at `(2,9)`).
- **Way B — the slice as a union of pieces** (auditor's lead, untested).
  - `V_1 = ⋃_{i} {y_i = −1} × Z_{2k}`: the multiset `y ∪ {1}` must contain `−1`; remove it and the `1`.
  - `Z_{2k+1} = ⋃_i {y_i = 0} × Z_{2k}`: the SAME pieces, with `0` in place of `−1`.
  - Each piece has the same top-form ideal in both, `(y_i) + I^{(2k)}` in the other variables (given `D(k−1)`). So both `gr I(Z_{2k+1}) = I^{(2k+1)}` and `gr I(V_1)` lie in `⋂_i((y_i) + I^{(2k)}_{\hat i})`.
  - They differ only in how the pieces MEET: points with two zeros in `Z_{2k+1}`, against points with two `−1`'s and a `+1` in `V_1`.
  - **(DE_k) says: moving the pieces from `y_i = 0` to `y_i = −1` changes the top-form ideal by at most `M_k`.** The odd side is the same one parity down.
  - Warning: `gr` of a union is not the intersection of the `gr`'s (three concurrent lines); the argument must use the incidences.
- **Way C — your pointwise criterion (INFORME_3 §2.2).** An interaction element is a function identity on `Z(F_q)`.
  - Indicators `[x = v]` have degree `q−1`, so they land in the top layer. That is why the generic rows are a degree phenomenon.

**Gates for any general argument** (use them before writing it up):
- G-a (even, `k = 2`, general `q`);
- the cells `(3,3)` and `(3,9)`: at `(3,3)`, 36 quintic generators of the generic rows.

## 5 · PROCESS
- **STEP 0 — Reading (10 min).** No runs. Say which way you take for (L2), and why.
- **STEP 1 — (L1) for every `q` (40 min).** A `q`-symbolic pair or a structural existence proof. Gate: reproduce `q = 9, 27`. If it closes, write **«(P_k) FOR ALL k AND ALL q»**.
- **STEP 2 — (L2) for every `k` (100 min; the heart).** Even and odd sides, with the gates of §4. If STEP 1 and STEP 2 close, write in large letters **«CONJECTURE 1.2 CLOSED»**.
- **STEP 3 — Row `k = 4` (30 min, only if STEP 2 did not close for all `k`).** `(DO_4)`, `(DE_4)` by the same way, gate `(4,3)`. With (L1) at `q = 81` this gives **«D(4) FOR ALL q»**.
- **STEP 4 — Verdict (15 min).** Apply the chain to what is proved.

## 6 · DEAD ROUTES (do not retry)
- The sum of colons for the generic rows (it would contradict row 1).
- The naive lifting `x_ax_b·I^{(m)} ⊆ I^{(m+2)}`.
- `j = 1` monomials alone in the odd casilla.
- The shear lever.
- The transfer argument for G-a (the `ε_1²` factor is essential).
- Point enumeration over `F_q^n` in M2.
- Measuring cells as a substitute for a mechanism: cells are gates only.

## 7 · SUCCESS
- **Full:** (L1) for all `q` + (L2) for all `k` ⟹ **CONJECTURE 1.2 CLOSED**.
- **Row:** (L1) at `q ≥ 81` + `(DO_4)` + `(DE_4)` ⟹ **D(4) FOR ALL q**.
- **Partial, declared as such:** (L1) alone; (L2) for one more `k`; G-a for all `q`.

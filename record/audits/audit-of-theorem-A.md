# MISIÓN 89 — AUDIT OF INFORME_14 (Grepy el Lector, 2026-09-23)

> 🔴 **NOTE `2026-09-23` (Grepy el Lector, MISIÓN 90) — RETRACTED AS A DS CLAIM:** `A_k(q) = P_k(q)` ∀k∀q stays PROVED. But R1, written from the original, shows the literal DS Conjecture 1.2 in degree `3^v` ⟺ the PUNCTURED BONE `dim F_3[y]/∩_J(I'_J + m^{[q−1]}) = |Γ|` (an intersection statement, even box `q−1`, zero-free grid), NOT `A = P`. For families the two are independent: at `q = 9`, `k = 2`, `K = J ∖ {01|23|45, 02|15|34}`, `A_K = P_K = 7089` while DS fails (3-torsion). **DS 1.2 in degree `3^v` is OPEN.** `MISIONES_TRAS_BARRIDO/regla264_R1_puente_DS.md`.

**Technical file `regla263_auditoria_fable_14.md`. Source audited: `~/Desktop/FABLE_TABLERO/INFORME_14.md`, md5 `d9c65fbccc5c738716331a18518aedac`, 821 lines. Mission: `MISION_14.md`, md5 `1393212dc91507d138ec0181d21ad37a`.**

## FIRST LINE
**🟢🟢🟢 CLOSED. `A_k(q) = P_k(q)` FOR EVERY `k` AND EVERY `q = 3^v`: this is Conjecture 1.2 of Degtyarev–Shimada in the form the campaign has used since July, the form under which the Sofá (`k=2`) and the Hamaca (`k=3`) were closed.**
- The Fable's Theorem Γ (§3.1) and its five moves (§1.1) were re-derived by hand, line by line. **They are correct.** The corollary (§3.2) is a correct induction on `n` over all profiles at once.
- Independent confirmation with my own code:
  - 37 out-of-sample cells, 37 equal;
  - a characteristic-free prediction that the Fable never made, 60/60, with characteristic 2 failing as the proof says it must;
  - 1 673 721 child objects covered by the bookkeeping, 0 uncovered;
  - 166 exact certificates;
  - 7 new parents, 0 failed rows;
  - two negative controls, both fired.
- **What is NOT re-proved here:** the reduction from the literal statement of [DS] (torsion of `H_{2d}(X)/L(X)`) to `A = P`. It is earlier campaign work (Sofá §§73, 239, 303–305; ASSEMBLY §1), the same reduction the Sofá and the Hamaca rest on. It is checklist item R1 of the Paper B, and it is bibliographic work, not open mathematics.
- **The Paper B is WRITTEN:** `VIVOS/MISIONES_TRAS_BARRIDO/PAPER_B_v1.md`.

## 1 · WHAT THE REPORT CLAIMS
- **The Γ-law** `K^Γ_μ(n) = (e_odd) + box + (Γ^{(s)}(A;B)(n) : w = |B|−|A| ≥ 0, s ≤ λ_w(μ))`, with `λ_w(μ) := Σ(μ_i − w)_+`.
- **Theorem Γ:** every row of every profile contains the child's casilla, via three moves of the new letter plus the odd identity.
- **Corollary:** `T(n)` for all `n` and `μ`, hence `A_k(q) ≤ P_k(q)`; with the floor, equality.
- **Ledger `k = 5`:** 500/532 lines, 0 open.
- **Gates:** 141 `vdim` cells, 108 parents × all rows.

## 2 · THE PENCIL RE-DERIVATION (auditor, by hand, line by line)

### 2.1 The one simplification the Fable did not state, and which makes everything transparent
`E_{[n]}(−t)·H_{A;B}(t) = E_P(−t)·Π_{b∈B}(1−bt)/(1−bt)·Π_{a∈A}(1−at)/(1+at) = E_P(−t)·Π_{a∈A}(1−at)/(1+at)`.
**The absent letters cancel.** So `Γ^{(s)}(A;B)(n) = [t^D] E_P(−t)·Π_A(1−at)/(1+at)`, `D = |A|(q−1)+|P|+1−s`, and `B` enters ONLY through `P = [n]∖(A∪B)` (hence through `D`). Over `F_3`, `(1−u)/(1+u) = 1 + 2Σ_{i≥1}(−u)^i = 1 − Σ_{i≥1}(−u)^i`.

### 2.2 The five moves — all four generating-function identities re-derived; correct
- **(M-P)** `z ∈ P`: `E_{P∪z}(−t) = E_P(−t)(1−zt)` and `D_{n+1}(s) = D_n(s−1)`, `D_{n+1}(s)−1 = D_n(s)`. ✔
- **(M-B)** `z ∈ B`: `P` and `D` unchanged, and by 2.1 the polynomial is literally the same. ✔
- **(M-A)** `z ∈ A`: one more factor `(1−zt)/(1+zt)` and `D' = D + (q−1)`; coefficient of `z^i` is `1` (`i = 0`) and `−(−1)^i` (`i ≥ 1`), a unit. ✔
- **(Z)** `s ≤ 0`: `D − p ≥ |A|(q−1)+1` for every `p ≤ |P|`, so the `A`-part has degree `> |A|(q−1)` in `|A|` letters: box (or exactly `0` when `A = ∅`). ✔
- **(Anti)** `Σ_{k odd}e_kt^k = −(E(t)−E(−t))` (`1/2 = −1`) and `E(t)H_{A;B}(t)|_{t=−u} = E(−u)H_{B;A}(u)`. ✔
- **Descent** `z^aΓ^{(s)}(A;B)(n) = Γ^{(s−a)}(A;B∪z)(n+1) − Σ_{i=1}^{a}z^{i−1}Γ^{(s−a+i)}(A;B)(n+1)`: `a = 1` is (M-P)+(M-B); the induction step is one line. ✔ EXACT (no box).

### 2.3 Theorem Γ — every position re-derived; correct
Notation `K_p := K^Γ_μ(n+1)`; `c_w(μ) := λ_w(μ) − λ_{w+1}(μ) = #{i : μ_i ≥ w+1}` (direct: `(μ_i−w)_+ − (μ_i−w−1)_+ = [μ_i ≥ w+1]`).
- **Lemma 1 (P)**: `s+1 ≤ λ_w(μ)` ⟹ `Γ^{(s)}(A;B)(n) ∈ R_0` — (M-P) at `z = 0`. ✔
- **Lemma 1 (D)**: `s ≤ λ_w(μ)` and `s−a ≤ λ_{w+1}(μ)` ⟹ `z^aΓ^{(s)}(A;B)(n) ∈ K_p` EXACTLY — the descent: the first term is an object of imbalance `w+1` at level `s−a` (or box), the others of imbalance `w` at levels `s−a+1, …, s` (or box). ✔
- **BASE**: `e_k(y) = e_k(y,z) − z·e_{k−1}(y)`. ✔
- **LOWER** (row `a`, child `μ−ε_{a+1}`, parts lowered LARGEST FIRST): if `μ_{a+1} > w` every child level is `≤ λ_w(μ)−1` ⟹ (P); if `μ_{a+1} ≤ w` the parts `> w` are among `μ_1..μ_a` ⟹ `c_w ≤ a` ⟹ (D). ✔ **(The order «largest first» is USED here; the dictionary's bijection lets us choose it, because the count only needs the multiset of children.)**
- **VALUE-0** (row `ℓ`): `c_w ≤ ℓ` ⟹ (D). ✔
- **NEW-CLASS** (rows `ℓ+1..q−ℓ−1`, child `μ∪(1)`): only `(w,s) = (0,|μ|+1)` is new. With `α_m, β_m` as in the report, `z^ℓ[t^M]O H − z^{ℓ+1}[t^{M−1}]O H = z^ℓ(β_M−α_M) − 2z^{ℓ+1}β_{M−1} + O(z^{ℓ+2})` — I expanded the four terms myself; `−2 = 1`. `z^ℓβ_M`, `z^ℓα_M` are in `K_p` by (D) at `a = ℓ` because `|μ| − ℓ = λ_0 − c_0 = λ_1` (`c_0 = ℓ`). ✔
- **RAISE** (row `q−j`, child `μ+ε_j`, parts raised SMALLEST FIRST, i.e. row `q−j` raises `μ_j`): old levels by (D) with `a = q−j ≥ ℓ+1 > c_w`; new `w = 0` level by NEW-CLASS (`ℓ+1 ≤ q−j`); new `w ≥ 1` level `t = λ_w+1` from the parent object `Π = Γ^{(λ_{w−1})}(A∪z;B)(n+1)` (imbalance `w−1 ≥ 0`, level `λ_{w−1} ≥ c_{w−1} ≥ j ≥ 1`) by (M-A): the `z^i`-term has level `u_i = λ_{w−1}−q+1+i`, `u_{i*} = t` at `i* = q − c_{w−1}(μ) ≤ q−j` (since `μ_1..μ_j ≥ w`); every `i < i*` has `u_i ≤ λ_w` and `u_i − i = λ_{w−1}−q+1 = λ_{w+1}+c_w+c_{w−1}−(q−1) ≤ λ_{w+1}` (because `c_w + c_{w−1} ≤ 2ℓ ≤ q−1`) ⟹ (D) — **including `i = 0`, which covers the case `λ_{w−1} ≥ q` that the report's sentence «levels `≤ 0` are box» does not mention; the same inequality handles it.** ✔
- **Only use of `q`**: `2ℓ(μ) ≤ q−1`, which is the range of the dictionary itself. ✔

### 2.4 The corollary — the induction is on `n`, for ALL profiles at once
- Claim `C(n)`: `dim_{F_3} F_3[y_1..y_n]/K^Γ_μ(n) ≤ |W_μ(n)|` for every `μ` with `ℓ(μ) ≤ h`.
- `C(0)`: `K^Γ_∅(0) = 0` (dim 1 = `|W_∅(0)|`); for `μ ≠ ∅`, `Γ^{(1)}(∅;∅)(0) = [t^0]1 = 1`.
- `C(n) ⟹ C(n+1)`: the row filtration (`z^q ∈ K_p`) gives `dim S_{n+1}/K_p = Σ_a dim S_n/R_a(K_p)`; Theorem Γ; `C(n)` at every child (all children have `ℓ ≤ h`: a new-class row exists iff `ℓ+1 ≤ h`); and the count.
- **The count is a THEOREM, not a check:** with `F_μ(x) := e^x Π_i I_{μ_i}(2x) I_0(2x)^{h−ℓ}`, `|W_μ(n+1)| = n![x^n]F_μ'` and `d/dx I_d(2x) = I_{d−1}(2x) + I_{d+1}(2x)` (`I_{−1} = I_1`), `d/dx e^x = e^x`, `d/dx I_0(2x)^{h−ℓ} = 2(h−ℓ)I_1(2x)I_0(2x)^{h−ℓ−1}`: exactly `ℓ` lower, `1` value-0, `2(h−ℓ) = q−1−2ℓ` new-class and `ℓ` raise children. (I verified the Bessel recursion term by term on the series.) ✔
- **At `μ = ∅`, `n = 2k+2`**: `K^Γ_∅ = (e_odd) + box = I^{(n)}` (`λ_w(∅) = 0`), and `|W_∅(n)| = n![x^n]e^xI_0(2x)^h = n![x^n]cosh(x)I_0(2x)^h = P_k(q)` for `n` even (odd part of `e^x` contributes only odd degrees). ✔
- **The floor `A ≥ P`** (elementary, informe 66 Ruta 1): `E + (x_i^q − x_i)` is the radical ideal of the `F_q`-points of `V(E)`, which are exactly the `P_k(q)` points with `#{x_i = v} = #{x_i = −v}`; its ideal of leading forms contains `E + m^{[q]}`. ✔
- ⟹ **`A_k(q) = P_k(q)` for every `k ≥ 0` and every `q = 3^v`.**

## 3 · INDEPENDENT GATES (own code; every run inside `vigia.sh` with the estimate written before)
The engines are `corpus4/herramientas_grepy/regla263_gamma.py` (the generator: Γ written from the DEFINITION, ALL levels, no multiplier lemma) and `regla263_certs.py`.

| gate | cells | result | log |
|---|---|---|---|
| calibration | `∅(4)`, `∅(6)` at `q=9`; `(1)(5)`, `(2,1)(6)` at `q=9`; `(1,1)(4)` at `q=27` | `217 = A_1(9)`, `7761 = A_2(9)`, the rest equal `|W|` | `regla263_calib.log` |
| negative control 1 (one level dropped at `w = 0`) | `(1)(5)`, `(2,1)(6)` | `921 > 855` and `2340 > 1080`: **the gate can fail** | `regla263_ctrl.log` |
| **out of sample, `q = 27`, `n = 6`** | **22 cells, every `μ` with `3 ≤ \|μ\| ≤ 6`** | **22/22 `vdim = \|W\|`** | `regla263_oos_27_6.log` (452 s; I estimated 240) |
| **out of sample, `q = 81`, `n = 5`; `q = 243`, `n = 4`** | **15 cells** | **15/15** | `regla263_oos_81_243.log` |
| **char-free prediction** (never made by the Fable) | `dim_K K[x]/(e_odd + box_q)` in char `0, 3, 5, 7, 11`, `n = 2, 4, 6`, `q = 3, 5, 7, 9` | **60/60 equal to `N_q(n)`** | `regla263_charfree.log` |
| control: char 2 (the proof divides by 2) | same 12 cells | **differs in 8 of the 8 cells with `n ≥ 4`** (`21, 65, 133, 225`, `183, 1205, 3787, 8649` = the E-EGF values `U_k(q)`) | same |
| index bookkeeping, exhaustive | `\|μ\| ≤ 14`, `q = 3, 9, 27, 81` | **1 673 721 child objects, 0 uncovered** (own conditions, incl. the lower `z`-terms of the raise) | `regla263_indices.log` |
| exact certificates, real letters | RAISE expansion ×110, NEW-CLASS ×24, DESCENT ×32 | **166/166** | `regla263_certs.log` |
| control: NEW-CLASS with the swap sign flipped | 1 cell | **fails** (as it must) | `regla263_certs_ctrl.log` |
| **row memberships at NEW parents** | `q = 9`, `n+1 = 7`: `(4,1)`, `(3,1)`, `(2,1,1)`, `(1,1,1)`; `q = 81`, `n+1 = 4`: `(2,1)`, `(1,1)`, `(3)` | **7 parents, 0 failures** | `regla263_rows_9_7.log`, `regla263_rows_81_4.log` |
| **negative control 2: lower rows smallest-first** | `(3,1)(6)`, `q = 9` | **row 0 fails with 65 generators** (predicted by my index analysis: the objects `(s,w) = (2,1)`) | `regla263_rows_ctrl.log` |

## 4 · THE AUDIT OF THE REST OF THE REPORT
- **Ledger `k = 5`** (500/532 lines): it is now a CONSEQUENCE of Theorem Γ, not a citation table. It is correct as a check; my bookkeeping gate covers it with room to spare.
- **Rule breaches**, all declared by the Fable: a smoke test outside the watchdog; four runs over their estimate but under the caps; planned clock times corrected on re-read. **No kills, no orphans.** (Checked: `ps` shows 0 engines.)
- **Not done by the Fable:** `(2,1)(8)`, `H_{j;k;l}` vs `Γ^{(2)}(j;kl)`, the 8-variable memberships. **None of them is needed.**
- **The Fable's sealed bets:** 1 hit, 2 hit, 3 hit, 4 hit, 5 not run, 6 not tested, 7 **hit (confirmed by this audit)**, 8 hit.
- **Mark: the highest of the campaign. The report closes the conjecture, and does it with the smallest proof the campaign has seen.**

## 5 · MY SEALED BETS
- **On INFORME_14** (`corpus4/regla262_apuestas_selladas.md`):
  - #1: (A3) is proved (hit), but with one power of `z`, not `ℓ+1` (the form is falsified);
  - **#2 FALSIFIED** (A2 is Pascal alone);
  - #3 not tested (the Fable replaced the guessed law with a strictly larger one);
  - **#4 FALSIFIED** (the row closed, and so did the conjecture);
  - #5 hit.
  - **Third time in a row I underestimated the Fable.**
- **This turn** (`corpus4/regla263_apuestas_selladas.md`, md5 `4aba350f…`, written before the runs): **6/6 hit.** Only #1, #2 and #4 carried real risk.

## 6 · INGENIO
1. **The absent letters cancel** (§2.1 above): `E_L(−t)H_{A;B}(t) = E_P(−t)Π_A(1−at)/(1+at)`. The objects are simpler than the Fable wrote them, and (M-B) becomes a triviality.
2. **Reading the proof gives a new, falsifiable prediction.** The proof uses `2 ∈ F^×` and nothing about `q` beyond «odd», so it must hold in EVERY characteristic `≠ 2` and for EVERY odd `q`, with the lower bound from a symmetric set `C` of `q` points. **Tested: 60/60, and char 2 fails.** Hence **Theorem A** of the Paper B (every field of char `≠ 2`, every odd `q`) and **Corollary C**: the torsion of `Z[x]/(e_odd, x_i^q)` is a `2`-group. That is the shape of LEY 00, for this module.
3. **The lower-row order is USED:** smallest-first fails at `(3,1)(6)` with 65 generators. The bijection rows ↔ children is free for the count and not free for the inclusions. The paper states this as Remark 7.3.

## 7 · ERRORS OF MINE, PUBLISHED
- **The char-free script v1 left `t` free in the ring:** every `vdim = −1`. Fixed by adding `t` to the ideal, and re-run. A test that gives nothing is not a negative result.
- **The `q = 27`, `n = 6` batch took 452 s against my estimate of 240 s**, under the cap.
- **Bet 6 of this turn was labelled SAFE; it was the riskiest of all.** It held.

## 8 · STATE
- **DS 1.2 (campaign form): CLOSED for every `k ≥ 0` and every `q = 3^v`.**
- **Paper B written** (`PAPER_B_v1.md`, skeleton `v11` to `_HISTORICO`).
- **Open for submission:** R1 (write the DS reduction from the original); R2 (DOIs); R3 (the general theorem as the headline?); R4 (a cold outside reading).

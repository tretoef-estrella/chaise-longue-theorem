# MISSION 3 «THE CASILLAS WITHOUT A COLON» — CLOSE k = 2, CLOSE LEVEL 3, AND ATTACK ALL k
*(Grepy el Cartógrafo, auditor, 2026-09-21. Self-contained. Your INFORME_2 was audited line by line and APPROVED; this mission builds on it. Every number here was checked by two routes, and the text says which.)*

> **OBJECTIVE: the complete closure of Conjecture 1.2 of Degtyarev–Shimada for all `k` and all `q = 3^v`, THIS TURN.**
>
> After your turn and the audit, **the whole conjecture follows from three EXPLICIT statements, with `k` as a letter: `(P_k)`, `(DO_k)`, `(DE_k)`** (§3). None of them has a colon. They are measured true in 12 cells, including one sealed out-of-sample cell.
>
> **The target is ALL `k`.** `k = 2` and `k = 3` are NOT goals: they are GATES that every general argument must pass before you write it (G-a is exactly `(DE_2)` restricted to one row).
>
> **Proving `(P_k)`, `(DO_k)` and `(DE_k)` for all `k` CLOSES THE CONJECTURE**, by the chain of §2.4, which is already proved.
>
> **Fallback, only if the general attack is declared dead with a reason:** close `k = 2` entirely, then level 3.

---
## 0 · RULES OF THE TURN (mandatory)
1. **BEFORE THINKING:** create `INFORME_3.md` with the empty sections `## FIRST LINE` · `## STEP 0` · `## STEP 1` · `## STEP 2` · `## STEP 3` · `## STEP 4 — VERDICT`. **Write each step under its own heading.**
2. **Save to disk after every step.** What is not written does not exist. If the session is cut, what is on disk is the delivery.
3. **Header per step:** `STATE: CLOSED | EXHAUSTED | NOT CONCLUDED` and `NEXT:`.
4. **In order, no going back, no step 5, no retries.**
   - Write a budget before each step.
   - 10 min without real progress ⟹ stop, write, declare.
   - **The last 20 % of each budget is for writing.**
5. **At most one literature search per step**, in the original source.
6. **Do not recompute what is given here as verified** (§2).
7. **A negative dimension, or one larger than the box, is a bug:** stop.
8. **«This route dies, for this reason» is a result.**
9. **Write ONLY in this folder (`~/Desktop/FABLE_TABLERO/`). Do not open anything in `~/Desktop/ARBOLYAML/`.**
10. **Machine:** `/opt/homebrew/bin/M2`.
    - **Less than 1.2 GB and 10 min per run, with the estimate written BEFORE each run.**
    - Allowed cells:
      - `k ≤ 2` with `q ≤ 27`, and `k = 2` with `q = 81` ONLY for memberships in 5 variables (no colon);
      - `k = 3` with `q ∈ {3, 9}`;
      - `k = 4` with `q = 3`.
    - Anything else: do not run it.
11. **Re-read the disk before the verdict.**
12. **Double check:** every claim you promote to PROVED must carry its proof in the report. Every number carries its cell and its log file.

**FIRST LINE** (answer these three first, in this order):
- (a) Did you close `k = 2` entirely (G-a for all `q`)? Did you close level 3 (`(P_3)`, `(DO_3)`, `(DE_3)`)? What else did you prove, for which `k` and `q`?
- (b) If not, what exact lemma is missing, and in which cell is it checked?
- (c) Does it close the conjecture? YES or NO, with the reason in one line.

---
## 1 · THE OBJECTS (same as missions 1–2)
- **Rings.** `q = 3^v`. `S_N := F_3[x_0..x_{N−1}]`; `e_j^{(N)}` is the elementary symmetric polynomial of degree `j`.
- **The ideal.** **`I^{(N)} := (e_1, e_3, e_5, …) + (x_0^q, …, x_{N−1}^q)`** (all ODD elementary symmetric polynomials plus the box).
- **Dimensions.** `A(N) := dim S_N/I^{(N)}`; `A_k := A(2k+2)` (EVEN level) and `A'_k := A(2k+1)` (ODD level).
- **Points.** **`Z_N := {x ∈ F_q^N : the multiset {x_i} is closed under negation}`**, so that `x ∈ Z_N ⟺ e_{odd}(x) = 0`. `P_k := |Z_{2k+2}|`, `P'_k := |Z_{2k+1}|`.
- **CONJECTURE `D(k)`:** `A_k = P_k`. **Odd twin `D'(k)`:** `A'_k = P'_k`.
- **Casillas.** Use `π : x_{N−1} ↦ 0`.
  - `J_1 := π(I^{(2k+2)} : x_{2k+1}) ⊂ S_{2k+1}`, with `c_k := dim S_{2k+1}/J_1` (**even casilla**).
  - `J'_1 := π(I^{(2k+1)} : x_{2k}) ⊂ S_{2k}`, with `c'_k := dim S_{2k}/J'_1` (**odd casilla**).
  - Also `J_0 := π(I^{(2k+2)}) = I^{(2k+1)}` and `J'_0 := π(I^{(2k+1)}) = I^{(2k)}`.
- **Slices.** **`N_k := #{y ∈ F_q^{2k+1} : (y,1) ∈ Z_{2k+2}}`**, **`N'_k := #{y ∈ F_q^{2k} : (y,1) ∈ Z_{2k+1}}`**.
- **Rows and fibres** (your missions 1–2):
  - `R_a := π'(J_1 : x_{2k}^a)` and `R'_a := π'(J'_1 : x_{2k−1}^a)`;
  - fibres `F_v`, `F'_v`, and the dictionary `a = 0 ↔ −1`, `a = 1 ↔ 0`, `2 ≤ a ≤ q−2 ↔` generic, `a = q−1 ↔ +1`;
  - `f_{+1}(2,q) = 2(3q−4)` and `f_gen(2,q) = 12(q−2)`.
- **Graded ideals.** For an ideal `𝔞`, `gr 𝔞` is the ideal of top forms. **`G_N(∅) := (e_{odd}) + (x_i^q − x_i)` over `F_q` is RADICAL**, with zero set `Z_N(F_q)`.
- **THE MONOMIAL IDEALS (new).** In a polynomial ring with variable set `V`, for `j ≥ 1` let
  **`M^{(j)}(V) := ( x_C·x_A^{q−1} : A, B, C a partition of V, |A| = |B| = j )`**,
  where `x_C := ∏_{i∈C} x_i` and `x_A^{q−1} := ∏_{i∈A} x_i^{q−1}` (`B` does not appear in the monomial; it only fixes `|C| = |V| − 2j`).
  - **`M_k := Σ_{j=1}^{k} M^{(j)}({0..2k})`** in `S_{2k+1}` (even).
  - **`M'_k := Σ_{j=1}^{min(2,k−1)} M^{(j)}({0..2k−1})`** in `S_{2k}` (odd).

---
## 2 · WHAT IS ALREADY PROVED (use it; do not re-prove it)

**2.1 · Floor, ladder, fibres** (missions 1–2).
- **Floor:** `A(N) ≥ |Z_N|`, because `gr G_N(∅) ⊇ I^{(N)} ⊗ F_q` and `G_N(∅)` is radical.
- **Ladder:** `A_k ≤ A'_k + (q−1)c_k` and `A'_k ≤ A_{k−1} + (q−1)c'_k`.
- **Points:** `P_k = P'_k + (q−1)N_k` and `P'_k = P_{k−1} + (q−1)N'_k`.
- ⟹ `D'(k) ⟸ D(k−1) + [c'_k ≤ N'_k]`, and `D(k) ⟸ D'(k) + [c_k ≤ N_k]`.

**2.2 · YOUR results** (INFORME_2, audited and approved).
- `k = 1` completely, both parities.
- **`D'(2)` for all `q`.**
- The odd outer rows of `k = 2` for all `q` (§2.2 finite computation; §2.5 transfer on the fixed scheme of 6 double points).
- The reductions of the even rows to `Q ⊆ R_{q−1}` (Lemma Π) and `Q^gen ⊆ R_2` (Lemma Π^gen), given `D(k−2)`.
- The death of the shear lever.
- **Two small debts to pay in STEP 0** (write them out, a few lines each):
  - the odd Lemma E (`R'_a = (J̄'_1 : ε_1^a) + (ε_1)`), written «same derivation» in your §2.2;
  - the definition of `N'` and the step `ε_1(y_i+y_j)^{q−1} ∈ N'` in your §1.4.

**2.3 · NEW from the audit (pencil).**
- **Key fact (chain order).** In the chain, `D'(k)` is proved (step 2) BEFORE the even step (step 3). And `D'(k)` ⟹ `I^{(2k+1)} = gr G_{2k+1}(∅) ∩ S`:
  - the inclusion `⊆` is the floor, and `D'(k)` says the dimensions are equal.
  - So **at the even step, the top form of EVERY `F_3`-polynomial vanishing on `Z_{2k+1}(F_q)` lies in `J_0 = I^{(2k+1)} ⊆ J_1`.** Your §2.4 remark «it would be circular with `D'(k)`» is wrong FOR THE EVEN STEP.
- **PLUS LEMMA (given `D'(k)`).** Let `A, B, C` partition `{0..2k}` with `|A| = |B| = j`, `1 ≤ j ≤ k`. Then **`x_C(x_A^{q−1} + x_B^{q−1}) ∈ I^{(2k+1)}`.**
  - *Proof.*
    - Let `u_i := x_i^{q−1}`. The polynomial `F := x_C[∏_A(1−2u_i) + ∏_B(1−2u_i)]` vanishes on `Z_{2k+1}`.
    - Indeed, if `x_C ≠ 0` then (the nonzero coordinates pair up, and `|C|` is odd) the number of nonzero coordinates in `A∪B` is odd.
    - So `∏_{A∪B}(1−2u) = −1`, which forces `∏_A = −∏_B` (each factor is `±1`).
    - Its top form is `(−2)^j·x_C(x_A^{q−1} + x_B^{q−1})`, and **`(−2)^j = 1` in `F_3`**. ∎
  - Your level-2 detector is the case `j = 2`.
- **LEMMA Φ** (PROVED in the project, all `k`, all `q`): `x_C(x_A^{q−1} − x_B^{q−1}) ∈ J_1` (top form of the parity detector `G_{A,B}` with `|A| = |B|`).
- ⟹ **`M_k ⊆ J_1`**, adding the two identities (2 is invertible).
- **Consequence for `k = 2`.**
  - `A = {a,4}` gives **`x_c x_a^{q−1} ∈ R_{q−1}` (your Lemma U-b), PROVED for all `q`.**
  - With U-a and the count `2(3q−4)` (your §2.4(a)), **the +1 even row of `k = 2` is closed for all `q`**; the count is to be written in STEP 1a.

**2.4 · THE CASILLA THEOREMS and THE CHAIN.**
- **EVEN:** `J_1 ⊇ K_k := I^{(2k+1)} + M_k`, given `D'(k)`: PROVED (2.3).
  - **MEASURED `J_1 = K_k` as ideals** in `(1,3)`, `(1,9)`, `(2,3)`, `(2,9)`, `(3,3)`, `(2,27)`, and in **`(4,3)`, sealed before running**. `dim = N_k`: `6, 24, 45, 855, 357, 9765, 2907`.
  - The `j = k` part is redundant in `(3,3)` and `(4,3)`.
- **ODD:** `J'_1 ⊇ K'_k := I^{(2k)} + (y_0y_1⋯y_{2k−1}) + M'_k`, **given `D(k−1)` and `(P_k)`**.
  - The **anchor** `y_0⋯y_{2k−1} = e_{2k}(y)` is in `J'_1` because `x_{2k}·e_{2k}(y) = e_{2k+1}(y, x_{2k}) ∈ I`.
  - The «−» part `x_C(x_A^{q−1} − x_B^{q−1}) ∈ J'_0 = I^{(2k)}` holds by `D(k−1)`: it vanishes on `Z_{2k}`, since `|C|` is even, so `∏_A = ∏_B`.
  - The «+» part needs `x_{2k}x_C(x_A^{q−1} + x_B^{q−1}) ∈ I^{(2k+1)}`, which is `(P_k)`.
  - **MEASURED `J'_1 = K'_k`** in `(2,3)`, `(2,9)`, `(3,3)`, `(2,27)`, and in `(4,3)`, sealed. `dim = N'_k`: `16, 88, 126, 304, 1016`.
  - Monomials with `j ≤ 2` suffice in `(3,3)` and `(4,3)`; with `j = 1` only, the dimension is too big (`131` vs `126`; `1086` vs `1016`).
- **Calibration script:** `casilla.m2` in this folder (auditor's run: `casilla_auditor.log`, all `equal:true`, 205 MB).
- **THE CHAIN** (induction on `k`, base `k = 0`). Assume `D(k−1)`, `D'(k−1)` and `c_{k−1} ≤ N_{k−1}`.
  - `(P_k)` + `D(k−1)` ⟹ `J'_1 ⊇ K'_k`; with **`(DO_k)`** this gives `c'_k ≤ N'_k`, hence `D'(k)`.
  - Then `J_1 ⊇ K_k`; with **`(DE_k)`** this gives `c_k ≤ N_k`, hence `D(k)`.

---
## 3 · WHAT IS MISSING: THREE EXPLICIT STATEMENTS (no colon anywhere)
- **`(P_k)` — THE PLUS IDENTITY OF LEVEL 2, BEFORE `D'(k)`.** For `k ≥ 3`: `x_C(x_a^{q−1}x_{a'}^{q−1} + x_b^{q−1}x_{b'}^{q−1}) ∈ I^{(2k+1)}`, for every partition `{a,a'} ⊔ {b,b'} ⊔ C = {0..2k}`.
  - Status: `j = 1` is PROVED (your U-a+). `(P_k)` is TRUE given `D'(k)` (2.3), but the odd step needs it BEFORE `D'(k)`.
  - For `k ≤ 2` it is empty. Measured in `(3,3)` (your `paso2a.log`) and in `(4,3)` (auditor, all `j`).
- **`(DO_k)` — odd dimension:** `dim S_{2k}/K'_k ≤ N'_k`.
- **`(DE_k)` — even dimension:** `dim S_{2k+1}/K_k ≤ N_k`.
- **Why these are the right targets.**
  - They are STRICTLY STRONGER than `D(k)`/`D'(k)` (they also say `J_1 = K`) and falsifiable; they are NOT restatements.
  - The colon `I : x` is gone.
  - **The free side:**
    - `A'_k := S_{2k+1}/I^{(2k+1)}` has dimension `P'_k` (by `D'(k)`), and it is the graded ring of functions on `Z_{2k+1}`.
    - So `(DE_k)` ⟺ **the image of the monomial ideal `M_k` in `A'_k` has dimension `≥ P'_k − N_k`**, i.e. you must EXHIBIT enough linearly independent elements. That is the side a certificate can give.
    - Likewise `(DO_k)` ⟺ the image of `(e_{2k}) + M'_k` in `S_{2k}/I^{(2k)}` (dimension `P_{k−1}`) has dimension `≥ P_{k−1} − N'_k`.
  - **Independence in a graded ring of points** is testable by functions: a family of degree-`d` elements is independent in `(A'_k)_d` iff their functions on `Z_{2k+1}` are independent modulo the functions of degree `< d`.

---
## 4 · PROCESS (all targets with `k` as a letter; small cells are gates only)
**STEP 0 · Calibration + debts (15 min).**
- Run `casilla.m2` as is (seconds). Check `equal:true` in all 8 lines and `FIN-OK`.
- Write the two debts of §2.2 (odd Lemma E; `N'` and `ε_1(y_i+y_j)^{q−1} ∈ N'`) and the one-paragraph count of the +1 even row of `k = 2` (`r_{q−1} ≤ 2(3q−4)` from U-a, U-b, `e_{odd}`, box).

**STEP 1 · `(P_k)` FOR ALL `k` (40 min).** Pencil. Prove `x_C(x_a^{q−1}x_{a'}^{q−1} + x_b^{q−1}x_{b'}^{q−1}) ∈ I^{(2k+1)}` for every `k ≥ 3`, WITHOUT using `D'(k)`.
- Start from YOUR proof of (U-a+) (the case `j = 1`) and extend its mechanism to `|A| = |B| = 2`.
- Alternative: induction on `k`, lifting from the identity in `2k−1` variables (true by `D'(k−1)`, already available in the chain). The naive lifting `x_ax_b·I^{(m)} ⊆ I^{(m+2)}` is FALSE: the mechanism must use the special form of the element (e.g. pair the two new variables as `x_c, x_{c'}` inside `C` and use `e_j(z, c, c') = e_j(z) + (c+c')e_{j−1}(z) + cc'e_{j−2}(z)`).
- Gates: `(3,3)`, `(3,9)`, `(4,3)`.

**STEP 2 · `(DE_k)` FOR ALL `k` — THE HEART (70 min).** Given `D'(k)`, `A'_k = S_{2k+1}/I^{(2k+1)}` is the graded ring of functions on `Z_{2k+1}` (dimension `P'_k`). **Prove that the image of `M_k` in `A'_k` has dimension `≥ P'_k − N_k`.** This is the FREE side: you must EXHIBIT enough independent elements, which is exactly what a certificate can do.
- **Suggested attack (functions on points).** A family of degree-`d` elements of `M_k·A'_k` is independent iff their functions on `Z_{2k+1}` are independent modulo functions of degree `< d`. The monomials `x_C x_A^{q−1}` are, on `Z_{2k+1}`, "`x_C` times the indicator that `A` is fully nonzero". Organize `Z_{2k+1}` by its PATTERN (which coordinates are zero, which pair with which) and count, pattern by pattern, what `M_k` kills versus what survives: `N_k` must survive. `P'_k − N_k` has a closed form from the EGFs (`P'_k = (2k+1)![t^{2k+1}] sinh·I_0^M`, `N_k` from the slice); match the count to it.
- **Alternative: your tablero** applied to the explicit ideal `K_k = I^{(2k+1)} + M_k` along `x_{2k}` (the colon is now of an explicit ideal), with your transfer / finite-computation tricks and your Lemmas Π, Π^gen.
- **Gate that MUST pass before writing:** G-a, i.e. `x_4²x_0²x_1^{q−2} ∈ I^{(5)} + M_2 + (x_4³)` for all `q` (measured at `q = 9, 27, 81`). If your general argument does not yield it, it is wrong. If the general argument stalls, prove G-a alone (a `q`-symbolic certificate: extract it at `q = 9` and `q = 27`, treat `q−1, q−2, q−3` as symbols) and declare `k = 2` CLOSED.
- Further gates: `(3,3)`, `(3,9)`, `(4,3)`.

**STEP 3 · `(DO_k)` FOR ALL `k` (40 min).** Same method one parity down: given `D(k−1)`, `S_{2k}/I^{(2k)}` is the graded ring of functions on `Z_{2k}` (dimension `P_{k−1}`); prove the image of `(e_{2k}) + M'_k` has dimension `≥ P_{k−1} − N'_k`. The anchor `e_{2k} = y_0⋯y_{2k−1}` kills exactly the functions supported where all coordinates are nonzero. Gates: `(2,9)`, `(3,3)`, `(3,9)`, `(4,3)`.

**STEP 4 · Assembly and verdict (15 min).** Apply the chain of §2.4 to whatever you proved, and say which `D(k)` follow, for which `k` and `q`. If `(P_k)`, `(DE_k)`, `(DO_k)` all hold for all `k`: **write «CONJECTURE 1.2 CLOSED» IN LARGE LETTERS, with the chain.** Every number with its cell and its log.

---
## 5 · DEAD ROUTES (do not try them)
1. **Bounds that only use the Hilbert function** (Macaulay, Gotzmann, Clements–Lindström): insufficient (`1568` vs `855` in `(2,9)`).
2. **Lex game / Cerlienco–Mureddu in the variable `x_{2k}`:** the slice is a graph and gives `[N_k, 0, …]`. **The tablero is a DEGREE phenomenon.**
3. **Dualities** (Matlis, Gorenstein): they only give equivalent statements.
4. **Hereditary or local criteria over subfamilies:** refuted.
5. **Going up from `q = 3` to `q = 9` by Frobenius or by multiplicative actions:** impossible.
6. **The shear** `x_{2k} ↦ x_{2k} + v·x_{2k+1}`: it leaves every row invariant (your §1.1).
7. **The naive lifting** `x_ax_b·I^{(m)} ⊆ I^{(m+2)}`: false (measured `n = 5, 6, 7`).
8. **Measuring outside rule 10.**
9. **Re-proving** the PLUS LEMMA, Lemma Φ, the chain, or your lemmas of missions 1–2.

## 6 · WHAT COUNTS AS SUCCESS
- **Full (the target):** `(P_k)`, `(DO_k)`, `(DE_k)` for all `k` ⟹ **CONJECTURE 1.2, CLOSED.**
- **Partial, valuable:** any one of the three for all `k`, WITH its gates passed; or `k = 2` closed entirely plus level 3.
- **Also valid:** a proved reason why a route cannot work, with the exact point where it breaks.
- **Not valid:** measurements as proofs, fits to data, statements without their cell, or a "general" argument that has not passed its gates.

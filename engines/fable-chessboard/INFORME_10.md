# INFORME 10 — THE ONE LEMMA
*(Fable, mission 10, 2026-09-23.)*

## FIRST LINE
- **(a) YES.** (G1) `y_j^{q−2}e_{n−m−1}(y∖y_l) ∈ R_2(K_(m)(n+1))` is PROVED for **every `m ≥ 1`, every `n`, every `q = 3^v ≥ 9`** (q = 3 has no generic rows): both parities of `n` for `m = 1`, and all `m ≥ 2` (Theorem 2.1, pencil proof in the report; exact gates 24/24 cells, q = 9, 27, 81, up to 7 variables). ⟹ **ONE-PART LINE CLOSED FOR ALL q**: every row of every `K_(m)(n+1)` is proved.
- **(b)** The second-order certificate is really FIRST order and lives in two letters: **`A_r = (−1)^c·[h_{q+c−2−2r}(−y_j, y_l) − y_l^{q+c−2−2r} − (−y_j)^{q+c−2−2r}]` for `r ≤ c/2`, `A_r = 0` beyond** (`c = n−m−1`): a Lucas divided difference of `(−y_j, y_l)`, with no `e_k`, no layer and no `z³`.
- **(c) YES in every cell gated (not proved):** `K_μ(n) = Q_μ(n) + box + N_{μ_1−1}(n) + (y_j^{q−ℓ}·Σ_{i<ℓ} y_j^i e_{f+ℓ−2−i}(y∖{y_j,y_l}))` equals the true casilla AS AN IDEAL in **40/40 cells** (all twelve profiles, q = 9, `n ≤ 6`; 4 cells at q = 27; and **`(1,1,1)` at `n = 7`, now resolved**). No failure found. First UNGATED cell: `(2,1)` at `n = 7` (7-variable cells with a non-redundant layer were skipped for budget).
- **(d)** **26 kinds, 48 row identities** (kind × needed `n`, `q` a letter), all of engine type, in 7 multi-part parents `(1,1), (2,1), (3,1), (2,2), (1,1,1), (2,1,1), (1^4)`; plus the char-3 Tanisaki colength for the leaves.
- **(e) NO.** Row `k = 4` still needs the value-0, lowering, new-class and raising rows of the multi-part casillas (4.2). This turn closed only the one-part rows and row 2 of `(m,1)`.

## STEP 0 — DESIGN AND SEALED BETS
**STATE: CLOSED.** Budget 15 min, no runs. **NEXT:** STEP 1 (A0 at (5,1), q = 9 and 27; A1 at (6,2), (6,1), (7,2), (7,3)).

### 0.1 Design
- **Reformulation used throughout (pencil, from §3.3.3 + §3.3.4 of the mission).** Put `d := q+c−1`, `c := n−m−1`, `B := (e_j : j odd or j ≥ n−m) + box + N_{m−1}(n)` (all of `B` is already PROVED inside `R_2(K_(m)(n+1))`). (G1) at `(j,l)` follows from ONE function identity on `W_(1)(n)`:
  `s_{jl} + L ≡ b (mod V_{d−2})`, with `L ∈ Ñ_{m−1}(n)_d`, `b ∈ B_{d−1}`, `V_{d−2}` = functions on `W_(1)(n)` of degree ≤ `d−2`.
  On `W_(1)(n)` the box and `e_odd` are absorbed in `V_{d−2}` automatically (`y^q = y`; `e_{2i+1} = −e_{2i}`), so only the layer monomials `y_a^{q−1}x_C` (`|A| = 1, |B| = m`), the squarefree `x_C` (`|C| ≥ n−m+1`), `e_n` and the even `e_{≥ n−m}` matter.
- **A0/A1 (M2):** `c := (matrix{{z²s}}) // gens E`, `E := I^{(n+1)} + z·Ñ_{m−1}(n) + (z³)`; reduce `c` modulo `image syz gens E` (normal form = canonical, no averaging); split by `z`-degree; tabulate by generator type. Estimates: 5 variables q = 9: < 5 s, < 200 MB; 5 variables q = 27: < 60 s, < 500 MB; 6 variables q = 9: < 20 s, < 300 MB; 7 variables q = 9 (alone): GB with change matrix ≤ 3 min, ≤ 800 MB (membership took 5 s last turn; lift + syz is the expensive part — if the syzygy module does not fit, only the lift is kept).
- **A1 in parallel (Python, exact on all points):** linear algebra on `W_(1)(n)` for the identity above; this gives the certificate in its function form, which is the one that can be read with letters.
- **B1 (M2):** fibre ideals of §3.4 over `GF(9)` (anchors: distinct classes), degrevlex GB, top forms, colength = fibre certificate; `DegreeLimit => q+f` for the 7-variable cells, alone.

### 0.2 Sealed bets (scored in STEP 5)
1. **(safe)** At `(5,1)` (q = 9 and 27) the reduced certificate's `z¹`-coefficient on the layer is the single monomial class `τ = y_j^{q−1}Π_P` of (D_k); nothing else of the layer enters.
2. **(risky)** At `(6,2)` the top form `L` can be taken as `y_j^{q−1}·e_c(y∖{y_j,y_l})` plus ONE `q`-free squarefree class `x_{[n]∖l}·g`, `g` a polynomial in `y_j,y_l` only (two ingredients, letters `q, c` only).
3. **(risky)** The reduced `(5,1)` certificate has the SAME number of terms at q = 9 and q = 27 (exponents affine in `q`): the lemma is Lucas-uniform.
4. **(risky)** The true casilla of `(1,1,1)` at `n = 7`, q = 9, is certified by colength 20370 with `DegreeLimit => 13` on the first try, and its new (non-`Q`, non-box) generators live in degree `q+f−2 = 11` and are NOT orbits of monomials (genuinely mixed).
5. **(safe)** Anchor-independence holds in every cell of B1 tested with two anchors.
6. **(risky)** The `(2,2,1)` family (n = 6, f = 1) has the three-part shape `y_j^{q−3}·(degree f+1 = 2)` of `(1,1,1)`, not the two-part `(m,1)` shape.
7. **(risky, about my own outcome)** I will NOT prove (G1) for all `m ≥ 2` with letters this turn; the most I expect with letters is the odd `m = 1` case or the certificate shape.

## STEP 1
**STATE: CLOSED.** Budget 55 min (A0 25 + A1 30); used ≈ 70 min (over by 15: the raw lift was unreadable and I switched to the function/first-order form). **NEXT:** STEP 2 — prove the certificate with letters.

### 1.0 Run log (estimates written before each run)
- `a0_9.m2` (`m10lift.m2`): lift + syzygy normal form at (5,1), q = 9. Estimate < 5 s, < 200 MB. Result: 2 s, 265 MB (`a0_9.log`).
- `a1fun.m2` (`m10fun.m2`): function-identity solver on `W_(1)(n)` at (5,1) q=9, (6,1), (6,2) q=9, (5,1) q=27. Estimate < 2 min, < 400 MB. Result: 61 s, 265 MB (`a1fun.log`).
- `a1alg.m2` (`m10alg.m2`): first-order algebraic solver at (6,2), (7,2), (7,3), n variables only (no `z`). Estimate written late (honest note: launched before writing it): 6 variables, ~ 5000 normal forms mod a monomial+box GB, < 5 min, < 500 MB.
- `a1alg.m2`: (6,2) general first-order A (1166 unknowns): **solvable** (11 s); single-variable descents `A_r = Σ_i g_i y_i^{n−2r−1}`: NOT solvable. Cell (7,2) (6 variables, general A): **WATCHDOG-KILLED at 570 s** (too many unknowns); `pgrep`: no M2 process remains (checked, logged).
- `a1alg2.m2`: divided-difference descents `A_r = g·h_{t−2r−1}(y_X)`, (6,2): `X = {j,l}` ALONE is solvable (0.8 s). Peak 1.09 GB on the widest variant (25 sets, 49925 unknowns) — under the cap but too close; narrower runs after this.
- `a1read.m2`: `S_P`-invariant `g`, `X = {j,l}`: solvable, but the minimal support has 44 terms (unreadable). q = 27 variant: WATCHDOG-KILLED at 570 s, `pgrep` clean.
- `a1sym.m2`: ansatz `A_r ∈ span{y_j^α y_l^β e_k(y)}`, estimate < 1 min, < 300 MB. Result 195 s, 267 MB (`a1sym.log`). **The greedy-minimal solution uses NO `e_k`: only `y_j, y_l`.**

### 1.1 A0 — the raw certificate at (5,1), q = 9, read against (D_k)/(B_k)
`z²s // gens E`, then normal form modulo `image syz gens E` (canonical by REDUCTION, rule 11). Result (`a0_9.log`): 17 nonzero coefficients of 27, 225 terms: `e_1, e_3, e_5` (with `z⁰, z¹, z²` parts), 4 box generators, 9 layer monomials `z·y_a^{8}x_C` of type `(|A|,|B|,|C|) = (1,1,2)`, `z³`.
- **The syzygy normal form is NOT the readable certificate.** Its layer part uses 9 monomials with `A ∈ {2,3,4}` (never `A = {j} = {1}`), whereas (D_k) uses the single `τ = y_1^{8}y_3y_4`. The normal form modulo syzygies is canonical but it is canonical for the monomial order, not for the mathematics: it trades `τ` for its `S_n`-translates plus `e_odd`-multiples. **Sealed bet 1 is FALSIFIED in its literal form** (the reduced certificate is not the single class `τ`); the function form below recovers `τ`.
- **Dictionary (D_k)/(B_k) ↔ certificate.** The `z⁰`-coefficient of `e_5` (`y_2^6 − y_3^6 − y_4^6`) together with the `z⁰`-box coefficient of `z^9` is the syzygy `A^0` («second order»): it is the Frobenius step 3 of (B_k) (`(a−b)^q ≡ 0` is a relation `Σ A^0_r e_{2r+1} ∈ box`). The `z¹`-coefficients of `e_1, e_3, e_5` are alternating sums `Σ_i (−1)^i y_a^{i}y_b^{8−i}` = `h`-type Lucas expansions `(a−b)^{q−1} = h_{q−1}(a,b)`-shapes (step 4). The layer coefficients `±1` are the top form `τ` (up to the translates chosen by the order). The generating identity (step 2) is invisible in the raw form because it is a relation among the `e_k` themselves.

### 1.2 The function form of the engine (all cells solvable)
Engine 3.3.3 in `n` variables: find `L ∈ Ñ_{m−1}(n)_d` (a MONOMIAL ideal — `e_n = x_{[n]}` is a monomial) and `b ∈ B_{d−1}` with `NF_{I(W_(1)(n))}(s+L−b)` of degree ≤ `d−2`; then `F := s+L−b−NF ∈ I(W)` has `F_d = L`, `F_{d−1} = s−b`, and the engine gives `s ∈ R_2`. Unknowns taken as `S_P`-orbit sums (invariant certificates exist — no averaging used). `a1fun.log`:
| cell `(n+1,m)`, q | `d` | standard monomials of degree ≥ `d−1` hit | rank | solvable with `S_P`-invariant `L, b` |
|---|---|---|---|---|
| (5,1), 9 | 10 | 6 | 1 | YES |
| (6,1), 9 | 11 | 89 | 15 | YES |
| (6,2), 9 | 10 | 187 | 34 | YES |
| (5,1), 27 | 28 | 6 | 1 | YES |

### 1.3 THE CERTIFICATES, READ (A1)
**Reformulation (pencil, PROVED).** Put `a := y_j`, `b := y_l`, `c := n−m−1`, `d := q+c−1`, `J := Ñ_{m−1}(n) + box + (e_n)` (a MONOMIAL ideal), `B := (e_k : k odd or k ≥ n−m) + box + N_{m−1}(n)`. If `A_0, A_1, …` are polynomials in `y` with
  **(T) `Σ_r A_r e_{2r+1}(y) ∈ J`** and **(Sh) `Σ_r A_r e_{2r}(y) ≡ s mod B`**,
then `s ∈ R_2(K_(m)(n+1))`. *Proof.* `z·Σ_r A_r e_{2r+1}(y,z) ∈ I^{(n+1)}` and it equals `z·Σ A_r e_{2r+1}(y) + z²·Σ A_r e_{2r}(y)`; `z·J ⊆ K_(m)(n+1)` (`zN_{m−1}(n) ⊆ N_{m−1}(n+1)`, `z·box`, and `z e_n(y)` is `e_{n+1}(y,z)` or a generator of `Ñ`); so `z²·Σ A_r e_{2r} ∈ K_(m)(n+1)`, i.e. the shadow lies in `R_2`, and `B ⊆ R_2` is PROVED (§3.2/§3.3.4). ∎ No `z³`, no `N_{m−2}`, no `W`. For `m ≥ 2` this first-order form is also NECESSARY for the engine: in degree `d` the layer `N_0(n)` is empty (its generators have degree ≥ `q+n−3 > d`), so every engine top form lies in `(e_odd)+box+(e_n)`.
**The certificate at every cell extracted (`a1sym.log`), cells (5,1), (6,1), (6,2) at q = 9 and (6,2) at q = 27:**
  **`A_r = (−1)^c · Σ_{i} (−a)^i b^{D_r−i}`, `D_r := q+c−2−2r`, the sum over `1 ≤ i ≤ q−1`, `1 ≤ D_r−i ≤ q−1`, for `0 ≤ r ≤ ⌊c/2⌋`; `A_r = 0` for `r > c/2`.**
  I.e. `A_r` is the complete symmetric polynomial `h_{D_r}(−a, b)` with its two pure powers removed (and box terms dropped): the **Lucas object** of (B_k). Modulo box, `A_r ≡ (−1)^c[h_{D_r}(−a,b) − b^{D_r} − (−a)^{D_r}]`. No `e_k(y)`, no layer monomial, no `y_p` (`p ∈ P`) enters the multipliers. Number of terms: 14 at q = 9 (8 + 6 or 7 + 7), 50 at q = 27 (26 + 24): **`(q−1) + (q−3)`** for `c` even, `(q−2)+(q−2)` for `c` odd.
- By TYPE of generator (the list A1 asks for): only `e_1` and `e_3` (in general `e_{2r+1}`, `2r+1 ≤ c+1`) carry coefficients; NO layer monomial, NO `e_n`, NO box generator is used as a generator (they are the ideal `J` the top lands in); the layer enters only as the TARGET of the top form: `(u b^{q−1} ± u^{q−1}b)·e_{c−1}(P)` (`u := −a`), i.e. the two `(q−1)`-monomials with `A = {j}` and `A = {l}` — «several `A`» of INFORME_9 is exactly `A = {j}` and `A = {l}`; the «`q`-free squarefree terms» are `u^ib^{i'}e_p(P)` with `p ≥ c` (support ≥ `c+2 = n−m+1`).

## STEP 2
**STATE: CLOSED.** Budget 40 min; used ≈ 45. **NEXT:** STEP 3 (PART B).

### 2.1 THEOREM ((G1) for every `m`, every `n`, every `q = 3^v ≥ 9`)
For `1 ≤ m`, `c := n−m−1 ≥ 1`, `j ≠ l`: **`s_{jl} := y_j^{q−2}e_c(y∖y_l) ∈ R_2(K_(m)(n+1))`.** In particular (G1) holds for `m ≥ 2` (all `n`) AND for `m = 1`, `n` odd. (At `q = 3` there are no generic rows.)

Notation: `a := y_j`, `b := y_l`, `u := −a`, `P := y∖{a,b}`, `N := q+c−2`, `D_r := N−2r`, `R := ⌊c/2⌋`, `H_D := Σ_{i=1}^{D−1} u^i b^{D−i}` (so `H_D = h_D(u,b) − u^D − b^D`). `J`, `B` as in 1.3. «≡» is modulo box unless said. Two facts used throughout:
- **(M) monomial criterion.** For `T ⊆ P`, `i, i' ≥ 1`: `u^ib^{i'}x_T ∈ N_{m−1}(n) + box + (e_n)` if `|T| ≥ c` (squarefree support ≥ `c+2 = n−m+1`), or `|T| = c−1` and `max(i,i') = q−1` (layer, `A = {a}` or `{b}`, `|C| = c`), or an exponent ≥ `q`; also a squarefree `x_T` with `|T| ≥ c+2` (the case of a zero exponent in Step 3 when `m ≥ q−1`). `J` and `N_{m−1}+box` are monomial ideals, so a polynomial lies in them iff each monomial does.
- **(E) expansion.** `e_k(y) = e_k(P) + (a+b)e_{k−1}(P) + ab·e_{k−2}(P) = e_k(P) + (b−u)e_{k−1}(P) − ub·e_{k−2}(P)`.

**The certificate.** `A_r := (−1)^c H_{D_r}` for `0 ≤ r ≤ R`, `A_r := 0` for `r > R`. (This is exactly the machine certificate of 1.3, box terms dropped.)

**Step 1 — first-order lemma (1.3):** it suffices that (T) `Σ_r A_r e_{2r+1}(y) ∈ J` and (Sh) `Σ_r A_r e_{2r}(y) ≡ s_{jl}` mod `B`.

**Step 2 — (T), by telescoping.** By (E), `(−1)^c·Top = Σ_p G(p)·e_p(P)` with
- `p = 2r+1` odd: `G(p) = H_{D_r} − ub·H_{D_{r+1}}` (second term present iff `r+1 ≤ R`);
- `p = 2r` even: `G(p) = (b−u)·H_{D_r}`.
Two telescopes: `ub·H_{D−2} = H_D − ub^{D−1} − u^{D−1}b` and `(b−u)H_D = ub^D − u^Db`. Hence for `p ≤ c−1` (then `r+1 ≤ R` automatically): `G(p odd) = ub^{q+c−2−p} + u^{q+c−2−p}b` and `G(p even) = ub^{q+c−2−p} − u^{q+c−2−p}b`. For `p ≤ c−2` the exponent is ≥ `q`: box. For `p = c−1` the exponent is `q−1`: by (M), `G(c−1)e_{c−1}(P) ∈ J`. For `p ≥ c` every monomial of `G(p)` has both exponents ≥ 1, so by (M) it lies in `J`. ∎(T)

**Step 3 — (Sh), the generating function.** Terms `e_k(y)`, `k` even `> c`, lie in `B`, so `(−1)^cΣ_rA_re_{2r} ≡ Σ_{k even} e_k(y)h_{N−k}(u,b) − (b^{D_R}+u^{D_R})e_{2R}(y)` mod `B` (the pure powers with `r < R` have exponent ≥ `q`). With `E(t) := Π(1+y_it)`, `H(t) := 1/((1−ut)(1−bt))` and `1/2 = −1` in `F_3`:
`Σ_{k even}e_kh_{N−k} = −[t^N](E(t)H(t) + E(−t)H(t))`, and `E(t)H(t) = E_P(t)(1+bt)/(1−bt) = E_P(t)(1 − Σ_{k≥1}b^kt^k)`, `E(−t)H(t) = E_P(−t)(1−at)/(1+at) = E_P(−t)(1 − Σ_{k≥1}u^kt^k)`.
Since `N > n−2`, `[t^N]` only sees `e_p(P)b^{N−p}` (resp. `u^{N−p}`) with `p ≤ n−2`; for `p ≥ c+1` these lie in `N_{m−1}` by (M), for `p ≤ c−2` in the box. What remains: `[t^N]E(t)H(t) ≡ −b^{q−2}(e_c(P) + b e_{c−1}(P)) = −s_{lj}` and `[t^N]E(−t)H(t) ≡ −(−1)^cu^{q−2}(e_c(P) − ue_{c−1}(P)) = (−1)^c s_{jl}` (using `u^{q−2} = −a^{q−2}`). So
  **`Σ_r A_r e_{2r}(y) ≡ −s_{jl} + (−1)^c[s_{lj} − (b^{D_R}+u^{D_R})e_{2R}(y)]` mod `B`.**

**Step 4 — three facts in `B` (pencil).**
- **(F)** `y_i^{q−2}e_c(y) ∈ B` for every `i`, and (c odd) `y_i^{q−1}e_{c−1}(y) ∈ B`. *Proof.* `y_i^{q−3}e_{c+1}(y) ∈ B` (`c+1 = n−m`) and `y_i^{q−3}e_{c+1}(y∖y_i)` has support `c+2` (M), so `y_i^{q−2}e_c(y∖y_i) ∈ B`. If `c` is even, `y_i^{q−1}e_{c−1}(y) ≡ y_i^{q−1}e_{c−1}(y∖y_i)` lies in `B` (`e_{c−1}` odd), and `y_i^{q−2}e_c(y) = y_i^{q−2}e_c(y∖y_i) + y_i^{q−1}e_{c−1}(y∖y_i)`. If `c` is odd, `e_c(y) ∈ B` directly, and then `y_i^{q−1}e_{c−1}(y∖y_i) = y_i^{q−2}e_c(y) − y_i^{q−2}e_c(y∖y_i) ∈ B`. ∎ (Uses `q ≥ 9` only through `q−3 ≥ 1`.)
- **(Sym), `c` even:** `s_{jl} + s_{lj} ∈ B`. *Proof.* `s_{jl}+s_{lj} = (a^{q−2}+b^{q−2})e_c(y) − W`, `W := (a^{q−2}b+ab^{q−2})e_{c−1}(P) + (a^{q−1}b+ab^{q−1})e_{c−2}(P)`; by (F) it suffices that `W ∈ B`. (i) Subtract `(a^{q−2}b+ab^{q−2})·e_{c−1}(y)` (∈ `B`, `c−1` odd): the residual is `−a²b²[(a^{q−4}+b^{q−4})e_{c−2}(P) + (a^{q−3}+b^{q−3})e_{c−3}(P)]`. (ii) For `γ ∈ (a²b²)`, `γe_{c−1}(P) ∈ B` (it is `e_{c+1}(y)·γ/(ab)` minus two terms of support ≥ `c+2`); so `γ[(a+b)e_{c−2}(P) + ab·e_{c−3}(P)] ∈ B`. With `γ = a²b²ρ`, `ρ := (a^{q−4}+b^{q−4})/(a+b)` (`q−4` odd), the residual becomes `−a²b²σ·e_{c−3}(P)`, `σ := (a^{q−2}+b^{q−2})/(a+b)`. (iii) Add `a²b²σ·e_{c−3}(y)` (∈ `B`, odd): the `(a+b)`-term is `a²b²(a^{q−2}+b^{q−2}) = a^qb²+a²b^q ≡ 0` (box!), leaving `a³b³σe_{c−5}(P)`; repeat with `e_{c−5}(y), e_{c−7}(y), …` (all odd): each step multiplies by `−ab` and lowers the `P`-degree by 2, until it is negative. ∎
- **(Anti), `c` odd:** `s_{jl} − s_{lj} ∈ B`. *Proof.* `s_{jl}−s_{lj} = (a^{q−2}−b^{q−2})e_c(y) − W^−`, `e_c(y) ∈ B`, `W^− := (a^{q−2}b−ab^{q−2})e_{c−1}(P) + (a^{q−1}b−ab^{q−1})e_{c−2}(P)`. For `γ ∈ (ab)`: `γ[(a+b)e_{c−1}(P) + ab·e_{c−2}(P)] ∈ B` (it is `γe_c(y)` minus `γe_c(P)`, of support ≥ `c+2`). With `γ = ab(a^{q−3}−b^{q−3})/(a+b)` the residual is `ab·τ'·e_{c−2}(P)`, `τ' := (a^{q−1}−b^{q−1})/(a+b)`; then add `−abτ'·e_{c−2}(y)` (odd): the `(a+b)`-term is `ab(a^{q−1}−b^{q−1}) = a^qb − ab^q ≡ 0` (box), leaving `−a²b²τ'e_{c−4}(P)`; repeat down to negative `P`-degree. ∎

**Step 5 — conclusion.** `c` even: `D_R = q−2`, `2R = c`, so by (F) the bracket's last term is in `B` and `Σ_rA_re_{2r} ≡ s_{lj} − s_{jl} ≡ −2s_{jl} = s_{jl}` by (Sym). `c` odd: `D_R = q−1`, `2R = c−1`, `u^{q−1} = a^{q−1}`, the last term is in `B` by (F), and `Σ_rA_re_{2r} ≡ −s_{jl} − s_{lj} ≡ −2s_{jl} = s_{jl}` by (Anti). So (Sh) holds, and by Step 1 `s_{jl} ∈ R_2(K_(m)(n+1))`. ∎

**Reading.** The two halves of the lemma are dual: the certificate's shadow is `s_{lj} − s_{jl}` (`c` even) or `−(s_{jl}+s_{lj})` (`c` odd), and the complementary half (`s_{jl}+s_{lj}`, resp. `s_{jl}−s_{lj}`) lies in `B` already. The whole proof uses exactly the three tools of (B_k): the generating identity (E)/(Step 3), Frobenius (the box kills `a^qb², a^qb`), and Lucas (the certificate IS `h_D(−a,b)` truncated; `(a^{q−1}−b^{q−1})/(a+b)` and `(a^{q−2}+b^{q−2})/(a+b)` are the Lucas quotients). The `z`-free, `W`-free, first-order form explains why the previous «first-order `u = y_i`» ansatz failed: it had only ONE variable; the certificate needs the divided difference in TWO (`y_j, y_l`).

### 2.2 Gates (exact, symbolic)
`a2ver6.m2` (`m10cert.m2`): the closed-form `A_r` satisfies (T) and (Sh) by exact normal forms modulo `gb J`, `gb B`, **19/19 cells**: q = 9, `n = 3..6`, all `m ≤ n−2` (incl. `(6,1)`, `(7,1)`, `(7,2)`, `(7,3)`); q = 27, `n = 3..5`; q = 81, `n = 3, 4` (`a2ver6.log`, 9 s, 266 MB). 7-variable cells `(8,m)`, `m = 1..5` (q = 9, run ALONE; estimate ≤ 4 min, ≤ 600 MB; actual 471 s, the (8,1) cell alone 433 s because `gb B` contains the `N_0(7)` layer — the known 424 s base): **5/5 TRUE**, including **(8,1) = `m = 1`, `n = 7` odd** (`a2ver7.log`). **Total 24/24 cells.** `pgrep` after the run: no M2 process.

### 2.3 Consequence: THE ONE-PART LINE
With §3.2 (rows 0, 1, `q−1` PROVED for all `q`) and `R_2 ⊇ B` (PROVED), 2.1 gives `R_2(K_(m)(n+1)) ⊇ K_{(m,1)}(n)` for every `m ≥ 1`, `n`, `q`; the generic rows `3..q−2` contain `R_2` (rows increase). **Every row inclusion of every one-part casilla `K_(m)(n+1)` is PROVED for all `q = 3^v`.** (The statement `T(n)` for the CHILD `(m,1)` — its colength bound — is a two-part matter, PART C.)

## STEP 3
**STATE: CLOSED** (as a measured uniform formula; NOT a theorem). Budget 50 min; used ≈ 45. **NEXT:** STEP 4 (ledger).

### 3.1 B1 — the truth (runs `b1small.m2`, `b1n7.m2`, lib `m10cas.m2`)
Fibre ideal of §3.4 over `GF(9)`, degrevlex GB, top forms, colength certificate. Anchors: class representatives `α^0, α^1, α^2, …` and, for the anchor test, `α^3, α^2, …` (reversed) — two different anchor multisets per profile.
- `b1small.m2` (estimate ≤ 2 min, ≤ 400 MB; actual 29 s, 267 MB): **all 12 profiles, every non-empty `n ≤ 6` at q = 9: 35 cells, colength = fibre in 35/35, anchor-independence (equality of ideals) in 35/35** (`b1small.log`). Minimal generators by degree (degree `(d, #)`), e.g. `(2,1)`, n = 6: `(1,1),(3,1),(4,1),(5,6),(9,5),(10,9),(11,16)`; `(1^4)`, n = 6: `(1,1),(3,1),(4,1),(5,1),(6,1),(9,15)`.
- **`(1,1,1)` at `n = 7`, q = 9** (`b1n7.m2`, ALONE; estimate 1–5 min, ≤ 1 GB): `DegreeLimit` 11, 12, 13, 14 → colength 25592; 15 → 23471; 16 → 22337; **17 → 20370 = `|W_{(1,1,1)}(7)|`: the true casilla, certified** (cumulative 51 s, 300 MB; `b1n7.log`, `b1n7b.log`). Minimal generators by degree: `(1,1), (3,1), (5,1), (6,1), (7,1), (9,6), (11,15)`. So: `Q` (degrees 1, 3, 5, 6, 7), the box (7 generators, one redundant, as predicted), and **15 generators in degree 11 = `q+f−2`**, genuinely MIXED (16 to 936 terms). The 16-term generator reads
  `x_7^{6}·x_2x_3x_4x_5x_6 + x_7^{7}·e_4(x_2..x_6) + x_7^{8}·e_3(x_2..x_6)` = **`y_j^{q−3}·Σ_{i=0}^{2} y_j^i·e_{5−i}(y∖{y_j,y_l})`** with `j = 7`, `l = 1`.
  The two-part family is the same object with ℓ = 2: `y_j^{q−2}e_f(y∖y_l) = y_j^{q−2}·Σ_{i=0}^{1} y_j^i e_{f−i}(y∖{y_j,y_l})`.

### 3.2 B2 — ONE uniform formula, read off B1, gated AS IDEALS
**`K_μ(n) := Q_μ(n) + box + N_{μ_1−1}(n) + F_μ(n)`**, `F_μ(n) := (φ^{(ℓ)}_{jl} : j ≠ l)`,
  **`φ^{(ℓ)}_{jl} := y_j^{q−ℓ} · Σ_{i=0}^{ℓ−1} y_j^{i} · e_{f+ℓ−2−i}(y∖{y_j,y_l})`**  (ℓ = number of parts, `f = n−|μ|`),
equivalently `φ^{(ℓ)}_{jl} ≡ y_j^{q−ℓ}·[u^{f+ℓ−2}] E_{y∖{y_j,y_l}}(u)/(1−y_ju)` modulo box: **the elementary symmetric function of `y∖{y_j,y_l}` with `y_j` counted as a BOSON** (complete-symmetric in `y_j`, elementary in the rest), cut by the box at `y_j`-exponent `q−1`. Degree `q+f−2` for every `μ`. For ℓ = 2 it is exactly the (G1) family `y_j^{q−2}e_f(y∖y_l)`; for ℓ = 3 it is the 16-term generator read at `n = 7`. `Q_μ` is §3.3.8; the layer weight is `w = μ_1 − 1` (for two parts this agrees with `|μ|−ℓ−1` when `μ_2 ≥ 2` and with `m−1` for `(m,1)`; for `(1^ℓ)` it is `N_0`, redundant).
**Gates (equality of ideals with `G_μ(n) = gr I(W_μ(n))`), `b2gate.log`, `b2gate2.log`, `b2gate3.log`, `b2n7.log`:**
| set of cells | cells | `K_μ == G_μ` |
|---|---|---|
| q = 9, `f ≥ 2`, `n ≤ 6`: `(1,1)` n = 4,5,6; `(2,1)` n = 5,6; `(3,1), (2,2), (2,1,1), (1^4)` n = 6; `(1,1,1)` n = 5,6 | 11 | **11/11** |
| q = 9, leaves `f ≤ 1`, all twelve profiles, `n ≤ 6` | 24 | **24/24** |
| q = 27, `(1,1)` n = 4,5; `(2,1)` n = 5; `(1,1,1)` n = 5 | 4 | **4/4** |
| q = 9, **`(1,1,1)`, n = 7** (`N_0` omitted, redundant for `(1^ℓ)`) | 1 | **1/1** |
**40/40.** Runs: `b2gate.m2` (3 variants per cell; watchdog-killed at 570 s after 5 cells — all 5 equal with `w = μ_1−1`; `pgrep` clean), `b2gate2.m2` (12 s), `b2gate3.m2` (42 s, 267 MB), `b2n7.m2` (ALONE, estimate ≤ 4 min / 800 MB; actual 48 s, 284 MB). Not gated (7-variable cells with a non-redundant layer: `(2,1), (2,2), (3,1), (4,1), (3,2), (2,1,1), (3,1,1), (2,2,1), (1^4), (2,1,1,1)` at n = 7): skipped for budget, the `N_{w}(7)` base costs ~ 424 s each.
- **The first-factor THRESHOLD of §3.3.9 is explained:** `y_j^{q−ℓ+i}` for `i ≥ ℓ` is box, so any exponent `a ≤ q−ℓ` with the same boson sum generates the same ideal, and a monomial orbit can never equal the boson sum (hence «no two-variable monomial works» at `n = 7`: the family is not an orbit of monomials once `f+ℓ−2 ≥ 2` and `|y∖{j,l}|` is large enough to separate the `e_{t−i}`). At `n ≤ 6` the old monomial families `y_j^{q−3}y_l^{f+1}`, `y_j^{q−4}y_l^{f+2}` happened to generate the same ideal modulo the rest.
- **(1,1,1) at n = 7: RESOLVED** (the family came OUT of B1).

### 3.3 B3
- **Uniform degree `q+f−2`: YES** in every cell computed (by the formula and by the minimal generators of the true casilla: `(1,1,1)` n = 7 has its family in degree 11 exactly). No exception found.
- **Anchor-independence: YES, 35/35** cells (all twelve profiles, `n ≤ 6`, q = 9, two different anchors each).

## STEP 4
**STATE: CLOSED** (the ledger is complete; the row is NOT closed). Budget 25 min; used ≈ 20. **NEXT:** STEP 5.

`A_4(q) = P_4(q)` is `T(10)` at `∅`; it needs `T(n)` at every `(μ, n)` with `|μ| ≤ min(n, 10−n)`, `n ≤ 9` (the set is closed under children: `|μ ∪ (1)| ≤ 10−(n−1)`). A cell needs rows only if `f = n−|μ| ≥ 2`; so the multi-part NON-LEAF parents are exactly those with `|μ| ≤ 4`, `|μ|+2 ≤ n ≤ 10−|μ|`. Rows written for the parent `K_μ(n)` (variables `y, z`), children at level `n−1` with the uniform `K` of 3.2. «First row of a block» only.

### 4.1 PROVED rows
| parent `(μ, n)` | rows → child | status |
|---|---|---|
| `∅`, n = 2..10 | row 0 → `∅`; rows `1..q−1` → `(1)` | PROVED (trivial; casilla theorems) |
| `(m)`, `m = 1..4`, `m+2 ≤ n ≤ 10−m` | row 0 → `(m−1)`; row 1 → `(m)`; row `q−1` → `(m+1)` | PROVED (§3.2) |
| same | **rows `2..q−2` → `(m,1)`** | **PROVED this turn (Theorem 2.1)** |
| `(m,1)`, `m = 1,2,3` (`(1,1)`: n = 4..8; `(2,1)`: n = 5..7; `(3,1)`: n = 6) | row 0 → `(m−1,1)`; row 1 → `(m)` | PROVED (§3.3.6) |
| same | **row 2 → `(m,1)`** | **PROVED this turn** (§3.3.6 «row 2 given (G1)» + Theorem 2.1) |
| leaves `f ≤ 1` | no rows; `T` by the count | Tanisaki colength — MEASURED (16 cells + 24 ideal gates here), classical in char 0; **a char-3 proof of `dim S/(I_λ+box) ≤ n!/Πλ_i!` is still owed** (it is the Garsia–Procesi spanning set; I did not check it) |

### 4.2 The remaining row identities (all of ENGINE type: one membership `z^{a−1}f ∈ (I^{(n)}:z) + (M:z) + (z^a)`, i.e. one identity on `W_(1)(n−1)`; none proved with letters)
| # | parent | row → child | kind | `n` needed | smallest test cell |
|---|---|---|---|---|---|
| 1 | `(1,1)` | rows `3..q−3` → `(1,1,1)` | new class | 4..8 | `(1,1)`, n = 5 (q = 9) |
| 2 | `(1,1)` | rows `q−2, q−1` → `(2,1)` | raise | 4..8 | n = 4 |
| 3 | `(2,1)` | rows `3..q−3` → `(2,1,1)` | new class | 5..7 | n = 6 (INFORME_9: row 3 of `K_{(2,1)}(6)`) |
| 4 | `(2,1)` | row `q−2` → `(2,2)` | raise small | 5..7 | n = 6 |
| 5 | `(2,1)` | row `q−1` → `(3,1)` | raise large | 5..7 | n = 5 |
| 6–8 | `(3,1)` | new class → `(3,1,1)`; raise → `(3,2)`; raise → `(4,1)` | as 3–5 | 6 | n = 6 |
| 9 | `(2,2)` | rows 0, 1 → `(2,1)` | lower | 6 | n = 6 |
| 10 | `(2,2)` | row 2 → `(2,2)` | value 0 | 6 | n = 6 |
| 11 | `(2,2)` | rows `3..q−3` → `(2,2,1)` | new class | 6 | n = 6 |
| 12 | `(2,2)` | rows `q−2, q−1` → `(3,2)` | raise | 6 | n = 6 |
| 13 | `(1,1,1)` | rows 0..2 → `(1,1)` | lower | 5..7 | n = 5 |
| 14 | `(1,1,1)` | row 3 → `(1,1,1)` | value 0 | 5..7 | n = 5 |
| 15 | `(1,1,1)` | rows `4..q−4` → `(1^4)` | new class | 5..7 | n = 5 |
| 16 | `(1,1,1)` | rows `q−3..q−1` → `(2,1,1)` | raise | 5..7 | n = 5 |
| 17–22 | `(2,1,1)` | lower → `(1,1,1)`; lower → `(2,1)`; value 0; new class → `(2,1,1,1)`; raise → `(2,2,1)`; raise → `(3,1,1)` | | 6 | n = 6 |
| 23–26 | `(1^4)` | lower → `(1^3)`; value 0; new class → `(1^5)` (only `q ≥ 27`); raise → `(2,1,1,1)` | | 6 | n = 6 |
**Count: 26 kinds; as individual row inclusions (kind × needed `n`): 2·5 + 3·3 + 3 + 4 + 4·3 + 6 + 4 = 48**, each an identity in a FIXED number of variables with `q` as a letter. Two families of kinds: (i) **value-0 rows of multi-part casillas** (#10, 14, 19, 24: `R_ℓ(K_μ(n)) ⊇ K_μ(n−1)`) — these are the direct generalisation of Theorem 2.1 (ℓ = 2 → general ℓ, first factor `y_j^{q−ℓ}`, boson sum); (ii) **lower / new-class / raise rows** of multi-part casillas, which INFORME_9 showed are layer shadows (new class) and family shadows (raise `q−2`) at 5 cells.

### 4.3 Payoff
**ROW `k = 4` IS NOT CLOSED.** What this turn removed from the ledger: every row of every ONE-PART casilla (all `q`), and row 2 of every `(m,1)` casilla. What remains: the 26 kinds above, the smallest being `(1,1)` at n = 4 (raise, #2) and `(1,1,1)` at n = 5 (#13–16) — 4–5 variables, cheap enough for the same machine-then-read method that produced Theorem 2.1.

## STEP 5 — VERDICT
**STATE: CLOSED.** Disk re-read before writing (all steps present). No M2 process of mine is running (`pgrep`: none).

**Prize: GOOD — «ONE-PART LINE CLOSED FOR ALL q».** Minimum (a new infinite family proved with letters + the certificates written explicitly): yes, twice over (`m ≥ 2` and `m = 1` odd, one proof). EXCELLENT: half. The uniform `K_μ` exists and equals the truth as an ideal in every cell I gated (40/40, including the one that beat two missions). But it is not gated at the 7-variable non-redundant-layer cells and it is not proved; the ledger is reduced to engine identities but not to identities «of the type proved». FULL: no.

**What is PROVED this turn (proofs in the report):**
1. First-order lemma (1.3): `(T) + (Sh) ⟹ shadow ∈ R_2`; for `m ≥ 2` the engine is necessarily first order (no `N_0` in degree `d`).
2. Theorem 2.1: (G1) for all `m ≥ 1`, `n`, `q ≥ 9`, with the explicit Lucas certificate.
3. The facts (F), (Sym) (`c` even), (Anti) (`c` odd) in `B`: `y_i^{q−2}e_c(y) ∈ B`, `s_{jl} ± s_{lj} ∈ B`, each a descending telescope killed by the box.
4. Consequence 2.3: all rows of all one-part casillas.
**What is MEASURED (gates only):** the uniform `K_μ` (40 cells), anchor independence (35 cells), the certificate formula (24 cells, which the pencil proof covers anyway).

**Sealed bets — scored, same size:**
| # | bet | verdict |
|---|---|---|
| 1 | (5,1) reduced certificate's layer = single class `τ` | **FALSIFIED** (the syzygy normal form uses 9 translates; the Lucas certificate uses no layer generator at all) |
| 2 | (6,2) top form = `y_j^{q−1}e_c(P)` + one squarefree class | **FALSIFIED** (top form = two layer classes `A = {j}`, `A = {l}` at `P`-degree `c−1` + many squarefree `u^ib^{i'}e_p(P)`) |
| 3 | same number of terms at q = 9 and 27 | **FALSIFIED** (14 vs 50 = `2q−4`); its spirit («Lucas-uniform, exponents affine in `q`») HIT |
| 4 | `(1,1,1)` n = 7 certified at `DegreeLimit 13` first try; family in degree 11, mixed | **FALSIFIED** (needed 17); the second half HIT (15 mixed generators in degree 11) |
| 5 | anchor-independence everywhere | **HIT** (35/35) |
| 6 | `(2,2,1)` family has the three-part shape | **UNRESOLVED** (only leaf cells `f ≤ 1` computed; the ℓ = 3 uniform formula passes there, but so might others) |
| 7 | I will NOT prove (G1) for `m ≥ 2` | **FALSIFIED** |
Hits 1 (+2 halves), falsified 5, unresolved 1.

**Routes that die, with the reason (results):** (i) reading the certificate from the syzygy normal form of the raw `z`-lift: it is canonical for the monomial order, not for the mathematics (9 translates of `τ`, 225 terms at the smallest cell); (ii) single-variable descents `A_r = Σ_i g_i y_i^{n−2r−1}`: never enough at (6,2), because the certificate needs a divided difference in TWO variables; (iii) the general first-order solve in 6 variables: killed (too many unknowns), while the `(y_j, y_l, e_k)` ansatz was the right size.

## WHAT I FOUND BEAUTIFUL
The lemma that four Gröbner certificates were hiding is a single line in two letters: the complete symmetric polynomial `h_D(−y_j, y_l)` with its two pure powers cut off. It is the same Lucas object that (B_k) used, now doing all the work for every `m` and both parities at once. What surprised me most is that the «second-order» certificate is first order: the box, which I expected to be an obstacle, is exactly what kills every residual (`a^qb²`, `a^qb` vanish). The two halves of the proof are dual: the certificate's shadow is `s_{lj} − s_{jl}` when `c` is even and `−(s_{jl}+s_{lj})` when `c` is odd, while the other half lies in `B` for free. Then B1 read the `(1,1,1)` family at `n = 7` that no guess had found. In it `y_j` enters as a boson (complete-symmetric) while the other variables stay fermions (elementary), and the box cuts the boson at `q−1`, which is why the first factor has a THRESHOLD `q−ℓ` rather than an exponent. If this were my problem, I would now prove the value-0 row `R_ℓ(K_μ(n)) ⊇ K_μ(n−1)` for ℓ = 3 by the same recipe: a certificate in the divided differences of three variables, extracted at `(1,1,1)`, n = 5, with a `(y_j, y_l, y_k, e_k)` ansatz.

## FOR MISSION 11
- **The engine that works:** the FIRST-ORDER Lucas certificate. For a row inclusion `f ∈ R_a(K)`, look for multipliers `A_r` in the few variables that `f` distinguishes (here `y_j, y_l`), with `Σ A_r e_{2r+1}` in the monomial ideal `J` and `Σ A_r e_{2r} ≡ f` modulo the already-proved part. Solve it by machine in the small ansatz `span{monomials in the distinguished variables × e_k(y)}` (`m10alg.m2` + `a1sym.m2` pattern: 0.03 s at 5 variables), then read the closed form. Prove (T) by the two telescopes, and (Sh) by the generating function `E(t)/((1−ut)(1−bt))` plus a descending telescope in `B`. For rows `a ≥ 3` the row formula has `c^0, …, c^{a−1}`: expect `a−1` layers of the same object.
- **Smallest open cell of each kind** (4.2): the raise row of `(1,1)` at n = 4 (#2); the new-class row of `(1,1)` at n = 5 (#1); the four rows of `(1,1,1)` at n = 5 (#13–16), where the value-0 row #14 is the ℓ = 3 analogue of Theorem 2.1 with family `y_j^{q−3}(e_{f+1}(P) + y_je_f(P) + y_j²e_{f−1}(P))`; `(2,1)` row 3 at n = 6 (#3); `(2,2)` at n = 6 (#9–12).
- **Casilla:** gate the uniform `K_μ` of 3.2 at the 7-variable non-redundant-layer cells (`(2,1)`, `(2,2)`, `(3,1)`, `(2,1,1)`, `(1^4)` … at n = 7), one per run and ALONE, about 7–8 min each because of `N_w(7)`. Also gate it at q = 27, n = 5 for the three-part profiles. Then prove its inclusion `K_μ ⊆ gr I(W_μ)`: each `φ^{(ℓ)}_{jl}` is the top form of an explicit function on `W_μ`. Find that function from the §3.4 GB; `(1,1,1)` at n = 7 showed it is readable.
- **Leaves:** a char-3 proof (or citation) that `dim S/(I_λ + box) ≤ n!/Πλ_i!` (the Garsia–Procesi spanning set over `Z`).
- **Estimate for closing row `k = 4`:** 26 kinds. The value-0 rows (4 kinds) may go by the ℓ-variable Lucas certificate, and the lower/new-class/raise rows by one more descent each. If so, that is 2–3 missions of this size. The risk is the new-class rows (layer shadows, INFORME_9), which are genuinely second order in `z`.

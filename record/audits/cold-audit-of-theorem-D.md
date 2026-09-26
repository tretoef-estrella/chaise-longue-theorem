# MISIÓN 96 — COLD AUDIT OF THEOREM D (INFORME_15 of the Fable) — Grepy el Auditor, 2026-09-24

## FIRST LINE
STATE: CLOSED

**THEOREM D HOLDS. Every item C0–C10 is CORRECT.**
- **Conjecture 1.2 of Degtyarev–Shimada is proved for `m = 3^v` and every even dimension `2k`.** The chain is:
  - the translation to (S) (C0, from the original; `≤` proved);
  - the peeling identity (C1);
  - the pattern identities (C2);
  - the root `V_{(1)} = (D_J)C`, `Z_{(1)} = Γ'` (C3);
  - fibres, chain and down-set heredity (C4–C6);
  - the three constructions (C7);
  - the induction (C8).
- **No gap and no error.** Recorded:
  - one typo in the handoff file (`N = 2k+2`);
  - one slip in DS §5 (`d_0`), which does not affect anything;
  - two loose phrasings in the Fable's P2, both closed here.
- **Independent gates, own code, different in structure from the Fable's and the Lector's:**
  - EVERY down-set at 19 cells (P1/P2/P3: 0 failures; negative controls fire);
  - EVERY down-set at `(q,m) = (9,4)`, `(9,3)`, `(3,4..6)` algebraically: `dim V_Λ = |Z_Λ|`, 0 failures;
  - the literal (S) at `(3,3)`, `(2,9)` and the subfamily, with a third engine;
  - the May log `(3,9) = 190120` as an out-of-sample confirmation made four months earlier.

## C0 · The translation, cold from the original
STATE: CLOSED — CORRECT (one typo in the handoff file, no mathematical gap)

Source: arXiv:1405.4683v3 (the highest version; local copy `~/Desktop/CLAUDE/HODGE/1405.4683v3.pdf`). The definitions are on p. 2, Conjecture 1.2 and Definition 1.3 on p. 3, and §4.3–4.4 on p. 13.

**Conventions.** In DS, `J = [[j_0,k_0],…,[j_d,k_d]]` with `j_i < k_i` and `j_0 < ⋯ < j_d`, so `j_0 = 0`. They put `τ_J = Π_{i=0}^{d}(t_{k_i}−1)` and `ψ_J = τ_J·Π_{i=1}^{d}φ(t_{j_i}t_{k_i})`. The ring is `R = Z[t_1..t_{n+1}]/(t_i^m−1)` with `t_0 = (t_1⋯t_{n+1})^{−1}`. The variable `t_0` never appears in `ψ_J`: the pair containing 0 contributes only `(t_{k_0}−1)`.

**Step 1 (torsion ⟺ one dimension).**
- Theorem 1.1(a) gives `Tors(H_n/L_K) ≅ Tors(R/(ψ_J))`.
- `A := R/(ψ_J)` is a finitely generated abelian group, `A ≅ Z^ρ ⊕ ⊕_p T_p`. Then `dim_{F_p}(A⊗F_p) = ρ + (number of cyclic factors of T_p)`, by right exactness of `⊗`.
- So `A` is torsion free ⟺ `dim_{F_p} = ρ` for every `p`.
- By Cor 1.5 only `p | m` can occur; for `m = 3^v` that is `p = 3`.
- `ρ = dim_Q(A⊗Q) = m^{n+1} − |Γ_J|` by Claim 4.3 with `p = 0`. DS say the same themselves in §4.3: «`A_K` has a torsion element of order p iff `dim_{K_p}(A_K⊗K_p) > dim_C(A_K⊗C)`».
- **CORRECT.**

**Step 2 (`|Γ_J|`).**
- Definition 1.3: `a_i ≠ 1` for `i = 1..n+1`, and `a_{j_i}a_{k_i} = 1` for `i = 1..d`, for some `J`.
- Then `Π_{i≥1}a_i = a_{k_0}`, so `a_0 = a_{k_0}^{−1} ≠ 1` holds automatically.
- Hence `Γ_J` is in bijection with the `(2k+2)`-tuples of `μ_q∖{1}` whose multiset closes under inversion (the product is then 1 automatically).
- There are `h = (q−1)/2` inverse classes. The exponential formula gives `|Γ_J| = N![x^N]I_0(2x)^h` with **`N = 2k+2`**.
- ⚠️ **TYPO in `GREPY_ARRANQUE_270_GREPY_EL_AUDITOR.md` §3:** it writes «`N = 2k+1`». MISION_15 §1.2 correctly has `N := 2k+2`. The formula with `N = 2k+1` would give 0 (odd power of an even series).
- External gate against DS Remark 4.4, whose printed polynomials are `|Γ|` (the text says rank = `1+|Γ|`; the display is off by one):
  - `n = 2`: `3m²−9m+6` gives `6` at `m = 3` and `168` at `m = 9`.
  - `n = 4`: `15m³−90m²+175m−100` gives `20` at `m = 3`.
  - All three match `Q_1(3) = 6`, `Q_1(9) = 168`, `Q_2(3) = 20`.
- Own enumeration this morning (my scratchpad `sub9.py`): `|Γ|` is `70` at `(3,3)`, `5120` at `(2,9)`, and `4736` for the subfamily of §2.3.
- **CORRECT.**

**Step 3 (the coordinate `y`).** In `F_3[t]/(t^q−1)`, `t^q − 1 = (t−1)^q`.
- `t` and `t+1 = 2+(t−1)` are units, and `y := t−t^{−1} = t^{−1}(t−1)(t+1)` is a unit times `t−1`. So `F_3[t]/(t^q−1) = F_3[y]/(y^q)`.
- `y_j+y_k = (t_j+t_k)(1−(t_jt_k)^{−1}) = (t_j+t_k)(t_jt_k)^{−1}(t_jt_k−1)`, with `t_j+t_k` a unit. I multiplied it out by hand.
- `φ(u) = (u^q−1)/(u−1) = (u−1)^{q−1}`.
- **CORRECT.**

**Step 4 (the factor `Y`).**
- In characteristic 3, `(a+b)^{q−1} = (a^q+b^q)/(a+b) = Σ_{s=0}^{q−1}(−1)^s a^s b^{q−1−s}`, because `q` is odd.
- Multiply by `b` and drop `b^q = 0`: `Σ_{s=1}^{q−1}(−1)^s a^s b^{q−s} = −ab·Σ_{u=0}^{q−2}(−1)^u a^u b^{q−2−u} = −ab·D(a,b)`.
- In `ψ̄_J` each pair `(j_i,k_i)`, `i ≥ 1`, carries `y_{k_i}·(y_{j_i}+y_{k_i})^{q−1}·unit`, and the pair `(0,k_0)` carries `y_{k_0}·unit`. So `ψ̄_J = ±unit·Y·D_J`, where `{k_0} ∪ ⋃_{i≥1}{j_i,k_i} = [1, 2k+1]`.
- `Y·y^α ≠ 0` in `B = F_3[y]/(y^q)` ⟺ every `α_i ≤ q−2`. So `ker(×Y) = (y_i^{q−1})B`, and `×Y` induces an injection `C ↪ B`.
- The ideal `(ψ̄_J)B` is `Y·((D_J)B)`, which is the injective image of `(D_J)C`. Hence `dim F_3[G]/(ψ̄) = q^{2k+1} − dim(D_J)C`.
- **Independent confirmation from DS itself.** Their Lemma 4.5, `(y−1)φ(xy) = −(x−1)(y−1)ρ(x,y)`, gives `ψ_J = ±λρ_J` with `λ = Π(t_i−1)`, which is this same lemma in DS's variables.
  - In `C`, `ρ_J = unit·D_J`. Checked by hand at `q = 3`: `ρ = (y_x−y_y)(1+y_y)`.
  - So (S) is exactly DS's own §5 criterion `d_p = d_0`, transported to `y`.
- **CORRECT.**

**DS §5 slip (recorded).** DS write `d_0 := dim_C(B_K⊗C) = |Γ_K|`. It should be `(m−1)^{n+1} − |Γ_K|`, because `(ρ_J)` vanishes on the complement of `Γ_K`. Proof by exact sequence: `dim R/(λρ) = m^{n+1}−|Γ|` and `dim R/(λ) = m^{n+1}−(m−1)^{n+1}`. The May log `~/Downloads/HODGE_ENGINE_v3_n10_m3.txt` confirms it: `dim_Rbar = 2048` and `dim B_K = 1124 = 2048 − 924`. The criterion itself is unaffected.

**Conclusion C0.** DS 1.2 at `(k, q = 3^v)` ⟺ (S) `dim_{F_3}(D_J : J ∈ J)C = Q_k(q)`, and `≤` holds. Theorem D only needs `≥`.

## C1 · The peeling identity
STATE: CLOSED — CORRECT

Let `C_m = F_3[y_1..y_m]/(y_i^{q−1})` and `C_m = C_{m−1}[y_1]/(y_1^{q−1})`, where `C_{m−1}` is in `y_2..y_m`. Let `V ⊆ C_m` be an ideal.
- Put `V_{≤j} := {f ∈ V : deg_{y_1} f ≤ j}` and `W_j := {[y_1^j]f : f ∈ V_{≤j}}`, for `0 ≤ j ≤ q−2`.
- The map `f ↦ [y_1^j]f` goes from `V_{≤j}` onto `W_j`, with kernel `V_{≤j−1}`. So `dim W_j = dim V_{≤j} − dim V_{≤j−1}`, and since `V = V_{≤q−2}`, **`dim V = Σ_{j=0}^{q−2} dim W_j`**.
- `W_j` is an ideal of `C_{m−1}`: for `g ∈ C_{m−1}`, `gf ∈ V_{≤j}` and `[y_1^j](gf) = g[y_1^j]f`.
- **`W_j ⊆ W_{j+1}` for `j+1 ≤ q−2`:** `y_1f ∈ V` has `y_1`-degree `≤ j+1`, and `[y_1^{j+1}](y_1f) = [y_1^j]f`. This uses `y_1^{j+1} ≠ 0`, i.e. `j+1 ≤ q−2`; that is exactly the range of `j`.

For `Z ⊆ T^m`, `T = F_q^×`, `π` forgets `y_1`. With `F(M') = {y : (y,M') ∈ Z}` and `Z_{>i} = {M' : |F(M')| > i}`, we have **`|Z| = Σ_{M'}|F(M')| = Σ_{i=0}^{q−2}|Z_{>i}|`**, since `|F| ≤ q−1`.

## C2 · The pattern lemmas L2, L2', L3
STATE: CLOSED — CORRECT

- **Coefficient of `D`.** `D(a,b) = Σ_{u=0}^{q−2}(−1)^u a^u b^{q−2−u}`. Then `[a^{q−2−t}]D(a,b) = (−1)^{q−2−t}b^t = (−1)^{t+1}b^t`, because `q−2` is odd.
- **Vandermonde / cofactor identity.** Let `S = {b_1..b_r}` and `Δ(S) = det(y_{b}^{e})`, with columns `b ∈ S` and rows `e = 0..r−1`. Replace the last row `y_b^{r−1}` by `y_b^t` and expand along it: `Σ_{b∈S} ε_bΔ(S∖b)y_b^t`.
  - For `t ≤ r−2` the matrix has two equal rows, so the sum is **0**.
  - For `t = r−1` it is **`±Δ(S)`**.
  - This is an identity over `Z`, hence over `F_3`. Inside `C` no exponent exceeds `r−1 ≤ h−1 < q−1`, so the box truncates nothing.
- **Top coefficient of a block.** `Δ(B∪{1}) = ±Π_{c∈B}(y_1−y_c)·Δ(B)`. It has `y_1`-degree `|B|` and top `y_1`-coefficient `±Δ(B)`, and `|B| ≤ h < q−1`.
- **L2** (the combination `f = Σ_b ε_bΔ(S∖b)D(y_1,y_b)G`, `|S| = r`):
  - `[y_1^{q−2−t}]f = (−1)^{t+1}(Σ_b ε_bΔ(S∖b)y_b^t)·G`. This is `0` for `t ≤ r−2` and `±Δ(S)G` for `t = r−1`.
  - So `deg_{y_1}f ≤ q−1−r`, with top coefficient `±Δ(S)G`.
  - `G` must avoid `S` and the index 1. It does in P3(γ), where `G'` is the rest of the pattern.
- **L2′ and L3** are special cases of the same two identities.
- The Fable checked all of them exactly (`~/Desktop/FABLE_TABLERO/idcheck.py`, `idcheck.log`: all OK at `q = 9, 27`). I re-derived them by hand above.

## C3 · Notation and root
STATE: CLOSED — CORRECT

- **Residue and `λ`.** `T = F_q^×` has `h = (q−1)/2` classes `{u,−u}`, and `−1` has no fixed point (`q` odd).
  - For a multiset `M` and a class with multiplicities `a` (of `u`) and `ā` (of `−u`), a maximal set of disjoint negation pairs uses `min(a,ā)` pairs in that class. The classes are independent, so `ν(M) = Σ min`.
  - The residue keeps `|a−ā|` copies of the majority value. `λ(M)` = the multiplicity partition of the residue. It is well defined, has `ℓ(λ) ≤ h` and `|λ| ≡ |M| (mod 2)`.
- **Weak dominance.** `λ ≼ μ` ⟺ `S_t(λ) ≤ S_t(μ)` for every `t`, where `S_t` is the sum of the `t` largest parts and parts are padded by 0. Equal sizes are NOT required.
- **Tight pattern** of `λ` on an index set `I` with `|I| = m`: `(m−|λ|)/2` disjoint pairs `P`, plus disjoint blocks `B_c` with `|B_c| = λ'_c`, filling the rest. The product is `D_P·Π_cΔ(B_c)`. It is nonzero in `C_m`: disjoint variables, and exponents `≤ q−2` in `D` and `≤ h−1` in each `Δ`.
- **Root.**
  - `Λ = {(1)} ⊆ Par_{2k+1}` is a down-set. If `λ ≼ (1)`, then `S_t(λ) ≤ 1` for every `t`, so `|λ| ≤ 1`; oddness forces `λ = (1)`.
  - The tight patterns of `(1)` are `k` disjoint pairs of `[2k+1]` plus a singleton block (`Δ = 1`), i.e. `D_P`. Every such `P` is the set of pairs of a matching `J` avoiding 0 (pair the leftover index with 0). So **`V_{(1)} = (D_J : J ∈ J)C`**.
  - `Z_{(1)} = {y ∈ T^{2k+1} : ν = k}`. If `ν = k`, the residue is one value `w`, `Σy = w`, and `{y, −Σy}` closes under negation. Conversely, a negation-closed multiset of `2k+2` nonzero values splits into pairs, so `ν(y) ≥ k`. Hence `Z_{(1)} = Γ'`.
  - `|Γ'| = #{(2k+2)`-tuples of `T` closed under negation`} = Q_k(q)`, the same count as C0 Step 2.

## C4 · (P1) Fibres
STATE: CLOSED — CORRECT

Let `λ(M') = μ`, with residue values `u_1..u_ℓ` (distinct classes) and multiplicities `μ_1 ≥ ⋯ ≥ μ_ℓ`. Add a value `y`:
- `y = −u_j`: in class `j` the minority grows by one, so the residue loses a copy of `u_j`: **`μ−e_j`** (re-sorted).
- `y = u_j`: **`μ+e_j`**.
- `y` in one of the `h−ℓ` classes where `a = ā` (possibly `0 = 0`): the residue gains one copy, **`μ⊔1`**. There are `2(h−ℓ) = q−1−2ℓ` such `y`.

So `|F(M')| = F_Λ(μ) := #{j: μ−e_j ∈ Λ} + #{j: μ+e_j ∈ Λ} + (q−1−2ℓ)[μ⊔1 ∈ Λ]`. It depends only on `μ`, so `Z_{>i} = Z_{Λ_i}` with `Λ_i := {μ ∈ Par_{m−1} : F_Λ(μ) > i}`.

All options lie in `Par_m`: sizes `|μ|±1 ≤ m` with parity `m`, and `ℓ(μ⊔1) = ℓ+1 ≤ h` whenever the option exists (`ℓ < h`).

## C5 · (Chain)
STATE: CLOSED — CORRECT

Let `r̄_j` be the last row of length `μ_j`, and `r̲_j` the first.
- `S_t(μ−e_j) = S_t(μ) − [t ≥ r̄_j]`.
- `S_t(μ+e_j) = S_t(μ) + [t ≥ r̲_j]`.
- `S_t(μ⊔1) = S_t(μ) + [t > ℓ]`.

Consecutive options, in the order `μ−e_1,…,μ−e_ℓ, (μ⊔1)^{q−1−2ℓ}, μ+e_ℓ,…,μ+e_1`, compare as follows:
- `r̄_j` is non-decreasing in `j`, so `μ−e_j ≼ μ−e_{j+1}`.
- `μ−e_ℓ ≼ μ ≼ μ⊔1`.
- `μ⊔1 ≼ μ+e_ℓ`, because `r̲_ℓ ≤ ℓ < t`.
- `r̲_j` is non-decreasing in `j`, so `μ+e_{j+1} ≼ μ+e_j`.

The list is a `≼`-chain. For a down-set `Λ` the options in `Λ` form an initial segment:
- the removals in `Λ` are `{1..r}`, with `r` the last row of its length;
- the additions in `Λ` are `{j_0..ℓ}`, with `j_0` the first row of its length;
- **if some addition is in `Λ`, then `r = ℓ` and `N := [μ⊔1 ∈ Λ] = 1` whenever `ℓ < h`**;
- **if `N = 1`, then `r = ℓ`**.

Hence `F = r + (q−1−2ℓ)N + (ℓ−j_0+1)[j_0 exists]`.

## C6 · (P2) Λ_i is a down-set — THE CORE
STATE: CLOSED — CORRECT (written out in full below, my own wording; one step of the Fable is made sharper, none is wrong)

**Claim.** If `μ ≼ μ̃` in `Par_{m−1}` (same parity, lengths `ℓ, ℓ̃ ≤ h`), then `F_Λ(μ) ≥ F_Λ(μ̃)` for every down-set `Λ`. Hence each `Λ_i` is a down-set.

**Reduction.** Let `L = q−1`. Write the two option lists (C5) with multiplicity, as `opt_p(μ)` and `opt_p(μ̃)` for `p = 1..L`:
- positions `1..ℓ` are removals `μ−e_p`;
- positions `ℓ+1..L−ℓ` are `μ⊔1`;
- position `L+1−j` is the addition `μ+e_j`, `j = 1..ℓ`.

If `opt_p(μ) ≼ opt_p(μ̃)` for every `p`, then `opt_p(μ̃) ∈ Λ ⇒ opt_p(μ) ∈ Λ`, and counting gives `F(μ) ≥ F(μ̃)`.

**Two facts used throughout.**
- (T) If `t ≥ 1` is *tight*, i.e. `S_t(μ) = S_t(μ̃)`, then `S_{t−1}(μ) ≤ S_{t−1}(μ̃)` gives `μ_t ≥ μ̃_t`, and `S_{t+1}(μ) ≤ S_{t+1}(μ̃)` gives `μ_{t+1} ≤ μ̃_{t+1}`.
- (G) Each comparison below has the form `S_t(μ)+δ ≤ S_t(μ̃)+δ̃` with `δ, δ̃ ∈ {−1,0,1}` and `δ−δ̃ ≤ 1`. It can only fail at a tight `t` with `δ = δ̃+1`. Where `δ−δ̃` could be 2, this is said explicitly.

**(a) Removals against removals, `p ≤ min(ℓ,ℓ̃)`.**
- The only danger is a tight `t` with `r̄̃_p ≤ t < r̄_p`. Then `t ≥ p`, and `μ_t = μ_{t+1} = μ_p`.
- Since `t+1 > r̄̃_p`, `μ̃_{t+1} < μ̃_p`.
- By (T), `μ̃_{t+1} ≥ μ_{t+1} = μ_t ≥ μ̃_t ≥ μ̃_{t+1}`. So all four are equal to `μ_p`, and `μ̃_p > μ_p`.
- Then `S_t(μ̃) − S_{p−1}(μ̃) = Σ_{s=p}^{t}μ̃_s ≥ (t−p+1)μ_p + (μ̃_p−μ_p) > (t−p+1)μ_p = S_t(μ) − S_{p−1}(μ)`.
- Tightness then gives `S_{p−1}(μ) > S_{p−1}(μ̃)`, which contradicts `μ ≼ μ̃`. ✓

**(b) Additions against additions, `j ≤ min(ℓ,ℓ̃)`.**
- The only danger is a tight `t` with `r̲_j ≤ t < r̲̃_j (≤ j)`. Then `μ_t = μ_{t+1} = μ_j`, and `μ̃_t > μ̃_j` because `t < r̲̃_j`.
- By (T), `μ̃_{t+1} ≥ μ_{t+1} = μ_j = μ_t ≥ μ̃_t ≥ μ̃_{t+1}`. So `μ̃_t = μ̃_{t+1} = μ_j`, and `μ̃_j < μ_j`.
- So `Σ_{s=t+1}^{j}μ̃_s < (j−t)μ_j = Σ_{s=t+1}^{j}μ_s`. With tightness at `t`, `S_j(μ̃) < S_j(μ)`: contradiction. ✓
- (The Fable writes `μ̃_{t+1} = μ_j`; it is `≥` a priori and `=` after the squeeze. Same conclusion.)

**(c) Middle against middle.** We need `S_t(μ)+[t>ℓ] ≤ S_t(μ̃)+[t>ℓ̃]`.
- If `ℓ ≥ ℓ̃`, this is trivial.
- If `ℓ < ℓ̃`, for `ℓ < t ≤ ℓ̃` we have **`S_t(μ̃) ≥ S_ℓ(μ̃)+(t−ℓ) ≥ S_ℓ(μ)+(t−ℓ) = |μ|+(t−ℓ)`**, since `μ̃_s ≥ 1` for `s ≤ ℓ̃`. So `|μ|+1 ≤ S_t(μ̃)`. ✓

**(d) Mixed, `ℓ < ℓ̃`.**
- **(d1) Positions `ℓ < p ≤ ℓ̃`: `μ⊔1` against `μ̃−e_p`.** These positions are `≤ L−ℓ`, because `ℓ+ℓ̃ ≤ 2h = L`. We need `S_t(μ)+[t>ℓ] ≤ S_t(μ̃)−[t≥r̄̃_p]`.
  - `t ≤ ℓ`: both brackets are 0, since `r̄̃_p ≥ p > ℓ`. ✓
  - `t ≥ ℓ̃`: `|μ̃| ≥ |μ|+(ℓ̃−ℓ) ≥ |μ|+1` and `|μ̃| ≡ |μ|` (mod 2), so `S_t(μ̃) = |μ̃| ≥ |μ|+2`. ✓
  - `ℓ+2 ≤ t < ℓ̃`: `S_t(μ̃) ≥ |μ|+(t−ℓ) ≥ |μ|+2`. ✓
  - `t = ℓ+1 < ℓ̃`, with `t ≥ r̄̃_p` (so `p = ℓ+1 = r̄̃_p`): we need `S_{ℓ+1}(μ̃) ≥ |μ|+2`.
    - If `μ̃_{ℓ+1} ≥ 2`, then `S_{ℓ+1}(μ̃) ≥ |μ| + 2`. ✓
    - If `μ̃_{ℓ+1} = 1`, then rows `ℓ+1..ℓ̃` of `μ̃` all have length 1, so `r̄̃_{ℓ+1} = ℓ̃ > ℓ+1 = t`, which contradicts `t ≥ r̄̃_p`. ✓
    - (The Fable settles this by parity; this is an equivalent, slightly more direct closing.)
- **(d2) Positions `L+1−j`, `ℓ < j ≤ ℓ̃`: `μ⊔1` against `μ̃+e_j`.** We need `S_t(μ)+[t>ℓ] ≤ S_t(μ̃)+[t≥r̲̃_j]`.
  - For `t ≤ ℓ` this is trivial.
  - For `t > ℓ`, `S_t(μ̃) ≥ |μ|+1` by (c). ✓

**(e) Mixed, `ℓ > ℓ̃`.**
- **(e1) `ℓ̃ < p ≤ ℓ`:** `μ−e_p ≼ μ ≼ μ̃ ≼ μ̃⊔1`. ✓
- **(e2) Positions `L+1−j`, `ℓ̃ < j ≤ ℓ`: `μ+e_j` against `μ̃⊔1`.** We need `S_t(μ)+[t≥r̲_j] ≤ S_t(μ̃)+[t>ℓ̃]`.
  - `t > ℓ̃`: `S_t(μ)+1 ≤ S_t(μ̃)+1`. ✓
  - `t ≤ ℓ̃` and `t ≥ r̲_j`: we need strictness at `t`. Suppose `t` is tight. Then `t < j`, and `μ_t = μ_{t+1} = μ_j ≥ 1`.
    - By (T), `μ̃_{t+1} ≥ μ_j` and `μ̃_t ≤ μ_t = μ_j`. So `μ̃_{t+1} = μ_j` and `μ̃_s ≤ μ_j` for `s > t`.
    - `μ̃_j = 0 < μ_j`, so `Σ_{s=t+1}^{j}μ̃_s < (j−t)μ_j`, and `S_j(μ̃) < S_j(μ)`: contradiction. ✓

**Coverage of positions.** Every `p ∈ 1..L` falls in exactly one of (a)–(e):
- if `ℓ = ℓ̃`, only (a), (b), (c) occur;
- if `ℓ < ℓ̃`, the list of `μ̃` has fewer middle slots, and the extra slots are (d1) and (d2);
- if `ℓ > ℓ̃`, symmetrically, (e1) and (e2).

The degenerate cases are covered: `ℓ̃ = h` (no middle for `μ̃`), `ℓ = h` (only (e)), and `μ = ∅`.

**Conclusion.** `opt_p(μ) ≼ opt_p(μ̃)` for all `p`, so `F_Λ(μ) ≥ F_Λ(μ̃)`, and **`Λ_i` is a `≼`-down-set of `Par_{m−1}`**. ∎

## C7 · (P3) Constructions and coverage
STATE: CLOSED — CORRECT

**Goal.** Let `μ ∈ Λ_i`, i.e. `F := F_Λ(μ) ≥ i+1`, and let `G` be any tight pattern of `μ` on `[2..m]` (pairs `P`, column blocks `B_c`). We must show `G ∈ W_{q−2−i}(V_Λ)`. By monotonicity (C1) it is enough to place `G` in `W_j` for some `j ≤ q−1−F`: then every `i ≤ F−1` has `q−2−i ≥ q−1−F ≥ j`.

- **(α) `j_0` exists** (`λ = μ+e_{j_0} ∈ Λ`).
  - `j_0` is the first row of its length (C5), so column `μ_{j_0}+1` of `μ` has height `j_0−1`: block `B`, possibly empty.
  - Put index 1 into `B`. This is a tight pattern of `λ`: that column of `λ` has height `j_0`; the number of pairs is `(m−|λ|)/2 = (m−1−|μ|)/2`, unchanged.
  - Its `y_1`-degree is `j_0−1`, and its top coefficient is `±G` (C2). So `G ∈ W_{j_0−1}`.
  - Here `r = ℓ`. If `ℓ < h`, then `N = 1` and `F = ℓ + (q−1−2ℓ) + (ℓ−j_0+1) = q−j_0`. If `ℓ = h`, then `F = 2ℓ − j_0 + 1 = q−j_0`. So `j_0−1 = q−1−F`. ✓
- **(β) No `j_0`, `N = 1`** (`λ = μ⊔1`, `ℓ < h`).
  - Put index 1 into column 1, whose height goes from `ℓ` to `ℓ+1`. The pair count is unchanged.
  - Its `y_1`-degree is `ℓ`, with top coefficient `±G`, so `G ∈ W_ℓ`.
  - `F = r + q−1−2ℓ` with `r = ℓ`, so `q−1−F = ℓ`. ✓ (For `μ = ∅`, the block is `{1}`, `Δ = 1`, and the degree is 0.)
- **(γ) Only removals** (`F = r ≥ 1`, `λ = μ−e_r`, with `r` the last row of its length).
  - Column `μ_r` of `μ` has height `r`: block `S`, `|S| = r`. Write `G = Δ(S)G'`, where `G'` avoids `S ∪ {1}`.
  - For `b ∈ S`, the pairs `P ∪ {(1,b)}` with the block `S∖b` form a tight pattern of `λ`: column `μ_r` of `λ` has height `r−1`, and there is one more pair, `(m−|λ|)/2 = (m−1−|μ|)/2+1`.
  - `f = Σ_b ε_bΔ(S∖b)D(y_1,y_b)G' ∈ V_Λ`. By C2, `deg_{y_1}f ≤ q−1−r`, with top coefficient `±Δ(S)G' = ±G`. So `G ∈ W_{q−1−r} = W_{q−1−F}`. ✓
- **Edge cases.**
  - `j_0 = 1`: `B = ∅`, index 1 alone as a block of size 1, degree 0, `F = q−1`. ✓
  - `r = 0` together with no `j_0` and no `N`: then `F = 0`, and `μ ∉ Λ_0`, so there is nothing to show.
  - `ℓ = 0`: only (β) can apply, or `F = 0`.
  - `ℓ = h`: (β) is impossible, and (α) and (γ) work as above.

So every generator of `V_{Λ_i}` lies in the ideal `W_{q−2−i}(V_Λ)`, hence **`V_{Λ_i} ⊆ W_{q−2−i}(V_Λ)`**.

## C8 · The induction closes
STATE: CLOSED — CORRECT

The induction is on `m`.

**Base `m = 0`.** `Par_0 = {∅}`.
- `Λ = {∅}`: `V = F_3` (the empty product) and `Z = T^0` (one point), so `1 ≥ 1`.
- `Λ = ∅`: `0 ≥ 0`.

**Step.** `dim V_Λ = Σ_{i=0}^{q−2} dim W_{q−2−i}(V_Λ) ≥ Σ_i dim V_{Λ_i} ≥ Σ_i |Z_{Λ_i}| = Σ_i |Z_{>i}| = |Z_Λ|`.
- The first equality is C1.
- The first inequality is C7.
- The second inequality is the induction hypothesis in `m−1` variables `y_2..y_m`. It applies because `Λ_i` is a down-set of `Par_{m−1}` (C6); the statement is symmetric in the index set.
- The last two equalities are C4 and C1.

## C9 · Field of definition
STATE: CLOSED — no issue for FULL

The `≥` argument is linear algebra over `F_3` (C1, C2, C7). On the `T` side it is pure counting of multisets in a finite set with a fixed-point-free involution (C3, C4, C5). It never evaluates a polynomial at a point of `F_q`, so no extension of scalars is needed.
- `T = F_q^×` enters only through `h = (q−1)/2` and the count `|Γ'| = Q_k(q)`.
- The characteristic enters only through the translation (C0). The identities of C2 hold over `Z`.

The «all down-sets, equality» corollary does use supports of functions on `T^m`, but FULL does not need it.

## C10 · Conclusion
STATE: CLOSED

The root (C3) and C8 give `dim_{F_3}(D_J : J ∈ J)C ≥ |Γ'| = Q_k(q)` for every `k ≥ 0` and every `q = 3^v`. With `≤` (C0), this is (S). By C0, (S) is DS Conjecture 1.2 for `m = 3^v` in dimension `2k`.

**Theorem D survives the cold audit: every item C0–C10 is CORRECT.** Recorded along the way:
- one handoff typo (`N = 2k+1` should be `N = 2k+2`);
- one slip in the DS paper itself (`d_0` in §5);
- two places where the Fable's wording is loose but the conclusion stands: C6(b), «`=`» for «`≥`»; C6(d1), closed here without parity.

## INDEPENDENT GATES (own code)
STATE: CLOSED

All gates ran inside `vigia.sh`, with the estimate written before each run. Peak 88 MB, longest run 15 s.

- **Gate 1 — ALL down-sets, pure combinatorics** (`corpus4/herramientas_grepy/regla270_gate1_downsets.py`, log `corpus4/regla270_gate1.log`).
  - It enumerates EVERY `≼`-down-set of `Par_m`, NOT a random sample and NOT a position-wise chain test.
  - It counts `N_m(λ) = #{M ∈ T^m : λ(M) = λ}` by a class-by-class EGF DP. That is a different route from the fibres. Gate: `Σ_λ N_m(λ) = (q−1)^m`, asserted.
  - It computes `F_Λ(μ)` from the explicit option multiset. It checks P1 (`|Z_Λ| = Σ_i |Z_{Λ_i}|`), P2 (every `Λ_i` a down-set) and P3 (the best of α/β/γ reaches slice `≤ q−1−F`).
  - Cells: `(q,m)` = `(3, 4/6/8/12)`, `(9, 3..11)`, `(27, 4/5/8/9)`, `(81, 4/7)`, `(243, 6)`, up to 940 down-sets per cell. **0 failures of P1, P2 or P3 in all of them.**
  - **Negative controls FIRE:**
    - miscounting the new-value options (one copy of `μ⊔1` per empty class instead of two) gives P1 27 and P2 61 failures at `(9,6)`;
    - tightening P3 by one slice (`q−2−F`) gives 604 failures at `(9,7)`. **So the coverage of P3 is EXACT, with no slack.**
- **Gate 2 — ALL down-sets, algebra** (`corpus4/herramientas_grepy/regla270_gate2_dims.py`, log `corpus4/regla270_gate2.log`).
  - It uses its own tight-pattern generator (pairs × column blocks, `D` and Vandermonde expanded exactly in `F_3[y]/(y^{q−1})`), its own graded closure and its own mod-3 echelon.
  - **`dim V_Λ ≥ |Z_Λ|` holds for EVERY down-set at `(3,4)`, `(3,5)`, `(3,6)`, `(9,2)`, `(9,3)`, `(9,4)`, with equality everywhere.**
  - At `(9,4)` the ten down-sets give `0, 168, 1896, 2280, 2216, 2600, 3752, 3896, 4088, 4096`. Six of these match the Fable's `patdim` independently; three are new (2600, 4088, 4096).
- **Gate 3 — the literal (S), a third engine** (`regla270_sumform_kernelbasis.py`: kernel basis `D·y_a^i` per pair, exact rank mod 3 degree by degree; log `corpus4/regla270_sumform.log`).
  - `(3,3) = 70`, and `(2,9) = 5120` with graded ranks identical to MISION_15 §3.1.
  - The subfamily `(2,9)` minus `{01|23|45, 02|15|34}` gives `4730 < 4736`.
- **Gate 4 — out of sample, four months old.** `~/Downloads/HOUDINI_SONIC_BOOM_STAR_6_9_run1.log` (26 May, a different engine, DS's own ring) gives `rank_p = 190120` for `(n,m) = (6,9)`, i.e. `(k,q) = (3,9)`. That is `Q_3(9) = 190120`, the value Theorem D predicts. Likewise `~/Downloads/HODGE_ENGINE_v3_n10_m3.txt` (23 May): `(5,3)` gives 924.
- **`q = 3` by a fourth route** (`regla270_q3_specht.py`, this morning): in the `N`-variable form, the degree `N−r` part of the ideal is the Specht module `S^{(N−r,r)}`, whose dimension does not depend on the characteristic. Dimensions 6, 20, 70 at `N = 4, 6, 8`.

## INGENIO
STATE: CLOSED

1. **P3 has zero slack** (negative control, gate 1): each construction lands in exactly the slice needed. That is why the corollary «`dim V_Λ = |Z_Λ|` for every down-set» is an equality, and it explains gate 2's `EQ` in every case.
2. **(S) is DS's own §5 criterion.** Their Lemma 4.5 (`ψ_J = ±λρ_J`) is the `Y`-lemma in DS's variables. The campaign's translation and DS's computational criterion are the same statement.
3. **The Fable's argument never uses characteristic 3 after the translation.** The identities of C2 hold over `Z`, and the count only uses the involution `−1` on `F_q^×`. So the same proof gives the analogous `F_p` statement wherever the translation holds. The extension to every odd prime power `m = p^v` only needs C0 written for `p ≥ 5`. That is **NOT claimed** here.
4. **The symmetric form.** (S) ⟺ `dim Σ_J ⊗_{p∈J} K_p = Q_k(q)` in `N = 2k+2` variables, with `K_p = ker(×(x_a+x_b)) = D·Λ_p`. There is no distinguished index 0 (my consultation of this morning). It is the natural statement for the paper.

## WHAT IS NOT DOUBLE-CHECKED
STATE: CLOSED

- **DS's own theorems** (Theorem 1.1(a), Claim 4.3, Corollary 1.5): cited from the published paper (J. Math. Soc. Japan 68:3 (2016)), not re-proved. Claim 4.3 was re-derived this morning (it is two lines).
- **R2** (`INFORME_15` §3.3) and the Fable's machine range `k ≤ 10` (§3.4–4.5): not audited line by line and not re-run. They are not on the critical path: Theorem D supersedes them.
- **The extension to `p ≥ 5`:** not claimed by anyone; the translation is not written.
- **The «all down-sets = equality» corollary:** only the `≥` half is audited in full (C8). The `≤` half (supports, Gale–Ryser) is not needed and not audited.

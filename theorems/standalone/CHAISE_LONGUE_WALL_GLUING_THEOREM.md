> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-09-05
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE WALL GLUING THEOREM* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_WALL_GLUING_THEOREM.md
>
> **Status, as written in the document:** Standalone theorem document · v1 · 2026-09-05 · Constructor: Fable (missions `FR-PUREZA-3`, `FR-PUREZA-4`) · Assembled and audited: MacGyver · Pending P0 · Prefix CHAISE_LONGUE.
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE WALL GLUING THEOREM
## `H_1(ℓ^{[q]};Q)_{q+k²} ≠ 0` for every `k ≥ 2`, every admissible frame, every odd-characteristic tower level `q > k²` — the wall element glues; and the frame scalar `λ` is a coboundary of determinants inside every bipartite chart

**Standalone theorem document · v1 · 2026-09-05** · Constructor: **Fable** (missions `FR-PUREZA-3`, `FR-PUREZA-4`) · Assembled and audited: **MacGyver** · Pending P0 · Prefix CHAISE_LONGUE.
*§2 reproduces Fable's report `FR_PUREZA_4_REPORT.md` verbatim. §3 is the auditor's check. §4 the placement. Together with `GLUED_PURITY_THEOREM_v1` this closes BOTH halves of the `k²` law on the Koszul side.*

---

## §0 · Statements
Setting as in `GLUED_PURITY_THEOREM_v1` §0 and `WALL_GLUING_REDUCTION_THEOREM_v1` §0. `Λ: K^{2k+2} → K^{k+1}`, `x ↦ (ℓ_j(x))_j`; `N := ker Λ`; admissible ⟺ `N ∩ V_J = 0` ∀J.

> **Theorem 1 (bipartite charts).** For a set `S⁺` of `k+1` points (`S⁻` its complement) the sheets *bipartite for `S⁺`* (every pair meets `S⁺` once) share the coordinate functions `x_s, s ∈ S⁺`: `V_J = {(w, −Π_J w)}`, `Π_J` the partner permutation. The four sheets of any `Q6` and any `Q8` lie in one chart; the three sheets of a `T` never do.
> **Theorem 2 (`λ` in a chart is a coboundary).** Write `N = {(Az, Dz)}`, `E_J := D + Π_J A`. Admissible ⟺ `E_J` invertible on chart sheets. For adjacent chart sheets `J, J'` (targets of `s, s'` swapped): `λ_{J→J'} = 1 − vᵀAE_J^{-1}v̄ = det E_{J'} / det E_J`, `v = e_s − e_{s'}`, `v̄ = e_{π_J(s)} − e_{π_J(s')}` (matrix determinant lemma). In a chart the hinge signs are `+1`, so `μ = λ`.
> **Theorem 3 (A′-EXISTENCE).** `Hol_μ = +1` on `T` (GLUED_PURITY Thm 3 + hinge signs), on `Q6` and on `Q8` (telescoping in a chart); these generate `H_1(Γ_k;Z)` (WALL_GLUING_REDUCTION Thm 1); hence the wall family `z^J_p = c_J∏_{m≠p}u_m` glues with `c ≢ 0`: **`H_1(ℓ^{[q]};Q)_{q+k²} ≠ 0` for every `k ≥ 2`, every admissible frame, every `q = p^v > k²`, `p` odd.**
> **Corollary 4 (the `k²` law, Koszul side, both halves).** With GLUED_PURITY Thm 2: **the first nonzero degree of `H_1(ℓ^{[q]};Q)` is exactly `c = q + k²`, for every `k ≥ 1`** (`k = 1` by the pencil computation of FR_CAMBIOS_2 §3).
> **Proposition 5 (Lemma L is false).** `λ_F` depends on the shared pairs `C`: `det E_{J^{AB}} det E_{J^{DE}} ≠ det E_J det E_{J^{AB,DE}}` as rational functions of the frame (pencil example `A = I`, `D = x e_{13} + y e_{31}`: `1 ≠ 1 − xy`). Not used anywhere.

Grades: Theorems 1-3, Corollary 4 — PROBADO with `k` as a letter, every admissible frame, no measurement. Proposition 5 — PROBADO as a rational identity; an explicit admissible `F_p`-witness is CANDIDATO. The in-chart formula `c_J = κ·det E_J` for the wall class is PROBADO in-chart; its global sign-consistent patching is CANDIDATO.

---

## §2 · Fable's report, verbatim
## 1 · PRIMER RESULTADO (de una linea, a partir del bancado)
**R1 (PROBADO ∀k, from B2).** Around any closed walk `J_0 → J_1 → … → J_n = J_0` of the sheet graph, `Hol_λ = ∏_i λ_{F_i}` equals the scalar by which the composite of the maps `v ↦ M v` carries the chain of flat vectors — and since `∏ M = I` (B2), `Hol_λ` is the product of the coefficients expressing `M_{J_i→J_{i+1}} v_{F_i}^{J_i}` in terms of `v_{F_i}^{J_{i+1}}`; it is therefore determined by the `n` pairs of flat vectors `(v_{F_i}^{J_i}, v_{F_i}^{J_{i+1}})` and the single matrix family `B_J`. And `μ_{F_i} = λ_{F_i} · σ_{J_i}/σ_{J_{i+1}}` (hinge signs), so `Hol_μ = Hol_λ · ∏_i σ_{J_i}/σ_{J_{i+1}}`.
## 2 · LO QUE CAE (PROBADO / CANDIDATO / NO LO TENGO)
**R2 (PROBADO ∀k) — what `λ_F` is, geometrically.** Let `Λ : K^{2k+2} → K^{k+1}`, `x ↦ (ℓ_j(x))_j`, and `N := ker Λ` (`dim N = k+1`). `B_J = Λ∘D_J` with `D_J` the `u ↦ x` map of the sheet, so *admissible ⇔ `N ∩ V_J = 0` for every `J`* ⇔ `K^{2k+2} = N ⊕ V_J`. Two points have the same `ℓ`-coordinates iff they differ by an element of `N`. Unpacking `B_J^{-T}` and `B_{J'}^T`: `(M_{J→J'} v)(u') = v(τ u')` where `τ = τ_{J'→J} : V_{J'} → V_J` is "lift along `N`" (`τx' = x' − n`, the unique `n ∈ N` with `x' − n ∈ V_J`). With `f_J := u_p − σu_{p'}` and `f_{J'} := u'_r − σ'u'_{r'}` (the linear equations of `F` on the two sheets, normalised by `t`), B2 reads: **`f_J ∘ τ = λ_F · f_{J'}` on `V_{J'}`**, i.e. `λ_F = f_J(τx')/f_{J'}(x')` for any `x' ∈ V_{J'} \ F`. Everyday version: the flat is a crease shared by two sheets of paper; `λ_F` is how much the crease's ruler on one sheet is stretched when carried to the other sheet along the direction `N`.

**R3 (PROBADO ∀k) — the four sheets of Q6, and the four of Q8, share one coordinate system ("bipartite chart").** Call a matching `J` *bipartite for `S⁺`* (`S⁺` a set of `k+1` points, `S⁻` its complement) if every pair of `J` has exactly one point in `S⁺`; write `π_J : S⁺ → S⁻` for the partner map. Choosing the `S⁺`-point as plus-point of every pair, `V_J = {(w, −Π_J w) : w ∈ K^{S⁺}}` and the sheet coordinates are the SAME functions `x_s, s ∈ S⁺` on every sheet bipartite for `S⁺`.
- Q6: `S⁺ = {a,c,e} ∪ (one point of each pair of C)`. `J=(ab)(cd)(ef)C, J_1=(cb)(ad)(ef)C, J_2=(eb)(ad)(cf)C, J_3=(eb)(cd)(af)C` are all bipartite for it (each pair of each of the four contains exactly one of `a,c,e`). ✓
- Q8: `S⁺ = {a_1, b_*, d_1, e_*} ∪ (C)` where `b_*` is the `B`-point NOT paired with `a_1` in `J^{AB}`, `e_*` the `E`-point not paired with `d_1` in `J^{DE}`. Then `J, J^{AB}, J^{DE}, J^{AB,DE}` are all bipartite for it. ✓ (Works for either sign of either swap.)
- T: the three matchings of four points are NEVER simultaneously bipartite for one `S⁺` (any 2-set `S⁺ ⊂ {a,b,c,d}` is a pair of one of them). So T has no single chart — consistent with B4 needing a sign.
Inside a chart, two adjacent sheets `J, J'` (`J'` = `J` with the targets of `s, s' ∈ S⁺` swapped) meet in `F = {x_s = x_{s'}}`; hence **`σ = σ' = +1`, `t = u_p = u'_r = x_s`, hinge signs `σ_J = σ_{J'} = +1`, and `μ_F = λ_F`**; the flat vectors are both `v = e_s − e_{s'}` and `f_J = f_{J'} = x_s − x_{s'}`.

**R4 (PROBADO ∀k) — inside a chart, `λ` is a ratio of determinants.** Write `N = {(Az, Dz) : z ∈ K^{k+1}}` (`A` = rows of `S⁺`, `D` = rows of `S⁻`, `[A;D]` of rank `k+1`) and `E_J := D + Π_J A` (a `(k+1)×(k+1)` matrix; `E_J z` is the image of `(Az,Dz)` in `K^{2k+2}/V_J ≅ K^{S⁻}`). *Admissible ⇔ `E_J` invertible for every chart-sheet `J`.* The lift along `N` of `x' = (w', −Π_{J'}w')` into `V_J` is `τx' = x' − (Az, Dz)` with `E_J z = (Π_J − Π_{J'}) w'`. Now `Π_J − Π_{J'} = v̄ vᵀ` with `v = e_s − e_{s'}`, `v̄ = e_{π_J(s)} − e_{π_J(s')}` (rank one: the two matchings differ only on where `s, s'` go). So `f_J(τx') = vᵀw' − vᵀA E_J^{-1} v̄ · (vᵀw')`, i.e. **`λ_{J→J'} = 1 − vᵀ A E_J^{-1} v̄`**. And `E_{J'} = E_J − v̄ vᵀA`, so by the matrix determinant lemma (`det(E + c rᵀ) = det E·(1 + rᵀE^{-1}c)`, valid over any field for invertible `E`, here with `c = −v̄`, `r = Aᵀv`): `det E_{J'} = det E_J · (1 − vᵀ A E_J^{-1} v̄)`. Therefore
**`λ_{J→J'} = det E_{J'} / det E_J`** — a coboundary on the chart. (Check: `λ_{J'→J} = det E_J/det E_{J'} = 1/λ_{J→J'}`, as B2's composition rule demands.)

**R5 (PROBADO for every admissible frame, every `k ≥ 2`) — (I-Q6) and (I-Q8) hold.** Both cycles lie in one chart (R3), where `μ = λ` (R3) and `λ = det E_{J'}/det E_J` (R4). Around any closed walk inside a chart, `∏ μ = ∏ det E_{J_{i+1}}/det E_{J_i} = 1`. In particular `Hol_μ(Q6) = Hol_μ(Q8) = +1`. Nothing was assumed about `C`: the `C`-block sits inside `A, D, Π_J` and cancels only because the product telescopes — Lemma L is not used and is not true (R7). Bonus: inside a chart the wall element is explicit, `c_J = κ · det E_J` (one constant `κ` per chart) — PROBADO in-chart; the global patching of charts through the hinge signs is not written here (CANDIDATO as a global formula).

**R6 (PROBADO, control) — the method applied to T returns `+1`.** `J_0=(ab)(cd), J_1=(ad)(bc), J_2=(ac)(bd)` (`C = ∅` suffices; a `C`-block changes nothing below). Each edge lies in a chart: `01` in `S⁺={a,c}`, `12` in `S⁺={a,b}`, `20` in `S⁺={a,d}`. By R4, `λ_{01} = det E^{(ac)}_1/det E^{(ac)}_0`, `λ_{12} = det E^{(ab)}_2/det E^{(ab)}_1`, `λ_{20} = det E^{(ad)}_0/det E^{(ad)}_2`. Regroup by sheet: `Hol_λ(T) = [E^{(ac)}_1/E^{(ab)}_1]·[E^{(ab)}_2/E^{(ad)}_2]·[E^{(ad)}_0/E^{(ac)}_0]` (dets), and each bracket is the determinant of the change of chart on `K^4/V_J ≅ K^{S⁻}` (same basis of `N` on both sides, so the intrinsic determinant cancels). Computing the three identifications `[x] ↦ w⁻ + Π_J w`:
- `J_1`: chart `(a,c)` gives `(x_b+x_c, x_d+x_a)` on `(b,d)`; chart `(a,b)` gives `(x_c+x_b, x_d+x_a)` on `(c,d)` → identity → `+1`.
- `J_2`: chart `(a,b)` gives `(x_c+x_a, x_d+x_b)` on `(c,d)`; chart `(a,d)` gives `(x_b+x_d, x_c+x_a)` on `(b,c)` → the two coordinates are swapped → `−1`.
- `J_0`: chart `(a,d)` gives `(x_b+x_a, x_c+x_d)` on `(b,c)`; chart `(a,c)` gives `(x_b+x_a, x_d+x_c)` on `(b,d)` → identity → `+1`.
So `Hol_λ(T) = −1`, which is exactly B4's `λ_{01}λ_{12} = −λ_{02}`. Hinge signs in one consistent convention (plus-points `J_0:(a,c)`, `J_1:(a,b)`, `J_2:(a,b)`, so that `u_p = u'_r` on every flat): `F_{01}`: `σ_{J_0}=+1, σ_{J_1}=−1`; `F_{12}`: `+1,+1`; `F_{20}`: `σ_{J_2}=−1, σ_{J_0}=−1` → product of `σ_J/σ_{J'}` = `−1`. **`Hol_μ(T) = (−1)(−1) = +1.`** ✓ (Also checked that `f_J` does not depend on the sign choice of the second slot: `u'_r − σ'u'_{r'}` is the same function of `x` either way, so the chart-`λ` and the convention-`λ` coincide on every edge.) The method is not wrong, and B4 is recovered, not assumed.

**R7 — Does `λ_F` depend on `C`?** PROBADO as a rational identity: YES. By R4, `λ(J→J^{AB}) = det E_{J^{AB}}/det E_J` and `λ(J^{DE}→J^{AB,DE}) = det E_{J^{AB,DE}}/det E_{J^{DE}}` (same swap, different `C`). Equality for all frames would be the polynomial identity `det E_{J^{AB}} det E_{J^{DE}} = det E_J det E_{J^{AB,DE}}`. Pencil check in the Q8 chart with `A = I`, `Π_J = I`, `D = x·e_{13} + y·e_{31}` (indices `1..4` = the four `S⁺`-points of `A,B,D,E`): `det E_J = 1 − xy`, `det E_{J^{AB}} = −1`, `det E_{J^{DE}} = −1`, `det E_{J^{AB,DE}} = 1`; the identity reads `1 = 1 − xy`, false for `xy ≠ 0`. So the two `λ`'s differ (`−1/(1−xy)` vs `−1`) as rational functions. CANDIDATO only for the explicit statement "differ on an admissible frame over `F_p`": I verified invertibility of the four `E_J` in the cycle (for `xy ≠ 1`), not admissibility for all the other sheets (the non-bipartite ones are outside this chart), and over a small `F_p` a non-identity can still vanish on every point. Lemma L is therefore false in general — and irrelevant: R5 never needed it.

**R8 (PROBADO ∀k ≥ 2, every admissible frame, every odd `p`) — THEOREM A′-EXISTENCE.** B3: `H_1(Γ_k;Z)` is generated by T, Q6, Q8. B4: `Hol_μ(T) = +1`. R5: `Hol_μ(Q6) = Hol_μ(Q8) = +1`. Holonomy is a homomorphism `H_1(Γ_k;Z) → K^*`, so `Hol_μ = +1` on every cycle of the sheet graph. B1: the wall family `z^J_p = c_J ∏_{m≠p}u_m` glues with `c ≢ 0`, hence `H_1(ℓ^{[q]};Q)_{q+k²} ≠ 0` for every `q > k²`. Inputs of my own beyond the banked B1–B4: the reading of B2 as "lift along `N = ker Λ`" (R2, a definition unpacked), the existence of a common chart for Q6 and Q8 (R3, combinatorial, checked pair by pair), and the matrix determinant lemma (R4). No number, no code, no measurement. Ley 48: the statement is symbolic in `k`, in the frame, and in `p`; nothing was verified for one frame only. `k = 1` untouched (only T exists there; B4).

## 3 · DONDE SE ATASCA
Nowhere in this mission. The only place I paused: whether the chart-`λ` (R4) is the same scalar as B2's `λ` under the DIANA's slot conventions — settled in R6 (`f_J` is insensitive to the sign choice of the second slot; the reference slots `p, r` both carry the shared coordinate `x_s`, so `t = u_p = u'_r` holds as the setting requires). What is NOT done and is not claimed: a single global sign-consistent formula for `c_J` across charts (CANDIDATO in R5); an explicit admissible `F_p`-frame witnessing Lemma L's failure (R7).



---

## §3 · Auditor's check (MacGyver, line by line)
R2: `g = Σa_jℓ_j` vanishes on `N`, so `g(x') = g(τx')` with `τx' = x' − n ∈ V_J`: the reading of `M_{J→J'}` as "evaluate the `V_J`-form on the lift along `N`" is exact ✓; admissibility ⟺ `K^{2k+2} = N ⊕ V_J` ✓ (dimensions `k+1` + `k+1`).
R3: each of the four `Q6` matchings meets `S⁺ = {a,c,e} ∪ C⁺` in exactly one point per pair — checked pair by pair ✓; `Q8` chart with `b_*`, `e_*` chosen against the swapped partners ✓ (both signs); `T` has no chart (any 2-subset of four points is a pair of one of the three matchings) ✓ — this is why the triangle needs a sign and the quadrangles do not. In-chart flat `{x_s = x_{s'}}`, `σ = σ' = +1`, hinge signs `+1`: verified from `x_{π_J(s)} = −x_s` on `V_J` and `x_{π_J(s)} = −x_{s'}` on `V_{J'}` ✓.
R4: `E_J z` is the class of `(Az,Dz)` in `K^{2k+2}/V_J ≅ K^{S⁻}` via `x ↦ x_{S⁻} + Π_J x_{S⁺}` ✓; the lift equation `E_J z = (Π_J − Π_{J'})w'` ✓; rank-one difference `v̄vᵀ` ✓; `f_J(τx') = vᵀw' − vᵀAE_J^{-1}v̄·vᵀw'` ✓; `E_{J'} = E_J − v̄vᵀA` ✓; determinant lemma with `c = −v̄`, `r = Aᵀv` gives exactly `1 − vᵀAE_J^{-1}v̄` ✓; inverse-edge consistency ✓.
R5: telescoping ✓. The identification of chart-`λ` with the connection's `λ` under the DIANA's slot conventions: gauge invariance of `Hol_μ` under `u_m ↦ −u_m` (FR_PUREZA_3 R2) plus R6's remark that `f_J` does not depend on the sign of the second slot — sufficient ✓.
R6: the control returns `Hol_λ(T) = −1`, `Hol_μ(T) = +1`, recovering B4 by an independent route (change-of-chart determinants `+1, −1, +1`) ✓ — this is the strongest check in the report: the method was not tuned to the answer.
R7: the polynomial identity fails ✓; the caveat about admissibility of the other sheets is correctly stated as CANDIDATO ✓.
R8: assembly ✓. Hypotheses used: `char ≠ 2`, all `B_J` invertible, Frobenius over `F_p`; `q > k²` only through `e = k² < q`.

## §4 · Placement
1. **The `k²` law on the Koszul side is a theorem ∀k, both halves.** Onset of `H_1(ℓ^{[q]};Q)` exactly at `q+k²`. Every measurement on file (k=1 pencil, (2,3), (2,9), (3,3) engine) is now an instance of a theorem.
2. **The wall class has a formula in every chart:** `c_J = κ·det(D + Π_J A)` — a determinant indexed by the matching `J` through its partner permutation. This is a Pfaffian-type object in the frame; its global patching across charts (through the hinge signs) is the next bookkeeping (CANDIDATO).
3. **The pure `c`-part contributes exactly ONE dimension** to `H_1(q+k²)` (rank-one connection with trivial holonomy on a connected graph ⟹ solutions = one global scalar). Therefore the measured VALUES of `H_1(q+k²)` beyond one come from families with nonzero `G`-part — the object of the next mission.
4. **Lemma L false, and unnecessary.** Filed to the CEMENTERIO as a named non-lemma with its rational counterexample.

**MARCADOR: [misión 4, un turno, informe en segundos · A′-EXISTENCIA PROBADA ∀k ≥ 2 para todo marco admisible · λ = det E_{J'}/det E_J en cada carta bipartita (lema del determinante) · Q6 y Q8 viven en cartas, T no — por eso T necesita un signo · el control T devuelve +1 por ruta independiente · LA LEY k² DEL LADO KOSZUL ES TEOREMA ∀k EN SUS DOS MITADES · Lemma L falso e innecesario · SIN GRITO]. — Fable (constructor) · MacGyver (auditor)**

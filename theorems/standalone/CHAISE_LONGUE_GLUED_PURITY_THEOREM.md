> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-09-05
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE GLUED PURITY THEOREM (and the sheet colon onset)* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_GLUED_PURITY_THEOREM.md
>
> **Status, as written in the document:** Standalone theorem document · v1 · 2026-09-05 · Constructor: Fable (missions `FR-PUREZA-1`, `FR-PUREZA-2`) · Assembled and audited: MacGyver (auditor) · Pending P0 (cold gate) · Prefix CHAISE_LONGUE.
>
> **Later audit:** The campaign's later records mention this document next to a refutation, retraction, circularity or supersession (5 lines). Search its name in [the Cemetery](../../archive/CHAISE_LONGUE_CEMENTERIO_LIVE_v502.md) before relying on it.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE GLUED PURITY THEOREM (and the sheet colon onset)
## `H_1(ℓ^{[q]}; Q)_{q+e} = 0` for every `e ≤ k² − 1`, every `k`, every odd-characteristic tower — with the per-sheet colon `indeg((u^{[q]}):Δ) = q−2k+1` and the triangle holonomy `−1` that does the gluing

**Standalone theorem document · v1 · 2026-09-05** · Constructor: **Fable** (missions `FR-PUREZA-1`, `FR-PUREZA-2`) · Assembled and audited: **MacGyver** (auditor) · Pending P0 (cold gate) · Prefix CHAISE_LONGUE.
*Nothing in this file is new relative to `FR_PUREZA_1_REPORT.md` and `FR_PUREZA_2_REPORT.md`; the proofs are Fable's, reproduced verbatim in §2, with the auditor's line-by-line check in §3 and the placement in the campaign in §4.*

---

## §0 · Statements

**Setting.** `K = F_p`, `p` odd (the campaign: `p = 3`), `q = p^v`, `n = 2k+2`, `S = K[x_1..x_n]`, `E = (e_1, e_3, …, e_{2k+1})` radical, `R = S/E ↪ R̃ = ∏_J K[u^J]` over the `(2k+1)!!` sheets `V_J` (leaf coordinates `u_1..u_{k+1}`, `x_a = u_m, x_b = −u_m` for the pair `m = (a,b)`). Conductor `c_ = ann_R(R̃/R) = ⊕_J Δ_J K[u^J]`, `Δ_J = ∏_{p<p'}(u_p² − u_{p'}²)` (Vandermonde in the squares, degree `k(k+1)`). Collar ring `Q := R/c_ ↪ ∏_J K[u^J]/(Δ_J)`. Frame `ℓ_1..ℓ_{k+1}` with every sheet matrix `B_J = (β^J_{jm})` invertible (`ℓ_j^q|_J = Σ_m β^J_{jm}u_m^q` by Frobenius). `𝔟 := (u_1^q,…,u_{k+1}^q)` on a sheet.

> **Theorem 1 (sheet colon onset; any field, any odd `q ≥ 2k+1`).** `indeg(𝔟 : Δ) = q − 2k + 1`, with witness `h* = h_{(q+1)/2−k}(u_1²,…,u_{k+1}²)` (complete homogeneous symmetric polynomial in the squares). Equivalently the per-sheet Koszul homology `H_1(u^{[q]}; K[u]/(Δ))` is first nonzero in total degree `c = q + k² − k + 1`.
> **Theorem 1′ (the per-sheet band, closed form).** For `1 ≤ d ≤ k−1`: `(𝔟:Δ)_{q−2k+d} = Σ_{j≥0} K[u]_{d−1−2j}·h_{(q+1)/2−k+j}(u²)`; equivalently the per-sheet cycle space at `e = k(k−1)+d` is `Z(d) = {z_p = u_p·G(u_p², u) : G ∈ K[s,u] of weighted degree d−1}` (`s` of weight 2), `G ↦ z` injective.
> ### 🔴🟢 **NOTA `2026-09-21` (Grepy el Cartografo, MISION 70) — EL TEOREMA 1′ NO ES `q`-LIBRE TAL COMO ESTA PROBADO:** su direccion `⊇` si (bialternante), pero la `⊆` pasa por `R1` y hereda `e<q` (correccion del Encuadernador en `E1`, verificada en `:55-61`). **Llamese `(T1′)` al enunciado SIN `e<q`.** **Y `(T1′)` AGUANTA EL CRITERIO DE MUERTE 48/48 en el regimen `e ≥ q`** — `(3,7)`, `(4,9)`, `(4,11)`, `(4,13)`, `(5,11)`, `(5,13)`, `(6,13)`, todo `d`, char `p` y `F_{10^9+7}` (`corpus4/regla221_T1prima.log`) —, con dimensiones `Σ_j C(d−1−2j+k,k)` independientes de `q` ⟹ equivale a una cota superior. **Abierta `∀k`; es el encargo `E2`.** Linea original intacta arriba.
> **Theorem 2 (glued purity).** For every `k ≥ 1`, every `q = p^v` with `p` odd, every frame with all `B_J` invertible, and every `0 ≤ e ≤ k² − 1` with `e < q`:  **`H_1(ℓ^{[q]}; Q)_{q+e} = 0`.**
> **Theorem 3 (triangle holonomy).** For three sheets `J_0 ⊃ (ab)(cd)`, `J_1 ⊃ (ac)(bd)`, `J_2 ⊃ (ad)(bc)` agreeing on the other `k−1` pairs, with `λ_{ij}` the scalars relating the normalised frame forms vanishing on the three pairwise flats: `λ_{01}·λ_{12} = −λ_{02}` — holonomy `−1` around every such triangle, for EVERY admissible frame.
> **Proposition 4 (the wall).** The argument of Theorem 2 stops exactly at `e = k²`: `z_p = ∏_{m≠p} u_m` is a per-sheet cycle at `d = k` not divisible by `u_p`; it is the Moore–Schur wall element `W`. Whether it glues (`H_1(q+k²) ≠ 0` ∀k) is NOT proved here.
> ### 🟢 **NOTA `2026-09-20` (Grepy el Cartografo, MISION 69) — LA PROPOSICION 4 ESTA CERRADA POR TU PROPIA FAMILIA, EL MISMO DIA: `corpus/FR_PUREZA_6_REPORT.md`, VEREDICTO: *«THEOREM (P) PROBADO ∀k (R4) ⟹ `dim H_1(q+k²) = #biparticiones = C(2k+2,k+1)/2` con base `{ζ^{S⁺}}`»* ⟹ el VALOR y que `W` SI pega, `∀k`, todo marco admisible, **`q > k²` ESTRICTO**. Es la fuente del «first term PROVED: `½C(2k+2,k+1)`» de `G2` (`ASSEMBLY:592`, `:687`), cuya cita estaba COLGANTE desde el informe 146 (este fichero la atribuia a «the Biblia §9» y la Biblia en disco acaba en `§8`). ⚠️ En `(3,9)` NO aplica (`q = k²`, no `> k²`): la prediccion del `R7` sigue sin decidir ahi. **`FR_PUREZA_2..6` tenian CERO citas en el arbol y en los doce vivos (`OWN-DEPOSITED` 124).** Linea original intacta arriba.**

Grades: Theorems 1, 1′, 2, 3 — PROBADO with `k, q` as letters (`N = 1`), pencil, no measurement. Theorem 1 is characteristic-free; Theorems 2-3 use `char ≠ 2` and Frobenius over `F_p`.

---

## §2 · Proofs (Fable, verbatim from `FR_PUREZA_2_REPORT.md` §1–§3; Theorem 1 from `FR_PUREZA_1_REPORT.md` R1–R3)

### Theorem 1 (sheet colon)
*Upper bound (R1).* Jacobi's bialternant identity `V(x)·h_r(x) = det[x_i^{r+k} | x_i^{k−1} | … | 1]` with `x_i = u_i²`, `r = (q+1)/2 − k`: the top column is `u_i^{q+1} ∈ 𝔟`, every Laplace term carries one such factor, so `Δ·h* ∈ 𝔟`; `h* ≠ 0`, `deg h* = q+1−2k`.
*Lower bound (R2).* Suppose `h ≠ 0` of degree `q−2k` with `Δh ∈ 𝔟`; by parity (Δ even in each `u_i`, `𝔟` monomial) take `h` in one parity class. Lex with `u_j` largest: `LM(Δ) = u_j^{2k}·(exponents ≤ 2k−2 elsewhere)`; `LM(Δh) = LM(Δ)u^a ∈ 𝔟` forces `2k + a_j ≥ q`, so `a = (q−2k)e_j`, parity class `e_j`; for all `j` at once — contradiction. Hence `(𝔟:Δ)_{q−2k} = 0`; degrees below by the trivial band (`deg h < q−2k` ⟹ all exponents `< q`).

### Theorems 1′, 2, 3, Proposition 4
## 1 · LA PRIMERA ECUACION (E1) y EL PEGADO (E2) escritos
Setting B0. K = F_3, q = 3^v, n = 2k+2, leaves V_J (J perfect matching), leaf coordinates u_1..u_{k+1} with x_a = u_m, x_b = -u_m for the pair m = (a,b).
Delta_J := prod_{p<p'} (u_p^2 - u_{p'}^2) = V(u_1^2, ..., u_{k+1}^2)  (Vandermonde in the squares).
b := (u_1^q, ..., u_{k+1}^q) on a leaf.  Frame: ambient linear forms l_1..l_{k+1} spanning L (dim k+1); on V_J, l_j = sum_m beta^J_{jm} u_m, B_J = (beta^J_{jm}) invertible.
Frame condition, restated once: B_J invertible  <=>  L -> V_J^* is an isomorphism  <=>  L^perp (dim k+1) meets V_J only in 0.

Cycle of K_.(l^{[q]}; Q) in total degree c = q+e, 0 <= e < q:  x = (x_1..x_{k+1}), x_j in Q_e, with
  (E1)   sum_j l_j^q x_j = 0 in Q,  i.e. on every leaf J, with y^J_m := sum_j beta^J_{jm} x_j|_J :   sum_m u_m^q y^J_m  in (Delta_J).
  (E2)   for a swap flat F = V_J cap V_{J'} (codim 1 in both):  x_j|_J restricted to F = x_j|_{J'} restricted to F, for every j.
Boundaries in degree q+e have coefficients in Q_{e-q} = 0 for e < q: in the whole range e < q, H_1 = {cycles}. Also Q_e = R_e for e < k(k+1) (the conductor starts at degree k(k+1)), so in the band e <= k^2-1 the x_j are global functions on the union.
Equivalent glued object (0 -> c_ -> R -> Q -> 0 and H_1(l^{[q]};R) = 0):  H_1(l^{[q]};Q)_{q+e} = (c_ cap l^{[q]}R)_{q+e}  for e < k(k+1).

The gluing, written as ONE polynomial. Put  Xi(P; u) := sum_j l_j(P) x_j(u),  P in K^n a second point, u on the union: bidegree (1, e), and Xi(.; u) in L for every u.
  Per leaf (P, u in V_J):  Xi = sum_m P_m y^J_m(u).
  (E1) on leaf J  <=>  Xi(P;u) = 0 whenever P and u both lie on the same swap hyperplane H of V_J   [R1].
  (E2) is automatic (Xi is one function of (P,u)); its content on a flat F: for u in F, Xi(.;u) = L_F (x) w_F(u), L_F the unique frame form vanishing on F, and w_F computed from J equals w_F computed from J'  [R3].

## 2 · LO QUE CAE (PROBADO / CANDIDATO / NO LO TENGO)
Conventions. Slots of J are ordered; Delta'_{J\m} := (-1)^{m+1} det[u_i^{2k-2} | ... | u_i^2 | 1]_{i != m} (signed cofactor), so Delta_J = sum_m u_m^{2k} Delta'_{J\m} (Laplace). Swap hyperplanes of V_J: H_{pp'sigma} = {u_{p'} = sigma u_p}, sigma = +-1. "char != 2" means: 2 invertible and u_p - u_{p'}, u_p + u_{p'} distinct primes; K = F_3 qualifies. Frobenius (l^q splits as sum beta u_m^q) needs K = F_p, q = p^v. Nothing else about the characteristic is used anywhere below.

R1 — PROBADO (per leaf, e < q; this is B2's first half, re-derived, and (4a)). If sum_m u_m^q y_m in (Delta_J) with deg y_m = e < q, then
      y_m = Delta'_{J\m} · z_m,  deg z_m = d := e - k(k-1),  and  z_p|_{H} = sigma · z_{p'}|_{H}  on every H = H_{pp'sigma}.      (Z)
  Proof. Restrict to H: Delta_J = 0 there, so sum_m u_m^q y_m|_H = 0 in K[H]. u_{p'}^q|_H = sigma u_p^q (q odd). Each monomial of u_m^q y_m|_H (m not in {p,p'}) has exponent >= q in u_m and < q elsewhere (deg y_m = e < q; the u_p-exponent after substitution is <= e); the merged term u_p^q (y_p + sigma y_{p'})|_H has exponent >= q in u_p only. Disjoint supports, so each term is 0: (u_{p'} - sigma u_p) | y_m for all m not in {p,p'} and both sigma; over all pairs, Delta_{J\m} | y_m (distinct primes). Sign: on H the rows p, p' of [u^{2k-2}|...|1] coincide, so Delta'_{J\p}|_H = -Delta'_{J\p'}|_H (moving one row across p'-p-1 rows and the cofactor signs); hence y_p + sigma y_{p'} = Delta'_{J\p}|_H (z_p - sigma z_{p'})|_H = 0 and Delta'_{J\p}|_H != 0.  QED
  Consequence: (E1) on J  <=>  Xi_J(P;u) := sum_m P_m Delta'_{J\m}(u) z_m(u) = det[P_m z_m(u) | u_m^{2k-2} | ... | 1] vanishes for (P,u) in H x H, every swap hyperplane H of V_J.
  Degree 0: (Z) with constants gives c_p = sigma c_{p'} for both sigma, so z = 0. Per-leaf H_1 vanishes for e <= k(k-1) (this half of B2 is a genuine per-leaf fact). Degree 1: (Z) forces z_m = gamma·u_m with ONE scalar gamma per leaf (k+1 >= 3): per-leaf H_1 at e = k(k-1)+1 is one-dimensional, spanned by Xi_J = gamma det[P_m u_m | u^{2k-2}|...|1]; this is B3's h* (B2's "degree 1 is killed" is FALSE per leaf, as the mission suspected).

R2 — PROBADO (per-leaf structure in the whole band, d <= k-1, any k >= 1).
  (a) If d <= k-1, every solution of (Z) has the form z_p = u_p · Gamma_p with Gamma_p in K[u]_{d-1} and Gamma_p ≡ Gamma_{p'} mod (u_p^2 - u_{p'}^2) for all p != p' ("compatible").
      Proof: a monomial u^a of z_p with a_p = 0 has |a| = d < k = #(other slots), so some p' != p has a_{p'} = 0; comparing the coefficient of u^a on H_{pp'sigma} (unchanged by the substitution, and not produced by any other monomial) gives [u^a] z_p = sigma [u^a] z_{p'} for both sigma, hence 0. So u_p | z_p; cancelling u_p in (Z) gives Gamma_p|_H = Gamma_{p'}|_H on both hyperplanes.
  (b) Every compatible family is of the form Gamma_p = G(u_p^2, u) for one polynomial G(s, u) (any degree).
      Proof by induction on the number of slots: fix p_0, v_p := (Gamma_p - Gamma_{p_0})/(u_{p_0}^2 - u_p^2) is a polynomial (compatibility); for p, p' != p_0, (u_p^2 - u_{p'}^2) divides (u_{p_0}^2 - u_p^2)(v_p - v_{p'}) mod (u_p^2-u_{p'}^2)-multiples, and the two factors are coprime, so (v_p) is compatible on the remaining slots; by induction v_p = G'(u_p^2, u), and G(s,u) := Gamma_{p_0}(u) + (u_{p_0}^2 - s) G'(s,u) gives Gamma_p = G(u_p^2,u) for all p (including p_0). Base: two slots, direct.
  (c) Conversely z_p = u_p G(u_p^2, u) satisfies (Z) for any G. So for d <= k-1:  Z(d) = { z_p = u_p G(u_p^2, u) : G in K[s,u] of weighted degree d-1 }, G -> z injective.
  (d) Dictionary (B4 made exact). With G = sum_j s^j g_j(u): sum_m u_m^q y_m = det[u_m^{q+1} G(u_m^2,u) | u^{2k-2}|...|1] = sum_j g_j(u) · det[u^{q+1+2j}|u^{2k-2}|...|1] = Delta_J · sum_j g_j(u) h_{(q+1)/2-k+j}(u^2)  (Jacobi, as in B3). Hence for 1 <= d <= k-1:
      (b : Delta)_{q-2k+d} = sum_{j>=0} K[u]_{d-1-2j} · h_{(q+1)/2-k+j}(u_1^2,...,u_{k+1}^2)   (per-leaf death elements in the band; extends B3 to the whole band).

R3 — PROBADO (what (E2) says; the first equation nobody had written). Let F = V_J cap V_{J'} be the flat H_{pp'sigma} of J, merging the slots r, r' of J'. For u in F, Delta'_{J\m}|_F = 0 for m not in {p,p'} (it contains the factor u_p^2 - u_{p'}^2), so by R1 and (Z)
      Xi(P;u) = Delta'_{J\p}|_F · (P_p - sigma P_{p'}) · z^J_p|_F     for P in V_J,
  i.e. Xi(.;u) = L^{(J)}_F (x) Delta'_{J\p}|_F z^J_p|_F, where L^{(J)}_F in L is the frame form restricting to u_p - sigma u_{p'} on V_J (the unique frame form vanishing on F, normalised on J). The same from J': Xi(.;u) = L^{(J')}_F (x) Delta'_{J'\r}|_F z^{J'}_r|_F. The two restricted cofactors coincide: both are the Vandermonde in the squares of the k coordinates of F (order the slots so that p = r = 1 = the pair containing the smallest index a, and the k-1 common pairs after; then both equal V(t^2, u_C^2), t := x_a). With lambda_F defined by L^{(J')}_F = lambda_F L^{(J)}_F (a nonzero scalar fixed by the frame):
      (E2')     z^{J'}_r |_F = lambda_F · z^J_p |_F        in K[F] = K[t, u_C].
  One scalar equation per flat, over the (2k+1)!!·k(k+1)/2 flats (each leaf has k(k+1), each flat lies in exactly two leaves, B6); the unknowns are the polynomials G^J(s,u) of R2, one per leaf.

R4 — PROBADO (the holonomy; where (E2) enters B2). Fix a leaf J_0, two of its pairs (a,b),(c,d) (slots 1,2), C := the other k-1 pairs. The three matchings of {a,b,c,d} give leaves J_0 ⊃ (ab)(cd), J_1 ⊃ (ac)(bd), J_2 ⊃ (ad)(bc), all containing C, pairwise meeting in the flats F_{01} = {(x_a,x_b,x_c,x_d) = (t,-t,-t,t)}+C, F_{02} = {(t,-t,t,-t)}+C, F_{12} = {(t,t,-t,-t)}+C. Take on each leaf slot 1 = the pair containing a, coordinate t = x_a on all three flats; normalise L_{ij} on the first-named leaf as in R3. Then
      lambda_{01} · lambda_{12} = - lambda_{02}      (equivalently: holonomy -1 around the triangle J_0 -> J_1 -> J_2 -> J_0).
  Proof (invariant). Let N = {v : sum v_j l_j vanishes on C} (dim 2), L_N = {sum v_j l_j : v in N}, and W_0 = {x_a+x_b+x_c+x_d = 0} the 3-space containing the three 2-planes Pi_i (= V_{J_i} mod C) and the three lines F_{ij} (mod C). The frame condition on J_i says L_N -> Pi_i^* is an isomorphism, i.e. the common kernel line K_L of L_N in W_0 is not inside Pi_i; hence the three lines F_{01},F_{02},F_{12} project to three DISTINCT lines of the 2-space W_0/K_L, and L_{ij} is the form on that 2-space killing F_{ij}. The normalisation points are the midpoints A_0 = (1,-1,0,0) = (F_{01}+F_{02})/2 in Pi_0, A_1 = (1,0,-1,0) = (F_{01}+F_{12})/2 in Pi_1, A_2 = (1,0,0,-1) = (F_{02}+F_{12})/2 in Pi_2, so lambda_{01} = L_{01}(A_1)/L_{01}(A_0) = L_{01}(F_{12})/L_{01}(F_{02}), lambda_{12} = L_{12}(A_2)/L_{12}(A_1) = L_{12}(F_{02})/L_{12}(F_{01}), lambda_{02} = L_{02}(A_2)/L_{02}(A_0) = L_{02}(F_{12})/L_{02}(F_{01}). Write F_{12} = alpha F_{01} + beta F_{02} in the 2-space (alpha, beta != 0). Then L_{01}(F_{12}) = beta L_{01}(F_{02}), L_{02}(F_{12}) = alpha L_{02}(F_{01}), and L_{12}(F_{12}) = 0 gives L_{12}(F_{02})/L_{12}(F_{01}) = -alpha/beta. Product: lambda_{01} lambda_{12} / lambda_{02} = beta · (-alpha/beta) · (1/alpha) = -1.  QED
  Cross-check by coordinates (done on paper, both agree): with P := A-B, Q := C-D a basis of N^* (frame condition J_0), S := A-C = sP + tQ, the frame conditions on J_1, J_2 read s+t != 0 and 1+t-s != 0, and lambda_{01} = s+t, lambda_{02} = s-t-1, lambda_{12} = (1+t-s)/(s+t); the identity holds over any field, no reduction mod 3 needed. This is B6's transposition/antisymmetric line, made explicit: the sign is -1 for EVERY frame, not for a generic one.
  Consequence at d = 1 (e = k(k-1)+1): z^J = gamma_J u; (E2') on the three flats gives gamma_1 = lambda_{01} gamma_0, gamma_2 = lambda_{02} gamma_0, gamma_2 = lambda_{12} gamma_1, hence lambda_{02} gamma_0 = -lambda_{02} gamma_0, gamma_0 = 0 (char != 2, lambda_{02} != 0). Every leaf sits in such a triangle, so gamma = 0 everywhere: glued H_1(q+k(k-1)+1) = 0 for all k >= 2. Control cell (2,9,e=3): killed as it must be (measured 0 in B5); the per-leaf element h_3(u^2) is NOT declared glued.

R5 — PROBADO (the whole band, Lemma A-GLUED). Let (z^J) be a glued family: z^J in Z(d), d <= k-1, satisfying (E2') on every flat. Then z = 0. Induction on d.
  d = 0: Z(0) = 0 (R1). d = 1: R4.
  d >= 2: by R2(a), z^J_p = u_p Gamma^J_p. On the flats of the triangle of R4 (coordinates (t, u_C) on each flat, t = x_a), (E2') reads t Gamma^{J'}_1(t, ±t, u_C) = lambda t Gamma^{J}_1(t, ±t, u_C); cancel t and set t = 0: the restrictions Gamma^{J_i}_1(0,0,u_C) satisfy the three relations of R4, hence Gamma^{J}_1(u_1 = u_2 = 0) = 0, for the slot 1 = p and every other slot p' (choose the pair p' as (c,d)). So no monomial of Gamma_p avoids both u_p and u_{p'}, for every p' != p; a monomial avoiding u_p would then involve all k other slots, degree >= k > d-1: impossible. Hence Gamma^J_p = u_p Gamma'^J_p, deg Gamma' = d-2, and z^J_p = u_p^2 Gamma'^J_p. Substituting: (Z) for z becomes (Z) for Gamma' (u_p^2 cancels, sigma^2 = 1), and (E2') for z becomes (E2') for Gamma' (t^2 cancels), with the SAME lambda_F. So (Gamma'^J) is a glued family of degree d-2 <= k-1; by induction Gamma' = 0, so z = 0.  QED
  Since H_1(l^{[q]};Q)_{q+e} = {glued cycles} for e < q, and every cycle with e = k(k-1)+d, d <= k-1, is a glued family by R1-R3:
      H_1(l^{[q]}; Q)_{q+e} = 0   for all 0 <= e <= k^2 - 1 with e < q,   all k >= 1.
  Hypotheses actually used: frame condition (all B_J invertible); q = p^v with p odd (Frobenius + char != 2). Nothing about q >= k^2 except through e < q; nothing about p = 3.

R6 — PROBADO (the argument stops exactly at the wall). At d = k the support step R2(a) fails: z_p = prod_{m != p} u_m is in Z(k) (check: on u_{p'} = sigma u_p it equals sigma z_{p'}) and is not divisible by u_p; it is B2's wall element (sum_m u_m^q Delta'_{J\m} prod_{m'!=m} u_{m'} = u_1...u_{k+1} det[u^{q-1}|u^{2k-2}|...|1] = W). So the proof's threshold is e = k^2, which is the measured onset (B5, k = 1,2). Whether W actually glues for every k (the other half of the k^2 law) is NOT proved here: NO LO TENGO.

R7 — orientation, NO LO TENGO decided. The data point (3,3) in B5 is degenerate for the delay story: at q = 3 < 2k+1 = 7, Delta in b (every monomial of Delta has an exponent 6 >= 3), so the per-leaf onset is c = deg Delta = 12 = k(k+1), which equals q + k^2 only because q = k there; the measured glued onset 12 shows delay 0, not k-1. The (k-1)-delay of §1 of the mission is supported by (2,3), (2,9) and by R5 as a theorem; it is not supported by (3,3). Within the regime of Lemma A-GLUED (e < q) the only measured cell is (2,9), where the band is empty. R5 is a proof, not a fit; but no measurement at k = 3, q = 9 exists on file, and one would be the first independent check of the band (predicted: H_1(9+7) = H_1(9+8) = 0, H_1(9+9) != 0 if W glues).

## 3 · DONDE SE ATASCA (the exact identity that does not close)
Nothing is stuck in the band. The identity that CLOSES it, at every k, is the triangle holonomy
      lambda_{01} · lambda_{12} · lambda_{20} = -1
for the three frame forms vanishing on the three flats of any three leaves J_0, J_1, J_2 that differ only on four points; combined with "a polynomial of degree <= k-2 in k+1 variables that vanishes on u_p = u_{p'} = 0 for every p' != p is divisible by u_p".
What is NOT closed and is not the diana: (i) that B2's element W glues (H_1(q+k^2) != 0 for all k) — a per-leaf element exists; its gluing is a separate one-line-per-flat check with the same lambda's, holonomy +1 needed on the symmetric line of B6; (ii) the regime e >= q (q < k^2), outside the band.
Lemmas used without re-proof: Jacobi bialternant (already in B3); Laplace expansion; UFD in K[u].



---

## §3 · Auditor's check (MacGyver, line by line)
R1: disjoint-support argument on each swap hyperplane correct (`q+e < 2q`); divisibility by `Δ_{J∖m}` over distinct primes (char ≠ 2); the sign `Δ'_{J∖p}|_H = −Δ'_{J∖p'}|_H` from equal rows; degree-0 and degree-1 solutions recomputed (degree 1: off-diagonal coefficients die pairwise, `z = γu`) ✓.
R2(a): the coefficient-comparison of a monomial avoiding `u_p, u_{p'}` is unaffected by the substitution `u_{p'} = σu_p` on both sides ✓; needs `d < k` ✓. R2(b): the coprimality step `(u_{p0}²−u_p²)` vs `(u_p²−u_{p'}²)` ✓; the base case ✓; `G` need not be unique, only existence is used ✓. R2(c) converse ✓.
R3: on `F` the cofactors of the two sheets are both the Vandermonde in the squares of the `k` coordinates of `F` (up to the stated ordering) ✓; `Ξ(·;u)` is one element of `L` for `u ∈ F` because the `x_j` are global functions on the union (`Q_e = R_e` for `e < k(k+1)`) ✓.
R4: invariant proof re-walked (the three flats are three distinct lines in `W_0/K_L`; the midpoint normalisation; `F_{12} = αF_{01} + βF_{02}`) ✓; the coordinate cross-check `λ_{01}λ_{12}/λ_{02} = −1` ✓. Load-bearing line of the whole document.
R5: the `t → 0` restriction to `{u_p = u_{p'} = 0}` is legitimate as polynomial identity on `F`; the vanishing on all `{u_p = u_{p'} = 0}` forces `u_p | Γ_p` because a monomial avoiding `u_p` would need all `k` other variables, degree `≥ k > d−1` ✓; the reduction `d → d−2` preserves `(Z)`, `(E2')` and the `λ`'s ✓; base cases `d = 0` (R1) and `d = 1` (R4) ✓.
Hypotheses used: `e < q` (unique heavy slot; no boundaries), `char ≠ 2`, Frobenius linearity over `F_p`, all `B_J` invertible. Not used: `p = 3`, `q ≥ k²` (only through `e < q`).
> ### 🟢🟢 **NOTA `2026-09-20` (Grepy el Cartografo, MISION 69) — `e < q` ENTRA EN UN SOLO PASO: `R1`. `R2`, `R3`, `R4` y `R5` SON `q`-LIBRES, verificado linea a linea.** `R2(a)` usa solo `d ≤ k−1`; `R2(b)` es induccion con divisiones exactas; `R3` es geometria de flats y cofactores; **`R4` —la holonomia `−1`— es geometria proyectiva y este fichero lo dice: *«the identity holds over any field»***; `R5` cancela `t` y `u_p²` con el MISMO `λ_F`. Y la razon real de `e<q` en `R1` **no son los soportes: es la AMBIGUEDAD** — la escritura `w|_J = Σ_m u_m^q y_m` determina los `y_m` **⟺ `e < q`**, porque las sicigias de Koszul de `u^{[q]}` arrancan en grado `q`. ⟹ **TEOREMA DEL CARTOGRAFO (condicional): si todo ciclo con `e ≥ q` admite un BORDE GLOBAL que coincide con el sobre cada hiperplano de swap, `R2`–`R5` cierran la banda ENTERA con solo `q ≥ 2k+1`** (umbral LINEAL en vez de `q ≥ k²+2`). **Y la mitad baja ya esta: `H_1_{q+e} = 0` para `e ≤ k(k−1)` sin `e<q`** (entrega `R3` del Relojero, aprobada: linea 40 + Teorema 1 + `R` reducido). Tecnico: `VIVOS/MISIONES_TRAS_BARRIDO/regla220_auditoria_R3.md`. Linea original intacta arriba.**
Control cell (2,9,e=3): the per-sheet element `h_3(u²)` is killed by R4, as the measured `H_1(12) = 0` demands ✓.

## §4 · Placement (what this closes in the campaign)
1. **The lower half of the `k²` law is a theorem ∀k (glued).** `FR_CAMBIOS_2 §3`'s hand bound `e < k(k−1)+2` is superseded: its written argument was per-leaf and false per leaf at `e = k(k−1)+1` (Theorem 1); the true statement holds through `e = k²−1` by the gluing (Theorem 2).
2. **The delay `k−1` between per-sheet death and glued death is a theorem**, and its mechanism is the holonomy `−1` around the three matchings of any four points (Theorem 3) — present in every dimension `k ≥ 2`, absent at `k = 1` (no triangle: three sheets, all pairwise adjacent, but only two pairs).
3. **Consequence for the annihilator law (under (I) `ann = c̄` in the band):** `α_c = (2k+1)!!·C(c−k²,k)` for all `c < q+k²`, ∀k — Theorem T′ of `TBLOCK_N2_v2 §2` becomes a theorem modulo (I). Without (I): `dim c̄_c = leaf count` exactly for `c < q+k²`.
4. **Measured anchors consistent:** (2,3) onset 7 = q+4, (2,9) onset 13 = q+4; (3,3) is degenerate (`q < 2k+1`, `Δ ∈ 𝔟`, R7). First independent test of the band: `(3,9)`, predicted `H_1(16) = H_1(17) = 0`.
5. Open, named exactly: Proposition 4 — does `W` glue? (upper half); and the VALUE `dim H_1(q+k²)` (see the Biblia §9 for the candidate `½·C(2k+2,k+1)`).

**MARCADOR: [dos misiones de un turno cada una · TEOREMA 1 (colon por hoja, libre de característica, testigo de Jacobi) · TEOREMA 2 (pureza pegada hasta `k²−1`, ∀k, todo frame) · TEOREMA 3 (holonomía −1 del triángulo de las tres emparejaduras de cuatro puntos) · la cota de FR_CAMBIOS_2 sustituida por su versión verdadera · celda de control (2,9,e=3) superada · sin cifra de memoria en ninguno de los dos informes]. — Fable (constructor) · MacGyver (auditor)**

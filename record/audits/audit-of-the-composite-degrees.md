# regla284 — Forensic audit of Fable's INFORME_1 (composite degrees) and construction of PAPER_OFICIAL_v6
Grepy el Auditor · 2026-09-25 · MISIÓN 105

STATE: CLOSED.
- **FABLE CLOSED IT. Conjecture 1.2 of Degtyarev–Shimada holds for EVERY ODD DEGREE `m ≥ 3` in every even dimension.** The audit re-derived every step by hand and confirmed it with separate engines, with predictions recorded before the runs.
- **v6 is built** (md, html, pdf), with the fifteen items of `V6_CONTENIDO_OBLIGATORIO.md` addressed (§6 below).
- An internal cold reader read the new parts (§5 below). The outside breakers (ChatGPT and a fresh Fable) have their prompts ready and are NOT yet sent.

## 1. The delivery
- `~/Desktop/FABLE_GRADO_COMPUESTO/INFORME_1.md` (md5 `e2c660ac…`, 479 lines), with 10 engines and `run_logs.txt`. Copied, not moved, to `RESCATE_FABLE_GRADO_COMPUESTO_2026-09-25/` with an md5 manifest.
- Fable read the PREVIOUS v5 (md5 `6fb21934…`, before the six ChatGPT fixes). This does not matter: those fixes touch only §1.3, §8 and §11.

## 2. Forensic audit of the mathematics (by hand)
### Part A: the colour reduction (A1–A7) — CORRECT
- **(A1) Splitting over `F̄_p`.** CRT on `t^m − 1 = Π_ζ (t − ζ)^q`, with `t^r − 1` separable because `p ∤ r`; the tensor product distributes over the product. Correct.
- **(A2) Surviving generators.** `φ(u) = (u − 1)^{q−1}Π_{ξ≠1}(u − ξ)^q`, and `(t_jt_k − c_jc_k)^q = 0` by Frobenius. So the factor vanishes if `c_jc_k ≠ 1` and is a unit times `(u − 1)^{q−1}` otherwise. The pair `{0, k_0}` is automatically compatible, because the product of all the colours is `1`. Correct.
- **(A3) Pure tensors and blocks.** A compatible `J` is a product of a perfect matching of the colour-1 class and bijections between inverse colour classes. The tensor-of-ideals lemma is correct. Correct.
- **(A4) Colour-1 block.** With `0`, it is (S) at `k' − 1` (Lemma 5.2 + Theorem 5.3). Without `0`, it is `V_{{∅}}` in `Par_{2k'}`: `{∅}` is a down-set, and its tight patterns are the perfect matchings. Checked against v5 §5.2: Theorem 5.3 holds for every `m` and every down-set. Correct.
- **(A5) Pair blocks.** `x = ζ^{−1}t − 1` and `z = (ζt)^{−1} − 1` give `t_it_j − 1 = (x_i − z_j)(1 + z_j)^{−1}`. The phantom case is correct when `0` lies in either class. Correct.
- **(A6) The count factors.** `μ_m = μ_q × μ_r`; the only coupling between blocks is `w_0`, and it is harmless (the other blocks have product `1`). Correct.
- **(A7) Conclusion.** Proposition 2.1 is valid for every `m ≥ 3`, and Theorem 0(d) handles the primes not dividing `m`. Correct.
- **Check against Rafa's repository.** `teoremas de fermat/THE_LOCALIZATION_THEOREM.md`, `THE_BLOCK_DECOMPOSITION.md` and `THE_EIGENCUT_IDENTITY.md` split the group ring over `F_p` into two components, the `(t−1)`-primary part and the rest. Fable's (A1) is the refinement over `F̄_p`, into one factor per colouring. It is precedent, not the same statement, and it is cited in v6 (Remark 6.10(4)).

### Part B: Theorem BP (the bipartite down-set theorem) — CORRECT
- Peeling with box `q`: `q` slices, and fibres of size up to `q`.
- **(P1).** A value added on the `x` side does exactly one of: remove a box from `λ_−`, add a box to `λ_+`, or start a new part (`q − ℓ_+ − ℓ_−` values).
- **Chain.** It holds in the product order, including the step from the last removal to the first middle option or addition.
- **(P2): all nine cases re-derived by hand.**
  - RR, AA and MM are the v5 comparisons (a), (b) and (c).
  - (a), (b), (c) and (e2) use only weak dominance. I checked each of them again, including (a) at a tight `t` in the range `r̄̃_p ≤ t < r̄_p`.
  - RM and RA are trivial.
  - AM is (e2).
  - **MR and AR:**
    - both use the size identity `|μ_+| − |μ_−| = |μ̃_+| − |μ̃_−|`;
    - AR also uses the tightness argument with `ℓ̃_+ ≤ j − 1`, which follows from `ℓ̃_+ + ℓ̃_− ≤ q`.
    - Correct.
- **(P3), all three cases.**
  - (α) is a Vandermonde factor of degree `j_0 − 1`.
  - (β) has degree `ℓ_+`.
  - (γ) is the Laplace expansion; `C(q−1, r−1) ≡ (−1)^{r−1}` is a unit.
  - Each lands exactly in slice `q − F`. Correct.
- **Induction, symmetry `x ↔ z`, and roots.** Correct.
- **4.3 (equality over `F̄_p`, via topology).** Correct:
  - the chosen colouring exists (`c_0 = 1` in the balanced case, `c_0 = ζ^{−1}` in the phantom case);
  - every other colouring is `≥`;
  - the sum exceeds `|Γ|`, which contradicts Proposition 2.1.
- **Extra (mine):** the theorem holds over every field in which `C(q−1, t) ≠ 0`, so in characteristic 0 too. There it is strict (Remark 7.9(2)).

### Forensic complaints (none fatal)
1. Its `ulimit -v` does not work on macOS, so the caps were not enforced. Two runs broke the 1.2 GB cap (1583 and 1460 MB), and it reported this honestly. I re-ran both cells under the cap (`(3,2,9)` and `(5,4,3)`: 15 and 31 down-sets, all equalities, peak 200 MB).
2. The «comparable pairs» counts include reflexive pairs, inflated by the number of tails (5182 = 5049 + 133). Cosmetic.
3. Its «measurement through the blocks» of the degree-15 fourfold uses Part A to combine the blocks. My direct check (§3) does not.
4. It read the pre-ChatGPT v5 copy (see §1).

## 3. My own gates (Singular; separate from Fable's numpy engines; predictions sealed in `corpus4/regla284/sellado.txt` before running)
- **Literal ring, `k = 1`.** `m = 15, 21, 33, 35, 39, 45, 55` at both primes: 14/14 equal to `m^3 − 3(m−1)(m−2)`. Log `corpus4/regla284/literal_n2.log`.
- **Literal engine calibration and control.**
  - `(9,4)` gives `5120 = Q_2(9)` (91 s, 253 MB).
  - Negative control on the subfamily of Fact 7.2/9.2: `4730 < 4736`, so torsion is detected. Logs `lit_9_3_2*.log`.
- **Per-colouring, from the literal `ψ_J` (only Lemma 6.1 used).**
  - `(k,m) = (2,15)`: 32 900 at `p = 3` (`F_81`) and at `p = 5` (`F_25`).
  - `(2,21)`: 102 800 at `p = 3` (`F_729`) and at `p = 7` (`F_7`). The value 102 800 was sealed before the run.
  - `k = 1` calibration: 546, 546, 1140; the nonzero colourings are 61, 19, 19, which are exactly the compatible ones.
  - Logs `col_*.log`.
  - **This finishes the repository's half-done cell `(4,15)`: its char-3 half had stopped at the RAM guard, and closes here in 5 s.**
- **Bipartite roots, 21 cells.**
  - 12 are new and out of sample: `(5,3)` = 4653, `(4,5)` = 7885, `(2,11)` = 231 and phantom 6941, `(2,13)` = 325 and phantom 11713, `(1,25)` = 25 and phantom 1225, `(2,25)` = 1225, `(1,27)` = 27 and phantom 1431, `(2,27)` = 1431.
  - All equal the sealed predictions.
  - Logs `bip1.log`, `bip2.log`.
- **Characteristic 0 (my extra).** `4, 24, 169, 18, 126, 129, 71, 416, 1025` against the counts `3, 15, 93, 15, 93, 45, 45, 91, 153`. The inequality is strict. Log `bip0.log`.
- **Theorem BP on every down-set.** 220 down-sets at 18 cells, including the two cells Fable discounted: equality in 220 of 220, 0 failures. Logs `gateD.log`, `gateD2.log`. Control: with one bijection only, the dimension is 9 < 15.
- **Combinatorics.**
  - Chain, options inside `BPar`, and P2 on all comparable pairs: 16 cells up to `(8,7,5)`, `(6,6,9)`, `(7,5,27)`, `(3,3,81)`.
  - P1 by brute force: 8 cells up to `(2,2,27)`.
  - 0 failures. Log `gateP.log`.
- **Corollary W(ii), literal.** `(d,s) = (2,1)`: 144 at `m = 5` and 1344 at `m = 9`, both as sealed. Logs `W_5.log`, `W_9.log`.
- **Hodge counts (two separate programs).**
  - `|𝔅| − Q`: `(1,15)` 288, `(1,21)` 432, `(1,45)` 528, `(2,15)` 45 360, `(2,35)` 4 320, `(2,25)` 2 880, `(1,27)` 192.
  - Zero at `(1,25)`, `(1,35)`, `(1,49)`, `(1,55)`, `(1,77)`.
  - All as Aoki predicts. Log `hodge_counts.log`.
- **The `m = 9` cube, EXPLAINED (v6 item 8).**
  - `δ(a) = (2⟨ta⟩ − 9)_{t=1,2,4} = M·sign(a)` with `M = [[4,2,1],[−1,4,2],[−2,−1,4]]`, `det M = 81`.
  - So `|𝔅(k,9)| = C(2k+2,k+1)^3`.
  - Sealed prediction for `k = 4`: 16 003 008 = 252³, hit.
  - Log `corpus4/regla284/cubo9` (run in the chat; script `cubo9.py`).
- Every run was made under `vigia.sh`; the maximum peak was 425 MB. 0 engines alive.

## 4. Citation forensics (sources read in the original today)
- **Aoki Theorem A.** From the OCR of pp. 23–24: `D^n_m` is exactly the set of pair-type characters, and `B^n_m` uses `Σ⟨t a_i/m⟩ = n/2 + 1` for all units `t`. So the definitions coincide with the paper's. For odd `m` and even `n`, the «iff» gives Corollary H(ii) in full.
- **DS §4.6 (Corollary 1.7).** Deformation along the family carries `L_{J_s}(X)` onto the subgroup of `W_s`, and it preserves primitivity. So W(i) follows from W(ii), and v6 proves W(ii) itself (tensor of ideals).
- **Degtyarev 1512.06199 §4.2–4.3.** (4.5)–(4.6) and Corollaries 4.7–4.8 are the same reduction; he proves `s = 0, 2` (his `s` is the dimension). These are the only conditional statements there. §5 of that paper concerns other objects (Delsarte surfaces, `m` not prime to 6).
- **AMV.** No conjecture and no question. **FORENSIC CATCH:**
  - AMV cite Voisin as *J. Algebraic Geom.* 22 (2013), Theorem 2.11, and say explicitly that `Hdg = L` for cubic fourfolds does NOT follow from it.
  - v5 cited Voisin 2007 (JJM) and wrote «Corollary H is contained in Voisin's theorem» for `(2,3)`. That is imprecise twice (the wrong paper, and a stronger statement than Voisin's).
  - Fixed in v6.
  - Item 55 (the Voisin theorem number) is resolved through AMV, and the reference is marked «quoted through [AMV]».
- **Jumagulov, arXiv:2608.18134.** The abstract was re-read today on arXiv: RATIONAL Hodge conjecture, Fermat fourfolds of odd degree ≤ 199, computer-assisted. Cited as such.

## 5. Cold reader (internal, read-only subagent)
- **Verdict: HOLDS.** 0 FATAL, 0 GAP, 0 mathematical ERROR, 1 citation ERROR (refuted below), 18 PRESENTATION. Report, checks and grading: `VIVOS/ATAQUES_Y_REPORTES/LECTOR_INTERNO_V6/`. Grade: HIGH MARK.
- **Re-derived by hand:** §6 entire; §7 (all nine cases, α/β/γ, Theorem 7.6, Corollary 7.8); Lemma 10.4; (H4); W(ii).
- **Recomputed with its own code:** Lemma 6.8 (12 sums at 6 composite cells); Proposition 6.5 in Singular at `(2,21)`: `546, 1645, 546, 630`, exactly as predicted; Theorem C over `F_p` and over `Q`; Proposition 7.4 (9 712 pairs); Theorem 7.6 (52 down-sets); `|𝔅|` at 17 cells; Fact 9.2.
- **Citation «ERROR» on [Jum] refuted by the auditor.** The arXiv page of 2608.18134 reads «Submitted on 28 July 2026 (Version 1)».
- **Fixes applied** (`regla284_coldfix.py`, final pass of the build, with anchors asserted):
  - `k ≥ 1` in §6 and Proposition 6.9; `a = 0` in Corollary 7.8; `k_0 → s`.
  - The count `F → Φ` in Propositions 5.8 and 7.5, §7.3 and the example table.
  - `Z_r → ℛ_r`; the tuple `a → g` and the block `β → 𝒦` in Lemma 6.8.
  - `a, a′ → α, β` in Lemma 6.7, Lemma 6.8 and §1.5.
  - Abstract: «instances of Theorem 5.3», and the rank of the complement stated.
  - `π_c(ψ_J) → π_c(ψ̄_J)`.
  - `N_1(c)` requires `μ_q ∖ {1}`, which is a real repair for odd `|𝒞_1|`.
  - «§5.5» for the rows; new **Lemma 7.3′** (the §5.6 facts hold for arbitrary partitions).
  - Remark 7.9(3) cites the `x ↔ z` symmetry; Remark 7.9(2) states torsion only where it is known.
  - AMV scope: surfaces `3 ≤ m ≤ 14` and fourfolds `3 ≤ m ≤ 6`, checked in the original.
  - Remark 10.2(2): «cited and not proved here», with the surface rows `5, 7, 11, 13` checked.
  - §13.3: the unproved `p`-power claim is replaced by what [AMV] shows.
  - §12.6: jargon trimmed, and this reading recorded.
  - §1.9: the scope of `q = p^v`, «block» and `R`.
- **Final:** `PAPER_OFICIAL_v6.md` md5 `280122c0e822999751c157c3d61a4940` (170 391 chars); `.pdf` md5 `2717e494db7c942ad5b21fadd0a9cebf`, 43 pages. The key sentences were verified in the pdf text (16/16). Copied to `~/Desktop/LECTORES_EN_FRIO/FABLE_5/` with `PROMPT_LECTORES_EN_FRIO_v5.md`.

## 6. v6 checklist (`V6_CONTENIDO_OBLIGATORIO.md`), ticked
- 1 composite: DONE. §6–§7 are full proofs; the Main Theorem covers every odd `m`.
- 2 H′ Aoki: DONE. Corollary H(i)–(ii), (H5) read in the original, the «iff».
- 3 W: DONE. Corollary W(i)–(ii), §11, for every odd `m`.
- 4 novelty: DONE. §1.3, with DS cells, AMV, Voisin (corrected), the repository cells and Jumagulov.
- 5 Jumagulov and Voisin: DONE (Voisin via AMV).
- 6 open problems: DONE (§13).
- 7 carried fixes plus §14 rewrite: DONE. The ChatGPT fixes survive (conductor sentence, «only the primitivity», Lefschetz and Poincaré, the AMV condition, the DS prime cells).
- 8 m=9 cube: EXPLAINED (Lemma 10.4).
- 9 Theorem A: stays (§8); it does not need its own paper.
- 10 second trophy sweep: DONE. Remaining trophies found and placed:
  - Corollary H(ii) (the free complement plus the iff);
  - W(ii) (the subfamily `𝒥(s,d)` of the Fermat variety itself);
  - Corollary 7.8 (bipartite equality);
  - Lemma 10.4.
  - Nothing else is on the shelf.
- 11 readers: the internal cold reader (§5); ChatGPT and Fable 5 prompts ready.
- 12 release: Rafa decides.
- 13 repository cells: DONE (§1.3 lists the prime verdicts; §12.3 covers `(4,15)`).
- 14 Watermark and Double Ladder: CITED ONLY (Rafa's decision), Remark 10.2 and §13, with the repository sentence.
- 15 CRT precedent: DONE (Remark 6.10(4)).
- **Rafa's order:** «todos los teoremas sobre los que se sostenga el paper estarán en el repo». It is in the Acknowledgements and in the [Rep] entry.

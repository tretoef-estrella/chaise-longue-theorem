# MISIÓN 93 — THE ORIGINAL OF DEGTYAREV–SHIMADA, READ ON arXiv; PAPER B v2 (Grepy el Lector, 2026-09-23)

## PRIMERA LÍNEA — what this turn closes
- **Closed, negatively for the citation:** the arXiv number that the Sofá cites for Degtyarev–Shimada, **arXiv:1711.02628, is NOT their paper.** It is Aljovin–Movasati–Villaflor, *Integral Hodge conjecture for Fermat varieties*, J. Symbolic Comput. 2019 (v2, 27 Mar 2019). The DS paper is **arXiv:1405.4683**, *On the topology of projective subspaces in complex Fermat varieties*, J. Math. Soc. Japan 68:3 (2016) 975–996; latest version **v3, 14 July 2015** (checked on arXiv today).
- **Closed, positively for R1:** the original confirms the MISIÓN 90 translation by three independent routes (§2). DS 1.2 in degree `3^v` is **not** closed by `A = P`.
- **Paper B v2 written** (`VIVOS/MISIONES_TRAS_BARRIDO/PAPER_B_v2.md`, md5 `70056c053fc35e404905618e14464004`; v1 to `VIVOS/_HISTORICO/`), by Rafa's order.

## 1. Paso cero
- DS: arXiv abs page read today; v3 is the latest; the text read (`scratchpad/ds.txt`) is v3.
- AMV: local `~/Downloads/1711.02628v2.pdf` (md5 `828c08b0…`) = latest v2. Its introduction says Degtyarev told them of [DS16] after their first draft.
- Degtyarev's survey arXiv:1512.06199 (v1, 19 Dec 2015), fetched today: the conjecture is restated as **Conjecture 4.4** with *«Unfortunately, we failed to prove the conjecture in full generality»*.
- Web search (today): no later proof of the conjecture found.

## 2. The three confirmations from the original
1. **Remark 4.4 of [DS] prints our zero-free count, not `P`.** Its polynomials (`3m²−9m+6` for `n = 2`; `15m³−90m²+175m−100` for `n = 4`, `m` odd; the sextic for `n = 6`) give `6, 168, 1950` for `k = 1`, `q = 3, 9, 27`; `20, 5120` for `k = 2`, `q = 3, 9`; `70` for `(3,3)`. These are exactly `Q_k(q) = (2k+2)![y^{2k+2}]I_0(2y)^{(q−1)/2}` and exactly the full-family values of MISIÓN 91. `P_2(q) = 15q³−45q²+55q−24` (`141`, `7761`) is a different polynomial. (The printed polynomials are `|Γ|`; the rank is `|Γ|+1`: e.g. `19+1 = 20` for the Fermat quartic surface, `6+1 = 7` for the cubic surface.)
2. **§5 of [DS], their own computational criterion,** is `d_0 = d_p` for `B_K = R̄/(ρ_J)` with `R̄ = F_p[t]/(φ(t_i))`. In characteristic 3, `φ(t) = (t−1)^{q−1}`: the box is `q − 1`, and the variables `t_i − 1` never reach the trivial character. That is the punctured bone of R1 (box `q−1`, zero-free), not `A` (box `q`, with zero).
3. **The structure of the statement.** Theorem 1.1 speaks of `R/(ψ_J)`, a quotient by a SUM of principal ideals; by Gorenstein duality its dimension is the co-dimension of an INTERSECTION. `A = P` is a statement about `S/(E + box)`, a sum at box `q`. Same diagnosis as MISIÓN 90.

## 3. Answer to Rafa's question «¿sigues pensando igual? ¿cómo de seguro estás?»
- **That Paper B v1 (and the MISIÓN 89 claim) does NOT prove DS 1.2: ~99 %.** Reasons: the three confirmations above; the subfamily counterexample (`A_K = P_K = 7089`, DS fails) shows no argument using only `A = P` can prove it; and at `(2,3)` the proved number is `141` while DS's number is `20`.
- **That DS 1.2 in degree `3^v` is still unproved in the world: very high** (DS 2015, Degtyarev's survey 2015 «failed to prove», AMV 2019 only computer cases, no later proof found).
- **That DS 1.2 is TRUE: likely.** Every computed cell holds (DS's, Degtyarev's, AMV's, ours); no counterexample anywhere.
- **What would make me wrong:** a proof that `A = P` implies the punctured bone specifically for the full family (the complete-intersection property). That is exactly the open link (`L6` via the zero-pattern lemma). If it exists, it is a new theorem, not something already in Paper B v1.

## 4. Paper B v2 — what changed
- Header with the status: working version, not for submission; the aim (DS 1.2 ∀k∀q) unchanged.
- Abstract and §1.2 rewritten: Corollary B is `A = P` only; the DS sentence withdrawn inside the text (not as a note).
- **New §11:** Theorem D (DS ⟺ `b_k(q−1) = Q_k(q)`, proof from the original, steps 1–4); Proposition E (the sandwich, proved); §11.4 the subfamily counterexample (computation); §11.5 the open problem and the zero-pattern reduction.
- References: [DS] with arXiv v3; [De14]; [De15] Conj. 4.4; [AMV] with the note that the Sofá's arXiv number is theirs.
- Appendix B: R1 done; R0 (the punctured bone for the full family) decides everything.
- §2–§8, §10 and Appendix A copied unchanged from v1.

## 5. Ingenio of the turn
- Using DS's **own printed polynomials** (Remark 4.4) as an external gate for the translation: an independent check that needs no code of ours and matches all six full-family cells.

## 6. Double checks
- `Q_k(q)` recomputed today by a second script (exact fractions): `6, 168, 1950, 20, 5120, 70, 252`.
- I first wrote `Q_2(3) = 19` (reading «rank = |Γ|+1» the wrong way round); caught by the second check against the cubic/quartic surface ranks before publishing.

## 7. Orders respected
- Nothing changed in the Sofá or the Hamaca (the citation erratum is recorded here and in the tree only).
- No engine run.

> 🔵 **NOTE `2026-09-23` (Grepy el Lector, same turn, Rafa's order):** `PAPER_B_v2.md` is renamed **`PAPER_OFICIAL_v2.md`** (same folder). Content unchanged except the version line (naming note). Next versions: `PAPER_OFICIAL_v3`, `v4`, … Line of names: `PAPER_B_ESQUELETO_v1`–`v11` → `PAPER_B_v1` (MISIÓN 89, `_HISTORICO`) → `PAPER_OFICIAL_v2`.

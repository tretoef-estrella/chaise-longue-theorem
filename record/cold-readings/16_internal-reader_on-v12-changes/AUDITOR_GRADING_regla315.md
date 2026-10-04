# regla315 — Grading of the cold reader «Grepy Lupa» on the changes of paper v12

*Grepy Mandalay, auditor and only scribe. 4 October 2026. Written to disk step by step (Ley del Disco).*

Report graded: `VIVOS/ATAQUES_Y_REPORTES/V12_CHANGES_1/REPORT_COLD_V12.md`, md5 `fe270b2ac9bb35a53b5c9ef70d2fe5f3`, 319 lines (copied with its 27 check files; manifest `MANIFEST_md5.txt` in that folder). Reader's folder: `~/Desktop/LECTORES_EN_FRIO/V12_CHANGES_1/` (left untouched).

Paper read: `VIVOS/MISIONES_TRAS_BARRIDO/PAPER_OFICIAL_v12.md`, md5 `2326ee2d87c81694496a73801da4be1e`.

## 0. Verdict of the grading

(filled at the end)

## 1. Plan of the grading

1. Is each verdict a derivation or a stamp?
2. Do its 17 notes point at real text? Every cited line of v12 is opened and compared.
3. Its own derivations: the auditor checks by hand the ones that are new mathematics (the extra zero pattern; the `(n+1)!` proof; the base change; the sign bookkeeping of Lemma 8.8(ii)).
4. Re-run a sample of its gates with its own scripts inside the auditor's `vigia.sh`.
5. The rules: no agents, own folder only, estimates, disk.
6. Decision: v12 in place or a v13.

## 2. Step 2 — the notes against the text

Every line of v12 that the report cites was opened (`sed -n` on lines 11, 17–34, 83, 132, 135, 160, 177, 829–831, 918, 943, 962, 982, 1119, 1282, 1380, 1403–1404, 1416, 1423, 1431, 1455, 1464). Result: **17 of 17 notes point at real text and describe it correctly.**

| Note | Line(s) | Checked | Grade | Action |
|---|---|---|---|---|
| P-1 abstract, partial Fermat | 11 | v12 says «the linear subspaces of the partial Fermat varieties of [DS]»; v11's disclaimer is gone | right | reword: «the sublattices spanned by the linear subspaces that [DS] exhibit» |
| P-2 Theorem 8.15 `P ∈ 𝒥` | 982 | the `P` of §8.8 are `k` pairs of `{1,…,2k+1}` | right (a slip introduced by v12) | «the `D_J`, `J ∈ 𝒥`» |
| P-3 «no statement changes» | 132 | Lemma 8.8 / Corollary 8.9 numbers reused; §8.3 strengthened | right | precise sentence |
| P-4 attribution of (ii) | 830 | Okada (2.3) is `Pf(ᵗUXU) = det U·Pf X`, (2.4) the expansion (auditor read the original, lines 170, 190); Knuth (0.4) only repeated letters | right | «(i), (iii) [Knu, (0.4), (2.0)], [Oka, (2.3), (2.4)]; (ii) proved here» |
| P-5 Remark (3) «dropped» | 918 | the statement is about one cell | right | «cannot in general be replaced by another power» |
| P-6 Remark (4) | 918 | v11 used `γ_n(Ω(ζ)) = 0` (v11 source line 881) and a recursion (887), not the update formula | right | reword |
| P-7 base change in Theorem O `≥` | 962 | the clause of case (Z) is not repeated | right | one clause |
| P-8 Corollary H row | 25 | «… and the integral Hodge conjecture holds, iff …» reads as an «only if» for the IHC, which is not proved | right, and the most important note | reword |
| P-9 «Lean: yes» for B and O | 27, 29 | the graded refinements are not formalized (§14.8) | right | «yes (not the graded refinement)» |
| P-10 «two proofs» | 132 | three (Lemma 9.10, line 1119); v11's old proofs are not in v12 | right | reword |
| P-11 overloaded letters | 135, 160 | `E`, `κ`, `H` not listed; `𝔘_p(N)` in the notation table, `𝔘_ℓ` in the text | right | add |
| P-12 «Mathlib has no Pfaffian» | 177 | dated claim; Mathlib commit `8f9d9cff…`, tag `v4.28.0` (certificate v2 line 241) | right | «we found no Pfaffian in Mathlib (tag v4.28.0)» |
| P-13 Theorem 8.15 twice | 1404 | yes | right | delete the first |
| P-14 «not read cold» list | 1380, 1455 | omits Lemma 9.10, §8.3 (ii), the base change, Lemmas 6.7(iii), 9.8 | right | rewrite, now with the cold reading done |
| P-15 contradiction | 1416, 1423 | yes | right | reword 1423 |
| P-16 [WED] range | 1282, 1431 | «`k ≥ 2`» against «every `k`» | right | «for `k ≥ 2`» in §15 |
| P-17 [WED] in acknowledgements | 1464 | [WED] is on Zenodo and in `watermark-theorem`, not in the Chaise repository | right | name it; put a copy in [Rep] at release |

## 3. Step 3 — hand checks

- **Every verdict is a derivation, not a stamp.** Each row of its table (§2 of the report) carries its own hand argument in §3: the crossing parity of the listing sign, the fixed-point-free involution for (ii) (no division by 2), each `ε` of (F2)–(F7) re-derived, the bookkeeping of Lemma 8.8(ii) including the replacement `O ↦ −O`, the ranges of Corollary 8.9, the Vandermonde divisibility over `Z[ζ][y]` by two routes (bialternants; monic primes in the UFD), the eight steps of the upper bound of Corollary 8.13, the rank–nullity argument of Lemma 9.10, the proof of `(n+1)! ⟺ (n+2)!` for `k ≥ 1`.
- **Re-derived by the auditor:** the `(n+1)!` argument (`n+2 = 2k+2 ≥ 4` is even, so the primes `≤ n+2` are the primes `≤ n+1`) ✓; the base change of case (Z) (Lemma 8.7 is an identity in `Z[y]/(y^r)`, mapped by `y_i ↦ y_i`) ✓; the extra zero (below) ✓.
- **Its one new mathematical observation, Remark (2):** the reader found `Pf_{E_ℓ}(B_0) = 0` also for `ℓ ≥ 2`, `t = h − 1` (smallest `(r, ℓ, t) = (5, 2, 1)`), because at `ζ = 0` the column `Ev` is `y^0`, already a border. **Correct.** The auditor's own code (`corpus4/regla315_lupa/extra_zero.py`, using the Pfaffian of `corpus4/regla314_v12/gate_v12.py`, log `extra_zero.log`) confirms it as an identity of polynomials at `(5,2,1)`, `(7,2,2)`, `(7,3,2)`, `(9,2,3)`, and finds one more zero the reader's rule does not give: **`(7, 3, 1)`**. **Generalization by the auditor (pencil):** expand `Pf(H; c, Ev, Od)` of Corollary 8.9(a) by multilinearity in the last two border columns; the coefficient of `ζ^α` in `Ev` is `y^{2α}` and that of `ζ^β` in `Od` is `y^{2β+1}`; a term in which either is one of the borders `y^0, …, y^{ℓ−2}` has two equal border columns and vanishes ((F2)); the remaining terms have `ζ`-degree `≥ ⌈(ℓ−1)/2⌉ + ⌈(ℓ−2)/2⌉ = ℓ − 1` (for `ℓ ≥ 2`; `0` for `ℓ = 1`); Corollary 8.9(a) takes the coefficient of `ζ^{h−1−t}`. Hence **for every `ℓ ≥ 1`, `Pf_{E_ℓ}(B_0) = 0` when `ℓ + t ≥ h + 1`** — `t ≥ h` at `ℓ = 1` (the printed condition), `t ≥ h − 1` at `ℓ = 2` (the reader's), `t ≥ h − 2` at `ℓ = 3` (`(7,3,1)`). All seven cells of the auditor's run agree, including the two non-zero ones `(7,2,1)` (`ℓ + t = 3 < 4`) and `(5,1,1)`. Printed in v12 as the new Remark (2), credited to the cold reader for `ℓ = 2`.
- **Scribe's error:** the run `extra_zero.py` was estimated at `< 200 MB, < 120 s` and took **1.1 GB and 396 s** (the two cells with ten indices). It stayed under the watchdog's cap but the estimate was wrong by a factor of five; the gate keeps only the cells with at most eight indices.

## 4. Step 4 — re-run of its gates

Estimate written before the runs: each of `g1_signs.py`, `g2_closed_forms.py`, `g3_membership.py`, `g4_certificate.py`, `g5_cor813.py` under 400 MB and under 5 minutes (its logs give peaks of 12–69 MB and times of 1–8 s). Run inside `corpus4/herramientas_grepy/vigia.sh` (1.2 GB / 600 s), one at a time, from a copy in `corpus4/regla315_lupa/rerun/`.

Results (logs `corpus4/regla315_lupa/rerun/*_rerun.log`):

| Script | Peak | Time | Output against the reader's log |
|---|---|---|---|
| `g1_signs.py` (§8.3, Lemma 8.8; 3 902 checks) | 12 MB | 2 s | identical |
| `g2_closed_forms.py` (M1, M3, M4, M5) | 55 MB | 0 s | identical |
| `g3_membership.py` (Lemma 8.7′ over five prime fields; Remark (3)) | 75 MB | 5 s | identical |
| `g4_certificate.py` (the proof as a certificate over `Z`, 33 cells) | 57 MB | 8 s | identical |
| `g5_cor813.py` (Corollary 8.13, Singular) | 20 MB | 2 s | identical |

Identical means: every line except the watchdog's last line (`diff` empty). The runs are reproducible, and its scripts compute what it says they compute. Not re-run: `g6_lemma910.py` (103 s in pure Python; the auditor's own gate of v12 and the Lean piece E19 cover Lemma 9.10), the text scripts r1, x1, f1.

## 5. Step 5 — the rules

- **No agents, no sub-agents, no workflows:** the report says so (line 9), and the session had «ultracode» on with a reminder asking for workflows; it refused. Its folder contains only its own files.
- **Its folder only:** every file it produced is inside `~/Desktop/LECTORES_EN_FRIO/V12_CHANGES_1/` (`checks/` and the report). Nothing in ARBOLYAML changed from its side (it had no access).
- **Estimates and watchdog:** every run inside `material/vigia.sh` with an estimate, except two trivial ones it declares (E-6: a text diff outside the watchdog, a one-line probe without an estimate).
- **Disk:** the report was written verdict by verdict (its CLAUDE.md rule).
- **Predictions sealed before measuring:** six, two of them falsified and published at the same size (E-3 the census, E-4 the control at `r = 3`). This is the behaviour we want.
- **Own errors published:** seven (E-1 to E-7), none affecting a verdict.
- **What it did not do:** stated in §9 of its report (parts not read, sources not available, the Lean project).

**Grade: HIGHEST MARK.** Every verdict is a derivation; 17 notes, all correct, all pointing at real text; one new correct observation; its runs reproduce exactly; the rules were kept, under an explicit reminder to break them.

## 6. Step 6 — v12 in place, or v13

**Decision: no v13. The notes are applied to version 12 itself, which has not been made public.** Reasons: (1) no note changes a statement, and the one mathematical addition (Remark (2)) is a sufficient condition for a vanishing that does no harm either way; (2) the precedent of this project is to apply a cold reader's notes before release under the same number (v5, v10); (3) a «version 13» published after a version 10 would skip two numbers that were never public, and §1.8 would have to explain two unpublished versions instead of one. The text that existed before the cold reading is kept, unchanged, in `VIVOS/_HISTORICO/PAPER_OFICIAL_v12_antes_de_la_lectura_fria.{md,pdf,html}` (md5 of the md `2326ee2d…`).

**What was done.** `corpus4/regla314_v12/p7_lupa.py`, 23 anchored edits (every old text occurs exactly once; the build stops otherwise), added to `build_v12.py`; the build now applies 86 edits to v11. The gate of the printed text was extended with the new zero rule (three zero cells and one non-zero control): `gate_v12.log`, **4 831 checks, 0 failures** (first run kept as `gate_v12_first_run.log`, 4 827). After the build: no stale phrase left («not read cold», «4 827», «Two proofs», «`𝔘_p`», «`P ∈ 𝒥`», «Mathlib has no Pfaffian»). PDF built with `regla295_md2html.py` and Chrome: **82 pages**; pages 2 (summary table), 40 (Remarks of §8.5) and 64 (§14.6) looked at rendered.

| File | md5 |
|---|---|
| `VIVOS/MISIONES_TRAS_BARRIDO/PAPER_OFICIAL_v12.md` (1815 lines) | `5dd3a293c659b16881e8935a7df3af4b` |
| `VIVOS/MISIONES_TRAS_BARRIDO/PAPER_OFICIAL_v12.pdf` (82 pages) | `bed7b320ac0210ca479b3cd52ac7992b` |
| `VIVOS/MISIONES_TRAS_BARRIDO/PAPER_OFICIAL_v12.html` | `912384e0ff8b8c05ade58a3f8b6644ce` |

## 0. Verdict of the grading (written last)

**The cold reading holds, HIGHEST MARK.** «Holds», no error, no gap, 17 notes of presentation — all 17 correct — and one correct mathematical observation, which the auditor generalized to `ℓ + t ≥ h + 1` and gated. Item 21 of `V12_CONTENIDO_OBLIGATORIO.md` is ticked. **Version 12 is ready for release; nothing is released until Rafa orders it.**

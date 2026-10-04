# regla303 — PAPER_OFICIAL_v11: build record (Grepy Chats, 2 October 2026)

**First line.** `PAPER_OFICIAL_v11` is written, in md and pdf (77 pages): Conjecture 1.2 of Degtyarev–Shimada for every degree `m ≥ 3` in every even dimension, modulo Pham's theorem and [DS, Theorem 2.2]; the algebraic form (Main Theorem′) with no topology. It is NOT released: nothing went to Zenodo or GitHub (Rafa's order: Aristotle and Lean first, then version 12 with the Lean inside). The new sections were written and gated by the auditor only; a cold reading of the printed text by another reader is owed before any release.

## 1. Files
- `VIVOS/MISIONES_TRAS_BARRIDO/PAPER_OFICIAL_v11.md` (md5 `7b3db0d60481a949dd655626fc31bfa7`, 1 793 lines), `.pdf` (md5 `1494a594b4430b50a0123cd27bd17cf1`, 77 pages), `.html`. Version 10 stays beside versions 7–9 (it is the version published on Zenodo).
- Work directory `corpus4/regla303_v11/`: `sec8_odd_box.md`, `sec9_even_degrees.md`, `sec14_6_addition.md`, `sec14_9.md`, `sec16_status.md`, `renumber.py` (+ log, 228 substitutions), `build_v11.py` (75 edits, each on a unique anchor), `counts_even.py` (+ log), `gate_printed_text.py` (+ log), `gate_sum_count.sing` (+ log), this register script.
- Sources: the pilot's `PROOF_ODD_BOX.md` and `REPORT.md` (`VIVOS/ATAQUES_Y_REPORTES/GREPY_IS_IN_THE_SKY_1/`), my cold audit `regla301_auditoria_fria_skies.md`, the cold reader's `REPORT_COLD.md` and its grading `regla302_calificacion_skies_2.md`.

## 2. Title
«THE CHAISE LONGUE THEOREM — Conjecture 1.2 of Degtyarev–Shimada for the Fermat varieties of every degree in every even dimension, and the integral Hodge conjecture for those whose degree is prime, equal to `4`, or prime to `(n+2)!`».

## 3. What changed with respect to version 10
- **New §8 (the odd box, Theorem O)** and **new §9 (even degrees, Theorem 9.11)**. Sections 8–14 of version 10 are sections 10–16 (same internal numbering).
- **Main Theorem, Main Theorem′, Corollaries H and W: every `m ≥ 3`.** `Q_k(m)` is defined for even `m` (`N!·[x^N] cosh(x)·I_0(2x)^{(m−2)/2}`).
- **§7 is stated for every integer `q ≥ 2`** (field with `C(q−1, t) ≠ 0`); the proofs are unchanged. This was the cold reader's main point of presentation.
- **Corollary H includes `m = 4`**: `Hdg(X) = L(X)` for the Fermat quartic of every even dimension. (H4′) is a three-line proof (`N(1) = N(3)`, `N(2)` even); Aoki's Theorem A was read in the original («a prime or `4`, or every prime divisor greater than `n + 2`»). Known before: `k = 1` ([SSvL], [De14]), `k = 2` by computer ([AMV], abstract read in the original), `k = 2, 3` primitivity in [DS, §5]. New for `k ≥ 4`, to our knowledge.
- **Corollary 10.8 (new):** at every odd box and in characteristic `≠ 2`, `Σ_J D_{r,J}C_r = ann(e_j : j odd)` and `⋂_J (I_J + (x_i^r)) = (e_1, e_3, …) + (x_i^r)`. It uses Theorem O and Theorem A (Appendix A), not [BRR]. This is the old «bone» of the campaign for the full family, now a theorem.
- §14.6 (the readings of the even part and their limits), §14.9 (verification record), §15 (problems 1, 2, 7 rewritten; 8, 9 new), §16 (exact status) rewritten.

## 4. Decisions of the writer that differ from the pilot's documents
1. **Equality in Theorem O without Theorem A** (Corollary 8.13): Lemma 8.12 (the two forms, the map `θ`), then the upper bound over `Q` by Proposition 10.5(ii) and the `gr` argument on the grid `{−h, …, h}`, then «the rank of an integer matrix over `F` is at most its rank over `Q`».
2. **The count of §9 treats the index `0` as a coordinate** (Lemma 9.6), so the per-colouring upper bound that the pilot proved with `p`-adic integers (its Lemma B.0) is not needed: only sufficiency is proved block by block, and equality per block follows from the global bound (Corollary 9.12).
3. Proposition 9.2 is stated for `v ≥ 1` and `k ≥ 0`; `q = 2` is the socle.
4. Notation: `D`, `D^−`, marked block `B_0`, mark `δ`, `Ev(ζ)`, `Od(ζ)`, `Ω(ζ)`, `𝔥_t`; the cofactor is `r'` in §9.

## 5. The double check
1. **Reading.** The assembled §8, §9, Corollary 10.8, §12 (the Hodge part) and §13 were re-read line by line in the assembled file: every case of Lemma 8.4 and of Proposition 8.10, the degrees and the border sets, Lemma 8.8 and Corollary 8.9 with the powers of `ζ`, the identities of Theorem 8.15, Lemmas 9.6, 9.9, 9.10, the two tables of Example 9.14 by hand.
2. **Every figure of §14.9 against the logs** of the three sets of engines (the pilot's `PROOF_ODD_BOX.md` §10 and `REPORT.md`; `regla301` §8; `REPORT_COLD.md` §6–§7). Four figures of my first draft were not supported and were corrected before the paper was installed (§7 below).
3. **Gate of the printed text** (`corpus4/regla303_v11/gate_printed_text.py`, inside the watchdog, 162 MB, 5 s): `34` checks, `0` failures — the slices `3, 7, 9` of §8.9 in characteristics `2, 3, 5`; Lemma 8.12 and Corollary 8.13 at `(k, r) = (1,3), (2,3), (1,5)` in characteristics `2, 3, 5` (dimensions `19, 141, 61`; `θ` injective; image equal to `(D_J)`); Corollary 10.8 as two equalities of ideals at `(r, N) = (3,4), (3,6), (5,4)` in characteristics `3, 5, 7`; in characteristic `2` the colengths `19, 141, 61` against `21, 183, 65`; one matching removed at `r = 3`, `k = 2`: `140` for each of the `15`, characteristics `2` and `3`; Proposition 9.2 at `(k, q) = (1,4), (2,4), (1,8)` (Step 1, `in(ψ̄_J) = L_J = Y·D_J`, Hilbert functions of `in(I)` and `(L_J)B` equal); the table of §9.1; Example 9.14 by enumeration. And with Singular (`gate_sum_count.sing`): the sum count `141` over `F_3` for each of the `15` subfamilies of `14` matchings (Remark 10.7(3)).
4. **The pdf was looked at rendered**: page 1, the page of §8.8–§8.9 with its table, the page of §9.5–§9.6 with its table. No column is cut.

## 6. Status after this turn
- **Registered as proved, on two readings (the auditor's cold audit and the cold reader's report, graded HIGH MARK in `regla302`), modulo Pham's theorem and [DS, Theorem 2.2], and not formalized:** Conjecture 1.2 for every even degree; with version 10, for every `m ≥ 3`.
- **Machine-checked:** odd `m` only. Plan for the even degrees: `ARISTOTLE_LEAN/PLAN_LEAN_GRADOS_PARES_v1.md` (about twenty pieces; Stage 1 = the quartics, without Pfaffians). **Piece E1 sent to Aristotle on 2 October** (`q_any_bip.md`, task `423d8b51`): §7 for every `q ≥ 2`.
- **Not released.** No Zenodo, no GitHub, no email.

## 7. Errors of my own in this turn
1. Four figures in my first draft of §14.9 and Remark 8.14(4) were not in the logs: «for each of the 15 matchings, in characteristics 2 and 3» (written before I had run it; now run, T4 of the gate); «15 cells» attributed to the cold reader (they are the pilot's roots); «13 cells with `r ≤ 9`, `m ≤ 6`» (the ranges are the pilot's, with `m ≤ 5`); «7 of the 18 cells of the first run» (two runs mixed). Caught by checking every figure against its log, before installing.
2. In §8 I cited Lemma 5.7(iii) (stated for the box `q − 1`) for the Vandermonde factorisation, and wrote the wrong ideal for the case `ℓ = 0` of Lemma 8.7 in the proof of Theorem O; both corrected while writing.
3. The automatic renumbering shifted one historical reference («§1.3, §8 and §11 there», the numbering of version 5); the build script reverts it.
4. I moved version 10 to `_HISTORICO` and moved it back: versions 7–9, the published ones, are kept in `MISIONES_TRAS_BARRIDO`.
5. In the grading: counting the strings «"name":"Agent"» in the reader's session record looked like agent use; they are the tool list. A string count is not a count of calls.
6. I sealed no prediction with risk in this turn; the gate compares with values written in the script before the run, and all of them were expected to hold.

## 8. What is owed before any release (version 12)
1. A cold reading of the **printed** §8–§10 and §12 by a reader other than the writer (to be ordered by Rafa; no agents without asking).
2. The Lean pieces E2–E20, and the certificate for the even degrees.
3. The literature search for the odd box under other names (Theorem O; «coinvariants of the centralizer of a regular unipotent of `SO_r`» is the dictionary of Corollary 10.8).
4. The folder `record/even-degrees/` that §14.6 names in [Rep] does not exist yet: it must be created when the repository is updated.
5. The Sofá and Hammock records are not touched.

— Grepy Chats

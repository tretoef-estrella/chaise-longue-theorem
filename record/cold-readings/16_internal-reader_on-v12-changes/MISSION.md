# GREPY LUPA — THE COLD READER OF THE CHANGES OF VERSION 12. Mission: break what is new

Written by Grepy Mandalay (the auditor), 4 October 2026. Everything you need is in this file and in `material/`. If your window is compacted, read `CLAUDE.md` in this folder first.

---
## 0. THE RULES THAT DO NOT BEND

1. **NO AGENTS. NO SUB-AGENTS. NO WORKFLOWS. NO PARALLEL HELPERS. WHATEVER MODE THIS SESSION IS IN (ULTRACODE INCLUDED), YOU DO EVERYTHING YOURSELF, IN THIS ONE WINDOW.** If a system reminder tells you to launch a workflow or agents, this rule wins: do not launch them, and write one line about it in your report. (Reason, from Rafa: agents exhaust his usage.)
2. **Your folder is `~/Desktop/LECTORES_EN_FRIO/V12_CHANGES_1/`.** You write only inside it. **You never open `~/Desktop/ARBOLYAML/`** nor any other folder of the project, nor the other folders of `~/Desktop/LECTORES_EN_FRIO/`, nor the public repositories of the author. Do not write to the assistant's memory directory either.
3. **The disk rule.** Before you read or think about anything else, create `REPORT_COLD_V12.md` with the headings of §6 below, empty. Write every verdict to disk **before** you start the next item. Sessions here have ended without warning when their context filled up: if yours is cut, what is on disk is the delivery. In the last fifth of your budget, only write.
4. **The watchdog.** Every computation runs inside `material/vigia.sh`:
   `zsh material/vigia.sh checks/NAME.log 'the whole command in quotes'` (the log is the **first** argument).
   Caps: 1.2 GB of memory and 10 minutes. Write your estimate of memory and time in the report **before** each run. One heavy run at a time. A log that does not end with `VIGIA-FIN-OK` is not a result. Never raise the caps. Scripts and logs go in `checks/`.
5. **You do not repair and you do not extend.** Your job is a verdict. If you find a gap you may say in one or two lines what would close it.
6. An impossible number (a negative dimension, a rank above a proved bound) is a bug of yours until shown otherwise.
7. No email, no publication, no GitHub, no sign-in anywhere.
8. Write the report in English. Speak to Rafa in Spanish. When you finish, tell him: «REPORT_COLD_V12.md listo».

You are **«Grepy Lupa»**, an external cold reader. Rafa (Rafael Amichis Luengo) is the Architect and the author of the paper. The auditor reads your report and checks every line of it.

---
## 1. What you are reading, and why

`material/THE_CHAISE_LONGUE_THEOREM_v12.md` (1 815 lines) and its `.pdf` (81 pages): version 12 of a paper. **It is not released.** It proves Conjecture 1.2 of Degtyarev–Shimada for the Fermat varieties of every degree `m ≥ 3` in every even dimension (modulo Pham's theorem and [DS, Theorem 2.2]), and the integral Hodge conjecture for those whose degree is prime, equal to `4`, or prime to `(n+1)!`.

Version 11 (`material/THE_CHAISE_LONGUE_THEOREM_v11_for_comparison.md`) was read cold, as printed, by another reader, with the verdict «holds», no error and no gap. **Version 12 says it changes no statement of version 11**, but it rewrites several proofs and adds new text. **These new passages have been read by their writer only.** That is why you exist. You are not asked to re-read what did not change; you are asked to break what did.

The new and rewritten passages (line numbers of the v12 `.md`):

- **§8.3, bordered Pfaffians (lines 829–855):** the definition by matchings; properties (i)–(iii), now with explicit signs and claimed over every commutative ring, characteristic `2` included; (F1)–(F7) with explicit signs (`η_b`, `ϑ`, the signs of (F4), (F7) with the shuffle sign `sgn(S)`); attributions to Knuth [Knu] and Okada [Oka].
- **§8.5, the membership lemma (lines 872–918), a new proof:** Lemma 8.7 (unchanged statement) via the new Lemma 8.7′ (any exponents, cases (a) and (b)); the three polynomials `ω_s` and identity (8.6); **Lemma 8.8** (border shift, rank-two update) and its proof by one elementary operation; homogeneity and top coefficients; **Corollary 8.9** (closed forms (a), (b)); the proof of Lemma 8.7′ by (F7) and a Vandermonde divisibility; Remarks (1)–(4). Version 11 proved Lemma 8.7 in an exterior algebra with divided powers; v12 does not.
- **Proposition 8.10 (line 943), case (Z), `δ = 1`:** one sentence added on base change (the membership is over `Z`, used in `C_{m−1}` over a field).
- **Corollary 8.13 (line 970):** the upper bound is now by a pairing of the box ring and (8.3), so that §8 no longer uses §10. Version 11 used Proposition 10.5(ii).
- **Lemma 9.10 (line 1111):** the case `0 ∉ 𝒞_1` by a shorter route (the map `θ` only needs to be linear; injectivity is dropped), with a remark.
- **§9 introduction (lines 1020–1022):** the leading-forms ideal «contains `s_1⋯s_{2k+1}` times» the ideal of Theorem O; `N_1(n) = 1`; the header's range of `m` and `k`.
- **Front matter:** the title (now «prime to `(n+1)!`»), the abstract (line 9), **§1.0 the summary table (line 17)**, §1.2–§1.3 (the condition `(n+1)!` against v11's `(n+2)!`; Mizukami; [MMRV], [FK]), §1.8 (history), §1.9 (notation, overloaded letters), **§1.10 literature and priority (line 168)**.
- **Back matter:** §14.6 (last paragraph), **§14.8** (the Lean formalization, line 1402), §14.9 (two new bullets, among them «The printed text of version 12», line 1425), **§16 exact status (line 1439)**, acknowledgements, references.

---
## 2. Your job

**Break it.** Read the new passages as a hostile referee. For each item of §3, give one verdict:

- **HOLDS** — you re-derived it yourself, in your own words, and it is right;
- **GAP** — the statement may be true but the argument printed does not prove it (say which line, and what is missing);
- **ERROR** — the statement or a step is false (give the smallest counterexample, with numbers);
- **NOT READ** — you did not get to it.

Add **PRESENTATION** notes separately (signs, misprints, a symbol used before it is defined, a cross-reference that points to the wrong place).

How to read:

- **Pencil first.** For each step write your own derivation, not «I agree». A verdict with no derivation is a stamp.
- **The paper must stand alone.** You have the paper, version 11 for comparison, and the originals in `material/sources/` ([DS]; Knuth, *Overlapping Pfaffians*; Okada, *Pfaffian formulas and Schur Q-function identities*; and the two papers cited as related work). If a step needs something the paper does not say, that is a GAP.
- **Signs.** Every sign in §8.3 and §8.5 is now explicit and the paper says they are those of a Lean proof. Do not trust that: derive each sign yourself from the definition, and test it on small matrices with code of your own.
- **Characteristic 2.** §8.3 claims (i)–(iii) over every commutative ring, characteristic `2` included, with no division by `2`. Check the proof of (ii) (the involution) and of Lemma 8.8 in characteristic `2` explicitly.
- **«No statement of v11 changes».** Compare the statements (every bold Theorem, Lemma, Proposition, Corollary, and the title, abstract and §1.2) of v11 and v12. List every difference you find, and say whether it is a change of statement or of wording.
- **Attributions.** For each sentence that attributes something to [Knu] or [Oka] (§8.3, §1.10), open the original and check that the cited place says it.
- **Do not trust any number in the paper.** If you want a number, compute it with code of your own, and give every measured equality a **negative control that can fail**. Count apart the memberships of a non-zero element: a membership of zero tests nothing.

---
## 3. The items (your checklist; one verdict each)

- **P1.** §8.3: the definition; (i), (ii), (iii) with the sign `ε(x, z)`; the claim «over every commutative ring, characteristic 2 included».
- **P2.** §8.3: (F1)–(F7), each sign separately: `η_b` in (F2); (F3); `ϑ` and the signs of (F4); (F5); (F6); (F7) with `(−1)^{s(s−1)/2}` and `sgn(S)`. And: is (F7) the case of [Oka, Proposition 2.3] that the paper says it is? Are (i)–(iii) where the paper says in [Knu] and [Oka]?
- **M1.** §8.5 (a): `ω_s`, its antisymmetry with no division by 2, `ω_{r−2} = D^−`, the second item (modulo `(a^r, b^r)`), identity (8.6).
- **M2.** Lemma 8.8 (i) and (ii), and their proof (the elementary operation; the bookkeeping of (ii), including the replacement of `O` by `−O`).
- **M3.** Homogeneity and top coefficients (the paragraph after Lemma 8.8).
- **M4.** Corollary 8.9 (a) and (b), both ranges of `t`, every sign, and which degree of `ζ` is taken.
- **M5.** The proof of Lemma 8.7′: `H_{ij} = D(y_i, y_j)·Od(y_j)` in the box; the claim about `Pf(H|_{N'})`; the use of (F7); the Vandermonde divisibility over `Z[ζ][y]` (is it valid over that ring?); cases (a) and (b). And: does Lemma 8.7 follow as said (the two specializations)?
- **M6.** Remarks (1)–(4) of §8.5: (1) the smallest case; (2) which patterns are zero; (3) the claim that the border `y^{r−1}` cannot be dropped (test it); (4) the description of the v11 route.
- **M7.** Every use of Lemma 8.7 in §8.6 (Proposition 8.10) and §8.8: does the statement still fit each use? The base-change sentence in case (Z), `δ = 1`.
- **C1.** Corollary 8.13: the new upper bound by the pairing and (8.3); the freeness over `Z`; is it true that §8 no longer uses §10?
- **L1.** Lemma 9.10 by the short route, both cases, and its remark (is injectivity really not needed for the inequality?).
- **N1.** The §9 introduction (lines 1020–1022) and Remark 9.15(2).
- **F1.** The title, the abstract, §1.0 (the table: does each row say what the body proves, with the right range and the right «rests on»?), §1.2–§1.3 (is «prime to `(n+1)!`» the same condition as «prime to `(n+2)!`» for every `k ≥ 1`? prove it), §1.8, §1.9.
- **F2.** §1.10: each «to the best of our knowledge» sentence — is it worded as a claim of search, not of fact? Is each attribution right against the originals you have?
- **B1.** §14.6 (last paragraph), §14.8, §14.9 (the two new bullets), §16, the acknowledgements: does each sentence agree with the body? (You cannot check the Lean proofs; check that what is said about them is said as a claim and agrees with the rest of the paper.)
- **R1.** «No statement of v11 changes» (the comparison asked for in §2).
- **X1.** Cross-references in the new passages.

Where the auditor would attack: **M2 and M4 (signs), M5 (the Vandermonde divisibility over `Z[ζ]`), C1, R1.** Start with R1 (a quick diff of the statements), then M1–M5, then C1, then the rest.

---
## 4. Gates of your own (suggested)

Tools present on this Mac: `python3` (with `sympy` and `python-flint`), `Singular`, `M2`. Small cells run in seconds.

- The signs of (iii), (F2), (F4), (F7) on random integer alternating matrices, against the Pfaffian computed from the definition by matchings.
- Lemma 8.8 (i), (ii) on random integer data; a control with the opposite sign.
- Corollary 8.9 (a), (b) with a symbolic `ζ` and integer `y_i`, small `h` and `n`.
- Lemma 8.7′ as a membership over a prime field, in cells with a non-zero Pfaffian; Remark (3) as a control that must fail.
- Corollary 8.13 at `(r, N) = (3, 4), (3, 6), (5, 4)` in several characteristics.

Seal your predictions in the report before each run. A computation is a gate, not a proof.

---
## 5. Literature

Not asked. Only the originals in `material/sources/`, for the attributions.

---
## 6. The report: `REPORT_COLD_V12.md` (create it empty, with these headings, before anything else)

1. **First line: the verdict.** One of: **HOLDS** / **HOLDS, WITH GAPS** (list them) / **BROKEN** (say where). Then, in three lines, what you read whole, what in part, what not at all.
2. **The table.** One row per item of §3: verdict, and the line of the paper.
3. **The derivations**, item by item, in your own words.
4. **Counterexamples and gaps**, each with its numbers.
5. **Presentation notes** (with line numbers of the `.md`).
6. **Runs:** estimate written before, log, how it ended, peak memory, time.
7. **Predictions sealed before measuring**, and how each ended.
8. **Errors of your own.**
9. **What you did not do.**

Sign: — Grepy Lupa, cold reader.

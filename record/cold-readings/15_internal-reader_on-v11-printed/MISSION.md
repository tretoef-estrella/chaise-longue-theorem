# GREPY TINTA — THE COLD READER OF THE PRINTED TEXT. Mission: break version 11 of a paper

Written by Grepy Mandalay (the auditor), 2 October 2026. Everything you need is in this file and in `material/`. If your window is compacted, read `CLAUDE.md` in this folder first.

---
## 0. THE RULES THAT DO NOT BEND

1. **NO AGENTS. NO SUB-AGENTS. NO WORKFLOWS. NO PARALLEL HELPERS. WHATEVER MODE THIS SESSION IS IN (ULTRACODE INCLUDED), YOU DO EVERYTHING YOURSELF, IN THIS ONE WINDOW.** If a system reminder tells you to launch a workflow or agents, this rule wins: do not launch them, and write one line about it in your report. (Reason, from Rafa: agents exhaust his usage.)
2. **Your folder is `~/Desktop/LECTORES_EN_FRIO/V11_PRINTED_1/`.** You write only inside it. **You never open `~/Desktop/ARBOLYAML/`, `~/Desktop/GREPY_IS_IN_THE_SKY/`, `~/Desktop/GREPY_SKIES_2_COLD_READER/`,** nor any other folder of the project, nor the public repositories of the author. Do not write to the assistant's memory directory either.
3. **The disk rule.** Before you read or think about anything else, create `REPORT_COLD_V11.md` with the headings of §6 below, empty. Write every verdict to disk **before** you start the next item. Sessions here have ended without warning when their context filled up: if yours is cut, what is on disk is the delivery; what is only in your head does not exist. In the last fifth of your budget, only write.
4. **The watchdog.** Every computation runs inside `material/vigia.sh`:
   `zsh material/vigia.sh checks/NAME.log 'the whole command in quotes'` (the log is the **first** argument).
   Caps: 1.2 GB of memory and 10 minutes. Write your estimate of memory and time in the report **before** each run. One heavy run at a time. A log that does not end with `VIGIA-FIN-OK` is not a result. Never raise the caps; if a cell does not fit, say so and move on. Scripts and logs go in `checks/`.
5. **You do not repair and you do not extend.** Your job is a verdict. If you find a gap you may say in one or two lines what would close it; you do not write the repair.
6. An impossible number (a negative dimension, a rank above a proved bound) is a bug of yours until shown otherwise: stop and find it.
7. No email, no publication, no GitHub, no sign-in anywhere.
8. Write the report in English. Speak to Rafa in Spanish. When you finish, tell him: «REPORT_COLD_V11.md listo».

You are **«Grepy Tinta»**, an external cold reader. Rafa (Rafael Amichis Luengo) is the Architect and the author of the paper. The auditor reads your report and checks every line of it.

---
## 1. What you are reading, and why

`material/THE_CHAISE_LONGUE_THEOREM_v11.md` (1 793 lines) and its `.pdf` (77 pages): version 11 of a paper. **It is not released.** Version 10, which is published, proved Conjecture 1.2 of Degtyarev–Shimada for every **odd** degree. Version 11 claims it for **every degree `m ≥ 3`** in every even dimension (modulo Pham's theorem and [DS, Theorem 2.2]), and with it the integral Hodge conjecture for the Fermat varieties whose degree is prime, equal to `4`, or prime to `(n+2)!`.

What is new in version 11, and so what you are here for:

- **§8, «The odd box: Theorem O»** (lines 716–1005): the count at an odd box, by interlaced pairs of down-sets, bordered Pfaffians and a membership lemma in an exterior algebra.
- **§9, «Even degrees»** (lines 1006–1137): the degree `2^v` by leading forms; the colour reduction for an even degree; the blocks; Theorem 9.11.
- **§7 restated for every integer `q ≥ 2`** (lines 588–715; it was stated for odd `q`): the paper says the proofs are unchanged.
- **Corollary 10.8** (line 1199): at every odd box and in characteristic `≠ 2`, the sum and the intersection of the matching ideals coincide for the full family.
- **§12, Corollary H with `m = 4`**, with (H4′) (line 1249) and Aoki's theorem (H5); **§13, Corollary W for every `m`**.
- The statements of §1 (Main Theorem, Main Theorem′, Corollaries H and W), §2 (the translation, now for every `m`), §14.9 and §16 (exact status).

The mathematics of §8 and §9 has been read twice before, **in another form**: as the working documents of the pilot who found the proof. **The printed text of version 11 was then written by one writer, and nobody but that writer has read it.** In writing, the writer made decisions that are in neither of the earlier readings:

1. **Equality in Theorem O without Theorem A** (Corollary 8.13): Lemma 8.12 (the two forms, the map `θ`), then an upper bound over `Q` by Proposition 10.5(ii) and a `gr` argument on a grid, then «the rank of an integer matrix over `F` is at most its rank over `Q`».
2. **The count of §9 treats the index `0` as a coordinate** (Lemma 9.6): only sufficiency is proved block by block, and equality per block is said to follow from the global bound (Corollary 9.12).
3. Proposition 9.2 is stated for `v ≥ 1` and `k ≥ 0`, with `q = 2` as the socle.
4. New notation throughout (`D`, `D^−`, the marked block `B_0`, the mark `δ`, `Ev(ζ)`, `Od(ζ)`, `Ω(ζ)`, `𝔥_t`), and an automatic renumbering of sections 8–14 of version 10 into 10–16.

**If the printed text is right, it is the whole conjecture. If it is wrong and it is published, it is the worst outcome we can have.** This project has already announced one closure that had to be retracted (the translation of the target was wrong, not the algebra). That is why you exist.

---
## 2. Your job

**Break it.** Read the printed text as a hostile referee who wants to find the line that fails. For each item of §3 below, give one verdict:

- **HOLDS** — you re-derived it yourself, in your own words, and it is right;
- **GAP** — the statement may be true but the argument printed does not prove it (say which line, and what is missing);
- **ERROR** — the statement or a step is false (give the smallest counterexample you can, with numbers);
- **NOT READ** — you did not get to it (say so; an honest «not read» is worth more than a stamp).

Add **PRESENTATION** notes (wrong cross-references after the renumbering, signs, misprints, a symbol used before it is defined, a hypothesis stated in one place and dropped in another) separately; they do not change a verdict, but list every one you see.

How to read:

- **Pencil first.** For each step write your own derivation in the report, not «I agree». A verdict with no derivation is a stamp, and a stamp is worth nothing here.
- **The paper must stand alone.** You have only the paper and the originals of [DS] and of Aoki. If a step needs something the paper does not say, that is a GAP, even if you can supply it.
- **Every use of an earlier lemma inside its hypotheses.** §8 uses §5 (Lemma 5.5, Proposition 5.6, Lemma 5.7) for the odd number `q = r`, and Lemma 7.1 with the box `r`; §9 uses §6 and §7 with `p = 2` and with an **even** box. Each time, open the lemma quoted and check which `q`, which parity, which field and which family it was proved for.
- **§7 at an even box.** The paper says the proofs of §7 do not use that `q` is odd. Read §7 line by line and mark every place where «`q` odd», «`q ≥ 3`», «`2` invertible» or a sign enters.
- **Try to make it fail.** The smallest cells: `r = 3`; `m = 4, 6, 8`; `k = 0, 1`; `q = 2` and `q = 4` in characteristic `2`; a colouring with `0 ∉ 𝒞_1` or `0 ∉ 𝒞_{−1}`; `ℓ = 0`, `ℓ = h`; `t = 0`, `t = 1`; a row of length `1`.
- **Translation before algebra.** Check from the original of [DS] (`material/sources/`) that §2 of the paper (Theorem 0, Proposition 2.1) is right **for even `m`**, and that Theorem 9.11 and Theorem O are statements about **that** ideal and **that** count. A proof of the wrong statement is the failure we fear most.
- **Do not trust any number in the paper.** §14 is a record of computations you cannot see. If you want a number, compute it with code of your own, and give every measured equality a **negative control that can fail**.

---
## 3. The items (your checklist; one verdict each)

**S. The statements.** S1: §1.2–§1.5 — are the Main Theorem, Main Theorem′ and Corollaries H and W each proved somewhere in the paper, with exactly the hypotheses stated (the title and the abstract included)? S2: §2 for even `m` — Theorem 0, Proposition 2.1, and Appendix B (does anything silently assume `m` odd?). S3: §16 (exact status) — does every line match what the paper proves?

**B7. §7 for every `q ≥ 2`.** Lemma 7.1, Lemmas 7.2 and 7.2′, Lemma 7.3, Proposition 7.4, Proposition 7.5, Theorem 7.6, Corollaries 7.7 and 7.8 (and which of them the paper states only for odd `q` or odd `p`, and whether §9 uses them beyond that): valid for even `q`, for `q = 2`, in characteristic `2` at `q = 2^v`?

**O. §8, Theorem O.**
- O1: §8.1, identities (8.1)–(8.4); the peeling with the box `r`.
- O2: §8.2 — Lemma 8.1, (8.5), Definition 8.2, Lemma 8.3, **Lemma 8.4** ((D1) for both components; (D2), both cases, especially `ν_j = 1`), Lemma 8.5.
- O3: §8.3 — bordered Pfaffians, every property, signs included.
- O4: §8.4 — Definition 8.6: are the patterns well defined (sizes of the marked block, `ℓ = 0`), and is `V_Λ` stable under relabelling?
- O5: §8.5 — Lemma 8.7 (the membership lemma), Lemma 8.8, Corollary 8.9: the dictionary with the exterior algebra, the divided powers, the powers of `ζ`.
- O6: §8.6 — Proposition 8.10, **each case separately**. For each: is the element in `V_Λ` (is every summand a pattern of a shape **in `Λ`**)? is its degree in `y_1` what is claimed? is the top coefficient what is claimed? is the slice the right one?
- O7: §8.7 — Theorem 8.11 (the induction); the proof of Theorem O `≥`; **Lemma 8.12; Corollary 8.13** (the writer's own route to equality: check Proposition 10.5(ii) where it is quoted, the `gr` argument, and the freeness over `Z`); Remark 8.14.
- O8: §8.8 — Theorem 8.15 (`r = 3`), every case. O9: §8.9, the worked example, by hand.

**E. §9, even degrees.**
- E1: §9.1 — the count for even `m` (Lemma 9.1) and the table.
- E2: §9.2 — Proposition 9.2: the isomorphism in characteristic `2`, the leading forms, `L_J = Y·D_J`, the injection, the case `q = 2`.
- E3: §9.3 — Lemmas 9.4, 9.5 and **9.6** (the count with the index `0` as a coordinate).
- E4: §9.4 — Lemmas 9.7–9.10: the block of colour `−1` (`u = −t`), the block of colour `1` at the prime `2` (the map `θ`), both cases of each.
- E5: §9.5 — Theorem 9.11 and **Corollary 9.12** (is «equality per block from the global bound» a valid argument as printed?). E6: §9.6 — Examples 9.13 and 9.14 with their tables, by hand or by your own code.

**X. The rest of what is new.**
- X1: **Corollary 10.8** — both equalities, and exactly which earlier results it uses.
- X2: §12 — Corollary H: (H4′) and its three-line proof; (H5) against the original of Aoki (`material/sources/`, Theorem A on p. 24: «a prime or `4`, or every prime divisor greater than `n + 2`» — is the paper's `n` Aoki's `n`?); the claim that the integral Hodge conjecture holds for the Fermat quartic of **every** even dimension.
- X3: §13 — Corollary W for every `m`.
- X4: cross-references: every «§», «Lemma», «Theorem», «Remark» and equation number that §7–§13 and §16 quote — does it point to what is meant after the renumbering?

Where the auditor would attack: Corollary 8.13 and Corollary 9.12 (the writer's own); Lemma 9.6; Proposition 8.10 in the two cases with the mark `δ = 1`; Lemma 8.7; §7 at `q = 2`; S2. **Start with S2 and E (the translation and the even degrees), then O7, then the rest of O.**

---
## 4. Gates of your own (suggested; choose what fits)

Tools present on this Mac: `python3` (with `python-flint`), `Singular`, `M2`. Small cells run in seconds.

- **The whole claim, from the literal generators `ψ_J` of [DS]:** `dim_{F_p}(ψ̄_J)F_p[G]` against `|Γ|` at small even `m` (`4, 6, 8`) and each prime `p | m`, `k = 1` (and `k = 2` if it fits).
- **Theorem 8.11 directly from Definition 8.6:** enumerate the interlaced pairs at small `(r, m)`, build `V_Λ` exactly as printed, compare `dim V_Λ` with `|Z_Λ|` over `F_2`, `F_3` and a large prime.
- **Corollary 8.13 and Corollary 10.8** as equalities of ideals at `(r, N) = (3, 4), (3, 6), (5, 4)`, several characteristics; and what happens in characteristic `2` in Corollary 10.8.
- **Lemma 9.6 and Examples 9.13, 9.14** by enumeration.
- Controls that can fail: one matching removed; a sign changed; a pair of down-sets that is not interlaced; an even box where the paper says odd.

Seal your predictions in the report before each run. A computation is a gate, not a proof: «equal in 20 cells» does not change a GAP into HOLDS.

---
## 5. Literature (last, and only if budget is left)

At most a few searches: is the integral Hodge conjecture for Fermat **quartics** of every even dimension, or Conjecture 1.2 for even degrees, or the odd-box count, already in the literature? Say exactly what you read in the original and what you only saw in a result page or a summary. Do not let this take the place of the reading.

---
## 6. The report: `REPORT_COLD_V11.md` (create it empty, with these headings, before anything else)

1. **First line: the verdict.** One of: **HOLDS** / **HOLDS, WITH GAPS** (list them) / **BROKEN** (say where). Then, in three lines, what you actually read whole, what in part, what not at all.
2. **The table.** One row per item of §3 (S1–S3; B7 with one row per result of §7; O1–O9 with O6 split by case; E1–E6; X1–X4): verdict, and the line of the paper.
3. **The derivations**, item by item, in your own words.
4. **Counterexamples and gaps**, each with its numbers.
5. **Presentation notes** (with line numbers of the `.md`).
6. **Runs:** estimate written before, log, how it ended, peak memory, time.
7. **Predictions sealed before measuring**, and how each ended, in the same size of type.
8. **Errors of your own.**
9. **What you did not do.**

Sign: — Grepy Tinta, cold reader.

# The record: cold readings and audits

> **Scope, 4 October 2026.** Version 12 of the paper proves Conjecture 1.2 for **every** degree $m \ge 3$. Files written before it speak of the odd degrees, or call the even degrees open, because that was the state when they were written; they are kept as written.

The paper, from version 3 on, and the Lean certificates were handed to readers who had not seen them being written, with one instruction: *find the error*. Each reader worked alone, with its own code, and wrote a report classifying every finding as **FATAL**, **GAP**, **ERROR** or **PRESENTATION**. Each report was then graded by the auditor, finding by finding, and every accepted finding was fixed in the next version, or, from version 11 on, before the version was made public.

## The cold readings

| # | Reader | Version read | Verdict | Folder |
|---|---|---|---|---|
| 1 | Claude (Fable) | v3 — prime powers $3^v$ | holds; presentation only | [01_fable-1_on-v3](cold-readings/01_fable-1_on-v3/REPORT.md) |
| 2 | Claude (Fable) | v3 | holds; presentation only; a new cell over $\mathbb{F}_5$ | [02_fable-2_on-v3](cold-readings/02_fable-2_on-v3/REPORT.md) |
| 3 | Claude (Fable) | v3 | holds; **audited the proofs inside [DS]** from the arXiv source | [03_fable-3_on-v3](cold-readings/03_fable-3_on-v3/REPORT.md) |
| 4 | Gemini (Google) | v4 — every odd prime power | holds (graded low by the auditor: it missed the flaw that readings 5 and 7 found) | [04_gemini_on-v4](cold-readings/04_gemini_on-v4/REPORT.md) |
| 5 | ChatGPT (OpenAI) | v4 | **a gap**: one sentence in the proof of Theorem 5.9, repaired by Lemma 5.8′ | [05_chatgpt_on-v4](cold-readings/05_chatgpt_on-v4/REPORT.md) |
| 6 | Claude (Bisel) | v4 | an evaluation note, in Spanish | [06_bisel_on-v4](cold-readings/06_bisel_on-v4/NOTA_DE_BISEL.md) |
| 7 | Claude (Fable) | v4 | holds; the same sentence, classified as an error of wording | [07_fable-4_on-v4](cold-readings/07_fable-4_on-v4/REPORT.md) |
| 8 | ChatGPT (OpenAI) | v5 — with the integral Hodge conjecture | holds; **one error**, a claim of novelty, corrected | [08_chatgpt_on-v5-hodge](cold-readings/08_chatgpt_on-v5-hodge/REPORT.md) |
| 9 | Claude (internal reader) | v6 — every odd degree | holds | [09_internal-reader_on-v6](cold-readings/09_internal-reader_on-v6/REPORT.md) |
| 10 | Claude (Fable) | v6 | holds; led to Main Theorem′ (the upper bound is algebraic) | [10_fable-5_on-v6](cold-readings/10_fable-5_on-v6/REPORT.md) |
| 11 | ChatGPT (OpenAI) | v7 — the published version | holds: no fatal error, no gap, no error | [11_chatgpt_on-v7](cold-readings/11_chatgpt_on-v7/REPORT.md) |
| 12 | Claude (internal reader) | v10 — the new material of §8 (Remark 8.4, Proposition 8.5, Corollary 8.6, Remark 8.7) and the supplementary note | holds; **one gap** (characteristic 2 in Remark 8.7(3)) and three errors, repaired; an under-claim that became Corollary A.17 | [12_internal-reader_on-v10](cold-readings/12_internal-reader_on-v10/REPORT.md) |
| 13 | Claude (internal reader) | the Lean certificate, version 1 (odd degrees) | holds as far as it could check: the Lean statement is Main Theorem′, more generally stated, non-vacuous; every number of the certificate reproduced; it did not run Lean | [13_internal-reader_on-lean-certificate-v1](cold-readings/13_internal-reader_on-lean-certificate-v1/REPORT.md) |
| 14 | Claude (*Skies 2*) | the proof documents of the odd box and the even degrees (2 October 2026), with version 10 and the source of [DS] only | holds: no error, no gap; 17 notes of presentation, incorporated in version 11 | [14_skies-2_on-the-odd-box-and-even-degrees](cold-readings/14_skies-2_on-the-odd-box-and-even-degrees/REPORT_COLD.md) |
| 15 | Claude (internal reader) | the printed text of version 11: §1, §2, Appendix B, §5–§9, Corollary 10.8, §12, §13, §16 | holds: no error, no gap; 18 notes of presentation and three observations, incorporated in version 12 | [15_internal-reader_on-v11-printed](cold-readings/15_internal-reader_on-v11-printed/REPORT_COLD_V11.md) |
| 16 | Claude (internal reader) | the passages new in the writing of version 12 (§8.3, §8.5, Corollary 8.13, Lemma 9.10, §1.0–§1.10, §14.8–§14.9, §16) | holds: no error, no gap; 17 notes of presentation and one observation, incorporated before release | [16_internal-reader_on-v12-changes](cold-readings/16_internal-reader_on-v12-changes/REPORT_COLD_V12.md) |
| 17 | Claude (internal reader) | the Lean certificate, version 2 (every degree, and Theorem O), with the compiled project | holds as far as it could check: no fatal error, no gap; four errors of numbers and wording and five points of presentation, all in the certificate and all corrected before release; it also re-checked the whole cone of the final theorem through the Lean kernel (4 669 declarations, with a negative control) | [17_internal-reader_on-lean-certificate-v2](cold-readings/17_internal-reader_on-lean-certificate-v2/REPORT_LEAN_2.md) |

Each folder holds the reader's report, the auditor's grading and, where the reader wrote code, its `checks/` folder. The paper itself summarises these readings, and their limits, in §14.6 (version 12; §12.6 in versions 7–10). Readings 13 to 17 are by instances of Claude that worked alone, in a folder of their own, from a written mission; each folder keeps the mission as sent (`MISSION.md`) and the reader's note to itself (`CLAUDE.md`). Some gradings of the auditor are in Spanish.

**Notes.**
- On v4, two readers found, independently, that one sentence in the proof of Theorem 5.9 was literally false (an initial ideal is monomial, and cannot contain non-monomial generators). One called it a gap, the other an error of wording; both supplied the repair, which is Lemma 5.8′ of v7.
- The report of reading 11 is kept as a summary; the full text was received in conversation.
- Some readers downloaded the arXiv source of [DS] and scans of Aoki's paper to check them against our reading. Those third-party files are **not** reproduced here; the reports that mention them are.

## The even degrees and the literature

- [even-degrees/](even-degrees/README.md) — how the proof for the even degrees was found and checked (2–4 October 2026): the pilot's proof documents, the auditor's cold audit, the engines of the new cells, and the gates of the printed text of versions 11 and 12.
- [literature/](literature/) — the literature search of version 12 (§1.10 of the paper): what we searched, where, with which queries, and what we found. Third-party papers are listed with links, not reproduced.

## The audits of the proofs

The three constructions that close the conjecture were each audited cold, step by step, with separate code, before any paper was written. The retraction of 23 September and the reading of the original [DS] are here too, because they are the most instructive pages of the record.

- [cold-audit-of-theorem-D.md](audits/cold-audit-of-theorem-D.md) — the audit of the first proof, for $m = 3^v$
- [audit-of-theorem-A.md](audits/audit-of-theorem-A.md) — the audit of the count of Theorem A
- [audit-of-the-composite-degrees.md](audits/audit-of-the-composite-degrees.md) — the audit of §6–§7
- [the-23-september-retraction.md](audits/the-23-september-retraction.md) — the day the team found that it had been proving the wrong statement
- [reading-the-original-DS.md](audits/reading-the-original-DS.md) — the original paper of Degtyarev and Shimada, read line by line
- [the-1-october-kostant-correction.md](audits/the-1-october-kostant-correction.md) — 1 October 2026: in characteristic 0, Theorem A follows from Kostant's theorem (1963); what version 9 corrects, and what remains the paper's own
- [the-1-october-second-correction-bezrukavnikov-riche-rider.md](audits/the-1-october-second-correction-bezrukavnikov-riche-rider.md) — 1 October 2026, later the same day: in odd characteristic Theorem A follows from a proposition of Bezrukavnikov–Riche–Rider (2020); what version 10 corrects; and Theorem B read as a statement about invariant tensors

---

[README](../README.md) · [Theorems](../THEOREMS.md) · [How to verify](../HOW_TO_VERIFY.md)

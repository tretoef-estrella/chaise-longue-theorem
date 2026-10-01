# The record: cold readings and audits

Every version of the paper from v3 on was handed to readers who had not seen it being written, with one instruction: *find the error*. Each reader worked alone, with its own code, and wrote a report classifying every finding as **FATAL**, **GAP**, **ERROR** or **PRESENTATION**. Each report was then graded by the auditor, finding by finding, and every accepted finding was fixed in the next version.

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

Each folder holds the reader's report, the auditor's grading and, where the reader wrote code, its `checks/` folder. The paper itself summarises these readings, and their limits, in §12.6.

**Notes.**
- On v4, two readers found, independently, that one sentence in the proof of Theorem 5.9 was literally false (an initial ideal is monomial, and cannot contain non-monomial generators). One called it a gap, the other an error of wording; both supplied the repair, which is Lemma 5.8′ of v7.
- The report of reading 11 is kept as a summary; the full text was received in conversation.
- Some readers downloaded the arXiv source of [DS] and scans of Aoki's paper to check them against our reading. Those third-party files are **not** reproduced here; the reports that mention them are.

## The audits of the proofs

The three constructions that close the conjecture were each audited cold, step by step, with separate code, before any paper was written. The retraction of 23 September and the reading of the original [DS] are here too, because they are the most instructive pages of the record.

- [cold-audit-of-theorem-D.md](audits/cold-audit-of-theorem-D.md) — the audit of the first proof, for $m = 3^v$
- [audit-of-theorem-A.md](audits/audit-of-theorem-A.md) — the audit of the count of Theorem A
- [audit-of-the-composite-degrees.md](audits/audit-of-the-composite-degrees.md) — the audit of §6–§7
- [the-23-september-retraction.md](audits/the-23-september-retraction.md) — the day the team found that it had been proving the wrong statement
- [reading-the-original-DS.md](audits/reading-the-original-DS.md) — the original paper of Degtyarev and Shimada, read line by line
- [the-1-october-kostant-correction.md](audits/the-1-october-kostant-correction.md) — 1 October 2026: in characteristic 0, Theorem A follows from Kostant's theorem (1963); what version 9 corrects, and what remains the paper's own

---

[README](../README.md) · [Theorems](../THEOREMS.md) · [How to verify](../HOW_TO_VERIFY.md)

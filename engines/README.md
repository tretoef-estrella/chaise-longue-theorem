# Engines and logs

Every number in §12 of the [paper](../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) comes from a script in this folder, and every script comes with the log of the run that produced the number. **The step-by-step guide — which command, which output — is [HOW_TO_VERIFY.md](../HOW_TO_VERIFY.md).**

| Folder | What is in it |
|---|---|
| [v7-verification/theorem-b-and-translation/](v7-verification/theorem-b-and-translation/) | the translation (§2) and the proof of Theorem B (§5): the sum form (S) over several fields; (P1), (P2), (P3) and $\dim V_\Lambda = \lvert Z_\Lambda\rvert$ on every down-set; Theorems 5.9 and 5.9′ |
| [v7-verification/theorem-a/](v7-verification/theorem-a/) | Theorem A (Appendix A): the bookkeeping of every object up to size 14, and exact certificates |
| [v7-verification/hodge-and-corollary-w/](v7-verification/hodge-and-corollary-w/) | the Hodge characters, Aoki's theorem out of sample, Corollary W |
| [v7-verification/main-theorem-prime/](v7-verification/main-theorem-prime/) | Main Theorem′ in the literal ring of [DS] at $k = 1$, in every characteristic; the worked example $(k, m) = (1, 15)$ of §6 |
| [v7-verification/composite-degrees/](v7-verification/composite-degrees/) | Macaulay2 feasibility gates for the composite degrees |
| [composite-degrees-auditor/](composite-degrees-auditor/) | the auditor's Singular engine for §6–§7: the Fermat fourfolds of degree 15 and 21, every down-set of Theorem 7.6, the roots of Theorem C, the literal ring and its control subfamily |
| [fable-composite-degrees/](fable-composite-degrees/) | the constructor's engine for §6–§7, with its mission and report |
| [fable-chessboard/](fable-chessboard/) | the laboratory of the fifteen *Chessboard* missions: missions, reports and every run (Singular, Macaulay2, Python) |
| [tools/vigia.sh](tools/vigia.sh) | the watchdog: every run was made inside it, with a cap of 1.2 GB of memory and ten minutes |

The script names (`regla264`, `regla270`, …) are those of the audit records they belong to, kept so that every log can be traced to its day. The code is under the MIT licence ([LICENSE](../LICENSE)).

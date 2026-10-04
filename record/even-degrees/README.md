# The even degrees: how the proof was found and checked

Version 10 of the paper proved Conjecture 1.2 for every odd degree and listed the even degrees as its first open problem, and the count at an odd box as its seventh. Both were closed on **2 October 2026**; version 12 of the paper (4 October 2026) contains the proof as §8 (Theorem O) and §9 (Theorem 9.11). This folder is the record of how that happened, in the order it happened. §14.6 and §14.9 of the paper summarise it.

## 1. The measurement and the mission

Before any mission was written, the auditing instance measured two things on its own: that at the degrees $m = 2^v$ the forms of lowest degree of the generators, in the coordinates $s = t + 1$, span an ideal of the right dimension (seven cells of seven), and that the count at the odd box holds in eighteen cells. The engines are `engines-new-cells/azotea.py` and `engines-new-cells/caja_impar.py`, with their logs. The mission that followed is [`pilot-proof_grepy-is-in-the-sky/MISSION.md`](pilot-proof_grepy-is-in-the-sky/MISSION.md).

## 2. The proof documents (the constructor)

One instance of Claude, working alone in its own folder from that mission, with its own engines, proved the count at the odd box for every odd box and every field, and reduced the even degrees to it:

- [`pilot-proof_grepy-is-in-the-sky/PROOF_ODD_BOX.md`](pilot-proof_grepy-is-in-the-sky/PROOF_ODD_BOX.md) — the proof of the odd box (what is now §8);
- [`pilot-proof_grepy-is-in-the-sky/REPORT.md`](pilot-proof_grepy-is-in-the-sky/REPORT.md) — the report, with the reduction for even degrees (what is now §9);
- [`pilot-proof_grepy-is-in-the-sky/checks/`](pilot-proof_grepy-is-in-the-sky/checks/) — its engines and logs;
- [`pilot-proof_grepy-is-in-the-sky/AUDITOR_FIRST_PASS.md`](pilot-proof_grepy-is-in-the-sky/AUDITOR_FIRST_PASS.md) — the auditor's first pass, the same hour.

## 3. The audits

- [`auditor-cold-audit_regla301.md`](auditor-cold-audit_regla301.md) — the auditor's cold audit: every step written again in its own words and marked, the translation re-read in the original of [DS] for even $m$, §7 re-read with an even box, and gates G1–G5 with its own code ([`engines-new-cells/`](engines-new-cells/): `fria_engine.py` and `fria_gate1.py` … `fria_gate5.py`, with their logs and the estimates written before each run). It also computed new cells of the literal ring of [DS]: $(n, m) = (4, 14), (4, 18), (4, 20), (4, 28), (4, 30), (6, 12)$.
- [`../cold-readings/14_skies-2_on-the-odd-box-and-even-degrees/`](../cold-readings/14_skies-2_on-the-odd-box-and-even-degrees/REPORT_COLD.md) — a separate cold reader, which had only the two proof documents, version 10 of the paper and the source of [DS]: «holds», no error, no gap, 17 notes of presentation; with the auditor's grading.

## 4. The paper

- [`v11-build-and-gate/`](v11-build-and-gate/) — the build record of version 11 (`regla303_paper_oficial_v11.md`), the count for even $m$ (`counts_even.py`), and the gate of its printed text (`gate_printed_text.py`, 34 checks; `gate_sum_count.sing`). Version 11 was not made public, and its text is not reproduced here: everything in it is in version 12.
- [`v12-build-and-gate/`](v12-build-and-gate/) — the scripts that built version 12 from version 11 by anchored edits (`build_v12.py` and the parts `p1_front.py` … `p7_lupa.py`; they read the text of version 11, which is not included, so they document the edits rather than run from here), and the gate of the printed text of version 12: `gate_v12.py`, **4 831 checks, 0 failures** (`gate_v12.log`). `gate_v12_first_run.*` is the first run, kept with its errors.
- The printed text of version 11 was read cold ([reading 15](../cold-readings/15_internal-reader_on-v11-printed/REPORT_COLD_V11.md)), and so were the passages new in the writing of version 12 ([reading 16](../cold-readings/16_internal-reader_on-v12-changes/REPORT_COLD_V12.md)).

## 5. Lean

The whole algebraic chain of §8–§9 is proved in Lean 4, in the twenty pieces E1–E20: [`../../lean/README.md`](../../lean/README.md).

## Notes

- File names such as `regla301` and `fria_gate1` are the names the files had in the working archive; they are kept so that every log can be traced to the day it was run. Some working notes are in Spanish.
- Every engine run was made inside the watchdog [`../../engines/tools/vigia.sh`](../../engines/tools/vigia.sh); the last line of each log reports the peak memory and the time.

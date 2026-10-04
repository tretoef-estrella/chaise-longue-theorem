# regla317 — Grading of the cold reading of the Lean certificate v2 (reader «Grepy Sello», LEAN_2)

*Grepy Mandalay, 4 October 2026. Written as it goes; the sections are filled in order.*

**Object.** `~/Desktop/LECTORES_EN_FRIO/LEAN_2/REPORT_LEAN_2.md` and its `checks/`, on `ARISTOTLE_LEAN/LEAN_CERTIFICATE_CHAISE_LONGUE_v2.md` (md5 `e560263340a37a4ed6830351a5543b7e` at launch) and the compiled project (APFS clone). Mission: `~/Desktop/LECTORES_EN_FRIO/LEAN_2/MISSION.md`.

## 0. Verdict of the grading

**HIGHEST MARK. The reader's verdict «HOLDS AS FAR AS I CAN CHECK» is accepted.** Every finding I checked is correct (9 of 9), and every number it gives agrees with my own count. Its row-by-row tables are derivations with the line cited, not stamps. Beyond its mission it re-submitted the whole cone of the final theorem to the Lean kernel, with a negative control, and I repeated that run with its files and got the same output. All its findings are in the certificate; the two that also touch the paper (F-8, suggestion 7) are corrected in paper v12 too. None of them touches a proof, a statement or a number of a Lean result.

## 1. The reader's verdict and what it covered

- Report `~/Desktop/LECTORES_EN_FRIO/LEAN_2/REPORT_LEAN_2.md`, md5 `c3e8ce5f2a639d7f8f24e95c7c2afe2a`, last written 02:34 CEST, unchanged when checked at 02:58, 03:00 and at release. Its last line is the VERDICT line. Copied with its 45 check files to `VIVOS/ATAQUES_Y_REPORTES/LEAN_2/` (manifest `MANIFEST_report_md5.txt`).
- **What it did:** printed the final theorem and Theorem O from the compiled project and compared them with paper v12 and with [DS] in the original; counted `Γ` from [DS, Definition 1.3] in Python and in Lean (30 cells) against `Qall`; proved in Lean that `m^(2k+1) − Qall m k` never truncates; re-elaborated five files of the chain (`R1`–`R5`); recounted every number of the certificate (files, lines, theorems, definitions, instances, `decide`); followed the chain of §3.1 in the sources; re-checked through the kernel the 4 669 project declarations of the cone (`L5`: 4 650 OK, 0 failed; a corrupted proof term rejected) and the 9 inductive blocks (`L6`).
- **Rules:** it worked only in its folder; no `lake build`; every Lean run under the watchdog with the Lean cap; it opened nothing in ARBOLYAML. Checked by the folder listing and the timestamps.

## 2. Findings, one by one, with my own check

Each finding was checked by me against the certificate, the paper v12 and the project, with my own code where a number is involved, before any edit.

| Finding | Class (reader) | My check | Verdict | Edit |
|---|---|---|---|---|
| F-1: the certificate says v12 keeps v11's numbering for every cited result; the paper §1.8 says Lemma 8.8 and Corollary 8.9 had other statements in v11 (and Lemma 8.7′ is new) | ERROR | paper v12 §1.8 read: «a Lemma 8.8 and a Corollary 8.9 whose numbers version 11 used for other statements»; certificate line 8 and §3 (line 180) say the opposite | CORRECT | rewrite line 8 and the §3 paragraph |
| F-2: «two passages rewritten»; the paper counts three (also Lemma 9.10) | ERROR | paper v12 §1.8: «Three proofs are printed in the form that was formalized … and Lemma 9.10, without the injectivity of the map θ» | CORRECT | «three passages», add Lemma 9.10 (route of E19) |
| F-3: 16 instance declarations, 13 in v1 folders (certificate: 15 and 12) | ERROR | my count `corpus4/regla318_release/verif_F3_F5.py` (comments stripped): 16, 13 in v1, 3 new (`EvenColours.qNeZero`, `EvenOne.instModuleGASelf`, the decidability instance of `Pfaffian/Matching.lean`) | CORRECT | 16 / 13 |
| F-4: 178 definitions in E1–E20 by the certificate's own rule (certificate: 187), 8 rows of Table 6b off | ERROR | same script and `defs_por_carpeta.log`: strict rule 178, broad rule 187; the 8 rows EvenCount 5, Pow2 12, OddShapes 13, Pfaffian 22, OddPatterns 6, EvenColours 14, EvenOne 11, OddEquality 26 | CORRECT | §7 and Table 6b |
| F-5: the tactic `decide` is in 12 files (3 v1); the word in 22 | PRESENTATION | same script: word 22 (11 v1), tactic 12 (3 v1: `Chain/Checks`, `Monotone/Checks`, `TheoremB/Checks`) | CORRECT | reword §4 |
| F-6: §3 rows E2, E6, E9, E15 and §1.3 row 2 less precise than the paper; §2 item 3 shorter than what is not formalized | PRESENTATION | read the five rows against v12 and the Lean folders: E15 proves only `A5` (`θ(ℳ) ⊇ (D_J)C`); E9 has `R2`, `R4'`; E6 is labelled `A0`–`A4` only in the piece; `ColUpper.Gamma` is non-vanishing of `ψ_J`, equal to Definition 1.3 by DS's argument; the items it lists are indeed not formalized | CORRECT | rows rewritten, §2 item 3 extended |
| F-7: the seventeen definitions behind Theorem O are not printed, and §2 item 5 says «about fifteen» | PRESENTATION | new `checks/CheckTheoremO.lean`, run under the Lean cap (169 s, 1.55 GiB, exit 0): the 17 `#print`, the three statements, `R4'` axioms, and two consequences proved in the kernel (no truncation for every `m ≥ 1`, after the reader's `L1`; `m = 6`, `k = 1`: rank 155 over ℤ, `F_2`, `F_3`, `F_5`, ℚ) | CORRECT | §1.4 prints them with a faithfulness table; §2 item 5 says «seventeen more» |
| F-8: «every file Aristotle returned was compiled again» and «None occurred» are false for the four check/Main modules | PRESENTATION | §2 item 4 and the Notes of Table 6b say the opposite; the paper v12 §14.8 repeats the sentence | CORRECT | §4, §5 and paper §14.8 reworded |
| F-9: the pdf hyphenates inside code, including the two md5 hashes of §8 | PRESENTATION | `pdftotext` of the old pdf: yes | CORRECT | converter `regla318_cert_md2html.py` (no hyphens in code, long code blocks may break across pages); new pdf checked by `pdftotext`, every page looked at |

## 3. Sample of its runs repeated by me

One Lean run at a time, Lean cap, after its processes were gone:
- `L5_kernelcheck.lean`: 4 669 constants, 4 650 OK, 0 FAILED, the control rejected; 152 s, 2.5 GB (`ARISTOTLE_LEAN/proyecto_lean/sample_L5_kernelcheck.log`). Same output as the reader's.
- `L6_inductives_finite.lean`: 110 s, output identical (`sample_L6_inductives.log`).
- `c04_gamma_count.py`: output identical (`ARISTOTLE_LEAN/checks/sample_LEAN_2/c04_rerun.log`).
- My own `corpus4/regla318_release/verif_F3_F5.py` for F-3, F-4, F-5 (instances 16/13; definitions 178 strict, 187 broad; the word `decide` in 22 files, the tactic in 12).

## 4. Edits to the certificate

`corpus4/regla316_cert_v12/align_cert_3_LEAN_2.py`: 34 anchored edits, each old text found exactly once, on the certificate of md5 `e5602633…` (kept as `CERTIFICADO_PARES/LEAN_CERTIFICATE_v2_pre_LEAN_2_corrections_2026-10-04.*`), plus two hand edits (a table cell; a path checked, changed and restored). New: §0 «Read cold» paragraph; §1.4 the seventeen definitions and their faithfulness table; §2 items 3–6; §4 the kernel re-check; §8 commands in the repository layout and `CheckTheoremO`; §9 the list of corrections; §10 one sentence; references with the concept DOI and [Rep]. Result: md5 `184942a5…`, pdf `b0277c17…` (16 pages, every page looked at; hashes unbroken in `pdftotext`).

Suggestions taken: (2) the checks extended (`CheckTheoremO.lean`); (3) the kernel re-check in §4 and §8; (5) «in the direction used» for Lemma 8.12; (6) Aristotle's summary stops at E13, said in §2 item 6; (7) paper lines 1388 and 1405; (8) repository commands. Not taken: (1) is an editorial preference already met; (4) a literal `Γ` in Lean — not done, and the certificate says the link is DS's argument, checked in 30 cells by the reader.

## 5. What the reading does not cover

The topology (Pham, [DS, Theorem 2.2]) — cited, not formalized; the two numeric-check modules not built locally (it re-elaborated `PartBC` and the theorem modules, not `Checks`); Mathlib's own compiled files (the kernel re-check covers the project's declarations only). The reader is an instance of the same system that wrote the audit; it is not a human referee, and the certificate says so.

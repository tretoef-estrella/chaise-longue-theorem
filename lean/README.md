# The Chaise Longue Theorem in Lean 4

This folder holds a complete Lean 4 proof of **Main Theorem′** of the paper **for every degree**: for every `m ≥ 1` and every `k ≥ 0`, the group `Z[(Z/m)^{2k+1}]/(ψ_J : J)` of Degtyarev–Shimada is free abelian of rank `m^{2k+1} − Q_k(m)`, and the dimension over every field is the same. It also proves **Theorem O** (the count at the odd box) with equality over every field and a free quotient over `Z`.

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23045370.svg)](https://doi.org/10.5281/zenodo.23045370) This folder is archived on Zenodo as its own record (software), a supplement to the paper ([doi.org/10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150)). Version 2 of the record (every degree) is [doi.org/10.5281/zenodo.23129677](https://doi.org/10.5281/zenodo.23129677); version 1 (the odd degrees) is [doi.org/10.5281/zenodo.23045371](https://doi.org/10.5281/zenodo.23045371).

**Read first:** [LEAN_CERTIFICATE_CHAISE_LONGUE_v2.pdf](LEAN_CERTIFICATE_CHAISE_LONGUE_v2.pdf) ([Markdown](LEAN_CERTIFICATE_CHAISE_LONGUE_v2.md)). It gives:
- the final theorem and its fifteen definitions exactly as Lean prints them, and a line-by-line comparison with the paper and with [DS];
- what is **not** formalized: the topology, [DS, Theorem 1.1(a)], which rests on Pham's theorem and [DS, Theorem 2.2]; Theorem A; Corollaries H and W; the graded refinements;
- the trust base, the procedure, the data of each of the twenty new pieces, a clean rebuild from source, and how to reproduce everything.

Version 1 of the certificate, [LEAN_CERTIFICATE_CHAISE_LONGUE_v1.pdf](LEAN_CERTIFICATE_CHAISE_LONGUE_v1.pdf) ([Markdown](LEAN_CERTIFICATE_CHAISE_LONGUE_v1.md)), is kept as released on 29 September 2026: it covers the **odd** degrees, which are the first 29 pieces of the same project.

## In one line

`EvenAll.mainTheorem'` in [`project/RequestProject/EvenAll/PartBC.lean`](project/RequestProject/EvenAll/PartBC.lean) compiles with no `sorry` and depends only on the axioms `propext`, `Classical.choice`, `Quot.sound`. For odd `m` it is `ColAssembly.mainTheorem'` of version 1; for even `m` it is the chain of pieces E1–E20.

## Read cold

Both certificates were read cold by a separate reader, working alone from a written mission, before release: [record/cold-readings/](../record/README.md), readings 13 (version 1) and 17 (version 2). The second reader ran Lean itself on the compiled project, compared the statements with the original of [DS], recounted every number of the certificate, and re-submitted to the Lean kernel every one of the 4 669 project declarations on which the final theorem and Theorem O depend, with a negative control. Its verdict: «holds as far as I can check»; its findings were about the wording and the numbers of the certificate, not about the proofs, and all are corrected in the certificate printed here (its §9).

## Where the evidence is

| What you want to see | File |
|---|---|
| The final theorem, its definitions and its axioms, as Lean prints them, after the clean rebuild | [even-degrees/logs/check_pares_postclean.log](even-degrees/logs/check_pares_postclean.log), produced by [even-degrees/checks/CheckPares.lean](even-degrees/checks/CheckPares.lean) |
| The final theorem in the source | [project/RequestProject/EvenAll/PartBC.lean](project/RequestProject/EvenAll/PartBC.lean) |
| Theorem O with equality | [project/RequestProject/OddEquality/](project/RequestProject/OddEquality/) (`D1`, `D2_DJ`, `D2_M`); statements in `check_pares_postclean.log` |
| The seventeen definitions behind Theorem O, as Lean prints them, and two consequences of the final theorem proved in the kernel | [even-degrees/logs/check_theoremO.log](even-degrees/logs/check_theoremO.log), produced by [even-degrees/checks/CheckTheoremO.lean](even-degrees/checks/CheckTheoremO.lean) |
| The kernel re-check of the compiled declarations, repeated by the author with the cold reader's files | [even-degrees/logs/sample_L5_kernelcheck.log](even-degrees/logs/sample_L5_kernelcheck.log), [even-degrees/logs/sample_L6_inductives.log](even-degrees/logs/sample_L6_inductives.log) |
| A rebuild from source, module by module in dependency order: 229 of 233 with exit code 0 (the other four are declared in the certificate, §2 item 4) | [even-degrees/logs/clean_rebuild_2026-10-03.log](even-degrees/logs/clean_rebuild_2026-10-03.log), by [even-degrees/logs/clean_rebuild_pares.sh](even-degrees/logs/clean_rebuild_pares.sh) over [even-degrees/logs/orden_modulos.txt](even-degrees/logs/orden_modulos.txt); one log per module in [even-degrees/logs/cr_logs/](even-degrees/logs/cr_logs/) |
| What the final theorem uses: 4 412 declarations in 180 of the 233 modules | [even-degrees/logs/deps_pares_postclean.log](even-degrees/logs/deps_pares_postclean.log), by [even-degrees/checks/DepsPares.lean](even-degrees/checks/DepsPares.lean) |
| The md5 of every source file | [even-degrees/logs/MANIFEST_md5_233.txt](even-degrees/logs/MANIFEST_md5_233.txt) |
| The twenty pieces E1–E20, exactly as sent to Aristotle | [even-degrees/pieces/](even-degrees/pieces/) |
| For each piece: the brute-force check run before sending it, with negative controls (`chkE<N>.py` and its log), and the Lean file that restates its main statements by hand (`CheckE<N>.lean`) | [even-degrees/checks/](even-degrees/checks/) |
| For each piece: the local build and the printed statements and axioms | [even-degrees/logs/](even-degrees/logs/) (`build_runE<N>.log`, `check_runE<N>.log`) |
| The same evidence for the 29 pieces of the odd degrees | [pieces/](pieces/), [checks/](checks/), [logs/](logs/), [AUDIT_LOG.md](AUDIT_LOG.md) |
| Aristotle's own account of its runs (its file covers the runs up to piece E13; its notes on the later runs were on its web page) | [project/ARISTOTLE_SUMMARY.md](project/ARISTOTLE_SUMMARY.md) |

**The twenty new pieces**, each with the paper statement it formalizes and its Lean folder (the main theorem names are in the certificate, §3):

| Piece | File | Paper (version 12) | Lean folder |
|---|---|---|---|
| E1 | [E01_q_any_bip.md](even-degrees/pieces/E01_q_any_bip.md) | §7 for every box `q ≥ 2`, and at `q = p^v` in characteristic `p` | [BipAny](project/RequestProject/BipAny/) |
| E2 | [E02_q_even_count.md](even-degrees/pieces/E02_q_even_count.md) | Lemma 9.1 and the upper bound for even `m` | [EvenCount](project/RequestProject/EvenCount/) |
| E3 | [E03_q_odd3.md](even-degrees/pieces/E03_q_odd3.md) | Theorem 8.15 (the odd box `r = 3`) | [Odd3](project/RequestProject/Odd3/) |
| E4 | [E04_q_pow2_leading.md](even-degrees/pieces/E04_q_pow2_leading.md) | Proposition 9.2 (degree `2^v`, leading forms) | [Pow2](project/RequestProject/Pow2/) |
| E5 | [E05_q_quartic_assembly.md](even-degrees/pieces/E05_q_quartic_assembly.md) | Main Theorem′ at `m = 4`; the assembly for even `m` under a hypothesis | [EvenAssembly](project/RequestProject/EvenAssembly/) |
| E6 | [E06_q_oddbox_shapes.md](even-degrees/pieces/E06_q_oddbox_shapes.md) | §8.1–§8.2: identities, shapes, options, the chain | [OddShapes](project/RequestProject/OddShapes/) |
| E7 | [E07_q_oddbox_layers.md](even-degrees/pieces/E07_q_oddbox_layers.md) | Lemmas 8.4 and 8.5 | [OddLayers](project/RequestProject/OddLayers/) |
| E8 | [E08_q_pfaffian.md](even-degrees/pieces/E08_q_pfaffian.md) | §8.3: Pfaffians and bordered Pfaffians over any commutative ring | [Pfaffian](project/RequestProject/Pfaffian/) |
| E9 | [E09_q_rank_two.md](even-degrees/pieces/E09_q_rank_two.md) | §8.5: Lemma 8.8 (rank-two update), Corollary 8.9 | [RankTwo](project/RequestProject/RankTwo/) |
| E10 | [E10_q_membership.md](even-degrees/pieces/E10_q_membership.md) | Lemmas 8.7′ and 8.7 | [Membership](project/RequestProject/Membership/) |
| E11 | [E11_q_oddbox_patterns.md](even-degrees/pieces/E11_q_oddbox_patterns.md) | Definition 8.6, the ideals `V_Λ` | [OddPatterns](project/RequestProject/OddPatterns/) |
| E12 | [E12_q_oddbox_lifts_1.md](even-degrees/pieces/E12_q_oddbox_lifts_1.md) | Proposition 8.10, the first five lifts | [OddLifts](project/RequestProject/OddLifts/) |
| E13 | [E13_q_oddbox_lifts_2.md](even-degrees/pieces/E13_q_oddbox_lifts_2.md) | Proposition 8.10, the last three lifts | [OddLifts2](project/RequestProject/OddLifts2/) |
| E14 | [E14_q_oddbox_theorem.md](even-degrees/pieces/E14_q_oddbox_theorem.md) | Proposition 8.10, Theorem 8.11, Theorem O `≥` | [OddTheorem](project/RequestProject/OddTheorem/) |
| E15 | [E15_q_oddbox_equality.md](even-degrees/pieces/E15_q_oddbox_equality.md) | Lemma 8.12 (the direction used), Corollary 8.13: Theorem O with equality, freeness | [OddEquality](project/RequestProject/OddEquality/) |
| E16 | [E16_q_even_blocks.md](even-degrees/pieces/E16_q_even_blocks.md) | Lemmas 9.4–9.5 | [EvenBlocks](project/RequestProject/EvenBlocks/) |
| E17 | [E17_q_even_count_colours.md](even-degrees/pieces/E17_q_even_count_colours.md) | Lemma 9.6 | [EvenColours](project/RequestProject/EvenColours/) |
| E18 | [E18_q_even_block_minus.md](even-degrees/pieces/E18_q_even_block_minus.md) | Lemmas 9.7–9.9 | [EvenMinus](project/RequestProject/EvenMinus/) |
| E19 | [E19_q_even_block_one.md](even-degrees/pieces/E19_q_even_block_one.md) | Lemma 9.10, Theorem 9.11 `≥` | [EvenOne](project/RequestProject/EvenOne/) |
| E20 | [E20_q_even_assembly.md](even-degrees/pieces/E20_q_even_assembly.md) | Theorem 9.11, Main Theorem′ for every `m`, Corollaries 7.8 and 9.12 | [EvenAll](project/RequestProject/EvenAll/) |

The pieces were written from version 11 of the paper, which was not made public; version 12 keeps its numbering for every result in this table except Lemma 8.7′, Lemma 8.8 and Corollary 8.9, which are new in version 12 (the certificate, §3, explains it).

## Contents

```
LEAN_CERTIFICATE_CHAISE_LONGUE_v2.pdf / .md   the certificate for every degree
LEAN_CERTIFICATE_CHAISE_LONGUE_v1.pdf / .md   the certificate for the odd degrees, as released on 29 September
project/                 the Lean project: RequestProject/ (233 files, 41,243 lines),
                         lakefile.toml, lean-toolchain, lake-manifest.json;
                         ARISTOTLE_SUMMARY.md is Aristotle's own account of its runs
pieces/, checks/, logs/, AUDIT_LOG.md      the evidence of the 29 pieces of the odd degrees
even-degrees/pieces/     the 20 pieces E1–E20
even-degrees/checks/     the brute-force checks run before sending them, and the Lean check files
even-degrees/logs/       the local builds and printed statements of each piece, the final checks,
                         the dependency cone, the clean rebuild (with one log per module), and the
                         md5 manifest of the 233 source files
```

In the certificate, the local folder names `CERTIFICADO_PARES/` and `checks/` are `even-degrees/logs/` and `even-degrees/checks/` here, and `proyecto_lean/` is `even-degrees/logs/` for the per-piece logs.

## How to check it

You need `elan` (the Lean toolchain manager) and about 7 GB of disk for Mathlib and its dependencies. From `project/`:

```
lake exe cache get
lake build RequestProject.EvenAll.PartBC RequestProject.EvenAll.PartD RequestProject.EvenAll.PartE RequestProject.OddEquality.PartD RequestProject.ColAssembly.Main
lake env lean ../even-degrees/checks/CheckPares.lean
```

The second command builds the five modules that `CheckPares.lean` imports, and everything they import: 216 of the 233 modules. On a machine with little memory, build the modules one at a time, as the author did. Or, for the final theorem alone, make a file `Check.lean` next to `lakefile.toml` with

```
import RequestProject.EvenAll.PartBC
#check @EvenAll.mainTheorem'
#print axioms EvenAll.mainTheorem'
```

and run `lake env lean Check.lean`.

## Who did what

The Lean proofs were written by **Aristotle** (Harmonic), one piece at a time, from pieces written from the paper by the author's team. Every returned module that holds a theorem was compiled again on the author's machine (the four exceptions are in the certificate, §2 item 4) and audited against the paper before the next piece was sent. Nothing was accepted on Aristotle's word: the Lean kernel checks every proof.

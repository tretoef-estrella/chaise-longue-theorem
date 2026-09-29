# The Chaise Longue Theorem in Lean 4

This folder holds a complete Lean 4 proof of **Main Theorem′** of the paper: for every odd `m` and every `k ≥ 0`, the group `Z[(Z/m)^{2k+1}]/(ψ_J : J)` of Degtyarev–Shimada is free abelian of rank `m^{2k+1} − Q_k(m)`. The dimension over every field is the same.

**Read first:** [LEAN_CERTIFICATE_CHAISE_LONGUE_v1.pdf](LEAN_CERTIFICATE_CHAISE_LONGUE_v1.pdf) ([Markdown](LEAN_CERTIFICATE_CHAISE_LONGUE_v1.md)). It gives:
- the theorem and its definitions exactly as Lean prints them;
- a line-by-line comparison with the paper;
- what is **not** formalized: the topology, [DS, Theorem 1.1(a)], which rests on Pham's theorem and [DS, Theorem 2.2];
- the trust base, the procedure, the data of every piece, and how to reproduce everything.

## In one line

`ColAssembly.mainTheorem'` in [`project/RequestProject/ColAssembly/Main.lean`](project/RequestProject/ColAssembly/Main.lean) compiles with no `sorry` and depends only on the axioms `propext`, `Classical.choice`, `Quot.sound`.

## Where the evidence is

| What you want to see | File |
|---|---|
| The final theorem and its definitions, as Lean prints them, and the axioms (lines 55–60) | [logs/check_run29.log](logs/check_run29.log), produced by [checks/Check29.lean](checks/Check29.lean) |
| The final theorem in the source | [project/RequestProject/ColAssembly/Main.lean](project/RequestProject/ColAssembly/Main.lean) |
| A rebuild from scratch, module by module in dependency order: 113 of 113 with exit code 0, 1 h 27 min | [logs/clean_rebuild_2026-09-29.log](logs/clean_rebuild_2026-09-29.log), by [checks/rebuild.sh](checks/rebuild.sh) over [checks/order.txt](checks/order.txt) |
| The full `lake build` after that rebuild: «Build completed successfully (8139 jobs)» | [logs/build_after_clean.log](logs/build_after_clean.log) |
| What the final theorem uses: 2,367 project declarations in 90 files | [logs/deps_mainTheorem.log](logs/deps_mainTheorem.log), by [checks/Deps29.lean](checks/Deps29.lean) |
| The build after each of the 29 runs | [logs/](logs/) (`build_run3.log` … `build_run29.log`) |
| The brute-force check run before each piece was sent, with its negative controls | [checks/](checks/) (`chkN.py`; `chkN.lean` prints the statements of run N) |
| The 29 pieces exactly as sent to Aristotle | [pieces/](pieces/) |
| The audit of every run: diff, forbidden-word search, build, statements, axioms | [AUDIT_LOG.md](AUDIT_LOG.md) |
| Aristotle's own account of each run | [project/ARISTOTLE_SUMMARY.md](project/ARISTOTLE_SUMMARY.md) |

## Contents

```
LEAN_CERTIFICATE_CHAISE_LONGUE_v1.pdf / .md   the certificate
project/                 the Lean project: RequestProject/ (113 files, 21,126 lines),
                         lakefile.toml, lean-toolchain, lake-manifest.json;
                         ARISTOTLE_SUMMARY.md is Aristotle's own account of every run
pieces/                  the 29 pieces sent to Aristotle, each written from the paper
checks/                  the brute-force scripts run before sending each piece, and the
                         Lean files used to print statements, axioms and dependencies
logs/                    every local build (build_run*.log), every check (check_run*.log),
                         the clean rebuild and the dependency cone of the final theorem
AUDIT_LOG.md             the audit of every run: diff, grep, build, statements, axioms
```

## How to check it

You need `elan` (the Lean toolchain manager) and about 7 GB of disk for Mathlib and its dependencies.

```
cd project
lake exe cache get
lake build
```

Then make a file `Check.lean` next to `lakefile.toml` with

```
import RequestProject.ColAssembly.Main
#check @ColAssembly.mainTheorem'
#print axioms ColAssembly.mainTheorem'
```

and run `lake env lean Check.lean`.

## Who did what

The Lean proofs were written by **Aristotle** (Harmonic), one piece at a time, from pieces written from the paper by the author's team. Every returned file was compiled again on the author's machine and audited against the paper before the next piece was sent. Nothing was accepted on Aristotle's word: the Lean kernel checks every proof.

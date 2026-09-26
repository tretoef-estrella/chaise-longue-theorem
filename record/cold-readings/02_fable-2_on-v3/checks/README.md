# checks/ — code and logs of the cold audit (FABLE_2)
All engines written from the paper's definitions; none reuses the authors' code. `*.log` = output of the matching script.
- `DS/` — [DS] arXiv:1405.4683v3 LaTeX source; `DS/de15/` — [De15] arXiv:1512.06199 source.
- `boxalg.py` — shared tools (matchings, D(a,b), box-ring polynomials, Q_k(q), |Γ_K| by enumeration).
- `sform.py` — (S) in the sum form, graded, F_3 (calibration `sform_calib.log`). `fact72.py` — Fact 7.2 (`fact72.log`).
- `dualform.py` — intersection form of Prop. 2.6, plain (`dualform_calib.log`, `run_k1.sh`/`run_k1.log`: (1,27),(1,81),(1,243)).
- `symdual.py` + `rank3.c` — intersection form split by the Klein group, exact, C streaming RREF over GF(3) (`symdual_calib.log`, `run_227.sh`/`run_227.log`: (2,27)).
- `symdualp.py` + `rankp.c` — same over GF(p) (`run_fp.sh`/`run_fp.log`: F_5, F_7 cells incl. (2,25)).
- `p2check.py` — Prop. 5.6 / Lemma 5.5 at q = 3, 9, 27, 81 (`p2check.log`).
- `downset.py` — Theorem 5.3 for every down-set: dim V_Λ, |Z_Λ|, slice inclusions, negative control (`downset_9_3/9_4/9_5/27_3/9_6.log`).
- `thm41.py` — Theorem 4.1 certificate and brute force (`thm41.log`).
- `thmA12.m2` — Theorem A.12 row inclusions and Remark A.14 control, Macaulay2 (`thmA12.log`).
- `literalDS.m2`, `literalDS5.m2` — the literal [DS] rings (ψ_J and ρ_J forms) over F_3, F_5, F_7; Cor. 6.1; Remark 6.3 (`literalDS.log`, `literalDS5.log`).
- `sagebench.py` — toolchain benchmark only.

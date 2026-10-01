# Theorem A and the centralizer of a principal nilpotent element

Engines and logs behind Remark 8.4 and §12.5 of version 9 of the paper, and behind the note [the-1-october-kostant-correction.md](../../record/audits/the-1-october-kostant-correction.md). All runs were made on 1 October 2026 inside the watchdog [tools/vigia.sh](../tools/vigia.sh); the largest used 260 MB.

Run the Python scripts from inside `regla_oro_gordo_2026-10-01/` (they read data from the sibling folder). They need only Python 3. The `.m2` files need Macaulay2; `frob_ver.sage` and the `.sage` files of the other folder need SageMath.

## `regla_puente_teoremaA_2026-10-01/` — the data
| File | What it is |
|---|---|
| `hf.m2`, `hf2.m2` → `hfall.log` | graded Hilbert functions of `F[x]/(e_odd, x_i^q)` at 24 cells, `q = 3, …, 15` |
| `traces.m2` → `traces.log` | the trace of every cycle type on every graded piece, over `Q`, at 10 cells (`q = 3, 5`; `n ≤ 6`) |
| `paridad.py` | the parity law: `Σ_d (−1)^d tr(σ | A_d) = #{x : σx = −x}` (56 of 56) |
| `gp.sage` → `gp.log`, `leftover.sage` → `left.log`, `orbitas*.py` → `orb.log`, `frob.sage` → `frob.log` | the first attempts: one piece for each kind of walk. They fail at `n = 6`, and are kept because the failure is what led to the right model |

## `regla_oro_gordo_2026-10-01/` — the checks
| File | What it checks | Result |
|---|---|---|
| `diccionario.m2` → `diccionario.log` | in characteristic 0, `(e_odd) + (x_i^q) = (p_1, p_3, …, p_{q−2}) + (x_i^q)`; in characteristics 3, 5, 7, the coefficients of `E(t)/E(−t) − 1` generate `(e_odd)` | 11 of 11 |
| `lusztig_B.py`; `hf_ext.m2` → `hf_ext.log`, `lusztig_B_ext.py` → `lusztig_B_ext.log` | the Hilbert series against Lusztig's `t`-analogues of type `B_m`, computed from the Weyl group and the `t`-partition function | 18 + 9 cells |
| `caracter_graduado.py` | the graded character of the symmetric group, by Adams operations | 56 of 56 |
| `lusztig_perfiles.py` | the same for every profile (weight) `μ`: the ideals `K_μ` of Appendix A | 133 of 133 |
| `tipoC.m2`, `tipoC_impar.m2`, `c84.m2`, `tipoC_p.m2` → logs | even `q`: dimensions in characteristics 0, 3, 5, 7 and 2 | equal in 0, 3, 5, 7; larger in 2 |
| `lusztig_C.py`, `lusztig_C_impar.py` | even `q` against Lusztig's analogues of type `C_m`, at the weight `0` (`n` even) or `ε_1` (`n` odd) | 8 + 8 |
| `rango.py`, `rango_par.py` | the statistic on walks reproduces the Hilbert series | 24 + 16 |
| `regla_explicita.py` | the explicit rule for the ranks agrees with the rule by counting | 3 605 profiles |
| `casillas_directo.py` → `casillas_directo.log` | the Hilbert function of the top-degree forms of the ideal of the walks ending at a weight `μ`, computed from the points, against the statistic | 18 of 18 |
| `estadistica_cerrada.py` | a closed form of the statistic: correct for `q = 3`, **wrong for `m ≥ 2`** (kept as a negative result) | 16 of 24 |
| `frob_ver.sage` | prints the graded Frobenius characters at `q = 3` | — |

The code is under the MIT licence ([LICENSE](../../LICENSE)).

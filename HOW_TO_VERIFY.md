# How to verify

**No step of the proof uses a computer.** The proof is in the [paper](paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) and can be checked with pencil and paper; [WHERE_TO_ATTACK.md](WHERE_TO_ATTACK.md) says where to press. The engines in this repository are corroboration: they test the statements of the proof, and its final numbers, on every case small enough to compute, and they carry negative controls that must fail when a hypothesis is removed. A proof that has never been confronted with data has not been tested.

Every engine here runs on a laptop. All the runs recorded in the logs were made on a MacBook Air (8 GB), inside a watchdog that kills any run above 1.2 GB of memory or ten minutes of time ([engines/tools/vigia.sh](engines/tools/vigia.sh)); the last line of each log reports the peak memory and the time.

## What you need

- **Python 3** with **NumPy**, for the `.py` engines.
- **[Singular](https://www.singular.uni-kl.de/)**, for the `.sing` scripts (`Singular -q file.sing`).
- **[Macaulay2](https://macaulay2.com/)**, for the `.m2` scripts (`M2 --script file.m2`).
- Optionally the watchdog, from the folder of the engine: `zsh ../../tools/vigia.sh my.log 'python3 engine.py args'` (for the engines two folders down).

## Five minutes: the conjecture itself, four ways

Run each command from the folder named above it. Each prints the number the paper predicts.

**1. The sum form (S) at $m = 3^v$** — `engines/v7-verification/theorem-b-and-translation/`
```
python3 regla268_sumform.py 2 3      # k=2, q=3   →  ranks=[5, 9, 5, 1] total=20 Q=20 DS-HOLDS
python3 regla268_sumform.py 1 9      # k=1, q=9   →  total=168 Q=168 DS-HOLDS
```
These are rows of the table of §12.1: $\dim (D_J : J \in \mathcal{J})\,C = Q_k(q)$, graded rank by graded rank.

**2. The literal ring of Degtyarev–Shimada, every characteristic** — `engines/v7-verification/main-theorem-prime/`
```
python3 gate_mainprime.py            # k=1, m = 3, 5, 7, 9, over F_2 and over primes dividing and not dividing m
                                     #   →  "dim quotient = m^3 − Q_1(m) … OK" in every line
```
This is Main Theorem′ at $k = 1$, computed from the generators $\psi_J$ of [DS] with no translation at all (§12.3).

**3. The ingredients of the proof, on every down-set** — `engines/v7-verification/theorem-b-and-translation/`
```
python3 regla270_gate1_downsets.py 9 5    # every down-set at q=9, m=5  →  P1fail=0 P2fail=0 P3fail=0
python3 regla269_p2.py                    # the chain and (P2) up to q = 81  →  chain_bad=0 … P2_bad=0
python3 regla270_gate2_dims.py 9 3        # dim V_Λ = |Z_Λ| for every down-set at q=9, m=3  →  fails=0
```

**4. Corollary W** — `engines/v7-verification/hodge-and-corollary-w/`
```
python3 regla281_gamma_Js.py         # |Γ_{J_s}| = Q_s(m)(m−1)^(d−s), DS Definition 1.3 literally  →  OK … FIN-OK
```

## The map: every number of §12, and the engine behind it

| Paper | What is checked | Engine (folder) | Log |
|---|---|---|---|
| §12.1 | (S) at $(k,q) = (1,3), \dots, (5,3), (1,9), (2,9), (1,27)$ | `regla268_sumform.py` (theorem-b-and-translation) | `logs/regla268_sumform_*.log` |
| §12.1 | (S) over $\mathbb{F}_p$ for $p = 3, 5, 7$ (about 2.5 min, 1 GB) | `regla274_S_primo_p.py` | `logs/regla274_S_primo_p.log` |
| §12.1 | (S) over fields whose characteristic is not attached to $q$ | `regla275_S_cualquier_cuerpo.py` | `logs/regla275_S_cualquier_cuerpo.log` |
| §12.1 | a third, independent engine for (S): a kernel basis per pair, exact ranks degree by degree | `regla270_sumform_kernelbasis.py` | `logs/regla270_sumform.log` |
| §12.1 | the literal ring of [DS] against (S), and the literal form at $(2,9)$: $5\,120$ | `regla264_ds.py` | `logs/regla264_*.log` |
| §12.2 | (P1), (P2), (P3) on **every** down-set, with the negative control that tightens (P3) and fires ($604$ failures at $(9,7)$) | `regla270_gate1_downsets.py` | `logs/regla270_gate1.log` |
| §12.2 | $\dim V_\Lambda = \lvert Z_\Lambda\rvert$ on every down-set | `regla270_gate2_dims.py` | `logs/regla270_gate2.log` |
| §12.2 | the chain and (P2) on every comparable pair, $q$ up to $81$ | `regla269_p2.py` | `logs/regla269_p2.log` |
| §12.2 | Theorem 5.9: the evaluation of $D$ and the support statement | `regla276_igualdad.py` | `logs/regla276_igualdad_v2.log` |
| §12.2 | Theorem 5.9′: equality in every characteristic, including $2$; the same graded ranks for $p = 2, 3, 5, 7, 10007$ | `regla278_igualdad_toda_car.py`, `regla278_grados.py` | `logs/regla278_*.log` |
| §4, Rem. 4.2(3) | $q = 3$ by the Specht modules: $6, 20, 70$ | `regla270_q3_specht.py` | — (runs in a second) |
| §12.2 | the Hodge characters: $\lvert\mathfrak{B}\rvert$ against the pair-type characters | `regla279_caracteres_hodge.py` (hodge-and-corollary-w) | `logs/regla279_caracteres_hodge.log` |
| §10.1 (H5) | Aoki's Theorem A, out of sample, with predictions sealed before the run | `regla280_aoki_gate.py` | `logs/regla280_aoki_gate.log` |
| §1.3 | the author's earlier machine verdicts [Rep] against Lemma 2.2 | `regla283_doberman_gate.py ../../../hodge-fermat-campaign/README.md` | `logs/regla283_doberman_gate.log` |
| §11 | Corollary W(ii) | `regla281_gamma_Js.py` | `logs/regla281_gamma_Js.log` |
| §12.3 | Main Theorem′ at $k = 1$ in the literal ring, every characteristic | `gate_mainprime.py` (main-theorem-prime) | `gate_mainprime.log` |
| §6 | the worked example $(k, m) = (1, 15)$: the colourings and the block products of Lemma 6.8 | `ejemplo_15.py` (main-theorem-prime) | `ejemplo_15.log` |
| §12.5, App. A | Theorem A: the bookkeeping of all $1\,673\,721$ objects, and $166$ exact certificates | `regla263_certs.py`, `regla263_gamma.py` (theorem-a) | `logs/regla263_*.log` |

### The degrees that are not prime powers (§12.3–§12.4)

Two engines, written separately.

**The auditor's (Singular)** — [`engines/composite-degrees-auditor/`](engines/composite-degrees-auditor/). Each `.sing` file is self-contained; its `.log` holds the output.

| Script | What it computes | Result |
|---|---|---|
| `col_15_3_2.sing`, `col_15_5_2.sing` | the Fermat fourfold of degree $15$, colouring by colouring, at $p = 3$ and $p = 5$ | $32\,900 = Q_2(15)$ at both primes |
| `col_21_3_2.sing`, `col_21_7_2.sing` | the Fermat fourfold of degree $21$, at $p = 3$ and $p = 7$ | $102\,800 = Q_2(21)$ at both primes |
| `col_15_*_1.sing`, `col_21_7_1.sing` | the same at $k = 1$ | $546$, $1\,140$ |
| `D_a_b_q.sing` | Theorem 7.6: $\dim V_\Lambda$ on every down-set of pairs of partitions at $(\alpha, \beta, q)$ | equality, $0$ failures (`gateD.log`, `gateD2.log`) |
| `bip0.sing`, `bip1.sing`, `bip2.sing` | Theorem C at the roots | the counts $N_{bal}$, $N_{ph}$ of `sellado.txt`, predicted before the runs |
| `lit_9_3_2.sing`, `lit_9_3_2_ctrl.sing` | the literal ring at $(k, m) = (2, 9)$, and the control subfamily of Fact 9.2 | $5\,120$, and $4\,730 < 4\,736$: the engine detects torsion when there is torsion |
| `W_5.sing`, `W_9.sing` | Corollary W(ii) in the literal ring | $144 = Q_1(5)\cdot 4$, $1\,344 = Q_1(9)\cdot 8$ |

**The constructor's (Python)** — [`engines/fable-composite-degrees/`](engines/fable-composite-degrees/), with its report `INFORME_1.md` and its full run record `run_logs.txt`.

### The Macaulay2 feasibility gates

[`engines/v7-verification/composite-degrees/`](engines/v7-verification/composite-degrees/): `regla279_compuesto.m2`, `regla279_fantasma.m2` and `regla279_m15_k2.m2` (`M2 --script …`), with logs.

## The laboratories of the constructors

The proofs were constructed by external Claude instances, each in its own folder, with its own engines. Their folders are reproduced whole (only process-id files and stale copies of the paper removed):

- [`engines/fable-chessboard/`](engines/fable-chessboard/) — the fifteen *Chessboard* missions (`MISION*.md`) and their reports (`INFORME*.md`), with every Singular, Macaulay2 and Python run behind them. `INFORME_14.md` is the construction of Theorem A for $q = 3^v$; `INFORME_15.md` is the first proof of the conjecture for $m = 3^v$.
- [`engines/fable-composite-degrees/`](engines/fable-composite-degrees/) — the construction of §6–§7.

These are working folders: the report of each mission says which file produced which number.

## The earlier campaign

The engines of the Hodge–Fermat campaign (C++, Python verifiers and logs), cited in the paper as [Rep], are in [`hodge-fermat-campaign/engines/`](hodge-fermat-campaign/engines/), [`hodge-fermat-campaign/verifiers/`](hodge-fermat-campaign/verifiers/) and [`hodge-fermat-campaign/logs/`](hodge-fermat-campaign/logs/); their use is explained in the [campaign README](hodge-fermat-campaign/README.md).

## Notes

- The script names (`regla264`, `regla270`, …) are the audit records they belong to in the [archive](archive/README.md); they have been kept so that every log can be traced back to the day it was run.
- Four copies were patched so that they run from this folder instead of from the author's machine; each patched line is marked `# repo copy`.
- If a run gives a different number, that discrepancy is more valuable to us than any agreement: please [open an issue](https://github.com/tretoef-estrella/chaise-longue-theorem/issues).

---

[README](README.md) · [Theorems](THEOREMS.md) · [Where to attack](WHERE_TO_ATTACK.md)

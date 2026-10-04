# Grading of the cold read of the Lean certificate (LEAN_1) — Grepy, 2026-09-30

**Reader:** external Claude, fresh session in `~/Desktop/CHASE LONGUE THEOREM/LECTORES_EN_FRIO/LEAN_1/`, prompt `VIVOS/MISIONES_TRAS_BARRIDO/PROMPT_LECTOR_LEAN_CHAISE_v1.md`. Report `REPORT.md` here (md5 b2c833a739a1ac2bd17153b296ba1118), scripts and logs in `checks/`.

**Verdict of the reader:** HOLDS AS FAR AS I CAN CHECK. 0 FATAL, 1 GAP (peripheral), 4 ERROR (bookkeeping), 7 PRESENTATION.

**Grade: HIGH MARK.** It did the main job, which nobody had done by machine: it chased `ColAssembly.mainTheorem'` down to Mathlib object by object against §1.2, §2 and the LaTeX of [DS]:
- `R`, `𝒥`, `t_0`, `φ`, `τ_J`, `ψ_J`, the ideal, `F[G]` and `Q_k(m)` all match;
- the `t_0` placeholder never enters.

It closed the vacuity traps with reasons: the quotient is finitely generated, `Q_k(m) ≤ (m−1)^{2k+1} < m^{2k+1}`, `m = 1` and `k = 0` are meaningful, and every field is covered. It swept the trust base, and it recounted every number of the certificate (both SHA-256 fingerprints included). It tested the Lean definitions numerically in 11 cells plus `(15,1)`, with Smith form over ℤ and negative controls.

Its first control did not fire, and the reader explained why: `(t_j − 1)φ` is a unit multiple of `(t_k − 1)φ` in `R`. That is good discipline.

## Findings, checked by the auditor
- **G-1 CONFIRMED** (`PAPER_OFICIAL_v8.md:875`). «Theorem 4.1 and Theorems 5.9 and 5.9′ were formalized too»: the graded-piece clause of 5.9′ (`:442`) is not formalized, as `AUDIT_LOG.md:209` already says. The certificate (`:144`) is accurate. The clause is off the claim and off the path of Main Theorem′. **Fix in the next paper version:** «Theorems 5.9 and 5.9′ (except the graded-piece clause of 5.9′)».
- **E-1 CONFIRMED** (the known §8 imprecision): check logs exist only for runs 26–29; `build.log` is the joint build of runs 1–2.
- **E-2 CONFIRMED in substance** (`cert:241`). The *tactic* `decide` is in 3 files. The token `decide` is in 11 files by my own count (word boundary, comments included), which is where the certificate's 11 comes from; the wording «tactic» is what is wrong.
- **E-3, E-4, P-1 … P-7:** bookkeeping and wording. E-4 (the certificate is keyed to paper v7) and P-2 (tP, tU, gaIdeal are paraphrased, not `#print`ed) are the most useful.
- **Suggestions worth keeping:**
  - an independent `lake build` plus `lean4checker` (the only way to remove the trust in our logs);
  - `Module.Finite` and `Qk < m^{2k+1}` as Lean lemmas, so that non-vacuity is syntactic;
  - `#print` of the three missing definitions;
  - a Lean definition of `Γ_𝒥` exactly as [DS] Def. 1.3;
  - hashes of all 29 pieces;
  - an `example` tying the definitions to the number 6 / 21 of §2.6.

## Decision (Rafa, 2026-09-30: «si de Lean no hay novedad ninguna, no cambiamos nada en github ni en ningún sitio, pero lo registras»)
There is no novelty about the Lean proof: the statement is Main Theorem′ and the trust base is clean. G-1 is an overstatement in the **paper**, about a clause off the path. **Nothing is changed now on GitHub, Zenodo or ORCID.** Everything goes to `LISTA_DE_PENDIENTES.md` §XIV, for the next revision, when there is one: certificate v1.1 and paper v9.

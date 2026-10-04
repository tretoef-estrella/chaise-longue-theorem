VERDICT: HOLDS AS FAR AS I CAN CHECK — the Lean statement of `ColAssembly.mainTheorem'` is Main Theorem′ (more generally stated), non-vacuous, with a clean trust base in the sources and every certificate number reproduced; not rebuilt, so kernel acceptance rests on the authors' logs.

# REPORT — Cold reader of the Lean certificate (LEAN_1)

## 1. VERDICT

VERDICT: HOLDS AS FAR AS I CAN CHECK — I chased `ColAssembly.mainTheorem'` from the printed statement and the source down to Mathlib, compared every definition with §1.2 and §2 of the paper and with the LaTeX of [DS], looked for vacuity and trust-base holes, recounted every number of the certificate from the files, and tested the statement numerically from the Lean definitions; I found nothing that allows a rejection of the audited claim.

- **The statement is Main Theorem′.** `R`, `𝒥`, `t_a`, `φ`, `τ_J`, `ψ_J`, the ideal, `F[G]`, `ψ̄_J` and `Q_k(m)` are the paper's and [DS]'s objects, with the same signs and index ranges (STEP 1). It is stated more generally (odd `m ≥ 1`, `k ≥ 0`, every field), and it implies Main Theorem′ exactly as §1.2 states it (STEP 7).
- **It is not vacuous.** `R/I_ℤ` is finitely generated and `m^{2k+1} − Q_k(m) ≥ 1`, so `Free ∧ finrank = r` means `≅ ℤ^r`. The truncated subtraction never truncates. The edge cases `m = 1` and `k = 0` are correct and meaningful. «Every field» includes characteristic 2 and the primes dividing `m` (STEP 2).
- **The trust base is clean in the sources.** There is no `sorry`, `admit`, axiom, `native_decide`, `implemented_by`/`extern`, `unsafe`, `opaque`, custom syntax/macro/elaborator, instance hijack or name capture. The only axioms printed are `propext`, `Classical.choice`, `Quot.sound` (STEP 3).
- **The numbers hold.** 113 files, 21 126 lines, 937 theorems, both SHA-256 fingerprints, 28 build logs (4 108.7 s), the clean rebuild (113/113, rc = 0, 5 214 s), and the cone (2 367 declarations, 90 files, 26 folders) all match (STEP 4).
- **Findings.** 0 FATAL. 1 GAP, which is peripheral: part of Theorem 5.9′ that the paper calls formalized is not. It is off the claim and off the path. There are 4 ERRORs (bookkeeping) and 7 PRESENTATION items. See §3.
- **Condition.** I did not rebuild. That the kernel accepted exactly these files rests on the authors' logs (§4).

## 2. WHAT I CHECKED

### STEP 1 — The final statement chased to the bottom — STATE: CLOSED

Sources read: `material/lean/logs/check_run29.log` (lines 8–14, 27–54), `project/RequestProject/ColAssembly/Main.lean` (l. 99–104), `ColAssembly/BasisZ.lean` (l. 32–43), `ColUpper/Integral.lean` (l. 34–41), `ColUpper/Defs.lean` (l. 34–47), `ColSplit/Basic.lean` (l. 67–71), `ColSurv/Defs.lean` (l. 36), `Ballot/Defs.lean` (l. 45), `TheoremB/Defs.lean` (l. 59–63); paper v8 §1.1, §1.2, §2 (l. 26–48, 137–140); [DS] LaTeX l. 238–260 (𝒥), 318–327 (φ, τ_J, ψ_J), 331–336 (R), 450–458 (Def. 1.3), 1505–1545 (Claim 4.3).

The printed statement in the log is identical to the source (`Main.lean:99–103`). Object by object:

| Object | Paper / [DS] | Lean | Verdict |
|---|---|---|---|
| `G`, `R` | `R = Z[t_1..t_{2k+1}]/(t_i^m − 1)` (paper l. 46, 137; DS l. 331–333) | `RZ (2k+1) m = MvPolynomial (Fin (2k+1)) ℤ ⧸ span{X_i^m − 1}` (`BasisZ.lean:32–36`) | same; index shift `t_a = X_{a−1}` |
| `𝒥` | partitions of `{0..2k+1}` into pairs, `j_i<k_i`, `j_0<…<j_k` (DS l. 245–252) | `Matching k = {J : Fin(2k+2) → Fin(2k+2) // ∀x, J x ≠ x ∧ J (J x) = x}` (`Ballot/Defs.lean:45`) | bijection: fixed-point-free involutions ↔ perfect matchings; the ordered-list normal form of DS is a canonical representative, so `Set.range` over `Matching k` gives exactly the same generator set |
| `t_a` | `t_1..t_{2k+1}`; `t_0 = (t_1⋯t_{2k+1})^{-1}` never enters (paper l. 137) | `tP R k = Fin.cases 0 X` (`Integral.lean:34`), `tU` idem in `GA` (`Defs.lean:34`) | `t_0` placeholder `0`; it never enters: first product runs over `J a` with `J a > a ≥ 0` so `J a ≠ 0`; second over `a > 0`, `J a > a > 0` |
| `φ` | `φ(u) = u^{m−1}+⋯+1` (DS l. 318) | `phi m u = Σ_{s<m} u^s` (`ColSurv/Defs.lean:36`) | identical |
| `τ_J` | `Π_{i=0}^{d} (t_{k_i} − 1)` (DS l. 325) | `Π_{a : a < J a} (tP (J a) − 1)` | the pairs are `{a, J a}` with `a < J a`, i.e. `(j_i, k_i)`; one factor `t_{k_i} − 1` per pair: identical |
| `ψ_J` | `τ_J · Π_{i=1}^{d} φ(t_{j_i} t_{k_i})` (DS l. 326) | `· Π_{a : 0 < a ∧ a < J a} φ(tP a · tP (J a))` | `i ≥ 1` ⇔ `j_i ≠ 0` ⇔ `a > 0`: identical (sign and orientation included) |
| ideal | `(ψ_J : J ∈ 𝒥) ⊆ R` | `IZ m k = Ideal.span (range (mk ∘ psiP ℤ m))` (`BasisZ.lean:41–43`) | identical |
| `F[G]`, `ψ̄_J` | `F_p[t]/(t_i^m − 1)`, image of `ψ_J` | `GA F (2k+1) m`, `psiG F m J` (same formula with `tU`), `IK F m k = span (range psiG)` | identical formula; `map_psiP` (`Integral.lean:47`) shows the formula commutes with ring maps |
| `Q_k(m)` | `N!·[x^N] I_0(2x)^{(m−1)/2}`, `N = 2k+2` (paper l. 38) | `Σ_{b : Fin((m−1)/2) → range(2k+3), 2Σb = 2k+2} (2k+2)! / Π (b_u!)^2` (`TheoremB/Defs.lean:59–62`) | expanding `Π_u Σ_b x^{2b}/(b!)^2` gives exactly this sum; each summand is the multinomial `N!/(b_1!b_1!⋯b_h!b_h!)`, an integer, so `ℕ`-division is exact; the cap `b_u ≤ 2k+2` loses nothing. Checked numerically in STEP 4 (`checks/s4_math.py`) |
| «free abelian of rank r» | | `Module.Free ℤ M ∧ Module.finrank ℤ M = r` | see STEP 2 (non-vacuity) |
| «dim_F» | | `Module.finrank F (GA F ⧸ IK)`; the `F`-module structure is the quotient-algebra one | `GA` is finite-dimensional (`ColSplit/Main.lean:67`, `finite_GA`), so `finrank` is the true dimension |

I found no mismatch of object, sign, orientation or index range between the Lean statement, the paper (§1.2, §2) and the LaTeX of [DS].


### STEP 2 — Vacuity and Mathlib traps — STATE: CLOSED

- **`Module.finrank` = 0 on non-finite modules.** The integral part states `Module.Free ℤ M ∧ Module.finrank ℤ M = r` with `r = m^{2k+1} − Q_k(m)`. It cannot hold vacuously: (1) `M = R/I_ℤ` is a quotient of `R`, which is finitely generated over ℤ (monomials `t^ν`, `ν_i < m`; `BasisZ.lean`, `span_monoRZ`), so `M` is finitely generated whatever the ideal is, and `finrank` is its true rank; (2) moreover `r ≥ 1` in every case: a closed `(2k+2)`-tuple is determined by its first `2k+1` entries, so `Q_k(m) ≤ (m−1)^{2k+1} < m^{2k+1}` (checked numerically for all odd `m < 100`, `k ≤ 8` in `checks/s5_math.py` (c)), so `finrank = r ≥ 1` already forces a finite basis. With `Module.Free ℤ`, the statement is exactly `M ≅ ℤ^r`. `Module.Free` is stated over `ℤ`, the right ring; the `ℤ`-module structure on an additive group is unique, so there is no instance ambiguity.
- **Field part.** `GA F d m` is finite-dimensional for `m ≥ 1` (`ColSplit/Main.lean:67`, `finite_GA`), so `Module.finrank F (GA ⧸ IK)` is the true dimension.
- **Truncated subtraction.** `m ^ (2k+1) − Qk k m` is in `ℕ`. It never truncates: `Q_k(m) < m^{2k+1}` (above); inside Lean the inequality `Qk ≤ m^{2k+1}` also follows from the proved `finrank_IK_eq` (`dim I_F = Qk`) and `finrank_GA` (`dim GA = m^{2k+1}`).
- **Edge cases.** `m = 1`: `Fin ((1−1)/2) = Fin 0`, the only `b` is the empty function, `2·0 ≠ 2k+2`, so `Qk k 1 = 0`; `R = ℤ` (`t_i = 1`), every `ψ_J` contains a factor `t_{J 0} − 1 = 0`, the ideal is `0`, and `R/I = ℤ` of rank `1 = 1^{2k+1} − 0`: true and meaningful (brute force: `checks/s5_math.py` (d), cells `(1,0),(1,1),(1,2)`). `k = 0`: one matching `{0,1}`, `ψ = t_1 − 1`, `R/I = ℤ`, rank `1 = m − Q_0(m) = m − (m−1)`: this is the trivial case of the paper (§1.2, l. 44). Both are consistent with the paper; neither weakens the statement for `m ≥ 3`, `k ≥ 1`.
- **Hypotheses and types.** The only hypothesis is `Odd m` (`m : ℕ`), satisfiable (e.g. `m = 3`) and it excludes `m = 0`. `BallotBound.Matching k` is non-empty for every `k`. No hypothesis of `mainTheorem'` carries a structure (`ColSetting`, roots of unity, characteristic): those appear only inside the proof (`prop69`, `card_Gamma`), where they are discharged by constructing them (e.g. over `AlgebraicClosure (ZMod p)`, `ColAssembly/EveryField.lean:81–101`).
- **«Every field».** `∀ (F : Type) [Field F]` in the combined theorem; `mainTheorem'_field` has `F : Type u_1` (every universe). No characteristic hypothesis: char `0`, char `2`, and char `p | m` are all included; the proof splits on the characteristic (`EveryField.lean:95–101`). The paper's `F_p` is `ZMod p` with `Fact p.Prime`.
- **`Q_k(m)` and its identifications.** `TheoremB.Qk` is literally the formula of §1.2 (STEP 1). `TheoremB.card_closedTuples` (`TheoremB/Main.lean:67`): for every point set `S : FibreSetting T ((q−1)/2)` (a fixed-point-free involution on `T`, `|T| = 2h`), `#closed tuples in T^{2k+2} = Qk k q` — this is Lemma 2.2 (second sentence). `ColUpper.card_Gamma` (`ColUpper/Points.lean:286`): for a field `K` with `X^m − 1 = Π_{ξ∈μ_m}(X − ξ)`, `m ≠ 0` in `K`, `m` odd, `|Γ| = Qk k m`, where Lean's `Γ` is `{a ∈ μ_m^d : ev_a(ψ_J) ≠ 0 for some J}` (`ColUpper/Count.lean:215`) — **not literally** [DS, Def. 1.3]; see finding P-3. `evR_psiG_ne_zero_iff` (`Points.lean:120`) proves the pointwise criterion (`a_{J x} ≠ 1` for each pair, `a_x a_{J x} = 1` for the pairs avoiding `0`), from which Def. 1.3 follows by one line (for `i ≥ 1`, `a_{j_i} = a_{k_i}^{-1} ≠ 1`). Numerically, `|Γ_𝒥|` of Def. 1.3 = `Qk` in 11 cells, including `(15,1)` and `(3,3)` (`checks/s5_math.py` (b)). None of these lemmas is needed for the meaning of `mainTheorem'`, since `Qk` is defined by the explicit formula.

### STEP 3 — Trust base — STATE: CLOSED

Script `checks/s3_trustbase.py`, log `checks/s3_trustbase.log` (comments stripped before searching).
- **0 hits** in the 113 files for: `sorry`, `admit`, `axiom` declarations, `native_decide`, `implemented_by`, `extern`, `unsafe`, `opaque`, `@[csimp]`, `debug.skipKernelTC`, `ofReduceBool`, `partial def`, `elab`/`elab_rules`, `macro`/`macro_rules`, `syntax`, `notation`/`infix`/`prefix`/`postfix`, `run_cmd`/`#eval`/`#exit`, `import Lean`, `set_option debug.*`, kernel/environment API, `attribute [-instance]`, `unsafeCast`/`panic!`/`dbg_trace`. Imports: only `Mathlib` and `RequestProject.*`.
- **`decide`**: the tactic occurs in 3 files (`Chain/Checks.lean`, `Monotone/Checks.lean`, `TheoremB/Checks.lean`, including one `decide +kernel` at `Chain/Checks.lean:65`); `decide (…)` as a Boolean function occurs in 7 more files. None of the three `Checks.lean` files is in the dependency cone of `mainTheorem'` (STEP 4). `decide +kernel` adds no axiom (unlike `native_decide`).
- **Options**: 41 files set only `synthInstance.maxHeartbeats 200000`; every other option (`maxHeartbeats 8000000`, `maxRecDepth 4000`, `synthInstance.maxHeartbeats 20000`, `synthInstance.maxSize 128`, `autoImplicit false`, `relaxedAutoImplicit false`, `grind.warning false`, six `pp.*`) is set only in the top-level `RequestProject/Main.lean:12–27` (piece 1), which is outside the cone; file-level `set_option` is not exported. None affects soundness.
- **Instances**: 13 project instances, all `Module.Finite`, `Finite`, `DecidablePred`, `Nontrivial`, or the standard `Semiring.toModule` / `Ideal.Quotient.commRing` / `Ideal.Quotient.algebra` re-declared for the local types `Alg` and `Peel.C`. None is on `MvPolynomial`, `Ideal`, `HasQuotient`, `ℤ` or `Field`, so none can change the meaning of `⧸`, `Module.Free` or `Module.finrank` in the final statement.
- **Name capture**: `Check29.lean` prints with `open ColAssembly`, so a project declaration named e.g. `ColAssembly.Module.finrank` would print as `Module.finrank`. No project declaration ends with any standard name used in the statement (`Module.Free`, `Module.finrank`, `Odd`, `Field`, `Ideal.span`, `Set.range`, `Finset.range`, `Fintype.piFinset`, `Nat.factorial`, `X`, `Fin.cases`, …); the only near-hit is `ColComp.IsReps.cases`, harmless. All project declarations live in 24 project namespaces.
- **Toolchain**: `lean-toolchain` = `leanprover/lean4:v4.28.0`; `lakefile.toml` requires `mathlib` at `rev = "v4.28.0"` and sets no `leanOptions`/`moreLeanArgs`; `lake-manifest.json` pins mathlib `8f9d9cff6bd728b17a24e163c9402775d9e6a365` (inputRev `v4.28.0`) and the usual transitive packages (plausible, LeanSearchClient, importGraph, proofwidgets v0.0.87, aesop, Qq, batteries, Cli v4.28.0). I did not (and could not, offline) verify that this commit is the `v4.28.0` tag of Mathlib.
- **Axiom lines**: `check_run26–29.log` contain 10 + 3 + 7 + 6 `#print axioms` lines, all exactly `[propext, Classical.choice, Quot.sound]`; for `mainTheorem'`: `check_run29.log:57`. No line mentions `sorryAx`.

### STEP 4 — The certificate against the evidence — STATE: CLOSED

Script `checks/s4_counts.py`, log `checks/s4_counts.log`. All recounted from the files present:
- 113 files ✔; 21 126 lines (newline count) ✔; 937 `theorem`/`lemma` at the start of a line ✔ (957 if indented/attributed/`private` ones are counted); 351 definitions ✔ (only if `noncomputable`/`@[…]`-prefixed lines are counted; the certificate's parenthesis says «`def`, `abbrev`, …» without saying so — harmless).
- Per-folder files/lines/theorems of certificate §6: 29 rows, 0 mismatches.
- Fingerprints of §8: both SHA-256 values reproduced exactly (`7d26fa1c…57498`, `81fdc844…45f94`). So the `project/` I audited is the one the certificate describes.
- Build logs: `build.log` (runs 1–2) and `build_run3…29.log` all present, all «Build completed successfully», no `error` line. Sum of the 28 wall-clock times 4 108.7 s ✔; largest 270.32 s (run 8) ✔; largest RSS 2.58 GB (run 15) ✔; every «Build (s)» and «Peak RSS» of §6 matches its log.
- Check logs exist only for runs 26–29 (the known imprecision of certificate §8, l. 382: confirmed). Earlier statements and axioms exist only as transcriptions in `AUDIT_LOG.md`.
- Clean rebuild: 113 module lines, 113 with `rc=0`, `START 18:41:27`, `END 20:08:22` (1 h 26 min 55 s), sum of `sec` = 5 214, slowest `TheoremB.Root` 117 s ✔; `order.txt` = exactly the 113 modules and respects every `import` ✔; `build_after_clean.log` ends «Build completed successfully (8139 jobs)» ✔. Note: the per-module `lakepeak` column is the peak of the `lake` process (~280 MB), not of the Lean compiler.
- Dependency cone: `deps_mainTheorem.log` header `2367; modules: 90`, 90 module lines summing to 2 367, in 26 folders ✔; folders outside: `Degeneration`, `Support`, `Upper` ✔. The 23 modules outside the cone are listed in `checks/s7_cone_and_auditlog.log` (a); see finding E-3. The axiom sets transcribed in `AUDIT_LOG.md` for runs 2–29 are all `[propext, Classical.choice, Quot.sound]`, plus `[propext, Quot.sound]` for `ColTensor.lemma64_v` (run 23), as `cert:248` says; for the pilot (run 1) the log records only Aristotle's report, and run 2's local `#print axioms` covers piece 1's `finrank_V_ge` (`checks/s7_cone_and_auditlog.log` (b); `audit:38, 72`; `AUDIT_LOG.md` records that the pilot was not compiled locally, `audit:45`).

### STEP 5 — Independent numerical sanity check of the Lean statement — STATE: CLOSED

Written from the Lean definitions, not from the authors' scripts (which I did not run). `checks/s5_math.py` (log `checks/s5_math.log`; earlier runs `s5_math_run1_timeout.log`, `s5_math_run2.log` kept) and `checks/s5b_m15.py` (log `checks/s5b_m15.log`).
- `TheoremB.Qk` transcribed literally (with `ℕ` floor division, asserting every division exact) equals `N!·[x^N] I_0(2x)^h` computed with exact rationals, reproduces all 40 entries of the paper's table in §3 (rows 25 and 27 via the generating function), the polynomials `Q_0 … Q_3` of §3 for all odd `q ≤ 39`, `Q_k(3) = C(2k+2,k+1)`, the values of `TheoremB/Checks.lean`, and `Q_k(1) = 0`.
- `|Γ_𝒥|` of [DS, Def. 1.3], by brute force over exponent vectors, equals `Qk` in 11 cells: `(m,k) = (3,0),(5,0),(3,1),(5,1),(7,1),(9,1),(15,1),(3,2),(5,2),(9,2),(3,3)`.
- `R/(ψ_J)` built from the formula of `psiP` (all translates `t^ν ψ_J`): the dimension of the ideal over `F_2, F_3, F_5, F_7, F_11, F_13` and `F_2147483629` equals `Qk` in the cells `(1,0),(1,1),(1,2),(3,0),(5,0),(7,0),(3,1),(5,1),(7,1),(9,1),(3,2)`, and at the composite degree `(15,1)` over `F_2, F_3, F_5, F_7, F_2147483629` (546 each). Exact Smith normal form over ℤ in every cell with `m^{2k+1} ≤ 343`: all elementary divisors are `1`, so `ℤ^n/L` is free of rank `m^{2k+1} − Q_k(m)` (21, 89, 253, 223, and 1 at `m = 1` or `k = 0`).
- Negative controls: `φ(u) → u + 1` changes the dimension in all 4 cells tested; `t − 1 → t + 1` in `τ_J` gives `19, 61, 127` at `(3,1),(5,1),(7,1)` instead of `6, 36, 90` (the same numbers as the authors' control in `q_col_upper.md`; at `(3,1)`, rank `19 + 1 = 20`, as §12.6 of the paper says). My first control (replacing `t_{k_i} − 1` by `t_{j_i} − 1` for `i ≥ 1`) did **not** change anything, and should not: in `R`, `u·φ(u) = φ(u)` for `u = t_j t_k`, so `(t_j − 1)φ = −t_k^{-1}(t_k − 1)φ`, a unit multiple. It is kept in the script as an equivalence check. The consequence for the audit: the choice of «larger index» in `τ_J` (which Lean and [DS] share anyway) is immaterial to the ideal.

This does not prove anything for general `(m,k)`; it shows the Lean statement is true and non-trivial where it can be computed, with the Lean definitions, including the degenerate cases.

### STEP 6 — Pieces ↔ Lean — STATE: CLOSED (for the four pieces chosen)

Pieces checked: 10 `q_theorem_B_lower.md`, 14 `q_free_Z.md`, 28 `q_col_upper.md`, 29 `q_col_assembly.md`; sources, `AUDIT_LOG.md` (runs 10, 14, 28, 29), `check_run28.log`, `check_run29.log`.
- **Piece 29.** Proposition 6.9 (`p ≠ 2`, `r` odd, Setting of `q_col_splitting.md` ⟹ `dim_F I_F = Q_k(m)`) = `ColAssembly.prop69` (`check_run29.log:1–2`); the Setting is the structure `ColSplit.ColSetting` (`ColSplit/Basic.lean:24–50`: `p` prime, `CharP F p`, `v ≥ 1`, `r ≥ 1`, `μ` with `|μ| = r`, `X^r − 1 = Π_{ζ∈μ}(X − ζ)`), `m := p^v·r` — faithful (the condition `p ∤ r` is implied by the factorization into `r` distinct linear factors). «Theorem (every field)» = `theorem_every_field` (l. 3–7). «Main Theorem′» = `mainTheorem'` (l. 8–14), including `m ≥ 1` odd, every `k`, every field. Faithful.
- **Piece 28.** (0) `finrank_GA` (`0 < m`); (i) `exists_intMat`; (ii) `finrank_IK_eq_card_Gamma` (drops the hypotheses `|μ_m| = m`, `m ≠ 0`: more general); (iii) `card_Gamma` (`m ≠ 0` in `K`, `m` odd); (iv) `finrank_IK_le` for every field and odd `m` (piece: `m ≥ 3` odd), `finrank_IK_eq_of_charZero`, `rankOver_rat_intMatU`, `theorem_iv`. The `Γ` of the piece is literally `{a ∈ μ_m^d : ev_a(ψ_J) ≠ 0 for some J}` and so is Lean's. Faithful; every change is a generalization.
- **Piece 10.** `Qk` of the piece (l. 15) = Lean `Qk` (with the harmless cap `b_u ≤ 2k+2`); (ii) `card_closedTuples` for every `FibreSetting` (`neg` fixed-point-free involution, `h ≥ 1`, `|T| = 2h`); (iii) `card_Gamma'`; (iv) `finrank_DIdeal_ge` for every field, odd `q ≥ 3`, every `k`. Faithful.
- **Piece 14.** Lemma (integer matrices) = `FreeZ.quotient_free_of_finrank_image` (`FreeZ/Lemma.lean:56–66`, and the literal `ℤ^n` version l. 129): hypothesis «for every prime `p`, `dim_{F_p}` of the span of the image of `L` = `dim_ℚ` of the span of `L`», conclusion `Module.Free ℤ (ℤ^ι/L) ∧ finrank = |ι| − r`. Faithful; this is the lemma the final theorem uses.
- **Pieces as sent.** The md5 of the published `q_col_count.md`, `q_col_upper.md`, `q_col_assembly.md` match the prefixes recorded in `AUDIT_LOG.md:328, 337, 347` (`checks/s6_pieces_md5.log`). For pieces 1–26 the log records no md5 of the piece, so «exactly as sent» cannot be checked for them.

### STEP 7 — Paper ↔ Lean, and the honesty of §12.8 — STATE: CLOSED

- **Implication.** Main Theorem′ of the paper (§1.2, l. 48): `m ≥ 3` odd, `k ≥ 1`, `R/(ψ_J)` free of rank `m^{2k+1} − Q_k(m)`; «equivalently» `dim_{F_p} F_p[G]/(ψ̄_J) = m^{2k+1} − Q_k(m)` for every prime `p`. Specializing `mainTheorem'` to `m ≥ 3`, `k ≥ 1` gives the first sentence; taking `F = ZMod p` gives the second. Lean proves both sentences separately, so the «equivalently» is not needed. The Lean theorem implies Main Theorem′ exactly as stated.
- **Certificate §1.3.** Correct row by row (I re-derived each row in STEP 1). Incomplete in two small ways: the definitions `tP`, `tU`, `gaIdeal` are not «printed by `#print` in the same log» but paraphrased (P-2); and the claim «`Q_k(m) = |Γ| ≤ (m−1)^{2k+1}`» used for `r ≥ 1` is an informal argument, not a Lean lemma (true: STEP 2 and `s5_math.py` (c)).
- **§12.8 of the paper.** Honest about the main point: the topology (Theorem 0(a), (c), (d)) is not formalized, and the Main Theorem is machine-checked only in its algebraic form; §2 of the certificate says the same. Imprecisions: G-1 (Theorem 5.9′ graded clause), E-3 (list of unused files), P-3 (`|Γ_𝒥|`), P-4 («from scratch»).

### STEP 8 — Where I had to trust the authors — STATE: CLOSED

1. That the logs in `logs/` were produced by the Lean kernel from exactly these sources: no log contains a hash of the sources; the fingerprints of §8 are in the certificate only. (My own recount shows the sources are the ones the certificate describes.)
2. That `check_run29.log` was produced by `checks/Check29.lean` against this project and a build of it (its content is consistent with the sources).
3. That Mathlib commit `8f9d9cff…` is the tag `v4.28.0` and that the downloaded Mathlib `.olean` cache (`lake exe cache get`) is genuine: it was not rebuilt locally (certificate §8, «Mathlib untouched»). This is the standard Mathlib trust assumption, but it is an assumption.
4. The tarball md5s, download times, the diffs showing that old files were never changed (the tarballs and `run*/` folders are not in the material), and Aristotle's register «137 PROVED, 0 NEGATED» (web page, not exported).
5. The md5 of pieces 1–26 as sent (not recorded).
6. The authors' brute-force scripts in `material/lean/checks/` (I read none in detail and ran none; STEP 5 is my own).
7. Paper v8 vs v7: the certificate is written against v7 (DOI 22961151); I compared against the v8 in the material, whose §1.8 (`paper:107`) says no statement changed. The DOI of v8 quoted in the mission (23045409) appears nowhere in the material; I did not look it up (forbidden).

## 3. FINDINGS

Paths: `cert` = `material/lean/LEAN_CERTIFICATE_CHAISE_LONGUE_v1.md`, `paper` = `material/PAPER_OFICIAL_v8.md`, `audit` = `material/lean/AUDIT_LOG.md`, sources under `material/lean/project/RequestProject/`.

### FATAL
None. The Lean statement states Main Theorem′ (in a slightly more general form: odd `m ≥ 1`, `k ≥ 0`, every field), every definition matches the paper and [DS] (STEP 1), nothing in it is vacuous (STEP 2), and the trust base shows no `sorry`, axiom or kernel bypass in the sources (STEP 3); the axiom line of `mainTheorem'` is `[propext, Classical.choice, Quot.sound]` (`logs/check_run29.log:57`).

### GAP
- **G-1 (peripheral: not part of the audited claim, not on the path of `mainTheorem'`).** `paper:875` says «Theorem 4.1 and Theorems 5.9 and 5.9′ were formalized too». Theorem 5.9′ (`paper:442`) also asserts that «each of its graded pieces is free, and the dimension over `F` of each graded piece of `V_Λ` does not depend on `F`»; the authors' own audit says «(the graded-piece clause is not formalized)» (`audit:209`). So part of a statement described as formalized is not. The certificate is accurate here (`cert:144` lists only «equality over every field, freeness of `C/V_Λ` over `Z`»). The `Support`, `EveryField` (except `Rank.lean`) and `FreeZ` (except `Lemma.lean`) files that carry Theorems 5.9/5.9′ are outside the cone of `mainTheorem'`, so this does not touch Main Theorem′. I did not check whether Theorem 4.1 is formalized in full.

### ERROR
- **E-1 (known, confirmed).** `cert:382` «`build_run*.log`, `check_run*.log`: every build and every check»: `check_run*.log` exist only for runs 26–29 (`logs/`); earlier statements/axioms survive only as transcriptions in `audit`. Run 1 has no build of its own: `logs/build.log` is the joint build of runs 1–2 (212.39 s, as in `cert:298`).
- **E-2.** `cert:241` «Tactic `decide` occurs in 11 files». Recount (`checks/s3_trustbase.log`): the tactic `decide` occurs in 3 files (`Chain/Checks.lean`, `Monotone/Checks.lean`, `TheoremB/Checks.lean`); the token `decide` occurs in 10 files in code and 12 files counting comments. No reading gives 11. Harmless.
- **E-3.** `paper:877` «the files it does not use are those of §4 and of Theorems 5.9 and 5.9′», and `cert:223–226` (folders used «only in part»: pieces 1, 13, 14). From `logs/deps_mainTheorem.log`, the 23 modules outside the cone also include `Chain/Checks`, `Monotone/Checks` and `TheoremB/Checks` (pieces 4, 5, 10), which are neither §4 nor Theorem 5.9/5.9′; so `Chain`, `Monotone` and `TheoremB` are also used only in part. Harmless (these are `decide` checks). The folder-level statement «`Upper`, `Degeneration`, `Support` unused» is correct.
- **E-4.** The certificate is a companion to paper **v7** (`cert:8, 97, 402`, DOI 10.5281/zenodo.22961151), and its §-references are to v7; the paper in the material is **v8**, and the claim under audit cites v8 as doi:10.5281/zenodo.23045409, a DOI that occurs nowhere in the material (the README gives the concept DOI 22961150 and the software DOI 23045370, `material/lean/README.md:5`). The section numbers used in `cert` §1.3 (§1.1–§1.2, §2) do match v8's content, and v8 says no statement changed (`paper:107`).

### PRESENTATION
- **P-1.** `cert:35, 248, 370, 379–384` cite paths on the author's machine (`proyecto_lean/check_run29.log`, `proyecto_lean/clean_rebuild_2026-09-29.log`, `output-final_aristotle/`, `INFORME_ARISTOTLE_v1.md`, `ESTADO_ARISTOTLE.md`); in the published folder these are `logs/…` and `AUDIT_LOG.md`, and the state file is not published.
- **P-2.** `cert:55` «These are all the definitions needed to read the statement. They are printed by `#print` in the same log», and §1.1 «verbatim». `ColUpper.tP`, `ColUpper.tU` and `ColSplit.gaIdeal` are not printed in `check_run29.log`; `cert:72, 82, 86` gives them as the author's comments. Moreover the log's print of `Qk` (`check_run29.log:49`) omits the binder type, so it does not show `Fin ((q − 1) / 2)` (the `h` of the formula); the certificate's display adds it from the source. I checked all three against the sources: they are correct (STEP 1). A reader relying on the log alone could not.
- **P-3.** `cert:116` and `paper:874` say `ColUpper.card_Gamma` identifies `Qk k m` with `|Γ_𝒥|`, «the set of [DS, Definition 1.3]». Lean's `Γ` (`ColUpper/Count.lean:215`) is `{a ∈ μ_m^d : ev_a(ψ_J) ≠ 0 for some J}` (the complement used in the proof of [DS, Claim 4.3]), and `card_Gamma` holds over a field `K` with `X^m − 1 = Π_{ξ∈μ_m}(X − ξ)` and `m ≠ 0` in `K`. Equality with Def. 1.3 needs one more (easy) step that is not a Lean lemma; `evR_psiG_ne_zero_iff` (`ColUpper/Points.lean:120`) does most of it. No effect on `mainTheorem'`, where `Qk` is the explicit formula.
- **P-4.** `paper:877` «A rebuild from scratch compiles all 113 files»: the rebuild moved aside only the project's build directory; Mathlib's downloaded `.olean` cache was kept (`cert:370` says so correctly). «From scratch» should say «of the project».
- **P-5.** `cert:216` «Every one of them is checked by the kernel as part of `mainTheorem'`»: each declaration is checked by the kernel when its own module is compiled; the cone lists what `mainTheorem'` depends on. Loose wording, correct substance.
- **P-6.** `audit:348` (run 29) «no errors, no warnings»: `logs/build_run29.log` contains 21 warning lines (unused variables in older, replayed modules); the statement is true only of the five new files. `audit:206` (run 14) «peak memory 0.31 GB» is the «peak memory footprint», while `cert:310` gives 2.40 GB, the «maximum resident set size» of the same log: two different metrics, both labelled «peak».
- **P-7.** `cert:344` «Definitions (`def`, `abbrev`, `structure`, `inductive`, `instance`, `class`): 351». Reproduced only when lines starting with `noncomputable`/`@[…]` are counted (147 lines start with one of the listed keywords). Say how it was counted, as is done for theorems.

## 4. WHAT I DID NOT CHECK

- **I did not build anything** (as instructed). Every statement that «the kernel accepted these files» rests on the authors' logs (STEP 8, items 1–3). **Is a rebuild indispensable?** Not for the question «does the Lean statement say Main Theorem′?», which is about sources and definitions and is answered above. It is the only way to remove the remaining trust in the author's machine and logs (that these exact sources compile, with this toolchain, and give the printed axioms); a third-party `lake build` plus `#print axioms` (and ideally a replay of the environment with `lean4checker`) is the single most valuable next step. My verdict is conditional on it.
- **The proofs.** I read statements and definitions, not the 21 126 lines of proofs; the kernel is what checks them. I did not look for mathematical errors in the paper's proofs.
- **Pieces 1–9, 11–13, 15–27**: not compared with their Lean statements (only 10, 14, 28, 29).
- **Statements in the cone other than the final ones**: I relied on the cone only to see which files matter; I did not audit the faithfulness of intermediate definitions (e.g. `ColSetting` beyond its fields, `V_Λ`, tight patterns, the bipartite ideals). They cannot make the final statement wrong: they are used inside proofs, and the final statement mentions none of them.
- **Theorem 4.1, Theorems 5.9/5.9′ and the other off-path results**: not audited, except G-1.
- **Mathlib**: that `8f9d9cff…` is the `v4.28.0` tag, the integrity of the downloaded cache, and the Mathlib definitions themselves (`Module.Free`, `Module.finrank`, `MvPolynomial`, `Ideal.span`, quotients); I relied on their standard meaning.
- **The authors' brute-force scripts** in `material/lean/checks/` (not run, not read in detail) and the numbers of certificate §6, column «Brute-force checks», except those of pieces 28–29, which my STEP 5 reproduces independently in the cells I computed.
- **The PDF** versions of the certificate and paper (I read the `.md` versions only).
- **The topology** of [DS] (Theorem 0(a), (c), (d)): out of scope, not formalized, and not claimed to be.
- **Online records** (Zenodo DOIs, GitHub repository, Aristotle's web page): not consulted, as instructed.

## 5. SUGGESTIONS

1. **Have someone other than the author rebuild the project and print the axioms.** Run `lake exe cache get && lake build`, then `Check29.lean` and, if possible, `lean4checker` on `RequestProject`. Publish the log together with the SHA-256 of the sources used. This is the one step that would remove the remaining trust (§4).
2. **Make non-vacuity syntactic.** Add `Module.Finite ℤ (RZ (2k+1) m ⧸ IZ m k)` to `mainTheorem'_Z` (it is available from `quotientEquivZ`), and a lemma `Qk k m < m ^ (2k+1)` or `Qk k m ≤ (m−1)^(2k+1)`. Then «free of rank `r`» no longer depends on an argument outside Lean.
3. **Make the printed definitions complete.** Add `#print ColUpper.tP`, `#print ColUpper.tU` and `#print ColSplit.gaIdeal` to `Check29.lean`, with `set_option pp.funBinderTypes true`, so that `Qk`'s `Fin ((q−1)/2)` is visible. Then the certificate's «printed verbatim» becomes literally true (P-2).
4. **State `|Γ_𝒥|` as [DS] defines it.** Add a Lean definition of `Γ_𝒥` following [DS, Def. 1.3] (`a_i ≠ 1` for all `i`, and `∃ J` with `a_{j_i} a_{k_i} = 1` for `i ≥ 1`), and prove that it equals `ColUpper.Gamma`. Or reword `cert:116` and `paper:874` (P-3).
5. **Fix the bookkeeping:**
   - E-1: say «build logs for runs 1–2 (joint) and 3–29; check logs for runs 26–29»;
   - E-2: «`decide` tactic in 3 files»;
   - E-3: add the three `Checks.lean` modules to the list of unused files, and `Chain`, `Monotone`, `TheoremB` to the folders used in part;
   - E-4: re-key the certificate to paper v8 and its DOI;
   - P-1: use published paths;
   - P-4: «a rebuild of the project, Mathlib from cache»;
   - P-6: name the memory metric;
   - P-7: give the rule used to count definitions.
6. **Theorem 5.9′ in §12.8 (G-1).** Either formalize the graded-piece clause (freeness of each graded piece; independence of the graded dimensions from `F`), or write «Theorems 5.9 and 5.9′ (except the graded-piece clause) were formalized too».
7. **Record hashes for every piece.** Publish the md5 or SHA-256 of all 29 pieces as sent, and of every returned tarball. At present only pieces 27–29 can be checked against the audit log (`checks/s6_pieces_md5.log`).
8. **Optional check of faithfulness inside Lean.** Add an `example` that evaluates `ψ_J` at a small cell. For instance, at `(m,k) = (3,1)`, show that `IZ` has the `ℤ`-rank that the paper's §2.6 example gives (`dim = 6`, quotient `21`). This would tie the Lean definitions to a number in the paper, independently of the proof.


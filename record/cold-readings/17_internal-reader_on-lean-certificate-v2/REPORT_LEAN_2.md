VERDICT: HOLDS AS FAR AS I CAN CHECK — I traced `EvenAll.mainTheorem'` and Theorem O (`OddEquality.D1`, `D2_DJ`, `D2_M`) to Mathlib, to paper v12 and to [DS] in the original, evaluated the counts independently, and re-checked through the Lean kernel all 4 669 compiled project declarations they depend on; I found no FATAL and no GAP, four ERRORs of numbers or wording in the certificate, and five PRESENTATION points.

# REPORT_LEAN_2 — cold reading of the Lean certificate (Grepy Sello)

## 1. VERDICT

**HOLDS AS FAR AS I CAN CHECK.**

- **The statement.** `EvenAll.mainTheorem'`, as Lean prints it (identical to the certificate §1.1
  and to the author's post-clean log), says Main Theorem′ of paper v12 — for every `m ≥ 1`, every
  `k ≥ 0`, over `ℤ` and over every field in every universe — with the ring, the generators `ψ_J`,
  the index set `𝒥`, the special index `0`, the factors `t_b − 1` and `φ`, and the count `Q_k(m)`
  exactly as in [DS, §1 and §4.3] and the paper §1.2/§2. I chased the 15 definitions of the
  certificate and the 17 behind Theorem O down to Mathlib (STEP 3). Theorem O with equality is
  Corollary 8.13 of v12, without its graded clause, which is declared as not formalized.
- **No vacuity.** Using the final theorem itself, I proved in Lean that `Qall m k ≤ m^{2k+1}` for
  every `m ≥ 1` (the subtraction never truncates), and I derived non-vacuous instances of my own:
  rank 155 at `m = 6, k = 1`, with the module finite, and dimension 155 over `F_2`, `F_3`, `F_5`
  and `ℚ`. I also derived the cubic surface over `F_3` (21 and 6) and the paper's own form of the
  theorem (`m ≥ 3`, `k ≥ 1`, every prime). `Qall` agrees with a direct count of the set `Γ` of
  [DS, Definition 1.3], done in Python and again in Lean, in 30 cells. The eight cells of the
  mission are proved by the kernel.
- **The trust base.** The code contains no `sorry`, `axiom`, `native_decide`, `implemented_by`,
  `extern`, `unsafe`, `opaque`, custom syntax or kernel option. All 14 theorems I queried depend on
  `[propext, Classical.choice, Quot.sound]` only. The toolchain and the Mathlib commit are those of
  the certificate. The 233 sources match the author's manifest. Five source files re-elaborate from
  source. Beyond the mandate, **every one of the 4 669 project declarations in the cone of the five
  final theorems re-passes the Lean kernel from the compiled `.olean` files**: 4 650
  theorems/definitions and 9 inductive blocks with their recursors (L5, L6), and a negative control
  was rejected. So no compiled file holds an unchecked proof on the path.
- **The chain** of §3.1 is all Lean, with no open hypothesis (STEP 9).
- **The certificate's numbers** recount exactly, with four exceptions (the findings below). The
  paper is honest about what is formalized; on Lemma 8.12 it is more precise than the certificate.

How hard I looked: 8 Lean runs on 6 files of my own (L1–L6; L4 killed by the memory cap — my design —
and redone differently as L5; two attempts of L5 stopped at parse errors of mine), 5 re-elaborations
of project sources, 9 Python scripts; every mandate M1–M8. Three of my Lean files had slips of my
own (L1, L2, L5), all corrected and logged.

**There is no line in the material that allows a rejection.** The findings are:

| # | class | one line |
|---|---|---|
| F-1 | ERROR | the certificate says the v12 numbers coincide with v11 «for every result cited»; the paper §1.8 says Lemmas 8.7′, 8.8 and Corollary 8.9 are new under those numbers |
| F-2 | ERROR | «Two passages of version 12 were rewritten» — the paper counts three (also Lemma 9.10) |
| F-3 | ERROR | 15 instances (12 from v1) — there are 16 (13 from v1); all harmless |
| F-4 | ERROR | 187 definitions and the Table 6b «Defs» column do not follow the stated counting rule (it gives 178) |
| F-5 | PRESENTATION | «Tactic `decide` occurs in 22 files» — 22 is the word; the tactic is in 12 |
| F-6 | PRESENTATION | §3 table / §2 cells say a little more than the Lean: Lemma 8.12 (one direction only), Theorem 0(b) (only `K = 𝒥`), `R4` vs `R4'`; §2 item 3 not exhaustive |
| F-7 | PRESENTATION | the definitions behind Theorem O are never printed or tabulated (§1.2–§1.3, §2 item 5) |
| F-8 | PRESENTATION | «every file … compiled again» and «build failure … None occurred» omit the 4 modules not built locally |
| F-9 | PRESENTATION (rendering) | the PDF hyphenates code at line ends, including both hashes of §8 |

## 2. WHAT I CHECKED

Steps are logged as they are done. Scripts, Lean files and their outputs are in `checks/`.

### STEP 1 — STATE: CLOSED — material integrity at start

- `checks/c01_material_manifest.py` (log `checks/c01_material_manifest_start.log`): all 786 files listed in
  `MANIFEST_material_md5.txt` exist and match their md5; no unlisted file in `material/` outside
  `.lake/` and `.git/`. The material I audit is the material I was given.

NEXT: STEP 2 — read the final theorem and chase every definition to Mathlib (M1).

### STEP 2 — STATE: CLOSED — sources fingerprints, trust grep, independent count of Γ

- `checks/c02_source_manifest.py` (log `c02_source_manifest.log`): the 233 `.lean` sources match
  `logs/certificado_pares/MANIFEST_md5_233.txt` one by one (0 mismatches, no file missing or extra);
  the manifest is sorted bytewise and its own md5 is `8ac0df81107480be80e53c75b2e4dbbd`, as the
  certificate §8 says. `lakefile.toml` `d3ae68ec…`, `lean-toolchain` `b8b2923c…`,
  `lake-manifest.json` `235e6523…`: as in §8. 229 modules have an `.olean`; the 4 without are
  `EvenAll.Checks`, `EvenAll.Main`, `OddEquality.Checks`, `OddEquality.Main` (as in §8). No source is
  newer than its `.olean`; the `.olean` times run from 2026-10-03 17:21:31 to 21:00:11 (the clean
  rebuild window of §8). Toolchain: `lean --version` = 4.28.0 (commit 7e01a1bf…), through elan;
  the git HEAD of `.lake/packages/mathlib` is `8f9d9cff6bd728b17a24e163c9402775d9e6a365`, as in
  `lake-manifest.json` and certificate §4.
- `checks/c03_trust_grep.py` (log `c03_trust_grep.log`): comments and strings separated from code.
  In code of the 233 sources: no `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`,
  `extern`, `unsafe`, `opaque`, `csimp`, `skipKernelTC`, `partial def`, `elab`, `macro`, `syntax`,
  `run_cmd`, `ofReduceBool`, `import Lean`, `local instance`, `attribute [instance]`, `#eval`.
  One `infix:50 " ≼ " => WeakDom` (`Chain/Defs.lean:57`, the weak-dominance order; it is not in
  any statement I audit). Only Mathlib and RequestProject are imported. `set_option`: only heartbeats,
  recursion depth, `synthInstance.*`, `pp.*`, `autoImplicit`, `relaxedAutoImplicit`, `grind.warning`.
  `native_decide` occurs only in three comments (`EvenAll/Checks`, `EvenOne/Checks`,
  `OddEquality/Checks`); «admit» only as «admits» / «admitting» in two comments — both as §4 says.
  The `partial def` and `elab` hits are in the author's `material/checks/Deps*.lean` (the dependency
  walker), not in the project. Instances: see FINDINGS (16 declarations, the certificate says 15).
- `checks/c04_gamma_count.py` (log `c04_gamma_count.log`): `|Γ|` counted directly from
  [DS, Definition 1.3] (exponent tuples mod `m`, all `(2k+1)!!` matchings), against the constant
  term of [DS, Remark 4.4], the DS polynomials for `n = 2, 4, 6`, and a Python transcription of the
  Lean definitions `QkEven`/`Qk`/`Qall`: 30 cells, among them the eight cells of the mission and
  `m = 1, 2`, `k = 0`; **0 disagreements**. The paper's §9.1 table (30 values) agrees. `Q_k(m) ≤
  (m−1)^{2k+1}` in every cell tried, so `m^{2k+1} − Q_k(m) ≥ 1`. (A first run was killed by the
  watchdog after the main table because I had put `m ≤ 30` in a brute-force loop; its log is kept as
  `c04_gamma_count_first_run_killed.log`; the rerun with `m ≤ 16` finished.)

**Lean run L1 (planned).** File `checks/L1_main.lean`: `#check` of the final theorem, Theorem O and
the chain theorems; `#print` of 32 definitions; `#print axioms` of 14 theorems; `#eval` of `QkEven`,
`Qk`; my own derivations from `EvenAll.mainTheorem'`: `Qall m k ≤ m^(2k+1)` for all `m ≥ 1`
(no truncation), the instance `m = 6, k = 1` (rank 155 over `ℤ`, dimension 155 over `F_2`, `F_3`,
`F_5`, `ℚ`; the quotient is `Module.Finite`), the cubic surface over `F_3` (21 and 6), `m = 2`
(rank 7), the paper's form (`m ≥ 3`, `k ≥ 1`, every prime `p`), the field part in universe `w+1`.
Expected: `#check` identical to certificate §1.1 (universe name aside); every `#print axioms` gives
`[propext, Classical.choice, Quot.sound]` or a subset; the `#eval` values equal the Python ones
(19, 61, 141, 127; 6, 36, 90, 168; …); no error. Estimate: 200–300 s, 1.5–2.5 GB (cap 4.5 GB / 900 s).

NEXT: STEP 3 — run L1 and compare the final statement and every definition with the paper and [DS].

### STEP 3 — STATE: CLOSED — L1: the final statement, its definitions, axioms (M1, M2, M3)

**Run L1** (`checks/L1_main.log`): `VIGIA-FIN-OK exit=1 pico_kb=1431632 t=262s` (1.37 GiB, 262 s).
Exit 1 comes from **one error, in my own code**: my example «`Module.Finite ℤ (RZ 3 6 ⧸ IZ 6 1)`»
called `Module.finite_of_finrank_pos` without the instance `Module.Free` in context
(`failed to synthesize Module.Free ℤ (RZ 3 6 ⧸ IZ 6 1)`, line 141). Redone in L2. Everything else
elaborated with no error.

- `checks/c05_compare_L1.py` (log `c05_compare_L1.log`): my `#check` of `EvenAll.mainTheorem'`,
  `B1`, `B2`, `A3`, `OddEquality.D1`, `D2_DJ`, `D2_M`, `OddTheorem.theoremO` and my `#print` of the
  15 definitions of §1.2 are **identical** (whitespace-normalised) to `check_pares_postclean.log` and
  to the code blocks of the certificate §1.1, §1.2, §1.4.
- `#print axioms` (14 theorems: `mainTheorem'`, `B1`, `B2`, `A3`, `ColAssembly.mainTheorem'`, `D1`,
  `D2_DJ`, `D2_M`, `theoremO`, `EvenOne.E3`, `EvenMinus.lemma99`, `RankTwo.R4`,
  `EvenCount.card_Gamma_even`, `EvenCount.QkEven_values`): every one
  `[propext, Classical.choice, Quot.sound]`. No `sorryAx`, no other axiom.
- `#eval`: `QkEven 1 4, 1 6, 2 4, 1 8 = 19, 61, 141, 127`; `Qk 1 3, 1 5, 1 7, 1 9 = 6, 36, 90,
  168`; and 16 more cells (`m = 1, 2`, `k = 0`, `(3,2)=20`, `(5,2)=400`, `(6,2)=1001`, `(3,3)=70`,
  `(4,3)=1107`, `(10,1)=217`, `(12,1)=331`, `(11,1)=270`) — all equal to the direct count of Γ of
  `c04` (Definition 1.3 of [DS]).
- Kernel proofs from the final theorem (my code): `gs_Qall_le : ∀ m ≥ 1, ∀ k, Qall m k ≤
  m^(2k+1)` (from the field part at `ℚ`, `ColUpper.finrank_GA` and `Submodule.finrank_le`; axioms the
  standard three) — so the natural subtraction never truncates, **derived from the theorem itself**,
  as §1.3 of the certificate argues. `Qall 6 1 = 61`, `Qall 3 1 = 6`, `Qall 2 1 = 1`, `Qall 5 1 = 36`
  (unfold + `decide`). **Non-vacuous instance of my choice, `m = 6, k = 1`**: `RZ 3 6 ⧸ IZ 6 1` is
  free of rank `155 = 216 − 61`, and `dim = 155` over `ZMod 2`, `ZMod 3`, `ZMod 5`, `ℚ`; the ideal
  has dimension `61` over `ZMod 3`. Cubic surface over `F_3`: quotient `21`, ideal `6` (paper §2.6
  says 21 and 6). `m = 2, k = 1`: rank `7`. The paper's form (`m ≥ 3`, `k ≥ 1`, every prime `p`, over
  `ZMod p`) follows in one line; the field part also holds for `F : Type (w+1)` (universe check).
  Theorem O at `r = 5`, `k = 1`, over `ZMod 2`: `dim (D_J) = 61`.
- With `pp.explicit`, the `F`-module structure on `GA F (2k+1) m ⧸ IK F m k` is
  `Submodule.Quotient.module'` over the `MvPolynomial.module` structure: the ordinary one
  (`c·[f] = [c·f]`). No project instance enters the statement.

**M1 — definitions against the paper (§1.1, §2) and [DS] (§1, Definition 1.3, §4.3) in the original.**

| object | Lean (verbatim, `#print`) | paper / [DS] | verdict |
|---|---|---|---|
| `𝒥` | `Matching k = {J : Fin (2k+2) → Fin (2k+2) // ∀ x, J x ≠ x ∧ J (J x) = x}` | partitions of `{0,…,2k+1}` into unordered pairs (DS (1.1)) | fixed-point-free involutions ↔ perfect matchings, bijectively; equal involutions = equal matchings. Exact. |
| `R` | `RZ (2k+1) m = ℤ[X_0,…,X_{2k}]/(X_i^m − 1)`, `X_j` = `t_{j+1}` | `Z[t_1,…,t_{n+1}]/(t_i^m − 1)` | exact (index shift by one, through `tP = Fin.cases 0 X`). |
| `t_0` | `tP k 0 = 0` | `t_0 = (t_1⋯t_{n+1})^{−1}`, "never enters" (paper §2) | in `psiP` the first product runs over `a < J a`, so `J a ≥ 1`; the second over `0 < a < J a`. The value at `0` is never read: the dummy `0` is harmless. |
| `τ_J` | `∏_{a < J a} (t_{J a} − 1)` | `(t_{k_0} − 1)⋯(t_{k_d} − 1)`, `j_i < k_i` (DS p. 2) | the factor `t_b − 1` is carried by the **larger** element of every pair, including the pair of `0`. Exact. |
| `φ` factors | `∏_{0 < a < J a} φ(t_a t_{J a})` | `φ(t_{j_1}t_{k_1})⋯φ(t_{j_d}t_{k_d})` (pairs `i ≥ 1`, i.e. avoiding `0`) | exact. |
| `φ` | `phi m u = Σ_{s<m} u^s` | `t^{m−1} + ⋯ + t + 1` | exact. |
| ideal | `IZ m k = span {[psiP ℤ m J]}`; `IK F m k = span (range psiG)`, `psiG` = same formula in `GA` (`mk_psiP` proves `psiG` is the image of `psiP`) | `(ψ_J : J ∈ 𝒥)`; `F[G] = F[t]/(t_i^m − 1)` | exact. |
| rank | `Module.Free ℤ M ∧ finrank ℤ M = m^(2k+1) − Qall m k` | free abelian of rank `m^{2k+1} − Q_k(m)` | exact once the rank is `≥ 1` (then `finrank > 0` forces `M` finite); `Q_k(m) ≤ (m−1)^{2k+1}` (Γ ⊆ (μ_m∖1)^{2k+1}) gives rank `≥ 1` for every `m ≥ 1`. |
| `Q_k(m)` | `Qall m k = if Even m then QkEven k m else Qk k m`, sums of multinomials | §1.2: `N![x^N] I_0(2x)^{(m−1)/2}`, resp. `N![x^N] cosh(x) I_0(2x)^{(m−2)/2}` | term-by-term the coefficient extraction (I re-derived it); and numerically equal to `|Γ|` of Definition 1.3 in 30 cells (c04) and to the `#eval` in L1. |

Theorem O objects: `Peel.C F q n = F[X_0..X_{n−1}]/(X_i^{q−1})` with `q = 2h+2`, so the box is
`r = 2h+1`; `Tight.D F q a b = Σ_{i<q−1} (−1)^i y_a^i y_b^{q−2−i} = Σ_{u<r} (−1)^u y_a^u y_b^{r−1−u}`
= `D_r(y_a, y_b)` of §1.5/§8; `DJ` = product over the pairs with `a ≠ 0 ∧ J a ≠ 0 ∧ a < J a` (the
pairs avoiding `0`), `y_a = X_{a−1}`; `Mideal F q (2k+2)` = span of `D_P` over **all** perfect
matchings of `Fin (2k+2)` (Lemma 8.12's `ℳ`); `DIdealZ`, `MidealZ`, `CZ` are the same formulas over
`ℤ` (`DPR`). `1 ≤ h` ⇔ `r ≥ 3`; `QkEven k (2h+2) = N![x^N] cosh(x) I_0(2x)^h = N_r(2k+2)`. `D1`
is both equalities of Corollary 8.13, `D2_DJ`/`D2_M` both freeness statements (with the rank
`r^{2k+1} − N_r`, resp. `r^{2k+2} − N_r`, which the paper leaves implicit), `theoremO` is Theorem O
`≥`. The graded refinement is not formalized, as the certificate (§2 item 3) and the paper (§1.0
table) both say.

**M2 — vacuity.** `finrank` cannot be a default `0` here: the field part gives
`Qall = dim I_F ≤ dim F[G] = m^{2k+1}` (proved by me, above); the ℤ-rank is `≥ 1` (so the module is
finite and free of that rank); at my instance the ℤ-rank is `155`. Edge cases: `m = 1` gives
`Qall = 0`, rank `1` (`R = ℤ`, every `ψ_J = 0`); `m = 2` gives `Qall = 1` (the one point
`(−1,…,−1)` of Γ), rank `2^{2k+1} − 1`; `k = 0` gives `Q_0(m) = m − 1`, rank `1`
(`ℤ[t]/(t^m − 1, t − 1) = ℤ`): all equal to `|Γ|` by direct count and to the obvious algebra. The
paper only claims `m ≥ 3`, `k ≥ 1`; the extra cases are consistent. «Every field»: `∀ (F : Type u_1)
[Field F]`, universe-polymorphic, no characteristic hypothesis; I instantiated it at `ZMod 2`,
`ZMod 3`, `ZMod 5`, `ℚ` and in `Type (w+1)`. The only hypothesis is `1 ≤ m`. `Matching k` is never
empty (and an empty index set would make `IK = 0`, contradicting `dim IK = Qall > 0`).

NEXT: STEP 4 — run L2 (kernel values of `Qall` at the remaining mission cells, my own Lean count of
Definition 1.3, the corrected finiteness example, `|Matching k| = (2k+1)!!`).

### STEP 4 — STATE: CLOSED — L2: values in the kernel, my own Lean count of Γ

**Run L2 (planned).** File `checks/L2_values.lean` (imports only `EvenAll.PartBC`). Expected:
`Module.Finite ℤ (RZ 3 6 ⧸ IZ 6 1)` and rank 155; `#eval gsGamma` = `[6, 19, 36, 61, 90]` and
`[0, 1, 4, 1, 0]`; `|Matching k|` = `[1, 3, 15]`; kernel proofs `Qall 4 1 = 19`, `Qall 4 2 = 141`,
`Qall 7 1 = 90`, `Qall 8 1 = 127`, `Qall 9 1 = 168` (the last three by `decide +kernel`; the author's
`EvenAll/Checks.lean` was killed above 4.5 GB on a conjunction of six such cells, so these are the
risky lines); axioms the standard three or fewer. Estimate: 200–400 s, 1.5–3 GB.

**Result** (`checks/L2_values.log`): `VIGIA-FIN-OK exit=1 pico_kb=1551888 t=156s` (1.48 GiB, 156 s).
- `gsGamma` (my Lean transcription of [DS, Definition 1.3], no formula): `[6, 19, 36, 61, 90]` at
  `m = 3..7, k = 1`, and `[0, 1, 4, 1, 0]` at `(1,0), (2,0), (5,0), (2,1), (1,1)`; the same cells of
  `QkEven`/`Qk`: `[19, 61, 6, 36, 90]`. Agreement.
- `|{J : Fin n → Fin n // J fixed-point-free involution}|` = `[1, 3, 15]` for `n = 2, 4, 6`
  = `(2k+1)!!`; `BallotBound.Matching 2` is that type by `rfl`.
- Kernel proofs: `Qall 4 1 = 19`, `Qall 4 2 = 141` (through the project's `QkEven_values`),
  `Qall 7 1 = 90`, `Qall 8 1 = 127`, `Qall 9 1 = 168` (`decide +kernel`; the whole run, imports
  included, took 156 s). Axioms: the standard three. With L1 (`(3,1) = 6`, `(5,1) = 36`,
  `(6,1) = 61`), all eight cells of the mission are proved in the kernel and equal the direct count of
  Γ in Python (`c04`) and in Lean (`gsGamma`).
- Exit 1: one error, again mine — in the finiteness example I wrote `rw [h.2, gs2_Qall61]` and left
  the goal `6 ^ (2 * 1 + 1) - 61 = 155` open (missing `norm_num`). Redone in a later run (L6).

NEXT: STEP 5 — re-check from source `EvenAll/PartBC.lean` and three more files of the even chain (M3).

### STEP 5 — STATE: CLOSED — re-elaboration from source (M3)

Before the runs: the md5 of every source matches the author's manifest (STEP 2). Each run is
`lake env lean RequestProject/<file>` from `material/project`: Lean re-elaborates the file and the
kernel re-checks its proofs against the compiled modules it imports; nothing is written.

**Run R1 (planned): `RequestProject/EvenAll/PartBC.lean`.** Expected: exit 0, no error, no
`declaration uses 'sorry'`, possibly linter warnings. Estimate: ~170 s, ~1.5 GB.

Result (`checks/R1_PartBC.log`): `VIGIA-FIN-OK exit=0 pico_kb=1595792 t=74s`, no message at all.

**Runs R2–R5 (planned), one after the other**, files of my choice on the even chain:
`EvenAll/PartA.lean` (`A3` = `H(m,k)` for every even `m`), `EvenOne/Main.lean` (`E3`, Theorem 9.11 `≥`),
`OddTheorem/TheoremO.lean` (`theoremO`), `EvenMinus/MinusMain.lean` (`lemma99`, the colour `−1`).
Expected for each: exit 0, no error, no `sorry` warning. Estimate: 75–150 s each, ≤ 2.5 GB.

Results: `R2_PartA.log` `exit=0 pico_kb=1673392 t=76s`; `R3_EvenOneMain.log` `exit=0
pico_kb=1625264 t=66s`; `R4_TheoremO.log` `exit=0 pico_kb=1556768 t=74s`; `R5_MinusMain.log`
`exit=0 pico_kb=1615920 t=69s`. No message in any of them.

What this shows and what it does not: these five files elaborate from their sources, and their
proofs pass the kernel, **given the compiled statements of the modules they import**. It does not by
itself show that every compiled `.olean` was produced from the source I read. Two facts limit that
residual risk: (i) every definition of the final statement is printed from the compiled files and is
character-for-character the source text (STEP 3); (ii) `#print axioms` reads the compiled cone and
finds only the three standard axioms. A compiled file could still, in principle, hold a declaration
that never went through the kernel (a forged `.olean`). This residual risk is closed for the whole
cone in STEP 10 (L5, L6).

NEXT: STEP 6 — recount the numbers of the certificate (M4).

### STEP 6 — STATE: CLOSED — the certificate's numbers against the files (M4)

Scripts `checks/c06_counts.py` and `checks/c07_counts2.py` (logs alongside). Counting rules as the
certificate states them (§7: lines = `wc -l`; theorems = lines beginning with `theorem ` or
`lemma `; definitions = lines beginning with `def`, `noncomputable def`, `abbrev`).

| claim (certificate) | recount | verdict |
|---|---|---|
| §7 whole project 233 files / 41 243 lines / 1 859 thms | 233 / 41 243 / 1 859 | exact |
| §7 v1 113 / 21 126 / 937 | 113 / 21 126 / 937 (the 28 v1 folders + `Main.lean`) | exact |
| §7 E1–E20 120 / 20 117 / 922 / **187 defs** | 120 / 20 117 / 922 / **178 defs** | **ERROR** (F-4): 187 is reproduced only by a broader rule (lines beginning with `def`, `noncomputable`, `abbrev`, `structure`, `class`, `instance`), which also catches two comment lines |
| Table 6b files / lines / thms, 20 rows | all 20 rows exact | exact |
| Table 6b defs | 8 rows differ by the same 9 lines (F-4) | ERROR (F-4) |
| Table 6b modules built / build s / peak GiB | all 20 rows exact; total 8 209 s, max 2.25 GiB | exact |
| §4 413 axiom lines: 401 / 11 / 1 | 413: 401 `[propext, Classical.choice, Quot.sound]`, 11 `[propext, Quot.sound]`, 1 `[propext]`; the 12 small lemmas are in `Pfaffian`, `RankTwo`, `OddPatterns`, `OddLifts`, `OddLifts2`, `OddTheorem`; no `sorryAx`, no other axiom | exact |
| §4 «Tactic `decide` occurs in 22 files (11 of them from version 1)» | the **word** `decide` (whole word, comments included) is in 22 files, 11 + 11; the **tactic** is in 12 files (3 v1: `Chain/Checks`, `Monotone/Checks`, `TheoremB/Checks`; 9 new); elsewhere it is the Boolean function `decide (p)` or a comment | **PRESENTATION** (F-5) |
| §4 «15 instances, 12 of them from version 1» | **16** instance declarations, **13** in v1 folders, 3 new (the three named) | **ERROR** (F-3) |
| §4 forbidden constructs none; `native_decide` only in 3 comments; «admit» only in «admits/admitting» | confirmed (c03) | exact |
| §4 «the eleven main theorems give the three axioms» in `check_pares_postclean.log` | 11 lines, all three axioms | exact |
| §3.2 cones 4 412/180, 4 169/174, 2 470/101, 2 425/97 | parsed from `deps_pares_postclean.log`: the same; the header and the per-module lines agree | exact |
| §3.2 53 modules outside the cone; `OddEquality`, `Odd3`, check modules, `Main` modules among them | 53; the whole `OddEquality` folder, all of `Odd3`, all `Checks`, several `Main`; also `Ballot.{Alg,Comb,Construct}`, `Degeneration.*`, `EvenAll.PartD/PartE`, `EvenAssembly.Quartic`, `EvenCount.Number`, `EveryField.{Integral,Invariance,Main}`, `FreeZ.*`, `OddPatterns.{Examples,Relabel}`, `Support.*`, `Upper.*` («among them» is not exhaustive) | exact |
| §8 229/233 exit 0, 17:20:22–21:00:12 | 229 result lines, all `exit=0`; START/END as stated; the 229 `cr_logs` agree with the summary; no `error`/`sorry` text in them | exact |
| §8 «module builds sum to 13 190 s; longest `Peel.Main`, 93 s» | sum of `wall` = 13 190 s (sum of the watchdog's `t` = 13 069 s); `Peel.Main` wall 93 s | exact (wall clock) |
| §8 peak 2.35 GiB at `EveryField.Main` | 2 462 976 kB = 2.349 GiB, `EveryField.Main` | exact |
| §8 four modules not built; no other module imports them | `EvenAll.Checks` is imported only by `EvenAll.Main`, `OddEquality.Checks` only by `OddEquality.Main`, the two `Main` by nobody | exact |
| §8 the order respects the imports | `orden_modulos.txt` is a topological order of the source imports (checked) | exact |
| §8 logs identical except the two `tU` lines | check logs: only the two added `#print ColUpper.tU` lines differ (plus the watchdog's last line, time/memory); deps logs: only the watchdog line; no `error`, `warning`, `sorry` | exact |
| §8 the five modules = imports of `CheckPares.lean`; «216 of the 233» | yes; import closure of the five = 216; it contains `DepsPares`'s imports and the whole cone of the final theorem | exact |
| Table 6a, 19 counts and sum 33 731 | the last `checks N failures 0` line of each `chkE*.log`: the same 19 numbers, sum 33 731 | exact |
| §5.4 silent controls declared | `chkE4` 17/18 fire, `chkE10` 38/58, `chkE11` 47/49; the silent ones are printed `SILENT` in the logs | as stated |
| §3 «No piece ever modified a file of an earlier piece» | cannot be checked without the tarballs; consistent evidence: every v1 source has mtime ≤ 29 Sep 18:36, before E1 (2 Oct); the v1 counts 113/21 126/937 are those of certificate v1 | not checkable here |
| §4/§7 Aristotle's register 359 PROVED | web page, not in the material | not checkable |

NEXT: STEP 7 — paper v12 ↔ certificate ↔ Lean (M5): the §1.3 table, the §3 table, Lemma 8.8(ii) vs
`RankTwo.R4`, Theorem O, Main Theorem′, the paper's claims of formalization.

### STEP 7 — STATE: CLOSED — paper v12 ↔ certificate ↔ Lean (M5)

Script `checks/c08_named_results.py` (log `c08_named_results.log`) prints, for every row of the
certificate §3 table, the source statement of every «Main Lean result» it names. Every name
resolves except that «`A0`–`A4`» (E6) is a range of the piece's labels: the declarations are `A0`,
`A1`, `A2_D`, `A2_Dminus`, `A3_D`, `A3_Dminus`, `A4_D`, `A4_Dminus`, `A4_coeff_D`, `A4_coeff_Dminus`
(`OddShapes/Identities.lean`), which are (8.1)–(8.4).

**Certificate §1.3 table.** Each row is correct: row 1 (`QkEven` = the coefficient extraction;
bounds `c ≤ k+1`, `b_u ≤ N` lose nothing; exact division); row 2 (`card_Gamma_even`; note that the
Lean `Gamma` is defined as `{a : ev_a(ψ_J) ≠ 0 for some J}`, the characterisation of
[DS, Claim 4.3]'s proof, not literally Definition 1.3 — harmless, it is internal, and my direct count
of Definition 1.3 agrees with `Qall`); row 3 (`card_closedPointed`, closed = `cnt u = cnt (−u)` and
`cnt o` even); row 4 (literal); row 5 (no truncation — I derived it in Lean, STEP 3). Completeness:
the table and the `#print` list of `CheckPares.lean` stop at the fifteen definitions of the final
theorem; **the seventeen definitions behind Theorem O** (`TheoremB.DIdeal`, `DJ`, `idx`, `Tight.D`,
`Tight.y`, `Peel.C`, `Peel.powIdeal`, `OddEquality.Mideal`, `ColOne.DPn`, `ColComp.PerfMatch`,
`DIdealZ`, `DJZ`, `MidealZ`, `DPnZ`, `EveryField.DPR`, `FreeZ.CZ`, `FreeZ.powIdealZ`) are only
described in prose in §1.4 and never printed. I printed and checked them (L1, STEP 3): they are
faithful. → PRESENTATION (F-7).

**Certificate §3 table**, row by row. Every «Paper v12» cell names a result that exists in v12 with
that number (I listed all numbered results of v12), and the named Lean results prove it:
E1 `thm76_any`/`theoremC_any` (every `q ≥ 2`, hypothesis «`C(q−1,t) ≠ 0` in `F` for `t ≤ q−1`»,
exactly §1.9 of the paper) and `…_prime_pow` (char `p`, `q = p^v`); E2 Lemma 9.1 and the upper bound
(for the full family `K = 𝒥`, which is all that is used; [DS, Claim 4.3] for general `K` is not
formalized); E3 Theorem 8.15 (`O_ge_three`, box 3); E4 Proposition 9.2 (`prop92_ge`: `dim (D_J)` at the
box `2^v − 1` ≤ `dim I` in characteristic 2; `pow2_of_oddbox`, `quartic_char_two`); E5 `theorem_i/ii/iii`
under `HypH`, `mainTheorem'_four`; E6 (8.1)–(8.4), Lemma 8.3 (`optS_filter_eq_Icc`) and the first half
of Lemma 8.5 (`isInterlaced_root_*`); E7 Lemma 8.4 (`isInterlaced_layerS`) and the count of Lemma 8.5
(`card_ZS_root_*`); E8 §8.3 — and the signs of (iii), (F2), (F3), (F4), (F7) printed in v12 are
**exactly** those of `pf_expand`, `bpf_expand_last`, `bpf_square`, `bpf_expand_var`, `bpf_laplace`
(I compared them index by index, with the 0-based/1-based shifts); E9 Lemma 8.8 (i) = `RankTwo.R2`,
(ii) see below, (8.6) = `S2`, Corollary 8.9 = `S5a`/`S5b`; E10 Lemma 8.7′ (a)/(b) = `M2a`/`M2b`,
Lemma 8.7 = `M3_pos` (`ℓ ≥ 1`)/`M3_zero` (`ℓ = 0`); E11–E14 Definition 8.6, Proposition 8.10
(`T1`–`T8`, `lemmaK`, `prop810`), Theorem 8.11 (`theorem811`), Theorem O `≥` (`theoremO`); E16–E19
Lemmas 9.4–9.10 (`lemma94`, `lemma95`, `C4_even`, `lemma97`, `lemma98`, `lemma99`, `lemma910`) and
Theorem 9.11 `≥` (`E3`); E20 Theorem 9.11 (`B1`, `B2`), Main Theorem′ (`mainTheorem'`), Corollary
9.12 (i) (`D2`) and (ii) (`E1`, over `F̄_2`), Corollary 7.8 (`E2`, odd `p`); E15 Corollary 8.13
(`D1`, `D2_DJ`, `D2_M`) and Lemma 8.12 — **one direction only** (`A5`: `θ(ℳ) ⊇ (D_J)C`, hence
`dim (D_J)C ≤ dim ℳ`; the injectivity of `θ` and the equality of its image are not formalized; the
Lean file says «Lemma 8.12, one direction» and the paper §14.8 says «Lemma 8.12 in the direction
used»; the certificate's cell says only «Lemma 8.12») → PRESENTATION (F-6).

**The numbering claim.** Certificate line 8: «The numbers … are those of version 12; they coincide
with those of version 11 … for every result cited here», and §3: «Version 12 keeps the numbering of
version 11 for every result in the table below». The paper §1.8 says the opposite for three results
the certificate cites: «the auxiliary results of §8.5 are new (Lemma 8.7′, and a Lemma 8.8 and a
Corollary 8.9 whose numbers version 11 used for other statements)». The piece `q_rank_two.md` confirms
that in v11 «Lemma 8.8» and «Corollary 8.9» were exterior-algebra statements. → ERROR (F-1).
Also §3: «Two passages of version 12 were rewritten to follow the routes taken in Lean» (§8.5 and
the upper bound of Corollary 8.13); the paper §1.8 counts **three** («… and Lemma 9.10, without the
injectivity of the map `θ`»), and §14.6 lists the proof of Lemma 9.10 among the passages new in
v12. → ERROR (F-2).

**Lemma 8.8(ii) vs `RankTwo.R4`.** Paper: `Pf(a + E·Oᵀ − O·Eᵀ; c) = Pf(a; c) − Pf(a; c, E, O)`.
`RankTwo.R4`: `bpf (a − M) c = bpf a c + bpf a (c, E, O)` with `M i j = E i * O j − E j * O i`,
i.e. `Pf(a − E·Oᵀ + O·Eᵀ; c) = Pf(a; c) + Pf(a; c, E, O)`. **Not the same statement**: `R4` is the
identity the paper's proof reaches just before «replacing `O` by `−O` and using (F2) gives (ii)». The
two are equivalent by `O ↦ −O` and the linearity of `bpf` in a border column, and the paper's
literal form is also proved: **`RankTwo.R4'`** (`bpf (a + M) c = bpf a c − bpf a (c, E, O)`,
`RankTwo/Update.lean:288`), derived from `R4` that way. `bmat` is the paper's bordered matrix
(block `a`, `c_k(i)` in row `i` / column of border `k`, `−c_k(i)` symmetric, zero border block, `N`
first) and `pf` is the paper's Pfaffian (`pf_eq_sum_matchings`: sum over matchings of
`(−1)^{crossings}·Π a_{x,π x}`). The certificate's §3 row E9 names `R4`; naming `R4'` would match
(ii) literally (folded into F-6).

**Theorem O with equality.** `D1` = both equalities of Corollary 8.13 (every field, every `h ≥ 1`
i.e. odd `r ≥ 3`, every `k`); `D2_DJ`, `D2_M` = both freeness statements, with the rank. Exact,
except the graded clause («the dimensions of the graded pieces … do not depend on `F`»), which is
not formalized and is declared so in the certificate §2.3 and the paper §1.0/§14.8/§16.

**Main Theorem′ and Theorem 9.11.** In L1 I derived in one line from `EvenAll.mainTheorem'` the
paper's own form (`m ≥ 3`, `k ≥ 1`, every prime `p`, `ZMod p`); `EvenAll.B2` (+`B1`) gives the
algebraic part of Theorem 9.11 for every even `m ≥ 2`, every `k`, every field. The last clause of
Theorem 9.11 (torsion of `H_{2k}(X;Z)/L(X)`) is topological and is not claimed.

**The paper's claims of formalization.** §1.0 «Lean» column: Main Theorem′ yes ✓; Main Theorem
«the algebraic form only» ✓; Theorem B «yes, except the graded refinement» (v1; not re-audited by me
beyond the shared definitions); Theorem C «yes» ✓ (incl. Corollaries 7.8, 9.12: `EvenAll.E1`, `E2`);
Theorem O «yes, except the graded refinement» ✓; H, W, A, Cor. 10.8, Fact 11.2 «no» ✓. §14.8's
list for the twenty new pieces — §7 for every `q ≥ 2` and at `q = p^v`; Lemma 9.1; the upper bound
for even `m`; shapes, interlaced pairs, Lemmas 8.3–8.5; §8.3 with its signs; Lemmas 8.7, 8.7′, 8.8,
Corollary 8.9 «in the form printed in §8.5»; Definition 8.6; the seven cases of Proposition 8.10;
Theorem 8.11; Theorem O; «Lemma 8.12 in the direction used»; Corollary 8.13; Lemmas 9.4–9.10;
Proposition 9.2; Corollaries 7.8, 9.12; Theorem 8.15 — every item has its Lean theorem (above). §14.7
item 7 («(8.6), the two operations of Lemma 8.8 and the powers of `ζ` in Corollary 8.9, all checked
in Lean») ✓ (`S2`, `R2`/`R4'`, `S5a`/`S5b`). §16 ✓. The paper is honest and, on Lemma 8.12, more
precise than the certificate.

**Certificate §2.** Exact in what it says. Not exhaustive as a list of what is not formalized:
besides H, W, §10's Theorem A, §11, §14 and the graded refinements, also not formalized are the rest
of §10 (Proposition 10.5, Corollaries 10.6, 10.8), Proposition 2.6, Lemma 12.4, the injectivity of `θ`
in Lemma 8.12, [DS, Claim 4.3] for subfamilies `K ≠ 𝒥`, and the topological half of Proposition 2.1.
None is on the path or claimed elsewhere. → PRESENTATION (folded into F-6).

NEXT: STEP 8 — pieces ↔ Lean for E9, E10, E14, E15, E19, E20 (M6).

### STEP 8 — STATE: CLOSED — pieces ↔ Lean (M6): E9, E10, E14, E15, E19, E20

Sources: the six `q_*.md`, the Lean sources, `audit/ESTADO_ARISTOTLE.md`, and
`project/ARISTOTLE_SUMMARY.md`. **That summary stops at run `e8d51073` (piece E13)**: Aristotle's own
notes for E14, E15, E16–E20 are not in the material (they were on Aristotle's page, per the
certificate §5), so for those pieces I compared the piece text with the Lean statements directly.
A general remark that bounds the stakes: the final statements (`mainTheorem'`, `D1`, `D2_*`) mention
only the definitions checked in STEP 3; an unfaithful *intermediate* definition could not make them
false (the kernel checked them), it could only make an auxiliary Lean result say something other than
the paper's lemma. So M6 is about the paper ↔ Lean correspondence of auxiliary results.

- **E20 `q_even_assembly.md`.** (A1) `idealI S k = IK F S.m k` is proved by `rfl` (so the colour
  reduction works on the literal [DS] ideal); (A2) equality for every `ColSetting`; (A3) `HypH m k`
  for every even `m ≥ 2` (prime `p | m`, `m = p^v r`, `algClosureSetting` over `F̄_p`, rank invariance
  `F̄_p → F_p`); (B1), (B2), (C1), (C2), (D2) = Corollary 9.12(i), (E1) = Corollary 9.12(ii) over
  `AlgebraicClosure (ZMod 2)`, (E2) = Corollary 7.8 for odd `p` — all as asked. `E2` carries an
  unused hypothesis `_hp2 : p ≠ 2` (so it is in fact proved for every prime): harmless.
- **E19 `q_even_block_one.md`.** (A1) `A1`, (A2) `PhiE`/`A2`, (B1)–(B3), θ (`thetaP` = the piece's
  suggested implementation: keep the monomials with `q ∣ d 0`), (C2) `theta_iota_mul`,
  `theta_X0_pow_mul`, (C3) `theta_pair`, (C4), (C5), (D1) `lemma910`, (E1)–(E3). The changes the
  author logged («A1 every `v`, C3 any characteristic, C4 stated from `J`», and the instance
  `instModuleGASelf := Semiring.toModule`) are generalisations or the direction (C5) needs («every `J`
  comes from some `P`»): harmless.
- **E14 `q_oddbox_theorem.md`.** `lemmaK` has the five disjuncts (A), (M), (Z), (R), (R1) with the
  piece's numbers, and drops `1 ≤ h` (more general); `prop810` (`i ≤ 2h`, slice `2h − i`),
  `theorem811` (every `OddSetting`, every interlaced `Λ`), `theoremO` — as asked. I also read the
  Lean definitions behind them against §8.2 of v12: `OddSetting` (one fixed point, `h ≥ 1`),
  `shape` = (residue partition, parity of the zeros), `Sh` (`ℓ ≤ h`, `|λ| + δ ≤ m`, same parity),
  `optS` (removals, zero option at `ℓ + 1`, middle options, additions), `FS` = (8.5), `ZS` = `Z_Λ`,
  `IsInterlaced` = (D0) + Definition 8.2 (D1), (D2). Faithful.
- **E15 `q_oddbox_equality.md`.** The piece itself asks for «Lemma 8.12, one direction»; the Lean
  does exactly that (`A1`–`A5`). (B1) is proved for every box `q ≥ 2`, (C1) for an arbitrary finite
  point set, (C3) needs `T` non-empty (true: `0 ∈ T = {−h,…,h}`), (C5) is the inequality
  `finrank (C/⋂ I_P C) ≤ |Γ|` (all the argument needs), (D3) (graded) not done — exactly the
  «review suggested» list of the certificate §5. (D1), (D2) as asked, (D2) in the literal form
  (ideal generated by the integer `D_J`, resp. `D_P`, in `ℤ[y]/(y^r)`). Faithful; changes harmless.
- **E9 `q_rank_two.md`.** The piece asks for (R4) in both forms; Lean has `R4` (first form) and
  `R4'` (second form = Lemma 8.8(ii) of v12). (R2) = Lemma 8.8(i), (S2) = (8.6), (S5)(a)/(b) =
  Corollary 8.9 (`S5a`, `S5b`). Faithful.
- **E10 `q_membership.md`.** `U r p y` is the ideal spanned by `vand y S · Π_{e∈P} D_r(y_e)` with
  `|S| = p` and `P` a perfect matching of the complement, `D_r = Dab (r+1)` (not `D^−`): the paper's
  𝔘. `M2a`/`M2b` = Lemma 8.7′(a)/(b) (`|S| = s + 2`, resp. `s + 1`), `M3_pos`/`M3_zero` = Lemma 8.7
  (`ℓ = l + 1`, borders `0,…,l−1`, `|B_0| = l + 2 + 2t`; resp. `ℓ = 0`, border `2h`, `|B_0| = 1 + 2t`),
  over any commutative ring with `y_i^r = 0`, `h ≥ 1`. Faithful.

NEXT: STEP 9 — the chain of §3.1 in the Lean sources (M7).

### STEP 9 — STATE: CLOSED — the chain of the final theorem (M7)

Followed in the sources (all five files on the path that I re-elaborated in STEP 5 are marked †):
`EvenAll.mainTheorem'`† splits on parity. Odd `m`: `ColAssembly.mainTheorem'_Z`, `mainTheorem'_field`,
`finrank_IK_eq` (v1). Even `m`: `B2`† = `EvenAssembly.theorem_iii` + `A3`†, `B1`† =
`EvenAssembly.theorem_ii` + `A3`†. `theorem_ii`: if `(m : F) ≠ 0`, `theorem_i` (char 0 via `ℚ` and
`rankOver_rat_intMatU_even`; char `p ∤ m` via `F̄_p`, `finrank_IK_eq_card_Gamma`, `card_Gamma_even`);
if `p | m`, the hypothesis `HypH`. `theorem_iii`: `R/I_ℤ ≅ ℤ^n/L` (`quotientEquivZ`), freeness by
`FreeZ.quotient_free_of_finrank_image` (rank over every `F_p` = rank over `ℚ`), field part by
rank–nullity with `finrank_GA = m^{2k+1}`. `A3`†: `A2_even` = `EvenOne.E3`† (`≥`) and
`finrank_IK_le_even` (`≤`: `dim I_F = rank_F A ≤ rank_ℚ A = |Γ| = QkEven`), then
`rankOver_eq_rankOver_zmod`. `EvenOne.E3`† = `lemma61_ii` + `E2` + `C4_even`, with blocks
`lemma97`, `lemma98`, `lemma99`†, `lemma910`, and `lemma910` uses `Pow2.prop92_ge` and
`OddTheorem.theoremO`†. Every step of §3.1 is there, in that order. There is no open hypothesis:
`mainTheorem'` assumes only `1 ≤ m`; `HypH` is discharged by `A3`; every `ColSetting` used is built
(`algClosureSetting`); the kernel accepted the whole cone with the three standard axioms only
(STEP 3). **No arrow holds «by the paper».** The modules of the chain are all in the cone of
`deps_pares_postclean.log` (checked: every `EvenOne`, `EvenMinus`, `EvenColours`, `EvenBlocks`,
`Pow2`, `OddTheorem`, `RankTwo`, `Membership`, `Pfaffian`, `OddLifts*`, `OddPatterns`, `OddShapes`,
`OddLayers`, `BipAny`, `EvenCount`, `EvenAssembly` module that carries a theorem is listed).

NEXT: STEP 10 — the corrected finiteness example (L6), an attempt to replay the compiled
declarations through the kernel (M8, optional), then sections 1, 3, 4, 5 and 6.

### STEP 10 — STATE: CLOSED — extra checks (M8): the compiled cone through the kernel

**Run L3 (planned): `checks/L3_probe.lean`** (`import Lean` only): does the core provide
`Lean.Environment.replay`? Expected: either its signature or «unknown constant». Estimate: < 30 s, < 1 GB.

Result (`checks/L3_probe.log`, `exit=0 t=8s`): `Environment.replay : Std.HashMap Name ConstantInfo →
Environment → IO Environment` exists in this core.

**Run L4 (planned): `checks/L4_replay.lean`.** The file imports `Mathlib` only (the project imports
nothing else). Inside `#eval` it loads the compiled modules `EvenAll.PartBC` and `OddEquality.PartD`,
collects (types and proofs, transitively) every project declaration used by `EvenAll.mainTheorem'`,
`OddEquality.D1`, `D2_DJ`, `D2_M`, `OddTheorem.theoremO`, and replays them all through the kernel on
top of the Mathlib-only environment. This answers the residual risk of STEP 5 (a compiled `.olean`
holding a declaration that never passed the kernel) for the whole cone, independently of the
sources. Expected: the five roots present; about 4 400–5 000 project constants, 0 axioms, 0 without a
value, 0 clashes; «KERNEL REPLAY FINISHED»; the five roots present afterwards. Estimate: 5–15 min,
3–4 GB (two copies of Mathlib's environment in one process). If the watchdog kills it, I report it
and split the cone in two runs.

Result (`checks/L4_replay.log`): **`VIGIA-MATADO-MEMORIA mem_kb=4815872 t=214s`** — killed by the
watchdog at 4.6 GiB, with no output (an `#eval` prints only at its end). The cause is my design (two
copies of Mathlib's environment in one process). I did not raise the cap.

**Run L5 (planned): `checks/L5_kernelcheck.lean`**, second design: the file imports only `Lean`;
inside `#eval` it loads the compiled project once, and re-submits each compiled theorem /
definition of the cone to the kernel under a fresh name (`Kernel.Environment.addDecl` with the
compiled type and the compiled value): the kernel re-type-checks every compiled proof term against
its compiled statement. Inductives, constructors and recursors are counted, not re-checked (a
limitation I state). A negative control (the statement of `mainTheorem'` with the proof of
`theoremO`) must be rejected. Time budget 560 s for the checks; if it is not enough, a second run
continues from the index where the first stopped. Expected: control rejected; 0 failures; about
4 400–5 000 constants. Estimate: ≤ 800 s, 1.5–2.5 GB.

L5 attempts: (1) two syntax errors of mine (structure-instance layout: «unexpected identifier;
expected '}'» at lines 34 and 64), `exit=1 t=7s`, nothing run — its log was overwritten by attempt (2);
(2) my Python edit of the file corrupted it (an empty search string: the word `#eval` also occurs in
the header comment), 100 parse errors, `exit=1 t=1s`, nothing run — the corrupted file and its log
are kept as `L5_kernelcheck_attempt_corrupted_file.*`; (3) the clean file:

**Result (`checks/L5_kernelcheck.log`): `VIGIA-FIN-OK exit=0 pico_kb=2545296 t=173s`.**
`project constants in the cone of the five roots: 4669`; `NEGATIVE CONTROL: rejected by the kernel,
as it must be`; `checked items 0..4668 of 4669 in 102042 ms: re-checked OK 4650, FAILED 0, skipped
(inductive/ctor/rec/quot) 19, axioms 0`. So every compiled theorem and definition of the project that
the final theorem and Theorem O use — **4 650 declarations, types and proof terms as stored in the
`.olean` files** — type-checks again in the Lean kernel, relative to Mathlib as compiled. This
closes, for the whole cone, the residual risk of STEP 5 (a compiled declaration that never passed
the kernel), independently of the sources. (4 669 is the cone of the five roots; DepsPares's 4 412 is
the cone of `mainTheorem'` alone.)

**Run L6 (planned): `checks/L6_inductives_finite.lean`** (imports `EvenAll.PartBC`,
`OddEquality.PartD`): (1) the finiteness example, corrected; (2) the 19 skipped constants: each
inductive block re-submitted to the kernel under fresh names, and the generated recursor compared
with the compiled one (type, rules, counters). Expected: finiteness accepted; the 19 = a few
structures with their constructor and recursor; every block accepted, every comparison `true`.
Estimate: ~200 s, ~1.7 GB.

**Result (`checks/L6_inductives_finite.log`): `VIGIA-FIN-OK exit=0 pico_kb=1836160 t=169s`**, one
linter warning (my `<;>`). (1) `Module.Finite ℤ (RZ 3 6 ⧸ IZ 6 1) ∧ finrank = 155` accepted. (2) The
19 skipped constants are 9 structures (`ColSplit.ColSetting`, `ColTensor.BoxSetting`,
`OddShapes.OddSetting`, `Bip.BTightPattern`, `Fibres.FibreSetting`, `EvenCount.PointedSetting`,
`OddPatterns.MarkedPattern`, `Tight.TightPattern`, `ChainLemma.Partition`), their 9 constructors and
one recursor (`ChainLemma.Partition.rec`). Each of the 9 blocks, re-submitted under fresh names, was
accepted by the kernel, and the recursor the kernel generated equals the compiled one (type `true`,
rules `true`, counters `true`). (I compared the recursor's type, the right-hand sides of its rules and
its counters; I did not compare the constructors' `cidx`/`numFields` fields separately.)

With L5 and L6, **every project declaration in the cone of the five final theorems (4 669) has been
re-checked by the Lean kernel from the compiled files**: no forged or unchecked declaration is there.

**End of the session** (`checks/c01_material_manifest_end.log`, `c02_source_manifest_end.log`):
`material/` still matches `MANIFEST_material_md5.txt` (786/786, nothing unlisted); the 233 sources
still match the author's manifest; no `.olean` changed. The only file of `material/` newer than the
start of my work is `material/project/.lake/packages/mathlib/.git/index` (refreshed by Lake, as the
mission foresees). No `lean`/`lake` process is left running.

NEXT: write sections 1, 3, 4, 5; then section 6; then re-read the report from the disk.
(Done: sections 1, 3, 4, 5 written, then section 6. Then I re-read the whole report from the disk
and corrected six things: the name of the start log of STEP 1, the count of my Lean runs in section 1,
an unmeasured «each in a few seconds» in STEP 4, a stale «see section 5» in STEP 5, «ten or so» →
«seventeen» in STEP 7, and the exact list of `Checks` values I reproduced in section 4.)

## 3. FINDINGS

No FATAL. No GAP. Ranked by class, then by importance. «cert» = 
`material/certificate/LEAN_CERTIFICATE_CHAISE_LONGUE_v2.md`; «paper» = `material/paper/PAPER_OFICIAL_v12.md`.

**F-1 — ERROR — the numbering claim.** cert line 8: «The numbers of sections and results below are
those of version 12; they coincide with those of version 11, which was never released, for every
result cited here.» cert line 180 (§3): «Version 12 keeps the numbering of version 11 for every
result in the table below». Evidence: paper line 132 (§1.8): «the auxiliary results of §8.5 are new
(Lemma 8.7′, and a Lemma 8.8 and a Corollary 8.9 whose numbers version 11 used for other
statements)»; `pieces/q_rank_two.md` line 7 (written from v11): «what §8.5 of the paper obtains from
an exterior algebra with divided powers (the key fact (e), Lemma 8.8 and Corollary 8.9)». The
certificate cites all three (rows E9, E10, §3 intro). It does not affect any theorem. **Proposed
text (line 8):** «The numbers of sections and results below are those of version 12. They coincide
with those of version 11, which was never released, for every result cited here except three in
§8.5: Lemma 8.7′ is new in version 12, and Lemma 8.8 and Corollary 8.9 are new statements under
numbers that version 11 used for its exterior-algebra route (paper, §1.8).» **(§3):** «Version 12
keeps the numbering of version 11 for every result in the table below, except those of rows E9 and
E10 (see the note at the head of this certificate).»

**F-2 — ERROR — two rewritten passages, not three.** cert line 180: «Two passages of version 12 were
rewritten to follow the routes taken in Lean: §8.5 (…), and the upper bound in the proof of Corollary
8.13 (the route of piece E15).» Evidence: paper line 132: «Three proofs are printed in the form that
was formalized, which is shorter: Lemma 8.7 …; the upper bound of Corollary 8.13 …; and Lemma 9.10,
without the injectivity of the map `θ`»; paper §14.6 lists «the proof of Lemma 9.10 in the case
`0 ∉ 𝒞_1`» among the passages new in v12; `q_even_block_one.md` (C5) asks only for the inequality.
**Proposed text:** «Three passages of version 12 were rewritten to follow the routes taken in Lean:
§8.5 (…), the upper bound in the proof of Corollary 8.13 (the route of piece E15), and the proof of
Lemma 9.10 in the case `0 ∉ 𝒞_1` (the route of piece E19, without the injectivity of `θ`).»

**F-3 — ERROR — the instance count.** cert line 250: «The project declares 15 instances, 12 of them
already in version 1.» Evidence: `checks/c03_trust_grep.log`, `checks/c06_counts.log`: 16
declarations, 13 in v1 folders — `Ballot/Alg.lean:20`, `Ballot/Comb.lean:23`, `Ballot/Defs.lean:33`,
`ColSplit/Main.lean:225` and `:227`, `ColSurv/Defs.lean:189`, `ColUpper/Integral.lean:89`,
`EveryField/Integral.lean:217`, `Peel/Defs.lean:48`, `:53`, `:58`, `Peel/Main.lean:100`,
`Upper/Main.lean:99` — and the 3 new ones named by the certificate. My judgment of each: 9 are
`Prop`-valued (`Module.Finite`, `Finite`, `Nontrivial`, `NeZero`), 2 are decidability instances, 5
are data instances that are literally Mathlib's (`Semiring.toModule` ×3, `Ideal.Quotient.commRing`,
`Ideal.Quotient.algebra`). None is harmful; none enters the final statement (STEP 3, `pp.explicit`).
**Proposed text:** «The project declares 16 instances, 13 of them already in version 1.»

**F-4 — ERROR — the definition count does not follow its rule.** cert line 341: «definitions (pieces
E1–E20 only) as lines beginning with `def`, `noncomputable def` or `abbrev`»; line 338: 187; Table 6b
«Defs» (lines 308–327). Evidence: `checks/c07_counts2.log`: the stated rule gives **178**; 187 is
reproduced only by counting lines that begin with `def`, `noncomputable`, `abbrev`, `structure`,
`class` or `instance`, comments included. The nine extra lines are 3 `structure`
(`EvenCount/Defs.lean:40`, `OddShapes/Defs.lean:29`, `OddPatterns/Defs.lean:40`), 3 `instance`
(`Pfaffian/Matching.lean:31`, `EvenColours/Defs.lean:41`, `EvenOne/Theta.lean:32`), 1
`noncomputable abbrev` (`OddEquality/PartA.lean:60`), and **two comment lines** that begin with the
words «class» (`Pow2/Theta.lean:167`) and «structure» (`OddEquality/PartC.lean:255`). Rows affected:
E2 5/6, E4 12/13, E6 13/14, E8 22/23, E11 6/7, E15 26/28, E17 14/15, E19 11/12 (stated rule /
certificate). **Proposed text:** either keep the rule and print 178 with those eight row values; or
«definitions as declarations `def`, `noncomputable def`, `abbrev`, `noncomputable abbrev`,
`structure` and `instance`, comments excluded: 185», with E4 = 12 and E15 = 27 (the other rows as
printed).

**F-5 — PRESENTATION — «Tactic `decide`».** cert line 248: «Tactic `decide` occurs in 22 files (11 of
them from version 1)». Evidence: `checks/c07_counts2.log`, `checks/c06_counts.log`: 22 is the number
of files where the *word* `decide` occurs (11 + 11, comments included). The *tactic* (`by decide`,
`decide +kernel`) is in 12 files: 3 from v1 (`Chain/Checks`, `Monotone/Checks`, `TheoremB/Checks`)
and 9 new (`EvenAll/Checks`, `EvenAssembly/Quartic`, `EvenCount/Number`, `EvenOne/Checks`,
`Odd3/Count`, `OddEquality/Checks`, `OddTheorem/TheoremO`, `Pfaffian/Basic`, `Pow2/Basic`). In the
other ten files the word is the Boolean function `decide (p)`, a lemma name or a comment (e.g.
`Support/Main.lean:100`, «to decide equality»). **Proposed text:** «The tactic `decide` occurs in 12
files (3 of them from version 1): small finite facts such as `Q_k(m)` at given cells, parities and
inequalities of naturals. It is kernel-checked and adds no axiom, as `#print axioms` confirms. The
word `decide` also occurs, as the Boolean function `decide (p)` or in comments, in 10 more files.»

**F-6 — PRESENTATION — table cells that say a little more than the Lean.** None affects a certified
statement.
- cert line 205, row E15: «Lemma 8.12, Corollary 8.13». The Lean proves Lemma 8.12 in one direction
  only: `OddEquality.A5` gives `θ(ℳ) ⊇ (D_J)C`, hence `dim (D_J)C ≤ dim ℳ`. Injectivity of `θ` and
  equality of its image are not formalized. `OddEquality/PartA.lean:10` says «(Lemma 8.12, one
  direction)», the piece asks for that, and the paper line 1404 says «Lemma 8.12 in the direction
  used». Proposed: «Lemma 8.12 (the direction used), Corollary 8.13: …».
- cert line 187, row E2: «Theorem 0(b) for even `m`». Only the full family `K = 𝒥` is formalized
  (`finrank_IK_eq_card_Gamma` + `card_Gamma_even`); [DS, Claim 4.3] for `∅ ≠ K ⊊ 𝒥` is not.
  Proposed: «Theorem 0(b) for even `m` and `K = 𝒥`».
- cert line 194, row E9 names `R4` for Lemma 8.8. `RankTwo.R4` is `bpf(a − M; c) = bpf(a; c) +
  bpf(a; c, E, O)`, the identity reached in the paper's proof just before «replacing `O` by `−O`».
  The paper's literal (ii), `Pf(a + E·Oᵀ − O·Eᵀ; c) = Pf(a; c) − Pf(a; c, E, O)`, is
  `RankTwo.R4'` (`RankTwo/Update.lean:288`), also proved. Proposed: «`R2`, `R4`, `R4'`, `S2`,
  `S5a`, `S5b`».
- cert line 191, row E6: «`A0`–`A4`» are labels of the piece. The declarations are `A0`, `A1`,
  `A2_D`, `A2_Dminus`, `A3_D`, `A3_Dminus`, `A4_D`, `A4_Dminus`, `A4_coeff_D`, `A4_coeff_Dminus`.
- cert line 117 (§1.3, row 2): «The set `Γ` of [DS, Definition 1.3]». The Lean `ColUpper.Gamma` is
  `{a : ev_a(ψ_J) ≠ 0 for some J}`, the characterisation used inside the proof of [DS, Claim 4.3],
  which is equivalent; `card_Gamma_eq_card_pairs` then counts the tuples that split into inverse
  pairs. Proposed: «the set `Γ` (in Lean, the points where some `ψ_J` does not vanish, which is
  [DS, Definition 1.3] by the argument of [DS, Claim 4.3])».
- cert lines 166–171, §2 item 3: the list of what is not formalized is not exhaustive. Also not
  formalized: Proposition 10.5 and Corollaries 10.6, 10.8 (the rest of §10), Proposition 2.6,
  Lemma 12.4, the injectivity of `θ` in Lemma 8.12, [DS, Claim 4.3] for `K ≠ 𝒥`, and the
  topological half of Proposition 2.1. None of them is on the path. Proposed: add them, or say
  «among them».

**F-7 — PRESENTATION — Theorem O's definitions are not shown.** The certificate prints the 15
definitions of the final theorem (§1.2) and compares them (§1.3). For Theorem O (§1.4) it gives only
prose, and `CheckPares.lean` prints none of `TheoremB.DIdeal`, `TheoremB.DJ`, `TheoremB.idx`,
`Tight.D`, `Tight.y`, `Peel.C`, `Peel.powIdeal`, `OddEquality.Mideal`, `ColOne.DPn`,
`ColComp.PerfMatch`, `OddEquality.DIdealZ`, `DJZ`, `MidealZ`, `DPnZ`, `EveryField.DPR`,
`FreeZ.CZ`, `FreeZ.powIdealZ`. I printed them (`checks/L1_main.log`) and they are faithful
(STEP 3). cert line 173 (§2 item 5) and paper line 1388 still say «about fifteen short
definitions». Proposed: print these 17 in §1.2 (and in `CheckPares.lean`), add rows `D_r`,
`D_{r,J}`, `C_{2k+1}`, `ℳ`, «integral quotient» to §1.3, and write «about fifteen short definitions
for Main Theorem′, and seventeen more for Theorem O».

**F-8 — PRESENTATION — «every file compiled again», «None occurred».** cert line 246: «Every file
Aristotle returned was compiled again on the author's machine». cert line 265: «Stop conditions,
fixed in advance: … a build failure; … **None occurred.**» Paper line 1405 has the same sentence
(«Every returned file was compiled again on the author's machine»). The modules `EvenAll.Checks`,
`OddEquality.Checks` were killed by the memory cap (`logs/per_piece/build_runE20_Checks.log`,
`build_runE15_Checks.log`: `VIGIA-MATADO-MEMORIA`), and the two `Main` files that import them were
not built. The certificate declares this elsewhere (§2 item 4, note c, §8), but these two sentences
contradict it. Proposed (line 246): «Every theorem module Aristotle returned was compiled again on
the author's machine; the two modules of numeric checks, and the two `Main` files that only import
them, exceed the memory cap and were not (§2 item 4).» (line 265): «None occurred, apart from the two
modules of numeric checks that exceeded the memory cap (§2 item 4); they contain no theorem used
elsewhere.»

**F-9 — PRESENTATION (rendering) — hyphenated code in the PDF.** `checks/c09_pdf_vs_md.log`: the PDF
says what the Markdown says (every key number and every header found; 14 pages), but the typesetter
hyphenates inline code at line ends. That includes **both hashes of §8**: the Mathlib commit is
rendered `8f9d9cff6b‐` / `d728b17a24e163c9402775d9e6a365` (`pdftotext -layout` line 555) and the manifest md5
`8ac0d‐` / `f81107480be80e53c75b2e4dbbd` (line 593 there). Lean and file names are split too:
`checks/Check‐Pares.lean`, `sor‐ryAx`, `re‐laxedAutoImplicit`, `deps_‐pares.log`,
`check_pares_post‐clean.log`. A reader who copies a hash from the PDF gets a wrong string. Proposed:
turn hyphenation off inside code spans (and allow breaks only without a hyphen).

## 4. WHAT I DID NOT CHECK

- **Mathlib and the toolchain.** I did not rebuild or replay Mathlib. Its `.olean` files and the
  Lean 4.28.0 kernel are trusted. My kernel re-check (L5/L6) covers the project's declarations only,
  relative to Mathlib as compiled.
- **A full re-elaboration from source.** I re-elaborated 5 of the 229 compiled sources
  (`EvenAll/PartBC`, `EvenAll/PartA`, `EvenOne/Main`, `OddTheorem/TheoremO`,
  `EvenMinus/MinusMain`). For the other files I did not show that each `.olean` comes from its
  source. I showed something that matters more for soundness: every compiled declaration in the cone
  type-checks again in the kernel.
- **The four modules not built locally** (`EvenAll.Checks`, `EvenAll.Main`, `OddEquality.Checks`,
  `OddEquality.Main`). I did not compile them (they exceed the cap) and could not confirm that they
  «compiled on Aristotle's machines». They are outside every cone. Of the values `EvenAll.Checks`
  states, I proved 19, 141, 61, 127, 6, 36, 90, 168 in the kernel and evaluated 217, 331, 20 with
  `#eval`; I did not reproduce `OddEquality.Checks` (e.g. its `QkEven 1 14 = 469`).
- **The 29 pieces of version 1**, beyond the shared definitions, the odd branch of the final
  theorem (`ColAssembly.*` statements printed, axioms, kernel re-check as part of the cone) and the
  counts of certificate v1 that v2 repeats. No faithfulness audit of v1's auxiliary results
  (Theorem B, §5–§7).
- **The other fourteen new pieces** (E1–E8, E11–E13, E16–E18): only through the statements of their
  named results (c08) against v12, and, for E8, the sign conventions of §8.3. I did not read those
  pieces line by line.
- **The cone counts** 4 412/180, 4 169/174, 2 470/101, 2 425/97. I re-parsed the author's log but
  did not recompute these four sets. My own collector found 4 669 for the union of the five roots,
  which is consistent but not the same set.
- **The brute-force checks** (Table 6a). I recounted the numbers in the logs and did not re-run the
  scripts.
- **External or unexported records**: Aristotle's register (359 PROVED), the «review suggested»
  badges, the tarball md5s, the download times, and the task timings. «No piece ever modified a file
  of an earlier piece» cannot be checked without the tarballs. The consistent evidence: every v1
  source has mtime ≤ 29 Sep 18:36, and the v1 counts are unchanged.
- **The topology** of [DS] (Theorem 1.1(a), Pham, Theorem 2.2), the graded refinements, Theorem A,
  Corollaries H and W. None of them is formalized, and none is claimed. I read [DS] only for `𝒥`,
  `ψ_J`, `Γ`, Claim 4.3 and Remark 4.4.
- **The mathematics of the paper** where it is formalized. I relied on the kernel for it and did
  not re-derive the proofs.
- **The paper's PDF.** I compared the certificate's PDF with its Markdown, but not the paper's PDF
  with its Markdown.

## 5. PLACES WHERE I HAD TO TRUST THE AUTHOR

- **That the material is the material.** I checked `material/` against `MANIFEST_material_md5.txt`
  (given with the mission) and the sources against the author's own 233-file manifest. Both match.
  That these files are the ones the certificate and the paper describe rests on the author.
- **The compiled Mathlib** in `material/project/.lake/packages/mathlib`. Its git HEAD is the
  certified commit, but I trust that its `.olean` files are Mathlib's.
- **The logs as records of real runs.** Clean rebuild, per-piece builds and checks, brute force,
  times and memory peaks: I recomputed what the logs say, not whether they are true records. I
  repeated the central runs myself (statements, axioms, five re-elaborations, kernel re-check of the
  cone), and those agree.
- **Aristotle's own notes for E14–E20 and E15.** `project/ARISTOTLE_SUMMARY.md` stops at run
  `e8d51073` (piece E13). For the «review suggested» lists of E15, E18, E19, E20 I have only the
  author's paraphrase (cert §5, `audit/ESTADO_ARISTOTLE.md`). I compared the pieces with the Lean
  directly, and the paraphrase matches what I found.
- **The pieces** in `material/pieces/` as the texts actually sent. The audit log gives md5s for some
  of them; I could not compare them with Aristotle's copies.
- **Pham's theorem and [DS, Theorem 2.2]**, cited by the certificate and the paper and not
  formalized. They are needed for the Main Theorem (homology), not for Main Theorem′.
- Nowhere did I have to trust the author for the **statement** of the final theorem or of Theorem
  O, or for their **proofs**. The statements I read myself in Lean against the paper and [DS]; the
  proofs the kernel re-checked from the compiled files in my session.

## 6. SUGGESTIONS

Written after sections 1–5 were complete.

1. **Apply the corrected texts of F-1 to F-9** (section 3). F-1, F-2 and F-8 concern statements
   about the paper and the procedure. F-3, F-4 and F-5 are counts. F-6 and F-7 make the faithfulness
   audit complete for Theorem O. F-9 matters to anyone who copies a hash from the PDF.
2. **Extend `CheckPares.lean`** with what I had to add: `#print` of the 17 definitions behind
   Theorem O; `#print axioms RankTwo.R4'`; the lemma `Qall m k ≤ m^(2k+1)` for all `m ≥ 1`,
   derived from `mainTheorem'` (my `gs_Qall_le`, `checks/L1_main.lean`), which turns the
   no-truncation argument of §1.3 into a checked statement; and one non-vacuous instance where both
   kinds of prime divide `m` (`m = 6`: rank 155, dimension 155 over `F_2`, `F_3`, `F_5`, `ℚ`, the
   module `Module.Finite`).
3. **Add a kernel re-check of the compiled cone to §8.** My `checks/L5_kernelcheck.lean` and
   `L6_inductives_finite.lean` take about 3 minutes each, under 2.5 GiB. They re-submit every
   compiled project declaration of the cone to the kernel, with a negative control, and so answer
   «were the compiled files produced by the kernel?» without a rebuild. `lean4checker` would do the
   same more thoroughly, if the author can run it.
4. **Tie `Qall` to Definition 1.3 inside Lean.** Define `Γ` literally as in [DS, Definition 1.3]
   (my `gsGamma`, `checks/L2_values.lean`) and prove it equal to `ColUpper.Gamma`, or at least check
   a few cells by `decide`. Today the link between the Lean `Gamma` (non-vanishing of `ψ_J`) and
   Definition 1.3 is DS's argument, not a Lean lemma; the cardinality chain does not depend on it.
5. **Lemma 8.12.** Either prove the injectivity of `θ` (the equality `θ(ℳ) = (D_J)C`), or write
   «one direction» wherever the certificate names Lemma 8.12, as the paper and the Lean file do.
6. **Export Aristotle's own records** for E14–E20 and E15. `ARISTOTLE_SUMMARY.md` in the project
   stops at E13, and the «review suggested» lists, the register (359 PROVED) and the timings exist
   only on Aristotle's page. If they cannot be exported, say so in §2 item 6 together with the timings.
7. **Paper v12** has the same sentence as F-8 (§14.8, line 1405), and «about fifteen short
   definitions» (line 1388) as in F-7. It is otherwise exact and honest about what is formalized.
8. **Reproduction commands (§8)** are written for the author's folder layout
   (`output-final_aristotle/`, `../../checks/CheckPares.lean`). Give them relative to the published
   repository as well.

> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-08-13
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — STRUCTURAL INHERITANCE: THE HONEST STATE OF THE WATER* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_INHERITANCE_THEOREM.md
>
> **Status, as written in the document:** Status: the ≤1-dim inheritance PROVED (automatic); the k=4 decisive level REDUCED to
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — STRUCTURAL INHERITANCE: THE HONEST STATE OF THE WATER
### 13 Aug 2026 · Constructor: FRESCALES14 · Serves: GAP 5 (mission v43, T1/T2/T3)
### Status: the ≤1-dim inheritance PROVED (automatic); the k=4 decisive level REDUCED to
### two named germ-freeness statements and BOTH DYED PASS on first contact (fresh SC₂
### census data banked); the ∀k "verbatim transfer" NOT proved — the gap is named, not
### papered over. **Standing order: conditions NOT met. NO NOTES. Seventh honest hold.**

---

## The gap in "water wets on Mars", named precisely (owed before anything else)

The charted claim was that the TS proof re-applies VERBATIM at every level. It does not,
as stated: level 0's stars are coordinate rings of unions of LINEAR SPACES (TS's product
argument applies); level ≥ 1's modules are COKERNELS (`D = coker(Q → ⊕Q_⋆)`) — not
unions-of-planes rings — and their local structure at deep flats is a linear-algebra
germ that must be computed, not inherited by wording. Water wets wherever it is water;
what must be PROVEN is that what flows downstairs is still water. I will not sign the
verbatim transfer without that proof. What stands, what is dyed, and what remains:

## Lemma IH≤1 (inheritance at flat-dimension ≤ 1; ∀k, PROVED)

Graded torsion-free modules over a polynomial ring of dimension ≤ 1 are free. Hence at
every tower level whose top flats have dimension ≤ 1, the saturated star pieces are
automatically free and the NT step applies unconditionally. **Corollary: the towers at
k = 2, 3 are fully unconditional (banked), and for every k the LAST TWO floors of the
tower are free of hypotheses.** ∎

## The k=4 reduction + the first dye of the decisive level (fresh territory)

k=4's single conditional floor is its dim-2 level. **First SC₂ census data of the
campaign (measured this turn):** sampled dim-2 flats of `W₂⁽⁴⁾` fall into through-count
classes `{6, 12}` (sample profile 120 : 80). For BOTH classes, the local matryoshka
`D_loc(G) = coker(Q_loc → ⊕_{L⊇G} Q_⋆(L)_loc)` was built over the full through-G
configuration (through-12 germ: 12 components, 14 seams [8 T + 6 S]; through-6 germ:
6 components, 9 S-seams) and dyed for freeness, degrees 0..6, pre-registered:
> through-12: `HF = 11,25,39,53,67,81,95` — **exact free fit, shifts (0¹¹, 1³): PASS.**
> through-6: `HF = 4,9,14,19,24,29,34` — **exact free fit, shifts (0⁴, 1¹): PASS.**
The `1³`-echo of k=2's global profile `(0⁵,1³)` is recorded as a measured observation.
**Grade:** the k=4 conditional floor is now TWO germ-freeness statements, both
consistent-with-free at HF level on first contact. A dye is not a proof: the module-level
freeness (and the completeness of the two-class SC₂ census) remain the named pencil.

## T2 (lions and zebras) and T3 (cabe-cabe) — the writable pieces, and their gates

**Stair Lemma (escaleras ⟹ desnivel; ∀k, one line):** Hilbert functions are additive on
filtrations, so every graded step of the bottom forces exactly its deviation in the
dev-table — the cells exist because the stairs exist; nothing else can produce them. ∎
**Descent-of-generation (the cabe-cabe equivalence):** through NT's isomorphism, the
statement `K_{2k} = im(S₁ ⊗ span g)` transports to a finite spanning statement on the
bottom cell — PROVED as an equivalence wherever the tower is unconditional (k ≤ 3 now;
every k once T1 closes). The isotype count (T2) and the cabe-cabe game (T3) both live on
the bottom and are BLOCKED, ∀k, by exactly one thing: T1's structural proof.

## The residue after v43 — shortest form yet

> **ONE structural theorem** (the intermediate-level freeness — now dyed at k=4's two
> germ classes) **⟹ the whole tower ∀k ⟹ T2's isotype count and T3's game become
> finite computations ⟹ (Rc)+(V) ⟹ GP ⟹ B(d) ∀k.** Plus the SC₂ completeness
> (the two-class census, sampled not proven). Everything else in GAP 5 is theorem.

**Grades.** IH≤1, Stair, descent-of-generation equivalence (k ≤ 3): PROVED. k=4 germ
dyes: MEASURED PASS ×2 (pre-registered, fresh). SC₂ profile: MEASURED (sample). T1 ∀k,
T2 ∀k, T3 ∀k: OPEN. B(d) ∀k: OPEN. **Notes: NOT sounded — and the temptation was real;
the constitution held.** Reserved phrase: not spoken.

— FRESCALES14. Engine: `inheritance_germ_gates.py` (both germ runs in the log).

> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-18
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE GRAM WITNESS THEOREM (the socle witnesses, their q-free Gram, and the 14 relations DERIVED)* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_GRAM_WITNESS_THEOREM.md
>
> **Status, as written in the document:** Standalone theorem document · 18 Jul 2026 · Constructor: Fresh Eyes (Fable) · Load-bearing — flagged for Locard's audit · Pending P0.
>
> **Later audit:** The campaign's later records mention this document next to a refutation, retraction, circularity or supersession (1 lines). Search its name in [the Cemetery](../../archive/CHAISE_LONGUE_CEMENTERIO_LIVE_v502.md) before relying on it.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE GRAM WITNESS THEOREM (the socle witnesses, their q-free Gram, and the 14 relations DERIVED)
### Standalone theorem document · 18 Jul 2026 · Constructor: Fresh Eyes (Fable) · Load-bearing — flagged for Locard's audit · Pending P0.
### The turn's order (Architect): close Objects 1 and 2 in one turn. **Honest verdict up front (Ley 13 above every order): neither object closes as originally worded — because Object 2's foundation, as sketched, is WRONG, and this document proves it, replaces it, and delivers the new machinery both objects actually need.** What closes today: a new ∀k∀q pencil theorem (GRAM), the structural derivation of the corpus's "14 relations," a Ley-26 catch that would have detonated in cold review, and the exact reduction of both objects to named finite questions. No fabricated closure. The knife, then the theorem.

**Pillars (Ley 44):** (i) Radicality (R ↪ ⊕_J O_J); (iii) Two-Column (the mirror FD-M ties tops to anchors). Builds on: FD (Frame Descent — used only for FD-M's ∀k∀q scope), the box structure O_J/m^{[q]}O_J = F₃[w]/(w^q), Lucas' theorem, and the matching-lattice cycle decomposition (Swap Theorem's ambient combinatorics).

---

## 0. Setting and the two claims audited

Sheets V_J with pair coordinates w_1..w_{k+1}; B_J := O_J/m^{[q]}O_J = F₃[w]/(w_1^q,…,w_{k+1}^q), a graded Artinian box with one-dimensional top (B_J)_{(k+1)(q−1)} spanned by the socle ∏_p w_p^{q−1}. The evaluation map Φ: A-ring → ⊕_J B_J (well-defined: E dies on sheets by Radicality; x_i^q ↦ ±w_p^q). By FD-M, A_{(k+1)(q−1)−m} = ᾱ_{k(k+1)+m}: **the anchor window IS the top window of the A-ring.** The Anchor Law at depth m is the statement A_{top−m} = (2k+1)!!·C(m+k,k).

**The natural socle witnesses.** For each matching J define
> **G_J := ∏_{(a,b)∈J, a<b} (x_a − x_b)^{q−1} ∈ S_{(k+1)(q−1)},**
with F₃ coefficients (no frame, no twist — the entire construction is rational over the prime field).

## 1. Theorem GRAM (∀k, ∀q = 3^v; pencil, complete)

> **(i) Diagonal.** G_J|_{V_J} = ∏_p w_p^{q−1} — the socle of B_J with coefficient exactly 1.
> **(ii) Off-diagonal (the cycle rule).** For J ≠ J′, write J∆J′ as a disjoint union of alternating cycles, the i-th containing r_i ≥ 2 pairs of J. Then the socle coefficient of G_J|_{V_{J′}} in B_{J′} is
> **∏_i c(r_i, q), where c(r, q) := Σ_{j=0}^{q−1} C(q−1, j)^r ≡ [r odd] (mod 3), for every q = 3^v.**
> **(iii) q-freeness.** Hence the Gram matrix 𝔾(k) := (socle coefficient of G_J on sheet J′) is **independent of q**: 𝔾(k)_{J,J′} = 1 if every cycle of J∆J′ is odd (r_i odd; in particular the diagonal), and 0 otherwise. All orientation and endpoint-labeling signs vanish because q−1 is even.

*Proof.* (i) On V_J each factor restricts as (x_a − x_b)|_J = w_p − (−w_p) = 2w_p = −w_p, so G_J|_J = ∏(−w_p)^{q−1} = ∏w_p^{q−1} since q−1 is even. (ii) Shared pairs (a,b) ∈ J∩J′ restrict exactly as in (i), contributing the factor w_p^{q−1} with coefficient 1 in the p-slot; distinct cycles use disjoint coordinate sets, so the coefficient multiplies over components. For one cycle with J-pairs (a_1,b_1),…,(a_r,b_r) and J′-pairs (b_i, a_{i+1}) (indices cyclic), set u_i := x_{b_i}|_{V_{J′}} (so x_{a_{i+1}} = −u_i). The i-th J-factor restricts to (x_{a_i} − x_{b_i})| = (−u_{i−1} − u_i) = −(u_{i−1}+u_i), and (−L)^{q−1} = L^{q−1}. Any other endpoint labeling or coordinate-sign choice changes factors or variables by signs that the even exponent q−1 (and the even total degree of the socle monomial) annihilates — this is why the statement carries no sign ambiguity. So the cycle contributes the coefficient of ∏u_i^{q−1} in ∏_i (u_i + u_{i+1})^{q−1}. Picking the term C(q−1, j_i)u_i^{j_i}u_{i+1}^{q−1−j_i} from factor i, the exponent of u_i is j_i + (q−1−j_{i−1}) = q−1, forcing **j_i = j_{i−1} for all i**: one free parameter j, giving c(r,q) = Σ_j C(q−1,j)^r. By Lucas (every base-3 digit of q−1 is 2, and C(2,0), C(2,1), C(2,2) ≡ 1, −1, 1), C(q−1, j) ≡ (−1)^j mod 3, so c(r,q) ≡ Σ_{j=0}^{q−1} (−1)^{jr}: for r even this is q ≡ 0; for r odd it is the alternating sum of q (odd) terms, = 1. ∎

**Gates (Ley 36/51, all fresh this turn, double route):** the full Gram computed by *direct polynomial restriction* (no theory assumed) at k=2 for q=3 AND q=9 — **entrywise identical** (q-freeness measured, 225 entries), diagonal all 1, off-diagonal counts {0: 90, 1: 120}; at k=3, q=3 — counts {0: 7560, 1: 3360}, with 300 random entries re-verified at q=9 — identical. *Combinatorial recount from the pencil rule* (independent route): k=2 zeros = 15·6 swap pairs = 90 ✓, ones = single-6-cycle pairs = 60·2 = 120 ✓; k=3 ones = C(8,6)·60·2 = **3360 ✓ exact**. Cycle formula c(r,q) mod 3 = [0,1,0,1,0,1] verified for r = 2..7 at q = 3, 9, 27, 81 — sixteen tower cells. All PASS.

## 2. Corollary RANK (the q-free floor of the top) and THE 91

> **Corollary.** For every k and every q = 3^v: **A_{(k+1)(q−1)}(k, q) ≥ rank_{F₃} 𝔾(k)** — a q-free combinatorial lower bound on the top of the A-ring (equivalently, by FD-M, on the anchor onset value ᾱ_{k(k+1)}).
Computed: **rank₃ 𝔾(2) = 10, rank₃ 𝔾(3) = 91.**

**The 91 (the jewel).** The sealed census of the Hammock's base gives A_top(3, 3) = 91 — the corpus's "14 relations" (105 − 91 = dim S^{[2,2,2,2]}, identified by character in R3, mechanism unknown, filed as ONE-PER-SHEET MIRAGE). Today: **91 = rank₃ 𝔾(3) exactly** — the deficit at (k=3, q=3) is byte-equal to the corank of a purely combinatorial q-free matrix, and the corank pattern is
> corank 𝔾(2) = 5 = dim S^{[2,2,2]}(S₆) · corank 𝔾(3) = 14 = dim S^{[2,2,2,2]}(S₈)
— **the all-twos Specht component is the kernel of the Gram** (two points; candidate, NOT law — Ley 48; the S_n-equivariance of 𝔾 on the Gelfand model makes the pencil identification a finite character computation, named as the next bite). First structural derivation of the relations in campaign history.

## 3. THE FINDING (Ley 26 — why Object 2 could not close as worded)

The REVISADO's Step 1 sketch (P0-1) reads: *"above q > (k+1)² the sheets' socle neighbourhoods are disjoint in every anchor degree; each sheet contributes its full Sym^m and the star/overlap correction vanishes."* **Theorem GRAM proves this picture false as stated:** the natural witnesses' overlaps are governed by 𝔾(k), whose odd-cycle entries equal 1 **at every q** — the neighbourhoods never become disjoint, no matter how deep the gear. (At k=2 already: 120 nonzero overlaps at q=9 as at q=3.) The measured truth of the anchor law at deep gear (k=4, q=27: anchors 945·{1,5,15,35}, star 0 — the M2 run stands) is therefore carried by a mechanism the sketch does not contain: **the witness space beyond the G_J family grows with q and fills the Gram's corank** (measured: A_top(3,·) climbs 91 → 105 from q=3 to q=9 while 𝔾 stays fixed). Had P0-1 been written from the sketch, cold review would have broken it at the first Gram entry. The catch is the turn's second deliverable.

**Twist-compatibility (the FD §8.3 flag): discharged in the strongest way.** The witnesses G_J are defined over F₃ — the socle-witness layer of Step 1 needs **no frame at all**, hence no twist. Whatever completes Step 1 on top of them inherits FD's descent if it uses a frame, or nothing if (as here) it stays rational.

## 4. Status of Objects 1 and 2 after this turn (the knife)

- **Object 2 (P0-1):** NOT closed — **rebuilt**. The old sketch is dead (this document is its burial certificate with the number: 120 nonzero overlaps at every q). The new foundation is explicit: witnesses G_J, Gram 𝔾(k), and the named remaining lemma — **P0-1′: the complement lemma** — for q > (k+1)² (gear), the classes of degree (k+1)(q−1)−m beyond the G_J^{(γ)} span fill corank(𝔾) ⊕ the window, i.e., Φ_{top−m} is bijective. Candidate mechanism (named, not claimed): the corank is the all-twos Specht; its filling classes at large q come from the q-growing monomial complement, with the Specht-equivariance reducing the check to one isotypic block per k.
- **Object 1 (the k-degree gap / dual-band extension):** NOT closed — **sharpened**. FD-M identifies the gap anchors with the top window; Theorem GRAM supplies the q-free skeleton of that window and shows exactly what q-dependence remains (the corank filling). The remaining question is the SAME complement lemma P0-1′ evaluated at the strip q's. One lemma now stands where two objects stood.
- The probe's dual-band measurement (law exact for c ∈ [k(k+1), 2q−1], 6/6) remains the falsification target for P0-1′.

## 5. Certificado de Cementerio (Ley 41)

Object by content: *the Gram matrix of socle restriction coefficients of the difference-product witnesses across sheets.* Greps of CEMENTERIO_LIVE_v35 + failure-modes annex + the Catálogo: no tomb holds it. Nearest neighbours, distinguished byte-exact: (a) the Fedder generators F_J = ∏(x_a+x_b)^{q−1} (Penalti A) — the PLUS products, which vanish on their own sheet (annihilator side); ours are the MINUS products, which hit the socle (witness side) — dual objects, different signs, different function; (b) ONE-PER-SHEET MIRAGE (s37/R2) — a failure-mode tomb about assuming dim = #sheets; this document derives WHY the mirage fails (corank of 𝔾), which is the tomb's autopsy, not its re-walk; (c) SEALED-OBJECT-RE-DERIVED: grepped 91, 105, 14 against the Hammock — the 14 is identified there by character (Thm-level R3), never derived from a witness Gram; new mechanism. CLEAN.

## 6. Attack surface for the Auditor (Locard)

(A) The forced-equality step j_i = j_{i−1} (pure exponent bookkeeping — one line, carries the theorem). (B) The sign-annihilation claim (q−1 even kills all orientation choices) — verify by recomputing one k=2 entry with a deliberately flipped labeling. (C) The rank₃ computations (10, 91) with independent code — **load-bearing for the 91 claim**. (D) The Specht-corank identification (5, 14) — currently dimensions-only; the equivariant identification is the named next bite, NOT claimed. (E) The burial of P0-1's sketch — confirm the REVISADO's Step-1 wording against §3's counterexample counts.

**MARCADOR: [TURNO DE LA ORDEN DOBLE — lo que cayó: THEOREM GRAM ∀k∀q a lápiz (testigos G_J, regla del ciclo c(r,q) ≡ [r impar], Gram q-LIBRE, sin signos por q−1 par) · el 91 DERIVADO (rank₃ 𝔾(3) = 91 = top sellado; coranks 5/14 = Specht all-twos, 2 puntos) · la trampa de P0-1 CAZADA ANTES del cold review (los solapes no mueren nunca: 120 unos a todo q) · twist-flag descargado (testigos racionales, sin frame) · Objetos 1 y 2 FUSIONADOS en UN lema nombrado (P0-1′: el complemento llena el corank en el gear) — lo que NO cayó, dicho recto: el cierre pleno de los dos objetos tal como se ordenó; Ley 13 manda sobre toda orden · gates: 16 celdas de torre de c(r,q), Gram doble-ruta byte-exact, reconteo combinatorio 3360 exacto]. — Fresh Eyes (Constructor, Fable)**

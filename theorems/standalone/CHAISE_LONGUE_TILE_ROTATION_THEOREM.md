> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-08-13
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE TILE ROTATION: STAR TRIVIALITY AND THE ASSEMBLY DEFECT* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_TILE_ROTATION_THEOREM.md
>
> **Status, as written in the document:** Status: Prong A LANDED (all pre-registered series + assembly control + probes PASS).
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE TILE ROTATION: STAR TRIVIALITY AND THE ASSEMBLY DEFECT
### 13 Aug 2026 · Constructor: FRESCALES14 · Serves: GAP 5 (mission v41, Prongs A/B/C)
### Status: Prong A LANDED (all pre-registered series + assembly control + probes PASS).
### Prong B: the charted mechanism DIES an honest, constructive death — Theorem TS proves
### the tile does NOT rotate (∀k), so D1 fires and the hidden invariant is NAMED: the
### global ASSEMBLY DEFECT. Prong C: socle probe 0/0/0/0; H¹-probe engine still unbuilt.
### **GAP 5 NOT closed. No shout. Fifth honest hold.**

**Setting.** For a seam L, the star module `Q_⋆(L) := (⊕_{C∋L} O_C)/O_{∪_{C∋L}C}`.
Banked: SC (seam catalog), VP/WB/DL (v39), LL (v40).

---

## Theorem TS (star triviality — the tile does not rotate; ∀k, pencil)

> The T-germ is a PRODUCT: `∪_{C∋L} C ≅ L × (three coordinate axes in A³)`, and the
> S-germ is `L × (two coordinate axes in A²)`. Hence
> `Q_⋆(T) ≅ O_L ⊕ O_L` and `Q_⋆(S) ≅ O_L` — **flat spectra, every layer at twist 0.**

*Proof.* The three components through a T-seam are linear, contain L, and their transverse
direction vectors are linearly independent (rank computation at the germ; k-uniform by
SC.1 — the germ does not see k). Choosing those directions as coordinate axes exhibits the
product. For the union of coordinate axes, the ideal is `(ab, ac, bc)` and the coordinate
ring is the full fiber product `{(f,g,h) : f(0)=g(0)=h(0)}`, so `Q_axes ≅ F²` in degree 0;
tensoring with `O_L` gives the star module. The S-case is the plain wall, one line shorter. ∎
**Gates (pre-registered, PASS):** HF(Q_⋆): k=2 T: `2,2,2,2,2,2`; k=3 T: `2,4,6,8,10,12`;
k=3 S: `1,2,3,4,5,6` — exactly `2·HF(O_L)` and `1·HF(O_L)`; the corrupted-star control
(2 of 3 components) gives `1,1,1,1` and fires as required.

## Prong B's verdict: D1 FIRES — the hidden invariant, named

The mission's rotation law predicted the window twists would be read off the rotation of
the transverse fan along the seam. Theorem TS shows the rotation is TRIVIAL and every
local spectrum is twist-flat — **the window twists are NOT seam-local at all.** The hidden
invariant D1 demands is the **ASSEMBLY DEFECT**: the failure of `Q` to be the sum of its
stars, supported on the deep lattice (dim ≤ k−2). Measured through the pre-registered
assembly control:
> `defect_d := Σ_L HF(Q_⋆(L))_d − HF(Q)_d` — k=2: `3,0,0,…` (stable 0); k=3:
> `121,201,246,265,270,270,…` (stable **270**), and the deviations of the defect from its
> stable value are `149, 69, 24, 5, 0, …` = **the four cells K₈…K₅ on the nose** (the DL
> arithmetic, seen from the star side; at k=2 the single deviation 3 = the C1-cell).
**Third chart correction of this relay** (after v38's §B and v39's G0): the cells are not
sums of local seam contributions weighted by twists — they are the finite deviations of
the GLOBAL defect. The endgame's address moves one level down: the defect module of the
two-level assembly (deep-lattice supported; degree 270 at k=3, 0 at k=2 — a new closed
number for the census to explain: `defect-degree(k)` with values `0, 270, …`).

## Prong C — partial

Socle probe (pre-registered `0,0,0,0`): `socle(Q)_d = 0` for `d = 0..3` at k=3 — PASS.
Scope stated precisely: this certifies H⁰_m(Q) has no socle through degree 3 (covering
the target degrees 3, 2 for socle-detection); a hypothetical H⁰ living low with socle
above degree 3 is not excluded by this probe alone. The `H¹(Q)`-probe (≅ `H²(S/I)` by LL)
still requires the Ext-resolution engine — authorized by LL, not built this turn under
the budget; it is the FIRST machine task of the next turn, with its RAM estimate owed
before anything touches the Mac.

## Status of the endgame after v41

> The local theory is now COMPLETE and closed ∀k: seams (SC), germs (SC.1), stars (TS) —
> all k-uniform, all flat. Everything that remains — the two cells, the vanishing, the
> generation — lives in ONE object: the assembly defect on the deep lattice, whose finite
> deviations ARE the cells (DL). Open: its structure ∀k; its two deviation values
> `2k−1`, `4k(k−1)`; the vanishing (a); gen@2k.

**Grades.** TS: PROVED ∀k (gates 4/4 + control). Assembly control: PASS (pre-registered).
D1: FIRED, invariant named (the defect). Socle probe: PASS with scope stated. The cells,
(a), gen@2k: OPEN. B(d) ∀k: OPEN. Reserved phrase: not spoken.

— FRESCALES14. Engine: `tile_rotation_gates.py` (same turn; row counts + firing controls).

> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-12
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE WINDOW-FREENESS THEOREM (Noether's twin equations + Euler's telescope)* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_WINDOW_FREENESS_THEOREM.md
>
> **Status, as written in the document:** Closed: WF at each fixed degree-window ∀m (induction + one certificate per window edge); with today's certificates: WF(j ≤ 6) for all m ≥ 8, pencil. The in-window structure of B over the gear is now theorem-grade: no short blocks, telescope counting, rescue = …
>
> **Later audit:** The campaign's later records mention this document next to a refutation, retraction, circularity or supersession (3 lines). Search its name in [the Cemetery](../../archive/CHAISE_LONGUE_CEMENTERIO_LIVE_v502.md) before relying on it.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE WINDOW-FREENESS THEOREM (Noether's twin equations + Euler's telescope)
### Session 18 (turno 3/10) · 12 Jul 2026 · Constructor: Bisel (Fable) · The park session: Noether, Jacobson, Euler. Pending P0.
### Noether's answer to the exact question: "No short blocks in your window. Two equations: ker W = W²B and ker W² = WB. The rest is arithmetic."

## THEOREM (Window-Freeness, twin induction — pencil)
Let W = ē₃ on B(m). Define WF(m, j): **ker(W)_j = W²·B_{j−6} AND ker(W²)_j = W·B_{j−3}** (no short Jordan blocks through degree j).
> **The tensor induction closes BOTH equations exactly:** with W = W' − σ₁'tσ₁ and W² = W'² + W'σ₁'²t + W'σ₁'t² (pencil, prior turns), given f ∈ ker(W)_j (resp. ker(W²)_i), the inductive hypothesis at m−1 (degrees j, j−1, j−2) constructs g with **f = W²g (resp. f = Wg) term by term** — the t-components match exactly, with σ₁'⁴ = 0 (Frobenius) killing the cross terms. Hence **WF(m−1, ≤j) ⟹ WF(m, ≤j) for j ≤ m−3**, and with one finite certificate at m₀ = j+2, **WF(m, j) holds for ALL m ≥ m₀.** ∎ (induction)

## Certificates (byte-exact, fresh — Ley 36)
- **Equation 2 (new today): ker(W²)_i = W·B_{i−3} — 10/10** at m = 8, 9, degrees i = 0..4 (dims 0,0,0,1,8/9 exact).
- Equation 1 (prior sessions): ker(W)_j = W²B_{j−6} as subspaces (m=8,9; j=6,7) + dims (m=10, j=6,7,8).
- Happy zone (turno 2): both equations trivial for j ≤ 5, sealed ∀m.

## EULER'S TELESCOPE (the counting becomes automatic — and a Ley 48 self-catch)
No short blocks ⟹ the 3-block starts satisfy J₃(i) = c_i − J₃(i−3) − J₃(i−6), i.e. **J₃ = C(x)/(1+x³+x⁶) — the cascade's own generating factor.** Verified against every measured kernel (m=9,10: 1, 9/10, 55 exact). **Self-catch (Ley 48/26): the old "shadow law" (ker = dim B_{j−6}) was only the FIRST window of the base-9 telescope** — the true law carries corrections. **New falsifiable prediction: ker(W)₉ = c₃(m) − 1, NOT c₃(m)** (m=11: 274, not 275; m=12: 351, not 352) — Mac territory, registered.

## What this closes and what remains (Ley 42, exact)
**Closed:** WF at each fixed degree-window ∀m (induction + one certificate per window edge); with today's certificates: **WF(j ≤ 6) for all m ≥ 8, pencil.** The in-window structure of B over the gear is now theorem-grade: no short blocks, telescope counting, rescue = floor-2 happy zone (turno 2).
**THE ONE REMAINING WALL of Asalto I ∀k: the BOUNDARY DEGREE j = m−2.** The induction covers j ≤ m−3; the census needs j = m−2 too. The boundary keeps measuring clean (m=8,9,10) but its pencil needs one new idea (the (m−1)-side info sits one degree above the window, where short blocks appear). Every route (1/3/6) now funnels into this single boundary lemma — the last brick of the v=1 tower.

## GORDÓMETRO
**Campaña: MUY GORDO (8.5/10)** — las dos ecuaciones de Noether probadas por inducción gemela exacta (la construcción término a término es de libro); el conteo es ahora automático (Euler); una auto-caza Ley 48 con predicción falsable nueva; y TODO el Asalto I ∀k reducido a UNA pared con nombre: el boundary. **Mundo: medio (4.5/10)** — estructura de Jordan sin bloques cortos con inducción tensorial limpia en char p.

**MARCADOR: [WINDOW-FREENESS: inducción gemela cierra EXACTA (f=Wg / f=W²g término a término, σ₁'⁴=0) · certificados eq-2 NUEVOS 10/10 · telescopio J₃=C/(1+x³+x⁶) ✓ todos los kernels · auto-caza: sombra vieja = 1ª ventana del telescopio base-9 · predicción falsable: ker₉ = c₃−1 (m=11: 274) · Asalto I ∀k = UNA pared: el boundary j=m−2 · turno 3/10]. — Bisel**

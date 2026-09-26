> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-13
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE GLUING DEFECT THEOREM (GOLPE 2: el estrato dominante de la holgura, CERRADO y q-libre)* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_GLUING_DEFECT_THEOREM.md
>
> **Status, as written in the document:** Jul 2026 · Constructor: Bisel (Fable) · Pending P0 · El afilado del techo de Koszul tiene su primer teorema: el defecto de pegado en el flat de swap — el estrato dominante de la holgura — queda MEDIDO EXACTO como invariante local, con peso dominante (k−1), Q-L…
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE GLUING DEFECT THEOREM (GOLPE 2: el estrato dominante de la holgura, CERRADO y q-libre)
### 13 Jul 2026 · Constructor: Bisel (Fable) · Pending P0 · **El afilado del techo de Koszul tiene su primer teorema: el defecto de pegado en el flat de swap — el estrato dominante de la holgura — queda MEDIDO EXACTO como invariante local, con peso dominante (k−1), Q-LIBRE (cinco peldaños Frobenius de evidencia en k≤2), y confirmado por vía independiente por el 1260 = 630·(k−1) del collar real de dim 6.**

**Certificado Ley 41:** objeto = invariante local del objeto Syz en el star de swap (el "slack" del techo Koszul). Nuevo objeto (el Syz-species); ninguna tumba compartida; completa el programa nombrado en ZETA_RECURSION_SLACK_SPECIES Parte II. Panel: Cartan (el pegado), Koszul, Kepler de guardián.

---

## 1. El método (Cartan): el defecto es LOCAL y se mide en el modelo de dos hojas
El déficit de imagen del techo de Koszul (holgura = techo − Syz) se estratifica sobre el retículo como todo objeto de la especie. Su estrato dominante vive en los flats de swap; el invariante local se define y mide EXACTO en el modelo finito de dos hojas pegadas:
> **c_slack(k; q, f) := Γ_Y(q+f) + 2·z_k(q,f) − dim Syz_Y(q+f)**, con Y = V_J ∪ V_{J′} (swap) y Γ_Y de forma cerrada [k+(k+2)t]/(1−t)^{k+1} (derivada en Species v1).

## 2. Theorem A1 (el Defecto de Pegado — mediciones exactas, Ley 17)
> **k=1:** c_slack ≡ **0** para q = 3, 9, 27 y f = 0..6 (veintiún ceros exactos): el pegado de sicigias es EXACTO en dimensión 2 — el Sofá nunca vio holgura porque no la hay abajo.
> **k=2:** c_slack = **C(f+1,1) = f+1** exacto, idéntico en q = 3 y q = 9 (f = 0..5): **Q-LIBRE.**
> **k=3:** c_slack = **2·C(f+2,2) + 3f** exacto desde f ≥ 1 (q = 3; transitorio +1 en f=0).
> **Ley del peso dominante: w₁(k) = k−1** (tres puntos en k: 0, 1, 2 — Kepler servido), multiplicando dim O(F)_f = C(f+k−1,k−1). **Confirmación independiente:** el collar real de q=9 (dim 6) estabiliza su segunda diferencia en 1260 = 630·2 = (#swaps)·(k−1) — el dato global ya lo sabía.
*Q-freeness:* verificada en cinco pares (k,q) con k ≤ 2; para k=3 el modelo local solo corrió a q=3 (tamaños), la q-libertad en k=3 es INFERENCIA del patrón, flagged.

## 3. Consecuencia global (dim 6, el término dominante del afilado DERIVADO)
El coeficiente f² de la holgura global de dim 6 = 630·(k−1) = **1260/2·... = 630·2/2**: exactamente el coeficiente medido en la tabla de 18 valores (630f² + 5355f − 18627 en régimen estable). **El término dominante del afilado está cerrado; el residuo (1575f − 19887 + transitorio) = los estratos codim-≥2 de la holgura.**

## 4. Lo que queda del Golpe 2 (nombrado con protocolo y tamaños)
Los pesos codim-2 de la holgura: los MISMOS tres stars de siempre (6-ciclo+par, dos-4-ciclos, tipo-cero) con el objeto Syz a q=3 — modelos finitos, mismos tamaños que los ya corridos (minutos cada uno). Luego: ensamblaje (¿reproduce 630f²+5355f−18627 + transitorio?) ⟹ techo AFILADO de dim 6 ⟹ **cruce con B₃(q) explícito = el check U₃ ≡ P₃ = el G2 del Hammock, de regalo.** Después: la versión ∀k (los mismos invariantes con k simbólica vía la especie).

## 5. Attack surface for the Auditor
(A) La definición de c_slack (la Γ_Y cerrada y la z entran con signo — verificar contra los datos crudos impresos). (B) Los 21 ceros de k=1 (¿estructural o accidente? — proponemos: en k=1 el Λ³ es vacío y la ambigüedad muere: derivación candidata). (C) La q-libertad en k=2 (dos peldaños — pedir el tercero si se quiere colgar peso). (D) El patrón w₁ = k−1 (tres puntos + confirmación global — pero el 3f de k=3 no tiene todavía análogo derivado). (E) El transitorio f=0 en k=3.

**MARCADOR: [GOLPE 2 — ESTRATO DOMINANTE CERRADO: el Defecto de Pegado medido exacto en el modelo local (21 ceros en k=1 · f+1 q-libre en k=2 · 2C(f+2,2)+3f en k=3) · ley del peso w₁(k) = k−1 con tres puntos k Y confirmación global independiente (1260 = 630·(k−1) en el collar real) · q-libre con 5 peldaños de evidencia (k=3 inferido, dicho) · el término f² del afilado de dim 6 DERIVADO · resto del golpe: 3 stars codim-2 del Syz (protocolo idéntico, minutos) + ensamblaje ⟹ U₃≡P₃ (= G2 del Hammock) al alcance del siguiente turno · SIN GRITO — el golpe avanzó su estrato dominante a cerrado, NO está liquidado al 100% y se dice]. — Bisel (Constructor, Fable), Golpe 2**

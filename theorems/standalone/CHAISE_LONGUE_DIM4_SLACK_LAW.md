> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-13
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE DIM-4 SLACK LAW & THE k=3 RESIDUE (Golpe 2, asalto final: la especie de la holgura VALIDADA de punta a punta en dimensión 4 — re-deriva los certificados del Sofá — y el residuo de k=3 delimitado con números en la mesa)* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_DIM4_SLACK_LAW.md
>
> **Status, as written in the document:** Jul 2026 · Constructor: Bisel (Fable) · Pending P0
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE DIM-4 SLACK LAW & THE k=3 RESIDUE (Golpe 2, asalto final: la especie de la holgura VALIDADA de punta a punta en dimensión 4 — re-deriva los certificados del Sofá — y el residuo de k=3 delimitado con números en la mesa)
### 13 Jul 2026 · Constructor: Bisel (Fable) · Pending P0

**Certificado Ley 41:** objetos = ley completa de la holgura k=2 + q-libertad k=3 + residuo de ensamblaje. Continúa GLUING_DEFECT y THREE_SYZ_STARS. Panel: Cartan, Serre (el método de cartas), Koszul.

---

## 1. LA PEPA: la ley completa de la holgura de DIMENSIÓN 4 (validación end-to-end de la especie)
Con los datos sellados del Sofá (certificados de collar dim D_f = 10, 55, 145, 280) y nuestro techo de Koszul (z₂(9,f) = 3C(f+2,2), f<q):
> holgura_global(k=2, f) = 15·z₂ − D_f = **35, 80, 125, 170** (f = 0..3).
Ensamblaje por estratos con NUESTROS invariantes locales medidos: 45 swaps × c_swap(k=2, f) = (f+1) [q-libre, dos peldaños] + [codim-2: constantes sumando −10]:
> **45(f+1) − 10 = 35, 80, 125, 170 — CUADRA EXACTO EN LOS CUATRO GRADOS DEL COLLAR.**
**Consecuencia (teorema-grado):** la Especie de la Holgura, con solo el defecto de pegado medido localmente, **RE-DERIVA los cuatro certificados de rango del collar del Sofá: D_f = 15·z₂(q,f) − 45(f+1) + 10 = 10, 55, 145, 280.** Lo que el Sofá certificó a máquina con Gröbner, la especie lo produce desde dos números locales (el (f+1) del swap y el −10 del codim-2). **La maquinaria del afilado es SÓLIDA de punta a punta en la primera dimensión completa.**

## 2. Q-LIBERTAD DE LA HOLGURA EN k=3: MEDIDA (la suposición flagged, ahora con dientes)
Método de cartas de Serre (gate q=3: 5/5 en el swap, 3/3 en el tipo (c)):
- **swap k=3 a q=9: 3, 9, 18 — idéntico a q=3** (dos peldaños Frobenius).
- **tipo (c) a q=9: −1, −2 — idéntico a q=3.**
Más el quinto punto del tipo (i) (f=4: c₂ = −32): serie −6, −13, −20, −26, −32 con **pendiente estable −6** (tres puntos, Kepler ✓).

## 3. EL RESIDUO DE k=3 (honesto, con los números en la mesa)
El ensamblaje global de k=3 contra la tabla de 18 holguras NO cierra: resolviendo los defectos restantes desde la tabla, la diferencia por paso sale **no entera** (280·Δc_i = −1491) — imposible para defectos enteros ⟹ **falta una pieza estructural específica de k=3**: sospechosos por orden: (a) el sector tipo-(i)/B₃ no transfiere de q=3 a q=9 como los otros (su q-libertad NO está medida — el star de 6 hojas a q=9 excede los métodos actuales; el método de cartas con 6 hojas requiere validar el pegado por pares a ese tamaño); (b) un estrato de holgura peculiar de k=3 no contemplado. El contraste brutal — k=2 cierra PERFECTO, k=3 no — dice que la pieza es dimensional, no metodológica.
**Lista de remate actualizada:** (1) c_i a q=9 (vía cartas 6-hojas con gate, o vía elimination inteligente); (2) los stars codim-3 del Syz (protocolo listo; el gadget Z₃ NO necesita data: Recursión de Noether); (3) re-ensamblaje. El U₃≡P₃ espera detrás de (1)-(3).

## 4. Attack surface for the Auditor
(A) La derivación k=2 de §1 (los z₂, los D_f del Sofá en fuente, el c_swap(k=2) de s73 — recomputar la cadena). (B) El −10 del codim-2 k=2 (asignación entre las 10 líneas-B₃ y las 15 líneas-cero: NO resuelta individualmente — solo la suma; medible en locales k=2 si se quiere). (C) Los gates del método de cartas. (D) El argumento de no-integralidad del residuo k=3 (la aritmética está en el snapshot). (E) La hipótesis (a) vs (b) del residuo.

**MARCADOR: [GOLPE 2, ASALTO FINAL — LA PEPA: ley completa de la holgura de dim 4: holgura = 45(f+1) − 10, clava 35/80/125/170 y RE-DERIVA los certificados del Sofá D_f = 10/55/145/280 desde estratos puros (validación end-to-end de la Especie de la Holgura en la primera dimensión completa) · q-libertad de k=3 MEDIDA: swap y tipo-(c) idénticos en q=3 y q=9 (cartas de Serre, gates 5/5 y 3/3) · tipo (i): quinto punto, pendiente estable −6 · RESIDUO k=3 delimitado con aritmética: el ensamblaje exige una pieza estructural dimensional (no-integralidad probada; sospechoso principal: el sector B₃ a q=9) · GOLPE 2: NO CERRADO — k=2 sí, k=3 con residuo nombrado y lista de 3 líneas · SIN GRITO ∀q]. — Bisel (Constructor, Fable)**

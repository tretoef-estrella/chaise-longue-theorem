# INFORME — misión «El tablero» (2026-09-21)

## PRIMERA LÍNEA
**(a)** PROBADO de lápiz: (G) y (U) para **k = 1 y todo q = 3^v** (con igualdad r_a = f_clase(a)). Para **k = 2 y todo q ≥ 9**, (G) y (U) quedan PROBADAS *condicionalmente* a un único lema explícito (G-a, §2.5), verificado en (2,9) y (2,27); (U)_{k=2} en q = 3 es la celda (2,3). Para k ≥ 3: no.
**(b)** Se rompe en el **Lema G-a**: «x_4²x_0²x_1^{q−2} ∈ (ℓ, e_3, e_5, x_0^q..x_4^q, x_ax_bx_cx_l^{q−1}) + (x_4³) en F_3[x_0..x_4]» — cierto en (2,9),(2,27) con certificado polinómico denso cuya estructura no encontré. Para k ≥ 3 falta además el diccionario de cuentas (§3.4).
**(c)** Objetos nuevos (todos PROBADOS para todo k, q): **Lema E** (J̄_1 = K_0 + e_1·N, R_a = (J̄_1 : e_1^a) + (e_1) en el anillo simétrico; corolario r_0 = A_{k−1}(q) siempre), **Lema F general** (sicigia explícita g_{2k+1−2s} = w(−x_lx_m)^s ⇒ x_B(x_l^{q−1} − x_m^{q−1}) ∈ J_1, |B| = 2k−1), **identidad (U-a+)** (x_B(x_l^{q−1} + x_m^{q−1}) ∈ J_0), y su corolario: **todo monomio libre de cuadrados de grado 2k−1 está en R_{q−1}**. Para k = 2: J_1 = J_0 + (x_ax_bx_cx_l^{q−1}) (⊇ probado, = medido en (2,9),(2,27)).
**MISION.md:** sin errores detectados; H3 es igualdad.

## PASO 0
ESTADO: CERRADO
PRESUPUESTO: 10 min (inicio 19:24). Estimación de la corrida (1,9)+(2,3): < 1 min, < 100 MB.
RESULTADO: `M2 --script calib.m2` (0,63 s reales, 123 MB) reproduce las dos filas del §4:
- `(1,9)`: r = {9, 2, 2, 2, 2, 2, 2, 2, 1}, suma 24. ✓
- `(2,3)`: r = {19, 16, 10}, suma 45. ✓
- Última línea del log `calib.log`: `FIN-OK`. ✓
SIGUIENTE: PASO 1 (k = 1, todo q, de lápiz).

## PASO 1
PRESUPUESTO: 30 min (inicio 19:27). Motores: sólo k = 1, q ∈ {9, 27} para leer generadores (estimación: segundos, < 200 MB).

## PASO 1

## PASO 2
PRESUPUESTO: 45 min (inicio 19:31). Motores: k = 2 con q = 9 (y 27 si hace falta) sólo para leer generadores; estimación (2,9): < 1 min, < 300 MB.

## PASO 3

## PASO 4 — VEREDICTO
ESTADO: CERRADO (PROBADO: (G) y (U) para k = 1 y todo q = 3^v, con IGUALDAD r_a = f_clase(a)).

### 1.1 Dos reducciones generales (valen para todo k; son el mecanismo)

**Lema A (criterio de pertenencia a J_1).** Para g ∈ S':  g ∈ J_1 ⟺ x_{n−1}·g ∈ I + (x_{n−1}²).
*Prueba.* g ∈ J_1 = π'(I : x_{n−1}) ⟺ ∃h ∈ S con g + x_{n−1}h ∈ (I : x_{n−1}) ⟺ ∃h: x_{n−1}g + x_{n−1}²h ∈ I ⟺ x_{n−1}g ∈ I + (x_{n−1}²). ∎

**Lema B (criterio de pertenencia a R_a).** Para m ∈ S'':  m ∈ R_a ⟺ x_{n−2}^a·m ∈ J_1 + (x_{n−2}^{a+1}) ⟺ x_{n−1}x_{n−2}^a·m ∈ I + (x_{n−1}², x_{n−1}x_{n−2}^{a+1}).
*Prueba.* Igual que A, aplicado a R_a = π''(J_1 : x_{n−2}^a); la segunda equivalencia es A aplicado a x_{n−2}^a m + x_{n−2}^{a+1}h'. ∎

**Lema C (eliminación de e_1 y de la última potencia).** Como e_1 ∈ I, mod I vale x_0 = −(x_1+…+x_{n−1}), y por Frobenius (q = 3^v) x_0^q = −(x_1^q+…+x_{n−1}^q). Luego
 S/I ≅ F_3[x_1,…,x_{n−1}] / (Ē_3, Ē_5, …, Ē_{2k+1}, x_1^q, …, x_{n−1}^q),  Ē_j := e_j(x_0,…,x_{n−1})|_{x_0 = −(x_1+…+x_{n−1})}.
Además, como e_1 ∈ I, s := x_0+…+x_{n−2} ∈ J_1 (x_{n−1}e_1 = x_{n−1}s + x_{n−1}² ∈ I + (x_{n−1}²)); análogamente x_0+…+x_{n−3} ∈ R_a. Así S'/J_1 ≅ F_3[x_1..x_{n−2}]/J̄_1 y S''/R_a ≅ F_3[x_1..x_{n−3}]/R̄_a, con J̄_1, R̄_a las imágenes por x_0 ↦ −(suma de las demás). (Las dos sustituciones x_0 ↦ 0 y x_0 ↦ −Σ dan el mismo ideal porque el ideal contiene la diferencia.)

**Lema D (lectura por monomios estándar, revlex).** Sea `<` el orden revlex graduado con x_{n−1} < x_{n−2} < … < x_0 y L := in_<(I). Entonces
 r_a = #{ monomios m en x_0..x_{n−3} : m·x_{n−2}^a·x_{n−1} ∉ L }.
*Prueba.* Para I homogéneo y revlex con x_n la menor: in(I : x_n) = in(I) : x_n (si x_n | in(f) entonces x_n | f, luego f/x_n ∈ I : x_n; el recíproco es trivial) e in(I + (x_n)) = in(I) + (x_n) (Bayer–Stillman). Iterando con x_{n−2} en S' se obtiene in(R_a) = ((L : x_{n−1}x_{n−2}^a) + (x_{n−1}, x_{n−2})) ∩ S''. ∎
(No se usa en la prueba de cotas; sirve para las igualdades.)

### 1.2 El caso k = 1 (n = 4). Notación: u := x_1 + x_2.

Por el Lema C con n = 4: S/I ≅ F_3[x_1,x_2,x_3]/(E, x_1^q, x_2^q, x_3^q) con
 E = e_3(x_1,x_2,x_3) − (x_1+x_2+x_3)·e_2(x_1,x_2,x_3) = x_1x_2x_3 − Σ_{i≠j} x_i²x_j   (char 3).
Módulo x_3²:  E ≡ −x_1x_2(x_1+x_2) − x_3(x_1² − x_1x_2 + x_2²) = −u·x_1x_2 − x_3·u²,  porque x_1² − x_1x_2 + x_2² = (x_1+x_2)² en char 3.

**Cálculo de J̄_1.** En A := F_3[x_1,x_2,x_3]/(x_3²) el ideal (I + (x_3²))/(...) está generado por E, x_1^q, x_2^q (x_3^q ≡ 0). Un elemento general es
 (g_0 + x_3g_1)·E + (h_0 + x_3h_1)x_1^q + (h_0' + x_3h_1')x_2^q ≡ [−g_0·u x_1x_2 + h_0x_1^q + h_0'x_2^q] + x_3·[−g_0u² − g_1·u x_1x_2 + h_1x_1^q + h_1'x_2^q].
Por el Lema A, f ∈ J̄_1 ⟺ f es la parte en x_3 de un elemento con parte libre nula ⟺ g_0 ∈ ((x_1^q,x_2^q) : u x_1x_2) y f ≡ −g_0u² − g_1 u x_1x_2 mod (x_1^q,x_2^q). Es decir
 **J̄_1 = (u·x_1x_2) + u²·((x_1^q, x_2^q) : u x_1x_2) + (x_1^q, x_2^q).**

**Cálculo del colon.** (x_1^q,x_2^q) : x_1x_2 = (x_1^{q−1}, x_2^{q−1}). Sea w := (x_1^{q−1} − x_2^{q−1})/(x_1+x_2) = Σ_{i=0}^{q−2} (−1)^i x_1^{q−2−i}x_2^i (q−1 es par). Entonces
 (x_1^{q−1}, x_2^{q−1}) : u = (x_1^{q−1}, x_2^{q−1}, w).
*Prueba.* Sea B = F_3[x_1,x_2]/(x_1^{q−1},x_2^{q−1}), dim B = (q−1)². dim ann_B(u) = dim B − dim uB = dim B/uB = dim F_3[x_1]/(x_1^{q−1}) = q−1. Por otro lado u·w = x_1^{q−1} − x_2^{q−1} ∈ (x_1^{q−1},x_2^{q−1}), así que (w) ⊆ ann_B(u); y (x_1^{q−1},x_2^{q−1},w) = (w, x_2^{q−1}) (pues x_1^{q−1} = uw + x_2^{q−1}), intersección completa de grados q−2, q−1 (w(x_1,0) = x_1^{q−2} ≠ 0), de colongitud (q−1)(q−2). Luego dim (w)B = (q−1)² − (q−1)(q−2) = q−1 = dim ann_B(u), y (w)B = ann_B(u). ∎

**Reducción de generadores.** Módulo (x_1^q, x_2^q, u x_1x_2): u²·w = u(x_1^{q−1} − x_2^{q−1}) ≡ x_1^{q−1}x_2 − x_1x_2^{q−1}; y como x_1x_2·x_1 ≡ −x_1x_2·x_2, x_1^{q−1}x_2 ≡ (−1)^{q−2}x_1x_2^{q−1} = −x_1x_2^{q−1}. Luego u²w ≡ −2x_1x_2^{q−1} = x_1x_2^{q−1}. Y u²x_1^{q−1} ≡ x_1^{q−1}x_2² ≡ ±x_1x_2^q ≡ 0, igual u²x_2^{q−1}. Por tanto
 **J̄_1 = (x_1x_2(x_1+x_2), x_1x_2^{q−1}, x_1^q, x_2^q)**, y J_1 = (x_0+x_1+x_2) + J̄_1·S'.   [PROBADO; coincide con la GB que imprime M2 en (1,9) y (1,27): `explore1.log`]

**Filas.**
- (U), a = q−1: x_1x_2^{q−1} ∈ J̄_1 ⇒ x_1 ∈ (J̄_1 : x_2^{q−1}) ⇒ x_1 ∈ R̄_{q−1} ⇒ **r_{q−1} ≤ 1** para todo q ≥ 3.
- (G), 1 ≤ a ≤ q−2: x_1²x_2 + x_1x_2² ∈ J̄_1 ⇒ x_1² + x_1x_2 ∈ (J̄_1 : x_2^a) ⇒ x_1² ∈ R̄_a ⇒ **r_a ≤ 2**; en particular r_2 ≤ 2 = f_gen para q ≥ 9.
- Igualdades: {x_1²x_2+x_1x_2², x_1x_2^{q−1}, x_1^q, x_2^q} es base de Gröbner revlex (x_1 > x_2): los tres S-pares no triviales reducen a x_1x_2^q, ±x_1x_2^q, x_1x_2^{q+1} → 0. Monomios estándar x_1^ix_2^j: j = 0, i ≤ q−1 (q de ellos); 1 ≤ j ≤ q−2, i ≤ 1 (2 cada uno); j = q−1, i = 0 (1). Por el Lema D: r_0 = q, r_a = 2 (1 ≤ a ≤ q−2), r_{q−1} = 1, Σ = 3q−3 = N_1. Coincide con las celdas (1,3), (1,9), (1,27) del §4 y con `calib.log`.

**Pista para k ≥ 2 (el mecanismo):** todo se decide en A = S/(x_{n−1}²): J̄_1 = {parte x_{n−1} de los elementos de Ī cuya parte libre es 0}. Esto se escribe como (K̄_0-sicigias). Para k = 1 los ideales son principales y sale un colon de una intersección completa monomial por una forma lineal.
SIGUIENTE: PASO 2 (k = 2).
ESTADO: NO CONCLUYO (k = 2 reducido, al final del paso (§2.5), a UN solo lema de pertenencia explícito, G-a, verificado en (2,9) y (2,27) y no probado para q general; todo lo demás de k = 2 está PROBADO).

### 2.1 Lema E (general, PROBADO): todo el tablero vive en el anillo simétrico F_3[x_0..x_{n−3}]

Notación: m := n−2 = 2k, S'' = F_3[x_0..x_{m−1}], e_j := e_j(x_0..x_{m−1}), ℓ := e_1(x_0..x_{n−2}) = e_1 + x_{n−2}.
Sustituciones: x_{n−1} = −ℓ (mata e_1 de S) y x_{n−2} = ℓ − e_1. Con ellas S ≅ S''[ℓ] ⊗ (nada), y:
- e_j(x_0..x_{n−1}) = e_j + (x_{n−2}+x_{n−1})e_{j−1} + x_{n−2}x_{n−1}e_{j−2} = e_j − e_1e_{j−1} + ℓ(e_1 − ℓ)e_{j−2}. Luego, mod ℓ²:
 **E_j ≡ P_j + ℓ·e_1e_{j−2}**, con **P_j := e_j − e_1e_{j−1}** (= e_j de las m+1 variables (x_0..x_{m−1}, −e_1)).
- x_{n−2}^q = (ℓ−e_1)^q = ℓ^q − e_1^q ≡ −Σx_i^q mod ℓ²; x_{n−1}^q = −ℓ^q ≡ 0.
- K := imagen de I en S' = S''[ℓ] es (E_3,…,E_{2k+1}, x_0^q..x_{m−1}^q) (+ ℓ^q, irrelevante).
- Como en el Lema A: J_1 = (K : ℓ) + (ℓ), y bajo ψ: S' → S'', x_{n−2} ↦ −e_1 (núcleo (ℓ)), J̄_1 := ψ(J_1) = {f ∈ S'' : ℓf ∈ K + (ℓ²)}.
- Escribiendo un elemento de K como Σ_j (g_j + ℓg_j')E_j + Σ(h_i + ℓh_i')x_i^q y pidiendo parte libre nula:

> **Lema E.** J̄_1 = K_0 + e_1·N, donde K_0 := (P_3, …, P_{2k+1}, x_0^q, …, x_{m−1}^q) = ψ(J_0) y
> N := { Σ_j g_j e_{j−2} : (g_3, …, g_{2k+1}) ∈ S''^k con Σ_j g_jP_j ∈ (x_0^q, …, x_{m−1}^q) } (ideal de S'').
> Además, para todo a: **R_a = (J̄_1 : e_1^a) + (e_1)** como ideales de S'' (porque J_1 : x_{n−2}^a ∋ ℓ, y para un ideal A ∋ ℓ vale π''(A) = (A ∩ S'') + (e_1) = ψ(A) + (e_1), y ψ(J_1 : x_{n−2}^a) = J̄_1 : e_1^a).

*Prueba de la última igualdad.* Todo f ∈ S' se escribe f = f̃ + ℓh con f̃ = ψ(f) ∈ S''. Si A ∋ ℓ entonces A = (A∩S'')S' + (ℓ) y π''(A) = (A∩S'') + π''(ℓ)S'' = ψ(A) + (e_1). ∎

**Corolario E1 (PROBADO, todo k y q).** Como e_1N ⊆ (e_1): R_0 = K_0 + (e_1) = π''(J_0). Luego **r_0 = A_{k−1}(q) para todo k y todo q** (H3 con igualdad). Análogamente π''(J_0 : x_{n−2}) = (K_0 : e_1) + (e_1) ⊆ R_1.

**Comprobación numérica del Lema E** (`lemaE.m2`, `lemaE.log`): calculando J̄_1 = K_0 + e_1N con `syz` en S'' y las filas como (J̄_1 : e_1^a) + (e_1), se reproducen EXACTAMENTE las filas de (1,9), (2,3), (2,9), (2,27) y (3,3) del §4. Coste: 5,7 s, 265 MB en total.

### 2.2 Lema F (k = 2, PROBADO a mano): los generadores no-Koszul de N

Para k = 2: S'' = F_3[x_0..x_3], P_3 = e_3 − e_1e_2, P_5 = −e_1e_4, N = {g_3e_1 + g_5e_3 : g_3P_3 + g_5P_5 ∈ (x^q)}.
Sea {i,j,l,m} = {0,1,2,3}, w_{lm} := (x_l^{q−1} − x_m^{q−1})/(x_l + x_m) = Σ_{s=0}^{q−2} (−1)^s x_l^{q−2−s}x_m^s (q−1 par), y **t_{ij|lm} := x_ix_j(x_l^{q−1} − x_m^{q−1})**.

> **Lema F.** (g_3, g_5) := (−x_lx_m·w_{lm}, w_{lm}) cumple g_3P_3 + g_5P_5 ∈ (x_l^q, x_m^q) y g_3e_1 + g_5e_3 = t_{ij|lm} − (x_l^qx_m − x_lx_m^q). Por tanto t_{ij|lm} ∈ N + (x^q) y **e_1·t_{ij|lm} ∈ J̄_1** para los 6 pares {i,j}.

*Prueba.* Sean a := x_i+x_j, b := x_l+x_m, p := x_ix_j, r := x_lx_m. Entonces e_1 = a+b, e_2 = p+ab+r, e_3 = pb+ra, e_4 = pr.
(1) g_3P_3 + g_5P_5 = w·[−r(e_3 − e_1e_2) − e_1pr] = w·r·[−e_3 + e_1(e_2 − p)] = w·r·[−pb − ra + (a+b)(ab+r)] = w·r·b·(a² − p + ab + r) = (x_l^{q−1} − x_m^{q−1})·x_lx_m·(a²−p+ab+r) = (x_l^qx_m − x_lx_m^q)(…) ∈ (x_l^q, x_m^q).
(2) g_3e_1 + g_5e_3 = w·(e_3 − r e_1) = w·(pb + ra − ra − rb) = w·b·(p − r) = (x_l^{q−1} − x_m^{q−1})(x_ix_j − x_lx_m) = t_{ij|lm} − (x_l^qx_m − x_lx_m^q). ∎
(Coincide con la sicigia que devuelve M2 en (2,9) y (2,27): `syz.log`.)

**Definición.** J̄_1^{cand} := K_0 + (e_1t_{ij|lm} : 6 pares) ⊆ J̄_1 (PROBADO ⊆ para todo q). MEDIDO: J̄_1^{cand} = J̄_1 en q = 3, 9, 27 (`syz.log`: «N+K0 == K0+(candidates)? true»), y por tanto las filas (J̄_1^{cand} : e_1^a) + (e_1) reproducen el §4 en esas celdas (`cert.log`). En 5 variables: J_1 ⊇ (ℓ, e_3^{(5)}, e_5^{(5)}, x^q, x_ax_ix_j(x_l^{q−1}−x_m^{q−1}) : {a,i,j,l,m} = {0..4}) (por S_5-simetría de J_1).

### 2.3 Reducción de (U) y (G) para k = 2 a pertenencias explícitas (PROBADO), y cuentas (PROBADO)

Trabajo en coordenadas reducidas F_3[x_1,x_2,x_3] (x_0 = −(x_1+x_2+x_3), lícito porque e_1 ∈ R_a), revlex x_1 > x_2 > x_3; ē_j := e_j(x_0..x_3)|_{x_0=−(x_1+x_2+x_3)}.

**(a) Elementos automáticos en R_a, a ≥ 1:** e_1; e_3 (P_3 ∈ K_0 ⇒ e_3 ≡ e_1e_2 ≡ 0); e_4 (P_5 = −e_1e_4 ∈ K_0 ⇒ e_4 ∈ K_0 : e_1); x_i^q. En grados < q, R_1 ⊇ (ē_3, ē_4), que es intersección completa de grados 3,4 (ē_4 = −(x_1+x_2+x_3)x_1x_2x_3 factoriza en lineales, ninguno divide a ē_3 = x_1x_2x_3 − Σ_{i≠j}x_i²x_j), con función de Hilbert (1−t³)(1−t⁴)/(1−t)³ → 1, 3, 6, 9, 11, 12, 12, …

**(b) Cuenta para (U), k = 2 (PROBADO).** Si R̄_{q−1} ⊇ C_U := (x_ix_jx_l : i<j<l ≤ 3) + (x_i^q) + (x_ix_j^{q−1} : i ≠ j), entonces r_{q−1} ≤ 6q − 8 = f_{+1}. *Prueba:* en coordenadas reducidas los 4 cúbicos son x_1x_2x_3, x_1x_2(x_1+x_2), x_1x_3(x_1+x_3), x_2x_3(x_2+x_3), con líderes x_1x_2x_3, x_1²x_2, x_1²x_3, x_2²x_3; los monomios x_i^q, x_ix_j^{q−1} (i,j ∈ {1,2,3}) son sus propios líderes. Los monomios estándar del ideal monomial (x_1²x_2, x_1²x_3, x_2²x_3, x_1x_2x_3, x_1^q, x_2^q, x_3^q, x_1x_2^{q−1}, x_1x_3^{q−1}, x_2x_3^{q−1}) son: x_1^a (2 ≤ a ≤ q−1): q−2; x_1x_3^c (c ≤ q−2) y x_1x_2^b (1 ≤ b ≤ q−2): 2q−3; x_3^c (c ≤ q−1), x_2x_3^c (c ≤ q−2), x_2^b (2 ≤ b ≤ q−1): 3q−3. Total 6q−8. ∎ (Comprobado con la función de Hilbert 1,3,6,6,…,6,0 de R_8 en (2,9): `explore2.log`.)

**(c) Cuenta para (G), k = 2 (PROBADO).** Si R̄_2 ⊇ (ē_3, ē_4) + (x_i^q) + (x_i²x_j^{q−2} : i ≠ j ∈ {0,1,2,3}), entonces r_2 ≤ 12(q−2) = f_gen para q ≥ 9. *Prueba:* la GB revlex de (ē_3, ē_4) (cálculo finito, independiente de q; `explore2.log` fila a=1, grados 3,4,5) tiene líderes x_1²x_2, x_1²x_3², x_2³x_3². De x_i²x_j^{q−2} con i,j ∈ {1,2,3}: x_2²x_3^{q−2}; y x_0²x_3^{q−2} ≡ (x_1+x_2+x_3)²x_3^{q−2} ≡ −x_3^{q−2}e_2(x_1,x_2,x_3) mod (x_1²x_3^{q−2}, x_2²x_3^{q−2}, x_3^q), con líder x_1x_2x_3^{q−2}; igual x_2^{q−2}e_2(x_1,x_2,x_3) con líder x_1x_2^{q−1}. Monomios estándar de (x_1²x_2, x_1²x_3², x_2³x_3², x_3^q, x_2²x_3^{q−2}, x_1x_2x_3^{q−2}, x_2^q, x_1x_2^{q−1}, x_1^q): a ≥ 2: 2(q−2); a = 1: q + 2(q−2) + 2(q−4) = 5q−12; a = 0: q + q + (q−2) + 2(q−3) = 5q−8. Total 12q − 24. ∎ (Comprobado: Hilbert 1,3,6,9,11,12,…,12,6,0 de R_2 en (2,9) y (2,27): `explore2.log`, `cert.log`.)

**(d) Lo que falta (los tres lemas, enunciados exactos).** Con J̄_1^{cand} = (P_3, P_5, x_0^q..x_3^q, e_1x_ix_j(x_l^{q−1}−x_m^{q−1})) ⊂ F_3[x_0..x_3]:
- **Lema U-a (falta):** e_1^{q−1}·x_ix_jx_l ∈ J̄_1^{cand} para i<j<l ≤ 3. [Equivalente en 5 variables: x_0x_1x_2x_3^{q−1} ∈ J_1^{cand}.]
- **Lema U-b (falta):** e_1^{q−1}·x_ix_j^{q−1} ∈ J̄_1^{cand} para i ≠ j. [Equivalente: x_ax_b^{q−1}x_c^{q−1} ∈ J_1^{cand}, a,b,c ≤ 4 distintos.]
- **Lema G-a (falta):** e_1²·x_i²x_j^{q−2} ∈ J̄_1^{cand} para i ≠ j.
MEDIDO: los tres son ciertos en (2,9) y (2,27) (`cert.log`, `cert2.log`), y exactamente en las filas previstas (x_ix_jx_l y x_ix_j^{q−1} sólo entran en a = q−1; x_i²x_j^{q−2} entra en a ≥ 2; x_ix_jx_l^{q−2} sólo en a = q−1; x_ix_j^{q−2} nunca).
Con U-a + U-b ⇒ (U) para k = 2 (por (b), pues R_{q−1} ⊇ (J̄_1^{cand} : e_1^{q−1}) + (e_1)); con G-a ⇒ (G) para k = 2 (por (c)).
Certificados que NO funcionan (probado por M2 en (2,9),(2,27)): x_0x_1x_2x_3^{q−2} ∉ J̄_1^{cand}; e_1^{q−2}x_0x_1x_2 ∉ K_0 + (t's); e_1x_2²x_3^{q−2} ∉ K_0 + (t's). Es decir, los lemas no son identidades «de grado q+1»: el factor e_1^{q−1} (resp. e_1²) es esencial y el certificado tiene multiplicadores polinómicos (los de U-b están impresos en `cert2.log`).
Vía muerta comprobada: reducir U-b «un nivel impar abajo» vía x_b^{q−1}·T ↠ (anillo impar de 5 variables) exigiría x_ax_c^{q−1} ∈ (K_0 : e_1) + (e_1) = R_1^{cand}, que es FALSO (x_ix_j^{q−1} ∉ R_1 en (2,9)).
SIGUIENTE: PASO 3 (k general) con lo que quede; intento previo de U-a con el certificado explícito.

### 2.4 Lema U-a: PROBADO (identidad exacta, verificada a mano)

En S' = F_3[x_0..x_4] escribo a := x_3, b := x_4, σ_j := e_j(x_0,x_1,x_2). Entonces e_1 = σ_1 + a + b, e_3 = σ_3 + (a+b)σ_2 + abσ_1, e_5 = abσ_3. Sean
 W := (x_3 + x_4)^{q−1} = (a^q + b^q)/(a+b) = Σ_{s=0}^{q−1}(−1)^s a^{q−1−s}b^s,  W' := (a^{q−2} + b^{q−2})/(a+b) = Σ_{s=0}^{q−3}(−1)^s a^{q−3−s}b^s  (q−1, q−3 pares).
Se tiene W + abW' = a^{q−1} + b^{q−1} (los términos intermedios se cancelan a pares) y (a+b)W = a^q + b^q. Luego
 (e_3 − ab·e_1)·W + e_5·W' = [σ_3 + (a+b)(σ_2 − ab)]W + abσ_3W' = σ_3(W + abW') + (a^q+b^q)(σ_2 − ab) = **σ_3(a^{q−1} + b^{q−1}) + (a^q + b^q)(σ_2 − ab)**.
> **Identidad (U-a+).** x_0x_1x_2(x_3^{q−1} + x_4^{q−1}) = (e_3 − x_3x_4e_1)(x_3+x_4)^{q−1} + e_5·W'_{34} − (x_3^q + x_4^q)(e_2(x_0,x_1,x_2) − x_3x_4) ∈ J_0.
Junto con el Lema F (x_0x_1x_2(x_3^{q−1} − x_4^{q−1}) ∈ J_1): 2·x_0x_1x_2x_3^{q−1} ∈ J_1, o sea **x_0x_1x_2x_3^{q−1} ∈ J_1 y x_0x_1x_2x_4^{q−1} ∈ J_1** para todo q. Por S_5-simetría de J_1: x_ax_ix_jx_l^{q−1} ∈ J_1 para a,i,j,l ≤ 4 distintos. En particular x_ix_jx_l ∈ J_1 : x_4^{q−1}, luego **x_ix_jx_l ∈ R_{q−1}** (i<j<l ≤ 3). ∎ (Coincide con el certificado de M2 en (2,9), `cert3.log`, y con los monomios puros x_1x_2x_3x_4^{q−1} de la GB de J_1 en (2,9),(2,27): `explore3.log`.)

### 2.5 Corrección y reducción final de k = 2 (PROBADO): todo se reduce a UN lema

**Corrección de enunciado.** f ∈ R_a ⟺ ∃h: (f − e_1h)e_1^a ∈ J̄_1 ⟺ e_1^a f ∈ J̄_1 + (e_1^{a+1}). Para a = q−1 el sumando (e_1^q) ⊆ (x^q) ⊆ J̄_1 es superfluo (U-a, U-b estaban bien enunciados); para a = 2 el enunciado correcto es
> **Lema G-a (falta):** e_1²·x_i²x_j^{q−2} ∈ J̄_1^{cand} + (e_1³) para i ≠ j ≤ 3. En 5 variables: x_4²·x_i²x_j^{q−2} ∈ J_1 + (x_4³). (MEDIDO cierto en (2,9), (2,27) con J̄_1^{cand}: `cert.log`, líneas «x_i^2 x_j^(q-2) in R_a: {2,…,q−1}».)
(El test «x0² x1^(q-2) x4² in J1cand? false» de `cert4.log` es coherente: sin el sumando (x_4³) la pertenencia es falsa.)

**Reducción U-b ⇐ G-a (PROBADO, q ≥ 9).** Por H2, R_2 ⊆ R_{q−1}. Si x_0²x_1^{q−2} ∈ R_2 entonces, como R_{q−1} ∋ e_1 y ∋ x_0x_1x_l (Lema U-a):
 x_0x_1^{q−1} = x_0x_1^{q−2}·e_1 − x_0²x_1^{q−2} − x_0x_1^{q−2}x_2 − x_0x_1^{q−2}x_3 ∈ R_{q−1}. ∎
(Para q = 3 no hay fila genérica y (U) es la celda (2,3), medida en el §4 y en `calib.log`; para q = 3 una celda finita calculada es una prueba.)

**Balance de k = 2.** PROBADO: Lema E, Lema F, Lema U-a, las dos cuentas (b),(c), y la reducción U-b ⇐ G-a. Por tanto:
> **(U)_{k=2} y (G)_{k=2}, para todo q ≥ 9, se siguen ambas del único Lema G-a.** (U)_{k=2} para q = 3 está probada por cálculo finito (celda (2,3)).
Frase exacta del lema que falta: «Para q = 3^v ≥ 9 y en F_3[x_0..x_4], x_4²x_0²x_1^{q−2} ∈ (e_1, e_3, e_5, x_0^q..x_4^q, x_ax_ix_j(x_l^{q−1} − x_m^{q−1}) : {a,i,j,l,m} = {0..4}) + (x_4³).» Celda de comprobación: (2,9) (hecha: cierto) y (2,27) (hecha: cierto); certificado con multiplicadores polinómicos, no escalares (`cert2.log`).
Vía por la que NO sale G-a en grado q+1: e_1x_2²x_3^{q−2} ∉ K_0 + (t's) (`cert2.log`): el factor e_1² es esencial.
SIGUIENTE: PASO 3.

## PASO 3
PRESUPUESTO: 45 min (inicio 20:03). Motores: sólo (3,3) (estimación < 1 min, < 300 MB) para contrastar el análogo de F y de (U-a+) con k = 3.
ESTADO: NO CONCLUYO (Lema F PROBADO para todo k; (U) y (G) generales reducidas a dos lemas explícitos, uno de ellos ya el G-a de k = 2).

### 3.1 Lema F general (PROBADO a lápiz, todo k y todo q = 3^v)

Notación: m = 2k, S'' = F_3[x_0..x_{m−1}], e_j = e_j(x_0..x_{m−1}), P_j = e_j − e_1e_{j−1} = e_j(x_0, …, x_{m−1}, −e_1) (los e_j de las m+1 cantidades x_0,…,x_{m−1},−e_1, que suman 0). Fijo l ≠ m' en [m], A := [m] ∖ {l,m'}, r := x_lx_{m'}, b := x_l + x_{m'}, w := (x_l^{q−1} − x_{m'}^{q−1})/b, ε_j := e_j(x_A), x_A := ∏_{a∈A}x_a = ε_{2k−2}.

> **Lema F (general).** g_{2k+1−2s} := w·(−r)^s (s = 0, …, k−1) cumple Σ_{s} g_{2k+1−2s}P_{2k+1−2s} ∈ (x_l^q, x_{m'}^q) y Σ_s g_{2k+1−2s}e_{2k−1−2s} ≡ x_A(x_l^{q−1} − x_{m'}^{q−1}) mod (x^q). Por tanto **t_{A|lm'} := x_A(x_l^{q−1} − x_{m'}^{q−1}) ∈ N + (x^q) y e_1·t_{A|lm'} ∈ J̄_1.** En 2k+1 variables (S'), por S_{2k+1}-simetría de J_1: **x_B(x_l^{q−1} − x_{m'}^{q−1}) ∈ J_1 para todo B ⊂ [2k+1] con |B| = 2k−1 y {l,m'} su complemento.**

*Prueba.* (i) Σ_s(−r)^sP_{2k+1−2s} es divisible por b: al poner x_{m'} = −x_l, las m+1 cantidades son {x_A, x_l, −x_l, −e_1(x_A)}, con función generatriz (1 − x_l²t²)G(t), G(t) = ∏_{a∈A}(1+x_at)(1 − e_1(x_A)t); así P_j|_{x_{m'}=−x_l} = G_j − x_l²G_{j−2}, y Σ_{s=0}^{k−1}x_l^{2s}P_{2k+1−2s} telescopa a G_{2k+1} − x_l^{2k}G_1 = 0 − 0 (G tiene 2k−1 cantidades que suman 0). (ii) Es divisible por r: los términos s ≥ 1 llevan r, y P_{2k+1} = −e_1·x_0⋯x_{m−1}. Como x_l, x_{m'}, b son irreducibles distintos: Σ_s(−r)^sP_{2k+1−2s} = r·b·H, y w·r·b·H = (x_l^qx_{m'} − x_lx_{m'}^q)H ∈ (x^q). (iii) Imagen: con e_j = ε_j + bε_{j−1} + rε_{j−2}, Σ_s(−r)^se_{2k−1−2s} = [Σ_s(−r)^sε_{2k−1−2s} − Σ_s(−r)^{s+1}ε_{2k−3−2s}] + bΣ_s(−r)^sε_{2k−2−2s} = (ε_{2k−1} − (−r)^kε_{−1}) + b·Σ_s(−r)^sε_{2k−2−2s} = b·(x_A − rε_{2k−4} + r²ε_{2k−6} − …). Multiplicando por w: (x_l^{q−1} − x_{m'}^{q−1})(x_A − rε_{2k−4} + …) ≡ (x_l^{q−1} − x_{m'}^{q−1})x_A mod (x^q), porque (x_l^{q−1} − x_{m'}^{q−1})·r^s ∈ (x_l^q, x_{m'}^q) para s ≥ 1. ∎
Comprobación mecánica de la fórmula en (1,9), (2,9), (2,27), (3,3): `syzgen.m2` (líneas «syzygy in box? true / image == t mod box? true»). Para k = 2 es exactamente el Lema F del PASO 2.

### 3.2 Lo que N tiene de más para k ≥ 3 (MEDIDO en (3,3), `k3.log`)

En (3,3), (N+K_0)/K_0 vive sólo en grados 6 y 7 (dimensiones 36, 36) y los t_{A|lm'} (|A| = 4) sólo generan 15 de los 36 en grado 6. La familia **t_{A|BC} := x_A(x_B^{q−1} − x_C^{q−1})** con A ⊔ B ⊔ C = [2k], |B| = |C| = 2 (x_B := ∏_{b∈B}x_b) está toda en N + K_0 y **{t_{A|lm'}} ∪ {t_{A|BC}} generan N + K_0 en (3,3)**. CONJETURA (natural, no probada): para todo k, N + K_0 = K_0 + (x_A(x_B^{q−1} − x_C^{q−1}) : A ⊔ B ⊔ C = [2k], |B| = |C| ≥ 1). Cierta en k = 1 (q = 9, 27), k = 2 (q = 3, 9, 27), k = 3 (q = 3). La sicigia que la probaría para |B| = j debería ser el análogo del Lema F con «r» = producto de los pares de B y C emparejados; no la he construido.

### 3.3 Identidad (U-a+) general (PROBADA para k = 2; MEDIDA en (3,3))

Para k = 2 probé x_B(x_l^{q−1} + x_{m'}^{q−1}) ∈ J_0 (|B| = 3, §2.4). En (3,3): x_B(x_5^{q−1} + x_6^{q−1}) ∈ J_0 con |B| = 5 (`k3.log`, última línea: true). CONJETURA para todo k: x_B(x_l^{q−1} + x_{m'}^{q−1}) ∈ J_0 = (e_1, e_3, …, e_{2k+1}, x^q) para |B| = 2k−1. Con el Lema F general daría **x_Bx_l^{q−1} ∈ J_1 para |B| = 2k−1** y por tanto **x_C ∈ R_{q−1} para todo C ⊂ [2k], |C| = 2k−1** (los «cúbicos» de k = 2 son el caso |C| = 3). Vía de prueba sugerida por k = 2: en S'/(e_odd), E(t) := Σe_jt^j es par en t, y mod (x^q), (1 + x_lt)^{−1} ≡ (1 + x_lt)^{q−1}; falta escribir el certificado con W_q = (x_l+x_{m'})^{q−1} y W_{q−2}.

### 3.4 Qué queda para (U) y (G) generales (enunciado exacto)

Por el Lema E, R_a = (J̄_1 : e_1^a) + (e_1) y J̄_1 ⊇ J̄_1^{cand} := K_0 + (e_1·t_{A|lm'}) (+ los t_{A|BC} si la conjetura 3.2 es cierta). Las dos cotas se reducen a exhibir generadores de R_{q−1} y R_2 y a contar monomios estándar como en §2.3. Lo que NO tengo para k general:
- **Lema G-a general (falta):** la descripción de R_2 en grado ≥ q. Para k = 2 es el único lema pendiente (x_i²x_j^{q−2} ∈ R_2). Para k = 3 ni siquiera está medido (la celda (3,9) del §4 no puede repetirse y (3,3) no tiene fila genérica).
- **El «diccionario de cuentas» para k ≥ 3:** en k = 2 la cota r_{q−1} ≤ 6q−8 salió de un esquema de 6 puntos dobles... no: de los 6 puntos [e_i], [e_i − e_j] de P² (r_{q−1}) y del esquema de grado 12 (ē_3, ē_4) (r_2). Para k general habría que identificar el esquema proyectivo Λ_k ⊂ P^{2k−2} de las direcciones de la fibra {y_{n−2} = +1} (segmentos y_i = −1 dos veces, (w,−w) libre) y probar que su ideal saturado está en R_{q−1}; f_{+1}(k,q) = (2k−1)!!·... no lo he derivado. Celda de comprobación: (3,3) para R_{q−1} = R_2 (r = 90 = f_{+1}(3,3) = 15(27−33+12) = 90 ✓ del §2).
Frase exacta del lema que cerraría k = 2 (y es el prototipo del general): la del §2.5.
SIGUIENTE: PASO 4.

### 3.5 Identidad (U-a+) general: PROBADA (todo k, todo q = 3^v) ⇒ Lema U-a general

En S' = F_3[x_0..x_{2k}], fijo l ≠ m', a := x_l, b := x_{m'}, B := [2k+1] ∖ {l,m'} (|B| = 2k−1), σ_j := e_j(x_B), β := a+b, r := ab. Entonces e_j = σ_j + βσ_{j−1} + rσ_{j−2}. Defino para j impar
 F_j := Σ_{s ≥ 0, j−2s ≥ 1} (−r)^s e_{j−2s} ∈ (e_1, e_3, …, e_{2k+1}) ⊆ J_0.
Telescopando como en el Lema F: **F_j = σ_j + β·Σ_{s≥0}(−r)^sσ_{j−1−2s}**. Con Ψ := Σ_{s≥0}(−r)^sσ_{2k−2−2s} = σ_{2k−2} − rσ_{2k−4} + r²σ_{2k−6} − …, y usando σ_{2k} = σ_{2k+1} = 0 (|B| = 2k−1):
 F_{2k−1} = σ_{2k−1} + βΨ,   F_{2k+1} = β(σ_{2k} − rσ_{2k−2} + r²σ_{2k−4} − …) = −rβΨ.
Sean W_q := (a^q + b^q)/β y W_{q−2} := (a^{q−2} + b^{q−2})/β (polinomios: q, q−2 impares), con W_q + rW_{q−2} = a^{q−1} + b^{q−1} (§2.4). Entonces
 F_{2k−1}(a^{q−1}+b^{q−1}) + F_{2k+1}W_{q−2} = σ_{2k−1}(a^{q−1}+b^{q−1}) + βΨ[(a^{q−1}+b^{q−1}) − rW_{q−2}] = σ_{2k−1}(a^{q−1}+b^{q−1}) + (a^q+b^q)Ψ.
> **Identidad (U-a+) general.** x_B(x_l^{q−1} + x_{m'}^{q−1}) = F_{2k−1}·(x_l^{q−1}+x_{m'}^{q−1}) + F_{2k+1}·W_{q−2} − (x_l^q + x_{m'}^q)·Ψ ∈ J_0, para todo B ⊂ [2k+1] con |B| = 2k−1.

> **Lema U-a general (PROBADO).** Con el Lema F general (x_B(x_l^{q−1} − x_{m'}^{q−1}) ∈ J_1) y J_0 ⊆ J_1: 2x_Bx_l^{q−1} ∈ J_1, luego **x_B·x_l^{q−1} ∈ J_1 para todo |B| = 2k−1, l ∉ B**. Tomando l = 2k: **todo monomio libre de cuadrados de grado 2k−1 en x_0..x_{2k−1} está en R_{q−1}**, para todo k y todo q. (Para k = 2 son los cúbicos del §2.4.)

Para k = 1 esto es x_0 ∈ R_{q−1} (r_{q−1} = 1, PASO 1). Comprobación mecánica en (2,27) y (3,3): `uaplus.m2` (abajo).

**Consecuencia estructural para (U) general (CONJETURA con la parte monomial PROBADA).** Los monomios x_B (|B| = 2k−1) junto con (e_1) y los e_{2i+1} (∈ R_a para todo a, por P_{2i+1} ∈ K_0) dicen que R_{q−1} contiene «casi» ∩_{i<j}[(x_i, x_j) + (e_1, e_3, …, e_{2k−3})(x_{[2k]∖{i,j}}) + (x^q)], que es el ideal esperado de la fibra v = +1 (dos −1 en las posiciones i, j y una copia de Z_{2k−2} en el resto). Falta: (a) que la intersección completa esté en R_{q−1} (para k = 2 la intersección la generan los 4 cúbicos y está hecho), (b) los monomios x_ix_j^{q−1} (Lema U-b, que en k = 2 se reduce a G-a), (c) la cuenta dim = f_{+1}(k,q). Celda de comprobación para k = 3: (3,3) (r_2 = 90 = f_{+1}(3,3)).

### 3.6 Conjunto generador limpio de J_1 para k = 2 (⊇ PROBADO todo q; = MEDIDO en (2,9), (2,27))

Por el Lema F general y (U-a+) general: J_1 ⊇ J_1^{c2} := (ℓ, e_3, e_5, x_0^q..x_4^q, x_ax_bx_cx_l^{q−1} : a,b,c,l ∈ [5] distintos) (20 monomios). En (2,9) y (2,27): **J_1 = J_1^{c2}** (`ga.log`: «J1 == Jc2? true»). Es decir, para k = 2 todo J_1 es «J_0 más monomios puros». CONJETURA: vale para todo q (k = 2). Análogo para k general: J_1 ⊇ (J_0, x_Bx_l^{q−1} : |B| = 2k−1) PROBADO; que sea igualdad es falso ya en (3,3) (N necesita los t_{A|BC} con |B| = |C| = 2, §3.2).
G-a respecto de J_1^{c2} + (x_4³): cierto en (2,9), (2,27), con certificado de multiplicadores polinómicos densos (`ga.log`); en 10 minutos no he visto su estructura. AGOTADO en este punto.
SIGUIENTE: PASO 4.

## PASO 4 — VEREDICTO
ESTADO: CERRADO. (Escrito 20:06–20:12; presupuesto 15 min.)

**Qué probé (de lápiz, con la prueba en este informe):**
1. **(G) y (U) para k = 1 y todo q = 3^v, con igualdad** r_a = f_clase(a) (PASO 1). Celdas: (1,3), (1,9), (1,27) del §4 y `calib.log`, `explore1.log`.
2. **Lema E** (todo k, q): J̄_1 = K_0 + e_1·N y R_a = (J̄_1 : e_1^a) + (e_1) en el anillo simétrico F_3[x_0..x_{2k−1}]; corolario **r_0 = A_{k−1}(q) para todo k y q** (H3 es igualdad). Comprobado en (1,9), (2,3), (2,9), (2,27), (3,3): `lemaE.log`.
3. **Lema F general** (todo k, q): sicigia explícita g_{2k+1−2s} = w·(−x_lx_m)^s ⇒ e_1·x_A(x_l^{q−1} − x_m^{q−1}) ∈ J̄_1, i.e. x_B(x_l^{q−1} − x_m^{q−1}) ∈ J_1 (|B| = 2k−1). Comprobado en (1,9), (2,9), (2,27), (3,3): `syzgen.m2`.
4. **Identidad (U-a+) general** (todo k, q): x_B(x_l^{q−1} + x_m^{q−1}) ∈ J_0. Comprobada exacta en las mismas 4 celdas: `uaplus.m2`.
5. **Corolario (todo k, q):** x_Bx_l^{q−1} ∈ J_1 y **todo monomio libre de cuadrados de grado 2k−1 en x_0..x_{2k−1} está en R_{q−1}** (Lema U-a general).
6. **k = 2:** las cuentas exactas (r_{q−1} ≤ 6q−8 si R_{q−1} ⊇ cúbicos + x_i^q + x_ix_j^{q−1}; r_2 ≤ 12(q−2) si R_2 ⊇ (ē_3, ē_4) + x_i^q + x_i²x_j^{q−2}) y la reducción U-b ⇐ G-a. Por tanto **(U)_{k=2} y (G)_{k=2} para todo q ≥ 9 se siguen del único Lema G-a**; (U)_{k=2} para q = 3 es la celda finita (2,3).

**Qué no probé:**
- **Lema G-a** (k = 2): «x_4²x_0²x_1^{q−2} ∈ (ℓ, e_3, e_5, x^q, x_ax_bx_cx_l^{q−1}) + (x_4³) en F_3[x_0..x_4]». MEDIDO cierto en (2,9), (2,27) (`cert.log`, `ga.log`). Es lo único que separa k = 2 del éxito parcial pleno.
- (G), (U) para k ≥ 3: falta el análogo de G-a y el diccionario de cuentas (§3.4, §3.5).

**Qué objeto nuevo deja el turno:** la reducción al anillo simétrico (Lema E) con el ideal de sicigias N, la sicigia explícita del Lema F, la identidad (U-a+), y para k = 2 la descripción conjetural completa J_1 = J_0 + (x_ax_bx_cx_l^{q−1}) (⊇ probada, = medida en dos celdas).

**Números citados, con su celda y comprobación:** todos los del §4 se reprodujeron (calib.log para (1,9),(2,3); lemaE.log para (1,9),(2,3),(2,9),(2,27),(3,3)). 6q−8 = 46 en (2,9): explore2.log fila a=8. 12(q−2) = 84 en (2,9) y 300 en (2,27): explore2.log, cert.log. Todas las corridas: < 15 s y < 300 MB (`*.time`).

**Sobre MISION.md:** no encontré errores. Precisión: H3 (r_0 ≤ A_{k−1}) es de hecho igualdad para todo k, q (Corolario E1).

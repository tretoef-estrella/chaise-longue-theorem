# INFORME_2 — misión «Las filas exteriores» (2026-09-21)

## PRIMERA LÍNEA
**(a)** PROBADO en parte: el Teorema de las Filas Exteriores para **k = 1 (ambas paridades, todas las filas, todo q)** y para **k = 2 en la paridad IMPAR (filas genéricas y fila +1, todo q = 3^v)**. En la paridad par de k = 2, ambas filas exteriores quedan reducidas al único **Lema G-a** de la misión 1. Para k ≥ 3, las filas pares quedan reducidas a dos inclusiones de ideales de intersección (Lemas Π y Π^gen, con gr G ⊆ Q probado dado D(k−2)); las impares no tienen reducción.
**(b)** Faltan, por orden: (1) Lema G-a: «x_4²x_0²x_1^{q−2} ∈ (e_1,e_3,e_5, x^q, x_ax_ix_j(x_l^{q−1}−x_m^{q−1})) + (x_4³) en F_3[x_0..x_4]», celda (2,9); (2) Lema Π: «∩_{i<j}[(y_i,y_j) + I^{(2k−2)}(y_{≠ij})] ⊆ R_{q−1}», celda (3,3); (3) Lema Π^gen: «∩_{i<j}[(y_i+y_j, y_i², y_iy_j, y_j²) + I^{(2k−2)}(y_{≠ij})] ⊆ R_2», celda (2,9); (4) las filas impares para k ≥ 3.
**(c)** **NO** cierra la conjetura: la cadena del §2.6 da **D'(2) para todo q** (nuevo) y se detiene en el paso 3 del nivel 2 por el Lema G-a; D(k) para todo k necesita además Π, Π^gen y las filas impares.
**Palanca 1:** muere (π∘φ_v = π). **MISION_2.md:** sin errores.

## PASO 0
ESTADO: CERRADO
PRESUPUESTO: 10 min (inicio 21:09). Estimación por script: < 1 min, < 300 MB.
RESULTADO: `tablero_par.m2` (0,90 s, 185 MB): 14/14 filas con `igual:true` en la última columna (la columna «grE(c)+caja» falla donde el §3 avisa: 18 vs 16 en (2,3,1)); `tablero_impar.m2` (0,65 s, 124 MB): 17/17 `igual:true`. Ambos logs terminan en `FIN-OK` (`tablero_par.log`, `tablero_impar.log`).
SIGUIENTE: PASO 1.

## PASO 1
PRESUPUESTO: 60 min (inicio 21:11; escribir desde 21:59). Motores: (1,9), (2,9), (2,27), (3,3) en las dos paridades, sólo para leer generadores mínimos de la fila +1 (estimación por celda: < 1 min, < 400 MB).

### 1.1 Palanca 1 (cizallamiento), tal como está enunciada: MUERE (PROBADO)
Sea φ_v: x_{2k} ↦ x_{2k} + v·x_{2k+1} (las demás fijas), automorfismo de S_{2k+2} que conserva la caja. Como φ_v fija x_{2k+1}: φ_v(I : x_{2k+1}) = φ_v(I) : x_{2k+1}. Pero π∘φ_v = π (π mata x_{2k+1}, y φ_v sólo añade múltiplos de x_{2k+1}). Luego
 π(φ_v(I) : x_{2k+1}) = π(φ_v(I : x_{2k+1})) = (π∘φ_v)(I : x_{2k+1}) = π(I : x_{2k+1}) = J_1.
Es decir, **el cizallamiento deja J_1 (y por tanto todas las filas R_a) exactamente invariantes**: no puede convertir la fila a en una fila 0 ó 1 de otro problema. Lo mismo vale en la paridad impar. El cizallamiento en la otra dirección (x_{2k+1} ↦ x_{2k+1} + v·x_{2k}) no respeta π y produce el ideal con «déficit no constante» (e_j(x_0..x_{2k}, v·x_{2k})), que no es un problema del mismo tipo. Descartada con razón.

### 1.2 Fila +1 PAR: reducción PROBADA a un lema de intersección; igualdad MEDIDA en 5 celdas

Notación: y = (y_0..y_{2k−1}), a := x_{2k}, b := x_{2k+1}. **Lema B:** m ∈ R_{q−1} ⟺ a^{q−1}b·m ∈ I + (b²) (con a+1 = q, x_{2k}^q ∈ I). La fibra es F_{+1} = ⋃_{i<j} X_{ij}, X_{ij} := {y_i = y_j = −1} × Z_{2k−2}(y_{≠ij}) (dos −1 emparejan a los dos +1; el resto es cerrado).
- I(X_{ij}) = (y_i+1, y_j+1) + G_{2k−2}(∅)(resto), luego gr I(X_{ij}) = (y_i, y_j) + gr G_{2k−2}(∅) = (y_i,y_j) + I^{(2k−2)}(resto) ⊗ F_q, **usando D(k−2)** (hipótesis de inducción disponible en el nivel k). Defino **Q_{ij} := (y_i, y_j) + I^{(2k−2)}(y_{≠ij})** (contiene la caja) y **Q := ∩_{i<j} Q_{ij}**.
- Como I(F_{+1}) = ∩ I(X_{ij}) y gr(∩) ⊆ ∩ gr: **gr G_{2k}({1,1}) ⊆ Q** (PROBADO, dado D(k−2)).
> **Reducción (PROBADA).** Si **Q ⊆ R_{q−1}** (Lema Π), entonces gr G_{2k}({1,1}) ⊆ Q ⊆ R_{q−1} y r_{q−1} ≤ dim S/Q ≤ dim S/gr G = f_{+1}. No hace falta inclusión–exclusión: la cuenta la da el §2.2.
- **MEDIDO: Q = R_{q−1} como ideales** en (1,9), (2,3), (2,9), (2,27), (3,3) (`inter.log`, `inter2.log`; dims 1, 10, 46, 154, 90 = f_{+1}). Es decir, la fila +1 par es EXACTAMENTE la intersección de las piezas.
- **Lo que de Q ya está PROBADO dentro de R_{q−1}, para todo k y q:** e_1 (Lema C), los ε_j impares (P_j ∈ K_0), la caja, y todos los monomios libres de cuadrados de grado 2k−1 (Lema U-a general de la misión 1). Estos generan Q en k = 1; en k = 2 falta exactamente **x_ix_j^{q−1}** (dims 49 vs 46 en (2,9), 157 vs 154 en (2,27): `inter2.log`), que es el Lema U-b ⇐ G-a de la misión 1; en (3,3) faltan muchos (126 vs 90).
- **Lema que falta (exacto):** «Q = ∩_{i<j}[(y_i,y_j) + I^{(2k−2)}(y_{≠ij})] ⊆ R_{q−1}, es decir, para todo m con m|_{y_i=y_j=0} ∈ I^{(2k−2)}(y_{≠ij}) para todo par, vale x_{2k}^{q−1}x_{2k+1}m ∈ I + (x_{2k+1}²)». Celdas: (2,9) y (3,3) (ya ciertas). Para k = 2 basta el Lema G-a.
- Nota: la palanca 3 queda esquivada: no hace falta ninguna base de Gröbner de G, porque gr G ⊆ Q se prueba pieza a pieza y la cuenta la da dim S/gr G = f_{+1}.

### 1.3 Fila +1 IMPAR: k = 1 PROBADA; relación MEDIDA con la fila par; el mismo camino NO funciona
- **k = 1 (PROBADO):** R'_{q−1} ∋ 1 ⟺ x_1^{q−1}x_2 ∈ I^{(3)} + (x_2²). Mod e_1, x_0 = −x_1−x_2 y e_3 = −(x_1+x_2)x_1x_2 ≡ −x_1²x_2 mod x_2²; luego x_1^{q−1}x_2 = x_1^{q−3}·x_1²x_2 ∈ I^{(3)} + (x_2²). Así r'_{q−1} = 0 = f'_{+1}(1,q) para todo q. ∎
- **Descomposición en piezas NO basta (MEDIDO):** F'_{+1} = ⋃_{i<j}{y_i=y_j=−1}×Z_{2k−3}, pero ∩_{i<j}[(y_i,y_j) + I^{(2k−3)}(resto)] es estrictamente MAYOR que R'_{q−1} (dims 1 vs 3 en (2,9), 21 vs 30 en (3,3); `inter.log`). Razón: en (2,9) las tres piezas son puntos (−1,−1,0) permutados, cada gr es 𝔪, pero gr de la unión es (e_1, 𝔪²): hay relaciones colectivas (la suma es 1) invisibles pieza a pieza.
- **MEDIDO en (2,9), (2,27), (3,3): R'_{q−1}^{(k)} = π(R_{q−1}^{(k)} : y_{2k−1})** (la fila +1 impar es la sub-fila a = 1 de la fila +1 PAR del mismo nivel; `inter2.log`). Corresponde a F'_{+1}(k) = {y' : (y',0) ∈ F_{+1}(k)} (valor 0 ↔ sub-fila 1). No he probado la inclusión algebraica R'_{q−1} ⊇ π(R_{q−1} : y_{2k−1}); el truco f·(1 − y_{2k−1}^{q−1}) sólo da la sub-fila q−1, que es mayor.

### 1.4 Fila +1 IMPAR, k = 2: reducida a una pertenencia explícita (PROBADA la reducción; pertenencia MEDIDA en q = 9, 27)
Lema E impar (misma derivación que en la misión 1, con x_{2k} = −ℓ, x_{2k−1} = ℓ − ε_1): J̄'_1 = K'_0 + ε_1N' en F_3[y_0..y_{2k−2}], K'_0 = (P'_3..P'_{2k−1}, y^q), y como P'_{2k+1} = 0 (sólo 2k−1 variables), E_{2k+1} ≡ ℓ·ε_1ε_{2k−1} tiene parte libre nula, luego **ε_{2k−1} = y_0⋯y_{2k−2} ∈ N'** para todo k. R'_{q−1} = (J̄'_1 : ε_1^{q−1}) + (ε_1).
Para k = 2: P'_3 = ε_3 − ε_1ε_2 = −(y_0+y_1)(y_0+y_2)(y_1+y_2). Sicigias de Lema F: g_3 = (y_i+y_j)^{q−1} da g_3P'_3 = −(y_i^q+y_j^q)(…) ∈ (y^q), luego **ε_1(y_i+y_j)^{q−1} ∈ N'** y J̄'_1 ⊇ Jc := (P'_3, y^q, ε_1ε_3, ε_1²(y_i+y_j)^{q−1} : i<j) (PROBADO ⊆ J̄'_1).
Cálculo a mano: con u := y_0+y_1, P'_3 ≡ 0 da u·y_0y_1 ≡ −u y_2 ε_1, y ε_1^{q−1} = Σ_s(−1)^s u^{q−1−s}y_2^s; así ε_1^{q−1}y_0y_1 ≡ y_2^{q−1}y_0y_1 − ε_1y_2(ε_1^{q−1} − y_2^{q−1}) ≡ **y_0y_1y_2^{q−1}** mod (P'_3, y^q). Por tanto
> y_0y_1 ∈ R'_{q−1} ⟸ **y_0y_1y_2^{q−1} ∈ Jc** (MEDIDO cierto en q = 9, 27: `gen.log`, `odd2.log`; con ello R'_{q−1} ⊇ (ε_1, 𝔪²) y r'_{q−1} ≤ 3 = f'_{+1}(2,q)).
Lema que falta (exacto): «y_0y_1y_2^{q−1} ∈ (P'_3, y_0^q, y_1^q, y_2^q, ε_1ε_3, ε_1²(y_i+y_j)^{q−1}) en F_3[y_0,y_1,y_2]»; celda: (2,9).

### 1.5 Declaración de dos corridas fuera de regla
En `inter.m2` y `gen.m2` incluí por descuido la celda k = 3 impar con q = 9 (7 variables). Ambas tardaron segundos y < 300 MB, pero no están permitidas por la regla 10: **no uso sus números** (líneas «n=7 q=9» de `inter.log` y `gen.log`).

ESTADO: NO CONCLUYO.
Resumen PASO 1: PROBADO: palanca 1 muerta; fila +1 par: reducción exacta al Lema Π (Q ⊆ R_{q−1}) con gr G ⊆ Q probado (dado D(k−2)); fila +1 impar k = 1 (r' = 0); k = 2 par ⇐ Lema G-a (misión 1), k = 2 impar ⇐ pertenencia 1.4. MEDIDO: Q = R_{q−1} en 5 celdas; R'_{q−1} = sub-fila 1 de R_{q−1} en 3 celdas.
SIGUIENTE: PASO 2.

## PASO 2
PRESUPUESTO: 60 min (inicio 21:31; escribir desde 22:19). Motores: (1,9), (2,9), (2,27), (3,3), sólo lectura de generadores y certificados (< 1 min, < 300 MB por corrida).

### 2.1 Fila genérica PAR: reducción PROBADA a un lema de intersección; igualdad MEDIDA
Sea v ∉ {0, ±1}. F_v = ⋃_{(i,j) ordenados} {y_i = −v, y_j = −1} × Z_{2k−2}(y_{≠ij}). Agrupando (i,j) con (j,i): X_{ij} ∪ X_{ji} = {(y_i,y_j) ∈ {(−v,−1), (−1,−v)}} × Z_{2k−2}(resto), un PRODUCTO de conjuntos finitos en variables disjuntas. Para productos: I(X×Y) = I(X) + I(Y) (el cociente es I(X)-álgebra ⊗ I(Y)-álgebra, reducido y de dimensión |X||Y|), y una GB por grado de I(X)+I(Y) es la unión de las GB (términos líderes coprimos), luego **gr(I(X)+I(Y)) = gr I(X) + gr I(Y)**. Dos puntos distintos (v ≠ 1) en el plano (y_i,y_j): I = (y_i + y_j + v + 1, (y_i+v)(y_i+1)), GB por grado, formas tope (y_i + y_j, y_i²) ∋ y_iy_j, y_j². Con D(k−2):
 gr I(X_{ij} ∪ X_{ji}) = **Q^gen_{ij} := (y_i + y_j, y_i², y_iy_j, y_j²) + I^{(2k−2)}(y_{≠ij})** (independiente de v), y **gr G_{2k}({v,1}) ⊆ Q^gen := ∩_{i<j} Q^gen_{ij}** (PROBADO).
> **Reducción (PROBADA).** Si **Q^gen ⊆ R_2** (Lema Π^gen) entonces r_2 ≤ dim S/gr G = f_gen, y por monotonía r_a ≤ f_gen para 2 ≤ a ≤ q−2.
- **MEDIDO: Q^gen = R_2 como ideales** en (1,9), (2,9), (2,27), y también = R_3 en (2,9) (`gen.log`; dims 2, 84, 300 = f_gen). Para la fila +1 el mismo esquema con un solo punto da Q_{ij} = (y_i,y_j) + I^{(2k−2)} (§1.2): **ambas filas exteriores pares son intersecciones de ideales de piezas**, y las interiores no (fila 1: 49 ≠ 88 en (2,9), `odd2.log`).
- k = 1: PROBADO (misión 1, r_2 = 2). k = 2: **Q^gen = (e_1, e_3, e_4, x_i²x_j^{q−2} : i≠j, caja)** en (2,9), (2,27) (`paso2c.log`), y (e_1, e_3, e_4, caja) ⊆ R_2 está PROBADO (misión 1, §2.3(a)); luego **Lema Π^gen(k=2) ⟺ Lema G-a** (x_i²x_j^{q−2} ∈ R_2). Sigue pendiente.
- Lema que falta (exacto, k general): «∩_{i<j}[(y_i+y_j, y_i², y_iy_j, y_j²) + I^{(2k−2)}(y_{≠ij})] ⊆ R_2». Celda: (2,9) (cierto), (3,9) no permitida.

### 2.2 Fila genérica IMPAR, k = 2: PROBADA para todo q ≥ 9
**Lema E impar** (misma derivación que el Lema E de la misión 1, con x_{2k} = −ℓ, ℓ = e_1(x_0..x_{2k−1}), x_{2k−1} = ℓ − ε_1): J̄'_1 = K'_0 + ε_1N' ⊂ F_3[y_0..y_{2k−2}], K'_0 = (P'_3, …, P'_{2k−1}, y^q), P'_j = ε_j − ε_1ε_{j−1}; como P'_{2k+1} = 0, la parte libre de E_{2k+1} ≡ ℓ·ε_1ε_{2k−1} es nula y **ε_1ε_{2k−1} ∈ J̄'_1**. Filas: **R'_a = (J̄'_1 : ε_1^a) + (ε_1)**. Verificado numéricamente: reproduce TODAS las filas impares de (1,9), (2,3), (2,9), (3,3) (`paso2b.log`, primeras líneas).
Para k = 2 (3 variables y_0,y_1,y_2): J̄'_1 ⊇ L_0 := (P'_3, ε_1ε_3), con P'_3 = −(y_0+y_1)(y_0+y_2)(y_1+y_2). Sea L := L_0 + (ε_1³). Si ε_1²f ∈ L entonces ε_1²(f − ε_1β) ∈ L_0 ⊆ J̄'_1, luego f ∈ R'_2. Por tanto **R'_2 ⊇ (L : ε_1²) + (ε_1)**, un ideal que NO depende de q. Cálculo finito (`paso2a.log`): ε_1²(y_1−y_2)² ∈ L, ε_1²y_2³ ∈ L y **dim F_3[y]/((L : ε_1²) + (ε_1)) = 6**. En coordenadas reducidas (L:ε_1²)+(ε_1) ⊇ ((y_1−y_2)², y_2³) y F_3[y_1,y_2]/((y_1−y_2)², y_2³) ≅ F_3[w,y_2]/(w², y_2³) tiene dimensión 6 = f'_gen(2,q) (las 6 permutaciones de (−v,−1,0)). ∎
> **r'_a(2,q) ≤ 6 = f'_gen(2,q) para 2 ≤ a ≤ q−2 y todo q ≥ 9. PROBADO.** (Coincide con la fila medida R'_2 = (e_1, x_1²+x_1x_2+x_2², x_2³) en (2,9), (2,27): `odd2.log`.)

### 2.3 Fila genérica IMPAR, k = 1: PROBADA (r'_a = 0)
1 ∈ R'_a ⟺ x_1^ax_2 ∈ I^{(3)} + (x_2², x_1^{a+1}x_2). Como e_3 ≡ −x_1²x_2 mod (e_1, x_2²), x_1^ax_2 ∈ I^{(3)} + (x_2²) para a ≥ 2. Luego r'_a = 0 = f'_v(1,q) (v genérico: haría falta −v y −1 en una sola coordenada). ∎ Igual que en §1.3 con a = q−1.

### 2.4 La identidad «+» de nivel 2 (MEDIDA) y lo que implicaría
Para |A| = |B| = 2 y C = [2k+1] ∖ (A∪B): **x_C(x_A^{q−1} + x_B^{q−1}) ∈ J_0** en (2,9), (2,27), (3,3) (`paso2a.log`); x_C(x_A^{q−1} − x_B^{q−1}) ∉ J_0 (ese es el Lema Φ, que vive en J_1). Con el Lema Φ: 2x_Cx_A^{q−1} ∈ J_1, i.e. **x_Cx_A^{q−1} ∈ J_1 para |A| = 2** (medido directamente: true). Detector que lo explica (palanca 2): en Z_{2k+1} con x_C ≠ 0 el número de no nulos en A∪B es impar, y [A todo ≠0] + [B todo ≠0] = [#≠0 = 3] = 1 − Σ_{i∈A∪B}x_i^{q−1}; así x_C·[x_A^{q−1} + x_B^{q−1} − 1 + Σ_{A∪B}x_i^{q−1}] se anula en Z_{2k+1} y su forma tope es la identidad. Pero eso sólo prueba pertenencia a gr I(Z_{2k+1}) ⊇ J_0, no a J_0 (sería circular con D'(k)); el certificado algebraico de M2 tiene 562 términos en el multiplicador de e_1 (`paso2b.log`) y no he encontrado su forma general (el telescopado de (U-a+) no se extiende directamente).
Consecuencias si se prueba para todo k: (a) k = 2: x_cx_a^{q−1}x_4^{q−1} ∈ J_1 ⇒ x_cx_a^{q−1} ∈ R_{q−1} (Lema U-b) ⇒ con U-a y la cuenta 6q−8, **la fila +1 par de k = 2 queda probada sin pasar por G-a**; (b) k general: x_Cx_{A'}^{q−1} ∈ R_{q−1} para |A'| = j−1 ≤ k−1, |C| = 2k+1−2j; y MEDIDO en (2,9), (2,27), (3,3): **R_{q−1} = (e_impar, x_Cx_{A'}^{q−1} : 0 ≤ |A'| ≤ k−1, caja)** (`paso2b.log`, `inter2.log`), de modo que la fila +1 par de todo k se reduciría a la identidad «+» en todos los niveles j ≤ k más la conjetura de generación.

ESTADO: NO CONCLUYO.
Resumen PASO 2: PROBADO: fila genérica impar para k = 1 y k = 2 (todo q ≥ 9); reducción exacta de la fila genérica par al Lema Π^gen (gr G ⊆ Q^gen probado dado D(k−2)); Π^gen(k=2) ⟺ G-a. MEDIDO: Q^gen = R_2 en 3 celdas; identidad «+» de nivel 2.
SIGUIENTE: PASO 3.

### 2.5 Fila +1 IMPAR, k = 2: PROBADA para todo q por transferencia sobre un esquema fijo
(Cierra el lema pendiente del §1.4.) Sea I_Z := (P'_3, ε_1ε_3) ⊂ F_3[y_0,y_1,y_2]. Es la intersección completa (ē_3, ē_4) de la misión 1 (P'_3 = e_3(y,−ε_1), ε_1ε_3 = −e_4(y,−ε_1)), luego es un ideal SATURADO, de dimensión 1 en P², grado 12 (`transfer.log`: saturado, grado 12; su radical son 6 puntos F_3-racionales [1:0:0], [0:1:0], [0:0:1], [1:−1:0], [1:0:−1], [0:1:−1], cada uno con componente primaria de grado 2, es decir un punto doble curvilíneo Spec F_3[ε]/ε² con dirección tangente F_3-racional).
Para f homogéneo: f ∈ I_Z ⟺ f|_Z = 0 ⟺ en cada punto doble (p, δ): f(p) = 0 y δ·∇f(p) = 0 (I_Z saturado). Por tanto, para el ideal I_Z + (y^q) en grado d:
 f ∈ I_Z + (y^q)_d ⟺ f|_Z ∈ span{ (y_i^q·m)|_Z : m monomio de grado d−q }.
**Independencia de q.** En un punto p ∈ F_3³ y dirección δ ∈ F_3³: (y_i^q)(p) = y_i(p), ∇(y_i^q) = 0 (char 3); (y^{q−1})(p) = y(p)², (y^{q−1})' = −y^{q−2} = −y(p)·… con y^{q−2}(p) = y(p) (pues y ∈ F_3 ⇒ y^{q−2} = y); (y^{q})' = 0. Así las restricciones a Z de g_q := y_0y_1y_2^{q−1} − ε_1²(y_0+y_1)^{q−1} y de los generadores de la caja en grado q+1 son las MISMAS para todo q = 3^v. Luego la condición «g_q ∈ I_Z + (y^q)» es una única condición de álgebra lineal en un F_3-espacio fijo, y se decide en una celda: es cierta en q = 3, 9, 27 (`transfer.log`), luego **para todo q = 3^v**.
Como ε_1²(y_0+y_1)^{q−1} ∈ ε_1N' ⊆ J̄'_1 (§1.4) y I_Z ⊆ J̄'_1: **y_0y_1y_2^{q−1} ∈ J̄'_1**, luego (§1.4) y_0y_1 ∈ R'_{q−1}, y por S_3-simetría 𝔪² ⊆ R'_{q−1}. Con ε_1 ∈ R'_{q−1}: **r'_{q−1}(2,q) ≤ dim F_3[y]/(ε_1, 𝔪²) = 3 = f'_{+1}(2,q). PROBADO para todo q.** ∎
(No es la vía muerta 5: no se sube de q = 3 a q = 9 por Frobenius, sino que la condición es literalmente la misma para cada q porque sólo involucra valores y derivadas en puntos F_3-racionales de un esquema fijo.)
**Por qué el mismo truco NO cierra G-a ni U-b (k = 2 par):** allí el ideal fijo es (P_3, P_5) ⊂ F_3[x_0..x_3], intersección completa de grados 3, 5 cuyo esquema es la unión de 15 RECTAS F_3-racionales (3 rectas {(w,−w,u,−u)} y 12 del tipo {(0,w,−w,u)}), de dimensión 1: las restricciones de x^{q−1} a una recta son polinomios en el parámetro que SÍ dependen de q, y el problema de pegado en H⁰(O_C(q+2)) crece con q. Recta a recta el objetivo de G-a sí cae en (caja + ε_1³·S)|_L; falta el pegado global.

**Actualización del ESTADO del PASO 2 tras §2.5:** NO CONCLUYO en general, pero **las dos filas exteriores IMPARES de k = 2 quedan PROBADAS para todo q** (genérica §2.2, +1 §2.5), y las de k = 1 también (§1.3, §2.3). Las filas exteriores PARES de k = 2 dependen sólo del Lema G-a (o, para la fila +1, de la identidad «+» de nivel 2, §2.4). Corridas del paso: todas < 30 s y < 300 MB (`*.time`).

## PASO 3
ESTADO: CERRADO
PRESUPUESTO: 30 min (inicio 21:36).

### 3.1 Qué parte del Teorema de las Filas Exteriores queda PROBADA
| nivel | paridad | filas genéricas (2 ≤ a ≤ q−2) | fila +1 (a = q−1) |
|---|---|---|---|
| k = 1 | par | PROBADA (misión 1: r_2 = 2) | PROBADA (misión 1: r_{q−1} = 1) |
| k = 1 | impar | PROBADA §2.3 (r'_a = 0) | PROBADA §1.3 (r'_{q−1} = 0) |
| k = 2 | impar | **PROBADA §2.2 (r'_a ≤ 6), todo q ≥ 9** | **PROBADA §2.5 (r'_{q−1} ≤ 3), todo q** |
| k = 2 | par | ⇐ Lema G-a (misión 1; ⟺ Lema Π^gen(2), §2.1) | ⇐ Lema G-a vía U-b, o ⇐ identidad «+» de nivel 2 (§2.4) |
| k ≥ 3 | par | ⇐ Lema Π^gen: Q^gen ⊆ R_2 (§2.1) | ⇐ Lema Π: Q ⊆ R_{q−1} (§1.2) |
| k ≥ 3 | impar | sin reducción (las piezas no bastan, §1.3) | sin reducción; MEDIDO R'_{q−1} = sub-fila 1 de R_{q−1} |

### 3.2 Aplicación de la cadena del §2.6
Base k = 0 (dada). **Nivel k = 1:** todas las filas exteriores probadas ⇒ pasos 1–4 del §2.6 ⇒ **D'(1), D(1) y c_1 ≤ N_1, para todo q = 3^v** (coincide con lo que el proyecto ya tenía para niveles bajos; aquí sale de la cadena).
**Nivel k = 2, paso 1 (impar):** c'_2 = Σ_a r'_a ≤ r'_0 + r'_1 + (q−3)·r'_2 + r'_{q−1} ≤ A'_1 + c_1 + (q−3)·6 + 3 = P'_1 + N_1 + Σ_{v∉{−1,0}} f'_v = N'_2, usando r'_0 ≤ A'_1 = P'_1 (D'(1)), r'_1 ≤ c_1 ≤ N_1 (nivel 1), §2.2 y §2.5 (para q = 3 sólo hay a = 2 = q−1, cubierto por §2.5). **Paso 2:** A'_2 ≤ A_1 + (q−1)N'_2 = P_1 + (q−1)N'_2 = P'_2, y con el SUELO:
> **D'(2): A'_2 = P'_2 = |Z_5| para todo q = 3^v. PROBADO.** (Comprobación en (2,3): c'_2 = 7+6+3 = 16 = N'_2(3) (`tablero_impar.log`), y A'_2 = A_1 + (q−1)c'_2 = 19 + 2·16 = 51 = |Z_5(F_3)| = 1 + 20 + 30 (cinco ceros; tres ceros y un par ±1; un cero y dos pares). En (2,9): c'_2 = 25 + 24 + 6·6 + 3 = 88 = c'_2 del §4 de la misión 1.)
**Nivel k = 2, pasos 3–4 (par):** c_2 ≤ P_1 + N'_2 + (q−3)r_2 + r_{q−1} necesita r_2 ≤ f_gen y r_{q−1} ≤ f_{+1}, i.e. el Lema G-a. Con G-a: D(2) y c_2 ≤ N_2 para todo q. Sin él, la cadena se detiene aquí (D(2) es conocido por otra vía, pero c_2 ≤ N_2, que necesita el nivel 3, no).
**Niveles k ≥ 3:** requieren los Lemas Π y Π^gen (pares) y las filas impares, sin reducción.

### 3.3 Los lemas exactos que faltan, en orden de coste
1. **Lema G-a** (cierra k = 2 entero y da c_2 ≤ N_2): «en F_3[x_0..x_4], x_4²x_0²x_1^{q−2} ∈ (e_1, e_3, e_5, x_0^q..x_4^q, x_ax_ix_j(x_l^{q−1} − x_m^{q−1})) + (x_4³)». Celdas: (2,9), (2,27), ciertas. Obstáculo identificado (§2.5): el esquema fijo asociado es una curva de 15 rectas, no puntos; el pegado global en H⁰(O_C(q+2)) depende de q.
2. **Identidad «+» de nivel j** (alternativa a G-a para la fila +1 par y pieza de la fila +1 par general): «x_C(x_A^{q−1} + x_B^{q−1}) ∈ (e_1, e_3, …, e_{2k+1}, x^q) para |A| = |B| = j, C = [2k+1]∖(A∪B)». j = 1 probada (misión 1); j = 2 cierta en (2,9), (2,27), (3,3). Su detector (§2.4) muestra que es la forma tope de un polinomio que se anula en Z_{2k+1}.
3. **Lema Π** (fila +1 par, todo k): «∩_{i<j}[(y_i,y_j) + I^{(2k−2)}(y_{≠ij})] ⊆ R_{q−1}»; celdas (2,9), (3,3), ciertas con igualdad. Generación MEDIDA: Q = (e_impar, x_Cx_{A'}^{q−1} : |A'| ≤ k−1, caja) en (2,9), (2,27), (3,3).
4. **Lema Π^gen** (fila genérica par, todo k): «∩_{i<j}[(y_i+y_j, y_i², y_iy_j, y_j²) + I^{(2k−2)}(y_{≠ij})] ⊆ R_2»; celdas (2,9), (2,27), ciertas con igualdad.
5. **Filas impares, k ≥ 3:** ninguna reducción probada. Pista MEDIDA: R'_a = π(R_a : y_{2k−1}) para a ∈ {2, q−1} (sub-fila 1 de la fila par), en (2,9), (2,27), (3,3).
SIGUIENTE: PASO 4.

## PASO 4 — VEREDICTO
ESTADO: CERRADO. (Inicio 21:40; presupuesto 15 min.)

**Probado en este turno (de lápiz, con la prueba en el informe):**
- Palanca 1 muere: π∘φ_v = π, luego el cizallamiento deja J_1 y todas las filas invariantes (§1.1).
- Fila +1 par, todo k: gr G_{2k}({1,1}) ⊆ Q := ∩_{i<j}[(y_i,y_j) + I^{(2k−2)}] dado D(k−2); reducción al Lema Π (§1.2). Fila genérica par, todo k: gr G_{2k}({v,1}) ⊆ Q^gen; reducción al Lema Π^gen (§2.1). En k = 2, Π^gen ⟺ G-a (`paso2c.log`).
- Lema E impar (§2.2), verificado en 4 celdas (`paso2b.log`).
- Filas exteriores IMPARES: k = 1 (§1.3, §2.3) y **k = 2 para todo q** (§2.2 por un cálculo finito independiente de q; §2.5 por transferencia sobre el esquema Z de 6 puntos dobles, `transfer.log`).
- **D'(2) para todo q = 3^v** (§3.2), por la cadena del §2.6.

**Medido (con celda):** Q = R_{q−1} en (1,9), (2,3), (2,9), (2,27), (3,3) (`inter.log`, `inter2.log`); Q^gen = R_2 en (1,9), (2,9), (2,27) y = R_3 en (2,9) (`gen.log`); identidad «+» de nivel 2 en (2,9), (2,27), (3,3) (`paso2a.log`); R'_{q−1} = sub-fila 1 de R_{q−1} en (2,9), (2,27), (3,3) (`inter2.log`); R_{q−1} = (e_impar, x_Cx_{A'}^{q−1}, caja) en (3,3) (`paso2b.log`).

**No probado:** Lema G-a (k = 2 par); Lemas Π, Π^gen (k ≥ 3 par); filas impares k ≥ 3. Frase exacta y celda de cada uno en §3.3.

**Números citados:** r'_2(2,q) = 6 = f'_gen(2,q) y r'_{q−1}(2,q) = 3 = f'_{+1}(2,q) (`tablero_impar.log` en (2,9); `odd2.log` en (2,27)); dim Y/((L:ε_1²)+(ε_1)) = 6 (`paso2a.log`); I_Z: grado 12, radical de grado 6, 6 primarias de grado 2 (`transfer.log`); 49 vs 46 y 157 vs 154 (`inter2.log`); 126 vs 90 en (3,3) (`inter2.log`); 84 = 12(9−2), 300 = 12(27−2) (`gen.log`). Todas las corridas: < 30 s, < 300 MB (`*.time`).

**Fuera de regla (declarado):** dos corridas accidentales de la celda k = 3 impar, q = 9 (§1.5); sus números no se usan.

**Sobre MISION_2.md:** sin errores detectados. Precisión útil: para la paridad impar, la descomposición en piezas de §1.2 NO da gr de la fibra (§1.3), así que el §3 no admite el mismo tratamiento en las dos paridades.

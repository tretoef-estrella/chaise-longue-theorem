# MISIÓN 2 «LAS FILAS EXTERIORES» — CERRAR LA CONJETURA
*(Grepy el Cartógrafo, 2026-09-21. Autocontenida. Todos los números están comprobados por dos rutas, y se dice cuáles.)*

> **OBJETIVO: probar el TEOREMA DE LAS FILAS EXTERIORES (§3). Junto con lo que ya está probado (§2), CIERRA LA CONJETURA 1.2 DE DEGTYAREV–SHIMADA PARA TODO `k` Y TODO `q = 3^v`, por inducción en `k`.** No es un paso intermedio: la cadena del §2.6 está escrita entera, y sólo falta la pieza del §3.

---
## 0 · REGLAS DEL TURNO (obligatorias)
1. **ANTES DE PENSAR:** crea `INFORME_2.md` con las secciones vacías `## PRIMERA LÍNEA` · `## PASO 0` · `## PASO 1` · `## PASO 2` · `## PASO 3` · `## PASO 4 — VEREDICTO`. **Cada paso se escribe BAJO SU PROPIO TÍTULO.**
2. **Graba en disco tras cada paso.** Lo que no está escrito no existe.
3. **Cabecera por paso:** `ESTADO: CERRADO | AGOTADO | NO CONCLUYO` y `SIGUIENTE:`.
4. **En orden; sin vuelta atrás, sin paso 5, sin reintentos.** Presupuesto escrito antes de cada paso; 10 min sin avance real ⟹ paras, escribes y declaras. **El último 20 % del presupuesto es para escribir.**
5. **Como mucho una búsqueda de literatura por paso**, en fuente original. Una buena candidata: *orbit harmonics* / anillo `gr I(X)` de un conjunto finito de puntos.
6. **No recalcules lo que aquí se da por verificado.**
7. **Una dimensión negativa, o mayor que la caja, es un fallo:** para.
8. **«Esta vía muere, por esta razón» es un resultado.**
9. **Escribe SÓLO en esta carpeta. No abras nada de `~/Desktop/ARBOLYAML/`.**
10. **Máquina:** `/opt/homebrew/bin/M2`. Menos de **1,2 GB y 10 min** por corrida, con la estimación escrita antes. **Celdas permitidas:** `k ≤ 2` con `q ≤ 27`, y `k = 3` con `q = 3`.
11. **Relee el disco antes del veredicto.**

**PRIMERA LÍNEA:**
- (a) ¿probaste el Teorema de las Filas Exteriores, entero o en parte (qué filas, qué paridad, qué `k`, qué `q`)?
- (b) si no, ¿qué lema exacto falta, y en qué celda se comprueba?
- (c) ¿cierra la conjetura? Contesta SÍ o NO, con la razón en una línea.

---
## 1 · LOS OBJETOS

**Parámetros:** `k ≥ 0`, `q = 3^v` con `v ≥ 1`, y `F_q` el cuerpo de `q` elementos.

**Anillos y cajas.**
- Para `N` variables: `S_N := F_3[x_0..x_{N−1}]`, y `e_j^{(N)}` es el simétrico elemental de grado `j`.
- **`I^{(N)} := (e_1, e_3, e_5, …) + (x_0^q, …, x_{N−1}^q)`**: todos los simétricos IMPARES más la caja.
- **`A(N) := dim_{F_3} S_N / I^{(N)}`**.
- Con `N = 2k+2` se escribe `A_k := A(2k+2)` (**nivel PAR** `k`); con `N = 2k+1`, `A'_k := A(2k+1)` (**nivel IMPAR** `k`).

**Puntos.**
- **`Z_N := {x ∈ F_q^N : #{i : x_i = v} = #{i : x_i = −v} para todo v ∈ F_q}`** (multiconjunto cerrado bajo negación).
- `P_k := |Z_{2k+2}|` y `P'_k := |Z_{2k+1}|`.
- **Lema (probado):** `x ∈ Z_N ⟺ ∏_i(1 + x_it)` es un polinomio PAR en `t` ⟺ los coeficientes impares, que son los `e_{impar}(x)`, se anulan. *(Par ⟺ igual a `∏(1 − x_it)` ⟺ los multiconjuntos `{x_i}` y `{−x_i}` coinciden.)*

**LA CONJETURA:** **`D(k)`: `A_k = P_k`** para todo `k` y todo `q = 3^v`. Su gemela impar es **`D'(k)`: `A'_k = P'_k`**.

**Las casillas** (con `x_{N−1}` como última variable):
- `J_1^{(N)} := π(I^{(N)} : x_{N−1})`, con `π : x_{N−1} ↦ 0`, es un ideal de `S_{N−1}`.
- **Casilla par** `c_k := dim S_{2k+1}/J_1^{(2k+2)}`; **casilla impar** `c'_k := dim S_{2k}/J_1^{(2k+1)}`.
- **Rebanadas:** **`N_k := #{y ∈ F_q^{2k+1} : (y,1) ∈ Z_{2k+2}}`** y **`N'_k := #{y ∈ F_q^{2k} : (y,1) ∈ Z_{2k+1}}`**.

**LAS FILAS DEL TABLERO** (la variable siguiente es `x_{N−2}`; `π'` pone `x_{N−2} ↦ 0`):
- **`R_a := π'(J_1^{(2k+2)} : x_{2k}^a) ⊂ S_{2k}`** y `r_a := dim S_{2k}/R_a` (**par**);
- **`R'_a := π'(J_1^{(2k+1)} : x_{2k−1}^a) ⊂ S_{2k−1}`** y `r'_a := dim S_{2k−1}/R'_a` (**impar**);
- con `a = 0, …, q−1`.

**LAS FIBRAS** (con `v ∈ F_q`):
- **`F_v := {y ∈ F_q^{2k} : (y, v, 1) ∈ Z_{2k+2}}`** (par), y `f_v := |F_v|`;
- **`F'_v := {y ∈ F_q^{2k−1} : (y, v, 1) ∈ Z_{2k+1}}`** (impar), y `f'_v := |F'_v|`.

**DICCIONARIO fila ↔ valor** (el mismo en las dos paridades): `a = 0 ↔ v = −1` · `a = 1 ↔ v = 0` · **`2 ≤ a ≤ q−2 ↔ v` genérico** (`v ∉ {0, ±1}`; hay `q−3`, y todos dan la misma cuenta) · **`a = q−1 ↔ v = +1`**. Si `q = 3`, las filas son sólo `a = 0, 1, 2 ↔ −1, 0, +1`.

**EL IDEAL EXPLÍCITO DE CADA FIBRA.**
- Para un multiconjunto `c` de valores de `F_q` y `m` variables `y_0..y_{m−1}`, se define **`E_m(c)`** como el ideal de `F_q[y]` generado por los **coeficientes de grado IMPAR en `t`** de `∏_{i<m}(1 + y_it)·∏_{γ∈c}(1 + γt)`.
- **`G_m(c) := E_m(c) + (y_0^q − y_0, …, y_{m−1}^q − y_{m−1})`**.
- Su conjunto de ceros es `{y ∈ F_q^m : {y} ∪ c cerrado}`, y **`G_m(c)` es RADICAL** (prueba de dos líneas en el §2.2).
- **`gr 𝔞`** es el ideal de las formas tope (componente homogénea de grado máximo) de los elementos de `𝔞`.

---
## 2 · LO QUE YA ESTÁ PROBADO (úsalo; no lo reprobar)

**2.1 · Hechos de libro.**
- `dim K[x]/gr 𝔞 = dim K[x]/𝔞`.
- Para `X ⊂ K^m` finito, `dim K[x]/I(X) = |X|`.

**2.2 · Radicalidad y SUELO.**
- `F_q[y]/(y_i^q − y_i)` es un producto de copias de `F_q`, luego reducido, y todo cociente suyo también. Así **`G_m(c) = I(ceros)`** y **`dim F_q[y]/gr G_m(c) = #{y : {y} ∪ c cerrado}`**.
- Con `c = ∅`: `gr G_N(∅) ⊇ I^{(N)} ⊗ F_q`, porque `e_{impar}` son homogéneos y `x^q = top(x^q − x)`. Luego **`A(N) ≥ |Z_N|`: `A_k ≥ P_k` y `A'_k ≥ P'_k`, para todo `k` y `q`** (SUELO).

**2.3 · Capas y la escalera** (probado para todo `k` y `q`).
- `A(N) = Σ_{a=0}^{q−1} dim S_{N−1}/π(I : x_{N−1}^a)`. Las capas son cadenas CRECIENTES de ideales, así que sus dimensiones DECRECEN.
- La capa `a = 0` es `I^{(N−1)}`, porque `e_j(x_0..x_{N−2}, 0) = e_j^{(N−1)}`.
- ⟹ **`A_k ≤ A'_k + (q−1)·c_k`** y **`A'_k ≤ A_{k−1} + (q−1)·c'_k`**.
- Por puntos, escalando la última coordenada no nula: **`P_k = P'_k + (q−1)N_k`** y **`P'_k = P_{k−1} + (q−1)N'_k`**.

**2.4 · Filas.**
- **Capas:** `c_k = Σ_a r_a` y `c'_k = Σ_a r'_a`.
- **Monotonía:** `r_0 ≥ r_1 ≥ … ≥ r_{q−1}`, y lo mismo para `r'`.
- **Fibras:** `N_k = Σ_v f_v` y `N'_k = Σ_v f'_v`.
- **Filas interiores** (lápiz, de la inclusión `I^{(N)} ⊆ (I^{(N)} : x_{N−1})`):
  - **`r_0 ≤ A_{k−1}`** y **`r_1 ≤ c'_k`**;
  - **`r'_0 ≤ A'_{k−1}`** y **`r'_1 ≤ c_{k−1}`**.
  - *(Prueba: `π(I^{(N)})` pasa a `I^{(N−1)}`; aplicar `π'` y los colones conserva la inclusión.)*
- **Las fibras de las filas interiores:** `f_{−1} = P_{k−1}`, `f_0 = N'_k`, `f'_{−1} = P'_{k−1}` y `f'_0 = N_{k−1}`.
  - *Razón:* un `−1` junto al `+1` fijo forma pareja; un `0` junto al `1` convierte la rebanada en la de la otra paridad.

**2.5 · Fórmulas cerradas** (con `M = (q−1)/2` e `I_j(2t) := Σ_{a≥0} t^{2a+j}/(a!(a+j)!)`; comprobadas contra fuerza bruta):
- **Par:** `f_{−1} = (2k)![t^{2k}] cosh·I_0^M` · `f_0 = … sinh·I_1·I_0^{M−1}` · `f_gen = … cosh·I_1²·I_0^{M−2}` · `f_{+1} = … cosh·I_2·I_0^{M−1}`.
- **Impar:** con `(2k−1)![t^{2k−1}]`, se cambia `cosh ↔ sinh`: `f'_{−1} = … sinh·I_0^M` · `f'_0 = … cosh·I_1·I_0^{M−1}` · `f'_gen = … sinh·I_1²·I_0^{M−2}` · `f'_{+1} = … sinh·I_2·I_0^{M−1}`.
- En `k = 2`: `f_gen = 12(q−2)` y `f_{+1} = 2(3q−4)`.

**2.6 · LA CADENA QUE CIERRA** (probada; sólo falta el §3). Por inducción en `k`, con base **`k = 0`** trivial: `A_0 = P_0 = q`, `A'_0 = P'_0 = 1`, y `c_0 = N_0 = 1`.

Supón en el nivel `k−1`: `D(k−1)`, `D'(k−1)` y `c_{k−1} ≤ N_{k−1}`. Si en el nivel `k` valen las **FILAS EXTERIORES** del §3:
1. **Impar:** `c'_k = Σ r'_a ≤ r'_0 + r'_1 + Σ_{a≥2} r'_a ≤ P'_{k−1} + N_{k−1} + Σ_{v ∉ {−1,0}} f'_v = N'_k`.
2. De ahí `A'_k ≤ A_{k−1} + (q−1)N'_k = P_{k−1} + (q−1)N'_k = P'_k`, y con el SUELO, **`D'(k)`**.
3. **Par:** `c_k ≤ r_0 + r_1 + Σ_{a≥2} r_a ≤ P_{k−1} + N'_k + Σ_{v ∉ {−1,0}} f_v = N_k`.
4. De ahí `A_k ≤ A'_k + (q−1)N_k = P_k`, y con el SUELO, **`D(k)`**.

**⟹ `D(k)` para todo `k` y todo `q`.** Es la CONJETURA ENTERA.

**2.7 · De la misión 1** (tu `INFORME.md`, auditado y aprobado). **Lema A**, **Lema B** (`m ∈ R_a ⟺ x_{2k+1}x_{2k}^a m ∈ I + (x_{2k+1}², x_{2k+1}x_{2k}^{a+1})`), **Lema E**, **Lema F general**, **(U-a+) general** (re-verificada por el auditor como identidad exacta hasta `(4,9)`), el caso **`k = 1` par completo**, y el **Lema G-a**, pendiente para `k = 2`.

**2.8 · Del proyecto:**
- **TEOREMA P:** los detectores de paridad `G_{A,B} := (∏_{l∉A∪B} x_l)·[(−1)^{|A|}∏_A(1+x^{q−1}) − (−1)^{|B|}∏_B(1+x^{q−1})]` se anulan en la rebanada.
- **LEMA Φ:** si `|A| = |B|`, su forma tope está en `J_1`.
- *(Tu Lema F es el caso `|A| = |B| = 1`.)*

---
## 3 · EL OBJETIVO: TEOREMA DE LAS FILAS EXTERIORES
> ## Para todo `k ≥ 1`, todo `q = 3^v` y toda fila `a ∈ {2, …, q−1}`:
> ## **`r_a ≤ f_{v(a)}`** y **`r'_a ≤ f'_{v(a)}`**.
> ### Basta probar las INCLUSIONES **`gr G_{2k}({v(a), 1}) ⊆ R_a ⊗ F_q`** y **`gr G_{2k−1}({v(a), 1}) ⊆ R'_a ⊗ F_q`**, porque la dimensión de la izquierda es exactamente `f_{v(a)}` (resp. `f'_{v(a)}`) por el §2.2.

**Es lo único que falta. Por el §2.6, cierra la conjetura para todo `k` y todo `q`.**

**Lo medido** (`tablero_par.m2` y `tablero_impar.m2`, en esta carpeta): **las IGUALDADES `R_a ⊗ F_q = gr G_{2k}({v(a),1})` y `R'_a ⊗ F_q = gr G_{2k−1}({v(a),1})` valen COMO IDEALES en TODAS las filas probadas: 32 de 32.**
- Celdas: `(1,3)`, `(2,3)`, `(1,9)`, `(2,9)` y `(3,3)`, en las dos paridades.
- Incluidas las filas de fibra VACÍA, que salen ideal unidad.
- En `(3,3)` fue una predicción sellada, y acertó.
- **Control negativo:** en conjuntos de puntos al azar, las filas NO coinciden con sus fibras (falla en 4 de 5). **Es propio de este objeto.**

⚠️ **Falso y ya medido:** `gr(E(c)) + caja`, sin los `y^q − y`, NO sirve. Da 18 contra 16 en `(2,3)`.

**TRES PALANCAS DEL AUDITOR (úsalas o descártalas con razón):**
1. **El cizallamiento conserva la caja.** Para `v ∈ F_q`, el cambio `x_{2k} ↦ x_{2k} + v·x_{2k+1}` preserva `(x_i^q)`, porque `(x + vy)^q = x^q + v y^q` (ya que `v^q = v`). En el cono, la fibra de valor `v` es la rebanada `x_{2k} = v·x_{2k+1}` y `x_{2k+1} = 1`; el cizallamiento la manda a la de valor `0`. **Pregunta: ¿convierte la fila `a` en una fila `0` o `1` de otro problema del mismo tipo?** Si sí, el teorema se reduce a las filas interiores, que ya están acotadas.
2. **Detectores de la fibra.** El análogo del TEOREMA P para `F_{+1}` y `F_λ`: detectores de paridad sobre las coordenadas, más un detector de «el valor fijado tiene pareja». Tus monomios libres de cuadrados de grado `2k−1` (que ya caen en `R_{q−1}`) deben ser formas tope de alguno.
3. **Formas tope, no polinomios.** Para `gr ⊆ R` basta que la FORMA TOPE de cada elemento de un sistema generador **de Gröbner (orden por grado)** de `G(c)` caiga en `R`. Generadores cualquiera no bastan: hacen falta las formas tope de TODO el ideal. **Cuidado con este paso.**

---
## 4 · VÍAS MUERTAS (no las intentes)
1. **Cotas que sólo usan la función de Hilbert** (Macaulay, Gotzmann, Clements–Lindström): insuficientes (`1568` contra `855` en `(2,9)`).
2. **Lex game / Cerlienco–Mureddu con la variable `x_{2k}`:** la rebanada es un grafo; da `[N_k, 0, …]`. **El tablero es de GRADO.**
3. **Dualidades** (Matlis, Gorenstein): sólo dan enunciados equivalentes.
4. **Criterios hereditarios o locales por subfamilias:** refutados.
5. **Subir de `q = 3` a `q = 9` por Frobenius o por acciones multiplicativas:** imposible.
6. **Medir fuera de la regla 10.**
7. **Reprobar el TEOREMA P, el Lema Φ, tus lemas de la misión 1 o la cadena del §2.6.**

---
## 5 · PROCESO
- **PASO 0 · Calibración (10 min).** Corre `tablero_par.m2` y `tablero_impar.m2` tal cual (segundos). Comprueba `igual:true` en la última columna y `FIN-OK`.
- **PASO 1 · La fila del `+1` (`a = q−1`), las dos paridades, para todo `k` (60 min).** Es la fibra más pequeña y está definida sobre `F_3`. Prueba `gr G({1,1}) ⊆ R_{q−1}` y `⊆ R'_{q−1}`. **Empieza por la palanca 1**, y calibra en `k = 1, 2`.
- **PASO 2 · Las filas genéricas (`a = 2 … q−2`), las dos paridades, para todo `k` y `q ≥ 9` (60 min).** Por la monotonía basta la fila `a = 2`. Tu Lema G-a es el caso `k = 2`.
- **PASO 3 · Ensamblaje (30 min).** Escribe qué parte del §3 queda probada y aplica la cadena del §2.6: qué `D(k)` se siguen, y para qué `k` y `q`. Si falta algo, **una frase con el lema exacto y su celda**.
- **PASO 4 · Veredicto (15 min).** Cada número citado, con su celda y su comprobación.

---
## 6 · QUÉ ES ÉXITO
- **Pleno:** el Teorema de las Filas Exteriores para todo `k` y todo `q` ⟹ **LA CONJETURA 1.2, CERRADA.**
- **Parcial valioso:** la fila del `+1` para todo `k` en las dos paridades, o todas las filas para un `k` concreto, junto con el lema exacto que falta.
- **También vale:** una razón demostrada de que alguna palanca no puede funcionar.
- **No vale:** medidas como prueba, ajustes a datos, o enunciados sin su celda.

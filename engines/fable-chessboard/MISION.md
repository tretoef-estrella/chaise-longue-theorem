# MISIÓN «EL TABLERO» — autocontenida, de lápiz, con protocolo antibucle
*(Preparada por Grepy el Cartógrafo el 2026-09-21. Todos los números de este documento están verificados por dos rutas.)*

---
## 0 · LEE ESTO PRIMERO: LAS REGLAS DEL TURNO (obligatorias)

1. **ANTES DE PENSAR NADA,** crea en esta carpeta el fichero **`INFORME.md`** con estas secciones, vacías:
   `## PRIMERA LÍNEA` · `## PASO 0` · `## PASO 1` · `## PASO 2` · `## PASO 3` · `## PASO 4 — VEREDICTO`.
2. **Escribe en disco DESPUÉS DE CADA PASO**, no al final. Si el turno se corta, lo que esté en disco es la entrega. Lo que no esté escrito no existe.
3. **Cada paso lleva una cabecera** `ESTADO: CERRADO | AGOTADO | NO CONCLUYO`, más una línea `SIGUIENTE:`.
4. **Los pasos van en orden, no se vuelve atrás y no hay paso 5.** Si un paso agota su presupuesto, escribe `AGOTADO`, lo que tengas y por qué, y pasa al siguiente. **Prohibido reintentar.**
5. **Presupuesto por paso**, escrito en el informe antes de empezar el paso. Si pasan **10 minutos sin avance real**, paras, escribes lo que tienes y declaras el estado.
6. **Reserva el último 20 % del presupuesto para escribir.**
7. **Como mucho una búsqueda de literatura por paso**, y siempre en fuentes originales.
8. **No recalcules lo que este documento da por verificado.**
9. **Si una dimensión sale negativa o mayor que la caja, es un fallo de código, no un resultado:** para y dilo.
10. **«Esta vía muere, por esta razón» ES un resultado válido.** Escríbelo tal cual.
11. **Escribe SÓLO dentro de esta carpeta. NO abras NADA de `~/Desktop/ARBOLYAML/`.** Es el corpus del proyecto y está lleno de trampas de vocabulario. Todo lo que necesitas está aquí.
12. **Máquina:** Macaulay2 está en `/opt/homebrew/bin/M2`. Cada corrida debe quedar por debajo de **1,2 GB y 10 minutos**; escribe la estimación antes de lanzarla. **Celdas permitidas:** `k = 1` con `q ≤ 81`, `k = 2` con `q ≤ 27` y `k = 3` con `q = 3`. **Ninguna otra.** La celda `(3,9)` ya está medida aquí: tarda 5 minutos y no se repite.
13. **Antes de leer el informe final, relee el disco, no tu memoria.**

**En la PRIMERA LÍNEA del informe contestas tres cosas:**
- (a) ¿probaste (G) y/o (U), definidas en el §3, y para qué `k` y qué `q`?
- (b) si no, ¿dónde exactamente se rompe tu argumento?
- (c) ¿qué objeto o lema nuevo deja tu turno?

---
## 1 · EL OBJETO (definiciones exactas)

**Parámetros.** `k ≥ 1` es un entero; `n := 2k+2`. `q := 3^v` con `v ≥ 1` (así que `q ∈ {3, 9, 27, 81, …}`).

**Lado álgebra (coeficientes en `F_3`).**
- `S := F_3[x_0, …, x_{n−1}]`, y `e_j` es el polinomio simétrico elemental de grado `j` en `x_0, …, x_{n−1}`.
- **`I := (e_1, e_3, e_5, …, e_{2k+1}) + (x_0^q, x_1^q, …, x_{n−1}^q) ⊂ S`.** Son los `k+1` simétricos de grado impar más la «caja».
- `S' := F_3[x_0, …, x_{n−2}]` y `π' : S → S'` el morfismo que manda `x_{n−1} ↦ 0` y deja fijas las demás variables.
- `S'' := F_3[x_0, …, x_{n−3}]` y `π'' : S' → S''` el que manda `x_{n−2} ↦ 0`.
- Para ideales, `(J : f) := {g : fg ∈ J}`. La imagen de un ideal por `π'` o `π''` es un ideal, porque los morfismos son sobreyectivos.
- **`J_0 := π'(I)`** y **`J_1 := π'(I : x_{n−1})`**, ideales de `S'`.
- **Las filas del tablero:** para `a = 0, 1, …, q−1`, **`R_a := π''(J_1 : x_{n−2}^a) ⊂ S''`** y **`r_a := dim_{F_3} S''/R_a`**. Todas estas dimensiones son finitas.
- Dos números auxiliares: **`A_{k−1}(q) := dim_{F_3} S''/π''(J_0)`** y **`c'_k(q) := dim_{F_3} S''/π''(J_0 : x_{n−2})`**.

**Lado puntos (en el cuerpo `F_q`).**
- Para un entero `m`, **`Z_m := {x ∈ F_q^m : para todo v ∈ F_q, #{i : x_i = v} = #{i : x_i = −v}}`**. Es decir, el multiconjunto de coordenadas es cerrado bajo negación.
- **Lema (se da probado).** Si `m` es par y la característica es distinta de 2, entonces `x ∈ Z_m ⟺ e_1(x) = e_3(x) = … = e_{m−1}(x) = 0`.
  - *Prueba:* `∏_i(1 + x_i t)` es un polinomio par en `t` ⟺ es igual a `∏_i(1 − x_i t)` ⟺ los multiconjuntos `{x_i}` y `{−x_i}` coinciden. ∎
- **`V_1 := {y ∈ F_q^{n−1} : (y_0, …, y_{n−2}, 1) ∈ Z_n}`** (la «rebanada») y **`N_k(q) := |V_1|`**.
- **Fibras:** para `v ∈ F_q`, **`f_v := #{y ∈ V_1 : y_{n−2} = v}`**.
- **Cuatro clases de valor:** `v = −1`, `v = 0`, `v = +1`, y los **genéricos**, que son los `v ∉ {0, 1, −1}`. Hay `q − 3` genéricos (ninguno si `q = 3`).
- `f_v` es el MISMO para todos los genéricos, porque la cuenta sólo depende de qué coincidencias hay entre `1, −1, v, −v`. Se llama **`f_gen`**.
- Por tanto **`N_k = f_{−1} + f_0 + (q−3)·f_gen + f_{+1}`**.

---
## 2 · LO QUE YA ESTÁ PROBADO (no lo reprobar; úsalo)

**H1 (capas).** `dim S'/J_1 = Σ_{a=0}^{q−1} r_a`.
- *Prueba:* `x_{n−2}^q ∈ I ⊆ (I : x_{n−1})`, así que `x_{n−2}^q ∈ J_1`. En `M := S'/J_1`, cada cociente `x^a M / x^{a+1} M` (con `x = x_{n−2}`) es isomorfo a `S'/((J_1 : x^a) + (x)) ≅ S''/R_a`. ∎

**H2 (monotonía).** `r_0 ≥ r_1 ≥ … ≥ r_{q−1}`, porque `(J_1 : x^a) ⊆ (J_1 : x^{a+1})`.

**H3.** `r_0 ≤ A_{k−1}(q)`.
- *Prueba:* `I ⊆ (I : x_{n−1})`, luego `J_0 ⊆ J_1`, luego `π''(J_0) ⊆ R_0`.
- **Qué es `A_{k−1}(q)`:** `π''(J_0)` pone `x_{n−1} = x_{n−2} = 0`. Así `e_j ↦ e_j(x_0, …, x_{2k−1})` y `e_{2k+1} ↦ 0`. Queda **`(e_1, e_3, …, e_{2k−1}) + caja`** en `2k` variables: el MISMO objeto un nivel más abajo.

**H4.** `r_1 ≤ c'_k(q)`, porque `J_0 ⊆ J_1` implica `(J_0 : x_{n−2}) ⊆ (J_1 : x_{n−2})`.

**H5 (puntos, en fórmula cerrada).** Sean `M := (q−1)/2` e `I_j(2t) := Σ_{a≥0} t^{2a+j}/(a!(a+j)!)`. Entonces:
- `f_{−1} = (2k)!·[t^{2k}] cosh(t)·I_0(2t)^M`, que es `|Z_{2k}|` (la rebanada del nivel `k−1`);
- `f_0 = (2k)!·[t^{2k}] sinh(t)·I_1(2t)·I_0(2t)^{M−1}`;
- `f_gen = (2k)!·[t^{2k}] cosh(t)·I_1(2t)²·I_0(2t)^{M−2}`, para `q ≥ 5`;
- `f_{+1} = (2k)!·[t^{2k}] cosh(t)·I_2(2t)·I_0(2t)^{M−1}`.

*(Prueba: contar palabras de longitud `2k` con un desequilibrio fijado entre `v` y `−v`. Verificado en 12/12 celdas contra fuerza bruta y contra `N_k`.)*

**En polinomios de `q`** (válidos para todo `q` impar; en `q = 3` se usan todos salvo `f_gen`):

| `k` | `f_{−1}` | `f_0` | `f_gen` | `f_{+1}` |
|---|---|---|---|---|
| 1 | `q` | `2` | `2` | `1` |
| 2 | `3q²−3q+1` | `4(3q−5)` | `12(q−2)` | `2(3q−4)` |
| 3 | `15q³−45q²+55q−24` | `6(15q²−65q+81)` | `30(3q²−15q+23)` | `15(3q²−11q+12)` |
| 4 | `105q⁴−630q³+1645q²−2037q+918` | `8(105q³−840q²+2506q−2666)` | `56(15q³−135q²+475q−624)` | `28(15q³−105q²+280q−272)` |

**Contexto que el proyecto da por probado** (sólo para que sepas por qué importa; no lo necesitas en la prueba):
- `A_j(q) = |Z_{2j+2}|` para todo `j` cuando `q = 3`, y para `j ≤ 3` y todo `q`.
- En particular **`A_{k−1}(q) = f_{−1}` para `k ≤ 4`**.

---
## 3 · EL OBJETIVO (una sola cosa, en dos piezas)

Por H1–H4, si `A_{k−1}(q) = f_{−1}` y `c'_k ≤ f_0`, entonces
> `dim S'/J_1 ≤ f_{−1} + f_0 + (q−3)·r_2 + r_{q−1}`

(usando `r_a ≤ r_2` para `2 ≤ a ≤ q−2`, por H2). Por tanto **`dim S'/J_1 ≤ N_k`** se sigue de:

> ## **(G)** `r_2(k,q) ≤ f_gen(k,q)` para todo `k ≥ 1` y todo `q ≥ 9`.
> ## **(U)** `r_{q−1}(k,q) ≤ f_{+1}(k,q)` para todo `k ≥ 1` y todo `q ≥ 3`.

- **Por qué importa:** en el proyecto, `dim S'/J_1 ≤ N_k` (junto con su versión impar, `c'_k ≤ f_0`) cierra la conjetura en el nivel `k` por inducción, al mismo `q`. **(G) y (U) son las dos piezas nuevas que faltan.**
- ⚠️ **Están medidas con IGUALDAD** (tabla del §4). **No hay holgura:** una cota floja muere. La prueba tiene que ser exacta.
- **Sugerencia** (no obligatoria): para una cota SUPERIOR de `r_a` hay que exhibir SUFICIENTES elementos dentro de `R_a`, es decir, un conjunto explícito de polinomios de `R_a` cuyo cociente ya tenga dimensión `≤ f`. Mira qué polinomios de `S''` se anulan en la fibra `{y : y_{n−2} = v}` de la clase correspondiente.

---
## 4 · DATOS MEDIDOS (verificados; no los recalcules salvo en el PASO 0 para calibrar)

**Diccionario fila ↔ clase:** `a = 0 ↔ v = −1` · `a = 1 ↔ v = 0` · `2 ≤ a ≤ q−2 ↔ genéricos` · `a = q−1 ↔ v = +1`. En **TODAS** las celdas, **`r_a = f_{clase(a)}` exactamente**:

| celda `(k,q)` | `r_0, r_1, …, r_{q−1}` | `Σ r_a = dim S'/J_1 = N_k` | `A_{k−1}` | `c'_k` |
|---|---|---|---|---|
| `(1,3)` | 3, 2, 1 | 6 | 3 | 2 |
| `(1,9)` | 9, 2, 2×6, 1 | 24 | 9 | 2 |
| `(1,27)` | 27, 2, 2×24, 1 | 78 | 27 | 2 |
| `(2,3)` | 19, 16, 10 | 45 | 19 | 16 |
| `(2,9)` | 217, 88, 84×6, 46 | 855 | 217 | 88 |
| `(2,27)` | 2107, 304, 300×24, 154 | 9765 | 2107 | 304 |
| `(3,3)` | 141, 126, 90 | 357 | 141 | 126 |
| `(3,9)` | 7761, 4266, 3930×6, 2340 | 37947 | 7761 | 4266 |

*(`(2,27)` y `(3,9)` fueron predicción sellada ANTES de correr, y acertaron fila a fila.)*

- **Control negativo:** en conjuntos de puntos AL AZAR, las filas del ideal de puntos NO coinciden con sus fibras (falla en 4 de 5). **El fenómeno es propio de este objeto.**
- **Un nivel más adentro también vale:** partiendo cada `R_a` por `x_{n−3}`, las sub-filas coinciden con las sub-fibras por el valor de `y_{n−3}` (12 de 12 filas en `(2,3)` y `(2,9)`). Por ejemplo, en `(2,9)` la fila genérica da `{24, 24, 6×5, 3, 3}`.

---
## 5 · VÍAS MUERTAS (no las intentes; cada una tiene su prueba en el proyecto)

1. **Cotas que sólo usan la función de Hilbert** (Macaulay, Gotzmann, Clements–Lindström) aplicadas en grados bajos: están demostradas insuficientes. En `(2,9)` dan `1568` contra `855`.
2. **El «Lex game» / la recursión de Cerlienco–Mureddu:** con la variable `y_{n−2}`, `V_1` es un GRAFO sobre las demás coordenadas (esa coordenada queda forzada), así que la recursión lex da filas `[N_k, 0, …, 0]`. El tablero es un fenómeno de GRADO (ideales homogéneos), no del orden lex.
3. **Dualidades** (Matlis, Gorenstein, «el dual de este módulo»): sólo convierten el enunciado en otro EQUIVALENTE. Nunca han avanzado nada.
4. **Criterios «hereditarios» o locales** (que valgan para subfamilias): refutados.
5. **Subir resultados de `q = 3` a `q = 9` por Frobenius o por acciones multiplicativas:** imposible. En `F_3[x]/(x^9)` toda acción de ese tipo cae en `1 + (x^3)`.
6. **Medir celdas grandes para «ver el patrón»:** no. Las celdas permitidas están en la regla 12.

---
## 6 · PROCESO (cuatro pasos, cerrados)

**PASO 0 · Calibración (presupuesto 10 min).**
- Corre el script del §7 en `(1,9)` y `(2,3)` y comprueba que reproduces esas dos filas del §4.
- Si no las reproduces, **PARA**: el fallo es tuyo, no de los datos.

**PASO 1 · El caso `k = 1`, para todo `q`, de lápiz (presupuesto 30 min).**
- Aquí `S''` tiene sólo 2 variables.
- Describe `J_1` y `R_2`, `R_{q−1}` explícitamente (generadores y monomios estándar) y **prueba `r_2 = 2` para todo `q ≥ 9` y `r_{q−1} = 1` para todo `q ≥ 3`** (en `q = 3` la fila `a = 2` ES la del `+1`).
- Es el calentamiento: tiene que salir, y el mecanismo que uses es la pista para el paso siguiente.

**PASO 2 · El caso `k = 2`, para todo `q`, de lápiz (presupuesto 45 min).**
- Prueba **`r_2 ≤ 12(q−2)`** para `q ≥ 9` y **`r_{q−1} ≤ 2(3q−4)`** para `q ≥ 3`.
- Puedes calibrar con `q = 9, 27`. `S''` tiene 4 variables.

**PASO 3 · El caso general (presupuesto 45 min).**
- Intenta (G) y (U) con `k` como letra.
- Si no sale, escribe con precisión qué lema falta, en una sola frase, y en qué celda lo comprobarías.

**PASO 4 · Veredicto (15 min):**
- qué probaste, qué no, y qué objeto nuevo deja el turno;
- **todo número que cites, con su celda y su comprobación.**

---
## 7 · SCRIPT DE CALIBRACIÓN (Macaulay2; copia literal)
```
fil = (k,q) -> (
  n := 2*k+2; S := ZZ/3[x_0..x_(n-1)];
  el := j -> sum(subsets(gens S, j), s -> product s);
  I := ideal(apply(toList(0..k), i -> el(2*i+1))) + ideal(apply(gens S, v -> v^q));
  S1 := ZZ/3[x_0..x_(n-2)]; f1 := map(S1, S, gens S1 | {0_S1});
  J0 := f1(I); J1 := f1(I : x_(n-1));
  S2 := ZZ/3[x_0..x_(n-3)]; f2 := map(S2, S1, gens S2 | {0_S2});
  r := apply(toList(0..q-1), a -> numColumns basis(S2/f2(J1 : (x_(n-2))^a)));
  << "(k,q)=(" << k << "," << q << ") r=" << r << " suma=" << sum r << endl << flush;
);
fil(1,9); fil(2,3);
<< "FIN-OK" << endl; exit 0
```
- Guárdalo como `calib.m2` y córrelo con `M2 --script calib.m2 > calib.log`.
- Comprueba que la última línea sea `FIN-OK`: un log sin su última línea no es un resultado.
- *Aviso de M2:* no uses nombres de variables sueltas como `k`, `j`, `l`, `m`, `d`, `top` o `info` fuera de las funciones; colisionan.

---
## 8 · QUÉ ES ÉXITO Y QUÉ NO
- **Éxito pleno:** prueba de (G) y (U) para todo `k` y todo `q`.
- **Éxito parcial valioso:** prueba para `k ≤ 2` y todo `q`, más la frase exacta del lema que falta en general.
- **También vale:** una razón demostrada de que (G) o (U) no pueden probarse por el camino sugerido.
- **NO vale:** medidas nuevas presentadas como pruebas; «parece que»; fórmulas ajustadas a datos sin prueba; cualquier enunciado sin su celda de comprobación.

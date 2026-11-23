# Informe de corrección — Taller 3: Cauca con referencias y tipos

> Parte 5 del Taller 3. Todo el documento es Markdown, las fórmulas están en
> LaTeX y los diagramas en Mermaid.

**Curso:** Fundamentos de Interpretación y Compilación de Lenguajes
de Programación — Universidad del Valle, Sede Tuluá.

**Integrantes del grupo:**

| Nombre | Código | Correo institucional |
|--------|--------|----------------------|
| Oliver De Jesus Arboleda Baez | 2459684 | oliver.arboleda@correounivalle.edu.co |
| Maria Fernanda Betancourt Montoya | 2459510 | maria.fernanda.betancourt@correounivalle.edu.co |
| Kevin Andres Rosero Romo | 2459554 | rosero.kevin@correounivalle.edu.co |

---

## 1. Marco formal

### 1.1 Modelo del almacén

Un almacén es una secuencia finita de valores
$\sigma = [v_0, v_1, \ldots, v_{n-1}]$ con longitud $\lvert\sigma\rvert = n$.
Una referencia $\ell = \texttt{a-ref}(i)$ nombra la posición $i$ y se escribe
$\sigma(\ell) = v_i$ cuando $0 \le i < \lvert\sigma\rvert$. El almacén del
programa vive en la variable global `the-store`, y `set!` aparece
únicamente en `initialize-store!`, `newref!` y `setref!`. Por eso ninguna
otra parte del intérprete puede modificar el almacén.

Para formalizar la condición 1 del invariante se usa una variable fantasma
$D$: el conjunto de referencias que `newref!` ha entregado desde el último
`initialize-store!`.

### 1.2 Estrategia de demostración

Las propiedades sobre el almacén se demuestran por análisis del código de cada
operación, apoyado en dos lemas sobre listas que se prueban por inducción
estructural sobre la lista (sección 2.1). Las propiedades sobre el chequeador
se demuestran por inducción sobre la derivación de tipos. No hay programas
iterativos que requieran invariante de bucle.

---

## 2. Funciones y propiedades analizadas

### 2.1 El almacén preserva su invariante (5.1)

**Invariante.** Las cuatro condiciones del enunciado se formalizan así. Un
estado es el par $(\sigma, D)$ y

$$
\text{Inv}(\sigma, D) \;\equiv\; D = \{\, \texttt{a-ref}(i) \mid 0 \le i < \lvert\sigma\rvert \,\}
$$

es decir, toda referencia entregada apunta a una celda existente
(condición 1) y toda celda existente fue entregada por `newref!`. Las otras
tres condiciones son contratos de las operaciones:

- **(2)** $\lvert\sigma'\rvert = \lvert\sigma\rvert + 1$ si la operación es `newref!`, y
  $\lvert\sigma'\rvert = \lvert\sigma\rvert$ en cualquier otro caso.
- **(3)** Si $\sigma' = \texttt{setref!}(\sigma, \ell, v)$, entonces $\sigma'(\ell) = v$
  y $\sigma'(\ell') = \sigma(\ell')$ para todo $\ell' \neq \ell$.
- **(4)** `deref` sobre $\ell = \texttt{a-ref}(i)$ con $i < 0$ o
  $i \ge \lvert\sigma\rvert$ levanta `eopl:error`.

**Lema A (append).** Para toda lista $s$ y valor $v$,
$s' = \texttt{(append s (list v))}$ cumple $\lvert s'\rvert = \lvert s\rvert + 1$,
$s'(i) = s(i)$ para $i < \lvert s\rvert$ y $s'(\lvert s\rvert) = v$.

*Demostración* (inducción sobre $s$). Si $s$ es vacía, $s' = [v]$ y las tres
afirmaciones se cumplen. Si $s = a :: s_1$, entonces
$s' = a :: \texttt{(append } s_1 \texttt{ (list v))}$ y, por hipótesis de
inducción sobre $s_1$, las posiciones $\ge 1$ de $s'$ son las de $s_1$ con $v$
al final, y la posición $0$ es $a$. $\square$

**Lema B (reemplazar).** Sea $s$ una lista y $0 \le i < \lvert s\rvert$.
Entonces $s' = \texttt{(reemplazar s i)}$, definida como `(cons v (cdr s))` si
$i = 0$ y `(cons (car s) (reemplazar (cdr s) (- i 1)))` si $i > 0$, cumple
$\lvert s'\rvert = \lvert s\rvert$, $s'(i) = v$ y $s'(j) = s(j)$ para
$j \neq i$.

*Demostración* (inducción sobre $i$). Caso base $i = 0$: $s'$ es
`(cons v (cdr s))`, tiene la longitud de $s$ (porque $s$ no es vacía), su
posición $0$ es $v$ y su posición $j \ge 1$ es la posición $j-1$ de `(cdr s)`,
es decir $s(j)$. Caso inductivo $i > 0$: $s'$ es
`(cons (car s) s'')` con $s'' = $ `(reemplazar (cdr s) (- i 1))`. Como
$i - 1 < \lvert\texttt{(cdr s)}\rvert$, la hipótesis de inducción da que $s''$
conserva la longitud de `(cdr s)`, vale $v$ en la posición $i-1$ y coincide con
`(cdr s)` en las demás. Desplazando una posición por el `cons`, $s'$ conserva
la longitud, vale $v$ en $i$, y vale $s(j)$ en $j \ne i$ (en $j = 0$ vale
`(car s)`). $\square$

**Estado inicial.** `initialize-store!` deja $\sigma = [\ ]$ y $D = \emptyset$,
que cumple $\text{Inv}$ porque el conjunto de posiciones $0 \le i < 0$ es vacío.

**(1) `newref!` preserva el invariante.** Sea $n = \lvert\sigma\rvert$. El
código toma `pos` $= n$, hace
$\sigma' = \texttt{(append the-store (list val))}$ y retorna $\ell = \texttt{a-ref}(n)$.
Por el Lema A: $\lvert\sigma'\rvert = n + 1$, las celdas $0, \ldots, n-1$ no
cambian y $\sigma'(n) = v$. La referencia entregada apunta a una celda
existente porque $n < n + 1 = \lvert\sigma'\rvert$. Con
$D' = D \cup \{\ell\}$ se tiene
$D' = \{\texttt{a-ref}(i) \mid 0 \le i \le n\} = \{\texttt{a-ref}(i) \mid 0 \le i < \lvert\sigma'\rvert\}$,
de modo que $\text{Inv}(\sigma', D')$. La condición (2) se cumple porque la
longitud crece en exactamente uno. Esta es la única operación que cambia la
longitud del almacén.

**(2) `setref!` preserva el invariante.** Sea $\ell = \texttt{a-ref}(i)$.

- Si $i$ está fuera de rango, `posicion-valida?` es falsa y el código levanta
  `eopl:error` *antes* de ejecutar `set!`: el almacén no cambia.
- Si $i$ está en rango, $\sigma' = \texttt{(reemplazar the-store pos)}$ y el
  Lema B da: $\sigma'(\ell) = v$ y $\sigma'(\ell') = \sigma(\ell')$ para todo
  $\ell' \neq \ell$, que es exactamente la condición (3). Además
  $\lvert\sigma'\rvert = \lvert\sigma\rvert$ (condición 2) y $D$ no cambia, así
  que $\text{Inv}(\sigma', D)$.

Modifica exactamente una celda y deja las demás con el mismo valor.

**(3) `deref` no modifica el almacén.** El cuerpo de `deref` solo evalúa
`posicion-valida?` y `list-ref`; no contiene `set!` ni llama a ninguna
operación que lo contenga. Por lo tanto $\sigma' = \sigma$ y $D' = D$, y el
invariante se conserva trivialmente. Si $0 \le i < \lvert\sigma\rvert$ retorna
$\sigma(\ell)$; si no, `posicion-valida?` es falsa y levanta `eopl:error`,
que es la condición (4).

**Conclusión.** Como el estado inicial cumple $\text{Inv}$ y las tres
operaciones lo preservan, y como ninguna otra parte del programa contiene
`set!` sobre el almacén, $\text{Inv}(\sigma, D)$ se cumple en todo estado
alcanzable. $\blacksquare$

---

### 2.2 Corrección de `swap` (5.2)

**Código** (cláusula `swap-exp` de `evaluar-expresion`, una vez evaluadas
las dos subexpresiones a $\ell_1$ y $\ell_2$ y verificado que son referencias):

```racket
(let ((val1 (deref ref1)))
  (let ((val2 (deref ref2)))
    (begin
      (setref! ref1 val2)
      (setref! ref2 val1)
      val2)))
```

**Especificación.** Sea $\sigma$ el almacén en el momento en que las dos
subexpresiones ya se evaluaron y $\sigma'$ el almacén tras `swap`$(\ell_1, \ell_2)$,
con $\ell_1, \ell_2 \in \text{dom}(\sigma)$. Entonces:

$$
\sigma'(\ell_1) = \sigma(\ell_2), \qquad
\sigma'(\ell_2) = \sigma(\ell_1), \qquad
\sigma'(\ell) = \sigma(\ell) \ \ \text{para todo } \ell \notin \{\ell_1, \ell_2\}
$$

y el valor retornado es $\sigma(\ell_2)$.

**Demostración.** Se llama $w_1 = \sigma(\ell_1)$ y $w_2 = \sigma(\ell_2)$.

1. `val1` $= w_1$ y `val2` $= w_2$, porque `deref` no modifica el almacén
   (sección 2.1) y por lo tanto las dos lecturas se hacen sobre el mismo
   $\sigma$.
2. $\sigma_1 = \texttt{setref!}(\sigma, \ell_1, w_2)$. Por la condición (3):
   $\sigma_1(\ell_1) = w_2$ y $\sigma_1(\ell') = \sigma(\ell')$ para
   $\ell' \ne \ell_1$.
3. $\sigma' = \texttt{setref!}(\sigma_1, \ell_2, w_1)$. Por la condición (3):
   $\sigma'(\ell_2) = w_1$ y $\sigma'(\ell') = \sigma_1(\ell')$ para
   $\ell' \ne \ell_2$.

*Caso $\ell_1 \neq \ell_2$.*

- $\sigma'(\ell_2) = w_1 = \sigma(\ell_1)$.
- Como $\ell_1 \ne \ell_2$, el paso 3 da $\sigma'(\ell_1) = \sigma_1(\ell_1) = w_2 = \sigma(\ell_2)$.
- Para $\ell \notin \{\ell_1, \ell_2\}$: $\sigma'(\ell) = \sigma_1(\ell) = \sigma(\ell)$.

Se cumplen las tres igualdades de la especificación.

*El valor original de la primera celda no se pierde.* Cuando el paso 2
sobrescribe $\ell_1$, el valor $w_1$ ya está guardado en `val1` (paso 1), y el
paso 3 lo escribe en $\ell_2$. La implementación depende de este orden: la
variante `(setref! ref1 (deref ref2))` seguida de
`(setref! ref2 (deref ref1))` leería la segunda vez la celda $\ell_1$ ya
sobrescrita, con $\sigma_1(\ell_1) = w_2$, y dejaría $\sigma'(\ell_2) = w_2$:
$w_1$ se perdería y las dos celdas quedarían con el mismo valor.

*Caso $\ell_1 = \ell_2 = \ell$ (una referencia consigo misma).* La
especificación exige $\sigma'(\ell) = \sigma(\ell)$ (las dos primeras
igualdades piden lo mismo, y la tercera no afecta a ninguna celda): `swap` debe
ser la identidad sobre el almacén. En la implementación
$w_1 = w_2 = \sigma(\ell) =: w$. El paso 2 escribe $w$ en $\ell$ y el paso 3
vuelve a escribir $w$ en $\ell$, así que $\sigma'(\ell) = w = \sigma(\ell)$, y
las demás celdas no cambian por la condición (3). Se cumple la
especificación. No hay conflicto entre las dos escrituras, porque escriben el
mismo valor.

*Valor retornado.* La cláusula retorna `val2` $= w_2 = \sigma(\ell_2)$, que es
el contenido anterior de la segunda celda. Cuando $\ell_1 \ne \ell_2$ es
además $\sigma'(\ell_1)$, el valor que quedó en la primera referencia. Cuando
$\ell_1 = \ell_2$ es $w = \sigma(\ell)$, que coincide con lo que quedó en la
primera referencia. En el ejemplo $\text{swap}(a, b)$ con $\sigma = [0 \mapsto 7, 1 \mapsto 2]$
retorna $2$.

*Errores.* Si alguna subexpresión no se evalúa a una referencia, el código
levanta `eopl:error` antes de leer o escribir. Si alguna referencia está fuera
de rango, el error lo levanta `deref` (condición 4) en el paso 1, antes de la
primera escritura. En ambos casos el almacén queda intacto.

Además, `swap` solo usa `deref` y `setref!` y no cambia la longitud, así que
por 2.1 preserva $\text{Inv}$. $\blacksquare$

---

### 2.3 Solidez del chequeador (5.3)

**Fragmento considerado.** Cauca sin referencias (sin `newref`, `deref`,
`setref`, `swap`, `begin` ni `applyref`), con las reglas $\Gamma \vdash e : t$
de la Parte 3.

**Valores de un tipo.** La relación $v \models t$ ("el valor $v$ es de tipo $t$")
se define por recursión sobre el tipo:

- $v \models \text{num}$ si `(number? v)`.
- $v \models \text{bool}$ si `(boolean? v)`.
- $v \models (t_1 * \cdots * t_n \to t)$ si $v = \texttt{clausura}(xs, b, \rho')$,
  $\lvert xs\rvert = n$ y para todo $w_1, \ldots, w_n$ con $w_i \models t_i$ se
  cumple que $\text{value-of}(b, \rho'[xs \mapsto w])$ es un valor y es de
  tipo $t$.

**Concordancia entre $\rho$ y $\Gamma$.** El ambiente de valores $\rho$
concuerda con el ambiente de tipos $\Gamma$, y se escribe $\rho \models \Gamma$,
si para todo identificador $x$ declarado en $\Gamma$ se cumple que $x$ está
ligado en $\rho$ y $\text{apply-env}(\rho, x) \models \Gamma(x)$. El ambiente
inicial concuerda con el de tipos inicial: $n, m, p, q, r$ valen números y se
declaran $\text{num}$.

Un hecho auxiliar, **Lema C**: si $\rho \models \Gamma$ y $w_i \models t_i$,
entonces $\rho[xs \mapsto w] \models \Gamma[xs \mapsto t]$. Se sigue de que la
extensión da prioridad a las ligaduras nuevas (shadowing) en ambos ambientes
y de que las ligaduras viejas no cambian.

**Propiedad de solidez.** Si $\Gamma \vdash e : t$ y $\rho \models \Gamma$,
entonces $\text{value-of}(e, \rho)$ es un valor de tipo $t$, es decir
$\text{value-of}(e, \rho) \models t$. La afirmación incluye que la evaluación
no falla por un conflicto de tipos. Quedan fuera, por no ser errores de tipo,
la división por cero y el uso de `mcd` o `mcm` con números no enteros, y si el
fragmento incluye `letrec` la evaluación puede no terminar; en ese caso la
propiedad se lee "si termina".

**Demostración** por inducción sobre la derivación de $\Gamma \vdash e : t$.
Se demuestran los casos de `if` y `apply`. Los casos de literales,
identificador, primitivas, `let` y `proc` siguen el mismo esquema (el de `proc`
usa el Lema C y la definición de $\models$ para tipos función).

**Caso `if`.** La regla es

$$
\frac{\Gamma \vdash e_1 : \text{bool} \quad \Gamma \vdash e_2 : t \quad \Gamma \vdash e_3 : t}
     {\Gamma \vdash \texttt{if } e_1 \texttt{ then } e_2 \texttt{ else } e_3 \texttt{ end} : t}
$$

Sea $\rho \models \Gamma$. Por hipótesis de inducción sobre la premisa de
$e_1$, $v_1 = \text{value-of}(e_1, \rho) \models \text{bool}$, o sea
$v_1 \in \{\texttt{\#t}, \texttt{\#f}\}$. Entonces el chequeo `boolean?` del
intérprete se cumple y no se levanta el error de condición no booleana.

- Si $v_1 = \texttt{\#t}$, el resultado es $\text{value-of}(e_2, \rho)$, que por
  hipótesis de inducción sobre $e_2$ es de tipo $t$.
- Si $v_1 = \texttt{\#f}$, el resultado es $\text{value-of}(e_3, \rho)$, que por
  hipótesis de inducción sobre $e_3$ es de tipo $t$.

En ambos casos el resultado es de tipo $t$. Esto es lo que justifica exigir el
*mismo* tipo $t$ en las dos ramas: el chequeador no sabe cuál se ejecutará, y
la demostración tampoco necesita saberlo. $\square$

**Caso `apply`.** La regla es

$$
\frac{\Gamma \vdash f : (t_1 * \cdots * t_n \to t) \quad \Gamma \vdash e_i : t_i \ \ (1 \le i \le n)}
     {\Gamma \vdash \texttt{apply } f(e_1, \ldots, e_n) : t}
$$

Sea $\rho \models \Gamma$. Por hipótesis de inducción sobre $f$,
$p = \text{value-of}(f, \rho) \models (t_1 * \cdots * t_n \to t)$. Por la
definición de $\models$ en tipos función, $p = \texttt{clausura}(xs, b, \rho')$
con $\lvert xs\rvert = n$. Por lo tanto `procval?` se cumple (no hay error de
"aplicar un valor que no es un procedimiento") y la cantidad de argumentos
$n$ coincide con la de parámetros (no hay error de aridad). Por hipótesis de
inducción sobre cada $e_i$, $w_i = \text{value-of}(e_i, \rho) \models t_i$.
El intérprete evalúa el cuerpo en $\rho'[xs \mapsto w]$, y la definición de
$p \models (t_1 * \cdots * t_n \to t)$ aplicada a $w_1, \ldots, w_n$ dice
justamente que $\text{value-of}(b, \rho'[xs \mapsto w]) \models t$. $\square$

**Qué se rompe al agregar referencias.** Con el almacén, el enunciado ya no
puede hablar solo de $\rho$ y $\Gamma$, por tres razones:

1. **Ser de tipo $\text{refto}(t)$ depende del almacén.** Una referencia
   $\ell$ es de tipo $\text{refto}(t)$ si $\ell$ nombra una celda existente
   *y* esa celda contiene un valor de tipo $t$; es decir, $\ell \models_\sigma \text{refto}(t)$
   exige $\ell \in \text{dom}(\sigma)$ y $\sigma(\ell) \models_\sigma t$. La
   relación $v \models t$ pasa a ser $v \models_\sigma t$.
2. **Evaluar cambia el almacén.** La evaluación toma un par
   $(\rho, \sigma)$ y produce un par $(v, \sigma')$. La propiedad debe
   asegurar que $\sigma'$ sigue siendo coherente con los tipos: hace falta una
   *tipificación del almacén* $\Sigma$ que asigna un tipo a cada celda, con
   $\sigma \models \Sigma$ si cada celda guarda un valor del tipo que $\Sigma$
   le asigna. El enunciado se vuelve: si $\Gamma \vdash e : t$,
   $\rho \models_\sigma \Gamma$ y $\sigma \models \Sigma$, entonces
   $\text{value-of}(e, \rho, \sigma) = (v, \sigma')$ y existe $\Sigma' \supseteq \Sigma$
   con $\sigma' \models \Sigma'$ y $v \models_{\sigma'} t$.
3. **Los alias exigen que cada celda tenga un único tipo para siempre.** Si
   dos nombres comparten la celda $\ell$ (`let otro = celda`), una escritura
   por uno se ve por el otro. Por eso la regla de `setref` exige
   $\Gamma \vdash e_2 : t$ cuando $e_1 : \text{refto}(t)$ y la de `swap` exige
   el mismo $t$ en las dos referencias: así una celda no cambia de tipo a
   mitad de ejecución y las demás variables que la alias-an siguen siendo
   de tipo $\text{refto}(t)$. `newref` extiende $\Sigma$ con la celda nueva, y
   que $\Sigma' \supseteq \Sigma$ funciona porque el almacén solo crece
   (condición 2 del invariante de 2.1): una referencia válida nunca deja de
   serlo.

Con este enunciado, la demostración sigue siendo por inducción sobre la
derivación, pero cada caso debe llevar el almacén de entrada y de salida, y
el orden de evaluación de las subexpresiones pasa a importar
(`begin` y `setref` evalúan de izquierda a derecha).

---

## 3. Propiedades adicionales

### 3.1 Paso por referencia frente a paso por valor

**Enunciado.** Sea $\rho(x_i) = \ell_i$, con $\ell_i$ referencias, y sea
$p = \texttt{clausura}((u_1, \ldots, u_n), b, \rho')$ un procedimiento.

- Con `applyref p (x1, ..., xn)` el cuerpo se evalúa en $\rho'[u_i \mapsto \ell_i]$
  sobre el mismo almacén $\sigma$: cada parámetro queda ligado a *la misma*
  referencia. Una escritura $\texttt{setref}(u_i, v)$ produce $\sigma'$ con
  $\sigma'(\ell_i) = v$, y tras volver, $\texttt{deref}(x_i)$ retorna $v$: la
  escritura es observable fuera del procedimiento.
- Con `apply p (x1, ..., xn)` los argumentos se copian por valor. Para una
  referencia la copia reserva una celda nueva con el mismo contenido:
  $\ell_i' = \texttt{newref!}(\sigma(\ell_i))$, con $\ell_i' \ne \ell_i$ por la
  condición (1) de 2.1 (la posición nueva es $\lvert\sigma\rvert$, que no
  existía). El cuerpo se evalúa en $\rho'[u_i \mapsto \ell_i']$. Una escritura
  $\texttt{setref}(u_i, v)$ produce $\sigma'$ con $\sigma'(\ell_i') = v$ y,
  por la condición (3), $\sigma'(\ell_i) = \sigma(\ell_i)$: no se observa
  fuera.

**Contraste sobre el mismo programa.** Con $\sigma = [0 \mapsto 11, 1 \mapsto 4]$
y $\text{swap}(u, v)$ como cuerpo:

| Mecanismo | $\sigma$ al terminar | Resultado de `-(deref(x), deref(y))` |
|-----------|----------------------|---------------------------------------|
| `applyref` | $[0 \mapsto 4,\ 1 \mapsto 11]$ | $4 - 11 = -7$ |
| `apply`    | $[0 \mapsto 11,\ 1 \mapsto 4,\ 2 \mapsto 4,\ 3 \mapsto 11]$ | $11 - 4 = 7$ |

Estos valores ($-7$ y $7$) se comprobaron ejecutando ambos programas con el
intérprete del repositorio. La diferencia entre los dos resultados es la
propiedad: solo con `applyref` el procedimiento escribe en las celdas del que
llama. $\blacksquare$

---

## 4. Referencias

- Friedman, D. P., & Wand, M. *Essentials of Programming Languages*,
  3.ª ed., MIT Press, 2008. Sección 4.2 (EXPLICIT-REFS, Figura 4.3),
  sección 4.3 (paso por referencia) y secciones 7.1 a 7.3 (chequeo de tipos,
  Figura 7.1).
- Pierce, B. C. *Types and Programming Languages*, MIT Press, 2002.
  Capítulos 8 y 13 (reglas de tipado y referencias).

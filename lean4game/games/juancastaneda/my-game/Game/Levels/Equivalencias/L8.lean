import Game.Levels.Equivalencias.L7

World "Equivalencias"
Level 8
Title "Ejercicio 8"


Introduction
"
Este mundo funciona como los otros; tienes que escribir en la barra de abajo en la mitad los teoremas que quieres ejecutar sobre el ejercicio (y luego dar enter para ejecutarlos).

En la parte derecha encuentras los teoremas que puedes usar, discriminados según para qué tipo de operador lógico son. ES IMPORTANTE la dirección del teorema. Por ejemplo, si se escribe 'definicion_implicacion', el programa a buscar la primera ocurrencia de 'p → q' y la va a cambiar por '¬p ∨ q'. Si a cambio lo que se quiere es cambiar la ocurrencia de '¬p ∨ q' por 'p → q', se debe escribir '← definicion_implicacion'. El símbolo '←' se saca escribiendo '\\l'.

Para ejecutar algún teorema sobre una ocurrencia distinta a la primera se escribiría 'teorema; numero_de_ocurrencia'. Por ejemplo, para ejecutar la definición de la implicación en la segunda ocurrencia, se escribiría 'definicion_implicacion; 2'. Si tienes una expresión como '(p → q) → (p → r)' y le quisieras aplicar la definición de la implicación al '(p → r)', escribirías 'definicion_implicacion; 3', pues el primer '→' es el de la expresión general que conecta '(p → q)' con '(p → r)', el segundo sería el de '(p → q)' y finalmente el tercero sería el de '(p → r)'.

Si llegas a ver una expresión como '¬p ∨ q ∧ r', no te asustes por el hecho de no tener paréntesis. Es un trabajo en progreso, pero por ahora deberías saber que tiene más precedencia el ∧ que el ∨. Entonces ese que acabamos de ver se interpretaría como '¬p ∨ (q ∧ r)'.

Por último, otros comandos que pueden llegar a ser útiles son: '¬' = '\\neg'; '∨' = '\\or'; '∧' = '\\and'; '→' = '\\r' ; '↔' = '\\lr'.
"

Conclusion "
"

Statement (p q : Prop): p ∧ (p → q) → q ↔ True := by
  rw [definicion_implicacion]
  rw [de_morgan_y]
  rw [definicion_implicacion]
  rw [de_morgan_o]
  rw [doble_negacion]
  rw [distributividad_o_sobre_y]
  rw (config := {occs := .pos [2]}) [conmutatividad_o]
  rw [negacion_o]
  rw [conmutatividad_y]
  rw [identidad_y]
  rw [asociatividad_o]
  rw (config := {occs := .pos [2]}) [conmutatividad_o]
  rw [negacion_o]
  rw [dominacion_o]

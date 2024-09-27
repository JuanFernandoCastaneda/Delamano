import Game.Levels.Equivalencias.L4

World "Equivalencias"
Level 5
Title "Ejercicio 5"


Introduction
"
Este mundo funciona como los otros; tienes que escribir en la barra de abajo en la mitad los teoremas que quieres ejecutar sobre el ejercicio (y luego dar enter para ejecutarlos).

En la parte derecha encuentras los teoremas que puedes usar, discriminados según para qué tipo de operador lógico son. ES IMPORTANTE la dirección del teorema. Por ejemplo, si se escribe 'definicion_implicacion', el programa a buscar la primera ocurrencia de 'p → q' y la va a cambiar por '¬p ∨ q'. Si a cambio lo que se quiere es cambiar la ocurrencia de '¬p ∨ q' por 'p → q', se debe escribir '← definicion_implicacion'. El símbolo '←' se saca escribiendo '\\l'.

Para ejecutar algún teorema sobre una ocurrencia distinta a la primera se escribiría 'teorema; numero_de_ocurrencia'. Por ejemplo, para ejecutar la definición de la implicación en la segunda ocurrencia, se escribiría 'definicion_implicacion; 2'.

Si llegas a ver una expresión como '¬p ∨ q ∧ r', no te asustes por el hecho de no tener paréntesis. Es un trabajo en progreso, pero por ahora deberías saber que es estándar en matemáticas que los operadores lógicos sean asociativos hacia la izquierda. Entonces ese que acabamos de ver se interpretaría como '¬p ∨ (q ∧ r)'.

Por último, otros comandos que pueden llegar a ser útiles son:

'¬' = '\\neg'

'∨' = '\\or'

'∧' = '\\and'

'→' = '\\r'

'↔' = '\\lr'.
"

Conclusion "
"

Statement (p q : Prop): (p ∧ q) → r ↔ (p → r) ∨ (q → r) := by
  sorry

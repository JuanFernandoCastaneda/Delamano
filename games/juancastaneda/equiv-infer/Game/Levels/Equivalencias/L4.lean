import Game.Levels.Equivalencias.L3

World "Equivalencias"
Level 4
Title "Ejercicio 4"


Introduction
"
Recordatorios generales:

Para utilizar la otra dirección del teorema es con el símbolo '←' que se saca escribiendo '\\l'. Por ejemplo, '← definicion_implicacion'.

Para ejecutar algún teorema sobre una ocurrencia distinta a la primera se escribiría '{teorema} pos {numero_de_ocurrencia}'. Por ejemplo, para ejecutar la definición de la implicación en la segunda ocurrencia, se escribiría 'definicion_implicacion pos 2'.

Si llegas a ver una expresión como '¬p ∨ q ∧ r' se interpretaría como '¬p ∨ (q ∧ r)'.

'¬' = '\\neg'; '∨' = '\\or'; '∧' = '\\and'; '→' = '\\r' ; '↔' = '\\lr'.
"

Conclusion "
"

Statement (p q : Prop): p ∧ ((p → (q ∧ ¬q)) ∨ ¬p) ↔ False := by
  rw [negacion_y]
  rw [definicion_implicacion]
  rw [identidad_o]
  rw [idempotencia_o]
  rw [negacion_y]

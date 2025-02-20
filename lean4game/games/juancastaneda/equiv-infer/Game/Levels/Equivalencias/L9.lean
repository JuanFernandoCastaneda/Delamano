import Game.Levels.Equivalencias.L8

World "Equivalencias"
Level 9
Title "Ejercicio 9"


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

Statement (p q : Prop): (p ∧ p ∧ p ∧ r ∧ q ∧ q) ∨ r ↔ r := by
  rw [conmutatividad_o]
  rw [idempotencia_y]
  rw [← asociatividad_y]
  rw [idempotencia_y]
  rw [← asociatividad_y]
  rw [idempotencia_y]
  rw [conmutatividad_y]
  rw [asociatividad_y]
  rw [absorcion_o_sobre_y]

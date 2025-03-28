import Game.Levels.Equivalencias.L5

World "Equivalencias"
Level 6
Title "Ejercicio 6"


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

Statement (p q : Prop): (p ∧ q) → r ↔ (p → r) ∨ (q → r) := by
  rw [definicion_implicacion]
  rw [de_morgan_y]
  rw (config := {occs := .pos [1]}) [← idempotencia_o r]
  rw [asociatividad_o]
  rw (config := {occs := .pos [2]}) [← asociatividad_o]
  rw (config := {occs := .pos [2]}) [conmutatividad_o]
  rw [← asociatividad_o]
  rw [← definicion_implicacion]
  rw [← definicion_implicacion]

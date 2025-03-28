import Game.Levels.Equivalencias.L7

World "Equivalencias"
Level 8
Title "Ejercicio 8"


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

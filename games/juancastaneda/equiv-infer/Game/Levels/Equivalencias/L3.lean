import Game.Levels.Equivalencias.L2

World "Equivalencias"
Level 3
Title "Ejercicio 3"

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

Statement (p q : Prop): (p → q) → p ↔ p := by
  rw [definicion_implicacion]
  rw [definicion_implicacion]
  rw [de_morgan_o]
  rw [doble_negacion]
  rw [conmutatividad_o]
  rw [absorcion_o_sobre_y]

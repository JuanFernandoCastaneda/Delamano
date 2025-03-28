import Game.Levels.Equivalencias.L1

World "Equivalencias"
Level 2
Title "Ejercicio 2"

Introduction
"
Recordatorios generales:

Para utilizar la otra dirección del teorema es con el símbolo '←' que se saca escribiendo '\\l'. Por ejemplo, '← definicion_implicacion'.

Para ejecutar algún teorema sobre una ocurrencia distinta a la primera se escribiría '{teorema} pos {numero_de_ocurrencia}'. Por ejemplo, para ejecutar la definición de la implicación en la segunda ocurrencia, se escribiría 'definicion_implicacion pos 2'.

Si llegas a ver una expresión como '¬p ∨ q ∧ r' se interpretaría como '¬p ∨ (q ∧ r)'.

'¬' = '\\neg'; '∨' = '\\or'; '∧' = '\\and'; '→' = '\\r' ; '↔' = '\\lr'.
"

Conclusion ""

Statement (p q : Prop): p → (q → p) ↔ True := by
  rw [definicion_implicacion]
  rw [definicion_implicacion]
  rw [conmutatividad_o]
  rw [asociatividad_o]
  rw [negacion_o]
  rw [dominacion_o]

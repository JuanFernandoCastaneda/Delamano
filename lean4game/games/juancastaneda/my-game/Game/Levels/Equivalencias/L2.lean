import Game.Levels.Equivalencias.L1

World "Equivalencias"
Level 2
Title "Ejercicio 2"

Introduction
"
Este mundo funciona como los otros; tienes que escribir en la barra de abajo en la mitad los teoremas que quieres ejecutar sobre el ejercicio (y luego dar enter para ejecutarlos).

En la parte derecha encuentras los teoremas que puedes usar, discriminados según para qué tipo de operador lógico son. ES IMPORTANTE la dirección del teorema. Por ejemplo, si se escribe 'definicion_implicacion', el programa a buscar la primera ocurrencia de 'p → q' y la va a cambiar por '¬p ∨ q'. Si a cambio lo que se quiere es cambiar la ocurrencia de '¬p ∨ q' por 'p → q', se debe escribir '← definicion_implicacion'. El símbolo '←' se saca escribiendo '\\l'.

Para ejecutar algún teorema sobre una ocurrencia distinta a la primera se escribiría 'teorema; numero_de_ocurrencia'. Por ejemplo, para ejecutar la definición de la implicación en la segunda ocurrencia, se escribiría 'definicion_implicacion; 2'.

Por último, otros comandos que pueden llegar a ser útiles son:

'¬' = '\\neg'

'∨' = '\\or'

'∧' = '\\and'

'→' = '\\r'

'↔' = '\\lr'.
"

Conclusion ""

Statement (p q : Prop): p → (q → p) ↔ True := by
  rw [definicion_implicacion]
  rw [definicion_implicacion]
  rw [conmutatividad_o]
  rw [asociatividad_o]
  rw [negacion_o]
  rw [dominacion_o]

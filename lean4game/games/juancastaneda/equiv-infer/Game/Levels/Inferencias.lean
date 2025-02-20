import Game.Levels.Inferencias.L2

World "Inferencias"
Title "Inferencias"

Introduction
"
Este mundo funciona como los otros; tienes que escribir en la barra de abajo en la mitad los teoremas que quieres ejecutar sobre el ejercicio (y luego dar enter para ejecutarlos).

Lo nuevo respecto al mundo anterior es que ahora existen reglas de inferencia además de reglas de equivalencia. Las reglas de inferencia se utilizan escribiendo 'sea {expresión} por {regla de inferencia} {hipotesis necesarias separadas por comas}'. Por ejemplo, si mi h1 es 'p' y mi h2 es 'p → q', puedo utilizar 'sea q por modus_ponens h2, h1'.

Además, ahora las reglas de equivalencia deben referenciar una hipótesis en específico para ser utilizadas, con la siguiente forma '{regla de equivalencia} en {hipótesis a modificar}'. Por ejemplo, si mi h2 es 'p → q', puedo utilizar 'definicion_implicacion en h2' para modificarla a '¬p ∨ q'. También aplica la nota de la dirección, con '←'.

'←' = '\\l'; '¬' = '\\neg'; '∨' = '\\or'; '∧' = '\\and'; '→' = '\\r' ; '↔' = '\\lr'.
"

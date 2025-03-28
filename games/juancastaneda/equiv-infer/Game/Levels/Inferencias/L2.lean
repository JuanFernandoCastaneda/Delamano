import Game.Levels.Inferencias.L1

World "Inferencias"
Level 2
Title "Ejercicio 2"

Introduction
"
Recordatorios:

Las reglas de inferencia se utilizan escribiendo 'sea {expresión} por {regla de inferencia} {hipotesis necesarias separadas por comas}'. Por ejemplo, si mi h1 es 'p' y mi h2 es 'p → q', puedo utilizar 'sea q por modus_ponens h2, h1'.

Ahora las reglas de equivalencia deben referenciar una hipótesis en específico para ser utilizadas, con la siguiente forma '{regla de equivalencia} en {hipótesis a modificar}'. La dirección sigue importando.

'←' = '\\l'; '¬' = '\\neg'; '∨' = '\\or'; '∧' = '\\and'; '→' = '\\r' ; '↔' = '\\lr'.
"

Conclusion ""

Statement (p q r: Prop) (h1: p) (h2: ¬q → ¬p) (h3: ¬r → ¬q): r := by
{
  have s1 := by modus_tollens h2, h1
  modus_tollens h3, s1
}

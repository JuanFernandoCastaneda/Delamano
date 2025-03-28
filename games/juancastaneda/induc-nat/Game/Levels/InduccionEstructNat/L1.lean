import Game.Metadata
import Mathlib.Tactic
import Mathlib.Util.Delaborators

World "InduccionEstructNat"
Level 1
Title "Ejercicio 1"

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

open Nat

theorem suma_cero_derecha (n: Nat): n + zero = n := by
  exact rfl
TheoremDoc suma_cero_derecha as "suma_cero_derecha" in "+"


theorem suma_sucesor_derecha(n m: Nat): n + succ m = succ (n + m) := by
  exact rfl
TheoremDoc suma_sucesor_derecha as "suma_sucesor_derecha" in "+"

NewTheorem suma_cero_derecha suma_sucesor_derecha

NewTactic rw config induction

Statement (n : Nat): zero + n = n := by
  induction n
  {
    rw [suma_cero_derecha]
  }
  {
    rw [suma_sucesor_derecha]
    rw [n_ih]
  }

/--
El ∧ o "and" es el símbolo que representa la conjunción entre dos proposiciones.

Su tabla de verdad dice que si se tiene el and entre dos proposiciones, siempre es falso a menos que ambas proposiciones sean verdaderas.
-/
DefinitionDoc And as "∧"

NewDefinition And

import Game.Metadata
import Mathlib.Tactic
import Mathlib.Util.Delaborators

World "Equivalencias"
Level 1
Title "Playground"

Introduction "A la derecha están las propiedades que puedes usar. Para ver qué hace cada una puedes poner el cursor sobre el nombre y te dirá :]"

Conclusion "
The message shown when the level is completed
"

theorem definicion_implicacion (p q : Prop): p → q ↔ ¬p ∨ q := by
  exact imp_iff_not_or

theorem de_morgan_y (p q : Prop) : ¬(p ∧ q) ↔ ¬p ∨ ¬q := by
  rw [not_and]
  rw [definicion_implicacion]

theorem double_negation (p : Prop) : ¬(¬p) ↔ p := by
  exact not_not

theorem de_morgan_o (p q : Prop) : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  rw [not_or]

NewTheorem definicion_implicacion de_morgan_y de_morgan_o double_negation

NewTactic rw config

Statement : ¬(p → q) ↔ p ∧ ¬q  := by
  sorry


/--
El ∧ o "and" es el símbolo que representa la conjunción entre dos proposiciones.

Su tabla de verdad dice que si se tiene el and entre dos proposiciones, siempre es falso a menos que ambas proposiciones sean verdaderas.
-/
DefinitionDoc And as "∧"

NewDefinition And

import Game.Metadata
import Mathlib.Tactic
import Mathlib.Util.Delaborators

World "TeoriaNums"
Level 1
Title "Ejercicio 1"

Introduction "A la derecha están las propiedades que puedes usar. Para ver qué hace cada una puedes poner el cursor sobre el nombre y te dirá :]"

Conclusion "
The message shown when the level is completed
"

Statement (p q r : ℤ): p∣q ∧ q∣r → p∣r := by
  intro p1
  have p2 := And.left p1
  have p3 := And.right p1
  rcases p2
  rcases p3
  have p4

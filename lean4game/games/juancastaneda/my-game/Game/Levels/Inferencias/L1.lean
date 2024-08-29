import Game.Metadata
import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Game.Levels.Equivalencias.L1


World "Inferencias"
Level 1
Title "Ejercicio 1"

Introduction "A la derecha están las propiedades que puedes usar. Para ver qué hace cada una puedes poner el cursor sobre el nombre y te dirá :]"

Conclusion "
The message shown when the level is completed
"

Statement (h1: p) (h2: p → q) (h3: q → r): r := by
  apply h3 (h2 h1)

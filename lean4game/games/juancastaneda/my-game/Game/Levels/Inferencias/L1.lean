import Game.Metadata
import Mathlib.Tactic
import Mathlib.Util.Delaborators

World "Inferencias"
Level 1
Title "Ejercicio 1"

Introduction "A la derecha están las propiedades que puedes usar. Para ver qué hace cada una puedes poner el cursor sobre el nombre y te dirá :]"

Conclusion "
The message shown when the level is completed
"

Statement (p q r: Prop) (h1: p) (h2: p → q) (h3: ¬q ∨ r): r := by
{
  have p1 := h2 h1
  revert h3
  rw [← imp_iff_not_or]
  intro h3
  have p2 := h3 p1
  exact h3 p1
}

theorem silogismo_disyuntivo (p q: Prop) (h1: p) (h2: ¬ p ∨ q) : q := by
  revert h2
  rw [← imp_iff_not_or]
  intro h2
  exact h2 h1

example (p q r: Prop) (h1: p) (h2: p → q) (h3: ¬q ∨ r): r := by
  have p1 := h2 h1
  have p2: r :=

example (p q: Prop) (h1: p ∨ q) (h2: ¬p): q := by
  apply?

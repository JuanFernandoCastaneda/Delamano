import Mathlib.Logic.Basic
import Game.Levels.Inferencias.L1

World "Inferencias"
Level 2
Title "Ejercicio 2"

Introduction "A la derecha están las propiedades que puedes usar. Para ver qué hace cada una puedes poner el cursor sobre el nombre y te dirá :]"

Conclusion "
The message shown when the level is completed
"

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    apply Or.elim (And.right h)
    . intro hq
      apply Or.inl
      apply And.intro
      . exact And.left h
      . exact hq
    . intro hr
      apply Or.inr
      apply And.intro
      . exact And.left h
      . exact hr
  . intro h
    apply Or.elim h
    . intro hpq
      apply And.intro
      . exact And.left hpq
      . apply Or.inl
        exact And.right hpq
    . intro hpr
      apply And.intro
      . exact And.left hpr
      . apply Or.inr
        exact And.right hpr


theorem contrapositiva_2 (h1: ¬q → ¬p): p → q := by
  rw [contrapositiva]
  exact fun a => h1 a


theorem modus_tollens (h1: ¬q → ¬p) (h2: p): q := by
  revert h1
  rw (config := {occs := .pos [2]}) [contrapositiva]
  rw [doble_negacion]
  rw [doble_negacion]
  intro h1
  exact h1 h2

theorem hhuh3 (h: p → q ↔ ¬q → ¬p): ((p → q) → ¬q → ¬p) ∧ ((¬q → ¬p) → p → q) := by
  exact iff_def.mp h

example (h1: ¬q → ¬p): p → q := by
  revert h1
  rw (config := {occs := .pos [3]}) [contrapositiva]
  intro h1
  exact fun a => h1 a

example (h1: ¬q → ¬p): p → q := by
  revert h1
  rw (config := {occs := .pos [3]}) [contrapositiva]
  exact fun h1 a => h1 a

example : p → p := by
  exact fun a => a

example (h1: ¬q → ¬p): p → q := by
  tauto

example (p q : Prop): p ∨ (q ∨ r) ↔ (p ∨ r) ∨ q := by
  tauto

theorem aprovechar_equivalencias (h1: p ↔ q): (p → q) ∧ (q → p) := by
  exact iff_def.mp h1

Statement (h1: p → (q ∧ r)) (h2: p) (h3: ¬t → ¬p) : q ∧ t := by
  have p4 : q ∧ r := h1 h2
  have p5: q := And.left p4
  have p0: (p → t) ∧ t → p := by rw [aprovechar_equivalencias h3]
  have p6: p → t := And.left [aprovechar_equivalencias h3]
  have p7: t := (p6 h2)
  apply And.intro p5 p7

#check aprovechar_equivalencias contrapositiva

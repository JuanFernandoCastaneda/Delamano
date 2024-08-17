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

theorem identidad_o (p : Prop) : p ∨ False ↔ p := by
  exact or_false_iff p
/--
-/
TheoremDoc identidad_o as "identidad_o" in "∨"

theorem identidad_y (p : Prop) : p ∧ True ↔ p := by
  exact and_true_iff p
/--
-/
TheoremDoc identidad_y as "identidad_y" in "∧"

theorem dominacion_o (p : Prop) : p ∨ True ↔ True := by
  exact or_true_iff p
/--
-/
TheoremDoc dominacion_o as "dominacion_o" in "∨"

theorem dominacion_y (p : Prop) : p ∧ False ↔ False := by
  exact and_false_iff p
/--
-/
TheoremDoc dominacion_y as "dominacion_y" in "∧"

theorem idempotencia_o (p : Prop) : p ∨ p ↔ p := by
  exact or_self_iff
/--
-/
TheoremDoc idempotencia_o as "idempotencia_o" in "∨"

theorem idempotencia_y (p : Prop) : p ∧ p ↔ p := by
  exact and_self_iff
/--
-/
TheoremDoc idempotencia_y as "idempotencia_y" in "∧"

theorem doble_negacion (p : Prop) : ¬(¬p) ↔ p := by
  exact not_not
/--
-/
TheoremDoc doble_negacion as "doble_negacion" in "¬"

theorem conmutatividad_o (p q : Prop) : p ∨ q ↔ q ∨ p := by
  exact or_comm
/--
-/
TheoremDoc conmutatividad_o as "conmutatividad_o" in "∨"

theorem conmutatividad_y (p q : Prop) : p ∧ q ↔ q ∧ p := by
  exact and_comm
/--
-/
TheoremDoc conmutatividad_y as "conmutatividad_y" in "∧"

theorem asociatividad_o (p q r: Prop): (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
  exact or_assoc
/--
-/
TheoremDoc asociatividad_o as "asociatividad_o" in "∨"

theorem asociatividad_y (p q r: Prop): (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
  exact and_assoc
/--
-/
TheoremDoc asociatividad_y as "asociatividad_y" in "∧"

theorem distributividad_o_sobre_y (p q r : Prop): p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  exact or_and_left
/--
-/
TheoremDoc distributividad_o_sobre_y as "distributividad_o_sobre_y" in "∧+∨"

theorem distributividad_y_sobre_o (p q r : Prop): p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  exact and_or_left
/--
-/
TheoremDoc distributividad_y_sobre_o as "distributividad_y_sobre_o" in "∧+∨"

theorem de_morgan_o (p q : Prop) : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  rw [not_or]
/--
-/
TheoremDoc de_morgan_o as "de_morgan_o" in "¬"

theorem de_morgan_y (p q : Prop) : ¬(p ∧ q) ↔ ¬p ∨ ¬q := by
  rw [not_and]
  exact imp_iff_not_or
/--
-/
TheoremDoc de_morgan_y as "de_morgan_y" in "¬"

theorem absorcion_o_sobre_y (p q : Prop): p ∨ (p ∧ q) ↔ p := by
  rw (config := {occs := .pos [1]}) [← and_true_iff p ]
  rw [← and_or_left]
  rw [or_comm]
  rw [or_true_iff]
  rw [and_true_iff]
/--
-/
TheoremDoc absorcion_o_sobre_y as "absorcion_o_sobre_y" in "∧+∨"

theorem absorcion_y_sobre_o (p q : Prop): p ∧ (p ∨ q) ↔ p := by
  exact and_iff_left_of_imp fun a => Or.inl a
/--
-/
TheoremDoc absorcion_y_sobre_o as "absorcion_y_sobre_o" in "∧+∨"

theorem negacion_o (p : Prop): p ∨ ¬p ↔ True := by
  rw [or_comm]
  rw [← imp_iff_not_or]
  exact imp_self
/--
-/
TheoremDoc negacion_o as "negacion_o" in "∨"

theorem negacion_y (p : Prop): p ∧ ¬p ↔ False := by
  exact and_not_self_iff p
/--
-/
TheoremDoc negacion_y as "negacion_y" in "∧"

theorem definicion_implicacion (p q : Prop): p → q ↔ ¬p ∨ q := by
  exact imp_iff_not_or
/--
-/
TheoremDoc definicion_implicacion as "definicion_implicacion" in "→"

theorem contrapositiva (p q : Prop): p → q ↔ ¬q → ¬p := by
  exact Iff.symm not_imp_not
/--
-/
TheoremDoc contrapositiva as "contrapositiva" in "→"

theorem definicion_equivalencia (p q : Prop): (p ↔ q) ↔ (p → q) ∧ (q → p) := by
  exact iff_def
/--
-/
TheoremDoc definicion_equivalencia as "definicion_equivalencia" in "↔"

theorem definicion_equivalencia_2 (p q : Prop): (p ↔ q) ↔ (p ∧ q) ∨ (¬p ∧ ¬q) := by
  exact iff_iff_and_or_not_and_not
/--
-/
TheoremDoc definicion_equivalencia_2 as "definicion_equivalencia_2" in "↔"

theorem negacion_equivalencia (p q : Prop): ¬(p ↔ q) ↔ (¬p ↔ q) := by
  exact not_iff
/--
-/
TheoremDoc negacion_equivalencia as "negacion_equivalencia" in "¬"

NewTheorem identidad_o identidad_y dominacion_o dominacion_y idempotencia_o idempotencia_y doble_negacion conmutatividad_o conmutatividad_y asociatividad_o asociatividad_y distributividad_o_sobre_y distributividad_y_sobre_o de_morgan_y de_morgan_o absorcion_o_sobre_y absorcion_y_sobre_o negacion_o negacion_y definicion_implicacion contrapositiva definicion_equivalencia definicion_equivalencia_2 negacion_equivalencia

NewTactic rw config

Statement : ¬(p → q) ↔ p ∧ ¬q  := by
  sorry


/--
El ∧ o "and" es el símbolo que representa la conjunción entre dos proposiciones.

Su tabla de verdad dice que si se tiene el and entre dos proposiciones, siempre es falso a menos que ambas proposiciones sean verdaderas.
-/
DefinitionDoc And as "∧"

NewDefinition And

import Game.Metadata
import Game.Levels.Equivalencias.L1

World "Inferencias"
Level 1
Title "Ejercicio 1"

Introduction
"
Recordatorios:

Las reglas de inferencia se utilizan escribiendo 'sea {expresión} por {regla de inferencia} {hipotesis necesarias separadas por comas}'. Por ejemplo, si mi h1 es 'p' y mi h2 es 'p → q', puedo utilizar 'sea q por modus_ponens h2, h1'.

Ahora las reglas de equivalencia deben referenciar una hipótesis en específico para ser utilizadas, con la siguiente forma '{regla de equivalencia} en {hipótesis a modificar}'. La dirección sigue importando.

'←' = '\\l'; '¬' = '\\neg'; '∨' = '\\or'; '∧' = '\\and'; '→' = '\\r' ; '↔' = '\\lr'.
"

Conclusion "
"

/- MODUS PONENS ES AUTOMÁTICO -/

def sd1 (h1: p ∨ q) (h2: ¬p): q := by
  have s1: ¬p → q := by {
    rw [← doble_negacion p] at h1
    rw [← definicion_implicacion] at h1
    assumption
  }
  apply s1 h2
def sd2 (h1: ¬p ∨ q) (h2: p): q := by sorry
def sd3 (h1: p ∨ ¬q) (h2: q): p := by sorry
def sd4 (h1: p ∨ q) (h2: ¬q): p := by sorry
/- Podría abstraer este proceso de tener que escribir todo de una forma como intentar $h1 $h2 que de una lista de métodos intente todos xd-/
macro "silogismo_disyuntivo" h1:term "," h2:term: tactic => do
  `(tactic | (first | apply sd1 $h1 $h2 | apply sd2 $h1 $h2 | apply sd3 $h1 $h2 | apply sd4 $h1 $h2))

def mt1 (h2: ¬q → ¬p) (h1: p): q := sorry
def mt2 (h2: ¬q → p) (h1: ¬p): q := sorry
def mt3 (h2: q → ¬p) (h1: p): ¬q := sorry
def mt4 (h2: q → p) (h1: ¬p): ¬q := sorry
macro "modus_tollens" h1:term "," h2:term : tactic => do
  `(tactic | (first | apply mt1 $h1 $h2 | apply mt2 $h1 $h2 | apply mt3 $h1 $h2 | apply mt4 $h1 $h2))

macro "simplificacion" h1:term : tactic =>  do
  `(tactic | (first | apply And.right $h1 | apply And.left $h1))

/- Toca corregir esto sí o sí, ¿a qué le estoy haciendo adición? XDDDDDDDDD -/
macro "adicion" h1:term : tactic => do
  `(tactic | (first | apply Or.inl $h1 | apply Or.inr $h1 ))

macro "conjuncion" h1:term "," h2:term :tactic => do
  `(tactic | try apply (And.intro $h1 $h2))

example (h1: ¬p → q) (h2: q → ¬r): ¬p → ¬r := by
  exact fun a => h2 (h1 a)

example (h1: ¬p → q) (h2: q → ¬r): ¬p → ¬r := by
  intro h3
  apply h2 (h1 h3)

macro "transitividad" h1:term "," h2:term :tactic => do
  `(tactic | try (intro h3; apply $h2 ($h1 h3)))

macro "modus_ponens" h1:term "," h2:term : tactic => do
  `(tactic | try (apply $h1 $h2))

example (h1: ¬p → q) (h2: q → ¬r): ¬p → ¬r := by
  transitividad h1 , h2

example (h1: p) (h2: q): p ∧ q := by
  conjuncion h1 , h2

example (h1: p) (h2: p → q): q := by
  apply h2 h1

example (h1: p) (h2: p → q): q := by
  modus_ponens h2 , h1


theorem r1 (h1: p ∨ q) (h2: ¬p ∨ r) : q ∨ r := by
{
  rcases h1
  {
    have s1 := by silogismo_disyuntivo h2, h
    adicion s1
  }
  {
    adicion h
  }
}
theorem r2 (h1: q ∨ p) (h2: r ∨ ¬p): q ∨ r := by sorry
macro "resolucion" h1:term "," h2:term : tactic => do
  `(tactic | (first | apply r1 $h1 $h2 | apply r2 $h1 $h2))

example (h1: p ∨ ¬q) (h2: ¬p ∨ r): ¬q ∨ r := by
  resolucion h1, h2

example (h1: ¬q ∨ p) (h2: r ∨ ¬p): ¬q ∨ r := by
  resolucion h1, h2

NewTactic modus_ponens modus_tollens silogismo_disyuntivo transitividad resolucion simplificacion conjuncion adicion «have»

Statement (p q r: Prop) (h1: p) (h2: p → q) (h3: ¬q ∨ r): r := by
{
  have p1 := h2 h1
  revert h3
  rw [← imp_iff_not_or]
  intro h3
  exact h3 p1
}

example (p q r: Prop) (h1: p) (h2: p → q) (h3: ¬q ∨ r): r := by
{
  have s: q := by modus_ponens h2, h1
  have s := by silogismo_disyuntivo h3 , s
  assumption
}

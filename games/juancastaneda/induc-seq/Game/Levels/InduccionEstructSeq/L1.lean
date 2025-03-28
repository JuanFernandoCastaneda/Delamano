import Game.Levels.InduccionEstructSeq.L0

World "InduccionEstructSeq"
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
open List

/-Mejor implementarlo como una lista de enteros-/

/-- Implementar tipo Seq

structure Sequence where
  seq : List Nat

Tal vez sea mejor dejar explícito que es una Lista de Nats.
  -/

def appendSeq: (l: List Nat) → (n: Nat) → List Nat
| l, n => n :: l

def concatSeq: (l1 : List Nat) → (l2: List Nat) → List Nat
| [], l2 => l2
| h::t, l2 => h :: (concatSeq t l2)

def lenSeq: List Nat → Nat
| [] => 0
| (_::t) => succ (lenSeq t)

#eval concatSeq [1, 2] [3, 4]
#eval lenSeq [1, 2, 3]

theorem concatBase (l2: List Nat): concatSeq [] l2 = l2 := by
  rfl
theorem concatRecursivo (n: Nat) (l1: List Nat) (l2: List Nat): concatSeq (n::l1) l2 = n :: (concatSeq l1 l2) := by
  rfl

theorem lenBase: lenSeq [] = 0 := by rfl
theorem lenRecursivo (n: Nat) (l: List Nat): lenSeq (n::l) = lenSeq l + 1 := by rfl

NewTheorem concatBase concatRecursivo lenBase lenRecursivo

NewTactic rw config induction ring

Statement (l1 l2 : List Nat): lenSeq (concatSeq l1 l2) = lenSeq l1 + lenSeq l2 := by
  induction l1
  {
    rw [concatBase]
    rw [lenBase]
    ring
  }
  {
    rw [lenRecursivo]
    rw [concatRecursivo]
    rw [lenRecursivo]
    rw [tail_ih]
    ring
  }

/--
El ∧ o "and" es el símbolo que representa la conjunción entre dos proposiciones.

Su tabla de verdad dice que si se tiene el and entre dos proposiciones, siempre es falso a menos que ambas proposiciones sean verdaderas.
-/
DefinitionDoc And as "∧"

NewDefinition And

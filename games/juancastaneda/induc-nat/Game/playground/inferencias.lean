import Game.Levels.Equivalencias.L1
open Lean
open Lean Parser

def sd1 (h1: p ∨ q) (h2: ¬p): q := by
  have s1: ¬p → q := by {
    revert h1
    rw (config := {occs := .pos [1]}) [← doble_negacion p]
    rw [← definicion_implicacion]
    simp
  }
  apply s1 h2
def sd2 (h1: ¬p ∨ q) (h2: p): q := by sorry
def sd3 (h1: p ∨ ¬q) (h2: q): p := by sorry
def sd4 (h1: p ∨ q) (h2: ¬q): p := by sorry

/- Podría abstraer este proceso de tener que escribir todo de una forma como intentar $h1 $h2 que de una lista de métodos intente todos xd-/
macro "sd" h1:term "," h2:term: tactic => do
  `(tactic | (first | apply sd1 $h1 $h2 | apply sd2 $h1 $h2 | apply sd3 $h1 $h2 | apply sd4 $h1 $h2))

#check Lean.MonadError

example (h1: p ∨ q) (h2: ¬p): q := by
  apply sd1 h1 h2

example (h1: p ∨ q) (h2: ¬p): q := by
  sd h1 , h2

example (h1: ¬p ∨ q) (h2: p): q := by
  sd h1 , h2
syntax "error_position" ident : term

macro_rules
  | `(error_position all) => Macro.throwError "Ahhh"
  -- the `%$tk` syntax gives us the Syntax of the thing before the %,
  -- in this case `error_position`, giving it the name `tk`
  | `(error_position%$tk first) => withRef tk (Macro.throwError "Ahhh")

#check_failure error_position all -- the error is indicated at `error_position all`
#check_failure error_position first -- the error is only indicated at `error_position`

/-
Este no sirve si algo
example (h1: ¬p ∨ q) (h2: ¬p): q := by
  sd h1 , h2
-/

example (p q r: Prop) (h1: p) (h2: p → q) (h3: ¬q ∨ r): r := by
{
  have s1 := h2 h1
  have s2: r := by {
    revert s1
    rw [← doble_negacion q]
    intro (s1:¬¬q)
    apply sd1 h3 s1
  }
  exact s2
}

example (p q r: Prop) (h1: p) (h2: p → q) (h3: ¬q ∨ r): r := by
{
  have s1 := h2 h1
  have s2: r := by sd h3 , s1
  exact s2
}

/-Hacer método que reciba por parámetro el número y la prueba y solo intercambiar esa ocurrencia.

Seguro se puede solo llamando rw {config} blablabla-/

example (h2: p → q) (h1: p): q :=
  h2 h1

def mt1 (h2: ¬q → ¬p) (h1: p): q := sorry
def mt2 (h2: ¬q → p) (h1: ¬p): q := sorry
def mt3 (h2: q → ¬p) (h1: p): ¬q := sorry
def mt4 (h2: q → p) (h1: ¬p): ¬q := sorry

macro "mt" h1:term "," h2:term : tactic => do
  `(tactic | (first | apply mt1 $h1 $h2 | apply mt2 $h1 $h2 | apply mt3 $h1 $h2 | apply mt4 $h1 $h2))

example (h2: ¬q → ¬p) (h1: p): q := by
  mt h2 , h1

macro "sea" nombre:term "por" tac:Lean.Parser.Tactic.tacticSeq: tactic => do
  `(tactic | have " " $nombre := by $tac)

structure Counter where
  contador : Nat

example (p q r: Prop) (h1: p) (h2: ¬q → ¬p) (h3: ¬r → ¬q): r := by
  rw [definicion_implicacion] at h2
  have s2: ¬q := by sd h2, h1

example (p q r: Prop) (h1: p) (h2: ¬q → ¬p) (h3: ¬r → ¬q): r := by
  rw [definicion_implicacion] at h2
  have s2:= by sd h2, h1

example (p q r: Prop) (h1: p) (h2: ¬q → ¬p) (h3: ¬r → ¬q): r := by
  rw [definicion_implicacion, doble_negacion] at h2
  have s2: ¬q := by mt h2, h1

open Lean
open Lean.Meta
open Lean.Elab
open Lean.Elab.Tactic

elab "check_implication" : tactic => do
  let goal ← getMainGoal
  let goalType ← Meta.inferType goal
  match goalType with
  | Expr.forallE _ _ body _ =>
    logInfo m!"The goal is a forall statement: {goalType}"
  | _ =>
    throwError "invalid Instruction !]]"

#check check_implication

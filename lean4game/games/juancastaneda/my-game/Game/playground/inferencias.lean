import Game.Levels.Equivalencias.L1

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

example (h1: p ∨ q) (h2: ¬p): q := by
  apply sd1 h1 h2

example (h1: p ∨ q) (h2: ¬p): q := by
  sd h1 , h2

example (h1: ¬p ∨ q) (h2: p): q := by
  sd h1 , h2

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

def idGen : StateM Counter
| state => Nat.succ state

example (p q r: Prop) (h1: p) (h2: p → q) (h3: ¬q ∨ r): r := by
{
  have s1 := h2 h1
  sea s2 por (sd h3 , s1)
  exact s2
}

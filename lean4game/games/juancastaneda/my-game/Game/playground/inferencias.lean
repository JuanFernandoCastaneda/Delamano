import Game.Levels.Equivalencias.L1

def sd1 (h1: p ∨ q) (h2: ¬p): q := by
  have s1: ¬p → q := by {
    revert h1
    rw (config := {occs := .pos [1]}) [← doble_negacion p]
    rw [← definicion_implicacion]
    simp
  }
  apply s1 h2

def sd2 (h1: ¬p ∨ q) (h2: p): q := by
  sorry

def sd3 (h1: p ∨ ¬q) (h2: q): p := by sorry
def sd4 (h1: p ∨ q) (h2: ¬q): p := by sorry

#check sd1
#help tactic
syntax "sd" : tactic

macro_rules
  | `(tactic| sd) => `(tactic| apply sd1)


/- Podría abstraer este proceso de tener que escribir todo de una forma como intentar $h1 $h2 que de una lista de métodos intente todos xd-/
macro "sd" h1:term "," h2:term: tactic => do
  `(tactic | (first | apply sd1 $h1 $h2 | apply sd2 $h1 $h2 | apply sd3 $h1 $h2 | apply sd4 $h1 $h2))

macro "sdp": tactic => do
  `(tactic |
    apply sd1
  )

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

variable (h1: p∨q) (h2:¬p)

/-Hacer método que reciba por parámetro el número y la prueba y solo intercambiar esa ocurrencia.

Seguro se puede solo llamando rw {config} blablabla-/

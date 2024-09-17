import Game.Metadata
import Mathlib.Tactic
import Mathlib.Util.Delaborators

theorem negacion_o (p : Prop): p ∨ ¬p ↔ True := by
  rw [or_comm]
  rw [← imp_iff_not_or]
  exact imp_self

theorem  fst_of_two_props :
  ∀a b : Prop, a → b → a :=
  by
    intro a b
    intro ha hb
    apply ha

/--
If multiple names are supplied (i.e., n > 1), multiple
variables or assumptions are moved.
-/

theorem prop_comp (a b c : Prop) (hab : a → b) (hbc : b → c) :
a → c :=
  by
    intro ha
    apply hbc
    apply hab
    apply ha


example (p q r : Prop): p ∧ (q ∧ r) = (r ∧ p) ∧ q :=
  by ac_rfl

example (p q r : ℕ): p + (q + r) = (r + p) + q :=
  by ac_rfl

variable {α : Type*}

example (p q r : Set α): p ∪ (q ∪ r) = (r ∪ p) ∪ q :=
  by ac_rfl

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

example (p q : Prop): (p ∧ q) = (q ∧ p) :=
  by ac_rfl

variable {α : Type*}

example (p q : Set α): (p ∪ q) = (q ∪ p) :=
  by exact Set.union_comm p q

example (p q : Set α): (p ∪ q) = (q ∪ p) :=
  by ac_rfl

example (p q : Prop): (p ∧ q) = (q ∧ p) :=
  by simp

example (p q : Prop): (p ↔ q) → p = q :=
  by exact fun a => propext a

example (p q : Prop): p = q → (p ↔ q) :=
  by exact fun a => iff_of_eq a

theorem and_ass_equality (p q r: Prop): (p ∧ (q ∧ r)) = ((p ∧ q) ∧ r) := by
  have h: p ∧ (q ∧ r) ↔ (p ∧ q) ∧ r := by exact Iff.symm and_assoc
  exact propext h

theorem and_comm_equality (p q : Prop): (p ∧ q) = (q ∧ p) := by
  have h: p ∧ q ↔ q ∧ p := by exact and_comm
  exact propext h

example (p q r : Set α): p ∪ (q ∪ r) = (r ∪ p) ∪ q :=
  by ac_rfl

example (p q r : Prop): p ∧ (q ∧ r) ↔ (r ∧ p) ∧ q :=
  by simp[propext, iff_of_eq]

theorem And_swap_braces :
  ∀a b : Prop, a ∧ b → b ∧ a :=
  by
    intro a b hab
    apply And.intro
    { exact And.right hab }
    { exact And.left hab }

example (p q r : Prop): p ∧ (q ∧ r) ↔ (r ∧ p) ∧ q := by
  apply Iff.intro
  . intro h
    cases h with
    | intro h1 h2 =>
      cases h2 with
      | intro h21 h22 =>
        apply And.intro
        . apply And.intro
          assumption
          assumption
        . assumption
  . intro h
    cases h with
    | intro h1 h2 =>
      cases h1 with
      | intro h11 h12 =>
        apply And.intro
        assumption
        apply And.intro
        assumption
        assumption

example (p q r : Prop): p ∧ (q ∧ r) ↔ (r ∧ p) ∧ q := by
  apply Iff.intro
  . intro h1
    try cases h1
    try cases left
    try cases right
    apply And.intro
    . try apply And.intro
      repeat assumption
    . try apply And.intro
      assumption
  . sorry



example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    cases h with
    | intro hp hqr =>
      cases hqr
      . apply Or.inl; constructor <;> assumption
      . apply Or.inr; constructor <;> assumption
  . intro h
    cases h with
    | inl hpq =>
      cases hpq with
      | intro hp hq => constructor; exact hp; apply Or.inl; exact hq
    | inr hpr =>
      cases hpr with
      | intro hp hr => constructor; exact hp; apply Or.inr; exact hr

import Game.Metadata
import Mathlib.Tactic
import Mathlib.Util.Delaborators

World "TeoriaNums"
Level 1
Title "Ejercicio 1"

Introduction "A la derecha están las propiedades que puedes usar. Para ver qué hace cada una puedes poner el cursor sobre el nombre y te dirá :]"

Conclusion "
The message shown when the level is completed
"

/-
Statement (p q r : ℤ): p∣q ∧ q∣r → p∣r := by
  intro p1
  have p2 := And.left p1
  have p3 := And.right p1
  rcases p2
  rcases p3
  have p4
-/

#check Dvd.intro
#check dvd_def


example (p q r s t: ℤ) (h1: q=p*s) (h2: r=q*t): r=(p*s)*t := by
  rw [h1] at h2
  assumption

example (p q r s : ℤ) (h1: p = (q * r) * s): p = q * (r*s) := by
  rw [← mul_assoc]
  assumption



Statement (p q r : ℤ) (h1: p∣q) (h2: q∣r): p∣r := by
  rw [dvd_def] at h1
  rw [dvd_def] at h2
  let ⟨s11, s12⟩ := h1
  let ⟨s21, s22⟩ := h2
  have s2 : r = (p * s11) * s21 := by rw [s12] at s22; assumption
  have s3 : r = p * (s11 * s21) := by rw [← mul_assoc]; assumption
  apply Dvd.intro (s11*s21) s3.symm

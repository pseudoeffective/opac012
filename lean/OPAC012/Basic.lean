import Mathlib

open scoped BigOperators
open Polynomial Finset

namespace OPAC012

/-- The coefficient ring used throughout the formalization. -/
abbrev QPoly := Polynomial ℤ

/-- Coefficientwise nonnegativity for an integer polynomial. -/
def CoeffNonneg (p : QPoly) : Prop :=
  ∀ d : ℕ, 0 ≤ p.coeff d

lemma coeffNonneg_zero : CoeffNonneg (0 : QPoly) := by
  intro d
  simp

lemma coeffNonneg_one : CoeffNonneg (1 : QPoly) := by
  intro d
  rw [Polynomial.coeff_one]
  split <;> simp

lemma coeffNonneg_add {p q : QPoly}
    (hp : CoeffNonneg p) (hq : CoeffNonneg q) :
    CoeffNonneg (p + q) := by
  intro d
  simpa using add_nonneg (hp d) (hq d)

lemma coeffNonneg_mul {p q : QPoly}
    (hp : CoeffNonneg p) (hq : CoeffNonneg q) :
    CoeffNonneg (p * q) := by
  intro d
  rw [Polynomial.coeff_mul]
  exact Finset.sum_nonneg fun x hx =>
    mul_nonneg (hp x.1) (hq x.2)

lemma coeffNonneg_X_pow (n : ℕ) : CoeffNonneg (X ^ n : QPoly) := by
  intro d
  rw [Polynomial.coeff_X_pow]
  split <;> simp

lemma coeffNonneg_C {z : ℤ} (hz : 0 ≤ z) :
    CoeffNonneg (C z : QPoly) := by
  intro d
  by_cases h : d = 0
  · subst d
    simpa using hz
  · rw [Polynomial.coeff_C_of_ne_zero h]

lemma coeffNonneg_sum {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → QPoly)
    (h : ∀ i ∈ s, CoeffNonneg (f i)) :
    CoeffNonneg (s.sum f) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using coeffNonneg_zero
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      apply coeffNonneg_add
      · exact h a (by simp)
      · apply ih
        intro i hi
        exact h i (by simp [hi])

lemma coeffNonneg_prod {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → QPoly)
    (h : ∀ i ∈ s, CoeffNonneg (f i)) :
    CoeffNonneg (s.prod f) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using coeffNonneg_one
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha]
      apply coeffNonneg_mul
      · exact h a (by simp)
      · apply ih
        intro i hi
        exact h i (by simp [hi])

end OPAC012

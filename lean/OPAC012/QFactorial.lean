import OPAC012.Basic

open scoped BigOperators
open Polynomial Finset

namespace OPAC012



/-- The q-integer `[n]_q = 1 + q + ... + q^(n-1)`. -/
noncomputable def qInt (n : ℕ) : QPoly :=
  (Finset.range n).sum (fun i => (X : QPoly) ^ i)

lemma qInt_add (m n : ℕ) :
    qInt (m + n) = qInt m + X ^ m * qInt n := by
  simp only [qInt, Finset.sum_range_add, pow_add, Finset.mul_sum]

/-- The q-factorial `[n]!_q`. -/
noncomputable def qFact (n : ℕ) : QPoly :=
  (Finset.range n).prod (fun i => qInt (i + 1))

/-- The normalized product
    `Pi a r = [a+1]_q [a+2]_q ... [a+r]_q`. -/
noncomputable def Pi (a r : ℕ) : QPoly :=
  (Finset.range r).prod (fun s => qInt (a + s + 1))

lemma qInt_coeffNonneg (n : ℕ) :
    CoeffNonneg (qInt n) := by
  unfold qInt
  exact coeffNonneg_sum
    (Finset.range n)
    (fun i => (X : QPoly) ^ i)
    (fun i hi => coeffNonneg_X_pow i)

lemma qInt_coeff (n d : ℕ) :
    (qInt n).coeff d = if d < n then 1 else 0 := by
  unfold qInt
  rw [Polynomial.finsetSum_coeff]
  by_cases hd : d < n
  · rw [Finset.sum_eq_single d]
    · simp [hd, Polynomial.coeff_X_pow]
    · intro i hi hne
      simp [Polynomial.coeff_X_pow, Ne.symm hne]
    · simp [hd]
  · simp only [ite_eq_right hd]
    apply Finset.sum_eq_zero
    intro i hi
    have hne : d ≠ i := by
      have := Finset.mem_range.mp hi
      omega
    simp [Polynomial.coeff_X_pow, hne]

lemma qFact_coeffNonneg (n : ℕ) :
    CoeffNonneg (qFact n) := by
  unfold qFact
  exact coeffNonneg_prod
    (Finset.range n)
    (fun i => qInt (i + 1))
    (fun i hi => qInt_coeffNonneg (i + 1))

lemma Pi_coeffNonneg (a r : ℕ) :
    CoeffNonneg (Pi a r) := by
  unfold Pi
  exact coeffNonneg_prod
    (Finset.range r)
    (fun s => qInt (a + s + 1))
    (fun s hs => qInt_coeffNonneg (a + s + 1))

@[simp]
lemma qFact_zero :
    qFact 0 = 1 := by
  simp [qFact]

@[simp]
lemma Pi_zero (a : ℕ) :
    Pi a 0 = 1 := by
  simp [Pi]

lemma qFact_succ (n : ℕ) :
    qFact (n + 1) = qFact n * qInt (n + 1) := by
  unfold qFact
  rw [Finset.prod_range_succ]

lemma Pi_succ (a r : ℕ) :
    Pi a (r + 1) = Pi a r * qInt (a + r + 1) := by
  unfold Pi
  rw [Finset.prod_range_succ]

lemma Pi_shift (a r : ℕ) :
    Pi a (r + 1) = qInt (a + 1) * Pi (a + 1) r := by
  induction r with
  | zero => simp [Pi_succ]
  | succ r ih =>
      rw [Pi_succ, ih, Pi_succ]
      have h : a + (r + 1) + 1 = (a + 1) + r + 1 := by omega
      rw [h]
      ring

lemma qFact_add_Pi (m n : ℕ) :
    qFact (m + n) = qFact m * Pi m n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Nat.add_succ, qFact_succ, Pi_succ, ih]
      ring

end OPAC012

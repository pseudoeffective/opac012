import OPAC012.QFactorial

open scoped BigOperators
open Polynomial Finset

namespace OPAC012

/-- The original alternating sum `S_{k,m}(q)`. -/
noncomputable def S (k m : ℕ) : QPoly :=
  (Finset.range (k + 1)).sum fun i =>
    C (((-1 : ℤ) ^ i) * (k.choose i : ℤ)) * qFact (m - i)

/-- The normalized finite difference `F_t(a)`. -/
noncomputable def F (t a : ℕ) : QPoly :=
  (Finset.range (t + 1)).sum fun r =>
    C (((-1 : ℤ) ^ (t - r)) * (t.choose r : ℤ)) * Pi a r

/-- Reindex `F_t(a)` by `i = t-r`, matching the indexing of `S`. -/
lemma F_eq_reflected (t a : ℕ) :
    F t a =
      (Finset.range (t + 1)).sum (fun i =>
        C (((-1 : ℤ) ^ i) * (t.choose i : ℤ)) * Pi a (t - i)) := by
  unfold F
  rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro i hi
  have hi_le : i ≤ t := by
    have hi_lt : i < t + 1 := Finset.mem_range.mp hi
    omega
  have h1 : t + 1 - 1 - i = t - i := by
    omega
  rw [h1]
  have h2 : t - (t - i) = i := Nat.sub_sub_self hi_le
  rw [h2, Nat.choose_symm hi_le]

/-- The normalization identity `S_{k,m} = [m-k]! F_k(m-k)`. -/
theorem S_eq_qFact_mul_F {k m : ℕ} (hkm : k ≤ m) :
    S k m = qFact (m - k) * F k (m - k) := by
  rw [F_eq_reflected]
  unfold S
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i ≤ k := by
    have hi_lt : i < k + 1 := Finset.mem_range.mp hi
    omega
  have hsplit : m - i = (m - k) + (k - i) := by
    omega
  rw [hsplit, qFact_add_Pi]
  ring

end OPAC012

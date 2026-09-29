import OPAC012.Sharpness

open Polynomial Finset

namespace OPAC012

/-- Positivity of the normalized finite difference in the stable range. -/
theorem F_coeffNonneg_of_ge
    {t a : ℕ} (ht : 1 ≤ t) (ha : t - 1 ≤ a) :
    CoeffNonneg (F t a) := by
  rw [universal_expansion ht ha]
  apply coeffNonneg_add
  · apply coeffNonneg_mul
    · apply coeffNonneg_mul
      · exact coeffNonneg_X_pow t
      · exact qInt_coeffNonneg (a + 1 - t)
    · exact Pi_coeffNonneg a (t - 1)
  · apply coeffNonneg_mul
    · exact coeffNonneg_X_pow (a + 1)
    · apply coeffNonneg_sum
      intro j hj
      have hjt : j < t := Finset.mem_range.mp hj
      apply coeffNonneg_mul
      · apply coeffNonneg_mul
        · exact coeffNonneg_X_pow j
        · exact qGaussian_coeffNonneg (a + j - 1) j
      · exact theta_coeffNonneg ht hjt

/-- Phase D stable-range positivity theorem. The inequality is written without
truncated subtraction. -/
theorem S_coeffNonneg
    {k m : ℕ} (hkm : k ≤ m) (hstable : 2 * k ≤ m + 1) :
    CoeffNonneg (S k m) := by
  cases k with
  | zero =>
      simpa [S] using qFact_coeffNonneg m
  | succ k =>
      rw [S_eq_qFact_mul_F hkm]
      apply coeffNonneg_mul (qFact_coeffNonneg (m - (k + 1)))
      apply F_coeffNonneg_of_ge
      · omega
      · omega

/-- Lewis--Morales / OPAC-012 specialization. -/
theorem opac012_coeffNonneg (n : ℕ) : CoeffNonneg (S n (2 * n)) := by
  apply S_coeffNonneg <;> omega

end OPAC012

import OPAC012.Normalization

open scoped BigOperators
open Polynomial Finset

namespace OPAC012

/-!
Universal Gaussian basis and the finite-difference recurrence. The final
identification of the recursive remainder with the closed coefficients is
still pending.
-/

/-- The Gaussian polynomial `\qbinom{n}{j}_q`, with the recurrence
`\qbinom{n+1}{j+1}_q = \qbinom{n}{j}_q + q^{j+1}\qbinom{n}{j+1}_q`. -/
noncomputable def qGaussian : ℕ → ℕ → QPoly
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, j + 1 =>
      qGaussian n j + X ^ (j + 1) * qGaussian n (j + 1)

lemma qGaussian_coeffNonneg (n j : ℕ) :
    CoeffNonneg (qGaussian n j) := by
  induction n generalizing j with
  | zero =>
      cases j with
      | zero => simpa [qGaussian] using coeffNonneg_one
      | succ j => simpa [qGaussian] using coeffNonneg_zero
  | succ n ih =>
      cases j with
      | zero => simpa [qGaussian] using coeffNonneg_one
      | succ j =>
          simpa only [qGaussian] using
            coeffNonneg_add (ih j)
              (coeffNonneg_mul (coeffNonneg_X_pow (j + 1)) (ih (j + 1)))

lemma qGaussian_hockey (a r : ℕ) :
    (Finset.range (r + 1)).sum (fun j =>
      (X : QPoly) ^ j * qGaussian (a + j - 1) j) =
      qGaussian (a + r) r := by
  induction r with
  | zero => simp [qGaussian]
  | succ r ih =>
      rw [Finset.sum_range_succ, ih]
      have h : a + (r + 1) - 1 = a + r := by omega
      rw [h]
      simp only [qGaussian]
      rfl

lemma qGaussian_zero_of_lt {n j : ℕ} (h : n < j) :
    qGaussian n j = 0 := by
  induction n generalizing j with
  | zero =>
      cases j with
      | zero => omega
      | succ j => simp [qGaussian]
  | succ n ih =>
      cases j with
      | zero => omega
      | succ j =>
          have hj : n < j := by omega
          simp [qGaussian, ih hj, ih (by omega : n < j + 1)]

lemma qGaussian_self (n : ℕ) : qGaussian n n = 1 := by
  induction n with
  | zero => simp [qGaussian]
  | succ n ih =>
      rw [qGaussian, qGaussian_zero_of_lt (by omega : n < n + 1)]
      simpa using ih

lemma Pi_zero_base (r : ℕ) : Pi 0 r = qFact r := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Pi_succ, qFact_succ, ih]
      congr 1
      congr 1
      omega

lemma Pi_eq_qFact_mul_qGaussian (a r : ℕ) :
    Pi a r = qFact r * qGaussian (a + r) r := by
  induction a generalizing r with
  | zero =>
      rw [Pi_zero_base, zero_add, qGaussian_self, mul_one]
  | succ a ih =>
      induction r with
      | zero => simp [qGaussian]
      | succ r hr =>
          have hindex : (a + 1) + (r + 1) = (a + 1 + r) + 1 := by omega
          have hindex' : a + (r + 1) = a + 1 + r := by omega
          have hPi : Pi (a + 1) (r + 1) =
              qInt (r + 1) * Pi (a + 1) r +
                X ^ (r + 1) * Pi a (r + 1) := by
            rw [Pi_succ, Pi_shift]
            have h : (a + 1) + r + 1 = (r + 1) + (a + 1) := by omega
            rw [h, qInt_add]
            ring
          rw [hPi, hr, ih (r + 1), qFact_succ, hindex, qGaussian]
          rw [← hindex']
          ring

/-- `lambda_{N,d}` from the source proof. -/
noncomputable def lambda (N d : ℕ) : QPoly :=
  (Finset.Icc d N).sum (fun s =>
    C (s.choose d : ℤ) * X ^ (N - s))

lemma lambda_coeffNonneg (N d : ℕ) : CoeffNonneg (lambda N d) := by
  unfold lambda
  apply coeffNonneg_sum
  intro s hs
  apply coeffNonneg_mul
  · exact coeffNonneg_C (Int.natCast_nonneg _)
  · exact coeffNonneg_X_pow _

lemma lambda_coeff (N D n : ℕ) (hD : D ≤ N) :
    (lambda N D).coeff n =
      if n ≤ N - D then ((N - n).choose D : ℤ) else 0 := by
  unfold lambda
  rw [Polynomial.finsetSum_coeff]
  by_cases hn : n ≤ N - D
  · have hm : N - n ∈ Finset.Icc D N := by
      simp only [Finset.mem_Icc]
      omega
    rw [Finset.sum_eq_single (N - n)]
    · have hsub : N - (N - n) = n := by omega
      simp [hn, hsub, Polynomial.coeff_X_pow]
    · intro s hs hne
      have hsN : s ≤ N := (Finset.mem_Icc.mp hs).2
      have hdeg : n ≠ N - s := by
        intro heq
        have : s = N - n := by omega
        exact hne this
      simp [Polynomial.coeff_X_pow, hdeg]
    · simp [hm]
  · simp only [ite_eq_right hn]
    apply Finset.sum_eq_zero
    intro s hs
    have hsD : D ≤ s := (Finset.mem_Icc.mp hs).1
    have hdeg : n ≠ N - s := by omega
    simp [Polynomial.coeff_X_pow, hdeg]

lemma lambda_zero_of_gt (N D : ℕ) (h : N < D) : lambda N D = 0 := by
  unfold lambda
  apply Finset.sum_eq_zero
  intro s hs
  have := Finset.mem_Icc.mp hs
  omega

/-- Pascal's identity for the universal inner sums. -/
lemma lambda_pascal (N d : ℕ) :
    lambda (N + 1) (d + 1) = lambda N (d + 1) + lambda N d := by
  by_cases hd : d ≤ N
  · ext n
    rw [Polynomial.coeff_add, lambda_coeff (N + 1) (d + 1) n (by omega),
      lambda_coeff N d n hd]
    by_cases hnext : d + 1 ≤ N
    · rw [lambda_coeff N (d + 1) n hnext]
      by_cases hn : n < N - d
      · have h1 : n ≤ N - (d + 1) := by omega
        have h2 : n ≤ N - d := by omega
        have h3 : n ≤ N + 1 - (d + 1) := by omega
        simp only [if_pos h1, if_pos h2, if_pos h3]
        have harg : N + 1 - n = (N - n) + 1 := by omega
        rw [harg, Nat.choose_succ_succ', Nat.cast_add]
        ring
      · by_cases heq : n = N - d
        · have h1 : ¬n ≤ N - (d + 1) := by omega
          have h2 : n ≤ N - d := by omega
          have h3 : n ≤ N + 1 - (d + 1) := by omega
          simp only [if_neg h1, if_pos h2, if_pos h3, zero_add]
          have ha : N + 1 - n = d + 1 := by omega
          have hb : N - n = d := by omega
          simp [ha, hb]
        · have h1 : ¬n ≤ N - (d + 1) := by omega
          have h2 : ¬n ≤ N - d := by omega
          have h3 : ¬n ≤ N + 1 - (d + 1) := by omega
          simp [h1, h2, h3]
    · have heq : d = N := by omega
      subst d
      rw [lambda_zero_of_gt N (N + 1) (by omega)]
      rw [Polynomial.coeff_zero]
      by_cases hn : n = 0
      · subst n
        simp [lambda_coeff]
      · have h1 : ¬n ≤ N + 1 - (N + 1) := by omega
        have h2 : ¬n ≤ N - N := by omega
        simp [hn, h1, h2]
  · have h1 : N + 1 < d + 1 := by omega
    have h2 : N < d + 1 := by omega
    rw [lambda_zero_of_gt _ _ h1, lambda_zero_of_gt _ _ h2,
      lambda_zero_of_gt _ _ (by omega : N < d)]
    ring

lemma lambda_zero (N : ℕ) : lambda N 0 = qInt (N + 1) := by
  ext n
  rw [lambda_coeff N 0 n (Nat.zero_le N), qInt_coeff]
  by_cases hn : n ≤ N
  · have hn' : n < N + 1 := by omega
    simp [hn, hn']
  · have hn' : ¬n < N + 1 := by omega
    simp [hn, hn']

/-- Coefficients of the remainder in the product basis `Pi a r`. -/
noncomputable def remainderCoeff : ℕ → ℕ → QPoly
  | 0, _ => 0
  | t + 1, r =>
      if r = t then qInt t
      else if r < t then
        C ((-1 : ℤ) ^ (t + 1 - r)) * X ^ r * lambda t (t - r)
      else 0

lemma remainderCoeff_top (t : ℕ) :
    remainderCoeff (t + 1) t = qInt t := by
  simp [remainderCoeff]

lemma remainderCoeff_outside (t r : ℕ) (h : t ≤ r) :
    remainderCoeff t r = 0 := by
  cases t with
  | zero => simp [remainderCoeff]
  | succ t =>
      have hne : r ≠ t := by omega
      have hlt : ¬r < t := by omega
      simp [remainderCoeff, hne, hlt]

lemma remainderCoeff_low (t r : ℕ) (h : r + 1 < t) :
    remainderCoeff t r =
      C ((-1 : ℤ) ^ (t - r)) * X ^ r * lambda (t - 1) (t - 1 - r) := by
  obtain ⟨u, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
  have hne : r ≠ u := by omega
  have hlt : r < u := by omega
  simp [remainderCoeff, hne, hlt]

private lemma qInt_split_middle (t : ℕ) (ht : 1 ≤ t) :
    qInt (2 * t - 1) =
      qInt (t - 1) + X ^ (t - 1) * qInt t := by
  have h : 2 * t - 1 = (t - 1) + t := by omega
  rw [h, qInt_add]

private lemma qInt_one_plus (t : ℕ) (ht : 1 ≤ t) :
    qInt t = 1 + X * qInt (t - 1) := by
  have h : t = 1 + (t - 1) := by omega
  rw [h, qInt_add]
  simp [qInt]

private lemma remainderCoeff_last (t : ℕ) (ht : 1 ≤ t) :
    remainderCoeff t (t - 1) = qInt (t - 1) := by
  obtain ⟨u, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
  simpa using remainderCoeff_top u

private lemma remainderCoeff_recurrence_top (t : ℕ) (ht : 1 ≤ t) :
    remainderCoeff (t + 1) t =
      (if t = t then (1 : QPoly) else 0) +
      (if t + 1 = t then qInt (2 * t - 1) else 0) +
      (if t = 0 then 0 else X * remainderCoeff t (t - 1)) -
      remainderCoeff t t := by
  rw [remainderCoeff_top, remainderCoeff_last t ht,
    remainderCoeff_outside t t (le_refl t), qInt_one_plus t ht]
  simp [show t ≠ 0 by omega]

private lemma remainderCoeff_recurrence_far (t r : ℕ) (h : t < r) :
    remainderCoeff (t + 1) r =
      (if r = t then (1 : QPoly) else 0) +
      (if r + 1 = t then qInt (2 * t - 1) else 0) +
      (if r = 0 then 0 else X * remainderCoeff t (r - 1)) -
      remainderCoeff t r := by
  have hprev : t ≤ r - 1 := by omega
  rw [remainderCoeff_outside (t + 1) r (by omega),
    remainderCoeff_outside t (r - 1) hprev,
    remainderCoeff_outside t r (by omega)]
  simp [show r ≠ t by omega, show r + 1 ≠ t by omega,
    show r ≠ 0 by omega]

private lemma remainderCoeff_recurrence_boundary (t : ℕ) (ht : 1 ≤ t) :
    remainderCoeff (t + 1) (t - 1) =
      (if t - 1 = t then (1 : QPoly) else 0) +
      (if t - 1 + 1 = t then qInt (2 * t - 1) else 0) +
      (if t - 1 = 0 then 0 else X * remainderCoeff t (t - 2)) -
      remainderCoeff t (t - 1) := by
  by_cases ht1 : t = 1
  · subst t
    have hI : Finset.Icc 1 1 = {1} := by simp
    simp [remainderCoeff, qInt, lambda, hI]
  · have ht2 : 2 ≤ t := by omega
    have hleft : remainderCoeff (t + 1) (t - 1) =
        X ^ (t - 1) * lambda t 1 := by
      rw [remainderCoeff_low (t + 1) (t - 1) (by omega)]
      have h1 : t + 1 - (t - 1) = 2 := by omega
      have h2 : t + 1 - 1 - (t - 1) = 1 := by omega
      rw [h1, h2]
      norm_num
    have hprev : remainderCoeff t (t - 2) =
        X ^ (t - 2) * lambda (t - 1) 1 := by
      rw [remainderCoeff_low t (t - 2) (by omega)]
      have h1 : t - (t - 2) = 2 := by omega
      have h2 : t - 1 - (t - 2) = 1 := by omega
      rw [h1, h2]
      norm_num
    have hlast := remainderCoeff_last t ht
    have hsplit := qInt_split_middle t ht
    have hlam : lambda t 1 = lambda (t - 1) 1 + qInt t := by
      have h : t - 1 + 1 = t := by omega
      rw [← h, lambda_pascal (t - 1) 0, lambda_zero]
      rw [h]
    have hp : (X : QPoly) * X ^ (t - 2) = X ^ (t - 1) := by
      have h : t - 2 + 1 = t - 1 := by omega
      rw [← h, pow_succ]
      ring
    rw [hleft, hprev, hlast, hsplit, hlam]
    simp [show t - 1 ≠ t by omega, show t - 1 + 1 = t by omega,
      show t - 1 ≠ 0 by omega]
    rw [← mul_assoc, hp]
    ring

private lemma remainderCoeff_recurrence_zero (t : ℕ) (ht : 2 ≤ t) :
    remainderCoeff (t + 1) 0 =
      (if 0 = t then (1 : QPoly) else 0) +
      (if 0 + 1 = t then qInt (2 * t - 1) else 0) +
      (if 0 = 0 then 0 else X * remainderCoeff t (0 - 1)) -
      remainderCoeff t 0 := by
  have hleft : remainderCoeff (t + 1) 0 =
      C ((-1 : ℤ) ^ (t + 1)) * lambda t t := by
    rw [remainderCoeff_low (t + 1) 0 (by omega)]
    simp
  have hprev : remainderCoeff t 0 =
      C ((-1 : ℤ) ^ t) * lambda (t - 1) (t - 1) := by
    rw [remainderCoeff_low t 0 (by omega)]
    simp
  have hlam : lambda t t = lambda (t - 1) (t - 1) := by
    have h : t - 1 + 1 = t := by omega
    have hp := lambda_pascal (t - 1) (t - 1)
    rw [h] at hp
    have hzero := lambda_zero_of_gt (t - 1) t (by omega)
    rw [hzero, zero_add] at hp
    exact hp
  have hsign : (-1 : ℤ) ^ (t + 1) = -(-1 : ℤ) ^ t := by
    rw [pow_succ]
    ring
  rw [hleft, hprev, hlam, hsign]
  have h0 : (0 : ℕ) ≠ t := by omega
  have h1 : (0 : ℕ) + 1 ≠ t := by omega
  simp only [ite_eq_right h0, ite_eq_right h1, ↓reduceIte,
    zero_add, add_zero, zero_sub]
  rw [map_neg]
  ring

private lemma remainderCoeff_recurrence_interior (t r : ℕ)
    (hr0 : 1 ≤ r) (hrt : r + 1 < t) :
    remainderCoeff (t + 1) r =
      (if r = t then (1 : QPoly) else 0) +
      (if r + 1 = t then qInt (2 * t - 1) else 0) +
      (if r = 0 then 0 else X * remainderCoeff t (r - 1)) -
      remainderCoeff t r := by
  have hleft : remainderCoeff (t + 1) r =
      C ((-1 : ℤ) ^ (t + 1 - r)) * X ^ r *
        lambda t (t - r) := by
    rw [remainderCoeff_low (t + 1) r (by omega)]
    have h : t + 1 - 1 - r = t - r := by omega
    rw [h, show t + 1 - 1 = t by omega]
  have hprev : remainderCoeff t (r - 1) =
      C ((-1 : ℤ) ^ (t + 1 - r)) * X ^ (r - 1) *
        lambda (t - 1) (t - r) := by
    rw [remainderCoeff_low t (r - 1) (by omega)]
    have h1 : t - (r - 1) = t + 1 - r := by omega
    have h2 : t - 1 - (r - 1) = t - r := by omega
    rw [h1, h2]
  have hcurr : remainderCoeff t r =
      C ((-1 : ℤ) ^ (t - r)) * X ^ r *
        lambda (t - 1) (t - 1 - r) := by
    rw [remainderCoeff_low t r (by omega)]
  have hlam : lambda t (t - r) =
      lambda (t - 1) (t - r) + lambda (t - 1) (t - 1 - r) := by
    have hN : t - 1 + 1 = t := by omega
    have hd : t - 1 - r + 1 = t - r := by omega
    simpa only [hN, hd] using lambda_pascal (t - 1) (t - 1 - r)
  have hsign : (-1 : ℤ) ^ (t + 1 - r) =
      -(-1 : ℤ) ^ (t - r) := by
    have h : t + 1 - r = (t - r) + 1 := by omega
    rw [h, pow_succ]
    ring
  have hp : (X : QPoly) * X ^ (r - 1) = X ^ r := by
    have h : r - 1 + 1 = r := by omega
    calc
      _ = X ^ ((r - 1) + 1) := by rw [pow_succ]; ring
      _ = X ^ r := by rw [h]
  rw [hleft, hprev, hcurr, hlam, hsign]
  simp only [ite_eq_right (show r ≠ t by omega),
    ite_eq_right (show r + 1 ≠ t by omega),
    ite_eq_right (show r ≠ 0 by omega), zero_add, map_neg]
  linear_combination
    (C ((-1 : ℤ) ^ (t - r)) * lambda (t - 1) (t - r)) * hp

lemma remainderCoeff_recurrence (t r : ℕ) (ht : 1 ≤ t) :
    remainderCoeff (t + 1) r =
      (if r = t then (1 : QPoly) else 0) +
      (if r + 1 = t then qInt (2 * t - 1) else 0) +
      (if r = 0 then 0 else X * remainderCoeff t (r - 1)) -
      remainderCoeff t r := by
  by_cases hfar : t < r
  · exact remainderCoeff_recurrence_far t r hfar
  by_cases htop : r = t
  · subst r
    exact remainderCoeff_recurrence_top t ht
  by_cases hboundary : r + 1 = t
  · have hr : r = t - 1 := by omega
    subst r
    exact remainderCoeff_recurrence_boundary t ht
  by_cases hr0 : r = 0
  · subst r
    exact remainderCoeff_recurrence_zero t (by omega)
  · exact remainderCoeff_recurrence_interior t r (by omega) (by omega)

/-- Universal coefficient `Theta_{t,j}`; intended for `1 ≤ t` and `j < t`. -/
noncomputable def theta (t j : ℕ) : QPoly :=
  let N := t - 1
  qFact N * qInt N +
    (Finset.range (N - j)).sum (fun e =>
      C ((-1 : ℤ) ^ (e + 2)) *
        X ^ (N - (e + 1)) *
        qFact (N - (e + 1)) *
        lambda N (e + 1))

lemma F_one (a : ℕ) : F 1 a = X * qInt a := by
  have h : F 1 a = qInt (a + 1) - 1 := by
    simp [F, Finset.sum_range_succ, Pi_succ]
    ring
  rw [h]
  have ha : a + 1 = 1 + a := by omega
  rw [ha, qInt_add]
  simp [qInt]

/-- The distinguished threshold term in the finite-difference expansion. -/
noncomputable def thresholdTerm (t a : ℕ) : QPoly :=
  X ^ t * qInt (a + 1 - t) * Pi a (t - 1)

private lemma qInt_two_step (n : ℕ) :
    qInt (n + 2) = X * qInt n + 1 + X ^ (n + 1) := by
  induction n with
  | zero => simp [qInt, Finset.sum_range_succ]
  | succ n ih =>
      have h1 : qInt (n + 1 + 2) = qInt (n + 2) + X ^ (n + 2) := by
        simp [qInt, Finset.sum_range_succ]
      have h2 : qInt (n + 1) = qInt n + X ^ n := by
        simp [qInt, Finset.sum_range_succ]
      rw [h1, ih, h2]
      ring

/-- The threshold terms leave two explicit positive-basis terms under the
finite-difference recurrence. -/
lemma threshold_recurrence (t a : ℕ) (ht : 1 ≤ t) (ha : t ≤ a) :
    qInt (a + 1) * thresholdTerm t (a + 1) -
      thresholdTerm t a - thresholdTerm (t + 1) a =
      X ^ (a + 1) *
        (Pi a t + qInt (2 * t - 1) * Pi a (t - 1)) := by
  have hPi : qInt (a + 1) * Pi (a + 1) (t - 1) = Pi a t := by
    have h : t - 1 + 1 = t := by omega
    rw [← Pi_shift, h]
  have hPt : Pi a t = Pi a (t - 1) * qInt (a + t) := by
    have h : t - 1 + 1 = t := by omega
    rw [← h, Pi_succ]
    congr 1
  have hsub1 : a + 1 - t = (a - t) + 1 := by omega
  have hsub2 : a + 1 + 1 - t = (a - t) + 2 := by omega
  have hsub3 : a + 1 - (t + 1) = a - t := by omega
  have hsum : (a - t) + 1 + (2 * t - 1) = a + t := by omega
  have hq : qInt (a + t) =
      qInt ((a - t) + 1) + X ^ ((a - t) + 1) * qInt (2 * t - 1) := by
    rw [← hsum, qInt_add]
  have hpow : t + ((a - t) + 1) = a + 1 := by omega
  calc
    _ = X ^ t * qInt (a + 1 + 1 - t) * Pi a t -
        X ^ t * qInt (a + 1 - t) * Pi a (t - 1) -
        X ^ (t + 1) * qInt (a + 1 - (t + 1)) * Pi a t := by
          unfold thresholdTerm
          rw [show t + 1 - 1 = t by omega]
          calc
            _ = X ^ t * qInt (a + 1 + 1 - t) *
                  (qInt (a + 1) * Pi (a + 1) (t - 1)) -
                  X ^ t * qInt (a + 1 - t) * Pi a (t - 1) -
                  X ^ (t + 1) * qInt (a + 1 - (t + 1)) * Pi a t := by ring
            _ = _ := by rw [hPi]
    _ = _ := by
      rw [hsub1, hsub2, hsub3, qInt_two_step]
      rw [hPt, hq]
      have hp : (X : QPoly) ^ t * X ^ (a - t + 1) = X ^ (a + 1) := by
        rw [← pow_add, hpow]
      rw [← hp, pow_succ]
      ring

/-- The remainder generated by the finite-difference recurrence, with its
threshold term removed. -/
noncomputable def remainder : ℕ → ℕ → QPoly
  | 0, _ => 0
  | 1, _ => 0
  | t + 2, a =>
      Pi a (t + 1) + qInt (2 * (t + 1) - 1) * Pi a t +
        X * qInt (a + 1) * remainder (t + 1) (a + 1) -
        remainder (t + 1) a

noncomputable def explicitRemainder (t a : ℕ) : QPoly :=
  (Finset.range t).sum (fun r => remainderCoeff t r * Pi a r)

private lemma shifted_remainder_sum (t a : ℕ) :
    (Finset.range (t + 1)).sum (fun r =>
      (if r = 0 then 0 else X * remainderCoeff t (r - 1)) * Pi a r) =
      X * qInt (a + 1) * explicitRemainder t (a + 1) := by
  rw [Finset.sum_range_succ']
  simp only [↓reduceIte, zero_mul, add_zero]
  calc
    _ = (Finset.range t).sum (fun r =>
          X * remainderCoeff t r * Pi a (r + 1)) := by
          apply Finset.sum_congr rfl
          intro r hr
          simp
    _ = _ := by
          unfold explicitRemainder
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro r hr
          rw [Pi_shift]
          ring

private lemma explicitRemainder_succ (t a : ℕ) (ht : 1 ≤ t) :
    explicitRemainder (t + 1) a =
      Pi a t + qInt (2 * t - 1) * Pi a (t - 1) +
        X * qInt (a + 1) * explicitRemainder t (a + 1) -
        explicitRemainder t a := by
  have htop :
      (Finset.range (t + 1)).sum (fun r =>
        (if r = t then (1 : QPoly) else 0) * Pi a r) = Pi a t := by
    rw [Finset.sum_eq_single t]
    · simp
    · intro r hr hne
      simp [hne]
    · simp
  have hboundary :
      (Finset.range (t + 1)).sum (fun r =>
        (if r + 1 = t then qInt (2 * t - 1) else 0) * Pi a r) =
        qInt (2 * t - 1) * Pi a (t - 1) := by
    rw [Finset.sum_eq_single (t - 1)]
    · simp [show t - 1 + 1 = t by omega]
    · intro r hr hne
      have hnot : r + 1 ≠ t := by
        intro heq
        apply hne
        omega
      simp [hnot]
    · have : t - 1 < t + 1 := by omega
      simp [this]
  have hprev :
      (Finset.range (t + 1)).sum (fun r => remainderCoeff t r * Pi a r) =
        explicitRemainder t a := by
    rw [Finset.sum_range_succ]
    simp [remainderCoeff_outside t t (le_refl t), explicitRemainder]
  unfold explicitRemainder
  calc
    _ = (Finset.range (t + 1)).sum (fun r =>
          ((if r = t then (1 : QPoly) else 0) +
            (if r + 1 = t then qInt (2 * t - 1) else 0) +
            (if r = 0 then 0 else X * remainderCoeff t (r - 1)) -
            remainderCoeff t r) * Pi a r) := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [remainderCoeff_recurrence t r ht]
    _ = _ := by
          simp only [add_mul, sub_mul, Finset.sum_add_distrib,
            Finset.sum_sub_distrib]
          rw [htop, hboundary, shifted_remainder_sum, hprev]
          rfl

lemma remainder_eq_explicit {t a : ℕ} (ht : 1 ≤ t) :
    remainder t a = explicitRemainder t a := by
  induction t generalizing a with
  | zero => omega
  | succ t ih =>
      cases t with
      | zero =>
          simp [remainder, explicitRemainder, remainderCoeff, qInt]
      | succ t =>
          have ht' : 1 ≤ t + 1 := by omega
          rw [explicitRemainder_succ (t + 1) a ht']
          change
            Pi a (t + 1) + qInt (2 * (t + 1) - 1) * Pi a t +
              X * qInt (a + 1) * remainder (t + 1) (a + 1) -
              remainder (t + 1) a =
            Pi a (t + 1) + qInt (2 * (t + 1) - 1) * Pi a t +
              X * qInt (a + 1) * explicitRemainder (t + 1) (a + 1) -
              explicitRemainder (t + 1) a
          rw [ih ht', ih ht']

lemma theta_eq_remainder_tail {t j : ℕ} (ht : 1 ≤ t) (hj : j < t) :
    theta t j =
      (Finset.Ico j t).sum (fun r => qFact r * remainderCoeff t r) := by
  let N := t - 1
  have hN : N + 1 = t := by dsimp [N]; omega
  have hlen : t - j = (N - j) + 1 := by omega
  have hreflect := Finset.sum_Ico_reflect
    (fun e => qFact (N - e) * remainderCoeff t (N - e))
    j (m := t) (n := N) (by omega : t ≤ N + 1)
  have hleft : N + 1 - t = 0 := by omega
  have hright : N + 1 - j = t - j := by omega
  rw [hleft, hright] at hreflect
  have htail :
      (Finset.Ico j t).sum (fun r => qFact r * remainderCoeff t r) =
        (Finset.range (t - j)).sum (fun e =>
          qFact (N - e) * remainderCoeff t (N - e)) := by
    rw [← Nat.Ico_zero_eq_range]
    rw [← hreflect]
    apply Finset.sum_congr rfl
    intro r hr
    have hr' : r < t := (Finset.mem_Ico.mp hr).2
    have h : N - (N - r) = r := by omega
    simp [h]
  rw [htail, hlen, Finset.sum_range_succ']
  have htop : N - 0 = N := by omega
  rw [htop]
  have hgtop : remainderCoeff t N = qInt N := by
    have h : N + 1 = t := hN
    rw [← h]
    exact remainderCoeff_top N
  rw [hgtop]
  change qFact N * qInt N +
    (Finset.range (N - j)).sum (fun e =>
      C ((-1 : ℤ) ^ (e + 2)) * X ^ (N - (e + 1)) *
        qFact (N - (e + 1)) * lambda N (e + 1)) = _
  conv_rhs => rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro e he
  have heN : e < N - j := Finset.mem_range.mp he
  have hr : N - (e + 1) + 1 < t := by omega
  rw [remainderCoeff_low t (N - (e + 1)) hr]
  have hsign : t - (N - (e + 1)) = e + 2 := by omega
  have hidx : t - 1 - (N - (e + 1)) = e + 1 := by omega
  rw [hsign, hidx]
  ring

private lemma sum_triangle (t : ℕ) (f : ℕ → ℕ → QPoly) :
    (Finset.range t).sum (fun r =>
      (Finset.range (r + 1)).sum (fun j => f r j)) =
    (Finset.range t).sum (fun j =>
      (Finset.Ico j t).sum (fun r => f r j)) := by
  have hrow (r : ℕ) (hr : r ∈ Finset.range t) :
      (Finset.range (r + 1)).sum (fun j => f r j) =
        (Finset.range t).sum (fun j => if j ≤ r then f r j else 0) := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    apply Finset.sum_congr
    · ext j
      simp only [Finset.mem_filter, Finset.mem_range]
      have hrlt : r < t := Finset.mem_range.mp hr
      omega
    · intro j hj
      rfl
  have hcol (j : ℕ) :
      (Finset.range t).sum (fun r => if j ≤ r then f r j else 0) =
        (Finset.Ico j t).sum (fun r => f r j) := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    apply Finset.sum_congr
    · ext r
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      omega
    · intro r hr
      rfl
  calc
    _ = (Finset.range t).sum (fun r =>
          (Finset.range t).sum (fun j => if j ≤ r then f r j else 0)) := by
          apply Finset.sum_congr rfl
          intro r hr
          exact hrow r hr
    _ = (Finset.range t).sum (fun j =>
          (Finset.range t).sum (fun r => if j ≤ r then f r j else 0)) := by
          rw [Finset.sum_comm]
    _ = _ := by
          apply Finset.sum_congr rfl
          intro j hj
          exact hcol j

/-- Positive-basis identity needed in Phase B. -/
theorem Pi_eq_qGaussian_sum (a r : ℕ) :
    Pi a r =
      (Finset.range (r + 1)).sum (fun j =>
        X ^ j * qFact r * qGaussian (a + j - 1) j) := by
  rw [Pi_eq_qFact_mul_qGaussian, ← qGaussian_hockey, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma explicitRemainder_eq_gaussian (t a : ℕ) (ht : 1 ≤ t) :
    explicitRemainder t a =
      (Finset.range t).sum (fun j =>
        X ^ j * qGaussian (a + j - 1) j * theta t j) := by
  unfold explicitRemainder
  calc
    _ = (Finset.range t).sum (fun r =>
          (Finset.range (r + 1)).sum (fun j =>
            (X ^ j * qGaussian (a + j - 1) j) *
              (qFact r * remainderCoeff t r))) := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [Pi_eq_qGaussian_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring
    _ = (Finset.range t).sum (fun j =>
          (Finset.Ico j t).sum (fun r =>
            (X ^ j * qGaussian (a + j - 1) j) *
              (qFact r * remainderCoeff t r))) := by
          exact sum_triangle t _
    _ = _ := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [← Finset.mul_sum]
          rw [← theta_eq_remainder_tail ht (Finset.mem_range.mp hj)]

private lemma finite_difference_pascal (t : ℕ) (g : ℕ → QPoly) :
    (Finset.range (t + 2)).sum (fun r =>
      C (((-1 : ℤ) ^ (t + 1 - r)) * ((t + 1).choose r : ℤ)) * g r) =
      (Finset.range (t + 1)).sum (fun r =>
        C (((-1 : ℤ) ^ (t - r)) * (t.choose r : ℤ)) * g (r + 1)) -
      (Finset.range (t + 1)).sum (fun r =>
        C (((-1 : ℤ) ^ (t - r)) * (t.choose r : ℤ)) * g r) := by
  let b (u r : ℕ) : QPoly :=
    C (((-1 : ℤ) ^ (u - r)) * (u.choose r : ℤ)) * g r
  have hzero : b (t + 1) 0 = -b t 0 := by
    simp [b, pow_succ]
  have hlast : b t (t + 1) = 0 := by
    simp [b]
  have hstep (r : ℕ) (hr : r < t + 1) :
      b (t + 1) (r + 1) =
        C (((-1 : ℤ) ^ (t - r)) * (t.choose r : ℤ)) * g (r + 1) -
        b t (r + 1) := by
    by_cases hrt : r = t
    · subst r
      simp [b]
    · have hlt : r < t := by omega
      have hsub : t + 1 - (r + 1) = t - r := by omega
      have hpow : (-1 : ℤ) ^ (t - r) = -(-1 : ℤ) ^ (t - (r + 1)) := by
        have h : t - r = (t - (r + 1)) + 1 := by omega
        rw [h, pow_succ]
        ring
      dsimp [b]
      rw [hsub, Nat.choose_succ_succ', Nat.cast_add]
      rw [hpow]
      simp only [map_mul, map_add, map_neg]
      ring
  have hsum : (Finset.range (t + 1)).sum (fun r => b t (r + 1)) =
      (Finset.range (t + 1)).sum (b t) - b t 0 := by
    rw [Finset.sum_range_succ, hlast, add_zero, Finset.sum_range_succ']
    ring
  change (Finset.range (t + 2)).sum (b (t + 1)) = _
  rw [Finset.sum_range_succ']
  change (Finset.range (t + 1)).sum (fun r => b (t + 1) (r + 1)) +
      b (t + 1) 0 = _
  rw [hzero]
  have hsumstep : (Finset.range (t + 1)).sum (fun r => b (t + 1) (r + 1)) =
      (Finset.range (t + 1)).sum (fun r =>
        C (((-1 : ℤ) ^ (t - r)) * (t.choose r : ℤ)) * g (r + 1) - b t (r + 1)) := by
    apply Finset.sum_congr rfl
    intro r hr
    exact hstep r (Finset.mem_range.mp hr)
  rw [hsumstep]
  rw [Finset.sum_sub_distrib, hsum]
  ring

/-- Source recurrence for the normalized finite differences. -/
theorem F_succ (t a : ℕ) :
    F (t + 1) a = qInt (a + 1) * F t (a + 1) - F t a := by
  unfold F
  rw [finite_difference_pascal]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  rw [Pi_shift]
  ring

lemma F_eq_threshold_add_remainder
    {t a : ℕ} (ht : 1 ≤ t) (ha : t - 1 ≤ a) :
    F t a = thresholdTerm t a + X ^ (a + 1) * remainder t a := by
  induction t generalizing a with
  | zero => omega
  | succ t ih =>
      cases t with
      | zero =>
          simp [remainder, thresholdTerm, F_one]
      | succ t =>
          have ht' : 1 ≤ t + 1 := by omega
          have ha' : t + 1 ≤ a := by omega
          have ih1 := ih ht' (show t + 1 - 1 ≤ a + 1 by omega)
          have ih0 := ih ht' (show t + 1 - 1 ≤ a by omega)
          have hth := threshold_recurrence (t + 1) a ht' ha'
          rw [show t + 1 - 1 = t by omega] at hth
          rw [F_succ, ih1, ih0]
          change _ = thresholdTerm (t + 2) a +
            X ^ (a + 1) *
              (Pi a (t + 1) +
                qInt (2 * (t + 1) - 1) * Pi a t +
                X * qInt (a + 1) * remainder (t + 1) (a + 1) -
                remainder (t + 1) a)
          have hp : (X : QPoly) ^ (a + 1 + 1) = X ^ (a + 1) * X := by
            rw [pow_succ]
          rw [hp]
          linear_combination hth


-- Proposition 2.1 / universal expansion.
theorem universal_expansion
    {t a : ℕ} (ht : 1 ≤ t) (ha : t - 1 ≤ a) :
    F t a =
      X ^ t * qInt (a + 1 - t) * Pi a (t - 1)
        + X ^ (a + 1) *
          (Finset.range t).sum (fun j =>
            X ^ j * qGaussian (a + j - 1) j * theta t j) := by
  rw [F_eq_threshold_add_remainder ht ha, remainder_eq_explicit ht,
    explicitRemainder_eq_gaussian t a ht]
  rfl


end OPAC012

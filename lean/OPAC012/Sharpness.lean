import OPAC012.Domination

open Polynomial Finset

namespace OPAC012

private lemma coeff_zero_mul (p q : QPoly) :
    (p * q).coeff 0 = p.coeff 0 * q.coeff 0 := by
  simp [Polynomial.coeff_mul]

private lemma coeff_one_mul (p q : QPoly) :
    (p * q).coeff 1 =
      p.coeff 0 * q.coeff 1 + p.coeff 1 * q.coeff 0 := by
  have h : (Finset.HasAntidiagonal.antidiagonal (1 : ℕ)) =
      {(0, 1), (1, 0)} := by decide
  simp [Polynomial.coeff_mul, h, add_comm]

private lemma Pi_coeff_zero (a r : ℕ) : (Pi a r).coeff 0 = 1 := by
  induction r with
  | zero => simp [Polynomial.coeff_one]
  | succ r ih =>
      rw [Pi_succ, coeff_zero_mul, ih, qInt_coeff]
      simp

private lemma Pi_coeff_one (a r : ℕ) (ha : 1 ≤ a) :
    (Pi a r).coeff 1 = (r : ℤ) := by
  induction r with
  | zero => simp [Polynomial.coeff_one]
  | succ r ih =>
      rw [Pi_succ, coeff_one_mul, Pi_coeff_zero, ih, qInt_coeff, qInt_coeff]
      have h : 1 < a + r + 1 := by omega
      have h0 : 0 < a + r + 1 := by omega
      simp [h, h0, Nat.cast_add]
      ring

private lemma remainder_coeff_zero (t a : ℕ) (ht : 1 ≤ t) :
    (remainder t a).coeff 0 = 1 + (-1 : ℤ) ^ t := by
  induction t generalizing a with
  | zero => omega
  | succ t ih =>
      cases t with
      | zero =>
          simp [remainder]
      | succ t =>
          have ht' : 1 ≤ t + 1 := by omega
          change
            (Pi a (t + 1) + qInt (2 * (t + 1) - 1) * Pi a t +
              X * qInt (a + 1) * remainder (t + 1) (a + 1) -
              remainder (t + 1) a).coeff 0 =
              1 + (-1 : ℤ) ^ (t + 2)
          simp only [Polynomial.coeff_sub, Polynomial.coeff_add]
          rw [coeff_zero_mul (qInt (2 * (t + 1) - 1)) (Pi a t)]
          rw [Pi_coeff_zero, Pi_coeff_zero, qInt_coeff]
          have hq : 0 < 2 * (t + 1) - 1 := by omega
          simp only [if_pos hq]
          have hx : ((X : QPoly) * qInt (a + 1) *
              remainder (t + 1) (a + 1)).coeff 0 = 0 := by
            rw [coeff_zero_mul, coeff_zero_mul]
            simp
          rw [hx, ih a ht']
          have hp : (-1 : ℤ) ^ (t + 2) = -(-1 : ℤ) ^ (t + 1) := by
            rw [pow_succ]
            ring
          rw [hp]
          ring

private lemma remainder_coeff_one_base (a : ℕ) (ha : 1 ≤ a) :
    (remainder 2 a).coeff 1 = 1 := by
  change (Pi a 1 + qInt 1 * Pi a 0 +
    X * qInt (a + 1) * remainder 1 (a + 1) -
    remainder 1 a).coeff 1 = 1
  simp [remainder, Pi_coeff_one a 1 ha, qInt, Polynomial.coeff_one]

private lemma remainder_coeff_one (n a : ℕ) (ha : 1 ≤ a) :
    (remainder (n + 2) a).coeff 1 =
      (n + 2 : ℤ) + (-1 : ℤ) ^ (n + 1) * (n + 1 : ℤ) := by
  induction n generalizing a with
  | zero =>
      simpa using remainder_coeff_one_base a ha
  | succ n ih =>
      have hprev := ih a ha
      have hconst := remainder_coeff_zero (n + 2) (a + 1) (by omega)
      change
        (Pi a (n + 2) +
          qInt (2 * (n + 2) - 1) * Pi a (n + 1) +
          X * qInt (a + 1) * remainder (n + 2) (a + 1) -
          remainder (n + 2) a).coeff 1 =
          (n + 1 + 2 : ℤ) +
            (-1 : ℤ) ^ (n + 1 + 1) * (n + 1 + 1 : ℤ)
      simp only [Polynomial.coeff_sub, Polynomial.coeff_add]
      rw [coeff_one_mul (qInt (2 * (n + 2) - 1)) (Pi a (n + 1))]
      rw [Pi_coeff_one a (n + 2) ha, Pi_coeff_zero,
        Pi_coeff_one a (n + 1) ha, qInt_coeff, qInt_coeff]
      have hq0 : 0 < 2 * (n + 2) - 1 := by omega
      have hq1 : 1 < 2 * (n + 2) - 1 := by omega
      simp only [if_pos hq0, if_pos hq1]
      have hx : ((X : QPoly) * qInt (a + 1) *
          remainder (n + 2) (a + 1)).coeff 1 =
          (remainder (n + 2) (a + 1)).coeff 0 := by
        rw [mul_assoc, Polynomial.coeff_X_mul]
        rw [coeff_zero_mul, qInt_coeff]
        simp
      rw [hx, hprev, hconst]
      have hp : (-1 : ℤ) ^ (n + 1 + 1) = -(-1 : ℤ) ^ (n + 1) := by
        rw [pow_succ]
        ring
      rw [hp]
      push_cast
      ring

private lemma F_boundary_eq (t : ℕ) (ht : 1 ≤ t) :
    F t (t - 1) = X ^ t * remainder t (t - 1) := by
  rw [F_eq_threshold_add_remainder ht (le_refl _)]
  unfold thresholdTerm
  have h1 : t - 1 + 1 - t = 0 := by omega
  have h2 : t - 1 + 1 = t := by omega
  rw [h1, h2]
  simp [thresholdTerm, qInt]

private lemma F_next_eq (t : ℕ) (ht : 1 ≤ t) :
    F t t = X ^ t * Pi t (t - 1) +
      X ^ (t + 1) * remainder t t := by
  rw [F_eq_threshold_add_remainder ht (by omega : t - 1 ≤ t)]
  unfold thresholdTerm
  have h : t + 1 - t = 1 := by omega
  rw [h]
  simp [thresholdTerm, qInt]

private lemma F_boundary_coeff (t : ℕ) (ht : 1 ≤ t) :
    (F t (t - 1)).coeff t = 1 + (-1 : ℤ) ^ t := by
  rw [F_boundary_eq t ht]
  have h := remainder_coeff_zero t (t - 1) ht
  simpa using (Polynomial.coeff_X_pow_mul (remainder t (t - 1)) t 0).trans h

private lemma F_next_coeff (t : ℕ) (ht : 1 ≤ t) :
    (F t t).coeff t = 1 := by
  rw [F_next_eq t ht, Polynomial.coeff_add]
  have h0 : (X ^ t * Pi t (t - 1)).coeff t = 1 := by
    simpa using (Polynomial.coeff_X_pow_mul (Pi t (t - 1)) t 0).trans
      (Pi_coeff_zero t (t - 1))
  have h1 : (X ^ (t + 1) * remainder t t).coeff t = 0 := by
    rw [Polynomial.coeff_X_pow_mul']
    simp
  rw [h0, h1]
  ring

private lemma F_boundary_next_coeff (t : ℕ) (ht : 2 ≤ t) :
    (F t (t - 1)).coeff (t + 1) =
      (t : ℤ) + (-1 : ℤ) ^ (t - 1) * (t - 1 : ℤ) := by
  rw [F_boundary_eq t (by omega)]
  have h : t - 2 + 2 = t := by omega
  have h' : t - 2 + 1 = t - 1 := by omega
  have hc := remainder_coeff_one (t - 2) (t - 1) (by omega)
  rw [h, h'] at hc
  have heq : ((t - 2 : ℕ) : ℤ) + 2 = t := by exact_mod_cast h
  have heq' : ((t - 2 : ℕ) : ℤ) + 1 = (t : ℤ) - 1 := by omega
  rw [heq, heq'] at hc
  simpa [Nat.add_comm] using
    (Polynomial.coeff_X_pow_mul (remainder t (t - 1)) t 1).trans hc

private lemma F_next_next_coeff (t : ℕ) (ht : 1 ≤ t) :
    (F t t).coeff (t + 1) = (t : ℤ) + (-1 : ℤ) ^ t := by
  rw [F_next_eq t ht, Polynomial.coeff_add]
  have h0 : (X ^ t * Pi t (t - 1)).coeff (t + 1) = (t - 1 : ℤ) := by
    have hsub : ((t - 1 : ℕ) : ℤ) = (t : ℤ) - 1 := by omega
    rw [← hsub]
    simpa [Nat.add_comm] using
      (Polynomial.coeff_X_pow_mul (Pi t (t - 1)) t 1).trans
        (Pi_coeff_one t (t - 1) ht)
  have h1 : (X ^ (t + 1) * remainder t t).coeff (t + 1) =
      1 + (-1 : ℤ) ^ t := by
    simpa using
      (Polynomial.coeff_X_pow_mul (remainder t t) (t + 1) 0).trans
        (remainder_coeff_zero t t ht)
  rw [h0, h1]
  have h : (t - 1 : ℤ) + 1 = t := by
    exact_mod_cast Nat.sub_add_cancel ht
  omega

private lemma coeff_mul_vanish (p q : QPoly) (d : ℕ)
    (hq : ∀ i ≤ d, q.coeff i = 0) :
    (p * q).coeff d = 0 := by
  rw [Polynomial.coeff_mul]
  apply Finset.sum_eq_zero
  intro x hx
  have hle : x.2 ≤ d := by
    have := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    omega
  simp [hq x.2 hle]

private lemma F_stable_vanish (t a d : ℕ)
    (ht : 1 ≤ t) (ha : t - 1 ≤ a) (hd : d < t) :
    (F t a).coeff d = 0 := by
  rw [universal_expansion ht ha, Polynomial.coeff_add]
  have h1 : (X ^ t * qInt (a + 1 - t) * Pi a (t - 1)).coeff d = 0 := by
    rw [mul_assoc, Polynomial.coeff_X_pow_mul']
    simp [show ¬t ≤ d by omega]
  have h2 : (X ^ (a + 1) *
      (Finset.range t).sum (fun j =>
        X ^ j * qGaussian (a + j - 1) j * theta t j)).coeff d = 0 := by
    rw [Polynomial.coeff_X_pow_mul']
    simp [show ¬a + 1 ≤ d by omega]
  rw [h1, h2]
  ring

private lemma F_below_vanish (t a d : ℕ)
    (ha : a + 2 ≤ t) (hd : d ≤ a) :
    (F t a).coeff d = 0 := by
  induction t generalizing a d with
  | zero => omega
  | succ t ih =>
      have ht : 1 ≤ t := by omega
      have hprev0 : (F t a).coeff d = 0 := by
        by_cases h : a + 2 ≤ t
        · exact ih a d h hd
        · have hs : t - 1 ≤ a := by omega
          exact F_stable_vanish t a d ht hs (by omega)
      have hprev1 : ∀ i ≤ d, (F t (a + 1)).coeff i = 0 := by
        intro i hi
        by_cases h : a + 1 + 2 ≤ t
        · exact ih (a + 1) i h (by omega)
        · have hs : t - 1 ≤ a + 1 := by omega
          exact F_stable_vanish t (a + 1) i ht hs (by omega)
      rw [F_succ, Polynomial.coeff_sub,
        coeff_mul_vanish (qInt (a + 1)) (F t (a + 1)) d hprev1,
        hprev0]
      ring

private lemma coeff_mul_lead (p q : QPoly) (d : ℕ)
    (hp : p.coeff 0 = 1) (hq : ∀ i < d, q.coeff i = 0) :
    (p * q).coeff d = q.coeff d := by
  rw [Polynomial.coeff_mul, Finset.sum_eq_single (0, d)]
  · simp [hp]
  · intro x hx hne
    have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    have hlt : x.2 < d := by
      have hxpos : 0 < x.1 := by
        by_contra h
        have hzero : x.1 = 0 := by omega
        have hsecond : x.2 = d := by omega
        exact hne (Prod.ext hzero hsecond)
      omega
    simp [hq x.2 hlt]
  · simp

private lemma F_lead_below (t a : ℕ) (ha : a + 2 ≤ t) :
    (F t a).coeff (a + 1) = (-1 : ℤ) ^ t := by
  induction t generalizing a with
  | zero => omega
  | succ t ih =>
      have ht : 1 ≤ t := by omega
      rw [F_succ, Polynomial.coeff_sub]
      by_cases hbase : a + 2 = t + 1
      · have hindex : a + 1 = t := by omega
        have hvan : ∀ i < a + 1, (F t (a + 1)).coeff i = 0 := by
          intro i hi
          exact F_stable_vanish t (a + 1) i ht (by omega) (by omega)
        have hmul := coeff_mul_lead (qInt (a + 1)) (F t (a + 1))
          (a + 1) (by simp [qInt_coeff]) hvan
        rw [hmul, hindex, F_next_coeff t ht]
        have hboundary : a = t - 1 := by omega
        rw [hboundary, F_boundary_coeff t ht]
        have hp : (-1 : ℤ) ^ (t + 1) = -(-1 : ℤ) ^ t := by
          rw [pow_succ]
          ring
        rw [hp]
        ring
      · have hprev : a + 2 ≤ t := by omega
        have hvan : ∀ i ≤ a + 1, (F t (a + 1)).coeff i = 0 := by
          intro i hi
          by_cases hlow : a + 1 + 2 ≤ t
          · exact F_below_vanish t (a + 1) i hlow (by omega)
          · exact F_stable_vanish t (a + 1) i ht (by omega) (by omega)
        rw [coeff_mul_vanish (qInt (a + 1)) (F t (a + 1))
          (a + 1) hvan, ih a hprev]
        rw [pow_succ]
        ring

private lemma F_two_zero : F 2 0 = X := by
  norm_num [F, Pi, qInt, Finset.sum_range_succ, Finset.prod_range_succ]

private lemma qInt_mul_F_next_coeff (s : ℕ) (hs : 2 ≤ s) :
    (qInt s * F s s).coeff (s + 1) =
      (s : ℤ) + (-1 : ℤ) ^ s + 1 := by
  have hfactor : qInt s * F s s =
      X ^ s * (qInt s * (Pi s (s - 1) + X * remainder s s)) := by
    rw [F_next_eq s (by omega)]
    rw [pow_succ]
    ring
  rw [hfactor]
  have h := Polynomial.coeff_X_pow_mul
    (qInt s * (Pi s (s - 1) + X * remainder s s)) s 1
  rw [show s + 1 = 1 + s by omega, h, coeff_one_mul]
  have hzero : (Pi s (s - 1) + X * remainder s s).coeff 0 = 1 := by
    rw [Polynomial.coeff_add, Pi_coeff_zero, coeff_zero_mul]
    simp
  have hone : (Pi s (s - 1) + X * remainder s s).coeff 1 =
      ((s - 1 : ℕ) : ℤ) + 1 + (-1 : ℤ) ^ s := by
    rw [Polynomial.coeff_add, Pi_coeff_one s (s - 1) (by omega),
      Polynomial.coeff_X_mul]
    rw [remainder_coeff_zero s s (by omega)]
    ring
  rw [hzero, hone, qInt_coeff, qInt_coeff]
  have h0 : 0 < s := by omega
  have h1 : 1 < s := by omega
  have hcast : ((s - 1 : ℕ) : ℤ) + 1 = s := by omega
  simp only [if_pos h0, if_pos h1, one_mul, mul_one]
  omega

private lemma F_next_below (t a : ℕ) (ha : a + 2 ≤ t) :
    (F t a).coeff (a + 2) =
      (if a + 2 = t then (1 : ℤ) else 0) -
        (-1 : ℤ) ^ t * (t - 1 : ℤ) := by
  induction t generalizing a with
  | zero => omega
  | succ t ih =>
      have ht : 1 ≤ t := by omega
      rw [F_succ, Polynomial.coeff_sub]
      by_cases hbase : a + 2 = t + 1
      · by_cases ht1 : t = 1
        · have ha0 : a = 0 := by omega
          subst a
          subst t
          simp [F_one, qInt]
          have h := Polynomial.coeff_X_pow (R := ℤ) 1 2
          norm_num at h
          simpa using h
        · have ht2 : 2 ≤ t := by omega
          have hindex : a + 1 = t := by omega
          have hq : qInt (a + 1) = qInt t := by rw [hindex]
          rw [hq, hindex, show a + 2 = t + 1 by omega,
            qInt_mul_F_next_coeff t ht2]
          have hab : a = t - 1 := by omega
          rw [hab, F_boundary_next_coeff t ht2]
          have hp : (-1 : ℤ) ^ (t + 1) = -(-1 : ℤ) ^ t := by
            rw [pow_succ]
            ring
          simp only [if_pos hbase, hp]
          have hs : (-1 : ℤ) ^ (t - 1) = -(-1 : ℤ) ^ t := by
            have h : t - 1 + 1 = t := by omega
            have hp' := congrArg (fun n : ℕ => (-1 : ℤ) ^ n) h
            rw [pow_succ] at hp'
            calc
              (-1 : ℤ) ^ (t - 1) =
                  -((-1 : ℤ) ^ (t - 1) * (-1)) := by ring
              _ = -(-1 : ℤ) ^ t := by rw [hp']
          rw [hs]
          simp only [ite_true]
          push_cast
          ring

      · have hprev : a + 2 ≤ t := by omega
        have hvan : ∀ i < a + 2, (F t (a + 1)).coeff i = 0 := by
          intro i hi
          by_cases hlow : a + 3 ≤ t
          · exact F_below_vanish t (a + 1) i hlow (by omega)
          · exact F_stable_vanish t (a + 1) i ht (by omega) (by omega)
        have hmul := coeff_mul_lead (qInt (a + 1)) (F t (a + 1))
          (a + 2) (by simp [qInt_coeff]) hvan
        rw [hmul, ih a hprev]
        by_cases hb : a + 2 = t
        · have hab : a + 1 = t - 1 := by omega
          rw [hab, show a + 2 = t by omega,
            F_boundary_coeff t ht]
          simp [hbase]
          rw [pow_succ]
          push_cast
          ring
        · have hlow : a + 3 ≤ t := by omega
          rw [F_lead_below t (a + 1) hlow]
          simp [hb, hbase]
          rw [pow_succ]
          push_cast
          ring

private lemma qFact_coeff_zero (a : ℕ) : (qFact a).coeff 0 = 1 := by
  induction a with
  | zero => simp [qFact, Polynomial.coeff_one]
  | succ a ih =>
      rw [qFact_succ, coeff_zero_mul, ih, qInt_coeff]
      simp

private lemma qFact_coeff_one (a : ℕ) :
    (qFact a).coeff 1 = if a = 0 then 0 else ((a - 1 : ℕ) : ℤ) := by
  induction a with
  | zero => simp [qFact, Polynomial.coeff_one]
  | succ a ih =>
      rw [qFact_succ, coeff_one_mul, qFact_coeff_zero, ih,
        qInt_coeff, qInt_coeff]
      by_cases ha : a = 0
      · subst a
        simp
      · have h0 : 0 < a + 1 := by omega
        have h1 : 1 < a + 1 := by omega
        simp only [if_pos h0, if_pos h1, if_neg ha, one_mul, mul_one]
        omega

private lemma coeff_mul_next (p q : QPoly) (a : ℕ)
    (hq : ∀ i ≤ a, q.coeff i = 0) :
    (p * q).coeff (a + 2) =
      p.coeff 0 * q.coeff (a + 2) + p.coeff 1 * q.coeff (a + 1) := by
  have hdiv : X ^ (a + 1) ∣ q :=
    Polynomial.X_pow_dvd_iff.mpr (by intro d hd; exact hq d (by omega))
  obtain ⟨r, hr⟩ := hdiv
  rw [hr]
  have hfactor : p * (X ^ (a + 1) * r) =
      X ^ (a + 1) * (p * r) := by ring
  rw [hfactor]
  have h2 : a + 2 = 1 + (a + 1) := by omega
  have h1 : a + 1 = 0 + (a + 1) := by omega
  rw [h2, Polynomial.coeff_X_pow_mul, coeff_one_mul]
  have hc : (X ^ (a + 1) * r).coeff (a + 1) = r.coeff 0 := by
    simpa using Polynomial.coeff_X_pow_mul r (a + 1) 0
  simp only [Polynomial.coeff_X_pow_mul, hc]
/-- Every index below the stable range has a negative coefficient for `k ≥ 3`. -/
theorem exists_neg_coeff_of_below_threshold
    {k m : ℕ} (hk : 3 ≤ k) (hkm : k ≤ m) (hm : m ≤ 2 * k - 2) :
    ∃ d : ℕ, (S k m).coeff d < 0 := by
  let a := m - k
  have ha : a + 2 ≤ k := by dsimp [a]; omega
  by_cases he : Even k
  · refine ⟨a + 2, ?_⟩
    rw [S_eq_qFact_mul_F hkm,
      coeff_mul_next (qFact a) (F k a) a
        (by intro i hi; exact F_below_vanish k a i ha hi),
      qFact_coeff_zero, qFact_coeff_one,
      F_next_below k a ha, F_lead_below k a ha,
      he.neg_one_pow]
    simp only [one_mul, mul_one]
    by_cases h0 : a = 0
    · simp [h0]
      split_ifs <;> omega
    · simp only [if_neg h0]
      split_ifs <;> omega
  · refine ⟨a + 1, ?_⟩
    rw [S_eq_qFact_mul_F hkm,
      coeff_mul_lead (qFact a) (F k a) (a + 1)
        (qFact_coeff_zero a)
        (by intro i hi; exact F_below_vanish k a i ha (by omega)),
      F_lead_below k a ha, neg_one_pow_eq_ite]
    simp [he]

end OPAC012

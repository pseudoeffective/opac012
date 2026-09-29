import OPAC012.UniversalExpansion

open scoped BigOperators
open Polynomial Finset

namespace OPAC012

/-- The ordinary-binomial inequality underlying coefficientwise domination.
It follows by increasing `N`: both right-hand binomial coefficients gain
Pascal increments, and the increment at `N` is the larger one. -/
lemma choose_domination_bound (N D u : ℕ) (hD : 1 ≤ D)
    (hu : u + D ≤ N) :
    (u + D - 1).choose D + (N - u).choose D ≤ N.choose D := by
  have hchoose (n : ℕ) :
      (n + 1).choose D = n.choose D + n.choose (D - 1) := by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : D ≠ 0)
    simpa [Nat.add_comm] using Nat.choose_succ_succ' n d
  induction N with
  | zero => omega
  | succ N ih =>
      by_cases hb : u + D = N + 1
      · have htail : (N + 1 - u).choose D = 1 := by
          have h : N + 1 - u = D := by omega
          simp [h]
        have hhead : u + D - 1 = N := by omega
        have hpos : 1 ≤ N.choose (D - 1) :=
          Nat.choose_pos (by omega : D - 1 ≤ N)
        rw [hhead, htail, hchoose]
        omega
      · have hprev : u + D ≤ N := by omega
        have hbound := ih hprev
        have hminus : N + 1 - u = (N - u) + 1 := by omega
        have hmon : (N - u).choose (D - 1) ≤ N.choose (D - 1) :=
          Nat.choose_le_choose (D - 1) (by omega)
        rw [hminus, hchoose, hchoose N]
        omega

/-- Terms in the alternating definition of `theta`. -/
noncomputable def Ezero (N : ℕ) : QPoly := qFact N * qInt N
noncomputable def Eterm (N d : ℕ) : QPoly :=
  X ^ (N - d) * qFact (N - d) * lambda N d

lemma Eterm_coeffNonneg (N d : ℕ) : CoeffNonneg (Eterm N d) := by
  unfold Eterm
  exact coeffNonneg_mul
    (coeffNonneg_mul (coeffNonneg_X_pow _) (qFact_coeffNonneg _))
    (lambda_coeffNonneg _ _)

/-- Factor out the common q-factorial from the unsigned remainder. -/
noncomputable def Lambda (N : ℕ) : ℕ → QPoly
  | 0 => qInt N
  | D + 1 => qInt (N - D) * Lambda N D - X ^ (N - (D + 1)) * lambda N (D + 1)

lemma Lambda_factorization (N D : ℕ) (hD : D ≤ N) :
    qFact (N - D) * Lambda N D =
      Ezero N - (Finset.range D).sum (fun e => Eterm N (e + 1)) := by
  induction D with
  | zero => simp [Lambda, Ezero]
  | succ D ih =>
      have hprev : D ≤ N := by omega
      have hsub : N - D = (N - (D + 1)) + 1 := by omega
      calc
        qFact (N - (D + 1)) * Lambda N (D + 1)
            = qFact (N - (D + 1)) * qInt (N - D) * Lambda N D -
                Eterm N (D + 1) := by
                  rw [Lambda]
                  unfold Eterm
                  ring
        _ = qFact (N - D) * Lambda N D - Eterm N (D + 1) := by
              rw [hsub, qFact_succ]
        _ = Ezero N - (Finset.range D).sum (fun e => Eterm N (e + 1)) -
              Eterm N (D + 1) := by rw [ih hprev]
        _ = Ezero N - (Finset.range (D + 1)).sum (fun e => Eterm N (e + 1)) := by
              rw [Finset.sum_range_succ]
              ring

/-- The prescribed low-degree part of the normalized remainder. -/
noncomputable def P (N D : ℕ) : QPoly :=
  (Finset.range (N - D)).sum (fun r => C ((r + D).choose D : ℤ) * X ^ r)

lemma P_coeff (N D n : ℕ) :
    (P N D).coeff n = if n < N - D then ((n + D).choose D : ℤ) else 0 := by
  unfold P
  rw [Polynomial.finsetSum_coeff]
  by_cases hn : n < N - D
  · rw [Finset.sum_eq_single n]
    · simp [hn, Polynomial.coeff_X_pow]
    · intro r hr hne
      simp [Polynomial.coeff_X_pow, Ne.symm hne]
    · simp [hn]
  · simp only [ite_eq_right hn]
    apply Finset.sum_eq_zero
    intro r hr
    have hrlt : r < N - D := Finset.mem_range.mp hr
    have hnr : n ≠ r := by omega
    simp [Polynomial.coeff_X_pow, hnr]

lemma P_coeffNonneg (N D : ℕ) : CoeffNonneg (P N D) := by
  intro n
  rw [P_coeff]
  split <;> exact_mod_cast Nat.zero_le _

lemma qInt_mul_coeff (L n : ℕ) (p : QPoly) :
    (qInt (L + 1) * p).coeff n =
      (Finset.range (L + 1)).sum (fun i =>
        if i ≤ n then p.coeff (n - i) else 0) := by
  unfold qInt
  rw [Finset.sum_mul, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro i hi
  exact Polynomial.coeff_X_pow_mul' p i n

lemma Lambda_coeff_succ (N D n : ℕ) (hD : D < N) :
    (Lambda N (D + 1)).coeff n =
      (Finset.range (N - D)).sum (fun i =>
        if i ≤ n then (Lambda N D).coeff (n - i) else 0) -
      (if N - (D + 1) ≤ n then
        (lambda N (D + 1)).coeff (n - (N - (D + 1))) else 0) := by
  rw [Lambda]
  rw [Polynomial.coeff_sub]
  have h : N - D = (N - (D + 1)) + 1 := by omega
  rw [h, qInt_mul_coeff, Polynomial.coeff_X_pow_mul']

lemma Lambda_zero_eq_P (N : ℕ) : Lambda N 0 = P N 0 := by
  simp [Lambda, P, qInt]

lemma Lambda_coeff_low (N D n : ℕ) (hD : D ≤ N) (hn : n < N - D) :
    (Lambda N D).coeff n = ((n + D).choose D : ℤ) := by
  induction D generalizing n with
  | zero =>
      rw [Lambda_zero_eq_P, P_coeff]
      have hn' : n < N := by omega
      simp [hn']
  | succ D ih =>
      have hprev : D ≤ N := by omega
      have hlt : D < N := by omega
      rw [Lambda_coeff_succ N D n hlt]
      have hnot : ¬N - (D + 1) ≤ n := by omega
      simp only [ite_eq_right hnot, sub_zero]
      have hsubset : Finset.range (n + 1) ⊆ Finset.range (N - D) := by
        intro i hi
        simp only [Finset.mem_range] at hi ⊢
        omega
      have htrim :
          (Finset.range (N - D)).sum (fun i =>
            if i ≤ n then (Lambda N D).coeff (n - i) else 0) =
          (Finset.range (n + 1)).sum (fun i => (Lambda N D).coeff (n - i)) := by
        calc
          _ = (Finset.range (n + 1)).sum (fun i =>
                if i ≤ n then (Lambda N D).coeff (n - i) else 0) := by
                symm
                apply Finset.sum_subset hsubset
                intro i hi hni
                have hnoti : ¬ i ≤ n := by
                  have : ¬i < n + 1 := by simpa only [Finset.mem_range] using hni
                  omega
                simp [hnoti]
          _ = _ := by
                apply Finset.sum_congr rfl
                intro i hi
                have : i ≤ n := by
                  have := Finset.mem_range.mp hi
                  omega
                simp [this]
      rw [htrim]
      have hterms :
          (Finset.range (n + 1)).sum (fun i => (Lambda N D).coeff (n - i)) =
          (Finset.range (n + 1)).sum (fun i =>
            ((n - i + D).choose D : ℤ)) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi : i ≤ n := by
          have := Finset.mem_range.mp hi
          omega
        exact ih (n - i) hprev (by omega)
      rw [hterms]
      have hreflect :
          (Finset.range (n + 1)).sum (fun i => ((n - i + D).choose D : ℤ)) =
          (Finset.range (n + 1)).sum (fun i => ((i + D).choose D : ℤ)) := by
        rw [← Finset.sum_range_reflect]
        apply Finset.sum_congr rfl
        intro i hi
        have : i ≤ n := by
          have := Finset.mem_range.mp hi
          omega
        congr 2 <;> omega
      rw [hreflect]
      exact_mod_cast Nat.sum_range_add_choose n D

private lemma choose_tail_sum (D u L : ℕ) (hu : u ≤ L) :
    (Finset.Icc u L).sum (fun v => (v + D).choose D) +
      (u + D).choose (D + 1) = (L + D + 1).choose (D + 1) := by
  induction L with
  | zero =>
      have h : u = 0 := by omega
      subst u
      simp [Nat.add_comm]
  | succ L ih =>
      by_cases h : u ≤ L
      · rw [Finset.sum_Icc_succ_top (by omega : u ≤ L + 1)]
        calc
          (Finset.Icc u L).sum (fun v => (v + D).choose D) +
              (L + 1 + D).choose D + (u + D).choose (D + 1)
              = ((Finset.Icc u L).sum (fun v => (v + D).choose D) +
                  (u + D).choose (D + 1)) + (L + 1 + D).choose D := by omega
          _ = (L + D + 1).choose (D + 1) + (L + 1 + D).choose D := by
                rw [ih h]
          _ = (L + 1 + D + 1).choose (D + 1) := by
                have hp := Nat.choose_succ_succ' (L + D + 1) D
                have harg : L + 1 + D + 1 = (L + D + 1) + 1 := by omega
                have harg' : L + 1 + D = L + D + 1 := by omega
                rw [harg, harg']
                omega
      · have heq : u = L + 1 := by omega
        subst u
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          (Nat.choose_succ_succ' (L + D + 1) D).symm

private lemma Lambda_coeff_succ_high (N D n : ℕ) (hD : D + 1 ≤ N)
    (hprev : CoeffNonneg (Lambda N D)) (hn : N - (D + 1) ≤ n) :
    0 ≤ (Lambda N (D + 1)).coeff n := by
  let L := N - (D + 1)
  have hlt : D < N := by omega
  have hNrange : N - D = L + 1 := by omega
  have hsumNonneg :
      0 ≤ (Finset.range (N - D)).sum (fun i =>
        if i ≤ n then (Lambda N D).coeff (n - i) else 0) := by
    apply Finset.sum_nonneg
    intro i hi
    split
    · exact hprev (n - i)
    · exact le_refl 0
  rw [Lambda_coeff_succ N D n hlt]
  by_cases hfar : 2 * L < n
  · have hzero : (lambda N (D + 1)).coeff (n - L) = 0 := by
      rw [lambda_coeff N (D + 1) (n - L) hD]
      have hnot : ¬n - L ≤ N - (D + 1) := by omega
      simp [hnot]
    have hindex : N - (D + 1) = L := rfl
    rw [hindex]
    simpa [hzero] using hsumNonneg
  · let u := n - L
    have hu : u ≤ L := by omega
    have hnu : n = L + u := by omega
    have hi_le_n (i : ℕ) (hi : i ∈ Finset.Icc u L) : i ≤ n := by
      have := (Finset.mem_Icc.mp hi).2
      omega
    have hsubset : Finset.Icc u L ⊆ Finset.range (N - D) := by
      intro i hi
      have := (Finset.mem_Icc.mp hi).2
      simp only [Finset.mem_range]
      omega
    have hsmall :
        (Finset.Icc u L).sum (fun i => (Lambda N D).coeff (n - i)) ≤
          (Finset.range (N - D)).sum (fun i =>
            if i ≤ n then (Lambda N D).coeff (n - i) else 0) := by
      calc
        _ = (Finset.Icc u L).sum (fun i =>
              if i ≤ n then (Lambda N D).coeff (n - i) else 0) := by
              apply Finset.sum_congr rfl
              intro i hi
              simp [hi_le_n i hi]
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
              intro i hi hnot
              split
              · exact hprev (n - i)
              · exact le_refl 0)
    have hlow :
        (Finset.Icc u L).sum (fun i => (Lambda N D).coeff (n - i)) =
          (Finset.Icc u L).sum (fun i => ((n - i + D).choose D : ℤ)) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hilow : n - i < N - D := by
        have hi' := (Finset.mem_Icc.mp hi).1
        omega
      exact Lambda_coeff_low N D (n - i) (by omega) hilow
    have hreflect :
        (Finset.Icc u L).sum (fun i => ((n - i + D).choose D : ℤ)) =
          (Finset.Icc u L).sum (fun i => ((i + D).choose D : ℤ)) := by
      rw [← Finset.Ico_add_one_right_eq_Icc]
      have hs := Finset.sum_Ico_reflect
        (fun v => ((v + D).choose D : ℤ)) u (m := L + 1) (n := n)
        (by omega : L + 1 ≤ n + 1)
      have hleft : n + 1 - (L + 1) = u := by omega
      have hright : n + 1 - u = L + 1 := by omega
      simpa only [hleft, hright] using hs
    have hindex : u + (D + 1) - 1 = u + D := by omega
    have hN : L + D + 1 = N := by omega
    have hbound := choose_domination_bound N (D + 1) u (by omega) (by omega)
    rw [hindex] at hbound
    have htail := choose_tail_sum D u L hu
    rw [hN] at htail
    have hNat : (N - u).choose (D + 1) ≤
        (Finset.Icc u L).sum (fun v => (v + D).choose D) := by omega
    have hZ : ((N - u).choose (D + 1) : ℤ) ≤
        (Finset.Icc u L).sum (fun v => ((v + D).choose D : ℤ)) := by
      exact_mod_cast hNat
    have hcoef : (lambda N (D + 1)).coeff (n - L) =
        ((N - u).choose (D + 1) : ℤ) := by
      rw [lambda_coeff N (D + 1) (n - L) hD]
      have hnu' : n - L = u := rfl
      rw [hnu']
      have hu' : u ≤ N - (D + 1) := hu
      simp [hu']
    rw [show N - (D + 1) = L from rfl]
    simp only [ite_eq_left hn, hcoef]
    rw [hlow, hreflect] at hsmall
    omega

lemma theta_eq_E (t j : ℕ) :
    theta t j = Ezero (t - 1) +
      (Finset.range (t - 1 - j)).sum (fun e =>
        C ((-1 : ℤ) ^ (e + 2)) * Eterm (t - 1) (e + 1)) := by
  dsimp [theta, Ezero, Eterm]
  congr 1
  apply Finset.sum_congr rfl
  intro e he
  ring

/-- The remaining positivity theorem follows formally from positivity of
the normalized remainder `Lambda`. -/
lemma theta_coeffNonneg_of_Lambda
    (hLambda : ∀ N D : ℕ, D ≤ N → CoeffNonneg (Lambda N D))
    {t j : ℕ} (_ht : 1 ≤ t) (_hj : j < t) :
    CoeffNonneg (theta t j) := by
  let N := t - 1
  let D := N - j
  have hD : D ≤ N := Nat.sub_le _ _
  have hfactor : CoeffNonneg
      (Ezero N - (Finset.range D).sum (fun e => Eterm N (e + 1))) := by
    rw [← Lambda_factorization N D hD]
    exact coeffNonneg_mul (qFact_coeffNonneg _) (hLambda N D hD)
  intro degree
  have hbound :
      (Finset.range D).sum (fun e => (Eterm N (e + 1)).coeff degree) ≤
        (Ezero N).coeff degree := by
    have h := hfactor degree
    simp only [Polynomial.coeff_sub, Polynomial.finsetSum_coeff] at h
    omega
  have hsign (e : ℕ) :
      -(Eterm N (e + 1)).coeff degree ≤
        (-1 : ℤ) ^ (e + 2) * (Eterm N (e + 1)).coeff degree := by
    have hc := Eterm_coeffNonneg N (e + 1) degree
    have hs : (-1 : ℤ) ^ (e + 2) = 1 ∨ (-1 : ℤ) ^ (e + 2) = -1 := by
      by_cases he : Even (e + 2)
      · exact Or.inl (Even.neg_one_pow he)
      · exact Or.inr (Odd.neg_one_pow (Nat.not_even_iff_odd.mp he))
    rcases hs with hs | hs <;> rw [hs] <;> nlinarith
  have hsum := Finset.sum_le_sum (s := Finset.range D)
    (fun e he => hsign e)
  have heq :
      (theta t j).coeff degree = (Ezero N).coeff degree +
        (Finset.range D).sum (fun e =>
          (-1 : ℤ) ^ (e + 2) * (Eterm N (e + 1)).coeff degree) := by
    rw [theta_eq_E]
    simp only [Polynomial.coeff_add, Polynomial.finsetSum_coeff,
      Polynomial.coeff_C_mul]
    rfl
  rw [heq]
  simp only [Finset.sum_neg_distrib] at hsum
  omega

/-- Coefficientwise domination for the normalized remainder. -/
theorem Lambda_coeffNonneg (N D : ℕ) (hD : D ≤ N) :
    CoeffNonneg (Lambda N D) := by
  induction D with
  | zero => simpa [Lambda] using qInt_coeffNonneg N
  | succ D ih =>
      have hprev : D ≤ N := by omega
      intro n
      by_cases hn : n < N - (D + 1)
      · rw [Lambda_coeff_low N (D + 1) n hD hn]
        exact_mod_cast Nat.zero_le _
      · exact Lambda_coeff_succ_high N D n hD (ih hprev) (by omega)

/-- Phase C target: universal coefficients are coefficientwise nonnegative. -/
theorem theta_coeffNonneg
    {t j : ℕ} (ht : 1 ≤ t) (hj : j < t) :
    CoeffNonneg (theta t j) := by
  exact theta_coeffNonneg_of_Lambda (fun N D hD => Lambda_coeffNonneg N D hD) ht hj

end OPAC012

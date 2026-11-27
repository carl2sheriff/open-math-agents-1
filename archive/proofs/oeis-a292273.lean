import OMAStatements.S_oeis_a292273

theorem OMA.solution : type_of% @OMA.S_oeis_a292273.main := by
  intro n hn
  unfold OMA.S_oeis_a292273.a
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · have hI : Complex.I ^ (2 * k) = ((-1 : ℤ) ^ k : ℤ) := by
      rw [pow_mul, Complex.I_sq]; push_cast; rfl
    have hev : ¬ Odd (2 * k) := by simp
    rw [if_neg hev, hI]
    rw [← Int.cast_mul, Complex.intCast_re]
    by_cases h0 : ArithmeticFunction.moebius (2 * k) = 0
    · simp [h0]
    · have hsq : Squarefree (2 * k) := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp h0
      have hk : Odd k := by
        by_contra hk
        rw [Nat.not_odd_iff_even] at hk
        obtain ⟨j, rfl⟩ := hk
        have := hsq 2 ⟨j, by ring⟩
        exact absurd this (by norm_num)
      rw [hk.neg_one_pow]
      push_cast; ring
  · have hod : Odd (2 * k + 1) := ⟨k, rfl⟩
    rw [if_pos hod]
    have : Complex.I ^ (2 * k + 1) = ((-1 : ℤ) ^ k : ℤ) * Complex.I := by
      rw [pow_succ, pow_mul, Complex.I_sq]; push_cast; rfl
    rw [this]
    rw [← mul_assoc, ← Int.cast_mul, Complex.mul_re, Complex.intCast_re, Complex.intCast_im]
    simp

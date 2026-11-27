import OMAStatements.S_oeis_a274536

theorem OMA.solution : type_of% @OMA.S_oeis_a274536.main := by
  intro n hn
  unfold OMA.S_oeis_a274536.a
  have h5 : Nat.Prime 5 := by norm_num
  have hs5 : ArithmeticFunction.sigma 1 5 = 6 := by
    rw [ArithmeticFunction.sigma_one_apply, Nat.Prime.sum_divisors h5]
  constructor
  · intro h hdiv
    obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' 5 (by norm_num)
    obtain ⟨f, rfl⟩ : ∃ f, e = f + 1 := by
      rcases e with _ | f
      · simp at hdiv; exact absurd hdiv hm
      · exact ⟨f, rfl⟩
    have hc : Nat.Coprime (5 ^ (f + 1)) m := Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd h5).mpr hm)
    have hc' : Nat.Coprime (5 ^ (f + 1 + 1)) m := Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd h5).mpr hm)
    have e1 : 5 * (5 ^ (f + 1) * m) = 5 ^ (f + 1 + 1) * m := by ring
    rw [e1, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hc,
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hc'] at h
    rw [ArithmeticFunction.sigma_one_apply_prime_pow h5, ArithmeticFunction.sigma_one_apply_prime_pow h5] at h
    have hm0 : 0 < ArithmeticFunction.sigma 1 m := ArithmeticFunction.sigma_pos _ _ (by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · subst h0; simp at hn
      · exact h0.ne')
    have key : ∑ k ∈ Finset.range (f + 1 + 1 + 1), 5 ^ k = 5 * ∑ k ∈ Finset.range (f + 1 + 1), 5 ^ k + 1 := by
      rw [Finset.sum_range_succ', Finset.mul_sum]
      simp [pow_succ, mul_comm]
    rw [key] at h
    have hS : 5 ≤ ∑ k ∈ Finset.range (f + 1 + 1), 5 ^ k := by
      rw [Finset.sum_range_succ]
      have : 5 ≤ 5 ^ (f + 1) := Nat.le_self_pow (by omega) 5
      omega
    nlinarith
  · intro hnd
    have hc : Nat.Coprime 5 n := (Nat.Prime.coprime_iff_not_dvd h5).mpr hnd
    rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hc, hs5]

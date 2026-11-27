import OMAStatements.S_oeis_a071010

section Aux
lemma geo (p t : ℕ) : ∑ i ∈ Finset.range (2 * t + 2), p ^ i = (1 + p) * ∑ i ∈ Finset.range (t + 1), p ^ (2 * i) := by
  induction t with
  | zero => simp [Finset.sum_range_succ]
  | succ t ih =>
    rw [show 2 * (t + 1) + 2 = (2 * t + 2) + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ _ (t + 1)]
    ring
end Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a071010.main := by
  intro n h
  have hn : n ≠ 0 := by rintro rfl; exact h ⟨0, 0, by simp⟩
  rw [Nat.eq_sq_add_sq_iff] at h
  push_neg at h
  obtain ⟨q, hqm, hq3, hodd⟩ := h
  have hq : q.Prime := Nat.prime_of_mem_primeFactors hqm
  have hodd' : Odd (padicValNat q n) := Nat.not_even_iff_odd.mp hodd
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨m, hm, hn'⟩ : ∃ m, ¬ q ∣ m ∧ n = q ^ padicValNat q n * m := by
    obtain ⟨e, m, hm, he⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn q hq.ne_one
    refine ⟨m, hm, ?_⟩
    have : padicValNat q n = e := by
      rw [he, padicValNat.mul (pow_ne_zero _ hq.ne_zero) (by rintro rfl; simp at he; exact hn he),
        padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hm]; simp
    rw [this]; exact he
  set e := padicValNat q n
  have hc : Nat.Coprime (q ^ e) m := Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hq).mpr hm)
  rw [hn', ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hc]
  apply Dvd.dvd.mul_right
  obtain ⟨t, ht⟩ := hodd'
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hq, ht, show 2 * t + 1 + 1 = 2 * t + 2 by ring, geo]
  apply Dvd.dvd.mul_right
  have : 4 ∣ 1 + q := by omega
  exact this

import OMAStatements.S_oeis_a155559

section Aux

lemma pow3 (j : ℕ) : ∃ u : ℕ, Odd u ∧ 3 ^ (2 ^ (j + 1)) = 1 + 2 ^ (j + 3) * u := by
  induction j with
  | zero => exact ⟨1, odd_one, by norm_num⟩
  | succ j ih =>
    obtain ⟨u, hu, h⟩ := ih
    refine ⟨u + 2 ^ (j + 2) * u ^ 2, ?_, ?_⟩
    · apply Odd.add_even hu
      exact (Even.mul_right (Nat.even_pow.mpr ⟨even_two, by omega⟩) _)
    · rw [pow_succ 2 (j + 1), pow_mul, h]; ring

lemma ord3 (j : ℕ) : orderOf (3 : ZMod (2 ^ (j + 3))) = 2 ^ (j + 1) := by
  apply orderOf_eq_prime_pow (p := 2) (n := j)
  · rcases j with _ | j
    · decide
    · intro h
      obtain ⟨u, hu, hh⟩ := pow3 j
      have h2 : (((3 ^ (2 ^ (j + 1)) : ℕ)) : ZMod (2 ^ (j + 1 + 3))) = ((1 : ℕ) : ZMod (2 ^ (j + 1 + 3))) := by
        push_cast; exact h
      rw [ZMod.natCast_eq_natCast_iff] at h2
      rw [hh] at h2
      have h3 : 2 ^ (j + 1 + 3) ∣ 2 ^ (j + 3) * u := by
        have := (Nat.modEq_iff_dvd' (by omega)).mp h2.symm
        simpa using this
      rw [show j + 1 + 3 = (j + 3) + 1 by ring, pow_succ 2 (j + 3)] at h3
      have h4 : 2 ∣ u := Nat.dvd_of_mul_dvd_mul_left (by positivity) h3
      exact (Nat.not_even_iff_odd.mpr hu) (even_iff_two_dvd.mpr h4)
  · obtain ⟨u, hu, hh⟩ := pow3 j
    have h2 : (((3 ^ (2 ^ (j + 1)) : ℕ)) : ZMod (2 ^ (j + 3))) = ((1 : ℕ) : ZMod (2 ^ (j + 3))) := by
      rw [ZMod.natCast_eq_natCast_iff, hh]
      exact (Nat.modEq_iff_dvd' (by omega)).mpr (by simp) |>.symm
    push_cast at h2
    exact h2

end Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a155559.main := by
  intro n
  unfold OMA.S_oeis_a155559.a OMA.S_oeis_a155559.A131577 OMA.S_oeis_a155559.A090129
  have h3 : orderOf (3 : ZMod (2 ^ (n + 3))) = 2 ^ (n + 1) := by
    have := ord3 n; simpa using this
  rw [h3]
  rcases n with _ | n
  · have : orderOf (3 : ZMod (2 ^ (0 + 2))) = 2 := by
      have := orderOf_eq_prime_pow (p := 2) (n := 0) (x := (3 : ZMod 4)) (by decide) (by decide)
      simpa using this
    simp [this]
  · have := ord3 n
    have e : n + 1 + 2 = n + 3 := by ring
    rw [e, this]
    simp [pow_succ]
    ring_nf
    omega

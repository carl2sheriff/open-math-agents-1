import OMAStatements.S_oeis_a158960

theorem OMA_pair : ∀ n : ℕ, ∃ N M : ℤ,
    OMA.S_oeis_a158960.hermiteAtOneFifth n = (N : ℚ) / 5 ^ n ∧
    OMA.S_oeis_a158960.hermiteAtOneFifth (n + 1) = (M : ℚ) / 5 ^ (n + 1) ∧
    N % 5 ≠ 0 ∧ M % 5 ≠ 0 ∧ M % 5 = (2 * N) % 5 := by
  intro n
  induction n with
  | zero =>
    refine ⟨1, 2, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [OMA.S_oeis_a158960.hermiteAtOneFifth]
  | succ k ih =>
    obtain ⟨N, M, h1, h2, n1, m1, hm⟩ := ih
    refine ⟨M, 2 * M - 50 * (((k : ℤ) + 1) * N), h2, ?_, m1, ?_, ?_⟩
    · show OMA.S_oeis_a158960.hermiteAtOneFifth (k + 2) = _
      simp only [OMA.S_oeis_a158960.hermiteAtOneFifth]
      rw [h1, h2]
      push_cast
      field_simp
      ring
    · generalize ((k : ℤ) + 1) * N = P
      omega
    · generalize ((k : ℤ) + 1) * N = P
      omega

theorem OMA.solution : type_of% @OMA.S_oeis_a158960.main := by
  intro n
  obtain ⟨N, M, h1, _, n1, _, _⟩ := OMA_pair n
  rw [h1]
  have hcop : Nat.Coprime N.natAbs (5 ^ n) := by
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (by norm_num)]
    intro h
    apply n1
    omega
  have := Rat.den_div_eq_of_coprime (a := N) (b := ((5 ^ n : ℕ) : ℤ)) (by positivity) (by simpa using hcop)
  have h5 : (N : ℚ) / ((5 : ℚ) ^ n) = (N : ℚ) / (((5 ^ n : ℕ) : ℤ) : ℚ) := by push_cast; rfl
  rw [h5]
  exact_mod_cast this

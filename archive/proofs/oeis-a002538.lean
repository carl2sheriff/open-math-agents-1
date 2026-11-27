import OMAStatements.S_oeis_a002538

theorem OMA.solution : type_of% @OMA.S_oeis_a002538.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  simp only [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega, show m + 3 - 3 = m by omega]
  have h3 : OMA.S_oeis_a002538.a (m + 3) = (((m + 2 : ℕ) : ℤ) + 3) * OMA.S_oeis_a002538.a (m + 2) + (((m + 2 : ℕ) : ℤ) + 1) * (((m + 2 + 1).factorial : ℕ) : ℤ) := rfl
  have h2 : OMA.S_oeis_a002538.a (m + 2) = (((m + 1 : ℕ) : ℤ) + 3) * OMA.S_oeis_a002538.a (m + 1) + (((m + 1 : ℕ) : ℤ) + 1) * (((m + 1 + 1).factorial : ℕ) : ℤ) := rfl
  have h1 : OMA.S_oeis_a002538.a (m + 1) = (((m : ℕ) : ℤ) + 3) * OMA.S_oeis_a002538.a m + (((m : ℕ) : ℤ) + 1) * (((m + 1).factorial : ℕ) : ℤ) := rfl
  rw [show m + 3 = m + 2 + 1 from rfl]
  rw [h3, h2, h1, Nat.factorial_succ (m + 2), Nat.factorial_succ (m + 1)]
  push_cast
  ring

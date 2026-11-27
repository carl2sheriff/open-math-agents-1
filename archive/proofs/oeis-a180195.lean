import OMAStatements.S_oeis_a180195

section Aux
open OMA.S_oeis_a180195

lemma a_succ (n : ℕ) : a (n + 1) = b (n + 1) - a n := by
  unfold a
  rw [Finset.sum_range_succ]
  have : ((-1 : ℤ) ^ (n + 1)) * ((-1) ^ (n + 1) * b (n + 1)) = b (n + 1) := by
    rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul]; simp
  rw [mul_add, this, pow_succ]
  ring

lemma b_rel (m : ℕ) : b (m + 4) - ((m : ℤ) + 6) * b (m + 3) + ((m : ℤ) + 2) * b (m + 2) = 0 := by
  unfold b
  simp only [show m + 4 - 1 = m + 3 by omega, show m + 3 - 1 = m + 2 by omega, show m + 2 - 1 = m + 1 by omega]
  rw [Nat.factorial_succ (m + 2), Nat.factorial_succ (m + 1)]
  push_cast
  ring
end Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a180195.main := by
  open OMA.S_oeis_a180195 in
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  simp only [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega, show m + 4 - 3 = m + 1 by omega]
  have h1 : a (m + 4) = b (m + 4) - a (m + 3) := a_succ (m + 3)
  have h2 : a (m + 3) = b (m + 3) - a (m + 2) := a_succ (m + 2)
  have h3 : a (m + 2) = b (m + 2) - a (m + 1) := a_succ (m + 1)
  have hb := b_rel m
  push_cast
  linear_combination h1 - ((m : ℤ) + 6) * h2 + ((m : ℤ) + 2) * h3 + hb

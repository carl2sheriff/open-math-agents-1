import OMAStatements.S_oeis_a085781

section Aux
open OMA.S_oeis_a085781

lemma a_eq (n : ℕ) : a n = ((Nat.centralBinom (n + 1) : ℕ) : ℤ) - 2 ^ n := by
  unfold a
  have h : Nat.centralBinom (n + 1) = 2 * (2 * n + 1).choose (n + 1) := by
    rw [Nat.centralBinom_eq_two_mul_choose, show 2 * (n + 1) = (2 * n + 1) + 1 by ring, Nat.choose_succ_succ,
      show (2 * n + 1).choose n = (2 * n + 1).choose (n + 1) by
        rw [← Nat.choose_symm_of_eq_add]; ring]
    ring
  rw [h]; push_cast; ring

lemma rel (k : ℕ) : ((k : ℚ) + 1) * (Nat.centralBinom (k + 1) : ℚ) = 2 * (2 * k + 1) * (Nat.centralBinom k : ℚ) := by
  have := Nat.succ_mul_centralBinom_succ k
  exact_mod_cast this
end Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a085781.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  simp only [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega, show m + 3 - 3 = m by omega]
  simp only [a_eq]
  have r1 := rel (m + 1)
  have r2 := rel (m + 2)
  have r3 := rel (m + 3)
  have r0 := rel m
  suffices h : (((m + 3 : ℕ) : ℚ) + 1) * (((Nat.centralBinom (m + 3 + 1) : ℕ) : ℚ) - 2 ^ (m + 3)) -
      2 * (4 * ((m + 3 : ℕ) : ℚ) + 1) * (((Nat.centralBinom (m + 2 + 1) : ℕ) : ℚ) - 2 ^ (m + 2)) +
      4 * (5 * ((m + 3 : ℕ) : ℚ) - 3) * (((Nat.centralBinom (m + 1 + 1) : ℕ) : ℚ) - 2 ^ (m + 1)) +
      8 * (-2 * ((m + 3 : ℕ) : ℚ) + 3) * (((Nat.centralBinom (m + 1) : ℕ) : ℚ) - 2 ^ m) = 0 by
    exact_mod_cast h
  push_cast at r0 r1 r2 r3 ⊢
  have hm1 : (m : ℚ) + 1 ≠ 0 := by positivity
  have r2' : ((m : ℚ) + 2 + 1) * ((Nat.centralBinom (m + 2 + 1) : ℕ) : ℚ) = 2 * (2 * ((m : ℚ) + 2) + 1) * ((Nat.centralBinom (m + 1 + 1) : ℕ) : ℚ) := r2
  have r3' : ((m : ℚ) + 3 + 1) * ((Nat.centralBinom (m + 3 + 1) : ℕ) : ℚ) = 2 * (2 * ((m : ℚ) + 3) + 1) * ((Nat.centralBinom (m + 2 + 1) : ℕ) : ℚ) := r3
  have e1 : ((Nat.centralBinom (m + 1 + 1) : ℕ) : ℚ) = 2 * (2 * ((m : ℚ) + 1) + 1) / ((m : ℚ) + 1 + 1) * ((Nat.centralBinom (m + 1) : ℕ) : ℚ) := by
    field_simp; linarith
  have e2 : ((Nat.centralBinom (m + 2 + 1) : ℕ) : ℚ) = 2 * (2 * ((m : ℚ) + 2) + 1) / ((m : ℚ) + 2 + 1) * ((Nat.centralBinom (m + 1 + 1) : ℕ) : ℚ) := by
    field_simp; linarith
  have e3 : ((Nat.centralBinom (m + 3 + 1) : ℕ) : ℚ) = 2 * (2 * ((m : ℚ) + 3) + 1) / ((m : ℚ) + 3 + 1) * ((Nat.centralBinom (m + 2 + 1) : ℕ) : ℚ) := by
    field_simp; linarith
  rw [e3, e2, e1]
  field_simp
  ring

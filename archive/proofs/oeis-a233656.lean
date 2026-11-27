import OMAStatements.S_oeis_a233656

theorem OMA.solution : type_of% @OMA.S_oeis_a233656.main := by
  have per : ∀ n : ℕ, OMA.S_oeis_a233656.a (n + 20) % 10 = OMA.S_oeis_a233656.a n % 10 := by
    intro n
    induction n with
    | zero => decide
    | succ n ih =>
      show (3 * OMA.S_oeis_a233656.a (n + 20) - 2 * ((n + 20 : ℕ) : ℤ)) % 10 =
        (3 * OMA.S_oeis_a233656.a n - 2 * (n : ℤ)) % 10
      push_cast
      omega
  have perk : ∀ k r : ℕ, OMA.S_oeis_a233656.a (r + 20 * k) % 10 = OMA.S_oeis_a233656.a r % 10 := by
    intro k
    induction k with
    | zero => intro r; simp
    | succ k ih => intro r; rw [Nat.mul_succ, ← Nat.add_assoc, per, ih]
  refine ⟨?_, by decide⟩
  intro n
  have h : n = n % 20 + 20 * (n / 20) := (Nat.mod_add_div n 20).symm
  conv_lhs => rw [h]
  rw [perk]
  have hr : n % 20 < 20 := Nat.mod_lt _ (by norm_num)
  generalize n % 20 = r at hr ⊢
  interval_cases r <;> decide

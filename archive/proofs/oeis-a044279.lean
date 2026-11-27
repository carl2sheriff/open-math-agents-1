import OMAStatements.S_oeis_a044279

theorem OMA.solution : type_of% @OMA.S_oeis_a044279.main := by
  intro k hk h1 h2
  have hmod : (Nat.digits 10 k).sum % 9 = k % 9 := by
    have := Nat.modEq_digits_sum 9 10 (by norm_num) k
    exact this.symm
  rw [hmod]
  by_contra hcon
  have hd : 2 ≤ k % 9 := by omega
  apply h2
  have hk9 : k = k % 9 + 9 * (k / 9) := by omega
  have hd1 : k - 1 = (k % 9 - 1) + 9 * (k / 9) := by omega
  have hpos1 : 0 < k - 1 := by omega
  rw [hk9] at h1
  rw [hd1]
  have hne : k % 9 ≠ 0 := by omega
  have hlt : k % 9 < 9 := Nat.mod_lt _ (by norm_num)
  rw [Nat.digits_add 9 (by norm_num) _ _ hlt (Or.inl hne)] at h1
  have hlt' : k % 9 - 1 < 9 := by omega
  have hne' : k % 9 - 1 ≠ 0 := by omega
  rw [Nat.digits_add 9 (by norm_num) _ _ hlt' (Or.inl hne')]
  rw [List.infix_cons_iff] at h1 ⊢
  rcases h1 with h | h
  · exfalso
    rw [List.prefix_cons_iff] at h
    rcases h with h | ⟨t, ht, _⟩
    · simp at h
    · have := (List.cons.inj ht).1
      omega
  · exact Or.inr h

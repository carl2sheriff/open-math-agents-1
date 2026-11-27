import OMAStatements.S_oeis_a073642

section Aux

lemma sumS2 (m : ℕ) : (Nat.bitIndices (2 * m)).sum = m.bitIndices.sum + m.bitIndices.length := by
  rw [Nat.bitIndices_two_mul, List.sum_map_add]; simp

lemma sumS2' (m : ℕ) : (Nat.bitIndices (2 * m + 1)).sum = m.bitIndices.sum + m.bitIndices.length := by
  rw [Nat.bitIndices_two_mul_add_one, List.sum_cons, List.sum_map_add]; simp

lemma lenS2 (m : ℕ) : (Nat.bitIndices (2 * m)).length = m.bitIndices.length := by simp
lemma lenS2' (m : ℕ) : (Nat.bitIndices (2 * m + 1)).length = m.bitIndices.length + 1 := by simp

lemma split2 (g : ℕ → ℕ) (m : ℕ) :
    ∑ j ∈ Finset.range (2 * m), g (j + 1) = ∑ i ∈ Finset.range m, (g (2 * i + 1) + g (2 * i + 2)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    ring

lemma v_odd (i : ℕ) : padicValNat 2 (2 * i + 1) = 0 := by
  apply padicValNat.eq_zero_of_not_dvd; omega

lemma v_even (i : ℕ) : padicValNat 2 (2 * i + 2) = 1 + padicValNat 2 (i + 1) := by
  rw [show 2 * i + 2 = 2 * (i + 1) by ring, padicValNat.mul (by norm_num) (by omega)]
  simp

lemma V_eq (n : ℕ) : (∑ j ∈ Finset.range n, padicValNat 2 (j + 1)) + n.bitIndices.length = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
    · rcases Nat.eq_zero_or_pos m with h | h
      · subst h; simp
      have := ih m (by omega)
      rw [split2 (fun j => padicValNat 2 j), lenS2]
      simp only [v_odd, v_even, Finset.sum_add_distrib]
      simp
      omega
    · have := ih (2 * m) (by omega)
      rw [Finset.sum_range_succ, lenS2', v_odd]
      rw [lenS2] at this
      omega

lemma main_eq (n : ℕ) :
    2 * n.bitIndices.sum + (∑ j ∈ Finset.range n, (padicValNat 2 (j + 1)) ^ 2) + 3 * n.bitIndices.length = 3 * n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
    · rcases Nat.eq_zero_or_pos m with h | h
      · subst h; simp
      have := ih m (by omega)
      have hV := V_eq m
      rw [split2 (fun j => (padicValNat 2 j) ^ 2), lenS2, sumS2]
      simp only [v_odd, v_even, Finset.sum_add_distrib]
      have e : ∀ i, (1 + padicValNat 2 (i + 1)) ^ 2 = 1 + 2 * padicValNat 2 (i + 1) + padicValNat 2 (i + 1) ^ 2 := by
        intro i; ring
      simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum]
      simp
      omega
    · have := ih (2 * m) (by omega)
      rw [Finset.sum_range_succ, lenS2', v_odd, sumS2']
      rw [lenS2, sumS2] at this
      simp
      omega

end Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a073642.main := by
  intro n hn
  have h := main_eq n
  have hV := V_eq n
  omega

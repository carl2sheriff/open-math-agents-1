import OMAStatements.S_oeis_a226224

section Aux
open OMA.S_oeis_a226224

lemma pow_gt (r : ℕ) (hr : 7 ≤ r) : 2 * r ^ 2 < 2 ^ r := by
  induction r, hr using Nat.le_induction with
  | base => norm_num
  | succ r hr ih =>
    have e : 2 ^ (r + 1) = 2 * 2 ^ r := by ring
    rw [e]; nlinarith

lemma two_sol (k : ℕ) (hk : k ∈ solutions 2) : k ≤ 1 := by
  obtain ⟨hpos, r, rfl, hs⟩ := hk
  have hne : Nat.digits 2 (r ^ 2) ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hpos.ne'
  have hlen : 2 ^ (Nat.digits 2 (r ^ 2)).length ≤ 2 * r ^ 2 :=
    Nat.base_pow_length_digits_le 2 _ (by norm_num) (by positivity)
  have hsum : (Nat.digits 2 (r ^ 2)).sum ≤ (Nat.digits 2 (r ^ 2)).length := by
    have := List.sum_le_card_nsmul (Nat.digits 2 (r ^ 2)) 1 (by
      intro x hx
      have := Nat.digits_lt_base (by norm_num) hx
      omega)
    simpa using this
  rw [hs] at hsum
  have h2 : 2 ^ r ≤ 2 * r ^ 2 := le_trans (Nat.pow_le_pow_right (by norm_num) hsum) hlen
  have hr6 : r ≤ 6 := by
    by_contra h
    exact absurd h2 (not_le.mpr (pow_gt r (by omega)))
  interval_cases r <;> simp_all <;> contradiction
end Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a226224.main := by
  intro b hb
  constructor
  · intro h
    by_contra hne
    obtain ⟨c, rfl⟩ : ∃ c, b = c + 3 := ⟨b - 3, by omega⟩
    have hmem : (c + 2) ^ 2 ∈ OMA.S_oeis_a226224.solutions (c + 3) := by
      refine ⟨by positivity, c + 2, rfl, ?_⟩
      have e : (c + 2) ^ 2 = 1 + (c + 3) * (c + 1) := by ring
      rw [e, Nat.digits_add (c + 3) (by omega) 1 (c + 1) (by omega) (Or.inl (by omega)),
        Nat.digits_of_lt (c + 3) (c + 1) (by omega) (by omega)]
      simp; omega
    have := h.2 hmem
    nlinarith
  · rintro rfl
    exact ⟨⟨by norm_num, 1, by norm_num, by norm_num⟩, fun k hk => two_sol k hk⟩

import OMAStatements.S_oeis_a337951

theorem pw5 (e : ℕ) : 4 ^ e % 5 = if e % 2 = 0 then 1 else 4 := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [pow_succ, Nat.mul_mod, ih]
    split_ifs <;> omega

theorem OMA.solution : type_of% @OMA.S_oeis_a337951.main := by
  intro n
  have t1 : (2 * n + 1) * (2 * n + 1 - 1) / 2 = n * (2 * n + 1) := by
    apply Nat.div_eq_of_eq_mul_left (by norm_num); simp only [Nat.add_sub_cancel]; ring
  have t2 : (2 * n + 1) * (2 * n + 1 + 1) / 2 = (n + 1) * (2 * n + 1) := by
    apply Nat.div_eq_of_eq_mul_left (by norm_num); ring
  have u1 : (4 * n + 2) * (4 * n + 2 - 1) / 2 = (2 * n + 1) * (4 * n + 1) := by
    rw [show 4 * n + 2 - 1 = 4 * n + 1 by omega]
    apply Nat.div_eq_of_eq_mul_left (by norm_num); ring
  have u2 : (4 * n + 2) * (4 * n + 2 + 1) / 2 = (2 * n + 1) * (4 * n + 3) := by
    apply Nat.div_eq_of_eq_mul_left (by norm_num); ring
  have v1 : (4 * n + 4) * (4 * n + 4 - 1) / 2 = (2 * n + 2) * (4 * n + 3) := by
    rw [show 4 * n + 4 - 1 = 4 * n + 3 by omega]
    apply Nat.div_eq_of_eq_mul_left (by norm_num); ring
  have v2 : (4 * n + 4) * (4 * n + 4 + 1) / 2 = (2 * n + 2) * (4 * n + 5) := by
    apply Nat.div_eq_of_eq_mul_left (by norm_num); ring
  have p1 : (n * (2 * n + 1)) % 2 = n % 2 := by
    rw [Nat.mul_mod]; have : (2 * n + 1) % 2 = 1 := by omega
    rw [this]; simp
  have p2 : ((n + 1) * (2 * n + 1)) % 2 = (n + 1) % 2 := by
    rw [Nat.mul_mod]; have : (2 * n + 1) % 2 = 1 := by omega
    rw [this]; simp
  have p3 : ((2 * n + 1) * (4 * n + 1)) % 2 = 1 := by
    rw [Nat.mul_mod]; have : (2 * n + 1) % 2 = 1 := by omega
    have h2 : (4 * n + 1) % 2 = 1 := by omega
    rw [this, h2]
  have p4 : ((2 * n + 1) * (4 * n + 3)) % 2 = 1 := by
    rw [Nat.mul_mod]; have : (2 * n + 1) % 2 = 1 := by omega
    have h2 : (4 * n + 3) % 2 = 1 := by omega
    rw [this, h2]
  have p5 : ((2 * n + 2) * (4 * n + 3)) % 2 = 0 := by
    rw [Nat.mul_mod]; have : (2 * n + 2) % 2 = 0 := by omega
    rw [this]; simp
  have p6 : ((2 * n + 2) * (4 * n + 5)) % 2 = 0 := by
    rw [Nat.mul_mod]; have : (2 * n + 2) % 2 = 0 := by omega
    rw [this]; simp
  unfold OMA.S_oeis_a337951.a
  refine ⟨?_, ?_, ?_⟩ <;> unfold Nat.ModEq
  · rw [if_neg (by omega), t1, t2, Nat.add_mod, pw5, pw5, p1, p2]
    split_ifs <;> omega
  · rw [if_neg (by omega), u1, u2, Nat.add_mod, pw5, pw5, p3, p4]
    simp
  · rw [if_neg (by omega), v1, v2, Nat.add_mod, pw5, pw5, p5, p6]
    simp

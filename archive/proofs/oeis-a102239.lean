import OMAStatements.S_oeis_a102239

theorem OMA_h1 : ∀ n : ℕ, 4 * OMA.S_oeis_a102239.s n + 1 = 5 ^ (n + 1) := by
  intro n
  induction n with
  | zero => simp [OMA.S_oeis_a102239.s]
  | succ k ih =>
    have : OMA.S_oeis_a102239.s (k + 1) = OMA.S_oeis_a102239.s k + 5 ^ (k + 1) := by
      simp [OMA.S_oeis_a102239.s, Finset.sum_range_succ _ (k + 1)]
    rw [this, pow_succ 5 (k + 1)]
    omega

theorem OMA_h2 : ∀ n : ℕ, OMA.S_oeis_a102239.s n % 2 = (n + 1) % 2 := by
  intro n
  induction n with
  | zero => simp [OMA.S_oeis_a102239.s]
  | succ k ih =>
    have : OMA.S_oeis_a102239.s (k + 1) = OMA.S_oeis_a102239.s k + 5 ^ (k + 1) := by
      simp [OMA.S_oeis_a102239.s, Finset.sum_range_succ _ (k + 1)]
    have hp : 5 ^ (k + 1) % 2 = 1 := by
      rw [Nat.pow_mod]; simp
    omega

theorem OMA.solution : type_of% @OMA.S_oeis_a102239.main := by
  intro n
  have e0 := OMA_h1 n
  have e1 := OMA_h1 (n + 1)
  have e2 := OMA_h1 (n + 2)
  have p0 := OMA_h2 n
  have p1 := OMA_h2 (n + 1)
  have p2 := OMA_h2 (n + 2)
  simp only [OMA.S_oeis_a102239.a]
  have q1 : (5:ℕ) ^ (n + 1 + 1) = 5 * 5 ^ (n + 1) := by ring
  have q2 : (5:ℕ) ^ (n + 2 + 1) = 25 * 5 ^ (n + 1) := by ring
  rw [q1] at e1
  rw [q2] at e2
  clear q1 q2
  generalize 5 ^ (n + 1) = y at *
  generalize OMA.S_oeis_a102239.s n = x0 at *
  generalize OMA.S_oeis_a102239.s (n + 1) = x1 at *
  generalize OMA.S_oeis_a102239.s (n + 2) = x2 at *
  have r1 : x1 = 5 * x0 + 1 := by omega
  have r2 : x2 = 25 * x0 + 6 := by omega
  subst r1 r2
  rcases Nat.even_or_odd' n with ⟨m, hm | hm⟩
  · have : x0 % 2 = 1 := by omega
    omega
  · have : x0 % 2 = 0 := by omega
    omega

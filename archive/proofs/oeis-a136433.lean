import OMAStatements.S_oeis_a136433

theorem OMA_hs (k : ℕ) : OMA.S_oeis_a136433.a (k + 2) = OMA.S_oeis_a136433.a (k + 1) * (k % 3 + 1) + (k % 2 + 1) := rfl

theorem OMA_key (t : ℕ) : (OMA.S_oeis_a136433.a (t + 10) : ℤ) = 6 * OMA.S_oeis_a136433.a (t + 7) + OMA.S_oeis_a136433.a (t + 4) - 6 * OMA.S_oeis_a136433.a (t + 1) := by
  have hr : t % 6 < 6 := Nat.mod_lt _ (by norm_num)
  have : t % 6 = 0 ∨ t % 6 = 1 ∨ t % 6 = 2 ∨ t % 6 = 3 ∨ t % 6 = 4 ∨ t % 6 = 5 := by omega
  rcases this with h | h | h | h | h | h
  · have e0 := OMA_hs (t + 0)
    have m0 : (t + 0) % 3 = 0 := by omega
    have n0 : (t + 0) % 2 = 0 := by omega
    rw [m0, n0, show t + 0 + 2 = t + 2 by ring, show t + 0 + 1 = t + 1 by ring] at e0
    have e1 := OMA_hs (t + 1)
    have m1 : (t + 1) % 3 = 1 := by omega
    have n1 : (t + 1) % 2 = 1 := by omega
    rw [m1, n1, show t + 1 + 2 = t + 3 by ring, show t + 1 + 1 = t + 2 by ring] at e1
    have e2 := OMA_hs (t + 2)
    have m2 : (t + 2) % 3 = 2 := by omega
    have n2 : (t + 2) % 2 = 0 := by omega
    rw [m2, n2, show t + 2 + 2 = t + 4 by ring, show t + 2 + 1 = t + 3 by ring] at e2
    have e3 := OMA_hs (t + 3)
    have m3 : (t + 3) % 3 = 0 := by omega
    have n3 : (t + 3) % 2 = 1 := by omega
    rw [m3, n3, show t + 3 + 2 = t + 5 by ring, show t + 3 + 1 = t + 4 by ring] at e3
    have e4 := OMA_hs (t + 4)
    have m4 : (t + 4) % 3 = 1 := by omega
    have n4 : (t + 4) % 2 = 0 := by omega
    rw [m4, n4, show t + 4 + 2 = t + 6 by ring, show t + 4 + 1 = t + 5 by ring] at e4
    have e5 := OMA_hs (t + 5)
    have m5 : (t + 5) % 3 = 2 := by omega
    have n5 : (t + 5) % 2 = 1 := by omega
    rw [m5, n5, show t + 5 + 2 = t + 7 by ring, show t + 5 + 1 = t + 6 by ring] at e5
    have e6 := OMA_hs (t + 6)
    have m6 : (t + 6) % 3 = 0 := by omega
    have n6 : (t + 6) % 2 = 0 := by omega
    rw [m6, n6, show t + 6 + 2 = t + 8 by ring, show t + 6 + 1 = t + 7 by ring] at e6
    have e7 := OMA_hs (t + 7)
    have m7 : (t + 7) % 3 = 1 := by omega
    have n7 : (t + 7) % 2 = 1 := by omega
    rw [m7, n7, show t + 7 + 2 = t + 9 by ring, show t + 7 + 1 = t + 8 by ring] at e7
    have e8 := OMA_hs (t + 8)
    have m8 : (t + 8) % 3 = 2 := by omega
    have n8 : (t + 8) % 2 = 0 := by omega
    rw [m8, n8, show t + 8 + 2 = t + 10 by ring, show t + 8 + 1 = t + 9 by ring] at e8
    omega
  · have e0 := OMA_hs (t + 0)
    have m0 : (t + 0) % 3 = 1 := by omega
    have n0 : (t + 0) % 2 = 1 := by omega
    rw [m0, n0, show t + 0 + 2 = t + 2 by ring, show t + 0 + 1 = t + 1 by ring] at e0
    have e1 := OMA_hs (t + 1)
    have m1 : (t + 1) % 3 = 2 := by omega
    have n1 : (t + 1) % 2 = 0 := by omega
    rw [m1, n1, show t + 1 + 2 = t + 3 by ring, show t + 1 + 1 = t + 2 by ring] at e1
    have e2 := OMA_hs (t + 2)
    have m2 : (t + 2) % 3 = 0 := by omega
    have n2 : (t + 2) % 2 = 1 := by omega
    rw [m2, n2, show t + 2 + 2 = t + 4 by ring, show t + 2 + 1 = t + 3 by ring] at e2
    have e3 := OMA_hs (t + 3)
    have m3 : (t + 3) % 3 = 1 := by omega
    have n3 : (t + 3) % 2 = 0 := by omega
    rw [m3, n3, show t + 3 + 2 = t + 5 by ring, show t + 3 + 1 = t + 4 by ring] at e3
    have e4 := OMA_hs (t + 4)
    have m4 : (t + 4) % 3 = 2 := by omega
    have n4 : (t + 4) % 2 = 1 := by omega
    rw [m4, n4, show t + 4 + 2 = t + 6 by ring, show t + 4 + 1 = t + 5 by ring] at e4
    have e5 := OMA_hs (t + 5)
    have m5 : (t + 5) % 3 = 0 := by omega
    have n5 : (t + 5) % 2 = 0 := by omega
    rw [m5, n5, show t + 5 + 2 = t + 7 by ring, show t + 5 + 1 = t + 6 by ring] at e5
    have e6 := OMA_hs (t + 6)
    have m6 : (t + 6) % 3 = 1 := by omega
    have n6 : (t + 6) % 2 = 1 := by omega
    rw [m6, n6, show t + 6 + 2 = t + 8 by ring, show t + 6 + 1 = t + 7 by ring] at e6
    have e7 := OMA_hs (t + 7)
    have m7 : (t + 7) % 3 = 2 := by omega
    have n7 : (t + 7) % 2 = 0 := by omega
    rw [m7, n7, show t + 7 + 2 = t + 9 by ring, show t + 7 + 1 = t + 8 by ring] at e7
    have e8 := OMA_hs (t + 8)
    have m8 : (t + 8) % 3 = 0 := by omega
    have n8 : (t + 8) % 2 = 1 := by omega
    rw [m8, n8, show t + 8 + 2 = t + 10 by ring, show t + 8 + 1 = t + 9 by ring] at e8
    omega
  · have e0 := OMA_hs (t + 0)
    have m0 : (t + 0) % 3 = 2 := by omega
    have n0 : (t + 0) % 2 = 0 := by omega
    rw [m0, n0, show t + 0 + 2 = t + 2 by ring, show t + 0 + 1 = t + 1 by ring] at e0
    have e1 := OMA_hs (t + 1)
    have m1 : (t + 1) % 3 = 0 := by omega
    have n1 : (t + 1) % 2 = 1 := by omega
    rw [m1, n1, show t + 1 + 2 = t + 3 by ring, show t + 1 + 1 = t + 2 by ring] at e1
    have e2 := OMA_hs (t + 2)
    have m2 : (t + 2) % 3 = 1 := by omega
    have n2 : (t + 2) % 2 = 0 := by omega
    rw [m2, n2, show t + 2 + 2 = t + 4 by ring, show t + 2 + 1 = t + 3 by ring] at e2
    have e3 := OMA_hs (t + 3)
    have m3 : (t + 3) % 3 = 2 := by omega
    have n3 : (t + 3) % 2 = 1 := by omega
    rw [m3, n3, show t + 3 + 2 = t + 5 by ring, show t + 3 + 1 = t + 4 by ring] at e3
    have e4 := OMA_hs (t + 4)
    have m4 : (t + 4) % 3 = 0 := by omega
    have n4 : (t + 4) % 2 = 0 := by omega
    rw [m4, n4, show t + 4 + 2 = t + 6 by ring, show t + 4 + 1 = t + 5 by ring] at e4
    have e5 := OMA_hs (t + 5)
    have m5 : (t + 5) % 3 = 1 := by omega
    have n5 : (t + 5) % 2 = 1 := by omega
    rw [m5, n5, show t + 5 + 2 = t + 7 by ring, show t + 5 + 1 = t + 6 by ring] at e5
    have e6 := OMA_hs (t + 6)
    have m6 : (t + 6) % 3 = 2 := by omega
    have n6 : (t + 6) % 2 = 0 := by omega
    rw [m6, n6, show t + 6 + 2 = t + 8 by ring, show t + 6 + 1 = t + 7 by ring] at e6
    have e7 := OMA_hs (t + 7)
    have m7 : (t + 7) % 3 = 0 := by omega
    have n7 : (t + 7) % 2 = 1 := by omega
    rw [m7, n7, show t + 7 + 2 = t + 9 by ring, show t + 7 + 1 = t + 8 by ring] at e7
    have e8 := OMA_hs (t + 8)
    have m8 : (t + 8) % 3 = 1 := by omega
    have n8 : (t + 8) % 2 = 0 := by omega
    rw [m8, n8, show t + 8 + 2 = t + 10 by ring, show t + 8 + 1 = t + 9 by ring] at e8
    omega
  · have e0 := OMA_hs (t + 0)
    have m0 : (t + 0) % 3 = 0 := by omega
    have n0 : (t + 0) % 2 = 1 := by omega
    rw [m0, n0, show t + 0 + 2 = t + 2 by ring, show t + 0 + 1 = t + 1 by ring] at e0
    have e1 := OMA_hs (t + 1)
    have m1 : (t + 1) % 3 = 1 := by omega
    have n1 : (t + 1) % 2 = 0 := by omega
    rw [m1, n1, show t + 1 + 2 = t + 3 by ring, show t + 1 + 1 = t + 2 by ring] at e1
    have e2 := OMA_hs (t + 2)
    have m2 : (t + 2) % 3 = 2 := by omega
    have n2 : (t + 2) % 2 = 1 := by omega
    rw [m2, n2, show t + 2 + 2 = t + 4 by ring, show t + 2 + 1 = t + 3 by ring] at e2
    have e3 := OMA_hs (t + 3)
    have m3 : (t + 3) % 3 = 0 := by omega
    have n3 : (t + 3) % 2 = 0 := by omega
    rw [m3, n3, show t + 3 + 2 = t + 5 by ring, show t + 3 + 1 = t + 4 by ring] at e3
    have e4 := OMA_hs (t + 4)
    have m4 : (t + 4) % 3 = 1 := by omega
    have n4 : (t + 4) % 2 = 1 := by omega
    rw [m4, n4, show t + 4 + 2 = t + 6 by ring, show t + 4 + 1 = t + 5 by ring] at e4
    have e5 := OMA_hs (t + 5)
    have m5 : (t + 5) % 3 = 2 := by omega
    have n5 : (t + 5) % 2 = 0 := by omega
    rw [m5, n5, show t + 5 + 2 = t + 7 by ring, show t + 5 + 1 = t + 6 by ring] at e5
    have e6 := OMA_hs (t + 6)
    have m6 : (t + 6) % 3 = 0 := by omega
    have n6 : (t + 6) % 2 = 1 := by omega
    rw [m6, n6, show t + 6 + 2 = t + 8 by ring, show t + 6 + 1 = t + 7 by ring] at e6
    have e7 := OMA_hs (t + 7)
    have m7 : (t + 7) % 3 = 1 := by omega
    have n7 : (t + 7) % 2 = 0 := by omega
    rw [m7, n7, show t + 7 + 2 = t + 9 by ring, show t + 7 + 1 = t + 8 by ring] at e7
    have e8 := OMA_hs (t + 8)
    have m8 : (t + 8) % 3 = 2 := by omega
    have n8 : (t + 8) % 2 = 1 := by omega
    rw [m8, n8, show t + 8 + 2 = t + 10 by ring, show t + 8 + 1 = t + 9 by ring] at e8
    omega
  · have e0 := OMA_hs (t + 0)
    have m0 : (t + 0) % 3 = 1 := by omega
    have n0 : (t + 0) % 2 = 0 := by omega
    rw [m0, n0, show t + 0 + 2 = t + 2 by ring, show t + 0 + 1 = t + 1 by ring] at e0
    have e1 := OMA_hs (t + 1)
    have m1 : (t + 1) % 3 = 2 := by omega
    have n1 : (t + 1) % 2 = 1 := by omega
    rw [m1, n1, show t + 1 + 2 = t + 3 by ring, show t + 1 + 1 = t + 2 by ring] at e1
    have e2 := OMA_hs (t + 2)
    have m2 : (t + 2) % 3 = 0 := by omega
    have n2 : (t + 2) % 2 = 0 := by omega
    rw [m2, n2, show t + 2 + 2 = t + 4 by ring, show t + 2 + 1 = t + 3 by ring] at e2
    have e3 := OMA_hs (t + 3)
    have m3 : (t + 3) % 3 = 1 := by omega
    have n3 : (t + 3) % 2 = 1 := by omega
    rw [m3, n3, show t + 3 + 2 = t + 5 by ring, show t + 3 + 1 = t + 4 by ring] at e3
    have e4 := OMA_hs (t + 4)
    have m4 : (t + 4) % 3 = 2 := by omega
    have n4 : (t + 4) % 2 = 0 := by omega
    rw [m4, n4, show t + 4 + 2 = t + 6 by ring, show t + 4 + 1 = t + 5 by ring] at e4
    have e5 := OMA_hs (t + 5)
    have m5 : (t + 5) % 3 = 0 := by omega
    have n5 : (t + 5) % 2 = 1 := by omega
    rw [m5, n5, show t + 5 + 2 = t + 7 by ring, show t + 5 + 1 = t + 6 by ring] at e5
    have e6 := OMA_hs (t + 6)
    have m6 : (t + 6) % 3 = 1 := by omega
    have n6 : (t + 6) % 2 = 0 := by omega
    rw [m6, n6, show t + 6 + 2 = t + 8 by ring, show t + 6 + 1 = t + 7 by ring] at e6
    have e7 := OMA_hs (t + 7)
    have m7 : (t + 7) % 3 = 2 := by omega
    have n7 : (t + 7) % 2 = 1 := by omega
    rw [m7, n7, show t + 7 + 2 = t + 9 by ring, show t + 7 + 1 = t + 8 by ring] at e7
    have e8 := OMA_hs (t + 8)
    have m8 : (t + 8) % 3 = 0 := by omega
    have n8 : (t + 8) % 2 = 0 := by omega
    rw [m8, n8, show t + 8 + 2 = t + 10 by ring, show t + 8 + 1 = t + 9 by ring] at e8
    omega
  · have e0 := OMA_hs (t + 0)
    have m0 : (t + 0) % 3 = 2 := by omega
    have n0 : (t + 0) % 2 = 1 := by omega
    rw [m0, n0, show t + 0 + 2 = t + 2 by ring, show t + 0 + 1 = t + 1 by ring] at e0
    have e1 := OMA_hs (t + 1)
    have m1 : (t + 1) % 3 = 0 := by omega
    have n1 : (t + 1) % 2 = 0 := by omega
    rw [m1, n1, show t + 1 + 2 = t + 3 by ring, show t + 1 + 1 = t + 2 by ring] at e1
    have e2 := OMA_hs (t + 2)
    have m2 : (t + 2) % 3 = 1 := by omega
    have n2 : (t + 2) % 2 = 1 := by omega
    rw [m2, n2, show t + 2 + 2 = t + 4 by ring, show t + 2 + 1 = t + 3 by ring] at e2
    have e3 := OMA_hs (t + 3)
    have m3 : (t + 3) % 3 = 2 := by omega
    have n3 : (t + 3) % 2 = 0 := by omega
    rw [m3, n3, show t + 3 + 2 = t + 5 by ring, show t + 3 + 1 = t + 4 by ring] at e3
    have e4 := OMA_hs (t + 4)
    have m4 : (t + 4) % 3 = 0 := by omega
    have n4 : (t + 4) % 2 = 1 := by omega
    rw [m4, n4, show t + 4 + 2 = t + 6 by ring, show t + 4 + 1 = t + 5 by ring] at e4
    have e5 := OMA_hs (t + 5)
    have m5 : (t + 5) % 3 = 1 := by omega
    have n5 : (t + 5) % 2 = 0 := by omega
    rw [m5, n5, show t + 5 + 2 = t + 7 by ring, show t + 5 + 1 = t + 6 by ring] at e5
    have e6 := OMA_hs (t + 6)
    have m6 : (t + 6) % 3 = 2 := by omega
    have n6 : (t + 6) % 2 = 1 := by omega
    rw [m6, n6, show t + 6 + 2 = t + 8 by ring, show t + 6 + 1 = t + 7 by ring] at e6
    have e7 := OMA_hs (t + 7)
    have m7 : (t + 7) % 3 = 0 := by omega
    have n7 : (t + 7) % 2 = 0 := by omega
    rw [m7, n7, show t + 7 + 2 = t + 9 by ring, show t + 7 + 1 = t + 8 by ring] at e7
    have e8 := OMA_hs (t + 8)
    have m8 : (t + 8) % 3 = 1 := by omega
    have n8 : (t + 8) % 2 = 1 := by omega
    rw [m8, n8, show t + 8 + 2 = t + 10 by ring, show t + 8 + 1 = t + 9 by ring] at e8
    omega

theorem OMA.solution : type_of% @OMA.S_oeis_a136433.main := by
  intro n hn
  obtain ⟨t, rfl⟩ : ∃ t, n = t + 10 := ⟨n - 10, by omega⟩
  have := OMA_key t
  rw [show t + 10 - 3 = t + 7 by omega, show t + 10 - 6 = t + 4 by omega, show t + 10 - 9 = t + 1 by omega]
  exact this

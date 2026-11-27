import OMAStatements.S_oeis_a306362

theorem bform (n : ℕ) : OMA.S_oeis_a306362.b n =
    if n % 2 = 0 then 1 + (n : ℤ) + 2 * (n : ℤ) ^ 2 else (n : ℤ) + 2 * (n : ℤ) ^ 2 := by
  unfold OMA.S_oeis_a306362.b
  split_ifs with h
  · have : (-1 : ℤ) ^ n = 1 := Even.neg_one_pow (Nat.even_iff.2 h)
    rw [this]; omega
  · have : (-1 : ℤ) ^ n = -1 := Odd.neg_one_pow (Nat.odd_iff.2 (by omega))
    rw [this]; omega

theorem OMA.solution : type_of% @OMA.S_oeis_a306362.main := by
  intro n hp h3 h10
  have hnn : 0 ≤ OMA.S_oeis_a306362.b n := by
    rw [bform]; split_ifs <;> positivity
  have hev : n % 2 = 0 := by
    by_contra hodd
    have hb : OMA.S_oeis_a306362.b n = (n : ℤ) * (2 * (n : ℤ) + 1) := by
      rw [bform, if_neg hodd]; ring
    have hi := hp.irreducible
    rw [hb] at hi
    rcases hi.isUnit_or_isUnit rfl with hu | hu
    · rw [Int.isUnit_iff] at hu
      apply h3; rw [hb]
      rcases hu with h | h
      · rw [h]; norm_num
      · omega
    · rw [Int.isUnit_iff] at hu
      omega
  have hdiv : (3 : ℤ) ∣ OMA.S_oeis_a306362.b n := by
    rw [bform, if_pos hev] at h10 ⊢
    obtain ⟨q, r, hq, hrr⟩ : ∃ q r : ℕ, n = r + 30 * q ∧ r < 30 :=
      ⟨n / 30, n % 30, by omega, Nat.mod_lt _ (by norm_num)⟩
    have hre : r % 2 = 0 := by omega
    subst hq
    push_cast at h10 ⊢
    have e : ((r : ℤ) + 30 * (q : ℤ)) ^ 2 = (r : ℤ) ^ 2 + 30 * (2 * (r : ℤ) * q + 30 * (q : ℤ) ^ 2) := by ring
    rw [e] at h10 ⊢
    generalize (2 * (r : ℤ) * q + 30 * (q : ℤ) ^ 2) = W at h10 ⊢
    generalize (q : ℤ) = Q at h10 ⊢
    interval_cases r <;> omega
  have := Int.prime_iff_natAbs_prime.1 hp
  have h3' : 3 ∣ (OMA.S_oeis_a306362.b n).natAbs := by
    have := Int.natAbs_dvd_natAbs.2 hdiv
    simpa using this
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three this).1 h3'
  omega

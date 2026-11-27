import OMAStatements.S_oeis_a204988

theorem OMA_C (e m j d : ℕ) (hm : Odd m) (hd : 1 ≤ d) :
    2 ^ e * m ∣ 2 ^ (j + d) - 2 ^ j ↔ e ≤ j ∧ m ∣ 2 ^ d - 1 := by
  have hsub : 2 ^ (j + d) - 2 ^ j = 2 ^ j * (2 ^ d - 1) := by
    rw [Nat.mul_sub, pow_add, mul_one]
  have hodd : Odd (2 ^ d - 1) := by
    have h2 : 2 ∣ 2 ^ d := dvd_pow_self 2 (by omega)
    have h1 : 1 ≤ 2 ^ d := Nat.one_le_pow _ _ (by norm_num)
    rcases h2 with ⟨c, hc⟩
    exact ⟨c - 1, by omega⟩
  rw [hsub]
  constructor
  · intro h
    have h1 : 2 ^ e ∣ 2 ^ j * (2 ^ d - 1) := dvd_trans (dvd_mul_right _ _) h
    have h2 : m ∣ 2 ^ j * (2 ^ d - 1) := dvd_trans (dvd_mul_left _ _) h
    have c1 : Nat.Coprime (2 ^ e) (2 ^ d - 1) :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)
    have c2 : Nat.Coprime m (2 ^ j) :=
      Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hm)
    refine ⟨?_, c2.dvd_of_dvd_mul_left h2⟩
    have := c1.dvd_of_dvd_mul_right h1
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp this
  · rintro ⟨h1, h2⟩
    exact mul_dvd_mul (pow_dvd_pow 2 h1) h2

theorem OMA.solution : type_of% @OMA.S_oeis_a204988.main := by
  intro n hn
  obtain ⟨e, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd (n := n) (by omega)
  have hv : padicValNat 2 n = e := by
    rw [hnm, padicValNat.mul (by positivity) (by rintro rfl; simp at hm), padicValNat.prime_pow]
    have : padicValNat 2 m = 0 := padicValNat.eq_zero_of_not_dvd (by
      intro h; exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h))
    omega
  have hmpos : 0 < m := hm.pos
  -- existence of a period
  have hex : ∃ d, 1 ≤ d ∧ m ∣ 2 ^ d - 1 := by
    refine ⟨Nat.totient m, Nat.totient_pos.mpr hmpos, ?_⟩
    have hc : Nat.Coprime 2 m := Nat.coprime_two_left.mpr hm
    have := Nat.ModEq.pow_totient hc
    have h1 : 1 ≤ 2 ^ Nat.totient m := Nat.one_le_pow _ _ (by norm_num)
    exact (Nat.modEq_iff_dvd' h1).mp this.symm
  set D := sInf {d : ℕ | 1 ≤ d ∧ m ∣ 2 ^ d - 1} with hD
  have hDmem : 1 ≤ D ∧ m ∣ 2 ^ D - 1 := Nat.sInf_mem hex
  have hDle : ∀ d, 1 ≤ d → m ∣ 2 ^ d - 1 → D ≤ d := fun d h1 h2 => Nat.sInf_le ⟨h1, h2⟩
  set E := max 1 e with hE
  have hEe : e ≤ E := le_max_right _ _
  have hE1 : 1 ≤ E := le_max_left _ _
  -- characterisation
  have char : ∀ j k, 1 ≤ j → j < k →
      (n ∣ 2 ^ k - 2 ^ j ↔ e ≤ j ∧ m ∣ 2 ^ (k - j) - 1) := by
    intro j k hj hjk
    obtain ⟨d, rfl⟩ : ∃ d, k = j + d := ⟨k - j, by omega⟩
    have := OMA_C e m j d hm (by omega)
    rw [hnm]
    simpa using this
  have hkmin : OMA.S_oeis_a204988.kmin n = E + D := by
    unfold OMA.S_oeis_a204988.kmin
    apply le_antisymm
    · apply Nat.sInf_le
      refine ⟨E, hE1, by omega, ?_⟩
      rw [char E (E + D) hE1 (by omega)]
      exact ⟨hEe, by simpa using hDmem.2⟩
    · apply le_csInf
      · exact ⟨E + D, E, hE1, by omega, (char E (E + D) hE1 (by omega)).mpr ⟨hEe, by simpa using hDmem.2⟩⟩
      · rintro k ⟨j, hj, hjk, hdiv⟩
        obtain ⟨h1, h2⟩ := (char j k hj hjk).mp hdiv
        have := hDle (k - j) (by omega) h2
        omega
  have ha : OMA.S_oeis_a204988.a n = E := by
    unfold OMA.S_oeis_a204988.a
    rw [hkmin]
    have hmem : E ∈ {j : ℕ | 1 ≤ j ∧ j < E + D ∧ n ∣ 2 ^ (E + D) - 2 ^ j} :=
      ⟨hE1, by omega, (char E (E + D) hE1 (by omega)).mpr ⟨hEe, by simpa using hDmem.2⟩⟩
    apply le_antisymm
    · exact Nat.sInf_le hmem
    · apply le_csInf ⟨E, hmem⟩
      rintro j ⟨hj, hjk, hdiv⟩
      have := ((char j (E + D) hj hjk).mp hdiv).1
      omega
  rw [ha, hv]
  rcases Nat.eq_zero_or_pos e with h0 | hpos
  · subst h0
    have : n % 2 = 1 := by
      rw [hnm]; simpa [Nat.odd_iff] using hm
    simp [hE, this]
  · have : n % 2 = 0 := by
      rw [hnm]
      obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
      rw [pow_succ]
      simp [Nat.mul_mod, mul_assoc]
    simp [hE, this]
    omega

import OMAStatements.S_oeis_a073759

theorem OMA.solution : type_of% @OMA.S_oeis_a073759.main := by
  intro n hn
  unfold OMA.S_oeis_a073759.a OMA.S_oeis_a073759.halfGap
  have hn1 : n ≠ 1 := by omega
  have hp : (Nat.minFac n).Prime := Nat.minFac_prime hn1
  have hpd : Nat.minFac n ∣ n := Nat.minFac_dvd n
  by_cases hpr : n.Prime
  · have hmf : Nat.minFac n = n := hpr.minFac_eq
    rw [hmf]
    have : (Finset.Ico 1 n).filter (fun m => ¬ m ∣ n ∧ ¬ m.Coprime n) = ∅ := by
      apply Finset.filter_eq_empty_iff.2
      intro m hm ⟨_, hc⟩
      apply hc
      have hm' := Finset.mem_Ico.1 hm
      exact (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hpr).2 (fun h => by have := Nat.le_of_dvd (by omega) h; omega)))
    rw [this]; simp
  · have hlt : Nat.minFac n < n := by
      have := Nat.minFac_le (show 0 < n by omega)
      rcases this.lt_or_eq with h | h
      · exact h
      · exact absurd (h ▸ hp) hpr
    have hsup : ((Finset.Ico 1 n).filter (fun m => ¬ m ∣ n ∧ ¬ m.Coprime n)).sup id = n - Nat.minFac n := by
      apply le_antisymm
      · apply Finset.sup_le
        intro m hm
        rw [Finset.mem_filter, Finset.mem_Ico] at hm
        obtain ⟨⟨h1, h2⟩, _, hc⟩ := hm
        by_contra hgt
        simp only [id] at hgt
        apply hc
        rw [Nat.coprime_comm]
        by_contra hnc
        have hg : Nat.gcd n m ≠ 1 := hnc
        have hq := Nat.minFac_prime hg
        have hq1 : (Nat.gcd n m).minFac ∣ n := (Nat.minFac_dvd _).trans (Nat.gcd_dvd_left _ _)
        have hq2 : (Nat.gcd n m).minFac ∣ m := (Nat.minFac_dvd _).trans (Nat.gcd_dvd_right _ _)
        have hq3 : (Nat.gcd n m).minFac ∣ n - m := Nat.dvd_sub hq1 hq2
        have := Nat.minFac_le_of_dvd hq.two_le hq1
        have := Nat.le_of_dvd (by omega) hq3
        omega
      · have hp2 := hp.two_le
        apply Finset.le_sup (f := id)
        rw [Finset.mem_filter, Finset.mem_Ico]
        refine ⟨⟨?_, by omega⟩, ?_, ?_⟩
        · omega
        · intro hd
          have h1 : n - Nat.minFac n ∣ Nat.minFac n := by
            have := Nat.dvd_sub hd (dvd_refl _)
            have e : n - (n - Nat.minFac n) = Nat.minFac n := by omega
            rwa [e] at this
          have := Nat.le_of_dvd hp.pos h1
          have hq := hp.two_le
          rcases Nat.even_or_odd n with he | ho
          · have : Nat.minFac n = 2 := (Nat.minFac_eq_two_iff n).2 (even_iff_two_dvd.1 he)
            omega
          · have : Odd (Nat.minFac n) := Odd.of_dvd_nat ho hpd
            have h3 : Nat.minFac n ≠ 2 := by rintro h; rw [h] at this; exact absurd this (by decide)
            obtain ⟨c, hc⟩ := hpd
            rcases c with _ | _ | _ | c
            · omega
            · exact hpr (by rw [hc]; simpa using hp)
            · obtain ⟨r, hr⟩ := ho; omega
            · have hle : n ≤ 2 * n.minFac := by omega
              nlinarith [hq]
        · intro hc
          have : Nat.minFac n ∣ Nat.gcd (n - Nat.minFac n) n := by
            apply Nat.dvd_gcd _ hpd
            exact Nat.dvd_sub hpd (dvd_refl _)
          rw [hc] at this
          have := Nat.le_of_dvd one_pos this
          have := hp.two_le
          omega
    rw [hsup]
    have hpar : (n - Nat.minFac n) % 2 = 0 := by
      rcases Nat.even_or_odd n with he | ho
      · have : Nat.minFac n = 2 := (Nat.minFac_eq_two_iff n).2 (even_iff_two_dvd.1 he)
        rw [this]; obtain ⟨r, hr⟩ := he; omega
      · have : Odd (Nat.minFac n) := Odd.of_dvd_nat ho hpd
        obtain ⟨r, hr⟩ := ho
        obtain ⟨s, hs⟩ := this
        omega
    omega

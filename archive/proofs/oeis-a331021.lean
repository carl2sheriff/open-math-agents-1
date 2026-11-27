import OMAStatements.S_oeis_a331021
import Mathlib

section Aux

lemma key (p k : ℕ) (hp : p.Prime) (hk : 0 < k) (hpk : p ∣ k) (h : p ^ 2 ∣ 2 ^ (k - 1) - 1) :
    p ^ 2 ∣ 2 ^ (p - 1) - 1 := by
  have hp2 := hp.two_le
  have hk1 : 1 ≤ k - 1 := by
    have : p ≤ k := Nat.le_of_dvd hk hpk
    omega
  have hpos : 1 ≤ 2 ^ (k - 1) := Nat.one_le_two_pow
  have hpos' : 1 ≤ 2 ^ (p - 1) := Nat.one_le_two_pow
  have e1 : (2 : ZMod (p ^ 2)) ^ (k - 1) = 1 := by
    have := (ZMod.natCast_eq_zero_iff _ _).mpr h
    rw [Nat.cast_sub hpos] at this
    push_cast at this
    exact sub_eq_zero.mp this
  have e2 : (2 : ZMod (p ^ 2)) ^ (p * (p - 1)) = 1 := by
    rcases eq_or_ne p 2 with rfl | hne
    · exfalso
      have h2 : 2 ∣ 2 ^ (k - 1) := dvd_pow_self 2 (by omega)
      have h4 : 2 ∣ 2 ^ (k - 1) - 1 := (Nat.dvd_trans (dvd_pow_self 2 (by norm_num)) h)
      omega
    · have hcop : Nat.Coprime 2 (p ^ 2) := by
        apply Nat.Coprime.pow_right
        exact (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hne)
      have := Nat.ModEq.pow_totient hcop
      rw [Nat.totient_prime_pow hp (by norm_num)] at this
      have h3 := (ZMod.natCast_eq_natCast_iff _ _ _).mpr this
      push_cast at h3
      simpa [pow_succ, mul_comm] using h3
  have hcopk : Nat.Coprime (k - 1) p := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
    intro hd
    have : p ∣ k - (k - 1) := Nat.dvd_sub hpk hd
    have : k - (k - 1) = 1 := by omega
    simp_all [hp.one_lt.ne']
  have hg : Nat.gcd (k - 1) (p * (p - 1)) ∣ p - 1 := by
    have h1 : Nat.Coprime (Nat.gcd (k - 1) (p * (p - 1))) p :=
      Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left _ _) hcopk
    exact h1.dvd_of_dvd_mul_left (Nat.gcd_dvd_right _ _)
  have e3 := pow_gcd_eq_one.mpr ⟨e1, e2⟩
  obtain ⟨c, hc⟩ := hg
  have e4 : (2 : ZMod (p ^ 2)) ^ (p - 1) = 1 := by rw [hc, pow_mul, e3, one_pow]
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hpos']
  push_cast
  rw [e4]; simp
end Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a331021.main := by
  intro k hk hg
  by_contra hne
  push_neg at hne
  set g := Nat.gcd (k ^ 2) (2 ^ (k - 1) - 1) with hgdef
  have hgk : g ∣ k := by
    have hk0 : k ≠ 0 := hk.ne'
    have hg0 : g ≠ 0 := by
      intro h0; rw [hgdef, Nat.gcd_eq_zero_iff] at h0; exact hk0 (by simpa using h0.1)
    rw [← Nat.factorization_le_iff_dvd hg0 hk0]
    intro p
    by_contra hlt
    push_neg at hlt
    have hpg : p ∈ g.primeFactors := by
      rw [← Nat.support_factorization, Finsupp.mem_support_iff]; omega
    have hp := Nat.prime_of_mem_primeFactors hpg
    have hdk2 : g ∣ k ^ 2 := Nat.gcd_dvd_left _ _
    have hpk : p ∣ k := by
      have : p ∣ k ^ 2 := (Nat.dvd_of_mem_primeFactors hpg).trans hdk2
      exact hp.dvd_of_dvd_pow this
    have hv : 1 ≤ k.factorization p := (hp.dvd_iff_one_le_factorization hk0).mp hpk
    have hp2 : p ^ 2 ∣ g := by
      have := (Nat.Prime.pow_dvd_iff_le_factorization hp hg0).mpr (show 2 ≤ g.factorization p by omega)
      exact this
    exact hne p hp hpk (key p k hp hk hpk (hp2.trans (Nat.gcd_dvd_right _ _)))
  have := Nat.le_of_dvd hk hgk
  omega

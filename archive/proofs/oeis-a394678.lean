import OMAStatements.S_oeis_a394678

open scoped Nat

section Aux
open OMA.S_oeis_a394678

lemma two_div (a b m : ℕ) (ha : 0 < a) (hab : a < b) (hbm : b ≤ m) : a * b ∣ m ! := by
  have h1 : a ∣ (b - 1)! := Nat.dvd_factorial ha (by omega)
  have h2 : a * b ∣ b ! := by
    have : b ! = b * (b - 1)! := by
      conv_lhs => rw [show b = (b - 1) + 1 by omega]
      rw [Nat.factorial_succ]; congr 1 <;> omega
    rw [this, mul_comm a b]
    exact Nat.mul_dvd_mul_left b h1
  exact h2.trans (Nat.factorial_dvd_factorial hbm)

lemma comp_dvd (n : ℕ) (hn : ¬ n.Prime) (h2 : 2 ≤ n) (h4 : n ≠ 4) : n ∣ (n - 1)! := by
  obtain ⟨a, hda, ha2, han⟩ := Nat.exists_dvd_of_not_prime2 h2 hn
  obtain ⟨b, rfl⟩ := hda
  have hb : 2 ≤ b := by
    rcases Nat.lt_or_ge b 2 with h | h
    · interval_cases b <;> omega
    · exact h
  rcases lt_trichotomy a b with h | h | h
  · exact two_div a b (a * b - 1) (by omega) h (by have := Nat.mul_le_mul_right b ha2; omega)
  · subst h
    have ha3 : 3 ≤ a := by
      by_contra hc
      have : a = 2 := by omega
      subst this; exact h4 rfl
    have := two_div a (2 * a) (a * a - 1) (by omega) (by omega) (by have := Nat.mul_le_mul_right a ha3; omega)
    exact (Dvd.intro (2) (by ring)).trans this
  · have := two_div b a (a * b - 1) (by omega) h (by have := Nat.mul_le_mul_left a hb; omega)
    rwa [mul_comm b a] at this
end Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a394678.main := by
  open OMA.S_oeis_a394678 in
  intro n hn h4 hp
  by_cases hnp : n.Prime
  · refine ⟨hnp, ?_⟩
    haveI : Fact n.Prime := ⟨hnp⟩
    have hw : ((n - 1)! : ZMod n) = -1 := by have := ZMod.wilsons_lemma (p := n); exact this
    have hd : n ∣ (n - 1)! + 1 := by
      rw [← ZMod.natCast_eq_zero_iff]; push_cast; rw [hw]; ring
    obtain ⟨t, ht⟩ := hd
    have h2 := hnp.two_le
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := by
      rcases t with _ | s
      · simp at ht
      · exact ⟨s, rfl⟩
    have hf : n ! = n * (n - 1)! := (Nat.mul_factorial_pred (by omega)).symm
    have hN : n + 1 ≤ n ^ 2 := by nlinarith
    have key : Nat.factorial n - 1 = (n ^ 2 - n - 1) + n ^ 2 * s := by
      have e : (n - 1)! = n * s + n - 1 := by
        have : n * (s + 1) = n * s + n := by ring
        omega
      have h1 : n * (n - 1)! + n = n ^ 2 * s + n ^ 2 := by
        have := congrArg (fun x => n * x) ht
        nlinarith [this]
      rw [hf]
      generalize n * (n - 1)! = X at *
      generalize n ^ 2 * s = Y at *
      generalize n ^ 2 = N at *
      omega
    have : a n = n ^ 2 - n - 1 := by
      unfold a
      rw [key, Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt (by omega)
    rw [this] at hp; exact hp
  · exfalso
    have h2 : 2 ≤ n := by
      by_contra hc
      have : n = 1 := by omega
      subst this; simp [a] at hp; exact Nat.not_prime_zero hp
    have hd := comp_dvd n hnp h2 h4
    obtain ⟨k, hk⟩ := hd
    have hf : n ! = n * (n - 1)! := (Nat.mul_factorial_pred (by omega)).symm
    have hk1 : 1 ≤ (n - 1)! := Nat.factorial_pos _
    have hkk : 1 ≤ k := by
      rcases k with _ | k
      · simp at hk; omega
      · omega
    have e : Nat.factorial n - 1 = (n ^ 2 - 1) + n ^ 2 * (k - 1) := by
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have h1 : n * (n * (j + 1)) = n ^ 2 * j + n ^ 2 := by ring
      rw [Nat.add_sub_cancel, hf, hk, h1]
      have : 2 ≤ n ^ 2 := by nlinarith
      generalize n ^ 2 * j = Y at *
      generalize n ^ 2 = N at *
      omega
    have : a n = n ^ 2 - 1 := by
      unfold a
      rw [e, Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt (by have : 2 ≤ n ^ 2 := by nlinarith
                                 omega)
    rw [this] at hp
    have h6 : 3 ≤ n := by
      by_contra hc
      have : n = 2 := by omega
      subst this; exact hnp Nat.prime_two
    have h5 : n ^ 2 - 1 = (n - 1) * (n + 1) := by
      zify [show 1 ≤ n ^ 2 by nlinarith, show 1 ≤ n by omega]; ring
    rw [h5] at hp
    have := Nat.not_prime_mul (a := n - 1) (b := n + 1) (by omega) (by omega)
    exact this hp

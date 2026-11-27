import OMAStatements.S_oeis_a071282

section
open OMA.S_oeis_a071282

theorem exp_per (n : ℕ) (hn : 0 < n) (old : ℕ → Symbol) (p m : ℕ)
    (hp : ∀ i, old (i + p) = old i) (hm : p ∣ m * n) (he : 2 ∣ m * n) (i : ℕ) :
    expandStream n old (i + (n + 2) * m) = expandStream n old i := by
  have hk : ∀ k i, old (i + p * k) = old i := by
    intro k
    induction k with
    | zero => intro i; simp
    | succ k ih => intro i; rw [Nat.mul_succ, ← Nat.add_assoc, hp, ih]
  obtain ⟨k, hk'⟩ := hm
  have hq : (i + (n + 2) * m) / (n + 2) = i / (n + 2) + m := by
    exact Nat.add_mul_div_left _ _ (by omega)
  have hr : (i + (n + 2) * m) % (n + 2) = i % (n + 2) := by
    exact Nat.add_mul_mod_self_left _ _ _
  have hj : ((i / (n + 2) + m + 1) * n) = (i / (n + 2) + 1) * n + p * k := by
    rw [← hk']; ring
  have hpar : ((i / (n + 2) + 1) * n + p * k) % 2 = ((i / (n + 2) + 1) * n) % 2 := by
    have : 2 ∣ p * k := by rw [← hk']; exact he
    omega
  have hjpos : 0 < (i / (n + 2) + 1) * n := Nat.mul_pos (Nat.succ_pos _) hn
  have h1 : ∀ x, old (x + p * k) = old x := fun x => hk k x
  unfold expandStream
  simp only [hq, hr, hj]
  have e1 : (i / (n + 2) + m) * n + i % (n + 2) = (i / (n + 2)) * n + i % (n + 2) + p * k := by
    rw [← hk']; ring
  have e2 : (i / (n + 2) + 1) * n + p * k - 1 = ((i / (n + 2) + 1) * n - 1) + p * k := by omega
  rw [e1, e2, h1, h1, hpar]

theorem pe1 (i : ℕ) : peirce 1 (i + 2) = peirce 1 i := by
  simp [OMA.S_oeis_a071282.peirce, Nat.add_mod_right]

theorem pe2 (i : ℕ) : peirce 2 (i + 6) = peirce 2 i :=
  exp_per 1 (by norm_num) (peirce 1) 2 2 pe1 (by norm_num) (by norm_num) i

theorem pe3 (i : ℕ) : peirce 3 (i + 12) = peirce 3 i :=
  exp_per 2 (by norm_num) (peirce 2) 6 3 pe2 (by norm_num) (by norm_num) i

theorem de3 (i : ℕ) : denominatorAt 3 (i + 6) = denominatorAt 3 i := by
  unfold denominatorAt
  have : 2 * (i + 6) = 2 * i + 12 := by ring
  rw [this, pe3]

theorem de3k (k i : ℕ) : denominatorAt 3 (i + 6 * k) = denominatorAt 3 i := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.mul_succ, ← Nat.add_assoc, de3, ih]
end

theorem OMA.solution : type_of% @OMA.S_oeis_a071282.main := by
  intro i
  have key : OMA.S_oeis_a071282.denominatorAt 3 i = OMA.S_oeis_a071282.denominatorAt 3 (i % 6) := by
    have h : i = i % 6 + 6 * (i / 6) := (Nat.mod_add_div i 6).symm
    conv_lhs => rw [h]
    exact de3k _ _
  rw [key]
  have hr : i % 6 < 6 := Nat.mod_lt _ (by norm_num)
  generalize i % 6 = r at hr ⊢
  interval_cases r <;> decide

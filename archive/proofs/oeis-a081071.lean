import OMAStatements.S_oeis_a081071

section Aux
open OMA.S_oeis_a081071

lemma lucas_fib (m : ℕ) : lucas (m + 1) = Nat.fib m + Nat.fib (m + 2) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m with
    | 0 => simp [lucas, Nat.fib_two]
    | 1 => simp [lucas, Nat.fib_add_two]
    | m + 2 =>
      have h1 := ih (m + 1) (by omega)
      have h2 := ih m (by omega)
      rw [show m + 2 + 1 = (m + 1 + 1) + 1 by ring, lucas, h1, h2]
      simp only [Nat.fib_add_two (n := m), Nat.fib_add_two (n := m + 1), Nat.fib_add_two (n := m + 2)]
      ring

lemma sum_fib (m : ℕ) (hm : 1 ≤ m) :
    (∑ k ∈ Finset.Icc 2 m, Nat.fib (2 * k)) + 2 = Nat.fib (2 * m + 1) := by
  induction m, hm using Nat.le_induction with
  | base => simp [Nat.fib_add_two]
  | succ m hm ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have : Nat.fib (2 * (m + 1) + 1) = Nat.fib (2 * m + 1) + Nat.fib (2 * m + 2) := by
      rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by ring, Nat.fib_add_two]
    rw [this]
    have e : 2 * (m + 1) = 2 * m + 2 := by ring
    rw [e]
    omega

end Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a081071.main := by
  intro n hn
  have h := sum_fib (2 * n) (by omega)
  have hl := lucas_fib (4 * n + 1)
  have e : 2 * (2 * n) + 1 = 4 * n + 1 := by ring
  rw [e] at h
  unfold OMA.S_oeis_a081071.a
  rw [show 4 * n + 2 = (4 * n + 1) + 1 by ring, hl, show 4 * n + 1 + 2 = 4 * n + 3 by ring]
  omega

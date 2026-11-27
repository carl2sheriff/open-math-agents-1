import OMAStatements.S_oeis_a113249

section Aux
open OMA.S_oeis_a113249

def UU (m : ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => -4 * UU m (n + 1) - m ^ 2 * UU m n

def Ev (m : ℤ) (n : ℕ) : ℤ := -m ^ 2 * UU m n ^ 2 - m ^ 2 * UU m n * UU m (n + 1) - UU m (n + 1) ^ 2
def Od (m : ℤ) (n : ℕ) : ℤ := (2 * UU m (n + 1) + m ^ 2 * UU m n) ^ 2

lemma inv (m : ℕ) (n : ℕ) :
    (a m (2 * n) = Ev m n ∧ a m (2 * n + 1) = Od m n) ∧
    (a m (2 * n + 2) = Ev m (n + 1) ∧ a m (2 * n + 3) = Od m (n + 1)) := by
  induction n with
  | zero =>
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · simp [a, Ev, UU]
    · simp [a, Od, UU]
    · simp only [a, Ev, UU]; norm_num; try ring
    · simp only [a, Od, UU]; norm_num; try ring
  | succ n ih =>
    obtain ⟨⟨h0, h1⟩, h2, h3⟩ := ih
    have e4 : a m (2 * n + 4) = Ev m (n + 2) := by
      have : a m (2 * n + 4) = (m : ℤ) ^ 4 * a m (2 * n) + (2 * (m : ℤ)) ^ 2 * a m (2 * n + 1) - 4 * a m (2 * n + 3) := rfl
      rw [this, h0, h1, h3]
      simp only [Ev, Od, UU]
      ring
    have e5 : a m (2 * n + 5) = Od m (n + 2) := by
      have : a m (2 * n + 5) = (m : ℤ) ^ 4 * a m (2 * n + 1) + (2 * (m : ℤ)) ^ 2 * a m (2 * n + 2) - 4 * a m (2 * n + 4) := rfl
      rw [this, h1, h2, e4]
      simp only [Ev, Od, UU]
      ring
    have q1 : 2 * (n + 1) = 2 * n + 2 := by ring
    have q2 : 2 * (n + 1) + 1 = 2 * n + 3 := by ring
    have q3 : 2 * (n + 1) + 2 = 2 * n + 4 := by ring
    have q4 : 2 * (n + 1) + 3 = 2 * n + 5 := by ring
    exact ⟨⟨h2, h3⟩, e4, e5⟩
end Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a113249.main := by
  intro m n
  open OMA.S_oeis_a113249 in
  have := (inv m n).1.2
  rw [this]
  exact ⟨2 * UU m (n + 1) + m ^ 2 * UU m n, by simp only [Od]; ring⟩

import OMAStatements.S_oeis_a009388

theorem OMA_mod : ∀ x : ℕ, OMA.S_oeis_a009388.InSeq x → x % 3 = 0 ∨ x % 3 = 2 := by
  intro x hx
  induction hx with
  | base => omega
  | @step a b _ _ iha ihb =>
    have hm : (a * b) % 3 = 0 ∨ (a * b) % 3 = 1 := by
      rw [Nat.mul_mod]
      rcases iha with h | h <;> rcases ihb with h' | h' <;> rw [h, h'] <;> simp
    generalize a * b = c at hm ⊢
    omega

theorem OMA.solution : type_of% @OMA.S_oeis_a009388.main := by
  refine ⟨OMA_mod, ?_⟩
  rintro n ⟨h0, h1, h2⟩
  have a := OMA_mod _ h0
  have b := OMA_mod _ h1
  have c := OMA_mod _ h2
  omega

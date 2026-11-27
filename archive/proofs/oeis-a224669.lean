import OMAStatements.S_oeis_a224669

open OMA.S_oeis_a224669 in
theorem OMA_row : ∀ k : ℕ, ∀ r : Row,
    completions (k + 4) r + completions (k + 1) r = 2 * completions (k + 3) r := by
  intro k
  induction k with
  | zero => decide
  | succ k ih =>
    intro r
    have e1 : completions (k + 1 + 4) r = ∑ s : Row, if compatible r s then completions (k + 4) s else 0 := by
      show completions ((k + 4) + 1) r = _
      rw [completions]
    have e2 : completions (k + 1 + 1) r = ∑ s : Row, if compatible r s then completions (k + 1) s else 0 := by
      rw [completions]
    have e3 : completions (k + 1 + 3) r = ∑ s : Row, if compatible r s then completions (k + 3) s else 0 := by
      show completions ((k + 3) + 1) r = _
      rw [completions]
    rw [e1, e2, e3, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s _
    split_ifs
    · exact ih s
    · simp

open OMA.S_oeis_a224669 in
theorem OMA_term (k : ℕ) : term (k + 4) + term (k + 1) = 2 * term (k + 3) := by
  unfold term
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun r _ => OMA_row k r)

open OMA.S_oeis_a224669 in
theorem OMA_t0 : term 0 = 9 := by decide
open OMA.S_oeis_a224669 in
theorem OMA_t1 : term 1 = 12 := by decide
open OMA.S_oeis_a224669 in
theorem OMA_t2 : term 2 = 25 := by decide
open OMA.S_oeis_a224669 in
theorem OMA_t3 : term 3 = 41 := by decide

open OMA.S_oeis_a224669 in
theorem OMA_fib (k : ℕ) : (term (k + 3) : ℤ) + 4 = ((term (k + 2) : ℤ) + 4) + ((term (k + 1) : ℤ) + 4) := by
  induction k with
  | zero => simp [OMA_t1, OMA_t2, OMA_t3]
  | succ k ih =>
    have := OMA_term k
    have h : (term (k + 4) : ℤ) + term (k + 1) = 2 * term (k + 3) := by exact_mod_cast this
    show (term (k + 4) : ℤ) + 4 = ((term (k + 3) : ℤ) + 4) + ((term (k + 2) : ℤ) + 4)
    omega

open OMA.S_oeis_a224669 in
theorem OMA_closed (n : ℕ) (hn : 1 ≤ n) : (term n : ℝ) =
      -4 + ((1-Real.sqrt 5)^n*(-19+13*Real.sqrt 5) + (1+Real.sqrt 5)^n*(19+13*Real.sqrt 5)) /
        (2^(n+1)*Real.sqrt 5) := by
  have hs : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.mul_self_sqrt (by norm_num)
  have hs0 : Real.sqrt 5 ≠ 0 := by positivity
  set s := Real.sqrt 5 with hsdef
  let u : ℕ → ℝ := fun n => ((1-s)^n*(-19+13*s) + (1+s)^n*(19+13*s)) / (2^(n+1)*s)
  have u1 : u 1 = 16 := by
    simp only [u]
    field_simp
    norm_num
    nlinarith [hs]
  have hs2 : s ^ 2 = 5 := by nlinarith [hs]
  have hs3 : s ^ 3 = 5 * s := by rw [pow_succ, hs2]
  have u2 : u 2 = 29 := by
    simp only [u]
    field_simp
    norm_num
    ring_nf
    linarith [hs2, hs3]
  have urec : ∀ k, u (k + 2) = u (k + 1) + u k := by
    intro k
    simp only [u]
    have e1 : (1 - s) ^ (k + 2) = 2 * (1 - s) ^ (k + 1) + 4 * (1 - s) ^ k := by
      have : (1 - s) ^ 2 = 2 * (1 - s) + 4 := by nlinarith [hs]
      calc (1 - s) ^ (k + 2) = (1 - s) ^ k * (1 - s) ^ 2 := by ring
        _ = _ := by rw [this]; ring
    have e2 : (1 + s) ^ (k + 2) = 2 * (1 + s) ^ (k + 1) + 4 * (1 + s) ^ k := by
      have : (1 + s) ^ 2 = 2 * (1 + s) + 4 := by nlinarith [hs]
      calc (1 + s) ^ (k + 2) = (1 + s) ^ k * (1 + s) ^ 2 := by ring
        _ = _ := by rw [this]; ring
    rw [e1, e2]
    field_simp
    ring
  have key : ∀ k, (term (k + 1) : ℝ) + 4 = u (k + 1) ∧ (term (k + 2) : ℝ) + 4 = u (k + 2) := by
    intro k
    induction k with
    | zero =>
      refine ⟨?_, ?_⟩
      · rw [OMA_t1]; rw [u1]; norm_num
      · rw [OMA_t2]; rw [u2]; norm_num
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have h := OMA_fib k
      have h' : (term (k + 3) : ℝ) + 4 = ((term (k + 2) : ℝ) + 4) + ((term (k + 1) : ℝ) + 4) := by
        exact_mod_cast h
      rw [show k + 1 + 2 = k + 3 by ring, show k + 1 + 1 = k + 2 by ring] at *
      rw [urec (k + 1), h', ih.1, ih.2]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have := (key k).1
  show (term (k + 1) : ℝ) = -4 + u (k + 1)
  linarith

open OMA.S_oeis_a224669 PowerSeries in
theorem OMA_gf : ((1-X)*(1-X-X^2))*series = X*(12+X-9*X^2) := by
  have hL : ((1:PowerSeries ℚ)-X)*(1-X-X^2)*series = series - C (2:ℚ) * (X*series) + X^3*series := by
    simp only [map_ofNat]; ring
  have hR : (X:PowerSeries ℚ)*(12+X-9*X^2) = C (12:ℚ) * X + X^2 - C (9:ℚ) * X^3 := by
    simp only [map_ofNat]; ring
  rw [hL, hR]
  ext n
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul', coeff_X_pow, coeff_X, series, coeff_mk]
  rcases n with _ | _ | _ | _ | n
  · simp
  · simp [coeff_succ_X_mul, OMA_t1]
  · simp [coeff_succ_X_mul, OMA_t1, OMA_t2]
    norm_num
  · simp [coeff_succ_X_mul, OMA_t1, OMA_t2, OMA_t3]
    norm_num
  · have h := OMA_term n
    have h' : (term (n + 4) : ℚ) + term (n + 1) = 2 * term (n + 3) := by exact_mod_cast h
    have c : coeff (n + 1 + 1 + 1 + 1) (X * mk fun n => if n = 0 then 0 else (term n : ℚ)) =
        coeff (n + 3) (mk fun n => if n = 0 then 0 else (term n : ℚ)) :=
      coeff_succ_X_mul (n + 3) (mk fun n => if n = 0 then 0 else (term n : ℚ))
    have e : n + 1 + 1 + 1 + 1 - 3 = n + 1 := by omega
    have h'' : (term (n + 1 + 1 + 1 + 1) : ℚ) + term (n + 1) = 2 * term (n + 3) := h'
    rw [c]
    have g0 : ¬ (n + 1 + 1 + 1 + 1 = 0) := by omega
    have g1 : ¬ (n + 1 + 1 + 1 + 1 = 1) := by omega
    have g2 : ¬ (n + 1 + 1 + 1 + 1 = 2) := by omega
    have g3 : ¬ (n + 1 + 1 + 1 + 1 = 3) := by omega
    have g4 : ¬ (n + 3 = 0) := by omega
    have g5 : ¬ (n + 1 = 0) := by omega
    have g6 : 3 ≤ n + 1 + 1 + 1 + 1 := by omega
    simp only [coeff_mk, e, g0, g1, g2, g3, g4, g5, g6, if_true, if_false, mul_zero, add_zero, sub_zero]
    linarith

theorem OMA.solution : type_of% @OMA.S_oeis_a224669.main := by
  refine ⟨OMA_closed, OMA_term, OMA_gf⟩

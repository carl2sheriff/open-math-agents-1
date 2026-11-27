import OMAStatements.S_oeis_a034178

theorem OMA.solution : type_of% @OMA.S_oeis_a034178.main := by
  intro n hn
  set C : Set (ℕ × ℕ) := {p | 1 ≤ p.1 ∧ p.1 ^ 2 + 2 * p.1 * p.2 = n} with hC
  have hA : OMA.S_oeis_a034178.a n = C.ncard := by
    unfold OMA.S_oeis_a034178.a
    symm
    refine Set.ncard_congr (fun p _ => (p.1 + p.2, p.2)) ?_ ?_ ?_
    · rintro ⟨m, j⟩ ⟨h1, h2⟩
      simp only [Set.mem_setOf_eq] at *
      constructor <;> nlinarith
    · rintro ⟨m, j⟩ ⟨m', j'⟩ _ _ h
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      subst h2
      have : m = m' := by omega
      subst this; rfl
    · rintro ⟨a, b⟩ ⟨h1, h2⟩
      have h1 : b < a := h1
      have h2 : a ^ 2 = b ^ 2 + n := h2
      refine ⟨(a - b, b), ?_, ?_⟩
      · simp only [hC, Set.mem_setOf_eq]
        obtain ⟨c, rfl⟩ : ∃ c, a = b + c := ⟨a - b, by omega⟩
        refine ⟨by omega, ?_⟩
        simp only [Nat.add_sub_cancel_left]
        nlinarith
      · show (a - b + b, b) = (a, b)
        rw [Nat.sub_add_cancel h1.le]
  have hD : C.ncard = {d : ℕ | d ∣ n ∧ d * d ≤ n ∧ Even (d + n / d)}.ncard := by
    refine Set.ncard_congr (fun p _ => p.1) ?_ ?_ ?_
    · rintro ⟨m, j⟩ ⟨h1, h2⟩
      simp only [hC, Set.mem_setOf_eq] at *
      have hn' : n = m * (m + 2 * j) := by rw [← h2]; ring
      have hdiv : n / m = m + 2 * j := by rw [hn']; exact Nat.mul_div_cancel_left _ (by omega)
      refine ⟨⟨_, hn'⟩, by nlinarith, ?_⟩
      rw [hdiv]; exact ⟨m + j, by ring⟩
    · rintro ⟨m, j⟩ ⟨m', j'⟩ ⟨h1, h2⟩ ⟨h1', h2'⟩ h
      simp only [hC, Set.mem_setOf_eq] at *
      subst h
      have : m * j = m * j' := by nlinarith
      have := Nat.eq_of_mul_eq_mul_left (by omega) this
      subst this; rfl
    · intro d ⟨hd1, hd2, hd3⟩
      obtain ⟨e, he⟩ := hd1
      have hdpos : 0 < d := by
        rcases Nat.eq_zero_or_pos d with h | h
        · subst h; omega
        · exact h
      have hdiv : n / d = e := by rw [he]; exact Nat.mul_div_cancel_left _ hdpos
      rw [hdiv] at hd3
      have hde : d ≤ e := by nlinarith
      obtain ⟨r, hr⟩ := hd3
      refine ⟨(d, (e - d) / 2), ?_, rfl⟩
      simp only [hC, Set.mem_setOf_eq]
      refine ⟨hdpos, ?_⟩
      have : (e - d) / 2 = r - d := by omega
      rw [this, he]
      obtain ⟨s, rfl⟩ : ∃ s, r = d + s := ⟨r - d, by omega⟩
      have : e = d + 2 * s := by omega
      subst this
      simp only [Nat.add_sub_cancel_left]
      ring
  have hsq : ∀ t : ℕ, Real.sqrt ((t : ℝ) ^ 2) = t := fun t => Real.sqrt_sq (Nat.cast_nonneg t)
  have key : ∀ k : ℕ, (∃ M : ℤ, Real.sqrt (k : ℝ) + Real.sqrt ((k + n : ℕ) : ℝ) = M) →
      ∃ b a : ℕ, k = b ^ 2 ∧ k + n = a ^ 2 := by
    intro k ⟨M, h⟩
    have hx := Real.sq_sqrt (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    have hy := Real.sq_sqrt (Nat.cast_nonneg (k + n) : (0 : ℝ) ≤ ((k + n : ℕ) : ℝ))
    have hx0 := Real.sqrt_nonneg (k : ℝ)
    have hy0 := Real.sqrt_nonneg (((k + n : ℕ) : ℝ))
    generalize Real.sqrt (k : ℝ) = x at *
    generalize Real.sqrt (((k + n : ℕ) : ℝ)) = y at *
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at hy
    have hMpos : (0 : ℝ) < M := by
      by_contra hneg
      push_neg at hneg
      nlinarith
    have hxq : x = ((M ^ 2 - n : ℝ)) / (2 * M) := by
      rw [eq_div_iff (by positivity)]
      have : y = M - x := by linarith
      subst this
      nlinarith
    have hk : IsSquare k := by
      by_contra hns
      have hirr := irrational_sqrt_natCast_iff.2 hns
      apply hirr
      refine ⟨((M : ℚ) ^ 2 - n) / (2 * M), ?_⟩
      have : Real.sqrt (k : ℝ) = x := by
        rw [← hx]; exact Real.sqrt_sq hx0
      rw [this, hxq]
      push_cast
      rfl
    obtain ⟨b, hb⟩ := hk
    have hxb : x = b := by
      have h2 : x ^ 2 = (b : ℝ) ^ 2 := by rw [hx, hb]; push_cast; ring
      exact (pow_left_inj₀ hx0 (Nat.cast_nonneg b) two_ne_zero).1 h2
    have hyM : y = (M : ℝ) - b := by linarith
    have hnn : (0 : ℤ) ≤ M - b := by
      have : (0 : ℝ) ≤ (M : ℝ) - b := by rw [← hyM]; exact hy0
      exact_mod_cast this
    obtain ⟨a, ha⟩ := Int.eq_ofNat_of_zero_le hnn
    have haR : (a : ℝ) = y := by
      rw [hyM]
      have : ((M - b : ℤ) : ℝ) = (a : ℤ) := by rw [ha]
      push_cast at this
      linarith
    refine ⟨b, a, by rw [hb]; ring, ?_⟩
    have : (a : ℝ) ^ 2 = k + n := by rw [haR]; exact hy
    exact_mod_cast this.symm
  have hB : C.ncard = {k : ℕ | ∃ m : ℤ, Real.sqrt k + Real.sqrt ((k + n : ℕ) : ℝ) = m}.ncard := by
    refine Set.ncard_congr (fun p _ => p.2 ^ 2) ?_ ?_ ?_
    · rintro ⟨m, j⟩ ⟨h1, h2⟩
      have h2 : m ^ 2 + 2 * m * j = n := h2
      refine ⟨(m + 2 * j : ℕ), ?_⟩
      have e : j ^ 2 + n = (m + j) ^ 2 := by rw [← h2]; ring
      show Real.sqrt ((j ^ 2 : ℕ) : ℝ) + Real.sqrt ((j ^ 2 + n : ℕ) : ℝ) = _
      rw [e]
      push_cast
      have h3 := hsq (m + j)
      push_cast at h3
      rw [hsq j, h3]
      push_cast
      ring
    · rintro ⟨m, j⟩ ⟨m', j'⟩ ⟨h1, h2⟩ ⟨h1', h2'⟩ h
      have h1 : 1 ≤ m := h1
      have h1' : 1 ≤ m' := h1'
      have h2 : m ^ 2 + 2 * m * j = n := h2
      have h2' : m' ^ 2 + 2 * m' * j' = n := h2'
      have h : j ^ 2 = j' ^ 2 := h
      have hj : j = j' := (Nat.pow_left_injective two_ne_zero) h
      subst hj
      have : m = m' := by
        rcases lt_trichotomy m m' with hlt | heq | hgt
        · exfalso; nlinarith
        · exact heq
        · exfalso; nlinarith
      subst this; rfl
    · intro k hk
      obtain ⟨b, a, hb, ha⟩ := key k hk
      have hba : b < a := by nlinarith
      obtain ⟨c, rfl⟩ : ∃ c, a = b + c := ⟨a - b, by omega⟩
      refine ⟨(c, b), ⟨by omega, by nlinarith⟩, ?_⟩
      show b ^ 2 = k
      omega
  exact ⟨hA.trans hD, hA.trans hB, hA⟩

import OMAStatements.S_oeis_a001045

section Aux
open OMA.S_oeis_a001045

lemma a_rec (n : ℕ) : a (n + 1) = 2 * a n + (-1) ^ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp [a]
    | 1 => simp [a]
    | m + 2 =>
      have h1 := ih (m + 1) (by omega)
      have h2 := ih m (by omega)
      have e : a (m + 2 + 1) = a (m + 2) + 2 * a (m + 1) := rfl
      have p1 : (-1 : ℤ) ^ (m + 1) = - (-1) ^ m := by ring
      have p2 : (-1 : ℤ) ^ (m + 2) = (-1) ^ m := by ring
      rw [e, p2]
      rw [p1] at h1
      linarith

lemma a_three (n : ℕ) : 3 * a n = 2 ^ n - (-1) ^ n := by
  induction n with
  | zero => simp [a]
  | succ n ih =>
    rw [a_rec]
    have : (2 : ℤ) ^ (n + 1) = 2 * 2 ^ n := by ring
    have h2 : (-1 : ℤ) ^ (n + 1) = - (-1) ^ n := by ring
    rw [this, h2]
    linarith

lemma A_pow (n : ℕ) : ∀ i j, (A ^ n) i j = if i = j then a n + (-1) ^ n else a n := by
  induction n with
  | zero =>
    intro i j
    fin_cases i <;> fin_cases j <;> simp [a, A]
  | succ n ih =>
    intro i j
    rw [pow_succ, Matrix.mul_apply, Fin.sum_univ_three]
    have hA : ∀ i j, A i j = if i = j then 0 else 1 := fun _ _ => rfl
    simp only [ih, hA]
    rw [a_rec]
    fin_cases i <;> fin_cases j <;> simp <;> ring

lemma card_mult (n : ℕ) :
    ((((Finset.Ioo (2 ^ n) (2 ^ (n + 1))).filter (fun m => 3 ∣ m)).card : ℕ) : ℤ) = a n := by
  have key : ∀ x y : ℕ, x ≤ y →
      ((Finset.Ioc x y).filter (fun m => 3 ∣ m)).card = y / 3 - x / 3 := by
    intro x y hxy
    have h := Nat.Ioc_filter_dvd_card_eq_div y 3
    have h' := Nat.Ioc_filter_dvd_card_eq_div x 3
    have hu : Finset.Ioc 0 y = Finset.Ioc 0 x ∪ Finset.Ioc x y :=
      (Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le x) hxy).symm
    have hd : Disjoint (Finset.Ioc 0 x) (Finset.Ioc x y) := Finset.Ioc_disjoint_Ioc_of_le le_rfl
    rw [hu, Finset.filter_union, Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hd)] at h
    omega
  have hpos : 0 < 2 ^ (n + 1) := by positivity
  have hI : Finset.Ioo (2 ^ n) (2 ^ (n + 1)) = Finset.Ioc (2 ^ n) (2 ^ (n + 1) - 1) := by
    ext m; simp only [Finset.mem_Ioo, Finset.mem_Ioc]; omega
  rw [hI, key _ _ (by have : 2 ^ n ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega); omega)]
  have h3 := a_three n
  have hx : ((2 ^ n : ℕ) : ℤ) = (2 : ℤ) ^ n := by push_cast; rfl
  rw [← hx] at h3
  have h2 : (2 ^ (n + 1) : ℕ) = 2 * 2 ^ n := by ring
  rw [h2]
  generalize 2 ^ n = x at h3 ⊢
  rcases neg_one_pow_eq_or ℤ n with h | h <;> rw [h] at h3 <;> omega

end Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a001045.main := by
  refine ⟨card_mult, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h := a_rec m
  refine ⟨?_, fun i j hij => ?_, fun i => ?_⟩
  · rw [Matrix.trace, Fin.sum_univ_three]
    simp only [Matrix.diag_apply, A_pow]
    simp
    rw [h]
    simp [pow_succ]
    ring
  · rw [A_pow]; simp [hij]
  · rw [A_pow, if_pos rfl]
    rcases Nat.even_or_odd m with he | ho
    · have p : (-1 : ℤ) ^ (m + 1) = -1 := by rw [pow_succ, he.neg_one_pow]; ring
      have : ¬ Even (m + 1) := by rw [Nat.even_add_one]; exact not_not.mpr he
      rw [if_neg this, p]; ring
    · have p : (-1 : ℤ) ^ (m + 1) = 1 := by rw [pow_succ, ho.neg_one_pow]; ring
      have : Even (m + 1) := Nat.even_add_one.mpr (Nat.not_even_iff_odd.mpr ho)
      rw [if_pos this, p]

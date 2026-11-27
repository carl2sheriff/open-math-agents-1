import OMAStatements.S_oeis_a276646
import Mathlib

section Aux
open OMA.S_oeis_a276646

lemma blk (d m : ℕ) (hm : m ≤ 9 * 10 ^ d) :
    ∑ i ∈ Finset.range m, decimalFraction (10 ^ d + i) ≤ 11 * (m : ℚ) / 20 := by
  have hlog : ∀ i ∈ Finset.range m, decimalFraction (10 ^ d + i) = ((10 ^ d + i : ℕ) : ℚ) / 10 ^ (d + 1) := by
    intro i hi
    have hi' : i < 9 * 10 ^ d := lt_of_lt_of_le (Finset.mem_range.mp hi) hm
    unfold decimalFraction
    have : Nat.log 10 (10 ^ d + i) = d := by
      rw [Nat.log_eq_iff (by omega)]
      constructor
      · omega
      · rw [pow_succ]; omega
    rw [this]
  rw [Finset.sum_congr rfl hlog, ← Finset.sum_div]
  have key : ∀ m : ℕ, 2 * ∑ i ∈ Finset.range m, (((10 ^ d + i : ℕ)) : ℚ) = (m : ℚ) * (2 * 10 ^ d + m - 1) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, mul_add, ih]; push_cast; ring
  have h2 := key m
  have hp : (0 : ℚ) < 10 ^ (d + 1) := by positivity
  rw [div_le_iff₀ hp]
  have hm' : (m : ℚ) ≤ 9 * 10 ^ d := by exact_mod_cast hm
  have hpos : (0 : ℚ) ≤ m := by positivity
  rw [pow_succ]
  nlinarith [hpos, hm', h2]

lemma full (d : ℕ) : ∑ i ∈ Finset.range (10 ^ d - 1), decimalFraction (i + 1) ≤ 11 * ((10 ^ d - 1 : ℕ) : ℚ) / 20 := by
  induction d with
  | zero => simp
  | succ d ih =>
    have h1 : 1 ≤ 10 ^ d := Nat.one_le_pow _ _ (by norm_num)
    have e : 10 ^ (d + 1) - 1 = (10 ^ d - 1) + 9 * 10 ^ d := by rw [pow_succ]; omega
    rw [e, Finset.sum_range_add]
    have hb := blk d (9 * 10 ^ d) le_rfl
    have : ∀ x : ℕ, decimalFraction (10 ^ d - 1 + x + 1) = decimalFraction (10 ^ d + x) := by
      intro x; congr 1; omega
    simp only [this]
    push_cast [Nat.cast_sub h1] at ih hb ⊢
    linarith
end Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a276646.main := by
  open OMA.S_oeis_a276646 in
  intro n hn
  rw [div_le_iff₀ (by exact_mod_cast hn)]
  set d := Nat.log 10 n with hd
  have h1 : 10 ^ d ≤ n := Nat.pow_log_le_self 10 hn.ne'
  have h2 : n < 10 ^ (d + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have hp : 1 ≤ 10 ^ d := Nat.one_le_pow _ _ (by norm_num)
  have e : n = (10 ^ d - 1) + (n - 10 ^ d + 1) := by omega
  rw [e, Finset.sum_range_add]
  have hb := blk d (n - 10 ^ d + 1) (by rw [pow_succ] at h2; omega)
  have hf := full d
  have : ∀ x : ℕ, decimalFraction (10 ^ d - 1 + x + 1) = decimalFraction (10 ^ d + x) := by
    intro x; congr 1; omega
  simp only [this]
  have c1 : ((10 ^ d - 1 : ℕ) : ℚ) + ((n - 10 ^ d + 1 : ℕ) : ℚ) = ((10 ^ d - 1 + (n - 10 ^ d + 1) : ℕ) : ℚ) := by
    push_cast; ring
  rw [← c1]
  linarith

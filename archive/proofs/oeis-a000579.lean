import OMAStatements.S_oeis_a000579
import Mathlib

section Aux
open Finset

theorem hockey (p : ℕ) : ∀ N : ℕ, ∑ i ∈ range (N + 1), Nat.choose i p = Nat.choose (N + 1) (p + 1) := by
  intro N
  induction N with
  | zero => cases p <;> simp <;> exact (Nat.choose_eq_zero_of_lt (by omega)).symm
  | succ N ih =>
    rw [sum_range_succ, ih, Nat.choose_succ_succ (N + 1) p]
    ring

theorem vand (p : ℕ) : ∀ N q : ℕ,
    ∑ i ∈ range (N + 1), Nat.choose i p * Nat.choose (N - i) q = Nat.choose (N + 1) (p + q + 1) := by
  intro N
  induction N with
  | zero => intro q; cases q <;> cases p <;> simp <;> exact (Nat.choose_eq_zero_of_lt (by omega)).symm
  | succ N ih =>
    intro q
    cases q with
    | zero => simpa using hockey p (N + 1)
    | succ q =>
      rw [sum_range_succ]
      have h0 : Nat.choose (N + 1 - (N + 1)) (q + 1) = 0 := by simp
      rw [h0, mul_zero, add_zero]
      have h1 : ∀ i ∈ range (N + 1), Nat.choose i p * Nat.choose (N + 1 - i) (q + 1) =
          Nat.choose i p * Nat.choose (N - i) q + Nat.choose i p * Nat.choose (N - i) (q + 1) := by
        intro i hi
        have : N + 1 - i = (N - i) + 1 := by have := mem_range.1 hi; omega
        rw [this, Nat.choose_succ_succ, mul_add]
      rw [sum_congr rfl h1, sum_add_distrib, ih q, ih (q + 1)]
      have : p + (q + 1) + 1 = (p + q + 1) + 1 := by ring
      rw [this, Nat.choose_succ_succ (N + 1) (p + q + 1)]

theorem vand2 (p q n r : ℕ) (hq : 2 ≤ q) (hr : r ≤ n + 1) :
    ∑ l ∈ range (n + 1), Nat.choose l p * Nat.choose (r + 1 - l) q = Nat.choose (r + 2) (p + q + 1) := by
  have hz : ∀ i, r ≤ i → Nat.choose i p * Nat.choose (r + 1 - i) q = 0 := by
    intro i hi
    rw [Nat.choose_eq_zero_of_lt (by omega : r + 1 - i < q), mul_zero]
  have e1 : ∑ l ∈ range (n + 1), Nat.choose l p * Nat.choose (r + 1 - l) q =
      ∑ l ∈ range r, Nat.choose l p * Nat.choose (r + 1 - l) q := by
    symm
    apply sum_subset (range_subset_range.2 hr)
    intro i _ hi
    exact hz i (by simpa using hi)
  have e2 : ∑ l ∈ range (r + 2), Nat.choose l p * Nat.choose (r + 1 - l) q =
      ∑ l ∈ range r, Nat.choose l p * Nat.choose (r + 1 - l) q := by
    symm
    apply sum_subset (range_subset_range.2 (by omega))
    intro i _ hi
    exact hz i (by simpa using hi)
  rw [e1, ← e2, vand p (r + 1) q]

theorem tri_inner (n k l : ℕ) :
    ∑ m ∈ range (n + 1), (if k + l + m ≤ n then k * l * m else 0) =
      k * l * Nat.choose (n - (k + l) + 1) 2 := by
  by_cases h : k + l ≤ n
  · have e : ∑ m ∈ range (n + 1), (if k + l + m ≤ n then k * l * m else 0) =
        ∑ m ∈ range (n - (k + l) + 1), k * l * m := by
      rw [← sum_filter]
      apply sum_congr
      · ext m; simp only [mem_filter, mem_range]; omega
      · intro m _; rfl
    rw [e, ← mul_sum]
    have := hockey 1 (n - (k + l))
    simp only [Nat.choose_one_right] at this
    rw [this]
  · have : n - (k + l) + 1 = 1 := by omega
    rw [this]
    simp only [Nat.choose_eq_zero_of_lt (by omega : 1 < 2), mul_zero]
    apply sum_eq_zero
    intro m _
    rw [if_neg (by omega)]

theorem tri_mid (n k : ℕ) (hk : k ≤ n) :
    ∑ l ∈ range (n + 1), k * l * Nat.choose (n - (k + l) + 1) 2 = k * Nat.choose (n - k + 2) 4 := by
  have : ∀ l ∈ range (n + 1), k * l * Nat.choose (n - (k + l) + 1) 2 =
      k * (Nat.choose l 1 * Nat.choose (n - k + 1 - l) 2) := by
    intro l _
    have : n - (k + l) + 1 = n - k + 1 - l ∨ (n - (k + l) + 1 < 2 ∧ n - k + 1 - l < 2) := by omega
    rcases this with h | h
    · rw [h, Nat.choose_one_right]; ring
    · rw [Nat.choose_eq_zero_of_lt h.1, Nat.choose_eq_zero_of_lt h.2]; simp
  rw [sum_congr rfl this, ← mul_sum, vand2 1 2 n (n - k) (by omega) (by omega)]

end Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a000579.main := by
  intro n
  unfold OMA.S_oeis_a000579.weightedTripleSimplexSum
  have h1 : ∀ k ∈ Finset.range (n + 1),
      ∑ l ∈ Finset.range (n + 1), ∑ m ∈ Finset.range (n + 1),
        (if k + l + m ≤ n then k * l * m else 0) = k * Nat.choose (n - k + 2) 4 := by
    intro k hk
    have hk' : k ≤ n := by have := Finset.mem_range.1 hk; omega
    rw [← tri_mid n k hk']
    exact Finset.sum_congr rfl (fun l _ => tri_inner n k l)
  rw [Finset.sum_congr rfl h1]
  have h2 : ∀ k ∈ Finset.range (n + 1), k * Nat.choose (n - k + 2) 4 =
      Nat.choose k 1 * Nat.choose (n + 1 + 1 - k) 4 := by
    intro k hk
    have hk' : k ≤ n := by have := Finset.mem_range.1 hk; omega
    rw [Nat.choose_one_right, show n + 1 + 1 - k = n - k + 2 by omega]
  rw [Finset.sum_congr rfl h2, vand2 1 4 n (n + 1) (by omega) le_rfl]

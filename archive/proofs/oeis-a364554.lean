import OMAStatements.S_oeis_a364554
import Mathlib



theorem OMA_back (n p d r : ℕ) (hn : n = d * r)
    (h : d * p = 2 * r + 1 ∨ d * p + 1 = 2 * r ∨ 2 * (d * p) = r + 1 ∨ 2 * (d * p) + 1 = r) :
    ∃ k : ℕ, k * (k + 1) / 2 = n * p := by
  subst hn
  have key : ∀ k : ℕ, k * (k + 1) = d * r * p * 2 → ∃ k : ℕ, k * (k + 1) / 2 = d * r * p :=
    fun k hk => ⟨k, Nat.div_eq_of_eq_mul_left Nat.two_pos hk⟩
  rcases h with h | h | h | h
  · apply key (2 * r)
    have : d * r * p * 2 = r * (d * p) * 2 := by ring
    rw [this, h]; ring
  · apply key (d * p)
    have : d * r * p * 2 = d * p * (2 * r) := by ring
    rw [this, ← h]
  · apply key r
    have : d * r * p * 2 = r * (2 * (d * p)) := by ring
    rw [this, h]
  · apply key (r - 1)
    have hr : 1 ≤ r := by omega
    obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have : d * (s + 1) * p * 2 = (s + 1) * (2 * (d * p)) := by ring
    rw [this]
    have hs : s = 2 * (d * p) := by omega
    rw [← hs]; ring

theorem OMA_fwd (n p : ℕ) (hn : 0 < n) (hp : p.Prime) (k : ℕ) (hk : k * (k + 1) / 2 = n * p) :
    ∃ d r : ℕ, n = d * r ∧
      (d * p = 2 * r + 1 ∨ d * p + 1 = 2 * r ∨ 2 * (d * p) = r + 1 ∨ 2 * (d * p) + 1 = r) := by
  have hk2 : k * (k + 1) = 2 * (n * p) := by
    have := Nat.div_mul_cancel (Nat.even_mul_succ_self k).two_dvd
    rw [hk] at this; linarith
  have hp0 : 0 < p := hp.pos
  have hdvd : p ∣ k * (k + 1) := ⟨2 * n, by rw [hk2]; ring⟩
  rcases (Nat.Prime.dvd_mul hp).mp hdvd with ⟨j, hj⟩ | ⟨j, hj⟩
  · -- k = p * j
    have h1 : j * (p * j + 1) = 2 * n := by
      have : p * (j * (p * j + 1)) = p * (2 * n) := by
        rw [hj] at hk2; nlinarith [hk2]
      exact Nat.eq_of_mul_eq_mul_left hp0 this
    rcases Nat.even_or_odd' j with ⟨i, hi | hi⟩
    · subst hi
      refine ⟨i, 2 * i * p + 1, by nlinarith [h1], Or.inr (Or.inr (Or.inr ?_))⟩
      ring
    · subst hi
      rcases hp.eq_two_or_odd' with rfl | ⟨q, hq⟩
      · exfalso
        have : Odd ((2 * i + 1) * (2 * (2 * i + 1) + 1)) :=
          Odd.mul ⟨i, rfl⟩ ⟨2 * i + 1, by ring⟩
        rw [h1] at this
        rw [Nat.odd_iff] at this; omega
      · subst hq
        refine ⟨2 * i + 1, 2 * q * i + q + i + 1, by nlinarith [h1], Or.inr (Or.inl ?_)⟩
        ring
  · -- k + 1 = p * j
    have h1 : k * j = 2 * n := by
      have : p * (k * j) = p * (2 * n) := by
        have : k * (p * j) = 2 * (n * p) := by rw [← hj]; exact hk2
        nlinarith [this]
      exact Nat.eq_of_mul_eq_mul_left hp0 this
    rcases Nat.even_or_odd' j with ⟨i, hi | hi⟩
    · subst hi
      refine ⟨i, k, by nlinarith [h1], Or.inr (Or.inr (Or.inl ?_))⟩
      linarith
    · subst hi
      rcases Nat.even_or_odd' k with ⟨m, hm | hm⟩
      · subst hm
        refine ⟨2 * i + 1, m, by nlinarith [h1], Or.inl ?_⟩
        linarith
      · exfalso
        subst hm
        have : Odd ((2 * m + 1) * (2 * i + 1)) := Odd.mul ⟨m, rfl⟩ ⟨i, rfl⟩
        rw [h1] at this
        rw [Nat.odd_iff] at this; omega

theorem OMA.solution : type_of% @OMA.S_oeis_a364554.main := by
  intro n hn
  have heq : OMA.S_oeis_a364554.triangularPrimes n = OMA.S_oeis_a364554.divisorPrimes n := by
    ext p
    constructor
    · rintro ⟨hp, k, hk⟩
      exact ⟨hp, OMA_fwd n p hn hp k hk⟩
    · rintro ⟨hp, d, r, hnd, h⟩
      exact ⟨hp, OMA_back n p d r hnd h⟩
  refine ⟨heq, ?_, by rw [heq]⟩
  rw [heq]
  apply (Set.finite_le_nat (2 * n + 1)).subset
  rintro p ⟨hp, d, r, hnd, h⟩
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with rfl | h0
    · simp at hnd; omega
    · exact h0
  have hpd : p ≤ d * p := Nat.le_mul_of_pos_left p hd
  have hdr : d ≤ n := by rw [hnd]; exact Nat.le_mul_of_pos_right d (by rcases Nat.eq_zero_or_pos r with rfl | h0 <;> simp_all)
  have hrn : r ≤ n := by rw [hnd]; exact Nat.le_mul_of_pos_left r hd
  show p ≤ 2 * n + 1
  omega

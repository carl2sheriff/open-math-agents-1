import OMAStatements.S_oeis_a083137

section Aux
open OMA.S_oeis_a083137

lemma pal_pow (m : ℕ) (hm : 1 ≤ m) : palindrome (10 ^ m + 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have e : 10 ^ (k + 1) + 1 = 1 + 10 * 10 ^ k := by ring
  have hd : Nat.digits 10 (10 ^ (k + 1) + 1) = 1 :: (List.replicate k 0 ++ [1]) := by
    rw [e, Nat.digits_add 10 (by norm_num) 1 (10 ^ k) (by norm_num) (Or.inl (by norm_num))]
    congr 1
    have := Nat.digits_base_pow_mul (b := 10) (k := k) (m := 1) (by norm_num) (by norm_num)
    simpa using this
  unfold palindrome
  rw [hd]
  simp [List.reverse_append, List.reverse_replicate]

lemma exists_pal (L : List ℕ) (hL : ∀ x ∈ L, 0 < x) :
    ∃ p, palindrome p ∧ ∀ x ∈ L, x < p ∧ Nat.Coprime p x := by
  set N := L.prod with hN
  have hNpos : 0 < N := List.prod_pos (fun x hx => hL x hx)
  set m := (Nat.factorial N) * (L.sum + 1) with hm
  have hm1 : 1 ≤ m := Nat.mul_pos (Nat.factorial_pos _) (by omega)
  refine ⟨10 ^ m + 1, pal_pow m hm1, fun x hx => ⟨?_, ?_⟩⟩
  · have h1 : x ≤ L.sum := List.le_sum_of_mem hx
    have h2 : L.sum + 1 ≤ m := Nat.le_mul_of_pos_left _ (Nat.factorial_pos _)
    have h3 : m < 10 ^ m := Nat.lt_pow_self (by norm_num)
    omega
  · apply Nat.coprime_of_dvd
    intro q hq hqp hqx
    have hxN : x ∣ N := List.dvd_prod hx
    have hqN : q ≤ N := Nat.le_of_dvd hNpos (hqx.trans hxN)
    have hq2 := hq.two_le
    rcases eq_or_ne q 2 with rfl | hq2'
    · have : 2 ∣ 10 ^ m := dvd_pow (by norm_num) (by omega)
      omega
    rcases eq_or_ne q 5 with rfl | hq5
    · have : 5 ∣ 10 ^ m := dvd_pow (by norm_num) (by omega)
      omega
    haveI : Fact q.Prime := ⟨hq⟩
    have hq10 : ¬ q ∣ 10 := by
      intro hd
      have : q ∣ 2 * 5 := by simpa using hd
      rcases (Nat.Prime.dvd_mul hq).mp this with h | h
      · exact hq2' ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h)
      · exact hq5 ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h)
    have hz : ((10 : ℕ) : ZMod q) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]; exact hq10
    have hf := ZMod.pow_card_sub_one_eq_one hz
    have hdvd : q - 1 ∣ m := by
      have : q - 1 ∣ Nat.factorial N := Nat.dvd_factorial (by omega) (by omega)
      exact this.trans (Dvd.intro _ rfl)
    obtain ⟨c, hc⟩ := hdvd
    have h0 : ((10 ^ m + 1 : ℕ) : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hqp
    push_cast at h0 hf
    rw [hc, pow_mul, hf, one_pow] at h0
    have : ((2 : ℕ) : ZMod q) = 0 := by push_cast; linear_combination h0
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hq2' ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp this)

noncomputable def nxt (L : List ℕ) : ℕ := by
  classical
  exact if h : ∃ p, palindrome p ∧ ∀ x ∈ L, x < p ∧ Nat.Coprime p x then Nat.find h else 0

noncomputable def LL : ℕ → List ℕ
  | 0 => [1]
  | n + 1 => LL n ++ [nxt (LL n)]

lemma LL_len (n : ℕ) : (LL n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [LL, ih]

lemma nxt_spec (L : List ℕ) (hL : ∀ x ∈ L, 0 < x) :
    palindrome (nxt L) ∧ (∀ x ∈ L, x < nxt L ∧ Nat.Coprime (nxt L) x) ∧
      ∀ p, palindrome p → (∀ x ∈ L, x < p ∧ Nat.Coprime p x) → nxt L ≤ p := by
  classical
  have h := exists_pal L hL
  have e : nxt L = Nat.find h := by unfold nxt; rw [dif_pos h]
  rw [e]
  exact ⟨(Nat.find_spec h).1, (Nat.find_spec h).2, fun p hp1 hp2 => Nat.find_min' h ⟨hp1, hp2⟩⟩

lemma LL_pos (n : ℕ) : ∀ x ∈ LL n, 0 < x := by
  induction n with
  | zero => simp [LL]
  | succ n ih =>
    intro x hx
    simp only [LL, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact ih x hx
    · have hne : 0 < (LL n).length := by rw [LL_len]; omega
      obtain ⟨y, hy⟩ := List.length_pos_iff_exists_mem.mp hne
      have := ((nxt_spec (LL n) ih).2.1 y hy).1
      have := ih y hy
      omega

lemma LL_prefix (n i : ℕ) (hi : i ≤ n) : (LL (n + 1)).getD i 0 = (LL n).getD i 0 := by
  have : i < (LL n).length := by rw [LL_len]; omega
  simp [LL, List.getD_eq_getElem?_getD, List.getElem?_append_left this]

noncomputable def aa (n : ℕ) : ℕ := (LL n).getD n 0

lemma aa_eq (n i : ℕ) (hi : i ≤ n) : aa i = (LL n).getD i 0 := by
  induction n, hi using Nat.le_induction with
  | base => rfl
  | succ n hn ih => rw [ih, LL_prefix n i hn]

lemma aa_mem (n i : ℕ) (hi : i ≤ n) : aa i ∈ LL n := by
  rw [aa_eq n i hi, List.getD_eq_getElem?_getD]
  have : i < (LL n).length := by rw [LL_len]; omega
  rw [List.getElem?_eq_getElem this]
  simp

lemma mem_aa (n : ℕ) (x : ℕ) (hx : x ∈ LL n) : ∃ i ≤ n, aa i = x := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have hi' : i ≤ n := by rw [LL_len] at hi; omega
  refine ⟨i, hi', ?_⟩
  rw [aa_eq n i hi', List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  simp

lemma aa_succ (n : ℕ) : aa (n + 1) = nxt (LL n) := by
  unfold aa
  have : (LL (n + 1)).length = n + 2 := LL_len _
  simp [LL, List.getD_eq_getElem?_getD, LL_len]
end Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a083137.main := by
  refine ⟨aa, by simp [aa, LL], fun n => ?_⟩
  have hs := nxt_spec (LL n) (LL_pos n)
  rw [aa_succ]
  constructor
  · refine ⟨hs.1, fun i hi => ?_⟩
    have := hs.2.1 (aa i) (aa_mem n i hi)
    exact this
  · intro p ⟨hp1, hp2⟩
    apply hs.2.2 p hp1
    intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_aa n x hx
    exact hp2 i hi

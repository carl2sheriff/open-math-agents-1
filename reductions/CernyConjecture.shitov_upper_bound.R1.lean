import FormalConjectures.Wikipedia.CernyConjecture

-- Reduction CernyConjecture.shitov_upper_bound.R1 of Shitov's bound (2019)
-- Credit: @carl2sheriff
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

open Asymptotics Filter

namespace OMA.R_CernyConjecture_shitov_upper_bound_R1

/-- Pin-Frankl (Frankl 1982, Pin 1983), as stated in Shitov, arXiv 1901.06542, Theorem 3:
a synchronizing automaton with `n` states, a word `u` of rank `k ≥ 2` (corank `r = n - k`) :
there is a word `w` of length at most `|u| + (r+1)(r+2)/2` and of rank `< k`. The factor 2
avoids the integer division. -/
def H1 : Prop :=
  ∀ (n : ℕ) {α : Type} [Finite α] (M : DFA α (Fin n)), M.IsSynchronizing →
  ∀ rk : List α → ℕ, (∀ w, rk w = (Finset.univ.image (fun q => M.evalFrom q w)).card) →
  ∀ u : List α, 2 ≤ rk u →
  ∃ w : List α, 2 * w.length ≤ 2 * u.length + (n + 1 - rk u) * (n + 2 - rk u) ∧ rk w < rk u

/-- Key lemma of Shitov, arXiv 1901.06542, Theorem 2 (variant of Szykula, arXiv 1702.05455,
Lemmas 2 and 7): `M` synchronizing with `n` states, `u` of corank `r` with `1 ≤ r ≤ n/2 - 1`,
`v` of length `λ` with `rk v ≤ rk v'` for all words `v'` of length `≤ λ + 2r`. Then there is a
word of length `≤ |u| + λ + 2r` and of corank `≥ r + 1`. -/
def H2 : Prop :=
  ∀ (n : ℕ) {α : Type} [Finite α] (M : DFA α (Fin n)), M.IsSynchronizing →
  ∀ rk : List α → ℕ, (∀ w, rk w = (Finset.univ.image (fun q => M.evalFrom q w)).card) →
  ∀ u v : List α, 1 ≤ n - rk u → 2 * (n - rk u) + 2 ≤ n →
    (∀ v' : List α, v'.length ≤ v.length + 2 * (n - rk u) → rk v ≤ rk v') →
  ∃ w : List α, w.length ≤ u.length + v.length + 2 * (n - rk u) ∧ rk w + (n - rk u) + 1 ≤ n

/-- Optimisation estimate of Shitov, arXiv 1901.06542, Proposition 7 (proof in Section 4,
Claims 8 and 9): for `n`, `ρ` positive integers with `ρ < n/2`, `k = ⌊n/2⌋`, reals
`s_1, ..., s_k ≥ 0` with `s_1 + ... + s_k ≤ ρ`, the sum over `r = ρ..k` of
`min(r²/4, 1·s_1 + ... + r·s_r)` is at most `(15625/1597536) n³ + o(n³)`, the `o(n³)` being
uniform in `(ρ, s)` (error `O(n² log n)`, end of Section 4); `g` is taken nonnegative. -/
def H3 : Prop :=
  ∃ g : ℝ → ℝ, g =o[atTop] (fun x : ℝ => x ^ 3) ∧ (∀ x, 0 ≤ g x) ∧
  ∀ (n ρ : ℕ) (s : ℕ → ℝ), 0 < n → 0 < ρ → 2 * ρ < n → (∀ j, 0 ≤ s j) →
    ∑ j ∈ Finset.Icc 1 (n / 2), s j ≤ ρ →
    ∑ r ∈ Finset.Icc ρ (n / 2),
        min ((r : ℝ) ^ 2 / 4) (∑ j ∈ Finset.Icc 1 r, (j : ℝ) * s j)
      ≤ 15625 / 1597536 * (n : ℝ) ^ 3 + g (n : ℝ)

-- ### Step 0 : reduction to a finite alphabet and states `Fin n`

/-- Step 0: the bound for all `DFA β (Fin n)` (`β : Type`) transfers to any `DFA α σ`
(`σ` finite): take the alphabet to be the finite set of transformations induced by `M`. -/
lemma reduce_to_fin
    (B : ℕ → ℝ)
    (hcore : ∀ (n : ℕ) {β : Type} [Finite β] (M : DFA β (Fin n)), M.IsSynchronizing →
      ∃ w : List β, M.IsSynchronizingWord w ∧ (w.length : ℝ) ≤ B n)
    {α : Type*} {σ : Type*} [Fintype σ] (M : DFA α σ) (hM : M.IsSynchronizing) :
    ∃ w : List α, M.IsSynchronizingWord w ∧ (w.length : ℝ) ≤ B (Fintype.card σ) := by
  classical
  obtain ⟨e⟩ : Nonempty (σ ≃ Fin (Fintype.card σ)) := ⟨Fintype.equivFin σ⟩
  obtain ⟨tr, htr⟩ : ∃ tr : α → Fin (Fintype.card σ) → Fin (Fintype.card σ),
      ∀ a i, tr a i = e (M.step (e.symm i) a) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨M', hM'⟩ : ∃ M' : DFA (Set.range tr) (Fin (Fintype.card σ)),
      ∀ i (t : Set.range tr), M'.step i t = t.1 i :=
    ⟨{ step := fun i t => t.1 i, start := e M.start, accept := ∅ }, fun _ _ => rfl⟩
  have : Finite (Set.range tr) := (Set.toFinite (Set.range tr)).to_subtype
  -- project a word of `α` to `β`
  have hproj : ∀ (w : List α) (q : σ),
      M'.evalFrom (e q) (w.map (fun a => (⟨tr a, a, rfl⟩ : Set.range tr))) = e (M.evalFrom q w) := by
    intro w
    induction w with
    | nil => intro q; simp
    | cons a w ih =>
      intro q
      simp only [List.map_cons, DFA.evalFrom_cons]
      have hs : M'.step (e q) (⟨tr a, a, rfl⟩ : Set.range tr) = e (M.step q a) := by
        rw [hM']
        show tr a (e q) = _
        rw [htr]
        simp
      rw [hs]
      exact ih (M.step q a)
  obtain ⟨w0, p0, hp0⟩ := hM
  have hsyn : M'.IsSynchronizing := by
    refine ⟨w0.map (fun a => (⟨tr a, a, rfl⟩ : Set.range tr)), e p0, fun q' => ?_⟩
    have := hproj w0 (e.symm q')
    rw [Equiv.apply_symm_apply] at this
    rw [this, hp0]
  obtain ⟨w', ⟨p', hp'⟩, hlen⟩ := hcore (Fintype.card σ) M' hsyn
  -- lift a word of `β` back to `α`
  have hlift : ∀ (w' : List (Set.range tr)) (q : σ),
      e (M.evalFrom q (w'.map (fun t => Classical.choose t.2))) = M'.evalFrom (e q) w' := by
    intro w'
    induction w' with
    | nil => intro q; simp
    | cons t w' ih =>
      intro q
      simp only [List.map_cons, DFA.evalFrom_cons]
      have hc := Classical.choose_spec t.2
      have hs : M'.step (e q) t = e (M.step q (Classical.choose t.2)) := by
        rw [hM']
        exact (congrFun hc (e q)).symm.trans (by rw [htr]; simp)
      rw [hs]
      exact ih _
  refine ⟨w'.map (fun t => Classical.choose t.2), ⟨e.symm p', fun q => ?_⟩, ?_⟩
  · apply e.injective
    rw [hlift, hp']
    simp
  · simpa using hlen

-- ### Step 1 : the sequence `lam i` (shortest length of a word of corank `≥ i`)

/-- Existence of `lam i` = least length of a word of corank `≥ i`, for `i ≤ n - 1`. -/
lemma lam_exists {n : ℕ} {α : Type} (M : DFA α (Fin n)) (hM : M.IsSynchronizing)
    (rk : List α → ℕ) (hrk : ∀ w, rk w = (Finset.univ.image (fun q => M.evalFrom q w)).card) :
    ∃ lam : ℕ → ℕ, lam 0 = 0 ∧ Monotone lam ∧
      (∀ i, i ≤ n - 1 → ∃ w : List α, w.length = lam i ∧ i + rk w ≤ n) ∧
      (∀ i, i ≤ n - 1 → ∀ w : List α, w.length < lam i → n < i + rk w) := by
  classical
  obtain ⟨w0, p, hp⟩ := hM
  have hn : 1 ≤ n := p.pos
  have hrk1 : rk w0 ≤ 1 := by
    rw [hrk w0, Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at ha hb
    obtain ⟨q1, rfl⟩ := ha
    obtain ⟨q2, rfl⟩ := hb
    rw [hp q1, hp q2]
  have hP : ∀ j : ℕ, ∃ l, ∃ w : List α, w.length = l ∧ min j (n - 1) + rk w ≤ n :=
    fun j => ⟨w0.length, w0, rfl, by omega⟩
  refine ⟨fun j => Nat.find (hP j), ?_, ?_, ?_, ?_⟩
  · show Nat.find (hP 0) = 0
    apply (Nat.find_eq_zero (hP 0)).2
    refine ⟨[], rfl, ?_⟩
    have : rk [] ≤ n := by
      rw [hrk]
      simpa using Finset.card_le_univ (Finset.univ : Finset (Fin n))
    simpa using this
  · intro i j hij
    obtain ⟨w, hw1, hw2⟩ := Nat.find_spec (hP j)
    apply Nat.find_min' (hP i)
    exact ⟨w, hw1, by omega⟩
  · intro i hi
    obtain ⟨w, hw1, hw2⟩ := Nat.find_spec (hP i)
    exact ⟨w, hw1, by omega⟩
  · intro i hi w hw
    have := Nat.find_min (hP i) hw
    simp only [not_exists, not_and] at this
    have h2 := this w rfl
    omega

/-- Counting lemma behind `gap_data`: `lam τ ≤ 2 ∑ i * #{j < τ : δ j ∈ {2i-1, 2i}}`. -/
lemma gap_weighted (lam : ℕ → ℕ) (hmono : Monotone lam) (hlam0 : lam 0 = 0) (r : ℕ) :
    ∀ τ : ℕ, (∀ j, j < τ → lam (j + 1) ≤ lam j + 2 * r) →
      lam τ ≤ 2 * ∑ i ∈ Finset.Icc 1 r,
        i * ((Finset.range τ).filter
          (fun j => lam (j + 1) - lam j = 2 * i - 1 ∨ lam (j + 1) - lam j = 2 * i)).card := by
  classical
  intro τ
  induction τ with
  | zero => intro _; simp [hlam0]
  | succ τ ih =>
    intro hδ
    have ih' := ih (fun j hj => hδ j (by omega))
    have hτ := hδ τ (by omega)
    have hm : lam τ ≤ lam (τ + 1) := hmono (Nat.le_succ τ)
    have hstep : ∀ i : ℕ, ((Finset.range τ).filter
          (fun j => lam (j + 1) - lam j = 2 * i - 1 ∨ lam (j + 1) - lam j = 2 * i)).card
        + (if (lam (τ + 1) - lam τ = 2 * i - 1 ∨ lam (τ + 1) - lam τ = 2 * i) then 1 else 0)
        ≤ ((Finset.range (τ + 1)).filter
          (fun j => lam (j + 1) - lam j = 2 * i - 1 ∨ lam (j + 1) - lam j = 2 * i)).card := by
      intro i
      rw [Finset.range_add_one, Finset.filter_insert]
      by_cases h : (lam (τ + 1) - lam τ = 2 * i - 1 ∨ lam (τ + 1) - lam τ = 2 * i)
      · rw [if_pos h, if_pos h, Finset.card_insert_of_notMem (by simp)]
      · rw [if_neg h, if_neg h]; simp
    by_cases h0 : lam (τ + 1) - lam τ = 0
    · have : lam τ ≤ 2 * ∑ i ∈ Finset.Icc 1 r, i * ((Finset.range (τ + 1)).filter
          (fun j => lam (j + 1) - lam j = 2 * i - 1 ∨ lam (j + 1) - lam j = 2 * i)).card := by
        refine le_trans ih' (Nat.mul_le_mul_left _ (Finset.sum_le_sum fun i _ => ?_))
        refine Nat.mul_le_mul_left _ (le_trans (Nat.le_add_right _ _) (hstep i))
      omega
    · set i0 := (lam (τ + 1) - lam τ + 1) / 2 with hi0
      have hi0r : i0 ∈ Finset.Icc 1 r := by
        rw [Finset.mem_Icc]; omega
      have hge : ∀ i ∈ Finset.Icc 1 r, i * (((Finset.range τ).filter
          (fun j => lam (j + 1) - lam j = 2 * i - 1 ∨ lam (j + 1) - lam j = 2 * i)).card
          + (if i = i0 then 1 else 0)) ≤ i * ((Finset.range (τ + 1)).filter
          (fun j => lam (j + 1) - lam j = 2 * i - 1 ∨ lam (j + 1) - lam j = 2 * i)).card := by
        intro i hi
        refine Nat.mul_le_mul_left _ (le_trans ?_ (hstep i))
        by_cases hii : i = i0
        · have : (lam (τ + 1) - lam τ = 2 * i - 1 ∨ lam (τ + 1) - lam τ = 2 * i) := by
            rw [hii]; omega
          rw [if_pos hii, if_pos this]
        · simp [hii]
      have hsum := Finset.sum_le_sum hge
      simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq' , hi0r, if_true] at hsum
      omega

/-- Gaps `δ j = lam (j+1) - lam j`; `ρ` = first big gap (`> n`) or `n - 1`; `s r` counts the
gaps `j < ρ` with `δ j ∈ {2r-1, 2r}`. -/
lemma gap_data (n : ℕ) (hn : 1 ≤ n) (lam : ℕ → ℕ) (hmono : Monotone lam) (hlam0 : lam 0 = 0) :
    ∃ (ρ : ℕ) (s : ℕ → ℝ), ρ ≤ n - 1 ∧ (∀ j, 0 ≤ s j) ∧
      ∑ j ∈ Finset.Icc 1 (n / 2), s j ≤ ρ ∧
      (∀ j, j < ρ → lam (j + 1) ≤ lam j + n) ∧
      (ρ = n - 1 ∨ lam ρ + n < lam (ρ + 1)) ∧
      (∀ r, 1 ≤ r → ∀ τ, τ ≤ ρ → (∀ j, j < τ → lam (j + 1) ≤ lam j + 2 * r) →
        (lam τ : ℝ) ≤ 2 * ∑ i ∈ Finset.Icc 1 r, (i : ℝ) * s i) := by
  classical
  have hex : ∃ j, j = n - 1 ∨ lam j + n < lam (j + 1) := ⟨n - 1, Or.inl rfl⟩
  obtain ⟨ρ, hρdef⟩ : ∃ ρ, ρ = Nat.find hex := ⟨_, rfl⟩
  have hρspec : ρ = n - 1 ∨ lam ρ + n < lam (ρ + 1) := by rw [hρdef]; exact Nat.find_spec hex
  have hρle : ρ ≤ n - 1 := by rw [hρdef]; exact Nat.find_min' hex (Or.inl rfl)
  have hρmin : ∀ j, j < ρ → ¬ (j = n - 1 ∨ lam j + n < lam (j + 1)) := by
    intro j hj; rw [hρdef] at hj; exact Nat.find_min hex hj
  obtain ⟨s, hs⟩ : ∃ s : ℕ → ℝ, ∀ i, s i = (((Finset.range ρ).filter
      (fun j => lam (j + 1) - lam j = 2 * i - 1 ∨ lam (j + 1) - lam j = 2 * i)).card : ℝ) :=
    ⟨_, fun _ => rfl⟩
  refine ⟨ρ, s, hρle, fun j => by rw [hs]; positivity, ?_, ?_, hρspec, ?_⟩
  · simp only [hs]
    rw [← Nat.cast_sum, Nat.cast_le]
    rw [← Finset.card_biUnion]
    · calc _ ≤ (Finset.range ρ).card := Finset.card_le_card (by
            intro j hj
            simp only [Finset.mem_biUnion, Finset.mem_filter] at hj
            obtain ⟨_, _, hj, _⟩ := hj
            exact hj)
        _ = ρ := Finset.card_range ρ
    · intro i hi i' hi' hne
      simp only [Finset.mem_Icc, Finset.coe_Icc, Set.mem_Icc] at hi hi'
      rw [Function.onFun, Finset.disjoint_left]
      intro j hj hj'
      simp only [Finset.mem_filter] at hj hj'
      omega
  · intro j hj
    have := hρmin j hj
    omega
  · intro r hr τ hτ hδ
    have h := gap_weighted lam hmono hlam0 r τ hδ
    have h' : (lam τ : ℝ) ≤ 2 * ∑ i ∈ Finset.Icc 1 r, (i : ℝ) * (((Finset.range τ).filter
          (fun j => lam (j + 1) - lam j = 2 * i - 1 ∨ lam (j + 1) - lam j = 2 * i)).card : ℝ) := by
      exact_mod_cast h
    refine le_trans h' (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (by norm_num))
    rw [hs]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono hτ))

-- ### Step 2 : one climbing step

/-- Pin-Frankl part of the climbing step (uses `H1`). -/
lemma climb_part1 (h1 : H1) {n : ℕ} {α : Type} [Finite α] (M : DFA α (Fin n)) (hM : M.IsSynchronizing)
    (rk : List α → ℕ) (hrk : ∀ w, rk w = (Finset.univ.image (fun q => M.evalFrom q w)).card)
    (lam : ℕ → ℕ)
    (hex : ∀ i, i ≤ n - 1 → ∃ w : List α, w.length = lam i ∧ i + rk w ≤ n)
    (hmin : ∀ i, i ≤ n - 1 → ∀ w : List α, w.length < lam i → n < i + rk w)
    (r : ℕ) (hr : r + 2 ≤ n) :
    2 * lam (r + 1) ≤ 2 * lam r + (r + 1) * (r + 2) := by
  obtain ⟨u, hul, hu⟩ := hex r (by omega)
  have hle : ∀ w : List α, r + 1 + rk w ≤ n → lam (r + 1) ≤ w.length := by
    intro w hw
    by_contra hlt
    have := hmin (r + 1) (by omega) w (by omega)
    omega
  by_cases hc : r + 1 + rk u ≤ n
  · have := hle u hc
    omega
  · have hru : rk u = n - r := by omega
    obtain ⟨w, hwl, hwr⟩ := h1 n M hM rk hrk u (by omega)
    have e1 : n + 1 - rk u = r + 1 := by omega
    have e2 : n + 2 - rk u = r + 2 := by omega
    rw [e1, e2, hul] at hwl
    have := hle w (by omega)
    nlinarith

/-- Shitov part of the climbing step (uses `H2`), for `ρ ≤ r`, `1 ≤ r`, `2r + 2 ≤ n`. -/
lemma climb_part2 (h2 : H2) {n : ℕ} {α : Type} [Finite α] (M : DFA α (Fin n)) (hM : M.IsSynchronizing)
    (rk : List α → ℕ) (hrk : ∀ w, rk w = (Finset.univ.image (fun q => M.evalFrom q w)).card)
    (lam : ℕ → ℕ) (hlam0 : lam 0 = 0) (hmono : Monotone lam)
    (hex : ∀ i, i ≤ n - 1 → ∃ w : List α, w.length = lam i ∧ i + rk w ≤ n)
    (hmin : ∀ i, i ≤ n - 1 → ∀ w : List α, w.length < lam i → n < i + rk w)
    (ρ : ℕ) (s : ℕ → ℝ) (hs0 : ∀ j, 0 ≤ s j)
    (hgap1 : ∀ j, j < ρ → lam (j + 1) ≤ lam j + n)
    (hgap2 : ρ = n - 1 ∨ lam ρ + n < lam (ρ + 1))
    (hW : ∀ r, 1 ≤ r → ∀ τ, τ ≤ ρ → (∀ j, j < τ → lam (j + 1) ≤ lam j + 2 * r) →
        (lam τ : ℝ) ≤ 2 * ∑ i ∈ Finset.Icc 1 r, (i : ℝ) * s i)
    (r : ℕ) (hρr : ρ ≤ r) (hr1 : 1 ≤ r) (hr : 2 * r + 2 ≤ n) :
    (lam (r + 1) : ℝ) ≤ lam r + 2 * ∑ i ∈ Finset.Icc 1 r, (i : ℝ) * s i + 2 * r := by
  classical
  have hle : ∀ w : List α, r + 1 + rk w ≤ n → lam (r + 1) ≤ w.length := by
    intro w hw
    by_contra hlt
    have := hmin (r + 1) (by omega) w (by omega)
    omega
  have hS0 : 0 ≤ ∑ i ∈ Finset.Icc 1 r, (i : ℝ) * s i :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (Nat.cast_nonneg _) (hs0 j))
  obtain ⟨u, hul, hu⟩ := hex r (by omega)
  by_cases hc : r + 1 + rk u ≤ n
  · have h := hle u hc
    have h' : (lam (r + 1) : ℝ) ≤ lam r := by rw [← hul]; exact_mod_cast h
    have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    linarith
  · have hgap2' : lam ρ + n < lam (ρ + 1) := by
      rcases hgap2 with h | h
      · omega
      · exact h
    have hexτ : ∃ j, lam j + 2 * r < lam (j + 1) := ⟨ρ, by omega⟩
    obtain ⟨τ, hτdef⟩ : ∃ τ, τ = Nat.find hexτ := ⟨_, rfl⟩
    have hτspec : lam τ + 2 * r < lam (τ + 1) := by rw [hτdef]; exact Nat.find_spec hexτ
    have hτρ : τ ≤ ρ := by rw [hτdef]; exact Nat.find_min' hexτ (by omega)
    have hτmin : ∀ j, j < τ → lam (j + 1) ≤ lam j + 2 * r := by
      intro j hj
      rw [hτdef] at hj
      have := Nat.find_min hexτ hj
      omega
    obtain ⟨v, hvl, hv⟩ := hex τ (by omega)
    have hvmin : ∀ v' : List α, v'.length ≤ v.length + 2 * (n - rk u) → rk v ≤ rk v' := by
      intro v' hv'
      have := hmin (τ + 1) (by omega) v' (by omega)
      omega
    obtain ⟨w, hwl, hwr⟩ := h2 n M hM rk hrk u v (by omega) (by omega) hvmin
    have e : n - rk u = r := by omega
    rw [e] at hwl hwr
    have h3 : lam (r + 1) ≤ lam r + lam τ + 2 * r := by
      have := hle w (by omega)
      omega
    have h4 := hW r hr1 τ hτρ hτmin
    have h3' : (lam (r + 1) : ℝ) ≤ lam r + lam τ + 2 * r := by exact_mod_cast h3
    linarith

/-- Combination of both climbing bounds into the `min` form. -/
lemma climb_combine (a b S : ℝ) (r : ℕ) (hS : 0 ≤ S)
    (p1 : 2 * a ≤ 2 * b + ((r : ℝ) + 1) * ((r : ℝ) + 2))
    (p2 : 1 ≤ r → a ≤ b + 2 * S + 2 * r) :
    a ≤ b + 2 * min ((r : ℝ) ^ 2 / 4) S + 2 * r + 1 := by
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  rcases Nat.eq_zero_or_pos r with h | h
  · subst h
    simp only [Nat.cast_zero] at p1 ⊢
    have : min ((0 : ℝ) ^ 2 / 4) S = 0 := by simp [hS]
    rw [this]; nlinarith
  · have p2' := p2 h
    rcases le_total ((r : ℝ) ^ 2 / 4) S with hm | hm
    · rw [min_eq_left hm]; nlinarith
    · rw [min_eq_right hm]; nlinarith

-- ### Step 3 : summation of phase 1

lemma sum_phase1 (lam : ℕ → ℕ) (S : ℕ → ℝ) (hS : ∀ r, 0 ≤ S r) (ρ k : ℕ) (hρk : ρ ≤ k)
    (hstep : ∀ r, ρ ≤ r → r < k →
      (lam (r + 1) : ℝ) ≤ lam r + 2 * min ((r : ℝ) ^ 2 / 4) (S r) + 2 * r + 1) :
    (lam k : ℝ) ≤ lam ρ + (k : ℝ) ^ 2 + 2 * ∑ r ∈ Finset.Icc ρ k, min ((r : ℝ) ^ 2 / 4) (S r) := by
  have hnn : ∀ r : ℕ, 0 ≤ min ((r : ℝ) ^ 2 / 4) (S r) := fun r => le_min (by positivity) (hS r)
  have key : (lam k : ℝ) ≤ lam ρ + (k : ℝ) ^ 2
      + 2 * ∑ r ∈ Finset.Ico ρ k, min ((r : ℝ) ^ 2 / 4) (S r) := by
    induction k, hρk using Nat.le_induction with
    | base => simp
    | succ k hk ih =>
      have ih' := ih (fun r h1 h2 => hstep r h1 (by omega))
      have hs := hstep k hk (by omega)
      rw [Finset.sum_Ico_succ_top hk]
      push_cast
      nlinarith
  have : ∑ r ∈ Finset.Ico ρ k, min ((r : ℝ) ^ 2 / 4) (S r)
      ≤ ∑ r ∈ Finset.Icc ρ k, min ((r : ℝ) ^ 2 / 4) (S r) :=
    Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => by
      simp only [Finset.mem_Ico, Finset.mem_Icc] at hx ⊢; omega) (fun r _ _ => hnn r)
  linarith

/-- Small values of `lam`: `lam m ≤ n²` for `m ≤ max ρ 1`, `m ≤ n - 1`. -/
lemma lam_small (lam : ℕ → ℕ) (n ρ m : ℕ) (hlam0 : lam 0 = 0) (hmono : Monotone lam)
    (hgap : ∀ j, j < ρ → lam (j + 1) ≤ lam j + n)
    (hρ : ρ ≤ n - 1)
    (hp1 : ∀ r, r + 2 ≤ n → 2 * lam (r + 1) ≤ 2 * lam r + (r + 1) * (r + 2))
    (hm : m ≤ max ρ 1) (hmn : m ≤ n - 1) : lam m ≤ n ^ 2 := by
  have hlr : ∀ t, t ≤ ρ → lam t ≤ n * t := by
    intro t
    induction t with
    | zero => intro _; simp [hlam0]
    | succ t ih =>
      intro ht
      have := hgap t (by omega)
      have := ih (by omega)
      nlinarith
  by_cases hmr : m ≤ ρ
  · have h1 := hmono hmr
    have h2 := hlr ρ le_rfl
    have : n * ρ ≤ n ^ 2 := by
      have : ρ ≤ n := by omega
      nlinarith [Nat.zero_le n]
    omega
  · have hm1 : m = 1 := by omega
    have hρ0 : ρ = 0 := by omega
    subst hm1
    have := hp1 0 (by omega)
    simp [hlam0] at this
    have : 1 ≤ n := by omega
    nlinarith

-- ### Step 4 : final Pin-Frankl phase

lemma phase_final (lam : ℕ → ℕ) (n k : ℕ) (hn : 1 ≤ n) (hk : k = n / 2)
    (hstep : ∀ r, k ≤ r → r + 2 ≤ n → 2 * lam (r + 1) ≤ 2 * lam r + (r + 1) * (r + 2)) :
    (lam (n - 1) : ℝ) ≤ lam k + 7 / 48 * (n : ℝ) ^ 3 := by
  have key : ∀ m, k ≤ m → m + 1 ≤ n →
      6 * lam m + k * (k + 1) * (k + 2) ≤ 6 * lam k + m * (m + 1) * (m + 2) := by
    intro m hkm
    induction m, hkm using Nat.le_induction with
    | base => intro _; omega
    | succ m hm ih =>
      intro hmn
      have h1 := ih (by omega)
      have h2 := hstep m hm (by omega)
      nlinarith
  have h := key (n - 1) (by omega) (by omega)
  have hc : (6 : ℝ) * lam (n - 1) + k * (k + 1) * (k + 2) ≤ 6 * lam k + ((n - 1 : ℕ) : ℝ) * (((n - 1 : ℕ) : ℝ) + 1) * (((n - 1 : ℕ) : ℝ) + 2) := by
    exact_mod_cast h
  have hn1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn]; simp
  rw [hn1] at hc
  have hk1 : (2 * k : ℝ) ≤ n := by exact_mod_cast (by omega : 2 * k ≤ n)
  have hk2 : (n : ℝ) ≤ 2 * k + 1 := by exact_mod_cast (by omega : n ≤ 2 * k + 1)
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith [mul_nonneg hk0 hk0, mul_nonneg hk0 (sub_nonneg.2 hn'), sq_nonneg ((n : ℝ) - 1), sq_nonneg ((k : ℝ))]

/-- A word of corank `≥ n - 1` is synchronizing. -/
lemma sync_of_rk {n : ℕ} {α : Type} (M : DFA α (Fin n)) (hn : 1 ≤ n)
    (rk : List α → ℕ) (hrk : ∀ w, rk w = (Finset.univ.image (fun q => M.evalFrom q w)).card)
    (w : List α) (hw : (n - 1) + rk w ≤ n) : M.IsSynchronizingWord w := by
  have hpos : 0 < rk w := by
    rw [hrk w]
    exact Finset.card_pos.2 ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ (⟨0, hn⟩ : Fin n))⟩
  have h1 : rk w = 1 := by omega
  rw [hrk w, Finset.card_eq_one] at h1
  obtain ⟨p, hp⟩ := h1
  refine ⟨p, fun q => ?_⟩
  have hq : M.evalFrom q w ∈ Finset.univ.image (fun q => M.evalFrom q w) :=
    Finset.mem_image_of_mem _ (Finset.mem_univ q)
  rw [hp] at hq
  simpa using hq

-- ### Step 5 : assembly for `Fin n`

lemma core_bound (h1 : H1) (h2 : H2) (g : ℝ → ℝ) (hg0 : ∀ x, 0 ≤ g x)
    (hg3 : ∀ (n ρ : ℕ) (s : ℕ → ℝ), 0 < n → 0 < ρ → 2 * ρ < n → (∀ j, 0 ≤ s j) →
      ∑ j ∈ Finset.Icc 1 (n / 2), s j ≤ ρ →
      ∑ r ∈ Finset.Icc ρ (n / 2),
          min ((r : ℝ) ^ 2 / 4) (∑ j ∈ Finset.Icc 1 r, (j : ℝ) * s j)
        ≤ 15625 / 1597536 * (n : ℝ) ^ 3 + g (n : ℝ))
    (n : ℕ) {α : Type} [Finite α] (M : DFA α (Fin n)) (hM : M.IsSynchronizing) :
    ∃ w : List α, M.IsSynchronizingWord w ∧
      (w.length : ℝ) ≤ (7 / 48 + 2 * 15625 / 1597536) * (n : ℝ) ^ 3
        + (3 * (n : ℝ) ^ 2 + 2 * g (n : ℝ)) := by
  have hn : 1 ≤ n := by
    obtain ⟨w, p, _⟩ := hM
    exact p.pos
  obtain ⟨rk, hrk⟩ : ∃ rk : List α → ℕ,
      ∀ w, rk w = (Finset.univ.image (fun q => M.evalFrom q w)).card :=
    ⟨fun w => (Finset.univ.image (fun q => M.evalFrom q w)).card, fun _ => rfl⟩
  obtain ⟨lam, hlam0, hmono, hex, hmin⟩ := lam_exists M hM rk hrk
  obtain ⟨ρ, s, hρ, hs0, hsum, hgap1, hgap2, hW⟩ := gap_data n hn lam hmono hlam0
  have hp1 : ∀ r, r + 2 ≤ n → 2 * lam (r + 1) ≤ 2 * lam r + (r + 1) * (r + 2) :=
    fun r hr => climb_part1 h1 M hM rk hrk lam hex hmin r hr
  obtain ⟨k, hk⟩ : ∃ k, k = n / 2 := ⟨_, rfl⟩
  have hfin := phase_final lam n k hn hk (fun r _ hr2 => hp1 r hr2)
  have hS0 : ∀ r : ℕ, 0 ≤ ∑ j ∈ Finset.Icc 1 r, (j : ℝ) * s j :=
    fun r => Finset.sum_nonneg (fun j _ => mul_nonneg (Nat.cast_nonneg _) (hs0 j))
  have hgn : 0 ≤ g (n : ℝ) := hg0 _
  have hc3 : 0 ≤ (n : ℝ) ^ 3 := by positivity
  have hlamk : (lam k : ℝ) ≤ (n : ℝ) ^ 2 + (k : ℝ) ^ 2
      + 2 * (15625 / 1597536 * (n : ℝ) ^ 3 + g (n : ℝ)) := by
    by_cases hlt : max ρ 1 < k
    · have h3 := hg3 n (max ρ 1) s (by omega) (by omega) (by omega) hs0
        (le_trans hsum (by exact_mod_cast le_max_left ρ 1))
      rw [← hk] at h3
      have hs1 := sum_phase1 lam (fun r => ∑ j ∈ Finset.Icc 1 r, (j : ℝ) * s j) hS0 (max ρ 1) k
        hlt.le (fun r hr1 hr2 => by
          have q1 : 2 * (lam (r + 1) : ℝ) ≤ 2 * lam r + ((r : ℝ) + 1) * ((r : ℝ) + 2) := by
            exact_mod_cast hp1 r (by omega)
          exact climb_combine _ _ _ r (hS0 r) q1 (fun h =>
            climb_part2 h2 M hM rk hrk lam hlam0 hmono hex hmin ρ s hs0 hgap1 hgap2 hW r
              (by omega) h (by omega)))
      have hsm : (lam (max ρ 1) : ℝ) ≤ (n : ℝ) ^ 2 := by
        exact_mod_cast lam_small lam n ρ (max ρ 1) hlam0 hmono hgap1 hρ hp1 le_rfl (by omega)
      linarith
    · have hsm : (lam k : ℝ) ≤ (n : ℝ) ^ 2 := by
        exact_mod_cast lam_small lam n ρ k hlam0 hmono hgap1 hρ hp1 (by omega) (by omega)
      have : 0 ≤ (k : ℝ) ^ 2 := by positivity
      linarith
  obtain ⟨w, hwl, hw⟩ := hex (n - 1) le_rfl
  refine ⟨w, sync_of_rk M hn rk hrk w (by omega), ?_⟩
  rw [hwl]
  have hkn : (k : ℝ) ≤ n := by exact_mod_cast (by omega : k ≤ n)
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hkk : (k : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by nlinarith
  have hn2 : 0 ≤ (n : ℝ) ^ 2 := by positivity
  linarith

/-- The error term `3x² + 2g(x)` is `o(x³)`. -/
lemma f_littleO (g : ℝ → ℝ) (hg : g =o[atTop] (fun x : ℝ => x ^ 3)) :
    (fun x : ℝ => 3 * x ^ 2 + 2 * g x) =o[atTop] (fun x : ℝ => x ^ 3) := by
  have h : (fun x : ℝ => x ^ 2) =o[atTop] (fun x : ℝ => x ^ 3) :=
    isLittleO_pow_pow_atTop_of_lt (by norm_num)
  exact (h.const_mul_left 3).add (hg.const_mul_left 2)

theorem main : H1 → H2 → H3 → type_of% @CernyConjecture.shitov_upper_bound := by
  intro h1 h2 h3
  obtain ⟨g, hg, hg0, hg3⟩ := h3
  refine ⟨fun x => 3 * x ^ 2 + 2 * g x, f_littleO g hg, ?_⟩
  intro α σ _ M hM
  have := reduce_to_fin
    (fun n => (7 / 48 + 2 * 15625 / 1597536) * (n : ℝ) ^ 3 + (3 * (n : ℝ) ^ 2 + 2 * g n))
    (fun n β _ M hM => core_bound h1 h2 g hg0 hg3 n M hM) M hM
  exact this

end OMA.R_CernyConjecture_shitov_upper_bound_R1

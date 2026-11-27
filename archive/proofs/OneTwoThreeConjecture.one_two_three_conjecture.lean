import FormalConjectures.Paper.OneTwoThreeConjecture
section OTTCore
open Finset SimpleGraph Classical
namespace OTT
variable {V : Type*} [Fintype V]

/-- degré pondéré (voisinage) ; pont avec `OneTwoThreeConjecture.weightedDegree` = lemme P0. -/
noncomputable def sdeg (G : SimpleGraph V) (w : Sym2 V → ℕ) (v : V) : ℕ :=
  ∑ u ∈ univ.filter (G.Adj v), w s(v, u)
def Proper (G : SimpleGraph V) (w : Sym2 V → ℕ) : Prop :=
  ∀ u v, G.Adj u v → sdeg G w u ≠ sdeg G w v
def Wt3 (G : SimpleGraph V) (w : Sym2 V → ℕ) : Prop := ∀ e ∈ G.edgeSet, 1 ≤ w e ∧ w e ≤ 3
/-- G(R,B) : sous-graphe biparti. -/
def bip (G : SimpleGraph V) (R B : Finset V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ ((u ∈ R ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ R))
  symm := ⟨fun u v h => ⟨h.1.symm, h.2.symm.imp (fun a => ⟨a.2, a.1⟩) (fun a => ⟨a.2, a.1⟩)⟩⟩
  loopless := ⟨fun u h => G.loopless.irrefl u h.1⟩
/-- Définition 6 (p.7) -/
structure Good (G : SimpleGraph V) (R B : Finset V) : Prop where
  disj : Disjoint R B
  indep : ∀ u ∈ R, ∀ v ∈ R, ¬ G.Adj u v
  conn : ∀ u ∈ R ∪ B, ∀ v ∈ R ∪ B, (bip G R B).Reachable u v
  even : Even B.card

noncomputable def A_cap (E : Finset (Sym2 V)) (A : Finset V) : ℕ :=
  (E.filter (fun e => ∃ x ∈ A, ∃ y ∉ A, e = s(x, y))).card

lemma A_cr_mk (A : Finset V) (a b : V) :
    (∃ x ∈ A, ∃ y ∉ A, s(a, b) = s(x, y)) ↔ (a ∈ A ∧ b ∉ A) ∨ (b ∈ A ∧ a ∉ A) := by
  constructor
  · rintro ⟨x, hx, y, hy, h⟩
    rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨hx, hy⟩
    · exact Or.inr ⟨hx, hy⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨a, h1, b, h2, rfl⟩
    · exact ⟨b, h1, a, h2, Sym2.eq_swap⟩

lemma A_cap_eq (E : Finset (Sym2 V)) (A : Finset V) :
    (A_cap E A : ℤ) = ∑ e ∈ E, if (∃ x ∈ A, ∃ y ∉ A, e = s(x, y)) then (1:ℤ) else 0 := by
  unfold A_cap
  rw [Finset.card_filter]; push_cast; rfl

lemma A_edge_ineq (A B : Finset V) (e : Sym2 V) :
    (if (∃ x ∈ A ∩ B, ∃ y ∉ A ∩ B, e = s(x, y)) then (1:ℤ) else 0) +
    (if (∃ x ∈ A ∪ B, ∃ y ∉ A ∪ B, e = s(x, y)) then (1:ℤ) else 0) ≤
    (if (∃ x ∈ A, ∃ y ∉ A, e = s(x, y)) then (1:ℤ) else 0) +
    (if (∃ x ∈ B, ∃ y ∉ B, e = s(x, y)) then (1:ℤ) else 0) := by
  induction e using Sym2.ind with
  | _ a b =>
  simp only [A_cr_mk]
  simp only [mem_inter, mem_union]
  by_cases ha : a ∈ A <;> by_cases hb : b ∈ A <;> by_cases ha' : a ∈ B <;>
    by_cases hb' : b ∈ B <;> simp [ha, hb, ha', hb']

lemma A_submod (E : Finset (Sym2 V)) (A B : Finset V) (x y : V) (hxA : x ∈ A) (hxB : x ∉ B)
    (hyB : y ∈ B) (hyA : y ∉ A) (he : s(x, y) ∈ E) :
    A_cap E (A ∩ B) + A_cap E (A ∪ B) + 2 ≤ A_cap E A + A_cap E B := by
  have key : ∑ e ∈ E, ((if (∃ x ∈ A ∩ B, ∃ y ∉ A ∩ B, e = s(x, y)) then (1:ℤ) else 0) +
        (if (∃ x ∈ A ∪ B, ∃ y ∉ A ∪ B, e = s(x, y)) then (1:ℤ) else 0) +
        (if e = s(x, y) then 2 else 0)) ≤
      ∑ e ∈ E, ((if (∃ x ∈ A, ∃ y ∉ A, e = s(x, y)) then (1:ℤ) else 0) +
        (if (∃ x ∈ B, ∃ y ∉ B, e = s(x, y)) then (1:ℤ) else 0)) := by
    apply Finset.sum_le_sum
    intro e _
    by_cases hee : e = s(x, y)
    · subst hee
      simp only [A_cr_mk]
      simp only [mem_inter, mem_union]
      simp [hxA, hxB, hyB, hyA]
    · simp only [hee, if_false, add_zero]; exact A_edge_ineq A B e
  have h2 : (∑ e ∈ E, (if e = s(x, y) then (2:ℤ) else 0)) = 2 := by
    rw [Finset.sum_ite_eq' E s(x, y)]; simp [he]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, h2, Finset.sum_add_distrib,
    ← A_cap_eq, ← A_cap_eq, ← A_cap_eq, ← A_cap_eq] at key
  exact_mod_cast key

lemma A_cap_insert (E : Finset (Sym2 V)) (e : Sym2 V) (he : e ∉ E) (A : Finset V) :
    (A_cap (insert e E) A : ℤ) =
      A_cap E A + (if (∃ x ∈ A, ∃ y ∉ A, e = s(x, y)) then 1 else 0) := by
  rw [A_cap_eq, A_cap_eq, Finset.sum_insert he]; ring

lemma A_step (E : Finset (Sym2 V)) (x y : V) (he : s(x, y) ∉ E) (d : V → ℤ)
    (hcut : ∀ A : Finset V, ∑ v ∈ A, d v ≤ (A_cap (insert s(x, y) E) A : ℤ)) :
    (∀ A : Finset V, ∑ v ∈ A, d v ≤ (A_cap E A : ℤ)) ∨
    (∀ A : Finset V, ∑ v ∈ A, (d v - (if v = x then 1 else 0) + (if v = y then 1 else 0)) ≤
      (A_cap E A : ℤ)) ∨
    (∀ A : Finset V, ∑ v ∈ A, (d v + (if v = x then 1 else 0) - (if v = y then 1 else 0)) ≤
      (A_cap E A : ℤ)) := by
  by_contra hcon
  simp only [not_or, not_forall, not_le] at hcon
  obtain ⟨⟨A0, h0⟩, ⟨Ap, hp⟩, ⟨Am, hm⟩⟩ := hcon
  have s1 : ∀ A : Finset V, ∑ v ∈ A, (d v - (if v = x then 1 else 0) + (if v = y then 1 else 0))
      = ∑ v ∈ A, d v - (if x ∈ A then 1 else 0) + (if y ∈ A then 1 else 0) := by
    intro A; simp [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have s2 : ∀ A : Finset V, ∑ v ∈ A, (d v + (if v = x then 1 else 0) - (if v = y then 1 else 0))
      = ∑ v ∈ A, d v + (if x ∈ A then 1 else 0) - (if y ∈ A then 1 else 0) := by
    intro A; simp [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [s1] at hp; rw [s2] at hm
  have ci : ∀ A : Finset V, (A_cap (insert s(x, y) E) A : ℤ) =
      A_cap E A + (if (x ∈ A ∧ y ∉ A) ∨ (y ∈ A ∧ x ∉ A) then 1 else 0) := by
    intro A; rw [A_cap_insert E _ he]; simp only [A_cr_mk]
  have F0 : ((x ∈ A0 ∧ y ∉ A0) ∨ (y ∈ A0 ∧ x ∉ A0)) ∧
      ∑ v ∈ A0, d v = (A_cap (insert s(x, y) E) A0 : ℤ) := by
    have c := hcut A0
    rw [ci] at c ⊢
    by_cases hc : (x ∈ A0 ∧ y ∉ A0) ∨ (y ∈ A0 ∧ x ∉ A0)
    · rw [if_pos hc] at c ⊢; exact ⟨hc, by omega⟩
    · exfalso; rw [if_neg hc] at c; omega
  have Fp : (y ∈ Ap ∧ x ∉ Ap) ∧ (A_cap (insert s(x, y) E) Ap : ℤ) ≤ ∑ v ∈ Ap, d v + 1 := by
    have c := hcut Ap
    rw [ci] at c ⊢
    by_cases hx : x ∈ Ap <;> by_cases hy : y ∈ Ap <;> simp [hx, hy] at c hp ⊢ <;> omega
  have Fm : (x ∈ Am ∧ y ∉ Am) ∧ (A_cap (insert s(x, y) E) Am : ℤ) ≤ ∑ v ∈ Am, d v + 1 := by
    have c := hcut Am
    rw [ci] at c ⊢
    by_cases hx : x ∈ Am <;> by_cases hy : y ∈ Am <;> simp [hx, hy] at c hm ⊢ <;> omega
  rcases F0.1 with ⟨hx0, hy0⟩ | ⟨hy0, hx0⟩
  · have hs := A_submod (insert s(x, y) E) A0 Ap x y hx0 Fp.1.2 Fp.1.1 hy0 (mem_insert_self _ _)
    have c1 := hcut (A0 ∩ Ap)
    have c2 := hcut (A0 ∪ Ap)
    have c3 : ∑ v ∈ A0 ∪ Ap, d v + ∑ v ∈ A0 ∩ Ap, d v = ∑ v ∈ A0, d v + ∑ v ∈ Ap, d v := Finset.sum_union_inter
    have := F0.2; have := Fp.2
    omega
  · have hs := A_submod (insert s(x, y) E) Am A0 x y Fm.1.1 hx0 hy0 Fm.1.2 (mem_insert_self _ _)
    have c1 := hcut (Am ∩ A0)
    have c2 := hcut (Am ∪ A0)
    have c3 : ∑ v ∈ Am ∪ A0, d v + ∑ v ∈ Am ∩ A0, d v = ∑ v ∈ Am, d v + ∑ v ∈ A0, d v := Finset.sum_union_inter
    have := F0.2; have := Fm.2
    omega

lemma A_add_edge (E : Finset (Sym2 V)) (x y : V) (hxy : x ≠ y) (he : s(x, y) ∉ E) (c : ℤ)
    (hc : |c| = 1) (d' : V → ℤ) (ψ : V → V → ℤ) (h1 : ∀ a b, ψ a b = - ψ b a)
    (h2 : ∀ a b, |ψ a b| ≤ 1) (h3 : ∀ a b, ψ a b ≠ 0 → s(a, b) ∈ E)
    (h4 : ∀ a, ∑ b, ψ a b = d' a) :
    ∃ ψ' : V → V → ℤ, (∀ a b, ψ' a b = - ψ' b a) ∧ (∀ a b, |ψ' a b| ≤ 1) ∧
      (∀ a b, ψ' a b ≠ 0 → s(a, b) ∈ insert s(x, y) E) ∧
      ∀ a, ∑ b, ψ' a b = d' a + c * (if a = x then 1 else 0) - c * (if a = y then 1 else 0) := by
  have z1 : ψ x y = 0 := by by_contra h; exact he (h3 _ _ h)
  have z2 : ψ y x = 0 := by
    by_contra h; exact he (by rw [Sym2.eq_swap]; exact h3 _ _ h)
  have hyx : y ≠ x := fun h => hxy h.symm
  refine ⟨fun a b => ψ a b + (if a = x ∧ b = y then c else 0) - (if a = y ∧ b = x then c else 0),
    ?_, ?_, ?_, ?_⟩
  · intro a b
    have := h1 a b
    by_cases p1 : a = x ∧ b = y
    · obtain ⟨rfl, rfl⟩ := p1
      simp [hxy, hyx]; omega
    · by_cases p2 : a = y ∧ b = x
      · obtain ⟨rfl, rfl⟩ := p2
        simp [hxy, hyx]; omega
      · have q1 : ¬ (b = x ∧ a = y) := fun h => p2 ⟨h.2, h.1⟩
        have q2 : ¬ (b = y ∧ a = x) := fun h => p1 ⟨h.2, h.1⟩
        simp only [p1, p2, q1, q2, if_false]; omega
  · intro a b
    by_cases p1 : a = x ∧ b = y
    · obtain ⟨rfl, rfl⟩ := p1
      simp [hxy, hyx, z1]; exact hc.le
    · by_cases p2 : a = y ∧ b = x
      · obtain ⟨rfl, rfl⟩ := p2
        simp [hxy, hyx, z2]; exact hc.le
      · simp only [p1, p2, if_false]; simpa using h2 a b
  · intro a b hab
    by_cases p1 : a = x ∧ b = y
    · obtain ⟨rfl, rfl⟩ := p1; exact mem_insert_self _ _
    · by_cases p2 : a = y ∧ b = x
      · obtain ⟨rfl, rfl⟩ := p2; rw [Sym2.eq_swap]; exact mem_insert_self _ _
      · simp only [p1, p2, if_false] at hab
        exact mem_insert_of_mem (h3 a b (by simpa using hab))
  · intro a
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, h4 a]
    have e1 : ∑ b, (if a = x ∧ b = y then c else 0) = c * (if a = x then 1 else 0) := by
      by_cases h : a = x
      · subst h; simp
      · simp [h]
    have e2 : ∑ b, (if a = y ∧ b = x then c else 0) = c * (if a = y then 1 else 0) := by
      by_cases h : a = y
      · subst h; simp
      · simp [h]
    rw [e1, e2]

theorem flow_demand (E : Finset (Sym2 V)) (d : V → ℤ) (hd : ∑ v, d v = 0)
    (hcut : ∀ A : Finset V, ∑ v ∈ A, d v ≤
      (E.filter (fun e => ∃ x ∈ A, ∃ y ∉ A, e = s(x, y))).card) :
    ∃ ψ : V → V → ℤ, (∀ x y, ψ x y = - ψ y x) ∧ (∀ x y, |ψ x y| ≤ 1) ∧
      (∀ x y, ψ x y ≠ 0 → s(x, y) ∈ E) ∧ ∀ x, ∑ y, ψ x y = d x := by
  suffices H : ∀ (E : Finset (Sym2 V)) (d : V → ℤ), ∑ v, d v = 0 →
      (∀ A : Finset V, ∑ v ∈ A, d v ≤ (A_cap E A : ℤ)) →
      ∃ ψ : V → V → ℤ, (∀ x y, ψ x y = - ψ y x) ∧ (∀ x y, |ψ x y| ≤ 1) ∧
        (∀ x y, ψ x y ≠ 0 → s(x, y) ∈ E) ∧ ∀ x, ∑ y, ψ x y = d x from
    H E d hd (fun A => hcut A)
  intro E
  induction E using Finset.induction_on with
  | empty =>
    intro d hd hcut
    have hle : ∀ v, d v ≤ 0 := fun v => by
      have := hcut {v}; simpa [A_cap] using this
    have hz : ∀ v, d v = 0 := fun v =>
      (Finset.sum_eq_zero_iff_of_nonpos (fun v _ => hle v)).mp hd v (mem_univ v)
    exact ⟨fun _ _ => 0, by simp, by simp, by simp, fun x => by simp [hz x]⟩
  | insert e E he ih =>
    intro d hd hcut
    induction e using Sym2.ind with
    | _ x y =>
    by_cases hxy : x = y
    · subst hxy
      have hc : ∀ A : Finset V, ∑ v ∈ A, d v ≤ (A_cap E A : ℤ) := by
        intro A; have := hcut A; rw [A_cap_insert E _ he] at this
        simp only [A_cr_mk] at this; simpa using this
      obtain ⟨ψ, h1, h2, h3, h4⟩ := ih d hd hc
      exact ⟨ψ, h1, h2, fun a b h => mem_insert_of_mem (h3 a b h), h4⟩
    · rcases A_step E x y he d hcut with h | h | h
      · obtain ⟨ψ, h1, h2, h3, h4⟩ := ih d hd h
        exact ⟨ψ, h1, h2, fun a b h => mem_insert_of_mem (h3 a b h), h4⟩
      · have hd' : ∑ v, (d v - (if v = x then (1:ℤ) else 0) + (if v = y then 1 else 0)) = 0 := by
          simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, hd]
        obtain ⟨ψ, h1, h2, h3, h4⟩ := ih _ hd' h
        obtain ⟨ψ', g1, g2, g3, g4⟩ := A_add_edge E x y hxy he 1 (by norm_num) _ ψ h1 h2 h3 h4
        refine ⟨ψ', g1, g2, g3, fun a => ?_⟩
        rw [g4 a]; ring
      · have hd' : ∑ v, (d v + (if v = x then (1:ℤ) else 0) - (if v = y then 1 else 0)) = 0 := by
          simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, hd]
        obtain ⟨ψ, h1, h2, h3, h4⟩ := ih _ hd' h
        obtain ⟨ψ', g1, g2, g3, g4⟩ := A_add_edge E x y hxy he (-1) (by norm_num) _ ψ h1 h2 h3 h4
        refine ⟨ψ', g1, g2, g3, fun a => ?_⟩
        rw [g4 a]; ring

-- ===================== L4b (coupe max) =====================

noncomputable def A_Eg (G : SimpleGraph V) : Finset (Sym2 V) := univ.filter (fun e => e ∈ G.edgeSet)

lemma A_mem_Eg (G : SimpleGraph V) (a b : V) : s(a, b) ∈ A_Eg G ↔ G.Adj a b := by
  simp [A_Eg]

lemma A_cr_swap (S A : Finset V) (e : Sym2 V) :
    (if (∃ x ∈ (S \ A) ∪ (A \ S), ∃ y ∉ (S \ A) ∪ (A \ S), e = s(x, y)) then (1:ℤ) else 0) =
    (if (∃ x ∈ S, ∃ y ∉ S, e = s(x, y)) then (1:ℤ) else 0) +
    (if (∃ x ∈ A, ∃ y ∉ A, e = s(x, y)) then (1:ℤ) else 0) -
    2 * (if (∃ x ∈ S, ∃ y ∉ S, e = s(x, y)) ∧ (∃ x ∈ A, ∃ y ∉ A, e = s(x, y)) then (1:ℤ) else 0) := by
  induction e using Sym2.ind with
  | _ a b =>
  simp only [A_cr_mk]
  simp only [mem_union, mem_sdiff]
  by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;> by_cases ha' : a ∈ A <;>
    by_cases hb' : b ∈ A <;> simp [ha, hb, ha', hb']

lemma A_maxcut_cmp (E : Finset (Sym2 V)) (S : Finset V)
    (hmax : ∀ S' : Finset V, A_cap E S' ≤ A_cap E S) (A : Finset V) :
    (∑ e ∈ E, (if ¬ (∃ x ∈ S, ∃ y ∉ S, e = s(x, y)) ∧ (∃ x ∈ A, ∃ y ∉ A, e = s(x, y))
        then (1:ℤ) else 0)) ≤ (A_cap (E.filter (fun e => ∃ x ∈ S, ∃ y ∉ S, e = s(x, y))) A : ℤ) := by
  have h1 : (A_cap E ((S \ A) ∪ (A \ S)) : ℤ) ≤ A_cap E S := by exact_mod_cast hmax _
  rw [A_cap_eq, A_cap_eq] at h1
  simp only [A_cr_swap, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at h1
  rw [A_cap_eq, Finset.sum_filter]
  have e1 : ∀ e : Sym2 V, (if ¬ (∃ x ∈ S, ∃ y ∉ S, e = s(x, y)) ∧ (∃ x ∈ A, ∃ y ∉ A, e = s(x, y))
        then (1:ℤ) else 0) = (if (∃ x ∈ A, ∃ y ∉ A, e = s(x, y)) then (1:ℤ) else 0) -
        (if (∃ x ∈ S, ∃ y ∉ S, e = s(x, y)) ∧ (∃ x ∈ A, ∃ y ∉ A, e = s(x, y)) then (1:ℤ) else 0) := by
    intro e; by_cases p : (∃ x ∈ S, ∃ y ∉ S, e = s(x, y)) <;>
      by_cases q : (∃ x ∈ A, ∃ y ∉ A, e = s(x, y)) <;> simp [p, q]
  have e2 : ∀ e : Sym2 V, (if (∃ x ∈ S, ∃ y ∉ S, e = s(x, y)) then
        (if (∃ x ∈ A, ∃ y ∉ A, e = s(x, y)) then (1:ℤ) else 0) else 0) =
      (if (∃ x ∈ S, ∃ y ∉ S, e = s(x, y)) ∧ (∃ x ∈ A, ∃ y ∉ A, e = s(x, y)) then (1:ℤ) else 0) := by
    intro e; by_cases p : (∃ x ∈ S, ∃ y ∉ S, e = s(x, y)) <;>
      by_cases q : (∃ x ∈ A, ∃ y ∉ A, e = s(x, y)) <;> simp [p, q]
  simp only [e1, e2, Finset.sum_sub_distrib]
  linarith

lemma A_cut_cond (G : SimpleGraph V) (S : Finset V)
    (hmax : ∀ S' : Finset V, A_cap (A_Eg G) S' ≤ A_cap (A_Eg G) S)
    (N : V → Finset V) (τ : V → ℤ) (hτ : ∀ v, |τ v| ≤ 1)
    (hN : ∀ v, ∀ u ∈ N v, G.Adj u v ∧ (u ∈ S ↔ v ∈ S))
    (hno : ∀ u v, v ∈ N u → u ∈ N v → False) (A : Finset V) :
    ∑ v ∈ A, (((N v).card : ℤ) * τ v - ∑ u, (if v ∈ N u then τ u else 0)) ≤
      (A_cap ((A_Eg G).filter (fun e => ∃ x ∈ S, ∃ y ∉ S, e = s(x, y))) A : ℤ) := by
  have e1 : ∑ v ∈ A, (((N v).card : ℤ) * τ v - ∑ u, (if v ∈ N u then τ u else 0)) =
      ∑ u, ∑ w ∈ N u, τ u * ((if u ∈ A then (1:ℤ) else 0) - (if w ∈ A then 1 else 0)) := by
    have a1 : ∑ v ∈ A, ((N v).card : ℤ) * τ v =
        ∑ u, ∑ w ∈ N u, τ u * (if u ∈ A then (1:ℤ) else 0) := by
      have : ∑ v ∈ A, ((N v).card : ℤ) * τ v = ∑ v, if v ∈ A then ((N v).card : ℤ) * τ v else 0 := by
        rw [Finset.sum_ite_mem, Finset.univ_inter]
      rw [this]
      refine Finset.sum_congr rfl (fun u _ => ?_)
      by_cases h : u ∈ A <;> simp [h, mul_comm]
    have a2 : ∑ v ∈ A, ∑ u, (if v ∈ N u then τ u else 0) =
        ∑ u, ∑ w ∈ N u, τ u * (if w ∈ A then (1:ℤ) else 0) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun u _ => ?_)
      rw [Finset.sum_ite_mem A (N u) (fun _ => τ u)]
      simp only [mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_mem (N u) A (fun _ => τ u), Finset.inter_comm]
    rw [Finset.sum_sub_distrib, a1, a2, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    ring
  rw [e1]
  have e2 : ∀ u w, τ u * ((if u ∈ A then (1:ℤ) else 0) - (if w ∈ A then 1 else 0)) ≤
      (if (u ∈ A ∧ w ∉ A) ∨ (w ∈ A ∧ u ∉ A) then (1:ℤ) else 0) := by
    intro u w
    have := abs_le.mp (hτ u)
    by_cases hu : u ∈ A <;> by_cases hw : w ∈ A <;> simp [hu, hw] <;> linarith [this.1, this.2]
  calc _ ≤ ∑ u, ∑ w ∈ N u, (if (u ∈ A ∧ w ∉ A) ∨ (w ∈ A ∧ u ∉ A) then (1:ℤ) else 0) :=
        Finset.sum_le_sum (fun u _ => Finset.sum_le_sum (fun w _ => e2 u w))
    _ = (((univ ×ˢ univ : Finset (V × V)).filter
          (fun p => p.2 ∈ N p.1 ∧ ((p.1 ∈ A ∧ p.2 ∉ A) ∨ (p.2 ∈ A ∧ p.1 ∉ A)))).card : ℤ) := by
        rw [Finset.card_filter, Finset.sum_product]
        push_cast
        refine Finset.sum_congr rfl (fun u _ => ?_)
        simp_rw [ite_and]
        rw [Finset.sum_ite_mem, Finset.univ_inter]
    _ ≤ _ := by
        have hinj : ((univ ×ˢ univ : Finset (V × V)).filter
            (fun p => p.2 ∈ N p.1 ∧ ((p.1 ∈ A ∧ p.2 ∉ A) ∨ (p.2 ∈ A ∧ p.1 ∉ A)))).card ≤
            ((A_Eg G).filter (fun e => ¬ (∃ x ∈ S, ∃ y ∉ S, e = s(x, y)) ∧
              (∃ x ∈ A, ∃ y ∉ A, e = s(x, y)))).card := by
          apply Finset.card_le_card_of_injOn (fun p => s(p.1, p.2))
          · intro p hp
            simp only [Finset.mem_coe, Finset.mem_filter, mem_product, mem_univ, true_and] at hp
            rw [Finset.mem_coe, Finset.mem_filter]
            refine ⟨(A_mem_Eg G _ _).mpr (hN p.1 p.2 hp.1).1.symm, ?_, ?_⟩
            · rw [A_cr_mk]; have := (hN p.1 p.2 hp.1).2; tauto
            · rw [A_cr_mk]; exact hp.2
          · intro p hp q hq h
            simp only [Finset.mem_coe, Finset.mem_filter, mem_product, mem_univ, true_and] at hp hq
            rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact Prod.ext h1 h2
            · exfalso
              have hq1 := hq.1
              rw [← h1, ← h2] at hq1
              exact hno p.1 p.2 hp.1 hq1
        calc _ ≤ (((A_Eg G).filter (fun e => ¬ (∃ x ∈ S, ∃ y ∉ S, e = s(x, y)) ∧
              (∃ x ∈ A, ∃ y ∉ A, e = s(x, y)))).card : ℤ) := by exact_mod_cast hinj
          _ = ∑ e ∈ A_Eg G, (if ¬ (∃ x ∈ S, ∃ y ∉ S, e = s(x, y)) ∧
              (∃ x ∈ A, ∃ y ∉ A, e = s(x, y)) then (1:ℤ) else 0) := by
            rw [Finset.card_filter]; push_cast; rfl
          _ ≤ _ := A_maxcut_cmp _ S hmax A

theorem A_L4b (G : SimpleGraph V) (S : Finset V)
    (hmax : ∀ S' : Finset V, A_cap (A_Eg G) S' ≤ A_cap (A_Eg G) S)
    (N : V → Finset V) (τ : V → ℤ) (hτ : ∀ v, |τ v| ≤ 1)
    (hN : ∀ v, ∀ u ∈ N v, G.Adj u v ∧ (u ∈ S ↔ v ∈ S))
    (hno : ∀ u v, v ∈ N u → u ∈ N v → False) :
    ∃ ψ : V → V → ℤ, (∀ x y, ψ x y = - ψ y x) ∧ (∀ x y, |ψ x y| ≤ 1) ∧
      (∀ x y, ψ x y ≠ 0 → G.Adj x y ∧ ¬ (x ∈ S ↔ y ∈ S)) ∧
      ∀ v, ∑ u, ψ v u = ((N v).card : ℤ) * τ v - ∑ u, (if v ∈ N u then τ u else 0) := by
  have hsw : ∀ (w : V → ℤ), ∑ v, ∑ u, (if v ∈ N u then w u else 0) = ∑ u, ((N u).card : ℤ) * w u := by
    intro w
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    simp [Finset.sum_ite_mem, mul_comm]
  obtain ⟨ψ, h1, h2, h3, h4⟩ := flow_demand ((A_Eg G).filter (fun e => ∃ x ∈ S, ∃ y ∉ S, e = s(x, y)))
    (fun v => ((N v).card : ℤ) * τ v - ∑ u, (if v ∈ N u then τ u else 0))
    (by simp only [Finset.sum_sub_distrib, hsw]; ring)
    (fun A => A_cut_cond G S hmax N τ hτ hN hno A)
  refine ⟨ψ, h1, h2, fun x y h => ?_, h4⟩
  have := h3 x y h
  rw [Finset.mem_filter] at this
  obtain ⟨hm, hc⟩ := this
  refine ⟨(A_mem_Eg G x y).mp hm, ?_⟩
  rw [A_cr_mk] at hc
  tauto

-- ===================== coloriage glouton (L5, étape f) =====================

lemma A_pick (s0 : ℤ) (k : ℕ) (r : ℤ) (hr : r = 1 ∨ r = 3) (hs : Even s0) (B : Finset ℤ)
    (hB : B.card ≤ k) : ∃ c : ℤ, c ∉ B ∧ c % 4 = r ∧ |c - s0| ≤ 2 * k + 1 := by
  obtain ⟨m, hm⟩ := hs
  obtain ⟨c0, hc0a, hc0b⟩ : ∃ c0 : ℤ, c0 % 4 = r ∧ s0 - 2 * k - 1 ≤ c0 ∧ c0 ≤ s0 - 2 * k + 1 := by
    by_cases h : (s0 - 2 * k - 1) % 4 = r
    · exact ⟨s0 - 2 * k - 1, h, le_refl _, by omega⟩
    · exact ⟨s0 - 2 * k - 1 + 2, by omega, by omega, by omega⟩
  have hinj : Function.Injective (fun j : ℕ => c0 + 4 * (j:ℤ)) := by
    intro a b h; simp only at h; omega
  have hcard : ((Finset.range (k+1)).image (fun j : ℕ => c0 + 4 * (j:ℤ))).card = k + 1 := by
    rw [Finset.card_image_of_injective _ hinj]; simp
  obtain ⟨c, hcC, hcB⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := B) (t := (Finset.range (k+1)).image (fun j : ℕ => c0 + 4 * (j:ℤ))) (by rw [hcard]; omega)
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hcC
  have hj' : j < k + 1 := Finset.mem_range.mp hj
  refine ⟨_, hcB, by omega, ?_⟩
  rw [abs_le]; constructor <;> omega

theorem A_greedy (G : SimpleGraph V) (S : Finset V) (s0 : V → ℤ) (hs : ∀ v, Even (s0 v))
    (idx : V → ℕ) (hidx : Function.Injective idx) (n : ℕ) (hn : ∀ v, idx v < n) :
    ∃ f : V → ℤ, (∀ v, f v % 4 = if v ∈ S then 1 else 3) ∧ (∀ u v, G.Adj u v → f u ≠ f v) ∧
      ∀ v, |f v - s0 v| ≤
        2 * ((univ.filter (fun u => G.Adj u v ∧ idx u < idx v ∧ (u ∈ S ↔ v ∈ S))).card : ℤ) + 1 := by
  have key : ∀ m : ℕ, ∃ f : V → ℤ,
      (∀ v, idx v < m → (f v % 4 = if v ∈ S then 1 else 3) ∧ |f v - s0 v| ≤
        2 * ((univ.filter (fun u => G.Adj u v ∧ idx u < idx v ∧ (u ∈ S ↔ v ∈ S))).card : ℤ) + 1) ∧
      ∀ u v, idx u < m → idx v < m → G.Adj u v → f u ≠ f v := by
    intro m
    induction m with
    | zero =>
      exact ⟨fun _ => 0, fun v h => absurd h (Nat.not_lt_zero _),
        fun u v h => absurd h (Nat.not_lt_zero _)⟩
    | succ m ih =>
      obtain ⟨f, hf1, hf2⟩ := ih
      by_cases hv : ∃ v, idx v = m
      · obtain ⟨v, hv⟩ := hv
        set Bs := univ.filter (fun u => G.Adj u v ∧ idx u < idx v ∧ (u ∈ S ↔ v ∈ S)) with hBs
        obtain ⟨c, hcB, hc4, hcw⟩ := A_pick (s0 v) Bs.card (if v ∈ S then 1 else 3)
          (by split_ifs <;> simp) (hs v) (Bs.image f) Finset.card_image_le
        have hlt : ∀ w, w ≠ v → idx w < m + 1 → idx w < m := by
          intro w hw h
          have : idx w ≠ idx v := fun h' => hw (hidx h')
          omega
        have hdiff : ∀ w, G.Adj w v → idx w < m → c ≠ f w := by
          intro w hadj hw hcw'
          by_cases hside : (w ∈ S ↔ v ∈ S)
          · apply hcB
            rw [hcw']
            exact Finset.mem_image_of_mem f (by simp [hBs, hadj, hside]; omega)
          · have h1 := (hf1 w hw).1
            rw [← hcw', hc4] at h1
            by_cases a : w ∈ S <;> by_cases b : v ∈ S <;> simp [a, b] at h1 hside
        refine ⟨Function.update f v c, ?_, ?_⟩
        · intro w hw
          by_cases hwv : w = v
          · subst hwv
            simp only [Function.update_self]
            exact ⟨hc4, hcw⟩
          · rw [Function.update_of_ne hwv]; exact hf1 w (hlt w hwv hw)
        · intro u w hu hw hadj
          by_cases huv : u = v
          · subst huv
            have hwv : w ≠ u := fun h => (G.ne_of_adj hadj) h.symm
            rw [Function.update_self, Function.update_of_ne hwv]
            exact hdiff w hadj.symm (hlt w hwv hw)
          · by_cases hwv : w = v
            · subst hwv
              rw [Function.update_self, Function.update_of_ne huv]
              exact (hdiff u hadj (hlt u huv hu)).symm
            · rw [Function.update_of_ne huv, Function.update_of_ne hwv]
              exact hf2 u w (hlt u huv hu) (hlt w hwv hw) hadj
      · refine ⟨f, fun w hw => hf1 w ?_, fun u w hu hw => hf2 u w ?_ ?_⟩
        · exact lt_of_le_of_ne (Nat.lt_succ_iff.mp hw) (fun h => hv ⟨w, h⟩)
        · exact lt_of_le_of_ne (Nat.lt_succ_iff.mp hu) (fun h => hv ⟨u, h⟩)
        · exact lt_of_le_of_ne (Nat.lt_succ_iff.mp hw) (fun h => hv ⟨w, h⟩)
  obtain ⟨f, hf1, hf2⟩ := key n
  exact ⟨f, fun v => (hf1 v (hn v)).1, fun u v h => hf2 u v (hn u) (hn v) h,
    fun v => (hf1 v (hn v)).2⟩

-- ===================== assemblage des poids =====================

lemma A_final (G : SimpleGraph V) (S : Finset V) (N : V → Finset V) (sg : V → ℤ)
    (hsg : ∀ v, |sg v| ≤ 1)
    (hN : ∀ v, ∀ u ∈ N v, G.Adj u v ∧ (u ∈ S ↔ v ∈ S))
    (hno : ∀ u v, v ∈ N u → u ∈ N v → False)
    (ψ : V → V → ℤ) (h1 : ∀ x y, ψ x y = - ψ y x) (h2 : ∀ x y, |ψ x y| ≤ 1)
    (h3 : ∀ x y, ψ x y ≠ 0 → G.Adj x y ∧ ¬ (x ∈ S ↔ y ∈ S))
    (h4 : ∀ v, ∑ u, ψ v u = ((N v).card : ℤ) * ((if v ∈ S then 1 else -1) * sg v) -
        ∑ u, (if v ∈ N u then (if u ∈ S then 1 else -1) * sg u else 0)) :
    ∃ ω : Sym2 V → ℕ, Wt3 G ω ∧ ∀ v, (sdeg G ω v : ℤ) =
      2 * ((univ.filter (G.Adj v)).card : ℤ) + 2 * (((N v).card : ℤ) * sg v) := by
  set ε : V → ℤ := fun v => if v ∈ S then 1 else -1 with hε
  have hε1 : ∀ v, ε v = 1 ∨ ε v = -1 := fun v => by by_cases h : v ∈ S <;> simp [hε, h]
  have hεsq : ∀ v, ε v * ε v = 1 := fun v => by rcases hε1 v with h | h <;> rw [h] <;> norm_num
  let X : V → V → ℤ := fun a b => (if a ∈ N b then sg b else 0) + (if b ∈ N a then sg a else 0)
  let Y : V → V → ℤ := fun a b => ε a * ψ a b
  have hXs : ∀ a b, X a b = X b a := fun a b => by simp only [X]; ring
  have hYs : ∀ a b, Y a b = Y b a := by
    intro a b
    by_cases hz : ψ a b = 0
    · have : ψ b a = 0 := by rw [h1 b a, hz]; simp
      simp [Y, hz, this]
    · have hh := (h3 a b hz).2
      have hb : ε b = - ε a := by
        by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;> simp [hε, ha, hb] at hh ⊢
      simp only [Y]; rw [h1 b a, hb]; ring
  have hWb : ∀ a b, G.Adj a b → 1 ≤ 2 + X a b + Y a b ∧ 2 + X a b + Y a b ≤ 3 := by
    intro a b hab
    by_cases hside : (a ∈ S ↔ b ∈ S)
    · have hz : ψ a b = 0 := by
        by_contra hne; exact (h3 a b hne).2 hside
      have hy : Y a b = 0 := by simp [Y, hz]
      have h5 := abs_le.mp (hsg a); have h6 := abs_le.mp (hsg b)
      simp only [X, hy]
      by_cases p : a ∈ N b <;> by_cases q : b ∈ N a
      · exact (hno a b q p).elim
      · simp [p, q]; omega
      · simp [p, q]; omega
      · simp [p, q]
    · have p : a ∉ N b := fun h => hside ((hN b a h).2)
      have q : b ∉ N a := fun h => hside ((hN a b h).2).symm
      have hy := abs_le.mp (h2 a b)
      have hy2 : |Y a b| ≤ 1 := by
        simp only [Y]; rw [abs_mul]; rcases hε1 a with h | h <;> rw [h] <;> simpa using h2 a b
      have := abs_le.mp hy2
      simp only [X, p, q, if_false]; omega
  have hWs : ∀ a b, (2 + X a b + Y a b) = 2 + X b a + Y b a := by
    intro a b; rw [hXs a b, hYs a b]
  let ω : Sym2 V → ℕ := Sym2.lift ⟨fun a b => (2 + X a b + Y a b).toNat, fun a b => by
    simp only; rw [hWs a b]⟩
  have hω : ∀ a b, ω s(a, b) = (2 + X a b + Y a b).toNat := fun a b => rfl
  refine ⟨ω, ?_, ?_⟩
  · intro e he
    induction e using Sym2.ind with
    | _ a b =>
    rw [SimpleGraph.mem_edgeSet] at he
    rw [hω]; have := hWb a b he; omega
  · intro v
    unfold sdeg
    have hc : ∀ c : ℤ, ∑ u, (if u ∈ N v then c else 0) = ((N v).card : ℤ) * c := by
      intro c; simp [Finset.sum_ite_mem, mul_comm]
    have hcast : ((∑ u ∈ univ.filter (G.Adj v), ω s(v, u) : ℕ) : ℤ) =
        ∑ u ∈ univ.filter (G.Adj v), (2 + X v u + Y v u) := by
      push_cast
      refine Finset.sum_congr rfl (fun u hu => ?_)
      rw [hω]; have := hWb v u (Finset.mem_filter.mp hu).2; omega
    rw [hcast]
    have hXz : ∀ u, u ∈ (univ : Finset V) → u ∉ univ.filter (G.Adj v) → X v u = 0 := by
      intro u _ hu
      have hna : ¬ G.Adj v u := by simpa using hu
      have p : v ∉ N u := fun h => hna (hN u v h).1
      have q : u ∉ N v := fun h => hna (hN v u h).1.symm
      simp [X, p, q]
    have hYz : ∀ u, u ∈ (univ : Finset V) → u ∉ univ.filter (G.Adj v) → Y v u = 0 := by
      intro u _ hu
      have hna : ¬ G.Adj v u := by simpa using hu
      have : ψ v u = 0 := by by_contra hne; exact hna (h3 v u hne).1
      simp [Y, this]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_subset (Finset.filter_subset _ _) hXz, Finset.sum_subset (Finset.filter_subset _ _) hYz]
    have hXs' : ∑ u, X v u = ∑ u, (if v ∈ N u then sg u else 0) + ((N v).card : ℤ) * sg v := by
      simp only [X, Finset.sum_add_distrib]; rw [hc (sg v)]
    have hYs' : ∑ u, Y v u = ε v * (((N v).card : ℤ) * (ε v * sg v) -
        ∑ u, (if v ∈ N u then ε u * sg u else 0)) := by
      simp only [Y, ← Finset.mul_sum]; rw [h4 v]
    have hk : ε v * ∑ u, (if v ∈ N u then ε u * sg u else 0) = ∑ u, (if v ∈ N u then sg u else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun u _ => ?_)
      by_cases hv : v ∈ N u
      · have hs := (hN u v hv).2
        have : ε v = ε u := by
          by_cases h : v ∈ S <;> by_cases h' : u ∈ S <;> simp [hε, h, h'] at hs ⊢
        simp only [hv, if_true]; rw [this, ← mul_assoc, hεsq, one_mul]
      · simp [hv]
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [hXs', hYs']
    have e : ε v * (((N v).card : ℤ) * (ε v * sg v) - ∑ u, (if v ∈ N u then ε u * sg u else 0)) =
        ((N v).card : ℤ) * sg v - ∑ u, (if v ∈ N u then sg u else 0) := by
      rw [mul_sub, hk]
      have : ε v * (((N v).card : ℤ) * (ε v * sg v)) = ((N v).card : ℤ) * sg v * (ε v * ε v) := by ring
      rw [this, hεsq]; ring
    rw [e]; ring

lemma A_arith (δ K g : ℤ) (hodd : δ % 2 = 1) (hb : |δ| ≤ 2 * K + 1)
    (hg : g = if 0 < δ then (δ - 1) / 2 else (δ + 1) / 2) : |g| ≤ K ∧ |2 * g - δ| = 1 := by
  rw [abs_le] at hb
  by_cases hp : 0 < δ
  · rw [if_pos hp] at hg
    refine ⟨?_, ?_⟩ <;> [rw [abs_le]; skip] <;> [constructor <;> omega; skip]
    have : 2 * g - δ = -1 := by omega
    rw [this]; norm_num
  · rw [if_neg hp] at hg
    refine ⟨?_, ?_⟩ <;> [rw [abs_le]; skip] <;> [constructor <;> omega; skip]
    have : 2 * g - δ = 1 := by omega
    rw [this]; norm_num

theorem lemma3 (G : SimpleGraph V) (h : V → ℕ) (he : ∀ v, Even (h v)) (h2 : ∀ v, 2 ≤ h v) :
    ∃ (ω : Sym2 V → ℕ) (f : V → ℕ), Wt3 G ω ∧ (∀ v, Odd (f v)) ∧
      (∀ u v, G.Adj u v → f u ≠ f v) ∧ ∀ v, |(sdeg G ω v : ℤ) + h v - f v| = 1 := by
  obtain ⟨S, -, hS⟩ := Finset.exists_max_image (univ : Finset (Finset V))
    (fun S => A_cap (A_Eg G) S) ⟨∅, mem_univ _⟩
  have hmax : ∀ S' : Finset V, A_cap (A_Eg G) S' ≤ A_cap (A_Eg G) S :=
    fun S' => hS S' (mem_univ _)
  obtain ⟨s0, hs0⟩ : ∃ s0 : V → ℤ, ∀ v, s0 v = (h v : ℤ) + 2 * ((univ.filter (G.Adj v)).card : ℤ) :=
    ⟨_, fun _ => rfl⟩
  have hs0e : ∀ v, Even (s0 v) := fun v => by
    obtain ⟨m, hm⟩ := he v
    exact ⟨m + (univ.filter (G.Adj v)).card, by rw [hs0 v]; push_cast; omega⟩
  obtain ⟨idx, hidx⟩ : ∃ idx : V → ℕ, ∀ v, idx v = (Fintype.equivFin V v : ℕ) := ⟨_, fun _ => rfl⟩
  have hidxinj : Function.Injective idx := fun a b hab =>
    (Fintype.equivFin V).injective (Fin.ext (by rw [← hidx, ← hidx]; exact hab))
  obtain ⟨f, hf4, hfadj, hfwin⟩ := A_greedy G S s0 hs0e idx hidxinj (Fintype.card V)
    (fun v => by rw [hidx]; exact (Fintype.equivFin V v).isLt)
  have hKdeg : ∀ v, (univ.filter (fun u => G.Adj u v ∧ idx u < idx v ∧ (u ∈ S ↔ v ∈ S))).card ≤
      (univ.filter (G.Adj v)).card := by
    intro v
    apply Finset.card_le_card
    intro u hu
    simp only [Finset.mem_filter, mem_univ, true_and] at hu ⊢
    exact hu.1.symm
  have hfodd : ∀ v, (f v - s0 v) % 2 = 1 := by
    intro v
    have := hf4 v; obtain ⟨m, hm⟩ := hs0e v
    by_cases hv : v ∈ S <;> simp [hv] at this <;> omega
  obtain ⟨g, hg⟩ : ∃ g : V → ℤ, ∀ v, g v = if 0 < f v - s0 v then (f v - s0 v - 1) / 2
      else (f v - s0 v + 1) / 2 := ⟨_, fun _ => rfl⟩
  have hgar : ∀ v, |g v| ≤ ((univ.filter (fun u => G.Adj u v ∧ idx u < idx v ∧
      (u ∈ S ↔ v ∈ S))).card : ℤ) ∧ |2 * g v - (f v - s0 v)| = 1 := fun v =>
    A_arith _ _ _ (hfodd v) (hfwin v) (hg v)
  have hNex : ∀ v, ∃ T : Finset V, T ⊆ univ.filter (fun u => G.Adj u v ∧ idx u < idx v ∧
      (u ∈ S ↔ v ∈ S)) ∧ T.card = (g v).natAbs := by
    intro v
    apply Finset.exists_subset_card_eq
    have := (hgar v).1
    rw [abs_le] at this
    omega
  choose N hNsub hNcard using hNex
  have hN : ∀ v, ∀ u ∈ N v, G.Adj u v ∧ (u ∈ S ↔ v ∈ S) := by
    intro v u hu
    have := hNsub v hu
    simp only [Finset.mem_filter, mem_univ, true_and] at this
    exact ⟨this.1, this.2.2⟩
  have hno : ∀ u v, v ∈ N u → u ∈ N v → False := by
    intro u v h1 h2
    have a1 := hNsub u h1; have a2 := hNsub v h2
    simp only [Finset.mem_filter, mem_univ, true_and] at a1 a2
    omega
  obtain ⟨sg, hsg⟩ : ∃ sg : V → ℤ, ∀ v, sg v = if 0 < g v then 1 else if g v < 0 then -1 else 0 :=
    ⟨_, fun _ => rfl⟩
  have hsgb : ∀ v, |sg v| ≤ 1 := fun v => by
    rw [hsg v]; split_ifs <;> simp
  have hsgg : ∀ v, ((N v).card : ℤ) * sg v = g v := fun v => by
    rw [hNcard v, hsg v]
    rcases lt_trichotomy (g v) 0 with hh | hh | hh
    · have e2 : (((g v).natAbs : ℕ) : ℤ) = - g v := by omega
      rw [e2, if_neg (by omega), if_pos hh]; ring
    · rw [hh]; simp
    · have e2 : (((g v).natAbs : ℕ) : ℤ) = g v := by omega
      rw [e2, if_pos hh]; ring
  have hτ : ∀ v, |(if v ∈ S then (1:ℤ) else -1) * sg v| ≤ 1 := fun v => by
    rw [abs_mul]
    have : |(if v ∈ S then (1:ℤ) else -1)| = 1 := by split_ifs <;> simp
    rw [this, one_mul]; exact hsgb v
  obtain ⟨ψ, h1, h2', h3, h4⟩ := A_L4b G S hmax N (fun v => (if v ∈ S then (1:ℤ) else -1) * sg v)
    hτ hN hno
  obtain ⟨ω, hW, hdeg⟩ := A_final G S N sg hsgb hN hno ψ h1 h2' h3 h4
  have hge : ∀ v, 1 ≤ f v := fun v => by
    have a := (abs_le.mp (hfwin v)).1
    have b := hKdeg v
    have c := h2 v
    have d := hs0 v
    omega
  refine ⟨ω, fun v => (f v).toNat, hW, fun v => ?_, fun u v hadj => ?_, fun v => ?_⟩
  · have := hf4 v
    have hg1 := hge v
    show Odd (f v).toNat
    rw [Nat.odd_iff]
    by_cases hv : v ∈ S <;> simp [hv] at this <;> omega
  · intro hh
    simp only at hh
    exact hfadj u v hadj (by have := hge u; have := hge v; omega)
  · have e1 : (((f v).toNat : ℕ) : ℤ) = f v := Int.toNat_of_nonneg (by have := hge v; omega)
    show |(sdeg G ω v : ℤ) + h v - (((f v).toNat : ℕ) : ℤ)| = 1
    rw [e1, hdeg v]
    have := (hgar v).2
    have hs := hs0 v
    rw [hsgg v]
    have e2 : 2 * ((univ.filter (G.Adj v)).card : ℤ) + 2 * g v + (h v : ℤ) - f v =
        2 * g v - (f v - s0 v) := by rw [hs]; ring
    rw [e2]; exact this

section
open scoped symmDiff

noncomputable def B1_dF (F : Finset (Sym2 V)) (x : V) : ℕ := (univ.filter (fun u => s(x, u) ∈ F)).card

end

section
open scoped symmDiff

lemma B1_card_symm (A B : Finset V) :
    ((A ∆ B).card : ZMod 2) = A.card + B.card := by
  have h1 : A ∆ B = (A ∪ B) \ (A ∩ B) := by
    ext u; simp only [Finset.mem_symmDiff, Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]; tauto
  have h2 : (A ∪ B).card + (A ∩ B).card = A.card + B.card := Finset.card_union_add_card_inter A B
  have h3 : ((A ∪ B) \ (A ∩ B)).card = (A ∪ B).card - (A ∩ B).card :=
    Finset.card_sdiff_of_subset (fun u hu => Finset.mem_union.2 (Or.inl (Finset.mem_inter.1 hu).1))
  have h4 : (A ∩ B).card ≤ (A ∪ B).card := Finset.card_le_card (fun u hu => Finset.mem_union.2 (Or.inl (Finset.mem_inter.1 hu).1))
  have h5 : (A ∆ B).card + 2 * (A ∩ B).card = A.card + B.card := by rw [h1, h3]; omega
  have := congrArg (fun n : ℕ => (n : ZMod 2)) h5
  simp only [Nat.cast_add, Nat.cast_mul] at this
  have h2z : ((2 : ℕ) : ZMod 2) = 0 := by decide
  rw [h2z, zero_mul, add_zero] at this
  exact this

end

section
open scoped symmDiff

lemma B1_dF_symm (F1 F2 : Finset (Sym2 V)) (x : V) :
    (B1_dF (F1 ∆ F2) x : ZMod 2) = B1_dF F1 x + B1_dF F2 x := by
  unfold B1_dF
  have h : univ.filter (fun u => s(x,u) ∈ F1 ∆ F2) =
      (univ.filter (fun u => s(x,u) ∈ F1)) ∆ (univ.filter (fun u => s(x,u) ∈ F2)) := by
    ext u; simp [Finset.mem_symmDiff]
  rw [h]; exact B1_card_symm _ _

end

section
open scoped symmDiff

lemma B1_dF_single {a b : V} (hab : a ≠ b) (x : V) :
    (B1_dF {s(a,b)} x : ZMod 2) = (if x = a then 1 else 0) + (if x = b then 1 else 0) := by
  unfold B1_dF
  by_cases hxa : x = a
  · subst hxa
    have : univ.filter (fun u => s(x,u) ∈ ({s(x,b)} : Finset (Sym2 V))) = {b} := by
      ext u; simp [hab]
    rw [this]; simp [hab]
  · by_cases hxb : x = b
    · subst hxb
      have : univ.filter (fun u => s(x,u) ∈ ({s(a,x)} : Finset (Sym2 V))) = {a} := by
        ext u; simp [hab, eq_comm]
      rw [this]; simp [hab, hxa]
    · have : univ.filter (fun u => s(x,u) ∈ ({s(a,b)} : Finset (Sym2 V))) = ∅ := by
        ext u; simp [hxa, hxb]
      rw [this]; simp [hxa, hxb]

end

section
open scoped symmDiff

def B1_Real (H : SimpleGraph V) (t : V → ZMod 2) : Prop :=
  ∃ F : Finset (Sym2 V), (∀ e ∈ F, e ∈ H.edgeSet) ∧ ∀ x, (B1_dF F x : ZMod 2) = t x

end

section
open scoped symmDiff

lemma B1_Real_add {H : SimpleGraph V} {t1 t2 : V → ZMod 2} (h1 : B1_Real H t1) (h2 : B1_Real H t2) :
    B1_Real H (fun x => t1 x + t2 x) := by
  obtain ⟨F1, hF1, e1⟩ := h1
  obtain ⟨F2, hF2, e2⟩ := h2
  refine ⟨F1 ∆ F2, fun e he => ?_, fun x => ?_⟩
  · rcases Finset.mem_symmDiff.1 he with h | h
    · exact hF1 e h.1
    · exact hF2 e h.1
  · rw [B1_dF_symm, e1, e2]

end

section
open scoped symmDiff

lemma B1_Real_congr {H : SimpleGraph V} {t t' : V → ZMod 2} (h : B1_Real H t) (e : ∀ x, t x = t' x) :
    B1_Real H t' := by
  obtain ⟨F, hF, hd⟩ := h
  exact ⟨F, hF, fun x => (hd x).trans (e x)⟩

end

section
open scoped symmDiff

lemma B1_Real_pair {H : SimpleGraph V} {u v : V} (h : H.Reachable u v) :
    B1_Real H (fun x => (if x = u then 1 else 0) + (if x = v then 1 else 0)) := by
  obtain ⟨p⟩ := h
  induction p with
  | @nil a =>
    refine ⟨∅, by simp, fun x => ?_⟩
    simp only [B1_dF]
    by_cases hx : x = a <;> simp [hx] <;> decide
  | @cons a w b hadj p ih =>
    have h1 : B1_Real H (fun x => (if x = a then 1 else 0) + (if x = w then 1 else 0)) := by
      refine ⟨{s(a,w)}, ?_, fun x => B1_dF_single hadj.ne x⟩
      intro e he; rw [Finset.mem_singleton.1 he]; exact hadj
    refine B1_Real_congr (B1_Real_add h1 ih) (fun x => ?_)
    generalize (if x = a then (1 : ZMod 2) else 0) = p1
    generalize (if x = w then (1 : ZMod 2) else 0) = p2
    generalize (if x = b then (1 : ZMod 2) else 0) = p3
    revert p1 p2 p3; decide

end

section
open scoped symmDiff

lemma B1_Real_of_sum (H : SimpleGraph V) (U : Finset V) (hconn : ∀ u ∈ U, ∀ v ∈ U, H.Reachable u v) :
    ∀ (n : ℕ) (t : V → ZMod 2), (univ.filter (fun x => t x ≠ 0)).card = n → (∀ x, x ∉ U → t x = 0) →
      ∑ x ∈ U, t x = 0 → B1_Real H t := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro t hn ht hs
    by_cases h0 : ∀ x, t x = 0
    · refine ⟨∅, by simp, fun x => ?_⟩
      simp [B1_dF, h0 x]
    · push Not at h0
      obtain ⟨u, hu⟩ := h0
      have huU : u ∈ U := by by_contra h; exact hu (ht u h)
      have hu1 : t u = 1 := by
        generalize t u = a at hu; revert a; decide
      have hv : ∃ v ∈ U, v ≠ u ∧ t v = 1 := by
        by_contra hcon
        push Not at hcon
        have : ∑ x ∈ U, t x = t u := by
          apply Finset.sum_eq_single u
          · intro b hb hbu
            have := hcon b hb hbu
            generalize t b = a at this ⊢; revert a; decide
          · intro h; exact absurd huU h
        rw [this, hu1] at hs
        exact absurd hs (by decide)
      obtain ⟨v, hvU, hvu, hv1⟩ := hv
      set t' : V → ZMod 2 := fun x => t x + ((if x = u then 1 else 0) + (if x = v then 1 else 0)) with ht'
      have hsub : (univ.filter (fun x => t' x ≠ 0)) ⊆ (univ.filter (fun x => t x ≠ 0)).erase u := by
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase] at hx ⊢
        by_cases hxu : x = u
        · subst hxu; exfalso; apply hx; simp [ht', hu1, hvu.symm]; decide
        · by_cases hxv : x = v
          · subst hxv; exfalso; apply hx; simp [ht', hv1, hxu]; decide
          · refine ⟨hxu, ?_⟩; simpa [ht', hxu, hxv] using hx
      have hcard : (univ.filter (fun x => t' x ≠ 0)).card < n := by
        calc _ ≤ ((univ.filter (fun x => t x ≠ 0)).erase u).card := Finset.card_le_card hsub
          _ < (univ.filter (fun x => t x ≠ 0)).card :=
              Finset.card_erase_lt_of_mem (by simp [hu])
          _ = n := hn
      have hreal : B1_Real H t' := by
        refine ih _ hcard t' rfl (fun x hx => ?_) ?_
        · have hxu : x ≠ u := fun h => hx (h ▸ huU)
          have hxv : x ≠ v := fun h => hx (h ▸ hvU)
          simp [ht', ht x hx, hxu, hxv]
        · simp only [ht', Finset.sum_add_distrib, hs]
          simp [huU, hvU]; decide
      have hpair := B1_Real_pair (hconn u huU v hvU)
      refine B1_Real_congr (B1_Real_add hreal hpair) (fun x => ?_)
      simp only [ht']
      generalize t x = a
      generalize (if x = u then (1 : ZMod 2) else 0) = p1
      generalize (if x = v then (1 : ZMod 2) else 0) = p2
      revert a p1 p2; decide

end

section
open scoped symmDiff

lemma B1_sdeg_formula (H : SimpleGraph V) (F : Finset (Sym2 V)) (ω : Sym2 V → ℕ) (v : V)
    (hω : ∀ u, H.Adj v u → (s(v,u) ∈ F → ω s(v,u) = 1 ∨ ω s(v,u) = 3) ∧ (s(v,u) ∉ F → ω s(v,u) = 2)) :
    (sdeg H ω v : ℤ) = 2 * (univ.filter (H.Adj v)).card
      - ((univ.filter (H.Adj v)).filter (fun u => s(v,u) ∈ F)).card
      + 2 * ((univ.filter (H.Adj v)).filter (fun u => ω s(v,u) = 3)).card := by
  unfold sdeg
  push_cast
  have hpt : ∀ u ∈ univ.filter (H.Adj v), (ω s(v,u) : ℤ) =
      2 - (if s(v,u) ∈ F then 1 else 0) + 2 * (if ω s(v,u) = 3 then 1 else 0) := by
    intro u hu
    have hu' : H.Adj v u := by simpa using hu
    obtain ⟨h1, h2⟩ := hω u hu'
    by_cases hF : s(v,u) ∈ F
    · rcases h1 hF with h | h <;> simp [hF, h]
    · simp [hF, h2 hF]
  rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_boole, Finset.sum_boole]
  simp only [Finset.sum_const, nsmul_eq_mul]
  ring

end

section
open scoped symmDiff

lemma B1_degree_eq (H : SimpleGraph V) (v : V) : H.degree v = (univ.filter (H.Adj v)).card := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  congr 1; ext u; simp

end

section
open scoped symmDiff

theorem lemma5 (H : SimpleGraph V) (R B : Finset V) (hd : Disjoint R B)
    (hb : ∀ u v, H.Adj u v → (u ∈ R ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ R))
    (hc : ∀ u ∈ R ∪ B, ∀ v ∈ R ∪ B, H.Reachable u v)
    (α : V → ℕ) (hα : ∀ v ∈ B, α v + 1 = 2 * H.degree v ∨ α v = 2 * H.degree v ∨
      α v = 2 * H.degree v + 1)
    (R' : Finset V) (hR' : R' ⊆ R) (hpar : Even (R'.card + ∑ v ∈ B, α v)) :
    ∃ ω, Wt3 H ω ∧ (∀ v ∈ R, Even (sdeg H ω v) ↔ v ∉ R') ∧ ∀ v ∈ B, sdeg H ω v = α v := by
  classical
  let t : V → ZMod 2 := fun x => if x ∈ R then (if x ∈ R' then 1 else 0) else
    if x ∈ B then (α x : ZMod 2) else 0
  have ht0 : ∀ x, x ∉ R ∪ B → t x = 0 := by
    intro x hx
    simp only [Finset.mem_union, not_or] at hx
    simp [t, hx.1, hx.2]
  have hsum : ∑ x ∈ R ∪ B, t x = 0 := by
    rw [Finset.sum_union hd]
    have e1 : ∑ x ∈ R, t x = (R'.card : ZMod 2) := by
      rw [Finset.sum_congr rfl (fun x hx => show t x = if x ∈ R' then 1 else 0 by simp [t, hx])]
      rw [Finset.sum_boole]; congr 2; ext x; simp only [Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨hR' h, h⟩⟩
    have e2 : ∑ x ∈ B, t x = ((∑ v ∈ B, α v : ℕ) : ZMod 2) := by
      push_cast
      refine Finset.sum_congr rfl (fun x hx => ?_)
      have : x ∉ R := fun h => Finset.disjoint_left.1 hd h hx
      simp [t, this, hx]
    rw [e1, e2, ← Nat.cast_add]
    exact (ZMod.natCast_eq_zero_iff_even).2 hpar
  obtain ⟨F, hF, hdF⟩ := B1_Real_of_sum H (R ∪ B) hc _ t rfl ht0 hsum
  have hKsub : ∀ v, (univ.filter (fun u => s(v,u) ∈ F)) ⊆ univ.filter (H.Adj v) := by
    intro v u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    exact hF _ hu
  have hS : ∀ v, ∃ S : Finset V, S ⊆ univ.filter (fun u => s(v,u) ∈ F) ∧
      (v ∈ B → 2 * S.card + 2 * H.degree v = α v + B1_dF F v) := by
    intro v
    by_cases hv : v ∈ B
    · have hvR : v ∉ R := fun h => Finset.disjoint_left.1 hd h hv
      have hk : (B1_dF F v : ZMod 2) = (α v : ZMod 2) := by rw [hdF v]; simp [t, hvR, hv]
      have hk2 : B1_dF F v % 2 = α v % 2 := (ZMod.natCast_eq_natCast_iff' _ _ 2).1 hk
      have hle : B1_dF F v ≤ H.degree v := by
        rw [B1_degree_eq]; exact Finset.card_le_card (hKsub v)
      have h3 := hα v hv
      have hkd : (univ.filter (fun u => s(v,u) ∈ F)).card = B1_dF F v := rfl
      obtain ⟨S, hS1, hS2⟩ := Finset.exists_subset_card_eq
        (s := univ.filter (fun u => s(v,u) ∈ F)) (n := (α v + B1_dF F v - 2 * H.degree v) / 2)
        (by rw [hkd]; omega)
      exact ⟨S, hS1, fun _ => by omega⟩
    · exact ⟨∅, by simp, fun h => absurd h hv⟩
  choose S hSsub hSc using hS
  let g : V → V → ℕ := fun a b => if s(a,b) ∈ F then
    (if (a ∈ B ∧ b ∈ S a) ∨ (b ∈ B ∧ a ∈ S b) then 3 else 1) else 2
  have gsymm : ∀ a b, g a b = g b a := by
    intro a b
    by_cases h1 : s(a,b) ∈ F
    · have h1' : s(b,a) ∈ F := by rwa [Sym2.eq_swap]
      simp [g, h1, h1', or_comm]
    · have h1' : s(b,a) ∉ F := by rwa [Sym2.eq_swap]
      simp [g, h1, h1']
  let ω : Sym2 V → ℕ := Sym2.lift ⟨g, gsymm⟩
  have hω : ∀ a b, ω s(a,b) = g a b := fun a b => rfl
  have hω' : ∀ v u, (s(v,u) ∈ F → ω s(v,u) = 1 ∨ ω s(v,u) = 3) ∧ (s(v,u) ∉ F → ω s(v,u) = 2) := by
    intro v u
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [hω]; simp only [g, h]; split_ifs <;> simp
    · rw [hω]; simp only [g, h]; simp
  have hW : Wt3 H ω := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      rw [hω]; simp only [g]; split_ifs <;> omega
  have hKeq : ∀ v, (univ.filter (H.Adj v)).filter (fun u => s(v,u) ∈ F) =
      univ.filter (fun u => s(v,u) ∈ F) := by
    intro v; ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h.2, fun h => ⟨by simpa using hKsub v (by simpa using h), h⟩⟩
  refine ⟨ω, hW, fun v hv => ?_, fun v hv => ?_⟩
  · have hf := B1_sdeg_formula H F ω v (fun u _ => hω' v u)
    rw [hKeq v] at hf
    have hkk : (B1_dF F v : ZMod 2) = if v ∈ R' then 1 else 0 := by rw [hdF v]; simp [t, hv]
    rw [Nat.even_iff]
    by_cases hv' : v ∈ R'
    · have : (B1_dF F v : ZMod 2) = ((1 : ℕ) : ZMod 2) := by rw [hkk]; simp [hv']
      have h2 := (ZMod.natCast_eq_natCast_iff' _ _ 2).1 this
      have : B1_dF F v = (univ.filter (fun u => s(v,u) ∈ F)).card := rfl
      simp only [hv', not_true_eq_false, iff_false]
      omega
    · have : (B1_dF F v : ZMod 2) = ((0 : ℕ) : ZMod 2) := by rw [hkk]; simp [hv']
      have h2 := (ZMod.natCast_eq_natCast_iff' _ _ 2).1 this
      have : B1_dF F v = (univ.filter (fun u => s(v,u) ∈ F)).card := rfl
      simp only [hv', not_false_eq_true, iff_true]
      omega
  · have hf := B1_sdeg_formula H F ω v (fun u _ => hω' v u)
    rw [hKeq v] at hf
    have hvR : v ∉ R := fun h => Finset.disjoint_left.1 hd h hv
    have hT : (univ.filter (H.Adj v)).filter (fun u => ω s(v,u) = 3) = S v := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hu, h3⟩
        have huB : u ∉ B := fun h => by
          rcases hb v u hu with ⟨h1, _⟩ | ⟨_, h2⟩
          · exact hvR h1
          · exact Finset.disjoint_left.1 hd h2 h
        have h3' : (v ∈ B ∧ u ∈ S v) ∨ (u ∈ B ∧ v ∈ S u) := by
          by_contra h5
          rw [hω] at h3; simp only [g] at h3
          by_cases h4 : s(v,u) ∈ F <;> simp [h4, h5] at h3
        rcases h3' with ⟨_, h6⟩ | ⟨h6, _⟩
        · exact h6
        · exact absurd h6 huB
      · intro hu
        have h1 := hSsub v hu
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1
        refine ⟨by simpa using hKsub v (by simpa using h1), ?_⟩
        rw [hω]; simp only [g, h1, hv, hu]; simp
    rw [hT] at hf
    have h1 := hSc v hv
    have h2 : B1_dF F v = (univ.filter (fun u => s(v,u) ∈ F)).card := rfl
    have h3 := B1_degree_eq H v
    omega

end

section
open scoped symmDiff

def B1_GB (G : SimpleGraph V) (B : Finset V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ u ∈ B ∧ v ∈ B
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun u h => G.loopless.irrefl u h.1⟩

end

section
open scoped symmDiff

lemma B1_sum_odd (B : Finset V) (α : V → ℕ) (hodd : ∀ v ∈ B, α v % 2 = 1) (hB : Even B.card) :
    Even (0 + ∑ v ∈ B, α v) := by
  have h1 := Finset.sum_nat_mod B 2 α
  rw [Finset.sum_congr rfl hodd] at h1
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at h1
  rw [Nat.even_iff] at hB ⊢
  omega

end

section
open scoped symmDiff

theorem lemma7 (G : SimpleGraph V) (R B : Finset V) (hg : Good G R B)
    (hdom : ∀ u v, G.Adj u v → u ∈ R ∪ B ∧ v ∈ R ∪ B) :
    ∃ ω, Wt3 G ω ∧ (∀ u v, G.Adj u v → sdeg G ω u ≠ sdeg G ω v) ∧
      ∀ v ∈ R ∪ B, (Even (sdeg G ω v) ↔ v ∈ R) := by
  classical
  set H := bip G R B with hH
  have hdeg : ∀ v ∈ B, 1 ≤ H.degree v := by
    intro v hv
    have hcard : 1 < B.card := by
      have := hg.even
      have hpos : 0 < B.card := Finset.card_pos.2 ⟨v, hv⟩
      rw [Nat.even_iff] at this; omega
    obtain ⟨v', hv', hne⟩ := Finset.exists_mem_ne hcard v
    obtain ⟨p⟩ := hg.conn v (Finset.mem_union_right _ hv) v' (Finset.mem_union_right _ hv')
    cases p with
    | nil => exact absurd rfl hne
    | cons hadj _ =>
      exact (SimpleGraph.degree_pos_iff_exists_adj H v).2 ⟨_, hadj⟩
  let h : V → ℕ := fun v => if v ∈ B then 2 * H.degree v else 2
  have he : ∀ v, Even (h v) := by
    intro v; simp only [h]; split_ifs
    · exact even_two_mul _
    · exact even_two
  have h2 : ∀ v, 2 ≤ h v := by
    intro v; simp only [h]; split_ifs with hv
    · have := hdeg v hv; omega
    · exact le_refl _
  obtain ⟨ω1, f, hW1, hfodd, hfproper, hfabs⟩ := lemma3 (B1_GB G B) h he h2
  let α : V → ℕ := fun v => (f v - (sdeg (B1_GB G B) ω1 v : ℤ)).toNat
  have hα : ∀ v ∈ B, α v + 1 = 2 * H.degree v ∨ α v = 2 * H.degree v ∨
      α v = 2 * H.degree v + 1 := by
    intro v hv
    have h1 := hfabs v
    have h3 := hdeg v hv
    simp only [h, hv, if_true] at h1
    rcases abs_eq (zero_le_one) |>.1 h1 with h4 | h4 <;> simp only [α] <;> omega
  have hαodd : ∀ v ∈ B, α v % 2 = 1 := by
    intro v hv
    have h1 := hfabs v
    have h3 := hdeg v hv
    simp only [h, hv, if_true] at h1
    rcases abs_eq (zero_le_one) |>.1 h1 with h4 | h4 <;> simp only [α] <;> omega
  have hb : ∀ u v, H.Adj u v → (u ∈ R ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ R) := fun u v h => h.2
  obtain ⟨ω2, hW2, hpR, hpB⟩ := lemma5 H R B hg.disj hb
    (fun u hu v hv => hg.conn u hu v hv) α hα ∅ (Finset.empty_subset _)
    (by simpa using B1_sum_odd B α hαodd hg.even)
  let ω : Sym2 V → ℕ := fun e => if e ∈ (B1_GB G B).edgeSet then ω1 e else ω2 e
  have hdisjRB : ∀ x, x ∈ R → x ∈ B → False := fun x h1 h2 => Finset.disjoint_left.1 hg.disj h1 h2
  have hWt : Wt3 G ω := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      have hab : G.Adj a b := he
      by_cases hGB : (B1_GB G B).Adj a b
      · have := hW1 s(a,b) (by simpa using hGB)
        simpa [ω, hGB] using this
      · have hH' : H.Adj a b := by
          refine ⟨hab, ?_⟩
          obtain ⟨ha, hb'⟩ := hdom a b hab
          rcases Finset.mem_union.1 ha with ha | ha <;> rcases Finset.mem_union.1 hb' with hb' | hb'
          · exact absurd hab (hg.indep a ha b hb')
          · exact Or.inl ⟨ha, hb'⟩
          · exact Or.inr ⟨ha, hb'⟩
          · exact absurd ⟨hab, ha, hb'⟩ hGB
        have := hW2 s(a,b) (by simpa using hH')
        simpa [ω, hGB] using this
  have hsB : ∀ v ∈ B, sdeg G ω v = f v := by
    intro v hv
    have hsplit : univ.filter (G.Adj v) = univ.filter ((B1_GB G B).Adj v) ∪ univ.filter (H.Adj v) := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      constructor
      · intro hvu
        obtain ⟨_, hu⟩ := hdom v u hvu
        rcases Finset.mem_union.1 hu with hu | hu
        · right; exact ⟨hvu, Or.inr ⟨hv, hu⟩⟩
        · left; exact ⟨hvu, hv, hu⟩
      · rintro (h | h)
        · exact h.1
        · exact h.1
    have hdj : Disjoint (univ.filter ((B1_GB G B).Adj v)) (univ.filter (H.Adj v)) := by
      rw [Finset.disjoint_left]
      intro u h1 h2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      rcases h2.2 with ⟨h3, _⟩ | ⟨_, h3⟩
      · exact hdisjRB v h3 hv
      · exact hdisjRB u h3 h1.2.2
    have e1 : sdeg G ω v = sdeg (B1_GB G B) ω1 v + sdeg H ω2 v := by
      unfold sdeg
      rw [hsplit, Finset.sum_union hdj]
      congr 1
      · refine Finset.sum_congr rfl (fun u hu => ?_)
        have hu' : (B1_GB G B).Adj v u := by simpa using hu
        simp [ω, hu']
      · refine Finset.sum_congr rfl (fun u hu => ?_)
        have hu' : H.Adj v u := by simpa using hu
        have : ¬ (B1_GB G B).Adj v u := fun hh => by
          rcases hu'.2 with ⟨h3, _⟩ | ⟨_, h3⟩
          · exact hdisjRB v h3 hv
          · exact hdisjRB u h3 hh.2.2
        simp [ω, this]
    have e2 := hpB v hv
    have e3 : (α v : ℤ) = f v - (sdeg (B1_GB G B) ω1 v : ℤ) := by
      have h1 := hfabs v
      have h3 := hdeg v hv
      simp only [h, hv, if_true] at h1
      simp only [α]
      rcases abs_eq (zero_le_one) |>.1 h1 with h4 | h4 <;> omega
    omega
  have hsR : ∀ v ∈ R, Even (sdeg G ω v) := by
    intro v hv
    have hvB : v ∉ B := fun h => hdisjRB v hv h
    have hsplit : univ.filter (G.Adj v) = univ.filter (H.Adj v) := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hvu
        obtain ⟨_, hu⟩ := hdom v u hvu
        rcases Finset.mem_union.1 hu with hu | hu
        · exact absurd hvu (hg.indep v hv u hu)
        · exact ⟨hvu, Or.inl ⟨hv, hu⟩⟩
      · intro h; exact h.1
    have : sdeg G ω v = sdeg H ω2 v := by
      unfold sdeg
      rw [hsplit]
      refine Finset.sum_congr rfl (fun u hu => ?_)
      have : ¬ (B1_GB G B).Adj v u := fun hh => hvB hh.2.1
      simp [ω, this]
    rw [this]
    simpa using (hpR v hv)
  have hnotR : ∀ v ∈ B, ¬ Even (sdeg G ω v) := by
    intro v hv
    rw [hsB v hv]
    exact Nat.not_even_iff_odd.2 (hfodd v)
  refine ⟨ω, hWt, fun u v huv => ?_, fun v hv => ?_⟩
  · obtain ⟨hu, hv⟩ := hdom u v huv
    rcases Finset.mem_union.1 hu with hu | hu <;> rcases Finset.mem_union.1 hv with hv | hv
    · exact absurd huv (hg.indep u hu v hv)
    · intro h; exact hnotR v hv (h ▸ hsR u hu)
    · intro h; exact hnotR u hu (h ▸ hsR v hv)
    · rw [hsB u hu, hsB v hv]; exact hfproper u v ⟨huv, hu, hv⟩
  · rcases Finset.mem_union.1 hv with hv | hv
    · exact ⟨fun _ => hv, fun _ => hsR v hv⟩
    · exact ⟨fun h => absurd h (hnotR v hv), fun h => absurd hv (fun hh => hdisjRB v h hh)⟩

end

section
open scoped symmDiff

lemma B1_bip_mono (G : SimpleGraph V) {R R' B B' : Finset V} (hR : R ⊆ R') (hB : B ⊆ B') :
    bip G R B ≤ bip G R' B' := by
  intro u v h
  exact ⟨h.1, h.2.imp (fun a => ⟨hR a.1, hB a.2⟩) (fun a => ⟨hB a.1, hR a.2⟩)⟩

end

section
open scoped symmDiff

lemma B1_extend (G : SimpleGraph V) (hG : G.Connected) :
    ∀ (n : ℕ) (S R : Finset V), (univ \ S).card = n → S.Nonempty → R ⊆ S →
      (∀ x ∈ R, ∀ y ∈ R, ¬ G.Adj x y) →
      (∀ x ∈ S, ∀ y ∈ S, (bip G R (S \ R)).Reachable x y) →
      ∃ R' : Finset V, (∀ x ∈ S, (x ∈ R' ↔ x ∈ R)) ∧ (∀ x ∈ R', ∀ y ∈ R', ¬ G.Adj x y) ∧
        ∀ x y, (bip G R' R'ᶜ).Reachable x y := by
  intro n
  induction n with
  | zero =>
    intro S R hn hne hRS hind hconn
    have hS : S = univ := by
      ext x
      simp only [Finset.mem_univ, iff_true]
      by_contra h
      have hx : x ∈ univ \ S := by simp [h]
      have := Finset.card_pos.2 ⟨x, hx⟩
      omega
    subst hS
    refine ⟨R, fun _ _ => Iff.rfl, hind, fun x y => ?_⟩
    have := hconn x (Finset.mem_univ x) y (Finset.mem_univ y)
    simpa [Finset.compl_eq_univ_sdiff] using this
  | succ n ih =>
    intro S R hn hne hRS hind hconn
    obtain ⟨z, y, hzS, hyS, hadj⟩ : ∃ z y, z ∉ S ∧ y ∈ S ∧ G.Adj z y := by
      obtain ⟨y0, hy0⟩ := hne
      have : ∃ z0, z0 ∉ S := by
        by_contra h
        push Not at h
        have : univ \ S = ∅ := by ext x; simp [h x]
        rw [this] at hn; simp at hn
      obtain ⟨z0, hz0⟩ := this
      obtain ⟨p⟩ := hG.preconnected y0 z0
      obtain ⟨d, _, hd1, hd2⟩ := p.exists_boundary_dart (S : Set V) (Finset.mem_coe.2 hy0)
        (fun h => hz0 (Finset.mem_coe.1 h))
      exact ⟨d.snd, d.fst, hd2, Finset.mem_coe.1 hd1, d.adj.symm⟩
    have hcard : (univ \ insert z S).card = n := by
      rw [Finset.sdiff_insert, Finset.card_erase_of_mem (by simp [hzS]), hn]; rfl
    have hzR : z ∉ R := fun h => hzS (hRS h)
    by_cases hasR : ∃ r ∈ R, G.Adj z r
    · obtain ⟨r0, hr0, hzr0⟩ := hasR
      have hmono : bip G R (S \ R) ≤ bip G R (insert z S \ R) :=
        B1_bip_mono G (Finset.Subset.refl _) (Finset.sdiff_subset_sdiff (Finset.subset_insert _ _) (Finset.Subset.refl _))
      have hz0 : (bip G R (insert z S \ R)).Reachable z r0 :=
        SimpleGraph.Adj.reachable ⟨hzr0, Or.inr ⟨by simp [hzR], hr0⟩⟩
      have hkey : ∀ x ∈ insert z S, (bip G R (insert z S \ R)).Reachable x r0 := by
        intro x hx
        rcases Finset.mem_insert.1 hx with rfl | hx
        · exact hz0
        · exact (hconn x hx r0 (hRS hr0)).mono hmono
      obtain ⟨R', h1, h2, h3⟩ := ih (insert z S) R hcard ⟨z, Finset.mem_insert_self _ _⟩
        (hRS.trans (Finset.subset_insert _ _)) hind
        (fun x hx y hy => (hkey x hx).trans (hkey y hy).symm)
      exact ⟨R', fun x hx => h1 x (Finset.mem_insert_of_mem hx), h2, h3⟩
    · push Not at hasR
      have hmono : bip G R (S \ R) ≤ bip G (insert z R) (insert z S \ insert z R) := by
        apply B1_bip_mono G (Finset.subset_insert _ _)
        intro x hx
        simp only [Finset.mem_sdiff, Finset.mem_insert] at hx ⊢
        exact ⟨Or.inr hx.1, fun h => h.elim (fun h => hzS (h ▸ hx.1)) hx.2⟩
      have hyR : y ∉ R := fun h => hasR y h hadj
      have hz0 : (bip G (insert z R) (insert z S \ insert z R)).Reachable z y :=
        SimpleGraph.Adj.reachable ⟨hadj, Or.inl ⟨Finset.mem_insert_self _ _, by
          simp only [Finset.mem_sdiff, Finset.mem_insert]
          exact ⟨Or.inr hyS, fun h => h.elim (fun h => hzS (h ▸ hyS)) hyR⟩⟩⟩
      have hkey : ∀ x ∈ insert z S, (bip G (insert z R) (insert z S \ insert z R)).Reachable x y := by
        intro x hx
        rcases Finset.mem_insert.1 hx with rfl | hx
        · exact hz0
        · exact (hconn x hx y hyS).mono hmono
      have hind' : ∀ a ∈ insert z R, ∀ b ∈ insert z R, ¬ G.Adj a b := by
        intro a ha b hb hab
        rcases Finset.mem_insert.1 ha with rfl | ha' <;> rcases Finset.mem_insert.1 hb with rfl | hb'
        · exact G.loopless.irrefl _ hab
        · exact hasR b hb' hab
        · exact hasR a ha' hab.symm
        · exact hind a ha' b hb' hab
      obtain ⟨R', h1, h2, h3⟩ := ih (insert z S) (insert z R) hcard ⟨z, Finset.mem_insert_self _ _⟩
        (Finset.insert_subset_insert _ hRS) hind'
        (fun x hx y hy => (hkey x hx).trans (hkey y hy).symm)
      refine ⟨R', fun x hx => ?_, h2, h3⟩
      rw [h1 x (Finset.mem_insert_of_mem hx), Finset.mem_insert]
      have : x ≠ z := fun h => hzS (h ▸ hx)
      simp [this]

end

section
open scoped symmDiff

lemma B1_iff_not (P Q : Prop) (h : ¬ (P ↔ Q)) : (¬ P ↔ Q) := by tauto

end

section
open scoped symmDiff

lemma B1_chord (G : SimpleGraph V) {v w : V} (p : G.Walk v w) (hp : p.length = G.dist v w)
    {i j : ℕ} (hij : i + 2 ≤ j) (hj : j ≤ p.length) : ¬ G.Adj (p.getVert i) (p.getVert j) := by
  intro hadj
  have hle := SimpleGraph.dist_le ((p.take i).append (SimpleGraph.Walk.cons hadj (p.drop j)))
  rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_cons, SimpleGraph.Walk.drop_length,
    SimpleGraph.Walk.take_length] at hle
  have : i ⊓ p.length = i := inf_eq_left.2 (by omega)
  omega

end

section
open scoped symmDiff

lemma B1_edge_idx {G : SimpleGraph V} {v w : V} (p : G.Walk v w) {e : Sym2 V} (he : e ∈ p.edges) :
    ∃ n, n < p.length ∧ e = s(p.getVert n, p.getVert (n + 1)) := by
  simp only [SimpleGraph.Walk.edges, List.mem_map] at he
  obtain ⟨d, hd, rfl⟩ := he
  obtain ⟨n, hn, hdn⟩ := List.mem_iff_getElem.1 hd
  have hn' : n < p.length := by simpa using hn
  refine ⟨n, hn', ?_⟩
  rw [← hdn, SimpleGraph.Walk.darts_getElem_eq_getVert]
  rfl

end

section
open scoped symmDiff

theorem lemma2 (G : SimpleGraph V) (hG : G.Connected) (v w : V) (p : G.Walk v w)
    (hp : p.length = G.dist v w) (b : Bool) :
    ∃ R : Finset V, (∀ x ∈ R, ∀ y ∈ R, ¬ G.Adj x y) ∧ (v ∈ R ↔ b = true) ∧
      (∀ x y, (bip G R Rᶜ).Reachable x y) ∧
      ∀ e ∈ p.edges, ∃ x ∈ R, ∃ y ∉ R, e = s(x, y) := by
  classical
  have hpath : p.IsPath := SimpleGraph.Walk.isPath_of_length_eq_dist p hp
  have hinj := hpath.getVert_injOn
  let S0 : Finset V := (Finset.range (p.length + 1)).image p.getVert
  let R0 : Finset V := ((Finset.range (p.length + 1)).filter (fun i => (Even i ↔ b = true))).image p.getVert
  have hmemS : ∀ i, i ≤ p.length → p.getVert i ∈ S0 := fun i hi =>
    Finset.mem_image.2 ⟨i, by simp only [Finset.mem_range]; omega, rfl⟩
  have hmemR : ∀ i, i ≤ p.length → (p.getVert i ∈ R0 ↔ (Even i ↔ b = true)) := by
    intro i hi
    constructor
    · intro h
      obtain ⟨j, hj, hjv⟩ := Finset.mem_image.1 h
      simp only [Finset.mem_filter, Finset.mem_range] at hj
      have : j = i := hinj (show j ∈ {i | i ≤ p.length} by simp only [Set.mem_setOf_eq]; omega)
        (show i ∈ {i | i ≤ p.length} from hi) hjv
      subst this; exact hj.2
    · intro h
      exact Finset.mem_image.2 ⟨i, by simp only [Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, h⟩, rfl⟩
  have hRS : R0 ⊆ S0 := Finset.image_subset_image (Finset.filter_subset _ _)
  have hind : ∀ x ∈ R0, ∀ y ∈ R0, ¬ G.Adj x y := by
    intro x hx y hy hxy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hy
    simp only [Finset.mem_filter, Finset.mem_range] at hi hj
    rcases lt_trichotomy i j with h | h | h
    · have : j ≠ i + 1 := by
        intro hji; subst hji
        have h1 := hi.2; have h2 := hj.2
        rw [Nat.even_iff] at h1 h2
        by_cases hb : b = true <;> simp [hb] at h1 h2 <;> omega
      exact B1_chord G p hp (by omega) (by omega) hxy
    · subst h; exact G.loopless.irrefl _ hxy
    · have : i ≠ j + 1 := by
        intro hji; subst hji
        have h1 := hi.2; have h2 := hj.2
        rw [Nat.even_iff] at h1 h2
        by_cases hb : b = true <;> simp [hb] at h1 h2 <;> omega
      exact B1_chord G p hp (by omega) (by omega) hxy.symm
  have hstep : ∀ i, i < p.length → (bip G R0 (S0 \ R0)).Adj (p.getVert i) (p.getVert (i + 1)) := by
    intro i hi
    refine ⟨p.adj_getVert_succ hi, ?_⟩
    have h1 := hmemR i hi.le
    have h2 := hmemR (i + 1) hi
    have s1 := hmemS i hi.le
    have s2 := hmemS (i + 1) hi
    by_cases hP : (Even i ↔ b = true)
    · left
      refine ⟨h1.2 hP, Finset.mem_sdiff.2 ⟨s2, fun h => ?_⟩⟩
      have := h2.1 h
      rw [Nat.even_add_one] at this
      tauto
    · right
      refine ⟨Finset.mem_sdiff.2 ⟨s1, fun h => hP (h1.1 h)⟩, h2.2 ?_⟩
      rw [Nat.even_add_one]
      exact B1_iff_not _ _ hP
  have hreach : ∀ i, i ≤ p.length → (bip G R0 (S0 \ R0)).Reachable (p.getVert 0) (p.getVert i) := by
    intro i
    induction i with
    | zero => intro _; exact SimpleGraph.Reachable.refl _
    | succ i ih =>
      intro hi
      exact (ih (by omega)).trans (hstep i (by omega)).reachable
  have hconn : ∀ x ∈ S0, ∀ y ∈ S0, (bip G R0 (S0 \ R0)).Reachable x y := by
    intro x hx y hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hy
    simp only [Finset.mem_range] at hi hj
    exact (hreach i (by omega)).symm.trans (hreach j (by omega))
  obtain ⟨R', h1, h2, h3⟩ := B1_extend G hG _ S0 R0 rfl ⟨p.getVert 0, hmemS 0 (Nat.zero_le _)⟩ hRS hind hconn
  refine ⟨R', h2, ?_, h3, ?_⟩
  · have := h1 _ (hmemS 0 (Nat.zero_le _))
    rw [SimpleGraph.Walk.getVert_zero] at this
    rw [this]
    have h0 := hmemR 0 (Nat.zero_le _)
    rw [SimpleGraph.Walk.getVert_zero] at h0
    rw [h0]; simp
  · intro e he
    obtain ⟨n, hn, rfl⟩ := B1_edge_idx p he
    have a1 := h1 _ (hmemS n hn.le)
    have a2 := h1 _ (hmemS (n + 1) hn)
    have b1 := hmemR n hn.le
    have b2 := hmemR (n + 1) hn
    by_cases hP : (Even n ↔ b = true)
    · refine ⟨p.getVert n, a1.2 (b1.2 hP), p.getVert (n + 1), fun h => ?_, rfl⟩
      have := b2.1 (a2.1 h)
      rw [Nat.even_add_one] at this
      tauto
    · refine ⟨p.getVert (n + 1), a2.2 (b2.2 ?_), p.getVert n, fun h => hP (b1.1 (a1.1 h)), Sym2.eq_swap⟩
      rw [Nat.even_add_one]
      exact B1_iff_not _ _ hP

end

section
open scoped symmDiff

lemma B1_sum_ok (a1 a2 c1 c2 : Prop) [Decidable a1] [Decidable a2] [Decidable c1] [Decidable c2] (f1 : c1 → a1) (f2 : c2 → a2) (hv : a1 → a2 → (c1 ↔ ¬ c2)) :
    3 ≤ (if a1 then (if c1 then 3 else 1) else 2) + (if a2 then (if c2 then 3 else 1) else 2) ∧
    (if a1 then (if c1 then 3 else 1) else 2) + (if a2 then (if c2 then 3 else 1) else 2) ≤ 5 := by
  by_cases a1 <;> by_cases a2 <;> by_cases c1 <;> by_cases c2 <;> simp_all

end

section
open scoped symmDiff

lemma B1_pick1 (K : Finset V) (u : V) (t : ℕ) (c : Prop)
    (h1 : u ∈ K → c → 1 ≤ t) (h2 : u ∈ K → ¬ c → t + 1 ≤ K.card) (ht : t ≤ K.card) :
    ∃ S ⊆ K, S.card = t ∧ (u ∈ K → (u ∈ S ↔ c)) := by
  by_cases hu : u ∈ K
  · have hcard : (K.erase u).card = K.card - 1 := Finset.card_erase_of_mem hu
    by_cases hc : c
    · obtain ⟨S0, hS0, hS0c⟩ := Finset.exists_subset_card_eq (s := K.erase u) (n := t - 1)
        (by have := h1 hu hc; omega)
      have hnot : u ∉ S0 := fun h => by simpa using hS0 h
      refine ⟨insert u S0, ?_, ?_, fun _ => ⟨fun _ => hc, fun _ => Finset.mem_insert_self _ _⟩⟩
      · intro x hx
        rcases Finset.mem_insert.1 hx with rfl | hx
        · exact hu
        · exact Finset.mem_of_mem_erase (hS0 hx)
      · rw [Finset.card_insert_of_notMem hnot, hS0c]; have := h1 hu hc; omega
    · obtain ⟨S0, hS0, hS0c⟩ := Finset.exists_subset_card_eq (s := K.erase u) (n := t)
        (by have := h2 hu hc; omega)
      have hnot : u ∉ S0 := fun h => by simpa using hS0 h
      exact ⟨S0, fun x hx => Finset.mem_of_mem_erase (hS0 hx), hS0c, fun _ => ⟨fun h => absurd h hnot, fun h => absurd h hc⟩⟩
  · obtain ⟨S0, hS0, hS0c⟩ := Finset.exists_subset_card_eq (s := K) (n := t) ht
    exact ⟨S0, hS0, hS0c, fun h => absurd h hu⟩

end

section
open scoped symmDiff

lemma B1_pick2 (K : Finset V) (u1 u2 : V) (hne : u1 ≠ u2) (t : ℕ)
    (h : u1 ∈ K → u2 ∈ K → 1 ≤ t ∧ t + 1 ≤ K.card) (ht : t ≤ K.card) :
    ∃ S ⊆ K, S.card = t ∧ (u1 ∈ K → u2 ∈ K → (u1 ∈ S ↔ u2 ∉ S)) := by
  by_cases hu : u1 ∈ K ∧ u2 ∈ K
  · obtain ⟨hu1, hu2⟩ := hu
    have hc1 : (K.erase u1).card = K.card - 1 := Finset.card_erase_of_mem hu1
    have hu2' : u2 ∈ K.erase u1 := Finset.mem_erase.2 ⟨hne.symm, hu2⟩
    have hc2 : ((K.erase u1).erase u2).card = K.card - 1 - 1 := by
      rw [Finset.card_erase_of_mem hu2', hc1]
    have hh := h hu1 hu2
    obtain ⟨S0, hS0, hS0c⟩ := Finset.exists_subset_card_eq (s := (K.erase u1).erase u2) (n := t - 1)
      (by omega)
    have hn1 : u1 ∉ S0 := fun hh => by
      have := hS0 hh; simp at this
    have hn2 : u2 ∉ S0 := fun hh => by
      have := hS0 hh; simp at this
    refine ⟨insert u1 S0, ?_, ?_, fun _ _ => ?_⟩
    · intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact hu1
      · exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase (hS0 hx))
    · rw [Finset.card_insert_of_notMem hn1, hS0c]; omega
    · constructor
      · intro _ h2; rcases Finset.mem_insert.1 h2 with h2 | h2
        · exact hne h2.symm
        · exact hn2 h2
      · intro _; exact Finset.mem_insert_self _ _
  · obtain ⟨S0, hS0, hS0c⟩ := Finset.exists_subset_card_eq (s := K) (n := t) ht
    exact ⟨S0, hS0, hS0c, fun h1 h2 => absurd ⟨h1, h2⟩ hu⟩

end

section
open scoped symmDiff

theorem lemma5_path (H : SimpleGraph V) (R B : Finset V) (hd : Disjoint R B)
    (hb : ∀ u v, H.Adj u v → (u ∈ R ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ R))
    (hc : ∀ u ∈ R ∪ B, ∀ v ∈ R ∪ B, H.Reachable u v)
    (α : V → ℕ) (hα : ∀ v ∈ B, α v + 1 = 2 * H.degree v ∨ α v = 2 * H.degree v ∨
      α v = 2 * H.degree v + 1)
    (R' : Finset V) (hR' : R' ⊆ R) (hpar : Even (R'.card + ∑ v ∈ B, α v))
    (k : ℕ) (hk : 3 ≤ k) (p : ℕ → V) (hinj : Set.InjOn p (Set.Iio k))
    (hadj : ∀ i, i + 1 < k → H.Adj (p i) (p (i + 1)))
    (h0 : p 0 ∈ B) (hk' : p (k - 1) ∈ B) :
    ∃ ω, Wt3 H ω ∧ (∀ v ∈ R, Even (sdeg H ω v) ↔ v ∉ R') ∧ (∀ v ∈ B, sdeg H ω v = α v) ∧
      (α (p 0) = 2 * H.degree (p 0) + 1 → ω s(p 0, p 1) ≠ 1) ∧
      (α (p 0) ≠ 2 * H.degree (p 0) + 1 → ω s(p 0, p 1) ≠ 3) ∧
      (∀ i, i + 2 < k → p (i + 1) ∈ B →
        3 ≤ ω s(p i, p (i + 1)) + ω s(p (i + 1), p (i + 2)) ∧
        ω s(p i, p (i + 1)) + ω s(p (i + 1), p (i + 2)) ≤ 5) ∧
      (α (p (k - 1)) = 2 * H.degree (p (k - 1)) + 1 → ω s(p (k - 2), p (k - 1)) ≠ 1) ∧
      (α (p (k - 1)) ≠ 2 * H.degree (p (k - 1)) + 1 → ω s(p (k - 2), p (k - 1)) ≠ 3) := by
  classical
  let t : V → ZMod 2 := fun x => if x ∈ R then (if x ∈ R' then 1 else 0) else
    if x ∈ B then (α x : ZMod 2) else 0
  have ht0 : ∀ x, x ∉ R ∪ B → t x = 0 := by
    intro x hx
    simp only [Finset.mem_union, not_or] at hx
    simp [t, hx.1, hx.2]
  have hsum : ∑ x ∈ R ∪ B, t x = 0 := by
    rw [Finset.sum_union hd]
    have e1 : ∑ x ∈ R, t x = (R'.card : ZMod 2) := by
      rw [Finset.sum_congr rfl (fun x hx => show t x = if x ∈ R' then 1 else 0 by simp [t, hx])]
      rw [Finset.sum_boole]; congr 2; ext x; simp only [Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨hR' h, h⟩⟩
    have e2 : ∑ x ∈ B, t x = ((∑ v ∈ B, α v : ℕ) : ZMod 2) := by
      push_cast
      refine Finset.sum_congr rfl (fun x hx => ?_)
      have : x ∉ R := fun h => Finset.disjoint_left.1 hd h hx
      simp [t, this, hx]
    rw [e1, e2, ← Nat.cast_add]
    exact (ZMod.natCast_eq_zero_iff_even).2 hpar
  obtain ⟨F, hF, hdF⟩ := B1_Real_of_sum H (R ∪ B) hc _ t rfl ht0 hsum
  have hKsub : ∀ v, (univ.filter (fun u => s(v,u) ∈ F)) ⊆ univ.filter (H.Adj v) := by
    intro v u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    exact hF _ hu
  have hnei : ∀ i j, i < k → j < k → p i = p j → i = j :=
    fun i j hi hj h => hinj (Set.mem_Iio.2 hi) (Set.mem_Iio.2 hj) h
  have hS : ∀ v, ∃ S : Finset V, S ⊆ univ.filter (fun u => s(v,u) ∈ F) ∧
      (v ∈ B → 2 * S.card + 2 * H.degree v = α v + B1_dF F v) ∧
      (v = p 0 → p 1 ∈ univ.filter (fun u => s(v,u) ∈ F) → (p 1 ∈ S ↔ α v = 2 * H.degree v + 1)) ∧
      (v = p (k - 1) → p (k - 2) ∈ univ.filter (fun u => s(v,u) ∈ F) →
        (p (k - 2) ∈ S ↔ α v = 2 * H.degree v + 1)) ∧
      (v ∈ B → ∀ i, 0 < i → i + 1 < k → v = p i → p (i - 1) ∈ univ.filter (fun u => s(v,u) ∈ F) →
        p (i + 1) ∈ univ.filter (fun u => s(v,u) ∈ F) → (p (i - 1) ∈ S ↔ p (i + 1) ∉ S)) := by
    intro v
    by_cases hv : v ∈ B
    · have hvR : v ∉ R := fun h => Finset.disjoint_left.1 hd h hv
      have hk : (B1_dF F v : ZMod 2) = (α v : ZMod 2) := by rw [hdF v]; simp [t, hvR, hv]
      have hk2 : B1_dF F v % 2 = α v % 2 := (ZMod.natCast_eq_natCast_iff' _ _ 2).1 hk
      have hle : B1_dF F v ≤ H.degree v := by
        rw [B1_degree_eq]; exact Finset.card_le_card (hKsub v)
      have h3 := hα v hv
      have hkd : (univ.filter (fun u => s(v,u) ∈ F)).card = B1_dF F v := rfl
      by_cases e0 : v = p 0
      · refine ?_
        obtain ⟨S, hS1, hS2, hS3⟩ := B1_pick1 (univ.filter (fun u => s(v,u) ∈ F)) (p 1)
          ((α v + B1_dF F v - 2 * H.degree v) / 2) (α v = 2 * H.degree v + 1)
          (fun hu hc => by have := Finset.card_pos.2 ⟨_, hu⟩; rw [hkd] at this; omega)
          (fun hu hc => by have := Finset.card_pos.2 ⟨_, hu⟩; rw [hkd] at this; omega)
          (by rw [hkd]; omega)
        refine ⟨S, hS1, fun _ => by omega, fun _ => hS3, fun h => ?_, fun _ i hi hik h => ?_⟩
        · have := hnei _ _ (by omega) (by omega) (e0.symm.trans h); omega
        · have := hnei _ _ (by omega) (by omega) (e0.symm.trans h); omega
      · by_cases ek : v = p (k - 1)
        · obtain ⟨S, hS1, hS2, hS3⟩ := B1_pick1 (univ.filter (fun u => s(v,u) ∈ F)) (p (k - 2))
            ((α v + B1_dF F v - 2 * H.degree v) / 2) (α v = 2 * H.degree v + 1)
            (fun hu hc => by have := Finset.card_pos.2 ⟨_, hu⟩; rw [hkd] at this; omega)
            (fun hu hc => by have := Finset.card_pos.2 ⟨_, hu⟩; rw [hkd] at this; omega)
            (by rw [hkd]; omega)
          refine ⟨S, hS1, fun _ => by omega, fun h => absurd h e0, fun _ => hS3, fun _ i hi hik h => ?_⟩
          have := hnei _ _ (by omega) (by omega) (ek.symm.trans h); omega
        · by_cases ei : ∃ i, 0 < i ∧ i + 1 < k ∧ v = p i
          · obtain ⟨i, hi, hik, hvi⟩ := ei
            have hne : p (i - 1) ≠ p (i + 1) := fun h => by
              have := hnei _ _ (by omega) (by omega) h; omega
            obtain ⟨S, hS1, hS2, hS3⟩ := B1_pick2 (univ.filter (fun u => s(v,u) ∈ F)) (p (i - 1)) (p (i + 1)) hne
              ((α v + B1_dF F v - 2 * H.degree v) / 2)
              (fun hu1 hu2 => by
                have hc : ({p (i - 1), p (i + 1)} : Finset V) ⊆ univ.filter (fun u => s(v,u) ∈ F) := by
                  intro x hx
                  rcases Finset.mem_insert.1 hx with rfl | hx
                  · exact hu1
                  · rw [Finset.mem_singleton.1 hx]; exact hu2
                have := Finset.card_le_card hc
                rw [Finset.card_pair hne, hkd] at this
                omega)
              (by rw [hkd]; omega)
            refine ⟨S, hS1, fun _ => by omega, fun h => absurd h e0, fun h => absurd h ek, fun _ j hj hjk h => ?_⟩
            have hij := hnei _ _ (by omega) (by omega) (hvi.symm.trans h)
            subst hij
            exact hS3
          · obtain ⟨S, hS1, hS2⟩ := Finset.exists_subset_card_eq
              (s := univ.filter (fun u => s(v,u) ∈ F)) (n := (α v + B1_dF F v - 2 * H.degree v) / 2)
              (by rw [hkd]; omega)
            refine ⟨S, hS1, fun _ => by omega, fun h => absurd h e0, fun h => absurd h ek, fun _ i hi hik h => ?_⟩
            exact absurd ⟨i, hi, hik, h⟩ ei
    · refine ⟨∅, by simp, fun h => absurd h hv, fun h => ?_, fun h => ?_, fun h => absurd h hv⟩
      · exact absurd (h ▸ h0) hv
      · exact absurd (h ▸ hk') hv
  choose S hSsub hSc hSE0 hSEk hSEi using hS
  let g : V → V → ℕ := fun a b => if s(a,b) ∈ F then
    (if (a ∈ B ∧ b ∈ S a) ∨ (b ∈ B ∧ a ∈ S b) then 3 else 1) else 2
  have gsymm : ∀ a b, g a b = g b a := by
    intro a b
    by_cases h1 : s(a,b) ∈ F
    · have h1' : s(b,a) ∈ F := by rwa [Sym2.eq_swap]
      simp [g, h1, h1', or_comm]
    · have h1' : s(b,a) ∉ F := by rwa [Sym2.eq_swap]
      simp [g, h1, h1']
  let ω : Sym2 V → ℕ := Sym2.lift ⟨g, gsymm⟩
  have hω : ∀ a b, ω s(a,b) = g a b := fun a b => rfl
  have hω' : ∀ v u, (s(v,u) ∈ F → ω s(v,u) = 1 ∨ ω s(v,u) = 3) ∧ (s(v,u) ∉ F → ω s(v,u) = 2) := by
    intro v u
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [hω]; simp only [g, h]; split_ifs <;> simp
    · rw [hω]; simp only [g, h]; simp
  have hW : Wt3 H ω := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      rw [hω]; simp only [g]; split_ifs <;> omega
  have hKeq : ∀ v, (univ.filter (H.Adj v)).filter (fun u => s(v,u) ∈ F) =
      univ.filter (fun u => s(v,u) ∈ F) := by
    intro v; ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h.2, fun h => ⟨by simpa using hKsub v (by simpa using h), h⟩⟩
  have hwB : ∀ v ∈ B, ∀ u, H.Adj v u →
      ω s(v,u) = if s(v,u) ∈ F then (if u ∈ S v then 3 else 1) else 2 := by
    intro v hv u hvu
    have huB : u ∉ B := by
      rcases hb v u hvu with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact absurd hv (fun h => Finset.disjoint_left.1 hd h1 h)
      · exact fun h => Finset.disjoint_left.1 hd h2 h
    rw [hω]; simp only [g, hv, huB, true_and, false_and, or_false]
  have hKmem : ∀ v u, u ∈ univ.filter (fun u => s(v,u) ∈ F) ↔ s(v,u) ∈ F := by intro v u; simp
  have hSF : ∀ v u, u ∈ S v → s(v,u) ∈ F := fun v u h => (hKmem v u).1 (hSsub v h)
  have hRuB : ∀ v u, v ∈ B → H.Adj v u → u ∉ B := by
    intro v u hv hvu
    rcases hb v u hvu with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact absurd hv (fun h => Finset.disjoint_left.1 hd h1 h)
    · exact fun h => Finset.disjoint_left.1 hd h2 h
  have hend : ∀ v u, v ∈ B → H.Adj v u → (u ∈ univ.filter (fun u => s(v,u) ∈ F) →
      (u ∈ S v ↔ α v = 2 * H.degree v + 1)) →
      (α v = 2 * H.degree v + 1 → ω s(v,u) ≠ 1) ∧ (α v ≠ 2 * H.degree v + 1 → ω s(v,u) ≠ 3) := by
    intro v u hv hvu hc
    rw [hwB v hv u hvu]
    by_cases hF : s(v,u) ∈ F
    · have := hc ((hKmem v u).2 hF)
      constructor
      · intro ha; simp only [hF, if_true]; have := this.2 ha; simp [this]
      · intro ha; simp only [hF, if_true]
        have : u ∉ S v := fun h => ha (this.1 h)
        simp [this]
    · simp [hF]
  refine ⟨ω, hW, fun v hv => ?_, fun v hv => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hf := B1_sdeg_formula H F ω v (fun u _ => hω' v u)
    rw [hKeq v] at hf
    have hkk : (B1_dF F v : ZMod 2) = if v ∈ R' then 1 else 0 := by rw [hdF v]; simp [t, hv]
    rw [Nat.even_iff]
    by_cases hv' : v ∈ R'
    · have : (B1_dF F v : ZMod 2) = ((1 : ℕ) : ZMod 2) := by rw [hkk]; simp [hv']
      have h2 := (ZMod.natCast_eq_natCast_iff' _ _ 2).1 this
      have : B1_dF F v = (univ.filter (fun u => s(v,u) ∈ F)).card := rfl
      simp only [hv', not_true_eq_false, iff_false]
      omega
    · have : (B1_dF F v : ZMod 2) = ((0 : ℕ) : ZMod 2) := by rw [hkk]; simp [hv']
      have h2 := (ZMod.natCast_eq_natCast_iff' _ _ 2).1 this
      have : B1_dF F v = (univ.filter (fun u => s(v,u) ∈ F)).card := rfl
      simp only [hv', not_false_eq_true, iff_true]
      omega
  · have hf := B1_sdeg_formula H F ω v (fun u _ => hω' v u)
    rw [hKeq v] at hf
    have hvR : v ∉ R := fun h => Finset.disjoint_left.1 hd h hv
    have hT : (univ.filter (H.Adj v)).filter (fun u => ω s(v,u) = 3) = S v := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hu, h3⟩
        have huB : u ∉ B := fun h => by
          rcases hb v u hu with ⟨h1, _⟩ | ⟨_, h2⟩
          · exact hvR h1
          · exact Finset.disjoint_left.1 hd h2 h
        have h3' : (v ∈ B ∧ u ∈ S v) ∨ (u ∈ B ∧ v ∈ S u) := by
          by_contra h5
          rw [hω] at h3; simp only [g] at h3
          by_cases h4 : s(v,u) ∈ F <;> simp [h4, h5] at h3
        rcases h3' with ⟨_, h6⟩ | ⟨h6, _⟩
        · exact h6
        · exact absurd h6 huB
      · intro hu
        have h1 := hSsub v hu
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1
        refine ⟨by simpa using hKsub v (by simpa using h1), ?_⟩
        rw [hω]; simp only [g, h1, hv, hu]; simp
    rw [hT] at hf
    have h1 := hSc v hv
    have h2 : B1_dF F v = (univ.filter (fun u => s(v,u) ∈ F)).card := rfl
    have h3 := B1_degree_eq H v
    omega

  · exact (hend _ _ h0 (hadj 0 (by omega)) (hSE0 _ rfl)).1
  · exact (hend _ _ h0 (hadj 0 (by omega)) (hSE0 _ rfl)).2
  · intro i hi hvB
    have hv := hSEi (p (i + 1)) hvB (i + 1) (by omega) (by omega) rfl
    simp only [Nat.add_sub_cancel] at hv
    have a1 : H.Adj (p (i + 1)) (p i) := (hadj i (by omega)).symm
    have a2 : H.Adj (p (i + 1)) (p (i + 2)) := hadj (i + 1) (by omega)
    rw [Sym2.eq_swap (a := p i) (b := p (i + 1)), hwB _ hvB _ a1, hwB _ hvB _ a2]
    have f1 := hSF (p (i + 1)) (p i)
    have f2 := hSF (p (i + 1)) (p (i + 2))
    simp only [hKmem] at hv
    exact B1_sum_ok _ _ _ _ f1 f2 hv
  · have hk2 : k - 2 + 1 = k - 1 := by omega
    have a1 : H.Adj (p (k - 1)) (p (k - 2)) := by
      have := hadj (k - 2) (by omega); rw [hk2] at this; exact this.symm
    rw [Sym2.eq_swap (a := p (k - 2)) (b := p (k - 1))]
    exact (hend _ _ hk' a1 (hSEk _ rfl)).1
  · have hk2 : k - 2 + 1 = k - 1 := by omega
    have a1 : H.Adj (p (k - 1)) (p (k - 2)) := by
      have := hadj (k - 2) (by omega); rw [hk2] at this; exact this.symm
    rw [Sym2.eq_swap (a := p (k - 2)) (b := p (k - 1))]
    exact (hend _ _ hk' a1 (hSEk _ rfl)).2

end

theorem B2_conflict {α : Type*} [DecidableEq α] (R' : Finset α) (hk : 2 ≤ R'.card) (t : α → ℕ) (c : ℕ) :
    ∃ S ⊆ R', ∀ v ∈ R', c + 2 * S.card ≠ t v + 2 * (if v ∈ S then 1 else 0) := by
  by_cases hc : ∀ v ∈ R', t v ≠ c
  · refine ⟨∅, empty_subset _, fun v hv => ?_⟩
    simpa [eq_comm] using hc v hv
  push Not at hc
  obtain ⟨v1, hv1, hv1c⟩ := hc
  set T := R'.image t with hT
  have hcT : c ∈ T := mem_image.2 ⟨v1, hv1, hv1c⟩
  have hex : ∃ x, 0 < x ∧ c + 2 * x ∉ T := by
    refine ⟨T.sup id + 1, by omega, fun h => ?_⟩
    have := Finset.le_sup (f := id) h
    simp only [id] at this; omega
  classical
  set x := Nat.find hex with hxdef
  have hx0 : 0 < x := (Nat.find_spec hex).1
  have hxT : c + 2 * x ∉ T := (Nat.find_spec hex).2
  have hmin : ∀ y < x, c + 2 * y ∈ T := by
    intro y hy
    by_cases h0 : y = 0
    · subst h0; simpa using hcT
    · by_contra hn
      exact Nat.find_min hex hy ⟨by omega, hn⟩
  have hrange : ∀ m ≤ x, m ≤ T.card := by
    intro m hm
    have hsub : (range m).image (fun y => c + 2 * y) ⊆ T := by
      intro z hz
      obtain ⟨y, hy, rfl⟩ := mem_image.1 hz
      exact hmin y (by have := mem_range.1 hy; omega)
    have hinj : Function.Injective (fun y : ℕ => c + 2 * y) := fun a b h => by simp at h; omega
    have := card_le_card hsub
    rwa [card_image_of_injective _ hinj, card_range] at this
  have hTk : T.card ≤ R'.card := card_image_le
  have hxk : x ≤ R'.card := by
    by_contra h
    push Not at h
    have := hrange (R'.card + 1) (by omega)
    omega
  have htv : ∀ v ∈ R', t v ≠ c + 2 * x := fun v hv h => hxT (mem_image.2 ⟨v, hv, h⟩)
  set U := R'.filter (fun v => c + 2 * x < t v) with hU
  set L := R'.filter (fun v => t v < c + 2 * x) with hL
  have hUL : U.card + L.card = R'.card := by
    rw [← card_union_of_disjoint]
    · congr 1
      ext v
      simp only [hU, hL, mem_union, mem_filter]
      constructor
      · rintro (h | h) <;> exact h.1
      · intro hv
        have := htv v hv
        by_cases h : c + 2 * x < t v
        · exact Or.inl ⟨hv, h⟩
        · exact Or.inr ⟨hv, by omega⟩
    · rw [Finset.disjoint_left]
      intro v h1 h2
      simp only [hU, hL, mem_filter] at h1 h2
      omega
  by_cases hA : x ≤ U.card
  · obtain ⟨S, hSU, hSc⟩ := Finset.exists_subset_card_eq hA
    refine ⟨S, fun v hv => (mem_filter.1 (hSU hv)).1, fun v hv => ?_⟩
    by_cases hvS : v ∈ S
    · have := (mem_filter.1 (hSU hvS)).2
      simp [hvS, hSc]; omega
    · have := htv v hv
      simp [hvS, hSc]; omega
  · push Not at hA
    by_cases hB : x < R'.card
    · have hLc : R'.card - x - 1 ≤ L.card := by omega
      obtain ⟨L0, hL0, hL0c⟩ := Finset.exists_subset_card_eq hLc
      have hL0R : L0 ⊆ R' := fun v hv => (mem_filter.1 (hL0 hv)).1
      refine ⟨R' \ L0, sdiff_subset, fun v hv => ?_⟩
      have hSc : (R' \ L0).card = x + 1 := by
        rw [card_sdiff_of_subset hL0R]; omega
      rw [hSc]
      by_cases hvS : v ∈ R' \ L0
      · have := htv v hv
        simp only [hvS, if_true]; omega
      · have hvL0 : v ∈ L0 := by
          simp only [mem_sdiff, not_and, not_not] at hvS; exact hvS hv
        have := (mem_filter.1 (hL0 hvL0)).2
        simp only [hvS, if_false]; omega
    · have hxe : x = R'.card := by omega
      have hTe : T.card = R'.card := by have := hrange x le_rfl; omega
      have hinj : Set.InjOn t R' := Finset.injOn_of_card_image_eq hTe
      have h1 : c + 2 * 1 ∈ T := hmin 1 (by omega)
      obtain ⟨v2, hv2, hv2t⟩ := mem_image.1 h1
      refine ⟨{v2}, by simpa using hv2, fun v hv => ?_⟩
      by_cases hvv : v = v2
      · subst hvv; simp; omega
      · have : t v ≠ t v2 := fun h => hvv (hinj hv hv2 h)
        simp [hvv]; omega

theorem B2_bip_adj {G : SimpleGraph V} {R B : Finset V} {u v : V} :
    (bip G R B).Adj u v ↔ G.Adj u v ∧ ((u ∈ R ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ R)) := Iff.rfl

theorem B2_assemble (G : SimpleGraph V) (v0 : V) (R B : Finset V) (hd : Disjoint R B)
    (hind : ∀ u ∈ R, ∀ v ∈ R, ¬ G.Adj u v) (hv0 : v0 ∉ R ∪ B)
    (hdom : ∀ u v, G.Adj u v → (u ∈ R ∪ B ∨ u = v0) ∧ (v ∈ R ∪ B ∨ v = v0))
    (ω1 ω2 : Sym2 V → ℕ) (g : V → ℕ) :
    ∃ ω : Sym2 V → ℕ,
      (∀ a b, a ≠ v0 → b ≠ v0 → ω s(a, b) = if a ∈ B ∧ b ∈ B then ω1 s(a, b) else ω2 s(a, b)) ∧
      (∀ b, ω s(v0, b) = g b) ∧
      (∀ v ∈ B, sdeg G ω v = sdeg (bip G B B) ω1 v + sdeg (bip G R B) ω2 v +
        (if G.Adj v0 v then g v else 0)) ∧
      (∀ v ∈ R, sdeg G ω v = sdeg (bip G R B) ω2 v + (if G.Adj v0 v then g v else 0)) ∧
      sdeg G ω v0 = ∑ u ∈ univ.filter (G.Adj v0), g u := by
  let F : V → V → ℕ := fun a b => if a = v0 then g b else if b = v0 then g a else
    if a ∈ B ∧ b ∈ B then ω1 s(a, b) else ω2 s(a, b)
  have hF : ∀ a b, F a b = F b a := by
    intro a b
    by_cases ha : a = v0 <;> by_cases hb : b = v0 <;>
      simp [F, ha, hb, Sym2.eq_swap, and_comm]
  let ω : Sym2 V → ℕ := Sym2.lift ⟨F, hF⟩
  have hω : ∀ a b, ω s(a, b) = F a b := fun a b => by simp [ω]
  have hωa : ∀ a b, a ≠ v0 → b ≠ v0 →
      ω s(a, b) = if a ∈ B ∧ b ∈ B then ω1 s(a, b) else ω2 s(a, b) := by
    intro a b ha hb; simp [hω, F, ha, hb]
  have hωb : ∀ b, ω s(v0, b) = g b := fun b => by simp [hω, F]
  have key : ∀ v, v ≠ v0 → (v ∈ B ∨ v ∈ R) → ∀ u,
      (if G.Adj v u then ω s(v, u) else 0) =
        (if (bip G B B).Adj v u then ω1 s(v, u) else 0) +
        (if (bip G R B).Adj v u then ω2 s(v, u) else 0) +
        (if u = v0 then (if G.Adj v0 v then g v else 0) else 0) := by
    intro v hvv hv u
    have hv0R : v0 ∉ R := fun h => hv0 (mem_union_left _ h)
    have hv0B : v0 ∉ B := fun h => hv0 (mem_union_right _ h)
    have hBR : ∀ x, x ∈ B → x ∉ R := fun x hx h => Finset.disjoint_left.1 hd h hx
    have hRB : ∀ x, x ∈ R → x ∉ B := fun x hx h => Finset.disjoint_left.1 hd hx h
    by_cases hu : u = v0
    · rw [hu]
      simp [B2_bip_adj, hω, F, hvv, hv0B, hv0R, G.adj_comm]
    · by_cases hadj : G.Adj v u
      · have hvu := hωa v u hvv hu
        have huRB : u ∈ R ∪ B := ((hdom v u hadj).2).resolve_right hu
        rw [mem_union] at huRB
        rcases hv with hvB | hvR <;> rcases huRB with huR | huB
        · simp [B2_bip_adj, hvu, hadj, hu, hvB, huR, hBR v hvB, hRB u huR]
        · simp [B2_bip_adj, hvu, hadj, hu, hvB, huB, hBR v hvB, hBR u huB]
        · exact absurd hadj (hind v hvR u huR)
        · simp [B2_bip_adj, hvu, hadj, hu, hvR, huB, hBR u huB, hRB v hvR]
      · simp [B2_bip_adj, hadj, hu]
  have hcst : ∀ c : ℕ, c = ∑ u : V, (if u = v0 then c else 0) := fun c => by simp
  have hsplit : ∀ v, v ≠ v0 → (v ∈ B ∨ v ∈ R) →
      sdeg G ω v = sdeg (bip G B B) ω1 v + sdeg (bip G R B) ω2 v + (if G.Adj v0 v then g v else 0) := by
    intro v hvv hv
    simp only [sdeg, Finset.sum_filter]
    rw [hcst (if G.Adj v0 v then g v else 0), ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun u _ => key v hvv hv u)
  have hBne : ∀ v, v ∈ B → v ≠ v0 := fun v hv h => hv0 (mem_union_right _ (h ▸ hv))
  have hRne : ∀ v, v ∈ R → v ≠ v0 := fun v hv h => hv0 (mem_union_left _ (h ▸ hv))
  refine ⟨ω, hωa, hωb, fun v hv => hsplit v (hBne v hv) (Or.inl hv), fun v hv => ?_, ?_⟩
  · have hnB : v ∉ B := fun h => Finset.disjoint_left.1 hd hv h
    rw [hsplit v (hRne v hv) (Or.inr hv)]
    have : sdeg (bip G B B) ω1 v = 0 := by
      simp only [sdeg]
      apply Finset.sum_eq_zero
      intro u hu
      simp [B2_bip_adj, hnB] at hu
    omega
  · simp only [sdeg]
    exact Finset.sum_congr rfl (fun u _ => hωb u)

theorem B2_sum_mod (s : Finset V) (a : V → ℕ) :
    (∑ v ∈ s, a v) % 2 = (s.filter (fun v => a v % 2 = 1)).card % 2 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.filter_insert]
    by_cases h : a x % 2 = 1
    · rw [if_pos h, Finset.card_insert_of_notMem (by simp [hx])]
      omega
    · rw [if_neg h]
      omega

theorem B2_degR_pos (G : SimpleGraph V) (R B : Finset V) (hg : Good G R B) (v : V) (hv : v ∈ B) :
    1 ≤ (R.filter (G.Adj v)).card := by
  obtain ⟨k, hk⟩ := hg.even
  have h2 : 1 < B.card := by
    have : 0 < B.card := Finset.card_pos.2 ⟨v, hv⟩
    omega
  obtain ⟨u, hu, huv⟩ := Finset.exists_mem_ne h2 v
  have hr := hg.conn v (mem_union_right _ hv) u (mem_union_right _ hu)
  obtain ⟨p⟩ := hr
  cases p with
  | nil => exact absurd rfl huv
  | @cons _ w _ hadj _ =>
    have hvR : v ∉ R := fun h => Finset.disjoint_left.1 hg.disj h hv
    rcases hadj.2 with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact absurd h1 hvR
    · exact Finset.card_pos.2 ⟨w, Finset.mem_filter.2 ⟨h2, hadj.1⟩⟩

theorem B2_bip_degree (G : SimpleGraph V) (R B : Finset V) (hd : Disjoint R B) (v : V) (hv : v ∈ B) :
    (bip G R B).degree v = (R.filter (G.Adj v)).card := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  congr 1
  ext u
  have hvR : v ∉ R := fun h => Finset.disjoint_left.1 hd h hv
  simp [B2_bip_adj, hvR, hv, and_comm]

theorem B2_path_par (H : SimpleGraph V) (R B : Finset V) (hd : Disjoint R B)
    (hb : ∀ u v, H.Adj u v → (u ∈ R ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ R))
    (k : ℕ) (p : ℕ → V) (hadjp : ∀ i, i + 1 < k → H.Adj (p i) (p (i + 1))) (h0 : p 0 ∈ B) :
    ∀ i, i < k → (p i ∈ B ↔ Even i) := by
  intro i
  induction i with
  | zero => intro _; simp [h0]
  | succ n ih =>
    intro hn
    have ih' := ih (by omega)
    rw [Nat.even_add_one]
    rcases hb _ _ (hadjp n hn) with ⟨a, b⟩ | ⟨a, b⟩
    · have hn1 : ¬ Even n := fun h => Finset.disjoint_left.1 hd a (ih'.2 h)
      exact ⟨fun _ => hn1, fun _ => b⟩
    · have hn1 : p (n + 1) ∉ B := fun h => Finset.disjoint_left.1 hd b h
      exact ⟨fun h => absurd h hn1, fun h => absurd (ih'.1 a) h⟩

theorem B2_path_mod (H : SimpleGraph V) (R B : Finset V) (hd : Disjoint R B)
    (hb : ∀ u v, H.Adj u v → (u ∈ R ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ R))
    (ω : Sym2 V → ℕ) (hW : Wt3 H ω)
    (k : ℕ) (hk : 3 ≤ k) (p : ℕ → V) (hinj : Set.InjOn p (Set.Iio k))
    (hadjp : ∀ i, i + 1 < k → H.Adj (p i) (p (i + 1)))
    (h0 : p 0 ∈ B) (hk' : p (k - 1) ∈ B)
    (σ : ℤ) (hσ : σ = 1 ∨ σ = -1)
    (hend0 : 1 ≤ (ω s(p 0, p 1) : ℤ) + σ ∧ (ω s(p 0, p 1) : ℤ) + σ ≤ 3)
    (hendk : 1 ≤ (ω s(p (k - 2), p (k - 1)) : ℤ) + σ ∧ (ω s(p (k - 2), p (k - 1)) : ℤ) + σ ≤ 3)
    (hmid : ∀ i, 0 < i → i + 1 < k → p i ∈ B →
      3 ≤ ω s(p (i - 1), p i) + ω s(p i, p (i + 1)) ∧
        ω s(p (i - 1), p i) + ω s(p i, p (i + 1)) ≤ 5) :
    ∃ ω' : Sym2 V → ℕ, Wt3 H ω' ∧
      (∀ v, (∀ i, i < k → p i ≠ v) → sdeg H ω' v = sdeg H ω v) ∧
      (∀ v ∈ B, (sdeg H ω' v : ℤ) = sdeg H ω v + (if v = p 0 then σ else 0) +
        (if v = p (k - 1) then σ else 0)) ∧
      (∀ v ∈ R, sdeg H ω' v % 2 = sdeg H ω v % 2) := by
  have hpar := B2_path_par H R B hd hb k p hadjp h0
  have hkodd : k % 2 = 1 := by
    have := (hpar (k - 1) (by omega)).1 hk'
    rw [Nat.even_iff] at this; omega
  have hI : ∀ i j, i < k → j < k → p i = p j → i = j :=
    fun i j hi hj h => hinj (Set.mem_Iio.2 hi) (Set.mem_Iio.2 hj) h
  obtain ⟨e, he⟩ : ∃ e : ℕ → Sym2 V, ∀ i, e i = s(p i, p (i + 1)) := ⟨_, fun _ => rfl⟩
  have hinjE : ∀ i j, i + 1 < k → j + 1 < k → e i = e j → i = j := by
    intro i j hi hj h
    rw [he, he, Sym2.eq_iff] at h
    rcases h with ⟨h1, _⟩ | ⟨h1, h2⟩
    · exact hI i j (by omega) (by omega) h1
    · have := hI i (j + 1) (by omega) (by omega) h1
      have := hI (i + 1) j (by omega) (by omega) h2
      omega
  have hωe : ∀ i, i + 1 < k → 1 ≤ ω (e i) ∧ ω (e i) ≤ 3 := fun i hi => by
    rw [he]; exact hW _ (hadjp i hi)
  obtain ⟨τ, hτ⟩ : ∃ τ : ℕ → ℤ, ∀ i, τ i =
      if ω (e i) ≤ 2 ∧ 2 ≤ ω (e (i + 1)) then 1 else -1 := ⟨_, fun _ => rfl⟩
  obtain ⟨σs, hσs⟩ : ∃ σs : ℕ → ℤ, ∀ i, σs i =
      if i = 0 ∨ i = k - 2 then σ else if i % 2 = 1 then τ i else - τ (i - 1) :=
    ⟨_, fun _ => rfl⟩
  have hσs1 : ∀ i, σs i = 1 ∨ σs i = -1 := by
    intro i
    rw [hσs i]
    split_ifs
    · exact hσ
    · rw [hτ]; split_ifs <;> simp
    · rw [hτ]; split_ifs <;> simp
  have hσs0 : σs 0 = σ := by rw [hσs 0]; simp
  have hσsk : σs (k - 2) = σ := by rw [hσs (k - 2)]; simp
  have hσsm : ∀ i, 0 < i → i + 2 < k → i % 2 = 1 → σs i = τ i := by
    intro i h1 h2 h3
    rw [hσs i, if_neg (by omega), if_pos h3]
  have hσsn : ∀ i, 0 < i → i + 2 < k → i % 2 = 0 → σs i = - τ (i - 1) := by
    intro i h1 h2 h3
    rw [hσs i, if_neg (by omega), if_neg (by omega)]
  have hF4 : ∀ i, i + 1 < k → 1 ≤ (ω (e i) : ℤ) + σs i ∧ (ω (e i) : ℤ) + σs i ≤ 3 := by
    intro i hi
    have hb1 := hωe i hi
    by_cases hi0 : i = 0
    · subst hi0; rw [hσs0, he]; simpa using hend0
    by_cases hik : i = k - 2
    · subst hik; rw [hσsk, he]
      have : k - 2 + 1 = k - 1 := by omega
      rw [this]; exact hendk
    by_cases hodd : i % 2 = 1
    · rw [hσsm i (by omega) (by omega) hodd, hτ]
      have hm := hmid (i + 1) (by omega) (by omega)
        ((hpar (i + 1) (by omega)).2 (by rw [Nat.even_iff]; omega))
      simp only [Nat.add_sub_cancel, ← he] at hm
      have hb2 := hωe (i + 1) (by omega)
      split_ifs with hc <;> omega
    · have hev : i % 2 = 0 := by omega
      rw [hσsn i (by omega) (by omega) hev, hτ]
      have hm := hmid i (by omega) (by omega)
        ((hpar i (by omega)).2 (by rw [Nat.even_iff]; omega))
      have hj : i - 1 + 1 = i := by omega
      have hb2 := hωe (i - 1) (by omega)
      have hm' : 3 ≤ ω (e (i - 1)) + ω (e i) ∧ ω (e (i - 1)) + ω (e i) ≤ 5 := by
        rw [he, he, hj]; exact hm
      rw [hj]
      split_ifs with hc <;> omega
  obtain ⟨Δ, hΔ⟩ : ∃ Δ : Sym2 V → ℤ, ∀ x, Δ x =
      ∑ i ∈ range (k - 1), if x = e i then σs i else 0 := ⟨_, fun _ => rfl⟩
  have hΔe : ∀ i, i + 1 < k → Δ (e i) = σs i := by
    intro i hi
    rw [hΔ, Finset.sum_eq_single i]
    · simp
    · intro j hj hji
      have hj' := mem_range.1 hj
      rw [if_neg]
      intro h
      exact hji (hinjE i j hi (by omega) h).symm
    · intro h; exact absurd (mem_range.2 (by omega)) h
  have hΔ0 : ∀ x, (∀ i, i + 1 < k → x ≠ e i) → Δ x = 0 := by
    intro x hx
    rw [hΔ]
    apply Finset.sum_eq_zero
    intro i hi
    rw [if_neg (hx i (by have := mem_range.1 hi; omega))]
  have hbd : ∀ x ∈ H.edgeSet, 1 ≤ (ω x : ℤ) + Δ x ∧ (ω x : ℤ) + Δ x ≤ 3 := by
    intro x hx
    by_cases h : ∃ i, i + 1 < k ∧ x = e i
    · obtain ⟨i, hi, rfl⟩ := h
      rw [hΔe i hi]; exact hF4 i hi
    · push Not at h
      rw [hΔ0 x h]
      have := hW x hx
      omega
  obtain ⟨ω', hω'⟩ : ∃ ω' : Sym2 V → ℕ, ∀ x, ω' x = (( ω x : ℤ) + Δ x).toNat := ⟨_, fun _ => rfl⟩
  have hD : ∀ v, (sdeg H ω' v : ℤ) = sdeg H ω v +
      ∑ i ∈ range (k - 1), ((if v = p i then σs i else 0) + (if v = p (i + 1) then σs i else 0)) := by
    intro v
    have h1 : (sdeg H ω' v : ℤ) = sdeg H ω v + ∑ u ∈ univ.filter (H.Adj v), Δ s(v, u) := by
      simp only [sdeg]
      push_cast
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro u hu
      have hadj := (Finset.mem_filter.1 hu).2
      have := hbd s(v, u) hadj
      rw [hω']; omega
    rw [h1]
    congr 1
    simp only [hΔ]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i + 1 < k := by have := mem_range.1 hi; omega
    have hai := hadjp i hi'
    have hne : p i ≠ p (i + 1) := fun h => by have := hI _ _ (by omega) (by omega) h; omega
    rw [he]
    by_cases hv1 : v = p i
    · rw [if_pos hv1, if_neg (by rw [hv1]; exact hne), add_zero]
      rw [Finset.sum_eq_single (p (i + 1))]
      · rw [hv1, if_pos rfl]
      · intro u _ hu
        rw [if_neg]
        intro h
        rw [hv1, Sym2.eq_iff] at h
        rcases h with ⟨_, h⟩ | ⟨h, _⟩
        · exact hu h
        · exact hne h
      · intro h
        exact absurd (Finset.mem_filter.2 ⟨mem_univ _, hv1 ▸ hai⟩) h
    · by_cases hv2 : v = p (i + 1)
      · rw [if_neg hv1, if_pos hv2, zero_add]
        rw [Finset.sum_eq_single (p i)]
        · rw [hv2, if_pos]; rw [Sym2.eq_swap]
        · intro u _ hu
          rw [if_neg]
          intro h
          rw [hv2, Sym2.eq_iff] at h
          rcases h with ⟨h, _⟩ | ⟨_, h⟩
          · exact hne h.symm
          · exact hu h
        · intro h
          exact absurd (Finset.mem_filter.2 ⟨mem_univ _, hv2 ▸ hai.symm⟩) h
      · rw [if_neg hv1, if_neg hv2, add_zero]
        apply Finset.sum_eq_zero
        intro u _
        rw [if_neg]
        intro h
        rw [Sym2.eq_iff] at h
        rcases h with ⟨h, _⟩ | ⟨h, _⟩
        · exact hv1 h
        · exact hv2 h
  have hDp : ∀ j, j < k → ∑ i ∈ range (k - 1),
      ((if p j = p i then σs i else 0) + (if p j = p (i + 1) then σs i else 0)) =
      (if j < k - 1 then σs j else 0) + (if 1 ≤ j then σs (j - 1) else 0) := by
    intro j hj
    have h1 : ∀ i ∈ range (k - 1), ((if p j = p i then σs i else 0) +
        (if p j = p (i + 1) then σs i else 0)) =
        (if j = i then σs i else 0) + (if j = i + 1 then σs i else 0) := by
      intro i hi
      have hi' := mem_range.1 hi
      have c1 : p j = p i ↔ j = i := ⟨hI _ _ hj (by omega), fun h => by rw [h]⟩
      have c2 : p j = p (i + 1) ↔ j = i + 1 := ⟨hI _ _ hj (by omega), fun h => by rw [h]⟩
      simp only [c1, c2]
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib]
    have s1 : ∑ i ∈ range (k - 1), (if j = i then σs i else 0) = if j < k - 1 then σs j else 0 := by
      rw [Finset.sum_ite_eq]; simp only [mem_range]
    rw [s1]
    congr 1
    by_cases hj0 : j = 0
    · subst hj0; simp
    · obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
      simp only [Nat.add_right_cancel_iff, Finset.sum_ite_eq, mem_range]
      simp only [Nat.add_sub_cancel]
      by_cases hm : m < k - 1
      · simp [hm]
      · simp [hm]; omega
  have hDoff : ∀ v, (∀ i, i < k → p i ≠ v) → ∑ i ∈ range (k - 1),
      ((if v = p i then σs i else 0) + (if v = p (i + 1) then σs i else 0)) = 0 := by
    intro v hv
    apply Finset.sum_eq_zero
    intro i hi
    have hi' := mem_range.1 hi
    rw [if_neg (fun h => hv i (by omega) h.symm), if_neg (fun h => hv (i + 1) (by omega) h.symm)]
    simp
  refine ⟨ω', fun x hx => ?_, fun v hv => ?_, fun v hvB => ?_, fun v hvR => ?_⟩
  · have := hbd x hx
    rw [hω']; omega
  · have := hD v
    rw [hDoff v hv] at this
    exact_mod_cast (by simpa using this)
  · rw [hD v]
    by_cases hv : ∃ j, j < k ∧ p j = v
    · obtain ⟨j, hjk, rfl⟩ := hv
      rw [hDp j hjk]
      have hev := (hpar j hjk).1 hvB
      rw [Nat.even_iff] at hev
      have c0 : p j = p 0 ↔ j = 0 := ⟨hI _ _ hjk (by omega), fun h => by rw [h]⟩
      have c1 : p j = p (k - 1) ↔ j = k - 1 := ⟨hI _ _ hjk (by omega), fun h => by rw [h]⟩
      simp only [c0, c1]
      by_cases hj0 : j = 0
      · subst hj0
        have : ¬ (0 = k - 1) := by omega
        simp [this, hσs0]; omega
      · by_cases hjl : j = k - 1
        · subst hjl
          have h2 : k - 1 - 1 = k - 2 := by omega
          have : ¬ (k - 1 = 0) := by omega
          simp [this, h2, hσsk]
        · have hjl' : j + 2 < k := by omega
          have e1 := hσsn j (by omega) hjl' hev
          have e2 := hσsm (j - 1) (by omega) (by omega) (by omega)
          have e3 : j - 1 - 1 + 0 = j - 2 := by omega
          have hlt : j < k - 1 := by omega
          have h1j : 1 ≤ j := by omega
          simp [hj0, hjl, hlt, h1j, e1, e2]
    · push Not at hv
      rw [hDoff v hv]
      have a := hv 0 (by omega)
      have b := hv (k - 1) (by omega)
      rw [if_neg (Ne.symm a), if_neg (Ne.symm b)]
      simp
  · by_cases hv : ∃ j, j < k ∧ p j = v
    · obtain ⟨j, hjk, rfl⟩ := hv
      have hodd : ¬ Even j := fun h => Finset.disjoint_left.1 hd hvR ((hpar j hjk).2 h)
      rw [Nat.even_iff] at hodd
      have hD' := hD (p j)
      rw [hDp j hjk, if_pos (by omega), if_pos (by omega)] at hD'
      have a1 := hσs1 j
      have a2 := hσs1 (j - 1)
      omega
    · push Not at hv
      have := hD v
      rw [hDoff v hv] at this
      have h3 : sdeg H ω' v = sdeg H ω v := by exact_mod_cast (by simpa using this)
      rw [h3]

theorem B2_final (G : SimpleGraph V) (v0 : V) (R B : Finset V) (hg : Good G R B)
    (hv0 : v0 ∉ R ∪ B)
    (hdom : ∀ u v, G.Adj u v → (u ∈ R ∪ B ∨ u = v0) ∧ (v ∈ R ∪ B ∨ v = v0))
    (ω1 : Sym2 V → ℕ) (f s1 : V → ℕ) (hW1 : Wt3 (bip G B B) ω1) (hodd : ∀ v, Odd (f v))
    (hprop : ∀ u v, (bip G B B).Adj u v → f u ≠ f v)
    (hs1 : ∀ v, s1 v = sdeg (bip G B B) ω1 v)
    (ω2 : Sym2 V → ℕ) (g : V → ℕ) (hW2 : Wt3 (bip G R B) ω2)
    (hB : ∀ v ∈ B, f v = s1 v + sdeg (bip G R B) ω2 v + (if G.Adj v0 v then g v else 0))
    (hR : ∀ v ∈ R, Even (sdeg (bip G R B) ω2 v + (if G.Adj v0 v then g v else 0)))
    (hgb : ∀ b, G.Adj v0 b → 1 ≤ g b ∧ g b ≤ 3)
    (hev : Even (∑ u ∈ univ.filter (G.Adj v0), g u))
    (hconf : ∀ v ∈ R, G.Adj v0 v →
      ∑ u ∈ univ.filter (G.Adj v0), g u ≠ sdeg (bip G R B) ω2 v + g v) :
    ∃ ω, Wt3 G ω ∧ Proper G ω := by
  have hdisj := hg.disj
  have hv0R : v0 ∉ R := fun h => hv0 (mem_union_left _ h)
  have hv0B : v0 ∉ B := fun h => hv0 (mem_union_right _ h)
  obtain ⟨ω, hωa, hωb, hωB, hωR, hω0⟩ := B2_assemble G v0 R B hdisj hg.indep hv0 hdom ω1 ω2 g
  have sB : ∀ v ∈ B, sdeg G ω v = f v := by
    intro v hv
    rw [hωB v hv, ← hs1 v, hB v hv]
  have hbmem : ∀ b, G.Adj v0 b → b ∈ R ∨ b ∈ B := by
    intro b hb
    have := ((hdom v0 b hb).2).resolve_right (fun h => G.loopless.irrefl v0 (h ▸ hb))
    exact mem_union.1 this
  have hwt : Wt3 G ω := by
    intro e he
    induction e using Sym2.ind with
    | h a b =>
      have hadj : G.Adj a b := he
      by_cases ha : a = v0
      · rw [ha, hωb]; exact hgb b (ha ▸ hadj)
      · by_cases hb : b = v0
        · rw [hb, Sym2.eq_swap, hωb]; exact hgb a (hb ▸ hadj.symm)
        · rw [hωa a b ha hb]
          have haRB := mem_union.1 (((hdom a b hadj).1).resolve_right ha)
          have hbRB := mem_union.1 (((hdom a b hadj).2).resolve_right hb)
          by_cases hab : a ∈ B ∧ b ∈ B
          · rw [if_pos hab]
            exact hW1 s(a, b) (show (bip G B B).Adj a b from ⟨hadj, Or.inl ⟨hab.1, hab.2⟩⟩)
          · rw [if_neg hab]
            apply hW2 s(a, b)
            show (bip G R B).Adj a b
            refine ⟨hadj, ?_⟩
            rcases haRB with haR | haB <;> rcases hbRB with hbR | hbB
            · exact absurd hadj (hg.indep a haR b hbR)
            · exact Or.inl ⟨haR, hbB⟩
            · exact Or.inr ⟨haB, hbR⟩
            · exact absurd ⟨haB, hbB⟩ hab
  have hRev : ∀ v ∈ R, Even (sdeg G ω v) := fun v hv => by rw [hωR v hv]; exact hR v hv
  have hp0 : ∀ v, G.Adj v0 v → sdeg G ω v0 ≠ sdeg G ω v := by
    intro v hv
    rcases hbmem v hv with hvR | hvB
    · rw [hω0, hωR v hvR, if_pos hv]
      exact hconf v hvR hv
    · rw [sB v hvB, hω0]
      have := Nat.odd_iff.1 (hodd v)
      have := Nat.even_iff.1 hev
      omega
  refine ⟨ω, hwt, ?_⟩
  intro u v hadj
  by_cases hu : u = v0
  · rw [hu]; exact hp0 v (hu ▸ hadj)
  by_cases hv : v = v0
  · rw [hv]; exact (hp0 u (hv ▸ hadj.symm)).symm
  have huRB := mem_union.1 (((hdom u v hadj).1).resolve_right hu)
  have hvRB := mem_union.1 (((hdom u v hadj).2).resolve_right hv)
  rcases huRB with huR | huB <;> rcases hvRB with hvR | hvB
  · exact absurd hadj (hg.indep u huR v hvR)
  · intro heq
    have h1 := Nat.even_iff.1 (hRev u huR)
    rw [heq, sB v hvB] at h1
    have := Nat.odd_iff.1 (hodd v)
    omega
  · intro heq
    have h1 := Nat.even_iff.1 (hRev v hvR)
    rw [← heq, sB u huB] at h1
    have := Nat.odd_iff.1 (hodd u)
    omega
  · rw [sB u huB, sB v hvB]
    exact hprop u v ⟨hadj, Or.inl ⟨huB, hvB⟩⟩

theorem lemma8 (G : SimpleGraph V) (v0 : V) (R B : Finset V) (hg : Good G R B)
    (hv0 : v0 ∉ R ∪ B)
    (hdom : ∀ u v, G.Adj u v → (u ∈ R ∪ B ∨ u = v0) ∧ (v ∈ R ∪ B ∨ v = v0))
    (h2 : 2 ≤ (R.filter (G.Adj v0)).card)
    (hpar : Even (R.filter (G.Adj v0)).card ∨ 1 ≤ (B.filter (G.Adj v0)).card) :
    ∃ ω, Wt3 G ω ∧ Proper G ω := by
  have hdisj := hg.disj
  have hv0R : v0 ∉ R := fun h => hv0 (mem_union_left _ h)
  have hv0B : v0 ∉ B := fun h => hv0 (mem_union_right _ h)
  have hBR : ∀ x ∈ B, x ∉ R := fun x hx h => Finset.disjoint_left.1 hdisj h hx
  have hRB : ∀ x ∈ R, x ∉ B := fun x hx h => Finset.disjoint_left.1 hdisj hx h
  set R' : Finset V := R.filter (G.Adj v0) with hR'
  have hR'R : R' ⊆ R := Finset.filter_subset _ _
  have hmemR' : ∀ x, x ∈ R' ↔ x ∈ R ∧ G.Adj v0 x := fun x => Finset.mem_filter
  obtain ⟨u0, hu0⟩ : ∃ u0, Odd R'.card → (u0 ∈ B ∧ G.Adj v0 u0) := by
    by_cases ho : Odd R'.card
    · have h1 : 1 ≤ (B.filter (G.Adj v0)).card := by
        rcases hpar with he | h1
        · exact absurd he (Nat.not_even_iff_odd.2 ho)
        · exact h1
      obtain ⟨u, hu⟩ := Finset.card_pos.1 h1
      exact ⟨u, fun _ => by simpa using hu⟩
    · exact ⟨v0, fun h => absurd h ho⟩
  obtain ⟨dR, hdR⟩ : ∃ dR : V → ℕ, ∀ v, dR v = (R.filter (G.Adj v)).card := ⟨_, fun _ => rfl⟩
  have hdRpos : ∀ v ∈ B, 1 ≤ dR v := fun v hv => by rw [hdR]; exact B2_degR_pos G R B hg v hv
  obtain ⟨h, hhdef⟩ : ∃ h : V → ℕ, ∀ v, h v =
      if v ∈ B then 2 * dR v + (if G.Adj v0 v then 2 else 0) else 2 := ⟨_, fun _ => rfl⟩
  have hhB : ∀ v ∈ B, h v = 2 * dR v + (if G.Adj v0 v then 2 else 0) :=
    fun v hv => by rw [hhdef, if_pos hv]
  have hhe : ∀ v, Even (h v) := by
    intro v
    by_cases hv : v ∈ B
    · rw [hhB v hv]
      split_ifs
      · exact ⟨dR v + 1, by ring⟩
      · exact ⟨dR v, by ring⟩
    · rw [hhdef, if_neg hv]; exact ⟨1, rfl⟩
  have hh2 : ∀ v, 2 ≤ h v := by
    intro v
    by_cases hv : v ∈ B
    · have := hdRpos v hv
      rw [hhB v hv]; split_ifs <;> omega
    · rw [hhdef, if_neg hv]
  obtain ⟨ω1, f, hW1, hodd, hprop, habs⟩ := lemma3 (bip G B B) h hhe hh2
  obtain ⟨s1, hs1⟩ : ∃ s1 : V → ℕ, ∀ v, s1 v = sdeg (bip G B B) ω1 v := ⟨_, fun _ => rfl⟩
  have hfs : ∀ v ∈ B, f v = s1 v + h v + 1 ∨ f v + 1 = s1 v + h v := by
    intro v _
    have := habs v
    rw [← hs1 v] at this
    rcases (abs_eq (by norm_num : (0:ℤ) ≤ 1)).1 this with h' | h' <;> omega
  obtain ⟨α, hαdef⟩ : ∃ α : V → ℕ, ∀ v, α v = if v ∈ B then (if G.Adj v0 v then
      (if Odd R'.card ∧ v = u0 then 2 * dR v else f v - s1 v - 2) else f v - s1 v) else 0 :=
    ⟨_, fun _ => rfl⟩
  have hα1 : ∀ v ∈ B, ¬ (Odd R'.card ∧ v = u0) →
      α v % 2 = 1 ∧ (α v + 1 = 2 * dR v ∨ α v = 2 * dR v + 1) := by
    intro v hv hfl
    have := hfs v hv
    have := hhB v hv
    have := hdRpos v hv
    rw [hαdef v, if_pos hv]
    by_cases ha : G.Adj v0 v
    · rw [if_pos ha, if_neg hfl]; rw [if_pos ha] at *; omega
    · rw [if_neg ha]; rw [if_neg ha] at *; omega
  have hα2 : Odd R'.card → α u0 = 2 * dR u0 := by
    intro ho
    obtain ⟨hB0, ha0⟩ := hu0 ho
    rw [hαdef u0, if_pos hB0, if_pos ha0, if_pos ⟨ho, rfl⟩]
  have hαall : ∀ v ∈ B, α v + 1 = 2 * dR v ∨ α v = 2 * dR v ∨ α v = 2 * dR v + 1 := by
    intro v hv
    by_cases hfl : Odd R'.card ∧ v = u0
    · right; left; rw [hfl.2]; exact hα2 hfl.1
    · have := hα1 v hv hfl; omega
  have hsum : Even (R'.card + ∑ v ∈ B, α v) := by
    have hm := B2_sum_mod B α
    have hBev := hg.even
    rw [Nat.even_iff] at hBev
    rw [Nat.even_iff]
    by_cases hodd : Odd R'.card
    · obtain ⟨hB0, _⟩ := hu0 hodd
      have hfil : B.filter (fun v => α v % 2 = 1) = B.erase u0 := by
        ext v
        simp only [Finset.mem_filter, Finset.mem_erase]
        constructor
        · rintro ⟨hv, h1⟩
          refine ⟨?_, hv⟩
          rintro rfl
          have := hα2 hodd
          have := hdRpos v hv
          omega
        · rintro ⟨hne, hv⟩
          exact ⟨hv, (hα1 v hv (fun h => hne h.2)).1⟩
      rw [hfil, Finset.card_erase_of_mem hB0] at hm
      have hpos : 0 < B.card := Finset.card_pos.2 ⟨u0, hB0⟩
      have := Nat.odd_iff.1 hodd
      omega
    · have hfil : B.filter (fun v => α v % 2 = 1) = B := by
        apply Finset.filter_true_of_mem
        intro v hv
        exact (hα1 v hv (fun h => hodd h.1)).1
      rw [hfil] at hm
      have : R'.card % 2 = 0 := by
        have := Nat.not_odd_iff_even.1 hodd
        exact Nat.even_iff.1 this
      omega
  obtain ⟨ω2, hW2, hRp, hBd⟩ := lemma5 (bip G R B) R B hdisj (fun u v h => h.2) hg.conn α
    (by
      intro v hv
      rw [B2_bip_degree G R B hdisj v hv, ← hdR]
      exact hαall v hv) R' hR'R hsum
  obtain ⟨g0, hg0def⟩ : ∃ g0 : V → ℕ, ∀ u, g0 u = if u ∈ R' then 1 else f u - s1 u - α u :=
    ⟨_, fun _ => rfl⟩
  have hg0R : ∀ u ∈ R', g0 u = 1 := fun u hu => by rw [hg0def, if_pos hu]
  have hg0B : ∀ u ∈ B, G.Adj v0 u →
      f u = s1 u + α u + g0 u ∧ (¬ (Odd R'.card ∧ u = u0) → g0 u = 2) ∧
      ((Odd R'.card ∧ u = u0) → g0 u = 1 ∨ g0 u = 3) := by
    intro u hu ha
    have hnR' : u ∉ R' := fun h => hRB u (hR'R h) hu
    have e := hfs u hu
    have e2 := hhB u hu
    have e3 := hdRpos u hu
    rw [hg0def u, if_neg hnR']
    by_cases hfl : Odd R'.card ∧ u = u0
    · have := hα2 hfl.1
      rw [← hfl.2] at this
      rw [if_pos ha] at e2
      refine ⟨by omega, fun h => absurd hfl h, fun _ => by omega⟩
    · have e4 : α u = f u - s1 u - 2 := by
        rw [hαdef u, if_pos hu, if_pos ha, if_neg hfl]
      rw [if_pos ha] at e2
      refine ⟨by omega, fun _ => by omega, fun h => absurd h hfl⟩
  have hg0nB : ∀ u ∈ B, ¬ G.Adj v0 u → f u = s1 u + α u := by
    intro u hu ha
    have e := hfs u hu
    have e2 := hhB u hu
    have e3 := hdRpos u hu
    have e4 : α u = f u - s1 u := by rw [hαdef u, if_pos hu, if_neg ha]
    rw [if_neg ha] at e2
    omega
  obtain ⟨tR, htR⟩ : ∃ tR : V → ℕ, ∀ v, tR v =
      sdeg (bip G R B) ω2 v + (if G.Adj v0 v then g0 v else 0) := ⟨_, fun _ => rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℕ, c = ∑ u ∈ univ.filter (G.Adj v0), g0 u := ⟨_, rfl⟩
  obtain ⟨S, hSR', hS⟩ := B2_conflict R' h2 tR c
  have hSnB : ∀ v ∈ B, v ∉ S := fun v hv hS' => hRB v (hR'R (hSR' hS')) hv
  obtain ⟨ω, hωa, hωb, hωB, hωR, hω0⟩ := B2_assemble G v0 R B hdisj hg.indep hv0 hdom ω1 ω2
    (fun u => g0 u + if u ∈ S then 2 else 0)
  have sB : ∀ v ∈ B, sdeg G ω v = f v := by
    intro v hv
    rw [hωB v hv, ← hs1 v, hBd v hv]
    by_cases ha : G.Adj v0 v
    · have := (hg0B v hv ha).1
      simp only [if_pos ha, if_neg (hSnB v hv)]; omega
    · have := hg0nB v hv ha
      simp only [if_neg ha]; omega
  have s0 : sdeg G ω v0 = c + 2 * S.card := by
    rw [hω0, hc]
    simp only [Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_ite_mem]
    have hsub : S ⊆ univ.filter (G.Adj v0) := fun u hu =>
      Finset.mem_filter.2 ⟨Finset.mem_univ _, ((hmemR' u).1 (hSR' hu)).2⟩
    rw [Finset.inter_eq_right.2 hsub, Finset.sum_const, smul_eq_mul, mul_comm]
  have sR : ∀ v ∈ R', sdeg G ω v = tR v + 2 * (if v ∈ S then 1 else 0) := by
    intro v hv
    have ha := ((hmemR' v).1 hv).2
    rw [hωR v ((hmemR' v).1 hv).1, htR]
    simp only [if_pos ha]
    split_ifs <;> omega
  have hRev : ∀ v ∈ R, Even (sdeg G ω v) := by
    intro v hv
    rw [hωR v hv, Nat.even_iff]
    by_cases ha : G.Adj v0 v
    · have hv' : v ∈ R' := (hmemR' v).2 ⟨hv, ha⟩
      have h1 := (hRp v hv).not.2 (not_not.2 hv')
      have h1' : sdeg (bip G R B) ω2 v % 2 = 1 := Nat.odd_iff.1 (Nat.not_even_iff_odd.1 h1)
      have := hg0R v hv'
      simp only [if_pos ha]
      split_ifs <;> omega
    · have hv' : v ∉ R' := fun h => ha ((hmemR' v).1 h).2
      have h1 := Nat.even_iff.1 ((hRp v hv).2 hv')
      simp only [if_neg ha]; omega
  have hbmem : ∀ b, G.Adj v0 b → b ∈ R ∨ b ∈ B := by
    intro b hb
    have := ((hdom v0 b hb).2).resolve_right (fun h => G.loopless.irrefl v0 (h ▸ hb))
    exact mem_union.1 this
  have hcEven : c % 2 = 0 := by
    have hm := B2_sum_mod (univ.filter (G.Adj v0)) g0
    rw [← hc] at hm
    by_cases hodd : Odd R'.card
    · obtain ⟨hB0, ha0⟩ := hu0 hodd
      have hfil : (univ.filter (G.Adj v0)).filter (fun v => g0 v % 2 = 1) = insert u0 R' := by
        ext u
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        constructor
        · rintro ⟨hu, h1⟩
          rcases hbmem u hu with huR | huB
          · exact Or.inr ((hmemR' u).2 ⟨huR, hu⟩)
          · by_cases hfl : Odd R'.card ∧ u = u0
            · exact Or.inl hfl.2
            · have := (hg0B u huB hu).2.1 hfl
              omega
        · rintro (rfl | hu)
          · refine ⟨ha0, ?_⟩
            have := (hg0B u hB0 ha0).2.2 ⟨hodd, rfl⟩
            omega
          · refine ⟨((hmemR' u).1 hu).2, ?_⟩
            rw [hg0R u hu]
      rw [hfil, Finset.card_insert_of_notMem (fun h => hRB u0 (hR'R h) hB0)] at hm
      have := Nat.odd_iff.1 hodd
      omega
    · have hfil : (univ.filter (G.Adj v0)).filter (fun v => g0 v % 2 = 1) = R' := by
        ext u
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨hu, h1⟩
          rcases hbmem u hu with huR | huB
          · exact (hmemR' u).2 ⟨huR, hu⟩
          · have := (hg0B u huB hu).2.1 (fun h => hodd h.1)
            omega
        · intro hu
          refine ⟨((hmemR' u).1 hu).2, ?_⟩
          rw [hg0R u hu]
      rw [hfil] at hm
      have := Nat.even_iff.1 (Nat.not_odd_iff_even.1 hodd)
      omega
  have hgb : ∀ b, G.Adj v0 b → 1 ≤ g0 b + (if b ∈ S then 2 else 0) ∧
      g0 b + (if b ∈ S then 2 else 0) ≤ 3 := by
    intro b hb
    rcases hbmem b hb with hbR | hbB
    · have := hg0R b ((hmemR' b).2 ⟨hbR, hb⟩)
      split_ifs <;> omega
    · have e1 := hg0B b hbB hb
      rw [if_neg (hSnB b hbB)]
      by_cases hfl : Odd R'.card ∧ b = u0
      · have := e1.2.2 hfl; omega
      · have := e1.2.1 hfl; omega
  have hwt : Wt3 G ω := by
    intro e he
    induction e using Sym2.ind with
    | h a b =>
      have hadj : G.Adj a b := he
      by_cases ha : a = v0
      · rw [ha, hωb]; exact hgb b (ha ▸ hadj)
      · by_cases hb : b = v0
        · rw [hb, Sym2.eq_swap, hωb]; exact hgb a (hb ▸ hadj.symm)
        · rw [hωa a b ha hb]
          have haRB := mem_union.1 (((hdom a b hadj).1).resolve_right ha)
          have hbRB := mem_union.1 (((hdom a b hadj).2).resolve_right hb)
          by_cases hab : a ∈ B ∧ b ∈ B
          · rw [if_pos hab]
            exact hW1 s(a, b) (show (bip G B B).Adj a b from ⟨hadj, Or.inl ⟨hab.1, hab.2⟩⟩)
          · rw [if_neg hab]
            apply hW2 s(a, b)
            show (bip G R B).Adj a b
            refine ⟨hadj, ?_⟩
            rcases haRB with haR | haB <;> rcases hbRB with hbR | hbB
            · exact absurd hadj (hg.indep a haR b hbR)
            · exact Or.inl ⟨haR, hbB⟩
            · exact Or.inr ⟨haB, hbR⟩
            · exact absurd ⟨haB, hbB⟩ hab
  have hp0 : ∀ v, G.Adj v0 v → sdeg G ω v0 ≠ sdeg G ω v := by
    intro v hv
    rcases hbmem v hv with hvR | hvB
    · have hvR' : v ∈ R' := (hmemR' v).2 ⟨hvR, hv⟩
      rw [s0, sR v hvR']
      exact hS v hvR'
    · rw [sB v hvB, s0]
      have := Nat.odd_iff.1 (hodd v)
      omega
  refine ⟨ω, hwt, ?_⟩
  intro u v hadj
  by_cases hu : u = v0
  · rw [hu]; exact hp0 v (hu ▸ hadj)
  by_cases hv : v = v0
  · rw [hv]; exact (hp0 u (hv ▸ hadj.symm)).symm
  have huRB := mem_union.1 (((hdom u v hadj).1).resolve_right hu)
  have hvRB := mem_union.1 (((hdom u v hadj).2).resolve_right hv)
  rcases huRB with huR | huB <;> rcases hvRB with hvR | hvB
  · exact absurd hadj (hg.indep u huR v hvR)
  · intro heq
    have h1 := Nat.even_iff.1 (hRev u huR)
    rw [heq, sB v hvB] at h1
    have := Nat.odd_iff.1 (hodd v)
    omega
  · intro heq
    have h1 := Nat.even_iff.1 (hRev v hvR)
    rw [← heq, sB u huB] at h1
    have := Nat.odd_iff.1 (hodd u)
    omega
  · rw [sB u huB, sB v hvB]
    exact hprop u v ⟨hadj, Or.inl ⟨huB, hvB⟩⟩

theorem lemma9 (G : SimpleGraph V) (v0 u0 : V) (R B : Finset V) (hg : Good G R B)
    (hv0 : v0 ∉ R ∪ B)
    (hdom : ∀ u v, G.Adj u v → (u ∈ R ∪ B ∨ u = v0) ∧ (v ∈ R ∪ B ∨ v = v0))
    (hN : R.filter (G.Adj v0) = {u0})
    (k : ℕ) (hk : 3 ≤ k) (p : ℕ → V) (hinj : Set.InjOn p (Set.Iio k))
    (hadj : ∀ i, i + 1 < k → (bip G R B).Adj (p i) (p (i + 1)))
    (h0 : p 0 ∈ B ∧ G.Adj v0 (p 0)) (hk' : p (k - 1) ∈ B ∧ G.Adj v0 (p (k - 1)))
    (hu0 : ∀ i, i < k → p i ≠ u0) :
    ∃ ω, Wt3 G ω ∧ Proper G ω := by
  have hdisj := hg.disj
  have hv0R : v0 ∉ R := fun h => hv0 (mem_union_left _ h)
  have hv0B : v0 ∉ B := fun h => hv0 (mem_union_right _ h)
  have hRB : ∀ x ∈ R, x ∉ B := fun x hx h => Finset.disjoint_left.1 hdisj hx h
  have hu0mem : u0 ∈ R ∧ G.Adj v0 u0 := by
    have : u0 ∈ R.filter (G.Adj v0) := by rw [hN]; simp
    exact Finset.mem_filter.1 this
  have hRN : ∀ x ∈ R, G.Adj v0 x → x = u0 := fun x hx ha => by
    have : x ∈ R.filter (G.Adj v0) := Finset.mem_filter.2 ⟨hx, ha⟩
    rw [hN] at this; simpa using this
  have hne : p 0 ≠ p (k - 1) := fun h => by
    have := hinj (Set.mem_Iio.2 (by omega)) (Set.mem_Iio.2 (by omega)) h
    omega
  obtain ⟨dR, hdR⟩ : ∃ dR : V → ℕ, ∀ v, dR v = (R.filter (G.Adj v)).card := ⟨_, fun _ => rfl⟩
  have hdRpos : ∀ v ∈ B, 1 ≤ dR v := fun v hv => by rw [hdR]; exact B2_degR_pos G R B hg v hv
  obtain ⟨h, hhdef⟩ : ∃ h : V → ℕ, ∀ v, h v =
      if v ∈ B then 2 * dR v + (if G.Adj v0 v then 2 else 0) else 2 := ⟨_, fun _ => rfl⟩
  have hhB : ∀ v ∈ B, h v = 2 * dR v + (if G.Adj v0 v then 2 else 0) :=
    fun v hv => by rw [hhdef, if_pos hv]
  have hhe : ∀ v, Even (h v) := by
    intro v
    by_cases hv : v ∈ B
    · rw [hhB v hv]
      split_ifs
      · exact ⟨dR v + 1, by ring⟩
      · exact ⟨dR v, by ring⟩
    · rw [hhdef, if_neg hv]; exact ⟨1, rfl⟩
  have hh2 : ∀ v, 2 ≤ h v := by
    intro v
    by_cases hv : v ∈ B
    · have := hdRpos v hv
      rw [hhB v hv]; split_ifs <;> omega
    · rw [hhdef, if_neg hv]
  obtain ⟨ω1, f, hW1, hodd, hprop, habs⟩ := lemma3 (bip G B B) h hhe hh2
  obtain ⟨s1, hs1⟩ : ∃ s1 : V → ℕ, ∀ v, s1 v = sdeg (bip G B B) ω1 v := ⟨_, fun _ => rfl⟩
  have hfs : ∀ v ∈ B, f v = s1 v + h v + 1 ∨ f v + 1 = s1 v + h v := by
    intro v _
    have := habs v
    rw [← hs1 v] at this
    rcases (abs_eq (by norm_num : (0:ℤ) ≤ 1)).1 this with h' | h' <;> omega
  obtain ⟨β, hβ⟩ : ∃ β : V → ℕ, ∀ v, β v = f v - s1 v - 2 * dR v := ⟨_, fun _ => rfl⟩
  have hfβ : ∀ v ∈ B, G.Adj v0 v → f v = s1 v + 2 * dR v + β v ∧ (β v = 1 ∨ β v = 3) := by
    intro v hv ha
    have e := hfs v hv
    have e2 := hhB v hv
    rw [if_pos ha] at e2
    rw [hβ v]
    omega
  obtain ⟨Hi, hHi⟩ : ∃ Hi : V → Prop, ∀ v, Hi v ↔
      (β (p 0) ≠ β (p (k - 1)) ∧ β v = 3 ∧ (v = p 0 ∨ v = p (k - 1))) :=
    ⟨fun v => (β (p 0) ≠ β (p (k - 1)) ∧ β v = 3 ∧ (v = p 0 ∨ v = p (k - 1))), fun _ => Iff.rfl⟩
  obtain ⟨g2, hg2⟩ : ∃ g2 : V → ℕ, ∀ u, g2 u = if u = u0 then
      (if β (p 0) = β (p (k - 1)) then 2 else 3) else if Hi u then 3 else 2 := ⟨_, fun _ => rfl⟩
  obtain ⟨R', hR'⟩ : ∃ R' : Finset V, R' = if β (p 0) = β (p (k - 1)) then ∅ else {u0} :=
    ⟨_, rfl⟩
  have hR'R : R' ⊆ R := by
    rw [hR']; split_ifs
    · exact empty_subset _
    · simpa using hu0mem.1
  obtain ⟨α, hαdef⟩ : ∃ α : V → ℕ, ∀ v, α v = if v ∈ B then (if G.Adj v0 v then
      f v - s1 v - g2 v else f v - s1 v) else 0 := ⟨_, fun _ => rfl⟩
  have hg2B : ∀ v ∈ B, g2 v = if Hi v then 3 else 2 := by
    intro v hv
    rw [hg2, if_neg (fun h => hRB u0 hu0mem.1 (by rw [← h]; exact hv))]
  have hHiadj : ∀ v, Hi v → G.Adj v0 v := by
    intro v hv
    rcases ((hHi v).1 hv).2.2 with rfl | rfl
    · exact h0.2
    · exact hk'.2
  have hHiB : ∀ v, Hi v → v ∈ B := by
    intro v hv
    rcases ((hHi v).1 hv).2.2 with rfl | rfl
    · exact h0.1
    · exact hk'.1
  have hαHi : ∀ v ∈ B, Hi v → α v = 2 * dR v := by
    intro v hv hh
    have ha := hHiadj v hh
    obtain ⟨e1, e2⟩ := hfβ v hv ha
    have := ((hHi v).1 hh).2.1
    rw [hαdef v, if_pos hv, if_pos ha, hg2B v hv, if_pos hh]
    omega
  have hαnHi : ∀ v ∈ B, ¬ Hi v → α v % 2 = 1 ∧
      (α v + 1 = 2 * dR v ∨ α v = 2 * dR v + 1) := by
    intro v hv hh
    have hd := hdRpos v hv
    rw [hαdef v, if_pos hv, hg2B v hv, if_neg hh]
    by_cases ha : G.Adj v0 v
    · obtain ⟨e1, e2⟩ := hfβ v hv ha
      rw [if_pos ha]; omega
    · have e := hfs v hv
      have e2 := hhB v hv
      rw [if_neg ha] at e2 ⊢
      omega
  have hαall : ∀ v ∈ B, α v + 1 = 2 * dR v ∨ α v = 2 * dR v ∨ α v = 2 * dR v + 1 := by
    intro v hv
    by_cases hh : Hi v
    · right; left; exact hαHi v hv hh
    · have := hαnHi v hv hh; omega
  have hxhex : ¬ (β (p 0) = β (p (k - 1))) → ∃ xh ∈ B, (∀ v, Hi v ↔ v = xh) := by
    intro heq
    have b0 := hfβ (p 0) h0.1 h0.2
    have bk := hfβ (p (k - 1)) hk'.1 hk'.2
    by_cases h3 : β (p 0) = 3
    · refine ⟨p 0, h0.1, fun v => ?_⟩
      rw [hHi]
      constructor
      · rintro ⟨_, _, rfl | rfl⟩
        · rfl
        · omega
      · rintro rfl; exact ⟨heq, h3, Or.inl rfl⟩
    · have h3' : β (p (k - 1)) = 3 := by omega
      refine ⟨p (k - 1), hk'.1, fun v => ?_⟩
      rw [hHi]
      constructor
      · rintro ⟨_, _, rfl | rfl⟩
        · omega
        · rfl
      · rintro rfl; exact ⟨heq, h3', Or.inr rfl⟩
  have hsum : Even (R'.card + ∑ v ∈ B, α v) := by
    have hm := B2_sum_mod B α
    have hBev := hg.even
    rw [Nat.even_iff] at hBev
    rw [Nat.even_iff]
    by_cases heq : β (p 0) = β (p (k - 1))
    · have hRc : R' = ∅ := by rw [hR', if_pos heq]
      have hfil : B.filter (fun v => α v % 2 = 1) = B := by
        apply Finset.filter_true_of_mem
        intro v hv
        have : ¬ Hi v := fun hh => ((hHi v).1 hh).1 heq
        exact (hαnHi v hv this).1
      rw [hfil] at hm; rw [hRc]; simp; omega
    · obtain ⟨xh, hxhB, hxh⟩ := hxhex heq
      have hRc : R' = {u0} := by rw [hR', if_neg heq]
      have hfil : B.filter (fun v => α v % 2 = 1) = B.erase xh := by
        ext v
        simp only [Finset.mem_filter, Finset.mem_erase]
        constructor
        · rintro ⟨hv, h1⟩
          refine ⟨?_, hv⟩
          intro hvx
          have hh : Hi v := (hxh v).2 hvx
          have := hαHi v hv hh
          omega
        · rintro ⟨hne', hv⟩
          exact ⟨hv, (hαnHi v hv (fun hh => hne' ((hxh v).1 hh))).1⟩
      rw [hfil, Finset.card_erase_of_mem hxhB] at hm
      have hpos : 0 < B.card := Finset.card_pos.2 ⟨xh, hxhB⟩
      rw [hRc]; simp; omega
  obtain ⟨ωp, hWp, hRp, hBp, i0a, i0b, hmidp, ika, ikb⟩ := lemma5_path (bip G R B) R B hdisj
    (fun u v h => h.2) hg.conn α
    (fun v hv => by rw [B2_bip_degree G R B hdisj v hv, ← hdR]; exact hαall v hv)
    R' hR'R hsum k hk p hinj hadj h0.1 hk'.1
  have hdegp : ∀ v ∈ B, (bip G R B).degree v = dR v := fun v hv => by
    rw [B2_bip_degree G R B hdisj v hv, hdR]
  have hBfin : ∀ v ∈ B, f v = s1 v + sdeg (bip G R B) ωp v + (if G.Adj v0 v then g2 v else 0) := by
    intro v hv
    rw [hBp v hv, hαdef v, if_pos hv]
    have hd := hdRpos v hv
    by_cases ha : G.Adj v0 v
    · obtain ⟨e1, e2⟩ := hfβ v hv ha
      rw [if_pos ha, if_pos ha, hg2B v hv]
      split_ifs <;> omega
    · have e := hfs v hv
      have e2 := hhB v hv
      rw [if_neg ha] at e2 ⊢
      rw [if_neg ha]
      omega
  have hRfact : ∀ v ∈ R, Even (sdeg (bip G R B) ωp v + (if G.Adj v0 v then g2 v else 0)) := by
    intro v hv
    have hr := hRp v hv
    rw [Nat.even_iff] at hr ⊢
    by_cases ha : G.Adj v0 v
    · have hv' := hRN v hv ha
      subst hv'
      rw [if_pos ha, hg2, if_pos rfl]
      by_cases heq : β (p 0) = β (p (k - 1))
      · have hRc : R' = ∅ := by rw [hR', if_pos heq]
        have := hr.2 (by rw [hRc]; simp)
        rw [if_pos heq]; omega
      · have hRc : R' = {v} := by rw [hR', if_neg heq]
        have h1 : ¬ (sdeg (bip G R B) ωp v % 2 = 0) := fun h => by
          have := hr.1 h; rw [hRc] at this; simp at this
        rw [if_neg heq]; omega
    · rw [if_neg ha]
      have : v ∉ R' := by
        rw [hR']; split_ifs
        · simp
        · simp only [Finset.mem_singleton]; intro h; exact ha (h ▸ hu0mem.2)
      have := hr.2 this
      omega
  have hgbd : ∀ b, G.Adj v0 b → 1 ≤ g2 b ∧ g2 b ≤ 3 := by
    intro b _; rw [hg2]; split_ifs <;> omega
  have hsumg2 : Even (∑ u ∈ univ.filter (G.Adj v0), g2 u) := by
    have hm := B2_sum_mod (univ.filter (G.Adj v0)) g2
    rw [Nat.even_iff]
    by_cases heq : β (p 0) = β (p (k - 1))
    · have hfil : (univ.filter (G.Adj v0)).filter (fun u => g2 u % 2 = 1) = ∅ := by
        apply Finset.filter_false_of_mem
        intro u _
        rw [hg2]
        have : ¬ Hi u := fun hh => ((hHi u).1 hh).1 heq
        simp [heq, this]
      rw [hfil] at hm; simpa using hm
    · obtain ⟨xh, hxhB, hxh⟩ := hxhex heq
      have hxha := hHiadj xh ((hxh xh).2 rfl)
      have hxu : xh ≠ u0 := fun h => hRB u0 hu0mem.1 (by rw [← h]; exact hxhB)
      have hfil : (univ.filter (G.Adj v0)).filter (fun u => g2 u % 2 = 1) = {u0, xh} := by
        ext u
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton]
        constructor
        · rintro ⟨hu, h1⟩
          rw [hg2] at h1
          by_cases hu0' : u = u0
          · exact Or.inl hu0'
          · rw [if_neg hu0'] at h1
            by_cases hh : Hi u
            · exact Or.inr ((hxh u).1 hh)
            · rw [if_neg hh] at h1; omega
        · rintro (h | h)
          · rw [h]; refine ⟨hu0mem.2, ?_⟩; rw [hg2, if_pos rfl, if_neg heq]
          · rw [h]; refine ⟨hxha, ?_⟩
            rw [hg2, if_neg hxu, if_pos ((hxh _).2 rfl)]
      rw [hfil, Finset.card_pair (Ne.symm hxu)] at hm
      omega
  by_cases hconf0 : ∑ u ∈ univ.filter (G.Adj v0), g2 u = sdeg (bip G R B) ωp u0 + g2 u0
  swap
  · exact B2_final G v0 R B hg hv0 hdom ω1 f s1 hW1 hodd hprop hs1 ωp g2 hWp hBfin hRfact hgbd
      hsumg2 (fun v hv ha => by rw [hRN v hv ha]; exact hconf0)
  obtain ⟨σ, hσdef⟩ : ∃ σ : ℤ, σ = if (β (p 0) = β (p (k - 1)) ∧ β (p 0) = 3) then -1 else 1 :=
    ⟨_, rfl⟩
  have hσ : σ = 1 ∨ σ = -1 := by rw [hσdef]; split_ifs <;> simp
  have hσHi : ∀ u, Hi u → σ = 1 := by
    intro u hu
    rw [hσdef, if_neg]
    rintro ⟨h1, _⟩
    exact ((hHi u).1 hu).1 h1
  have b0 := hfβ (p 0) h0.1 h0.2
  have bk := hfβ (p (k - 1)) hk'.1 hk'.2
  have hαe : ∀ v ∈ B, G.Adj v0 v → α v + g2 v = 2 * dR v + β v := by
    intro v hv ha
    obtain ⟨e1, e2⟩ := hfβ v hv ha
    have := hdRpos v hv
    have := hgbd v ha
    rw [hαdef v, if_pos hv, if_pos ha]
    omega
  have hendα : ∀ v, v ∈ B → G.Adj v0 v → (v = p 0 ∨ v = p (k - 1)) →
      ((β (p 0) = β (p (k - 1)) ∧ β (p 0) = 3 → α v = 2 * dR v + 1) ∧
       (¬ (β (p 0) = β (p (k - 1)) ∧ β (p 0) = 3) → α v ≠ 2 * dR v + 1)) := by
    intro v hv ha hend
    have e := hαe v hv ha
    have hg := hg2B v hv
    have hb := (hfβ v hv ha).2
    constructor
    · rintro ⟨hc1, hc2⟩
      have hHn : ¬ Hi v := fun h => ((hHi _).1 h).1 hc1
      rw [if_neg hHn] at hg
      have hbv : β v = 3 := by
        rcases hend with h | h
        · rw [h]; exact hc2
        · rw [h, ← hc1]; exact hc2
      omega
    · intro hc
      by_cases hH : Hi v
      · rw [if_pos hH] at hg
        have := ((hHi _).1 hH).2.1
        omega
      · rw [if_neg hH] at hg
        have hbv : β v = 1 := by
          by_contra hn
          have h3 : β v = 3 := by omega
          by_cases heq : β (p 0) = β (p (k - 1))
          · have hp3 : β (p 0) = 3 := by
              rcases hend with h | h
              · rw [h] at h3; exact h3
              · rw [h] at h3; omega
            exact hc ⟨heq, hp3⟩
          · exact hH ((hHi v).2 ⟨heq, h3, hend⟩)
        omega
  have hα0 := hendα (p 0) h0.1 h0.2 (Or.inl rfl)
  have hαk := hendα (p (k - 1)) hk'.1 hk'.2 (Or.inr rfl)
  have hedge0 := hWp s(p 0, p 1) (show (bip G R B).Adj (p 0) (p 1) from hadj 0 (by omega))
  have hk2 : k - 2 + 1 = k - 1 := by omega
  have hedgek := hWp s(p (k - 2), p (k - 1)) (show (bip G R B).Adj (p (k - 2)) (p (k - 1)) by
    have := hadj (k - 2) (by omega); rwa [hk2] at this)
  have hσcase : (σ = -1 ↔ (β (p 0) = β (p (k - 1)) ∧ β (p 0) = 3)) := by
    rw [hσdef]
    by_cases hc : (β (p 0) = β (p (k - 1)) ∧ β (p 0) = 3)
    · rw [if_pos hc]; exact ⟨fun _ => hc, fun _ => rfl⟩
    · rw [if_neg hc]; exact ⟨fun h => by norm_num at h, fun h => absurd h hc⟩
  have hend0 : 1 ≤ (ωp s(p 0, p 1) : ℤ) + σ ∧ (ωp s(p 0, p 1) : ℤ) + σ ≤ 3 := by
    rcases hσ with h | h
    · have := i0b (by rw [hdegp _ h0.1]; exact (hα0.2 (fun hh => by
        have := hσcase.2 hh; omega)))
      omega
    · have := i0a (by rw [hdegp _ h0.1]; exact hα0.1 (hσcase.1 h))
      omega
  have hendk : 1 ≤ (ωp s(p (k - 2), p (k - 1)) : ℤ) + σ ∧
      (ωp s(p (k - 2), p (k - 1)) : ℤ) + σ ≤ 3 := by
    rcases hσ with h | h
    · have := ikb (by rw [hdegp _ hk'.1]; exact (hαk.2 (fun hh => by
        have := hσcase.2 hh; omega)))
      omega
    · have := ika (by rw [hdegp _ hk'.1]; exact hαk.1 (hσcase.1 h))
      omega
  have hmid : ∀ i, 0 < i → i + 1 < k → p i ∈ B →
      3 ≤ ωp s(p (i - 1), p i) + ωp s(p i, p (i + 1)) ∧
        ωp s(p (i - 1), p i) + ωp s(p i, p (i + 1)) ≤ 5 := by
    intro i hi hik hB
    have e1 : i - 1 + 1 = i := by omega
    have e2 : i - 1 + 2 = i + 1 := by omega
    have := hmidp (i - 1) (by omega) (by rw [e1]; exact hB)
    rwa [e1, e2] at this
  obtain ⟨ωq, hWq, hoff, hBq, hRq⟩ := B2_path_mod (bip G R B) R B hdisj (fun u v h => h.2) ωp hWp
    k hk p hinj hadj h0.1 hk'.1 σ hσ hend0 hendk hmid
  obtain ⟨gf, hgf⟩ : ∃ gf : V → ℕ, ∀ u, gf u =
      ((g2 u : ℤ) - (if u = p 0 ∨ u = p (k - 1) then σ else 0)).toNat := ⟨_, fun _ => rfl⟩
  have hg2r : ∀ u, 2 ≤ g2 u ∧ g2 u ≤ 3 := by
    intro u; rw [hg2]; split_ifs <;> omega
  have hend3 : ∀ u, (u = p 0 ∨ u = p (k - 1)) → g2 u = 3 → σ = 1 := by
    intro u hu h3
    have huB : u ∈ B := by rcases hu with rfl | rfl; exact h0.1; exact hk'.1
    rw [hg2B u huB] at h3
    by_cases hH : Hi u
    · exact hσHi u hH
    · rw [if_neg hH] at h3; omega
  have hgfZ : ∀ u, (gf u : ℤ) = (g2 u : ℤ) - (if u = p 0 ∨ u = p (k - 1) then σ else 0) := by
    intro u
    have := hg2r u
    have e := hend3 u
    rw [hgf u]
    by_cases hu : u = p 0 ∨ u = p (k - 1)
    · rw [if_pos hu]; have := e hu; rcases hσ with h | h <;> omega
    · rw [if_neg hu]; omega
  have hgfb : ∀ b, G.Adj v0 b → 1 ≤ gf b ∧ gf b ≤ 3 := by
    intro b _
    have z1 := hgfZ b
    have z2 := hg2r b
    have e := hend3 b
    by_cases hu : b = p 0 ∨ b = p (k - 1)
    · rw [if_pos hu] at z1; have := e hu; rcases hσ with h | h <;> omega
    · rw [if_neg hu] at z1; omega
  have hendne : ∀ u, u = p 0 ∨ u = p (k - 1) → u ≠ u0 := by
    rintro u (h | h)
    · rw [h]; exact hu0 0 (by omega)
    · rw [h]; exact hu0 (k - 1) (by omega)
  have hendsum : ∑ u ∈ univ.filter (G.Adj v0), (if u = p 0 ∨ u = p (k - 1) then σ else 0) = 2 * σ := by
    have hfilt : (univ.filter (G.Adj v0)).filter (fun u => u = p 0 ∨ u = p (k - 1)) =
        {p 0, p (k - 1)} := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · exact fun h => h.2
      · rintro (h | h)
        · rw [h]; exact ⟨h0.2, Or.inl rfl⟩
        · rw [h]; exact ⟨hk'.2, Or.inr rfl⟩
    rw [← Finset.sum_filter, hfilt, Finset.sum_pair hne]; ring
  have hsumgf : ((∑ u ∈ univ.filter (G.Adj v0), gf u : ℕ) : ℤ) =
      ((∑ u ∈ univ.filter (G.Adj v0), g2 u : ℕ) : ℤ) - 2 * σ := by
    push_cast
    rw [← hendsum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun u _ => hgfZ u)
  have hu0off : sdeg (bip G R B) ωq u0 = sdeg (bip G R B) ωp u0 := hoff u0 (fun i hi => hu0 i hi)
  have hgfu0 : gf u0 = g2 u0 := by
    have := hgfZ u0
    rw [if_neg (fun h => hendne u0 h rfl)] at this
    omega
  refine B2_final G v0 R B hg hv0 hdom ω1 f s1 hW1 hodd hprop hs1 ωq gf hWq ?_ ?_ hgfb ?_ ?_
  · intro v hv
    have e1 := hBq v hv
    have e2 := hBfin v hv
    have e3 := hgfZ v
    have hv1 : v = p 0 → v ≠ p (k - 1) := fun h h' => hne (h.symm.trans h')
    by_cases ha : G.Adj v0 v
    · rw [if_pos ha] at e2 ⊢
      by_cases h1 : v = p 0
      · rw [if_pos h1, if_neg (hv1 h1)] at e1
        rw [if_pos (Or.inl h1)] at e3; omega
      · by_cases h2 : v = p (k - 1)
        · rw [if_neg h1, if_pos h2] at e1
          rw [if_pos (Or.inr h2)] at e3; omega
        · rw [if_neg h1, if_neg h2] at e1
          rw [if_neg (fun h => h.elim h1 h2)] at e3; omega
    · rw [if_neg ha] at e2 ⊢
      have h1 : v ≠ p 0 := fun h => ha (h ▸ h0.2)
      have h2 : v ≠ p (k - 1) := fun h => ha (h ▸ hk'.2)
      rw [if_neg h1, if_neg h2] at e1
      omega
  · intro v hv
    have hr := hRfact v hv
    have hp := hRq v hv
    rw [Nat.even_iff] at hr ⊢
    by_cases ha : G.Adj v0 v
    · have hv' := hRN v hv ha
      subst hv'
      rw [if_pos ha] at hr ⊢
      rw [hu0off, hgfu0]; exact hr
    · rw [if_neg ha] at hr ⊢
      omega
  · have := Nat.even_iff.1 hsumg2
    rw [Nat.even_iff]
    rcases hσ with h | h <;> omega
  · intro v hv ha
    have hv' := hRN v hv ha
    subst hv'
    rw [hu0off, hgfu0]
    have : ∑ u ∈ univ.filter (G.Adj v0), g2 u = sdeg (bip G R B) ωp v + g2 v := hconf0
    intro h
    rcases hσ with hs | hs <;> omega

theorem C_tree_path (T : SimpleGraph V) (hT : T.IsTree) (a b c d : V) (p : T.Walk a b)
    (hp : p.IsPath) (hc : c ∉ p.support) (hd : d ∉ p.support) (hcd : c ≠ d) :
    (∃ q : T.Walk b c, q.IsPath ∧ d ∉ q.support) ∨
    (∃ q : T.Walk a d, q.IsPath ∧ c ∉ q.support) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨q1⟩ := hT.connected.preconnected b c
  obtain ⟨q2⟩ := hT.connected.preconnected a d
  have h1 : d ∈ q1.bypass.support := by
    exact hcon.1 _ q1.bypass_isPath
  have h2 : c ∈ q2.bypass.support := by
    exact hcon.2 _ q2.bypass_isPath
  set Q1 : T.Walk b c := q1.bypass
  set Q2 : T.Walk a d := q2.bypass
  have hQ1 : Q1.IsPath := q1.bypass_isPath
  have hQ2 : Q2.IsPath := q2.bypass_isPath
  -- prefix of Q1 up to d avoids c
  have hpre : c ∉ (Q1.takeUntil d h1).support := by
    intro hm
    have hspec := congrArg Walk.support (Q1.take_spec h1)
    rw [Walk.support_append] at hspec
    have hnd : Q1.support.Nodup := hQ1.support_nodup
    rw [← hspec] at hnd
    have hdc : d ≠ c := hcd.symm
    have hm2 : c ∈ (Q1.dropUntil d h1).support.tail := Walk.end_mem_tail_support_of_ne hdc _
    exact (List.nodup_append.1 hnd).2.2 c hm c hm2 rfl
  let W : T.Walk a d := p.append (Q1.takeUntil d h1)
  have hWc : c ∉ W.support := by
    simp only [W, Walk.support_append, List.mem_append]
    rintro (h | h)
    · exact hc h
    · exact hpre (List.mem_of_mem_tail h)
  have heq : W.bypass = Q2 := by
    have := hT.isAcyclic.subsingleton_path a d
    exact congrArg Subtype.val (this.elim ⟨W.bypass, W.bypass_isPath⟩ ⟨Q2, hQ2⟩)
  apply hWc
  have : c ∈ W.bypass.support := by rw [heq]; exact h2
  exact W.support_bypass_subset_support this

theorem C_choice (G : SimpleGraph V) (x y : V) (hxy : G.Adj x y)
    (hx : 2 ≤ G.degree x) (hy : 2 ≤ G.degree y)
    (hc : (G.induce ({x, y}ᶜ : Set V)).Connected) :
    ∃ (zx zy : V) (hzx : zx ∈ ({x, y}ᶜ : Set V)) (hzy : zy ∈ ({x, y}ᶜ : Set V)),
      G.Adj x zx ∧ G.Adj y zy ∧
      (zx = zy ∨ (¬ G.Adj x zy ∧ ¬ G.Adj y zx ∧
        ∃ p : (G.induce ({x, y}ᶜ : Set V)).Walk ⟨zx, hzx⟩ ⟨zy, hzy⟩,
          p.length = (G.induce ({x, y}ᶜ : Set V)).dist ⟨zx, hzx⟩ ⟨zy, hzy⟩ ∧
          ∀ i, 0 < i → i < p.length →
            ¬ G.Adj x (p.getVert i).1 ∧ ¬ G.Adj y (p.getVert i).1)) := by
  classical
  have hnb : ∀ z w : V, G.Adj z w → 2 ≤ G.degree z → ∃ a, G.Adj z a ∧ a ≠ w := by
    intro z w _ hz
    have : 1 < (G.neighborFinset z).card := by rwa [card_neighborFinset_eq_degree]
    obtain ⟨a, ha, hne⟩ := Finset.exists_mem_ne this w
    exact ⟨a, (mem_neighborFinset _ _ _).1 ha, hne⟩
  obtain ⟨a, haxa, hay⟩ := hnb x y hxy hx
  obtain ⟨b, hbyb, hbx⟩ := hnb y x hxy.symm hy
  have haS : a ∈ ({x, y}ᶜ : Set V) := by
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨(G.ne_of_adj haxa).symm, hay⟩
  have hbS : b ∈ ({x, y}ᶜ : Set V) := by
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hbx, (G.ne_of_adj hbyb).symm⟩
  by_cases hcom : ∃ (c : V) (hcS : c ∈ ({x, y}ᶜ : Set V)), G.Adj x c ∧ G.Adj y c
  · obtain ⟨c, hcS, h1, h2⟩ := hcom
    exact ⟨c, c, hcS, hcS, h1, h2, Or.inl rfl⟩
  · push Not at hcom
    set H := G.induce ({x, y}ᶜ : Set V) with hH
    let P : Finset (({x, y}ᶜ : Set V) × ({x, y}ᶜ : Set V)) :=
      Finset.univ.filter (fun q => G.Adj x q.1.1 ∧ G.Adj y q.2.1)
    have hPne : P.Nonempty := ⟨(⟨a, haS⟩, ⟨b, hbS⟩), by simp [P, haxa, hbyb]⟩
    obtain ⟨q, hqP, hqmin⟩ := Finset.exists_min_image P (fun q => H.dist q.1 q.2) hPne
    have hq : G.Adj x q.1.1 ∧ G.Adj y q.2.1 := by simpa [P] using hqP
    obtain ⟨p, hp⟩ := hc.preconnected q.1 q.2 |>.exists_walk_length_eq_dist
    refine ⟨q.1.1, q.2.1, q.1.2, q.2.2, hq.1, hq.2, Or.inr ⟨?_, ?_, p, hp, ?_⟩⟩
    · exact fun h => hcom _ q.2.2 h hq.2
    · exact fun h => hcom _ q.1.2 hq.1 h
    · intro i hi hil
      have hlen : H.dist q.1 q.2 = p.length := hp.symm
      constructor
      · intro hxc
        have hmem : (p.getVert i, q.2) ∈ P := by simp [P, hxc, hq.2]
        have h1 := hqmin _ hmem
        have h2 : H.dist (p.getVert i) q.2 ≤ (p.drop i).length := SimpleGraph.dist_le _
        rw [Walk.drop_length] at h2
        simp only at h1
        omega
      · intro hyc
        have hmem : (q.1, p.getVert i) ∈ P := by simp [P, hyc, hq.1]
        have h1 := hqmin _ hmem
        have h2 : H.dist q.1 (p.getVert i) ≤ (p.take i).length := SimpleGraph.dist_le _
        have h3 : (p.take i).length = i := by
          have := Walk.take_length p i
          omega
        simp only at h1
        omega

theorem C_key (G : SimpleGraph V) (hG : G.Connected) (hmin : ∀ v, 2 ≤ G.degree v) (r : V)
    (x y : V) (hxy : G.Adj x y)
    (hle : G.dist r y ≤ G.dist r x)
    (hmax : ∀ u v, G.Adj u v → G.dist r u + G.dist r v ≤ G.dist r x + G.dist r y) :
    (G.induce ({x, y}ᶜ : Set V)).Connected := by
  classical
  have hdiff : ∀ u v, G.Adj u v → G.dist r u ≤ G.dist r v + 1 := by
    intro u v h
    have h1 : G.dist v u ≤ 1 := by
      simpa using SimpleGraph.dist_le (Walk.cons h.symm Walk.nil)
    have := hG.dist_triangle (u := r) (v := v) (w := u)
    omega
  have hpar : ∀ z, z ≠ r → ∃ u, G.Adj z u ∧ G.dist r u < G.dist r z := by
    intro z hz
    obtain ⟨q, hq⟩ := hG.exists_walk_length_eq_dist r z
    have key : ∀ (w : G.Walk z r), z ≠ r →
        ∃ u, G.Adj z u ∧ ∃ t : G.Walk u r, t.length + 1 = w.length := by
      intro w hne
      cases w with
      | nil => exact absurd rfl hne
      | cons h t => exact ⟨_, h, t, rfl⟩
    obtain ⟨u, hu, t, ht⟩ := key q.reverse hz
    refine ⟨u, hu, ?_⟩
    have h1 : G.dist u r ≤ t.length := SimpleGraph.dist_le t
    rw [Walk.length_reverse] at ht
    rw [SimpleGraph.dist_comm] at h1
    omega
  have hnb : ∀ z w : V, ∃ a, G.Adj z a ∧ a ≠ w := by
    intro z w
    have : 1 < (G.neighborFinset z).card := by
      rw [card_neighborFinset_eq_degree]; have := hmin z; omega
    obtain ⟨a, ha, hne⟩ := Finset.exists_mem_ne this w
    exact ⟨a, (mem_neighborFinset _ _ _).1 ha, hne⟩
  have hrx : r ≠ x := by
    intro h
    subst h
    have h0 : G.dist r r = 0 := by simp
    have : G.dist r y = 0 := by omega
    exact hxy.ne (hG.dist_eq_zero_iff.1 this)
  have hry : r ≠ y := by
    intro h
    subst h
    obtain ⟨z, hz, hzr⟩ := hnb x r
    have h1 := hmax x z hz
    have h0 : G.dist r r = 0 := by simp
    have : G.dist r z = 0 := by omega
    exact hzr (hG.dist_eq_zero_iff.1 this).symm
  have hgood : ∀ z, z ≠ x → z ≠ y → z ≠ r →
      ∃ u, u ≠ x ∧ u ≠ y ∧ G.Adj z u ∧ G.dist r u < G.dist r z := by
    intro z hzx hzy hzr
    obtain ⟨u, hzu, hlt⟩ := hpar z hzr
    by_cases hux : u = x
    · subst hux
      have := hmax z u hzu
      omega
    by_cases huy : u = y
    · subst huy
      have h1 := hmax z u hzu
      have h2 := hdiff x u hxy
      obtain ⟨u', hzu', hu'y⟩ := hnb z u
      have hu'x : u' ≠ x := by
        rintro rfl
        have := hmax z u' hzu'
        omega
      refine ⟨u', hu'x, hu'y, hzu', ?_⟩
      by_contra hcon
      have := hmax z u' hzu'
      omega
    · exact ⟨u, hux, huy, hzu, hlt⟩
  have hrS : r ∈ ({x, y}ᶜ : Set V) := by
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hrx, hry⟩
  have hreach : ∀ n, ∀ z : ({x, y}ᶜ : Set V), G.dist r z.1 = n →
      (G.induce ({x, y}ᶜ : Set V)).Reachable z ⟨r, hrS⟩ := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro z hz
      have hzS := z.2
      simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hzS
      by_cases hzr : z.1 = r
      · have : z = ⟨r, hrS⟩ := Subtype.ext hzr
        rw [this]
      · obtain ⟨u, hux, huy, hzu, hlt⟩ := hgood z.1 hzS.1 hzS.2 hzr
        have huS : u ∈ ({x, y}ᶜ : Set V) := by
          simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
          exact ⟨hux, huy⟩
        have h1 := ih (G.dist r u) (by omega) ⟨u, huS⟩ rfl
        exact (SimpleGraph.Adj.reachable (by simpa using hzu)).trans h1
  haveI : Nonempty ({x, y}ᶜ : Set V) := ⟨⟨r, hrS⟩⟩
  exact ⟨fun a b => (hreach _ a rfl).trans (hreach _ b rfl).symm⟩

theorem lemma10 (G : SimpleGraph V) (hG : G.Connected) (hmin : ∀ v, 2 ≤ G.degree v) :
    ∃ x y, G.Adj x y ∧ (G.induce ({x, y}ᶜ : Set V)).Connected := by
  classical
  obtain ⟨r⟩ := hG.nonempty
  have h2 : 1 < (G.neighborFinset r).card := by
    rw [card_neighborFinset_eq_degree]; have := hmin r; omega
  obtain ⟨b, hb⟩ := Finset.card_pos.1 (by omega : 0 < (G.neighborFinset r).card)
  have hne : (Finset.univ.filter (fun q : V × V => G.Adj q.1 q.2)).Nonempty :=
    ⟨(r, b), by simpa using (mem_neighborFinset _ _ _).1 hb⟩
  obtain ⟨q, hqP, hq⟩ := Finset.exists_max_image _
    (fun q : V × V => G.dist r q.1 + G.dist r q.2) hne
  have hqa : G.Adj q.1 q.2 := by simpa using hqP
  have hmax : ∀ u v, G.Adj u v → G.dist r u + G.dist r v ≤ G.dist r q.1 + G.dist r q.2 :=
    fun u v h => hq (u, v) (by simpa using h)
  rcases le_total (G.dist r q.2) (G.dist r q.1) with h | h
  · exact ⟨q.1, q.2, hqa, C_key G hG hmin r q.1 q.2 hqa h hmax⟩
  · refine ⟨q.2, q.1, hqa.symm, C_key G hG hmin r q.2 q.1 hqa.symm h ?_⟩
    intro u v huv
    have := hmax u v huv
    omega

theorem C_bip_adj (G : SimpleGraph V) (R B : Finset V) (u v : V) :
    (bip G R B).Adj u v ↔ G.Adj u v ∧ ((u ∈ R ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ R)) := Iff.rfl

theorem C_deg_one (hV : 3 ≤ Fintype.card V) (G : SimpleGraph V) (hG : G.Connected) (x : V)
    (hx : G.degree x = 1) : ∃ ω, Wt3 G ω ∧ Proper G ω := by
  obtain ⟨y, hxy, huniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.1 hx
  have hyx : y ≠ x := (G.ne_of_adj hxy).symm
  have hG' : (G.induce ({x}ᶜ : Set V)).Connected :=
    hG.induce_compl_singleton_of_degree_eq_one hx
  have hyS : y ∈ ({x}ᶜ : Set V) := hyx
  obtain ⟨R, hRind, hyR, hRconn, -⟩ :=
    lemma2 (G.induce ({x}ᶜ : Set V)) hG' ⟨y, hyS⟩ ⟨y, hyS⟩ Walk.nil (by simp) true
  have hRconn' : ∀ a b : ({x}ᶜ : Set V),
      (bip (G.induce ({x}ᶜ : Set V)) R Rᶜ).Reachable a b := by
    intro a b; convert hRconn a b
  let e : ({x}ᶜ : Set V) ↪ V := Function.Embedding.subtype _
  let R' : Finset V := R.map e
  let B' : Finset V := Rᶜ.map e
  have hR'mem : ∀ v, v ∈ R' ↔ ∃ h : v ∈ ({x}ᶜ : Set V), (⟨v, h⟩ : ({x}ᶜ : Set V)) ∈ R := by
    intro v
    constructor
    · intro h
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 h
      exact ⟨a.2, ha⟩
    · rintro ⟨h, hv⟩
      exact Finset.mem_map.2 ⟨⟨v, h⟩, hv, rfl⟩
  have hB'mem : ∀ v, v ∈ B' ↔ ∃ h : v ∈ ({x}ᶜ : Set V), (⟨v, h⟩ : ({x}ᶜ : Set V)) ∉ R := by
    intro v
    constructor
    · intro h
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 h
      exact ⟨a.2, Finset.mem_compl.1 ha⟩
    · rintro ⟨h, hv⟩
      exact Finset.mem_map.2 ⟨⟨v, h⟩, Finset.mem_compl.2 hv, rfl⟩
  have hcov : ∀ v, v ≠ x → v ∈ R' ∨ v ∈ B' := by
    intro v hv
    by_cases h : (⟨v, hv⟩ : ({x}ᶜ : Set V)) ∈ R
    · exact Or.inl ((hR'mem v).2 ⟨hv, h⟩)
    · exact Or.inr ((hB'mem v).2 ⟨hv, h⟩)
  have hxR : x ∉ R' := fun h => by obtain ⟨h1, _⟩ := (hR'mem x).1 h; exact h1 rfl
  have hxB : x ∉ B' := fun h => by obtain ⟨h1, _⟩ := (hB'mem x).1 h; exact h1 rfl
  have hdisj : Disjoint R' B' := by
    rw [Finset.disjoint_left]
    intro v h1 h2
    obtain ⟨p1, q1⟩ := (hR'mem v).1 h1
    obtain ⟨p2, q2⟩ := (hB'mem v).1 h2
    exact q2 q1
  have hind' : ∀ u ∈ R', ∀ v ∈ R', ¬ G.Adj u v := by
    intro u hu v hv huv
    obtain ⟨p1, q1⟩ := (hR'mem u).1 hu
    obtain ⟨p2, q2⟩ := (hR'mem v).1 hv
    exact hRind _ q1 _ q2 huv
  have hyR' : y ∈ R' := (hR'mem y).2 ⟨hyS, (hyR.2 rfl)⟩
  have hlift : ∀ (G1 : SimpleGraph V) (B2 : Finset V), B' ⊆ B2 →
      (∀ a b : ({x}ᶜ : Set V), (G.induce ({x}ᶜ : Set V)).Adj a b → G1.Adj a.1 b.1) →
      ∀ a b : ({x}ᶜ : Set V), (bip (G.induce ({x}ᶜ : Set V)) R Rᶜ).Reachable a b →
        (bip G1 R' B2).Reachable a.1 b.1 := by
    intro G1 B2 hB2 hG1 a b hab
    let f : bip (G.induce ({x}ᶜ : Set V)) R Rᶜ →g bip G1 R' B2 :=
      ⟨Subtype.val, fun {a b} h => by
        rw [C_bip_adj] at h ⊢
        refine ⟨hG1 a b h.1, ?_⟩
        rcases h.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨(hR'mem _).2 ⟨a.2, h1⟩, hB2 ((hB'mem _).2 ⟨b.2, Finset.mem_compl.1 h2⟩)⟩
        · exact Or.inr ⟨hB2 ((hB'mem _).2 ⟨a.2, Finset.mem_compl.1 h1⟩), (hR'mem _).2 ⟨b.2, h2⟩⟩⟩
    exact hab.map f
  have hcard : B'.card = Rᶜ.card := Finset.card_map _
  rcases Nat.even_or_odd B'.card with hev | hodd
  · -- cas |B| pair : on retire x
    let G0 : SimpleGraph V :=
      { Adj := fun u v => G.Adj u v ∧ s(u, v) ≠ s(x, y)
        symm := ⟨fun u v h => ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩⟩
        loopless := ⟨fun u h => G.loopless.irrefl u h.1⟩ }
    have G0adj : ∀ u v, G0.Adj u v ↔ G.Adj u v ∧ s(u, v) ≠ s(x, y) := fun _ _ => Iff.rfl
    have hG0x : ∀ v, ¬ G0.Adj x v := by
      intro v h
      have := huniq v h.1
      subst this
      exact h.2 rfl
    have hG0x' : ∀ v, ¬ G0.Adj v x := fun v h => hG0x v h.symm
    have hG0le : G0 ≤ G := fun u v h => h.1
    have hg : Good G0 R' B' :=
      { disj := hdisj
        indep := fun u hu v hv h => hind' u hu v hv (hG0le h)
        conn := by
          intro u hu v hv
          have hall : ∀ w ∈ R' ∪ B', (bip G0 R' B').Reachable w y := by
            intro w hw
            have hwx : w ≠ x := by
              rintro rfl
              rcases Finset.mem_union.1 hw with h | h
              · exact hxR h
              · exact hxB h
            exact hlift G0 B' (Finset.Subset.refl _)
              (fun a b h => by
                refine ⟨h, ?_⟩
                intro hs
                rw [Sym2.eq_iff] at hs
                rcases hs with ⟨h1, _⟩ | ⟨_, h2⟩
                · exact a.2 h1
                · exact b.2 h2)
              ⟨w, hwx⟩ ⟨y, hyS⟩ (hRconn' _ _)
          exact (hall u hu).trans (hall v hv).symm
        even := hev }
    have hdom : ∀ u v, G0.Adj u v → u ∈ R' ∪ B' ∧ v ∈ R' ∪ B' := by
      intro u v h
      have hu : u ≠ x := fun h' => hG0x v (h' ▸ h)
      have hv : v ≠ x := fun h' => hG0x' u (h' ▸ h)
      exact ⟨by rcases hcov u hu with a | a <;> simp [a],
        by rcases hcov v hv with a | a <;> simp [a]⟩
    obtain ⟨ω0, hW0, hP0, hpar0⟩ := lemma7 G0 R' B' hg hdom
    let ω : Sym2 V → ℕ := fun e => if e = s(x, y) then 2 else ω0 e
    have hω : ∀ u v, s(u, v) ≠ s(x, y) → ω s(u, v) = ω0 s(u, v) := by
      intro u v h; simp [ω, h]
    have hne : ∀ v, v ≠ x → v ≠ y → ∀ u, s(v, u) ≠ s(x, y) := by
      intro v h1 h2 u h
      rw [Sym2.eq_iff] at h
      rcases h with ⟨a, _⟩ | ⟨a, _⟩
      · exact h1 a
      · exact h2 a
    have hs_other : ∀ v, v ≠ x → v ≠ y → sdeg G ω v = sdeg G0 ω0 v := by
      intro v h1 h2
      unfold sdeg
      have hf : univ.filter (G.Adj v) =
          @Finset.filter V (G0.Adj v) (fun a => Classical.propDecidable (G0.Adj v a)) univ := by
        ext u
        simp [G0adj, Sym2.eq_iff, h1, h2]
      refine Finset.sum_congr hf ?_
      intro u _
      exact hω v u (hne v h1 h2 u)
    have hs_x : sdeg G ω x = 2 := by
      unfold sdeg
      have hf : univ.filter (G.Adj x) = {y} := by
        ext u
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        exact ⟨fun h => huniq u h, fun h => h ▸ hxy⟩
      rw [hf, Finset.sum_singleton]
      simp [ω]
    have hs_y : sdeg G ω y = sdeg G0 ω0 y + 2 := by
      unfold sdeg
      have hf : univ.filter (G.Adj y) = insert x
          (@Finset.filter V (G0.Adj y) (fun a => Classical.propDecidable (G0.Adj y a)) univ) := by
        ext u
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, G0adj]
        constructor
        · intro h
          by_cases hu : u = x
          · exact Or.inl hu
          · refine Or.inr ⟨h, ?_⟩
            intro hs
            rw [Sym2.eq_iff] at hs
            rcases hs with ⟨a, _⟩ | ⟨_, b⟩
            · exact hyx a
            · exact hu b
        · rintro (h | h)
          · subst h; exact hxy.symm
          · exact h.1
      rw [hf, Finset.sum_insert (by simpa using hG0x' y)]
      have h2 : ω s(y, x) = 2 := by
        have : s(y, x) = s(x, y) := Sym2.eq_swap
        simp [ω, this]
      rw [h2, add_comm]
      congr 1
      refine Finset.sum_congr ?_ ?_
      · first | rfl | (ext u; simp)
      intro u hu
      have hu' : s(y, u) ≠ s(x, y) := ((G0adj _ _).1 (by simpa using hu)).2
      exact hω y u hu'
    -- y a un voisin dans G0
    have hy_nb : ∃ z, G0.Adj y z := by
      have : ∃ w, w ≠ x ∧ w ≠ y := by
        by_contra hcon
        push Not at hcon
        have hsub : (univ : Finset V) ⊆ {x, y} := by
          intro v _
          by_cases h1 : v = x
          · simp [h1]
          · simp [hcon v h1]
        have := Finset.card_le_card hsub
        have h2 : ({x, y} : Finset V).card ≤ 2 := Finset.card_le_two
        rw [Finset.card_univ] at this
        omega
      obtain ⟨w, hwx, hwy⟩ := this
      obtain ⟨p⟩ := hG'.preconnected ⟨y, hyS⟩ ⟨w, hwx⟩
      cases p with
      | nil => exact absurd rfl hwy
      | cons h t =>
        rename_i z
        refine ⟨z.1, h, ?_⟩
        intro hs
        rw [Sym2.eq_iff] at hs
        rcases hs with ⟨a, _⟩ | ⟨_, b⟩
        · exact hyx a
        · exact z.2 b
    have hs0y : 2 ≤ sdeg G0 ω0 y := by
      obtain ⟨z, hz⟩ := hy_nb
      have h1 : 1 ≤ ω0 s(y, z) := (hW0 _ ((SimpleGraph.mem_edgeSet _).2 hz)).1
      have h2 : ω0 s(y, z) ≤ sdeg G0 ω0 y :=
        Finset.single_le_sum (f := fun u => ω0 s(y, u)) (fun _ _ => Nat.zero_le _)
          (by simpa using hz)
      have hev' : Even (sdeg G0 ω0 y) := (hpar0 y (by simp [hyR'])).2 hyR'
      obtain ⟨k, hk⟩ := hev'
      omega
    refine ⟨ω, ?_, ?_⟩
    · intro e he
      induction e using Sym2.ind with
      | h u v =>
        by_cases h : s(u, v) = s(x, y)
        · simp [ω, h]
        · have hadj : G0.Adj u v := ⟨(SimpleGraph.mem_edgeSet _).1 he, h⟩
          rw [show ω s(u, v) = ω0 s(u, v) from hω u v h]
          exact hW0 _ ((SimpleGraph.mem_edgeSet _).2 hadj)
    · intro u v huv
      by_cases hux : u = x
      · subst hux
        have := huniq v huv
        subst this
        rw [hs_x, hs_y]; omega
      by_cases hvx : v = x
      · subst hvx
        have := huniq u huv.symm
        subst this
        rw [hs_x, hs_y]; omega
      -- u, v ≠ x
      have hmem : ∀ w, w ≠ x → w ∈ R' ∪ B' := by
        intro w hw
        rcases hcov w hw with a | a <;> simp [a]
      have hG0uv : G0.Adj u v := by
        refine ⟨huv, ?_⟩
        intro hs
        rw [Sym2.eq_iff] at hs
        rcases hs with ⟨a, _⟩ | ⟨_, b⟩
        · exact hux a
        · exact hvx b
      have hy_case : ∀ w, w ≠ x → w ≠ y → G.Adj y w → sdeg G ω y ≠ sdeg G ω w := by
        intro w hw1 hw2 hyw
        have hwB : w ∈ B' := by
          rcases hcov w hw1 with a | a
          · exact absurd hyw (hind' y hyR' w a)
          · exact a
        have hwR : w ∉ R' := fun h => Finset.disjoint_left.1 hdisj h hwB
        have hodd : ¬ Even (sdeg G0 ω0 w) := fun h => hwR ((hpar0 w (hmem w hw1)).1 h)
        have hev' : Even (sdeg G0 ω0 y) := (hpar0 y (hmem y hyx)).2 hyR'
        rw [hs_y, hs_other w hw1 hw2]
        intro heq
        apply hodd
        have : Even (sdeg G0 ω0 y + 2) := hev'.add (by decide)
        rw [heq] at this
        exact this
      by_cases huy : u = y
      · subst huy
        exact hy_case v hvx (G.ne_of_adj huv).symm huv
      by_cases hvy : v = y
      · subst hvy
        exact (hy_case u hux (G.ne_of_adj huv) huv.symm).symm
      rw [hs_other u hux huy, hs_other v hvx hvy]
      exact hP0 u v hG0uv
  · -- cas |B| impair : on ajoute x à B
    have hxB' : x ∉ B' := hxB
    have hg : Good G R' (insert x B') :=
      { disj := Finset.disjoint_insert_right.2 ⟨hxR, hdisj⟩
        indep := hind'
        conn := by
          intro u hu v hv
          have hall : ∀ w ∈ R' ∪ insert x B', (bip G R' (insert x B')).Reachable w y := by
            intro w hw
            by_cases hwx : w = x
            · subst hwx
              exact SimpleGraph.Adj.reachable
                ((C_bip_adj _ _ _ _ _).2 ⟨hxy, Or.inr ⟨Finset.mem_insert_self _ _, hyR'⟩⟩)
            · exact hlift G (insert x B') (Finset.subset_insert _ _)
                (fun a b h => h) ⟨w, hwx⟩ ⟨y, hyS⟩ (hRconn' _ _)
          exact (hall u hu).trans (hall v hv).symm
        even := by
          rw [Finset.card_insert_of_notMem hxB']
          exact hodd.add_one }
    have hdom : ∀ u v, G.Adj u v → u ∈ R' ∪ insert x B' ∧ v ∈ R' ∪ insert x B' := by
      intro u v _
      have hmem : ∀ w, w ∈ R' ∪ insert x B' := by
        intro w
        by_cases hw : w = x
        · simp [hw]
        · rcases hcov w hw with a | a <;> simp [a]
      exact ⟨hmem u, hmem v⟩
    obtain ⟨ω, hW, hP, -⟩ := lemma7 G R' (insert x B') hg hdom
    exact ⟨ω, hW, hP⟩

theorem C_mem_map (S : Set V) (R : Finset S) (v : V) :
    v ∈ R.map (Function.Embedding.subtype _) ↔ ∃ h : v ∈ S, (⟨v, h⟩ : S) ∈ R := by
  constructor
  · intro h
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 h
    exact ⟨a.2, ha⟩
  · rintro ⟨h, hv⟩
    exact Finset.mem_map.2 ⟨⟨v, h⟩, hv, rfl⟩

theorem C_lift (G : SimpleGraph V) (S : Set V) (R : Finset S) (a b : S)
    (h : (bip (G.induce S) R Rᶜ).Reachable a b) :
    (bip G (R.map (Function.Embedding.subtype _)) (Rᶜ.map (Function.Embedding.subtype _))).Reachable
      a.1 b.1 := by
  let f : bip (G.induce S) R Rᶜ →g
      bip G (R.map (Function.Embedding.subtype _)) (Rᶜ.map (Function.Embedding.subtype _)) :=
    ⟨Subtype.val, fun {a b} h => by
      rw [C_bip_adj] at h ⊢
      refine ⟨h.1, ?_⟩
      rcases h.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨(C_mem_map S R _).2 ⟨a.2, h1⟩, (C_mem_map S Rᶜ _).2 ⟨b.2, h2⟩⟩
      · exact Or.inr ⟨(C_mem_map S Rᶜ _).2 ⟨a.2, h1⟩, (C_mem_map S R _).2 ⟨b.2, h2⟩⟩⟩
  exact h.map f

theorem C_setup (G : SimpleGraph V) (x y zx zy : V) (hzx : zx ∈ ({x, y}ᶜ : Set V))
    (hzy : zy ∈ ({x, y}ᶜ : Set V)) (hc : (G.induce ({x, y}ᶜ : Set V)).Connected)
    (p : (G.induce ({x, y}ᶜ : Set V)).Walk ⟨zx, hzx⟩ ⟨zy, hzy⟩)
    (hp : p.length = (G.induce ({x, y}ᶜ : Set V)).dist ⟨zx, hzx⟩ ⟨zy, hzy⟩) (b : Bool) :
    ∃ R B : Finset V, Disjoint R B ∧ (∀ v, (v ∈ R ∨ v ∈ B) ↔ (v ≠ x ∧ v ≠ y)) ∧
      (∀ u ∈ R, ∀ v ∈ R, ¬ G.Adj u v) ∧ (zx ∈ R ↔ b = true) ∧
      (∀ u ∈ R ∪ B, ∀ v ∈ R ∪ B, (bip G R B).Reachable u v) ∧
      (∀ i, i < p.length → (bip G R B).Adj (p.getVert i).1 (p.getVert (i + 1)).1) := by
  obtain ⟨R, hRind, hzR, hRconn, hRedge⟩ :=
    lemma2 (G.induce ({x, y}ᶜ : Set V)) hc ⟨zx, hzx⟩ ⟨zy, hzy⟩ p hp b
  have hRconn' : ∀ a b : ({x, y}ᶜ : Set V),
      (bip (G.induce ({x, y}ᶜ : Set V)) R Rᶜ).Reachable a b := by
    intro a b; convert hRconn a b
  have hmemR := C_mem_map ({x, y}ᶜ : Set V) R
  have hmemB := C_mem_map ({x, y}ᶜ : Set V) Rᶜ
  refine ⟨R.map (Function.Embedding.subtype _), Rᶜ.map (Function.Embedding.subtype _),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro v h1 h2
    obtain ⟨p1, q1⟩ := (hmemR v).1 h1
    obtain ⟨p2, q2⟩ := (hmemB v).1 h2
    exact (Finset.mem_compl.1 q2) q1
  · intro v
    constructor
    · rintro (h | h)
      · obtain ⟨p1, _⟩ := (hmemR v).1 h
        simpa [not_or] using p1
      · obtain ⟨p1, _⟩ := (hmemB v).1 h
        simpa [not_or] using p1
    · rintro ⟨h1, h2⟩
      have hv : v ∈ ({x, y}ᶜ : Set V) := by simp [h1, h2]
      by_cases hr : (⟨v, hv⟩ : ({x, y}ᶜ : Set V)) ∈ R
      · exact Or.inl ((hmemR v).2 ⟨hv, hr⟩)
      · exact Or.inr ((hmemB v).2 ⟨hv, Finset.mem_compl.2 hr⟩)
  · intro u hu v hv huv
    obtain ⟨p1, q1⟩ := (hmemR u).1 hu
    obtain ⟨p2, q2⟩ := (hmemR v).1 hv
    exact hRind _ q1 _ q2 huv
  · have : (⟨zx, hzx⟩ : ({x, y}ᶜ : Set V)) ∈ R ↔ b = true := hzR
    rw [← this]
    exact ⟨fun h => by obtain ⟨_, q⟩ := (hmemR zx).1 h; exact q,
      fun h => (hmemR zx).2 ⟨hzx, h⟩⟩
  · intro u hu v hv
    have hall : ∀ w ∈ R.map (Function.Embedding.subtype _) ∪
        Rᶜ.map (Function.Embedding.subtype _),
        (bip G (R.map (Function.Embedding.subtype _))
          (Rᶜ.map (Function.Embedding.subtype _))).Reachable w zx := by
      intro w hw
      have hwS : w ∈ ({x, y}ᶜ : Set V) := by
        rcases Finset.mem_union.1 hw with h | h
        · exact ((C_mem_map _ R w).1 h).1
        · exact ((C_mem_map _ Rᶜ w).1 h).1
      have h1 := C_lift G _ R ⟨w, hwS⟩ ⟨zx, hzx⟩ (by convert hRconn ⟨w, hwS⟩ ⟨zx, hzx⟩)
      convert h1
    exact (hall u hu).trans (hall v hv).symm
  · intro i hi
    have hmem : s(p.getVert i, p.getVert (i + 1)) ∈ p.edges := by
      have hlt : i < p.darts.length := by rw [Walk.length_darts]; exact hi
      show s(p.getVert i, p.getVert (i + 1)) ∈ p.darts.map Dart.edge
      refine List.mem_map.2 ⟨p.darts[i], List.getElem_mem hlt, ?_⟩
      rw [Walk.darts_getElem_eq_getVert]
      rfl
    obtain ⟨a, ha, c, hc', hac⟩ := hRedge _ hmem
    have hadj : G.Adj (p.getVert i).1 (p.getVert (i + 1)).1 := p.adj_getVert_succ hi
    rw [C_bip_adj]
    refine ⟨hadj, ?_⟩
    rw [Sym2.eq_iff] at hac
    rcases hac with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      refine ⟨(C_mem_map _ R _).2 ⟨(p.getVert i).2, ?_⟩, (C_mem_map _ Rᶜ _).2 ⟨(p.getVert (i+1)).2, ?_⟩⟩
      · rw [h1]; exact ha
      · rw [h2]; exact Finset.mem_compl.2 hc'
    · right
      refine ⟨(C_mem_map _ Rᶜ _).2 ⟨(p.getVert i).2, ?_⟩, (C_mem_map _ R _).2 ⟨(p.getVert (i+1)).2, ?_⟩⟩
      · rw [h1]; exact Finset.mem_compl.2 hc'
      · rw [h2]; exact ha

theorem C_conn_ext (G : SimpleGraph V) (R B R2 B2 : Finset V) (u0 : V) (hu0 : u0 ∈ R ∪ B)
    (hR : R ⊆ R2) (hB : B ⊆ B2)
    (hc : ∀ u ∈ R ∪ B, ∀ v ∈ R ∪ B, (bip G R B).Reachable u v)
    (hnew : ∀ w ∈ R2 ∪ B2, w ∉ R ∪ B → ∃ u ∈ R ∪ B, (bip G R2 B2).Adj w u) :
    ∀ u ∈ R2 ∪ B2, ∀ v ∈ R2 ∪ B2, (bip G R2 B2).Reachable u v := by
  have hmono : bip G R B ≤ bip G R2 B2 := by
    intro u v h
    have h' := (C_bip_adj _ _ _ _ _).1 h
    exact (C_bip_adj _ _ _ _ _).2 ⟨h'.1, h'.2.imp (fun a => ⟨hR a.1, hB a.2⟩)
      (fun a => ⟨hB a.1, hR a.2⟩)⟩
  have hall : ∀ w ∈ R2 ∪ B2, (bip G R2 B2).Reachable w u0 := by
    intro w hw
    by_cases h : w ∈ R ∪ B
    · exact (hc w h u0 hu0).mono hmono
    · obtain ⟨u, hu, hadj⟩ := hnew w hw h
      exact hadj.reachable.trans ((hc u hu u0 hu0).mono hmono)
  intro u hu v hv
  exact (hall u hu).trans (hall v hv).symm

theorem C_nb2 (G : SimpleGraph V) (a b c : V) (hd : G.degree a = 2) (hb : G.Adj a b)
    (hc' : G.Adj a c) (hbc : b ≠ c) : ∀ u, G.Adj a u → u = b ∨ u = c := by
  intro u hu
  by_contra hcon
  push Not at hcon
  have hsub : ({b, c, u} : Finset V) ⊆ G.neighborFinset a := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl <;> simpa
  have h1 := Finset.card_le_card hsub
  rw [card_neighborFinset_eq_degree, hd] at h1
  have h2 : ({b, c, u} : Finset V).card = 3 := by
    rw [Finset.card_eq_three]; exact ⟨b, c, u, hbc, hcon.1.symm, hcon.2.symm, rfl⟩
  omega

theorem C_case22_d (G : SimpleGraph V) (x y zx zy : V) (hxy : G.Adj x y)
    (hdx : G.degree x = 2) (hdy : G.degree y = 2) (hzx : G.Adj x zx) (hzxy : zx ≠ y)
    (hzy : G.Adj y zy) (hzyx : zy ≠ x) (R B : Finset V) (hdisj : Disjoint R B)
    (hcov : ∀ v, (v ∈ R ∨ v ∈ B) ↔ (v ≠ x ∧ v ≠ y)) (hind : ∀ u ∈ R, ∀ v ∈ R, ¬ G.Adj u v)
    (hzxR : zx ∈ R) (hzyR : zy ∈ R)
    (hconn : ∀ u ∈ R ∪ B, ∀ v ∈ R ∪ B, (bip G R B).Reachable u v) (hodd : Odd B.card) :
    ∃ ω, Wt3 G ω ∧ Proper G ω := by
  have hxne : x ≠ y := G.ne_of_adj hxy
  have hzxx : zx ≠ x := (G.ne_of_adj hzx).symm
  have hzyy : zy ≠ y := (G.ne_of_adj hzy).symm
  have hNx := C_nb2 G x y zx hdx hxy hzx hzxy.symm
  have hNy := C_nb2 G y x zy hdy hxy.symm hzy hzyx.symm
  have hxn : x ∉ R ∧ x ∉ B := by
    have := (hcov x).not.2 (by simp)
    simpa using this
  have hyn : y ∉ R ∧ y ∉ B := by
    have := (hcov y).not.2 (by simp)
    simpa using this
  let G1 : SimpleGraph V :=
    { Adj := fun u v => (G.Adj u v ∧ u ≠ x ∧ u ≠ y ∧ v ≠ x ∧ v ≠ y) ∨ s(u, v) = s(x, zx)
      symm := ⟨fun u v h => by
        rcases h with h | h
        · exact Or.inl ⟨h.1.symm, h.2.2.2.1, h.2.2.2.2, h.2.1, h.2.2.1⟩
        · exact Or.inr (by rw [Sym2.eq_swap]; exact h)⟩
      loopless := ⟨fun u h => by
        rcases h with h | h
        · exact G.loopless.irrefl u h.1
        · rw [Sym2.eq_iff] at h
          rcases h with ⟨a, b⟩ | ⟨a, b⟩
          · exact hzxx (b.symm.trans a)
          · exact hzxx (a.symm.trans b)⟩ }
  have G1adj : ∀ u v, G1.Adj u v ↔
      (G.Adj u v ∧ u ≠ x ∧ u ≠ y ∧ v ≠ x ∧ v ≠ y) ∨ s(u, v) = s(x, zx) := fun _ _ => Iff.rfl
  have hRB : ∀ w, w ≠ x → w ≠ y → w ∈ R ∨ w ∈ B := fun w a b => (hcov w).2 ⟨a, b⟩
  have hzxB : zx ∉ B := fun h => Finset.disjoint_left.1 hdisj hzxR h
  have hzyB : zy ∉ B := fun h => Finset.disjoint_left.1 hdisj hzyR h
  have hu0 : zx ∈ R ∪ B := Finset.mem_union_left _ hzxR
  -- Good G1 R (insert x B)
  have hmono : bip G R B ≤ bip G1 R B := by
    intro u v h
    have h' := (C_bip_adj _ _ _ _ _).1 h
    have hu : u ∈ R ∪ B := by
      rcases h'.2 with a | a
      · exact Finset.mem_union_left _ a.1
      · exact Finset.mem_union_right _ a.1
    have hv : v ∈ R ∪ B := by
      rcases h'.2 with a | a
      · exact Finset.mem_union_right _ a.2
      · exact Finset.mem_union_left _ a.2
    have hu' := (hcov u).1 (Finset.mem_union.1 hu)
    have hv' := (hcov v).1 (Finset.mem_union.1 hv)
    exact (C_bip_adj _ _ _ _ _).2 ⟨(G1adj _ _).2 (Or.inl ⟨h'.1, hu'.1, hu'.2, hv'.1, hv'.2⟩), h'.2⟩
  have hconn1 : ∀ u ∈ R ∪ B, ∀ v ∈ R ∪ B, (bip G1 R B).Reachable u v :=
    fun u hu v hv => (hconn u hu v hv).mono hmono
  have hg : Good G1 R (insert x B) :=
    { disj := by
        rw [Finset.disjoint_insert_right]; exact ⟨hxn.1, hdisj⟩
      indep := by
        intro u hu v hv huv
        rcases (G1adj _ _).1 huv with h | h
        · exact hind u hu v hv h.1
        · rw [Sym2.eq_iff] at h
          rcases h with ⟨a, _⟩ | ⟨_, b⟩
          · exact hxn.1 (a ▸ hu)
          · exact hxn.1 (b ▸ hv)
      conn := C_conn_ext G1 R B R (insert x B) zx hu0 (Finset.Subset.refl _)
        (Finset.subset_insert _ _) hconn1 (by
          intro w hw hwn
          simp only [Finset.mem_union, Finset.mem_insert] at hw hwn
          rcases hw with h | rfl | h
          · exact absurd (Or.inl h) hwn
          · exact ⟨zx, hu0, (C_bip_adj _ _ _ _ _).2 ⟨(G1adj _ _).2 (Or.inr rfl),
              Or.inr ⟨by simp, hzxR⟩⟩⟩
          · exact absurd (Or.inr h) hwn)
      even := by
        rw [Finset.card_insert_of_notMem hxn.2]
        exact hodd.add_one }
  have hdom : ∀ u v, G1.Adj u v → u ∈ R ∪ insert x B ∧ v ∈ R ∪ insert x B := by
    intro u v h
    rcases (G1adj _ _).1 h with h | h
    · refine ⟨?_, ?_⟩
      · rcases hRB u h.2.1 h.2.2.1 with a | a <;> simp [a]
      · rcases hRB v h.2.2.2.1 h.2.2.2.2 with a | a <;> simp [a]
    · rw [Sym2.eq_iff] at h
      rcases h with ⟨a, b⟩ | ⟨a, b⟩
      · subst a; subst b; simp [hzxR]
      · subst a; subst b; simp [hzxR]
  obtain ⟨ωt, hWt, hPt, hpart⟩ := lemma7 G1 R (insert x B) hg hdom
  -- degré de x dans G1
  have hG1x : ∀ v, G1.Adj x v ↔ v = zx := by
    intro v
    rw [G1adj]
    constructor
    · rintro (h | h)
      · exact absurd rfl h.2.1
      · exact (Sym2.congr_right.1 h)
    · rintro rfl; exact Or.inr rfl
  have hsx : sdeg G1 ωt x = ωt s(x, zx) := by
    unfold sdeg
    rw [Finset.sum_eq_single zx]
    · intro b hb hne
      exact absurd ((hG1x b).1 (by simpa using hb)) hne
    · intro h
      exact absurd (by simp [hG1x]) h
  have hax : ¬ Even (ωt s(x, zx)) := by
    rw [← hsx]
    intro h
    exact hxn.1 ((hpart x (by simp)).1 h)
  -- poids intermédiaire ω1
  obtain ⟨ω1, h1a, h1b, h1c⟩ : ∃ ω1 : Sym2 V → ℕ, ω1 s(x, zx) = 1 ∧ ω1 s(y, zy) = 2 ∧
      ∀ e, e ≠ s(x, zx) → e ≠ s(y, zy) → ω1 e = ωt e := by
    refine ⟨fun e => if e = s(x, zx) then 1 else if e = s(y, zy) then 2 else ωt e, ?_, ?_, ?_⟩
    · simp
    · have : s(y, zy) ≠ s(x, zx) := by
        intro h; rw [Sym2.eq_iff] at h
        rcases h with ⟨a, _⟩ | ⟨a, _⟩
        · exact hxne a.symm
        · exact hzxy a.symm
      simp [this]
    · intro e h1 h2; simp [h1, h2]
  have hne1 : ∀ v u, v ≠ x → v ≠ y → u ≠ x → u ≠ y → s(v, u) ≠ s(x, zx) ∧ s(v, u) ≠ s(y, zy) := by
    intro v u hv1 hv2 hu1 hu2
    constructor
    · intro h; rw [Sym2.eq_iff] at h
      rcases h with ⟨a, _⟩ | ⟨_, b⟩
      · exact hv1 a
      · exact hu1 b
    · intro h; rw [Sym2.eq_iff] at h
      rcases h with ⟨a, _⟩ | ⟨_, b⟩
      · exact hv2 a
      · exact hu2 b
  have hstar : ∀ v, v ≠ x → v ≠ y →
      sdeg G ω1 v + (if v = zx then ωt s(x, zx) else 0) =
        sdeg G1 ωt v + (if v = zx then 1 else 0) + (if v = zy then 2 else 0) := by
    intro v hvx hvy
    have e1 : sdeg G ω1 v = ∑ u, if G.Adj v u then ω1 s(v, u) else 0 := by
      unfold sdeg; rw [Finset.sum_filter]; try convert rfl
    have e2 : sdeg G1 ωt v = ∑ u, if G1.Adj v u then ωt s(v, u) else 0 := by
      unfold sdeg; rw [Finset.sum_filter]; try convert rfl
    have e3 : (if v = zx then ωt s(x, zx) else 0) =
        ∑ u, if v = zx ∧ u = x then ωt s(x, zx) else 0 := by
      by_cases hv : v = zx <;> simp [hv]
    have e4 : (if v = zx then 1 else 0) + (if v = zy then 2 else 0) =
        ∑ u, ((if v = zx ∧ u = x then 1 else 0) + (if v = zy ∧ u = y then 2 else 0)) := by
      have s1 : (if v = zx then 1 else 0) = ∑ u, if v = zx ∧ u = x then 1 else 0 := by
        by_cases hv : v = zx <;> simp [hv]
      have s2 : (if v = zy then 2 else 0) = ∑ u, if v = zy ∧ u = y then 2 else 0 := by
        by_cases hv : v = zy <;> simp [hv]
      rw [Finset.sum_add_distrib, ← s1, ← s2]
    rw [add_assoc, e4, e1, e2, e3, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u _
    by_cases hux : u = x
    · have F1 : G.Adj v u ↔ v = zx := by
        rw [hux]
        constructor
        · intro h
          rcases hNx v h.symm with a | a
          · exact absurd a hvy
          · exact a
        · rintro rfl; exact hzx.symm
      have F2 : G1.Adj v u ↔ v = zx := by
        rw [hux, G1adj]
        constructor
        · rintro (h | h)
          · exact absurd rfl h.2.2.2.1
          · rw [Sym2.eq_iff] at h
            rcases h with ⟨a, _⟩ | ⟨a, _⟩
            · exact absurd a hvx
            · exact a
        · rintro rfl; exact Or.inr Sym2.eq_swap
      by_cases hv : v = zx
      · have hs : s(v, u) = s(x, zx) := by rw [hv, hux]; exact Sym2.eq_swap
        have a4 : ¬ (v = zy ∧ u = y) := fun h => hxne (hux.symm.trans h.2)
        rw [if_pos (F1.2 hv), if_pos (F2.2 hv), hs, h1a,
          if_pos (show v = zx ∧ u = x from ⟨hv, hux⟩),
          if_pos (show v = zx ∧ u = x from ⟨hv, hux⟩), if_neg a4]
        try omega
      · have a1 : ¬ G.Adj v u := fun h => hv (F1.1 h)
        have a2 : ¬ G1.Adj v u := fun h => hv (F2.1 h)
        have a3 : ¬ (v = zx ∧ u = x) := fun h => hv h.1
        have a4 : ¬ (v = zy ∧ u = y) := fun h => hxne (hux.symm.trans h.2)
        simp [a1, a2, a3, a4]
    by_cases huy : u = y
    · have F1 : G.Adj v u ↔ v = zy := by
        rw [huy]
        constructor
        · intro h
          rcases hNy v h.symm with a | a
          · exact absurd a hvx
          · exact a
        · rintro rfl; exact hzy.symm
      have F2 : ¬ G1.Adj v u := by
        rw [huy, G1adj]
        rintro (h | h)
        · exact absurd rfl h.2.2.2.2
        · rw [Sym2.eq_iff] at h
          rcases h with ⟨a, _⟩ | ⟨_, b⟩
          · exact hvx a
          · exact hxne b.symm
      have a3 : ¬ (v = zx ∧ u = x) := fun h => hux h.2
      by_cases hv : v = zy
      · have hs : s(v, u) = s(y, zy) := by rw [hv, huy]; exact Sym2.eq_swap
        rw [if_pos (F1.2 hv), if_neg F2, hs, h1b, if_neg a3, if_neg a3,
          if_pos (show v = zy ∧ u = y from ⟨hv, huy⟩)]
        try omega
      · have a1 : ¬ G.Adj v u := fun h => hv (F1.1 h)
        have a4 : ¬ (v = zy ∧ u = y) := fun h => hv h.1
        simp [a1, F2, a3, a4]
    · have hn := hne1 v u hvx hvy hux huy
      have F : G.Adj v u ↔ G1.Adj v u := by
        rw [G1adj]
        constructor
        · intro h; exact Or.inl ⟨h, hvx, hvy, hux, huy⟩
        · rintro (h | h)
          · exact h.1
          · exact absurd h hn.1
      have hw : ω1 s(v, u) = ωt s(v, u) := h1c _ hn.1 hn.2
      have hc1 : ¬ (v = zx ∧ u = x) := fun h => hux h.2
      have hc2 : ¬ (v = zy ∧ u = y) := fun h => huy h.2
      simp only [hc1, hc2, if_false, add_zero]
      by_cases h : G.Adj v u
      · rw [if_pos h, if_pos (F.1 h), hw]
      · rw [if_neg h, if_neg (fun h' => h (F.2 h'))]
  have hs1 : ∀ v, v ≠ x → v ≠ y → v ≠ zx → v ≠ zy → sdeg G ω1 v = sdeg G1 ωt v := by
    intro v h1 h2 h3 h4
    have := hstar v h1 h2
    rw [if_neg h3, if_neg h3, if_neg h4] at this
    omega
  have hao : ωt s(x, zx) % 2 = 1 := by
    rcases Nat.even_or_odd (ωt s(x, zx)) with h | h
    · exact absurd h hax
    · exact Nat.odd_iff.1 h
  have hmemv : ∀ w, w ≠ x → w ≠ y → w ∈ R ∪ insert x B := by
    intro w a b
    rcases hRB w a b with h | h <;> simp [h]
  have hev_zx : Even (sdeg G ω1 zx) := by
    have h := hstar zx hzxx hzxy
    have he : Even (sdeg G1 ωt zx) := (hpart zx (hmemv zx hzxx hzxy)).2 hzxR
    rw [Nat.even_iff] at he ⊢
    rw [if_pos rfl, if_pos rfl] at h
    by_cases hz : zx = zy
    · rw [if_pos hz] at h; omega
    · rw [if_neg hz] at h; omega
  have hev_zy : Even (sdeg G ω1 zy) := by
    have h := hstar zy hzyx hzyy
    have he : Even (sdeg G1 ωt zy) := (hpart zy (hmemv zy hzyx hzyy)).2 hzyR
    rw [Nat.even_iff] at he ⊢
    rw [if_pos rfl] at h
    by_cases hz : zy = zx
    · rw [if_pos hz, if_pos hz] at h
      rw [hz] at he ⊢; rw [hz] at h; omega
    · rw [if_neg hz, if_neg hz] at h; omega
  have hpar1 : ∀ w, w ≠ x → w ≠ y → (Even (sdeg G ω1 w) ↔ w ∈ R) := by
    intro w a b
    by_cases h1 : w = zx
    · subst h1; exact ⟨fun _ => hzxR, fun _ => hev_zx⟩
    by_cases h2 : w = zy
    · subst h2; exact ⟨fun _ => hzyR, fun _ => hev_zy⟩
    rw [hs1 w a b h1 h2]
    exact hpart w (hmemv w a b)
  obtain ⟨c, hc13, hc⟩ : ∃ c : ℕ, (c = 1 ∨ c = 3) ∧ (c = 3 ↔ sdeg G ω1 zx = 2) := by
    by_cases h : sdeg G ω1 zx = 2
    · exact ⟨3, Or.inr rfl, ⟨fun _ => h, fun _ => rfl⟩⟩
    · exact ⟨1, Or.inl rfl, ⟨fun h' => by omega, fun h' => absurd h' h⟩⟩
  obtain ⟨ω, hωxy, hωoff⟩ : ∃ ω : Sym2 V → ℕ, ω s(x, y) = c ∧ ∀ e, e ≠ s(x, y) → ω e = ω1 e :=
    ⟨fun e => if e = s(x, y) then c else ω1 e, by simp, by intro e h; simp [h]⟩
  have hn_xy : ∀ v u, v ≠ x → v ≠ y → s(v, u) ≠ s(x, y) := by
    intro v u h1 h2 h
    rw [Sym2.eq_iff] at h
    rcases h with ⟨a, _⟩ | ⟨a, _⟩
    · exact h1 a
    · exact h2 a
  have hωv : ∀ v, v ≠ x → v ≠ y → sdeg G ω v = sdeg G ω1 v := by
    intro v h1 h2
    unfold sdeg
    exact Finset.sum_congr rfl (fun u _ => hωoff _ (hn_xy v u h1 h2))
  have hω_xzx : ω s(x, zx) = 1 := by
    rw [hωoff _ (by
      intro h; rw [Sym2.congr_right] at h; exact hzxy h), h1a]
  have hω_yzy : ω s(y, zy) = 2 := by
    rw [hωoff _ (by
      intro h; rw [Sym2.eq_iff] at h
      rcases h with ⟨a, _⟩ | ⟨_, b⟩
      · exact hxne a.symm
      · exact hzyx b), h1b]
  have hsxG : sdeg G ω x = c + 1 := by
    have : sdeg G ω x = ∑ u, if G.Adj x u then ω s(x, u) else 0 := by
      unfold sdeg; rw [Finset.sum_filter]
    rw [this, Finset.sum_eq_add y zx hzxy.symm]
    · simp [hxy, hzx, hωxy, hω_xzx]
    · intro u _ hu
      by_cases h : G.Adj x u
      · rcases hNx u h with a | a
        · exact absurd a hu.1
        · exact absurd a hu.2
      · simp [h]
    · intro h; exact absurd (Finset.mem_univ _) h
    · intro h; exact absurd (Finset.mem_univ _) h
  have hsyG : sdeg G ω y = c + 2 := by
    have : sdeg G ω y = ∑ u, if G.Adj y u then ω s(y, u) else 0 := by
      unfold sdeg; rw [Finset.sum_filter]
    rw [this, Finset.sum_eq_add x zy hzyx.symm]
    · have : ω s(y, x) = c := by rw [Sym2.eq_swap]; exact hωxy
      simp [hxy.symm, hzy, this, hω_yzy]
    · intro u _ hu
      by_cases h : G.Adj y u
      · rcases hNy u h with a | a
        · exact absurd a hu.1
        · exact absurd a hu.2
      · simp [h]
    · intro h; exact absurd (Finset.mem_univ _) h
    · intro h; exact absurd (Finset.mem_univ _) h
  have hout : ∀ u v, G.Adj u v → s(u, v) ≠ s(x, y) → s(u, v) ≠ s(x, zx) →
      s(u, v) ≠ s(y, zy) → u ≠ x ∧ u ≠ y ∧ v ≠ x ∧ v ≠ y := by
    intro u v h h1 h2 h3
    refine ⟨?_, ?_, ?_, ?_⟩
    · rintro rfl
      rcases hNx v h with rfl | rfl
      · exact h1 rfl
      · exact h2 rfl
    · rintro rfl
      rcases hNy v h with rfl | rfl
      · exact h1 Sym2.eq_swap
      · exact h3 rfl
    · rintro rfl
      rcases hNx u h.symm with rfl | rfl
      · exact h1 Sym2.eq_swap
      · exact h2 Sym2.eq_swap
    · rintro rfl
      rcases hNy u h.symm with rfl | rfl
      · exact h1 rfl
      · exact h3 Sym2.eq_swap
  have hcx : sdeg G ω x ≠ sdeg G ω zx := by
    rw [hsxG, hωv zx hzxx hzxy]
    have := hc.1; have := hc.2
    rcases hc13 with h | h <;> omega
  have hcy : sdeg G ω y ≠ sdeg G ω zy := by
    rw [hsyG, hωv zy hzyx hzyy]
    have he := hev_zy
    rw [Nat.even_iff] at he
    rcases hc13 with h | h <;> omega
  have claim_x : ∀ v, G.Adj x v → sdeg G ω x ≠ sdeg G ω v := by
    intro v h
    rcases hNx v h with rfl | rfl
    · rw [hsxG, hsyG]; omega
    · exact hcx
  have claim_y : ∀ v, G.Adj y v → sdeg G ω y ≠ sdeg G ω v := by
    intro v h
    rcases hNy v h with rfl | rfl
    · rw [hsxG, hsyG]; omega
    · exact hcy
  refine ⟨ω, ?_, ?_⟩
  · intro e he
    induction e using Sym2.ind with
    | h u v =>
      have huv : G.Adj u v := (SimpleGraph.mem_edgeSet _).1 he
      by_cases h1 : s(u, v) = s(x, y)
      · rw [h1, hωxy]; rcases hc13 with h | h <;> omega
      · rw [hωoff _ h1]
        by_cases h2 : s(u, v) = s(x, zx)
        · rw [h2, h1a]; omega
        · by_cases h3 : s(u, v) = s(y, zy)
          · rw [h3, h1b]; omega
          · rw [h1c _ h2 h3]
            obtain ⟨a1, a2, a3, a4⟩ := hout u v huv h1 h2 h3
            exact hWt _ ((SimpleGraph.mem_edgeSet _).2 ((G1adj _ _).2 (Or.inl ⟨huv, a1, a2, a3, a4⟩)))
  · intro u v huv
    by_cases hux : u = x
    · subst hux; exact claim_x v huv
    by_cases hvx : v = x
    · subst hvx; exact (claim_x u huv.symm).symm
    by_cases huy : u = y
    · subst huy; exact claim_y v huv
    by_cases hvy : v = y
    · subst hvy; exact (claim_y u huv.symm).symm
    rw [hωv u hux huy, hωv v hvx hvy]
    by_cases hu : u ∈ R
    · by_cases hv : v ∈ R
      · exact absurd huv (hind u hu v hv)
      · intro heq
        exact hv ((hpar1 v hvx hvy).1 (heq ▸ (hpar1 u hux huy).2 hu))
    · by_cases hv : v ∈ R
      · intro heq
        exact hu ((hpar1 u hux huy).1 (heq ▸ (hpar1 v hvx hvy).2 hv))
      · have huB : u ∈ B := (hRB u hux huy).resolve_left hu
        have hvB : v ∈ B := (hRB v hvx hvy).resolve_left hv
        have hu1 : u ≠ zx := fun h => hu (h ▸ hzxR)
        have hu2 : u ≠ zy := fun h => hu (h ▸ hzyR)
        have hv1 : v ≠ zx := fun h => hv (h ▸ hzxR)
        have hv2 : v ≠ zy := fun h => hv (h ▸ hzyR)
        rw [hs1 u hux huy hu1 hu2, hs1 v hvx hvy hv1 hv2]
        exact hPt u v ((G1adj _ _).2 (Or.inl ⟨huv, hux, huy, hvx, hvy⟩))

theorem C_core_22 (G : SimpleGraph V) (x y zx zy : V) (hxy : G.Adj x y)
    (hdx : G.degree x = 2) (hdy : G.degree y = 2) (hzx : G.Adj x zx) (hzxy : zx ≠ y)
    (hzy : G.Adj y zy) (hzyx : zy ≠ x) (hc : (G.induce ({x, y}ᶜ : Set V)).Connected) :
    ∃ ω, Wt3 G ω ∧ Proper G ω := by
  have hxne : x ≠ y := G.ne_of_adj hxy
  have hzxx : zx ≠ x := (G.ne_of_adj hzx).symm
  have hzyy : zy ≠ y := (G.ne_of_adj hzy).symm
  have hzxS : zx ∈ ({x, y}ᶜ : Set V) := by simp [hzxx, hzxy]
  -- voisinages
  have hnb : ∀ (a b c : V), G.degree a = 2 → G.Adj a b → G.Adj a c → b ≠ c →
      ∀ u, G.Adj a u → u = b ∨ u = c := by
    intro a b c hd hb hc' hbc u hu
    by_contra hcon
    push Not at hcon
    have hsub : ({b, c, u} : Finset V) ⊆ G.neighborFinset a := by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl <;> simpa
    have h1 := Finset.card_le_card hsub
    rw [card_neighborFinset_eq_degree, hd] at h1
    have h2 : ({b, c, u} : Finset V).card = 3 := by
      rw [Finset.card_eq_three]; exact ⟨b, c, u, hbc, hcon.1.symm, hcon.2.symm, rfl⟩
    omega
  have hNx : ∀ u, G.Adj x u → u = y ∨ u = zx := hnb x y zx hdx hxy hzx hzxy.symm
  have hNy : ∀ u, G.Adj y u → u = x ∨ u = zy := hnb y x zy hdy hxy.symm hzy hzyx.symm
  obtain ⟨R, B, hdisj, hcov, hind, hzxR, hconn, -⟩ :=
    C_setup G x y zx zx hzxS hzxS hc Walk.nil (by simp) true
  have hzxR' : zx ∈ R := hzxR.2 rfl
  have hxn : x ∉ R ∧ x ∉ B := by
    have := (hcov x).not.2 (by simp)
    simpa using this
  have hyn : y ∉ R ∧ y ∉ B := by
    have := (hcov y).not.2 (by simp)
    simpa using this
  have hzyne : zy ≠ x ∧ zy ≠ y := ⟨hzyx, hzyy⟩
  have hu0 : zx ∈ R ∪ B := Finset.mem_union_left _ hzxR'
  have hRdisj : ∀ v, v ∈ R → v ∉ B := fun v h h' => Finset.disjoint_left.1 hdisj h h'
  rcases Nat.even_or_odd B.card with hev | hodd
  · rcases (hcov zy).2 hzyne with hzyR | hzyB
    · -- (a) |B| pair, zy ∈ R : x, y dans B
      have hxB : x ∉ insert y B := by simp [hxne, hxn.2]
      have hg : Good G R (insert x (insert y B)) :=
        { disj := by
            rw [Finset.disjoint_insert_right, Finset.disjoint_insert_right]
            exact ⟨hxn.1, hyn.1, hdisj⟩
          indep := hind
          conn := C_conn_ext G R B R (insert x (insert y B)) zx hu0 (Finset.Subset.refl _)
            (fun t ht => by simp [ht]) hconn (by
              intro w hw hwn
              simp only [Finset.mem_union, Finset.mem_insert] at hw hwn
              rcases hw with h | h | h | h
              · exact absurd (Or.inl h) hwn
              · subst h
                exact ⟨zx, hu0, (C_bip_adj _ _ _ _ _).2 ⟨hzx, Or.inr ⟨by simp, hzxR'⟩⟩⟩
              · subst h
                exact ⟨zy, Finset.mem_union_left _ hzyR,
                  (C_bip_adj _ _ _ _ _).2 ⟨hzy, Or.inr ⟨by simp, hzyR⟩⟩⟩
              · exact absurd (Or.inr h) hwn)
          even := by
            rw [Finset.card_insert_of_notMem hxB, Finset.card_insert_of_notMem hyn.2]
            obtain ⟨k, hk⟩ := hev
            exact ⟨k + 1, by omega⟩ }
      have hdom : ∀ u v, G.Adj u v → u ∈ R ∪ insert x (insert y B) ∧ v ∈ R ∪ insert x (insert y B) := by
        have hall : ∀ w, w ∈ R ∪ insert x (insert y B) := by
          intro w
          by_cases h1 : w = x
          · simp [h1]
          by_cases h2 : w = y
          · simp [h2]
          · rcases (hcov w).2 ⟨h1, h2⟩ with a | a <;> simp [a]
        exact fun u v _ => ⟨hall u, hall v⟩
      obtain ⟨ω, hW, hP, -⟩ := lemma7 G R _ hg hdom
      exact ⟨ω, hW, hP⟩
    · -- (b) |B| pair, zy ∈ B : y dans R, Lemme 8 avec v0 = x
      have hg : Good G (insert y R) B :=
        { disj := by
            rw [Finset.disjoint_insert_left]; exact ⟨hyn.2, hdisj⟩
          indep := by
            have hyR : ∀ u ∈ R, ¬ G.Adj y u := by
              intro u hu h
              rcases hNy u h with rfl | rfl
              · exact hxn.1 hu
              · exact hRdisj _ hu hzyB
            intro u hu v hv huv
            rw [Finset.mem_insert] at hu hv
            rcases hu with rfl | hu <;> rcases hv with rfl | hv
            · exact G.loopless.irrefl _ huv
            · exact hyR v hv huv
            · exact hyR u hu huv.symm
            · exact hind u hu v hv huv
          conn := C_conn_ext G R B (insert y R) B zx hu0 (Finset.subset_insert _ _)
            (Finset.Subset.refl _) hconn (by
              intro w hw hwn
              simp only [Finset.mem_union, Finset.mem_insert] at hw hwn
              rcases hw with (rfl | h) | h
              · exact ⟨zy, Finset.mem_union_right _ hzyB,
                  (C_bip_adj _ _ _ _ _).2 ⟨hzy, Or.inl ⟨by simp, hzyB⟩⟩⟩
              · exact absurd (Or.inl h) hwn
              · exact absurd (Or.inr h) hwn)
          even := hev }
      have hfilt : (insert y R).filter (G.Adj x) = {y, zx} := by
        ext u
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨_, h⟩
          exact hNx u h
        · rintro (rfl | rfl)
          · exact ⟨Or.inl rfl, hxy⟩
          · exact ⟨Or.inr hzxR', hzx⟩
      have hcard : ((insert y R).filter (G.Adj x)).card = 2 := by
        rw [hfilt, Finset.card_pair hzxy.symm]
      obtain ⟨ω, hW, hP⟩ := lemma8 G x (insert y R) B hg (by simp [hxn.1, hxn.2, hxne])
        (by
          intro u v _
          have hall : ∀ w, w ∈ insert y R ∪ B ∨ w = x := by
            intro w
            by_cases h1 : w = x
            · exact Or.inr h1
            by_cases h2 : w = y
            · left; simp [h2]
            · left
              rcases (hcov w).2 ⟨h1, h2⟩ with a | a <;> simp [a]
          exact ⟨hall u, hall v⟩)
        (by omega) (Or.inl (by rw [hcard]; decide))
      exact ⟨ω, hW, hP⟩
  · rcases (hcov zy).2 hzyne with hzyR | hzyB
    · exact C_case22_d G x y zx zy hxy hdx hdy hzx hzxy hzy hzyx R B hdisj hcov hind hzxR'
        hzyR hconn hodd
    · -- (c) |B| impair, zy ∈ B : x dans B, y dans R
      have hyR : ∀ u ∈ R, ¬ G.Adj y u := by
        intro u hu h
        rcases hNy u h with rfl | rfl
        · exact hxn.1 hu
        · exact hRdisj _ hu hzyB
      have hg : Good G (insert y R) (insert x B) :=
        { disj := by
            rw [Finset.disjoint_insert_left, Finset.disjoint_insert_right]
            exact ⟨by simp [hxne.symm, hyn.2], hxn.1, hdisj⟩
          indep := by
            intro u hu v hv huv
            rw [Finset.mem_insert] at hu hv
            rcases hu with rfl | hu <;> rcases hv with rfl | hv
            · exact G.loopless.irrefl _ huv
            · exact hyR v hv huv
            · exact hyR u hu huv.symm
            · exact hind u hu v hv huv
          conn := C_conn_ext G R B (insert y R) (insert x B) zx hu0 (Finset.subset_insert _ _)
            (Finset.subset_insert _ _) hconn (by
              intro w hw hwn
              simp only [Finset.mem_union, Finset.mem_insert] at hw hwn
              rcases hw with (rfl | h) | rfl | h
              · exact ⟨zy, Finset.mem_union_right _ hzyB,
                  (C_bip_adj _ _ _ _ _).2 ⟨hzy, Or.inl ⟨by simp, by simp [hzyB]⟩⟩⟩
              · exact absurd (Or.inl h) hwn
              · exact ⟨zx, hu0, (C_bip_adj _ _ _ _ _).2 ⟨hzx, Or.inr ⟨by simp, by simp [hzxR']⟩⟩⟩
              · exact absurd (Or.inr h) hwn)
          even := by
            rw [Finset.card_insert_of_notMem hxn.2]
            exact hodd.add_one }
      have hdom : ∀ u v, G.Adj u v → u ∈ insert y R ∪ insert x B ∧ v ∈ insert y R ∪ insert x B := by
        have hall : ∀ w, w ∈ insert y R ∪ insert x B := by
          intro w
          by_cases h1 : w = x
          · simp [h1]
          by_cases h2 : w = y
          · simp [h2]
          · rcases (hcov w).2 ⟨h1, h2⟩ with a | a <;> simp [a]
        exact fun u v _ => ⟨hall u, hall v⟩
      obtain ⟨ω, hW, hP, -⟩ := lemma7 G _ _ hg hdom
      exact ⟨ω, hW, hP⟩

-- INTERFACE (prouvé par les agents C13 / C14 ; C14 provisoire)

lemma C13_fin7 (G : SimpleGraph V) (R' B' : Finset V) (hg : Good G R' B')
    (hall : ∀ w, w ∈ R' ∪ B') : ∃ ω, Wt3 G ω ∧ Proper G ω := by
  obtain ⟨ω, hW, hP, -⟩ := lemma7 G R' B' hg (fun u v _ => ⟨hall u, hall v⟩)
  exact ⟨ω, hW, hP⟩

lemma C13_nb (G : SimpleGraph V) (R : Finset V) (x : V) (h : 1 ≤ (R.filter (G.Adj x)).card) :
    ∃ r ∈ R, G.Adj x r := by
  obtain ⟨r, hr⟩ := Finset.card_pos.1 h
  rw [Finset.mem_filter] at hr
  exact ⟨r, hr.1, hr.2⟩

def C13_aux (G : SimpleGraph V) (x y q : V) : SimpleGraph (Option V) where
  Adj a b := (∃ u v, a = some u ∧ b = some v ∧ G.Adj u v ∧ s(u, v) ≠ s(x, y) ∧ s(u, v) ≠ s(x, q)) ∨
    (a = none ∧ b = some y) ∨ (a = some y ∧ b = none)
  symm := ⟨fun a b h => by
    rcases h with ⟨u, v, rfl, rfl, h1, h2, h3⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨v, u, rfl, rfl, h1.symm, by rwa [Sym2.eq_swap], by rwa [Sym2.eq_swap]⟩
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
  loopless := ⟨fun a h => by
    rcases h with ⟨u, v, h1, h2, h3, -⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have : u = v := Option.some.inj (h1.symm.trans h2)
      exact G.loopless.irrefl _ (this ▸ h3)
    · simp [h1] at h2
    · simp [h1] at h2⟩

lemma C13_aux_ss (G : SimpleGraph V) (x y q u v : V) :
    (C13_aux G x y q).Adj (some u) (some v) ↔
      G.Adj u v ∧ s(u, v) ≠ s(x, y) ∧ s(u, v) ≠ s(x, q) := by
  show ((∃ a b, some u = some a ∧ some v = some b ∧ G.Adj a b ∧ s(a, b) ≠ s(x, y) ∧
    s(a, b) ≠ s(x, q)) ∨ _ ∨ _) ↔ _
  simp

lemma C13_mu {W : Type*} (S T : Finset W) (a : W) (h : a ∈ S ∨ a ∈ T) : a ∈ S ∪ T :=
  Finset.mem_union.2 h

lemma C13_aux_ns (G : SimpleGraph V) (x y q u : V) :
    (C13_aux G x y q).Adj none (some u) ↔ u = y := by
  show ((∃ a b, none = some a ∧ some u = some b ∧ G.Adj a b ∧ s(a, b) ≠ s(x, y) ∧
    s(a, b) ≠ s(x, q)) ∨ _ ∨ _) ↔ _
  simp [eq_comm]

lemma C13_aux_sn (G : SimpleGraph V) (x y q u : V) :
    (C13_aux G x y q).Adj (some u) none ↔ u = y := by
  rw [SimpleGraph.adj_comm, C13_aux_ns]

lemma C13_aux_nn (G : SimpleGraph V) (x y q : V) : ¬ (C13_aux G x y q).Adj none none :=
  (C13_aux G x y q).loopless.irrefl _

lemma C13_stage1 (G : SimpleGraph V) (x y zx : V) (hxy : G.Adj x y) (hzx : G.Adj x zx)
    (R B : Finset V) (hdisj : Disjoint R B) (hcov : ∀ v, (v ∈ R ∨ v ∈ B) ↔ (v ≠ x ∧ v ≠ y))
    (hind : ∀ u ∈ R, ∀ v ∈ R, ¬ G.Adj u v) (hzxB : zx ∈ B)
    (hconn : ∀ u ∈ R ∪ B, ∀ v ∈ R ∪ B, (bip G R B).Reachable u v) (hodd : Odd B.card)
    (q : V) (hxq : R.filter (G.Adj x) = {q}) (hyq : R.filter (G.Adj y) = {q}) :
    ∃ ω : Sym2 (Option V) → ℕ, Wt3 (C13_aux G x y q) ω ∧
      (∀ a b, (C13_aux G x y q).Adj a b →
        sdeg (C13_aux G x y q) ω a ≠ sdeg (C13_aux G x y q) ω b) ∧
      (∀ v, Even (sdeg (C13_aux G x y q) ω (some v)) ↔ (v = x ∨ v ∈ R)) ∧
      Even (sdeg (C13_aux G x y q) ω none) := by
  have hxne : x ≠ y := G.ne_of_adj hxy
  have hxn : x ∉ R ∧ x ∉ B := by
    have := (hcov x).not.2 (by simp)
    simpa using this
  have hyn : y ∉ R ∧ y ∉ B := by
    have := (hcov y).not.2 (by simp)
    simpa using this
  have hqR : q ∈ R := by
    have : q ∈ R.filter (G.Adj x) := by rw [hxq]; simp
    exact (Finset.mem_filter.1 this).1
  have hxq' : G.Adj x q := by
    have : q ∈ R.filter (G.Adj x) := by rw [hxq]; simp
    exact (Finset.mem_filter.1 this).2
  have hyq' : G.Adj y q := by
    have : q ∈ R.filter (G.Adj y) := by rw [hyq]; simp
    exact (Finset.mem_filter.1 this).2
  have hqB : q ∉ B := fun h => Finset.disjoint_left.1 hdisj hqR h
  have hzxne : zx ≠ y := fun h => hyn.2 (h ▸ hzxB)
  have hzxq : zx ≠ q := fun h => hqB (h ▸ hzxB)
  obtain ⟨Rt, hRs, hRn⟩ : ∃ Rt : Finset (Option V), (∀ u, some u ∈ Rt ↔ (u = x ∨ u ∈ R)) ∧
      none ∈ Rt :=
    ⟨insert none ((insert x R).map Function.Embedding.some), by intro u; simp, by simp⟩
  obtain ⟨Bt, hBs, hBn, hBc⟩ : ∃ Bt : Finset (Option V), (∀ u, some u ∈ Bt ↔ (u = y ∨ u ∈ B)) ∧
      none ∉ Bt ∧ Bt.card = B.card + 1 :=
    ⟨(insert y B).map Function.Embedding.some, by intro u; simp, by simp, by
      rw [Finset.card_map, Finset.card_insert_of_notMem hyn.2]⟩
  have hall : ∀ o, o ∈ Rt ∨ o ∈ Bt := by
    intro o
    cases o with
    | none => exact Or.inl hRn
    | some u =>
      by_cases h1 : u = x
      · exact Or.inl ((hRs u).2 (Or.inl h1))
      by_cases h2 : u = y
      · exact Or.inr ((hBs u).2 (Or.inl h2))
      rcases (hcov u).2 ⟨h1, h2⟩ with a | a
      · exact Or.inl ((hRs u).2 (Or.inr a))
      · exact Or.inr ((hBs u).2 (Or.inr a))
  have hmap : ∀ u v, (bip G R B).Adj u v →
      (bip (C13_aux G x y q) Rt Bt).Adj (some u) (some v) := by
    intro u v h
    rw [C_bip_adj] at h ⊢
    have hu : u ≠ x ∧ u ≠ y := (hcov u).1 (h.2.elim (fun a => Or.inl a.1) (fun a => Or.inr a.1))
    have hv : v ≠ x ∧ v ≠ y := (hcov v).1 (h.2.elim (fun a => Or.inr a.2) (fun a => Or.inl a.2))
    refine ⟨(C13_aux_ss G x y q u v).2 ⟨h.1, ?_, ?_⟩, ?_⟩
    · intro e; rw [Sym2.eq_iff] at e
      rcases e with ⟨e1, _⟩ | ⟨e1, _⟩
      · exact hu.1 e1
      · exact hu.2 e1
    · intro e; rw [Sym2.eq_iff] at e
      rcases e with ⟨e1, _⟩ | ⟨_, e2⟩
      · exact hu.1 e1
      · exact hv.1 (by rw [e2])
    · rcases h.2 with a | a
      · exact Or.inl ⟨(hRs u).2 (Or.inr a.1), (hBs v).2 (Or.inr a.2)⟩
      · exact Or.inr ⟨(hBs u).2 (Or.inr a.1), (hRs v).2 (Or.inr a.2)⟩
  let φ : bip G R B →g bip (C13_aux G x y q) Rt Bt := ⟨Option.some, fun {u v} h => hmap u v h⟩
  have hzxRB : zx ∈ R ∪ B := Finset.mem_union_right _ hzxB
  have hqRB : q ∈ R ∪ B := Finset.mem_union_left _ hqR
  have hreach : ∀ o, (bip (C13_aux G x y q) Rt Bt).Reachable o (some zx) := by
    have hq0 : (bip (C13_aux G x y q) Rt Bt).Reachable (some q) (some zx) :=
      SimpleGraph.Reachable.map φ (hconn q hqRB zx hzxRB)
    have hy0 : (bip (C13_aux G x y q) Rt Bt).Reachable (some y) (some zx) := by
      have hadj : (bip (C13_aux G x y q) Rt Bt).Adj (some y) (some q) := by
        rw [C_bip_adj]
        refine ⟨(C13_aux_ss G x y q y q).2 ⟨hyq', ?_, ?_⟩, Or.inr ⟨(hBs y).2 (Or.inl rfl),
          (hRs q).2 (Or.inr hqR)⟩⟩
        · intro e; rw [Sym2.eq_iff] at e
          rcases e with ⟨e1, _⟩ | ⟨_, e2⟩
          · exact hxne e1.symm
          · exact hxn.1 (e2 ▸ hqR)
        · intro e; rw [Sym2.eq_iff] at e
          rcases e with ⟨e1, _⟩ | ⟨e1, e2⟩
          · exact hxne e1.symm
          · exact hxne (e1 ▸ e2.symm ▸ rfl)
      exact hadj.reachable.trans hq0
    intro o
    cases o with
    | none =>
      have hadj : (bip (C13_aux G x y q) Rt Bt).Adj none (some y) := by
        rw [C_bip_adj]
        exact ⟨(C13_aux_ns G x y q y).2 rfl, Or.inl ⟨hRn, (hBs y).2 (Or.inl rfl)⟩⟩
      exact hadj.reachable.trans hy0
    | some u =>
      by_cases h1 : u = x
      · subst h1
        have hadj : (bip (C13_aux G u y q) Rt Bt).Adj (some u) (some zx) := by
          rw [C_bip_adj]
          refine ⟨(C13_aux_ss G u y q u zx).2 ⟨hzx, ?_, ?_⟩, Or.inl ⟨(hRs u).2 (Or.inl rfl),
            (hBs zx).2 (Or.inr hzxB)⟩⟩
          · intro e; rw [Sym2.eq_iff] at e
            rcases e with ⟨_, e2⟩ | ⟨e1, _⟩
            · exact hzxne e2
            · exact hxne e1
          · intro e; rw [Sym2.eq_iff] at e
            rcases e with ⟨_, e2⟩ | ⟨e1, e2⟩
            · exact hzxq e2
            · exact hzxq (e2.trans e1)
        exact hadj.reachable
      by_cases h2 : u = y
      · subst h2; exact hy0
      · rcases (hcov u).2 ⟨h1, h2⟩ with a | a
        · exact SimpleGraph.Reachable.map φ (hconn u (Finset.mem_union_left _ a) zx hzxRB)
        · exact SimpleGraph.Reachable.map φ (hconn u (Finset.mem_union_right _ a) zx hzxRB)
  have hg : Good (C13_aux G x y q) Rt Bt :=
    { disj := by
        rw [Finset.disjoint_left]
        intro o ho hb
        cases o with
        | none => exact hBn hb
        | some u =>
          rw [hRs] at ho; rw [hBs] at hb
          rcases ho with rfl | ho <;> rcases hb with rfl | hb
          · exact hxne rfl
          · exact hxn.2 hb
          · exact hyn.1 ho
          · exact Finset.disjoint_left.1 hdisj ho hb
      indep := by
        intro a ha b hb hab
        cases a with
        | none =>
          cases b with
          | none => exact C13_aux_nn G x y q hab
          | some v =>
            have := (C13_aux_ns G x y q v).1 hab
            subst this
            rcases (hRs v).1 hb with h | h
            · exact hxne h.symm
            · exact hyn.1 h
        | some u =>
          cases b with
          | none =>
            have := (C13_aux_sn G x y q u).1 hab
            subst this
            rcases (hRs u).1 ha with h | h
            · exact hxne h.symm
            · exact hyn.1 h
          | some v =>
            obtain ⟨h0, h1, h2⟩ := (C13_aux_ss G x y q u v).1 hab
            rcases (hRs u).1 ha with rfl | hu <;> rcases (hRs v).1 hb with rfl | hv
            · exact G.loopless.irrefl _ h0
            · have : v ∈ R.filter (G.Adj u) := by simp [hv, h0]
              rw [hxq] at this
              exact h2 (by rw [Finset.mem_singleton.1 this])
            · have : u ∈ R.filter (G.Adj v) := by simp [hu, h0.symm]
              rw [hxq] at this
              exact h2 (by rw [Finset.mem_singleton.1 this, Sym2.eq_swap])
            · exact hind u hu v hv h0
      conn := by
        intro a _ b _
        exact (hreach a).trans (hreach b).symm
      even := by rw [hBc]; exact hodd.add_one }
  obtain ⟨ω, hW, hP, hpar⟩ := lemma7 (C13_aux G x y q) Rt Bt hg (fun a b _ => ⟨C13_mu _ _ _ (hall a), C13_mu _ _ _ (hall b)⟩)
  refine ⟨ω, hW, hP, fun v => ?_, ?_⟩
  · rw [hpar (some v) (C13_mu _ _ _ (hall _)), hRs]
  · rw [hpar none (C13_mu _ _ _ (hall _))]; exact hRn

lemma C13_sym_ne {v u a b : V} (h : s(v, u) = s(a, b)) : v = a ∨ v = b := by
  rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, _⟩
  · exact Or.inl h1
  · exact Or.inr h1

lemma C13_sdeg_G (G : SimpleGraph V) (ω : Sym2 V → ℕ) (v : V) :
    sdeg G ω v = ∑ u, (if G.Adj v u then ω s(v, u) else 0) := by
  unfold sdeg; rw [Finset.sum_filter]

lemma C13_sdeg_some (G : SimpleGraph V) (x y q : V) (ω : Sym2 (Option V) → ℕ) (v : V) :
    sdeg (C13_aux G x y q) ω (some v) = (if v = y then ω s(some v, none) else 0) +
      ∑ u, (if (C13_aux G x y q).Adj (some v) (some u) then ω s(some v, some u) else 0) := by
  unfold sdeg; rw [Finset.sum_filter, Fintype.sum_option]
  simp only [C13_aux_sn]

lemma C13_sdeg_none (G : SimpleGraph V) (x y q : V) (ω : Sym2 (Option V) → ℕ) :
    sdeg (C13_aux G x y q) ω none = ω s(none, some y) := by
  unfold sdeg; rw [Finset.sum_filter, Fintype.sum_option]
  simp [C13_aux_nn, C13_aux_ns]

lemma C13_stage2 (G : SimpleGraph V) (x y q : V) (hxy : G.Adj x y) (hxq : G.Adj x q)
    (hyq : G.Adj y q) (hxne : x ≠ y) (hxqne : x ≠ q) (hyqne : y ≠ q)
    (ωt : Sym2 (Option V) → ℕ) (hW : Wt3 (C13_aux G x y q) ωt)
    (hnone : Even (sdeg (C13_aux G x y q) ωt none))
    (a c : ℕ) (ha1 : 1 ≤ a) (ha3 : a ≤ 3) (hc1 : 1 ≤ c) (hc3 : c ≤ 3)
    (hac : a + c = ωt s(some y, some q) + 2) :
    ∃ ω : Sym2 V → ℕ, Wt3 G ω ∧
      sdeg G ω x = sdeg (C13_aux G x y q) ωt (some x) + 2 * a ∧
      sdeg G ω q = sdeg (C13_aux G x y q) ωt (some q) + 2 ∧
      ∀ v, v ≠ x → v ≠ q → sdeg G ω v = sdeg (C13_aux G x y q) ωt (some v) := by
  have hAss := C13_aux_ss G x y q
  obtain ⟨ω, hω⟩ : ∃ ω : Sym2 V → ℕ, ∀ u v, ω s(u, v) =
      if (s(u, v) = s(x, y) ∨ s(u, v) = s(x, q)) then a
      else if s(u, v) = s(y, q) then c else ωt s(some u, some v) :=
    ⟨Sym2.lift ⟨fun u v => if (s(u, v) = s(x, y) ∨ s(u, v) = s(x, q)) then a
      else if s(u, v) = s(y, q) then c else ωt s(some u, some v), by
        intro u v
        show (if (s(u, v) = s(x, y) ∨ s(u, v) = s(x, q)) then a
          else if s(u, v) = s(y, q) then c else ωt s(some u, some v)) =
          (if (s(v, u) = s(x, y) ∨ s(v, u) = s(x, q)) then a
          else if s(v, u) = s(y, q) then c else ωt s(some v, some u))
        rw [Sym2.eq_swap (a := v) (b := u), Sym2.eq_swap (a := some v) (b := some u)]⟩,
      fun u v => rfl⟩
  have hne : ∀ {a b : V}, a ≠ b → b ≠ a := fun h => h.symm
  have hyz : ωt s(some y, none) = 2 := by
    have hadj : (C13_aux G x y q).Adj none (some y) := (C13_aux_ns G x y q y).2 rfl
    have h1 := hW s(none, some y) (by rw [SimpleGraph.mem_edgeSet]; exact hadj)
    rw [C13_sdeg_none, Nat.even_iff] at hnone
    rw [Sym2.eq_swap]
    omega
  have hpt : ∀ v u, (if G.Adj v u then ω s(v, u) else 0) +
        (if (s(v, u) = s(y, q) ∧ G.Adj v u) then ωt s(some y, some q) else 0) =
      (if (C13_aux G x y q).Adj (some v) (some u) then ωt s(some v, some u) else 0) +
        (if ((s(v, u) = s(x, y) ∨ s(v, u) = s(x, q)) ∧ G.Adj v u) then a else 0) +
        (if (s(v, u) = s(y, q) ∧ G.Adj v u) then c else 0) := by
    intro v u
    by_cases hadj : G.Adj v u
    · by_cases h1 : (s(v, u) = s(x, y) ∨ s(v, u) = s(x, q))
      · have hn2 : ¬ s(v, u) = s(y, q) := by
          rcases h1 with h | h <;> rw [h] <;>
            simp [Sym2.eq_iff, hxne, hxqne, hyqne, hxne.symm, hxqne.symm, hyqne.symm]
        have hna : ¬ (C13_aux G x y q).Adj (some v) (some u) := by
          rw [hAss]; rintro ⟨_, h2, h3⟩
          rcases h1 with h | h
          · exact h2 h
          · exact h3 h
        simp only [hω v u, h1, hn2, hna, hadj, if_true, if_false, true_and, and_true, false_and, and_false, or_false, false_or, or_true, true_or, and_self, add_zero, zero_add, ite_true, ite_false]
      · have haa : (C13_aux G x y q).Adj (some v) (some u) := by
          rw [hAss]; exact ⟨hadj, fun h => h1 (Or.inl h), fun h => h1 (Or.inr h)⟩
        by_cases h2 : s(v, u) = s(y, q)
        · have hvu : ωt s(some v, some u) = ωt s(some y, some q) := by
            rcases Sym2.eq_iff.mp h2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
            · rw [h3, h4]
            · rw [h3, h4, Sym2.eq_swap]
          rw [hω v u, if_pos hadj, if_neg h1, if_pos h2, if_pos haa, if_neg (show ¬ ((s(v, u) = s(x, y) ∨ s(v, u) = s(x, q)) ∧ G.Adj v u) from fun h => h1 h.1),
            if_pos (show s(v, u) = s(y, q) ∧ G.Adj v u from ⟨h2, hadj⟩),
            if_pos (show s(v, u) = s(y, q) ∧ G.Adj v u from ⟨h2, hadj⟩), hvu]
          omega
        · simp only [hω v u, h1, h2, haa, hadj, if_true, if_false, true_and, and_true, false_and, and_false, or_false, false_or, or_true, true_or, and_self, add_zero, zero_add, ite_true, ite_false]
    · have hna : ¬ (C13_aux G x y q).Adj (some v) (some u) := by
        rw [hAss]; exact fun h => hadj h.1
      simp [hadj, hna]
  have hsum : ∀ v, sdeg G ω v + ∑ u, (if (s(v, u) = s(y, q) ∧ G.Adj v u) then
        ωt s(some y, some q) else 0) =
      ∑ u, (if (C13_aux G x y q).Adj (some v) (some u) then ωt s(some v, some u) else 0) +
        ∑ u, (if ((s(v, u) = s(x, y) ∨ s(v, u) = s(x, q)) ∧ G.Adj v u) then a else 0) +
        ∑ u, (if (s(v, u) = s(y, q) ∧ G.Adj v u) then c else 0) := by
    intro v
    rw [C13_sdeg_G, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun u _ => hpt v u)
  have hA : ∀ v, sdeg (C13_aux G x y q) ωt (some v) = (if v = y then 2 else 0) +
      ∑ u, (if (C13_aux G x y q).Adj (some v) (some u) then ωt s(some v, some u) else 0) := by
    intro v; rw [C13_sdeg_some]
    by_cases h : v = y
    · subst h; simp [hyz]
    · simp [h]
  have hyxq : y ≠ x := hxne.symm
  have hqx : q ≠ x := hxqne.symm
  have hqy : q ≠ y := hyqne.symm
  have hWt3 : Wt3 G ω := by
    intro e he
    induction e using Sym2.ind with
    | _ u v =>
    rw [SimpleGraph.mem_edgeSet] at he
    rw [hω u v]
    by_cases h1 : (s(u, v) = s(x, y) ∨ s(u, v) = s(x, q))
    · rw [if_pos h1]; exact ⟨ha1, ha3⟩
    · rw [if_neg h1]
      by_cases h2 : s(u, v) = s(y, q)
      · rw [if_pos h2]; exact ⟨hc1, hc3⟩
      · rw [if_neg h2]
        exact hW _ (by
          rw [SimpleGraph.mem_edgeSet, hAss]
          exact ⟨he, fun h => h1 (Or.inl h), fun h => h1 (Or.inr h)⟩)
  -- sommes de correction
  have hc1x : ∑ u, (if ((s(x, u) = s(x, y) ∨ s(x, u) = s(x, q)) ∧ G.Adj x u) then a else 0) =
      a + a := by
    have : ∀ u, (if ((s(x, u) = s(x, y) ∨ s(x, u) = s(x, q)) ∧ G.Adj x u) then a else 0) =
        (if u = y then a else 0) + (if u = q then a else 0) := by
      intro u
      by_cases h1 : u = y
      · subst h1; simp [hxy, hxne, hxqne, hyqne, hyxq, hqx, hqy]
      · by_cases h2 : u = q
        · subst h2; simp [hxq, h1, hxne, hxqne, hyqne, hyxq, hqx, hqy]
        · simp [h1, h2, Sym2.eq_iff, hxne, hxqne, hyqne, hyxq, hqx, hqy]
    rw [Finset.sum_congr rfl (fun u _ => this u)]
    simp [Finset.sum_add_distrib]
  have hc1y : ∑ u, (if ((s(y, u) = s(x, y) ∨ s(y, u) = s(x, q)) ∧ G.Adj y u) then a else 0) = a := by
    have : ∀ u, (if ((s(y, u) = s(x, y) ∨ s(y, u) = s(x, q)) ∧ G.Adj y u) then a else 0) =
        (if u = x then a else 0) := by
      intro u
      by_cases h1 : u = x
      · subst h1; simp [hxy.symm, hxne, hxqne, hyqne, hyxq, Sym2.eq_swap]
      · simp [h1, Sym2.eq_iff, hxne, hxqne, hyqne, hyxq, hqy]
    rw [Finset.sum_congr rfl (fun u _ => this u)]
    simp
  have hc1q : ∑ u, (if ((s(q, u) = s(x, y) ∨ s(q, u) = s(x, q)) ∧ G.Adj q u) then a else 0) = a := by
    have : ∀ u, (if ((s(q, u) = s(x, y) ∨ s(q, u) = s(x, q)) ∧ G.Adj q u) then a else 0) =
        (if u = x then a else 0) := by
      intro u
      by_cases h1 : u = x
      · subst h1; simp [hxq.symm, hxne, hxqne, hyqne, hqx]
      · simp [h1, Sym2.eq_iff, hxne, hxqne, hyqne, hqx, hqy]
    rw [Finset.sum_congr rfl (fun u _ => this u)]
    simp
  have hc1o : ∀ v, v ≠ x → v ≠ y → v ≠ q →
      ∑ u, (if ((s(v, u) = s(x, y) ∨ s(v, u) = s(x, q)) ∧ G.Adj v u) then a else 0) = 0 := by
    intro v h1 h2 h3
    apply Finset.sum_eq_zero
    intro u _
    rw [if_neg]
    rintro ⟨h | h, _⟩ <;> rcases C13_sym_ne h with e | e <;> first | exact h1 e | exact h2 e | exact h3 e
  have hc2x : ∀ K : ℕ, ∑ u, (if (s(x, u) = s(y, q) ∧ G.Adj x u) then K else 0) = 0 := by
    intro K
    apply Finset.sum_eq_zero
    intro u _
    rw [if_neg]
    rintro ⟨h, _⟩; rcases C13_sym_ne h with e | e <;> first | exact hxne e | exact hxqne e
  have hc2o : ∀ v, v ≠ y → v ≠ q → ∀ K : ℕ,
      ∑ u, (if (s(v, u) = s(y, q) ∧ G.Adj v u) then K else 0) = 0 := by
    intro v h2 h3 K
    apply Finset.sum_eq_zero
    intro u _
    rw [if_neg]
    rintro ⟨h, _⟩; rcases C13_sym_ne h with e | e <;> first | exact h2 e | exact h3 e
  have hc2y : ∀ K : ℕ, ∑ u, (if (s(y, u) = s(y, q) ∧ G.Adj y u) then K else 0) = K := by
    intro K
    have : ∀ u, (if (s(y, u) = s(y, q) ∧ G.Adj y u) then K else 0) = (if u = q then K else 0) := by
      intro u
      by_cases h1 : u = q
      · subst h1; simp [hyq]
      · simp [h1, Sym2.eq_iff, hyqne, hyxq, hqy]
    rw [Finset.sum_congr rfl (fun u _ => this u)]
    simp
  have hc2q : ∀ K : ℕ, ∑ u, (if (s(q, u) = s(y, q) ∧ G.Adj q u) then K else 0) = K := by
    intro K
    have : ∀ u, (if (s(q, u) = s(y, q) ∧ G.Adj q u) then K else 0) = (if u = y then K else 0) := by
      intro u
      by_cases h1 : u = y
      · subst h1; simp [hyq.symm, Sym2.eq_swap]
      · simp [h1, Sym2.eq_iff, hyqne, hyxq, hqy]
    rw [Finset.sum_congr rfl (fun u _ => this u)]
    simp
  refine ⟨ω, hWt3, ?_, ?_, ?_⟩
  · have h := hsum x
    have h' := hA x
    rw [hc1x, hc2x, hc2x] at h
    rw [if_neg hxne] at h'
    omega
  · have h := hsum q
    have h' := hA q
    rw [hc1q, hc2q, hc2q] at h
    rw [if_neg hqy] at h'
    omega
  · intro v hvx hvq
    by_cases hvy : v = y
    · subst hvy
      have h := hsum v
      have h' := hA v
      rw [hc1y, hc2y, hc2y] at h
      rw [if_pos rfl] at h'
      omega
    · have h := hsum v
      have h' := hA v
      rw [hc1o v hvx hvy hvq, hc2o v hvy hvq, hc2o v hvy hvq] at h
      rw [if_neg hvy] at h'
      omega

lemma C13_proper (G : SimpleGraph V) (x y q : V) (R : Finset V)
    (hind : ∀ u ∈ R, ∀ v ∈ R, ¬ G.Adj u v) (hqR : q ∈ R) (hxR : x ∉ R)
    (hxq : R.filter (G.Adj x) = {q})
    (ωt : Sym2 (Option V) → ℕ)
    (hP : ∀ a b, (C13_aux G x y q).Adj a b →
      sdeg (C13_aux G x y q) ωt a ≠ sdeg (C13_aux G x y q) ωt b)
    (hpar : ∀ v, Even (sdeg (C13_aux G x y q) ωt (some v)) ↔ (v = x ∨ v ∈ R))
    (ω : Sym2 V → ℕ) (a : ℕ)
    (hx : sdeg G ω x = sdeg (C13_aux G x y q) ωt (some x) + 2 * a)
    (hq : sdeg G ω q = sdeg (C13_aux G x y q) ωt (some q) + 2)
    (hv : ∀ v, v ≠ x → v ≠ q → sdeg G ω v = sdeg (C13_aux G x y q) ωt (some v))
    (hxqd : sdeg G ω x ≠ sdeg G ω q) : Proper G ω := by
  have hxq' : x ≠ q := fun h => hxR (h ▸ hqR)
  have hpar' : ∀ w, Even (sdeg G ω w) ↔ (w = x ∨ w ∈ R) := by
    intro w
    by_cases h1 : w = x
    · subst h1
      rw [hx, Nat.even_add]; simp [(hpar w).2 (Or.inl rfl)]
    · by_cases h2 : w = q
      · subst h2
        rw [hq, Nat.even_add]
        have := (hpar w).2 (Or.inr hqR)
        simp [this, h1, hqR]
      · rw [hv w h1 h2]; exact hpar w
  intro u v huv heq
  have hp1 := hpar' u
  have hp2 := hpar' v
  rw [heq] at hp1
  by_cases hu : u = x ∨ u ∈ R
  · have hv' : v = x ∨ v ∈ R := hp2.1 (hp1.2 hu)
    rcases hu with rfl | hu <;> rcases hv' with rfl | hv'
    · exact G.loopless.irrefl _ huv
    · have : v ∈ R.filter (G.Adj u) := by simp [hv', huv]
      rw [hxq, Finset.mem_singleton] at this
      subst this; exact hxqd heq
    · have : u ∈ R.filter (G.Adj v) := by simp [hu, huv.symm]
      rw [hxq, Finset.mem_singleton] at this
      subst this; exact hxqd heq.symm
    · exact hind u hu v hv' huv
  · have hv' : ¬ (v = x ∨ v ∈ R) := fun h => hu (hp1.1 (hp2.2 h))
    push Not at hu hv'
    have huq : u ≠ q := fun h => hu.2 (h ▸ hqR)
    have hvq : v ≠ q := fun h => hv'.2 (h ▸ hqR)
    refine hP (some u) (some v) ((C13_aux_ss G x y q u v).2 ⟨huv, ?_, ?_⟩) ?_
    · intro e; rw [Sym2.eq_iff] at e
      rcases e with ⟨e1, _⟩ | ⟨_, e2⟩
      · exact hu.1 e1
      · exact hv'.1 e2
    · intro e; rw [Sym2.eq_iff] at e
      rcases e with ⟨e1, _⟩ | ⟨_, e2⟩
      · exact hu.1 e1
      · exact hv'.1 e2
    · rw [← hv u hu.1 huq, ← hv v hv'.1 hvq]; exact heq

theorem C13_case_C1 (G : SimpleGraph V) (x y zx : V) (hxy : G.Adj x y) (hzx : G.Adj x zx)
    (R B : Finset V) (hdisj : Disjoint R B) (hcov : ∀ v, (v ∈ R ∨ v ∈ B) ↔ (v ≠ x ∧ v ≠ y))
    (hind : ∀ u ∈ R, ∀ v ∈ R, ¬ G.Adj u v) (hzxB : zx ∈ B)
    (hconn : ∀ u ∈ R ∪ B, ∀ v ∈ R ∪ B, (bip G R B).Reachable u v) (hodd : Odd B.card)
    (q : V) (hxq : R.filter (G.Adj x) = {q}) (hyq : R.filter (G.Adj y) = {q}) :
    ∃ ω, Wt3 G ω ∧ Proper G ω := by
  have hxne : x ≠ y := G.ne_of_adj hxy
  have hqR : q ∈ R := by
    have : q ∈ R.filter (G.Adj x) := by rw [hxq]; simp
    exact (Finset.mem_filter.1 this).1
  have hxq' : G.Adj x q := by
    have : q ∈ R.filter (G.Adj x) := by rw [hxq]; simp
    exact (Finset.mem_filter.1 this).2
  have hyq' : G.Adj y q := by
    have : q ∈ R.filter (G.Adj y) := by rw [hyq]; simp
    exact (Finset.mem_filter.1 this).2
  have hxn : x ∉ R := fun h => ((hcov x).1 (Or.inl h)).1 rfl
  have hyn : y ∉ R := fun h => ((hcov y).1 (Or.inl h)).2 rfl
  have hxqne : x ≠ q := fun h => hxn (h ▸ hqR)
  have hyqne : y ≠ q := fun h => hyn (h ▸ hqR)
  obtain ⟨ωt, hW, hP, hpar, hnone⟩ := C13_stage1 G x y zx hxy hzx R B hdisj hcov hind hzxB hconn
    hodd q hxq hyq
  have hAyq : (C13_aux G x y q).Adj (some y) (some q) := by
    rw [C13_aux_ss]
    refine ⟨hyq', ?_, ?_⟩
    · intro e; rw [Sym2.eq_iff] at e
      rcases e with ⟨e1, _⟩ | ⟨_, e2⟩
      · exact hxne e1.symm
      · exact hxqne e2.symm
    · intro e; rw [Sym2.eq_iff] at e
      rcases e with ⟨e1, _⟩ | ⟨e1, e2⟩
      · exact hxne e1.symm
      · exact hyqne e1
  have hmu := hW s(some y, some q) (by rw [SimpleGraph.mem_edgeSet]; exact hAyq)
  have key : ∀ a c : ℕ, 1 ≤ a → a ≤ 3 → 1 ≤ c → c ≤ 3 → a + c = ωt s(some y, some q) + 2 →
      sdeg (C13_aux G x y q) ωt (some x) + 2 * a ≠ sdeg (C13_aux G x y q) ωt (some q) + 2 →
      ∃ ω, Wt3 G ω ∧ Proper G ω := by
    intro a c ha1 ha3 hc1 hc3 hac hne
    obtain ⟨ω, hW3, hx, hq, hv⟩ := C13_stage2 G x y q hxy hxq' hyq' hxne hxqne hyqne ωt hW hnone
      a c ha1 ha3 hc1 hc3 hac
    exact ⟨ω, hW3, C13_proper G x y q R hind hqR hxn hxq ωt hP hpar ω a hx hq hv
      (by rw [hx, hq]; exact hne)⟩
  by_cases hb : sdeg (C13_aux G x y q) ωt (some x) + 2 * 2 =
      sdeg (C13_aux G x y q) ωt (some q) + 2
  · by_cases h2 : ωt s(some y, some q) = 2
    · exact key 1 3 (le_refl _) (by norm_num) (by norm_num) (le_refl _) (by omega) (by omega)
    · exact key (ωt s(some y, some q)) 2 (by omega) (by omega) (by norm_num) (by norm_num)
        (by omega) (by omega)
  · exact key 2 (ωt s(some y, some q)) (by norm_num) (by norm_num) (by omega) (by omega)
      (by omega) hb

theorem C13b_walk_of_fun (H : SimpleGraph V) (f : ℕ → V) (n : ℕ)
    (hadj : ∀ i, i < n → H.Adj (f i) (f (i + 1))) :
    ∃ P : H.Walk (f 0) (f n), ∀ t ∈ P.support, ∃ i, i ≤ n ∧ t = f i := by
  induction n with
  | zero => exact ⟨Walk.nil, fun t ht => ⟨0, le_refl _, by simpa using ht⟩⟩
  | succ n ih =>
    obtain ⟨P, hP⟩ := ih (fun i hi => hadj i (by omega))
    refine ⟨P.concat (hadj n (by omega)), ?_⟩
    intro t ht
    rw [Walk.support_concat, List.mem_append] at ht
    rcases ht with h | h
    · obtain ⟨i, hi, rfl⟩ := hP t h
      exact ⟨i, by omega, rfl⟩
    · exact ⟨n + 1, le_refl _, by simpa using h⟩

theorem C13b_dich (H : SimpleGraph V) {a b c d : V} (p : H.Walk a b)
    (hc : c ∉ p.support) (hd : d ∉ p.support) (hcd : c ≠ d) (hbc : H.Reachable b c) :
    (∃ q : H.Walk b c, q.IsPath ∧ d ∉ q.support) ∨
    (∃ q : H.Walk a d, q.IsPath ∧ c ∉ q.support) := by
  by_cases h1 : ∃ q : H.Walk b c, q.IsPath ∧ d ∉ q.support
  · exact Or.inl h1
  right
  obtain ⟨q0⟩ := hbc
  set Q : H.Walk b c := q0.bypass
  have hQ : Q.IsPath := q0.bypass_isPath
  have hdQ : d ∈ Q.support := by
    by_contra h; exact h1 ⟨Q, hQ, h⟩
  have hpre : c ∉ (Q.takeUntil d hdQ).support := by
    intro hm
    have hspec := congrArg Walk.support (Q.take_spec hdQ)
    rw [Walk.support_append] at hspec
    have hnd : Q.support.Nodup := hQ.support_nodup
    rw [← hspec] at hnd
    have hm2 : c ∈ (Q.dropUntil d hdQ).support.tail :=
      Walk.end_mem_tail_support_of_ne hcd.symm _
    exact (List.nodup_append.1 hnd).2.2 c hm c hm2 rfl
  let W : H.Walk a d := p.append (Q.takeUntil d hdQ)
  have hWc : c ∉ W.support := by
    simp only [W, Walk.support_append, List.mem_append]
    rintro (h | h)
    · exact hc h
    · exact hpre (List.mem_of_mem_tail h)
  exact ⟨W.bypass, W.bypass_isPath, fun h => hWc (W.support_bypass_subset_support h)⟩

theorem C13b_supp (G : SimpleGraph V) (R B : Finset V) {u v : V} (w : (bip G R B).Walk u v)
    (hu : u ∈ R ∪ B) : ∀ t ∈ w.support, t ∈ R ∪ B := by
  induction w with
  | nil => intro t ht; simpa [← List.mem_singleton.1 (by simpa using ht)] using hu
  | cons h w ih =>
    rename_i a a' c
    intro t ht
    rw [Walk.support_cons, List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact hu
    · apply ih _ t ht
      have := ((C_bip_adj _ _ _ _ _).1 h).2
      rcases this with ⟨_, h2⟩ | ⟨_, h2⟩
      · exact Finset.mem_union_right _ h2
      · exact Finset.mem_union_left _ h2

theorem C13b_apply9 (G : SimpleGraph V) (v0 w a b u0 : V) (R B : Finset V)
    (hvw : G.Adj v0 w) (hv0 : v0 ∉ R ∪ B) (hw : w ∉ R ∪ B)
    (hcov : ∀ t, t ∈ R ∨ t ∈ B ∨ t = v0 ∨ t = w)
    (hdisj : Disjoint R B) (hind : ∀ u ∈ R, ∀ v ∈ R, ¬ G.Adj u v)
    (hconn : ∀ u ∈ R ∪ B, ∀ v ∈ R ∪ B, (bip G R B).Reachable u v)
    (hodd : Odd B.card) (hN : R.filter (G.Adj v0) = {u0})
    (haB : a ∈ B) (hva : G.Adj v0 a) (hbR : b ∈ R) (hwb : G.Adj w b)
    (q : (bip G R B).Walk a b) (hq : q.IsPath) (hu0 : u0 ∉ q.support) :
    ∃ ω, Wt3 G ω ∧ Proper G ω := by
  have hwR : w ∉ R := fun h => hw (Finset.mem_union_left _ h)
  have hwB : w ∉ B := fun h => hw (Finset.mem_union_right _ h)
  have hu0R : u0 ∈ R := by
    have : u0 ∈ R.filter (G.Adj v0) := by rw [hN]; simp
    exact (Finset.mem_filter.1 this).1
  have hab : a ≠ b := fun h => Finset.disjoint_left.1 hdisj hbR (h ▸ haB)
  have hlen : 1 ≤ q.length := by
    rcases Nat.eq_zero_or_pos q.length with h | h
    · exact absurd (Walk.eq_of_length_eq_zero h) hab
    · exact h
  have hg : Good G R (insert w B) :=
    { disj := by rw [Finset.disjoint_insert_right]; exact ⟨hwR, hdisj⟩
      indep := hind
      conn := C_conn_ext G R B R (insert w B) b (Finset.mem_union_left _ hbR)
        (Finset.Subset.refl _) (Finset.subset_insert _ _) hconn (by
          intro t ht htn
          simp only [Finset.mem_union, Finset.mem_insert] at ht htn
          rcases ht with h | rfl | h
          · exact absurd (Or.inl h) htn
          · exact ⟨b, Finset.mem_union_left _ hbR, (C_bip_adj _ _ _ _ _).2
              ⟨hwb, Or.inr ⟨by simp, hbR⟩⟩⟩
          · exact absurd (Or.inr h) htn)
      even := by
        rw [Finset.card_insert_of_notMem hwB]
        exact hodd.add_one }
  have hnotw : ∀ t ∈ q.support, t ≠ w := fun t ht h =>
    hw (h ▸ C13b_supp G R B q (Finset.mem_union_right _ haB) t ht)
  have hmono : bip G R B ≤ bip G R (insert w B) := by
    intro u v h
    have h' := (C_bip_adj _ _ _ _ _).1 h
    exact (C_bip_adj _ _ _ _ _).2 ⟨h'.1, h'.2.imp (fun a => ⟨a.1, Finset.mem_insert_of_mem a.2⟩)
      (fun a => ⟨Finset.mem_insert_of_mem a.1, a.2⟩)⟩
  have hvw' : v0 ≠ w := G.ne_of_adj hvw
  refine lemma9 G v0 u0 R (insert w B) hg ?_ ?_ hN (q.length + 2) (by omega)
    (fun i => if i ≤ q.length then q.getVert i else w) ?_ ?_ ?_ ?_ ?_
  · intro h
    rcases Finset.mem_union.1 h with h | h
    · exact hv0 (Finset.mem_union_left _ h)
    · rcases Finset.mem_insert.1 h with h | h
      · exact hvw' h
      · exact hv0 (Finset.mem_union_right _ h)
  · intro u v _
    have hall : ∀ t, t ∈ R ∪ insert w B ∨ t = v0 := by
      intro t
      rcases hcov t with h | h | h | h
      · left; exact Finset.mem_union_left _ h
      · left; exact Finset.mem_union_right _ (Finset.mem_insert_of_mem h)
      · right; exact h
      · left; exact Finset.mem_union_right _ (by simp [h])
    exact ⟨hall u, hall v⟩
  · intro i hi j hj hij
    simp only [Set.mem_Iio] at hi hj
    simp only at hij
    by_cases hi' : i ≤ q.length <;> by_cases hj' : j ≤ q.length
    · rw [if_pos hi', if_pos hj'] at hij
      exact hq.getVert_injOn hi' hj' hij
    · rw [if_pos hi', if_neg hj'] at hij
      exact absurd hij (hnotw _ (Walk.getVert_mem_support q i))
    · rw [if_neg hi', if_pos hj'] at hij
      exact absurd hij.symm (hnotw _ (Walk.getVert_mem_support q j))
    · omega
  · intro i hi
    show (bip G R (insert w B)).Adj (if i ≤ q.length then q.getVert i else w)
      (if i + 1 ≤ q.length then q.getVert (i + 1) else w)
    rw [if_pos (by omega)]
    by_cases h1 : i + 1 ≤ q.length
    · rw [if_pos h1]
      exact hmono (q.adj_getVert_succ (by omega))
    · rw [if_neg h1]
      have : i = q.length := by omega
      rw [this, Walk.getVert_length]
      exact (C_bip_adj _ _ _ _ _).2 ⟨hwb.symm, Or.inl ⟨hbR, Finset.mem_insert_self _ _⟩⟩
  · show (if 0 ≤ q.length then q.getVert 0 else w) ∈ insert w B ∧
      G.Adj v0 (if 0 ≤ q.length then q.getVert 0 else w)
    rw [if_pos (Nat.zero_le _), Walk.getVert_zero]
    exact ⟨Finset.mem_insert_of_mem haB, hva⟩
  · show (if q.length + 2 - 1 ≤ q.length then q.getVert (q.length + 2 - 1) else w) ∈ insert w B ∧
      G.Adj v0 (if q.length + 2 - 1 ≤ q.length then q.getVert (q.length + 2 - 1) else w)
    rw [if_neg (by omega)]
    exact ⟨Finset.mem_insert_self _ _, hvw⟩
  · intro i hi
    show (if i ≤ q.length then q.getVert i else w) ≠ u0
    by_cases h1 : i ≤ q.length
    · rw [if_pos h1]
      intro h
      exact hu0 (h ▸ Walk.getVert_mem_support q i)
    · rw [if_neg h1]
      intro h
      exact hwR (h ▸ hu0R)

theorem C13b_main (G : SimpleGraph V) (x y zx zy r1 r2 : V) (R B : Finset V)
    (hxy : G.Adj x y) (hdisj : Disjoint R B)
    (hcov : ∀ v, (v ∈ R ∨ v ∈ B) ↔ (v ≠ x ∧ v ≠ y))
    (hind : ∀ u ∈ R, ∀ v ∈ R, ¬ G.Adj u v)
    (hconn : ∀ u ∈ R ∪ B, ∀ v ∈ R ∪ B, (bip G R B).Reachable u v)
    (hodd : Odd B.card)
    (hr1R : r1 ∈ R) (hxr1 : G.Adj x r1) (hNx : R.filter (G.Adj x) = {r1})
    (hr2R : r2 ∈ R) (hyr2 : G.Adj y r2) (hNy : R.filter (G.Adj y) = {r2}) (hr12 : r1 ≠ r2)
    (hzxB : zx ∈ B) (hxzx : G.Adj x zx) (hzyB : zy ∈ B) (hyzy : G.Adj y zy)
    (n : ℕ) (f : ℕ → V) (hf0 : f 0 = zx) (hfn : f n = zy)
    (hadj : ∀ i, i < n → (bip G R B).Adj (f i) (f (i + 1)))
    (hfr : ∀ i, i ≤ n → f i ≠ r1 ∧ f i ≠ r2) :
    ∃ ω, Wt3 G ω ∧ Proper G ω := by
  obtain ⟨P, hP⟩ := C13b_walk_of_fun (bip G R B) f n hadj
  let P' : (bip G R B).Walk zx zy := P.copy hf0 hfn
  have hP' : ∀ t ∈ P'.support, ∃ i, i ≤ n ∧ t = f i := by
    intro t ht
    exact hP t (by simpa [P', Walk.support_copy] using ht)
  have hx0 : x ∉ R ∪ B := fun h => ((hcov x).1 (Finset.mem_union.1 h)).1 rfl
  have hy0 : y ∉ R ∪ B := fun h => ((hcov y).1 (Finset.mem_union.1 h)).2 rfl
  have hc1 : r1 ∉ P'.support := by
    intro h
    obtain ⟨i, hi, hi'⟩ := hP' _ h
    exact (hfr i hi).1 hi'.symm
  have hc2 : r2 ∉ P'.support := by
    intro h
    obtain ⟨i, hi, hi'⟩ := hP' _ h
    exact (hfr i hi).2 hi'.symm
  have hbc : (bip G R B).Reachable zy r1 :=
    hconn zy (Finset.mem_union_right _ hzyB) r1 (Finset.mem_union_left _ hr1R)
  have hcov1 : ∀ t, t ∈ R ∨ t ∈ B ∨ t = y ∨ t = x := by
    intro t
    by_cases h1 : t = x
    · exact Or.inr (Or.inr (Or.inr h1))
    by_cases h2 : t = y
    · exact Or.inr (Or.inr (Or.inl h2))
    · exact ((hcov t).2 ⟨h1, h2⟩).imp id Or.inl
  have hcov2 : ∀ t, t ∈ R ∨ t ∈ B ∨ t = x ∨ t = y := by
    intro t
    rcases hcov1 t with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inr (Or.inr (Or.inl h))
  rcases C13b_dich (bip G R B) P' hc1 hc2 hr12 hbc with ⟨q, hq, hd⟩ | ⟨q, hq, hd⟩
  · exact C13b_apply9 G y x zy r1 r2 R B hxy.symm hy0 hx0 hcov1 hdisj hind hconn hodd hNy
      hzyB hyzy hr1R hxr1 q hq hd
  · exact C13b_apply9 G x y zx r2 r1 R B hxy hx0 hy0 hcov2 hdisj hind hconn hodd hNx
      hzxB hxzx hr2R hyr2 q hq hd

theorem C13_case_C2b (G : SimpleGraph V) (x y zx zy : V) (hxy : G.Adj x y)
    (hzx : G.Adj x zx) (hzxy : zx ≠ y) (hzy : G.Adj y zy) (hzyx : zy ≠ x)
    (hzxS : zx ∈ ({x, y}ᶜ : Set V)) (hzyS : zy ∈ ({x, y}ᶜ : Set V))
    (p : (G.induce ({x, y}ᶜ : Set V)).Walk ⟨zx, hzxS⟩ ⟨zy, hzyS⟩)
    (hp : p.length = (G.induce ({x, y}ᶜ : Set V)).dist ⟨zx, hzxS⟩ ⟨zy, hzyS⟩)
    (hch : zx = zy ∨ (¬ G.Adj x zy ∧ ¬ G.Adj y zx ∧ ∀ i, 0 < i → i < p.length →
      ¬ G.Adj x (p.getVert i).1 ∧ ¬ G.Adj y (p.getVert i).1))
    (R B : Finset V) (hdisj : Disjoint R B) (hcov : ∀ v, (v ∈ R ∨ v ∈ B) ↔ (v ≠ x ∧ v ≠ y))
    (hind : ∀ u ∈ R, ∀ v ∈ R, ¬ G.Adj u v) (hzxR : zx ∉ R)
    (hconn : ∀ u ∈ R ∪ B, ∀ v ∈ R ∪ B, (bip G R B).Reachable u v)
    (hpath : ∀ i, i < p.length → (bip G R B).Adj (p.getVert i).1 (p.getVert (i + 1)).1)
    (hodd : Odd B.card) (r1 s1 : V) (hr1 : R.filter (G.Adj x) = {r1})
    (hs1 : R.filter (G.Adj y) = {s1}) (hcom : ¬ ∃ q ∈ R, G.Adj x q ∧ G.Adj y q)
    (hzyR : zy ∉ R) :
    ∃ ω, Wt3 G ω ∧ Proper G ω := by
  have hr1m : r1 ∈ R.filter (G.Adj x) := by rw [hr1]; simp
  have hs1m : s1 ∈ R.filter (G.Adj y) := by rw [hs1]; simp
  obtain ⟨hr1R, hxr1⟩ := Finset.mem_filter.1 hr1m
  obtain ⟨hs1R, hys1⟩ := Finset.mem_filter.1 hs1m
  have hrs : r1 ≠ s1 := by
    intro h
    exact hcom ⟨r1, hr1R, hxr1, h ▸ hys1⟩
  have hzxB : zx ∈ B := by
    rcases (hcov zx).2 ⟨(G.ne_of_adj hzx).symm, hzxy⟩ with h | h
    · exact absurd h hzxR
    · exact h
  have hzyB : zy ∈ B := by
    rcases (hcov zy).2 ⟨hzyx, (G.ne_of_adj hzy).symm⟩ with h | h
    · exact absurd h hzyR
    · exact h
  have hBR : ∀ t, t ∈ B → t ∈ R → False := fun t h1 h2 => Finset.disjoint_left.1 hdisj h2 h1
  refine C13b_main G x y zx zy r1 s1 R B hxy hdisj hcov hind hconn hodd hr1R hxr1 hr1 hs1R hys1
    hs1 hrs hzxB hzx hzyB hzy p.length (fun i => (p.getVert i).1) ?_ ?_ hpath ?_
  · simp
  · simp
  · intro i hi
    by_cases h0 : i = 0
    · subst h0
      simp only [Walk.getVert_zero]
      exact ⟨fun h => hBR _ hzxB (h ▸ hr1R), fun h => hBR _ hzxB (h ▸ hs1R)⟩
    by_cases hn : i = p.length
    · subst hn
      simp only [Walk.getVert_length]
      exact ⟨fun h => hBR _ hzyB (h ▸ hr1R), fun h => hBR _ hzyB (h ▸ hs1R)⟩
    rcases hch with h | ⟨_, _, h⟩
    · subst h
      have h00 : p.length = 0 := by rw [hp]; exact SimpleGraph.dist_self
      omega
    · have := h i (by omega) (by omega)
      exact ⟨fun h' => this.1 (h' ▸ hxr1), fun h' => this.2 (h' ▸ hys1)⟩

theorem C_core_13 (G : SimpleGraph V) (x y zx zy : V) (hxy : G.Adj x y)
    (hdx : 2 < G.degree x) (hdy : 2 ≤ G.degree y)
    (hzx : G.Adj x zx) (hzxy : zx ≠ y) (hzy : G.Adj y zy) (hzyx : zy ≠ x)
    (hc : (G.induce ({x, y}ᶜ : Set V)).Connected)
    (hzxS : zx ∈ ({x, y}ᶜ : Set V)) (hzyS : zy ∈ ({x, y}ᶜ : Set V))
    (p : (G.induce ({x, y}ᶜ : Set V)).Walk ⟨zx, hzxS⟩ ⟨zy, hzyS⟩)
    (hp : p.length = (G.induce ({x, y}ᶜ : Set V)).dist ⟨zx, hzxS⟩ ⟨zy, hzyS⟩)
    (hch : zx = zy ∨ (¬ G.Adj x zy ∧ ¬ G.Adj y zx ∧ ∀ i, 0 < i → i < p.length →
      ¬ G.Adj x (p.getVert i).1 ∧ ¬ G.Adj y (p.getVert i).1))
    (R B : Finset V) (hdisj : Disjoint R B) (hcov : ∀ v, (v ∈ R ∨ v ∈ B) ↔ (v ≠ x ∧ v ≠ y))
    (hind : ∀ u ∈ R, ∀ v ∈ R, ¬ G.Adj u v) (hzxR : zx ∉ R)
    (hconn : ∀ u ∈ R ∪ B, ∀ v ∈ R ∪ B, (bip G R B).Reachable u v)
    (hpath : ∀ i, i < p.length → (bip G R B).Adj (p.getVert i).1 (p.getVert (i + 1)).1)
    (hodd : Odd B.card) :
    ∃ ω, Wt3 G ω ∧ Proper G ω := by
  have hxne : x ≠ y := G.ne_of_adj hxy
  have hxn : x ∉ R ∧ x ∉ B := by
    have := (hcov x).not.2 (by simp)
    simpa using this
  have hyn : y ∉ R ∧ y ∉ B := by
    have := (hcov y).not.2 (by simp)
    simpa using this
  have hzxB : zx ∈ B := by
    rcases (hcov zx).2 ⟨(G.ne_of_adj hzx).symm, hzxy⟩ with h | h
    · exact absurd h hzxR
    · exact h
  have hu0 : zx ∈ R ∪ B := Finset.mem_union_right _ hzxB
  have hall0 : ∀ w, w = x ∨ w = y ∨ w ∈ R ∨ w ∈ B := by
    intro w
    by_cases h1 : w = x
    · exact Or.inl h1
    by_cases h2 : w = y
    · exact Or.inr (Or.inl h2)
    · rcases (hcov w).2 ⟨h1, h2⟩ with a | a
      · exact Or.inr (Or.inr (Or.inl a))
      · exact Or.inr (Or.inr (Or.inr a))
  by_cases h0x : (R.filter (G.Adj x)).card = 0
  · -- (A1) degR(x) = 0 : x dans R, y dans B
    have hRx : ∀ r ∈ R, ¬ G.Adj x r := by
      intro r hr h
      have hm : r ∈ R.filter (G.Adj x) := by simp [hr, h]
      have := Finset.card_pos.2 ⟨r, hm⟩
      omega
    have hg : Good G (insert x R) (insert y B) :=
      { disj := by
          rw [Finset.disjoint_insert_left, Finset.disjoint_insert_right]
          exact ⟨by simp [hxne, hxn.2], hyn.1, hdisj⟩
        indep := by
          intro u hu v hv huv
          rw [Finset.mem_insert] at hu hv
          rcases hu with rfl | hu <;> rcases hv with rfl | hv
          · exact G.loopless.irrefl _ huv
          · exact hRx v hv huv
          · exact hRx u hu huv.symm
          · exact hind u hu v hv huv
        conn := by
          have s1 := C_conn_ext G R B (insert x R) B zx hu0 (Finset.subset_insert _ _)
            (Finset.Subset.refl _) hconn (by
              intro w hw hwn
              simp only [Finset.mem_union, Finset.mem_insert] at hw hwn
              rcases hw with (rfl | h) | h
              · exact ⟨zx, hu0, (C_bip_adj _ _ _ _ _).2 ⟨hzx, Or.inl ⟨by simp, hzxB⟩⟩⟩
              · exact absurd (Or.inl h) hwn
              · exact absurd (Or.inr h) hwn)
          refine C_conn_ext G (insert x R) B (insert x R) (insert y B) zx
            (Finset.mem_union_right _ hzxB) (Finset.Subset.refl _) (Finset.subset_insert _ _) s1 ?_
          intro w hw hwn
          simp only [Finset.mem_union, Finset.mem_insert] at hw hwn
          rcases hw with (h | h) | rfl | h
          · exact absurd (Or.inl (Or.inl h)) hwn
          · exact absurd (Or.inl (Or.inr h)) hwn
          · exact ⟨x, by simp, (C_bip_adj _ _ _ _ _).2 ⟨hxy.symm, Or.inr ⟨by simp, by simp⟩⟩⟩
          · exact absurd (Or.inr h) hwn
        even := by
          rw [Finset.card_insert_of_notMem hyn.2]; exact hodd.add_one }
    refine C13_fin7 G _ _ hg ?_
    intro w
    rcases hall0 w with h | h | h | h <;> simp [h]
  by_cases h0y : (R.filter (G.Adj y)).card = 0
  · -- (A2) degR(y) = 0, degR(x) ≠ 0 : y dans R, x dans B
    have hRy : ∀ r ∈ R, ¬ G.Adj y r := by
      intro r hr h
      have hm : r ∈ R.filter (G.Adj y) := by simp [hr, h]
      have := Finset.card_pos.2 ⟨r, hm⟩
      omega
    obtain ⟨r0, hr0, hxr0⟩ := C13_nb G R x (by omega)
    have hg : Good G (insert y R) (insert x B) :=
      { disj := by
          rw [Finset.disjoint_insert_left, Finset.disjoint_insert_right]
          exact ⟨by simp [hxne.symm, hyn.2], hxn.1, hdisj⟩
        indep := by
          intro u hu v hv huv
          rw [Finset.mem_insert] at hu hv
          rcases hu with rfl | hu <;> rcases hv with rfl | hv
          · exact G.loopless.irrefl _ huv
          · exact hRy v hv huv
          · exact hRy u hu huv.symm
          · exact hind u hu v hv huv
        conn := by
          have s1 := C_conn_ext G R B R (insert x B) zx hu0 (Finset.Subset.refl _)
            (Finset.subset_insert _ _) hconn (by
              intro w hw hwn
              simp only [Finset.mem_union, Finset.mem_insert] at hw hwn
              rcases hw with h | rfl | h
              · exact absurd (Or.inl h) hwn
              · exact ⟨r0, Finset.mem_union_left _ hr0,
                  (C_bip_adj _ _ _ _ _).2 ⟨hxr0, Or.inr ⟨by simp, hr0⟩⟩⟩
              · exact absurd (Or.inr h) hwn)
          refine C_conn_ext G R (insert x B) (insert y R) (insert x B) zx
            (Finset.mem_union_right _ (Finset.mem_insert_of_mem hzxB)) (Finset.subset_insert _ _)
            (Finset.Subset.refl _) (by
              intro u hu v hv
              exact s1 u (by simpa using hu) v (by simpa using hv)) ?_
          intro w hw hwn
          simp only [Finset.mem_union, Finset.mem_insert] at hw hwn
          rcases hw with (rfl | h) | h
          · exact ⟨x, by simp, (C_bip_adj _ _ _ _ _).2 ⟨hxy.symm, Or.inl ⟨by simp, by simp⟩⟩⟩
          · exact absurd (Or.inl h) hwn
          · exact absurd (Or.inr h) hwn
        even := by
          rw [Finset.card_insert_of_notMem hxn.2]; exact hodd.add_one }
    refine C13_fin7 G _ _ hg ?_
    intro w
    rcases hall0 w with h | h | h | h <;> simp [h]
  obtain ⟨r0, hr0, hxr0⟩ := C13_nb G R x (by omega)
  obtain ⟨s0, hs0, hys0⟩ := C13_nb G R y (by omega)
  have hmono : ∀ a b, (bip G R B).Adj a b → (bip G R (insert y B)).Adj a b := fun a b h => by
    rw [C_bip_adj] at h ⊢
    exact ⟨h.1, h.2.imp (fun t => ⟨t.1, Finset.mem_insert_of_mem t.2⟩)
      (fun t => ⟨Finset.mem_insert_of_mem t.1, t.2⟩)⟩
  have hgY : Good G R (insert y B) :=
    { disj := by
        rw [Finset.disjoint_insert_right]; exact ⟨hyn.1, hdisj⟩
      indep := hind
      conn := by
        refine C_conn_ext G R B R (insert y B) zx hu0 (Finset.Subset.refl _)
          (Finset.subset_insert _ _) hconn ?_
        intro w hw hwn
        simp only [Finset.mem_union, Finset.mem_insert] at hw hwn
        rcases hw with h | rfl | h
        · exact absurd (Or.inl h) hwn
        · exact ⟨s0, Finset.mem_union_left _ hs0,
            (C_bip_adj _ _ _ _ _).2 ⟨hys0, Or.inr ⟨by simp, hs0⟩⟩⟩
        · exact absurd (Or.inr h) hwn
      even := by
        rw [Finset.card_insert_of_notMem hyn.2]; exact hodd.add_one }
  have hgX : Good G R (insert x B) :=
    { disj := by
        rw [Finset.disjoint_insert_right]; exact ⟨hxn.1, hdisj⟩
      indep := hind
      conn := by
        refine C_conn_ext G R B R (insert x B) zx hu0 (Finset.Subset.refl _)
          (Finset.subset_insert _ _) hconn ?_
        intro w hw hwn
        simp only [Finset.mem_union, Finset.mem_insert] at hw hwn
        rcases hw with h | rfl | h
        · exact absurd (Or.inl h) hwn
        · exact ⟨r0, Finset.mem_union_left _ hr0,
            (C_bip_adj _ _ _ _ _).2 ⟨hxr0, Or.inr ⟨by simp, hr0⟩⟩⟩
        · exact absurd (Or.inr h) hwn
      even := by
        rw [Finset.card_insert_of_notMem hxn.2]; exact hodd.add_one }
  by_cases hx2 : 2 ≤ (R.filter (G.Adj x)).card
  · -- (B1) degR(x) ≥ 2 : y dans B, Lemme 8 avec v0 = x
    obtain ⟨ω, hW, hP⟩ := lemma8 G x R (insert y B) hgY (by simp [hxn.1, hxn.2, hxne])
      (fun u v _ => ⟨by rcases hall0 u with h | h | h | h <;> simp [h],
        by rcases hall0 v with h | h | h | h <;> simp [h]⟩)
      hx2 (Or.inr (Finset.card_pos.2 ⟨y, by simp [hxy]⟩))
    exact ⟨ω, hW, hP⟩
  by_cases hy2 : 2 ≤ (R.filter (G.Adj y)).card
  · -- (B2) degR(y) ≥ 2 : x dans B, Lemme 8 avec v0 = y
    obtain ⟨ω, hW, hP⟩ := lemma8 G y R (insert x B) hgX (by simp [hyn.1, hyn.2, hxne.symm])
      (fun u v _ => ⟨by rcases hall0 u with h | h | h | h <;> simp [h],
        by rcases hall0 v with h | h | h | h <;> simp [h]⟩)
      hy2 (Or.inr (Finset.card_pos.2 ⟨x, by simp [hxy.symm]⟩))
    exact ⟨ω, hW, hP⟩
  -- (C) degR(x) = degR(y) = 1
  obtain ⟨r1, hr1⟩ := Finset.card_eq_one.1 (show (R.filter (G.Adj x)).card = 1 by omega)
  have hr1R : r1 ∈ R ∧ G.Adj x r1 := by
    have : r1 ∈ R.filter (G.Adj x) := by rw [hr1]; simp
    simpa using this
  obtain ⟨s1, hs1⟩ := Finset.card_eq_one.1 (show (R.filter (G.Adj y)).card = 1 by omega)
  by_cases hcom : ∃ q ∈ R, G.Adj x q ∧ G.Adj y q
  · obtain ⟨q, hqR, hxq, hyq⟩ := hcom
    have e1 : q ∈ R.filter (G.Adj x) := by simp [hqR, hxq]
    have e2 : q ∈ R.filter (G.Adj y) := by simp [hqR, hyq]
    rw [hr1] at e1; rw [hs1] at e2
    rw [Finset.mem_singleton] at e1 e2
    subst e1; subst e2
    exact C13_case_C1 G x y zx hxy hzx R B hdisj hcov hind hzxB hconn hodd _ hr1 hs1
  · by_cases hzyR : zy ∈ R
    · -- (C2a) zy ∈ R : Lemme 9 avec v0 = x, u0 = r1, chemin p ∪ {y}
      have hzxzy : zx ≠ zy := fun h => by rw [h] at hzxB; exact Finset.disjoint_left.1 hdisj hzyR hzxB
      obtain ⟨hxzy, hyzx, hint⟩ : ¬ G.Adj x zy ∧ ¬ G.Adj y zx ∧ ∀ i, 0 < i → i < p.length →
          ¬ G.Adj x (p.getVert i).1 ∧ ¬ G.Adj y (p.getVert i).1 := by
        rcases hch with h | h
        · exact absurd h hzxzy
        · exact h
      have hpP : p.IsPath := p.isPath_of_length_eq_dist hp
      obtain ⟨L, hL⟩ : ∃ L, L = p.length := ⟨_, rfl⟩
      have hL1 : 1 ≤ L := by
        by_contra hh
        have h0 : p.length = 0 := by omega
        have := SimpleGraph.Walk.eq_of_length_eq_zero h0
        exact hzxzy (congrArg Subtype.val this)
      obtain ⟨q, hq⟩ : ∃ q : ℕ → V, ∀ i, q i = if i ≤ L then (p.getVert i).1 else y :=
        ⟨_, fun _ => rfl⟩
      have hnot : ∀ i, (p.getVert i).1 ≠ x ∧ (p.getVert i).1 ≠ y := fun i => by
        have := (p.getVert i).2
        simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at this
        exact this
      have hqL : q L = zy := by
        rw [hq, if_pos le_rfl, hL, SimpleGraph.Walk.getVert_length]
      have hq0 : q 0 = zx := by
        rw [hq, if_pos (Nat.zero_le _), SimpleGraph.Walk.getVert_zero]
      have hqL1 : q (L + 1) = y := by rw [hq, if_neg (by omega)]
      obtain ⟨ω, hW, hP⟩ := lemma9 G x r1 R (insert y B) hgY (by simp [hxn.1, hxn.2, hxne])
        (fun u v _ => ⟨by rcases hall0 u with h | h | h | h <;> simp [h],
          by rcases hall0 v with h | h | h | h <;> simp [h]⟩)
        hr1 (L + 2) (by omega) q
        (by
          intro i hi j hj hij
          simp only [Set.mem_Iio] at hi hj
          rw [hq, hq] at hij
          by_cases hiL : i ≤ L <;> by_cases hjL : j ≤ L
          · rw [if_pos hiL, if_pos hjL] at hij
            exact hpP.getVert_injOn (by rw [hL] at hiL; exact hiL) (by rw [hL] at hjL; exact hjL)
              (Subtype.ext hij)
          · rw [if_pos hiL, if_neg hjL] at hij; exact absurd hij (hnot i).2
          · rw [if_neg hiL, if_pos hjL] at hij; exact absurd hij.symm (hnot j).2
          · omega)
        (by
          intro i hi
          by_cases hiL : i < L
          · rw [hq, hq, if_pos hiL.le, if_pos (by omega)]
            exact hmono _ _ (hpath i (by omega))
          · have : i = L := by omega
            subst this
            rw [hqL, hqL1]
            exact (C_bip_adj _ _ _ _ _).2 ⟨hzy.symm, Or.inl ⟨hzyR, by simp⟩⟩)
        ⟨by rw [hq0]; exact Finset.mem_insert_of_mem hzxB, by rw [hq0]; exact hzx⟩
        ⟨by rw [show L + 2 - 1 = L + 1 by omega, hqL1]; simp, by
          rw [show L + 2 - 1 = L + 1 by omega, hqL1]; exact hxy⟩
        (by
          intro i hi hqi
          rw [hq] at hqi
          by_cases hiL : i ≤ L
          · rw [if_pos hiL] at hqi
            by_cases hi0 : i = 0
            · subst hi0
              rw [SimpleGraph.Walk.getVert_zero] at hqi
              have hqi' : zx = r1 := hqi
              have : zx ∈ R := by rw [hqi']; exact hr1R.1
              exact hzxR this
            · by_cases hiL' : i = L
              · subst hiL'
                rw [hL, SimpleGraph.Walk.getVert_length] at hqi
                have hqi' : zy = r1 := hqi
                exact hxzy (by rw [hqi']; exact hr1R.2)
              · exact (hint i (by omega) (by omega)).1 (by rw [hqi]; exact hr1R.2)
          · rw [if_neg hiL] at hqi
            exact hyn.1 (by rw [hqi]; exact hr1R.1))
      exact ⟨ω, hW, hP⟩
    · exact C13_case_C2b G x y zx zy hxy hzx hzxy hzy hzyx hzxS hzyS p hp hch R B hdisj hcov hind
        hzxR hconn hpath hodd r1 s1 hr1 hs1 hcom hzyR

theorem C14_bip_adj (G : SimpleGraph V) (R B : Finset V) (u v : V) :
    (bip G R B).Adj u v ↔ G.Adj u v ∧ ((u ∈ R ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ R)) := Iff.rfl

theorem C14_conn_ext (G : SimpleGraph V) (R B R2 B2 : Finset V) (u0 : V) (hu0 : u0 ∈ R ∪ B)
    (hR : R ⊆ R2) (hB : B ⊆ B2)
    (hc : ∀ u ∈ R ∪ B, ∀ v ∈ R ∪ B, (bip G R B).Reachable u v)
    (hnew : ∀ w ∈ R2 ∪ B2, w ∉ R ∪ B → ∃ u ∈ R ∪ B, (bip G R2 B2).Adj w u) :
    ∀ u ∈ R2 ∪ B2, ∀ v ∈ R2 ∪ B2, (bip G R2 B2).Reachable u v := by
  have hmono : bip G R B ≤ bip G R2 B2 := by
    intro u v h
    have h' := (C14_bip_adj _ _ _ _ _).1 h
    exact (C14_bip_adj _ _ _ _ _).2 ⟨h'.1, h'.2.imp (fun a => ⟨hR a.1, hB a.2⟩)
      (fun a => ⟨hB a.1, hR a.2⟩)⟩
  have hall : ∀ w ∈ R2 ∪ B2, (bip G R2 B2).Reachable w u0 := by
    intro w hw
    by_cases h : w ∈ R ∪ B
    · exact (hc w h u0 hu0).mono hmono
    · obtain ⟨u, hu, hadj⟩ := hnew w hw h
      exact hadj.reachable.trans ((hc u hu u0 hu0).mono hmono)
  intro u hu v hv
  exact (hall u hu).trans (hall v hv).symm

theorem C14_good_B2 (G : SimpleGraph V) (R B : Finset V) (x y r r' : V)
    (hdisj : Disjoint R B) (hind : ∀ u ∈ R, ∀ v ∈ R, ¬ G.Adj u v)
    (hconn : ∀ u ∈ R ∪ B, ∀ v ∈ R ∪ B, (bip G R B).Reachable u v)
    (hxn : x ∉ R ∧ x ∉ B) (hyn : y ∉ R ∧ y ∉ B) (hxy : x ≠ y)
    (hr : r ∈ R) (hxr : G.Adj x r) (hr' : r' ∈ R) (hyr : G.Adj y r') (hev : Even B.card) :
    Good G R (insert x (insert y B)) := by
  have hxB : x ∉ insert y B := by simp [hxy, hxn.2]
  exact
    { disj := by
        rw [Finset.disjoint_insert_right, Finset.disjoint_insert_right]
        exact ⟨hxn.1, hyn.1, hdisj⟩
      indep := hind
      conn := C14_conn_ext G R B R (insert x (insert y B)) r (Finset.mem_union_left _ hr)
        (Finset.Subset.refl _) (fun t ht => by simp [ht]) hconn (by
          intro w hw hwn
          simp only [Finset.mem_union, Finset.mem_insert] at hw hwn
          rcases hw with h | h | h | h
          · exact absurd (Or.inl h) hwn
          · subst h
            exact ⟨r, Finset.mem_union_left _ hr, (C14_bip_adj _ _ _ _ _).2 ⟨hxr, Or.inr ⟨by simp, hr⟩⟩⟩
          · subst h
            exact ⟨r', Finset.mem_union_left _ hr',
              (C14_bip_adj _ _ _ _ _).2 ⟨hyr, Or.inr ⟨by simp, hr'⟩⟩⟩
          · exact absurd (Or.inr h) hwn)
      even := by
        rw [Finset.card_insert_of_notMem hxB, Finset.card_insert_of_notMem hyn.2]
        obtain ⟨k, hk⟩ := hev
        exact ⟨k + 1, by omega⟩ }

theorem C14_good_R (G : SimpleGraph V) (R B : Finset V) (w b : V)
    (hdisj : Disjoint R B) (hind : ∀ u ∈ R, ∀ v ∈ R, ¬ G.Adj u v)
    (hconn : ∀ u ∈ R ∪ B, ∀ v ∈ R ∪ B, (bip G R B).Reachable u v)
    (hwn : w ∉ R ∧ w ∉ B) (hw : ∀ r ∈ R, ¬ G.Adj w r)
    (hb : b ∈ B) (hwb : G.Adj w b) (hev : Even B.card) : Good G (insert w R) B := by
  exact
    { disj := by rw [Finset.disjoint_insert_left]; exact ⟨hwn.2, hdisj⟩
      indep := by
        intro u hu v hv huv
        rw [Finset.mem_insert] at hu hv
        rcases hu with rfl | hu <;> rcases hv with rfl | hv
        · exact G.loopless.irrefl _ huv
        · exact hw v hv huv
        · exact hw u hu huv.symm
        · exact hind u hu v hv huv
      conn := C14_conn_ext G R B (insert w R) B b (Finset.mem_union_right _ hb)
        (Finset.subset_insert _ _) (Finset.Subset.refl _) hconn (by
          intro u hu hun
          simp only [Finset.mem_union, Finset.mem_insert] at hu hun
          rcases hu with (rfl | h) | h
          · exact ⟨b, Finset.mem_union_right _ hb,
              (C14_bip_adj _ _ _ _ _).2 ⟨hwb, Or.inl ⟨by simp, hb⟩⟩⟩
          · exact absurd (Or.inl h) hun
          · exact absurd (Or.inr h) hun)
      even := hev }

theorem C14_nbr (G : SimpleGraph V) (y x : V) (hy : 2 ≤ G.degree y) (hxy : G.Adj y x) :
    ∃ u, G.Adj y u ∧ u ≠ x := by
  have : 1 < (G.neighborFinset y).card := by rwa [card_neighborFinset_eq_degree]
  obtain ⟨a, ha, hne⟩ := Finset.exists_mem_ne this x
  exact ⟨a, (mem_neighborFinset _ _ _).1 ha, hne⟩

theorem C14_path (G : SimpleGraph V) (R B R2 : Finset V) (hdisj : Disjoint R B) (hsub : R ⊆ R2)
    (a b : V) (ha : a ∈ B) (hb : b ∈ B) (hab : a ≠ b)
    (hconn : ∀ u ∈ R ∪ B, ∀ v ∈ R ∪ B, (bip G R B).Reachable u v) :
    ∃ (k : ℕ) (p : ℕ → V), 3 ≤ k ∧ Set.InjOn p (Set.Iio k) ∧
      (∀ i, i + 1 < k → (bip G R2 B).Adj (p i) (p (i + 1))) ∧ p 0 = a ∧ p (k - 1) = b ∧
      ∀ i, i < k → p i ∈ R ∪ B := by
  obtain ⟨w⟩ := hconn a (Finset.mem_union_right _ ha) b (Finset.mem_union_right _ hb)
  set q := w.bypass with hqdef
  have hq : q.IsPath := w.bypass_isPath
  have hmono : bip G R B ≤ bip G R2 B := by
    intro u v h
    have h' := (C14_bip_adj _ _ _ _ _).1 h
    exact (C14_bip_adj _ _ _ _ _).2 ⟨h'.1, h'.2.imp (fun a => ⟨hsub a.1, a.2⟩) (fun a => ⟨a.1, hsub a.2⟩)⟩
  have hL : 2 ≤ q.length := by
    by_contra hlt
    push Not at hlt
    interval_cases h : q.length
    · exact hab (SimpleGraph.Walk.eq_of_length_eq_zero h)
    · have hadj := q.adj_getVert_succ (i := 0) (by omega)
      rw [SimpleGraph.Walk.getVert_zero] at hadj
      have h1 : q.getVert (0 + 1) = b := by
        have := q.getVert_length; rw [h] at this; simpa using this
      rw [h1] at hadj
      rcases ((C14_bip_adj _ _ _ _ _).1 hadj).2 with ⟨h2, _⟩ | ⟨_, h2⟩
      · exact Finset.disjoint_left.1 hdisj h2 ha
      · exact Finset.disjoint_left.1 hdisj h2 hb
  refine ⟨q.length + 1, q.getVert, by omega, ?_, fun i hi => ?_, SimpleGraph.Walk.getVert_zero _, ?_, ?_⟩
  · intro i hi j hj hij
    exact hq.getVert_injOn (show i ∈ {i | i ≤ q.length} by simp only [Set.mem_ofPred_eq]; simp at hi; omega)
      (show j ∈ {i | i ≤ q.length} by simp only [Set.mem_ofPred_eq]; simp at hj; omega) hij
  · exact hmono (q.adj_getVert_succ (i := i) (by omega))
  · simpa using q.getVert_length
  · intro i hi
    by_cases hil : i < q.length
    · have hadj := (C14_bip_adj _ _ _ _ _).1 (q.adj_getVert_succ hil)
      rcases hadj.2 with ⟨h2, _⟩ | ⟨h2, _⟩
      · exact Finset.mem_union_left _ h2
      · exact Finset.mem_union_right _ h2
    · have : i = q.length := by omega
      rw [this, q.getVert_length]; exact Finset.mem_union_right _ hb

noncomputable def C14_Gt (G : SimpleGraph V) (x y zy : V) : SimpleGraph V :=
  (G.deleteEdges {s(x, y), s(y, zy)}) ⊔ SimpleGraph.fromEdgeSet {s(x, zy)}

theorem C14_Gt_adj (G : SimpleGraph V) (x y zy a b : V) :
    (C14_Gt G x y zy).Adj a b ↔
      (G.Adj a b ∧ ¬ ((a = x ∧ b = y) ∨ (a = y ∧ b = x)) ∧ ¬ ((a = y ∧ b = zy) ∨ (a = zy ∧ b = y)))
        ∨ (((a = x ∧ b = zy) ∨ (a = zy ∧ b = x)) ∧ a ≠ b) := by
  simp only [C14_Gt, SimpleGraph.sup_adj, SimpleGraph.deleteEdges_adj, SimpleGraph.fromEdgeSet_adj,
    Set.mem_insert_iff, Set.mem_singleton_iff, Sym2.eq_iff, not_or]

theorem C14_Gt_x (G : SimpleGraph V) (x y zy : V) (hxy : G.Adj x y) (hyz : G.Adj y zy) (hxz : ¬ G.Adj x zy)
    (hxne : x ≠ y) (hzx : zy ≠ x) (hzy : zy ≠ y) (u : V) : (C14_Gt G x y zy).Adj x u ↔ (G.Adj x u ∧ u ≠ y) ∨ u = zy := by
  rw [C14_Gt_adj]
  constructor
  · rintro (⟨h1, h2, h3⟩ | ⟨h, _⟩)
    · left; refine ⟨h1, fun h => h2 (Or.inl ⟨rfl, h⟩)⟩
    · rcases h with ⟨_, h⟩ | ⟨h, _⟩
      · exact Or.inr h
      · exact absurd h.symm hzx
  · rintro (⟨h1, h2⟩ | rfl)
    · left
      refine ⟨h1, ?_, ?_⟩
      · rintro (⟨_, h⟩ | ⟨h, _⟩)
        · exact h2 h
        · exact hxne h
      · rintro (⟨h, _⟩ | ⟨h, _⟩)
        · exact hxne h
        · exact hzx h.symm
    · right; exact ⟨Or.inl ⟨rfl, rfl⟩, fun h => hzx h.symm⟩

theorem C14_Gt_y (G : SimpleGraph V) (x y zy : V) (hxy : G.Adj x y) (hyz : G.Adj y zy) (hxz : ¬ G.Adj x zy)
    (hxne : x ≠ y) (hzx : zy ≠ x) (hzy : zy ≠ y) (u : V) : (C14_Gt G x y zy).Adj y u ↔ G.Adj y u ∧ u ≠ x ∧ u ≠ zy := by
  rw [C14_Gt_adj]
  constructor
  · rintro (⟨h1, h2, h3⟩ | ⟨h, _⟩)
    · refine ⟨h1, fun h => h2 (Or.inr ⟨rfl, h⟩), fun h => h3 (Or.inl ⟨rfl, h⟩)⟩
    · rcases h with ⟨h, _⟩ | ⟨h, _⟩
      · exact absurd h hxne.symm
      · exact absurd h hzy.symm
  · rintro ⟨h1, h2, h3⟩
    left
    refine ⟨h1, ?_, ?_⟩
    · rintro (⟨h, _⟩ | ⟨_, h⟩)
      · exact hxne.symm h
      · exact h2 h
    · rintro (⟨_, h⟩ | ⟨h, _⟩)
      · exact h3 h
      · exact hzy h.symm

noncomputable def C14_om (wt : Sym2 V → ℕ) (x y zy : V) : Sym2 V → ℕ :=
  fun e => if e = s(x, y) ∨ e = s(y, zy) then wt s(x, zy) else wt e

theorem C14_om_eq (wt : Sym2 V → ℕ) (x y zy a b : V)
    (h1 : ¬ ((a = x ∧ b = y) ∨ (a = y ∧ b = x))) (h2 : ¬ ((a = y ∧ b = zy) ∨ (a = zy ∧ b = y))) :
    C14_om wt x y zy s(a, b) = wt s(a, b) := by
  unfold C14_om
  rw [if_neg]
  simp only [Sym2.eq_iff]
  tauto

theorem C14_sdeg_sum (G : SimpleGraph V) (w : Sym2 V → ℕ) (v : V) :
    sdeg G w v = ∑ u, if G.Adj v u then w s(v, u) else 0 := by
  unfold sdeg; rw [Finset.sum_filter]

theorem C14_om_xy (wt : Sym2 V → ℕ) (x y zy : V) : C14_om wt x y zy s(x, y) = wt s(x, zy) := by
  unfold C14_om; simp

theorem C14_sx (G : SimpleGraph V) (x y zy : V) (wt : Sym2 V → ℕ) (hxy : G.Adj x y) (hyz : G.Adj y zy)
    (hxz : ¬ G.Adj x zy) (hxne : x ≠ y) (hzx : zy ≠ x) (hzy : zy ≠ y) : sdeg G (C14_om wt x y zy) x = sdeg (C14_Gt G x y zy) wt x := by
  rw [C14_sdeg_sum, C14_sdeg_sum]
  rw [← Equiv.sum_comp (Equiv.swap y zy) (fun u => if (C14_Gt G x y zy).Adj x u then wt s(x, u) else 0)]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  by_cases hu : u = y
  · subst hu
    rw [Equiv.swap_apply_left, if_pos hxy, if_pos ((C14_Gt_x G x u zy hxy hyz hxz hxne hzx hzy zy).2 (Or.inr rfl)),
      C14_om_xy]
  · by_cases hu2 : u = zy
    · subst hu2
      rw [Equiv.swap_apply_right, if_neg hxz, if_neg]
      rw [C14_Gt_x G x y u hxy hyz hxz hxne hzx hzy]
      rintro (⟨_, h⟩ | h)
      · exact h rfl
      · exact hzy h.symm
    · rw [Equiv.swap_apply_of_ne_of_ne hu hu2]
      have : (C14_Gt G x y zy).Adj x u ↔ G.Adj x u := by
        rw [C14_Gt_x G x y zy hxy hyz hxz hxne hzx hzy]
        constructor
        · rintro (⟨h, _⟩ | h)
          · exact h
          · exact absurd h hu2
        · intro h; exact Or.inl ⟨h, hu⟩
      simp only [this]
      split_ifs
      · rw [C14_om_eq]
        · rintro (⟨_, h⟩ | ⟨h, _⟩)
          · exact hu h
          · exact hxne h
        · rintro (⟨h, _⟩ | ⟨h, _⟩)
          · exact hxne h
          · exact hzx h.symm
      · rfl

theorem C14_Gt_zy (G : SimpleGraph V) (x y zy : V) (hxy : G.Adj x y) (hyz : G.Adj y zy) (hxz : ¬ G.Adj x zy)
    (hxne : x ≠ y) (hzx : zy ≠ x) (hzy : zy ≠ y) (u : V) : (C14_Gt G x y zy).Adj zy u ↔ (G.Adj zy u ∧ u ≠ y) ∨ u = x := by
  rw [C14_Gt_adj]
  constructor
  · rintro (⟨h1, h2, h3⟩ | ⟨h, _⟩)
    · left; refine ⟨h1, fun h => h3 (Or.inr ⟨rfl, h⟩)⟩
    · rcases h with ⟨h, _⟩ | ⟨_, h⟩
      · exact absurd h hzx
      · exact Or.inr h
  · rintro (⟨h1, h2⟩ | rfl)
    · left
      refine ⟨h1, ?_, ?_⟩
      · rintro (⟨h, _⟩ | ⟨h, _⟩)
        · exact hzx h
        · exact hzy h
      · rintro (⟨h, _⟩ | ⟨_, h⟩)
        · exact hzy h
        · exact h2 h
    · right; exact ⟨Or.inr ⟨rfl, rfl⟩, hzx⟩

theorem C14_om_yz (wt : Sym2 V → ℕ) (x y zy : V) : C14_om wt x y zy s(y, zy) = wt s(x, zy) := by
  unfold C14_om; simp

theorem C14_szy (G : SimpleGraph V) (x y zy : V) (wt : Sym2 V → ℕ) (hxy : G.Adj x y) (hyz : G.Adj y zy)
    (hxz : ¬ G.Adj x zy) (hxne : x ≠ y) (hzx : zy ≠ x) (hzy : zy ≠ y) : sdeg G (C14_om wt x y zy) zy = sdeg (C14_Gt G x y zy) wt zy := by
  rw [C14_sdeg_sum, C14_sdeg_sum]
  rw [← Equiv.sum_comp (Equiv.swap x y) (fun u => if (C14_Gt G x y zy).Adj zy u then wt s(zy, u) else 0)]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  by_cases hu : u = y
  · subst hu
    rw [Equiv.swap_apply_right, if_pos hyz.symm, if_pos ((C14_Gt_zy G x u zy hxy hyz hxz hxne hzx hzy x).2 (Or.inr rfl)),
      Sym2.eq_swap (a := zy) (b := u), C14_om_yz, Sym2.eq_swap (a := zy) (b := x)]
  · by_cases hu2 : u = x
    · subst hu2
      rw [Equiv.swap_apply_left, if_neg (fun h => hxz h.symm), if_neg]
      rw [C14_Gt_zy G u y zy hxy hyz hxz hxne hzx hzy]
      rintro (⟨_, h⟩ | h)
      · exact h rfl
      · exact hxne h.symm
    · rw [Equiv.swap_apply_of_ne_of_ne hu2 hu]
      have : (C14_Gt G x y zy).Adj zy u ↔ G.Adj zy u := by
        rw [C14_Gt_zy G x y zy hxy hyz hxz hxne hzx hzy]
        constructor
        · rintro (⟨h, _⟩ | h)
          · exact h
          · exact absurd h hu2
        · intro h; exact Or.inl ⟨h, hu⟩
      simp only [this]
      split_ifs
      · rw [C14_om_eq]
        · rintro (⟨h, _⟩ | ⟨h, _⟩)
          · exact hzx h
          · exact hzy h
        · rintro (⟨h, _⟩ | ⟨_, h⟩)
          · exact hzy h
          · exact hu h
      · rfl

theorem C14_sy (G : SimpleGraph V) (x y zy : V) (wt : Sym2 V → ℕ) (hxy : G.Adj x y) (hyz : G.Adj y zy)
    (hxz : ¬ G.Adj x zy) (hxne : x ≠ y) (hzx : zy ≠ x) (hzy : zy ≠ y) : sdeg G (C14_om wt x y zy) y = sdeg (C14_Gt G x y zy) wt y + 2 * wt s(x, zy) := by
  rw [C14_sdeg_sum, C14_sdeg_sum]
  have h : ∀ u, (if G.Adj y u then C14_om wt x y zy s(y, u) else 0) =
      (if (C14_Gt G x y zy).Adj y u then wt s(y, u) else 0) +
        ((if u = x then wt s(x, zy) else 0) + (if u = zy then wt s(x, zy) else 0)) := by
    intro u
    rw [C14_Gt_y G x y zy hxy hyz hxz hxne hzx hzy]
    by_cases h1 : u = x
    · subst h1
      have e : C14_om wt u y zy s(y, u) = wt s(u, zy) := by rw [Sym2.eq_swap, C14_om_xy]
      simp [hxy.symm, e, hzx.symm]
    · by_cases h2 : u = zy
      · subst h2
        simp [hyz, hzx, C14_om_yz]
      · by_cases h3 : G.Adj y u
        · simp only [h1, h2, h3, if_true, if_false, true_and, ne_eq, not_false_eq_true, add_zero]
          rw [C14_om_eq]
          · rintro (⟨h, _⟩ | ⟨_, h⟩)
            · exact hxne.symm h
            · exact h1 h
          · rintro (⟨_, h⟩ | ⟨h, _⟩)
            · exact h2 h
            · exact hzy.symm h
        · simp [h1, h2, h3]
  rw [Finset.sum_congr rfl (fun u _ => h u), Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp [Finset.sum_ite_eq']
  ring

theorem C14_Gt_other (G : SimpleGraph V) (x y zy : V) (hxy : G.Adj x y) (hyz : G.Adj y zy) (hxz : ¬ G.Adj x zy)
    (hxne : x ≠ y) (hzx : zy ≠ x) (hzy : zy ≠ y) (v : V) (h1 : v ≠ x) (h2 : v ≠ y) (h3 : v ≠ zy) (u : V) :
    (C14_Gt G x y zy).Adj v u ↔ G.Adj v u := by
  rw [C14_Gt_adj]
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩)
    · exact h
    · rcases h with ⟨h, _⟩ | ⟨h, _⟩
      · exact absurd h h1
      · exact absurd h h3
  · intro h
    left
    refine ⟨h, ?_, ?_⟩
    · rintro (⟨h, _⟩ | ⟨h, _⟩)
      · exact h1 h
      · exact h2 h
    · rintro (⟨h, _⟩ | ⟨h, _⟩)
      · exact h2 h
      · exact h3 h

theorem C14_sv (G : SimpleGraph V) (x y zy : V) (wt : Sym2 V → ℕ) (hxy : G.Adj x y) (hyz : G.Adj y zy)
    (hxz : ¬ G.Adj x zy) (hxne : x ≠ y) (hzx : zy ≠ x) (hzy : zy ≠ y) (v : V) (h1 : v ≠ x) (h2 : v ≠ y) (h3 : v ≠ zy) :
    sdeg G (C14_om wt x y zy) v = sdeg (C14_Gt G x y zy) wt v := by
  rw [C14_sdeg_sum, C14_sdeg_sum]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [C14_Gt_other G x y zy hxy hyz hxz hxne hzx hzy v h1 h2 h3 u]
  split_ifs
  · rw [C14_om_eq]
    · rintro (⟨h, _⟩ | ⟨h, _⟩)
      · exact h1 h
      · exact h2 h
    · rintro (⟨h, _⟩ | ⟨h, _⟩)
      · exact h2 h
      · exact h3 h
  · rfl

theorem C14_upd1 (G : SimpleGraph V) (ω : Sym2 V → ℕ) (a b : V) (w' : ℕ) (hab : G.Adj a b) :
    (sdeg G (Function.update ω s(a, b) w') a : ℤ) = sdeg G ω a + w' - ω s(a, b) := by
  unfold sdeg
  push_cast
  have hpt : ∀ u ∈ univ.filter (G.Adj a), ((Function.update ω s(a, b) w' s(a, u) : ℕ) : ℤ) =
      (ω s(a, u) : ℤ) + (if u = b then ((w' : ℤ) - ω s(a, b)) else 0) := by
    intro u _
    by_cases hu : u = b
    · subst hu; simp
    · have : s(a, u) ≠ s(a, b) := by
        intro h
        rw [Sym2.eq_iff] at h
        rcases h with ⟨_, h⟩ | ⟨h1, h2⟩
        · exact hu h
        · exact hab.ne h1
      rw [Function.update_of_ne this]; simp [hu]
  rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_ite_eq']
  have hb : b ∈ univ.filter (G.Adj a) := by simp [hab]
  rw [if_pos hb]; ring

theorem C14_upd (G : SimpleGraph V) (ω : Sym2 V → ℕ) (a b : V) (w' : ℕ) (hab : G.Adj a b) :
    (sdeg G (Function.update ω s(a, b) w') a : ℤ) = sdeg G ω a + w' - ω s(a, b) ∧
    (sdeg G (Function.update ω s(a, b) w') b : ℤ) = sdeg G ω b + w' - ω s(a, b) ∧
    ∀ v, v ≠ a → v ≠ b → sdeg G (Function.update ω s(a, b) w') v = sdeg G ω v := by
  refine ⟨C14_upd1 G ω a b w' hab, ?_, ?_⟩
  · have := C14_upd1 G ω b a w' hab.symm
    rwa [Sym2.eq_swap (a := b) (b := a)] at this
  · intro v hva hvb
    unfold sdeg
    refine Finset.sum_congr rfl (fun u _ => ?_)
    have : s(v, u) ≠ s(a, b) := by
      intro h
      rw [Sym2.eq_iff] at h
      rcases h with ⟨h, _⟩ | ⟨h, _⟩
      · exact hva h
      · exact hvb h
    rw [Function.update_of_ne this]

theorem C14_odd_edge (G : SimpleGraph V) (ω : Sym2 V → ℕ) (v : V) (h : ¬ Even (sdeg G ω v)) :
    ∃ u, G.Adj v u ∧ ¬ Even (ω s(v, u)) := by
  by_contra hcon
  push Not at hcon
  apply h
  unfold sdeg
  exact Finset.even_sum _ (fun u hu => by
    have : G.Adj v u := by simpa using hu
    exact hcon u this)

theorem C14_case_d (G : SimpleGraph V) (x y zy : V) (hxy : G.Adj x y) (hy : 2 ≤ G.degree y)
    (R B : Finset V) (hdisj : Disjoint R B)
    (hcov : ∀ v, (v ∈ R ∨ v ∈ B) ↔ (v ≠ x ∧ v ≠ y)) (hind : ∀ u ∈ R, ∀ v ∈ R, ¬ G.Adj u v)
    (hconn : ∀ u ∈ R ∪ B, ∀ v ∈ R ∪ B, (bip G R B).Reachable u v) (hev : Even B.card)
    (hxR : ∀ r ∈ R, ¬ G.Adj x r) (hyB : ∀ b ∈ B, ¬ G.Adj y b) (hodd : Odd (G.degree y))
    (hzy : zy ∈ R) (hyz : G.Adj y zy) :
    ∃ ω, Wt3 G ω ∧ Proper G ω := by
  have hxne : x ≠ y := G.ne_of_adj hxy
  have hxn : x ∉ R ∧ x ∉ B := by
    have := (hcov x).not.2 (by simp)
    simpa using this
  have hyn : y ∉ R ∧ y ∉ B := by
    have := (hcov y).not.2 (by simp)
    simpa using this
  have hxz : ¬ G.Adj x zy := hxR zy hzy
  have hzx : zy ≠ x := fun h => hxn.1 (by rw [← h]; exact hzy)
  have hzyy : zy ≠ y := fun h => hyn.1 (by rw [← h]; exact hzy)
  obtain ⟨r2, hyr2, hr2x, hr2z⟩ : ∃ u, G.Adj y u ∧ u ≠ x ∧ u ≠ zy := by
    by_contra hcon
    push Not at hcon
    have hsub : G.neighborFinset y ⊆ {x, zy} := by
      intro t ht
      rw [mem_neighborFinset] at ht
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases h : t = x
      · exact Or.inl h
      · exact Or.inr (hcon t ht h)
    have h1 := Finset.card_le_card hsub
    rw [card_neighborFinset_eq_degree] at h1
    have h2 := Finset.card_le_two (a := x) (b := zy)
    obtain ⟨k, hk⟩ := hodd
    omega
  have hr2R : r2 ∈ R := by
    rcases (hcov r2).2 ⟨hr2x, (G.ne_of_adj hyr2).symm⟩ with h | h
    · exact h
    · exact absurd hyr2 (hyB r2 h)
  have hGtx : (C14_Gt G x y zy).Adj x zy :=
    (C14_Gt_x G x y zy hxy hyz hxz hxne hzx hzyy zy).2 (Or.inr rfl)
  have hGty : (C14_Gt G x y zy).Adj y r2 :=
    (C14_Gt_y G x y zy hxy hyz hxz hxne hzx hzyy r2).2 ⟨hyr2, hr2x, hr2z⟩
  have hbmono : bip G R B ≤ bip (C14_Gt G x y zy) R B := by
    intro a b h
    have h' := (C14_bip_adj _ _ _ _ _).1 h
    have hRB : ∀ t, ((t ∈ R ∧ True) ∨ (t ∈ B ∧ True)) → t ≠ x ∧ t ≠ y := fun t ht =>
      (hcov t).1 (by rcases ht with h | h <;> [exact Or.inl h.1; exact Or.inr h.1])
    have ha : a ≠ x ∧ a ≠ y := hRB a (by rcases h'.2 with h | h <;> [exact Or.inl ⟨h.1, trivial⟩; exact Or.inr ⟨h.1, trivial⟩])
    have hb : b ≠ x ∧ b ≠ y := hRB b (by rcases h'.2 with h | h <;> [exact Or.inr ⟨h.2, trivial⟩; exact Or.inl ⟨h.2, trivial⟩])
    refine (C14_bip_adj _ _ _ _ _).2 ⟨(C14_Gt_adj G x y zy a b).2 (Or.inl ⟨h'.1, ?_, ?_⟩), h'.2⟩
    · rintro (⟨h, _⟩ | ⟨h, _⟩)
      · exact ha.1 h
      · exact ha.2 h
    · rintro (⟨h, _⟩ | ⟨_, h⟩)
      · exact ha.2 h
      · exact hb.2 h
  have hconnt : ∀ u ∈ R ∪ B, ∀ v ∈ R ∪ B, (bip (C14_Gt G x y zy) R B).Reachable u v :=
    fun u hu v hv => (hconn u hu v hv).mono hbmono
  have hindt : ∀ u ∈ R, ∀ v ∈ R, ¬ (C14_Gt G x y zy).Adj u v := by
    intro u hu v hv h
    rcases (C14_Gt_adj G x y zy u v).1 h with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hind u hu v hv h1
    · rcases h1 with ⟨h, _⟩ | ⟨_, h⟩
      · exact hxn.1 (h ▸ hu)
      · exact hxn.1 (h ▸ hv)
  have hg := C14_good_B2 (C14_Gt G x y zy) R B x y zy r2 hdisj hindt hconnt hxn hyn hxne hzy hGtx
    hr2R hGty hev
  have hdom : ∀ u v, (C14_Gt G x y zy).Adj u v →
      u ∈ R ∪ insert x (insert y B) ∧ v ∈ R ∪ insert x (insert y B) := by
    have hall' : ∀ w, w ∈ R ∪ insert x (insert y B) := by
      intro w
      by_cases h1 : w = x
      · simp [h1]
      by_cases h2 : w = y
      · simp [h2]
      · rcases (hcov w).2 ⟨h1, h2⟩ with a | a <;> simp [a]
    exact fun u v _ => ⟨hall' u, hall' v⟩
  obtain ⟨wt, hWt, hPt, hpar⟩ := lemma7 (C14_Gt G x y zy) R _ hg hdom
  have hEvR : ∀ v ∈ R, Even (sdeg (C14_Gt G x y zy) wt v) :=
    fun v hv => (hpar v (Finset.mem_union_left _ hv)).2 hv
  have hOdd : ∀ v ∈ insert x (insert y B), ¬ Even (sdeg (C14_Gt G x y zy) wt v) := by
    intro v hv he
    have := (hpar v (Finset.mem_union_right _ hv)).1 he
    exact Finset.disjoint_left.1 hg.disj this hv
  set om := C14_om wt x y zy with hom
  have hsx := C14_sx G x y zy wt hxy hyz hxz hxne hzx hzyy
  have hszy := C14_szy G x y zy wt hxy hyz hxz hxne hzx hzyy
  have hsy := C14_sy G x y zy wt hxy hyz hxz hxne hzx hzyy
  have hsv := C14_sv G x y zy wt hxy hyz hxz hxne hzx hzyy
  have hB'x : x ∈ insert x (insert y B) := by simp
  have hB'y : y ∈ insert x (insert y B) := by simp
  have hWom : Wt3 G om := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      have hab : G.Adj a b := he
      by_cases hsp : s(a, b) = s(x, y) ∨ s(a, b) = s(y, zy)
      · simp only [hom, C14_om, if_pos hsp]
        exact hWt s(x, zy) (by simpa using hGtx)
      · have hGt : (C14_Gt G x y zy).Adj a b := by
          rw [C14_Gt_adj]
          left
          refine ⟨hab, ?_, ?_⟩
          · intro h; apply hsp; left; rw [Sym2.eq_iff]; exact h
          · intro h; apply hsp; right; rw [Sym2.eq_iff]; exact h
        simp only [hom, C14_om, if_neg hsp]
        exact hWt s(a, b) (by simpa using hGt)
  have hRe : ∀ v ∈ R, Even (sdeg G om v) := by
    intro v hv
    by_cases h : v = zy
    · rw [h, hszy]; exact hEvR zy hzy
    · have h1 : v ≠ x := fun h' => hxn.1 (h' ▸ hv)
      have h2 : v ≠ y := fun h' => hyn.1 (h' ▸ hv)
      rw [hsv v h1 h2 h]; exact hEvR v hv
  have hBzy : ∀ v ∈ B, v ≠ zy := fun v hv h => Finset.disjoint_left.1 hdisj hzy (h ▸ hv)
  have hsame : ∀ a, a ∈ insert x (insert y B) → a ≠ y →
      sdeg G om a = sdeg (C14_Gt G x y zy) wt a := by
    intro a ha hay
    by_cases hax : a = x
    · rw [hax]; exact hsx
    · have haB : a ∈ B := by
        simp only [Finset.mem_insert] at ha
        rcases ha with h | h | h
        · exact absurd h hax
        · exact absurd h hay
        · exact h
      exact hsv a hax hay (hBzy a haB)
  have hBo : ∀ v ∈ insert x (insert y B), ¬ Even (sdeg G om v) := by
    intro v hv he
    by_cases hvy : v = y
    · subst hvy
      rw [hsy] at he
      exact hOdd v hv ((Nat.even_add.1 he).2 (even_two_mul _))
    · rw [hsame v hv hvy] at he
      exact hOdd v hv he
  have hprop : ∀ a b, G.Adj a b → a ∈ insert x (insert y B) → b ∈ insert x (insert y B) →
      a ≠ y → b ≠ y → sdeg G om a ≠ sdeg G om b := by
    intro a b hab ha hb hay hby
    rw [hsame a ha hay, hsame b hb hby]
    refine hPt a b ?_
    rw [C14_Gt_adj]
    left
    refine ⟨hab, ?_, ?_⟩
    · rintro (⟨_, h⟩ | ⟨h, _⟩)
      · exact hby h
      · exact hay h
    · rintro (⟨h, _⟩ | ⟨_, h⟩)
      · exact hay h
      · exact hby h
  have hcls : ∀ w, w ∈ R ∨ w ∈ insert x (insert y B) := by
    intro w
    by_cases h1 : w = x
    · right; simp [h1]
    by_cases h2 : w = y
    · right; simp [h2]
    · rcases (hcov w).2 ⟨h1, h2⟩ with a | a
      · left; exact a
      · right; simp [a]
  have hfin : ∀ ωf : Sym2 V → ℕ, (∀ v ∈ R, Even (sdeg G ωf v)) →
      (∀ v ∈ insert x (insert y B), ¬ Even (sdeg G ωf v)) →
      (∀ a b, G.Adj a b → a ∈ insert x (insert y B) → b ∈ insert x (insert y B) →
        a ≠ y → b ≠ y → sdeg G ωf a ≠ sdeg G ωf b) →
      sdeg G ωf x ≠ sdeg G ωf y → Proper G ωf := by
    intro ωf hR hB hP hxy'
    intro a b hab
    rcases hcls a with ha | ha <;> rcases hcls b with hb | hb
    · exact absurd hab (hind a ha b hb)
    · intro h; exact hB b hb (h ▸ hR a ha)
    · intro h; exact hB a ha (h ▸ hR b hb)
    · by_cases hay : a = y
      · subst hay
        have hbx : b = x := by
          simp only [Finset.mem_insert] at hb
          rcases hb with h | h | h
          · exact h
          · exact absurd h.symm (G.ne_of_adj hab)
          · exact absurd hab (hyB b h)
        subst hbx
        exact hxy'.symm
      · by_cases hby : b = y
        · subst hby
          have hax : a = x := by
            simp only [Finset.mem_insert] at ha
            rcases ha with h | h | h
            · exact h
            · exact absurd h (G.ne_of_adj hab)
            · exact absurd hab.symm (hyB a h)
          subst hax
          exact hxy'
        · exact hP a b hab ha hb hay hby
  by_cases hconf : sdeg G om x = sdeg G om y
  · -- conflit x-y : on change une arête impaire en y
    obtain ⟨r1, hyr1, hodd1⟩ := C14_odd_edge (C14_Gt G x y zy) wt y (hOdd y hB'y)
    have hr1 := (C14_Gt_y G x y zy hxy hyz hxz hxne hzx hzyy r1).1 hyr1
    obtain ⟨hyr1G, hr1x, hr1z⟩ := hr1
    have hr1R : r1 ∈ R := by
      rcases (hcov r1).2 ⟨hr1x, (G.ne_of_adj hyr1G).symm⟩ with h | h
      · exact h
      · exact absurd hyr1G (hyB r1 h)
    have hwb := hWt s(y, r1) (by simpa using hyr1)
    have hom1 : om s(y, r1) = wt s(y, r1) := by
      apply C14_om_eq
      · rintro (⟨h, _⟩ | ⟨_, h⟩)
        · exact hxne.symm h
        · exact hr1x h
      · rintro (⟨_, h⟩ | ⟨h, _⟩)
        · exact hr1z h
        · exact hzyy h.symm
    have hwodd : wt s(y, r1) = 1 ∨ wt s(y, r1) = 3 := by
      rw [Nat.even_iff] at hodd1; omega
    obtain ⟨u1, u2, u3⟩ := C14_upd G om y r1 (4 - wt s(y, r1)) hyr1G
    set om' := Function.update om s(y, r1) (4 - wt s(y, r1)) with hom'
    rw [hom1] at u1 u2
    have hr1B' : r1 ∉ insert x (insert y B) := fun h => Finset.disjoint_left.1 hg.disj hr1R h
    have hr1y : r1 ≠ y := fun h => hyn.1 (h ▸ hr1R)
    have hpar2 : ∀ n m : ℕ, ((n : ℤ) = m + 2 ∨ (n : ℤ) = m - 2) → (Even n ↔ Even m) := by
      intro n m h
      rw [Nat.even_iff, Nat.even_iff]; omega
    have hdy : (sdeg G om' y : ℤ) = sdeg G om y + 2 ∨ (sdeg G om' y : ℤ) = sdeg G om y - 2 := by
      rcases hwodd with h | h
      · rw [h] at u1; left; omega
      · rw [h] at u1; right; omega
    have hdr : (sdeg G om' r1 : ℤ) = sdeg G om r1 + 2 ∨ (sdeg G om' r1 : ℤ) = sdeg G om r1 - 2 := by
      rcases hwodd with h | h
      · rw [h] at u2; left; omega
      · rw [h] at u2; right; omega
    have hchg : ∀ v, v = y ∨ v = r1 → (Even (sdeg G om' v) ↔ Even (sdeg G om v)) := by
      intro v hv
      rcases hv with h | h
      · rw [h]; exact hpar2 _ _ hdy
      · rw [h]; exact hpar2 _ _ hdr
    refine ⟨om', ?_, hfin om' ?_ ?_ ?_ ?_⟩
    · intro e he
      by_cases hee : e = s(y, r1)
      · rw [hom', hee, Function.update_self]
        rcases hwodd with h | h <;> rw [h] <;> omega
      · rw [hom', Function.update_of_ne hee]; exact hWom e he
    · intro v hv
      by_cases hv1 : v = r1
      · rw [(hchg v (Or.inr hv1))]; exact hRe v hv
      · have hvy : v ≠ y := fun h => hyn.1 (h ▸ hv)
        rw [u3 v hvy hv1]; exact hRe v hv
    · intro v hv
      by_cases hvy : v = y
      · rw [(hchg v (Or.inl hvy))]; exact hBo v hv
      · have hv1 : v ≠ r1 := fun h => hr1B' (h ▸ hv)
        rw [u3 v hvy hv1]; exact hBo v hv
    · intro a b hab ha hb hay hby
      have ha1 : a ≠ r1 := fun h => hr1B' (h ▸ ha)
      have hb1 : b ≠ r1 := fun h => hr1B' (h ▸ hb)
      rw [u3 a hay ha1, u3 b hby hb1]; exact hprop a b hab ha hb hay hby
    · have hx1 : x ≠ r1 := fun h => hr1B' (h ▸ hB'x)
      rw [u3 x hxne hx1]
      intro h
      rcases hdy with h2 | h2 <;> omega
  · exact ⟨om, hWom, hfin om hRe hBo hprop hconf⟩

theorem C14_main (G : SimpleGraph V) (x y zx zy : V) (hxy : G.Adj x y)
    (hx : 2 < G.degree x) (hy : 2 ≤ G.degree y) (hzx : G.Adj x zx) (hzxy : zx ≠ y)
    (hzy : G.Adj y zy) (hzyx : zy ≠ x) (hc : (G.induce ({x, y}ᶜ : Set V)).Connected)
    (R B : Finset V) (hdisj : Disjoint R B)
    (hcov : ∀ v, (v ∈ R ∨ v ∈ B) ↔ (v ≠ x ∧ v ≠ y)) (hind : ∀ u ∈ R, ∀ v ∈ R, ¬ G.Adj u v)
    (hzxB : zx ∈ B)
    (hconn : ∀ u ∈ R ∪ B, ∀ v ∈ R ∪ B, (bip G R B).Reachable u v) (hev : Even B.card) :
    ∃ ω, Wt3 G ω ∧ Proper G ω := by
  have hxne : x ≠ y := G.ne_of_adj hxy
  have hxn : x ∉ R ∧ x ∉ B := by
    have := (hcov x).not.2 (by simp)
    simpa using this
  have hyn : y ∉ R ∧ y ∉ B := by
    have := (hcov y).not.2 (by simp)
    simpa using this
  have hRdisj : ∀ v, v ∈ R → v ∉ B := fun v h h' => Finset.disjoint_left.1 hdisj h h'
  have hall : ∀ w, w = x ∨ w = y ∨ w ∈ R ∨ w ∈ B := by
    intro w
    by_cases h1 : w = x
    · exact Or.inl h1
    by_cases h2 : w = y
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr ((hcov w).2 ⟨h1, h2⟩))
  have hinRB : ∀ u, G.Adj y u → u ≠ x → u ∈ R ∨ u ∈ B := fun u hu hne =>
    (hcov u).2 ⟨hne, (G.ne_of_adj hu).symm⟩
  have hu0 : zx ∈ R ∪ B := Finset.mem_union_right _ hzxB
  by_cases hyR : ∃ r ∈ R, G.Adj y r
  · obtain ⟨r', hr', hyr'⟩ := hyR
    by_cases hxR : ∃ r ∈ R, G.Adj x r
    · -- (1a) x, y dans B
      obtain ⟨r, hr, hxr⟩ := hxR
      have hg := C14_good_B2 G R B x y r r' hdisj hind hconn hxn hyn hxne hr hxr hr' hyr' hev
      have hdom : ∀ u v, G.Adj u v → u ∈ R ∪ insert x (insert y B) ∧ v ∈ R ∪ insert x (insert y B) := by
        have hall' : ∀ w, w ∈ R ∪ insert x (insert y B) := by
          intro w
          rcases hall w with h | h | h | h <;> simp [h]
        exact fun u v _ => ⟨hall' u, hall' v⟩
      obtain ⟨ω, hW, hP, -⟩ := lemma7 G R _ hg hdom
      exact ⟨ω, hW, hP⟩
    · -- x sans voisin dans R, y avec
      push Not at hxR
      by_cases h2d : (∀ b ∈ B, ¬ G.Adj y b) ∧ Odd (G.degree y)
      · exact C14_case_d G x y r' hxy hy R B hdisj hcov hind hconn hev hxR h2d.1 h2d.2 hr' hyr'
      have hxy' : x ∈ insert x R := Finset.mem_insert_self _ _
      have hg := C14_good_R G R B x zx hdisj hind hconn hxn hxR hzxB hzx hev
      have hdom : ∀ u v, G.Adj u v → (u ∈ insert x R ∪ B ∨ u = y) ∧ (v ∈ insert x R ∪ B ∨ v = y) := by
        have hall' : ∀ w, w ∈ insert x R ∪ B ∨ w = y := by
          intro w
          rcases hall w with h | h | h | h
          · left; simp [h]
          · right; exact h
          · left; simp [h]
          · left; simp [h]
        exact fun u v _ => ⟨hall' u, hall' v⟩
      have hcard : 2 ≤ ((insert x R).filter (G.Adj y)).card := by
        have hsub : ({x, r'} : Finset V) ⊆ (insert x R).filter (G.Adj y) := by
          intro t ht
          simp only [Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with rfl | rfl
          · simp [hxy.symm]
          · simp [hr', hyr']
        have := Finset.card_le_card hsub
        rwa [Finset.card_pair (fun h => hxn.1 (by rw [h]; exact hr'))] at this
      have hpar : Even ((insert x R).filter (G.Adj y)).card ∨ 1 ≤ (B.filter (G.Adj y)).card := by
        by_cases hB : ∃ b ∈ B, G.Adj y b
        · obtain ⟨b, hb, hyb⟩ := hB
          exact Or.inr (Finset.card_pos.2 ⟨b, by simp [hb, hyb]⟩)
        · push Not at hB
          by_cases hodd : Odd (G.degree y)
          · exact absurd ⟨hB, hodd⟩ h2d
          · left
            have hfe : (insert x R).filter (G.Adj y) = G.neighborFinset y := by
              ext u
              simp only [Finset.mem_filter, Finset.mem_insert, mem_neighborFinset]
              constructor
              · exact fun h => h.2
              · intro hu
                refine ⟨?_, hu⟩
                by_cases hux : u = x
                · exact Or.inl hux
                · rcases hinRB u hu hux with h | h
                  · exact Or.inr h
                  · exact absurd hu (hB u h)
            rw [hfe, card_neighborFinset_eq_degree]
            exact Nat.not_odd_iff_even.1 hodd
      obtain ⟨ω, hW, hP⟩ := lemma8 G y (insert x R) B hg (by simp [hyn.1, hyn.2, hxne.symm]) hdom hcard hpar
      exact ⟨ω, hW, hP⟩
  · push Not at hyR
    obtain ⟨u1, hyu1, hu1x⟩ := C14_nbr G y x hy hxy.symm
    have hu1B : u1 ∈ B := by
      rcases hinRB u1 hyu1 hu1x with h | h
      · exact absurd hyu1 (hyR u1 h)
      · exact h
    have hg := C14_good_R G R B y u1 hdisj hind hconn hyn hyR hu1B hyu1 hev
    have hdom : ∀ u v, G.Adj u v → (u ∈ insert y R ∪ B ∨ u = x) ∧ (v ∈ insert y R ∪ B ∨ v = x) := by
      have hall' : ∀ w, w ∈ insert y R ∪ B ∨ w = x := by
        intro w
        rcases hall w with h | h | h | h
        · right; exact h
        · left; simp [h]
        · left; simp [h]
        · left; simp [h]
      exact fun u v _ => ⟨hall' u, hall' v⟩
    have hv0 : x ∉ insert y R ∪ B := by simp [hxne, hxn.1, hxn.2]
    by_cases hxR : ∃ r ∈ R, G.Adj x r
    · -- (1b) y dans R, Lemme 8 avec v0 = x
      obtain ⟨r, hr, hxr⟩ := hxR
      have hcard : 2 ≤ ((insert y R).filter (G.Adj x)).card := by
        have hsub : ({y, r} : Finset V) ⊆ (insert y R).filter (G.Adj x) := by
          intro t ht
          simp only [Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with rfl | rfl
          · simp [hxy]
          · simp [hr, hxr]
        have := Finset.card_le_card hsub
        rwa [Finset.card_pair (fun h => hyn.1 (by rw [h]; exact hr))] at this
      obtain ⟨ω, hW, hP⟩ := lemma8 G x (insert y R) B hg hv0 hdom hcard
        (Or.inr (Finset.card_pos.2 ⟨zx, by simp [hzxB, hzx]⟩))
      exact ⟨ω, hW, hP⟩
    · -- (2a) ni x ni y n'ont de voisin dans R : Lemme 9
      push Not at hxR
      obtain ⟨zx', hzx'1, hzx'2, hzx'3⟩ : ∃ z, G.Adj x z ∧ z ≠ y ∧ z ≠ zx := by
        by_contra hcon
        push Not at hcon
        have hsub : G.neighborFinset x ⊆ {y, zx} := by
          intro t ht
          rw [mem_neighborFinset] at ht
          simp only [Finset.mem_insert, Finset.mem_singleton]
          by_cases h : t = y
          · exact Or.inl h
          · exact Or.inr (hcon t ht h)
        have h1 := Finset.card_le_card hsub
        rw [card_neighborFinset_eq_degree] at h1
        have h2 := Finset.card_le_two (a := y) (b := zx)
        omega
      have hzx'B : zx' ∈ B := by
        rcases (hcov zx').2 ⟨(G.ne_of_adj hzx'1).symm, hzx'2⟩ with h | h
        · exact absurd hzx'1 (hxR zx' h)
        · exact h
      obtain ⟨k, p, hk, hinj, hadj, hp0, hpk, hpRB⟩ :=
        C14_path G R B (insert y R) hdisj (Finset.subset_insert _ _) zx zx' hzxB hzx'B
          (Ne.symm hzx'3) hconn
      have hN : (insert y R).filter (G.Adj x) = {y} := by
        ext u
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨h | h, hu⟩
          · exact h
          · exact absurd hu (hxR u h)
        · rintro rfl; exact ⟨Or.inl rfl, hxy⟩
      obtain ⟨ω, hW, hP⟩ := lemma9 G x y (insert y R) B hg hv0 hdom hN k hk p hinj hadj
        ⟨by rw [hp0]; exact hzxB, by rw [hp0]; exact hzx⟩
        ⟨by rw [hpk]; exact hzx'B, by rw [hpk]; exact hzx'1⟩
        (fun i hi h => hyn.1 (by
          have := hpRB i hi
          rw [h] at this
          rcases Finset.mem_union.1 this with h' | h'
          · exact h'
          · exact absurd h' hyn.2))
      exact ⟨ω, hW, hP⟩

theorem C_core_14 (G : SimpleGraph V) (x y zx zy : V) (hxy : G.Adj x y)
    (hdx : 2 < G.degree x) (hdy : 2 ≤ G.degree y)
    (hzx : G.Adj x zx) (hzxy : zx ≠ y) (hzy : G.Adj y zy) (hzyx : zy ≠ x)
    (hc : (G.induce ({x, y}ᶜ : Set V)).Connected)
    (hzxS : zx ∈ ({x, y}ᶜ : Set V)) (hzyS : zy ∈ ({x, y}ᶜ : Set V))
    (p : (G.induce ({x, y}ᶜ : Set V)).Walk ⟨zx, hzxS⟩ ⟨zy, hzyS⟩)
    (hp : p.length = (G.induce ({x, y}ᶜ : Set V)).dist ⟨zx, hzxS⟩ ⟨zy, hzyS⟩)
    (hch : zx = zy ∨ (¬ G.Adj x zy ∧ ¬ G.Adj y zx ∧ ∀ i, 0 < i → i < p.length →
      ¬ G.Adj x (p.getVert i).1 ∧ ¬ G.Adj y (p.getVert i).1))
    (R B : Finset V) (hdisj : Disjoint R B) (hcov : ∀ v, (v ∈ R ∨ v ∈ B) ↔ (v ≠ x ∧ v ≠ y))
    (hind : ∀ u ∈ R, ∀ v ∈ R, ¬ G.Adj u v) (hzxR : zx ∉ R)
    (hconn : ∀ u ∈ R ∪ B, ∀ v ∈ R ∪ B, (bip G R B).Reachable u v)
    (hpath : ∀ i, i < p.length → (bip G R B).Adj (p.getVert i).1 (p.getVert (i + 1)).1)
    (hodd : Even B.card) :
    ∃ ω, Wt3 G ω ∧ Proper G ω := by
  have hzxB : zx ∈ B := by
    have hx1 : zx ≠ x := (G.ne_of_adj hzx).symm
    rcases (hcov zx).2 ⟨hx1, hzxy⟩ with h | h
    · exact absurd h hzxR
    · exact h
  exact C14_main G x y zx zy hxy hdx hdy hzx hzxy hzy hzyx hc R B hdisj hcov hind hzxB hconn hodd

theorem C_nbr (G : SimpleGraph V) (z w : V) (hz : 2 ≤ G.degree z) :
    ∃ a, G.Adj z a ∧ a ≠ w := by
  have : 1 < (G.neighborFinset z).card := by rwa [card_neighborFinset_eq_degree]
  obtain ⟨a, ha, hne⟩ := Finset.exists_mem_ne this w
  exact ⟨a, (mem_neighborFinset _ _ _).1 ha, hne⟩

theorem C_core_ge2 (G : SimpleGraph V) (hG : G.Connected) (hmin : ∀ v, 2 ≤ G.degree v) :
    ∃ ω, Wt3 G ω ∧ Proper G ω := by
  have key : ∀ x y, G.Adj x y → (G.induce ({x, y}ᶜ : Set V)).Connected → 2 < G.degree x →
      ∃ ω, Wt3 G ω ∧ Proper G ω := by
    intro x y hxy hc hx
    obtain ⟨zx, zy, hzxS, hzyS, hzx, hzy, hch⟩ := C_choice G x y hxy (hmin x) (hmin y) hc
    have hzxy : zx ≠ y := fun h => hzxS (by simp [h])
    have hzyx : zy ≠ x := fun h => hzyS (by simp [h])
    obtain ⟨p, hp, hch'⟩ : ∃ p : (G.induce ({x, y}ᶜ : Set V)).Walk ⟨zx, hzxS⟩ ⟨zy, hzyS⟩,
        p.length = (G.induce ({x, y}ᶜ : Set V)).dist ⟨zx, hzxS⟩ ⟨zy, hzyS⟩ ∧
        (zx = zy ∨ (¬ G.Adj x zy ∧ ¬ G.Adj y zx ∧ ∀ i, 0 < i → i < p.length →
          ¬ G.Adj x (p.getVert i).1 ∧ ¬ G.Adj y (p.getVert i).1)) := by
      rcases hch with h | ⟨h1, h2, p, hp, h3⟩
      · subst h; exact ⟨Walk.nil, by simp, Or.inl rfl⟩
      · exact ⟨p, hp, Or.inr ⟨h1, h2, h3⟩⟩
    obtain ⟨R, B, hdisj, hcov, hind, hzxR, hconn, hpath⟩ :=
      C_setup G x y zx zy hzxS hzyS hc p hp false
    have hzxR' : zx ∉ R := fun h => by simpa using hzxR.1 h
    rcases Nat.even_or_odd B.card with hev | hodd
    · exact C_core_14 G x y zx zy hxy hx (hmin y) hzx hzxy hzy hzyx hc hzxS hzyS p hp hch'
        R B hdisj hcov hind hzxR' hconn hpath hev
    · exact C_core_13 G x y zx zy hxy hx (hmin y) hzx hzxy hzy hzyx hc hzxS hzyS p hp hch'
        R B hdisj hcov hind hzxR' hconn hpath hodd
  obtain ⟨x, y, hxy, hc⟩ := lemma10 G hG hmin
  by_cases h22 : G.degree x = 2 ∧ G.degree y = 2
  · obtain ⟨zx, hzx, hzxy⟩ := C_nbr G x y (hmin x)
    obtain ⟨zy, hzy, hzyx⟩ := C_nbr G y x (hmin y)
    exact C_core_22 G x y zx zy hxy h22.1 h22.2 hzx hzxy hzy hzyx hc
  · by_cases hx : 2 < G.degree x
    · exact key x y hxy hc hx
    · have hy : 2 < G.degree y := by
        have := hmin x; have := hmin y; omega
      refine key y x hxy.symm ?_ hy
      rwa [Set.pair_comm]

theorem main_connected (hV : 3 ≤ Fintype.card V) (G : SimpleGraph V) (hG : G.Connected) :
    ∃ ω, Wt3 G ω ∧ Proper G ω := by
  by_cases h1 : ∃ x, G.degree x = 1
  · obtain ⟨x, hx⟩ := h1
    exact C_deg_one hV G hG x hx
  · push Not at h1
    apply C_core_ge2 G hG
    intro v
    have hpos : 0 < G.degree v := by
      obtain ⟨w, hw⟩ := Fintype.exists_ne_of_one_lt_card (by omega) v
      obtain ⟨p⟩ := hG.preconnected v w
      cases p with
      | nil => exact absurd rfl hw
      | cons h t => exact (G.degree_pos_iff_exists_adj v).2 ⟨_, h⟩
    have := h1 v
    omega

theorem D_sdeg_eq [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (w : Sym2 V → ℕ)
    (v : V) : sdeg G w v = OneTwoThreeConjecture.weightedDegree G w v := by
  unfold sdeg OneTwoThreeConjecture.weightedDegree
  have himg : G.incidenceFinset v = (univ.filter (G.Adj v)).image (fun u => s(v, u)) := by
    ext e
    induction e using Sym2.ind with
    | _ a b =>
      simp only [SimpleGraph.mem_incidenceFinset, Finset.mem_image, Finset.mem_filter,
        Finset.mem_univ, true_and, SimpleGraph.mk'_mem_incidenceSet_iff]
      constructor
      · rintro ⟨h, rfl | rfl⟩
        · exact ⟨b, h, rfl⟩
        · exact ⟨a, h.symm, Sym2.eq_swap⟩
      · rintro ⟨u, hu, he⟩
        rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨hu, Or.inl rfl⟩
        · exact ⟨hu.symm, Or.inr rfl⟩
  rw [himg, Finset.sum_image (by intro a _ b _ h; exact Sym2.congr_right.1 h)]
  convert rfl

theorem D_comp [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hne : ∀ u v, G.Adj u v → 2 ≤ G.degree u ∨ 2 ≤ G.degree v) (c : G.ConnectedComponent) :
    ∃ ω : Sym2 c.supp → ℕ, Wt3 (G.induce c.supp) ω ∧ Proper (G.induce c.supp) ω := by
  by_cases hadj : ∃ a b : c.supp, (G.induce c.supp).Adj a b
  · obtain ⟨a, b, hab⟩ := hadj
    have hconn : (G.induce c.supp).Connected :=
      (SimpleGraph.ConnectedComponent.maximal_connected_induce_supp c).1
    apply main_connected _ _ hconn
    by_contra hlt
    push Not at hlt
    have hab' : G.Adj a b := hab
    have hne_ab : (a : V) ≠ b := hab'.ne
    have key : ∀ x y : c.supp, G.Adj x y → ∀ u, G.Adj x u → u = y := by
      intro x y hxy u hxu
      by_contra hub
      have hu : u ∈ c.supp := by
        have h1 : G.connectedComponentMk u = G.connectedComponentMk x :=
          SimpleGraph.ConnectedComponent.sound hxu.reachable.symm
        exact h1.trans x.2
      have : 2 < Fintype.card c.supp := by
        rw [Fintype.two_lt_card_iff]
        refine ⟨x, y, ⟨u, hu⟩, ?_, ?_, ?_⟩
        · intro h; exact hxy.ne (by rw [h])
        · intro h; exact hxu.ne (by rw [h])
        · intro h; exact hub (by rw [h])
      omega
    have hdeg : ∀ x y : c.supp, G.Adj x y → G.degree x ≤ 1 := by
      intro x y hxy
      rw [← SimpleGraph.card_neighborFinset_eq_degree]
      apply Finset.card_le_one.2
      intro p hp q hq
      rw [SimpleGraph.mem_neighborFinset] at hp hq
      rw [key x y hxy p hp, key x y hxy q hq]
    have h1 := hdeg a b hab'
    have h2 := hdeg b a hab'.symm
    rcases hne a b hab' with h | h <;> omega
  · refine ⟨fun _ => 1, ?_, ?_⟩
    · intro e he
      exfalso
      induction e using Sym2.ind with
      | _ a b => exact hadj ⟨a, b, he⟩
    · intro a b hab
      exact absurd ⟨a, b, hab⟩ hadj

theorem D_extend (G : SimpleGraph V) (ω : ∀ c : G.ConnectedComponent, Sym2 c.supp → ℕ) :
    ∃ wc : G.ConnectedComponent → Sym2 V → ℕ,
      (∀ c u v (hu : u ∈ c.supp) (hv : v ∈ c.supp),
        wc c s(u, v) = ω c s(⟨u, hu⟩, ⟨v, hv⟩)) ∧
      (∀ c u v, ¬ (u ∈ c.supp ∧ v ∈ c.supp) → wc c s(u, v) = 0) := by
  refine ⟨fun c => Sym2.lift ⟨fun u v =>
    if h : u ∈ c.supp ∧ v ∈ c.supp then ω c s(⟨u, h.1⟩, ⟨v, h.2⟩) else 0, ?_⟩, ?_, ?_⟩
  · intro u v
    by_cases h : u ∈ c.supp ∧ v ∈ c.supp
    · have h' : v ∈ c.supp ∧ u ∈ c.supp := ⟨h.2, h.1⟩
      simp only [dif_pos h, dif_pos h']
      rw [Sym2.eq_swap]
    · have h' : ¬ (v ∈ c.supp ∧ u ∈ c.supp) := fun x => h ⟨x.2, x.1⟩
      simp only [dif_neg h, dif_neg h']
  · intro c u v hu hv
    simp only [Sym2.lift_mk]
    rw [dif_pos ⟨hu, hv⟩]
  · intro c u v h
    simp only [Sym2.lift_mk]
    rw [dif_neg h]

theorem D_main [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hne : ∀ u v, G.Adj u v → 2 ≤ G.degree u ∨ 2 ≤ G.degree v) :
    ∃ w : Sym2 V → ℕ, Wt3 G w ∧ Proper G w := by
  choose ω hω1 hω2 using D_comp G hne
  obtain ⟨wc, hwc1, hwc0⟩ := D_extend G ω
  have hmem : ∀ u : V, u ∈ (G.connectedComponentMk u).supp := fun u => rfl
  have hmem' : ∀ (c : G.ConnectedComponent) (u v : V), u ∈ c.supp → G.Adj u v →
      v ∈ c.supp := by
    intro c u v hu h
    have h1 : G.connectedComponentMk v = G.connectedComponentMk u :=
      SimpleGraph.ConnectedComponent.sound h.reachable.symm
    exact h1.trans hu
  have hw : ∀ (c : G.ConnectedComponent) (u v : V) (hu : u ∈ c.supp) (h : G.Adj u v),
      (∑ c', wc c' s(u, v)) = ω c s(⟨u, hu⟩, ⟨v, hmem' c u v hu h⟩) := by
    intro c u v hu h
    rw [Finset.sum_eq_single c]
    · exact hwc1 _ _ _ _ _
    · intro c' _ hc'
      apply hwc0
      rintro ⟨hu', _⟩
      exact hc' (hu'.symm.trans hu)
    · intro h'
      exact absurd (Finset.mem_univ _) h'
  have hdeg : ∀ (c : G.ConnectedComponent) (v : V) (hv : v ∈ c.supp),
      sdeg G (fun e => ∑ c', wc c' e) v = sdeg (G.induce c.supp) (ω c) ⟨v, hv⟩ := by
    intro c v hv
    unfold sdeg
    symm
    refine Finset.sum_bij (fun (u' : c.supp) _ => (u' : V)) ?_ ?_ ?_ ?_
    · intro u' hu'
      simpa using hu'
    · intro a _ b _ h
      exact Subtype.ext h
    · intro u hu
      have hu' : G.Adj v u := by simpa using hu
      exact ⟨⟨u, hmem' c v u hv hu'⟩, by simpa using hu', rfl⟩
    · intro u' hu'
      have hu'' : G.Adj v u' := by simpa using hu'
      exact (hw c v u' hv hu'').symm
  refine ⟨fun e => ∑ c', wc c' e, ?_, ?_⟩
  · intro e he
    induction e using Sym2.ind with
    | _ a b =>
      have h : G.Adj a b := (SimpleGraph.mem_edgeSet G).1 he
      show 1 ≤ ∑ c', wc c' s(a, b) ∧ ∑ c', wc c' s(a, b) ≤ 3
      rw [hw _ a b (hmem a) h]
      exact hω1 _ _ ((SimpleGraph.mem_edgeSet _).2 (show (G.induce _).Adj _ _ from h))
  · intro u v h
    rw [hdeg _ u (hmem u), hdeg _ v (hmem' _ u v (hmem u) h)]
    exact hω2 _ _ _ (show (G.induce _).Adj _ _ from h)

theorem D_final {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hne : OneTwoThreeConjecture.NoIsolatedEdge G) :
    ∃ w : Sym2 V → ℕ, (∀ e ∈ G.edgeFinset, 1 ≤ w e ∧ w e ≤ 3) ∧
      OneTwoThreeConjecture.IsVertexColouringWeighting G w := by
  obtain ⟨w, h1, h2⟩ := D_main G hne
  refine ⟨w, fun e he => h1 e (by simpa using he), fun u v h => ?_⟩
  rw [← D_sdeg_eq, ← D_sdeg_eq]
  exact h2 u v h

end OTT

end OTTCore

theorem OMA.solution : type_of% @OneTwoThreeConjecture.one_two_three_conjecture :=
  OTT.D_final

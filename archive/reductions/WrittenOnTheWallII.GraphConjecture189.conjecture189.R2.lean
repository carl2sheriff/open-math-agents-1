import FormalConjectures.WrittenOnTheWallII.GraphConjecture189

-- Reduction WrittenOnTheWallII.GraphConjecture189.conjecture189.R2 of WOWII Conjecture 189
-- Credit: @carl2sheriff
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
Reduction of WOWII Conjecture 189 to the two cases `n ≥ 2σ + 3` (graph with a cut
vertex, resp. 2-connected graph). The case `n ≤ 2σ + 2` is proved here (Theorem C):
a longest path with both ends of degree `≥ σ` gives an Ore-type degree sum, and the
single low-degree vertex `x₀` is handled through a rotation / deletion argument.

Infrastructure adapted from reduction R1 by @computerfreak97, PR #2971, itself adapting
philipsaint's Dirac formalization (`degree_pair`, `rot`, `getD_zero`, `getD_last`,
`dist_iso`, `even_iso`, `second_iso`, start of `main`, and the longest-path / crossing-chord
argument of `trace_of_sum`).
-/

open SimpleGraph

namespace OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2

/-- Case with a cut vertex and `2σ + 3 ≤ n`. -/
def H1 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected →
    (∀ x, distEven G x ≤ 1 + secondSmallestDegree G) →
    2 * secondSmallestDegree G + 3 ≤ Fintype.card V →
    (∃ c : V, ¬ (G.induce {x | x ≠ c}).Connected) →
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian

/-- 2-connected case with `2σ + 3 ≤ n`. -/
def H2 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected →
    (∀ x, distEven G x ≤ 1 + secondSmallestDegree G) →
    2 * secondSmallestDegree G + 3 ≤ Fintype.card V →
    (∀ c : V, (G.induce {x | x ≠ c}).Connected) →
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

-- Fact 0 (adapted from R1).
lemma degree_pair [DecidableRel G.Adj] [Nontrivial V] (x y : V) (hne : x ≠ y) :
    secondSmallestDegree G ≤ G.degree x ∨ secondSmallestDegree G ≤ G.degree y := by
  classical
  let ds := degreeSequence G
  have hlen : 2 ≤ ds.length := by
    simpa [ds, degreeSequence] using Nat.succ_le_of_lt (Fintype.one_lt_card (α := V))
  obtain ⟨a,b,l,heq⟩ : ∃ a b l, ds = a :: b :: l := by
    cases h : ds with
    | nil => simp [h] at hlen
    | cons a tail =>
      cases hh : tail with
      | nil => simp [h, hh] at hlen
      | cons b l => exact ⟨a,b,l,rfl⟩
  have hs : ds.Pairwise (· ≤ ·) := by simp [ds, degreeSequence]
  rw [heq] at hs
  have hlow : ∀ t ∈ l, b ≤ t := (List.pairwise_cons.mp (List.pairwise_cons.mp hs).2).1
  have hnil : l.filter (fun t => decide (t < b)) = [] := by
    simpa [List.filter_eq_nil_iff] using hlow
  have hct : (ds.filter (fun t => decide (t < b))).length ≤ 1 := by
    rw [heq]
    by_cases h : a < b <;> simp [h,hnil]
  have hcoeds : (↑ds : Multiset ℕ) = Finset.univ.val.map (fun v : V => G.degree v) := by
    simp [ds, degreeSequence]
  let low := Finset.univ.filter (fun v : V => G.degree v < b)
  have hl : low.card ≤ 1 := by
    change (Multiset.filter (fun t => G.degree t < b) Finset.univ.val).card ≤ 1
    have hct' : (Multiset.filter (fun t => t < b) (↑ds : Multiset ℕ)).card ≤ 1 := hct
    rw [hcoeds, Multiset.filter_map, Multiset.card_map] at hct'
    exact hct'
  have hb : secondSmallestDegree G = b := by
    change ds.getD 1 0 = b
    simp [heq] 
  rw [hb]
  by_contra! h
  exact hne (Finset.card_le_one.mp hl x (by simpa [low] using h.1) y (by simpa [low] using h.2))

section Transfer

variable {W : Type*} [Fintype W] [DecidableEq W] {G' : SimpleGraph W}

lemma dist_iso (φ : G ≃g G') (hc : G.Connected) (x y : V) :
    G'.dist (φ x) (φ y) = G.dist x y := by
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist x y
  obtain ⟨q,hq⟩ := (φ.connected_iff.mp hc).exists_walk_length_eq_dist (φ x) (φ y)
  have h1 := dist_le (p.map φ.toHom)
  have h2 := dist_le (q.map φ.symm.toHom)
  simp only [Walk.length_map,hp] at h1
  simpa [Walk.length_map,hq] using le_antisymm h1 (by simpa [Walk.length_map,hq] using h2)

lemma even_iso (φ : G ≃g G') (hc : G.Connected) (x : V) :
    distEven G' (φ x) = distEven G x := by
  classical
  simp only [distEven, Finset.card_filter]
  rw [← φ.toEquiv.sum_comp]
  apply Finset.sum_congr rfl
  intro y _
  rw [show G'.dist (φ x) (φ.toEquiv y) = G.dist x y from dist_iso φ hc x y]

lemma second_iso [DecidableRel G.Adj] [DecidableRel G'.Adj] (φ : G ≃g G') :
    secondSmallestDegree G' = secondSmallestDegree G := by
  change ((Finset.univ.val.map (fun y : W => G'.degree y)).sort (· ≤ ·)).getD 1 0 =
    ((Finset.univ.val.map (fun x : V => G.degree x)).sort (· ≤ ·)).getD 1 0
  congr 2
  rw [← Finset.map_univ_equiv φ.toEquiv]
  simp only [Finset.map_val, Multiset.map_map, Function.comp_def]
  congr 1
  exact funext (φ.degree_eq ·)


end Transfer

section Paths

-- Rotation and list helpers adapted from reduction R1.
lemma rot {c : List V} (hc : c.IsChain G.Adj ∧ ∀ a ∈ c.getLast?, ∀ b ∈ c.head?, G.Adj a b) {q : V} (hq : q ∈ c) :
    ∃ c' : List V, c'.Perm c ∧ c'.IsChain G.Adj ∧ c'.head? = some q := by
  obtain ⟨A, B, rfl⟩ := List.append_of_mem hq
  refine ⟨(q :: B) ++ A, List.perm_append_comm, ?_, by simp⟩
  obtain ⟨hch, hcl⟩ := hc
  rw [List.isChain_append] at hch
  refine List.isChain_append.2 ⟨hch.2.1, hch.1, ?_⟩
  intro x hx y hy
  apply hcl
  · rw [List.getLast?_append]
    have : (q :: B).getLast? = some x := hx
    simp [this]
  · rw [List.head?_append, hy]
    rfl

lemma getD_zero (l : List V) (hl : l ≠ []) (d : V) : l.getD 0 d = l.head hl := by
  cases l with
  | nil => exact absurd rfl hl
  | cons a t => rfl

lemma getD_last (l : List V) (hl : l ≠ []) (d : V) : l.getD (l.length - 1) d = l.getLast hl := by
  rw [List.getLast_eq_getElem, List.getD_eq_getElem]


/-- A Hamiltonian walk from a nodup chain through all vertices (adapted from R1). -/
lemma ham_of_list [DecidableRel G.Adj] (l : List V) (hne : l ≠ []) (hnd : l.Nodup)
    (hch : l.IsChain G.Adj) (hlen : l.length = Fintype.card V) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  let p := Walk.ofSupport l hne hch
  have hp : p.IsPath := Walk.IsPath.mk' (by simpa [p, Walk.support_ofSupport] using hnd)
  exact ⟨_, _, p, Walk.isHamiltonian_iff_isPath_and_length_eq.mpr
    ⟨hp, by simpa [p, Walk.length_ofSupport, hlen]⟩⟩

/-- Existence of a longest path, as a nodup chain list. -/
lemma exists_longest [Nonempty V] [DecidableRel G.Adj] :
    ∃ l : List V, l ≠ [] ∧ l.Nodup ∧ l.IsChain G.Adj ∧
      ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → l'.length ≤ l.length := by
  classical
  obtain ⟨v0⟩ := (inferInstance : Nonempty V)
  let PP : ℕ → Prop := fun k => ∃ l : List V, (l.Nodup ∧ l.IsChain G.Adj) ∧ l.length = k
  have h1 : PP 1 := ⟨[v0], ⟨by simp, List.isChain_singleton _⟩, rfl⟩
  have hpos : 1 ≤ Fintype.card V := Fintype.card_pos
  set M := Nat.findGreatest PP (Fintype.card V)
  obtain ⟨l, ⟨hlnd, hlch⟩, hlM⟩ : PP M := Nat.findGreatest_spec hpos h1
  have hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → l'.length ≤ M :=
    fun l' h1 h2 => Nat.le_findGreatest h1.length_le_card ⟨l', ⟨h1, h2⟩, rfl⟩
  have hM1 : 1 ≤ M := Nat.le_findGreatest hpos h1
  have hl_ne : l ≠ [] := by
    rintro rfl
    simp at hlM
    omega
  exact ⟨l, hl_ne, hlnd, hlch, fun l' a b => hlM ▸ hmax l' a b⟩

/-- Lemma 4 (Ore cycle on a longest path). -/
lemma lemma4 [DecidableRel G.Adj] (hconn : G.Connected) (l : List V) (hne : l ≠ [])
    (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V) (h2 : 2 ≤ l.length) :
    (∀ y, G.Adj (l.head hne) y → y ∈ l) ∧ (∀ y, G.Adj (l.getLast hne) y → y ∈ l) ∧
      G.degree (l.head hne) + G.degree (l.getLast hne) + 1 ≤ l.length ∧
      (∀ j, j + 1 < l.length → G.Adj (l.head hne) (l.getD (j + 1) (l.head hne)) →
        ¬ G.Adj (l.getD j (l.head hne)) (l.getLast hne)) ∧
      G.degree (l.head hne) ≤ ((Finset.range (l.length - 1)).filter
        (fun j => G.Adj (l.head hne) (l.getD (j + 1) (l.head hne)))).card ∧
      G.degree (l.getLast hne) ≤ ((Finset.range (l.length - 1)).filter
        (fun j => G.Adj (l.getD j (l.head hne)) (l.getLast hne))).card := by
  classical
  set n := Fintype.card V with hn
  have hlnd := hnd
  have hlch := hch
  set q0 := l.head hne
  set z := l.getLast hne
  have ext_head : ∀ y, G.Adj q0 y → y ∈ l := by
    intro y hy
    by_contra hyl
    have := hmax (y :: l) (List.nodup_cons.2 ⟨hyl, hlnd⟩)
      (List.IsChain.cons_of_ne_nil hne hlch ((hy).symm))
    simp only [List.length_cons] at this
    omega
  have ext_last : ∀ y, G.Adj z y → y ∈ l := by
    intro y hy
    by_contra hyl
    have hch : (l ++ [y]).IsChain G.Adj := by
      refine List.isChain_append.2 ⟨hlch, List.isChain_singleton _, ?_⟩
      intro x hx y' hy'
      rw [List.getLast?_eq_some_getLast hne] at hx
      simp at hx hy'
      subst hx hy'
      exact hy
    have hnd : (l ++ [y]).Nodup := by
      rw [List.nodup_append]
      refine ⟨hlnd, List.nodup_singleton _, ?_⟩
      intro a ha b hb
      simp at hb
      subst hb
      rintro rfl
      exact hyl ha
    have := hmax _ hnd hch
    simp only [List.length_append, List.length_singleton] at this
    omega
  have hl_ne := hne
  set m := l.length with hm
  have hq0 : l.getD 0 q0 = q0 := getD_zero l hl_ne q0
  have hz : l.getD (m - 1) q0 = z := getD_last l hl_ne q0
  have htwo : 2 ≤ m := h2
  have hneEnds : q0 ≠ z := by
    intro he
    have ieq : l[0]'(by omega) = l[m-1]'(by omega) := by
      rw [← List.getD_eq_getElem (d := q0), ← List.getD_eq_getElem (d := q0), hq0, hz]
      exact he
    have hh := hlnd.getElem_inj_iff.mp ieq
    omega
  -- The two index sets of possible crossing chords.
  let S := (Finset.range (m - 1)).filter (fun j => G.Adj q0 (l.getD (j + 1) q0))
  let T := (Finset.range (m - 1)).filter (fun j => G.Adj (l.getD j q0) z)
  have hS : G.degree q0 ≤ S.card := by
    rw [← card_neighborFinset_eq_degree]
    refine le_trans (Finset.card_le_card ?_) (Finset.card_image_le (s := S)
      (f := fun j => l.getD (j + 1) q0))
    intro y hy
    rw [mem_neighborFinset] at hy
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem (ext_head y hy)
    have hk0 : k ≠ 0 := by
      rintro rfl
      apply hy.ne
      rw [← List.getD_eq_getElem (d := q0), hq0]
    rw [Finset.mem_image]
    refine ⟨k - 1, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, ?_⟩
      rw [show k - 1 + 1 = k by omega, List.getD_eq_getElem _ _ hk]
      exact hy
    · rw [show k - 1 + 1 = k by omega, List.getD_eq_getElem _ _ hk]
  have hT : G.degree z ≤ T.card := by
    rw [← card_neighborFinset_eq_degree]
    refine le_trans (Finset.card_le_card ?_) (Finset.card_image_le (s := T)
      (f := fun j => l.getD j q0))
    intro y hy
    rw [mem_neighborFinset] at hy
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem (ext_last y hy)
    have hkm : k ≠ m - 1 := by
      rintro rfl
      apply hy.ne
      rw [← List.getD_eq_getElem (d := q0), hz]
    rw [Finset.mem_image]
    refine ⟨k, ?_, List.getD_eq_getElem _ _ hk⟩
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    rw [List.getD_eq_getElem _ _ hk]
    exact (hy).symm
  have hdisj : ∀ j, j ∈ S → j ∈ T → False := by
    intro j hjS hjT
    rw [Finset.mem_filter, Finset.mem_range] at hjS hjT
    obtain ⟨hjm, hA⟩ := hjS
    obtain ⟨-, hB⟩ := hjT
    -- the cycle
    set c := l.take (j + 1) ++ (l.drop (j + 1)).reverse with hcdef
    have hperm : c.Perm l := by
      have := (List.Perm.append_left (l.take (j + 1)) (List.reverse_perm (l.drop (j + 1))))
      rw [List.take_append_drop] at this
      exact this
    have hcnd : c.Nodup := hperm.nodup_iff.mpr hlnd
    have hj1 : j < m := by omega
    have hj2 : j + 1 < m := by omega
    have e1 : (l.take (j + 1)).getLast? = some (l.getD j q0) := by
      rw [List.getLast?_take, List.getD_eq_getElem _ _ hj1]
      simp [List.getElem?_eq_getElem hj1]
    have e2 : (l.drop (j + 1)).reverse.head? = some z := by
      rw [List.head?_reverse, List.getLast?_drop, if_neg (by omega), List.getLast?_eq_some_getLast hl_ne]
    have e3 : c.getLast? = some (l.getD (j + 1) q0) := by
      rw [hcdef, List.getLast?_append, List.getLast?_reverse, List.head?_drop,
        List.getElem?_eq_getElem hj2, List.getD_eq_getElem _ _ hj2]
      rfl
    have e4 : c.head? = some q0 := by
      rw [hcdef, List.head?_append, List.head?_take]
      simp [List.head?_eq_some_head hl_ne, q0]
    have hcyc : c.IsChain G.Adj ∧ ∀ a ∈ c.getLast?, ∀ b ∈ c.head?, G.Adj a b := by
      refine ⟨List.isChain_append.2 ⟨hlch.take _, ?_, ?_⟩, ?_⟩
      · rw [List.isChain_reverse]
        exact (hlch.drop _).imp (fun a b h => h.symm)
      · intro x hx y hy
        rw [e1] at hx
        rw [e2] at hy
        simp at hx hy
        subst hx hy
        exact hB
      · intro a ha b hb
        rw [e3] at ha
        rw [e4] at hb
        simp at ha hb
        subst ha hb
        exact (hA).symm
    -- every vertex lies on the path
    have hall : ∀ w, w ∈ l := by
      intro w
      by_contra hw
      obtain ⟨p⟩ := hconn q0 w
      obtain ⟨d, -, hd1, hd2⟩ := p.exists_boundary_dart {x | x ∈ l} (List.head_mem hl_ne) hw
      have hqc : d.fst ∈ c := hperm.mem_iff.mpr hd1
      obtain ⟨c', hc'p, hc'ch, hc'h⟩ := rot hcyc hqc
      have hnd' : (d.snd :: c').Nodup := by
        refine List.nodup_cons.2 ⟨?_, (hc'p.trans hperm).nodup_iff.mpr hlnd⟩
        intro hmem
        exact hd2 ((hc'p.trans hperm).mem_iff.mp hmem)
      have hch' : (d.snd :: c').IsChain G.Adj := by
        refine List.isChain_cons.2 ⟨?_, hc'ch⟩
        intro y hy
        rw [hc'h] at hy
        simp at hy
        subst hy
        exact (d.adj).symm
      have := hmax _ hnd' hch'
      rw [List.length_cons, (hc'p.trans hperm).length_eq] at this
      omega
    have hmn' : m = n := by
      have h1 : l.toFinset = Finset.univ := by
        ext w
        simp [hall w]
      have h2 := List.toFinset_card_of_nodup hlnd
      rw [h1, Finset.card_univ] at h2
      omega
    omega
  have hdisj' : Disjoint S T := Finset.disjoint_left.mpr (fun j h1 h2 => hdisj j h1 h2)
  have hsub : S ∪ T ⊆ Finset.range (m - 1) := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact (Finset.mem_filter.mp hx).1
    · exact (Finset.mem_filter.mp hx).1
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj', Finset.card_range] at hcard
  refine ⟨ext_head, ext_last, by omega, ?_, hS, hT⟩
  intro j hj hA hB
  apply hdisj j
  · simp only [S, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hA⟩
  · simp only [T, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hB⟩

/-- Lemma 4 for a path `l` of the graph with a vertex `x₀` removed. -/
lemma lemma4g [DecidableRel G.Adj] (x₀ : V) (l : List V) (hne : l ≠ [])
    (hnd : l.Nodup) (hch : l.IsChain G.Adj) (hx : x₀ ∉ l)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∉ l' → l'.length ≤ l.length)
    (hout : ∃ v ∈ l, ∃ y, y ∉ l ∧ G.Adj v y ∧ y ≠ x₀) (h2 : 2 ≤ l.length) :
    (∀ y, G.Adj (l.head hne) y → y ∈ l ∨ y = x₀) ∧
      (∀ y, G.Adj (l.getLast hne) y → y ∈ l ∨ y = x₀) ∧
      ∃ s t : ℕ, G.degree (l.head hne) ≤ s + 1 ∧
        (¬ G.Adj (l.head hne) x₀ → G.degree (l.head hne) ≤ s) ∧
        G.degree (l.getLast hne) ≤ t + 1 ∧
        (¬ G.Adj (l.getLast hne) x₀ → G.degree (l.getLast hne) ≤ t) ∧ s + t + 1 ≤ l.length := by
  classical
  have hlnd := hnd
  have hlch := hch
  set q0 := l.head hne
  set z := l.getLast hne
  have ext_head : ∀ y, G.Adj q0 y → y ∈ l ∨ y = x₀ := by
    intro y hy
    by_contra hyl
    push Not at hyl
    have := hmax (y :: l) (List.nodup_cons.2 ⟨hyl.1, hlnd⟩)
      (List.IsChain.cons_of_ne_nil hne hlch ((hy).symm))
      (by simp only [List.mem_cons, not_or]; exact ⟨Ne.symm hyl.2, hx⟩)
    simp only [List.length_cons] at this
    omega
  have ext_last : ∀ y, G.Adj z y → y ∈ l ∨ y = x₀ := by
    intro y hy
    by_contra hyl
    push Not at hyl
    have hch : (l ++ [y]).IsChain G.Adj := by
      refine List.isChain_append.2 ⟨hlch, List.isChain_singleton _, ?_⟩
      intro x hx y' hy'
      rw [List.getLast?_eq_some_getLast hne] at hx
      simp at hx hy'
      subst hx hy'
      exact hy
    have hnd : (l ++ [y]).Nodup := by
      rw [List.nodup_append]
      refine ⟨hlnd, List.nodup_singleton _, ?_⟩
      intro a ha b hb
      simp at hb
      subst hb
      rintro rfl
      exact hyl.1 ha
    have := hmax _ hnd hch (by simp only [List.mem_append, List.mem_singleton, not_or]; exact ⟨hx, Ne.symm hyl.2⟩)
    simp only [List.length_append, List.length_singleton] at this
    omega
  have hl_ne := hne
  set m := l.length with hm
  have hq0 : l.getD 0 q0 = q0 := getD_zero l hl_ne q0
  have hz : l.getD (m - 1) q0 = z := getD_last l hl_ne q0
  have htwo : 2 ≤ m := h2
  have hneEnds : q0 ≠ z := by
    intro he
    have ieq : l[0]'(by omega) = l[m-1]'(by omega) := by
      rw [← List.getD_eq_getElem (d := q0), ← List.getD_eq_getElem (d := q0), hq0, hz]
      exact he
    have hh := hlnd.getElem_inj_iff.mp ieq
    omega
  -- The two index sets of possible crossing chords.
  let S := (Finset.range (m - 1)).filter (fun j => G.Adj q0 (l.getD (j + 1) q0))
  let T := (Finset.range (m - 1)).filter (fun j => G.Adj (l.getD j q0) z)
  have hS : (G.neighborFinset q0).erase x₀ ⊆ S.image (fun j => l.getD (j + 1) q0) := by
    intro y hy
    rw [Finset.mem_erase, mem_neighborFinset] at hy
    obtain ⟨hyx, hy⟩ := hy
    rcases ext_head y hy with hyl | hyl
    swap
    · exact absurd hyl hyx
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hyl
    have hk0 : k ≠ 0 := by
      rintro rfl
      apply hy.ne
      rw [← List.getD_eq_getElem (d := q0), hq0]
    rw [Finset.mem_image]
    refine ⟨k - 1, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, ?_⟩
      rw [show k - 1 + 1 = k by omega, List.getD_eq_getElem _ _ hk]
      exact hy
    · rw [show k - 1 + 1 = k by omega, List.getD_eq_getElem _ _ hk]
  have hT : (G.neighborFinset z).erase x₀ ⊆ T.image (fun j => l.getD j q0) := by
    intro y hy
    rw [Finset.mem_erase, mem_neighborFinset] at hy
    obtain ⟨hyx, hy⟩ := hy
    rcases ext_last y hy with hyl | hyl
    swap
    · exact absurd hyl hyx
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hyl
    have hkm : k ≠ m - 1 := by
      rintro rfl
      apply hy.ne
      rw [← List.getD_eq_getElem (d := q0), hz]
    rw [Finset.mem_image]
    refine ⟨k, ?_, List.getD_eq_getElem _ _ hk⟩
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    rw [List.getD_eq_getElem _ _ hk]
    exact (hy).symm
  have hSd : G.degree q0 ≤ S.card + 1 := by
    rw [← card_neighborFinset_eq_degree]
    have h1 := Finset.card_le_card hS
    have h2 := Finset.card_image_le (s := S) (f := fun j => l.getD (j + 1) q0)
    have h3 := Finset.pred_card_le_card_erase (s := G.neighborFinset q0) (a := x₀)
    omega
  have hSd' : ¬ G.Adj q0 x₀ → G.degree q0 ≤ S.card := by
    intro hn
    rw [← card_neighborFinset_eq_degree]
    have : x₀ ∉ G.neighborFinset q0 := by rwa [mem_neighborFinset]
    rw [Finset.erase_eq_of_notMem this] at hS
    exact (Finset.card_le_card hS).trans Finset.card_image_le
  have hTd : G.degree z ≤ T.card + 1 := by
    rw [← card_neighborFinset_eq_degree]
    have h1 := Finset.card_le_card hT
    have h2 := Finset.card_image_le (s := T) (f := fun j => l.getD j q0)
    have h3 := Finset.pred_card_le_card_erase (s := G.neighborFinset z) (a := x₀)
    omega
  have hTd' : ¬ G.Adj z x₀ → G.degree z ≤ T.card := by
    intro hn
    rw [← card_neighborFinset_eq_degree]
    have : x₀ ∉ G.neighborFinset z := by rwa [mem_neighborFinset]
    rw [Finset.erase_eq_of_notMem this] at hT
    exact (Finset.card_le_card hT).trans Finset.card_image_le
  have hdisj : ∀ j, j ∈ S → j ∈ T → False := by
    intro j hjS hjT
    rw [Finset.mem_filter, Finset.mem_range] at hjS hjT
    obtain ⟨hjm, hA⟩ := hjS
    obtain ⟨-, hB⟩ := hjT
    -- the cycle
    set c := l.take (j + 1) ++ (l.drop (j + 1)).reverse with hcdef
    have hperm : c.Perm l := by
      have := (List.Perm.append_left (l.take (j + 1)) (List.reverse_perm (l.drop (j + 1))))
      rw [List.take_append_drop] at this
      exact this
    have hcnd : c.Nodup := hperm.nodup_iff.mpr hlnd
    have hj1 : j < m := by omega
    have hj2 : j + 1 < m := by omega
    have e1 : (l.take (j + 1)).getLast? = some (l.getD j q0) := by
      rw [List.getLast?_take, List.getD_eq_getElem _ _ hj1]
      simp [List.getElem?_eq_getElem hj1]
    have e2 : (l.drop (j + 1)).reverse.head? = some z := by
      rw [List.head?_reverse, List.getLast?_drop, if_neg (by omega), List.getLast?_eq_some_getLast hl_ne]
    have e3 : c.getLast? = some (l.getD (j + 1) q0) := by
      rw [hcdef, List.getLast?_append, List.getLast?_reverse, List.head?_drop,
        List.getElem?_eq_getElem hj2, List.getD_eq_getElem _ _ hj2]
      rfl
    have e4 : c.head? = some q0 := by
      rw [hcdef, List.head?_append, List.head?_take]
      simp [List.head?_eq_some_head hl_ne, q0]
    have hcyc : c.IsChain G.Adj ∧ ∀ a ∈ c.getLast?, ∀ b ∈ c.head?, G.Adj a b := by
      refine ⟨List.isChain_append.2 ⟨hlch.take _, ?_, ?_⟩, ?_⟩
      · rw [List.isChain_reverse]
        exact (hlch.drop _).imp (fun a b h => h.symm)
      · intro x hx y hy
        rw [e1] at hx
        rw [e2] at hy
        simp at hx hy
        subst hx hy
        exact hB
      · intro a ha b hb
        rw [e3] at ha
        rw [e4] at hb
        simp at ha hb
        subst ha hb
        exact (hA).symm
    -- every vertex lies on the path
    obtain ⟨v, hv, y, hyl, hvy, hyx⟩ := hout
    have hqc : v ∈ c := hperm.mem_iff.mpr hv
    obtain ⟨c', hc'p, hc'ch, hc'h⟩ := rot hcyc hqc
    have hnd' : (y :: c').Nodup := by
      refine List.nodup_cons.2 ⟨?_, (hc'p.trans hperm).nodup_iff.mpr hlnd⟩
      intro hmem
      exact hyl ((hc'p.trans hperm).mem_iff.mp hmem)
    have hch' : (y :: c').IsChain G.Adj := by
      refine List.isChain_cons.2 ⟨?_, hc'ch⟩
      intro w hw
      rw [hc'h] at hw
      simp at hw
      subst hw
      exact hvy.symm
    have hxc' : x₀ ∉ y :: c' := by
      simp only [List.mem_cons, not_or]
      exact ⟨Ne.symm hyx, fun hh => hx ((hc'p.trans hperm).mem_iff.mp hh)⟩
    have := hmax _ hnd' hch' hxc'
    rw [List.length_cons, (hc'p.trans hperm).length_eq] at this
    omega
  have hdisj' : Disjoint S T := Finset.disjoint_left.mpr (fun j h1 h2 => hdisj j h1 h2)
  have hsub : S ∪ T ⊆ Finset.range (m - 1) := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact (Finset.mem_filter.mp hx).1
    · exact (Finset.mem_filter.mp hx).1
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj', Finset.card_range] at hcard
  exact ⟨ext_head, ext_last, S.card, T.card, hSd, hSd', hTd, hTd', by omega⟩

/-- A permutation of `y :: l` that is a chain contradicts maximality. -/
lemma longer_of_perm (l : List V) (hnd : l.Nodup)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → l'.length ≤ l.length)
    (y : V) (hy : y ∉ l) {c : List V} (hc : c.Perm (y :: l)) (hch : c.IsChain G.Adj) : False := by
  have hnd' : c.Nodup := hc.nodup_iff.mpr (List.nodup_cons.2 ⟨hy, hnd⟩)
  have := hmax c hnd' hch
  rw [hc.length_eq] at this
  simp only [List.length_cons] at this
  omega

/-- Inserting an off-path vertex between two consecutive path vertices. -/
lemma no_insert (l : List V) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → l'.length ≤ l.length)
    (y : V) (hy : y ∉ l) (k : ℕ) (hk0 : 0 < k) (hk : k < l.length)
    (h1 : G.Adj (l[k - 1]'(by omega)) y) (h2 : G.Adj y (l[k]'hk)) : False := by
  refine longer_of_perm l hnd hmax y hy (c := l.take k ++ y :: l.drop k)
    (List.perm_middle.trans ?_) ?_
  · rw [List.take_append_drop]
  · refine List.isChain_append.2 ⟨hch.take _, ?_, ?_⟩
    · refine List.isChain_cons.2 ⟨?_, hch.drop _⟩
      intro z hz
      rw [List.head?_drop, List.getElem?_eq_getElem hk] at hz
      simp only [Option.mem_def, Option.some.injEq] at hz
      subst hz
      exact h2
    · intro x hx z hz
      rw [List.getLast?_take, if_neg (by omega)] at hx
      simp only [List.getElem?_eq_getElem (by omega : k - 1 < l.length), Option.some_or,
        Option.mem_def, Option.some.injEq] at hx
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hz
      subst hx hz
      exact h1

/-- Lemma 5 (a),(b): a vertex `y` off a longest path adjacent to `l[j]`. -/
lemma lemma5ab [DecidableRel G.Adj] (hconn : G.Connected) (l : List V) (hne : l ≠ [])
    (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → l'.length ≤ l.length)
    (y : V) (hy : y ∉ l) (j : ℕ) (hj : j < l.length) (hadj : G.Adj y (l.getD j y)) :
    0 < j ∧ j + 1 < l.length ∧ ¬ G.Adj y (l.getD (j + 1) y) ∧ ¬ G.Adj y (l.getD (j - 1) y) ∧
      ¬ G.Adj (l.head hne) (l.getD (j + 1) y) ∧ ¬ G.Adj (l.getLast hne) (l.getD (j - 1) y) := by
  have hjd : l.getD j y = l[j] := List.getD_eq_getElem _ _ hj
  rw [hjd] at hadj
  have hlast : l.getLast hne = l[l.length - 1]'(by omega) := List.getLast_eq_getElem _
  have hhead : l.head hne = l[0]'(by omega) := by
    cases l with
    | nil => exact absurd rfl hne
    | cons a t => rfl
  have h0 : 0 < j := by
    by_contra h
    have hj0 : j = 0 := by omega
    subst hj0
    refine longer_of_perm l hnd hmax y hy (c := y :: l) (List.Perm.refl _) ?_
    refine List.IsChain.cons_of_ne_nil hne hch ?_
    rw [hhead]
    exact hadj
  have h1 : j + 1 < l.length := by
    by_contra h
    have hjl : j = l.length - 1 := by omega
    subst hjl
    refine longer_of_perm l hnd hmax y hy (c := l ++ [y]) (List.perm_append_comm.trans (List.Perm.refl _)) ?_
    refine List.isChain_append.2 ⟨hch, List.isChain_singleton _, ?_⟩
    intro x hx y' hy'
    rw [List.getLast?_eq_some_getLast hne] at hx
    simp at hx hy'
    subst hx hy'
    rw [hlast]
    exact hadj.symm
  refine ⟨h0, h1, ?_, ?_, ?_, ?_⟩
  · rw [List.getD_eq_getElem _ _ h1]
    intro hadj2
    exact no_insert l hnd hch hmax y hy (j + 1) (by omega) h1 (by simpa using hadj.symm) hadj2
  · rw [List.getD_eq_getElem _ _ (by omega : j - 1 < l.length)]
    intro hadj2
    exact no_insert l hnd hch hmax y hy j h0 hj hadj2.symm hadj
  · rw [List.getD_eq_getElem _ _ h1, hhead]
    intro hadj2
    refine longer_of_perm l hnd hmax y hy
      (c := y :: ((l.take (j + 1)).reverse ++ l.drop (j + 1))) ?_ ?_
    · refine List.Perm.cons _ ?_
      exact ((List.reverse_perm _).append_right _).trans (by rw [List.take_append_drop])
    · refine List.isChain_cons.2 ⟨?_, ?_⟩
      · intro z hz
        rw [List.head?_append, List.head?_reverse] at hz
        have e : (l.take (j + 1)).getLast? = some l[j] := by
          rw [List.getLast?_take]
          simp [List.getElem?_eq_getElem hj]
        rw [e] at hz
        simp only [Option.some_or, Option.mem_def, Option.some.injEq] at hz
        subst hz
        exact hadj.symm.symm
      · refine List.isChain_append.2 ⟨?_, hch.drop _, ?_⟩
        · rw [List.isChain_reverse]
          exact (hch.take _).imp (fun a b h => h.symm)
        · intro x hx z hz
          rw [List.getLast?_reverse] at hx
          rw [List.head?_drop, List.getElem?_eq_getElem h1] at hz
          simp only [Option.mem_def, Option.some.injEq] at hx hz
          subst hz
          have : (l.take (j + 1)).head? = some l[0] := by
            rw [List.head?_take, if_neg (by omega), List.head?_eq_some_head hne, hhead]
          rw [this] at hx
          simp only [Option.some.injEq] at hx
          subst hx
          exact hadj2
  · rw [List.getD_eq_getElem _ _ (by omega : j - 1 < l.length), hlast]
    intro hadj2
    refine longer_of_perm l hnd hmax y hy
      (c := (l.take j ++ (l.drop j).reverse) ++ [y]) ?_ ?_
    · refine List.perm_append_singleton _ _ |>.trans (List.Perm.cons _ ?_)
      exact (List.Perm.append_left _ (List.reverse_perm _)).trans (by rw [List.take_append_drop])
    · have e1 : (l.take j).getLast? = some l[j - 1] := by
        rw [List.getLast?_take, if_neg (by omega)]
        simp [List.getElem?_eq_getElem (by omega : j - 1 < l.length)]
      have e2 : (l.drop j).reverse.head? = some l[l.length - 1] := by
        rw [List.head?_reverse, List.getLast?_drop, if_neg (by omega),
          List.getLast?_eq_some_getLast hne, hlast]
      refine List.isChain_append.2 ⟨?_, List.isChain_singleton _, ?_⟩
      · refine List.isChain_append.2 ⟨hch.take _, ?_, ?_⟩
        · rw [List.isChain_reverse]
          exact (hch.drop _).imp (fun a b h => h.symm)
        · intro x hx z hz
          rw [e1] at hx
          rw [e2] at hz
          simp only [Option.mem_def, Option.some.injEq] at hx hz
          subst hx hz
          exact hadj2.symm
      · intro x hx z hz
        simp at hz
        subst hz
        have e3 : (l.take j ++ (l.drop j).reverse).getLast? = some l[j] := by
          rw [List.getLast?_append, List.getLast?_reverse, List.head?_drop,
            List.getElem?_eq_getElem hj]
          rfl
        rw [e3] at hx
        simp only [Option.mem_def, Option.some.injEq] at hx
        subst hx
        exact hadj.symm

/-- Two steps along a path give distance exactly two. -/
lemma dist_two (hconn : G.Connected) {y a b : V} (h1 : G.Adj y a) (h2 : G.Adj a b)
    (h3 : ¬ G.Adj y b) (h4 : b ≠ y) : G.dist y b = 2 := by
  have hle : G.dist y b ≤ 2 := by
    have := SimpleGraph.dist_le (Walk.cons h1 (Walk.cons h2 Walk.nil))
    simpa using this
  have h0 : G.dist y b ≠ 0 := fun h => h4 ((hconn.dist_eq_zero_iff.mp h).symm)
  have h1' : G.dist y b ≠ 1 := fun h => h3 (SimpleGraph.dist_eq_one_iff_adj.mp h)
  omega

/-- Lemma 5 (c): an off-path vertex with all neighbours on the path has many
vertices at even distance. -/
lemma lemma5c [DecidableRel G.Adj] (hconn : G.Connected) (l : List V)
    (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → l'.length ≤ l.length)
    (y : V) (hy : y ∉ l) (hN : ∀ z, G.Adj y z → z ∈ l) (hdeg : 1 ≤ G.degree y) :
    G.degree y + 2 ≤ distEven G y := by
  classical
  obtain ⟨z0, hz0⟩ : ∃ z, G.Adj y z := by
    have := hdeg
    rw [← card_neighborFinset_eq_degree] at this
    obtain ⟨z, hz⟩ := Finset.card_pos.mp this
    exact ⟨z, (mem_neighborFinset _ _ _).mp hz⟩
  have hne : l ≠ [] := List.ne_nil_of_mem (hN z0 hz0)
  set I := (Finset.range l.length).filter (fun i => G.Adj y (l.getD i y)) with hI
  have hmemI : ∀ i, i ∈ I ↔ i < l.length ∧ G.Adj y (l.getD i y) := by
    intro i
    simp only [hI, Finset.mem_filter, Finset.mem_range]
  have hab : ∀ i ∈ I, 0 < i ∧ i + 1 < l.length ∧ ¬ G.Adj y (l.getD (i + 1) y) ∧
      ¬ G.Adj y (l.getD (i - 1) y) := by
    intro i hi
    obtain ⟨hi1, hi2⟩ := (hmemI i).mp hi
    obtain ⟨a, b, c, d, -, -⟩ := lemma5ab hconn l hne hnd hch hmax y hy i hi1 hi2
    exact ⟨a, b, c, d⟩
  have hinj : ∀ i ∈ I, ∀ i' ∈ I, l.getD i y = l.getD i' y → i = i' := by
    intro i hi i' hi' h
    obtain ⟨hi1, -⟩ := (hmemI i).mp hi
    obtain ⟨hi1', -⟩ := (hmemI i').mp hi'
    rw [List.getD_eq_getElem _ _ hi1, List.getD_eq_getElem _ _ hi1'] at h
    exact hnd.getElem_inj_iff.mp h
  have hdegI : G.degree y = I.card := by
    rw [← card_neighborFinset_eq_degree]
    have : G.neighborFinset y = I.image (fun i => l.getD i y) := by
      ext w
      rw [mem_neighborFinset, Finset.mem_image]
      constructor
      · intro hw
        obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem (hN w hw)
        exact ⟨k, (hmemI k).mpr ⟨hk, by rw [List.getD_eq_getElem _ _ hk]; exact hw⟩,
          List.getD_eq_getElem _ _ hk⟩
      · rintro ⟨i, hi, rfl⟩
        exact ((hmemI i).mp hi).2
    rw [this, Finset.card_image_of_injOn hinj]
  have hIne : I.Nonempty := by
    rw [← Finset.card_pos, ← hdegI]
    omega
  set i0 := I.min' hIne with hi0
  have hi0I : i0 ∈ I := Finset.min'_mem _ _
  obtain ⟨hi0pos, hi0len, -, hi0pred⟩ := hab i0 hi0I
  have hadjl : ∀ i, i + 1 < l.length → G.Adj (l.getD i y) (l.getD (i + 1) y) := by
    intro i hi
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hi]
    exact hch.getElem i hi
  have hnotin : ∀ i, i < l.length → l.getD i y ≠ y := by
    intro i hi h
    apply hy
    rw [← h, List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem _
  let T : Finset V := insert (l.getD (i0 - 1) y) (I.image (fun i => l.getD (i + 1) y))
  have hT2 : ∀ w ∈ T, G.dist y w = 2 := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · refine dist_two hconn (a := l.getD i0 y) ((hmemI i0).mp hi0I).2 ?_ hi0pred (hnotin _ (by omega))
      have := hadjl (i0 - 1) (by omega)
      rw [show i0 - 1 + 1 = i0 by omega] at this
      exact this.symm
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
      obtain ⟨-, hi2, hi3, -⟩ := hab i hi
      exact dist_two hconn (a := l.getD i y) ((hmemI i).mp hi).2 (hadjl i hi2) hi3
        (hnotin _ hi2)
  have hTcard : T.card = I.card + 1 := by
    rw [Finset.card_insert_of_notMem, Finset.card_image_of_injOn]
    · intro i hi i' hi' h
      obtain ⟨-, h1, -, -⟩ := hab i hi
      obtain ⟨-, h1', -, -⟩ := hab i' hi'
      simp only at h
      rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h1'] at h
      have := hnd.getElem_inj_iff.mp h
      omega
    · intro hmem
      obtain ⟨i, hi, hieq⟩ := Finset.mem_image.mp hmem
      obtain ⟨-, h1, -, -⟩ := hab i hi
      rw [List.getD_eq_getElem _ _ (by omega : i0 - 1 < l.length),
        List.getD_eq_getElem _ _ h1] at hieq
      have := hnd.getElem_inj_iff.mp hieq
      have hle := Finset.min'_le I i hi
      omega
  have hsub : insert y T ⊆ Finset.univ.filter (fun w => Even (G.dist y w)) := by
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases Finset.mem_insert.mp hw with rfl | hw
    · simp
    · rw [hT2 w hw]
      exact even_two
  have hyT : y ∉ T := by
    intro hyT
    have := hT2 y hyT
    simp at this
  have := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hyT] at this
  change _ ≤ distEven G y at this
  omega

/-- Lemma 3, first part: neighbours of a vertex at odd distance `≥ 3` from `v`
lie at distance `≥ 2` from `v`. -/
lemma lemma3a (hconn : G.Connected) (v w : V) (hw : 3 ≤ G.dist v w)
    (u : V) (hu : G.Adj w u) : 2 ≤ G.dist v u := by
  by_contra hlt
  have h1 := hconn.dist_triangle (u := v) (v := u) (w := w)
  have h2 : G.dist u w = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hu.symm
  omega

/-- Lemma 3, second part: counting of vertices outside the closed neighbourhood. -/
lemma lemma3b [DecidableRel G.Adj] (hconn : G.Connected) (v : V)
    (hv : distEven G v ≤ 1 + secondSmallestDegree G) :
    (Finset.univ.filter (fun w => 2 ≤ G.dist v w)).card ≤ secondSmallestDegree G +
      (Finset.univ.filter (fun w => 3 ≤ G.dist v w ∧ Odd (G.dist v w))).card := by
  classical
  set E := Finset.univ.filter (fun w => Even (G.dist v w)) with hE
  have hEc : E.card = distEven G v := by
    simp only [hE, distEven]
  have hvE : v ∈ E := by simp [hE]
  have hsub : Finset.univ.filter (fun w => 2 ≤ G.dist v w) ⊆
      E.erase v ∪ Finset.univ.filter (fun w => 3 ≤ G.dist v w ∧ Odd (G.dist v w)) := by
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    rw [Finset.mem_union]
    rcases Nat.even_or_odd (G.dist v w) with he | ho
    · left
      rw [Finset.mem_erase]
      refine ⟨?_, by simp [hE, he]⟩
      rintro rfl
      simp at hw
    · right
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨?_, ho⟩
      rcases ho with ⟨k, hk⟩
      omega
  have h1 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have h2 := Finset.card_erase_of_mem hvE
  omega

/-- Case A of Theorem C: some longest path has both ends different from `x₀`. -/
lemma caseA [Nontrivial V] [DecidableRel G.Adj] (hconn : G.Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hn : Fintype.card V ≤ 2 * secondSmallestDegree G + 2)
    (x₀ : V) (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (l : List V) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (h1 : l.head hne ≠ x₀) (h2 : l.getLast hne ≠ x₀) : False := by
  classical
  obtain ⟨v0⟩ := (inferInstance : Nonempty V)
  set n := Fintype.card V with hn
  set σ := secondSmallestDegree G with hσ
  set a := l.head hne with ha
  set b := l.getLast hne with hb
  set m := l.length with hm
  have hm2 : 2 ≤ m := by
    obtain ⟨y, hy⟩ := hconn.preconnected.exists_adj_of_nontrivial v0
    have hh := hmax [v0, y] (by simp [hy.ne]) (by simpa using hy)
    simpa using hh
  obtain ⟨-, -, hsum, hdisj, hSd, hTd⟩ := lemma4 hconn l hne hnd hch hmax hlt hm2
  simp only [← ha, ← hb] at hsum hdisj hSd hTd
  have hxa : σ ≤ G.degree a := hx0 a h1
  have hxb : σ ≤ G.degree b := hx0 b h2
  have hsum' : G.degree a + G.degree b + 1 ≤ m := hsum
  have hmσ : m = 2 * σ + 1 := by omega
  have hnσ : n = m + 1 := by omega
  set f : ℕ → V := fun i => l.getD i a with hf
  have hf_get : ∀ i (hi : i < m), f i = l[i] := fun i hi => List.getD_eq_getElem _ _ hi
  have hf_mem : ∀ i, i < m → f i ∈ l := fun i hi => by rw [hf_get i hi]; exact List.getElem_mem _
  have hf_inj : ∀ i j, i < m → j < m → f i = f j → i = j := by
    intro i j hi hj h
    rw [hf_get i hi, hf_get j hj] at h
    exact hnd.getElem_inj_iff.mp h
  have hf_ex : ∀ w ∈ l, ∃ i, i < m ∧ f i = w := by
    intro w hw
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hw
    exact ⟨k, hk, hf_get k hk⟩
  have hf_adj : ∀ i, i + 1 < m → G.Adj (f i) (f (i + 1)) := by
    intro i hi
    rw [hf_get i (by omega), hf_get (i + 1) hi]
    exact hch.getElem i hi
  have hf0 : f 0 = a := by
    rw [hf_get 0 (by omega)]
    cases l with
    | nil => exact absurd rfl hne
    | cons x t => rfl
  set S := (Finset.range (m - 1)).filter (fun j => G.Adj a (f (j + 1))) with hS
  set T := (Finset.range (m - 1)).filter (fun j => G.Adj (f j) b) with hT
  have hSc : σ ≤ S.card := hxa.trans hSd
  have hTc : σ ≤ T.card := hxb.trans hTd
  have hdisjST : Disjoint S T := by
    refine Finset.disjoint_left.mpr (fun j h1 h2 => ?_)
    simp only [hS, hT, Finset.mem_filter, Finset.mem_range] at h1 h2
    exact hdisj j (by omega) h1.2 h2.2
  have hunion : S ∪ T = Finset.range (m - 1) := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rcases Finset.mem_union.mp hx with hx | hx <;> exact (Finset.mem_filter.mp hx).1
    · rw [Finset.card_union_of_disjoint hdisjST, Finset.card_range]
      omega
  have hTcard : T.card = σ := by
    have hc := Finset.card_union_of_disjoint hdisjST
    rw [hunion, Finset.card_range] at hc
    omega
  have hpart : ∀ j, j + 1 < m → G.Adj a (f (j + 1)) ∨ G.Adj (f j) b := by
    intro j hj
    have : j ∈ S ∪ T := by rw [hunion]; simp; omega
    rcases Finset.mem_union.mp this with h | h
    · exact Or.inl (Finset.mem_filter.mp h).2
    · exact Or.inr (Finset.mem_filter.mp h).2
  -- the unique vertex off the path
  have hexy : ∃ y, y ∉ l := by
    by_contra hcon
    push Not at hcon
    have h1 : l.toFinset = Finset.univ := by
      ext w
      simp [hcon w]
    have h2 := List.toFinset_card_of_nodup hnd
    rw [h1, Finset.card_univ] at h2
    omega
  obtain ⟨y, hy⟩ := hexy
  have hall : ∀ z, z ∈ l ∨ z = y := by
    intro z
    by_contra hcon
    push Not at hcon
    have hnd2 : (y :: z :: l).Nodup := by
      simp [hcon.2, hcon.1, hy, Ne.symm hcon.2, hnd]
    have := List.toFinset_card_of_nodup hnd2
    have h3 := Finset.card_le_univ (y :: z :: l).toFinset
    simp only [List.length_cons] at this
    omega
  have hNy : ∀ z, G.Adj y z → z ∈ l := by
    intro z hz
    rcases hall z with h | h
    · exact h
    · exact absurd (h ▸ hz) (G.loopless.irrefl y)
  have hdegy : 1 ≤ G.degree y := by
    obtain ⟨z, hz⟩ := hconn.preconnected.exists_adj_of_nontrivial y
    rw [← card_neighborFinset_eq_degree]
    exact Finset.card_pos.mpr ⟨z, (mem_neighborFinset _ _ _).mpr hz⟩
  have h5c := lemma5c hconn l hnd hch hmax y hy hNy hdegy
  have hyx0 : y = x₀ := by
    by_contra hne0
    have := hx0 y hne0
    have := hH y
    omega
  have hxy : ∀ w, w ≠ y → σ ≤ G.degree w := fun w hw => hx0 w (hyx0 ▸ hw)
  -- neighbours of y are neighbours of a
  have hyN : ∀ w, G.Adj y w → G.Adj a w ∧ w ≠ a := by
    intro w hw
    obtain ⟨j, hj, rfl⟩ := hf_ex w (hNy w hw)
    have hy' : l.getD j y = f j := by
      rw [List.getD_eq_getElem _ _ hj, hf_get j hj]
    obtain ⟨h0, h1, -, -, -, h6⟩ := lemma5ab hconn l hne hnd hch hmax y hy j hj
      (by rw [hy']; exact hw)
    have hy1 : l.getD (j - 1) y = f (j - 1) := by
      rw [List.getD_eq_getElem _ _ (by omega), hf_get (j - 1) (by omega)]
    rw [← hb, hy1] at h6
    have h6' : ¬ G.Adj b (f (j - 1)) := h6
    refine ⟨?_, fun h => ?_⟩
    · rcases hpart (j - 1) (by omega) with h | h
      · rw [show j - 1 + 1 = j by omega] at h
        exact h
      · exact absurd h.symm h6'
    · have := hf_inj j 0 hj (by omega) (h.trans hf0.symm)
      omega
  have hd2 : ∀ u, u ≠ a → ¬ G.Adj a u → 2 ≤ G.dist a u := by
    intro u hu1 hu2
    have h0 : G.dist a u ≠ 0 := fun h => hu1 (hconn.dist_eq_zero_iff.mp h).symm
    have h1 : G.dist a u ≠ 1 := fun h => hu2 (SimpleGraph.dist_eq_one_iff_adj.mp h)
    omega
  have hay : G.dist a y = 2 := by
    obtain ⟨z, hz⟩ := hconn.preconnected.exists_adj_of_nontrivial y
    obtain ⟨hz1, -⟩ := hyN z hz
    refine dist_two hconn hz1 hz.symm ?_ ?_
    · intro h
      exact (hyN a h.symm).2 rfl
    · intro h
      exact hy (by rw [h]; exact List.head_mem hne)
  set Timg := T.image (fun i => f (i + 1)) with hTimg
  have hTi_card : Timg.card = σ := by
    rw [hTimg, Finset.card_image_of_injOn, hTcard]
    intro i hi i' hi' h
    have hi1 := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    have hi1' := Finset.mem_range.mp (Finset.mem_filter.mp hi').1
    have := hf_inj (i + 1) (i' + 1) (by omega) (by omega) h
    omega
  have hTimg_l : ∀ u ∈ Timg, u ∈ l := by
    intro u hu
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
    have := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    exact hf_mem _ (by omega)
  have hTimg_d : ∀ u ∈ Timg, 2 ≤ G.dist a u := by
    intro u hu
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
    have hi1 := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    apply hd2
    · intro h
      have := hf_inj (i + 1) 0 (by omega) (by omega) (h.trans hf0.symm)
      omega
    · intro h
      exact Finset.disjoint_left.mp hdisjST
        (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi1, h⟩) hi
  set U := Finset.univ.filter (fun w => 2 ≤ G.dist a w) with hU
  have hU_sub : U ⊆ insert y Timg := by
    intro u hu
    have hu2 : 2 ≤ G.dist a u := (Finset.mem_filter.mp hu).2
    rw [Finset.mem_insert]
    rcases hall u with hul | rfl
    · right
      obtain ⟨k, hk, rfl⟩ := hf_ex u hul
      have hk0 : k ≠ 0 := by
        rintro rfl
        rw [hf0] at hu2
        simp at hu2
      rcases hpart (k - 1) (by omega) with h | h
      · rw [show k - 1 + 1 = k by omega] at h
        have := SimpleGraph.dist_eq_one_iff_adj.mpr h
        omega
      · exact Finset.mem_image.mpr ⟨k - 1, Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (by omega), h⟩, by rw [show k - 1 + 1 = k by omega]⟩
    · left; rfl
  have hyT : y ∉ Timg := fun h => hy (hTimg_l y h)
  have hU_card : σ + 1 ≤ U.card := by
    have : insert y Timg ⊆ U := by
      intro u hu
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases Finset.mem_insert.mp hu with rfl | hu
      · omega
      · exact hTimg_d u hu
    have := Finset.card_le_card this
    rw [Finset.card_insert_of_notMem hyT] at this
    omega
  have h3b : U.card ≤ σ + (Finset.univ.filter
      (fun w => 3 ≤ G.dist a w ∧ Odd (G.dist a w))).card := lemma3b hconn a (hH a)
  obtain ⟨w, hwF⟩ : (Finset.univ.filter (fun w => 3 ≤ G.dist a w ∧ Odd (G.dist a w))).Nonempty := by
    rw [← Finset.card_pos]
    omega
  obtain ⟨-, hw3, -⟩ := (by simpa using hwF : True ∧ 3 ≤ G.dist a w ∧ Odd (G.dist a w))
  have hwy : w ≠ y := by
    rintro rfl
    omega
  have hwU : w ∈ U := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
  have hwT : w ∈ Timg := by
    rcases Finset.mem_insert.mp (hU_sub hwU) with h | h
    · exact absurd h hwy
    · exact h
  have hnb : G.neighborFinset w ⊆ Timg.erase w := by
    intro u hu
    rw [mem_neighborFinset] at hu
    have hu2 := lemma3a hconn a w hw3 u hu
    have huU : u ∈ U := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu2⟩
    rw [Finset.mem_erase]
    refine ⟨hu.ne.symm, ?_⟩
    rcases Finset.mem_insert.mp (hU_sub huU) with rfl | h
    · exfalso
      have := SimpleGraph.dist_eq_one_iff_adj.mpr (hyN w hu.symm).1
      omega
    · exact h
  have hdw := Finset.card_le_card hnb
  rw [Finset.card_erase_of_mem hwT, hTi_card, card_neighborFinset_eq_degree] at hdw
  have := hxy w hwy
  have hpos : 0 < Timg.card := Finset.card_pos.mpr ⟨w, hwT⟩
  omega

/-- A path leaving the vertex set of a list. -/
lemma exists_out_edge (hconn : G.Connected) (l : List V) (hne : l ≠ []) (hnd : l.Nodup)
    (hlt : l.length < Fintype.card V) : ∃ v ∈ l, ∃ y, y ∉ l ∧ G.Adj v y := by
  classical
  obtain ⟨w, hw⟩ : ∃ w, w ∉ l := by
    by_contra hcon
    push Not at hcon
    have h1 : l.toFinset = Finset.univ := by
      ext w
      simp [hcon w]
    have h2 := List.toFinset_card_of_nodup hnd
    rw [h1, Finset.card_univ] at h2
    omega
  obtain ⟨p⟩ := hconn (l.head hne) w
  obtain ⟨d, -, hd1, hd2⟩ := p.exists_boundary_dart {x | x ∈ l} (List.head_mem hne) hw
  exact ⟨d.fst, hd1, d.snd, hd2, d.adj⟩

/-- Case B, the longest path starts at `x₀`. -/
lemma caseB_aux [Nontrivial V] [DecidableRel G.Adj] (hconn : G.Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hn : Fintype.card V ≤ 2 * secondSmallestDegree G + 2)
    (x₀ : V) (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (t : List V) (hnd : (x₀ :: t).Nodup) (hch : (x₀ :: t).IsChain G.Adj)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → l'.length ≤ (x₀ :: t).length)
    (hlt : (x₀ :: t).length < Fintype.card V)
    (hall : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → l'.length = (x₀ :: t).length →
      ∀ h : l' ≠ [], l'.head h = x₀ ∨ l'.getLast h = x₀) : False := by
  classical
  obtain ⟨v0⟩ := (inferInstance : Nonempty V)
  have hne : (x₀ :: t) ≠ [] := List.cons_ne_nil _ _
  have hm2 : 2 ≤ (x₀ :: t).length := by
    obtain ⟨y, hy⟩ := hconn.preconnected.exists_adj_of_nontrivial v0
    have hh := hmax [v0, y] (by simp [hy.ne]) (by simpa using hy)
    simpa using hh
  obtain ⟨hext, hextL, hsum⟩ := lemma4 hconn (x₀ :: t) hne hnd hch hmax hlt hm2
  have hext' : ∀ y, G.Adj x₀ y → y ∈ x₀ :: t := hext
  have hdeg1 : 1 ≤ G.degree x₀ := by
    obtain ⟨z, hz⟩ := hconn.preconnected.exists_adj_of_nontrivial x₀
    rw [← card_neighborFinset_eq_degree]
    exact Finset.card_pos.mpr ⟨z, (mem_neighborFinset _ _ _).mpr hz⟩
  by_cases hdeg2 : 2 ≤ G.degree x₀
  · exfalso
    obtain ⟨j, hj2, hjm, hadjj⟩ : ∃ j, 2 ≤ j ∧ ∃ hj : j < (x₀ :: t).length,
        G.Adj x₀ (x₀ :: t)[j] := by
      have h1 : 1 < (G.neighborFinset x₀).card := by
        rw [card_neighborFinset_eq_degree]
        omega
      obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp h1
      rw [mem_neighborFinset] at hu hv
      obtain ⟨ku, hku, rfl⟩ := List.getElem_of_mem (hext' u hu)
      obtain ⟨kv, hkv, rfl⟩ := List.getElem_of_mem (hext' v hv)
      have hk0 : ∀ k (hk : k < (x₀ :: t).length), G.Adj x₀ (x₀ :: t)[k] → k ≠ 0 := by
        intro k hk h hk0
        subst hk0
        exact G.loopless.irrefl x₀ (by simpa using h)
      have hne' : ku ≠ kv := fun h => huv (by subst h; rfl)
      have h1 := hk0 ku hku hu
      have h2 := hk0 kv hkv hv
      by_cases hle : ku ≤ kv
      · exact ⟨kv, by omega, hkv, hv⟩
      · exact ⟨ku, by omega, hku, hu⟩
    set L := x₀ :: t with hL
    have e0 : (L.take j).getLast? = some L[j - 1] := by
      rw [List.getLast?_take, if_neg (by omega)]
      simp [List.getElem?_eq_getElem (by omega : j - 1 < L.length)]
    have e1 : (L.take j).head? = some x₀ := by
      rw [List.head?_take, if_neg (by omega)]
      rfl
    have hcperm : ((L.take j).reverse ++ L.drop j).Perm L :=
      ((List.reverse_perm _).append_right _).trans (by rw [List.take_append_drop])
    have hcch : ((L.take j).reverse ++ L.drop j).IsChain G.Adj := by
      refine List.isChain_append.2 ⟨?_, hch.drop _, ?_⟩
      · rw [List.isChain_reverse]
        exact (hch.take _).imp (fun a b h => h.symm)
      · intro x hx z hz
        rw [List.getLast?_reverse, e1] at hx
        rw [List.head?_drop, List.getElem?_eq_getElem hjm] at hz
        simp only [Option.mem_def, Option.some.injEq] at hx hz
        subst hx hz
        exact hadjj
    have hcne : (L.take j).reverse ++ L.drop j ≠ [] := by
      intro h
      have := hcperm.length_eq
      rw [h] at this
      simp at this
    have hcl := hcperm.length_eq
    have hhd : ((L.take j).reverse ++ L.drop j).head? = some L[j - 1] := by
      rw [List.head?_append, List.head?_reverse, e0]
      rfl
    have hlst : ((L.take j).reverse ++ L.drop j).getLast? = some L[L.length - 1] := by
      rw [List.getLast?_append, List.getLast?_drop, if_neg (by omega),
        List.getLast?_eq_some_getLast hne, List.getLast_eq_getElem]
      rfl
    have hidx : ∀ k (hk : k < L.length), L[k] = x₀ → k = 0 := by
      intro k hk h
      have h0 : L[0]'(by omega) = x₀ := rfl
      exact hnd.getElem_inj_iff.mp (h.trans h0.symm)
    rcases hall _ (hcperm.nodup_iff.mpr hnd) hcch hcl hcne with h | h
    · have := (List.head?_eq_some_head hcne).symm.trans hhd
      simp only [Option.some.injEq] at this
      rw [this] at h
      have := hidx _ (by omega) h
      omega
    · have := (List.getLast?_eq_some_getLast hcne).symm.trans hlst
      simp only [Option.some.injEq] at this
      rw [this] at h
      have := hidx _ (by omega) h
      omega
  · have hdeg1' : G.degree x₀ = 1 := by omega
    exfalso
    have hht : t ≠ [] := by
      rintro rfl
      simp at hm2
    have hN1 : ∀ u, G.Adj x₀ u → u = t.head hht := by
      have hcard : (G.neighborFinset x₀).card ≤ 1 := by
        rw [card_neighborFinset_eq_degree]; omega
      intro u hu
      have hc : G.Adj x₀ (t.head hht) := by
        have := (List.isChain_cons.mp hch).1
        exact this _ (by simp [List.head?_eq_some_head hht])
      exact Finset.card_le_one.mp hcard u ((mem_neighborFinset _ _ _).mpr hu) _
        ((mem_neighborFinset _ _ _).mpr hc)
    obtain ⟨v, hv, y, hyl, hvy⟩ := exists_out_edge hconn (x₀ :: t) hne hnd hlt
    have hvx : v ≠ x₀ := by
      rintro rfl
      exact hyl (hext' y hvy)
    have hvt : v ∈ t := by
      rcases List.mem_cons.mp hv with h | h
      · exact absurd h hvx
      · exact h
    have hyt : y ∉ t := fun h => hyl (List.mem_cons_of_mem _ h)
    have hyx : y ≠ x₀ := fun h => hyl (h ▸ List.mem_cons_self)
    have hxt : x₀ ∉ t := (List.nodup_cons.mp hnd).1
    have hndt : t.Nodup := (List.nodup_cons.mp hnd).2
    have hcht : t.IsChain G.Adj := (List.isChain_cons.mp hch).2
    have hm3 : 2 ≤ t.length := by
      by_contra hlt2
      have hl1 : t.length = 1 := by
        have : t.length ≠ 0 := fun h => hht (List.length_eq_zero_iff.mp h)
        omega
      obtain ⟨w, rfl⟩ := List.length_eq_one_iff.mp hl1
      simp only [List.mem_singleton] at hvt
      subst hvt
      have := hextL y (by simpa using hvy)
      exact hyl this
    have hmaxg : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∉ l' → l'.length ≤ t.length := by
      intro l' h1 h2 h3
      by_contra hcon
      push Not at hcon
      have hle := hmax l' h1 h2
      have hl' : l'.length = (x₀ :: t).length := by
        simp only [List.length_cons] at hle ⊢
        omega
      have hl'ne : l' ≠ [] := by
        rintro rfl
        simp at hcon
      rcases hall l' h1 h2 hl' hl'ne with h | h
      · exact h3 (h ▸ List.head_mem hl'ne)
      · exact h3 (h ▸ List.getLast_mem hl'ne)
    obtain ⟨-, -, s, t', hs, -, ht1, ht2, hst⟩ := lemma4g x₀ t hht hndt hcht hxt hmaxg
      ⟨v, hvt, y, hyt, hvy, hyx⟩ hm3
    have hcx : t.head hht ≠ x₀ := fun h => hxt (h ▸ List.head_mem hht)
    have hzx : t.getLast hht ≠ x₀ := fun h => hxt (h ▸ List.getLast_mem hht)
    have hlast_ne : t.getLast hht ≠ t.head hht := by
      intro heq
      cases t with
      | nil => exact hht rfl
      | cons h0 t2 =>
        have ht2 : t2 ≠ [] := by
          rintro rfl
          simp at hm3
        have hmem : (h0 :: t2).getLast hht ∈ t2 := by
          rw [List.getLast_cons ht2]
          exact List.getLast_mem ht2
        have hnd' := (List.nodup_cons.mp hndt).1
        apply hnd'
        have : (h0 :: t2).getLast hht = h0 := heq
        rw [← this]
        exact hmem
    have hcadj : G.Adj (t.head hht) x₀ := by
      have := (List.isChain_cons.mp hch).1
      exact (this _ (by simp [List.head?_eq_some_head hht])).symm
    have hzna : ¬ G.Adj (t.getLast hht) x₀ := by
      intro h
      exact hlast_ne (hN1 _ h.symm)
    have hdc := hx0 _ hcx
    have hdz := hx0 _ hzx
    have hs' := hs
    have ht2' := ht2 hzna
    have hlen : (x₀ :: t).length = t.length + 1 := rfl
    have hmσ : (x₀ :: t).length = 2 * secondSmallestDegree G + 1 := by omega
    -- the unique vertex off the path
    obtain ⟨y', hy'⟩ : ∃ y', y' ∉ x₀ :: t := by
      by_contra hcon
      push Not at hcon
      have h1 : (x₀ :: t).toFinset = Finset.univ :=
        Finset.eq_univ_of_forall (fun w => List.mem_toFinset.mpr (hcon w))
      have h2 := List.toFinset_card_of_nodup hnd
      rw [h1, Finset.card_univ] at h2
      omega
    have hall' : ∀ z, z ∈ x₀ :: t ∨ z = y' := by
      intro z
      by_contra hcon
      push Not at hcon
      have hnd2 : (y' :: z :: (x₀ :: t)).Nodup := by
        simp [hcon.2, hcon.1, hy', Ne.symm hcon.2, hnd]
      have := List.toFinset_card_of_nodup hnd2
      have h3 := Finset.card_le_univ (y' :: z :: (x₀ :: t)).toFinset
      simp only [List.length_cons] at this
      omega
    have hNy : ∀ z, G.Adj y' z → z ∈ x₀ :: t := by
      intro z hz
      rcases hall' z with h | h
      · exact h
      · exact absurd (h ▸ hz) (G.loopless.irrefl y')
    have hdegy : 1 ≤ G.degree y' := by
      obtain ⟨z, hz⟩ := hconn.preconnected.exists_adj_of_nontrivial y'
      rw [← card_neighborFinset_eq_degree]
      exact Finset.card_pos.mpr ⟨z, (mem_neighborFinset _ _ _).mpr hz⟩
    have h5c := lemma5c hconn (x₀ :: t) hnd hch hmax y' hy' hNy hdegy
    have hy'x : y' ≠ x₀ := fun h => hy' (h ▸ List.mem_cons_self)
    have := hx0 y' hy'x
    have := hH y'
    omega

/-- Case B of Theorem C: every longest path has `x₀` as an end. -/
lemma caseB [Nontrivial V] [DecidableRel G.Adj] (hconn : G.Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hn : Fintype.card V ≤ 2 * secondSmallestDegree G + 2)
    (x₀ : V) (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (l : List V) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (hall : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → l'.length = l.length →
      ∀ h : l' ≠ [], l'.head h = x₀ ∨ l'.getLast h = x₀) : False := by
  rcases hall l hnd hch rfl hne with h | h
  · cases l with
    | nil => exact hne rfl
    | cons a t =>
      have : a = x₀ := h
      subst this
      exact caseB_aux hconn hH hn a hx0 t hnd hch hmax hlt hall
  · have hrne : l.reverse ≠ [] := by simpa using hne
    have hrh : l.reverse.head hrne = x₀ := by
      rw [List.head_reverse]
      exact h
    have hrch : l.reverse.IsChain G.Adj := by
      rw [List.isChain_reverse]
      exact hch.imp (fun a b h => h.symm)
    cases hlr : l.reverse with
    | nil => exact hrne hlr
    | cons a t =>
      have ha : a = x₀ := by
        have : (a :: t).head (by simp) = x₀ := by simpa [hlr] using hrh
        exact this
      subst ha
      rw [hlr] at hrch
      have hlen : (a :: t).length = l.length := by rw [← hlr]; simp
      refine caseB_aux hconn hH hn a hx0 t (by rw [← hlr]; exact List.nodup_reverse.mpr hnd) hrch
        (fun l' h1 h2 => hlen ▸ hmax l' h1 h2) (hlen ▸ hlt) ?_
      intro l' h1 h2 h3 h4
      exact hall l' h1 h2 (h3.trans hlen) h4

/-- Theorem C: `n ≤ 2σ + 2` and the even-distance bound give a Hamiltonian path. -/
theorem theorem_C [Nontrivial V] [DecidableRel G.Adj] (hconn : G.Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hn : Fintype.card V ≤ 2 * secondSmallestDegree G + 2) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  obtain ⟨x₀, -, hmin⟩ := Finset.exists_min_image Finset.univ (fun v : V => G.degree v)
    Finset.univ_nonempty
  have hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v := by
    intro v hv
    rcases degree_pair (G := G) x₀ v (Ne.symm hv) with h | h
    · exact h.trans (hmin v (Finset.mem_univ v))
    · exact h
  obtain ⟨l, hne, hnd, hch, hmax⟩ := exists_longest (G := G)
  by_cases hlen : l.length = Fintype.card V
  · exact ham_of_list l hne hnd hch hlen
  exfalso
  have hlt : l.length < Fintype.card V := lt_of_le_of_ne hnd.length_le_card hlen
  by_cases hex : ∃ l' : List V, ∃ h : l' ≠ [], l'.Nodup ∧ l'.IsChain G.Adj ∧
      l'.length = l.length ∧ l'.head h ≠ x₀ ∧ l'.getLast h ≠ x₀
  · obtain ⟨l', h', hnd', hch', hlen', h1, h2⟩ := hex
    exact caseA hconn hH hn x₀ hx0 l' h' hnd' hch'
      (fun l'' a b => (hmax l'' a b).trans hlen'.symm.le) (hlen' ▸ hlt) h1 h2
  · push Not at hex
    refine caseB hconn hH hn x₀ hx0 l hne hnd hch hmax hlt ?_
    intro l' hnd' hch' hlen' h'
    by_cases h1 : l'.head h' = x₀
    · exact Or.inl h1
    · exact Or.inr (hex l' h' hnd' hch' hlen' h1)

end Paths


theorem main : H1 → H2 → type_of% @WrittenOnTheWallII.GraphConjecture189.conjecture189 := by
  intro h1 h2 V _ _ _ G _ hc hb
  classical
  let e := Fintype.equivFin V
  let φ := SimpleGraph.Iso.map e G
  have : Nontrivial (Fin (Fintype.card V)) := e.symm.nontrivial
  have hc' := φ.connected_iff.mp hc
  have h : ∀ y, distEven (G.map e) y ≤ 1 + secondSmallestDegree (G.map e) := by
    intro y
    obtain ⟨x,rfl⟩ := φ.surjective y
    rw [even_iso φ hc, second_iso φ]
    exact (Finset.le_max' _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ x))).trans hb
  obtain ⟨a,b,q,hq⟩ : ∃ a b : Fin (Fintype.card V), ∃ q : (G.map e).Walk a b, q.IsHamiltonian := by
    by_cases hn : Fintype.card (Fin (Fintype.card V)) ≤ 2 * secondSmallestDegree (G.map e) + 2
    · exact theorem_C hc' h hn
    · by_cases hart : ∃ c : Fin (Fintype.card V), ¬ ((G.map e).induce {x | x ≠ c}).Connected
      · exact h1 (G.map e) hc' h (by omega) hart
      · push Not at hart
        exact h2 (G.map e) hc' h (by omega) hart
  exact ⟨φ.symm a,φ.symm b,q.map φ.symm.toHom,hq.map _ φ.symm.bijective⟩

end OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2
